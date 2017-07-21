#include <postgres.h>
#include <catalog/pg_collation.h>
#include <miscadmin.h>
#include <nodes/parsenodes.h>
#include <nodes/relation.h>
#include <nodes/execnodes.h>
#include <nodes/nodeFuncs.h>
#include <lib/stringinfo.h>
#include <utils/builtins.h>
#include <utils/formatting.h>
#include <foreign/foreign.h>
#include <commands/defrem.h>
#include <utils/lsyscache.h>
#include <utils/syscache.h>
#include <utils/selfuncs.h>
#include <utils/varlena.h>
#include <utils/guc.h>
#include <catalog/pg_type.h>
#include <access/htup_details.h>
#include <optimizer/clauses.h>
#include <optimizer/cost.h>
#include <optimizer/tlist.h>
#include <optimizer/pathnode.h>
#include <parser/parse_oper.h>
#include <executor/executor.h>

#include <sys/stat.h>
#include <sqlite3.h>
#include <signal.h>
#include <unistd.h>

#include "sqlite_private.h"


static char const * translate_sqliteType__(char const * type);
static char const * get_affinity__(char const * type);
static void add_columnDefinition__(StringInfoData *cftsql, int counter,
                                   SqliteTableImportOptions importOpts,
                                   sqlite3_stmt *columns);


static int
compare_text(void * tmp, int len1, const void * str1,
             int len2, const void * str2)
{
    return varstr_cmp((char *)str1, len1, 
                      (char *)str2, len2,
                      DEFAULT_COLLATION_OID);
}


typedef struct PgTypeInputTraits__ 
{
    regproc   typeinput;
    int       typmod;
    bool      valid;
} PgTypeInputTraits__;

static PgTypeInputTraits__ get_pgTypeInputTraits__(Oid pgtyp);
static Datum make_datumFloat__(sqlite3_stmt *stmt, int col, Oid pgtyp, 
                               PgTypeInputTraits__ traits);
static Datum make_datumInt__(sqlite3_stmt *stmt, int col, Oid pgtyp, 
                             PgTypeInputTraits__ traits);
static Datum make_datumViaCString__(sqlite3_stmt *stmt, int col,
                                    PgTypeInputTraits__ traits);



/*
 *   https://sqlite.org/datatype3.html
 *   Sqlite3 has two notions embedded in it
 *   1. Storage class. This represents the value on disk and can be
 *      a. null, 
 *      b. integer 
 *      c. real
 *      d. text
 *      e. blob.
 *   2. Column affinity. This can take values:
 *      a. Text
 *      b. Numeric
 *      c. Integer
 *      d. Real
 *      e. Blob
 *
 *   When sqlite wants to store a value it looks up the column
 *   affinity and tries to cast the value into the appropriate
 *   storage class. If it fails, then it goes to being a blob.
 *   
 *   Numeric is a union of Real and Integer. There are rules 
 *   about trying to convert input Numeric text to real, then trying
 *   further to make it an integer (if possible losslessly)
 *
 *   For our use case we will not be able to tolerate any
 *   ambiguity. We are going to support types:
 *      a. Text
 *      b. Integer
 *      c. Real
 *      d. Blob 
 *     and further more
 *      e. Timestamp
 *      f. Date
 *      b. Boolean
 *   In other words when the column type (as specified in a 
 *   sqlite schema) maps via affinity to Text, Integer, Real
 *   or Blob, then we are good to go. In addition if the 
 *   column type is explicity timestamp, date or boolean then 
 *   again we are good.
 *   Otherwise we croak.
 */
static char const *
translate_sqliteType__(char const *type)
{
    char const * affinity;
    type = asc_tolower(type, strlen(type) + 1);
    affinity = get_affinity__(type);
    
    if ( strcmp(affinity, "Text") == 0 )
        return "text";
    if ( strcmp(affinity, "Integer") == 0 )
        return "bigint";
    if ( strcmp(affinity, "Real") == 0 )
        return "double precision";
    if ( strcmp(affinity, "Blob") == 0 )
        return "bytea";

    // Now we have the Numeric affinity
    // and we will see if we have timestamp, date, boolean
    if ( strcmp(type, "timestamp") == 0 ||
         strcmp(type, "date") )
        return type;

    if ( strncmp(type, "bool", 4) == 0 )
        return "boolean";
    
    ereport(ERROR,
        (errcode(ERRCODE_FDW_ERROR),
        errmsg("Could not handle type %s from a sqlite db", type)
        ));
}


/*
 *   See comments for translate_sqliteType__
 *   Implementing the affinity deduction rules set out in
 *   https://sqlite.org/datatype3.html   section 3.1
 */
static char const*
get_affinity__(char const *type)
{
    if ( strstr(type, "int") != NULL )
        return "Integer";

    if ( strstr(type, "char") != NULL ||
         strstr(type, "clob") != NULL ||
         strstr(type, "text") != NULL )
        return "Text";

    if ( strstr(type, "blob") != NULL )
        return "Blob";
    
    if ( strstr(type, "real") != NULL ||
         strstr(type, "floa") != NULL ||
         strstr(type, "doub") != NULL )
        return "Real";
    
    return "Numeric";
}


sqlite3 *
get_sqliteDbHandle(char const *filename)
{
    sqlite3 *db;
	if (sqlite3_open(filename, &db) != SQLITE_OK) 
		ereport(ERROR,
			(errcode(ERRCODE_FDW_OUT_OF_MEMORY),
			errmsg("Can't open sqlite database %s: %s", 
                    filename, 
                    sqlite3_errmsg(db))
			));
    
    /*
     *  Remap the BINARY collation of sqlite3 to use the comparison 
     *  operator provided by postgres (DEFAULT_COLLATION_OID)
     */
    sqlite3_create_collation_v2(db, "BINARY", SQLITE_UTF8, 
                                NULL, compare_text, NULL);
    return db;
}


sqlite3_stmt *
prepare_sqliteQuery(sqlite3 *db, char *query, const char **pzTail)
{
    sqlite3_stmt *stmt;
    
	/* Execute the query */
	if ( sqlite3_prepare_v2(db, query, -1, &stmt, pzTail) != 
            SQLITE_OK )
	{
		sqlite3_close(db);
		ereport(ERROR,
			(errcode(ERRCODE_FDW_UNABLE_TO_CREATE_EXECUTION),
			errmsg("SQL error during prepare: %s\n query was: %s", 
                    sqlite3_errmsg(db), query)
			));
	}
    return stmt;
}


bool
is_sqliteTableRequired(ImportForeignSchemaStmt *stmt, 
                       char const * tablename)
{
	ListCell   *lc;

    switch ( stmt->list_type )
    {
        case FDW_IMPORT_SCHEMA_LIMIT_TO:
            foreach(lc, stmt->table_list)
            {
                RangeVar *rv = (RangeVar *) lfirst(lc);
                if ( strcmp(tablename, rv->relname) == 0 )
                    return true;
            }
            return false;

        case FDW_IMPORT_SCHEMA_EXCEPT:
            foreach(lc, stmt->table_list)
            {
                RangeVar *rv = (RangeVar *) lfirst(lc);
                if ( strcmp(tablename, rv->relname) == 0 )
                    return false;
            }

        default:
            return true;
    }
}


char * 
get_foreignTableCreationSql(ImportForeignSchemaStmt *stmt,
                            sqlite3 * db,
                            char const * tablename,
                            SqliteTableImportOptions importOptions)
{
    StringInfoData	cftsql;
    char  *columns_q = palloc0(strlen(tablename) + 32);
    sqlite3_stmt * volatile  columns;
    int volatile counter = 0;

    if ( !is_sqliteTableRequired(stmt, tablename) )
        return NULL;

    PG_TRY();
    {
        cftsql.data = NULL;
        
        initStringInfo(&cftsql);
        appendStringInfo(&cftsql, 
            "CREATE FOREIGN TABLE %s.%s (",
            stmt->local_schema, 
            quote_identifier(tablename));
        
        sprintf(columns_q, "PRAGMA table_info(%s)", tablename);
        columns = prepare_sqliteQuery(db, columns_q, NULL);
        while (sqlite3_step(columns) == SQLITE_ROW)
            add_columnDefinition__(&cftsql, counter++, 
                                   importOptions, columns);
    }
    PG_CATCH();
    {
        if ( cftsql.data )
            pfree(cftsql.data);
        pfree(columns_q);
        if ( columns )
            sqlite3_finalize(columns);
        PG_RE_THROW();
    }
    PG_END_TRY();
    
    if ( columns )
        sqlite3_finalize(columns);
    
    appendStringInfo(&cftsql, "\n) SERVER %s\n"
            "OPTIONS (table '%s')",
            quote_identifier(stmt->server_name),
            quote_identifier(tablename));

    return cftsql.data;
}


SqliteTableSource
get_tableSource(Oid foreigntableid)
{
	ForeignTable   *f_table;
	ForeignServer  *f_server;
	List           *options;
	ListCell       *lc;
    SqliteTableSource opt;
	
	/*
	 * Extract options from FDW objects.
	 */
	f_table = GetForeignTable(foreigntableid);
	f_server = GetForeignServer(f_table->serverid);

	options = NIL;
	options = list_concat(options, f_table->options);
	options = list_concat(options, f_server->options);

	/* Loop through the options */
	foreach(lc, options)
	{
		DefElem *def = (DefElem *) lfirst(lc);

		if (strcmp(def->defname, "database") == 0)
			opt.database = defGetString(def);

		if (strcmp(def->defname, "table") == 0)
			opt.table = defGetString(def);
	}

	if (!opt.table)
		opt.table = get_rel_name(foreigntableid);

	/* Check we have the options we need to proceed */
	if (!opt.database || !opt.table)
		ereport(ERROR,
			(errcode(ERRCODE_SYNTAX_ERROR),
			errmsg("a database and a table must be specified")
			));
    return opt;
}


static void 
add_columnDefinition__(StringInfoData *cftsql,
                       int counter,
                       SqliteTableImportOptions importOpts,
                       sqlite3_stmt *columns)
{
    char *colname = (char *) sqlite3_column_text(columns, 1);
    char *typename = sqlite3_column_type(columns, 2) ==
                         SQLITE_NULL ? "blob" :
                         (char *) sqlite3_column_text(columns, 2);
    char const *pgtypename = translate_sqliteType__(typename);

    if ( counter > 0 )
        appendStringInfo(cftsql, ",");
    appendStringInfo(cftsql, "\n");
        
    appendStringInfo(cftsql, "%s ", quote_identifier(colname));
    appendStringInfo(cftsql, "%s ", pgtypename);
    
    // the third column is 1 if column is not null in sqlite schema
    if ( importOpts.import_notnull )
        if ( sqlite3_column_int(columns, 3) == 1 )
            appendStringInfo(cftsql, " NOT NULL ");

    if ( importOpts.import_default )
        if ( sqlite3_column_type(columns, 4 ) != SQLITE_NULL )
            appendStringInfo(cftsql, " DEFAULT %s::%s ",
                    (char *) sqlite3_column_text(columns, 4),
                    pgtypename);
}


SqliteTableImportOptions 
get_sqliteTableImportOptions(ImportForeignSchemaStmt *stmt)
{
    ListCell *lc;
    SqliteTableImportOptions ret;

	foreach(lc, stmt->options)
	{
		DefElem    *def = (DefElem *) lfirst(lc);

		if (strcmp(def->defname, "import_default") == 0)
			ret.import_default = defGetBoolean(def);
		else if (strcmp(def->defname, "import_not_null") == 0)
			ret.import_notnull = defGetBoolean(def);
		else
			ereport(ERROR,
					(errcode(ERRCODE_FDW_INVALID_OPTION_NAME),
					  errmsg("invalid option \"%s\"", def->defname)));
	}

    return ret;
}


static Datum
make_datumViaCString__(sqlite3_stmt *stmt, int col, PgTypeInputTraits__ traits)
{
    return OidFunctionCall3(
                traits.typeinput, 
                CStringGetDatum((char*) sqlite3_column_text(stmt, col)),
                ObjectIdGetDatum(InvalidOid), 
                Int32GetDatum(traits.typmod));
}


static Datum
make_datumInt__(sqlite3_stmt *stmt, int col, Oid pgtyp, 
                PgTypeInputTraits__ traits)
{
    switch ( pgtyp )
    {
        case BOOLOID:
            return BoolGetDatum(sqlite3_column_int(stmt, col) > 0);
        
        case INT8OID:
            return Int64GetDatum(sqlite3_column_int(stmt, col));

        case INT4OID:
            return Int32GetDatum(sqlite3_column_int(stmt, col));

        case INT2OID:
            return Int16GetDatum(sqlite3_column_int(stmt, col));

        case CHAROID:
            return CharGetDatum((char) sqlite3_column_int(stmt, col));

        default:
            return make_datumViaCString__(stmt, col, traits);
    }
}


static Datum
make_datumFloat__(sqlite3_stmt *stmt, int col, Oid pgtyp, 
                  PgTypeInputTraits__ traits)
{
    switch ( pgtyp )
    {
        case FLOAT4OID:
            return Float4GetDatum((float) sqlite3_column_double(stmt, col));
        
        case FLOAT8OID:
            return Float8GetDatum(sqlite3_column_double(stmt, col));
        
        default:
            return make_datumViaCString__(stmt, col, traits);
    }
}


static PgTypeInputTraits__
get_pgTypeInputTraits__(Oid pgtyp)
{
    PgTypeInputTraits__ traits;
	HeapTuple tuple;
	
    tuple = SearchSysCache1(TYPEOID, ObjectIdGetDatum(pgtyp));
	if (!HeapTupleIsValid(tuple))
    {
		elog(ERROR, "cache lookup failed for type%u", pgtyp);
        traits.valid = false;
    }
    else
    {
        traits.typeinput = ((Form_pg_type)GETSTRUCT(tuple))->typinput;
	    traits.typmod  = ((Form_pg_type)GETSTRUCT(tuple))->typtypmod;
        traits.valid = true;
    }
	
	ReleaseSysCache(tuple);
    return traits;
}


Datum
make_datum(sqlite3_stmt *stmt, int col, Oid pgtyp, bool *isnull)
{
    PgTypeInputTraits__ traits = get_pgTypeInputTraits__(pgtyp);
    if (!traits.valid)
        return (Datum) 0;
	
    *isnull = false;
    switch ( sqlite3_column_type(stmt, col) )
    {
        case SQLITE_INTEGER:
            return make_datumInt__(stmt, col, pgtyp, traits);
        case SQLITE_FLOAT:
            return make_datumFloat__(stmt, col, pgtyp, traits);
        case SQLITE_TEXT:
            return make_datumViaCString__(stmt, col, traits);
        case SQLITE_BLOB:
        {
            void * blob = palloc(sqlite3_column_bytes(stmt, col) + VARHDRSZ);
            memcpy((char *)blob + VARHDRSZ, 
                    sqlite3_column_blob(stmt, col), 
                    sqlite3_column_bytes(stmt, col));
			SET_VARSIZE(blob, sqlite3_column_bytes(stmt, col) + VARHDRSZ);
			return PointerGetDatum(blob);
        }
        case SQLITE_NULL:
        default:
            *isnull = true;
            return (Datum) 0;
    }
}


/*
 * Assess whether the join between inner and outer relations can be pushed down
 * to the foreign server. As a side effect, save information we obtain in this
 * function to SqliteFdwRelationInfo passed in.
 */
bool
foreign_join_ok(PlannerInfo *root, RelOptInfo *joinrel, JoinType jointype,
				RelOptInfo *outerrel, RelOptInfo *innerrel,
				JoinPathExtraData *extra)
{
	SqliteFdwRelationInfo *fpinfo;
	SqliteFdwRelationInfo *fpinfo_o;
	SqliteFdwRelationInfo *fpinfo_i;
	ListCell   *lc;
	List	   *joinclauses;

	/*
	 * We support pushing down INNER, LEFT, RIGHT and FULL OUTER joins.
	 * Constructing queries representing SEMI and ANTI joins is hard, hence
	 * not considered right now.
	 */
	if (jointype != JOIN_INNER && jointype != JOIN_LEFT &&
		jointype != JOIN_RIGHT && jointype != JOIN_FULL)
		return false;

	/*
	 * If either of the joining relations is marked as unsafe to pushdown, the
	 * join can not be pushed down.
	 */
	fpinfo = (SqliteFdwRelationInfo *) joinrel->fdw_private;
	fpinfo_o = (SqliteFdwRelationInfo *) outerrel->fdw_private;
	fpinfo_i = (SqliteFdwRelationInfo *) innerrel->fdw_private;
	if (!fpinfo_o || !fpinfo_o->pushdown_safe ||
		!fpinfo_i || !fpinfo_i->pushdown_safe)
		return false;
    
	/*
	 * If joining relations have local conditions, those conditions are
	 * required to be applied before joining the relations. Hence the join can
	 * not be pushed down.
	 */
	if (fpinfo_o->local_conds || fpinfo_i->local_conds)
		return false;
    
	/*
	 * Merge FDW options.  We might be tempted to do this after we have deemed
	 * the foreign join to be OK.  But we must do this beforehand so that we
	 * know which quals can be evaluated on the foreign server, which might
	 * depend on shippable_extensions.
	 */
	fpinfo->src.database = fpinfo_o->src.database;
	// merge_fdw_options(fpinfo, fpinfo_o, fpinfo_i);

	/*
	 * Separate restrict list into join quals and pushed-down (other) quals.
	 *
	 * Join quals belonging to an outer join must all be shippable, else we
	 * cannot execute the join remotely.  Add such quals to 'joinclauses'.
	 *
	 * Add other quals to fpinfo->remote_conds if they are shippable, else to
	 * fpinfo->local_conds.  In an inner join it's okay to execute conditions
	 * either locally or remotely; the same is true for pushed-down conditions
	 * at an outer join.
	 *
	 * Note we might return failure after having already scribbled on
	 * fpinfo->remote_conds and fpinfo->local_conds.  That's okay because we
	 * won't consult those lists again if we deem the join unshippable.
	 */
	joinclauses = NIL;
	foreach(lc, extra->restrictlist)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);
		bool		is_remote_clause = is_foreign_expr(root, joinrel,
													   rinfo->clause);

		if (IS_OUTER_JOIN(jointype) && !rinfo->is_pushed_down)
		{
			if (!is_remote_clause)
				return false;
			joinclauses = lappend(joinclauses, rinfo);
		}
		else
		{
			if (is_remote_clause)
				fpinfo->remote_conds = lappend(fpinfo->remote_conds, rinfo);
			else
				fpinfo->local_conds = lappend(fpinfo->local_conds, rinfo);
		}
	}

	/*
	 * deparseExplicitTargetList() isn't smart enough to handle anything other
	 * than a Var.  In particular, if there's some PlaceHolderVar that would
	 * need to be evaluated within this join tree (because there's an upper
	 * reference to a quantity that may go to NULL as a result of an outer
	 * join), then we can't try to push the join down because we'll fail when
	 * we get to deparseExplicitTargetList().  However, a PlaceHolderVar that
	 * needs to be evaluated *at the top* of this join tree is OK, because we
	 * can do that locally after fetching the results from the remote side.
	 */
	foreach(lc, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = lfirst(lc);
		Relids		relids = joinrel->relids;

		if (bms_is_subset(phinfo->ph_eval_at, relids) &&
			bms_nonempty_difference(relids, phinfo->ph_eval_at))
			return false;
	}

	/* Save the join clauses, for later use. */
	fpinfo->joinspec.clauses = joinclauses;

	fpinfo->joinspec.outerrel = outerrel;
	fpinfo->joinspec.innerrel = innerrel;
	fpinfo->joinspec.type = jointype;

	/*
	 * By default, both the input relations are not required to be deparsed
	 * as subqueries, but there might be some relations covered by the input
	 * relations that are required to be deparsed as subqueries, so save the
	 * relids of those relations for later use by the deparser.
	 */
	fpinfo->subqspec.make_outerrel = false;
	fpinfo->subqspec.make_innerrel = false;
	Assert(bms_is_subset(fpinfo_o->subqspec.lower_rels, outerrel->relids));
	Assert(bms_is_subset(fpinfo_i->subqspec.lower_rels, innerrel->relids));
	fpinfo->subqspec.lower_rels = bms_union(fpinfo_o->subqspec.lower_rels,
											fpinfo_i->subqspec.lower_rels);

	/*
	 * Pull the other remote conditions from the joining relations into join
	 * clauses or other remote clauses (remote_conds) of this relation
	 * wherever possible. This avoids building subqueries at every join step.
	 *
	 * For an inner join, clauses from both the relations are added to the
	 * other remote clauses. For LEFT and RIGHT OUTER join, the clauses from
	 * the outer side are added to remote_conds since those can be evaluated
	 * after the join is evaluated. The clauses from inner side are added to
	 * the joinclauses, since they need to be evaluated while constructing the
	 * join.
	 *
	 * For a FULL OUTER JOIN, the other clauses from either relation can not
	 * be added to the joinclauses or remote_conds, since each relation acts
	 * as an outer relation for the other.
	 *
	 * The joining sides can not have local conditions, thus no need to test
	 * shippability of the clauses being pulled up.
	 */
	switch (jointype)
	{
		case JOIN_INNER:
			fpinfo->remote_conds = list_concat(fpinfo->remote_conds,
										  list_copy(fpinfo_i->remote_conds));
			fpinfo->remote_conds = list_concat(fpinfo->remote_conds,
										  list_copy(fpinfo_o->remote_conds));
			break;

		case JOIN_LEFT:
			fpinfo->joinspec.clauses = list_concat(fpinfo->joinspec.clauses,
										  list_copy(fpinfo_i->remote_conds));
			fpinfo->remote_conds = list_concat(fpinfo->remote_conds,
										  list_copy(fpinfo_o->remote_conds));
			break;

		case JOIN_RIGHT:
			fpinfo->joinspec.clauses = list_concat(fpinfo->joinspec.clauses,
										  list_copy(fpinfo_o->remote_conds));
			fpinfo->remote_conds = list_concat(fpinfo->remote_conds,
										  list_copy(fpinfo_i->remote_conds));
			break;

		case JOIN_FULL:

			/*
			 * In this case, if any of the input relations has conditions,
			 * we need to deparse that relation as a subquery so that the
			 * conditions can be evaluated before the join.  Remember it in
			 * the fpinfo of this relation so that the deparser can take
			 * appropriate action.  Also, save the relids of base relations
			 * covered by that relation for later use by the deparser.
			 */
			if (fpinfo_o->remote_conds)
			{
				fpinfo->subqspec.make_outerrel = true;
				fpinfo->subqspec.lower_rels =
					bms_add_members(fpinfo->subqspec.lower_rels,
									outerrel->relids);
			}
			if (fpinfo_i->remote_conds)
			{
				fpinfo->subqspec.make_innerrel = true;
				fpinfo->subqspec.lower_rels =
					bms_add_members(fpinfo->subqspec.lower_rels,
									innerrel->relids);
			}
			break;

		default:
			/* Should not happen, we have just check this above */
			elog(ERROR, "unsupported join type %d", jointype);
	}

	/*
	 * For an inner join, all restrictions can be treated alike. Treating the
	 * pushed down conditions as join conditions allows a top level full outer
	 * join to be deparsed without requiring subqueries.
	 */
	if (jointype == JOIN_INNER)
	{
		Assert(!fpinfo->joinspec.clauses);
		fpinfo->joinspec.clauses = fpinfo->remote_conds;
		fpinfo->remote_conds = NIL;
	}

	/* Mark that this join can be pushed down safely */
	fpinfo->pushdown_safe = true;

	/*
	 * Set the string describing this join relation to be used in EXPLAIN
	 * output of corresponding ForeignScan.
	 */
	fpinfo->relation_name = makeStringInfo();
	appendStringInfo(fpinfo->relation_name, "(%s) %s JOIN (%s)",
					 fpinfo_o->relation_name->data,
					 get_jointype_name(fpinfo->joinspec.type),
					 fpinfo_i->relation_name->data);

	/*
	 * Set the relation index.  This is defined as the position of this
	 * joinrel in the join_rel_list list plus the length of the rtable list.
	 * Note that since this joinrel is at the end of the join_rel_list list
	 * when we are called, we can get the position by list_length.
	 */
	Assert(fpinfo->relation_index == 0);	/* shouldn't be set yet */
	fpinfo->relation_index =
		list_length(root->parse->rtable) + list_length(root->join_rel_list);

	return true;
}


/*
 * Examine each qual clause in input_conds, and classify them into two groups,
 * which are returned as two lists:
 *	- remote_conds contains expressions that can be evaluated remotely
 *	- local_conds contains expressions that can't be evaluated remotely
 */
void
classifyConditions(PlannerInfo *root,
				   RelOptInfo *baserel,
				   List *input_conds,
				   List **remote_conds,
				   List **local_conds)
{
	ListCell   *lc;

	*remote_conds = NIL;
	*local_conds = NIL;

	foreach(lc, input_conds)
	{
		RestrictInfo *ri = lfirst_node(RestrictInfo, lc);

		if (is_foreign_expr(root, baserel, ri->clause))
			*remote_conds = lappend(*remote_conds, ri);
		else
			*local_conds = lappend(*local_conds, ri);
	}
}

/*
 * Returns true if given expr is safe to evaluate on the foreign server.
 */
bool
is_foreign_expr(PlannerInfo *root, RelOptInfo *baserel, Expr *expr)
{
	Oid collation = InvalidOid;

	if (!foreign_expr_walker((Node *) expr, &collation, NULL)) {
        elog(SQLITE_FDW_LOG_LEVEL,
                "foreign_expr_walker A for %s, %d",
                FDW_RELINFO(baserel->fdw_private)->relation_name->data, 
                collation);
		return false;
    }
    
	/*
	 * An expression which includes any mutable functions can't be sent over
	 * because its result is not stable.  For example, sending now() remote
	 * side could cause confusion from clock offsets.  Future versions might
	 * be able to make this choice with more granularity.  (We check this last
	 * because it requires a lot of expensive catalog lookups.)
	 */
	if (contain_mutable_functions((Node *) expr))
		return false;

	/* OK to evaluate on the remote server */
	return true;
}

    
void
sqlite_bind_param_value(SqliteFdwExecutionState *festate,
                        int index, 
                        Oid ptype, 
                        Datum pval, 
                        bool isNull)
{
    int rc;
	Oid   typoutput;
	bool  typIsVarlena;
    sqlite3_stmt *stmt = festate->stmt;
    
    if ( isNull ) 
        rc = sqlite3_bind_null(stmt, index);
    else
        switch(ptype)
        {
            case INT2OID:
                rc = sqlite3_bind_int(stmt, index, DatumGetInt16(pval));
                break;
            
            case INT4OID:
                rc = sqlite3_bind_int(stmt, index, DatumGetInt32(pval));
                break;
            
            case INT8OID:
                rc = sqlite3_bind_int64(stmt, index, DatumGetInt64(pval));
                break;

            case FLOAT4OID:
                rc = sqlite3_bind_double(stmt, index, DatumGetFloat4(pval));
                break;

            case FLOAT8OID:
                rc = sqlite3_bind_double(stmt, index, DatumGetFloat8(pval));
                break;

            case BOOLOID:
                rc = sqlite3_bind_int(stmt, index, DatumGetBool(pval) ? 1 : 0);
                break;

            case BYTEAOID:
                rc = sqlite3_bind_blob(
                        stmt, index, 
                        VARDATA(DatumGetPointer(pval)),
                        VARSIZE(DatumGetPointer(pval)), SQLITE_TRANSIENT);
                break;

            default:
	            getTypeOutputInfo(ptype, &typoutput, &typIsVarlena);
                rc = sqlite3_bind_text(
                            stmt, index, 
                            OidOutputFunctionCall(typoutput, pval), 
                            -1, SQLITE_TRANSIENT);
                break;
        }

    if ( rc != SQLITE_OK ) {
        ereport(ERROR,
            (errcode(ERRCODE_FDW_ERROR),
            errmsg("error while trying to bind param \"%s\"", 
                        sqlite3_errmsg(festate->db))
            ));
    }
}

    
static void
estimate_join_rel_cost(PlannerInfo *root, RelOptInfo *foreignrel)
{
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);
    SqliteRelationCostSize *store = &fpinfo->costsize;
    SqliteFdwRelationInfo *fpinfo_i;
    SqliteFdwRelationInfo *fpinfo_o;
    QualCost	join_cost;
    QualCost	remote_conds_cost;
    double      cross_join_nrows;

    /* For join we expect inner and outer relations set */
    Assert(fpinfo->joinspec.innerrel && fpinfo->joinspec.outerrel);
    fpinfo_i = FDW_RELINFO(fpinfo->joinspec.innerrel->fdw_private);
    fpinfo_o = FDW_RELINFO(fpinfo->joinspec.outerrel->fdw_private);
    cross_join_nrows = fpinfo_i->costsize.rows * fpinfo_o->costsize.rows;

    store->width = foreignrel->reltarget->width;
    store->startup_cost = DEFAULT_FDW_STARTUP_COST;
    store->rows = clamp_row_est(cross_join_nrows * fpinfo->joinspec.clause_sel);
    
    /*
     * Calculate required per tuple costs
     */
    cost_qual_eval(&remote_conds_cost, fpinfo->remote_conds, root);
    cost_qual_eval(&join_cost, fpinfo->joinspec.clauses, root);

    /*
     * Run time cost includes:
     *
     * 1. Run time cost of applying join clauses on the cross product
     * of the joining relations.
     *
     * 2. Run time cost of applying pushed down other clauses on the
     * result of join
     *
     * 3. Run time cost of applying nonpushable other clauses locally
     * on the result fetched from the foreign server.
     */
    
    store->run_cost = cross_join_nrows * join_cost.per_tuple;
    store->run_cost += store->rows * remote_conds_cost.per_tuple;
    store->run_cost += store->rows * store->local_conds_cost.per_tuple;
}

    
static void
estimate_upper_rel_cost(PlannerInfo *root,
					    RelOptInfo *foreignrel)
{
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);
    SqliteRelationCostSize *store = &fpinfo->costsize;
    SqliteFdwRelationInfo *ofpinfo = FDW_RELINFO(fpinfo->grouped_rel->
                                                 fdw_private);
    PathTarget *ptarget = root->upper_targets[UPPERREL_GROUP_AGG];
    AggClauseCosts aggcosts;
    double		numGroups = 1;

    /*
     * This cost model is mixture of costing done for sorted and
     * hashed aggregates in cost_agg().  We are not sure which
     * strategy will be considered at remote side, thus for
     * simplicity, we put all startup related costs in startup_cost
     * and all finalization and run cost are added in total_cost.
     *
     * Also, core does not care about costing HAVING expressions and
     * adding that to the costs.  So similarly, here too we are not
     * considering remote and local conditions for costing.
     */

    /* Collect statistics about aggregates for estimating costs. */
    MemSet(&aggcosts, 0, sizeof(AggClauseCosts));
    if (root->parse->hasAggs)
    {
        get_agg_clause_costs(root, (Node *) fpinfo->grouped_tlist,
                             AGGSPLIT_SIMPLE, &aggcosts);
        get_agg_clause_costs(root, (Node *) root->parse->havingQual,
                             AGGSPLIT_SIMPLE, &aggcosts);
    }

    /* Get number of grouping columns and possible number of groups */
    numGroups = estimate_num_groups(
                    root,
                    get_sortgrouplist_exprs(root->parse->groupClause,
                                            fpinfo->grouped_tlist),
                    ofpinfo->costsize.rows, NULL);

    store->width = foreignrel->reltarget->width;
    store->startup_cost = DEFAULT_FDW_STARTUP_COST;
    store->rows = numGroups;

    /*-----
     * Run time cost includes:
     *	  1. Run time cost of underneath input relation
     *	  2. Run time cost of performing aggregation, per cost_agg()
     *	  3. PathTarget eval cost for each output row
     *-----
     */
    store->run_cost = ofpinfo->costsize.run_cost + 
        (aggcosts.finalCost + cpu_tuple_cost 
            + ptarget->cost.per_tuple) * numGroups;
}

    
static void
estimate_base_rel_cost(PlannerInfo *root,
					   RelOptInfo *foreignrel)
{
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);
    SqliteRelationCostSize *store = &fpinfo->costsize;
	Cost	cpu_per_tuple = cpu_tuple_cost + 
                            foreignrel->baserestrictcost.per_tuple;
    /*
     * Cost as though this were a seqscan, which is pessimistic.  We
     * effectively imagine the local_conds are being evaluated
     * remotely, too. (run_cost is set as cpu_per_tuple * foreignrel->tuples)
     */
    store->width = foreignrel->reltarget->width;
    store->startup_cost = DEFAULT_FDW_STARTUP_COST;
    store->rows = foreignrel->rows;
    store->run_cost =  cpu_per_tuple * foreignrel->tuples;
}


/*
 * estimate_path_cost_size
 *		Get cost and size estimates for a foreign scan on given foreign relation
 *		either a base relation or a join between foreign relations or an upper
 *		relation containing foreign relations.
 *
 * param_join_conds are the parameterization clauses with outer relations.
 * pathkeys specify the expected sort order if any for given path being costed.
 */
void
estimate_path_cost_size(PlannerInfo *root, RelOptInfo *foreignrel)
{
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);
    SqliteRelationCostSize *store = &fpinfo->costsize;
    double retrieved_rows = 1.0;
    
    if (IS_JOIN_REL(foreignrel))
        estimate_join_rel_cost(root, foreignrel);
    else if (IS_UPPER_REL(foreignrel))
        estimate_upper_rel_cost(root, foreignrel);
    else
        estimate_base_rel_cost(root, foreignrel);
    
    /* Back into an estimate of the number of retrieved rows. */
    if ( store->local_conds_sel > 0 )
        retrieved_rows = clamp_row_est(store->rows / store->local_conds_sel);
    else
        retrieved_rows = clamp_row_est(store->rows);
    
    store->total_cost = store->startup_cost + store->run_cost +
                        cpu_tuple_cost * retrieved_rows;
    
    elog(SQLITE_FDW_LOG_LEVEL,
        "Various costs for %s, %f, %f, %f", 
            fpinfo->relation_name->data,
            store->rows,
            store->startup_cost,
            store->total_cost);
}

    
bool
file_exists(const char *name)
{
	struct stat st;

	AssertArg(name != NULL);

	if (stat(name, &st) == 0)
		return S_ISDIR(st.st_mode) ? false : true;
	else if (!(errno == ENOENT || errno == ENOTDIR || errno == EACCES))
		ereport(ERROR,
                (errcode_for_file_access(),
				 errmsg("could not access file \"%s\": %m", name)));

	return false;
}


void
sqlite_bind_param_values(ForeignScanState *node)
{
	SqliteFdwExecutionState   *festate = (SqliteFdwExecutionState *) 
                                          node->fdw_state;
    List * fdw_exprs = ((ForeignScan *) node->ss.ps.plan)->fdw_exprs;
    MemoryContext oldcontext = MemoryContextSwitchTo(
                    node->ss.ps.ps_ExprContext->ecxt_per_tuple_memory);
	ListCell   *lc, *lcf;
    int i = 0;
    
    forboth(lc, festate->param_exprs, lcf, fdw_exprs)
	{
		ExprState  *expr_state = (ExprState *) lfirst(lc);
		Datum		expr_value;
		bool		isNull;
        Oid         ptype = exprType((Node *) lfirst(lcf));

		/* Evaluate the parameter expression */
		expr_value = ExecEvalExpr(expr_state, node->ss.ps.ps_ExprContext, 
                                  &isNull);
        sqlite_bind_param_value(festate, i+1, ptype, expr_value, isNull);
        i++;
    }
    MemoryContextSwitchTo(oldcontext);
    festate->params_bound = true;
}


void
cleanup_(SqliteFdwExecutionState *festate)
{
    if ( festate->stmt ) {
        sqlite3_finalize(festate->stmt);
        festate->stmt = NULL;
    }
    if ( festate->db ) {
        sqlite3_close(festate->db);
        festate->db = NULL;
    }
}


void
add_pathsWithPathKeysForRel(PlannerInfo *root, 
                            RelOptInfo *rel,
                            Path *epq_path)
{
	ListCell   *lc;
    SqliteRelationCostSize *costs = &(FDW_RELINFO(rel)->costsize);

	/* Create one path for each set of pathkeys we find*/
	foreach(lc, get_useful_pathkeys_for_relation(root, rel))
	{
		add_path(rel, (Path *)
				 create_foreignscan_path(root, rel,
                             NULL,
                             costs->rows,
                             costs->startup_cost * DEFAULT_FDW_SORT_MULTIPLIER,
                             costs->total_cost * DEFAULT_FDW_SORT_MULTIPLIER,
                             lfirst(lc),
                             NULL,
                             epq_path,
                             NIL));
	}
}



/*
 * get_useful_pathkeys_for_relation
 *		Determine which orderings of a relation might be useful.
 *
 * Getting data in sorted order can be useful either because the requested
 * order matches the final output ordering for the overall query we're
 * planning, or because it enables an efficient merge join.  Here, we try
 * to figure out which pathkeys to consider.
 */
List *
get_useful_pathkeys_for_relation(PlannerInfo *root, RelOptInfo *rel)
{
	List	   *useful_pathkeys_list = NIL;
	ListCell   *lc;

	/*
	 * Pushing the query_pathkeys to the remote server is always worth
	 * considering, because it might let us avoid a local sort.
	 */
	if (root->query_pathkeys)
	{
		bool		query_pathkeys_ok = true;

		foreach(lc, root->query_pathkeys)
		{
			PathKey    *pathkey = (PathKey *) lfirst(lc);
			EquivalenceClass *pathkey_ec = pathkey->pk_eclass;
			Expr	   *em_expr;

			/*
			 * The planner and executor don't have any clever strategy for
			 * taking data sorted by a prefix of the query's pathkeys and
			 * getting it to be sorted by all of those pathkeys. We'll just
			 * end up resorting the entire data set.  So, unless we can push
			 * down all of the query pathkeys, forget it.
			 *
			 * is_foreign_expr would detect volatile expressions as well, but
			 * checking ec_has_volatile here saves some cycles.
			 */
			if (pathkey_ec->ec_has_volatile ||
				!(em_expr = find_em_expr_for_rel(pathkey_ec, rel)) ||
				!is_foreign_expr(root, rel, em_expr))
			{
				query_pathkeys_ok = false;
				break;
			}
		}

		if (query_pathkeys_ok)
			useful_pathkeys_list = list_make1(list_copy(root->query_pathkeys));
	}

    return useful_pathkeys_list;
}



/*
 * Detect whether we want to process an EquivalenceClass member.
 *
 * This is a callback for use by generate_implied_equalities_for_column.
 */
bool
ec_member_matches_foreign(PlannerInfo *root, RelOptInfo *rel,
						  EquivalenceClass *ec, EquivalenceMember *em,
						  void *arg)
{
	ec_member_foreign_arg *state = (ec_member_foreign_arg *) arg;
	Expr	   *expr = em->em_expr;

	/*
	 * If we've identified what we're processing in the current scan, we only
	 * want to match that expression.
	 */
	if (state->current != NULL)
		return equal(expr, state->current);

	/*
	 * Otherwise, ignore anything we've already processed.
	 */
	if (list_member(state->already_used, expr))
		return false;

	/* This is the new target to process. */
	state->current = expr;
	return true;
}


/*
 * Force assorted GUC parameters to settings that ensure that we'll output
 * data values in a form that is unambiguous to the remote server.
 *
 * This is rather expensive and annoying to do once per row, but there's
 * little choice if we want to be sure values are transmitted accurately;
 * we can't leave the settings in place between rows for fear of affecting
 * user-visible computations.
 *
 * We use the equivalent of a function SET option to allow the settings to
 * persist only until the caller calls reset_transmission_modes().  If an
 * error is thrown in between, guc.c will take care of undoing the settings.
 *
 * The return value is the nestlevel that must be passed to
 * reset_transmission_modes() to undo things.
 */
int
set_transmission_modes(void)
{
	int			nestlevel = NewGUCNestLevel();

	/*
	 * The values set here should match what pg_dump does.  See also
	 * configure_remote_session in connection.c.
	 */
	if (DateStyle != USE_ISO_DATES)
		(void) set_config_option("datestyle", "ISO",
								 PGC_USERSET, PGC_S_SESSION,
								 GUC_ACTION_SAVE, true, 0, false);
	if (IntervalStyle != INTSTYLE_POSTGRES)
		(void) set_config_option("intervalstyle", "postgres",
								 PGC_USERSET, PGC_S_SESSION,
								 GUC_ACTION_SAVE, true, 0, false);
	if (extra_float_digits < 3)
		(void) set_config_option("extra_float_digits", "3",
								 PGC_USERSET, PGC_S_SESSION,
								 GUC_ACTION_SAVE, true, 0, false);

	return nestlevel;
}

/*
 * Undo the effects of set_transmission_modes().
 */
void
reset_transmission_modes(int nestlevel)
{
	AtEOXact_GUC(true, nestlevel);
}


/*
 * Find an equivalence class member expression, all of whose Vars, come from
 * the indicated relation.
 */
extern Expr *
find_em_expr_for_rel(EquivalenceClass *ec, RelOptInfo *rel)
{
	ListCell   *lc_em;

	foreach(lc_em, ec->ec_members)
	{
		EquivalenceMember *em = lfirst(lc_em);

		if (bms_is_subset(em->em_relids, rel->relids))
		{
			/*
			 * If there is more than one equivalence member whose Vars are
			 * taken entirely from this relation, we'll be content to choose
			 * any one of those.
			 */
			return em->em_expr;
		}
	}

	/* We didn't find any suitable equivalence class expression */
	return NULL;
}
