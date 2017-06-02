#include <postgres.h>
#include <nodes/parsenodes.h>
#include <lib/stringinfo.h>
#include <utils/builtins.h>
#include <utils/formatting.h>
#include <foreign/foreign.h>
#include <commands/defrem.h>
#include <utils/lsyscache.h>
#include <utils/syscache.h>
#include <catalog/pg_type.h>
#include <access/htup_details.h>
#include <sqlite3.h>

#include "sqlite_fdw.h"
#include "funcs.h"


static char const * translate_sqliteType__(char const * type);
static char const * get_affinity__(char const * type);
static void add_columnDefinition__(StringInfoData *cftsql, int counter,
                                   SqliteTableImportOptions importOpts,
                                   sqlite3_stmt *columns);


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
 *   storage class. It it fails, then it goes to being a blob.
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
    return db;
}


sqlite3_stmt *
prepare_sqliteQuery(sqlite3 *db, char *query, const char **pzTail)
{
    sqlite3_stmt *stmt;
    
    elog(SQLITE_FDW_LOG_LEVEL, 
         "entering function prepare_sqliteQuery with \n%s", query);

	/* Execute the query */
	if ( sqlite3_prepare_v2(db, query, -1, &stmt, pzTail) != 
            SQLITE_OK )
	{
		sqlite3_close(db);
		ereport(ERROR,
			(errcode(ERRCODE_FDW_UNABLE_TO_CREATE_EXECUTION),
			errmsg("SQL error during prepare: %s", sqlite3_errmsg(db))
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
