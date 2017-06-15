/*-------------------------------------------------------------------------
 *
 * sqlite Foreign Data Wrapper for PostgreSQL
 *
 * Copyright (c) 2013-2016 Guillaume Lelarge
 *
 * This software is released under the PostgreSQL Licence
 *
 * Author: Guillaume Lelarge <guillaume@lelarge.info>
 *
 * IDENTIFICATION
 *        sqlite_fdw/src/sqlite_fdw.c
 *
 *-------------------------------------------------------------------------
 */

#include <postgres.h>

#include <access/reloptions.h>
#include <access/htup_details.h>
#include <foreign/fdwapi.h>
#include <foreign/foreign.h>
#include <optimizer/pathnode.h>
#include <optimizer/planmain.h>
#include <optimizer/restrictinfo.h>
#include <optimizer/var.h>
#include <optimizer/cost.h>
#include <optimizer/clauses.h>
#include <optimizer/tlist.h>
#include <optimizer/paths.h>

#include <funcapi.h>
#include <catalog/pg_collation.h>
#include <catalog/pg_foreign_server.h>
#include <catalog/pg_foreign_table.h>
#include <catalog/pg_type.h>
#include <commands/defrem.h>
#include <commands/explain.h>
#include <utils/builtins.h>
#include <utils/formatting.h>
#include <utils/rel.h>
#include <utils/selfuncs.h>
#include <utils/lsyscache.h>
#include <utils/memutils.h>
#include <nodes/nodeFuncs.h>

#include <sqlite3.h>
#include <sys/stat.h>

#include <signal.h>
#include <sys/types.h>
#include <unistd.h>

#include "sqlite_fdw.h"
#include "funcs.h"
#include "deparse.h"
#include "sqlite_private.h"

PG_MODULE_MAGIC;

/*
 * Default values
 */
/* ----
 * This value is taken from sqlite
   (without stats, sqlite defaults to 1 million tuples for a table)
 */
#define DEFAULT_ESTIMATED_LINES 1000000
#define DEFAULT_FDW_STARTUP_COST 100.0
#define DEFAULT_FDW_SORT_MULTIPLIER 1.2

/*
 * SQL functions
 */
extern Datum sqlite_fdw_handler(PG_FUNCTION_ARGS);
extern Datum sqlite_fdw_validator(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(sqlite_fdw_handler);
PG_FUNCTION_INFO_V1(sqlite_fdw_validator);


/* callback functions */
static void sqliteGetForeignRelSize(PlannerInfo *root, RelOptInfo *baserel,
						            Oid foreigntableid);
static void sqliteGetForeignPaths(PlannerInfo *root, RelOptInfo *baserel,
						          Oid foreigntableid);
static ForeignScan *sqliteGetForeignPlan(PlannerInfo *root, RelOptInfo *baserel,
						                 Oid foreigntableid,
						                 ForeignPath *best_path, List *tlist,
						                 List *scan_clauses, Plan *outer_plan);
static void sqliteBeginForeignScan(ForeignScanState *node, int eflags);
static TupleTableSlot *sqliteIterateForeignScan(ForeignScanState *node);
static void sqliteReScanForeignScan(ForeignScanState *node);
static void sqliteEndForeignScan(ForeignScanState *node);
static void sqliteAddForeignUpdateTargets(Query *parsetree,
								          RangeTblEntry *target_rte,
								          Relation target_relation);
static List *sqlitePlanForeignModify(PlannerInfo *root, ModifyTable *plan,
						             Index resultRelation,
						             int subplan_index);
static void sqliteBeginForeignModify(ModifyTableState *mtstate,
							         ResultRelInfo *rinfo,
							         List *fdw_private, int subplan_index,
							         int eflags);
static TupleTableSlot *sqliteExecForeignInsert(EState *estate,
						                       ResultRelInfo *rinfo,
						                       TupleTableSlot *slot,
						                       TupleTableSlot *planSlot);
static TupleTableSlot *sqliteExecForeignUpdate(EState *estate,
						                       ResultRelInfo *rinfo,
						                       TupleTableSlot *slot,
						                       TupleTableSlot *planSlot);
static TupleTableSlot *sqliteExecForeignDelete(EState *estate,
						   ResultRelInfo *rinfo,
						   TupleTableSlot *slot,
						   TupleTableSlot *planSlot);
static void sqliteEndForeignModify(EState *estate, ResultRelInfo *rinfo);
static void sqliteExplainForeignScan(ForeignScanState *node, 
                                     struct ExplainState *es);
static void sqliteExplainForeignModify(ModifyTableState *mtstate,
							  ResultRelInfo *rinfo,
							  List *fdw_private,
							  int subplan_index,
							  struct ExplainState *es);
static bool sqliteAnalyzeForeignTable(Relation relation,
							 AcquireSampleRowsFunc *func,
							 BlockNumber *totalpages);
static List *sqliteImportForeignSchema(ImportForeignSchemaStmt *stmt,
							           Oid serverOid);
static void sqliteGetForeignJoinPaths(PlannerInfo *root,
                          RelOptInfo *joinrel,
                          RelOptInfo *outerrel,
                          RelOptInfo *innerrel,
                          JoinType jointype,
                          JoinPathExtraData *extra);

/*
 * Helper functions
 */
static bool sqliteIsValidOption(const char *option, Oid context);
static bool file_exists(const char *name);
static void estimate_path_cost_size(PlannerInfo *root,
						RelOptInfo *baserel,
						List *join_conds,
						List *pathkeys,
                        SqliteRelationCosts *costs);
static void add_paths_with_pathkeys_for_rel(PlannerInfo *root, 
                                            RelOptInfo *rel,
								            Path *epq_path);
static const char * get_jointype_name(JoinType jointype);
static void estimate_join_rel_cost(PlannerInfo *root,
					               RelOptInfo *foreignrel,
                                   SqliteCostEstimates * est);
static void estimate_upper_rel_cost(PlannerInfo *root,
					                RelOptInfo *foreignrel,
                                    SqliteCostEstimates * est);
static void estimate_base_rel_cost(PlannerInfo *root,
					                RelOptInfo *foreignrel,
                                    SqliteCostEstimates * est);
static List * get_useful_pathkeys_for_relation(PlannerInfo *root, 
                                               RelOptInfo *rel);
static Expr * find_em_expr_for_rel(EquivalenceClass *ec, RelOptInfo *rel);
static bool ec_member_matches_foreign(PlannerInfo *root, RelOptInfo *rel,
						  EquivalenceClass *ec, EquivalenceMember *em,
						  void *arg);

/*
 * structures used by the FDW
 */

/*
 * Describes the valid options for objects that use this wrapper.
 */
struct SQLiteFdwOption
{
	const char	*optname;
	Oid		optcontext;	/* Oid of catalog in which option may appear */
};

/*
 * Describes the valid options for objects that use this wrapper.
 */
static struct SQLiteFdwOption valid_options[] =
{

	/* Connection options */
	{ "database",  ForeignServerRelationId },

	/* Table options */
	{ "table",     ForeignTableRelationId },

	/* Sentinel */
	{ NULL,			InvalidOid }
};


/*
 * FDW-specific information for ForeignScanState.fdw_state.
 */

typedef struct SqliteFdwExecutionState
{
	sqlite3       *db;
	sqlite3_stmt  *stmt;
	char          *query;
	List          *retrieved_attrs;   /* list of target attribute numbers */
} SqliteFdwExecutionState;


static void sqlite_bind_param_values(SqliteFdwExecutionState *festate,
                                     List *fdw_exprs, 
                                     ForeignScanState * node);
static void sqlite_bind_param_value(SqliteFdwExecutionState *festate,
                                    int index, 
                                    Oid ptype, 
                                    Datum pval, 
                                    bool isNull);
static void cleanup_(SqliteFdwExecutionState *);
static bool foreign_join_ok(PlannerInfo *root, RelOptInfo *joinrel,
				JoinType jointype, RelOptInfo *outerrel, RelOptInfo *innerrel,
				JoinPathExtraData *extra);


Datum
sqlite_fdw_handler(PG_FUNCTION_ARGS)
{
	FdwRoutine *fdwroutine = makeNode(FdwRoutine);

	// elog(SQLITE_FDW_LOG_LEVEL,"entering function %s", __func__);

	/* assign the handlers for the FDW */

	/* these are required */
	fdwroutine->GetForeignRelSize = sqliteGetForeignRelSize;
	fdwroutine->GetForeignPaths = sqliteGetForeignPaths;
	fdwroutine->GetForeignPlan = sqliteGetForeignPlan;
	fdwroutine->BeginForeignScan = sqliteBeginForeignScan;
	fdwroutine->IterateForeignScan = sqliteIterateForeignScan;
	fdwroutine->ReScanForeignScan = sqliteReScanForeignScan;
	fdwroutine->EndForeignScan = sqliteEndForeignScan;

	/* remainder are optional - use NULL if not required */
	/* support for insert / update / delete */
	fdwroutine->AddForeignUpdateTargets = sqliteAddForeignUpdateTargets;
	fdwroutine->PlanForeignModify = sqlitePlanForeignModify;
	fdwroutine->BeginForeignModify = sqliteBeginForeignModify;
	fdwroutine->ExecForeignInsert = sqliteExecForeignInsert;
	fdwroutine->ExecForeignUpdate = sqliteExecForeignUpdate;
	fdwroutine->ExecForeignDelete = sqliteExecForeignDelete;
	fdwroutine->EndForeignModify = sqliteEndForeignModify;

	/* support for EXPLAIN */
	fdwroutine->ExplainForeignScan = sqliteExplainForeignScan;
	fdwroutine->ExplainForeignModify = sqliteExplainForeignModify;

	/* support for ANALYSE */
	fdwroutine->AnalyzeForeignTable = sqliteAnalyzeForeignTable;

	/* support for IMPORT FOREIGN SCHEMA */
	fdwroutine->ImportForeignSchema = sqliteImportForeignSchema;
	
    /* Support functions for join push-down */
	fdwroutine->GetForeignJoinPaths = sqliteGetForeignJoinPaths;

	PG_RETURN_POINTER(fdwroutine);
}

Datum
sqlite_fdw_validator(PG_FUNCTION_ARGS)
{
	List      *options_list = untransformRelOptions(PG_GETARG_DATUM(0));
	Oid       catalog = PG_GETARG_OID(1);
	char      *svr_database = NULL;
	char      *svr_table = NULL;
	ListCell  *cell;

	// elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);

	/*
	 * Check that only options supported by sqlite_fdw,
	 * and allowed for the current object type, are given.
	 */
	foreach(cell, options_list)
	{
		DefElem	   *def = (DefElem *) lfirst(cell);

		if (!sqliteIsValidOption(def->defname, catalog))
		{
			struct SQLiteFdwOption *opt;
			StringInfoData buf;

			/*
			 * Unknown option specified, complain about it. Provide a hint
			 * with list of valid options for the object.
			 */
			initStringInfo(&buf);
			for (opt = valid_options; opt->optname; opt++)
			{
				if (catalog == opt->optcontext)
					appendStringInfo(&buf, "%s%s", (buf.len > 0) ? ", " : "",
							 opt->optname);
			}

			ereport(ERROR,
				(errcode(ERRCODE_FDW_INVALID_OPTION_NAME),
				errmsg("invalid option \"%s\"", def->defname),
				errhint("Valid options in this context are: %s", buf.len ? buf.data : "<none>")
				));
		}

		if (strcmp(def->defname, "database") == 0)
		{
			if (svr_database)
				ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					errmsg("redundant options: database (%s)", defGetString(def))
					));
			if (!file_exists(defGetString(def)))
				ereport(ERROR,
					(errcode_for_file_access(),
					errmsg("could not access file \"%s\"", defGetString(def))
					));

			svr_database = defGetString(def);
		}
		else if (strcmp(def->defname, "table") == 0)
		{
			if (svr_table)
				ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					errmsg("redundant options: table (%s)", defGetString(def))
					));

			svr_table = defGetString(def);
		}
	}

	/* Check we have the options we need to proceed */
	if (catalog == ForeignServerRelationId && !svr_database)
		ereport(ERROR,
			(errcode(ERRCODE_SYNTAX_ERROR),
			errmsg("The database name must be specified")
			));

	PG_RETURN_VOID();
}



/*
 * Check if the provided option is one of the valid options.
 * context is the Oid of the catalog holding the object the option is for.
 */
static bool
sqliteIsValidOption(const char *option, Oid context)
{
	struct SQLiteFdwOption *opt;

	for (opt = valid_options; opt->optname; opt++)
	{
		if (context == opt->optcontext && strcmp(opt->optname, option) == 0)
			return true;
	}

	return false;
}


static void
sqliteGetForeignRelSize(PlannerInfo *root,
                        RelOptInfo *baserel,
                        Oid foreigntableid)
{
	SqliteFdwRelationInfo *fpinfo;
	ListCell              *lc;
    
    //elog(SQLITE_FDW_LOG_LEVEL, 
         // "entering function sqliteGetForeignRelSize");

    // initialize the fields of baserel that we will set
	baserel->rows = 0;
	fpinfo = palloc0(sizeof(SqliteFdwRelationInfo));
    fpinfo->src = get_tableSource(foreigntableid);
    fpinfo->pushdown_safe = true;
	baserel->fdw_private = (void *) fpinfo;
    
    pull_varattnos((Node *) baserel->reltarget->exprs, 
                    baserel->relid, 
                    &fpinfo->attrs_used);
    
    //  classify the condition as local or remote
    foreach(lc, baserel->baserestrictinfo)
	{
		RestrictInfo *ri = (RestrictInfo *) lfirst(lc);

		if (is_foreignExpr(root, baserel, ri->clause))
			fpinfo->remote_conds = lappend(fpinfo->remote_conds, ri);
		else
			fpinfo->local_conds = lappend(fpinfo->local_conds, ri);
	}
	
    // fetch the attributes that are needed locally by postgres
	foreach(lc, fpinfo->local_conds)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
		pull_varattnos((Node *) rinfo->clause, 
                        baserel->relid, 
                        &fpinfo->attrs_used);
	}

    // Get the costing done
	/*
	 * Compute the selectivity and cost of the local_conds, so we don't have
	 * to do it over again for each path.  The best we can do for these
	 * conditions is to estimate selectivity on the basis of local statistics.
	 */
	fpinfo->costs.local_conds_sel = clauselist_selectivity(root,
													 fpinfo->local_conds,
													 baserel->relid,
													 JOIN_INNER,
													 NULL);

	cost_qual_eval(&fpinfo->costs.local_conds_cost, fpinfo->local_conds, root);
	
    /*
	 * Set cached relation costs to some negative value, so that we can detect
	 * when they are set to some sensible costs during one (usually the first)
	 * of the calls to estimate_path_cost_size().
	 */
	fpinfo->costs.rel_startup_cost = -1;
	fpinfo->costs.rel_total_cost = -1;

    /*
     *   We are going to assume that postgres is responsible for keeping 
     *   the statistics for the foreign tables.  This saves us the major
     *   headache of extracting/translating sqlite3 information
     */
    
    /*
     * If the foreign table has never been ANALYZEd, it will have relpages
     * and reltuples equal to zero, which most likely has nothing to do
     * with reality.  We can't do a whole lot about that if we're not
     * allowed to consult the remote server, but we can use a hack similar
     * to plancat.c's treatment of empty relations: use a minimum size
     * estimate of 10 pages, and divide by the column-datatype-based width
     * estimate to get the corresponding number of tuples.
     */
    if (baserel->pages == 0 && baserel->tuples == 0)
    {
        baserel->pages = 10;
        baserel->tuples =
            (10 * BLCKSZ) / (baserel->reltarget->width +
                             MAXALIGN(SizeofHeapTupleHeader));
    }

    /* Estimate baserel size as best we can with local statistics. */
    set_baserel_size_estimates(root, baserel);

    /* Fill in basically-bogus cost estimates for use later. */
    estimate_path_cost_size(root, baserel, NIL, NIL, &fpinfo->costs);
	
    /*
	 * Set the name of relation in fpinfo, while we are constructing it here.
	 * It will be used to build the string describing the join relation in
	 * EXPLAIN output. We can't know whether VERBOSE option is specified or
	 * not, so always schema-qualify the foreign table name.
	 */
	fpinfo->relation_name = makeStringInfo();
	appendStringInfo(fpinfo->relation_name, "%s.%s",
         quote_identifier(get_namespace_name(get_rel_namespace(foreigntableid))),
         quote_identifier(get_rel_name(foreigntableid)));

	/* No outer and inner relations. */
	fpinfo->subqspec.make_outerrel = false;
	fpinfo->subqspec.make_innerrel = false;
	fpinfo->subqspec.lower_rels = NULL;
	
    /* Set the relation index. */
	fpinfo->relation_index = baserel->relid;
    
	/* Cache connection to the server */
	fpinfo->db = get_sqliteDbHandle(fpinfo->src.database);
}


static void
sqliteGetForeignPaths(PlannerInfo *root,
                      RelOptInfo *baserel,
                      Oid foreigntableid)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) 
                                     baserel->fdw_private;
	ForeignPath *path;
	List	   *ppi_list;
	ListCell   *lc;

	/* Create a ForeignPath node and add it as only possible path */
	add_path(baserel, (Path *)
			 create_foreignscan_path(root, baserel,
									 NULL,		/* default pathtarget */
									 fpinfo->costs.rows,
									 fpinfo->costs.startup_cost,
									 fpinfo->costs.total_cost,
									 NIL,		/* no pathkeys */
									 NULL,		/* no outer rel either */
									 NULL,		/* no extra plan */
									 NIL));		/* no fdw_private data */
	
    /* Add paths with pathkeys */
	add_paths_with_pathkeys_for_rel(root, baserel, NULL);
	
    /*
	 * Thumb through all join clauses for the rel to identify which outer
	 * relations could supply one or more safe-to-send-to-remote join clauses.
	 * We'll build a parameterized path for each such outer relation.
	 *
	 * It's convenient to manage this by representing each candidate outer
	 * relation by the ParamPathInfo node for it.  We can then use the
	 * ppi_clauses list in the ParamPathInfo node directly as a list of the
	 * interesting join clauses for that rel.  This takes care of the
	 * possibility that there are multiple safe join clauses for such a rel,
	 * and also ensures that we account for unsafe join clauses that we'll
	 * still have to enforce locally (since the parameterized-path machinery
	 * insists that we handle all movable clauses).
	 */
	ppi_list = NIL;
	foreach(lc, baserel->joininfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
		Relids		required_outer;
		ParamPathInfo *param_info;

		/* Check if clause can be moved to this rel */
		if (!join_clause_is_movable_to(rinfo, baserel))
			continue;

		/* See if it is safe to send to remote */
		if (!is_foreignExpr(root, baserel, rinfo->clause))
			continue;

		/* Calculate required outer rels for the resulting path */
		required_outer = bms_union(rinfo->clause_relids,
								   baserel->lateral_relids);
		/* We do not want the foreign rel itself listed in required_outer */
		required_outer = bms_del_member(required_outer, baserel->relid);

		/*
		 * required_outer probably can't be empty here, but if it were, we
		 * couldn't make a parameterized path.
		 */
		if (bms_is_empty(required_outer))
			continue;

		/* Get the ParamPathInfo */
		param_info = get_baserel_parampathinfo(root, baserel,
											   required_outer);
		Assert(param_info != NULL);

		/*
		 * Add it to list unless we already have it.  Testing pointer equality
		 * is OK since get_baserel_parampathinfo won't make duplicates.
		 */
		ppi_list = list_append_unique_ptr(ppi_list, param_info);
	}

	/*
	 * The above scan examined only "generic" join clauses, not those that
	 * were absorbed into EquivalenceClauses.  See if we can make anything out
	 * of EquivalenceClauses.
	 */
	if (baserel->has_eclass_joins)
	{
		/*
		 * We repeatedly scan the eclass list looking for column references
		 * (or expressions) belonging to the foreign rel.  Each time we find
		 * one, we generate a list of equivalence joinclauses for it, and then
		 * see if any are safe to send to the remote.  Repeat till there are
		 * no more candidate EC members.
		 */
		ec_member_foreign_arg arg;

		arg.already_used = NIL;
		for (;;)
		{
			List	   *clauses;

			/* Make clauses, skipping any that join to lateral_referencers */
			arg.current = NULL;
			clauses = generate_implied_equalities_for_column(root,
															 baserel,
												   ec_member_matches_foreign,
															 (void *) &arg,
											   baserel->lateral_referencers);

			/* Done if there are no more expressions in the foreign rel */
			if (arg.current == NULL)
			{
				Assert(clauses == NIL);
				break;
			}

			/* Scan the extracted join clauses */
			foreach(lc, clauses)
			{
				RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
				Relids		required_outer;
				ParamPathInfo *param_info;

				/* Check if clause can be moved to this rel */
				if (!join_clause_is_movable_to(rinfo, baserel))
					continue;

				/* See if it is safe to send to remote */
				if (!is_foreignExpr(root, baserel, rinfo->clause))
					continue;

				/* Calculate required outer rels for the resulting path */
				required_outer = bms_union(rinfo->clause_relids,
										   baserel->lateral_relids);
				required_outer = bms_del_member(required_outer, baserel->relid);
				if (bms_is_empty(required_outer))
					continue;

				/* Get the ParamPathInfo */
				param_info = get_baserel_parampathinfo(root, baserel,
													   required_outer);
				Assert(param_info != NULL);

				/* Add it to list unless we already have it */
				ppi_list = list_append_unique_ptr(ppi_list, param_info);
			}

			/* Try again, now ignoring the expression we found this time */
			arg.already_used = lappend(arg.already_used, arg.current);
		}
	}

	/*
	 * Now build a path for each useful outer relation.
	 */
	foreach(lc, ppi_list)
	{
		ParamPathInfo *param_info = (ParamPathInfo *) lfirst(lc);
        SqliteRelationCosts est;

		/* Get a cost estimate from the remote */
		estimate_path_cost_size(root, baserel,
								param_info->ppi_clauses, NIL, &est);

		/*
		 * ppi_rows currently won't get looked at by anything, but still we
		 * may as well ensure that it matches our idea of the rowcount.
		 */
		param_info->ppi_rows = est.rows;

		/* Make the path */
		path = create_foreignscan_path(root, baserel,
									   NULL,	/* default pathtarget */
									   est.rows,
									   est.startup_cost,
									   est.total_cost,
									   NIL,		/* no pathkeys */
									   param_info->ppi_req_outer,
									   NULL,
									   NIL);	/* no fdw_private list */
		add_path(baserel, (Path *) path);
	}
}

    
static ForeignScan *
get_foreignPlanSimple__(PlannerInfo *root,
					    RelOptInfo *baserel,
					    Oid foreigntableid,
					    ForeignPath *best_path,
					    List *tlist,
					    List *scan_clauses,
					    Plan *outer_plan)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) 
                                     baserel->fdw_private;
	List        *fdw_private;
	List        *local_exprs = NULL;
	List        *remote_exprs = NULL;
	List        *params_list = NULL;
	List        *remote_conds = NIL;
	StringInfoData sql;
	List           *retrieved_attrs;
	ListCell       *lc;

    /*
	 * Separate the scan_clauses into those that can be executed remotely and
	 * those that can't.  baserestrictinfo clauses that were previously
	 * determined to be safe or unsafe by classifyConditions are shown in
	 * fpinfo->remote_conds and fpinfo->local_conds.  Anything else in the
	 * scan_clauses list will be a join clause, which we have to check for
	 * remote-safety.
	 *
	 * Note: the join clauses we see here should be the exact same ones
	 * previously examined by postgresGetForeignPaths.  Possibly it'd be worth
	 * passing forward the classification work done then, rather than
	 * repeating it here.
	 *
	 * This code must match "extract_actual_clauses(scan_clauses, false)"
	 * except for the additional decision about remote versus local execution.
	 * Note however that we only strip the RestrictInfo nodes from the
	 * local_exprs list, since appendWhereClause expects a list of
	 * RestrictInfos.
	 */
	foreach(lc, scan_clauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		Assert(IsA(rinfo, RestrictInfo));

		/* Ignore any pseudoconstants, they're dealt with elsewhere */
		if (rinfo->pseudoconstant)
			continue;

		if ( list_member_ptr(fpinfo->remote_conds, rinfo) ||
             is_foreignExpr(root, baserel, rinfo->clause) )
		{
			remote_conds = lappend(remote_conds, rinfo);
			remote_exprs = lappend(remote_exprs, rinfo->clause);
		}
        else
			local_exprs = lappend(local_exprs, rinfo->clause);
	}
	
    /* Build the query */
	initStringInfo(&sql);
    deparse_selectStmt(&sql, root, baserel, fpinfo->attrs_used, 
                          fpinfo->src.table, &retrieved_attrs);

	if (remote_conds)
		append_whereClause(&sql, root, baserel, remote_conds,
						           true, &params_list);
	
    if (baserel->relid == root->parse->resultRelation &&
		(root->parse->commandType == CMD_UPDATE ||
		root->parse->commandType == CMD_DELETE))
			/* Relation is UPDATE/DELETE target, so use FOR UPDATE */
			appendStringInfoString(&sql, " FOR UPDATE");
	
    /*   The sql query and the attributes are salted away
     *   Will be used later in BeginForeignScan
     */
	fdw_private = list_make3(makeString(sql.data), retrieved_attrs, fpinfo);

	/*
	 * Create the ForeignScan node from target list, local filtering
	 * expressions, remote parameter expressions, and FDW private information.
	 *
	 * Note that the remote parameter expressions are stored in the fdw_exprs
	 * field of the finished plan node; we can't keep them in private state
	 * because then they wouldn't be subject to later planner processing.
	 */
	return make_foreignscan(tlist,
	                        local_exprs,
	                        baserel->relid,
	                        params_list,
	                        fdw_private,
	                        NIL,
	                        remote_exprs,
	                        outer_plan
	                       );
}


/*
 * Build the targetlist for given relation to be deparsed as SELECT clause.
 *
 * The output targetlist contains the columns that need to be fetched from the
 * foreign server for the given relation.  If foreignrel is an upper relation,
 * then the output targetlist can also contain expressions to be evaluated on
 * foreign server.
 */
static List *
build_tlist_to_deparse(RelOptInfo *foreignrel)
{
	List	   *tlist = NIL;
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) 
                                     foreignrel->fdw_private;
	ListCell   *lc;

	/*
	 * For an upper relation, we have already built the target list while
	 * checking shippability, so just return that.
	 */
	if (IS_UPPER_REL(foreignrel))
		return fpinfo->grouped_tlist;

	/*
	 * We require columns specified in foreignrel->reltarget->exprs and those
	 * required for evaluating the local conditions.
	 */
	tlist = add_to_flat_tlist(tlist,
					   pull_var_clause((Node *) foreignrel->reltarget->exprs,
									   PVC_RECURSE_PLACEHOLDERS));
	foreach(lc, fpinfo->local_conds)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);

		tlist = add_to_flat_tlist(tlist,
								  pull_var_clause((Node *) rinfo->clause,
												  PVC_RECURSE_PLACEHOLDERS));
	}

	return tlist;
}

    
static ForeignScan *
get_foreignPlanJoinUpper__(PlannerInfo *root,
					       RelOptInfo *foreignrel,
					       Oid foreigntableid,
					       ForeignPath *best_path,
					       List *tlist,
					       List *scan_clauses,
					       Plan *outer_plan)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) 
                                     foreignrel->fdw_private;
	List        *local_exprs = NULL;
	List        *remote_exprs = NULL;
	List	   *fdw_scan_tlist = NULL;
    /*
     * For a join rel, baserestrictinfo is NIL and we are not considering
     * parameterization right now, so there should be no scan_clauses for
     * a joinrel or an upper rel either.
     */
    Assert(!scan_clauses);

    /*
     * Instead we get the conditions to apply from the fdw_private
     * structure.
     */
    remote_exprs = extract_actual_clauses(fpinfo->remote_conds, false);
    local_exprs = extract_actual_clauses(fpinfo->local_conds, false);

    /*
     * We leave fdw_recheck_quals empty in this case, since we never need
     * to apply EPQ recheck clauses.  In the case of a joinrel, EPQ
     * recheck is handled elsewhere --- see postgresGetForeignJoinPaths().
     * If we're planning an upperrel (ie, remote grouping or aggregation)
     * then there's no EPQ to do because SELECT FOR UPDATE wouldn't be
     * allowed, and indeed we *can't* put the remote clauses into
     * fdw_recheck_quals because the unaggregated Vars won't be available
     * locally.
     */

    /* Build the list of columns to be fetched from the foreign server. */
    fdw_scan_tlist = build_tlist_to_deparse(foreignrel);

    /*
     * Ensure that the outer plan produces a tuple whose descriptor
     * matches our scan tuple slot. This is safe because all scans and
     * joins support projection, so we never need to insert a Result node.
     * Also, remove the local conditions from outer plan's quals, lest
     * they will be evaluated twice, once by the local plan and once by
     * the scan.
     */
    if (outer_plan)
    {
        ListCell   *lc;

        /*
         * Right now, we only consider grouping and aggregation beyond
         * joins. Queries involving aggregates or grouping do not require
         * EPQ mechanism, hence should not have an outer plan here.
         */
        Assert(!IS_UPPER_REL(foreignrel));

        outer_plan->targetlist = fdw_scan_tlist;

        foreach(lc, local_exprs)
        {
            Join	   *join_plan = (Join *) outer_plan;
            Node	   *qual = lfirst(lc);

            outer_plan->qual = list_delete(outer_plan->qual, qual);

            /*
             * For an inner join the local conditions of foreign scan plan
             * can be part of the joinquals as well.
             */
            if (join_plan->jointype == JOIN_INNER)
                join_plan->joinqual = list_delete(join_plan->joinqual,
                                                  qual);
        }
    }
	return make_foreignscan(tlist,
	                        local_exprs,
	                        0,
	                        params_list,
	                        fdw_private,
	                        fdw_scan_tlist,
	                        NULL,
	                        outer_plan
	                       );
}


static ForeignScan *
sqliteGetForeignPlan(PlannerInfo *root,
					 RelOptInfo *baserel,
					 Oid foreigntableoid,
					 ForeignPath *best_path,
					 List *tlist,
					 List *scan_clauses,
					 Plan *outer_plan)
{
	if (IS_SIMPLE_REL(baserel))
        return get_foreignPlanSimple__(root, baserel, foreigntableoid,
                                       best_path, tlist, scan_clauses,
                                       outer_plan);
    else
        return get_foreignPlanJoinUpper__(root, baserel, foreigntableoid,
                                          best_path, tlist, scan_clauses,
                                          outer_plan);
}


static void
sqliteBeginForeignScan(ForeignScanState *node,
                       int eflags)
{
	/*
	 * Begin executing a foreign scan. This is called during executor startup.
	 * It should perform any initialization needed before the scan can start,
	 * but not start executing the actual scan (that should be done upon the
	 * first call to IterateForeignScan). The ForeignScanState node has
	 * already been created, but its fdw_state field is still NULL.
	 * Information about the table to scan is accessible through the
	 * ForeignScanState node (in particular, from the underlying ForeignScan
	 * plan node, which contains any FDW-private information provided by
	 * GetForeignPlan). eflags contains flag bits describing the executor's
	 * operating mode for this plan node.
	 *
	 * Note that when (eflags & EXEC_FLAG_EXPLAIN_ONLY) is true, this function
	 * should not perform any externally-visible actions; it should only do
	 * the minimum required to make the node state valid for
	 * ExplainForeignScan and EndForeignScan.
	 *
	 */
	SqliteFdwExecutionState  *festate;
	ForeignScan *fsplan = (ForeignScan *) node->ss.ps.plan;
    SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *)
                                    list_nth(fsplan->fdw_private, 2);

	// elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);
	
    /*
	 * We'll save private state in node->fdw_state.
	 */
	festate = (SqliteFdwExecutionState *) 
                    palloc0(sizeof(SqliteFdwExecutionState));
	node->fdw_state = (void *) festate;

    festate->db = fpinfo->db;
    festate->query = strVal(list_nth(fsplan->fdw_private, 0));
    festate->retrieved_attrs = list_nth(fsplan->fdw_private, 1);
    PG_TRY();
    {
        festate->stmt = prepare_sqliteQuery(festate->db, festate->query, NULL);
        if ( list_length(fsplan->fdw_exprs) > 0 )
            sqlite_bind_param_values(festate, fsplan->fdw_exprs, node);
    }
    PG_CATCH();
    {
        cleanup_(festate);
		PG_RE_THROW();
    }
    PG_END_TRY();
}


static TupleTableSlot *
sqliteIterateForeignScan(ForeignScanState *node)
{
	/*
	 * Fetch one row from the foreign source, returning it in a tuple table
	 * slot (the node's ScanTupleSlot should be used for this purpose). Return
	 * NULL if no more rows are available. The tuple table slot infrastructure
	 * allows either a physical or virtual tuple to be returned; in most cases
	 * the latter choice is preferable from a performance standpoint. Note
	 * that this is called in a short-lived memory context that will be reset
	 * between invocations. Create a memory context in BeginForeignScan if you
	 * need longer-lived storage, or use the es_query_cxt of the node's
	 * EState.
	 *
	 * The rows returned must match the column signature of the foreign table
	 * being scanned. If you choose to optimize away fetching columns that are
	 * not needed, you should insert nulls in those column positions.
	 *
	 * Note that PostgreSQL's executor doesn't care whether the rows returned
	 * violate any NOT NULL constraints that were defined on the foreign table
	 * columns — but the planner does care, and may optimize queries
	 * incorrectly if NULL values are present in a column declared not to
	 * contain them. If a NULL value is encountered when the user has declared
	 * that none should be present, it may be appropriate to raise an error
	 * (just as you would need to do in the case of a data type mismatch).
	 */
	SqliteFdwExecutionState   *festate = (SqliteFdwExecutionState *) 
                                          node->fdw_state;
	TupleTableSlot  *tupleSlot = node->ss.ss_ScanTupleSlot;
	TupleDesc       tupleDescriptor = tupleSlot->tts_tupleDescriptor;
	int             attid = 0;
	ListCell        *lc = NULL;
	int             rc = 0;

	memset (tupleSlot->tts_values, 0, sizeof(Datum) * tupleDescriptor->natts);
	memset (tupleSlot->tts_isnull, true, sizeof(bool) * tupleDescriptor->natts);
	attid = 0;
	ExecClearTuple(tupleSlot);
    
    rc = sqlite3_step(festate->stmt);
	if (rc == SQLITE_ROW)
	{
		foreach(lc, festate->retrieved_attrs)
		{
			int attnum = lfirst_int(lc) - 1;
			Oid pgtype = tupleDescriptor->attrs[attnum]->atttypid;
            tupleSlot->tts_values[attnum] = 
                    make_datum(festate->stmt, attid, pgtype, 
                               tupleSlot->tts_isnull + attnum);
			attid++;
		}
		ExecStoreVirtualTuple(tupleSlot);
	}
    return tupleSlot;
}


static void
sqliteReScanForeignScan(ForeignScanState *node)
{
	/*
	 * Restart the scan from the beginning. Note that any parameters the scan
	 * depends on may have changed value, so the new scan does not necessarily
	 * return exactly the same rows.
	 */

	// elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);
}


static void
sqliteEndForeignScan(ForeignScanState *node)
{
	cleanup_((SqliteFdwExecutionState *) node->fdw_state);
}


static void
sqliteAddForeignUpdateTargets(Query *parsetree,
                              RangeTblEntry *target_rte,
                              Relation target_relation)
{
	/*
	 * UPDATE and DELETE operations are performed against rows previously
	 * fetched by the table-scanning functions. The FDW may need extra
	 * information, such as a row ID or the values of primary-key columns, to
	 * ensure that it can identify the exact row to update or delete. To
	 * support that, this function can add extra hidden, or "junk", target
	 * columns to the list of columns that are to be retrieved from the
	 * foreign table during an UPDATE or DELETE.
	 *
	 * To do that, add TargetEntry items to parsetree->targetList, containing
	 * expressions for the extra values to be fetched. Each such entry must be
	 * marked resjunk = true, and must have a distinct resname that will
	 * identify it at execution time. Avoid using names matching ctidN or
	 * wholerowN, as the core system can generate junk columns of these names.
	 *
	 * This function is called in the rewriter, not the planner, so the
	 * information available is a bit different from that available to the
	 * planning routines. parsetree is the parse tree for the UPDATE or DELETE
	 * command, while target_rte and target_relation describe the target
	 * foreign table.
	 *
	 * If the AddForeignUpdateTargets pointer is set to NULL, no extra target
	 * expressions are added. (This will make it impossible to implement
	 * DELETE operations, though UPDATE may still be feasible if the FDW
	 * relies on an unchanging primary key to identify rows.)
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);
}


static List *
sqlitePlanForeignModify(PlannerInfo *root,
						   ModifyTable *plan,
						   Index resultRelation,
						   int subplan_index)
{
	/*
	 * Perform any additional planning actions needed for an insert, update,
	 * or delete on a foreign table. This function generates the FDW-private
	 * information that will be attached to the ModifyTable plan node that
	 * performs the update action. This private information must have the form
	 * of a List, and will be delivered to BeginForeignModify during the
	 * execution stage.
	 *
	 * root is the planner's global information about the query. plan is the
	 * ModifyTable plan node, which is complete except for the fdwPrivLists
	 * field. resultRelation identifies the target foreign table by its
	 * rangetable index. subplan_index identifies which target of the
	 * ModifyTable plan node this is, counting from zero; use this if you want
	 * to index into plan->plans or other substructure of the plan node.
	 *
	 * If the PlanForeignModify pointer is set to NULL, no additional
	 * plan-time actions are taken, and the fdw_private list delivered to
	 * BeginForeignModify will be NIL.
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);
	return NULL;
}


static void
sqliteBeginForeignModify(ModifyTableState *mtstate,
							ResultRelInfo *rinfo,
							List *fdw_private,
							int subplan_index,
							int eflags)
{
	/*
	 * Begin executing a foreign table modification operation. This routine is
	 * called during executor startup. It should perform any initialization
	 * needed prior to the actual table modifications. Subsequently,
	 * ExecForeignInsert, ExecForeignUpdate or ExecForeignDelete will be
	 * called for each tuple to be inserted, updated, or deleted.
	 *
	 * mtstate is the overall state of the ModifyTable plan node being
	 * executed; global data about the plan and execution state is available
	 * via this structure. rinfo is the ResultRelInfo struct describing the
	 * target foreign table. (The ri_FdwState field of ResultRelInfo is
	 * available for the FDW to store any private state it needs for this
	 * operation.) fdw_private contains the private data generated by
	 * PlanForeignModify, if any. subplan_index identifies which target of the
	 * ModifyTable plan node this is. eflags contains flag bits describing the
	 * executor's operating mode for this plan node.
	 *
	 * Note that when (eflags & EXEC_FLAG_EXPLAIN_ONLY) is true, this function
	 * should not perform any externally-visible actions; it should only do
	 * the minimum required to make the node state valid for
	 * ExplainForeignModify and EndForeignModify.
	 *
	 * If the BeginForeignModify pointer is set to NULL, no action is taken
	 * during executor startup.
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);
}


static TupleTableSlot *
sqliteExecForeignInsert(EState *estate,
						   ResultRelInfo *rinfo,
						   TupleTableSlot *slot,
						   TupleTableSlot *planSlot)
{
	/*
	 * Insert one tuple into the foreign table. estate is global execution
	 * state for the query. rinfo is the ResultRelInfo struct describing the
	 * target foreign table. slot contains the tuple to be inserted; it will
	 * match the rowtype definition of the foreign table. planSlot contains
	 * the tuple that was generated by the ModifyTable plan node's subplan; it
	 * differs from slot in possibly containing additional "junk" columns.
	 * (The planSlot is typically of little interest for INSERT cases, but is
	 * provided for completeness.)
	 *
	 * The return value is either a slot containing the data that was actually
	 * inserted (this might differ from the data supplied, for example as a
	 * result of trigger actions), or NULL if no row was actually inserted
	 * (again, typically as a result of triggers). The passed-in slot can be
	 * re-used for this purpose.
	 *
	 * The data in the returned slot is used only if the INSERT query has a
	 * RETURNING clause. Hence, the FDW could choose to optimize away
	 * returning some or all columns depending on the contents of the
	 * RETURNING clause. However, some slot must be returned to indicate
	 * success, or the query's reported rowcount will be wrong.
	 *
	 * If the ExecForeignInsert pointer is set to NULL, attempts to insert
	 * into the foreign table will fail with an error message.
	 *
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);

	return slot;
}


static TupleTableSlot *
sqliteExecForeignUpdate(EState *estate,
						   ResultRelInfo *rinfo,
						   TupleTableSlot *slot,
						   TupleTableSlot *planSlot)
{
	/*
	 * Update one tuple in the foreign table. estate is global execution state
	 * for the query. rinfo is the ResultRelInfo struct describing the target
	 * foreign table. slot contains the new data for the tuple; it will match
	 * the rowtype definition of the foreign table. planSlot contains the
	 * tuple that was generated by the ModifyTable plan node's subplan; it
	 * differs from slot in possibly containing additional "junk" columns. In
	 * particular, any junk columns that were requested by
	 * AddForeignUpdateTargets will be available from this slot.
	 *
	 * The return value is either a slot containing the row as it was actually
	 * updated (this might differ from the data supplied, for example as a
	 * result of trigger actions), or NULL if no row was actually updated
	 * (again, typically as a result of triggers). The passed-in slot can be
	 * re-used for this purpose.
	 *
	 * The data in the returned slot is used only if the UPDATE query has a
	 * RETURNING clause. Hence, the FDW could choose to optimize away
	 * returning some or all columns depending on the contents of the
	 * RETURNING clause. However, some slot must be returned to indicate
	 * success, or the query's reported rowcount will be wrong.
	 *
	 * If the ExecForeignUpdate pointer is set to NULL, attempts to update the
	 * foreign table will fail with an error message.
	 *
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);
	return slot;
}


static TupleTableSlot *
sqliteExecForeignDelete(EState *estate,
						   ResultRelInfo *rinfo,
						   TupleTableSlot *slot,
						   TupleTableSlot *planSlot)
{
	/*
	 * Delete one tuple from the foreign table. estate is global execution
	 * state for the query. rinfo is the ResultRelInfo struct describing the
	 * target foreign table. slot contains nothing useful upon call, but can
	 * be used to hold the returned tuple. planSlot contains the tuple that
	 * was generated by the ModifyTable plan node's subplan; in particular, it
	 * will carry any junk columns that were requested by
	 * AddForeignUpdateTargets. The junk column(s) must be used to identify
	 * the tuple to be deleted.
	 *
	 * The return value is either a slot containing the row that was deleted,
	 * or NULL if no row was deleted (typically as a result of triggers). The
	 * passed-in slot can be used to hold the tuple to be returned.
	 *
	 * The data in the returned slot is used only if the DELETE query has a
	 * RETURNING clause. Hence, the FDW could choose to optimize away
	 * returning some or all columns depending on the contents of the
	 * RETURNING clause. However, some slot must be returned to indicate
	 * success, or the query's reported rowcount will be wrong.
	 *
	 * If the ExecForeignDelete pointer is set to NULL, attempts to delete
	 * from the foreign table will fail with an error message.
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);

	return slot;
}


static void
sqliteEndForeignModify(EState *estate,
						  ResultRelInfo *rinfo)
{
	/*
	 * End the table update and release resources. It is normally not
	 * important to release palloc'd memory, but for example open files and
	 * connections to remote servers should be cleaned up.
	 *
	 * If the EndForeignModify pointer is set to NULL, no action is taken
	 * during executor shutdown.
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);

}


static void
sqliteExplainForeignScan(ForeignScanState *node,
							struct ExplainState *es)
{
	/*
	 * Print additional EXPLAIN output for a foreign table scan. This function
	 * can call ExplainPropertyText and related functions to add fields to the
	 * EXPLAIN output. The flag fields in es can be used to determine what to
	 * print, and the state of the ForeignScanState node can be inspected to
	 * provide run-time statistics in the EXPLAIN ANALYZE case.
	 *
	 * If the ExplainForeignScan pointer is set to NULL, no additional
	 * information is printed during EXPLAIN.
	 */
	sqlite3					   *db;
	sqlite3_stmt			   *stmt;
	char					   *query;
	size_t						len;
	const char				   *pzTail;
	SqliteFdwExecutionState	   *festate = (SqliteFdwExecutionState *) 
                                          node->fdw_state;
    SqliteTableSource          opt;

	// elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);

	/* Show the query (only if VERBOSE) */
	if (es->verbose)
	{
		/* show query */
		ExplainPropertyText("sqlite query", festate->query, es);
	}

	/* Fetch options  */
	opt = get_tableSource(
            RelationGetRelid(node->ss.ss_currentRelation));

	/* Connect to the server */
	db = get_sqliteDbHandle(opt.database);

	/* Build the query */
	len = strlen(festate->query) + 20;
	query = (char *)palloc(len);
	snprintf(query, len, "EXPLAIN QUERY PLAN %s", festate->query);

    /* Execute the query */
	stmt= prepare_sqliteQuery(db, query, &pzTail);

	/* get the next record, if any, and fill in the slot */
	while (sqlite3_step(stmt) == SQLITE_ROW)
	{
		/*
		 * I don't keep the three first columns;
		   it could be a good idea to add that later
		 */
		/*
		 * for (x = 0; x < sqlite3_column_count(festate->stmt); x++)
		 * {
		 */
			ExplainPropertyText("sqlite plan", (char*)sqlite3_column_text(stmt, 3), es);
		/* } */
	}

	/* Free the query stmts */
	sqlite3_finalize(stmt);

	/* Close temporary connection */
	sqlite3_close(db);
}


static void
sqliteExplainForeignModify(ModifyTableState *mtstate,
							  ResultRelInfo *rinfo,
							  List *fdw_private,
							  int subplan_index,
							  struct ExplainState *es)
{
	/*
	 * Print additional EXPLAIN output for a foreign table update. This
	 * function can call ExplainPropertyText and related functions to add
	 * fields to the EXPLAIN output. The flag fields in es can be used to
	 * determine what to print, and the state of the ModifyTableState node can
	 * be inspected to provide run-time statistics in the EXPLAIN ANALYZE
	 * case. The first four arguments are the same as for BeginForeignModify.
	 *
	 * If the ExplainForeignModify pointer is set to NULL, no additional
	 * information is printed during EXPLAIN.
	 */

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);
}


static bool
sqliteAnalyzeForeignTable(Relation relation,
                          AcquireSampleRowsFunc *func,
                          BlockNumber *totalpages)
{
	/* ----
	 * This function is called when ANALYZE is executed on a foreign table. If
	 * the FDW can collect statistics for this foreign table, it should return
	 * true, and provide a pointer to a function that will collect sample rows
	 * from the table in func, plus the estimated size of the table in pages
	 * in totalpages. Otherwise, return false.
	 *
	 * If the FDW does not support collecting statistics for any tables, the
	 * AnalyzeForeignTable pointer can be set to NULL.
	 *
	 * If provided, the sample collection function must have the signature:
	 *
	 *	  int
	 *	  AcquireSampleRowsFunc (Relation relation, int elevel,
	 *							 HeapTuple *rows, int targrows,
	 *							 double *totalrows,
	 *							 double *totaldeadrows);
	 *
	 * A random sample of up to targrows rows should be collected from the
	 * table and stored into the caller-provided rows array. The actual number
	 * of rows collected must be returned. In addition, store estimates of the
	 * total numbers of live and dead rows in the table into the output
	 * parameters totalrows and totaldeadrows. (Set totaldeadrows to zero if
	 * the FDW does not have any concept of dead rows.)
	 * ----
	 */

	elog(SQLITE_FDW_LOG_LEVEL,"entering function %s",__func__);

	return false;
}

static List *
sqliteImportForeignSchema(ImportForeignSchemaStmt *stmt,
                          Oid serverOid)
{
	sqlite3		   *volatile db = NULL;
	sqlite3_stmt   *volatile tbls = NULL;
	char		   *filename = NULL;
	List		   *commands = NIL;
    ListCell       *lc;
    SqliteTableImportOptions importOptions = 
            get_sqliteTableImportOptions(stmt);

	elog(SQLITE_FDW_LOG_LEVEL, "entering function %s", __func__);

	/*
	 * The only legit sqlite schema are temp and main, 
     * We want only "main"
	 */
	if ( strcmp(stmt->remote_schema, "main") != 0)
	{
		ereport(ERROR,
			(errcode(ERRCODE_FDW_SCHEMA_NOT_FOUND),
			errmsg("Foreign schema \"%s\" is invalid", 
                    stmt->remote_schema)
			));
	}

	/* get the db filename */
	foreach(lc, GetForeignServer(serverOid)->options)
	{
		DefElem *def = (DefElem *) lfirst(lc);
		if (strcmp(def->defname, "database") == 0)
		{
			filename = defGetString(def);
			break;
		}
	}

    if ( !filename )
		ereport(ERROR,
			(errcode(ERRCODE_FDW_ERROR),
			errmsg("Need database option for server %s", 
                    stmt->server_name)
			));

	/* Connect to the server */
	db = get_sqliteDbHandle(filename);

	PG_TRY();
	{
		/* You want all tables, except system tables */
        char tablenames_q[256] = "select name from sqlite_master "
                                  "where type = 'table' "
                                  "and name not like 'sqlite_%%'";
		
        /* Iterate to all matching tables, and get their definition */
		tbls = prepare_sqliteQuery(db, tablenames_q, NULL);
		while (sqlite3_step(tbls) == SQLITE_ROW)
		{
            char *tablename = (char *) sqlite3_column_text(tbls, 0);
            char *cftsql = get_foreignTableCreationSql(
                    stmt, db, tablename, importOptions);
            if ( cftsql )
                commands = lappend(commands, cftsql);
		}
	}
	PG_CATCH();
	{
		if (tbls)
			sqlite3_finalize(tbls);
        sqlite3_close(db);
        pfree(filename);

		PG_RE_THROW();
	}
	PG_END_TRY();

	sqlite3_finalize(tbls);
	sqlite3_close(db);
    pfree(filename);

	return commands;
}


static bool
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
sqlite_bind_param_values(SqliteFdwExecutionState *festate, List *fdw_exprs, 
                         ForeignScanState *node)
{
	ListCell   *lc;
    Oid  *param_types;
	List *param_exprs;
    int i;
    MemoryContext oldcontext;

    param_exprs = (List *) ExecInitExpr((Expr *) fdw_exprs, (PlanState *)node);
    param_types = (Oid *) palloc0(sizeof(Oid) * list_length(fdw_exprs));
    
    i = 0;
    foreach(lc, fdw_exprs)
		param_types[i++] = exprType((Node *) lfirst(lc));

    oldcontext = MemoryContextSwitchTo(
                    node->ss.ps.ps_ExprContext->ecxt_per_tuple_memory);

    i = 0;
    foreach(lc, param_exprs)
	{
		ExprState  *expr_state = (ExprState *) lfirst(lc);
		Datum		expr_value;
		bool		isNull;

		/* Evaluate the parameter expression */
		expr_value = ExecEvalExpr(expr_state, node->ss.ps.ps_ExprContext, &isNull);
        sqlite_bind_param_value(festate, i+1, param_types[i], expr_value, isNull);
        i++;
    }
    oldcontext = MemoryContextSwitchTo(oldcontext);
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


void
cleanup_(SqliteFdwExecutionState *festate)
{
    if ( festate->stmt ) {
        sqlite3_finalize(festate->stmt);
        festate->stmt = NULL;
    }
    if ( festate->db ) {
        sqlite3_close(festate->db);
        festate->stmt = NULL;
    }
}


/*
 * postgresGetForeignJoinPaths
 *		Add possible ForeignPath to joinrel, if join is safe to push down.
 */
static void
sqliteGetForeignJoinPaths(PlannerInfo *root,
                          RelOptInfo *joinrel,
                          RelOptInfo *outerrel,
                          RelOptInfo *innerrel,
                          JoinType jointype,
                          JoinPathExtraData *extra)
{
	SqliteFdwRelationInfo *fpinfo;
	ForeignPath *joinpath;
	Path	   *epq_path;		/* Path to create plan to be executed when
								 * EvalPlanQual gets triggered. */
	
    elog(SQLITE_FDW_LOG_LEVEL,"XXXXXXXX startGetForeignJoin");

	/*
	 * Skip if this join combination has been considered already.
	 */
	if (joinrel->fdw_private)
		return;

	/*
	 * Create unfinished SqliteFdwRelationInfo entry which is used to indicate
	 * that the join relation is already considered, so that we won't waste
	 * time in judging safety of join pushdown and adding the same paths again
	 * if found safe. Once we know that this join can be pushed down, we fill
	 * the entry.
	 */
	fpinfo = (SqliteFdwRelationInfo *) palloc0(sizeof(SqliteFdwRelationInfo));
	fpinfo->pushdown_safe = false;
	joinrel->fdw_private = fpinfo;
	/* attrs_used is only for base relations. */
	fpinfo->attrs_used = NULL;

	/*
	 * If there is a possibility that EvalPlanQual will be executed, we need
	 * to be able to reconstruct the row using scans of the base relations.
	 * GetExistingLocalJoinPath will find a suitable path for this purpose in
	 * the path list of the joinrel, if one exists.  We must be careful to
	 * call it before adding any ForeignPath, since the ForeignPath might
	 * dominate the only suitable local path available.  We also do it before
	 * reconstruct the row for EvalPlanQual(). Find an alternative local path
	 * calling foreign_join_ok(), since that function updates fpinfo and marks
	 * it as pushable if the join is found to be pushable.
	 */
	if (root->parse->commandType == CMD_DELETE ||
		root->parse->commandType == CMD_UPDATE ||
		root->rowMarks)
	{
		epq_path = GetExistingLocalJoinPath(joinrel);
		if (!epq_path)
		{
			elog(DEBUG3, "could not push down foreign join because "
                         "a local path suitable for EPQ checks was not found");
			return;
		}
	}
	else
		epq_path = NULL;

	if (!foreign_join_ok(root, joinrel, jointype, outerrel, innerrel, extra))
	{
		/* Free path required for EPQ if we copied one; we don't need it now */
		if (epq_path)
			pfree(epq_path);
		return;
	}
    elog(SQLITE_FDW_LOG_LEVEL,"XXXXXXXX GetForeignJoinPaths 1");

	/*
	 * Compute the selectivity and cost of the local_conds, so we don't have
	 * to do it over again for each path. The best we can do for these
	 * conditions is to estimate selectivity on the basis of local statistics.
	 * The local conditions are applied after the join has been computed on
	 * the remote side like quals in WHERE clause, so pass jointype as
	 * JOIN_INNER.
	 */
	fpinfo->costs.local_conds_sel = clauselist_selectivity(
        root,
        fpinfo->local_conds,
        0,
        JOIN_INNER,
        NULL);
	cost_qual_eval(&fpinfo->costs.local_conds_cost, fpinfo->local_conds, root);
    fpinfo->joinspec.clause_sel = clauselist_selectivity(
                root, fpinfo->joinspec.clauses,
                0, fpinfo->joinspec.type,
                extra->sjinfo);

	/* Estimate costs for bare join relation */
	estimate_path_cost_size(root, joinrel, NIL, NIL, &fpinfo->costs);
	/* Now update this information in the joinrel */
	joinrel->rows = fpinfo->costs.rows;
	joinrel->reltarget->width = fpinfo->costs.width;
    elog(SQLITE_FDW_LOG_LEVEL,"XXXXXXXX GetForeignJoinPaths 2 %f %f", 
                fpinfo->costs.startup_cost, 
                fpinfo->costs.total_cost);

	/*
	 * Create a new join path and add it to the joinrel which represents a
	 * join between foreign tables.
	 */
    // AG TODO: the total cost is hardocded here
	joinpath = create_foreignscan_path(root,
									   joinrel,
									   NULL,	/* default pathtarget */
									   joinrel->rows,
									   fpinfo->costs.startup_cost,
									   // fpinfo->costs.total_cost,
                                       1.0,
									   NIL,		/* no pathkeys */
									   NULL,	/* no required_outer */
									   epq_path,
									   NIL);	/* no fdw_private */

	/* Add generated path into joinrel by add_path(). */
	add_path(joinrel, (Path *) joinpath);

	/* Consider pathkeys for the join relation */
	add_paths_with_pathkeys_for_rel(root, joinrel, epq_path);
    
    elog(SQLITE_FDW_LOG_LEVEL,"XXXXXXXX GetForeignJoinPaths 3 %d", 
                getpid());
    raise(SIGSTOP);

	/* XXX Consider parameterized paths for the join relation */
}


/*
 * Assess whether the join between inner and outer relations can be pushed down
 * to the foreign server. As a side effect, save information we obtain in this
 * function to SqliteFdwRelationInfo passed in.
 */
static bool
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
	// fpinfo->server = fpinfo_o->server;
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
		bool		is_remote_clause = is_foreignExpr(root, joinrel,
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
 * estimate_path_cost_size
 *		Get cost and size estimates for a foreign scan on given foreign relation
 *		either a base relation or a join between foreign relations or an upper
 *		relation containing foreign relations.
 *
 * param_join_conds are the parameterization clauses with outer relations.
 * pathkeys specify the expected sort order if any for given path being costed.
 *
 * The function returns the cost and size estimates in p_row, p_width,
 * p_startup_cost and p_total_cost variables.
 */
static void
estimate_path_cost_size(PlannerInfo *root,
						RelOptInfo *foreignrel,
						List *param_join_conds,
						List *pathkeys,
                        SqliteRelationCosts * store)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) foreignrel->fdw_private;
    SqliteCostEstimates est = {0};

    /*
     * We don't support join conditions in this mode (hence, no
     * parameterized paths can be made).
     */
    Assert(param_join_conds == NIL);

    /*
     * Use rows/width estimates made by set_baserel_size_estimates() for
     * base foreign relations and set_joinrel_size_estimates() for join
     * between foreign relations.
     */
    est.rows = foreignrel->rows;
    est.width = foreignrel->reltarget->width;

    /* Back into an estimate of the number of retrieved rows. */
    est.retrieved_rows = clamp_row_est(est.rows / fpinfo->costs.local_conds_sel);

    /*
     * We will come here again and again with different set of pathkeys
     * that caller wants to cost. We don't need to calculate the cost of
     * bare scan each time. Instead, use the costs if we have cached them
     * already.
     */
    if (fpinfo->costs.rel_startup_cost > 0 && fpinfo->costs.rel_total_cost > 0)
    {
        est.startup_cost = fpinfo->costs.rel_startup_cost;
        est.run_cost = fpinfo->costs.rel_total_cost - est.startup_cost;
    }
    else if (IS_JOIN_REL(foreignrel))
    {
        estimate_join_rel_cost(root, foreignrel, &est);
    }
    else if (IS_UPPER_REL(foreignrel))
    {
        estimate_upper_rel_cost(root, foreignrel, &est);
    }
    else
    {
        estimate_base_rel_cost(root, foreignrel, &est);
    }

    /*
     * Without remote estimates, we have no real way to estimate the cost
     * of generating sorted output.  It could be free if the query plan
     * the remote side would have chosen generates properly-sorted output
     * anyway, but in most cases it will cost something.  Estimate a value
     * high enough that we won't pick the sorted path when the ordering
     * isn't locally useful, but low enough that we'll err on the side of
     * pushing down the ORDER BY clause when it's useful to do so.
     */
    if (pathkeys != NIL)
    {
        est.startup_cost *= DEFAULT_FDW_SORT_MULTIPLIER;
        est.run_cost *= DEFAULT_FDW_SORT_MULTIPLIER;
    }

	/*
	 * Cache the costs for scans without any pathkeys or parameterization
	 * before adding the costs for transferring data from the foreign server.
	 * These costs are useful for costing the join between this relation and
	 * another foreign relation or to calculate the costs of paths with
	 * pathkeys for this relation, when the costs can not be obtained from the
	 * foreign server. This function will be called at least once for every
	 * foreign relation without pathkeys and parameterization.
	 */
	if (pathkeys == NIL && param_join_conds == NIL)
	{
		fpinfo->costs.rel_startup_cost = est.startup_cost;
		fpinfo->costs.rel_total_cost = est.startup_cost + est.run_cost;
	}
	
    // Connection overhead
    est.startup_cost += fpinfo->costs.fdw_startup_cost;

	/* Return results.
     * Add all costs and account for network transfer and local manipulation
     * of the rows
	 * (fdw_tuple_cost per retrieved row), and local manipulation of the data
	 * (cpu_tuple_cost per retrieved row).
	*/
    store->rows = est.rows;
    store->width = est.width;
    store->startup_cost = est.startup_cost;
    store->total_cost = est.startup_cost + est.run_cost + 
                        (fpinfo->costs.fdw_tuple_cost + cpu_tuple_cost) *
                        est.retrieved_rows;
}


static void
estimate_join_rel_cost(PlannerInfo *root,
					   RelOptInfo *foreignrel,
                       SqliteCostEstimates * est)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) foreignrel->fdw_private;
    SqliteFdwRelationInfo *fpinfo_i;
    SqliteFdwRelationInfo *fpinfo_o;
    QualCost	join_cost;
    QualCost	remote_conds_cost;
    double		nrows;

    /* For join we expect inner and outer relations set */
    Assert(fpinfo->joinspec.innerrel && fpinfo->joinspec.outerrel);

    fpinfo_i = (SqliteFdwRelationInfo *) fpinfo->joinspec.innerrel->fdw_private;
    fpinfo_o = (SqliteFdwRelationInfo *) fpinfo->joinspec.outerrel->fdw_private;

    /* Estimate of number of rows in cross product */
    nrows = fpinfo_i->costs.rows * fpinfo_o->costs.rows;
    /* Clamp retrieved rows estimate to at most size of cross product */
    est->retrieved_rows = Min(est->retrieved_rows, nrows);

    /*
     * The cost of foreign join is estimated as cost of generating
     * rows for the joining relations + cost for applying quals on the
     * rows.
     */

    /*
     * Calculate the cost of clauses pushed down to the foreign server
     */
    cost_qual_eval(&remote_conds_cost, fpinfo->remote_conds, root);
    /* Calculate the cost of applying join clauses */
    cost_qual_eval(&join_cost, fpinfo->joinspec.clauses, root);

    /*
     * Startup cost includes startup cost of joining relations and the
     * startup cost for join and other clauses. We do not include the
     * startup cost specific to join strategy (e.g. setting up hash
     * tables) since we do not know what strategy the foreign server
     * is going to use.
     */
    est->startup_cost = fpinfo_i->costs.rel_startup_cost + fpinfo_o->costs.rel_startup_cost;
    est->startup_cost += join_cost.startup;
    est->startup_cost += remote_conds_cost.startup;
    est->startup_cost += fpinfo->costs.local_conds_cost.startup;

    /*
     * Run time cost includes:
     *
     * 1. Run time cost (total_cost - startup_cost) of relations being
     * joined
     *
     * 2. Run time cost of applying join clauses on the cross product
     * of the joining relations.
     *
     * 3. Run time cost of applying pushed down other clauses on the
     * result of join
     *
     * 4. Run time cost of applying nonpushable other clauses locally
     * on the result fetched from the foreign server.
     */
    est->run_cost = fpinfo_i->costs.rel_total_cost - fpinfo_i->costs.rel_startup_cost;
    est->run_cost += fpinfo_o->costs.rel_total_cost - fpinfo_o->costs.rel_startup_cost;
    est->run_cost += nrows * join_cost.per_tuple;
    nrows = clamp_row_est(nrows * fpinfo->joinspec.clause_sel);
    est->run_cost += nrows * remote_conds_cost.per_tuple;
    est->run_cost += fpinfo->costs.local_conds_cost.per_tuple * est->retrieved_rows;
}

    
static void
estimate_upper_rel_cost(PlannerInfo *root,
					    RelOptInfo *foreignrel,
                        SqliteCostEstimates * est)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) foreignrel->fdw_private;
    SqliteFdwRelationInfo *ofpinfo;
    PathTarget *ptarget = root->upper_targets[UPPERREL_GROUP_AGG];
    AggClauseCosts aggcosts;
    double		input_rows;
    int			numGroupCols;
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

    ofpinfo = (SqliteFdwRelationInfo *) fpinfo->joinspec.outerrel->fdw_private;

    /* Get rows and width from input rel */
    input_rows = ofpinfo->costs.rows;
    // width = ofpinfo->cost.width;

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
    numGroupCols = list_length(root->parse->groupClause);
    numGroups = estimate_num_groups(root,
                    get_sortgrouplist_exprs(root->parse->groupClause,
                                            fpinfo->grouped_tlist),
                                    input_rows, NULL);

    /*
     * Number of rows expected from foreign server will be same as
     * that of number of groups.
     */
    est->rows = est->retrieved_rows = numGroups;

    /*-----
     * Startup cost includes:
     *	  1. Startup cost for underneath input * relation
     *	  2. Cost of performing aggregation, per cost_agg()
     *	  3. Startup cost for PathTarget eval
     *-----
     */
    est->startup_cost = ofpinfo->costs.rel_startup_cost;
    est->startup_cost += aggcosts.transCost.startup;
    est->startup_cost += aggcosts.transCost.per_tuple * input_rows;
    est->startup_cost += (cpu_operator_cost * numGroupCols) * input_rows;
    est->startup_cost += ptarget->cost.startup;

    /*-----
     * Run time cost includes:
     *	  1. Run time cost of underneath input relation
     *	  2. Run time cost of performing aggregation, per cost_agg()
     *	  3. PathTarget eval cost for each output row
     *-----
     */
    est->run_cost = ofpinfo->costs.rel_total_cost - ofpinfo->costs.rel_startup_cost;
    est->run_cost += aggcosts.finalCost * numGroups;
    est->run_cost += cpu_tuple_cost * numGroups;
    est->run_cost += ptarget->cost.per_tuple * numGroups;
}

    
static void
estimate_base_rel_cost(PlannerInfo *root,
					    RelOptInfo *foreignrel,
                        SqliteCostEstimates * est)
{
	Cost	cpu_per_tuple = cpu_tuple_cost + 
                            foreignrel->baserestrictcost.per_tuple;
    
    /* Clamp retrieved rows estimates to at most foreignrel->tuples. */
    est->retrieved_rows = Min(est->retrieved_rows, foreignrel->tuples);

    /*
     * Cost as though this were a seqscan, which is pessimistic.  We
     * effectively imagine the local_conds are being evaluated
     * remotely, too.
     */
    est->startup_cost = 0;
    est->run_cost = 0;
    est->run_cost += seq_page_cost * foreignrel->pages;

    est->startup_cost += foreignrel->baserestrictcost.startup;
    est->run_cost += cpu_per_tuple * foreignrel->tuples;
}

    
static void
add_paths_with_pathkeys_for_rel(PlannerInfo *root, RelOptInfo *rel,
								Path *epq_path)
{
	List	   *useful_pathkeys_list = NIL;		/* List of all pathkeys */
	ListCell   *lc;

	useful_pathkeys_list = get_useful_pathkeys_for_relation(root, rel);

	/* Create one path for each set of pathkeys we found above. */
	foreach(lc, useful_pathkeys_list)
	{
		List	   *useful_pathkeys = lfirst(lc);
        SqliteRelationCosts costs;
		estimate_path_cost_size(root, rel, NIL, useful_pathkeys, &costs);
		add_path(rel, (Path *)
				 create_foreignscan_path(root, rel,
										 NULL,
										 costs.rows,
										 costs.startup_cost,
										 costs.total_cost,
										 useful_pathkeys,
										 NULL,
										 epq_path,
										 NIL));
	}
}


/* Output join name for given join type */
static const char *
get_jointype_name(JoinType jointype)
{
	switch (jointype)
	{
		case JOIN_INNER:
			return "INNER";

		case JOIN_LEFT:
			return "LEFT";

		case JOIN_RIGHT:
			return "RIGHT";

		case JOIN_FULL:
			return "FULL";

		default:
			/* Shouldn't come here, but protect from buggy code. */
			elog(ERROR, "unsupported join type %d", jointype);
	}

	/* Keep compiler happy */
	return NULL;
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
static List *
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
				!is_foreignExpr(root, rel, em_expr))
			{
				query_pathkeys_ok = false;
				break;
			}
		}

		if (query_pathkeys_ok)
			useful_pathkeys_list = list_make1(list_copy(root->query_pathkeys));
	}

	/*
	 * Even if we're not using remote estimates, having the remote side do the
	 * sort generally won't be any worse than doing it locally, and it might
	 * be much better if the remote side can generate data in the right order
	 * without needing a sort at all.  However, what we're going to do next is
	 * try to generate pathkeys that seem promising for possible merge joins,
	 * and that's more speculative.  A wrong choice might hurt quite a bit, so
	 * bail out if we can't use remote estimates.
	 */
    return useful_pathkeys_list;
}


/*
 * Find an equivalence class member expression, all of whose Vars, come from
 * the indicated relation.
 */
static Expr *
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


/*
 * Detect whether we want to process an EquivalenceClass member.
 *
 * This is a callback for use by generate_implied_equalities_for_column.
 */
static bool
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
