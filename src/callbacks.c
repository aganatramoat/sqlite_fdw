#include <signal.h>
#include <sys/types.h>
#include <unistd.h>

#include <postgres.h>
#include <access/htup_details.h>
#include <foreign/fdwapi.h>
#include <nodes/relation.h>
#include <optimizer/cost.h>
#include <optimizer/paths.h>
#include <optimizer/pathnode.h>
#include <optimizer/planmain.h>
#include <optimizer/tlist.h>
#include <optimizer/restrictinfo.h>
#include <optimizer/var.h>
#include <utils/builtins.h>
#include <utils/lsyscache.h>
#include <utils/relcache.h>
#include <foreign/foreign.h>
#include <commands/defrem.h>
#include <commands/explain.h>

#include <sqlite3.h>

#include "sqlite_private.h"
#include "callbacks.h"


static int8 SQLITE_ANALYZE_NUM_ROWS = 0;


void
get_foreignPaths(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid)
{
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(baserel->fdw_private);
	ForeignPath *path;
	List	   *ppi_list;
	ListCell   *lc;

	/* Create a ForeignPath node and add it as only possible path */
	add_path(baserel, (Path *)
			 create_foreignscan_path(root, baserel,
									 NULL,		/* default pathtarget */
									 fpinfo->costsize.rows,
									 fpinfo->costsize.startup_cost,
									 fpinfo->costsize.total_cost,
									 NIL,		/* no pathkeys */
									 NULL,		/* no outer rel either */
									 NULL,		/* no extra plan */
									 NIL));		/* no fdw_private data */
	
    /* Add paths with pathkeys */
	add_pathsWithPathKeysForRel(root, baserel, NULL);
	
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
		if (!is_foreign_expr(root, baserel, rinfo->clause))
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
				if (!is_foreign_expr(root, baserel, rinfo->clause))
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

		/*
		 * ppi_rows currently won't get looked at by anything, but still we
		 * may as well ensure that it matches our idea of the rowcount.
		 */
		param_info->ppi_rows = fpinfo->costsize.rows;

		/* Make the path */
		path = create_foreignscan_path(root, baserel,
									   NULL,	/* default pathtarget */
									   fpinfo->costsize.rows,
									   fpinfo->costsize.startup_cost,
									   fpinfo->costsize.total_cost,
									   NIL,		/* no pathkeys */
									   param_info->ppi_req_outer,
									   NULL,
									   NIL);	/* no fdw_private list */
		add_path(baserel, (Path *) path);
	}
    
    // elog(SQLITE_FDW_LOG_LEVEL, "XXXXXX pid is %d", getpid());
    // raise(SIGSTOP);
}

    
/*
 * This is the first function that gets called back
 */
void
get_foreignRelSize(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid)
{
	SqliteFdwRelationInfo *fpinfo;
	ListCell              *lc;
    
    // initialize the fields of baserel that we will set
	baserel->rows = 0;
	fpinfo = palloc0(sizeof(SqliteFdwRelationInfo));
    fpinfo->src = get_tableSource(foreigntableid);
    fpinfo->pushdown_safe = true;
	baserel->fdw_private = (void *) fpinfo;
    
	fpinfo->relation_name = makeStringInfo();
	appendStringInfo(fpinfo->relation_name, "%s.%s",
         quote_identifier(get_namespace_name(get_rel_namespace(foreigntableid))),
         quote_identifier(get_rel_name(foreigntableid)));
	
	fpinfo->subqspec.make_outerrel = false;
	fpinfo->subqspec.make_innerrel = false;
	fpinfo->subqspec.lower_rels = NULL;
	fpinfo->relation_index = baserel->relid;
    
    pull_varattnos((Node *) baserel->reltarget->exprs, 
                    baserel->relid, 
                    &fpinfo->attrs_used);
    
    //  classify the condition as local or remote
    classifyConditions(root, baserel, baserel->baserestrictinfo, 
                       &fpinfo->remote_conds, &fpinfo->local_conds);
	
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
	fpinfo->costsize.local_conds_sel = clauselist_selectivity(root,
													 fpinfo->local_conds,
													 baserel->relid,
													 JOIN_INNER,
													 NULL);

	cost_qual_eval(&fpinfo->costsize.local_conds_cost, 
                   fpinfo->local_conds, root);
	
    /*
     * We are going to assume that postgres is responsible for keeping 
     * the statistics for the foreign tables.  This saves us the major
     * headache of extracting/translating sqlite3 information
     */
    
    /* 
     * Estimate baserel size as best we can with local statistics.
     * The following function will set baserel->rows and baserel->width
     * and baserel->baserestrictcost
     */
    set_baserel_size_estimates(root, baserel);
    estimate_path_cost_size(root, baserel);
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
	StringInfoData sql;
	List           *retrieved_attrs;
	ListCell       *lc;
	List	       *fdw_scan_tlist = NULL;

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
             is_foreign_expr(root, baserel, rinfo->clause) )
			remote_exprs = lappend(remote_exprs, rinfo->clause);
        else
			local_exprs = lappend(local_exprs, rinfo->clause);
	}
	
    /* Build the query */
    fdw_scan_tlist = build_tlist_to_deparse(baserel);
	initStringInfo(&sql);
	deparseSelectStmtForRel(&sql, root, baserel, fdw_scan_tlist,
							remote_exprs, best_path->path.pathkeys,
							false, &retrieved_attrs, &params_list);

    /* goodies for begin_foreignScan */
	fdw_private = list_make3(makeString(sql.data), retrieved_attrs, fpinfo);

	/*
     * params_list -> fdw_exprs
     * remote_exprs -> fdw_recheck_quals
	 */
	return make_foreignscan(tlist, local_exprs, baserel->relid,
	                        params_list, fdw_private, NIL,
	                        remote_exprs, outer_plan);
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
	StringInfoData sql;
	List           *retrieved_attrs = NULL;
	List           *params_list = NULL;
	List           *fdw_private = NULL;
    
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
    
    initStringInfo(&sql);
	deparseSelectStmtForRel(&sql, root, foreignrel, fdw_scan_tlist,
							remote_exprs, best_path->path.pathkeys,
							false, &retrieved_attrs, &params_list);

	/* Remember remote_exprs for possible use by postgresPlanDirectModify */
	// fpinfo->final_remote_exprs = remote_exprs;

    /* goodies for begin_foreignScan */
	fdw_private = list_make3(makeString(sql.data), retrieved_attrs, fpinfo);
	
    /*
     * scanrelid -> 0 for join and upper
     * params_list -> fdw_exprs
     * fdw_recheck_quals -> NULL
	 */
	return make_foreignscan(tlist, local_exprs, 0,
							params_list, fdw_private, fdw_scan_tlist,
							NULL, outer_plan);
}


ForeignScan *
get_foreignPlan(PlannerInfo *root, RelOptInfo *baserel,
                Oid foreigntableoid, ForeignPath *best_path,
                List *tlist, List *scan_clauses, Plan *outer_plan)
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


/*
 * get_foreignJoinPaths
 *		Add possible ForeignPath to joinrel, if join is safe to push down.
 */
void
get_foreignJoinPaths(PlannerInfo *root, RelOptInfo *joinrel,
                     RelOptInfo *outerrel, RelOptInfo *innerrel,
                     JoinType jointype, JoinPathExtraData *extra)
{
	SqliteFdwRelationInfo *fpinfo;
	ForeignPath *joinpath;
	Path	   *epq_path;		/* Path to create plan to be executed when
								 * EvalPlanQual gets triggered. */
	
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
    
	/*
	 * Compute the selectivity and cost of the local_conds, so we don't have
	 * to do it over again for each path. The best we can do for these
	 * conditions is to estimate selectivity on the basis of local statistics.
	 * The local conditions are applied after the join has been computed on
	 * the remote side like quals in WHERE clause, so pass jointype as
	 * JOIN_INNER.
	 */
	fpinfo->costsize.local_conds_sel = clauselist_selectivity(
        root,
        fpinfo->local_conds,
        0,
        JOIN_INNER,
        NULL);
	cost_qual_eval(&fpinfo->costsize.local_conds_cost, 
                    fpinfo->local_conds, root);
    fpinfo->joinspec.clause_sel = clauselist_selectivity(
                root, fpinfo->joinspec.clauses,
                0, fpinfo->joinspec.type,
                extra->sjinfo);

	/* Estimate costs for bare join relation */
	estimate_path_cost_size(root, joinrel);
	
    /* Now update this information in the joinrel */
	joinrel->rows = fpinfo->costsize.rows;
	joinrel->reltarget->width = fpinfo->costsize.width;

	/*
	 * Create a new join path and add it to the joinrel which represents a
	 * join between foreign tables.
	 */
	joinpath = create_foreignscan_path(root,
									   joinrel,
									   NULL,	/* default pathtarget */
									   joinrel->rows,
									   fpinfo->costsize.startup_cost,
									   fpinfo->costsize.total_cost,
									   NIL,		/* no pathkeys */
									   NULL,	/* no required_outer */
									   epq_path,
									   NIL);	/* no fdw_private */

	/* Add generated path into joinrel by add_path(). */
	add_path(joinrel, (Path *) joinpath);

	/* Consider pathkeys for the join relation */
	add_pathsWithPathKeysForRel(root, joinrel, epq_path);
    

	/* XXX Consider parameterized paths for the join relation */
}

    
void
begin_foreignScan(ForeignScanState *node, int eflags)
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
	SqliteFdwExecutionState  *festate = (SqliteFdwExecutionState *)
                    palloc0(sizeof(SqliteFdwExecutionState));
	ForeignScan *fsplan = (ForeignScan *) node->ss.ps.plan;
    SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(
                                    list_nth(fsplan->fdw_private, 2));

    /* will be accessed in iterate_foreignScan */
	node->fdw_state = (void *) festate;
	
	festate->db = get_sqliteDbHandle(fpinfo->src.database);
    festate->query = strVal(list_nth(fsplan->fdw_private, 0));
    festate->retrieved_attrs = list_nth(fsplan->fdw_private, 1);
    festate->param_exprs = ExecInitExprList(fsplan->fdw_exprs, 
                                            (PlanState *)node);
    festate->traits = get_pgTypeInputTraits(
            node->ss.ss_ScanTupleSlot->tts_tupleDescriptor);
    
    PG_TRY();
    {
        festate->stmt = prepare_sqliteQuery(festate->db, festate->query, NULL);
    }
    PG_CATCH();
    {
        cleanup_(festate);
		PG_RE_THROW();
    }
    PG_END_TRY();
}


List *
import_foreignSchema(ImportForeignSchemaStmt *stmt, Oid serverOid)
{
	sqlite3		   *db = NULL;
	sqlite3_stmt   *volatile tbls = NULL;
	char		   *filename = NULL;
	List		   *commands = NIL;
    ListCell       *lc;
    SqliteTableImportOptions importOptions = 
            get_sqliteTableImportOptions(stmt);

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
                                  "and name not like 'sqlite_%'";
		
        /* Iterate to all matching tables, and get their definition */
		tbls = prepare_sqliteQuery(db, tablenames_q, NULL);
		while (sqlite3_step(tbls) == SQLITE_ROW)
		{
            char *tablename = (char *) sqlite3_column_text(tbls, 0);
            char *cftsql = get_foreignTableCreationSql(
                            stmt, db, tablename, importOptions);
            if ( cftsql ) {
                commands = lappend(commands, cftsql);
            }
		}
	}
	PG_CATCH();
	{
        dispose_sqlite(&db, (sqlite3_stmt **)&tbls);
		PG_RE_THROW();
	}
	PG_END_TRY();
    
    dispose_sqlite(&db, (sqlite3_stmt **)&tbls);
	return commands;
}

    
void
explain_foreignScan(ForeignScanState *node, ExplainState *es)
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
	sqlite3_stmt			   *volatile stmt = NULL;
	char					   *query;
	size_t						len;
	const char				   *pzTail;
	SqliteFdwExecutionState	   *festate = (SqliteFdwExecutionState *) 
                                          node->fdw_state;

	/* Show the query (only if VERBOSE) */
	if (es->verbose)
		/* show query */
		ExplainPropertyText("sqlite query", festate->query, es);

	/* Build the query */
	len = strlen(festate->query) + 32;
	query = (char *)palloc(len);
	snprintf(query, len, "EXPLAIN QUERY PLAN %s", festate->query);

    /* Execute the query */
    PG_TRY();
    {
	    stmt = prepare_sqliteQuery(festate->db, query, &pzTail);
        while (sqlite3_step(stmt) == SQLITE_ROW)
            ExplainPropertyText(
                    "sqlite plan", 
                    (char*)sqlite3_column_text(stmt, 3), 
                    es);
    }
    PG_CATCH();
    {
        dispose_sqlite(NULL, (sqlite3_stmt **)&stmt);
        PG_RE_THROW();
    }
    PG_END_TRY();

    dispose_sqlite(NULL, (sqlite3_stmt **)&stmt);
}


static int
acquire_foreignSamples(Relation relation, int elevel,
                       HeapTuple *rows, int targrows,
                       double *totalrows,
	                   double *totaldeadrows)
{
    SqliteAnalyzeState   state = {0};
	StringInfoData sql;
	ForeignTable *table = GetForeignTable(RelationGetRelid(relation));
    TupleDesc desc = relation->rd_att;
    
    state.relation = relation;
    state.rows = rows;
    state.targrows = targrows;
    state.src = get_tableSource(table->relid);
    state.traits = get_pgTypeInputTraits(desc);
    state.slot = MakeTupleTableSlot();
    state.slot->tts_tupleDescriptor = desc;
    state.slot->tts_values = palloc(desc->natts * sizeof(Datum));
    state.slot->tts_isnull = palloc(desc->natts * sizeof(bool));
    
    if (targrows > 0)
        state.toskip = SQLITE_ANALYZE_NUM_ROWS / targrows - 1;
    else
        state.toskip = SQLITE_ANALYZE_NUM_ROWS;
    if (state.toskip <= 0)
        state.toskip = 1;

    sql = construct_foreignSamplesQuery(&state);
    collect_foreignSamples(&state, sql);
    
    *totalrows = state.count;
    *totaldeadrows = 0;
	ereport(elevel,
			(errmsg("\"%s\": table contains %.0f rows, %d rows in sample",
					RelationGetRelationName(relation),
					*totalrows, state.numsamples)));
    return state.numsamples;
}


bool
analyze_foreignTable(Relation relation, AcquireSampleRowsFunc *func,
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
	ForeignTable *table = GetForeignTable(RelationGetRelid(relation));
    SqliteTableSource src = get_tableSource(table->relid);
    double rowsize = get_rowSize(relation);
    SQLITE_ANALYZE_NUM_ROWS = get_rowCount(src.database, src.table);

    *totalpages = (BlockNumber) ((rowsize * SQLITE_ANALYZE_NUM_ROWS) / BLCKSZ);
    *func = acquire_foreignSamples;
    
    return true;
}


TupleTableSlot *
iterate_foreignScan(ForeignScanState *node)
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
	TupleTableSlot  *slot = node->ss.ss_ScanTupleSlot;

    if ( ! festate->params_bound )
        sqlite_bind_param_values(node);
	
    ExecClearTuple(slot);
    if (sqlite3_step(festate->stmt) == SQLITE_ROW)
        populate_tupleTableSlot(festate->stmt, slot,
                                festate->retrieved_attrs, festate->traits);
    return slot;
}

    
void
end_foreignScan(ForeignScanState *node)
{
    SqliteFdwExecutionState *festate = (SqliteFdwExecutionState *)
                                            node->fdw_state;
    printf("%s", "");
	cleanup_(festate);
}

    
void
rescan_foreignScan(ForeignScanState *node)
{
	/*
	 * Restart the scan from the beginning. Note that any parameters the scan
	 * depends on may have changed value, so the new scan does not necessarily
	 * return exactly the same rows.
	 */
}


/*
 * Assess whether the aggregation, grouping and having operations can be pushed
 * down to the foreign server.  As a side effect, save information we obtain in
 * this function to PgFdwRelationInfo of the input relation.
 */
static bool
foreign_grouping_ok(PlannerInfo *root, RelOptInfo *grouping_rel)
{
	Query	   *query = root->parse;
	PathTarget *grouping_target;
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) 
                                     grouping_rel->fdw_private;
	SqliteFdwRelationInfo *grouped_fpinfo;
	List	   *aggvars;
	ListCell   *lc;
	int			i;
	List	   *tlist = NIL;

	/* Grouping Sets are not pushable */
	if (query->groupingSets)
		return false;

	/* Get the fpinfo of the underlying scan relation. */
	grouped_fpinfo = (SqliteFdwRelationInfo *) fpinfo->grouped_rel->fdw_private;

	/*
	 * If underneath input relation has any local conditions, those conditions
	 * are required to be applied before performing aggregation.  Hence the
	 * aggregate cannot be pushed down.
	 */
	if (grouped_fpinfo->local_conds)
		return false;

	/*
	 * The targetlist expected from this node and the targetlist pushed down
	 * to the foreign server may be different. The latter requires
	 * sortgrouprefs to be set to push down GROUP BY clause, but should not
	 * have those arising from ORDER BY clause. These sortgrouprefs may be
	 * different from those in the plan's targetlist. Use a copy of path
	 * target to record the new sortgrouprefs.
	 */
	grouping_target = copy_pathtarget(root->upper_targets[UPPERREL_GROUP_AGG]);

	/*
	 * Evaluate grouping targets and check whether they are safe to push down
	 * to the foreign side.  All GROUP BY expressions will be part of the
	 * grouping target and thus there is no need to evaluate it separately.
	 * While doing so, add required expressions into target list which can
	 * then be used to pass to foreign server.
	 */
	i = 0;
	foreach(lc, grouping_target->exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);
		Index		sgref = get_pathtarget_sortgroupref(grouping_target, i);
		ListCell   *l;

		/* Check whether this expression is part of GROUP BY clause */
		if (sgref && get_sortgroupref_clause_noerr(sgref, query->groupClause))
		{
			/*
			 * If any of the GROUP BY expression is not shippable we can not
			 * push down aggregation to the foreign server.
			 */
			if (!is_foreign_expr(root, grouping_rel, expr))
				return false;

			/* Pushable, add to tlist */
			tlist = add_to_flat_tlist(tlist, list_make1(expr));
		}
		else
		{
			/* Check entire expression whether it is pushable or not */
			if (is_foreign_expr(root, grouping_rel, expr))
			{
				/* Pushable, add to tlist */
				tlist = add_to_flat_tlist(tlist, list_make1(expr));
			}
			else
			{
				/*
				 * If we have sortgroupref set, then it means that we have an
				 * ORDER BY entry pointing to this expression.  Since we are
				 * not pushing ORDER BY with GROUP BY, clear it.
				 */
				if (sgref)
					grouping_target->sortgrouprefs[i] = 0;

				/* Not matched exactly, pull the var with aggregates then */
				aggvars = pull_var_clause((Node *) expr,
										  PVC_INCLUDE_AGGREGATES);

				if (!is_foreign_expr(root, grouping_rel, (Expr *) aggvars))
					return false;

				/*
				 * Add aggregates, if any, into the targetlist.  Plain var
				 * nodes should be either same as some GROUP BY expression or
				 * part of some GROUP BY expression. In later case, the query
				 * cannot refer plain var nodes without the surrounding
				 * expression.  In both the cases, they are already part of
				 * the targetlist and thus no need to add them again.  In fact
				 * adding pulled plain var nodes in SELECT clause will cause
				 * an error on the foreign server if they are not same as some
				 * GROUP BY expression.
				 */
				foreach(l, aggvars)
				{
					Expr	   *expr = (Expr *) lfirst(l);

					if (IsA(expr, Aggref))
						tlist = add_to_flat_tlist(tlist, list_make1(expr));
				}
			}
		}

		i++;
	}

	/*
	 * Classify the pushable and non-pushable having clauses and save them in
	 * remote_conds and local_conds of the grouping rel's fpinfo.
	 */
	if (root->hasHavingQual && query->havingQual)
	{
		ListCell   *lc;

		foreach(lc, (List *) query->havingQual)
		{
			Expr	   *expr = (Expr *) lfirst(lc);
			RestrictInfo *rinfo;

			/*
			 * Currently, the core code doesn't wrap havingQuals in
			 * RestrictInfos, so we must make our own.
			 */
			Assert(!IsA(expr, RestrictInfo));
			rinfo = make_restrictinfo(expr,
									  true,
									  false,
									  false,
									  root->qual_security_level,
									  grouping_rel->relids,
									  NULL,
									  NULL);
			if (is_foreign_expr(root, grouping_rel, expr))
				fpinfo->remote_conds = lappend(fpinfo->remote_conds, rinfo);
			else
				fpinfo->local_conds = lappend(fpinfo->local_conds, rinfo);
		}
	}

	/*
	 * If there are any local conditions, pull Vars and aggregates from it and
	 * check whether they are safe to pushdown or not.
	 */
	if (fpinfo->local_conds)
	{
		List	   *aggvars = NIL;
		ListCell   *lc;

		foreach(lc, fpinfo->local_conds)
		{
			RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);

			aggvars = list_concat(aggvars,
								  pull_var_clause((Node *) rinfo->clause,
												  PVC_INCLUDE_AGGREGATES));
		}

		foreach(lc, aggvars)
		{
			Expr	   *expr = (Expr *) lfirst(lc);

			/*
			 * If aggregates within local conditions are not safe to push
			 * down, then we cannot push down the query.  Vars are already
			 * part of GROUP BY clause which are checked above, so no need to
			 * access them again here.
			 */
			if (IsA(expr, Aggref))
			{
				if (!is_foreign_expr(root, grouping_rel, expr))
					return false;

				tlist = add_to_flat_tlist(tlist, list_make1(expr));
			}
		}
	}

	/* Transfer any sortgroupref data to the replacement tlist */
	apply_pathtarget_labeling_to_tlist(tlist, grouping_target);

	/* Store generated targetlist */
	fpinfo->grouped_tlist = tlist;

	/* Safe to pushdown */
	fpinfo->pushdown_safe = true;

	/*
	 * Set the string describing this grouped relation to be used in EXPLAIN
	 * output of corresponding ForeignScan.
	 */
	fpinfo->relation_name = makeStringInfo();
	appendStringInfo(fpinfo->relation_name, "Aggregate on (%s)",
					 grouped_fpinfo->relation_name->data);

	return true;
}


/*
 * add_foreign_grouping_paths
 *		Add foreign path for grouping and/or aggregation.
 *
 * Given input_rel represents the underlying scan.  The paths are added to the
 * given grouping_rel.
 */
static void
add_foreign_grouping_paths(PlannerInfo *root, RelOptInfo *input_rel,
						   RelOptInfo *grouping_rel)
{
	Query	   *parse = root->parse;
	SqliteFdwRelationInfo *ifpinfo = input_rel->fdw_private;
	SqliteFdwRelationInfo *fpinfo = grouping_rel->fdw_private;
	ForeignPath *grouppath;
	PathTarget *grouping_target;
    
	/* Nothing to be done, if there is no grouping or aggregation required. */
	if (!parse->groupClause && !parse->groupingSets && !parse->hasAggs &&
		!root->hasHavingQual)
		return;

	grouping_target = root->upper_targets[UPPERREL_GROUP_AGG];

	/* save the input_rel as grouped_rel in fpinfo */
	fpinfo->grouped_rel = input_rel;
    fpinfo->src.database = ifpinfo->src.database;
    
	/* Assess if it is safe to push down aggregation and grouping. */
	if (!foreign_grouping_ok(root, grouping_rel))
		return;

	/* Estimate the cost of push down */
	estimate_path_cost_size(root, grouping_rel);
    
	/* Create and add foreign path to the grouping relation. */
	grouppath = create_foreignscan_path(root,
										grouping_rel,
										grouping_target,
										fpinfo->costsize.rows,
										fpinfo->costsize.startup_cost,
										fpinfo->costsize.total_cost,
										NIL,	/* no pathkeys */
										NULL,	/* no required_outer */
										NULL,
										NIL);	/* no fdw_private */

	/* Add generated path into grouping_rel by add_path(). */
	add_path(grouping_rel, (Path *) grouppath);
}

    
void
get_foreignUpperPaths(PlannerInfo *root, UpperRelationKind stage,
                      RelOptInfo *input_rel, RelOptInfo *grouping_rel)
{
	SqliteFdwRelationInfo *fpinfo;

	/*
	 * If input rel is not safe to pushdown, then simply return as we cannot
	 * perform any post-join operations on the foreign server.
	 */
	if (!input_rel->fdw_private ||
		!((SqliteFdwRelationInfo *) input_rel->fdw_private)->pushdown_safe)
		return;

	/* Ignore stages we don't support; and skip any duplicate calls. */
	if (stage != UPPERREL_GROUP_AGG || grouping_rel->fdw_private)
		return;

	fpinfo = (SqliteFdwRelationInfo *) palloc0(sizeof(SqliteFdwRelationInfo));
	fpinfo->pushdown_safe = false;
	grouping_rel->fdw_private = fpinfo;

	add_foreign_grouping_paths(root, input_rel, grouping_rel);
}
