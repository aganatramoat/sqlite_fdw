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
#include <optimizer/restrictinfo.h>
#include <optimizer/var.h>
#include <utils/builtins.h>
#include <utils/lsyscache.h>
#include <utils/relcache.h>

#include "sqlite_private.h"
#include "callbacks.h"
#include "deparse.h"


void
get_foreignPaths(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid)
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
        SqliteRelationCostSize est;

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

    
void
get_foreignRelSize(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid)
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

		if (is_foreign_expr(root, baserel, ri->clause))
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
	fpinfo->costsize.local_conds_sel = clauselist_selectivity(root,
													 fpinfo->local_conds,
													 baserel->relid,
													 JOIN_INNER,
													 NULL);

	cost_qual_eval(&fpinfo->costsize.local_conds_cost, 
                   fpinfo->local_conds, root);
	
    /*
	 * Set cached relation costs to some negative value, so that we can detect
	 * when they are set to some sensible costs during one (usually the first)
	 * of the calls to estimate_path_cost_size().
	 */
	fpinfo->costsize.rel_startup_cost = -1;
	fpinfo->costsize.rel_total_cost = -1;

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
    estimate_path_cost_size(root, baserel, NIL, NIL, &fpinfo->costsize);
	
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
	// fpinfo->db = get_sqliteDbHandle(fpinfo->src.database);
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
             is_foreign_expr(root, baserel, rinfo->clause) )
		{
			remote_conds = lappend(remote_conds, rinfo);
			remote_exprs = lappend(remote_exprs, rinfo->clause);
		}
        else
			local_exprs = lappend(local_exprs, rinfo->clause);
	}
	
    /* Build the query */
	initStringInfo(&sql);
	deparseSelectStmtForRel(&sql, root, baserel, NULL,
							remote_exprs, best_path->path.pathkeys,
							false, &retrieved_attrs, &params_list);

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

	/*
	 * Build the fdw_private list that will be available to the executor.
	 * Items in the list must match order in enum FdwScanPrivateIndex.
	 */
	fdw_private = list_make3(makeString(sql.data), retrieved_attrs,
							 makeString(fpinfo->relation_name->data));
	
    /*
	 * Create the ForeignScan node for the given relation.
	 *
	 * Note that the remote parameter expressions are stored in the fdw_exprs
	 * field of the finished plan node; we can't keep them in private state
	 * because then they wouldn't be subject to later planner processing.
	 */
	return make_foreignscan(tlist,
							local_exprs,
							0,
							params_list,
							fdw_private,
							fdw_scan_tlist,
							NULL,
							outer_plan);
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
	estimate_path_cost_size(root, joinrel, NIL, NIL, &fpinfo->costsize);
	/* Now update this information in the joinrel */
	joinrel->rows = fpinfo->costsize.rows;
	joinrel->reltarget->width = fpinfo->costsize.width;
    elog(SQLITE_FDW_LOG_LEVEL,"XXXXXXXX GetForeignJoinPaths 2 %f %f", 
                fpinfo->costsize.startup_cost, 
                fpinfo->costsize.total_cost);

	/*
	 * Create a new join path and add it to the joinrel which represents a
	 * join between foreign tables.
	 */
    // AG TODO: the total cost is hardocded here
	joinpath = create_foreignscan_path(root,
									   joinrel,
									   NULL,	/* default pathtarget */
									   joinrel->rows,
									   fpinfo->costsize.startup_cost,
									   // fpinfo->costs.total_cost,
                                       1.0,
									   NIL,		/* no pathkeys */
									   NULL,	/* no required_outer */
									   epq_path,
									   NIL);	/* no fdw_private */

	/* Add generated path into joinrel by add_path(). */
	add_path(joinrel, (Path *) joinpath);

	/* Consider pathkeys for the join relation */
	add_pathsWithPathKeysForRel(root, joinrel, epq_path);
    
    elog(SQLITE_FDW_LOG_LEVEL,"XXXXXXXX GetForeignJoinPaths 3 %d", 
                getpid());
    /// raise(SIGSTOP);

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
