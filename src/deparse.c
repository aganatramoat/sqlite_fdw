/*-------------------------------------------------------------------------
 *
 * deparse.c
 *		  Query deparser for postgres_fdw
 *
 * This file includes functions that examine query WHERE clauses to see
 * whether they're safe to send to the remote server for execution, as
 * well as functions to construct the query text to be sent.  The latter
 * functionality is annoyingly duplicative of ruleutils.c, but there are
 * enough special considerations that it seems best to keep this separate.
 * One saving grace is that we only need deparse logic for node types that
 * we consider safe to send.
 *
 * We assume that the remote session's search_path is exactly "pg_catalog",
 * and thus we need schema-qualify all and only names outside pg_catalog.
 *
 * We do not consider that it is ever safe to send COLLATE expressions to
 * the remote server: it might not have the same collation names we do.
 * (Later we might consider it safe to send COLLATE "C", but even that would
 * fail on old remote servers.)  An expression is considered safe to send
 * only if all operator/function input collations used in it are traceable to
 * Var(s) of the foreign table.  That implies that if the remote server gets
 * a different answer than we do, the foreign table's columns are not marked
 * with collations that match the remote table's columns, which we can
 * consider to be user error.
 *
 * Portions Copyright (c) 2012-2017, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *		  contrib/postgres_fdw/deparse.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"


#include "access/heapam.h"
#include "access/htup_details.h"
#include "access/sysattr.h"
#include "catalog/pg_aggregate.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "foreign/foreign.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/execnodes.h"
#include "nodes/plannodes.h"
#include "optimizer/clauses.h"
#include "optimizer/prep.h"
#include "optimizer/tlist.h"
#include "optimizer/var.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/syscache.h"
#include "utils/typcache.h"

#include "sqlite_private.h"


/*
 * Context for deparseExpr
 */
typedef struct deparse_expr_cxt 
{
	PlannerInfo *root;			/* global planner state */
	RelOptInfo *foreignrel;		/* the foreign relation we are planning for */
	RelOptInfo *scanrel;		/* the underlying scan relation. Same as
								 * foreignrel, when that represents a join or
								 * a base relation. */
	StringInfo	buf;			/* output buffer to append to */
	List	  **params_list;	/* exprs that will become remote Params */
} deparse_expr_cxt;

#define REL_ALIAS_PREFIX	"r"
/* Handy macro to add relation name qualification */
#define ADD_REL_QUALIFIER(buf, varno)	\
		appendStringInfo((buf), "%s%d.", REL_ALIAS_PREFIX, (varno))
#define SUBQUERY_REL_ALIAS_PREFIX	"s"
#define SUBQUERY_COL_ALIAS_PREFIX	"c"

/*
 * Functions to determine whether an expression can be evaluated safely on
 * remote server.
 */
static char *deparse_type_name(Oid type_oid, int32 typemod);

/*
 * Functions to construct string representation of a node tree.
 */
static void deparseTargetList(StringInfo buf,
				  PlannerInfo *root,
				  Index rtindex,
				  Relation rel,
				  bool is_returning,
				  Bitmapset *attrs_used,
				  bool qualify_col,
				  List **retrieved_attrs);
static void deparseExplicitTargetList(List *tlist, List **retrieved_attrs,
						  deparse_expr_cxt *context);
static void deparseSubqueryTargetList(deparse_expr_cxt *context);
static void deparseColumnRef(StringInfo buf, int varno, int varattno,
				 PlannerInfo *root, bool qualify_col);
static void deparseRelation(StringInfo buf, Relation rel);
static void deparseExpr(Expr *expr, deparse_expr_cxt *context);
static void deparseVar(Var *node, deparse_expr_cxt *context);
static void deparseConst(Const *node, deparse_expr_cxt *context, int showtype);
static void deparseParam(Param *node, deparse_expr_cxt *context);
static void deparseArrayRef(ArrayRef *node, deparse_expr_cxt *context);
static void deparseFuncExpr(FuncExpr *node, deparse_expr_cxt *context);
static void deparseOpExpr(OpExpr *node, deparse_expr_cxt *context);
static void deparseOperatorName(StringInfo buf, Form_pg_operator opform);
static void deparseDistinctExpr(DistinctExpr *node, deparse_expr_cxt *context);
static void deparseScalarArrayOpExpr(ScalarArrayOpExpr *node,
						 deparse_expr_cxt *context);
static void deparseRelabelType(RelabelType *node, deparse_expr_cxt *context);
static void deparseBoolExpr(BoolExpr *node, deparse_expr_cxt *context);
static void deparseNullTest(NullTest *node, deparse_expr_cxt *context);
static void deparseArrayExpr(ArrayExpr *node, deparse_expr_cxt *context);
static void printRemoteParam(int paramindex, Oid paramtype, int32 paramtypmod,
				 deparse_expr_cxt *context);
static void printRemotePlaceholder(Oid paramtype, int32 paramtypmod,
					   deparse_expr_cxt *context);
static void deparseSelectSql(List *tlist, bool is_subquery, List **retrieved_attrs,
				 deparse_expr_cxt *context);
static void appendOrderByClause(List *pathkeys, deparse_expr_cxt *context);
static void appendConditions(List *exprs, deparse_expr_cxt *context);
static void deparseFromExprForRel(StringInfo buf, PlannerInfo *root,
					RelOptInfo *joinrel, bool use_alias, List **params_list);
static void deparseFromExpr(List *quals, deparse_expr_cxt *context);
static void deparseRangeTblRef(StringInfo buf, PlannerInfo *root,
							   RelOptInfo *foreignrel, bool make_subquery,
							   List **params_list);
static void deparseAggref(Aggref *node, deparse_expr_cxt *context);
static void appendGroupByClause(List *tlist, deparse_expr_cxt *context);
static void appendAggOrderBy(List *orderList, List *targetList,
				 deparse_expr_cxt *context);
static void appendFunctionName(Oid funcid, deparse_expr_cxt *context);
static Node *deparseSortGroupClause(Index ref, List *tlist,
					   deparse_expr_cxt *context);

/*
 * Helper functions
 */
static bool is_subquery_var(Var *node, RelOptInfo *foreignrel,
							int *relno, int *colno);
static void get_relation_column_alias_ids(Var *node, RelOptInfo *foreignrel,
										  int *relno, int *colno);


/*
 * Check if expression is safe to execute remotely, and return true if so.
 *
 * The collation of the expr is reported in expr_collid
 * If we expect the collation of the expr to be something,
 * we pass that along as expected_collid
 *
 * For the moment the fdw ships the default collation to sqlite3. 
 * If we were ever to extend that to shipping all collations then 
 * this function has to change
 */
bool
foreign_expr_walker(Node *node, Oid *expr_collid, Oid *expected_collid)
{
    Oid collation = InvalidOid;

	/* Need do nothing for empty subexpressions */
	if (node == NULL)
		return true;

    if ( expected_collid ) 
        if ( *expected_collid != DEFAULT_COLLATION_OID && 
             *expected_collid != InvalidOid )
            return false;
    
    elog(SQLITE_FDW_LOG_LEVEL,
         "in foreign_expr_walker %s", nodeToString(node));
    
	switch (nodeTag(node))
	{
		case T_Var:
            collation = ((Var *) node)->varcollid;
			break;
		case T_Const:
            collation = ((Const *) node)->constcollid;
			break;
		case T_Param:
            collation = ((Param *) node)->paramcollid;
			break;
		case T_OpExpr:
			{
				OpExpr	   *oe = (OpExpr *) node;

				/*
				 * Shipping only builtin operators
				 */
                if (!is_builtin(oe->opno))
                    return false;

                /*
                 * the semantics of like in sqlite are different than
                 * postgres.  So we will ship over the textlike function
                 * to sqlite. 
                 * Also sqlite does not have an ilike operator
                 */
                if (oe->opno >= OID_NAME_ICLIKE_OP &&
                    oe->opno <= OID_BPCHAR_ICLIKE_OP)
                    return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) oe->args, NULL,
										 &oe->inputcollid))
                    return false;

                collation = oe->opcollid;
			}
			break;
		case T_RelabelType:
            return false;
			break;
		case T_BoolExpr:
			{
				BoolExpr   *b = (BoolExpr *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) b->args, NULL, NULL))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
			}
			break;
		case T_NullTest:
			{
				NullTest   *nt = (NullTest *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) nt->arg, NULL, NULL))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
			}
			break;
		case T_List:
			{
				List	   *l = (List *) node;
				ListCell   *lc;
                Oid       *vec = l->length > 0 ?
                                 palloc0(l->length * sizeof(Oid)) : NULL;
                int        i = 0;

				/*
				 * Recurse to component subexpressions.
				 */
				foreach(lc, l)
				{
					if (!foreign_expr_walker((Node *) lfirst(lc), vec + i, 
                                              expected_collid))
						return false;
                    i++;
				}
                for ( i = 1; i < l->length; i++)
                    if ( vec[i] != vec[0] )
                        return false;
                collation = vec ? vec[0] : InvalidOid;
			}
			break;
		case T_Aggref:
			{
				Aggref	   *agg = (Aggref *) node;
				ListCell   *lc;

				/* Only non-split aggregates are pushable. */
				if (agg->aggsplit != AGGSPLIT_SIMPLE)
					return false;

				/* As usual, it must be shippable. */
				if (!is_shippable_agg(agg->aggfnoid))
					return false;
				
                /*
				 * For aggorder elements, check whether the sort operator, if
				 * specified, is shippable or not.
				 */
				if (agg->aggorder)  // no support in sqlite for aggorder
                    return false;

                if (agg->aggfilter) // no support in sqlite for aggfilter
                    return false;

				/*
				 * Recurse to input args. aggdirectargs, aggorder and
				 * aggdistinct are all present in args, so no need to check
				 * their shippability explicitly.
				 */
				foreach(lc, agg->args)
				{
					Node	   *n = (Node *) lfirst(lc);

					/* If TargetEntry, extract the expression from it */
					if (IsA(n, TargetEntry))
					{
						TargetEntry *tle = (TargetEntry *) n;

						n = (Node *) tle->expr;
					}

					if (!foreign_expr_walker(n, NULL, &agg->inputcollid))
						return false;
				}
                collation = agg->aggcollid;
			}
			break;
		case T_FuncExpr:
            {
				FuncExpr   *fe = (FuncExpr *) node;

				/*
				 * If function used by the expression is not shippable, it
				 * can't be sent to remote because it might have incompatible
				 * semantics on remote side.
				 */
				if (!is_shippable_func(fe->funcid))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) fe->args, NULL,
                                         &fe->inputcollid))
					return false;

                collation = fe->funccollid;
			}
		case T_ScalarArrayOpExpr: 
            {
                /*
                 *  When the sql statement is where blah in (...) we get 
                 *  here as where blah = any(....)
                 *  We visit this node for blah = all(...), in this case
                 *  we will let postgres handle the query
                 */
				ScalarArrayOpExpr *oe = (ScalarArrayOpExpr *) node;
                Node *arraynode = (Node *) lsecond(oe->args); 
                
                if ( (!oe->useOr) || 
                     (!arraynode) ||
                     (!IsA(arraynode, Const)) ||
                     ( ((Const *)arraynode)->constisnull ) 
                   )
                    return false;
                
                if (!foreign_expr_walker((Node *) oe->args, NULL,
                                         &oe->inputcollid))
					return false;
                
                collation = InvalidOid;
            }
            break;
		case T_DistinctExpr:	/* IS DISTINCT FROM, no support in sqlite */
		case T_ArrayExpr:   // No array support in sqlite
		default:
			return false;
	}

    if ( collation != InvalidOid && collation != DEFAULT_COLLATION_OID )
        return false;

    if ( expected_collid && collation != *expected_collid )
        return false;

    if ( expr_collid )
        *expr_collid = collation;

    return true;
}

/*
 * Convert type OID + typmod info into a type name we can ship to the remote
 * server.  Someplace else had better have verified that this type name is
 * expected to be known on the remote end.
 *
 * This is almost just format_type_with_typemod(), except that if left to its
 * own devices, that function will make schema-qualification decisions based
 * on the local search_path, which is wrong.  We must schema-qualify all
 * type names that are not in pg_catalog.  We assume here that built-in types
 * are all in pg_catalog and need not be qualified; otherwise, qualify.
 */
static char *
deparse_type_name(Oid type_oid, int32 typemod)
{
	if (is_builtin(type_oid))
		return format_type_with_typemod(type_oid, typemod);
	else
		return format_type_with_typemod_qualified(type_oid, typemod);
}

/*
 * Build the targetlist for given relation to be deparsed as SELECT clause.
 *
 * The output targetlist contains the columns that need to be fetched from the
 * foreign server for the given relation.  If foreignrel is an upper relation,
 * then the output targetlist can also contain expressions to be evaluated on
 * foreign server.
 */
List *
build_tlist_to_deparse(RelOptInfo *foreignrel)
{
	List	   *tlist = NIL;
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);
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

/*
 * Deparse SELECT statement for given relation into buf.
 *
 * tlist contains the list of desired columns to be fetched from foreign server.
 * For a base relation fpinfo->attrs_used is used to construct SELECT clause,
 * hence the tlist is ignored for a base relation.
 *
 * remote_conds is the list of conditions to be deparsed into the WHERE clause
 * (or, in the case of upper relations, into the HAVING clause).
 *
 * If params_list is not NULL, it receives a list of Params and other-relation
 * Vars used in the clauses; these values must be transmitted to the remote
 * server as parameter values.
 *
 * If params_list is NULL, we're generating the query for EXPLAIN purposes,
 * so Params and other-relation Vars should be replaced by dummy values.
 *
 * pathkeys is the list of pathkeys to order the result by.
 *
 * is_subquery is the flag to indicate whether to deparse the specified
 * relation as a subquery.
 *
 * List of columns selected is returned in retrieved_attrs.
 */
extern void
deparseSelectStmtForRel(StringInfo buf, PlannerInfo *root, RelOptInfo *rel,
						List *tlist, List *remote_conds, List *pathkeys,
						bool is_subquery, List **retrieved_attrs,
						List **params_list)
{
	deparse_expr_cxt context;
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(rel->fdw_private);
	List	*quals;
    
	/*
	 * We handle relations for foreign tables, joins between those and upper
	 * relations.
	 */
	Assert(IS_JOIN_REL(rel) || IS_SIMPLE_REL(rel) || IS_UPPER_REL(rel));

	/* Fill portions of context common to upper, join and base relation */
	context.buf = buf;
	context.root = root;
	context.foreignrel = rel;
	context.scanrel = IS_UPPER_REL(rel) ? fpinfo->grouped_rel : rel;
	context.params_list = params_list;

	/* Construct SELECT clause */
	deparseSelectSql(tlist, is_subquery, retrieved_attrs, &context);
    
	/*
	 * For upper relations, the WHERE clause is built from the remote
	 * conditions of the underlying scan relation; otherwise, we can use the
	 * supplied list of remote conditions directly.
	 */
	if (IS_UPPER_REL(rel)) {
        if (! context.scanrel )
            elog(ERROR, "internal error needed grouped_rel");
		quals = FDW_RELINFO(context.scanrel->fdw_private)->remote_conds;
    }
	else
		quals = remote_conds;

	/* Construct FROM and WHERE clauses */
	deparseFromExpr(quals, &context);
    

	if (IS_UPPER_REL(rel))
	{
		/* Append GROUP BY clause */
		appendGroupByClause(tlist, &context);

		/* Append HAVING clause */
		if (remote_conds)
		{
			appendStringInfo(buf, " HAVING ");
			appendConditions(remote_conds, &context);
		}
	}

	/* Add ORDER BY clause if we found any useful pathkeys */
	if (pathkeys)
		appendOrderByClause(pathkeys, &context);
}

/*
 * Construct a simple SELECT statement that retrieves desired columns
 * of the specified foreign table, and append it to "buf".  The output
 * contains just "SELECT ... ".
 *
 * We also create an integer List of the columns being retrieved, which is
 * returned to *retrieved_attrs, unless we deparse the specified relation
 * as a subquery.
 *
 * tlist is the list of desired columns.  is_subquery is the flag to
 * indicate whether to deparse the specified relation as a subquery.
 * Read prologue of deparseSelectStmtForRel() for details.
 */
static void
deparseSelectSql(List *tlist, bool is_subquery, List **retrieved_attrs,
				 deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	RelOptInfo *foreignrel = context->foreignrel;
	PlannerInfo *root = context->root;
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);

	/*
	 * Construct SELECT list
	 */
	appendStringInfoString(buf, "SELECT ");

	if (is_subquery)
	{
		/*
		 * For a relation that is deparsed as a subquery, emit expressions
		 * specified in the relation's reltarget.  Note that since this is
		 * for the subquery, no need to care about *retrieved_attrs.
		 */
		deparseSubqueryTargetList(context);
	}
	else if (IS_JOIN_REL(foreignrel) || IS_UPPER_REL(foreignrel))
	{
		/*
		 * For a join or upper relation the input tlist gives the list of
		 * columns required to be fetched from the foreign server.
		 */
		deparseExplicitTargetList(tlist, retrieved_attrs, context);
	}
	else
	{
		/*
		 * For a base relation fpinfo->attrs_used gives the list of columns
		 * required to be fetched from the foreign server.
		 */
		RangeTblEntry *rte = planner_rt_fetch(foreignrel->relid, root);

		/*
		 * Core code already has some lock on each rel being planned, so we
		 * can use NoLock here.
		 */
		Relation	rel = heap_open(rte->relid, NoLock);
		deparseTargetList(buf, root, foreignrel->relid, rel, false,
						  fpinfo->attrs_used, false, retrieved_attrs);
		heap_close(rel, NoLock);
	}
}

/*
 * Construct a FROM clause and, if needed, a WHERE clause, and append those to
 * "buf".
 *
 * quals is the list of clauses to be included in the WHERE clause.
 * (These may or may not include RestrictInfo decoration.)
 */
static void
deparseFromExpr(List *quals, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	RelOptInfo *scanrel = context->scanrel;

	/* For upper relations, scanrel must be either a joinrel or a baserel */
	Assert(!IS_UPPER_REL(context->foreignrel) ||
		   IS_JOIN_REL(scanrel) || IS_SIMPLE_REL(scanrel));

	/* Construct FROM clause */
	appendStringInfoString(buf, " FROM ");
	deparseFromExprForRel(buf, context->root, scanrel,
						  (bms_num_members(scanrel->relids) > 1),
						  context->params_list);

	/* Construct WHERE clause */
	if (quals != NIL)
	{
		appendStringInfo(buf, " WHERE ");
		appendConditions(quals, context);
	}
}

/*
 * Emit a target list that retrieves the columns specified in attrs_used.
 * This is used for both SELECT and RETURNING targetlists; the is_returning
 * parameter is true only for a RETURNING targetlist.
 *
 * The tlist text is appended to buf, and we also create an integer List
 * of the columns being retrieved, which is returned to *retrieved_attrs.
 *
 * If qualify_col is true, add relation alias before the column name.
 */
static void
deparseTargetList(StringInfo buf,
				  PlannerInfo *root,
				  Index rtindex,
				  Relation rel,
				  bool is_returning,
				  Bitmapset *attrs_used,
				  bool qualify_col,
				  List **retrieved_attrs)
{
	TupleDesc	tupdesc = RelationGetDescr(rel);
	bool		have_wholerow;
	bool		first;
	int			i;

	*retrieved_attrs = NIL;

	/* If there's a whole-row reference, we'll need all the columns. */
	have_wholerow = bms_is_member(0 - FirstLowInvalidHeapAttributeNumber,
								  attrs_used);

	first = true;
	for (i = 1; i <= tupdesc->natts; i++)
	{
		Form_pg_attribute attr = tupdesc->attrs[i - 1];

		/* Ignore dropped attributes. */
		if (attr->attisdropped)
			continue;

		if (have_wholerow ||
			bms_is_member(i - FirstLowInvalidHeapAttributeNumber,
						  attrs_used))
		{
			if (!first)
				appendStringInfoString(buf, ", ");
			else if (is_returning)
				appendStringInfoString(buf, " RETURNING ");
			first = false;

			deparseColumnRef(buf, rtindex, i, root, qualify_col);

			*retrieved_attrs = lappend_int(*retrieved_attrs, i);
		}
	}

	/*
	 * Add ctid and oid if needed.  We currently don't support retrieving any
	 * other system columns.
	 */
	if (bms_is_member(SelfItemPointerAttributeNumber - FirstLowInvalidHeapAttributeNumber,
					  attrs_used))
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		else if (is_returning)
			appendStringInfoString(buf, " RETURNING ");
		first = false;

		if (qualify_col)
			ADD_REL_QUALIFIER(buf, rtindex);
		appendStringInfoString(buf, "ctid");

		*retrieved_attrs = lappend_int(*retrieved_attrs,
									   SelfItemPointerAttributeNumber);
	}
	if (bms_is_member(ObjectIdAttributeNumber - FirstLowInvalidHeapAttributeNumber,
					  attrs_used))
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		else if (is_returning)
			appendStringInfoString(buf, " RETURNING ");
		first = false;

		if (qualify_col)
			ADD_REL_QUALIFIER(buf, rtindex);
		appendStringInfoString(buf, "oid");

		*retrieved_attrs = lappend_int(*retrieved_attrs,
									   ObjectIdAttributeNumber);
	}

	/* Don't generate bad syntax if no undropped columns */
	if (first && !is_returning)
		appendStringInfoString(buf, "NULL");
}


/*
 * Deparse conditions from the provided list and append them to buf.
 *
 * The conditions in the list are assumed to be ANDed. This function is used to
 * deparse WHERE clauses, JOIN .. ON clauses and HAVING clauses.
 *
 * Depending on the caller, the list elements might be either RestrictInfos
 * or bare clauses.
 */
static void
appendConditions(List *exprs, deparse_expr_cxt *context)
{
	int			nestlevel;
	ListCell   *lc;
	bool		is_first = true;
	StringInfo	buf = context->buf;

	/* Make sure any constants in the exprs are printed portably */
	nestlevel = set_transmission_modes();

	foreach(lc, exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);

		/* Extract clause from RestrictInfo, if required */
		if (IsA(expr, RestrictInfo))
			expr = ((RestrictInfo *) expr)->clause;

		/* Connect expressions with "AND" and parenthesize each condition. */
		if (!is_first)
			appendStringInfoString(buf, " AND ");

		appendStringInfoChar(buf, '(');
		deparseExpr(expr, context);
		appendStringInfoChar(buf, ')');

		is_first = false;
	}

	reset_transmission_modes(nestlevel);
}

/* Output join name for given join type */
extern const char *
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
 * Deparse given targetlist and append it to context->buf.
 *
 * tlist is list of TargetEntry's which in turn contain Var nodes.
 *
 * retrieved_attrs is the list of continuously increasing integers starting
 * from 1. It has same number of entries as tlist.
 */
static void
deparseExplicitTargetList(List *tlist, List **retrieved_attrs,
						  deparse_expr_cxt *context)
{
	ListCell   *lc;
	StringInfo	buf = context->buf;
	int			i = 0;

	*retrieved_attrs = NIL;

	foreach(lc, tlist)
	{
		TargetEntry *tle = lfirst_node(TargetEntry, lc);

		if (i > 0)
			appendStringInfoString(buf, ", ");
		deparseExpr((Expr *) tle->expr, context);

		*retrieved_attrs = lappend_int(*retrieved_attrs, i + 1);
		i++;
	}

	if (i == 0)
		appendStringInfoString(buf, "NULL");
}

/*
 * Emit expressions specified in the given relation's reltarget.
 *
 * This is used for deparsing the given relation as a subquery.
 */
static void
deparseSubqueryTargetList(deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	RelOptInfo *foreignrel = context->foreignrel;
	bool		first;
	ListCell   *lc;

	/* Should only be called in these cases. */
	Assert(IS_SIMPLE_REL(foreignrel) || IS_JOIN_REL(foreignrel));

	first = true;
	foreach(lc, foreignrel->reltarget->exprs)
	{
		Node	   *node = (Node *) lfirst(lc);

		if (!first)
			appendStringInfoString(buf, ", ");
		first = false;

		deparseExpr((Expr *) node, context);
	}

	/* Don't generate bad syntax if no expressions */
	if (first)
		appendStringInfoString(buf, "NULL");
}

/*
 * Construct FROM clause for given relation
 *
 * The function constructs ... JOIN ... ON ... for join relation. For a base
 * relation it just returns schema-qualified tablename, with the appropriate
 * alias if so requested.
 */
static void
deparseFromExprForRel(StringInfo buf, PlannerInfo *root, RelOptInfo *foreignrel,
					  bool use_alias, List **params_list)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) 
                                    foreignrel->fdw_private;

	if (IS_JOIN_REL(foreignrel))
	{
		StringInfoData join_sql_o;
		StringInfoData join_sql_i;

		/* Deparse outer relation */
		initStringInfo(&join_sql_o);
		deparseRangeTblRef(&join_sql_o, root, fpinfo->joinspec.outerrel,
						   fpinfo->subqspec.make_outerrel, params_list);

		/* Deparse inner relation */
		initStringInfo(&join_sql_i);
		deparseRangeTblRef(&join_sql_i, root, fpinfo->joinspec.innerrel,
						   fpinfo->subqspec.make_innerrel, params_list);

		/*
		 * For a join relation FROM clause entry is deparsed as
		 *
		 * ((outer relation) <join type> (inner relation) ON (joinclauses))
		 */
		appendStringInfo(buf, "(%s %s JOIN %s ON ", join_sql_o.data,
					   get_jointype_name(fpinfo->joinspec.type), join_sql_i.data);

		/* Append join clause; (TRUE) if no join clause */
		if (fpinfo->joinspec.clauses)
		{
			deparse_expr_cxt context;

			context.buf = buf;
			context.foreignrel = foreignrel;
			context.scanrel = foreignrel;
			context.root = root;
			context.params_list = params_list;

			appendStringInfo(buf, "(");
			appendConditions(fpinfo->joinspec.clauses, &context);
			appendStringInfo(buf, ")");
		}
		else
			appendStringInfoString(buf, "(TRUE)");

		/* End the FROM clause entry. */
		appendStringInfo(buf, ")");
	}
	else
	{
		RangeTblEntry *rte = planner_rt_fetch(foreignrel->relid, root);

		/*
		 * Core code already has some lock on each rel being planned, so we
		 * can use NoLock here.
		 */
		Relation	rel = heap_open(rte->relid, NoLock);

		deparseRelation(buf, rel);

		/*
		 * Add a unique alias to avoid any conflict in relation names due to
		 * pulled up subqueries in the query being built for a pushed down
		 * join.
		 */
		if (use_alias)
			appendStringInfo(buf, " %s%d", REL_ALIAS_PREFIX, foreignrel->relid);

		heap_close(rel, NoLock);
	}
}

/*
 * Append FROM clause entry for the given relation into buf.
 */
static void
deparseRangeTblRef(StringInfo buf, PlannerInfo *root, RelOptInfo *foreignrel,
				   bool make_subquery, List **params_list)
{
	SqliteFdwRelationInfo *fpinfo = (SqliteFdwRelationInfo *) foreignrel->fdw_private;

	/* Should only be called in these cases. */
	Assert(IS_SIMPLE_REL(foreignrel) || IS_JOIN_REL(foreignrel));

	Assert(fpinfo->local_conds == NIL);

	/* If make_subquery is true, deparse the relation as a subquery. */
	if (make_subquery)
	{
		List	   *retrieved_attrs;
		int			ncols;

		/* Deparse the subquery representing the relation. */
		appendStringInfoChar(buf, '(');
		deparseSelectStmtForRel(buf, root, foreignrel, NIL,
								fpinfo->remote_conds, NIL, true,
								&retrieved_attrs, params_list);
		appendStringInfoChar(buf, ')');

		/* Append the relation alias. */
		appendStringInfo(buf, " %s%d", SUBQUERY_REL_ALIAS_PREFIX,
						 fpinfo->relation_index);

		/*
		 * Append the column aliases if needed.  Note that the subquery emits
		 * expressions specified in the relation's reltarget (see
		 * deparseSubqueryTargetList).
		 */
		ncols = list_length(foreignrel->reltarget->exprs);
		if (ncols > 0)
		{
			int			i;

			appendStringInfoChar(buf, '(');
			for (i = 1; i <= ncols; i++)
			{
				if (i > 1)
					appendStringInfoString(buf, ", ");

				appendStringInfo(buf, "%s%d", SUBQUERY_COL_ALIAS_PREFIX, i);
			}
			appendStringInfoChar(buf, ')');
		}
	}
	else
		deparseFromExprForRel(buf, root, foreignrel, true, params_list);
}


/*
 * Construct SELECT statement to acquire size in blocks of given relation.
 *
 * Note: we use local definition of block size, not remote definition.
 * This is perhaps debatable.
 *
 * Note: pg_relation_size() exists in 8.1 and later.
 */
void
deparseAnalyzeSizeSql(StringInfo buf, Relation rel)
{
	StringInfoData relname;

	/* We'll need the remote relation name as a literal. */
	initStringInfo(&relname);
	deparseRelation(&relname, rel);

	appendStringInfoString(buf, "SELECT pg_catalog.pg_relation_size(");
	deparseStringLiteral(buf, relname.data);
	appendStringInfo(buf, "::pg_catalog.regclass) / %d", BLCKSZ);
}

/*
 * Construct SELECT statement to acquire sample rows of given relation.
 *
 * SELECT command is appended to buf, and list of columns retrieved
 * is returned to *retrieved_attrs.
 */
void
deparseAnalyzeSql(StringInfo buf, Relation rel, List **retrieved_attrs)
{
	Oid			relid = RelationGetRelid(rel);
	TupleDesc	tupdesc = RelationGetDescr(rel);
	int			i;
	char	   *colname;
	List	   *options;
	ListCell   *lc;
	bool		first = true;

	*retrieved_attrs = NIL;

	appendStringInfoString(buf, "SELECT ");
	for (i = 0; i < tupdesc->natts; i++)
	{
		/* Ignore dropped columns. */
		if (tupdesc->attrs[i]->attisdropped)
			continue;

		if (!first)
			appendStringInfoString(buf, ", ");
		first = false;

		/* Use attribute name or column_name option. */
		colname = NameStr(tupdesc->attrs[i]->attname);
		options = GetForeignColumnOptions(relid, i + 1);

		foreach(lc, options)
		{
			DefElem    *def = (DefElem *) lfirst(lc);

			if (strcmp(def->defname, "column_name") == 0)
			{
				colname = defGetString(def);
				break;
			}
		}

		appendStringInfoString(buf, quote_identifier(colname));

		*retrieved_attrs = lappend_int(*retrieved_attrs, i + 1);
	}

	/* Don't generate bad syntax for zero-column relation. */
	if (first)
		appendStringInfoString(buf, "NULL");

	/*
	 * Construct FROM clause
	 */
	appendStringInfoString(buf, " FROM ");
	deparseRelation(buf, rel);
}

/*
 * Construct name to use for given column, and emit it into buf.
 * If it has a column_name FDW option, use that instead of attribute name.
 *
 * If qualify_col is true, qualify column name with the alias of relation.
 */
static void
deparseColumnRef(StringInfo buf, int varno, int varattno, PlannerInfo *root,
				 bool qualify_col)
{
	RangeTblEntry *rte;

	/* We support fetching the remote side's CTID and OID. */
	if (varattno == SelfItemPointerAttributeNumber)
	{
		if (qualify_col)
			ADD_REL_QUALIFIER(buf, varno);
		appendStringInfoString(buf, "ctid");
	}
	else if (varattno == ObjectIdAttributeNumber)
	{
		if (qualify_col)
			ADD_REL_QUALIFIER(buf, varno);
		appendStringInfoString(buf, "oid");
	}
	else if (varattno < 0)
	{
		/*
		 * All other system attributes are fetched as 0, except for table OID,
		 * which is fetched as the local table OID.  However, we must be
		 * careful; the table could be beneath an outer join, in which case it
		 * must go to NULL whenever the rest of the row does.
		 */
		Oid			fetchval = 0;

		if (varattno == TableOidAttributeNumber)
		{
			rte = planner_rt_fetch(varno, root);
			fetchval = rte->relid;
		}

		if (qualify_col)
		{
			appendStringInfoString(buf, "CASE WHEN (");
			ADD_REL_QUALIFIER(buf, varno);
			appendStringInfo(buf, "*)::text IS NOT NULL THEN %u END", fetchval);
		}
		else
			appendStringInfo(buf, "%u", fetchval);
	}
	else if (varattno == 0)
	{
		/* Whole row reference */
		Relation	rel;
		Bitmapset  *attrs_used;

		/* Required only to be passed down to deparseTargetList(). */
		List	   *retrieved_attrs;

		/* Get RangeTblEntry from array in PlannerInfo. */
		rte = planner_rt_fetch(varno, root);

		/*
		 * The lock on the relation will be held by upper callers, so it's
		 * fine to open it with no lock here.
		 */
		rel = heap_open(rte->relid, NoLock);

		/*
		 * The local name of the foreign table can not be recognized by the
		 * foreign server and the table it references on foreign server might
		 * have different column ordering or different columns than those
		 * declared locally. Hence we have to deparse whole-row reference as
		 * ROW(columns referenced locally). Construct this by deparsing a
		 * "whole row" attribute.
		 */
		attrs_used = bms_add_member(NULL,
									0 - FirstLowInvalidHeapAttributeNumber);

		/*
		 * In case the whole-row reference is under an outer join then it has
		 * to go NULL whenever the rest of the row goes NULL. Deparsing a join
		 * query would always involve multiple relations, thus qualify_col
		 * would be true.
		 */
		if (qualify_col)
		{
			appendStringInfoString(buf, "CASE WHEN (");
			ADD_REL_QUALIFIER(buf, varno);
			appendStringInfo(buf, "*)::text IS NOT NULL THEN ");
		}

		appendStringInfoString(buf, "ROW(");
		deparseTargetList(buf, root, varno, rel, false, attrs_used, qualify_col,
						  &retrieved_attrs);
		appendStringInfoString(buf, ")");

		/* Complete the CASE WHEN statement started above. */
		if (qualify_col)
			appendStringInfo(buf, " END");

		heap_close(rel, NoLock);
		bms_free(attrs_used);
	}
	else
	{
		char	   *colname = NULL;
		List	   *options;
		ListCell   *lc;

		/* varno must not be any of OUTER_VAR, INNER_VAR and INDEX_VAR. */
		Assert(!IS_SPECIAL_VARNO(varno));

		/* Get RangeTblEntry from array in PlannerInfo. */
		rte = planner_rt_fetch(varno, root);

		/*
		 * If it's a column of a foreign table, and it has the column_name FDW
		 * option, use that value.
		 */
		options = GetForeignColumnOptions(rte->relid, varattno);
		foreach(lc, options)
		{
			DefElem    *def = (DefElem *) lfirst(lc);

			if (strcmp(def->defname, "column_name") == 0)
			{
				colname = defGetString(def);
				break;
			}
		}

		/*
		 * If it's a column of a regular table or it doesn't have column_name
		 * FDW option, use attribute name.
		 */
		if (colname == NULL)
			colname = get_relid_attribute_name(rte->relid, varattno);

		if (qualify_col)
			ADD_REL_QUALIFIER(buf, varno);

		appendStringInfoString(buf, quote_identifier(colname));
	}
}

/*
 * Append remote name of specified foreign table to buf.
 * Use value of table_name FDW option (if any) instead of relation's name.
 * Similarly, schema_name FDW option overrides schema name.
 */
static void
deparseRelation(StringInfo buf, Relation rel)
{
	ForeignTable *table;
	const char *relname = NULL;
	ListCell   *lc;

	/* obtain additional catalog information. */
	table = GetForeignTable(RelationGetRelid(rel));

	/*
	 * Use value of FDW options if any, instead of the name of object itself.
	 */
	foreach(lc, table->options)
	{
		DefElem    *def = (DefElem *) lfirst(lc);
		if (strcmp(def->defname, "table_name") == 0)
			relname = defGetString(def);
	}

	if (relname == NULL)
		relname = RelationGetRelationName(rel);

	appendStringInfo(buf, "%s", quote_identifier(relname));
}

/*
 * Append a SQL string literal representing "val" to buf.
 */
void
deparseStringLiteral(StringInfo buf, const char *val)
{
	const char *valptr;

	/*
	 * Rather than making assumptions about the remote server's value of
	 * standard_conforming_strings, always use E'foo' syntax if there are any
	 * backslashes.  This will fail on remote servers before 8.1, but those
	 * are long out of support.
	 */
	// if (strchr(val, '\\') != NULL)
	// 	appendStringInfoChar(buf, ESCAPE_STRING_SYNTAX);
	appendStringInfoChar(buf, '\'');
	for (valptr = val; *valptr; valptr++)
	{
		char		ch = *valptr;

		if (SQL_STR_DOUBLE(ch, true))
			appendStringInfoChar(buf, ch);
		appendStringInfoChar(buf, ch);
	}
	appendStringInfoChar(buf, '\'');
}

/*
 * Deparse given expression into context->buf.
 *
 * This function must support all the same node types that foreign_expr_walker
 * accepts.
 *
 * Note: unlike ruleutils.c, we just use a simple hard-wired parenthesization
 * scheme: anything more complex than a Var, Const, function call or cast
 * should be self-parenthesized.
 */
static void
deparseExpr(Expr *node, deparse_expr_cxt *context)
{
	if (node == NULL)
		return;
    
	switch (nodeTag(node))
	{
		case T_Var:
			deparseVar((Var *) node, context);
			break;
		case T_Const:
			deparseConst((Const *) node, context, 0);
			break;
		case T_Param:
			deparseParam((Param *) node, context);
			break;
		case T_ArrayRef:
			deparseArrayRef((ArrayRef *) node, context);
			break;
		case T_FuncExpr:
			deparseFuncExpr((FuncExpr *) node, context);
			break;
		case T_OpExpr:
			deparseOpExpr((OpExpr *) node, context);
			break;
		case T_DistinctExpr:
			deparseDistinctExpr((DistinctExpr *) node, context);
			break;
		case T_ScalarArrayOpExpr:
			deparseScalarArrayOpExpr((ScalarArrayOpExpr *) node, context);
			break;
		case T_RelabelType:
			deparseRelabelType((RelabelType *) node, context);
			break;
		case T_BoolExpr:
			deparseBoolExpr((BoolExpr *) node, context);
			break;
		case T_NullTest:
			deparseNullTest((NullTest *) node, context);
			break;
		case T_ArrayExpr:
		    deparseArrayExpr((ArrayExpr *) node, context);
		    break;
		case T_Aggref:
			deparseAggref((Aggref *) node, context);
			break;
		default:
			elog(ERROR, "unsupported expression type for deparse: %d",
				 (int) nodeTag(node));
			break;
	}
}

/*
 * Deparse given Var node into context->buf.
 *
 * If the Var belongs to the foreign relation, just print its remote name.
 * Otherwise, it's effectively a Param (and will in fact be a Param at
 * run time).  Handle it the same way we handle plain Params --- see
 * deparseParam for comments.
 */
static void
deparseVar(Var *node, deparse_expr_cxt *context)
{
	Relids		relids = context->scanrel->relids;
	int			relno;
	int			colno;

	/* Qualify columns when multiple relations are involved. */
	bool		qualify_col = (bms_num_members(relids) > 1);

	/*
	 * If the Var belongs to the foreign relation that is deparsed as a
	 * subquery, use the relation and column alias to the Var provided
	 * by the subquery, instead of the remote name.
	 */
	if (is_subquery_var(node, context->scanrel, &relno, &colno))
	{
		appendStringInfo(context->buf, "%s%d.%s%d",
						 SUBQUERY_REL_ALIAS_PREFIX, relno,
						 SUBQUERY_COL_ALIAS_PREFIX, colno);
		return;
	}

	if (bms_is_member(node->varno, relids) && node->varlevelsup == 0)
		deparseColumnRef(context->buf, node->varno, node->varattno,
						 context->root, qualify_col);
	else
	{
		/* Treat like a Param */
		if (context->params_list)
		{
			int			pindex = 0;
			ListCell   *lc;

			/* find its index in params_list */
			foreach(lc, *context->params_list)
			{
				pindex++;
				if (equal(node, (Node *) lfirst(lc)))
					break;
			}
			if (lc == NULL)
			{
				/* not in list, so add it */
				pindex++;
				*context->params_list = lappend(*context->params_list, node);
			}

			printRemoteParam(pindex, node->vartype, node->vartypmod, context);
		}
		else
		{
			printRemotePlaceholder(node->vartype, node->vartypmod, context);
		}
	}
}


static bool
const_is_array(Const * node)
{
    Oid typeoid = node->consttype;
    HeapTuple	 tuple = SearchSysCache1(TYPEOID, ObjectIdGetDatum(typeoid));
	Form_pg_type typeform;
    bool         isarray;
	
	if (!HeapTupleIsValid(tuple))
        elog(ERROR, "cache lookup failed for type %u", typeoid);
	typeform = (Form_pg_type) GETSTRUCT(tuple);

    isarray = typeform->typelem != InvalidOid && typeform->typstorage != 'p';
    ReleaseSysCache(tuple);
    return isarray;
}

/*
 * Deparse given constant value into context->buf.
 *
 * This function has to be kept in sync with ruleutils.c's get_const_expr.
 * As for that function, showtype can be -1 to never show "::typename" decoration,
 * or +1 to always show it, or 0 to show it only if the constant wouldn't be assumed
 * to be the right type by default.
 */
static void
deparseConst(Const *node, deparse_expr_cxt *context, int showtype)
{
	StringInfo	buf = context->buf;
	Oid			typoutput;
	bool		typIsVarlena;
	char	   *extval;
	bool		isfloat = false;
	bool		needlabel;
    
    elog(SQLITE_FDW_LOG_LEVEL,
         "in deparseConst %s, isarray = %d", 
         nodeToString(node), const_is_array(node));

	if (node->constisnull)
	{
		appendStringInfoString(buf, "NULL");
		return;
	}

	getTypeOutputInfo(node->consttype,
					  &typoutput, &typIsVarlena);
	extval = OidOutputFunctionCall(typoutput, node->constvalue);
    
	switch (node->consttype)
	{
		case INT2OID:
		case INT4OID:
		case INT8OID:
		case OIDOID:
		case FLOAT4OID:
		case FLOAT8OID:
		case NUMERICOID:
			{
				/*
				 * No need to quote unless it's a special value such as 'NaN'.
				 * See comments in get_const_expr().
				 */
				if (strspn(extval, "0123456789+-eE.") == strlen(extval))
				{
					if (extval[0] == '+' || extval[0] == '-')
						appendStringInfo(buf, "(%s)", extval);
					else
						appendStringInfoString(buf, extval);
					if (strcspn(extval, "eE.") != strlen(extval))
						isfloat = true; /* it looks like a float */
				}
				else
					appendStringInfo(buf, "'%s'", extval);
			}
			break;
		case BITOID:
		case VARBITOID:
			appendStringInfo(buf, "x'%s'", extval);
			break;
		case BOOLOID: // booleans should be ints for sqlite
			if (strcmp(extval, "t") == 0)
				appendStringInfoString(buf, "1");
			else
				appendStringInfoString(buf, "0");
			break;
		default:
			deparseStringLiteral(buf, extval);
			break;
	}

	pfree(extval);

	if (showtype < 0)
		return;

	/*
	 * For showtype == 0, append ::typename unless the constant will be
	 * implicitly typed as the right type when it is read in.
	 *
	 * XXX this code has to be kept in sync with the behavior of the parser,
	 * especially make_const.
	 */
	switch (node->consttype)
	{
		case BOOLOID:
		case INT4OID:
		case UNKNOWNOID:
			needlabel = false;
			break;
		case NUMERICOID:
			needlabel = !isfloat || (node->consttypmod >= 0);
			break;
		default:
			needlabel = true;
			break;
	}
    // TODO: AG we don't need this type casting business
	if (needlabel || showtype > 0)
        ;
		// appendStringInfo(buf, "::%s",
		// 				 deparse_type_name(node->consttype,
		// 								   node->consttypmod));
}


static void
deparseConstArray(Const *arraynode, deparse_expr_cxt *context)
{
    ArrayType *arrayval = DatumGetArrayTypeP(arraynode->constvalue);
    int16   elmlen;
    bool    elmbyval;
    char    elmalign;
    int     num_elements, i;
    Datum   *element_values;
    bool    *element_null;
    Const   array_member;
    bool    isfirst = true;

    
    get_typlenbyvalalign(
            ARR_ELEMTYPE(arrayval),                                
            &elmlen, &elmbyval, &elmalign); 
    
    deconstruct_array(arrayval, ARR_ELEMTYPE(arrayval),
                      elmlen, elmbyval, elmalign,
                      &element_values, &element_null, &num_elements);

    array_member.xpr.type = T_Const;
    array_member.consttype = ARR_ELEMTYPE(arrayval);
    array_member.consttypmod = -1;
    array_member.constcollid = arraynode->constcollid;
    array_member.constlen = elmlen;
    array_member.constbyval = elmbyval;

    for ( i = 0; i < num_elements; i++) {
        if (!isfirst)
            appendStringInfoString(context->buf, ",");
        array_member.constvalue = element_values[i];
        array_member.constisnull = element_null[i];
        deparseConst(&array_member, context, -1);
        isfirst = false;
    }
}


/*
 * Deparse given Param node.
 *
 * If we're generating the query "for real", add the Param to
 * context->params_list if it's not already present, and then use its index
 * in that list as the remote parameter number.  During EXPLAIN, there's
 * no need to identify a parameter number.
 */
static void
deparseParam(Param *node, deparse_expr_cxt *context)
{
	if (context->params_list)
	{
		int			pindex = 0;
		ListCell   *lc;

		/* find its index in params_list */
		foreach(lc, *context->params_list)
		{
			pindex++;
			if (equal(node, (Node *) lfirst(lc)))
				break;
		}
		if (lc == NULL)
		{
			/* not in list, so add it */
			pindex++;
			*context->params_list = lappend(*context->params_list, node);
		}

		printRemoteParam(pindex, node->paramtype, node->paramtypmod, context);
	}
	else
	{
		printRemotePlaceholder(node->paramtype, node->paramtypmod, context);
	}
}

/*
 * Deparse an array subscript expression.
 */
static void
deparseArrayRef(ArrayRef *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	ListCell   *lowlist_item;
	ListCell   *uplist_item;

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, '(');

	/*
	 * Deparse referenced array expression first.  If that expression includes
	 * a cast, we have to parenthesize to prevent the array subscript from
	 * being taken as typename decoration.  We can avoid that in the typical
	 * case of subscripting a Var, but otherwise do it.
	 */
	if (IsA(node->refexpr, Var))
		deparseExpr(node->refexpr, context);
	else
	{
		appendStringInfoChar(buf, '(');
		deparseExpr(node->refexpr, context);
		appendStringInfoChar(buf, ')');
	}

	/* Deparse subscript expressions. */
	lowlist_item = list_head(node->reflowerindexpr);	/* could be NULL */
	foreach(uplist_item, node->refupperindexpr)
	{
		appendStringInfoChar(buf, '[');
		if (lowlist_item)
		{
			deparseExpr(lfirst(lowlist_item), context);
			appendStringInfoChar(buf, ':');
			lowlist_item = lnext(lowlist_item);
		}
		deparseExpr(lfirst(uplist_item), context);
		appendStringInfoChar(buf, ']');
	}

	appendStringInfoChar(buf, ')');
}

/*
 * Deparse a function call.
 */
static void
deparseFuncExpr(FuncExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	bool		use_variadic;
	bool		first;
	ListCell   *arg;
	
	/*
	 * If the function call came from an implicit coercion, then just show the
	 * first argument.
	 */
	if (node->funcformat == COERCE_IMPLICIT_CAST)
	{
		deparseExpr((Expr *) linitial(node->args), context);
		return;
	}

	/*
	 * If the function call came from a cast, then show the first argument
	 * plus an explicit cast operation.
	 */
	if (node->funcformat == COERCE_EXPLICIT_CAST)
	{
		Oid			rettype = node->funcresulttype;
		int32		coercedTypmod;

		/* Get the typmod if this is a length-coercion function */
		(void) exprIsLengthCoercion((Node *) node, &coercedTypmod);

		deparseExpr((Expr *) linitial(node->args), context);
		appendStringInfo(buf, "::%s",
						 deparse_type_name(rettype, coercedTypmod));
		return;
	}

	/* Check if need to print VARIADIC (cf. ruleutils.c) */
	use_variadic = node->funcvariadic;

	/*
	 * Normal function: display as proname(args).
	 */
	appendFunctionName(node->funcid, context);
	appendStringInfoChar(buf, '(');

	/* ... and all the arguments */
	first = true;
	foreach(arg, node->args)
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		if (use_variadic && lnext(arg) == NULL)
			appendStringInfoString(buf, "VARIADIC ");
		deparseExpr((Expr *) lfirst(arg), context);
		first = false;
	}
	appendStringInfoChar(buf, ')');
}

/*
 * Deparse given operator expression.   To avoid problems around
 * priority of operations, we always parenthesize the arguments.
 */
static void
deparseOpExpr(OpExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	HeapTuple	tuple;
	Form_pg_operator form;
	char		oprkind;
	ListCell   *arg;

	/* Retrieve information about the operator from system catalog. */
	tuple = SearchSysCache1(OPEROID, ObjectIdGetDatum(node->opno));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for operator %u", node->opno);
	form = (Form_pg_operator) GETSTRUCT(tuple);
	oprkind = form->oprkind;

	/* Sanity check. */
	Assert((oprkind == 'r' && list_length(node->args) == 1) ||
		   (oprkind == 'l' && list_length(node->args) == 1) ||
		   (oprkind == 'b' && list_length(node->args) == 2));

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, '(');

	/* Deparse left operand. */
	if (oprkind == 'r' || oprkind == 'b')
	{
		arg = list_head(node->args);
		deparseExpr(lfirst(arg), context);
		appendStringInfoChar(buf, ' ');
	}

	/* Deparse operator name. */
	deparseOperatorName(buf, form);

	/* Deparse right operand. */
	if (oprkind == 'l' || oprkind == 'b')
	{
		arg = list_tail(node->args);
		appendStringInfoChar(buf, ' ');
		deparseExpr(lfirst(arg), context);
	}

	appendStringInfoChar(buf, ')');

	ReleaseSysCache(tuple);
}


static char const *
translate_opname__(char *opname)
{
    if (strcmp(opname, "~~") == 0)
        return "like";
    else if (strcmp(opname, "!~~") == 0)
        return "not like";
    if (strcmp(opname, "~") == 0)
        return "regexp";
    else if (strcmp(opname, "!~") == 0)
        return "not regexp";
    else
        return opname;
}

/*
 * Print the name of an operator.
 */
static void
deparseOperatorName(StringInfo buf, Form_pg_operator opform)
{
	char	   *opname;

	/* opname is not a SQL identifier, so we should not quote it. */
	opname = NameStr(opform->oprname);

	/* Print schema name only if it's not pg_catalog */
	if (opform->oprnamespace != PG_CATALOG_NAMESPACE)
	{
		const char *opnspname;

		opnspname = get_namespace_name(opform->oprnamespace);
		/* Print fully qualified operator name. */
		appendStringInfo(buf, "OPERATOR(%s.%s)",
						 quote_identifier(opnspname), opname);
	}
	else
	{
		/* Just print operator name. */
		appendStringInfoString(buf, translate_opname__(opname));
	}
}

/*
 * Deparse IS DISTINCT FROM.
 */
static void
deparseDistinctExpr(DistinctExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;

	Assert(list_length(node->args) == 2);

	appendStringInfoChar(buf, '(');
	deparseExpr(linitial(node->args), context);
	appendStringInfoString(buf, " IS DISTINCT FROM ");
	deparseExpr(lsecond(node->args), context);
	appendStringInfoChar(buf, ')');
}


/*
 * Deparse given ScalarArrayOpExpr expression.  To avoid problems
 * around priority of operations, we always parenthesize the arguments.
 */
static void
deparseScalarArrayOpExpr(ScalarArrayOpExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	// HeapTuple	tuple;
	// Form_pg_operator form;
	Expr	   *arg1;
	Expr	   *arg2;

	/* Retrieve information about the operator from system catalog. */
	// tuple = SearchSysCache1(OPEROID, ObjectIdGetDatum(node->opno));
	// if (!HeapTupleIsValid(tuple))
		// elog(ERROR, "cache lookup failed for operator %u", node->opno);
	// form = (Form_pg_operator) GETSTRUCT(tuple);

	/* Sanity check. */
	Assert(list_length(node->args) == 2);

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, '(');

	/* Deparse left operand. */
	arg1 = linitial(node->args);
	deparseExpr(arg1, context);
	appendStringInfoChar(buf, ' ');

	/* Deparse operator name plus decoration. */
	appendStringInfo(buf, " IN (");

	/* Deparse right operand. */
	arg2 = lsecond(node->args);
	deparseConstArray((Const *)arg2, context);

	appendStringInfoChar(buf, ')');

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, ')');

	// ReleaseSysCache(tuple);
}

/*
 * Deparse a RelabelType (binary-compatible cast) node.
 */
static void
deparseRelabelType(RelabelType *node, deparse_expr_cxt *context)
{
	deparseExpr(node->arg, context);
	if (node->relabelformat != COERCE_IMPLICIT_CAST)
		appendStringInfo(context->buf, "::%s",
						 deparse_type_name(node->resulttype,
										   node->resulttypmod));
}

/*
 * Deparse a BoolExpr node.
 */
static void
deparseBoolExpr(BoolExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	const char *op = NULL;		/* keep compiler quiet */
	bool		first;
	ListCell   *lc;

	switch (node->boolop)
	{
		case AND_EXPR:
			op = "AND";
			break;
		case OR_EXPR:
			op = "OR";
			break;
		case NOT_EXPR:
			appendStringInfoString(buf, "(NOT ");
			deparseExpr(linitial(node->args), context);
			appendStringInfoChar(buf, ')');
			return;
	}

	appendStringInfoChar(buf, '(');
	first = true;
	foreach(lc, node->args)
	{
		if (!first)
			appendStringInfo(buf, " %s ", op);
		deparseExpr((Expr *) lfirst(lc), context);
		first = false;
	}
	appendStringInfoChar(buf, ')');
}

/*
 * Deparse IS [NOT] NULL expression.
 */
static void
deparseNullTest(NullTest *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;

	appendStringInfoChar(buf, '(');
	deparseExpr(node->arg, context);

	/*
	 * For scalar inputs, we prefer to print as IS [NOT] NULL, which is
	 * shorter and traditional.  If it's a rowtype input but we're applying a
	 * scalar test, must print IS [NOT] DISTINCT FROM NULL to be semantically
	 * correct.
	 */
	if (node->argisrow || !type_is_rowtype(exprType((Node *) node->arg)))
	{
		if (node->nulltesttype == IS_NULL)
			appendStringInfoString(buf, " IS NULL)");
		else
			appendStringInfoString(buf, " IS NOT NULL)");
	}
	else
	{
		if (node->nulltesttype == IS_NULL)
			appendStringInfoString(buf, " IS NOT DISTINCT FROM NULL)");
		else
			appendStringInfoString(buf, " IS DISTINCT FROM NULL)");
	}
}

/*
 * Deparse ARRAY[...] construct.
 */
static void
deparseArrayExpr(ArrayExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	bool		first = true;
	ListCell   *lc;

	appendStringInfoString(buf, "ARRAY[");
	foreach(lc, node->elements)
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		deparseExpr(lfirst(lc), context);
		first = false;
	}
	appendStringInfoChar(buf, ']');

	/* If the array is empty, we need an explicit cast to the array type. */
	if (node->elements == NIL)
		appendStringInfo(buf, "::%s",
						 deparse_type_name(node->array_typeid, -1));
}

/*
 * Deparse an Aggref node.
 */
static void
deparseAggref(Aggref *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	bool		use_variadic;

	/* Only basic, non-split aggregation accepted. */
	Assert(node->aggsplit == AGGSPLIT_SIMPLE);

	/* Check if need to print VARIADIC (cf. ruleutils.c) */
	use_variadic = node->aggvariadic;

	/* Find aggregate name from aggfnoid which is a pg_proc entry */
	appendFunctionName(node->aggfnoid, context);
	appendStringInfoChar(buf, '(');

	/* Add DISTINCT */
	appendStringInfo(buf, "%s", (node->aggdistinct != NIL) ? "DISTINCT " : "");

	if (AGGKIND_IS_ORDERED_SET(node->aggkind))
	{
		/* Add WITHIN GROUP (ORDER BY ..) */
		ListCell   *arg;
		bool		first = true;

		Assert(!node->aggvariadic);
		Assert(node->aggorder != NIL);

		foreach(arg, node->aggdirectargs)
		{
			if (!first)
				appendStringInfoString(buf, ", ");
			first = false;

			deparseExpr((Expr *) lfirst(arg), context);
		}

		appendStringInfoString(buf, ") WITHIN GROUP (ORDER BY ");
		appendAggOrderBy(node->aggorder, node->args, context);
	}
	else
	{
		/* aggstar can be set only in zero-argument aggregates */
		if (node->aggstar)
			appendStringInfoChar(buf, '*');
		else
		{
			ListCell   *arg;
			bool		first = true;

			/* Add all the arguments */
			foreach(arg, node->args)
			{
				TargetEntry *tle = (TargetEntry *) lfirst(arg);
				Node	   *n = (Node *) tle->expr;

				if (tle->resjunk)
					continue;

				if (!first)
					appendStringInfoString(buf, ", ");
				first = false;

				/* Add VARIADIC */
				if (use_variadic && lnext(arg) == NULL)
					appendStringInfoString(buf, "VARIADIC ");

				deparseExpr((Expr *) n, context);
			}
		}

		/* Add ORDER BY */
		if (node->aggorder != NIL)
		{
			appendStringInfoString(buf, " ORDER BY ");
			appendAggOrderBy(node->aggorder, node->args, context);
		}
	}

	/* Add FILTER (WHERE ..) */
	if (node->aggfilter != NULL)
	{
		appendStringInfoString(buf, ") FILTER (WHERE ");
		deparseExpr((Expr *) node->aggfilter, context);
	}

	appendStringInfoChar(buf, ')');
}

/*
 * Append ORDER BY within aggregate function.
 */
static void
appendAggOrderBy(List *orderList, List *targetList, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	ListCell   *lc;
	bool		first = true;

	foreach(lc, orderList)
	{
		SortGroupClause *srt = (SortGroupClause *) lfirst(lc);
		Node	   *sortexpr;
		Oid			sortcoltype;
		TypeCacheEntry *typentry;

		if (!first)
			appendStringInfoString(buf, ", ");
		first = false;

		sortexpr = deparseSortGroupClause(srt->tleSortGroupRef, targetList,
										  context);
		sortcoltype = exprType(sortexpr);
		/* See whether operator is default < or > for datatype */
		typentry = lookup_type_cache(sortcoltype,
									 TYPECACHE_LT_OPR | TYPECACHE_GT_OPR);
		if (srt->sortop == typentry->lt_opr)
			appendStringInfoString(buf, " ASC");
		else if (srt->sortop == typentry->gt_opr)
			appendStringInfoString(buf, " DESC");
		else
		{
			HeapTuple	opertup;
			Form_pg_operator operform;

			appendStringInfoString(buf, " USING ");

			/* Append operator name. */
			opertup = SearchSysCache1(OPEROID, ObjectIdGetDatum(srt->sortop));
			if (!HeapTupleIsValid(opertup))
				elog(ERROR, "cache lookup failed for operator %u", srt->sortop);
			operform = (Form_pg_operator) GETSTRUCT(opertup);
			deparseOperatorName(buf, operform);
			ReleaseSysCache(opertup);
		}

		if (srt->nulls_first)
			appendStringInfoString(buf, " NULLS FIRST");
		else
			appendStringInfoString(buf, " NULLS LAST");
	}
}

/*
 * Print the representation of a parameter to be sent to the remote side.
 *
 * Note: we always label the Param's type explicitly rather than relying on
 * transmitting a numeric type OID in PQexecParams().  This allows us to
 * avoid assuming that types have the same OIDs on the remote side as they
 * do locally --- they need only have the same names.
 */
static void
printRemoteParam(int paramindex, Oid paramtype, int32 paramtypmod,
				 deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	appendStringInfo(buf, "$%d", paramindex);
}

/*
 * Print the representation of a placeholder for a parameter that will be
 * sent to the remote side at execution time.
 *
 * This is used when we're just trying to EXPLAIN the remote query.
 * We don't have the actual value of the runtime parameter yet, and we don't
 * want the remote planner to generate a plan that depends on such a value
 * anyway.  Thus, we can't do something simple like "$1::paramtype".
 * Instead, we emit "((SELECT null::paramtype)::paramtype)".
 * In all extant versions of Postgres, the planner will see that as an unknown
 * constant value, which is what we want.  This might need adjustment if we
 * ever make the planner flatten scalar subqueries.  Note: the reason for the
 * apparently useless outer cast is to ensure that the representation as a
 * whole will be parsed as an a_expr and not a select_with_parens; the latter
 * would do the wrong thing in the context "x = ANY(...)".
 */
static void
printRemotePlaceholder(Oid paramtype, int32 paramtypmod,
					   deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	appendStringInfo(buf, "(SELECT null)");
}

/*
 * Deparse GROUP BY clause.
 */
static void
appendGroupByClause(List *tlist, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	Query	   *query = context->root->parse;
	ListCell   *lc;
	bool		first = true;

	/* Nothing to be done, if there's no GROUP BY clause in the query. */
	if (!query->groupClause)
		return;

	appendStringInfo(buf, " GROUP BY ");

	/*
	 * Queries with grouping sets are not pushed down, so we don't expect
	 * grouping sets here.
	 */
	Assert(!query->groupingSets);

	foreach(lc, query->groupClause)
	{
		SortGroupClause *grp = (SortGroupClause *) lfirst(lc);

		if (!first)
			appendStringInfoString(buf, ", ");
		first = false;

		deparseSortGroupClause(grp->tleSortGroupRef, tlist, context);
	}
}

/*
 * Deparse ORDER BY clause according to the given pathkeys for given base
 * relation. From given pathkeys expressions belonging entirely to the given
 * base relation are obtained and deparsed.
 */
static void
appendOrderByClause(List *pathkeys, deparse_expr_cxt *context)
{
	ListCell   *lcell;
	int			nestlevel;
	char	   *delim = " ";
	RelOptInfo *baserel = context->scanrel;
	StringInfo	buf = context->buf;

	/* Make sure any constants in the exprs are printed portably */
	nestlevel = set_transmission_modes();

	appendStringInfo(buf, " ORDER BY");
	foreach(lcell, pathkeys)
	{
		PathKey    *pathkey = lfirst(lcell);
		Expr	   *em_expr;

		em_expr = find_em_expr_for_rel(pathkey->pk_eclass, baserel);
		Assert(em_expr != NULL);

		appendStringInfoString(buf, delim);
        appendStringInfoString(buf, " case ");
        deparseExpr(em_expr, context);
        appendStringInfoString(buf, " when null then 0 else 1 end ");
        appendStringInfoString(buf, pathkey->pk_nulls_first ?
                                    "ASC, " :
                                    "DESC, ");
		deparseExpr(em_expr, context);
		if (pathkey->pk_strategy == BTLessStrategyNumber)
			appendStringInfoString(buf, " ASC");
		else
			appendStringInfoString(buf, " DESC");

		// if (pathkey->pk_nulls_first)
		// 	appendStringInfoString(buf, " NULLS FIRST");
		// else
		// 	appendStringInfoString(buf, " NULLS LAST");

		delim = ", ";
	}
	reset_transmission_modes(nestlevel);
}

/*
 * appendFunctionName
 *		Deparses function name from given function oid.
 */
static void
appendFunctionName(Oid funcid, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	HeapTuple	proctup;
	Form_pg_proc procform;
	const char *proname;

	proctup = SearchSysCache1(PROCOID, ObjectIdGetDatum(funcid));
	if (!HeapTupleIsValid(proctup))
		elog(ERROR, "cache lookup failed for function %u from %s", 
                funcid, __func__);
	procform = (Form_pg_proc) GETSTRUCT(proctup);

	/* Print schema name only if it's not pg_catalog */
	if (procform->pronamespace != PG_CATALOG_NAMESPACE)
	{
		const char *schemaname;

		schemaname = get_namespace_name(procform->pronamespace);
		appendStringInfo(buf, "%s.", quote_identifier(schemaname));
	}

	/* Always print the function name */
	proname = NameStr(procform->proname);
	appendStringInfo(buf, "%s", quote_identifier(proname));

	ReleaseSysCache(proctup);
}

/*
 * Appends a sort or group clause.
 *
 * Like get_rule_sortgroupclause(), returns the expression tree, so caller
 * need not find it again.
 */
static Node *
deparseSortGroupClause(Index ref, List *tlist, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	TargetEntry *tle;
	Expr	   *expr;

	tle = get_sortgroupref_tle(ref, tlist);
	expr = tle->expr;

	if (expr && IsA(expr, Const))
	{
		/*
		 * Force a typecast here so that we don't emit something like "GROUP
		 * BY 2", which will be misconstrued as a column position rather than
		 * a constant.
		 */
		deparseConst((Const *) expr, context, 1);
	}
	else if (!expr || IsA(expr, Var))
		deparseExpr(expr, context);
	else
	{
		/* Always parenthesize the expression. */
		appendStringInfoString(buf, "(");
		deparseExpr(expr, context);
		appendStringInfoString(buf, ")");
	}

	return (Node *) expr;
}


/*
 * Returns true if given Var is deparsed as a subquery output column, in
 * which case, *relno and *colno are set to the IDs for the relation and
 * column alias to the Var provided by the subquery.
 */
static bool
is_subquery_var(Var *node, RelOptInfo *foreignrel, int *relno, int *colno)
{
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);
	RelOptInfo *outerrel = fpinfo->joinspec.outerrel;
	RelOptInfo *innerrel = fpinfo->joinspec.innerrel;

	/* Should only be called in these cases. */
	Assert(IS_SIMPLE_REL(foreignrel) || IS_JOIN_REL(foreignrel));

	/*
	 * If the given relation isn't a join relation, it doesn't have any lower
	 * subqueries, so the Var isn't a subquery output column.
	 */
	if (!IS_JOIN_REL(foreignrel))
		return false;

	/*
	 * If the Var doesn't belong to any lower subqueries, it isn't a subquery
	 * output column.
	 */
	if (!bms_is_member(node->varno, fpinfo->subqspec.lower_rels))
		return false;

	if (bms_is_member(node->varno, outerrel->relids))
	{
		/*
		 * If outer relation is deparsed as a subquery, the Var is an output
		 * column of the subquery; get the IDs for the relation/column alias.
		 */
		if (fpinfo->subqspec.make_outerrel)
		{
			get_relation_column_alias_ids(node, outerrel, relno, colno);
			return true;
		}

		/* Otherwise, recurse into the outer relation. */
		return is_subquery_var(node, outerrel, relno, colno);
	}
	else
	{
		Assert(bms_is_member(node->varno, innerrel->relids));

		/*
		 * If inner relation is deparsed as a subquery, the Var is an output
		 * column of the subquery; get the IDs for the relation/column alias.
		 */
		if (fpinfo->subqspec.make_innerrel)
		{
			get_relation_column_alias_ids(node, innerrel, relno, colno);
			return true;
		}

		/* Otherwise, recurse into the inner relation. */
		return is_subquery_var(node, innerrel, relno, colno);
	}
}

/*
 * Get the IDs for the relation and column alias to given Var belonging to
 * given relation, which are returned into *relno and *colno.
 */
static void
get_relation_column_alias_ids(Var *node, RelOptInfo *foreignrel,
							  int *relno, int *colno)
{
	SqliteFdwRelationInfo *fpinfo = FDW_RELINFO(foreignrel->fdw_private);
	int			i;
	ListCell   *lc;

	/* Get the relation alias ID */
	*relno = fpinfo->relation_index;

	/* Get the column alias ID */
	i = 1;
	foreach(lc, foreignrel->reltarget->exprs)
	{
		if (equal(lfirst(lc), (Node *) node))
		{
			*colno = i;
			return;
		}
		i++;
	}

	/* Shouldn't get here */
	elog(ERROR, "unexpected expression in subquery output");
}


static const char * 
get_colname__(int attrnum, Form_pg_attribute attr, Oid relid)
{
	ListCell   *lc;
    
    foreach(lc, GetForeignColumnOptions(relid, attrnum + 1))
    {
        DefElem    *def = (DefElem *) lfirst(lc);
        if (strcmp(def->defname, "column_name") == 0)
            return defGetString(def);
    }
    return NameStr(attr->attname);
}

StringInfoData
construct_foreignSamplesQuery(SqliteAnalyzeState *state)
{
    StringInfoData sql;
	TupleDesc	tupdesc = RelationGetDescr(state->relation);
	Oid			relid = RelationGetRelid(state->relation);
    int i = 0;
    bool first = true;

    initStringInfo(&sql);
	appendStringInfoString(&sql, "SELECT ");

    for ( i = 0; i < tupdesc->natts; i++ )
    {
		if (tupdesc->attrs[i]->attisdropped)
			continue;
		if (!first)
			appendStringInfoString(&sql, ", ");
		first = false;
		appendStringInfoString(&sql, 
                quote_identifier(get_colname__(i, tupdesc->attrs[i], relid)));
        state->retrieved_attrs = lappend_int(
                state->retrieved_attrs, i + 1);
    }
    
    return sql;
}
