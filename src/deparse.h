#ifndef SQLITE_FDW_DEPARSE_H
#define SQLITE_FDW_DEPARSE_H


bool is_foreignExpr(PlannerInfo *root, RelOptInfo *baserel, Expr *expr);
void deparse_selectStmtForRel(StringInfo buf, PlannerInfo *root, RelOptInfo *rel,
						 List *tlist, List *remote_conds, List *pathkeys,
						 bool is_subquery, List **retrieved_attrs,
						 List **params_list);
void append_whereClause(StringInfo buf, PlannerInfo *root, RelOptInfo *baserel,
                        List *exprs, bool is_first, List **params); 

#endif
