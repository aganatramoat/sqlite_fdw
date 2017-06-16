#ifndef SQLITE_FDW_DEPARSE_H
#define SQLITE_FDW_DEPARSE_H


bool is_foreign_expr(PlannerInfo *root, RelOptInfo *baserel, Expr *expr);
void deparseSelectStmtForRel(StringInfo buf, PlannerInfo *root, RelOptInfo *rel,
						List *tlist, List *remote_conds, List *pathkeys,
						bool is_subquery, List **retrieved_attrs,
						List **params_list);
void classifyConditions(PlannerInfo *root, RelOptInfo *baserel,
				   List *input_conds,
				   List **remote_conds,
				   List **local_conds);

#endif
