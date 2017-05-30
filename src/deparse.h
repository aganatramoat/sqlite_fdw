#ifndef SQLITE_FDW_DEPARSE_H
#define SQLITE_FDW_DEPARSE_H


bool is_foreignExpr(PlannerInfo *root, 
                    RelOptInfo *baserel, Expr *expr);
void deparse_selectStmt(StringInfo buf,
                        PlannerInfo *root, 
                        RelOptInfo *baserel,
                        Bitmapset *attrs_used, 
                        char *svr_table, 
                        List **retrieved_attrs);
void append_whereClause(StringInfo buf,
                        PlannerInfo *root, 
                        RelOptInfo *baserel,
                        List *exprs, 
                        bool is_first, 
                        List **params);

#endif
