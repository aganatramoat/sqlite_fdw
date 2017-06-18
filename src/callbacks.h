#ifndef SQLITE_FDW_CALLBACKS_H
#define SQLITE_FDW_CALLBACKS_H
#pragma GCC visibility push(hidden)

void get_foreignPaths(PlannerInfo *root, RelOptInfo *baserel, 
                      Oid foreigntableid);
void get_foreignRelSize(PlannerInfo *root, RelOptInfo *baserel, 
                        Oid foreigntableid);
ForeignScan * get_foreignPlan(PlannerInfo *root, RelOptInfo *baserel,
                Oid foreigntableoid, ForeignPath *best_path,
                List *tlist, List *scan_clauses, Plan *outer_plan);
void get_foreignJoinPaths(PlannerInfo *root, RelOptInfo *joinrel,
                          RelOptInfo *outerrel, RelOptInfo *innerrel,
                          JoinType jointype, JoinPathExtraData *extra);
void begin_foreignScan(ForeignScanState *node, int eflags);

#pragma GCC visibility pop
#endif
