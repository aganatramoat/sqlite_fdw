#ifndef SQLITE_FDW_CALLBACKS_H
#define SQLITE_FDW_CALLBACKS_H
// #pragma GCC visibility push(hidden)

void get_foreignPaths(PlannerInfo *root, RelOptInfo *baserel, 
                      Oid foreigntableid);
void get_foreignJoinPaths(PlannerInfo *root, RelOptInfo *joinrel,
                          RelOptInfo *outerrel, RelOptInfo *innerrel,
                          JoinType jointype, JoinPathExtraData *extra);
void get_foreignUpperPaths(PlannerInfo *root, UpperRelationKind stage,
                           RelOptInfo *input_rel, RelOptInfo *output_rel);

void get_foreignRelSize(PlannerInfo *root, RelOptInfo *baserel, 
                        Oid foreigntableid);
ForeignScan * get_foreignPlan(PlannerInfo *root, RelOptInfo *baserel,
                Oid foreigntableoid, ForeignPath *best_path,
                List *tlist, List *scan_clauses, Plan *outer_plan);

void begin_foreignScan(ForeignScanState *node, int eflags);
TupleTableSlot * iterate_foreignScan(ForeignScanState *node);
void end_foreignScan(ForeignScanState *node);
void rescan_foreignScan(ForeignScanState *node);
void explain_foreignScan(ForeignScanState *node, struct ExplainState *es);

List * import_foreignSchema(ImportForeignSchemaStmt *stmt, Oid serverOid);
bool analyze_foreignTable(Relation relation, AcquireSampleRowsFunc *func,
                          BlockNumber *totalpages);

// #pragma GCC visibility pop
#endif
