#ifndef SQLITE_FDW_CALLBACKS_H
#define SQLITE_FDW_CALLBACKS_H
// #pragma GCC visibility push(hidden)

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
List * import_foreignSchema(ImportForeignSchemaStmt *stmt, Oid serverOid);
void explain_foreignScan(ForeignScanState *node, struct ExplainState *es);
bool analyze_foreignTable(Relation relation, AcquireSampleRowsFunc *func,
                          BlockNumber *totalpages);
void explain_foreignModify(ModifyTableState *mtstate, ResultRelInfo *rinfo,
                           List *fdw_private, int subplan_index,
                           struct ExplainState *es);
TupleTableSlot * iterate_foreignScan(ForeignScanState *node);
void end_foreignModify(EState *estate, ResultRelInfo *rinfo);
void begin_foreignModify(ModifyTableState *mtstate,
							ResultRelInfo *rinfo,
							List *fdw_private,
							int subplan_index,
							int eflags);
TupleTableSlot * exec_foreignInsert(EState *estate, ResultRelInfo *rinfo,
						            TupleTableSlot *slot, 
                                    TupleTableSlot *planSlot);
void end_foreignScan(ForeignScanState *node);
TupleTableSlot * exec_foreignDelete(EState *estate,
						   ResultRelInfo *rinfo,
						   TupleTableSlot *slot,
						   TupleTableSlot *planSlot);
List * plan_foreignModify(PlannerInfo *root,
						   ModifyTable *plan,
						   Index resultRelation,
						   int subplan_index);
void rescan_foreignScan(ForeignScanState *node);
void add_foreignUpdateTargets(Query *parsetree,
                              RangeTblEntry *target_rte,
                              Relation target_relation);
TupleTableSlot *
exec_foreginUpdate(EState *estate,
						   ResultRelInfo *rinfo,
						   TupleTableSlot *slot,
						   TupleTableSlot *planSlot);
void get_foreignUpperPaths(PlannerInfo *root, UpperRelationKind stage,
                           RelOptInfo *input_rel, RelOptInfo *output_rel);

// #pragma GCC visibility pop
#endif
