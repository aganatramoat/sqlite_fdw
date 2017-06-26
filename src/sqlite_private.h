#ifndef SQLITE_FDW_PRIVATE_H
#define SQLITE_FDW_PRIVATE_H
// #pragma GCC visibility push(hidden)

#define SQLITE_FDW_LOG_LEVEL WARNING
#define DEFAULT_FDW_SORT_MULTIPLIER 1.2
#define DEFAULT_FDW_STARTUP_COST 100.0

typedef struct 
{
    bool import_notnull;
    bool import_default;
} SqliteTableImportOptions;


typedef struct 
{
    char   *database;
    char   *table;
} SqliteTableSource;


typedef struct 
{
	/* Cost and selectivity of local_conds. */
	QualCost	local_conds_cost;
	Selectivity local_conds_sel;
	
    /* Estimated size and cost for a scan or join. */
	double		rows;
	int			width;
	Cost		startup_cost;
	Cost		total_cost;
	
    /* Costs excluding costs for transferring data from the foreign server */
	Cost		rel_startup_cost;
	Cost		rel_total_cost;

    /* Other costs */
    Cost  fdw_startup_cost;
    Cost  fdw_tuple_cost;
} SqliteRelationCostSize;


typedef struct 
{
	double		rows;
	double		retrieved_rows;
	int			width;
	Cost		startup_cost;
    Cost		run_cost;
} SqliteCostEstimates;


typedef struct 
{
	/* Join information */
	RelOptInfo *outerrel;
	RelOptInfo *innerrel;
	JoinType	type;
	Selectivity clause_sel;
	
    /* clauses contains only JOIN/ON conditions for an outer join */
	List	   *clauses;	/* List of RestrictInfo */
} SqliteJoinSpec;


typedef struct 
{
	/* Subquery information */
	bool		make_outerrel;	/* do we deparse outerrel as a subquery? */
	bool		make_innerrel;	/* do we deparse innerrel as a subquery? */
	Relids		lower_rels;	    /* all relids appearing in lower subqueries */
} SqliteSubquerySpec;


typedef struct 
{
    // Filename (i.e. sqlite database ) and tablename
    SqliteTableSource src;
    struct sqlite3 *db;
    
    /* baserestrictinfo clauses, broken down into safe/unsafe */
	List	   *remote_conds;
	List	   *local_conds;
	
    /* Bitmap of attr numbers to fetch from the remote server. */
	Bitmapset  *attrs_used;
    bool       pushdown_safe;

    SqliteRelationCostSize costsize;
    SqliteJoinSpec         joinspec;
    SqliteSubquerySpec     subqspec;
	
    /* Grouping information */
	List	   *grouped_tlist;
	RelOptInfo *grouped_rel;
	
    /*
	 * Name of the relation while EXPLAINing ForeignScan. It is used for join
	 * relations but is set for all relations. For join relation, the name
	 * indicates which foreign tables are being joined and the join type used.
	 */
	StringInfo	relation_name;
	
    List	   *shippable_extensions;	/* OIDs of whitelisted extensions */

	/*
	 * Index of the relation.  It is used to create an alias to a subquery
	 * representing the relation.
	 */
    int relation_index;
} SqliteFdwRelationInfo;


/* Callback argument for ec_member_matches_foreign */
typedef struct
{
	Expr	   *current;		/* current expr, or NULL if not yet found */
	List	   *already_used;	/* expressions already dealt with */
} ec_member_foreign_arg;


typedef struct SqliteFdwExecutionState
{
	struct sqlite3 *db;
	struct sqlite3_stmt  *stmt;
	char          *query;
	List          *retrieved_attrs;   /* list of target attribute numbers */
} SqliteFdwExecutionState;


/*
 * Global context for foreign_expr_walker's search of an expression tree.
 */
typedef struct foreign_glob_cxt
{
	PlannerInfo *root;			/* global planner state */
	RelOptInfo *foreignrel;		/* the foreign relation we are planning for */
	Relids		relids;			/* relids of base relations in the underlying
								 * scan */
} foreign_glob_cxt;


/*
 * Local (per-tree-level) context for foreign_expr_walker's search.
 * This is concerned with identifying collations used in the expression.
 */
typedef enum
{
	FDW_COLLATE_NONE,			/* expression is of a noncollatable type, or
								 * it has default collation that is not
								 * traceable to a foreign Var */
	FDW_COLLATE_SAFE,			/* collation derives from a foreign Var */
	FDW_COLLATE_UNSAFE			/* collation is non-default and derives from
								 * something other than a foreign Var */
} FDWCollateState;


typedef struct foreign_loc_cxt
{
	Oid			collation;		/* OID of current collation, if any */
	FDWCollateState state;		/* state of current collation choice */
} foreign_loc_cxt;


// from shippable.c
bool is_builtin(Oid objectId);
bool is_shippable(Oid objectId, Oid classId, SqliteFdwRelationInfo *fpinfo);


// from deparse.c
List * build_tlist_to_deparse(RelOptInfo *foreignrel);
const char * get_jointype_name(JoinType jointype);
void deparseInsertSql(StringInfo buf, PlannerInfo *root,
				      Index rtindex, Relation rel,
				      List *targetAttrs, bool doNothing,
				      List *returningList, List **retrieved_attrs);
void deparseUpdateSql(StringInfo buf, PlannerInfo *root,
				      Index rtindex, Relation rel,
				      List *targetAttrs, List *returningList,
				      List **retrieved_attrs);
void deparseDirectUpdateSql(StringInfo buf, PlannerInfo *root,
					        Index rtindex, Relation rel,
					        List *targetlist,
					        List *targetAttrs,
					        List *remote_conds,
					        List **params_list,
					        List *returningList,
					        List **retrieved_attrs);
void deparseDeleteSql(StringInfo buf, PlannerInfo *root,
				      Index rtindex, Relation rel,
				      List *returningList,
				      List **retrieved_attrs);
void deparseDirectDeleteSql(StringInfo buf, PlannerInfo *root,
					        Index rtindex, Relation rel,
					        List *remote_conds,
					        List **params_list,
					        List *returningList,
					        List **retrieved_attrs);
void deparseAnalyzeSizeSql(StringInfo buf, Relation rel);
void deparseStringLiteral(StringInfo buf, const char *val);
void deparseAnalyzeSql(StringInfo buf, Relation rel, List **retrieved_attrs);
void deparseSelectStmtForRel(StringInfo buf, PlannerInfo *root, RelOptInfo *rel,
						List *tlist, List *remote_conds, List *pathkeys,
						bool is_subquery, List **retrieved_attrs,
						List **params_list);
bool foreign_expr_walker(Node *node, foreign_glob_cxt *glob_cxt,
					     foreign_loc_cxt *outer_cxt);


// from funcs.c
void add_pathsWithPathKeysForRel(PlannerInfo *root, RelOptInfo *rel,
                                     Path *epq_path);
void estimate_path_cost_size(PlannerInfo *root, RelOptInfo *baserel,
						     List *join_conds, List *pathkeys,
                             SqliteRelationCostSize *costs);
void sqlite_bind_param_values(SqliteFdwExecutionState *festate,
                              List *fdw_exprs, 
                              ForeignScanState * node);
void cleanup_(SqliteFdwExecutionState *);
SqliteTableSource get_tableSource(Oid foreigntableid);
struct sqlite3_stmt * prepare_sqliteQuery(struct sqlite3 *db, char *query, 
                                          const char **pzTail);
bool foreign_join_ok(PlannerInfo *root, RelOptInfo *joinrel, JoinType jointype,
				RelOptInfo *outerrel, RelOptInfo *innerrel,
				JoinPathExtraData *extra);
bool is_foreign_expr(PlannerInfo *root, RelOptInfo *baserel, Expr *expr);
void classifyConditions(PlannerInfo *root, RelOptInfo *baserel,
				        List *input_conds,
				        List **remote_conds, List **local_conds);
Datum make_datum(struct sqlite3_stmt *stmt, int col, Oid pgtyp, bool *isnull);
struct sqlite3 * get_sqliteDbHandle(char const *filename);
bool is_sqliteTableRequired(ImportForeignSchemaStmt *stmt, 
                            char const * tablename);
char *get_foreignTableCreationSql(ImportForeignSchemaStmt *stmt, 
                                  struct sqlite3 *db,
                                  char const * tablename,
                                  SqliteTableImportOptions options);
SqliteTableImportOptions get_sqliteTableImportOptions(
        ImportForeignSchemaStmt *stmt);
void sqlite_bind_param_value(SqliteFdwExecutionState *festate,
                        int index, Oid ptype, Datum pval, bool isNull);
void estimate_path_cost_size(PlannerInfo *root,
						RelOptInfo *foreignrel,
						List *param_join_conds,
						List *pathkeys,
                        SqliteRelationCostSize * store);
bool file_exists(const char *name);
void sqlite_bind_param_values(SqliteFdwExecutionState *festate, 
                              List *fdw_exprs, 
                              ForeignScanState *node);
void cleanup_(SqliteFdwExecutionState *festate);
void add_pathsWithPathKeysForRel(PlannerInfo *root, RelOptInfo *rel,
								 Path *epq_path);
List * get_useful_pathkeys_for_relation(PlannerInfo *root, RelOptInfo *rel);
bool ec_member_matches_foreign(PlannerInfo *root, RelOptInfo *rel,
						       EquivalenceClass *ec, EquivalenceMember *em,
						       void *arg);
int set_transmission_modes(void);
Expr * find_em_expr_for_rel(EquivalenceClass *ec, RelOptInfo *rel);
void reset_transmission_modes(int nestlevel);


// #pragma GCC visibility pop
#endif
