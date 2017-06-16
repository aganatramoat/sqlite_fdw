#ifndef SQLITE_FDW_PRIVATE_H
#define SQLITE_FDW_PRIVATE_H


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
} SqliteRelationCosts;


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

    SqliteRelationCosts costs;
    SqliteJoinSpec      joinspec;
    SqliteSubquerySpec  subqspec;
	
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

// from sqlite_fdw.c
int set_transmission_modes(void);
void reset_transmission_modes(int nestlevel);
Expr * find_em_expr_for_rel(EquivalenceClass *ec, RelOptInfo *rel);

#endif
