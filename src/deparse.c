
#include <postgres.h>
#include <pgtime.h>
#include <lib/stringinfo.h>
#include <parser/parsetree.h>
#include <nodes/relation.h>
#include <nodes/nodeFuncs.h>
#include <foreign/foreign.h>
#include <commands/defrem.h>
#include <utils/lsyscache.h>
#include <utils/syscache.h>
#include <utils/relcache.h>
#include <utils/rel.h>
#include <utils/timestamp.h>
#include <access/heapam.h>
#include <access/sysattr.h>
#include <access/htup_details.h>
#include <catalog/pg_type.h>
#include <catalog/pg_proc.h>
#include <catalog/pg_operator.h>
#include <catalog/pg_namespace.h>
#include <catalog/pg_collation.h>
#include <sqlite3.h>

#include "sqlite_fdw.h"
#include "deparse.h"


/*
 * Context for deparse_expr__
 */
typedef struct DeparseExprCxt__
{
	PlannerInfo *root;		/* global planner state */
	RelOptInfo *foreignrel;	/* the foreign relation we are planning for */
	StringInfo	buf;		/* output buffer to append to */
	List	**params_list;	/* exprs that will become remote Params */
} DeparseExprCxt__;


/*
 * Local (per-tree-level) context for walk_foreignExpr__'s search.
 * This is concerned with identifying collations used in the expression.
 */
typedef enum
{
	FDW_COLLATE_NONE,	/* expression is of a noncollatable type */
	FDW_COLLATE_SAFE,	/* collation derives from a foreign Var */
	FDW_COLLATE_UNSAFE	/* collation derives from something else */
} FDWCollateState;


/*
 * Global context for walk_foreignExpr__'s search of an expression tree.
 */
typedef struct GlobalCxt__
{
	PlannerInfo *root;		/* global planner state */
	RelOptInfo *foreignrel;	/* the foreign relation we are planning for */
} GlobalCxt__;


typedef struct LocalCxt__
{
	Oid			collation;		/* OID of current collation, if any */
	FDWCollateState state;		/* state of current collation choice */
} LocalCxt__;


static char *quote_identifier__(const char *s, char q);

static void deparse_columnRef__(StringInfo buf, int varno, int varattno, 
                                PlannerInfo *root);
static void deparse_targetList__(StringInfo buf, PlannerInfo *root, 
                                 Index rtindex,
                                 Relation rel, 
                                 Bitmapset *attrs_used, 
                                 List **retrieved_attrs);
static void deparse_relaltion__(StringInfo buf, Relation rel);
static void deparse_interval(StringInfo buf, Datum datum);
static void deparse_expr__(Expr *expr, DeparseExprCxt__ *context);
static void deparse_var__(Var *, DeparseExprCxt__ *);
static void deparse_const__(Const *, DeparseExprCxt__ *);
static void deparse_boolExpr__(BoolExpr *, DeparseExprCxt__ *);
static void deparse_nullTest__(NullTest *, DeparseExprCxt__ *);
static void deparse_param__(Param *, DeparseExprCxt__ *);
static void deparse_funcExpr__(FuncExpr *, DeparseExprCxt__ *);
static void deparse_arrayRef__(ArrayRef *, DeparseExprCxt__ *);
static void deparse_opExpr__(OpExpr *, DeparseExprCxt__ *);
static void deparse_distinctExpr__(DistinctExpr *, DeparseExprCxt__ *);
static void deparse_scalarArrayOpExpr__(ScalarArrayOpExpr *, DeparseExprCxt__ *);
static void deparse_relabelType__(RelabelType *, DeparseExprCxt__ *);
static void deparse_arrayExpr__(ArrayExpr *, DeparseExprCxt__ *);
static void print_remoteParam__(int paramindex, DeparseExprCxt__ *context);
static void print_remotePlaceholder__(DeparseExprCxt__ *context);
static void deparse_stringLiteral__(StringInfo buf, const char *val);
static char* replace_function__(char *in);
static void deparse_operatorName__(StringInfo buf, Form_pg_operator opform);
static void deparse_string__(StringInfo buf, const char *val, 
                             bool isstr);
static bool walk_foreignExpr__(Node *node, GlobalCxt__ *glob_cxt, 
                               LocalCxt__ *outer_cxt);
static bool is_builtin(Oid oid);

/*
 * Local variables.
 */
static char *cur_opname = NULL;


static char *
quote_identifier__(const char *s , char q)
{
	char  *result = palloc(strlen(s) * 2 + 3);
	char  *r = result;

	*r++ = q;
	while (*s)
	{
		if (*s == q)
			*r++ = *s;
		*r++ = *s;
		s++;
	}
	*r++ = q;
	*r++ = '\0';
	return result;
}



/*
 * Construct name to use for given column, and emit it into buf.
 * If it has a column_name FDW option, use that instead of attribute name.
 */
static void
deparse_columnRef__(StringInfo buf, 
                    int varno, 
                    int varattno, 
                    PlannerInfo *root)
{
	RangeTblEntry *rte;
	char          *colname = NULL;
	List          *options;
	ListCell      *lc;

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
		DefElem *def = (DefElem *) lfirst(lc);

		if (strcmp(def->defname, "column_name") == 0)
		{
			colname = defGetString(def);
			break;
		}
	}

	/*
	 * If it's a column of a regular table or it doesn't have column_name FDW
	 * option, use attribute name.
	 */
	if (colname == NULL)
		colname = get_relid_attribute_name(rte->relid, varattno);

	appendStringInfoString(buf, quote_identifier__(colname, '`'));
}


/*
 * Emit a target list that retrieves the columns specified in attrs_used.
 * This is used for both SELECT and RETURNING targetlists.
 */
static void
deparse_targetList__(StringInfo buf,
				     PlannerInfo *root,
				     Index rtindex,
				     Relation rel,
				     Bitmapset *attrs_used,
				     List **retrieved_attrs)
{
	TupleDesc	tupdesc = RelationGetDescr(rel);
	bool		have_wholerow;
	bool		first;
	int			i;

	/* If there's a whole-row reference, we'll need all the columns. */
	have_wholerow = bms_is_member(0 - FirstLowInvalidHeapAttributeNumber,
								  attrs_used);

	first = true;
	
	*retrieved_attrs = NIL;
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
			first = false;

			deparse_columnRef__(buf, rtindex, i, root);
			*retrieved_attrs = lappend_int(*retrieved_attrs, i);
		}
	}

	/* Don't generate bad syntax if no undropped columns */
	if (first)
		appendStringInfoString(buf, "NULL");
}


void
deparse_selectStmt(StringInfo buf,
				 PlannerInfo *root,
				 RelOptInfo *baserel,
				 Bitmapset *attrs_used,
				 char *svr_table, List **retrieved_attrs)
{
	RangeTblEntry *rte = planner_rt_fetch(baserel->relid, root);
	Relation	rel;

	/*
	 * Core code already has some lock on each rel being planned, so we can
	 * use NoLock here.
	 */
	rel = heap_open(rte->relid, NoLock);

	appendStringInfoString(buf, "SELECT ");
	deparse_targetList__(buf, root, baserel->relid, rel, attrs_used, retrieved_attrs);

	/*
	 * Construct FROM clause
	 */
	appendStringInfoString(buf, " FROM ");
	deparse_relaltion__(buf, rel);
	heap_close(rel, NoLock);
}


/*
 * Append remote name of specified foreign table to buf.
 * Use value of table_name FDW option (if any) instead of relation's name.
 * Similarly, schema_name FDW option overrides schema name.
 */
static void
deparse_relaltion__(StringInfo buf, Relation rel)
{
	ForeignTable  *table;
	const char    *nspname = NULL;
	const char    *relname = NULL;
	ListCell      *lc = NULL;

	/* obtain additional catalog information. */
	table = GetForeignTable(RelationGetRelid(rel));

	/*
	 * Use value of FDW options if any, instead of the name of object itself.
	 */
	foreach(lc, table->options)
	{
		DefElem *def = (DefElem *) lfirst(lc);

		if (strcmp(def->defname, "dbname") == 0)
			nspname = defGetString(def);
		else if (strcmp(def->defname, "table_name") == 0)
			relname = defGetString(def);
	}

	/*
	 * Note: we could skip printing the schema name if it's pg_catalog, but
	 * that doesn't seem worth the trouble.
	 */
	if (nspname == NULL)
		nspname = get_namespace_name(RelationGetNamespace(rel));
	if (relname == NULL)
		relname = RelationGetRelationName(rel);

	appendStringInfo(buf, "%s.%s", 
        quote_identifier__(nspname, '`'), 
        quote_identifier__(relname, '`'));
}

    
void
append_whereClause(StringInfo buf,
				  PlannerInfo *root,
				  RelOptInfo *baserel,
				  List *exprs,
				  bool is_first,
				  List **params)
{
	DeparseExprCxt__ context;
	ListCell   *lc;

	if (params)
		*params = NIL;			/* initialize result list to empty */

	/* Set up context struct for recursion */
	context.root = root;
	context.foreignrel = baserel;
	context.buf = buf;
	context.params_list = params;

	foreach(lc, exprs)
	{
		RestrictInfo *ri = (RestrictInfo *) lfirst(lc);

		/* Connect expressions with "AND" and parenthesize each condition. */
		if (is_first)
			appendStringInfoString(buf, " WHERE ");
		else
			appendStringInfoString(buf, " AND ");

		appendStringInfoChar(buf, '(');
		deparse_expr__(ri->clause, &context);
		appendStringInfoChar(buf, ')');

		is_first = false;
	}
}


/*
 * Deparse given expression into context->buf.
 *
 * This function must support all the same node types that walk_foreignExpr__
 * accepts.
 *
 * Note: unlike ruleutils.c, we just use a simple hard-wired parenthesization
 * scheme: anything more complex than a Var, Const, function call or cast
 * should be self-parenthesized.
 */
static void
deparse_expr__(Expr *node, DeparseExprCxt__ *context)
{
	if (node == NULL)
		return;

	switch (nodeTag(node))
	{
		case T_Var:
			deparse_var__((Var *) node, context);
			break;
		case T_Const:
			deparse_const__((Const *) node, context);
			break;
		case T_Param:
			deparse_param__((Param *) node, context);
			break;
		case T_ArrayRef:
			deparse_arrayRef__((ArrayRef *) node, context);
			break;
		case T_FuncExpr:
			deparse_funcExpr__((FuncExpr *) node, context);
			break;
		case T_OpExpr:
			deparse_opExpr__((OpExpr *) node, context);
			break;
		case T_DistinctExpr:
			deparse_distinctExpr__((DistinctExpr *) node, context);
			break;
		case T_ScalarArrayOpExpr:
			deparse_scalarArrayOpExpr__((ScalarArrayOpExpr *) node, context);
			break;
		case T_RelabelType:
			deparse_relabelType__((RelabelType *) node, context);
			break;
		case T_BoolExpr:
			deparse_boolExpr__((BoolExpr *) node, context);
			break;
		case T_NullTest:
			deparse_nullTest__((NullTest *) node, context);
			break;
		case T_ArrayExpr:
			deparse_arrayExpr__((ArrayExpr *) node, context);
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
deparse_var__(Var *node, DeparseExprCxt__ *context)
{
	StringInfo	buf = context->buf;

	if (node->varno == context->foreignrel->relid &&
		node->varlevelsup == 0)
	{
		/* Var belongs to foreign table */
		deparse_columnRef__(buf, node->varno, node->varattno, context->root);
	}
	else
	{
		/* Treat like a Param */
		if (context->params_list)
		{
			int pindex = 0;
			ListCell *lc;

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
			print_remoteParam__(pindex, context);
		}
		else
		{
			print_remotePlaceholder__(context);
		}
	}
}


/*
 * Deparse given constant value into context->buf.
 *
 * This function has to be kept in sync with ruleutils.c's get_const_expr.
 */
static void
deparse_const__(Const *node, DeparseExprCxt__ *context)
{
	StringInfo  buf = context->buf;
	Oid         typoutput;
	bool        typIsVarlena;
	char        *extval;

	if (node->constisnull)
	{
		appendStringInfoString(buf, "NULL");
		return;
	}

	getTypeOutputInfo(node->consttype,
					  &typoutput, &typIsVarlena);

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
				extval = OidOutputFunctionCall(typoutput, node->constvalue);
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
				}
				else
					appendStringInfo(buf, "'%s'", extval);
			}
			break;
		case BITOID:
		case VARBITOID:
			extval = OidOutputFunctionCall(typoutput, node->constvalue);
			appendStringInfo(buf, "B'%s'", extval);
			break;
		case BOOLOID:
			extval = OidOutputFunctionCall(typoutput, node->constvalue);
			if (strcmp(extval, "t") == 0)
				appendStringInfoString(buf, "true");
			else
				appendStringInfoString(buf, "false");
			break;
		case INTERVALOID:
			deparse_interval(buf, node->constvalue);
			break;
		default:
			extval = OidOutputFunctionCall(typoutput, node->constvalue);
			deparse_stringLiteral__(buf, extval);
			break;
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
deparse_param__(Param *node, DeparseExprCxt__ *context)
{
	if (context->params_list)
	{
		int pindex = 0;
		ListCell *lc;

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

		print_remoteParam__(pindex, context);
	}
	else
	{
		print_remotePlaceholder__(context);
	}
}


/*
 * Deparse a function call.
 */
static void
deparse_funcExpr__(FuncExpr *node, DeparseExprCxt__ *context)
{
	StringInfo     buf = context->buf;
	HeapTuple      proctup;
	Form_pg_proc   procform;
	const char     *proname;
	bool           first;
	ListCell       *arg;

	/*
	 * Normal function: display as proname(args).
	 */
	proctup = SearchSysCache1(PROCOID, ObjectIdGetDatum(node->funcid));
	if (!HeapTupleIsValid(proctup))
		elog(ERROR, "cache lookup failed for function %u", node->funcid);
	procform = (Form_pg_proc) GETSTRUCT(proctup);

	/* Translate PostgreSQL function into mysql function */
	proname = replace_function__(NameStr(procform->proname));

	/* Deparse the function name ... */
	appendStringInfo(buf, "%s(", proname);
	
	/* ... and all the arguments */
	first = true;
	foreach(arg, node->args)
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		deparse_expr__((Expr *) lfirst(arg), context);
		first = false;
	}
	appendStringInfoChar(buf, ')');
	ReleaseSysCache(proctup);
}


/*
 * Deparse an array subscript expression.
 */
static void
deparse_arrayRef__(ArrayRef *node, DeparseExprCxt__ *context)
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
		deparse_expr__(node->refexpr, context);
	else
	{
		appendStringInfoChar(buf, '(');
		deparse_expr__(node->refexpr, context);
		appendStringInfoChar(buf, ')');
	}

	/* Deparse subscript expressions. */
	lowlist_item = list_head(node->reflowerindexpr);	/* could be NULL */
	foreach(uplist_item, node->refupperindexpr)
	{
		appendStringInfoChar(buf, '[');
		if (lowlist_item)
		{
			deparse_expr__(lfirst(lowlist_item), context);
			appendStringInfoChar(buf, ':');
			lowlist_item = lnext(lowlist_item);
		}
		deparse_expr__(lfirst(uplist_item), context);
		appendStringInfoChar(buf, ']');
	}

	appendStringInfoChar(buf, ')');
}


/*
 * Deparse given operator expression.   To avoid problems around
 * priority of operations, we always parenthesize the arguments.
 */
static void
deparse_opExpr__(OpExpr *node, DeparseExprCxt__ *context)
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
		deparse_expr__(lfirst(arg), context);
		appendStringInfoChar(buf, ' ');
	}

	/* Deparse operator name. */
	deparse_operatorName__(buf, form);

	/* Deparse right operand. */
	if (oprkind == 'l' || oprkind == 'b')
	{
		arg = list_tail(node->args);
		appendStringInfoChar(buf, ' ');
		deparse_expr__(lfirst(arg), context);
	}

	appendStringInfoChar(buf, ')');

	ReleaseSysCache(tuple);
}


/*
 * Deparse IS DISTINCT FROM.
 */
static void
deparse_distinctExpr__(DistinctExpr *node, DeparseExprCxt__ *context)
{
	StringInfo	buf = context->buf;

	Assert(list_length(node->args) == 2);

	appendStringInfoChar(buf, '(');
	deparse_expr__(linitial(node->args), context);
	appendStringInfoString(buf, " IS DISTINCT FROM ");
	deparse_expr__(lsecond(node->args), context);
	appendStringInfoChar(buf, ')');
}


/*
 * Deparse given ScalarArrayOpExpr expression.  To avoid problems
 * around priority of operations, we always parenthesize the arguments.
 */
static void
deparse_scalarArrayOpExpr__(ScalarArrayOpExpr *node, DeparseExprCxt__ *context)
{
	StringInfo        buf = context->buf;
	HeapTuple         tuple;
	Expr              *arg1;
	Expr              *arg2;
	Form_pg_operator  form;
	char              *opname;
	Oid               typoutput;
	bool              typIsVarlena;
	char              *extval;

	/* Retrieve information about the operator from system catalog. */
	tuple = SearchSysCache1(OPEROID, ObjectIdGetDatum(node->opno));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for operator %u", node->opno);
	form = (Form_pg_operator) GETSTRUCT(tuple);

	/* Sanity check. */
	Assert(list_length(node->args) == 2);

	/* Deparse left operand. */
	arg1 = linitial(node->args);
	deparse_expr__(arg1, context);
	appendStringInfoChar(buf, ' ');

	opname = NameStr(form->oprname);
	if (strcmp(opname, "<>") == 0)
		appendStringInfo(buf, " NOT ");

	/* Deparse operator name plus decoration. */
	appendStringInfo(buf, " IN (");

	/* Deparse right operand. */
	arg2 = lsecond(node->args);
	switch (nodeTag((Node*)arg2))
	{
		case T_Const:
		{
			Const *c = (Const*)arg2;
			if (!c->constisnull)
			{
				getTypeOutputInfo(c->consttype,
								&typoutput, &typIsVarlena);
				extval = OidOutputFunctionCall(typoutput, c->constvalue);

				switch (c->consttype)
				{
					case INT4ARRAYOID:
					case OIDARRAYOID:
						deparse_string__(buf, extval, false);
						break;
					default:
						deparse_string__(buf, extval, true);
						break;
				}
			}
			else
			{
				appendStringInfoString(buf, " NULL");
				return;
			}
		}
		break;
		default:
			deparse_expr__(arg2, context);
			break;
	}
	appendStringInfoChar(buf, ')');
	ReleaseSysCache(tuple);
}


/*
 * Deparse a RelabelType (binary-compatible cast) node.
 */
static void
deparse_relabelType__(RelabelType *node, DeparseExprCxt__ *context)
{
	deparse_expr__(node->arg, context);
}


/*
 * Deparse a BoolExpr node.
 *
 * Note: by the time we get here, AND and OR expressions have been flattened
 * into N-argument form, so we'd better be prepared to deal with that.
 */
static void
deparse_boolExpr__(BoolExpr *node, DeparseExprCxt__ *context)
{
	StringInfo	buf = context->buf;
	const char *op = NULL;		/* keep compiler quiet */
	bool		first;
	ListCell *lc;

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
			deparse_expr__(linitial(node->args), context);
			appendStringInfoChar(buf, ')');
			return;
	}

	appendStringInfoChar(buf, '(');
	first = true;
	foreach(lc, node->args)
	{
		if (!first)
			appendStringInfo(buf, " %s ", op);
		deparse_expr__((Expr *) lfirst(lc), context);
		first = false;
	}
	appendStringInfoChar(buf, ')');
}


/*
 * Deparse IS [NOT] NULL expression.
 */
static void
deparse_nullTest__(NullTest *node, DeparseExprCxt__ *context)
{
	StringInfo	buf = context->buf;

	appendStringInfoChar(buf, '(');
	deparse_expr__(node->arg, context);
	if (node->nulltesttype == IS_NULL)
		appendStringInfoString(buf, " IS NULL)");
	else
		appendStringInfoString(buf, " IS NOT NULL)");
}


/*
 * Deparse ARRAY[...] construct.
 */
static void
deparse_arrayExpr__(ArrayExpr *node, DeparseExprCxt__ *context)
{
	StringInfo	buf = context->buf;
	bool		first = true;
	ListCell   *lc;

	appendStringInfoString(buf, "ARRAY[");
	foreach(lc, node->elements)
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		deparse_expr__(lfirst(lc), context);
		first = false;
	}
	appendStringInfoChar(buf, ']');
}


/*
 * Print the representation of a parameter to be sent to sqlite.
 */
static void
print_remoteParam__(int paramindex, DeparseExprCxt__ *context)
{
	appendStringInfo(context->buf, "?%d", paramindex);
}

    
static void
print_remotePlaceholder__(DeparseExprCxt__ *context)
{
	StringInfo	buf = context->buf;
	appendStringInfo(buf, "(SELECT null)");
}


/*
 * Deparse Interval type into MySQL Interval representation.
 */
static void
deparse_interval(StringInfo buf, Datum datum)
{
	struct pg_tm tm;
	fsec_t		fsec;
	bool		is_first = true;

#define append_interval(expr, unit) \
do { \
	if (!is_first) \
		appendStringInfo(buf, " %s ", cur_opname); \
	appendStringInfo(buf, "INTERVAL %d %s", expr, unit); \
	is_first = false; \
} while (0)

	/* Check saved opname. It could be only "+" and "-" */
	Assert(cur_opname);

	if (interval2tm(*DatumGetIntervalP(datum), &tm, &fsec) != 0)
		elog(ERROR, "could not convert interval to tm");

	if (tm.tm_year > 0)
		append_interval(tm.tm_year, "YEAR");

	if (tm.tm_mon > 0)
		append_interval(tm.tm_mon, "MONTH");

	if (tm.tm_mday > 0)
		append_interval(tm.tm_mday, "DAY");

	if (tm.tm_hour > 0)
		append_interval(tm.tm_hour, "HOUR");

	if (tm.tm_min > 0)
		append_interval(tm.tm_min, "MINUTE");

	if (tm.tm_sec > 0)
		append_interval(tm.tm_sec, "SECOND");

	if (fsec > 0)
	{
		if (!is_first)
			appendStringInfo(buf, " %s ", cur_opname);
#ifdef HAVE_INT64_TIMESTAMP
		appendStringInfo(buf, "INTERVAL %d MICROSECOND", fsec);
#else
		appendStringInfo(buf, "INTERVAL %f MICROSECOND", fsec);
#endif
	}
}


/*
* Append a SQL string literal representing "val" to buf.
*/
static void
deparse_stringLiteral__(StringInfo buf, const char *val)
{
	const char *valptr;
	appendStringInfoChar(buf, '\'');
	for (valptr = val; *valptr; valptr++)
	{
		char	ch = *valptr;
		if (SQL_STR_DOUBLE(ch, true))
		appendStringInfoChar(buf, ch);
		appendStringInfoChar(buf, ch);
	}
	appendStringInfoChar(buf, '\'');
}


/*
 * This possible that name of function in PostgreSQL and
 * mysql differ, so return the mysql equelent function name
 */
static char*
replace_function__(char *in)
{
	if (strcmp(in, "btrim") == 0)
	{
		return "trim";
	}
	return in;
}


/*
 * Print the name of an operator.
 */
static void
deparse_operatorName__(StringInfo buf, Form_pg_operator opform)
{
	/* opname is not a SQL identifier, so we should not quote it. */
	cur_opname = NameStr(opform->oprname);

	/* Print schema name only if it's not pg_catalog */
	if (opform->oprnamespace != PG_CATALOG_NAMESPACE)
	{
		const char *opnspname;

		opnspname = get_namespace_name(opform->oprnamespace);
		/* Print fully qualified operator name. */
		appendStringInfo(buf, "OPERATOR(%s.%s)",
						 quote_identifier__(opnspname, '`'), cur_opname);
	}
	else
	{
		if (strcmp(cur_opname, "~~") == 0)
		{
			appendStringInfoString(buf, "LIKE BINARY");
		}
		else if (strcmp(cur_opname, "~~*") == 0)
		{
			appendStringInfoString(buf, "LIKE");
		}
		else if (strcmp(cur_opname, "!~~") == 0)
		{
			appendStringInfoString(buf, "NOT LIKE BINARY");
		}
		else if (strcmp(cur_opname, "!~~*") == 0)
		{
			appendStringInfoString(buf, "NOT LIKE");
		}
		else if (strcmp(cur_opname, "~") == 0)
		{
			appendStringInfoString(buf, "REGEXP BINARY");
		}
		else if (strcmp(cur_opname, "~*") == 0)
		{
			appendStringInfoString(buf, "REGEXP");
		}
		else if (strcmp(cur_opname, "!~") == 0)
		{
			appendStringInfoString(buf, "NOT REGEXP BINARY");
		}
		else if (strcmp(cur_opname, "!~*") == 0)
		{
			appendStringInfoString(buf, "NOT REGEXP");
		}
		else
		{
			appendStringInfoString(buf, cur_opname);
		}
	}
}

    
static void
deparse_string__(StringInfo buf, const char *val, bool isstr)
{
	const char *valptr;
	int i = -1;

	for (valptr = val; *valptr; valptr++)
	{
		char ch = *valptr;
		i++;

		if (i == 0 && isstr)
			appendStringInfoChar(buf, '\'');

		/*
		 * Remove '{', '}' and \" character from the string. Because
		 * this syntax is not recognize by the remote MySQL server.
		 */
		if ((ch == '{' && i == 0) || (ch == '}' && (i == (strlen(val) - 1))) || ch == '\"')
			continue;

		if (ch == ',' && isstr)
		{
			appendStringInfoChar(buf, '\'');
			appendStringInfoChar(buf, ch);
			appendStringInfoChar(buf, ' ');
			appendStringInfoChar(buf, '\'');
			continue;
		}
		appendStringInfoChar(buf, ch);
	}
	if (isstr)
		appendStringInfoChar(buf, '\'');
}

/*
 * Returns true if given expr is safe to evaluate on the foreign server.
 */
bool
is_foreignExpr(PlannerInfo *root,
                RelOptInfo *baserel,
                Expr *expr)
{
    GlobalCxt__ glob_cxt;
    LocalCxt__ loc_cxt;

    /*
     * Check that the expression consists of nodes that are safe to 
     * execute remotely.
     */
    glob_cxt.root = root;
    glob_cxt.foreignrel = baserel;
    loc_cxt.collation = InvalidOid;
    loc_cxt.state = FDW_COLLATE_NONE;
    if (!walk_foreignExpr__((Node *) expr, &glob_cxt, &loc_cxt))
            return false;

    /* Expressions examined here should be boolean, ie noncollatable */
    Assert(loc_cxt.collation == InvalidOid);
    Assert(loc_cxt.state == FDW_COLLATE_NONE);

    /* OK to evaluate on the remote server */
    return true;
}


/*
 * Check if expression is safe to execute remotely, and return true if so.
 *
 * In addition, *outer_cxt is updated with collation information.
 *
 * We must check that the expression contains only node types we can deparse,
 * that all types/functions/operators are safe to send (which we approximate
 * as being built-in), and that all collations used in the expression derive
 * from Vars of the foreign table.  Because of the latter, the logic is
 * pretty close to assign_collations_walker() in parse_collate.c, though we
 * can assume here that the given expression is valid.
 */
static bool
walk_foreignExpr__(Node *node,
				   GlobalCxt__ *glob_cxt,
				   LocalCxt__ *outer_cxt)
{
	bool		check_type = true;
	LocalCxt__  inner_cxt;
	Oid			collation;
	FDWCollateState state;

	/* Need do nothing for empty subexpressions */
	if (node == NULL)
		return true;

	/* Set up inner_cxt for possible recursion to child nodes */
	inner_cxt.collation = InvalidOid;
	inner_cxt.state = FDW_COLLATE_NONE;

	switch (nodeTag(node))
	{
		case T_Var:
			{
				Var		   *var = (Var *) node;

				/*
				 * If the Var is from the foreign table, we consider its
				 * collation (if any) safe to use.  If it is from another
				 * table, we treat its collation the same way as we would a
				 * Param's collation, ie it's not safe for it to have a
				 * non-default collation.
				 */
				if (var->varno == glob_cxt->foreignrel->relid &&
					var->varlevelsup == 0)
				{
					/* Var belongs to foreign table */
					collation = var->varcollid;
					state = OidIsValid(collation) ? FDW_COLLATE_SAFE : FDW_COLLATE_NONE;
				}
				else
				{
					/* Var belongs to some other table */
					if (var->varcollid != InvalidOid &&
						var->varcollid != DEFAULT_COLLATION_OID)
						return false;

					/* We can consider that it doesn't set collation */
					collation = InvalidOid;
					state = FDW_COLLATE_NONE;
				}
			}
			break;
		case T_Const:
			{
				Const	   *c = (Const *) node;

				/*
				 * If the constant has nondefault collation, either it's of a
				 * non-builtin type, or it reflects folding of a CollateExpr;
				 * either way, it's unsafe to send to the remote.
				 */
				if (c->constcollid != InvalidOid &&
					c->constcollid != DEFAULT_COLLATION_OID)
					return false;

				/* Otherwise, we can consider that it doesn't set collation */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_Param:
			{
				Param	   *p = (Param *) node;

				/*
				 * Collation rule is same as for Consts and non-foreign Vars.
				 */
				collation = p->paramcollid;
				if (collation == InvalidOid ||
					collation == DEFAULT_COLLATION_OID)
					state = FDW_COLLATE_NONE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_ArrayRef:
			{
				ArrayRef   *ar = (ArrayRef *) node;;

				/* Assignment should not be in restrictions. */
				if (ar->refassgnexpr != NULL)
					return false;

				/*
				 * Recurse to remaining subexpressions.  Since the array
				 * subscripts must yield (noncollatable) integers, they won't
				 * affect the inner_cxt state.
				 */
				if (!walk_foreignExpr__((Node *) ar->refupperindexpr,
										 glob_cxt, &inner_cxt))
					return false;
				if (!walk_foreignExpr__((Node *) ar->reflowerindexpr,
										 glob_cxt, &inner_cxt))
					return false;
				if (!walk_foreignExpr__((Node *) ar->refexpr,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * Array subscripting should yield same collation as input,
				 * but for safety use same logic as for function nodes.
				 */
				collation = ar->refcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_FuncExpr:
			{
				FuncExpr   *fe = (FuncExpr *) node;

				/*
				 * If function used by the expression is not built-in, it
				 * can't be sent to remote because it might have incompatible
				 * semantics on remote side.
				 */
				if (!is_builtin(fe->funcid))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!walk_foreignExpr__((Node *) fe->args,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * If function's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (fe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 fe->inputcollid != inner_cxt.collation)
					return false;

				/*
				 * Detect whether node is introducing a collation not derived
				 * from a foreign Var.  (If so, we just mark it unsafe for now
				 * rather than immediately returning false, since the parent
				 * node might not care.)
				 */
				collation = fe->funccollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_OpExpr:
		case T_DistinctExpr:	/* struct-equivalent to OpExpr */
			{
				OpExpr	   *oe = (OpExpr *) node;

				/*
				 * Similarly, only built-in operators can be sent to remote.
				 * (If the operator is, surely its underlying function is
				 * too.)
				 */
				if (!is_builtin(oe->opno))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!walk_foreignExpr__((Node *) oe->args,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * If operator's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (oe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 oe->inputcollid != inner_cxt.collation)
					return false;

				/* Result-collation handling is same as for functions */
				collation = oe->opcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *oe = (ScalarArrayOpExpr *) node;

				/*
				 * Again, only built-in operators can be sent to remote.
				 */
				if (!is_builtin(oe->opno))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!walk_foreignExpr__((Node *) oe->args,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * If operator's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (oe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 oe->inputcollid != inner_cxt.collation)
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_RelabelType:
			{
				RelabelType *r = (RelabelType *) node;

				/*
				 * Recurse to input subexpression.
				 */
				if (!walk_foreignExpr__((Node *) r->arg,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * RelabelType must not introduce a collation not derived from
				 * an input foreign Var.
				 */
				collation = r->resultcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_BoolExpr:
			{
				BoolExpr   *b = (BoolExpr *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!walk_foreignExpr__((Node *) b->args,
										 glob_cxt, &inner_cxt))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_NullTest:
			{
				NullTest   *nt = (NullTest *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!walk_foreignExpr__((Node *) nt->arg,
										 glob_cxt, &inner_cxt))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_ArrayExpr:
			{
				ArrayExpr  *a = (ArrayExpr *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!walk_foreignExpr__((Node *) a->elements,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * ArrayExpr must not introduce a collation not derived from
				 * an input foreign Var.
				 */
				collation = a->array_collid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_List:
			{
				List	   *l = (List *) node;
				ListCell   *lc;

				/*
				 * Recurse to component subexpressions.
				 */
				foreach(lc, l)
				{
					if (!walk_foreignExpr__((Node *) lfirst(lc),
											 glob_cxt, &inner_cxt))
						return false;
				}

				/*
				 * When processing a list, collation state just bubbles up
				 * from the list elements.
				 */
				collation = inner_cxt.collation;
				state = inner_cxt.state;

				/* Don't apply exprType() to the list. */
				check_type = false;
			}
			break;
		default:

			/*
			 * If it's anything else, assume it's unsafe.  This list can be
			 * expanded later, but don't forget to add deparse support below.
			 */
			return false;
	}

	/*
	 * If result type of given expression is not built-in, it can't be sent to
	 * remote because it might have incompatible semantics on remote side.
	 */
	if (check_type && !is_builtin(exprType(node)))
		return false;

	/*
	 * Now, merge my collation information into my parent's state.
	 */
	if (state > outer_cxt->state)
	{
		/* Override previous parent state */
		outer_cxt->collation = collation;
		outer_cxt->state = state;
	}
	else if (state == outer_cxt->state)
	{
		/* Merge, or detect error if there's a collation conflict */
		switch (state)
		{
			case FDW_COLLATE_NONE:
				/* Nothing + nothing is still nothing */
				break;
			case FDW_COLLATE_SAFE:
				if (collation != outer_cxt->collation)
				{
					/*
					 * Non-default collation always beats default.
					 */
					if (outer_cxt->collation == DEFAULT_COLLATION_OID)
					{
						/* Override previous parent state */
						outer_cxt->collation = collation;
					}
					else if (collation != DEFAULT_COLLATION_OID)
					{
						/*
						 * Conflict; show state as indeterminate.  We don't
						 * want to "return false" right away, since parent
						 * node might not care about collation.
						 */
						outer_cxt->state = FDW_COLLATE_UNSAFE;
					}
				}
				break;
			case FDW_COLLATE_UNSAFE:
				/* We're still conflicted ... */
				break;
		}
	}

	/* It looks OK */
	return true;
}


/*
 * Return true if given object is one of PostgreSQL's built-in objects.
 *
 * We use FirstBootstrapObjectId as the cutoff, so that we only consider
 * objects with hand-assigned OIDs to be "built in", not for instance any
 * function or type defined in the information_schema.
 *
 * Our constraints for dealing with types are tighter than they are for
 * functions or operators: we want to accept only types that are in pg_catalog,
 * else format_type might incorrectly fail to schema-qualify their names.
 * (This could be fixed with some changes to format_type, but for now there's
 * no need.)  Thus we must exclude information_schema types.
 *
 * XXX there is a problem with this, which is that the set of built-in
 * objects expands over time.  Something that is built-in to us might not
 * be known to the remote server, if it's of an older version.  But keeping
 * track of that would be a huge exercise.
 */
static bool
is_builtin(Oid oid)
{
	return (oid < FirstBootstrapObjectId);
}
