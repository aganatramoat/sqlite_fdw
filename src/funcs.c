#include <postgres.h>
#include <nodes/parsenodes.h>
#include <lib/stringinfo.h>
#include <utils/builtins.h>
#include <sqlite3.h>

#define MODULE_LOG_LEVEL WARNING

/*
 * Function declarations
 */
bool foreignSchemaTableIsRequired(
    ImportForeignSchemaStmt *stmt, 
    char const * tablename);

StringInfoData constructCreateForeignTableStatement(
    ImportForeignSchemaStmt *stmt, 
    sqlite3 * db,
    char const * tablename);

void sqliteOpen(char const *filename, sqlite3 **db);

sqlite3_stmt * sqlitePrepare(
    sqlite3 *db, 
    char *query, 
    const char **pzTail);
/**************************************/


void
sqliteOpen(char const *filename, sqlite3 **db)
{
	if (sqlite3_open(filename, db) != SQLITE_OK) 
    {
        char const * errmsg_from_sqlite3 = pstrdup(sqlite3_errmsg(*db));
		ereport(ERROR,
			(errcode(ERRCODE_FDW_OUT_OF_MEMORY),
			errmsg("Can't open sqlite database %s: %s", 
                    filename, 
                    errmsg_from_sqlite3)
			));
    }
}


sqlite3_stmt *
sqlitePrepare(sqlite3 *db, char *query, const char **pzTail)
{
	int rc;
    sqlite3_stmt *stmt;
    
    elog(MODULE_LOG_LEVEL, "entering function sqlitePrepare with \n%s", query);

	/* Execute the query */
	rc = sqlite3_prepare_v2(db, query, -1, &stmt, pzTail);
	if (rc != SQLITE_OK)
	{
		sqlite3_close(db);
		ereport(ERROR,
			(errcode(ERRCODE_FDW_UNABLE_TO_CREATE_EXECUTION),
			errmsg("SQL error during prepare: %s", sqlite3_errmsg(db))
			));
	}
    return stmt;
}


bool
foreignSchemaTableIsRequired(ImportForeignSchemaStmt *stmt, 
                             char const * tablename)
{
	ListCell   *lc;
    
    if ( stmt->list_type == FDW_IMPORT_SCHEMA_LIMIT_TO ) 
    {
        foreach(lc, stmt->table_list)
        {
            RangeVar *rv = (RangeVar *) lfirst(lc);
            if ( strcmp(tablename, rv->relname) == 0 )
                return true;
        }
        return false;
    }
    
    if ( stmt->list_type == FDW_IMPORT_SCHEMA_EXCEPT ) 
        foreach(lc, stmt->table_list)
        {
            RangeVar *rv = (RangeVar *) lfirst(lc);
            if ( strcmp(tablename, rv->relname) == 0 )
                return false;
        }
    
    return true;
}


StringInfoData 
constructCreateForeignTableStatement(ImportForeignSchemaStmt *stmt,
                                     sqlite3 * db,
                                     char const * tablename,
                                     bool import_not_null,
                                     bool import_default)
{
    StringInfoData	cftsql;
    char           *tableinfo_query;
    sqlite3_stmt   *tableinfo;
    
    initStringInfo(&cftsql);
    appendStringInfo(&cftsql, 
        "CREATE FOREIGN TABLE %s.%s (",
        stmt->local_schema, 
        quote_identifier(tablename));
    
    tableinfo_query = palloc0(strlen(tablename) + 32);
    sprintf(tableinfo_query, "PRAGMA table_info(%s)", tablename);
    
    tableinfo = sqlitePrepare(db, tableinfo_query, &pzTail);
    while (sqlite3_step(tableinfo) == SQLITE_ROW)
    {
        char   *col_name;
        char   *typ_name;
        bool	not_null;
        char   *default_val;

        col_name = (char *) sqlite3_column_text(tableinfo, 1);
        typ_name = (char *) sqlite3_column_text(tableinfo, 2);
        not_null = (sqlite3_column_int(tableinfo, 3) == 1);
        default_val = (char *) sqlite3_column_text(tableinfo, 4);

        appendStringInfo(&cftsql, ",\n");
        appendStringInfo(&cftsql, "%s ", 
                         quote_identifier(col_name));

        /* translated datatype */
        sqliteTranslateType(&cftsql, typ_name);

        if (not_null && import_not_null)
            appendStringInfo(&cftsql, " NOT NULL");

        if (default_val && import_default)
            appendStringInfo(&cftsql, " DEFAULT %s", default_val);
    }

    return cftsql;
}
