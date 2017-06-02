#ifndef SQLITE_FDW_FUNCS_H
#define SQLITE_FDW_FUNCS_H


typedef struct SqliteTableImportOptions
{
    bool import_notnull;
    bool import_default;
} SqliteTableImportOptions;


typedef struct SqliteTableSource
{
    char   *database;
    char   *table;
} SqliteTableSource;


bool is_sqliteTableRequired(ImportForeignSchemaStmt *stmt, 
                            char const * tablename);
char *get_foreignTableCreationSql(ImportForeignSchemaStmt *stmt, sqlite3 *db,
                                  char const * tablename,
                                  SqliteTableImportOptions options);
sqlite3 * get_sqliteDbHandle(char const *filename);
sqlite3_stmt * prepare_sqliteQuery(sqlite3 *db, char *query, 
                                   const char **pzTail);
SqliteTableImportOptions get_sqliteTableImportOptions(
        ImportForeignSchemaStmt *stmt);
SqliteTableSource get_tableSource(Oid foreigntableid);
Datum make_datum(sqlite3_stmt *stmt, int col, Oid pgtyp, bool *isnull);


#endif
