#ifndef SQLITE_FDW_H
#define SQLITE_FDW_H

#define SQLITE_FDW_LOG_LEVEL WARNING

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

#endif
