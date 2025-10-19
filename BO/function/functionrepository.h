#ifndef FUNCTIONREPOSITORY_H
#define FUNCTIONREPOSITORY_H

#include <QList>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QVariant>
#include <QSet>

struct FunctionRecord
{
    int id = 0;
    QString name;
    QString cmdValList;
    QString execsList;
    QString remark;
    QString link;
    QString componentDependency;
    QString allComponents;
    QString functionDependency;
    bool persistent = true;
    double faultProbability = 0.0;
    int symbolId = 0;
    QString symbolName;
};

class FunctionRepository
{
public:
    explicit FunctionRepository(const QSqlDatabase &db = QSqlDatabase::database());

    bool ensureTables();

    QList<FunctionRecord> fetchAll() const;
    QList<FunctionRecord> fetchBySymbol(int symbolId) const;
    FunctionRecord getById(int id) const;

    int insert(const FunctionRecord &record);
    bool update(const FunctionRecord &record);
    bool remove(int id);

private:
    QSqlDatabase m_db;

    int nextId() const;
    bool bindSymbol(int functionId, int symbolId);
    void logError(const QSqlQuery &query, const QString &context) const;
};

#endif // FUNCTIONREPOSITORY_H
