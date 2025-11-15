#ifndef FUNCTIONREPOSITORY_H
#define FUNCTIONREPOSITORY_H

#include <QList>
#include <QMap>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QVariant>
#include <QSet>
#include <QStringList>

#include "BO/function/functioninfo.h"

class QDomElement;

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
    QString variableConfigXml;
};

struct FunctionTreeNode
{
    QString name;
    QList<FunctionTreeNode> children;
};

struct FunctionDocumentRecord
{
    int id = 0;
    int containerId = 0;
    QString xmlText;
    QString formatVersion = QString("1.0");
    QString checksum;
    QString sourceHint;
    QString metadataJson;
    QString createdAt;
    QString updatedAt;

    bool isValid() const { return containerId > 0 && !xmlText.isEmpty(); }
};

struct FunctionDocumentParseResult
{
    QList<FunctionTreeNode> tree;
    QMap<QString, FunctionInfo> functionMap;
    QStringList warnings;
    bool success = false;
};

class FunctionRepository
{
public:
    explicit FunctionRepository(const QSqlDatabase &db = QSqlDatabase::database());

    bool ensureTables();
    bool ensureFunctionDocumentTable();

    QList<FunctionRecord> fetchAll() const;
    QList<FunctionRecord> fetchBySymbol(int symbolId) const;
    FunctionRecord getById(int id) const;

    int insert(const FunctionRecord &record);
    bool update(const FunctionRecord &record);
    bool remove(int id);

    FunctionDocumentRecord loadDocument(int containerId) const;
    bool saveDocument(FunctionDocumentRecord &record);
    bool deleteDocument(int containerId);
    FunctionDocumentParseResult parseFunctionDocument(const QString &xml) const;

private:
    QSqlDatabase m_db;

    int nextId() const;
    bool bindSymbol(int functionId, int symbolId);
    void logError(const QSqlQuery &query, const QString &context) const;
    bool ensureFunctionTable();
    bool ensureFunctionBindingTable();
    QString computeChecksum(const QString &xml) const;
    FunctionTreeNode parseTreeItem(const QDomElement &element) const;
    FunctionInfo parseFunctionElement(const QDomElement &element, QStringList &warnings) const;
    QStringList parseComponentList(const QString &text) const;
};

#endif // FUNCTIONREPOSITORY_H
