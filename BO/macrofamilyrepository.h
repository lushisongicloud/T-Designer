#ifndef MACROFAMILYREPOSITORY_H
#define MACROFAMILYREPOSITORY_H

#include <QString>
#include <QStringList>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QVariant>
#include <QDebug>
#include <QJsonDocument>
#include <QJsonObject>
#include <QJsonArray>
#include <QMap>

/**
 * @brief Data structure for a single connection macro
 */
struct ConnectionMacro {
    int arity = 0;                  // 端口数量（2/3/4/...）
    QString macroName;              // 宏名称，如 connect2e, connect3e
    QString expansionTemplate;       // 展开模板，如 "(assert (= (+ %1.i %2.i) 0))"
    
    bool isValid() const { return arity > 0 && !macroName.isEmpty(); }
};

/**
 * @brief Data structure for a macro family
 */
struct MacroFamily {
    int familyId = -1;
    QString familyName;             // 宏族名称，如 electric-connect
    QString domain;                 // 领域：electric/hydraulic/mechanical/other
    QString description;
    bool isBuiltin = false;         // 是否为内置宏族
    QMap<int, ConnectionMacro> macros; // arity -> macro mapping
    
    bool isValid() const { return !familyName.isEmpty() && !macros.isEmpty(); }
    
    // 根据端口数量获取对应的宏
    ConnectionMacro getMacroByArity(int arity) const;
    
    // 从JSON加载宏定义
    bool loadMacrosFromJson(const QString &json, QString *errorMsg = nullptr);
    
    // 导出宏定义为JSON
    QString exportMacrosToJson() const;
};

/**
 * @brief Repository for managing connection macro families
 */
class MacroFamilyRepository
{
public:
    explicit MacroFamilyRepository(const QSqlDatabase &db);
    
    // Query operations
    QList<MacroFamily> getAllMacroFamilies(QString *errorMsg = nullptr);
    QList<MacroFamily> getBuiltinMacroFamilies(QString *errorMsg = nullptr);
    QList<MacroFamily> getUserMacroFamilies(QString *errorMsg = nullptr);
    MacroFamily getMacroFamily(int familyId, QString *errorMsg = nullptr);
    MacroFamily getMacroFamilyByName(const QString &familyName, QString *errorMsg = nullptr);
    
    // CRUD operations
    bool saveMacroFamily(MacroFamily &family, QString *errorMsg = nullptr);
    bool updateMacroFamily(const MacroFamily &family, QString *errorMsg = nullptr);
    bool deleteMacroFamily(int familyId, QString *errorMsg = nullptr);
    
    // Initialization
    bool ensureSchema();
    bool initializeBuiltinMacroFamilies(QString *errorMsg = nullptr);
    
    // Macro expansion
    QString expandMacro(const QString &familyName, int arity, const QStringList &ports, QString *errorMsg = nullptr);
    
private:
    bool macroFamilyExists(const QString &familyName);
    MacroFamily createElectricConnectFamily();
    MacroFamily createHydraulicConnectFamily();
    MacroFamily createMechanicalConnectFamily();
    
    QSqlDatabase m_db;
};

#endif // MACROFAMILYREPOSITORY_H
