#ifndef SMTREPOSITORY_H
#define SMTREPOSITORY_H

#include <QString>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QDebug>
#include <QVariant>

/**
 * @brief Repository for managing component and system SMT descriptions
 * 
 * This class provides interfaces to:
 * 1. Access component SMT templates from ref/Model.db (read-only)
 * 2. Access component SMT instances from project component_smt table
 * 3. Access system SMT descriptions from project system_smt table
 * 4. Save and update SMT descriptions
 */
class SmtRepository
{
public:
    explicit SmtRepository(const QSqlDatabase &projectDb, const QString &refModelDbPath = QString());
    
    // Component SMT template access (from ref/Model.db)
    QString getComponentTemplate(const QString &componentMark, QString *errorMsg = nullptr);
    QString getComponentVariableDeclarations(const QString &componentMark, QString *errorMsg = nullptr);
    QString getComponentDescription(const QString &componentMark, QString *errorMsg = nullptr);
    QString getComponentFailureMode(const QString &componentMark, QString *errorMsg = nullptr);
    
    // Component SMT instance access (from project component_smt table)
    QString getComponentSmt(int equipmentId, QString *errorMsg = nullptr);
    QString getContainerSmt(int containerId, QString *errorMsg = nullptr);
    
    // System SMT access (from project system_smt table)
    struct SystemSmtData {
        QString defBlock;
        QString connectBlock;
        QString rawBlock;
        QString generatedBy;
        bool isValid = false;
    };
    SystemSmtData getSystemSmt(int containerId, QString *errorMsg = nullptr);
    
    // Save/Update operations
    bool saveComponentSmt(int equipmentId, const QString &smtText, const QString &portSignature = QString(), QString *errorMsg = nullptr);
    bool saveContainerSmt(int containerId, const QString &smtText, const QString &portSignature = QString(), QString *errorMsg = nullptr);
    bool saveSystemSmt(int containerId, const QString &defBlock, const QString &connectBlock, const QString &rawBlock = QString(), QString *errorMsg = nullptr);
    
    // Validation support
    bool validateComponentSmt(const QString &smtText, QString *errorMsg = nullptr);
    
private:
    bool openRefModelDb();
    void closeRefModelDb();
    
    QSqlDatabase m_projectDb;
    QSqlDatabase m_refModelDb;
    QString m_refModelDbPath;
    bool m_refModelDbOpened;
};

#endif // SMTREPOSITORY_H
