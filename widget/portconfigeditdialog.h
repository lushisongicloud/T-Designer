#ifndef PORTCONFIGEDITDIALOG_H
#define PORTCONFIGEDITDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include <QString>

namespace Ui {
class PortConfigEditDialog;
}

struct PortConfigData {
    int portConfigId = 0;
    QString functionBlock;
    QString portName;
    QString portType = "electric";
    QString direction = "bidirectional";
    QString variableProfile = "default";
    QString variablesText;  // 逗号分隔的变量列表，如 "i,u"
    QString connectMacro;
};

class PortConfigEditDialog : public QDialog
{
    Q_OBJECT

public:
    explicit PortConfigEditDialog(const QSqlDatabase &db, int containerId, QWidget *parent = nullptr);
    ~PortConfigEditDialog() override;

    void setPortInfo(const QString &functionBlock, const QString &portName);
    bool loadConfig();
    bool saveConfig();

    PortConfigData getConfig() const;

private slots:
    void onPortTypeChanged(const QString &type);
    void onVariableProfileChanged(const QString &profile);
    void onMacroTableClicked(const QModelIndex &index);
    void onAddMacroFamily();
    void onDeleteMacroFamily();

private:
    void loadAvailableMacros();
    void updateDefaultVariables();
    void updateDefaultMacro();
    QString variablesJsonFromText(const QString &text) const;
    QString variablesTextFromJson(const QString &json) const;

    Ui::PortConfigEditDialog *ui;
    QSqlDatabase m_db;
    int m_containerId = 0;
    QString m_functionBlock;
    QString m_portName;
    int m_portConfigId = 0;
};

#endif // PORTCONFIGEDITDIALOG_H
