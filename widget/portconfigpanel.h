#ifndef PORTCONFIGPANEL_H
#define PORTCONFIGPANEL_H

#include <QWidget>
#include <QSqlDatabase>
#include <QVector>

struct PortConfigEntry
{
    int portConfigId = 0;
    QString functionBlock;
    QString portName;
    QString portType;      // electric/hydraulic/mechanical/other
    QString direction;     // input/output/bidirectional/internal
    QString variableProfile; // default/custom/alias:*
    QString variablesJson; // JSON array of variable descriptors
    QString connectMacro;  // macro name
    QString customMetadata;// JSON object for UI/meta
};

struct ConnectMacroEntry
{
    int macroId = 0;
    QString macroName;
    QString domain;        // electric/hydraulic/mechanical/generic
    int arity = 2;
    QString expansionTemplate;
    QString description;
    QString metadataJson;
};

class QTableWidget;
class QPushButton;
class QComboBox;
class QTextEdit;
class QJsonDocument;

namespace Ui {
class PortConfigPanel;
}

class PortConfigPanel : public QWidget
{
    Q_OBJECT
public:
    explicit PortConfigPanel(QWidget *parent = nullptr);
    explicit PortConfigPanel(const QSqlDatabase &db, QWidget *parent = nullptr);
    ~PortConfigPanel() override;

    void setDatabase(const QSqlDatabase &db);
    void setContainerId(int containerId);

    bool load();
    bool save();
    bool validate(QString *errorMessage = nullptr) const;

signals:
    void panelChanged();

private slots:
    void addPort();
    void removeSelectedPorts();
    void addMacro();
    void removeSelectedMacros();
    void onPortCellChanged(int row, int column);
    void onMacroCellChanged(int row, int column);

private:
    bool ensureTables();
    void setupUi();
    void setupPortTable();
    void setupMacroTable();
    PortConfigEntry readPortRow(int row) const;
    void writePortRow(int row, const PortConfigEntry &entry);
    ConnectMacroEntry readMacroRow(int row) const;
    void writeMacroRow(int row, const ConnectMacroEntry &entry);
    bool loadPorts();
    bool loadMacros();
    bool savePorts();
    bool saveMacros();

    QSqlDatabase m_db;
    int m_containerId = 0;
    Ui::PortConfigPanel *ui = nullptr;
};

#endif // PORTCONFIGPANEL_H
