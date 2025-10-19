#ifndef FUNCTIONSYMBOLPICKERDIALOG_H
#define FUNCTIONSYMBOLPICKERDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include <QTreeWidget>

class FunctionSymbolPickerDialog : public QDialog
{
    Q_OBJECT

public:
    explicit FunctionSymbolPickerDialog(const QSqlDatabase &db, QWidget *parent = nullptr);
    int selectedSymbolId() const { return m_selectedSymbolId; }
    QString selectedSymbolName() const { return m_selectedSymbolName; }

private slots:
    void onItemActivated(QTreeWidgetItem *item, int column);
    void onSelectionChanged();
    void acceptSelection();

private:
    void loadData();

    QSqlDatabase m_db;
    QTreeWidget *m_tree;
    QPushButton *m_okButton;
    int m_selectedSymbolId = 0;
    QString m_selectedSymbolName;
};

#endif // FUNCTIONSYMBOLPICKERDIALOG_H
