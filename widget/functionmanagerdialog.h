#ifndef FUNCTIONMANAGERDIALOG_H
#define FUNCTIONMANAGERDIALOG_H

#include <QDialog>
#include <QSqlDatabase>

#include "BO/function/functionrepository.h"

namespace Ui {
class FunctionManagerDialog;
}

class FunctionManagerDialog : public QDialog
{
    Q_OBJECT
public:
    explicit FunctionManagerDialog(const QSqlDatabase &db, QWidget *parent = nullptr);
    ~FunctionManagerDialog() override;

private slots:
    void onAdd();
    void onEdit();
    void onDelete();
    void onRefresh();
    void onTableDoubleClicked(int row, int column);

private:
    void loadData();
    void updateButtons();
    FunctionRecord currentRecord() const;

    Ui::FunctionManagerDialog *ui;
    QSqlDatabase m_db;
    FunctionRepository m_repo;
    QList<FunctionRecord> m_records;
};

#endif // FUNCTIONMANAGERDIALOG_H
