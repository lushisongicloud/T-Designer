#ifndef CONTAINERTREEDIALOG_H
#define CONTAINERTREEDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include "widget/containermodel.h"

namespace Ui { class ContainerTreeDialog; }

class ContainerTreeDialog : public QDialog
{
    Q_OBJECT
public:
    enum class Mode { Manage, Select };

    explicit ContainerTreeDialog(QWidget *parent = nullptr);
    ~ContainerTreeDialog();

    void setDatabase(const QSqlDatabase &db);
    void setMode(Mode mode);
    void setAllowedTypes(const QList<ContainerType> &types);
    ContainerEntity selectedEntity() const;

private slots:
    void onAdd();
    void onRemove();
    void onRefresh();
    void acceptSelection();
    void showContextMenu(const QPoint &pos);

private:
    void refreshTypeCombo();

    Ui::ContainerTreeDialog *ui;
    ContainerModel *m_model;
    Mode m_mode;
    QList<ContainerType> m_allowedTypes;
    QVector<ContainerType> m_comboTypes;
    ContainerEntity m_selected;
    QSqlDatabase m_db;
};

#endif // CONTAINERTREEDIALOG_H
