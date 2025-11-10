#ifndef DIALOGALLBASEPARA_H
#define DIALOGALLBASEPARA_H

#include <QDialog>
#include <QCheckBox>
#include "myqsqldatabase.h"
namespace Ui {
class DialogAllBasePara;
}

class DialogAllBasePara : public QDialog
{
    Q_OBJECT

public:
    explicit DialogAllBasePara(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~DialogAllBasePara();
    void InitTabWidget_Variable();
    void LoadParaList();
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);
    QVector<DataBase::Str_Signal> m_BasicSignal;//基础信号列表
    myQSqlDatabase *m_Database = nullptr;//数据库检索类
    QStringList ListPara;
    QStringList ListComparePara;
    bool Canceled;
private slots:
    void on_BtnSetUnchecked_clicked();

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void CheckCompareList(bool);

private:
    Ui::DialogAllBasePara *ui;
};

#endif // DIALOGALLBASEPARA_H
