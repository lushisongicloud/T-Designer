#ifndef DIALOGWARNINGDEFINE_H
#define DIALOGWARNINGDEFINE_H

#include <QDialog>
#include <QMessageBox>
#include "myqsqldatabase.h"
#include <QTableWidget>
#include "dialogallbasepara.h"
namespace Ui {
class DialogWarningDefine;
}

class DialogWarningDefine : public QDialog
{
    Q_OBJECT

public:
    explicit DialogWarningDefine(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr
            ,DataBase::Str_WarnRule rule = {},bool isCreatRule = false);
    ~DialogWarningDefine();
    void InitTabWidget();
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);
    void LoadInfo();
    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    DataBase::Str_WarnRule m_WarnRule;//规则
    bool m_isCreatRule = false;//为新建规则还是修改规则
    bool Canceled=true;

private slots:

    void on_Btn_TaskFeatureMod_clicked();

    void on_Btn_TaskFeatureDelete_clicked();

    void on_Btn_TaskAssoMod_clicked();
    
    void on_Btn_TaskAssoDelete_clicked();
    
    void on_Btn_OK_clicked();
    
    void on_Btn_Cancel_clicked();
    
private:
    Ui::DialogWarningDefine *ui;
};

#endif // DIALOGWARNINGDEFINE_H
