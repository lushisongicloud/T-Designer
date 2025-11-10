#ifndef QXCOMBOBOX_H
#define QXCOMBOBOX_H

#include <QWidget>
#include <QComboBox>
#include <QDialog>
#include <QFormLayout>
#include "common.h"
class qxcombobox : public QComboBox
{
    Q_OBJECT
public:
    qxcombobox(QWidget * parent = 0);
    QString DT,StrSystemDefine,CurFunctionID;
    QStringList ExistedUnits,CurExecsList;
    int Mode,RbMode;
public slots:
    void UpdateCmdItems(QString Name);
    void UpdateExecItems(QString DT);
    void UpdateExecStateItems(QString ExecName);
    void UpdateExecStateValueItems(QString ExecName);
    void UpdateItems(bool OnlyExec);
    void UpdateObserveItems(bool OnlyExec);
    void UpdateUserItems(bool OnlyExec);
    void UpdateUnitSpurItems(QString DT);
    void UpdateUnitPara(QString UnitName);
};

#endif // QXCOMBOBOX_H
