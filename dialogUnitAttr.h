#ifndef DIALOGNEWUNIT_H
#define DIALOGNEWUNIT_H

#include <QDialog>
#include "dialogpagenameset.h"
#include "dialogunitmanage.h"
#include "common.h"
#include <Qsci/qsciscintilla.h>
#include <Qsci/qscilexercpp.h>
#include <Qsci/qsciapis.h>
#include "qscilexercppattach.h"
#include "dialogtag.h"
namespace Ui {
class DialogUnitAttr;
}

class PortConfigPanel;

class DialogUnitAttr : public QDialog
{
    Q_OBJECT

public:
    explicit DialogUnitAttr(QWidget *parent = nullptr);
    ~DialogUnitAttr();
    void LoadInfo(int Mode,int Equipment_ID);
    void InitUIInfo();
    void UpdateUIInfo(QSqlQuery QueryEquipment);
    void InitTEdit();
    void LoadDiagnoseParameter();
    void ReplaceMarkToTag();
    void ReloadLib();
    DialogPageNameSet dlgPageNameSet;
    QString StrProTag,CurEquipment_ID,LibEquipment_ID;
    bool Canceled;
    bool UnitTypeChanged,UnitTagChanged;
    bool UnitProSetUpdated;
    int NewProjectStructure_ID;
    int AttrMode;//AttrMode=1:add  AttrMode=2:modify
    QsciScintilla *QsciEdit;//*QsciEditVariable,
    DialogUnitManage *dlgUnitManage;
    QStringList ListSymbolSpurInfo;
private slots:
    void on_BtnProSet_clicked();

    void on_tableWidgetSpur_clicked(const QModelIndex &index);

    void on_BtnOk_clicked();

    void on_BtnUnitChoose_clicked();

    void on_EdUnitTag_textChanged(const QString &arg1);

    void on_BtnCancel_clicked();

    void on_BtnAddPara_clicked();

    void on_BtnDeletePara_clicked();

    void on_BtnCompile_clicked();

    void on_BtnValidateTModel_clicked();

    void on_tableRepairInfo_clicked(const QModelIndex &index);

    void on_TextEdRepairPlan_textChanged();

    void on_TextEdRepairResource_textChanged();

    void on_BtnAddUnitPic_clicked();

    void on_tableWidgetUnitPic_clicked(const QModelIndex &index);

    void on_BtnReplaceUnitPic_clicked();

    void on_BtnDelUnitPic_clicked();

    void SlotDrawTagWrapper(int Type,QColor mColor);

    void SlotDrawTermTagWrapper(int Type,QColor mColor);

    void SlotChangeColorWrapper(QColor mColor);

    void SlotChangeTermColorWrapper(QColor mColor);

    void on_BtnCancelSign_clicked();

    void on_BtnSave_clicked();

    void on_tableTerm_clicked(const QModelIndex &index);

    void showTableTermContextMenu(const QPoint &pos);

    void onConfigurePort();

    void onRemovePortConfig();

    void on_BtnFromUnitImage_clicked();

    void on_BtnFromDisk_clicked();

    void on_BtnCancelTermSign_clicked();

    void on_BtnSaveTerm_clicked();

    void fillUnitPicTable(const QString &picture, const QString &supplier);

signals:
    void UpdateProjectUnits();

protected:
    void closeEvent(QCloseEvent *event) override; //对话框关闭时需要执行的动作

private:
    Ui::DialogUnitAttr *ui;
    BQGraphicsScene m_scene,m_scene_term;
    dialogTag *m_dialogTag,*m_dialogTermTag;
    unsigned char CurUnitImageIndex=0;
    QString CurImgPath;
    PortConfigPanel *m_portConfigPanel = nullptr;
    int m_componentContainerId = 0;

    void loadPortConfig(int equipmentId);
    int resolveContainerId(int equipmentId, bool createIfMissing);
    bool savePortConfig();
    QString getPortVariables(const QString &functionBlock, const QString &portName) const;
};

#endif // DIALOGNEWUNIT_H
