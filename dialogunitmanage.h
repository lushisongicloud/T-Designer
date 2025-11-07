#ifndef DIALOGUNITMANAGE_H
#define DIALOGUNITMANAGE_H

#include <QDialog>
#include <QDebug>
#include <QStringList>
#include <QtSql>
#include <QIcon>
#include <QTableWidget>
#include <QFileSystemModel>
#include <QFormLayout>
#include <QMouseEvent>
#include <QFileDialog>
#include <QPainter>
#include "qxlabel.h"
#include "mxdrawxlib.h"
#include "common.h"
#include "dialogfuncdefine.h"
#include "dialogloadsymbol.h"
#include "dialogfactorymanage.h"
#include <Qsci/qsciscintilla.h>
#include <Qsci/qscilexercpp.h>
#include <Qsci/qsciapis.h>
#include "qscilexercppattach.h"
#include "bqgraphicsitem.h"
#include "bqgraphicsscene.h"
#include "dialogtag.h"
#include "widget/codecheckdialog.h"
#include "BO/function/tmodelparser.h"
#include "BO/ai/tmodelautogenerator.h"

extern QSqlDatabase  T_Database;

using namespace MxDrawXLib;
namespace Ui {
class DialogUnitManage;
}

class PortConfigPanel;

class DialogUnitManage : public QDialog
{
    Q_OBJECT

public:
    explicit DialogUnitManage(QWidget *parent = nullptr);
    ~DialogUnitManage();
    void closeEvent(QCloseEvent *event);
    void LoadDBFactory();
    void LoadDBGroup();
    void UpdateCbFactory();
    void FindUnitAccordingToDesc(QTableWidget *tablewidget,const QModelIndex &index,int Level);
    void FindUnitAccordingToGroup(QTableWidget *tablewidget,const QModelIndex &index,int Level);
    void SetStackWidget(int PageIndex);
    void LocateToUnitIndex(QString Equipment_ID);
    void DeleteUnitByClass_ID(QString Class_ID,QString Factory_ID);
    void InitTEdit();
    void LoadDiagnoseParameters(int Equipment_ID);
    bool Canceled;
    int RetCode=-1,EquipmentTemplate_ID=0;
    QStandardItemModel *Model;
    QString CurEquipment_ID;//UnitJpgName;
    QString CurEquipment_Supplier;
    DialogFuncDefine *dlgFuncDefine;
   DialogLoadSymbol *dlgLoadSymbol;
   QString CopyEquipment_ID="";
   QsciScintilla *QsciEdit;

   QMap<QString, QString> factoryMap;
   QSet<QString> equipmentID_IN_EquipmentTemplate;
    PortConfigPanel *m_portConfigPanel = nullptr;
    int m_componentContainerId = 0;

    void loadPortConfig(int equipmentId);
    int resolveContainerId(int equipmentId, bool createIfMissing);
    bool savePortConfig();
    QString getPortVariables(const QString &functionBlock, const QString &portName) const;
private slots:
    void on_BtnClose_clicked();

    void on_RbType_clicked(bool checked);

    void on_treeViewUnitGroup_clicked(const QModelIndex &index);

    void on_tableWidgetUnit_clicked(const QModelIndex &index);

    void on_RbFactory_clicked(bool checked);

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnSearch_clicked();

    void on_BtnEditFunc_clicked();

    void on_BtnApply_clicked();

    void on_BtnReplaceUnitPic_clicked();

    void on_BtnDelUnitPic_clicked();

    void on_BtnReplaceStamp_clicked();

    void on_BtnDeleteStamp_clicked();

    void on_BtnAddSpur_clicked();

    void on_BtnDeleteSpur_clicked();

    void on_BtnAddUnit_clicked();

    void on_BtnCopySelectRow_clicked();

    void on_tableWidgetSpur_clicked(const QModelIndex &index);

    void on_tableWidgetSpur_doubleClicked(const QModelIndex &index);

    void on_BtnSpurSymbolEdit_clicked();

    void ShowtreeViewUnitGroupPopMenu(const QPoint &pos);

    void NewLevel();

    void NewLevel0();

    void Rename();

    void Delete();

    void on_BtnFactoryManage_clicked();

    void on_BtnCopyUnit_clicked();

    void on_BtnPasteUnit_clicked();

    void on_BtnDeleteUnit_clicked();

    void on_BtnAddPara_clicked();

    void on_BtnDeletePara_clicked();

    void on_CbAllSourceConn_clicked();

    void on_BtnUpdatePortVars_clicked();

    void on_BtnCompile_clicked();

    void on_BtnAutoGenerate_clicked();

    void on_tableRepairInfo_clicked(const QModelIndex &index);

    void showRepairInfoContextMenu(const QPoint &pos);

    void onAddRepairInfo();

    void onDeleteRepairInfo();

    void onAutoFillFromTModel();

    void on_TextEdRepairPlan_textChanged();

    void on_TextEdRepairResource_textChanged();

    void on_BtnHideShow_clicked();

    void on_BtnInsertSpur_clicked();

    void on_BtnAddUnitPic_clicked();

    void on_tableWidgetUnitPic_clicked(const QModelIndex &index);

    void on_BtnFromUnitImage_clicked();

    void on_BtnFromDisk_clicked();

    void on_BtnSign_clicked();

    void on_BtnSave_clicked();

    void on_tableTerm_clicked(const QModelIndex &index);

    void on_BtnCancelSign_clicked();

    void SlotChangeColorWrapper(QColor mColor);

    void SlotDrawTagWrapper(int Type,QColor mColor);

    void on_BtnUpdatePath_clicked();

    void on_BtnCategory_clicked();

    void on_BtnCountUnit_clicked();

    void showTableTermContextMenu(const QPoint &pos);

    void onConfigurePort();

    void onRemovePortConfig();

    void on_BtnCopyUnitPic_clicked();

    void on_BtnAckUnitPic_clicked();

    void addTotableTerm(const QString &spurDT, const QString &equipTempId, const QString &connNum, const QString &connDesc,const QString &cost,const QSqlQuery *queryTermInfo, const QString &supplier);

    void on_BtnDelItem_clicked();

    void on_BtnCheck_clicked();

    void showConstantsContextMenu(const QPoint &pos);

    void onAddConstant();

    void onDeleteConstants();

    void onInsertConstantName();

    void on_BtnBatchAutoGenerate_clicked();

private:
    void performTModelValidation();
    //void setupConstantsTable();
    void loadConstants(const QString &constantsData);
    QString saveConstants() const;
    bool validateConstantName(const QString &name, int excludeRow = -1) const;
    Ui::DialogUnitManage *ui;
    unsigned char CurUnitImageIndex=0;
    QString CurImgPath;
    BQGraphicsScene m_scene;
    dialogTag *m_dialogTag;
    BQGraphicsScene m_scene_unit;
    //QColor CurTagColor;


signals:
    void SignalCloseWnd(QString Type,QString Factory);
    void SignalUpdated();
};

#endif // DIALOGUNITMANAGE_H
