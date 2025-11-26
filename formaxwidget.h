#ifndef FORMAXWIDGET_H
#define FORMAXWIDGET_H

#include <QWidget>
#include <QTimer>
#include "common.h"
#include "dialogloadsymbol.h"
#include "dialogsymbolattribute.h"
#include "dialogmultiline.h"
#include "dialogBranchAttr.h"
#include "dialoglinedefine.h"
#include "dialogcabledefine.h"
#include "dialogconnectattr.h"
#include "dialoglinkedit.h"
#include "dialogsingletermattr.h"
#include "dialogattrdefset.h"
#include "dialogterminalattr.h"
#include "dialogaddterminal.h"
#include <QCursor>
#include <QList>
#include <QPushButton>
#include <QComboBox>
namespace Ui {
class formaxwidget;
}
using namespace MxDrawXLib;

struct stLayerPara
{
    QString Name;
    int Wight;
    QColor color;
    QString LineType;
};
struct stTextStyle
{
    QString Name;
    QString Font;
    double Hieight;
    double Width;//宽度缩放系数
};
class formaxwidget : public QWidget
{
    Q_OBJECT

public:
    explicit formaxwidget(QWidget *parent = nullptr,QString FileName="",int Page_ID=0);
    ~formaxwidget();
    void closeEvent(QCloseEvent *event);
    void CreateTextStyle();
    void CreateLayer();
    void SetGridStyle();
    bool SetEntityRed(QString Handle);//诊断可视化用，将块变红色
    void DoOpenDwgFileCommand();
    void DomAxWidgetOpenDwgFileCommand();
    void SymbolLoad(QString BlockFileName,QString SymbolID);
    void NodeLoad(QString NodeName);   
    void DoNodeLoad();
    void TerminalAdd(QString Terminal_ID);
    bool BlockRecordExist(QString BlkName);
    bool DoLoadSymbolCommand(QString LayerName);
    bool DoAddTerminalCommand(QString LayerName,int Terminal_ID,bool SetPos,double Posx,double Posy);
    void CheckAndUpdateTermLine(IMxDrawPoint *ConnectorPosition,IMxDrawPoint *PtPosition);
    void UpdateTermLineShortage(QString Handle,QStringList ShortageLines);
    void SplitLineByTerminal(IMxDrawBlockReference *BlkEnty);
    void EraseTerms(IMxDrawBlockReference *blkEnty);
    void DoSetSymbolSpurHighLight();
    void SetSymbolSpurHighLight();
    void SetTerminalHighLight();
    void DoSetTerminalHighLight();
    void EditSymbol();
    void DoEditSymbolCommand();
    void DoSymbolAttribute();
    void DoLoadSymbolSpur();
    void DoLoadUnitStamp();
    void DoLoadWholeUnit();
    void DoLoadTerminal();
    void GetUrPoint();
    void PuttingAttrDef();
    void LoadSymbolSpur(QList<int> ListSymbol_ID);
    void LoadUnitStamp(QString MultiLibName);
    void LoadWholeUnit(int UnitID,int Mode);
    void WriteUserDataToBlkEnty();//将符号dwg文件的拓展数据写入到块
    void DeleteEnty(QString Handle);
    //void SetSymbolSpurHighLight();
    void RotateEnty();
    void ChangeWholeUnitTermsGap(QString Mode);//改变WholeUnitTermsGap
    void LoadTerminal(QList<int> ListSymbol_ID);
    void LineConnect();
    void DoLineConnect();
    void TermBatchMark();
    void DoTermBatchMark();
    void MultiLine();
    void DoMultiLine();
    void LineDefine();
    void DoLineDefine();
    void DrawBlackBox();
    void DoDrawBlackBox();
    void DrawStructBox();
    void DoDrawStructBox();
    void CableDefine();
    void DoCableDefine();
    void DrawTypicalLine(QList<stPoint> DrawPoints,int Dir,int Type,IMxDrawWorldDraw *pDrawWorldDraw);
    void SetTermVisible(bool IsVisible);//显示或隐藏所有接线端点
    void SetBlkRed();
    void ShowWireAttr(IMxDrawBlockReference *EntyWire,int Wires_ID);
    void ShowCableAttr(IMxDrawEntity *EntyCableLine,int Mode,int Cable_ID);//Mode=1 Add , Mode=2 Modify
    IMxDrawBlockReference* UpdateSymbolBlock(QString Handle,QString StrSymbolName);
    void UpdateLinkBlk(IMxDrawBlockReference *blkNode,int Link_ID,QString RetStrLinkTag,QString RetStrLinkTextPosition);
    QAxWidget* GetAxWidget();
    void CombineLine(IMxDrawLine *mLine);
    bool CheckConnectLinePt(int Mode);
    void InsertNodes();
    void UpdateBlkDB(int Mode);//在执行粘贴、撤销等操作时，遍历当前dwg的块，更新对应的数据库
    IMxDrawPoint* GetGridPtVal(IMxDrawPoint* Pt);
    IMxDrawPoint* GetBesideTermPtVal(IMxDrawPoint* Pt);//找到最近的接线点坐标
    double GetGridPosVal(double Val);
    void PutCursorInGrid(int Mode,double &dX,double &dY);
    void InsertNodeRecordToDB(IMxDrawBlockReference *blkNode);
    IMxDrawPoint* FindAutoConnectPt(double Ptx,double Pty,QString LD_PARTLIB_DOTCONDIRECT);
    void DrawAutoConnectLine(int Mode,QString SymbolName,double BlkPosx,double BlkPosy,IMxDrawWorldDraw *pDrawWorldDraw);
    void DrawWholeUnit(int Mode,double Posx,double Posy,IMxDrawWorldDraw *pDrawWorldDraw);
    void InsertAllDirSymbol(QString BlkName);
    void GetListAllDirSymbols(QString BlkName);
    QString GetSymbolNameByDir(QString StrSymbolName,QString StrDir);
    void DeleteRecordOfEntity(qlonglong DeleteEntyID);
    void EntyGridEdit(qlonglong EntyID);
    void PasteEnty(qlonglong EntyID);
    void UndoEnty(QString EntyHandle);
    QString GetSymbolTag(IMxDrawBlockReference *BlkModifyed);
    void UpdateSymbolXData();
    void LoadEqualDistance(QList<int> List_DbID,int Mode);//Mode=0 Symbol  Mode=1 Terminals
    void DoLoadEqualDistance();//等距绘制
    void DealSymbolSpurBlock(double Posx,double Posy);
    void DealTerminalBlock(double Posx,double Posy);
    void CutLine(IMxDrawBlockReference *BlkEnty);//用端点截断导线
    void SelectEntitys();
    void DoSelectEntitys();
    void DrawDiagnoseLinkRoad(QList<int> ListSymbolID);
    void EditMultiLib(QString FileName);
    void DoEditMultiLib();
    void DoDrawMultiLibLine();
    void DoMultiLibSymbolLoad();
    void LoadText(QString TextStr);
    void DoLoadText();

    DialogSymbolAttribute *dlgSymbolAttribute;
    QString SymbolName;//后缀名为.dwg
    QString DataBaseSymbolID,DataBaseTerminalInstanceID,SymbolType,Symb2Lib_ID,SymbType,FunctionDefineClass_ID;//SymbType可能为"普通"  "端子"  "插针"
    QMdiSubWindow *mdisubwindow;
    QString dwgFileName;
    bool FlagSetSymbolSpurHighLight=false,FlagSetTerminalHighLight=false,OpenFinished=false,FlagNewLib=false,FirstOpen=true;
    int SymbolIdInDB,UnitIdInDB,Page_IDInDB,LoadAllUnitMode;
    qlonglong lBlockID=-1;
    QString BlkPath;
    IMxDrawResbuf *BlkResp;
    QStringList ListAllDirSymbols;
    int PickPointCount;
    IMxDrawPoint* Pt1;
    IMxDrawPoint* Pt2;
    IMxDrawResbuf *RespSelectedModifyId ;
    //IMxDrawResbuf *RespSelectedId;
    QString LastCommandName;
    //DialogSymbolAttribute *dlgSymbolAttribute;
    int ConnectLineDir=0;//0:未确定 1:先水平后垂直 2：先垂直后水平
    int MultiLineDir=0;//0:未确定 1:先水平后垂直 2：先垂直后水平
    QList<stPoint> DrawPoints;
    int DrawMode;
    int DrawLineCount;
    int DrawLineGap;
    bool IsDrawingMultiLine=false,UpdateCursorPos=false,IsDrawingWholeUnit=false,FlagAutoConnectLine=true,DoingGridEdit=false;
    double WholeUnitTermsGap;
    QList<stPoint> listSelectPort;//多线绘制中元件端口选择模式中所选择的端口ID记录
    QList<IMxDrawEntity*> ListSelectEntys;
    QStringList ListDeletedEntyInfo;//DbId,FunDefine,Symbol_Category,Symbol_Remark,Tag,ConnNum_Logic,ConnNum
    QList<int> ListLoadingDbID;
    int CurEqualDrawMode=0;//0:Symbol 1:Terminal
    QList<IMxDrawPoint*> ListInitGridEditPos;
    QString NewSymbolDwgName;
    bool IsDoingCommand=false,IsDoingSymbolEdit=false;
    bool IsDrawingMultiLib=false;
    QString MultiLibFilePath,LoadingTextStr;
    //QString AddTerminalTag;
    //int AddTerminalDesignation;

private:
    Ui::formaxwidget *ui;
    QList<stLayerPara> layertypes;
    QList<stTextStyle> styles;
    QTimer *timerAutoSaveDelay;
    bool WaitingForSaveDwg=false;
    bool IsSavedBeforeClose=false;
signals:
    void SignalCloseMdiWnd(int Mode);
    void GetUrPoint(IMxDrawPoint* frstPt);
    void SignalDrawAttrDefDone(QString Tag,qlonglong AttrDefID);
    void SignalDrawAttrDefDelete(QString Tag,qlonglong AttrDefID);
    void UpdateProjectUnits();
    void UpdateProjectTerminals();
    void SigalShowSpurAttr(int Symbol_ID);
    void SigalShowTerminalAttr(int Mode,int Terminal_ID);
    void UpdateCounterLink(int Link_ID,QString LinkText);
    void SignalUpdateSpur(int Symbol_ID);
    void SignalUpdateTerminal(int Terminal_ID);
    void SignalSelectDone(int Mode);
    void SignalUpdateSymbolLib(QString CurSelectSymb2Class_ID);
    void SignalSetCurMdiActive();
    void SignalUpdateDwgBlkTagByPage_ID(int Page_ID,QString Handle,QString TagStr,QString ProjectStructure_ID);
    void ConnectLinesChanged(int pageId);
private slots:
    void on_axWidget_ImplementCommandEvent(int iCommandId);
    void on_axWidget_DynWorldDraw(double dX, double dY, IDispatch *pWorldDraw, IDispatch *pData, int &pRet);
    void SlotEditSymbolWndClosed();
    void on_axWidget_CommandEnded(const QString &sCmdName);
    void on_axWidget_SelectModified(IDispatch *pAryId, IDispatch *pModifyId, bool isAdd);
    void on_axWidget_MouseEvent(int lType, double dX, double dY, int &lRet);
    void on_axWidget_MxKeyDown(int lVk, int &pRet);
    void on_axWidget_ObjectModifyed(const qlonglong &lId, bool isErase);
    void on_axWidget_CommandWillStart(const QString &sCmdName);
    void SlotUpdateLib(QString CurSelectSymb2Class_ID);
    void on_axWidget_OpenFileComplete();
    void on_axWidget_InitComplete();
    void InitAxwidget();
    void AutoSave();
    void NewTerminalStrip();//插入新端子排并设定新插入图纸的端子
    void AddExistedTerminal();//插入已有端子
    void SendUpdateTerminalSignalToMainWindow();
    void ShiftTerminalConnect();//切换选中的端子的连接点
    void TransformToLine();//切换至普通导线
    void TransformToShortageLine();//切换至短接片
};

#endif // FORMAXWIDGET_H
