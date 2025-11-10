#ifndef COMMON_H
#define COMMON_H

#include "mxdrawxlib.h"
#include "DrawStyle.h"
#include <QStandardItemModel>
#include <QDesktopWidget>
#include <QFile>
#include <QDebug>
#include <QCheckBox>
#include <QTableWidget>
#include <QLabel>
#include <QStringList>
#include <QDir>
#include <QtSql>
#include <QMessageBox>
#include <qt_windows.h>
#include <QFileInfo>
#include <QFileDialog>
#include <QMdiSubWindow>
#include <QMenu>
#include <QAction>
#include "bqgraphicsitem.h"
#include "bqgraphicsscene.h"
#include "widget/mygraphicsview.h"
//#define DEBUGMODE 1
#define PIC_BASE_PATH "D:/T-Designer/UnitPicture"
#define PROJECT_PIC_PATH "/img"
using namespace MxDrawXLib;
extern QSqlDatabase  T_LibDatabase;
extern QSqlDatabase  T_ProjectDatabase;
extern QString CurProjectPath;
extern QString CurProjectName;
extern int CurComponentCount;
extern QAxWidget *GlobalBackAxWidget;
extern IMxDrawApplication *pApp;
extern QList<QColor> ListTagColor;

//1:只看信息熵 2：只看测试代价 3：信息熵优先 4：测试代价优先
enum TestPointSort
{
    InformationEntropOnly=1,		//只根据信息熵排序，默认 0
    TestCostOnly,                   //只根据测试代价
    InformationEntropFirst,         //偏好信息熵
    TestCostFirst                   //偏好测试代价
};

class TestPoint
{
public:

    TestPoint() {}
    TestPoint(QString& name, double data):point_name(name), calculate(data){}

    QString point_name;

    double calculate;       //信息熵的结果

    double test_cost;       //测试代价

    double pref_data;       //用于存放根据偏好排序时计算的值

    static bool compareTestPointInformationEntropOnly(const TestPoint &pt1, const TestPoint &pt2){return pt1.calculate < pt2.calculate;}// 用于对比的 函数 只根据信息熵

    static bool compareTestPointTestCostOnly(const TestPoint &pt1, const TestPoint &pt2){return pt1.test_cost < pt2.test_cost;}// 用于对比的 函数  只根据测试代价

    static bool compareTestPointPref(const TestPoint &pt1, const TestPoint &pt2){return pt1.pref_data < pt2.pref_data;}// 用于对比的 函数      根据偏好
};

#define information_pref_main 90.0                  //这个用来在根据信息熵偏好排序中计算，表示偏好中主要部分的占比，按照总体100计算，注意该值不能超过100

#define test_cost_pref_main 90.0                 //这个用来在根据测点代价偏好排序中计算，表示偏好中主要部分的占比，按照总体100计算，注意该值不能超过100


#define LocalDataBasePath "C:/TBD/data"
//#define LocalProjectDefaultPath "C:/TBD/MyProjects" 为方便调试，暂时把目的定义到项目目录中
#define LocalProjectDefaultPath "D:/SynologyDrive/Project/T_DESIGNER/MyProjects"

#ifdef PI
#undef PI
#endif
#define PI 3.1415926535
#define minDelta 0.2
extern QString FindLocalFileFromPath(const QString &strFilePath, const QString filename);
extern void LoadPicTag(QString StrTag, MyGraphicsView *graphicsView);
extern void LoadLbPicture(QLabel *pLabel,QString Path);
extern void wirteGlobalVer(QAxWidget* tmp_MxDrawWidget,QString DicName,QString sName, IMxDrawResbuf* res);
extern IMxDrawResbuf* readGlobalVar(QAxWidget* tmp_MxDrawWidget,QString DicName,QString sName);
extern QList<IMxDrawPolyline*> GetTermEnty(QAxWidget *mAxwidget,QString BlkName);
extern QList<IMxDrawPolyline*> GetCurrentSpaceTerms(QAxWidget *mAxwidget);
extern void SetCurLayer(QAxWidget* tmp_MxDrawWidget,QString sLayerName);
extern bool SetCurLayerVisible(QAxWidget* tmp_MxDrawWidget,QString sLayerName,bool Visible);
extern void UnitSymbolsView(QString PathDwg,QString PathJpg,QLabel *mLabel,bool Reload);
extern bool EntyIsErased(QAxWidget *mAxwidget,IMxDrawEntity *Enty);
extern QString GetAttrDefTextString(QAxWidget* tmp_MxDrawWidget,QString Tag);
extern qlonglong DrawAttrDef(QAxWidget* tmp_MxDrawWidget,double dInsertionPointX,double dInsertionPointY,QString Tag,QString Text);
extern void DeleteAttrDef(QAxWidget* tmp_MxDrawWidget,QString Tag);
extern void AddAttrToBlock(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkEnty,IMxDrawAttributeDefinition *attrdef,QString TextStr);
extern void CopyAttr(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkEntyOld,IMxDrawBlockReference *BlkEntyNew);
extern void FindAttrDefAndAddAttrToBlock(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkEnty,QString ConnNum_Logic,QString ConnNum);
extern void GetAttrRange(QAxWidget* tmp_MxDrawWidget,QString BlkName,QString TagDef,double &deltaminx,double &deltamaxx,double &deltaminy,double &deltamaxy);
extern bool StrIsNumber(QString Str);
extern bool StrIsDouble(QString Str);
extern QString GetGaoCengNameByPageID(int Page_ID);
extern QString GetPageNameByPageID(int Page_ID);
extern QString BuildCanonicalPagePrefix(const QString &rawPrefix, const QString &pageCode);
extern QString BuildCanonicalPageName(const QString &rawPrefix, const QString &pageCode, const QString &baseName);
extern QString ExtractPagePrefix(const QString &fullName);
extern QString ExtractPageBaseName(const QString &fullName);
extern void SplitPagePrefix(const QString &prefix, QString *gaoceng, QString *pos, QString *pageCode);
extern QStringList PageNameCandidates(const QString &fullName);
extern QString IncrementPageBaseName(const QString &baseName);
extern int FindFirstPageIDUnderStructure(int projectStructureId);
extern bool UpdateProjectStructureDesc(const QString &structureId, const QString &structureInt, const QString &desc, int parentId = -1);
extern void RemoveEmptyStructureNodes(int projectStructureId);
extern QString GetTypeBySymb2Class_ID(QString Symb2Class_ID);
extern QString GetProjectStructureIDByPageID(int Page_ID);//for Unit Structure_ID=5
extern QString GetProjectStructureStrByProjectStructureID(int ProjectStructure_ID);
extern QString GetPosProjectStructure_IDByGaocengAndPos(QString GaocengStr,QString PosStr);
extern QString GetPageProjectStructure_IDByGaocengAndPos(QString GaocengStr,QString PosStr,QString PageInt);
extern void GetPageGaocengAndPos(int PageID,QString &Gaoceng,QString &Pos);
extern int GetUnitStripIDBySymbolID(QString SymbolID,int Type);
extern int GetTerminal_IDByTerminalInstanceID(int TerminalInstanceID);
extern QString GetComponentDTBySymbolID(QString SymbolID,int Type);
extern int GetUnitStripIDByTermID(int Type,int TermID,QString &DT);
extern int GetSymbolIDByTermID(int Type,QString TermID);
extern void GetUnitTermimalGaocengAndPos(int Type,int ID,QString &Gaoceng,QString &Pos);
// 缓存版本：使用 ProjectDataCache 避免重复查询
extern void GetUnitTermimalGaocengAndPos_Cached(class ProjectDataCache *cache, int Type, int ID, QString &Gaoceng, QString &Pos);
extern void UpdateBlockAttr(IMxDrawBlockReference *BlkEnty,QString TagStr,QString TextStr);
extern IMxDrawPoint* GetBlockAttrPos(IMxDrawBlockReference *BlkEnty,QString Tag);
extern QString GetBlockAttrTextString(IMxDrawBlockReference *BlkEnty,QString Tag);
extern int InsertRecordToProjectStructure(int Mode,QString GaocengStr,QString PosStr,QString PageStr);
extern QString GetDwgDicData(QString DwgPath,QString BlkName,QString ParaName);
extern QStringList GetBlockTermData(QAxWidget *mAxwidget,QString BlkName,int TermIndex);
extern QStringList GetDwgTermData(QString DwgPath,QString BlkName,int TermIndex);
extern int GetDwgTermCount(QString DwgPath,QString BlkName);
extern void LoadCbSymbolPattern(QString SymbolName,QComboBox *CbSymbolPattern);
extern void UpdateDBSymbolInfoByBlkEnty(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkModifyed,QString Page_ID,QString Equipment_ID);
extern int InsertDBSymbolInfoByBlkEnty(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *blkEnty,QString Page_ID,QString Equipment_ID);
extern int UpdateTerminalInfoBySymb2Lib_ID(QString Symb2Lib_ID,QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *blkEnty,QString Page_ID,QString MaxTerminalStrip_ID,QString Designation);
extern int UpdateSymbolInfoBySymb2Lib_ID(QString Symb2Lib_ID,QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *blkEnty,QString Page_ID,QString MaxEquipment_ID,QString Designation);
extern int AddSymbTblAndSymb2TermInfoTbl(QString LibEquipment_ID,QString MaxEquipment_ID,QString EquipmentTemplate_ID,QStringList ListSymbolSpurInfo);
extern IMxDrawPoint* GetSymbolBlockTermPos(QAxWidget *mAxwidget,IMxDrawBlockReference *BlkEnty,QString LD_SYMB1LIB_TERMPOINT);
extern void CreateLayer(QAxWidget *mAxwidget,QString sLayerName);
extern void SetLayerColor(QAxWidget *mAxwidget,QString sLayerName,MxDrawMcCmColor color);
extern int GetMaxIDOfDB(QSqlDatabase DataBase,QString TableName,QString ColumnName);
extern int GetMaxIDOfLibDatabase(QSqlDatabase DataBase,QString TableName,QString ColumnName);
extern int GetMaxIDOfLibDatabaseByLevel(QSqlDatabase DataBase,QString TableName,QString ColumnName,QString Level,QString ParentNo);
extern void AddAttrToWireBlock(IMxDrawBlockReference *BlkEnty,int Mode,QString ConnectionNumber,QString Wires_Color,QString Wires_Diameter);
extern void AddAttrToBlockBesideDefAttr(QAxWidget* tmp_MxDrawWidget,int Direction,IMxDrawBlockReference *BlkEnty,QString TagDef,QString TagNew,QString TextStr,McColor mccolor);
extern void LoadLinkText(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference* BlkEnty,QString RetStrLinkTag ,QString LinkText,QString RetStrLinkTextPosition,QString SymbolName);
extern bool MyInsertBlock(QAxWidget *mAxwidget,QString BlkPath,QString BlkName);//通过dwg文件导入块
extern QString GetSymbolDescBySymb2Lib_ID(QString Symb2Lib_ID);
extern QString GetFunctionDefineNameBySymb2Lib_ID(QString Symb2Lib_ID);
extern int GetStrLastNum(QString Str);
extern QString GetStrRemoveLastNum(QString Str);
extern QString GetLineDir(IMxDrawLine *Line);
extern int CheckLineCDPCross(IMxDrawLine *Line,QString Page_ID);
extern bool CheckProjectStructure_IDSameOrNot(QString PageProjectStructure_ID1,QString UnitProjectStructure_ID2);
extern bool CheckTerminalBeside(int Terminal_ID,QAxWidget* tmp_MxDrawWidget);
extern bool CheckSpinBeside(int Symbol_ID,QAxWidget* tmp_MxDrawWidget);
extern int CheckBlackBox(QAxWidget* tmp_MxDrawWidget,double posx,double posy,int Symbol_ID);
extern int CheckStructBox(QAxWidget* tmp_MxDrawWidget,double posx,double posy);
extern void SetAllAttrDefPos(QAxWidget* tmp_MxDrawWidget,double basex,double basey);
extern QString InsertOrUpdateSymb2Lib(int Mode,QString UpdateSymb2Class_ID,QString FunctionDefineClass_ID,QString SymbolFileName,int TermCount);
extern QFileInfoList GetFileList(QString path);
extern int GetNodeCountBySymb2TermInfo_ID(QString Symb_ID,int Category);
extern bool IsSourceConn(QString Symb2TermInfo_ID,int Category);
extern bool IsExecConn(QString Symb2TermInfo_ID,int Category);
extern void UpdateKnownLineValidRoadCnt(QStringList &listLinkRoad,QStringList &KnownLineValidRoadCnt);
extern QString GetUnitSpurStrBySymbol_ID(QSqlQuery QuerySymbol);
extern QString GetUnitSpurStrBySymbol_ID_Cached(class ProjectDataCache* cache, int symbolId, const QString& designation);
extern int GetSourcePriorBySymbolID(QString SymbolID);
extern QString GetLibIDBySymbolID(int SymbolID);
extern void UpdateComponentString(QString &StrDefinedComponent,QString SymbolID,QString Category,QString MirrorCount);
extern void UpdateListFinalLinkInfoOrder(QStringList &ListFinalLinkInfo);
extern void UpdateJmplInfo(QStringList &ListJmplInfo);
extern void UpdateEquipmentTModelDiag(QStringList ListJmplInfo);//镜像Count>1的SymbolID对应的元件TModelDiag描述
extern QString MirroredStrOneTime(QString StrTModelDiag,QString StrTermInModel);
extern QString GetMirroredStr(QString StrTModelDiag,QString StrTermInModel,QString MirrorCount);
extern QString GetTModelOfComponent(QString SymbolID,QString Category,int TModelType);
extern QStringList GetTermNameListBySymbolID(QString SymbolID,QString Catergory);
extern QStringList GetCurrentNameBySymbolID(QString StrTModel,QString SymbolID,QString Catergory,QString MirrorNum);
extern int GetMirrorIndex(QStringList ListFinalLinkInfo,QString SymbolID,QString Catergory,QString LinkId);
extern void GetHrnAndIniInfoOfComponent(QString &Strhrn,QString &Strini,QString StrSystemDefine);
extern bool CheckIfLinkSpurIsNew(QStringList ListFinalLinkInfo,int Curindex);//检查当前链路是否是新的子块
extern QStringList GetSubComponentList(QString TModelDiag);//筛选出子器件
extern void CompileStructure(QString StrUnitDesc,QString SubComponentName,QStringList &ListEnumName,QStringList &ListEnumTypeName,QStringList &ListEnumVal,QStringList &ListIniVal,QStringList &ListCmdObsVal);//筛选出Enum
extern void SortTestPoint(QList<TestPoint> &m_TestPoint,int type);
extern bool CheckLinkRoad(QString LineStr,QStringList KnownLineValidRoadCnt);
extern int GetUnitStripOtherSideTerm(QString &Symb2TermInfo_ID,int &Category);
extern QList<QStringList> GetLinkRoadByUnitStripID(QString Symb2TermInfo_ID);//获取端口信号链路
extern QString GetLinkRoadBySymbol(int Symbol_ID);//获取信号链路(针对功能子块)
extern QStringList MakeListFinalLinkInfo(QStringList ListExecSpurID);
extern QString GetSubUnitBySymbolID(QString SymbolID,QString Catergory);
extern bool PointsIsCovered(IMxDrawPoint *Point1,IMxDrawPoint *Point2);
extern bool CheckExistTerminal(IMxDrawPoint *Point,int Page_ID);
extern QStringList GetShortJumpTerminalInstance(QString TerminalInstanceID);
extern QString GetShortJumpVertualLine(QString TerminalInstanceID1,QString TerminalInstanceID2);
extern QString TransformTModelToTModelDiag(QString StrTModel);
extern QStringList GetListTermNameByTModel(QString TModel,QString CurrentInOutName);
extern QString GetRangeValByTModel(QString TModel,QString CurrentInOutName,QString Val,QString Type);
extern QString m_dragText;
extern QStringList findImagesInDir(const QDir &dir, QStringList &imageNames);
//extern QString genTagInfoFromScene(const QGraphicsScene &scene, int tagColor);
extern QString genTagInfoFromScene(const BQGraphicsScene &scene, int tagColor);
extern QString copyImageToDirectory(const QString &sourceImagePath, const QString &baseDirPath, const QString &subDirName);
extern void SlotDrawTag(MyGraphicsView *graphicsView, int Type, QColor mColor);
extern void SlotChangeColor(MyGraphicsView *graphicsView, QColor mColor);
extern void processPictureInfo(const QString &picture, const QString &supplier, const QStringList &searchDirs,
                               QMap<QString, QString> &imagePaths, QMap<QString, QString> &tagInfos);
extern bool isTagInfoValid(const QString &strTagInfo);
class common
{
public:
    common();
};
class MyCheckBox : public QCheckBox
{
public:
    MyCheckBox(QString text,QWidget *parent = Q_NULLPTR);
    MyCheckBox(QWidget *parent = Q_NULLPTR);

protected:
    void mouseReleaseEvent(QMouseEvent *e);
};

#endif // COMMON_H
