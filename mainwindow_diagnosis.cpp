#include "mainwindow.h"
#include "ui_mainwindow.h"
#include <ActiveQt/QAxObject>
#include <ActiveQt/QAxWidget>
#include <QTimer>
#include <QFileInfo>
#include <QFile>
#include <QDir>
#include <QStringList>
#include <QMenu>
#include <QSet>
#include <QInputDialog>
#include <QShortcut>
#include <QSqlError>
#include <cmath>
#include "BO/containerrepository.h"
#include "widget/containertreedialog.h"
#include "DO/containerentity.h"
#include "widget/containerhierarchyutils.h"
#include "widget/functionmanagerdialog.h"
#include "widget/functioneditdialog.h"
#include "BO/function/functionrepository.h"
#include "demo_projectbuilder.h"

using namespace ContainerHierarchy;

namespace {

constexpr double kTestCostThreshold = 0.8;

bool shouldSkipConnectionId(const QString &id)
{
    if (id.isEmpty())
        return true;
    return id.contains(":C") || id.contains(":G") || id.contains(":1") ||
           id.contains(":2") || id.contains(":3");
}

double parseTestCost(const QVariant &value)
{
    if (!value.isValid())
        return 1.0;
    bool ok = false;
    double cost = value.toDouble(&ok);
    if (!ok) {
        QString text = value.toString().trimmed();
        if (text.contains(',')) {
            text = text.section(',', 0, 0).trimmed();
        }
        cost = text.toDouble(&ok);
    }
    if (!ok)
        return 1.0;
    return cost;
}

int parsePortId(const QString &text, bool *okOut)
{
    QString normalized = text;
    const int dotIndex = normalized.indexOf('.');
    if (dotIndex > 0)
        normalized = normalized.left(dotIndex);
    bool ok = false;
    const int portId = normalized.toInt(&ok);
    if (okOut)
        *okOut = ok;
    return portId;
}

double computeMtbf(int componentCount, int connectionCount)
{
    constexpr double kComponentMtbf = 80000.0;
    constexpr double kConnectionMtbf = 60000.0;
    constexpr double kMinMtbf = 2000.0;
    constexpr double kMaxMtbf = 80000.0;

    auto accumulateLogReliability = [](int count, double baseMtbf) -> double {
        if (count <= 0 || baseMtbf <= 0.0)
            return 0.0;
        const double perHourReliability = std::exp(-1.0 / baseMtbf);
        return count * std::log(perHourReliability);
    };

    const double logReliability =
        accumulateLogReliability(componentCount, kComponentMtbf) +
        accumulateLogReliability(connectionCount, kConnectionMtbf);

    double mtbf = kMaxMtbf;
    if (logReliability < 0.0) {
        const double reliability = std::exp(logReliability);
        const double denom = -std::log(reliability);
        if (denom > 0.0 && std::isfinite(denom)) {
            mtbf = 1.0 / denom;
        }
    }
    if (!std::isfinite(mtbf) || mtbf <= 0.0) {
        mtbf = kMaxMtbf;
    }
    if (mtbf > kMaxMtbf) mtbf = kMaxMtbf;
    if (mtbf < kMinMtbf) mtbf = kMinMtbf;
    return mtbf;
}

double computeMttr(int componentCount, int connectionCount)
{
    constexpr double kRepairHours = 5.0 / 60.0; // 5 minutes
    constexpr double kTestStepHours = 4.0 / 60.0; // 4 minutes
    constexpr double kMinimumHours = 1.0 / 12.0; // 5 minutes

    const int totalElements = std::max(1, componentCount + connectionCount);
    const double testSteps = std::log2(static_cast<double>(totalElements));
    double mttr = kRepairHours + kTestStepHours * testSteps;
    if (mttr < kMinimumHours)
        mttr = kMinimumHours;
    return mttr;
}

}

void MainWindow::on_BtnRefreshExecConn_clicked()
{
    QSqlQuery QuerySymbol(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symbol WHERE ExecConn= TRUE";
    QuerySymbol.exec(StrSql);
    QString Gaoceng,Pos;
    ui->tableWidgetExecConn->setRowCount(0);
    while(QuerySymbol.next())
    {
        GetUnitTermimalGaocengAndPos(0,QuerySymbol.value("Symbol_ID").toInt(),Gaoceng,Pos);
        qDebug()<<"Equipment_ID="<<QuerySymbol.value("Equipment_ID").toInt()<<",Gaoceng="<<Gaoceng<<",Pos="<<Pos;
        if((ui->CbExecConnGaoceng->currentText()!="高层")||(ui->CbExecPos->currentText()!="位置"))
        {
            if((ui->CbExecConnGaoceng->currentText()!="高层")&&(ui->CbExecConnGaoceng->currentText()!=Gaoceng)) continue;
            if((ui->CbExecPos->currentText()!="位置")&&(ui->CbExecPos->currentText()!=Pos)) continue;
        }
        ui->tableWidgetExecConn->setRowCount(ui->tableWidgetExecConn->rowCount()+1);
        QTableWidgetItem *ItemExecConn=new QTableWidgetItem("");
        ItemExecConn->setCheckState(Qt::Unchecked);
        ItemExecConn->setData(Qt::UserRole,QuerySymbol.value("Symbol_ID").toInt());
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,0,ItemExecConn);//源端口
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,1,new QTableWidgetItem(Gaoceng));//高层
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,2,new QTableWidgetItem(Pos));//位置
        QSqlQuery QueryEquipment(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
        QueryEquipment.exec(StrSql);
        if(QueryEquipment.next())
        {
            ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,3,new QTableWidgetItem(QueryEquipment.value("DT").toString()));//元件名称
        }
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,4,new QTableWidgetItem(GetUnitSpurStrBySymbol_ID(QuerySymbol)));//功能子块名称
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,5,new QTableWidgetItem(QuerySymbol.value("LinkRoad").toString()));//诊断链路
    }

}

void MainWindow::on_BtnShowLinkRoad_clicked()
{
    //创建新的mdi
    formaxwidget *formMxdraw=new formaxwidget(this);
    formMxdraw->setWindowTitle("诊断链路图");
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
    QList<int> ListSymbolID;
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
            ListSymbolID.append(ui->tableWidgetExecConn->item(i,0)->data(Qt::UserRole).toInt());
    }
    formMxdraw->DrawDiagnoseLinkRoad(ListSymbolID);
}

/*
void MainWindow::MakeListFinalLinkInfo()
{
    //QStringList ListFinalLinkInfo;
    ListFinalLinkInfo.clear();
    int Linkid=0;
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
        {
            Linkid++;
            QString StrLinkRoad=GetLinkRoadBySymbol(ui->tableWidgetExecConn->item(i,0)->data(Qt::UserRole).toInt());
            ui->tableWidgetExecConn->item(i,5)->setText(StrLinkRoad);
            QStringList ListAllLinkRoad;
            while(1)
            {
                if(!(StrLinkRoad.contains("[")&&StrLinkRoad.contains("]"))) break;
                int index1=StrLinkRoad.indexOf("[");
                int index2=StrLinkRoad.indexOf("]");
                ListAllLinkRoad.append(StrLinkRoad.mid(index1+1,index2-index1-1));
                StrLinkRoad=StrLinkRoad.mid(index2+1,StrLinkRoad.count()-index2-1);
            }
//qDebug()<<"while(1) ListAllLinkRoad="<<ListAllLinkRoad;
            if(ListAllLinkRoad.count()==2)//正负两条链路
            {
                //将优先级高的链路放在ListAllLinkRoad前面
                for(int j=0;j<ListAllLinkRoad.count();j++)
                {
                    QString StrSourceConn=ListAllLinkRoad.at(j).split(";").last();
                    if((StrSourceConn.split(",").count()!=2)||(StrSourceConn.split(",").at(1)!="0"))
                    {
                        ListAllLinkRoad.removeAt(j);
                        continue;
                    }
                    int SourcePrior=GetSourcePriorBySymbolID(StrSourceConn.split(",").at(0));
                    if(SourcePrior<0)
                    {
                        ListAllLinkRoad.removeAt(j);
                        continue;
                    }
                    for(int k=j;k<ListAllLinkRoad.count();k++)
                    {
                        QString StrCompareSourceConn=ListAllLinkRoad.at(k).split(";").last();
                        if((StrCompareSourceConn.split(",").count()!=2)||(StrCompareSourceConn.split(",").at(1)!="0")) continue;
                        int CompareSourcePrior=GetSourcePriorBySymbolID(StrCompareSourceConn.split(",").at(0));
                        if(SourcePrior>CompareSourcePrior)//数字小的优先级高
                        {
                            //j k 互换
                            QString tmpStr=ListAllLinkRoad[j];
                            ListAllLinkRoad[j]=ListAllLinkRoad[k];
                            ListAllLinkRoad[k]=tmpStr;
                        }
                    }
                }//将优先级高的链路放在ListAllLinkRoad前面
//qDebug()<<"排序完成 ListAllLinkRoad="<<ListAllLinkRoad;
                //根据ListAllLinkRoad生成诊断文件CurProjectName.jmpl
                QStringList ListLinkRoad=ListAllLinkRoad.at(0).split(";");
                ListFinalLinkInfo.append(ListLinkRoad.at(ListLinkRoad.count()-1)+","+QString::number(Linkid)+",false,1,0");
                for(int k=ListLinkRoad.count()-2;k>=0;k--)
                {
                    //if((j>0)&&(k==(ListLinkRoad.count()-1))) continue;//源只统计一次
                    if(k==0) continue;//执行器只统计一次
                    //if((j!=(ListAllLinkRoad.count()-1))&&(k==0)) continue;//执行器只统计一次
                    ListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1,1");
                }
                ListLinkRoad=ListAllLinkRoad.at(1).split(";");
                for(int k=ListLinkRoad.count()-1;k>0;k--)
                {
                    if(k==(ListLinkRoad.count()-1)) continue;//源只统计一次
                    ListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1,2");
                }
                ListFinalLinkInfo.append(ListLinkRoad.at(0)+","+QString::number(Linkid)+",false,1,3");
            }//end of if(ListAllLinkRoad.count()==2)//正负两条链路
        }//end of if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
    }//end of for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
//qDebug()<<"ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateJmplInfo(ListFinalLinkInfo);//更新ListJmplInfo中相同功能子块出现的次数
//qDebug()<<"重新排序前a，ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateListFinalLinkInfoOrder(ListFinalLinkInfo);//根据功能子块出现的次数对每一条单链重新排序
    //return ListFinalLinkInfo;
}
*/

void MainWindow::RemakeLinkRoad(QStringList ListExecSpurID)
{
    ListFinalLinkInfo=MakeListFinalLinkInfo(ListExecSpurID);

    qDebug()<<"MakeListFinalLinkInfo，ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateEquipmentTModelDiag(ListFinalLinkInfo);//镜像SymbolID对应的元件TModelDiag描述
    qDebug()<<"UpdateEquipmentTModelDiag，ListFinalLinkInfo="<<ListFinalLinkInfo;
    //根据链路生成诊断文件CurProjectName.jmpl CurProjectName.xmpl,CurProjectName.hrn CurProjectName.ini
    QString Strjmpl,Strhrn,Strini,StrSystemConnection;
    StrSystemDefine="\r\nclass Test {\r\n";

    QFile jmplfile(CurProjectPath+"/"+CurProjectName+".jmpl");
    jmplfile.remove();
    jmplfile.open(QIODevice::WriteOnly);

    //CurProjectName.jmpl
    QSqlQuery QueryEnumerations = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr;
    SqlStr = "SELECT * FROM Enumerations";
    QueryEnumerations.exec(SqlStr);
    while(QueryEnumerations.next())
    {
        Strjmpl+="\r\n";
        Strjmpl+="enum "+QueryEnumerations.value("EnumName").toString();
        Strjmpl+="{"+QueryEnumerations.value("EnumMember").toString()+"};";
    }
    Strjmpl+="\r\n\r\n";
    //器件T语言
    for(int i=0;i<ListFinalLinkInfo.count();i++)
    {
        ListFinalLinkInfo[i]=ListFinalLinkInfo.at(i).split(",").at(0)+","+ListFinalLinkInfo.at(i).split(",").at(1)+","+ListFinalLinkInfo.at(i).split(",").at(2)+",false,"+ListFinalLinkInfo.at(i).split(",").at(4)+","+ListFinalLinkInfo.at(i).split(",").at(5);
    }
    QString StrLastePort_out;
    QString LastLinkId="0";
    for(int i=0;i<ListFinalLinkInfo.count();i++)
    {
        bool FlagSpurIsNew=true;
        if(!CheckIfLinkSpurIsNew(ListFinalLinkInfo,i)) FlagSpurIsNew=false;
        //连接关系
        QString DT=GetComponentDTBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt());
        QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),0);//用于获取链路信号
        QString StrTModelDiag=GetTModelOfComponent(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),1);//用于诊断
        //获取当前功能子块的镜像号次
        int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),ListFinalLinkInfo.at(i).split(",").at(2));
        //if(ListFinalLinkInfo.at(i).split(",").at(4)!="1") DT=DT+"mirror"+QString::number(NumIndex);
        //从T语言中提取含有Symbol的Current变量名
        qDebug()<<"ListFinalLinkInfo.at(i).split().at(0)="<<ListFinalLinkInfo.at(i).split(",").at(0)<<",ListFinalLinkInfo.at(i).split().at(1)="<<ListFinalLinkInfo.at(i).split(",").at(1);
        QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),QString::number(NumIndex));
        qDebug()<<"TermNameList="<<TermNameList;
        if((ListFinalLinkInfo.at(i).split(",").at(2)==LastLinkId)&&FlagSpurIsNew)
            StrSystemConnection+="\r\n        "+StrLastePort_out+" = "+DT+"."+TermNameList.at(0)+";";
        StrLastePort_out=DT+"."+TermNameList.at(1);
        LastLinkId=ListFinalLinkInfo.at(i).split(",").at(2);

        if(!FlagSpurIsNew) continue;
        if(ListFinalLinkInfo.at(i).split(",").at(3)=="true") continue;

        //将器件实例化添加进StrSystemDefine，将连接关系添加进StrSystemConnection
        StrSystemDefine+="\r\n"+StrTModelDiag.mid(StrTModelDiag.indexOf("class")+5,StrTModelDiag.indexOf("{")-StrTModelDiag.indexOf("class")-5).remove(" ")+" "+DT+";";

        //添加器件class定义
        UpdateComponentString(Strjmpl,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),ListFinalLinkInfo.at(i).split(",").at(4));
        ListFinalLinkInfo[i]=ListFinalLinkInfo.at(i).split(",").at(0)+","+ListFinalLinkInfo.at(i).split(",").at(1)+","+ListFinalLinkInfo.at(i).split(",").at(2)+",true,"+ListFinalLinkInfo.at(i).split(",").at(4)+","+ListFinalLinkInfo.at(i).split(",").at(5);;
        for(int j=i;j<ListFinalLinkInfo.count();j++)
        {
            bool SkipFlag=false;
            if(ListFinalLinkInfo.at(i).split(",").at(1)=="2")
            {
                if((ListFinalLinkInfo.at(j).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(j).split(",").at(0)==ListFinalLinkInfo.at(i).split(",").at(0)))
                    SkipFlag=true;
            }
            else if(ListFinalLinkInfo.at(i).split(",").at(1)=="3")
            {
                if((ListFinalLinkInfo.at(j).split(",").at(1)=="3")&&(ListFinalLinkInfo.at(j).split(",").at(0)==ListFinalLinkInfo.at(i).split(",").at(0)))
                    SkipFlag=true;
            }
            else
            {
                if(ListFinalLinkInfo.at(j).split(",").at(1)!="2")
                {
                    int idj=GetUnitStripIDBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt());
                    int idi=GetUnitStripIDBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt());

                    if((idj==idi)&&(ListFinalLinkInfo.at(j).split(",").at(1)==ListFinalLinkInfo.at(i).split(",").at(1)))
                        SkipFlag=true;
                }
            }
            if(SkipFlag)
                ListFinalLinkInfo[j]=ListFinalLinkInfo.at(j).split(",").at(0)+","+ListFinalLinkInfo.at(j).split(",").at(1)+","+ListFinalLinkInfo.at(j).split(",").at(2)+",true,"+ListFinalLinkInfo.at(j).split(",").at(4)+","+ListFinalLinkInfo.at(j).split(",").at(5);;
        }
    }
    qDebug()<<"StrSystemDefine="<<StrSystemDefine;
    //根据StrSystemDefine将器件的Structure信息添加进Strhrn和Strini
    GetHrnAndIniInfoOfComponent(Strhrn,Strini,StrSystemDefine);
    qDebug()<<"Strjmpl="<<Strjmpl;
    qDebug()<<"StrSystemDefine="<<StrSystemDefine;
    qDebug()<<"StrSystemConnection="<<StrSystemConnection;
    jmplfile.write((Strjmpl+StrSystemDefine+"\r\n    {"+StrSystemConnection+"\r\n    }\r\n}").toLatin1().data());
    jmplfile.close();

    QFile hrnfile(CurProjectPath+"/test.hrn");
    hrnfile.remove();
    hrnfile.open(QIODevice::WriteOnly);
    hrnfile.write(Strhrn.toLatin1().data());
    hrnfile.close();

    QFile inifile(CurProjectPath+"/test.ini");
    inifile.remove();
    inifile.open(QIODevice::WriteOnly);
    inifile.write(Strini.toLatin1().data());
    inifile.close();

    //调用jmplcompiler生成.xmpl
    QProcess jmplcompiler;
    jmplcompiler.setWorkingDirectory(CurProjectPath);
    QString cmdstr="java -cp C:/TBD/data/l2compilerfull.jar gov.nasa.arc.skunkworks.io.jmpl.JmplCompiler Test test "+CurProjectPath+"/"+CurProjectName+".jmpl";
    jmplcompiler.start(cmdstr);
    jmplcompiler.waitForFinished(-1);

    //dlgFunctionManage->StrSystemDefine=this->StrSystemDefine;
}

void MainWindow::on_BtnRemakeLinkRoad_clicked()
{
    QStringList ListExecSpurID;
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
            ListExecSpurID.append(ui->tableWidgetExecConn->item(i,0)->data(Qt::UserRole).toString());
    }
    RemakeLinkRoad(ListExecSpurID);
}

void MainWindow::on_CbAllExecConn_clicked()
{
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->CbAllExecConn->isChecked())
            ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Checked);
        else
            ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Unchecked);
    }
}

void MainWindow::UpdateXmplInfo(QString FunctionID)
{
    QStringList ListExecSpurID;
    QSqlQuery QueryFunction(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Function WHERE FunctionID = "+FunctionID;
    QueryFunction.exec(StrSql);
    if(!QueryFunction.next()) return;
    QStringList ExecsList=QueryFunction.value("ExecsList").toString().split(",");

    for(int i=0;i<ExecsList.count();i++)
    {
        QString StrSpur="";
        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+ExecsList.at(i).mid(0,ExecsList.at(i).indexOf("."))+"'";
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                if(GetUnitSpurStrBySymbol_ID(QuerySymbol).split("￤").count()>1)
                {
                    if(ExecsList.at(i).mid(ExecsList.at(i).indexOf(".")+1,ExecsList.at(i).count()-ExecsList.at(i).indexOf(".")-1)==GetUnitSpurStrBySymbol_ID(QuerySymbol))
                    {
                        if(StrSpur!="") StrSpur+=",";
                        StrSpur+=QuerySymbol.value("Symbol_ID").toString();
                    }
                }
                else if(GetUnitSpurStrBySymbol_ID(QuerySymbol)!="")
                {
                    if(ExecsList.at(i).mid(ExecsList.at(i).indexOf(".")+1,ExecsList.at(i).count()-ExecsList.at(i).indexOf(".")-1).remove(" ").split("￤").contains(GetUnitSpurStrBySymbol_ID(QuerySymbol)))
                    {
                        if(StrSpur!="") StrSpur+=",";
                        StrSpur+=QuerySymbol.value("Symbol_ID").toString();
                    }
                }
            }
        }
        ListExecSpurID.append(StrSpur);
    }
    qDebug()<<"ListExecSpurID="<<ListExecSpurID;
    RemakeLinkRoad(ListExecSpurID);

    /*
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
       ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Unchecked);
    }

    QSqlQuery QueryFunction(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Function WHERE FunctionID = "+FunctionID;
    QueryFunction.exec(StrSql);
    if(!QueryFunction.next()) return;
    QStringList ExecsList=QueryFunction.value("ExecsList").toString().split(",");
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        for(int j=0;j<ExecsList.count();j++)
        {
           if(ExecsList.at(j).contains(ui->tableWidgetExecConn->item(i,3)->text())&&ExecsList.at(j).contains(ui->tableWidgetExecConn->item(i,4)->text()))
              ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Checked);
        }
    }
    on_BtnRemakeLinkRoad_clicked();*/
}

void MainWindow::StartDiagnose(QString SendCmdStr)
{
    QString modelfileName = CurProjectPath+"/test.xmpl";
    QFile file(modelfileName);
    if(file.exists())
    {
        modelfileName = modelfileName.left(modelfileName.lastIndexOf("."));
        QString program = "C:/TBD/data/l2test.exe";
        QStringList arguments;
        arguments<<modelfileName;//传递到exe的参数
        cmdDiagnose->start(program,arguments);
        cmdStarted = cmdDiagnose->waitForStarted(500);
    }

    QString jmplfileName = CurProjectPath+"/"+CurProjectName+".jmpl";
    QFile jmplfile(jmplfileName);
    if(!jmplfile.open(QIODevice::ReadOnly|QIODevice::Text))  return;
    if(jmplfile.exists())
    {
        qDebug()<<"GetGraphList";
        GetGraphList(jmplfile);
    }
    input_test_point.clear();
    qDebug()<<"GetGraphList ok";

    if(SendCmdStr!="") SendCmd(SendCmdStr,true);
}

void MainWindow::on_BtnStartDiagnose_clicked()
{
    //根据jmpl的系统描述筛选出执行器
    QFile Filejmpl(CurProjectPath+"/"+CurProjectName+".jmpl");
    if(!Filejmpl.open(QIODevice::ReadOnly)) return;
    QString StrJmpl= Filejmpl.readAll();
    StrJmpl=StrJmpl.mid(StrJmpl.indexOf("class Test {")+12,StrJmpl.count()-StrJmpl.indexOf("class Test {")-12);
    StrJmpl=StrJmpl.mid(0,StrJmpl.indexOf("{"));
    QStringList ListStrJmpl=StrJmpl.split(";");
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        for(int j=0;j<ListStrJmpl.count();j++)
        {
            if(ListStrJmpl.at(j).contains(ui->tableWidgetExecConn->item(i,3)->text()))
                ui->tableWidgetExecConn ->item(i,0)->setCheckState(Qt::Checked);
        }
    }

    DiagnoseStepNumber=0;
    QsciEdit->clear();
    StartDiagnose("");
}

void MainWindow::GetGraphList(QFile& file)
{
    Q_UNUSED(file);
    /*
    QTextStream in(&file);

    QString data = in.readAll();
    data = data.simplified();
    data = data.right(data.count() - data.lastIndexOf("class"));

//    qDebug()<<"data"<<data;

    QStringList data1 = data.split("{");

    //解析连接
    QString connect = data1[2];
    QStringList connect_data = connect.split(";");
    connect_data.removeLast();

//    qDebug()<<"connect";
    for(QString& temp_data : connect_data)
        temp_data.simplified();

    QVector<ArcData> connect_arc;

    QStringList module_data;
    QMultiMap<QString, QString>  port_data;     //用来处理模块内部连接
    QStringList keys;
    for(QString& temp_data : connect_data)
    {
        ArcData temp;
        QStringList temp_list = temp_data.split("=");

        temp.Tail = temp_list[0].simplified();
        temp.Head = temp_list[1].simplified();
        temp.Weight = 1;

        module_data.push_back(temp.Tail);
        module_data.push_back(temp.Head);

        QStringList tail = temp.Tail.split('.');
        QStringList head = temp.Head.split('.');
        QString tail_name = tail[0].simplified();
        QString tail_port = tail[1].simplified();
        QString head_name = head[0].simplified();
        QString head_port = head[1].simplified();

        if(!keys.contains(tail_name))
            keys.push_back(tail_name);
        if(!keys.contains(head_name))
            keys.push_back(head_name);

        if(!port_data.contains(tail_name, tail_port))
            port_data.insert(tail_name, tail_port);
        if(!port_data.contains(head_name, head_port))
            port_data.insert(head_name, head_port);

        connect_arc.push_back(temp);
    }

    //处理内部连接
    for(int i=0; i<keys.count(); i++)
    {
        QList<QString> values = port_data.values(keys[i]);

        if(values.count() == 1)
                continue;

        QVector<bool> visit(values.count(), false);
        for (int m = 0; m < values.size(); m++)
        {
            if(visit[m])    continue;
            visit[m] = true;

            for(int j=m; j<values.size(); j++)
            {
                if(m == j)  continue;

                QStringList m_last_data = values[m].split('_');
                QStringList j_last_data = values[j].split('_');
//                qDebug()<<"i_last_data"<<i_last_data;
//                qDebug()<<"j_last_data"<<j_last_data;
                if(m_last_data[1] == j_last_data[1] && m_last_data[2] == j_last_data[2])
                {
                    ArcData temp;
                    if(m_last_data[0].endsWith('In'))
                    {
                        temp.Tail = keys[i]+'.'+values[m];
                        temp.Head = keys[i]+'.'+values[j];
                        connect_arc.push_back(temp);
                    }
                    else
                    {
                        temp.Head = keys[i]+'.'+values[m];
                        temp.Tail = keys[i]+'.'+values[j];
                        temp.Weight = 1;
                    }

                    connect_arc.push_back(temp);

                    visit[j] = true;
                }
            }
        }
    }

    //根据数据库内的信息处理器件内部功能子块的关系，比如继电器的线圈子块控制着开关子块后面的器件
    QStringList inter_connect_port = GetInterLogicConnect();
    for(int i=0; i<inter_connect_port.count(); i = i+2)
    {
        ArcData temp;

        temp.Tail = inter_connect_port[i];
        temp.Head = inter_connect_port[i+1];
        temp.Weight = 1;

        connect_arc.push_back(temp);
    }
//    qDebug()<<"connect_arc";
//    for(int i=0; i<connect_arc.count(); i++)
//    {
//        qDebug()<<"tail"<<connect_arc[i].Tail
//               <<"head"<<connect_arc[i].Head;
//    }

    module_data.removeDuplicates();

    graph_list->Init(module_data, &connect_arc);

//    graph_list->DisplayNode();

    qDebug()<<"graph";
    QString temp_s = "SP01.ePort_out_p_n";
    graph_list->Display_DFS(&temp_s);

//    GetTestPoint();
    */
}



QList<TestPoint>  MainWindow::GetTestPoint()
{/*
    test_point.clear();

        QStringList candidate_port_name;


        for(int i=0; i<candidate_list.count(); i++)
            candidate_port_name.append(graph_list->GetModulePort(candidate_list[i].FaultSpur.split('.')[0]));

        candidate_port_name.removeDuplicates();
        for(int i=0; i<candidate_port_name.count(); i++)
            test_point.push_back(TestPoint(candidate_port_name[i], 0.0));


        for(int i=0; i<candidate_port_name.count(); i++)
        {
            QStringList front, back;
            graph_list->FindRepeat(candidate_port_name[i], candidate_port_name, front, back);

            test_point[i].calculate = CalculateRank(candidate_port_name[i], front, back);
            test_point[i].test_cost = GetTestCost(test_point[i].point_name);//(double)i/candidate_port_name.count();
  qDebug()<<"GetTestCost,point_name="<<test_point[i].point_name<<",test_cost="<<test_point[i].test_cost;
        }

        //排序前
    //    qDebug()<<"排序前";
    //    for(int i=0; i<test_pt.count(); i++)
    //        qDebug()<<test_pt[i].point_name << QString::number(test_pt[i].calculate);

        RemoveRepeatTestPoint(test_point);
        RemoveTestedPoint(test_point);
        qSort(test_point.begin(),test_point.end(),TestPoint::compareTestPointInformationEntropOnly);

    //    qDebug()<<"排序后";
    //    for(int i=0; i<test_pt.count(); i++)
    //        qDebug()<<test_pt[i].point_name << QString::number(test_pt[i].calculate);

        qDebug()<<"输出测点";
        for(int i=0; i<test_point.count(); i++)
            qDebug()<<test_point[i].point_name<<test_point[i].calculate;
*/
    return test_point;

}




double MainWindow::CalculateRank(const QString& port_name,const QStringList& front, const QStringList& back)
{
    //    if(front.empty())
    //        return INT_MAX;     //表示开头这点不可能

    //去除front里面重复的
    QStringList front_temp, back_temp;

    bool isInput = port_name.contains("In");    //判断是输出还是输入
    if(isInput)
        back_temp.push_back(port_name.split('.')[0]);
    else
        front_temp.push_back(port_name.split('.')[0]);

    for(int i=0; i<front.count(); i++)
    {
        if(!front_temp.contains(front[i].split('.')[0]))
            front_temp.push_back(front[i].split('.')[0]);
    }
    for(int i=0; i<back.count(); i++)
    {
        if(!back_temp.contains(back[i].split('.')[0]))
            back_temp.push_back(back[i].split('.')[0]);
    }


    QVector<double> front_prob, back_prob;

    for(int i=0; i<front_temp.count(); i++)
        front_prob.push_back(module_fault_prob[front_temp[i]]);

    for(int i=0; i<back_temp.count(); i++)
        back_prob.push_back(module_fault_prob[back_temp[i]]);

    //归一化处理
    double all_prob = 0.0;
    for(int i=0; i<front_prob.count(); i++)
        all_prob += front_prob[i];
    for(int i=0; i<back_prob.count(); i++)
        all_prob += back_prob[i];

    for(int i=0; i<front_prob.count(); i++)
        front_prob[i] = front_prob[i] / all_prob;
    for(int i=0; i<back_prob.count(); i++)
        back_prob[i] = back_prob[i] / all_prob;

    double work_well = 1.0;
    for(int i=0; i<front_prob.count(); i++)
    {
        work_well *= 1-front_prob[i];
    }

    double front_rank = 0.0, back_rank = 0.0;
    //计算如果成功后的熵
    for(int i=0; i<back_prob.count(); i++)
    {
        if(back_prob[i]<=0)    back_rank += 0;
        else
            back_rank += back_prob[i] * log(1/back_prob[i]);
    }
    back_rank = back_rank * work_well;
    //计算如果失败后的熵
    for(int i=0; i<front_prob.count(); i++)
    {
        if(front_prob[i]<=0)    front_rank += 0;
        else
            front_rank += front_prob[i] * log(1/front_prob[i]);
    }
    front_rank = front_rank *(1-work_well);

    qDebug()<<"输出概率"<<port_name << QString::number(front_rank) << QString::number(back_rank) <<QString::number(work_well);
    qDebug()<<"front";
    for(int i=0; i<front_temp.count(); i++)
        qDebug()<<front_temp[i]<<front_prob[i];
    qDebug()<<"back";
    for(int i=0; i<back_temp.count(); i++)
        qDebug()<<back_temp[i]<<back_prob[i];

    return front_rank + back_rank;
}



void MainWindow::RemoveRepeatTestPoint(QList<TestPoint>& test_pt)
{
    Q_UNUSED(test_pt);
/*
    //    QVector<bool> is_have(test_pt.count(), true);

    //    qDebug()<<"输出原始的所有测地";
    //    for(int i=0; i<test_pt.count(); i++)
    //        qDebug()<<test_pt[i].point_name<<test_pt[i].calculate;

    //    for(int i=0; i<test_pt.count(); i++)
    //    {

    //        for(int j=0; j < test_pt.count(); j++)
    //        {
    //            if(abs(test_pt[i].calculate - test_pt[j].calculate) > 0.0001)
    //                continue;
    //            if(test_pt[i].point_name.split('.')[0] == test_pt[j].point_name.split('.')[0])    //同一个器件的端口不进行删除
    //                continue;

    //            bool is_connect = graph_list->isDirectConnect(test_pt[i].point_name, test_pt[j].point_name);
    //            if(is_connect)
    //            {
    //                //删除一条线的
    //                if(test_pt[i].point_name.startsWith('L'))
    //                    is_have[i] = false;
    //                else if(test_pt[j].point_name.startsWith('L'))
    //                    is_have[j] = false;
    //            }
    //        }

    //    }

    //    QList<TestPoint> ans;
    //    for(int i=0; i<is_have.count(); i++)
    //        if(is_have[i])
    //            ans.push_back(test_pt[i]);

    //    test_pt = ans;


        //上面是原来的版本，只考虑加入两个点直接连在一起，那么去掉一个点
        //但是有可能有好几个点连在一起，但是他们的信息熵是不一样的，所以这种情况就选择他们中间不是线的一点，然后信息熵选择他们中间最小的，然后重建一个测点

        QList<TestPoint> new_test_pt;
        QList<QSet<int>> all_connect;      //所有连接超过1的情况，先得到所有的，然后挑选不重复的

        for(int i=0; i<test_pt.count(); i++)
        {
            QSet<int> connect_test_pt;     //注意connect_test_pt保存测点在test_pt中的位置
            connect_test_pt.insert(i);

            for(int j=0; j < test_pt.count(); j++)
            {

                if(test_pt[i].point_name.split('.')[0] == test_pt[j].point_name.split('.')[0])    //同一个器件的端口不进行删除，注意j==i的情况包含在这里了
                    continue;

                bool is_connect = graph_list->isDirectConnect(test_pt[i].point_name, test_pt[j].point_name);
                if(is_connect)
                {
                    connect_test_pt.insert(j);
                }
            }

            if(connect_test_pt.count() == 1)
                continue;

            all_connect.push_back(connect_test_pt);
        }

        QVector<bool> is_delete(all_connect.count(), false);    //如果有共同的数字，那么合并到i处，那么j处的就要删掉
        for(int i=0; i<all_connect.count()-1; i++)
        {
            if(is_delete[i])    continue;

            bool all_is_find = false;
            while(!all_is_find)
            {
                all_is_find = true;
                for(int j=i+1; j<all_connect.count(); j++)
                {
                    if(is_delete[j])    continue;

                    bool is_connect = all_connect[i].intersects(all_connect[j]);        //只要all_connect[i]和all_connect[j]中有一个共同量，那么他们相连
                    if(is_connect)
                    {
                        all_connect[i].unite(all_connect[j]);
                        is_delete[j] = true;
                        all_is_find = false;
                    }
                }
            }

        }



        QVector<bool> is_single(test_pt.count(), false);    //在得到了所有连接的端口后，记录哪些端口是不在这些连接的端口里的，单独拿出来放入结果
        for(int m=0; m<all_connect.count(); m++)
        {
            if(is_delete[m])    continue;

            TestPoint temp_test_pt;
            for(QSet<int>::iterator it = all_connect[m].begin(); it!=all_connect[m].end(); it++)
            {
                is_single[*it] = true;
                if(it ==all_connect[m].begin() )
                {
                    temp_test_pt.point_name = test_pt[*it].point_name;
                    temp_test_pt.calculate = test_pt[*it].calculate;
                    temp_test_pt.test_cost = test_pt[*it].test_cost;
                    continue;
                }

                if(temp_test_pt.point_name.startsWith('L'))
                {
                    if(!test_pt[*it].point_name.startsWith("L"))
                        temp_test_pt.point_name = test_pt[*it].point_name;
                }

                if(temp_test_pt.calculate > test_pt[*it].calculate)
                    temp_test_pt.calculate = test_pt[*it].calculate;

                if(temp_test_pt.test_cost > test_pt[*it].test_cost)
                    temp_test_pt.test_cost = test_pt[*it].test_cost;

            }
            new_test_pt.append(temp_test_pt);
        }

        for(int i=0; i<is_single.count(); i++)
        {
            if(!is_single[i])
                new_test_pt.push_back(test_pt[i]);
        }

        qDebug()<<"整合后";
        for(int i=0; i<new_test_pt.count(); i++)
            qDebug()<<new_test_pt[i].point_name <<new_test_pt[i].calculate<<new_test_pt[i].test_cost;

        test_pt = new_test_pt;
        */
}

void MainWindow::RemoveTestedPoint(QList<TestPoint>& test_pt)
{
    Q_UNUSED(test_pt);
/*
    QVector<bool> is_have(test_pt.count(), true);

    for(int i=0; i<test_pt.count()-1; i++)
    {

        if(input_test_point.find(test_pt[i].point_name) != input_test_point.end())
        {
            is_have[i] = false;
            continue;
        }

        QString module_name = test_pt[i].point_name.split('.')[0];      //加入是一个器件的两个端口，不删除
        for(QMap<QString, int>::iterator it=input_test_point.begin(); it != input_test_point.end(); it++)
        {
            if(module_name == it.key().split('.')[0])    //同一个器件的端口不进行删除
                continue;

            bool is_connect = graph_list->isDirectConnect(test_pt[i].point_name, it.key());
            if(is_connect)
                is_have[i] = false;
        }
    }

    QList<TestPoint> ans;
    for(int i=0; i<is_have.count(); i++)
        if(is_have[i])
            ans.push_back(test_pt[i]);

    test_pt = ans;
    */
}

QStringList MainWindow::GetInterLogicConnect()
{

    QStringList ans;
    return ans;
    QSqlQuery temp_connect = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT Symbol_ID,Equipment_ID, InterConnect from Symbol WHERE InterConnect IS NOT NULL AND InterConnect IS NOT ''";
    temp_connect.exec(SqlStr);
    while(temp_connect.next())
    {
        QString head, tail;

        QString id = temp_connect.value(0).toString();
        QString equip_id = temp_connect.value(1).toString();
        QString inter_connect = temp_connect.value(2).toString();

        QStringList head_port = GetTermNameListBySymbolID(id,"");
        QStringList tail_port = GetTermNameListBySymbolID(inter_connect,"");

        QSqlQuery module_name = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString sql_module_name = "SELECT DT, TModel from Equipment WHERE Equipment_ID = " + equip_id;
        module_name.exec(sql_module_name);

        if(module_name.next())
        {
            QString module = module_name.value(0).toString();
            QString T_model = module_name.value(1).toString();

            QString test_head1 = "ePort_out_" + head_port[0] + '_' + head_port[1];
            QString test_head2 = "ePort_out_" + head_port[1] + '_' + head_port[0];
            if(T_model.contains(test_head1))
                head = module + '.' + test_head1;
            else
                head = module + '.' + test_head2;

            QString test_tail1 = "ePort_in_" + tail_port[0] + '_' + tail_port[1];
            QString test_tail2 = "ePort_in_" + tail_port[1] + '_' + tail_port[0];
            if(T_model.contains(test_tail1))
                tail = module + '.' + test_tail1;
            else
                tail = module + '.' + test_tail2;

            //注意先尾部后头部；
            ans.push_back(tail);
            ans.push_back(head);
        }
    }

    return ans;

}


void MainWindow::SendCmd(QString SendCmdStr,bool print)
{
    ClearListRedEntity();
    ui->tableWidgetDiagResult->setRowCount(0);
    ui->tableWidgetTestPoint->setRowCount(0);
    cmdDiagnose->write(SendCmdStr.toLocal8Bit()+ '\n');
    if(print)
    {
        if(QsciEdit->text()!="") QsciEdit->append("\r\n");
        QsciEdit->append(SendCmdStr);
    }
    //张新宇
    candidate_list.clear();
    GetInputTestPoint(SendCmdStr);
}
void MainWindow::on_BtnSendCmd_clicked()
{
    QString Sendcmd=QsciEdit->text();
    while(Sendcmd.endsWith('\n')) Sendcmd.chop(1);
    SendCmd(Sendcmd.toLocal8Bit(),false);
}

void MainWindow::GetInputTestPoint(QString& cmd)
{
    QStringList data = cmd.split("\n");
    for(int i=0; i<data.count(); i++)
    {
        data[i] = data[i].simplified();
        if(data[i].startsWith("assign"))
            continue;

        data.removeAt(i);
        i--;
    }

    for(int i=0; i<data.count(); i++)
    {
        int start_pos = data[i].indexOf('.');
        int end_pos = data[i].indexOf('=');

        data[i] = data[i].mid(start_pos+1, end_pos-start_pos-1);
        data[i] = data[i].simplified();
    }

    for(int m=0; m<data.count(); m++)
    {
        if(input_test_point.find(data[m]) == input_test_point.end())
            input_test_point[data[m]] = 1;
    }

}

void MainWindow::on_BtnEndDiagnose_clicked()
{ 
    ClearListRedEntity();
    ClearDrawArrow();
    cmdDiagnose->waitForFinished(500);
    cmdDiagnose->close();
    ui->tableWidgetDiagResult->setRowCount(0);
    ui->tableWidgetDiagResult->setRowCount(1);
    ui->tableWidgetDiagResult->setItem(ui->tableWidgetDiagResult->rowCount()-1,0,new QTableWidgetItem("诊断未开始"));
    ui->tableWidgetTestPoint->setRowCount(0);
}

//Category=0:元件 Category=2：导线标号 3：导线 4：connector 5:黑盒Text
formaxwidget* MainWindow::GetOpenedDwgaxwidget(QString Symbol_Handle,int Category)
{
    QString Page_ID;
    if(Category==0)
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_Handle= '"+Symbol_Handle+"'";
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            if(QuerySymbol.value("Symbol_Handle").toString()=="") return nullptr;
            Page_ID=QuerySymbol.value("Page_ID").toString();
        }
    }
    else if(Category==2)
    {
        QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM JXB WHERE ConnectionNumber_Handle= '"+Symbol_Handle+"'";
        QueryJXB.exec(SqlStr);
        if(QueryJXB.next())
        {
            if(QueryJXB.value("ConnectionNumber_Handle").toString()=="") return nullptr;
            Page_ID=QueryJXB.value("Page_ID").toString();
        }
    }
    else if(Category==3)
    {
        QSqlQuery QueryLine=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Line WHERE Wires_Handle= '"+Symbol_Handle+"'";
        QueryLine.exec(SqlStr);
        if(QueryLine.next())
        {
            Page_ID=QueryLine.value("Page_ID").toString();
        }
    }
    else if(Category==4)
    {
        QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Connector WHERE Connector_Handle= '"+Symbol_Handle+"'";
        QueryConnector.exec(SqlStr);
        if(QueryConnector.next())
        {
            Page_ID=QueryConnector.value("Page_ID").toString();
        }
    }
    else if(Category==5)
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE DT_Handle= '"+Symbol_Handle+"'";
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            if(QuerySymbol.value("DT_Handle").toString()=="") return nullptr;
            Page_ID=QuerySymbol.value("Page_ID").toString();
        }
    }

    if(Page_ID!="")
    {
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) return nullptr;
        formaxwidget *formMxdraw;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
                return formMxdraw;
            }
        }
    }
    return nullptr;
}

QString MainWindow::GetEquipment_IDByDT(QString DT)
{
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        return QueryEquipment.value("Equipment_ID").toString();
    }
    return "";
}

//根据OneComponentInfo.CurrentInOutName查找对应的TermID,格式为TermID,Category(0器件 1端子排 2导线),正负极(1正 2负),SymbolID/JXB_ID
QString MainWindow::GetValidTermIDString(QString OneComponentInfo,QString CurrentInOutName)
{
    qDebug()<<"GetValidTermIDString,OneComponentInfo="<<OneComponentInfo<<",CurrentInOutName="<<CurrentInOutName;
    QString DT=OneComponentInfo;
    QString ValidLocalTermID;
    if(DT.contains(".")) DT=DT.mid(0,DT.indexOf("."));
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        bool FlagFindLine=false;
        QString Equipment_ID=QueryEquipment.value("Equipment_ID").toString();
        QString TModel=QueryEquipment.value("TModel").toString();
        //QStringList ListTModel=TModelDiag.split(";");
        QString ValidSymbol_ID;
        QStringList ListTermID;
        QString TmpStr=CurrentInOutName;
        //在TModel中找到CurrentInOutName映射的端口号
        QStringList ListTermName=GetListTermNameByTModel(TModel,CurrentInOutName);//TmpStr.remove("ePort_out_").remove("ePort_in_").split("_");
        qDebug()<<"GetListTermNameByTModel,ListTermName="<<ListTermName;
        //根据ListTermName在Symbol中找到匹配的功能子块的ValidSymbol_ID
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+Equipment_ID+"'";
        QuerySymbol.exec(SqlStr);
        while(QuerySymbol.next())
        {
            //qDebug()<<"Symbol_ID="<<QuerySymbol.value("Symbol_ID").toString();
            ListTermID.clear();
            bool FlagFindSymbol=false;
            QString Symbol_ID=QuerySymbol.value("Symbol_ID").toString();
            int SymbolType=0;//普通：0 源：1 执行器：2
            if(QuerySymbol.value("SourceConn").toBool()) SymbolType=1;
            else if(QuerySymbol.value("ExecConn").toBool()) SymbolType=2;
            QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+Symbol_ID+"'";
            QuerySymb2TermInfo.exec(SqlStr);
            while(QuerySymb2TermInfo.next())
            {
                if(ListTermName.count()>0)
                {
                    if(ListTermName.contains(QuerySymb2TermInfo.value("ConnNum").toString()))
                    {
                        FlagFindSymbol=true;
                        ListTermID.append(QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString());
                        break;
                    }
                }
            }
            if(!FlagFindSymbol) continue;
            //找到正确的ValidSymbol_ID,然后根据ListTermName来确定测试点端口号，同时ValidSymbol_ID必须在ListFinalLinkInfo中存在；如果功能子块是源或者执行器，则根据端口的连线在正极回路确定本地端口；
            ValidSymbol_ID=Symbol_ID;
            if(SymbolType==0)//普通传递功能子块
            {
                for(int i=0;i<ListFinalLinkInfo.count();i++)
                {
                    if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidSymbol_ID)&&(ListFinalLinkInfo.at(i).split(",").at(1)=="0"))
                    {
                        ValidLocalTermID=ListTermID.at(0)+",0,"+ListFinalLinkInfo.at(i).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                        FlagFindLine=true;
                        break;
                    }
                }
            }
            else//源或执行器
            {
                for(int i=0;i<ListFinalLinkInfo.count();i++)
                {
                    if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidSymbol_ID)&&(ListFinalLinkInfo.at(i).split(",").at(1)=="0"))
                    {
                        if(SymbolType==1)//源，检索单链往后传递的第一根正极导线
                        {
                            for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                            {
                                if((ListFinalLinkInfo.at(j).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(j).split(",").at(5)=="1"))
                                {
                                    //在JXB数据库中检索与ListFinalLinkInfo.at(j).split(",").at(0)导线相连的两个Symb2TermInfo_ID，其中一个必然连向ValidSymbol_ID
                                    QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
                                    SqlStr="SELECT * FROM JXB WHERE JXB_ID = "+ListFinalLinkInfo.at(j).split(",").at(0);
                                    QueryJXB.exec(SqlStr);
                                    if(QueryJXB.next())
                                    {
                                        QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
                                        QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
                                        QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
                                        QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
                                        if((Symb1_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb1_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb1_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                        if((Symb2_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb2_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb2_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                        }//end of if(SymbolType==1)//源，检索单链往后传递的第一根正极导线
                        else if(SymbolType==2)//执行器，检索单链往前传递的第一根正极导线
                        {
                            for(int j=i-1;j>=0;j--)
                            {
                                if((ListFinalLinkInfo.at(j).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(j).split(",").at(5)=="1"))
                                {
                                    //在JXB数据库中检索与ListFinalLinkInfo.at(j).split(",").at(0)导线相连的两个Symb2TermInfo_ID，其中一个必然连向ValidSymbol_ID
                                    QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
                                    SqlStr="SELECT * FROM JXB WHERE JXB_ID = "+ListFinalLinkInfo.at(j).split(",").at(0);
                                    QueryJXB.exec(SqlStr);
                                    if(QueryJXB.next())
                                    {
                                        QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
                                        QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
                                        QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
                                        QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
                                        if((Symb1_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb1_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb1_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                        if((Symb2_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb2_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb2_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }//end of for(int j=i-1;j>=0;j--)
                        }
                        else//普通功能子块
                        {
                            ValidLocalTermID=ListTermID.at(0)+",0,"+ListFinalLinkInfo.at(i).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                            FlagFindLine=true;
                            break;
                        }
                    }
                    if(FlagFindLine) break;
                }//end of for(int i=0;i<ListFinalLinkInfo.count();i++)
            }
            /*
            //绘制测试点箭头,根据ListFinalLinkInfo和JXB确定本地端口和相对端口
            //本地端口：查看与ValidSymbol_ID连接的功能子块，然后根据ListFinalLinkInfo的顺序确定端口
            //qDebug()<<"ValidSymbol_ID="<<ValidSymbol_ID<<",ListFinalLinkInfo="<<ListFinalLinkInfo;
            for(int i=0;i<ListTermID.count();i++)
            {
                //qDebug()<<"i="<<i;
                QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
                SqlStr="SELECT * FROM JXB WHERE (Symb1_Category= '0' AND Symb1_ID = '"+ListTermID.at(i)+"') OR (Symb2_Category= '0' AND Symb2_ID = '"+ListTermID.at(i)+"')";
                QueryJXB.exec(SqlStr);
                while(QueryJXB.next())
                {
                    for(int j=0;j<ListFinalLinkInfo.count();j++)
                    {
                        if((ListFinalLinkInfo.at(j).split(",").at(0)==ValidSymbol_ID)&&(ListFinalLinkInfo.at(j).split(",").at(1)=="0"))
                        {
                            //qDebug()<<"find ,j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                            //如果是执行器，则执行器之前的那根导线为负极的线
                            if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")
                            {
                  //qDebug()<<"是执行器";
                                if(CurrentInOutName.contains("ePort_in"))
                                {
                  //qDebug()<<"JXB_ID="<<QueryJXB.value("JXB_ID").toString();
                                    for(int k=j-1;k>=0;k--)
                                    {
                                        if((QueryJXB.value("JXB_ID").toString()==ListFinalLinkInfo.at(k).split(",").at(0))&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)=="1"))
                                        {
                                            ValidLocalTermID=ListTermID.at(i)+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                                else if(CurrentInOutName.contains("ePort_out"))
                                {
                                    for(int k=j-1;k>=0;k--)
                                    {
                                        if((QueryJXB.value("JXB_ID").toString()==ListFinalLinkInfo.at(k).split(",").at(0))&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)=="1"))
                                        {
                                            if(i==0)  ValidLocalTermID=ListTermID.at(1)+",0,2,"+ValidSymbol_ID;
                                            else ValidLocalTermID=ListTermID.at(0)+",0,2,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="0")//是源
                            {
                                if(CurrentInOutName.contains("ePort_out"))
                                {
                                    for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                                    {
                                        if((QueryJXB.value("JXB_ID").toString()==ListFinalLinkInfo.at(k).split(",").at(0))&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)=="1"))
                                        {
                                            ValidLocalTermID=ListTermID.at(0)+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }
                            else//不是执行器
                            {
                  //qDebug()<<"不是执行器";
                                if(CurrentInOutName.contains("ePort_in"))
                                {
                                    for(int k=j-1;k>=0;k--)
                                    {
               //qDebug()<<"k="<<k<<",ListFinalLinkInfo.at(k)="<<ListFinalLinkInfo.at(k);
                                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                                        if((ListFinalLinkInfo.at(k).split(",").at(0)==QueryJXB.value("JXB_ID").toString())&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5)))
                                        {
                                            qDebug()<<"find ,k="<<k;
                                            ValidLocalTermID=ListTermID.at(i)+",0,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                                else if(CurrentInOutName.contains("ePort_out"))
                                {
                                    for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                                    {
                                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                                        if((ListFinalLinkInfo.at(k).split(",").at(0)==QueryJXB.value("JXB_ID").toString())&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5)))
                                        {
                                            qDebug()<<"find ,k="<<k;
                                            ValidLocalTermID=ListTermID.at(i)+",0,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }//end of else if(CurrentInOutName.contains("ePort_out"))
                            }
                        }
                        if(FlagFindLine) break;
                    }//end of for(int j=0;j<ListFinalLinkInfo.count();j++)
                    if(FlagFindLine) break;
                }//end of while(QueryJXB.next())
                if(FlagFindLine) break;
            }//end of for(int i=0;i<ListTermID.count();i++)
            */
            if(FlagFindLine) break;
        }//end of while(QuerySymbol.next())
    }//end of if(QueryEquipment.next())

    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+DT+"'";
    QueryJXB.exec(SqlStr);
    if(QueryJXB.next())
    {
        bool FlagFindLocalTerm=false;
        //找到ListFinalLinkInfo中与当前导线的下一个器件或导线的
        QString JXB_ID=QueryJXB.value("JXB_ID").toString();
        QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
        QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
        QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
        QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
        //qDebug()<<"ValidJXB_ID="<<JXB_ID<<",Symb1_ID="<<Symb1_ID<<",Symb2_ID="<<Symb2_ID<<",ListFinalLinkInfo="<<ListFinalLinkInfo;
        for(int j=0;j<ListFinalLinkInfo.count();j++)
        {
            if((ListFinalLinkInfo.at(j).split(",").at(0)==JXB_ID)&&(ListFinalLinkInfo.at(j).split(",").at(1)=="2"))
            {
                //qDebug()<<"find ,j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                QString NextID,NextCategory;
                if(CurrentInOutName.contains("ePort_out"))
                {
                    for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                    {
                        //qDebug()<<"Cur k="<<k<<",ListFinalLinkInfo.at(k)="<<ListFinalLinkInfo.at(k);
                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                        //如果k是执行器了，那就选执行器
                        bool FlagIsExec=false;
                        if(ListFinalLinkInfo.at(k).split(",").at(5)=="3")
                            FlagIsExec=true;
                        if((ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5))||FlagIsExec)
                        {
                            //qDebug()<<"find ,k="<<k<<",NextID="<<ListFinalLinkInfo.at(k).split(",").at(0);
                            NextID=ListFinalLinkInfo.at(k).split(",").at(0);
                            NextCategory=ListFinalLinkInfo.at(k).split(",").at(1);
                            break;
                            //qDebug()<<"NextCategory="<<NextCategory;

                        }
                    }//end of for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                }//end of if(CurrentInOutName.contains("ePort_out"))
                else if(CurrentInOutName.contains("ePort_in"))
                {
                    for(int k=j-1;k>=0;k--)
                    {
                        //qDebug()<<"Cur k="<<k<<",ListFinalLinkInfo.at(k)="<<ListFinalLinkInfo.at(k);
                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                        //如果k是执行器了，那就选执行器
                        bool FlagIsExec=false;
                        bool FlagIsSource=false;
                        if(ListFinalLinkInfo.at(k).split(",").at(5)=="3")
                            FlagIsExec=true;
                        if(ListFinalLinkInfo.at(k).split(",").at(5)=="0")
                            FlagIsSource=true;
                        if((ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5))||FlagIsExec||FlagIsSource)
                        {
                            //qDebug()<<"find ,k="<<k<<",NextID="<<ListFinalLinkInfo.at(k).split(",").at(0);
                            NextID=ListFinalLinkInfo.at(k).split(",").at(0);
                            NextCategory=ListFinalLinkInfo.at(k).split(",").at(1);
                            //qDebug()<<"NextCategory="<<NextCategory;
                            break;


                        }
                    }//end of for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                }//end of else if(CurrentInOutName.contains("ePort_in"))

                if(NextCategory=="0")//与导线相连的是器件子块
                {
                    QStringList ListTermID;
                    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                    SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+NextID+"'";
                    QuerySymb2TermInfo.exec(SqlStr);
                    while(QuerySymb2TermInfo.next())
                    {
                        ListTermID.append(QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString());
                    }
                    //qDebug()<<"ListTermID="<<ListTermID;
                    if(ListTermID.count()==2)
                    {
                        if(ListTermID.at(0)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                        else if(ListTermID.at(1)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                        else if(ListTermID.at(0)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                        else if(ListTermID.at(1)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                        FlagFindLocalTerm=true;
                        break;
                    }
                    else if(ListTermID.count()==1)
                    {
                        int SymbolID=GetSymbolIDByTermID(0,Symb1_ID);
                        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                        SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(SymbolID);
                        QuerySymbol.exec(SqlStr);
                        if(QuerySymbol.next())
                        {
                            if(QuerySymbol.value("SourceConn").toBool()) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                            else ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                            FlagFindLocalTerm=true;
                            break;
                        }
                    }
                }//end of if(NextCategory=="0")//与导线相连的是器件子块
                else if(NextCategory=="2")//与导线相连的是导线
                {
                    QStringList ListTermID;
                    QSqlQuery QueryJXB2=QSqlQuery(T_ProjectDatabase);
                    SqlStr="SELECT * FROM JXB WHERE JXB_ID= "+NextID;
                    QueryJXB2.exec(SqlStr);
                    if(QueryJXB2.next())
                    {
                        ListTermID.append(QueryJXB2.value("Symb1_ID").toString());
                        ListTermID.append(QueryJXB2.value("Symb2_ID").toString());
                    }
                    //qDebug()<<"ListTermID="<<ListTermID;
                    if(ListTermID.count()==2)
                    {
                        if(ListTermID.at(0)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb1_ID.toInt()));
                        else if(ListTermID.at(1)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb1_ID.toInt()));
                        else if(ListTermID.at(0)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb2_ID.toInt()));
                        else if(ListTermID.at(1)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb2_ID.toInt()));
                        FlagFindLocalTerm=true;
                        break;
                    }
                }
                if(FlagFindLocalTerm) break;
            }
        }//end of for(int j=0;j<ListFinalLinkInfo.count();j++)
    }//end of if(QueryJXB.next())
    qDebug()<<"Get ValidLocalTermID="<<ValidLocalTermID;
    return ValidLocalTermID;
}

QStringList MainWindow::GetTestPointTermID(QString OneComponentInfo,QString CurrentInOutName)
{
    //qDebug()<<"DrawTestPoint,OneComponentInfo="<<OneComponentInfo<<",CurrentInOutName="<<CurrentInOutName;
    //QStringList ListFinalLinkInfo=MakeListFinalLinkInfo();
    QString ValidLocalTermID=GetValidTermIDString(OneComponentInfo,CurrentInOutName);
    QString ValidRelativeTermID;
    //根据ValidLocalTermID查找相对测试点，正极则寻找相对地，负极则寻找相对正
    qDebug()<<"ValidLocalTermID="<<ValidLocalTermID;
    QString RelativePole;
    if(ValidLocalTermID.split(",").at(2)=="1") RelativePole="2";
    else RelativePole="1";
    bool FlagFind=false;
    for(int i=0;i<ListFinalLinkInfo.count();i++)//ListFinalLinkInfo:(SymbolID,Category,LinkID,Checked,Count,+-)
    {
        //找到测试点所在的ListFinalLinkInfo位置
        if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID.split(",").at(3))&&(ListFinalLinkInfo.at(i).split(",").at(1)==ValidLocalTermID.split(",").at(1)))
        {
            //当前选择的测试点是执行器，向前搜索
            if(ListFinalLinkInfo.at(i).split(",").at(5)=="3")
            {
                for(int j=i-1;j>=0;j--)
                {
                    if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                    if((ListFinalLinkInfo.at(j).split(",").at(5)==RelativePole)||(ListFinalLinkInfo.at(j).split(",").at(5)=="0"))
                    {
                        QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                        int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                        QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                        ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[1]);
                        FlagFind=true;
                        break;
                    }
                }
            }
            else //if(ListFinalLinkInfo.at(i).split(",").at(5)=="0")//非执行器，向后搜索
            {
                for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                {
                    if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                    if((ListFinalLinkInfo.at(j).split(",").at(5)==RelativePole)||(ListFinalLinkInfo.at(j).split(",").at(5)=="3"))
                    {
                        QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                        int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                        QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                        ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0]);
                        FlagFind=true;
                        break;
                    }
                }
            }
        }
        if(FlagFind) break;
    }
    qDebug()<<"ValidRelativeTermID="<<ValidRelativeTermID;
    /*
    if(ValidLocalTermID.split(",").at(2)=="1")//寻找相对地
    {
        bool FlagFind=false;
        for(int i=0;i<ListFinalLinkInfo.count();i++)
        {
            if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID.split(",").at(3))&&(ListFinalLinkInfo.at(i).split(",").at(1)==ValidLocalTermID.split(",").at(1)))
            {
                //当前选择的测试点是执行器，向前搜索
                if(ListFinalLinkInfo.at(i).split(",").at(5)=="3")
                {
                    QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),0);
                    int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),ListFinalLinkInfo.at(i).split(",").at(2));
                    QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),QString::number(NumIndex));
                    ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt()),TermNameList[0].replace("ePort_in","ePort_out"));//currentIn
                    FlagFind=true;
                }
                else if(ListFinalLinkInfo.at(i).split(",").at(5)=="0")//当前选择的测试点是源
                {
                    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                    QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ValidLocalTermID.split(",").at(0);
                    QuerySymb2TermInfo.exec(SqlStr);
                    if(QuerySymb2TermInfo.next())
                    {
                        QString ConnNum=QuerySymb2TermInfo.value("ConnNum").toString();
                        QString tmpStr=CurrentInOutName;
                        QString AnotherConnNum=tmpStr.remove("ePort_in").remove("ePort_out").remove(ConnNum).remove("_");
                        QString DT;
                        int Equipment_ID=GetUnitStripIDByTermID(0,ValidLocalTermID.split(",").at(0).toInt(),DT);
                        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                        SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(Equipment_ID)+"'";
                        QuerySymbol.exec(SqlStr);
                        while(QuerySymbol.next())
                        {
                            SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+QuerySymbol.value("Symbol_ID").toString()+"' AND ConnNum = '"+AnotherConnNum+"'";
                            QuerySymb2TermInfo.exec(SqlStr);
                            if(QuerySymb2TermInfo.next())
                            {
                                ValidRelativeTermID=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()+",0,2,"+QuerySymbol.value("Symbol_ID").toString();
                                FlagFind=true;
                            }
                        }
                    }
                }
                else//当前选择的测试点是器件或者导线
                {
                    if(CurrentInOutName.contains("ePort_in"))
                    {
                        for(int j=i-1;j>=0;j--)
                        {
                            //qDebug()<<"j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                            if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                            if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            {
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(1));//ePort_out
                                FlagFind=true;
                                break;
                            }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="0")//源
                            {
                                //源只能通过GetValidTermIDString找到源的正极，需要去找匹配的负极
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(1));//ePort_out
                                //查找与ValidRelativeTermID.split(",").at(0)匹配的n极
                                QString Str_n=TermNameList.at(1);
                                QStringList Listpn=Str_n.remove("ePort_out_").split("_");
                                bool FlagFindRelativeTermID=false;
                                QString Equipment_ID=GetEquipment_IDByDT(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()));
                                QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                                QString SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+Equipment_ID+"'";
                                QuerySymbol.exec(SqlStr);
                                while(QuerySymbol.next())
                                {

                                    QString Symbol_ID=QuerySymbol.value("Symbol_ID").toString();
                                    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                                    SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+Symbol_ID+"'";
                                    QuerySymb2TermInfo.exec(SqlStr);
                                    while(QuerySymb2TermInfo.next())
                                    {
                                        if(Listpn.contains(QuerySymb2TermInfo.value("ConnNum").toString())&&(ValidRelativeTermID.split(",").at(0)!=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()))
                                        {
                                            FlagFindRelativeTermID=true;
                                            ValidRelativeTermID=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()+",0,2,"+Symbol_ID;
                                            break;
                                        }
                                    }
                                    if(FlagFindRelativeTermID) break;
                                }//end of while(QuerySymbol.next())
                            }
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                            {
                                //因为执行器没有ePort_out_X_X,所以采用ePort_in_X_X的_X_X生成ePort_out_X_X
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0].replace("ePort_in","ePort_out"));
                                FlagFind=true;
                                break;
                            }
                        }
                    }//end of if(CurrentInOutName.contains("ePort_in"))
                    else
                    {
                        for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                        {
                            //qDebug()<<"j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                            if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                            if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            {
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(0));//currentIn
                                FlagFind=true;
                                break;
                            }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                            {
                                //因为执行器没有ePort_out_X_X,所以采用ePort_in_X_X的_X_X生成ePort_out_X_X
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0].replace("ePort_in","ePort_out"));
                                FlagFind=true;
                                break;
                            }
                        }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                    }
                }
            }//end of if(ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID)
            if(FlagFind) break;
        }//end of for(int i=0;i<ListFinalLinkInfo.count();i++)
    }//end of if(ValidLocalTermID.split(",").at(2)=="1")//寻找相对地
    else if(ValidLocalTermID.split(",").at(2)=="2")//寻找相对正
    {
        bool FlagFind=false;
        for(int i=0;i<ListFinalLinkInfo.count();i++)
        {
            if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID.split(",").at(3))&&(ListFinalLinkInfo.at(i).split(",").at(1)==ValidLocalTermID.split(",").at(1)))
            {
                if(CurrentInOutName.contains("ePort_in"))
                {
                    for(int j=i-1;j>=0;j--)
                    {
                        if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                        if((ListFinalLinkInfo.at(j).split(",").at(5)=="1")||(ListFinalLinkInfo.at(j).split(",").at(5)=="0"))
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(1));
                            FlagFind=true;
                            break;
                        }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                        else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0]);
                            //ValidRelativeTermID=GetValidTermIDString(ListFinalLinkInfo,GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0).toInt(),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),"ePort_in");
                            FlagFind=true;
                            break;
                        }
                    }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                }//end of if(CurrentInOutName.contains("ePort_in"))
                else
                {
                    for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                    {
                        if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                        if(ListFinalLinkInfo.at(j).split(",").at(5)=="1")
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(0));
                            FlagFind=true;
                            break;
                        }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                        else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0]);
                            //ValidRelativeTermID=GetValidTermIDString(ListFinalLinkInfo,GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0).toInt(),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),"ePort_in");
                            FlagFind=true;
                            break;
                        }
                    }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                }
            }//end of if(ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID)
            if(FlagFind) break;
        }//end of for(int i=0;i<ListFinalLinkInfo.count();i++)
    }//end of if(ValidLocalTermID.split(",").at(2)=="1")//寻找相对地
    */
    return {ValidLocalTermID,ValidRelativeTermID};
}

void MainWindow::DrawTestPoint(QString OneComponentInfo,QString CurrentInOutName)
{
    QStringList ListValidTermID=GetTestPointTermID(OneComponentInfo,CurrentInOutName);
    //将两个TermID的位置发送给dlgDiagnoseUI
    DrawArrow(ListValidTermID);
    LoadTestPointInfo(OneComponentInfo,CurrentInOutName,ListValidTermID);
    LoadUserTestInfo();//自定义测试显示
}

//自定义测试显示
void MainWindow::LoadUserTestInfo()
{
    ListUserTest.clear();
    QSqlQuery QueryUserTest=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM UserTest WHERE FunctionID= '"+CurFunctionID+"'";
    QueryUserTest.exec(SqlStr);
    while(QueryUserTest.next())
    {
        QString Condition=QueryUserTest.value("Condition").toString();
        QStringList ListCondition=Condition.split(",");
        bool FlagBreak=false;
        for(QString StrOneCondition:ListCondition)//满足一个条件就可以
        {
            if(StrOneCondition.contains("="))//故障模式判断
            {
                for(CandidateData m_CandidateData:candidate_list)
                {
                    if((m_CandidateData.FaultSpur==StrOneCondition.split("=").at(0))&&(m_CandidateData.modeTransition==StrOneCondition.split("=").at(1)))
                    {
                        ListUserTest.append(QueryUserTest.value("Name").toString()+":"+QueryUserTest.value("Test").toString());
                        FlagBreak=true;
                        break;
                    }
                }
            }
            else//包含判断
            {
                for(CandidateData m_CandidateData:candidate_list)
                {
                    if(m_CandidateData.FaultSpur==StrOneCondition)
                    {
                        //将QueryUserTest.value("Test").toString()不全部在当前的观测中
                        QString Test=QueryUserTest.value("Test").toString();
                        QStringList ListTest=Test.split(",");
                        QString ValidTest;
                        qDebug()<<"ListTest="<<ListTest<<",ListAllObserve="<<ListAllObserve;
                        for(QString StrCurTest:ListTest)
                        {
                            bool FlagObserveExisted=false;
                            for(int i=0;i<ListAllObserve.count();i++)
                            {
                                if(ListAllObserve.at(i).contains(StrCurTest))
                                {
                                    FlagObserveExisted=true;
                                    break;
                                }
                            }
                            if(!FlagObserveExisted)
                            {
                                if(ValidTest!="") ValidTest+=",";
                                ValidTest+=StrCurTest;
                            }
                        }
                        if(ValidTest!="") ListUserTest.append(QueryUserTest.value("Name").toString()+":"+ValidTest);
                        FlagBreak=true;
                        break;
                    }
                }
            }
            if(FlagBreak) break;
        }//end of for(QString StrOneCondition:ListCondition)//满足一个条件就可以
    }//end of while(QueryUserTest.next())

    //刷新UI界面，按钮闪烁，点击按钮可查看自定义测试
    if(ListUserTest.count()>0)
    {
        ui->BtnUserTest->setEnabled(true);
    }
    else
    {
        ui->BtnUserTest->setEnabled(false);
    }
}

void MainWindow::DrawArrow(QStringList ListTermID)
{
    ClearDrawArrow();
    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    bool FirstIn=true;
    qDebug()<<"DrawArrow,ListTermID="<<ListTermID;
    if(ListTermID.count()==2)
    {
        if(ListTermID.at(0).split(",").at(2).toInt()>ListTermID.at(1).split(",").at(2).toInt())
        {
            ListTermID[0]=ListTermID.at(0).split(",").at(0)+","+ListTermID.at(0).split(",").at(1)+",2";
            ListTermID[1]=ListTermID.at(1).split(",").at(0)+","+ListTermID.at(1).split(",").at(1)+",1";
        }
        else
        {
            ListTermID[0]=ListTermID.at(0).split(",").at(0)+","+ListTermID.at(0).split(",").at(1)+",1";
            ListTermID[1]=ListTermID.at(1).split(",").at(0)+","+ListTermID.at(1).split(",").at(1)+",2";
        }
    }
    QStringList ListConn_Coordinate;
    for(int i=0;i<ListTermID.count();i++)
    {
        QString TermID=ListTermID.at(i).split(",").at(0);
        QString StrPolar=ListTermID.at(i).split(",").at(2);
        SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+TermID;
        QuerySymb2TermInfo.exec(SqlStr);
        if(QuerySymb2TermInfo.next())
        {
            QString ConnDirection=QuerySymb2TermInfo.value("ConnDirection").toString();
            QString Symbol_ID=QuerySymb2TermInfo.value("Symbol_ID").toString();
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+Symbol_ID;
            QuerySymbol.exec(SqlStr);
            if(QuerySymbol.next())
            {
                if(FirstIn)
                {
                    FirstIn=false;
                    QString dwgfilename=GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt());
                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                    QFileInfo file(path);
                    if(!file.exists()) return;
                    if(CurDiagnoseDwgFilePath!=path)
                    {
                        CurDiagnoseDwgFilePath=path;
                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                    }
                    //ui->axWidgetDiagnose->dynamicCall("ZoomAll()");
                    //FlagSetTestPointHighLight=true;
                    //ClearDrawArrow();
                }
                DrawArrow(QuerySymb2TermInfo.value("Conn_Coordinate").toString(),StrPolar,ConnDirection);
                ListConn_Coordinate.append(QuerySymb2TermInfo.value("Conn_Coordinate").toString());
            }//end of if(QuerySymbol.next())
        }//end of if(QuerySymb2TermInfo.next())
    }//end of for(int i=0;i<ListTermID.count();i++)
    //ListConn_Coordinate适应屏幕显示
    if(ListConn_Coordinate.count()==2)
    {
        dCenterX=(ListConn_Coordinate.at(0).split(",").at(0).toDouble()+ListConn_Coordinate.at(1).split(",").at(0).toDouble())/2;
        dCenterY=(ListConn_Coordinate.at(0).split(",").at(1).toDouble()+ListConn_Coordinate.at(1).split(",").at(1).toDouble())/2;
        //connect(&TimerDelay,SIGNAL(timeout()), this, SLOT(timerSetTestPointHighLight()));
        QTimer::singleShot(100, this,SLOT(timerSetTestPointHighLight()));
        //TimerDelay.start(100);
        ui->axWidgetDiagnose->dynamicCall("ZoomCenter(double,double)",dCenterX,dCenterY);
    }
}

void MainWindow::timerSetTestPointHighLight()
{
    //TimerDelay.stop();
    ui->axWidgetDiagnose->dynamicCall("ZoomAll()");
    ui->axWidgetDiagnose->dynamicCall("ZoomScale(double)",0.2);
    ui->axWidgetDiagnose->dynamicCall("ZoomCenter(double,double)",dCenterX,dCenterY);
}

void MainWindow::DoSetTestPointHighLight()
{
}

void MainWindow::DrawArrow(QString Conn_Coordinate,QString Tag,QString ConnDirection)
{
    qDebug()<<"DrawArrow(),Conn_Coordinate="<<Conn_Coordinate<<",Tag="<<Tag;
    QString ArrowName,ArrowColor;
    //if(Tag=="1") ArrowColor="RED";//红
    //else ArrowColor="BLUE";//蓝
    ArrowColor="RED";//红

    if(ConnDirection=="向右") ArrowName="ARROW_"+ArrowColor+"_HOR";
    else if(ConnDirection=="向左") ArrowName="ARROW_"+ArrowColor+"_HOR";
    else if(ConnDirection=="向上") ArrowName="ARROW_"+ArrowColor+"_VER";
    else if(ConnDirection=="向下") ArrowName="ARROW_"+ArrowColor+"_VER";

    MyInsertBlock(ui->axWidgetDiagnose,"C:/TBD/SymbConnLib/"+ArrowName+".dwg",ArrowName);
    SetCurLayer(ui->axWidgetDiagnose,"ARROW");
    double Posx=Conn_Coordinate.split(",").at(0).toDouble();
    double Posy=Conn_Coordinate.split(",").at(1).toDouble();
    qlonglong lBlockID=ui->axWidgetDiagnose->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Posx,Posy,ArrowName,1.0,0).toLongLong();
    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidgetDiagnose->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    if(Tag=="1") FindAttrDefAndAddAttrToBlock(ui->axWidgetDiagnose,blkEnty,"设备标识符(显示)","+");
    else FindAttrDefAndAddAttrToBlock(ui->axWidgetDiagnose,blkEnty,"设备标识符(显示)","-");
    // 准备闪烁颜色.
    MxDrawResbuf* colors = new MxDrawResbuf();
    //if(Tag=="1") colors->AddLong(255);
    //else colors->AddLong(0xFF0000);
    colors->AddLong(255);
    colors->AddLong(0);
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeColor(QVariant)",colors->asVariant());
    // 设置闪烁间隔的时间
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeTime(int)",500);
    // 开始闪烁
    ui->axWidgetDiagnose->dynamicCall("TwinkeEnt(QString)",blkEnty->ObjectID());

    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
}

//清除所有的箭头
void MainWindow::ClearDrawArrow()
{
    qDebug()<<"ClearDrawArrow()";
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)ui->axWidgetDiagnose->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidgetDiagnose->querySubObject("NewResbuf()");
    filter->AddStringEx("ARROW",8);  // 筛选图层
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    for(int i=0;i<Cnt;i++)
    {
        IMxDrawEntity *Enty = (IMxDrawEntity*)ss1->querySubObject("Item(int)",i);
        Enty->dynamicCall("Erase()");
    }
    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
}

void MainWindow::SetDiagResultRed(QString StrFaultComponentInfo)
{
    QStringList ListFaultComponentInfo=StrFaultComponentInfo.split(" ");
    for(QString OneComponentInfo:ListFaultComponentInfo)
    {
        //映射到原理图上标红
        //这里可能是元件或者是子元件
        QString DT=OneComponentInfo.mid(0,OneComponentInfo.indexOf(":"));
        QString modeTransition=OneComponentInfo.mid(OneComponentInfo.indexOf(":")+1,OneComponentInfo.indexOf("(")-OneComponentInfo.indexOf(":")-1);
        if(DT=="") continue;
        if(DT.contains(".")) DT=DT.mid(0,DT.indexOf("."));

        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr;
        SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            QString Equipment_ID=QueryEquipment.value("Equipment_ID").toString();

            //qDebug()<<"Equipment_ID="<<Equipment_ID;
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+Equipment_ID+"'";
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()=="") continue;

                QString dwgfilename=GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt());
                QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                QFileInfo file(path);
                if(!file.exists()) return;
                if(CurDiagnoseDwgFilePath!=path)
                {
                    CurDiagnoseDwgFilePath=path;
                    ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                }
                SetEntityRed(QuerySymbol.value("Symbol_Handle").toString());
                ListRedEntity.append(QuerySymbol.value("Symbol_Handle").toString()+",0");
                if(QuerySymbol.value("DT_Handle").toString()!="")
                {
                    if(SetEntityRed(QuerySymbol.value("DT_Handle").toString()))
                    {
                        ListRedEntity.append(QuerySymbol.value("DT_Handle").toString()+",5");
                    }
                }
                /*
                formaxwidget *formMxdraw=GetOpenedDwgaxwidget(QuerySymbol.value("Symbol_Handle").toString(),0);
                if(formMxdraw==nullptr) continue;
 //qDebug()<<"Symbol_Handle="<<QuerySymbol.value("Symbol_Handle").toString();
                if(formMxdraw->SetEntityRed(QuerySymbol.value("Symbol_Handle").toString()))
                {
                    ListRedEntity.append(QuerySymbol.value("Symbol_Handle").toString()+",0");
                }
                //如果是黑盒，别忘了黑盒对应的标号
                if(QuerySymbol.value("DT_Handle").toString()!="")
                {
                    if(formMxdraw->SetEntityRed(QuerySymbol.value("DT_Handle").toString()))
                    {
                        ListRedEntity.append(QuerySymbol.value("DT_Handle").toString()+",5");
                    }
                }
*/
            }//end of while(QuerySymbol.next())
        }//end of if(QueryEquipment.next())

        QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+OneComponentInfo.mid(0,OneComponentInfo.indexOf(":"))+"'";
        QueryJXB.exec(SqlStr);
        if(QueryJXB.next())
        {
            QString ConnectionNumber_Handle=QueryJXB.value("ConnectionNumber_Handle").toString();

            QString dwgfilename=GetPageNameByPageID(QueryJXB.value("Page_ID").toInt());
            QString path=CurProjectPath+"/"+dwgfilename+".dwg";
            QFileInfo file(path);
            if(!file.exists()) return;
            if(CurDiagnoseDwgFilePath!=path)
            {
                CurDiagnoseDwgFilePath=path;
                ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
            }
            SetEntityRed(ConnectionNumber_Handle);
            ListRedEntity.append(ConnectionNumber_Handle+",2");
            /*
            formaxwidget *formMxdraw=GetOpenedDwgaxwidget(ConnectionNumber_Handle,2);
            if(formMxdraw==nullptr) continue;
            if(formMxdraw->SetEntityRed(ConnectionNumber_Handle))
            {
                ListRedEntity.append(ConnectionNumber_Handle+",2");
            }*/
            //找到所有ConnectionNumber相关导线
            QStringList ListFindedSymb_ID;
            QSqlQuery QueryConnectLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM ConnectLine WHERE ConnectionNumber = '"+OneComponentInfo.mid(0,OneComponentInfo.indexOf(":"))+"'";
            QueryConnectLine.exec(SqlStr);
            while(QueryConnectLine.next())
            {
                QString Symb1_ID=QueryConnectLine.value("Symb1_ID").toString();
                QString Symb2_ID=QueryConnectLine.value("Symb2_ID").toString();
                if((Symb1_ID=="")&&(Symb2_ID=="")) continue;
                if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) continue;
                if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) continue;
                QString ConnectLine_ID=QueryConnectLine.value("ConnectLine_ID").toString();
                QSqlQuery QueryLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                QSqlQuery QueryConnector = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Line WHERE Line_ID = "+ConnectLine_ID;
                QueryLine.exec(SqlStr);
                if(QueryLine.next())
                {
                    QString dwgfilename=GetPageNameByPageID(QueryLine.value("Page_ID").toInt());
                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                    QFileInfo file(path);
                    if(!file.exists()) return;
                    if(CurDiagnoseDwgFilePath!=path)
                    {
                        CurDiagnoseDwgFilePath=path;
                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                    }
                    SetEntityRed(QueryLine.value("Wires_Handle").toString());
                    ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                    /*
                    formMxdraw=GetOpenedDwgaxwidget(QueryLine.value("Wires_Handle").toString(),3);
                    if(formMxdraw!=nullptr)
                    {
                        if(formMxdraw->SetEntityRed(QueryLine.value("Wires_Handle").toString()))
                           ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                    }*/
                    QStringList ListLineSearchID={ConnectLine_ID};
                    while(1)
                    {
                        if(ListLineSearchID.count()<1) break;
                        QueryLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        SqlStr = "SELECT * FROM Line WHERE Line_ID = "+ListLineSearchID.at(0);
                        QueryLine.exec(SqlStr);
                        if(QueryLine.next())
                        {
                            ListLineSearchID.removeFirst();
                            Symb1_ID=QueryLine.value("Symb1_ID").toString();
                            Symb2_ID=QueryLine.value("Symb2_ID").toString();
                            bool GoOn=false;
                            QStringList ListSymb_ID;
                            if(Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3"))
                            {
                                QString Symb_ID=Symb1_ID;
                                if(ListFindedSymb_ID.contains(Symb_ID)) continue;
                                ListFindedSymb_ID.append(Symb_ID);
                                Symb_ID=Symb_ID.mid(0,Symb_ID.count()-1)+"C";
                                ListSymb_ID.append(Symb_ID);
                                GoOn=true;
                            }
                            if(Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3"))
                            {
                                QString Symb_ID=Symb2_ID;
                                if(ListFindedSymb_ID.contains(Symb_ID)) continue;
                                ListFindedSymb_ID.append(Symb_ID);
                                Symb_ID=Symb_ID.mid(0,Symb_ID.count()-1)+"C";
                                ListSymb_ID.append(Symb_ID);
                                GoOn=true;
                            }
                            if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))
                            {
                                for(int i=0;i<2;i++)
                                {
                                    QString Symb_ID;
                                    if(i==0)
                                    {
                                        if(Symb1_ID.contains(":C")) Symb_ID = Symb1_ID;
                                        else continue;
                                    }
                                    else
                                    {
                                        if(Symb2_ID.contains(":C")) Symb_ID = Symb2_ID;
                                        else continue;
                                    }
                                    SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID.mid(0,Symb_ID.count()-2);
                                    QueryConnector.exec(SqlStr);
                                    if(QueryConnector.next())
                                    {
                                        if(QueryConnector.value("Connector_Name").toString().contains("SYMB2_M_PWF_CO"))
                                        {
                                            if(ListFindedSymb_ID.contains(Symb_ID)) continue;
                                            ListFindedSymb_ID.append(Symb_ID);
                                            Symb_ID=Symb_ID.mid(0,Symb_ID.count()-1)+"1";
                                            ListSymb_ID.append(Symb_ID);
                                            GoOn=true;
                                        }
                                    }
                                }//end of for(int i=0;i<2;i++)
                            }//end of if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))
                            if(!GoOn) continue;
                            for(QString Symb_ID:ListSymb_ID)
                            {
                                SqlStr = "SELECT * FROM Line WHERE (Symb1_ID = '"+Symb_ID+"') OR (Symb2_ID = '"+Symb_ID+"')";
                                QueryLine.exec(SqlStr);
                                if(QueryLine.next())
                                {
                                    QString dwgfilename=GetPageNameByPageID(QueryLine.value("Page_ID").toInt());
                                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                                    QFileInfo file(path);
                                    if(!file.exists()) return;
                                    if(CurDiagnoseDwgFilePath!=path)
                                    {
                                        CurDiagnoseDwgFilePath=path;
                                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                                    }
                                    SetEntityRed(QueryLine.value("Wires_Handle").toString());
                                    ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                                    /*
                                    formMxdraw=GetOpenedDwgaxwidget(QueryLine.value("Wires_Handle").toString(),3);
                                    if(formMxdraw!=nullptr)
                                    {
                                        if(formMxdraw->SetEntityRed(QueryLine.value("Wires_Handle").toString()))
                                            ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                                    }
                                    else qDebug()<<"formMxdraw=nullptr 2";*/
                                    ListLineSearchID.append(QueryLine.value("Line_ID").toString());
                                }

                                SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID.mid(0,Symb_ID.count()-2);
                                QueryConnector.exec(SqlStr);
                                if(QueryConnector.next())
                                {
                                    QString dwgfilename=GetPageNameByPageID(QueryConnector.value("Page_ID").toInt());
                                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                                    QFileInfo file(path);
                                    if(!file.exists()) return;
                                    if(CurDiagnoseDwgFilePath!=path)
                                    {
                                        CurDiagnoseDwgFilePath=path;
                                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                                    }
                                    SetEntityRed(QueryConnector.value("Connector_Handle").toString());
                                    ListRedEntity.append(QueryConnector.value("Connector_Handle").toString()+",4");
                                    /*
                                    formMxdraw=GetOpenedDwgaxwidget(QueryConnector.value("Connector_Handle").toString(),4);
                                    if(formMxdraw!=nullptr)
                                    {
                                        if(formMxdraw->SetEntityRed(QueryConnector.value("Connector_Handle").toString()))
                                          ListRedEntity.append(QueryConnector.value("Connector_Handle").toString()+",4");
                                    }*/
                                }
                            } //end of for(QString Symb_ID:ListSymb_ID)
                        }
                    }//end of while(1)
                    break;
                }
            }//end of while(QueryConnectLine.next())
        }//end of if(QueryJXB.next())
    }//end of for(QString OneComponentInfo:ListFaultComponentInfo)
}
void MainWindow::on_tableWidgetDiagResult_clicked(const QModelIndex &index)
{
    //清空ListRedEntity
    ClearListRedEntity();
    if(!index.isValid()) return;

    for(int selectedindex=0;selectedindex<ui->tableWidgetDiagResult->selectionModel()->selectedIndexes().count();selectedindex++)
    {
        int rowindex=ui->tableWidgetDiagResult->selectionModel()->selectedIndexes().at(selectedindex).row();
        QString StrFaultComponentInfo=ui->tableWidgetDiagResult->item(rowindex,0)->text();
        SetDiagResultRed(StrFaultComponentInfo);
    }//end of for(int selectedindex=0;selectedindex<ui->tableWidgetDiagResult->selectionModel()->selectedIndexes().count();selectedindex++)

}

void MainWindow::on_BtnSaveDwg_clicked()
{
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
        formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",formMxdraw->dwgFileName);
    }
}

void MainWindow::on_tableWidgetTestPoint_clicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    ClearListRedEntity();
    QString testpointName=ui->tableWidgetTestPoint->item(index.row(),0)->text();
    DrawTestPoint(testpointName.mid(0,testpointName.indexOf(".")),testpointName.mid(testpointName.indexOf(".")+1,testpointName.count()-testpointName.indexOf(".")-1));//绘制正负测试点箭头
}

void MainWindow::on_BtnModifyFunction_clicked()
{
    if(pDlgSelectFunctionDialog->isHidden())
    {
        // 将functionTree控件从 MainWindow 中移除
        QLayout *mainWindowLayout = ui->widget_func->layout();
        if (mainWindowLayout != nullptr) {
            qDebug()<<"准备将functionTree控件从 MainWindow 中移除";
            mainWindowLayout->removeWidget(pDlgSelectFunctionDialog->GetTreeWidget());
            pDlgSelectFunctionDialog->GetTreeWidget()->setParent(nullptr);
        }

        //在对话框中显示functionTree控件
        pDlgSelectFunctionDialog->ShowSet();
        pDlgSelectFunctionDialog->move(this->width()/2 - pDlgSelectFunctionDialog->width()/2,
                                       this->height()/2 - pDlgSelectFunctionDialog->height()/2);
        pDlgSelectFunctionDialog->show();
        if(pDlgSelectFunctionDialog->exec() == QDialog::Accepted) {
            // Do something on accept
        }
        // 将 functionTree 再次添加回 MainWindow
        UpdateFuncTree();
    }
}
void MainWindow::UpdateFuncTable()
{

    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function";
    QueryFunction.exec(SqlStr);
    ui->tableWidgetFunction->setRowCount(0);
    while(QueryFunction.next())
    {
        ui->tableWidgetFunction->setRowCount(ui->tableWidgetFunction->rowCount()+1);
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,0,new QTableWidgetItem(QueryFunction.value("FunctionName").toString()));
        ui->tableWidgetFunction->item(ui->tableWidgetFunction->rowCount()-1,0)->setData(Qt::UserRole,QueryFunction.value("FunctionID").toString());
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,1,new QTableWidgetItem(QueryFunction.value("CmdValList").toString()));
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,2,new QTableWidgetItem(QueryFunction.value("ExecsList").toString()));
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,3,new QTableWidgetItem(QueryFunction.value("Remark").toString()));
    }
}

void MainWindow::on_BtnDiagnose_clicked()
{
    // 创建并显示诊断对话框
    dialogDiagnoseUI *diagnoseDialog = new dialogDiagnoseUI(this);
    
    // 连接信号与槽
    connect(diagnoseDialog, &dialogDiagnoseUI::signalUpdateExec, 
            this, &MainWindow::onDiagnoseUpdateExec);
    connect(diagnoseDialog, &dialogDiagnoseUI::signalStartDiagnose, 
            this, &MainWindow::StartDiagnose);
    connect(diagnoseDialog, &dialogDiagnoseUI::signalSendCmdStr, 
            this, &MainWindow::onDiagnoseSendCmd);
    
    // 显示对话框（非模态）
    diagnoseDialog->show();
}

void MainWindow::onDiagnoseUpdateExec(QString FunctionID)
{
    // 调用原有的 UpdateXmplInfo 函数
    UpdateXmplInfo(FunctionID);
}

void MainWindow::onDiagnoseSendCmd(QString SendCmdStr)
{
    // 调用原有的 SendCmd 函数
    SendCmd(SendCmdStr, true);
}

void MainWindow::initDiagnoseUI()
{
    ui->tableWidget_function_select->setStyleSheet("selection-background-color: rgb(85, 170, 255)");
    ui->tableWidget_function_select->setColumnWidth(0,140);//功能名称
    ui->tableWidget_function_select->setColumnWidth(1,400);//控制变量
    ui->tableWidget_function_select->setColumnWidth(2,400);//执行器名称
    ui->tableWidget_function_select->setColumnWidth(3,150);//备注
    ui->tableWidget_function_select->setFocusPolicy(Qt::NoFocus);

    ui->tableWidget_tool_select->setColumnWidth(0,400);//工具名称
    ui->tableWidget_tool_select->setFocusPolicy(Qt::NoFocus);
    LoadAllFunction();
    LoadAllTools();
    
    // 隐藏工具选择相关UI元素
    ui->label_tool_select_2->setVisible(false);
    ui->tableWidget_tool_select->setVisible(false);
}

void MainWindow::LoadAllFunction()
{
    // 使用新的diagnosis_tree表加载功能列表
    // 优先尝试从function_definition表联合查询，如果没有则直接使用diagnosis_tree
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);
    
    // 先检查function_definition表是否有数据与diagnosis_tree关联
    QString SqlStr = R"(
        SELECT 
            dt.tree_id,
            dt.function_id,
            COALESCE(fd.name, f.FunctionName, '未命名功能' || dt.tree_id) AS function_name,
            COALESCE(fd.description, f.Remark, '') AS description,
            f.CmdValList,
            f.ExecsList
        FROM diagnosis_tree dt
        LEFT JOIN function_definition fd ON dt.function_id = fd.function_id
        LEFT JOIN Function f ON dt.function_id = f.FunctionID
        ORDER BY dt.tree_id
    )";
    
    if (!QueryFunction.exec(SqlStr)) {
        qWarning() << "加载功能列表失败:" << QueryFunction.lastError().text();
        return;
    }

    ui->tableWidget_function_select->setRowCount(0);
    while(QueryFunction.next())
    {
        int row = ui->tableWidget_function_select->rowCount();
        ui->tableWidget_function_select->setRowCount(row + 1);
        
        // 列0: 功能名称，存储tree_id作为UserRole数据
        QString functionName = QueryFunction.value("function_name").toString();
        QTableWidgetItem *nameItem = new QTableWidgetItem(functionName);
        nameItem->setData(Qt::UserRole, QueryFunction.value("tree_id").toInt()); // 存储tree_id用于诊断
        ui->tableWidget_function_select->setItem(row, 0, nameItem);
        
        // 列1: CmdValList（兼容旧数据）
        ui->tableWidget_function_select->setItem(row, 1, 
            new QTableWidgetItem(QueryFunction.value("CmdValList").toString()));
        
        // 列2: ExecsList（兼容旧数据，格式化显示）
        QString execsList = QueryFunction.value("ExecsList").toString();
        ui->tableWidget_function_select->setItem(row, 2, 
            new QTableWidgetItem(execsList.remove(" ").replace(","," , ")));
        
        // 列3: 描述/备注
        ui->tableWidget_function_select->setItem(row, 3, 
            new QTableWidgetItem(QueryFunction.value("description").toString()));
    }
    
    qDebug() << "已加载" << ui->tableWidget_function_select->rowCount() << "个诊断功能";
}

void MainWindow::LoadAllTools()
{
    ui->tableWidget_tool_select->setRowCount(0);
    ui->tableWidget_tool_select->setRowCount(ui->tableWidget_tool_select->rowCount()+1);
    ui->tableWidget_tool_select->setItem(ui->tableWidget_tool_select->rowCount()-1,0,new QTableWidgetItem("万用表"));
}

void MainWindow::SetStackIndex(int index)
{
    ui->stackedWidget_main->setCurrentIndex(index);
}

void MainWindow::init_symptom_list()//初始化征兆信号UI列表
{
    ui->tableWidget_known_symptom_select->setStyleSheet("selection-background-color: rgb(85, 170, 255)");
    ui->tableWidget_known_symptom_select->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_known_symptom_select->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_known_symptom_select->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);

    ui->tableWidget_known_symptom_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("观测对象名称") << tr("观测对象变量") << tr("观测值");
    ui->tableWidget_known_symptom_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_known_symptom_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);

    ui->tableWidget_known_symptom_select->setAlternatingRowColors(true);//使表格颜色交错功能为真

    //设置表头
    ui->tableWidget_known_symptom_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_known_symptom_select->setFocusPolicy(Qt::NoFocus);

    ui->tableWidget_known_symptom_select->setRowCount(0);
}

void MainWindow::AddOrModifyExec(int Mode,QString StrSelectedExec,QString StrExecState,QString StrExecStateVal)//Mode=1:add Mode=2:modify
{
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增观测变量");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改观测变量");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");

    QCheckBox *CbOnlyExec=new QCheckBox(nullptr);
    CbOnlyExec->setText("只选择执行器");
    CbOnlyExec->setChecked(true);


    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("观测对象");
    m_label1->setMaximumWidth(50);
    qxcombobox *m_QComboBox1 = new qxcombobox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);
    m_QComboBox1->StrSystemDefine=StrSystemDefine;
    m_QComboBox1->CurFunctionID=CurFunctionID;
    connect(CbOnlyExec,SIGNAL(clicked(bool)),m_QComboBox1,SLOT(UpdateItems(bool)));

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    m_label2->setText("观测变量");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    QHBoxLayout *linelayout3= new QHBoxLayout(nullptr);
    QLabel *m_label3 = new QLabel(dialogNewExec);
    m_label3->setText("观测值");
    m_label3->setMaximumWidth(50);
    qxcombobox *m_QComboBox3 = new qxcombobox(dialogNewExec);
    linelayout3->addWidget(m_label3);
    linelayout3->addWidget(m_QComboBox3);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addWidget(CbOnlyExec);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);
    layout3->addLayout(linelayout3);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateExecStateItems(QString)));
    QObject::connect(m_QComboBox2,SIGNAL(currentTextChanged(QString)),m_QComboBox3,SLOT(UpdateExecStateValueItems(QString)));
    for(int i=0;i<ui->tableWidget_known_symptom_select->rowCount();i++)
        m_QComboBox1->ExistedUnits.append(ui->tableWidget_known_symptom_select->item(i,0)->text());
    m_QComboBox1->Mode=Mode;




    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+CurFunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
        QString tmpStr=StrSystemDefine;
        QStringList FunctionUnitList=tmpStr.remove("\r\n").split(";");
        for(int i=0;i<FunctionUnitList.count();i++)
        {
            FunctionUnitList[i]=FunctionUnitList.at(i).split(" ").last();
            if(FunctionUnitList[i]=="") FunctionUnitList.removeAt(i);
        }
        qDebug()<<"FunctionUnitList="<<FunctionUnitList;
        if(Mode==2)
        {
            bool SelectExecExist=false;
            for(int i=0;i<QueryFunction.value("ExecsList").toString().split(",").count();i++)
            {
                if(QueryFunction.value("ExecsList").toString().split(",").at(i).contains(StrSelectedExec))
                {
                    SelectExecExist=true;
                    break;
                }
            }
            if(!SelectExecExist) CbOnlyExec->setChecked(false);
        }

        QStringList ExecsList;
        if(CbOnlyExec->isChecked()) FunctionUnitList=QueryFunction.value("ExecsList").toString().split(",");

        //去除没有可观测变量的器件
        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        for(QString StrFunctionUnit:FunctionUnitList)
        {
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+StrFunctionUnit+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
                bool NoObservable=true;
                for(QString StrStructure:ListStructure)
                {
                    if(StrStructure.split(",").at(2)=="Observable") NoObservable=false;
                }
                if(NoObservable) FunctionUnitList.removeAt(FunctionUnitList.indexOf(StrFunctionUnit));
            }
        }
        m_QComboBox1->clear();
        for(QString StrExec:FunctionUnitList)
        {
            bool skip=false;
            if(Mode==1)
            {
                for(int i=0;i<ui->tableWidget_known_symptom_select->rowCount();i++)
                {
                    if(StrExec.mid(0,StrExec.indexOf("."))==ui->tableWidget_known_symptom_select->item(i,0)->text())
                    {
                        skip=true;
                        break;
                    }
                }
            }
            if(!skip) m_QComboBox1->addItem(StrExec.mid(0,StrExec.indexOf(".")));
        }
    }
    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedExec);
        m_QComboBox2->setCurrentText(StrExecState);
        m_QComboBox3->setCurrentText(StrExecStateVal);
    }
    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        if(Mode==1)
        {
            ui->tableWidget_known_symptom_select->setRowCount(ui->tableWidget_known_symptom_select->rowCount()+1);
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,0,new QTableWidgetItem(m_QComboBox1->currentText()));
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,1,new QTableWidgetItem(m_QComboBox2->currentText()));
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,2,new QTableWidgetItem(m_QComboBox3->currentText()));
        }
        else if(Mode==2)
        {
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),0)->setText(m_QComboBox1->currentText());
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),1)->setText(m_QComboBox2->currentText());
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),2)->setText(m_QComboBox3->currentText());
        }
    }
    else return;
}

QString MainWindow::GetTermJpgPath(QString Type,QString ConnNum)
{
    //获取所选文件类型过滤器
    QStringList filters;

    //文件过滤
    filters<<QString("*.jpg");

    //定义迭代器并设置过滤器
    QDirIterator dir_iterator("C:/TBD/data/TermImage/",
                              filters,
                              QDir::Files | QDir::NoSymLinks);
    while(dir_iterator.hasNext())
    {
        dir_iterator.next();
        QFileInfo file_info = dir_iterator.fileInfo();

        if(file_info.fileName().contains("_"+ConnNum)&&file_info.fileName().contains(Type))
            return file_info.filePath();
    }
    return "";
}

//TestPointName:DT
void MainWindow::LoadTestPointInfo(QString TestPointName,QString CurrentInOutName,QStringList ListTermStr)
{
    qDebug()<<"LoadTestPointInfo,TestPointName="<<TestPointName<<",CurrentInOutName="<<CurrentInOutName<<",ListTermStr="<<ListTermStr;
    CurTestPointName=TestPointName+"."+CurrentInOutName;
    QString DT=TestPointName;
    if(DT.contains(".")) DT=DT.mid(0,DT.indexOf("."));
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        QString Name=QueryEquipment.value("Name").toString()+DT;
        CurTestUnit.Name=QueryEquipment.value("Name").toString();
        CurTestUnit.DT=DT;
        CurTestUnit.Equipment_ID=QueryEquipment.value("Equipment_ID").toInt();
        CurTestUnit.CurrentInOutName=CurrentInOutName;
        CurTestUnit.TModel=QueryEquipment.value("TModel").toString();
        ui->label_diagnosis_TestWord->setText("测试："+Name);
        ui->label_test_procedure->setText("检测电压");
    }
    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+DT+"'";
    QueryJXB.exec(SqlStr);
    if(QueryJXB.next())
    {
        CurTestUnit.Name="导线";
        CurTestUnit.DT=DT;
        CurTestUnit.Equipment_ID=QueryJXB.value("JXB_ID").toInt();
        CurTestUnit.CurrentInOutName=CurrentInOutName;

        QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
        QString StrSql="SELECT * FROM FunctionDefineClass WHERE Level =1 AND FunctionDefineName = '导线新'";
        QueryFunctionDefineClass.exec(StrSql);
        if(QueryFunctionDefineClass.next())
            CurTestUnit.TModel=QueryFunctionDefineClass.value("TModel").toString();

        QString Name="导线"+DT;
        ui->label_diagnosis_TestWord->setText("测试："+Name);
        ui->label_test_procedure->setText("检测电压");
    }

    ui->tabWidget_testpointPic->clear();
    AddTestPicture("工具图","万用表.png","C:/TBD/data/ToolImage/万用表.png");

    QString test_description;
    for(int i=0;i<ListTermStr.count();i++)
    {
        if(i>0) test_description+="\r\n";
        //if(ListTermStr.at(i).split(",").at(1)=="0")//器件
        {
            QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+ListTermStr.at(i).split(",").at(0);
            QuerySymb2TermInfo.exec(SqlStr);
            if(QuerySymb2TermInfo.next())
            {
                QString pointDT,pointName;
                int UnitStripID=GetUnitStripIDByTermID(0,ListTermStr.at(i).split(",").at(0).toInt(),pointDT);
                SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(UnitStripID);
                QueryEquipment.exec(SqlStr);
                if(QueryEquipment.next())
                {
                    pointName=QueryEquipment.value("Name").toString();
                    QString PolarStr=(i==0)?"正极":"负极";
                    test_description+="万用表"+PolarStr+":"+pointName+pointDT+"."+QuerySymb2TermInfo.value("ConnNum").toString();
                    //查找测试点jpg图片
                    QString Tabname=QueryEquipment.value("DT").toString()+"."+QuerySymb2TermInfo.value("ConnNum").toString();
                    QString jpgPath=GetTermJpgPath(QueryEquipment.value("Type").toString(),QuerySymb2TermInfo.value("ConnNum").toString());
                    if(jpgPath!="") AddTestPicture(Tabname,jpgPath.mid(jpgPath.lastIndexOf("/")+1,jpgPath.count()-jpgPath.lastIndexOf("/")-1),jpgPath);
                }
            }
        }
    }
    ui->label_test_description_1->setText(test_description);
    ui->EdInputVal1->setText("");
    SetStackIndex(2);
    qDebug()<<"LoadTestPointInfo over";
}

void MainWindow::OpenPic(int ID)
{
    Q_UNUSED(ID);
    QXlabel *m_Label=(QXlabel*)sender();
    QPixmap photo(m_Label->PicPath);
    picture_Label->setPixmap(photo);
    picture_Label->setScaledContents(true);
    dlg_showPicture->setWindowTitle(m_Label->PicName);
    //dlg_showPicture->setWindowFlags( Qt::MSWindowsFixedSizeDialogHint);

    dlg_showPicture->show();
    QScreen *screen = QGuiApplication::primaryScreen ();
    QRect screenRect =  screen->availableVirtualGeometry();
    int screenWidth = screenRect.width();
    int screenHeight = screenRect.height();
    dlg_showPicture->move(screenWidth/2- dlg_showPicture->width()/2,screenHeight/2- dlg_showPicture->height()/2);
}

void MainWindow::AddTestPicture(QString Tabname,QString PicName,QString Path)
{
    QWidget* widget = new QWidget(nullptr);
    QVBoxLayout * layout = new QVBoxLayout(widget);//铺满布局

    ui->tabWidget_testpointPic->addTab(widget,Tabname);

    QWidget* widgetPic = new QWidget(widget);
    QXlabel* pLabel = new QXlabel(widgetPic);
    pLabel->PicPath=Path;
    pLabel->PicName=PicName;
    connect(pLabel,SIGNAL(doubleClicked(int)),this,SLOT(OpenPic(int)));
    widgetPic->setSizePolicy(QSizePolicy::Preferred,QSizePolicy::Preferred);//铺满布局
    //pLabel->setScaledContents(true);
    //pLabel->setFrameShape(QFrame::Panel);
    //pLabel->setFrameShadow(QFrame::Sunken);
    //pLabel->setLineWidth(3);
    //pLabel->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);

    layout->addWidget(widgetPic);

    QLabel* name_Label = new QLabel(widget);
    name_Label->setMaximumHeight(20);

    name_Label->setStyleSheet("font: 75 10pt '微软雅黑';");
    name_Label->setAlignment(Qt::AlignHCenter);

    QString picture_name = PicName;
    //picture_name.remove(".jpg").remove(".JPG").remove(".png").remove(".PNG");
    name_Label->setText(picture_name);
    layout->addWidget(name_Label);

    QPixmap photo(Path);
    //pLabel->resize(photo.width()-40,photo.height());

    pLabel->setScaledContents(true);
    int wLabel=376-12;
    int hLabel=321-20-18-75;
    //pLabel->setScaledContents(false);
    int wPhoto=photo.width();
    int hPhoto=photo.height();
    int Finalw,Finalh;
    if((wPhoto>=wLabel)&&(hPhoto>=hLabel))
    {
        if((wPhoto/hPhoto)>(wLabel/hLabel))
        {
            Finalw=wLabel;
            Finalh=wLabel*hPhoto/wPhoto;
        }
        else
        {
            Finalh=hLabel;
            Finalw=hLabel*wPhoto/hPhoto;
        }
    }
    else if((wPhoto>=wLabel)&&(hPhoto<=hLabel))
    {
        Finalw=wLabel;
        Finalh=wLabel*hPhoto/wPhoto;
    }
    else if((wPhoto<=wLabel)&&(hPhoto>=hLabel))
    {
        Finalh=hLabel;
        Finalw=hLabel*wPhoto/hPhoto;
    }
    else
    {
        Finalw=wPhoto;
        Finalh=hPhoto;
    }
    //qDebug()<<"wLabel="<<wLabel<<",hLabel="<<hLabel<<",wPhoto="<<wPhoto<<",hPhoto="<<hPhoto<<",Finalw="<<Finalw<<",Finalh="<<Finalh;
    //pLabel->resize(Finalw,Finalh);
    pLabel->move(0,0);
    //qDebug()<<"pLabel->width()="<<pLabel->width()<<",pLabel->height()="<<pLabel->height();
    pLabel->setPixmap(photo.scaled(Finalw,Finalh));//(photo.scaled(w,h,Qt::KeepAspectRatio,Qt::SmoothTransformation));
    //qDebug()<<"pLabel->width()="<<pLabel->width()<<",pLabel->height()="<<pLabel->height();
}

void MainWindow::on_toolButton_start_diagnosis_clicked()
{
    if(ui->tableWidget_function_select->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", "请选择系统功能！");
        return;
    }
    
    // 获取选中的tree_id（新架构使用tree_id而非FunctionID）
    int selectedTreeId = ui->tableWidget_function_select->item(
        ui->tableWidget_function_select->currentRow(), 0)->data(Qt::UserRole).toInt();
    
    QString functionName = ui->tableWidget_function_select->item(
        ui->tableWidget_function_select->currentRow(), 0)->text();
    
    if (!diagnosisEngine) {
        QMessageBox::critical(nullptr, "错误", "诊断引擎未初始化！");
        qCritical() << "DiagnosisEngine is null in on_toolButton_start_diagnosis_clicked";
        return;
    }
    
    // 使用DiagnosisEngine启动诊断会话
    if (!diagnosisEngine->startDiagnosisSession(selectedTreeId)) {
        QMessageBox::warning(nullptr, "错误", 
            QString("无法启动诊断会话！\n功能: %1\n树ID: %2")
            .arg(functionName).arg(selectedTreeId));
        qWarning() << "启动诊断会话失败: tree_id=" << selectedTreeId;
        return;
    }
    
    qDebug() << "诊断会话已启动: tree_id=" << selectedTreeId << ", 功能名称=" << functionName;
    
    // 保存当前功能信息（兼容性）
    CurFunctionID = QString::number(selectedTreeId); // 存储tree_id作为字符串
    ui->LbFunction->setText("当前诊断功能: " + functionName);
    
    // 跳过征兆选择，直接进入测试执行页面
    // 检查是否有推荐的测试
    DiagnosisTreeNode* firstTest = diagnosisEngine->getCurrentRecommendedTest();
    if (firstTest) {
        // 切换到测试执行页面（index=2，根据原有代码推断）
        SetStackIndex(2);
        // 显示第一个推荐的测试
        displayCurrentTest();
    } else {
        QMessageBox::warning(nullptr, "提示", "该功能没有可用的诊断测试！");
        qWarning() << "诊断树为空或无有效测试节点";
    }
}

//解析当前测试模块的阈值信息
void MainWindow::on_btm_CalTestResult_clicked()
{
    if(!StrIsDouble(ui->EdInputVal1->text()))
    {
        QMessageBox::warning(nullptr, "提示", " 请输入正确的电压数值！");
        return;
    }
    QString SendCmdStr="assign test.";
    if(ui->CbTestType->currentText()=="电压")
    {
        QString StrVal=GetRangeValByTModel(CurTestUnit.TModel,CurTestUnit.CurrentInOutName,ui->EdInputVal1->text(),"电压");
        if(StrVal!="")
        {
            SendCmdStr+=CurTestPointName+".U="+StrVal;
            SendCmdStr+="\r\nfc";
            SendCmd(SendCmdStr,true);
        }
        //if(ui->EdInputVal1->text().toDouble()<3) SendCmdStr+=CurTestPointName+".U=none";
        //else if(ui->EdInputVal1->text().toDouble()<16) SendCmdStr+=CurTestPointName+".U=low";
        //else if(ui->EdInputVal1->text().toDouble()<26) SendCmdStr+=CurTestPointName+".U=middle";
        //else if(ui->EdInputVal1->text().toDouble()<30) SendCmdStr+=CurTestPointName+".U=high";
        //else SendCmdStr+=CurTestPointName+".U=infinite";
        //SendCmdStr+="\r\nfc";
        //SendCmd(SendCmdStr,true);
    }
    else if(ui->CbTestType->currentText()=="电流")
    {
        QString StrVal=GetRangeValByTModel(CurTestUnit.TModel,CurTestUnit.CurrentInOutName,ui->EdInputVal1->text(),"电流");
        if(StrVal!="")
        {
            SendCmdStr+=CurTestPointName+".I="+StrVal;
            SendCmdStr+="\r\nfc";
            SendCmd(SendCmdStr,true);
        }
    }
    else if(ui->CbTestType->currentText()=="电阻")
    {
        QString StrVal=GetRangeValByTModel(CurTestUnit.TModel,CurTestUnit.CurrentInOutName,ui->EdInputVal1->text(),"电阻");
        if(StrVal!="")
        {
            SendCmdStr+=CurTestPointName+".R="+StrVal;
            SendCmdStr+="\r\nfc";
            SendCmd(SendCmdStr,true);
        }
    }
}

void MainWindow::on_toolButton_known_symptom_select_next_clicked()
{
    if(ui->tableWidget_known_symptom_select->rowCount()<1)
    {
        QMessageBox::warning(nullptr, "提示", " 请选择观测现象！");
        return;
    }
    ListSkipTestPoint.clear();
    QString CmdValList;
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+CurFunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
        CmdValList=QueryFunction.value("CmdValList").toString();
    }
    QString SendCmdStr;
    for(QString StrCmdVal:CmdValList.split(","))
    {
        if(SendCmdStr!="") SendCmdStr+="\r\n";
        SendCmdStr+="progress test."+StrCmdVal;
    }
    ListAllObserve.clear();
    for(int i=0;i<ui->tableWidget_known_symptom_select->rowCount();i++)
    {
        QString CurObserve=ui->tableWidget_known_symptom_select->item(i,0)->text()+"."+ui->tableWidget_known_symptom_select->item(i,1)->text()+"="+ui->tableWidget_known_symptom_select->item(i,2)->text();
        ListAllObserve.append(CurObserve);
        if(SendCmdStr!="") SendCmdStr+="\r\n";
        SendCmdStr+="assign test."+CurObserve;
    }
    DiagnoseInitStr=SendCmdStr;
    if(ui->tableWidget_known_symptom_select->rowCount()>0) SendCmdStr+="\r\nfc";
    qDebug()<<"SendCmdStr="<<SendCmdStr;
    StartDiagnose(SendCmdStr);


    //SetStackIndex(2);
}

//张新宇写
double MainWindow::CalculateInformation(QString& module_name)
{
    double all_prob = 0.0;
    double all_work_well_prob = 1.0;
    double module_name_prob = 1.0;
    bool is_have = false;


    if(module_fault_prob.isEmpty())
    {
        qDebug()<<"module_fault_prob为空，输出错误";
        return INT_MAX;
    }

    //归一化
    QVector<double> prob;
    for(auto it = module_fault_prob.begin(); it!=module_fault_prob.end(); it++)
        all_prob+=it.value();

    for(auto it = module_fault_prob.begin(); it!=module_fault_prob.end(); it++)
    {
        if(it.key() == module_name)
        {
            is_have = true;
            module_name_prob = it.value()/all_prob;
        }
        else
            prob.append(it.value()/all_prob);
    }

    if(!is_have)      //如果自定义测点不在module_fault_prob里面
        qDebug()<<"自定义测试"<<module_name<<"没有找到概率";

    for(int i=0; i<prob.count(); i++)
    {
        all_work_well_prob *= (1-prob[i]);
    }


    //如果自定义测试成功，那么信息熵为0，不进行计算

    //如果自定义测试没有成功
    //如果输入的自定义测试器件不在module_fault_prob里，那么默认这个器件对系统的信息熵没有影响
    //如果输入的自定义测试器件在在module_fault_prob里，那么考虑这个器件对系统的信息熵的影响
    double faild_prob;
    if(is_have)
        faild_prob = 1-(module_name_prob * all_work_well_prob);
    else
        faild_prob = 1;


    double information = 1.0;
    for(int i=0; i<prob.size(); i++)
        information += prob[i] * log(1/prob[i]);

    qDebug()<<"输出module_fault_prob";
    for(auto it = module_fault_prob.begin(); it!=module_fault_prob.end(); it++)
        qDebug()<<it.key()<<it.value();

    qDebug()<<"输出归一化prob";
    for(auto it = prob.begin(); it!=prob.end(); it++)
        qDebug()<<*it;

    qDebug()<<"输出faild_prob "<< faild_prob<<" module_name_prob "<<module_name_prob<<" all_work_well_prob "<<all_work_well_prob;

    qDebug()<<"输出Information "<<information << "输出Information*faild_prob" << faild_prob * information;
    return faild_prob * information;
}

void MainWindow::CalculateCustomInformation(QString& base,QStringList& list)
{
    this->base = base;
    this->list = list;
    this->depth = 0;
    custom_process = new QProcess();
    connect(custom_process , SIGNAL(readyReadStandardOutput()) , this , SLOT(on_custom_read()));
    information = 0.0;

    StartCustomProcess();


}

void MainWindow::StartCustomProcess()
{
    if(depth >= list.count())
    {
        delete custom_process;
        custom_process = nullptr;
        return ;
    }

    qDebug()<<"process start "<<base<<" depth "<<depth<<" "<<list[depth];
    QString modelfileName = CurProjectPath+"/test.xmpl";
    QFile file(modelfileName);
    if(file.exists())
    {


        modelfileName = modelfileName.left(modelfileName.lastIndexOf("."));
        QString program = "C:/TBD/data/l2test.exe";
        QStringList arguments;
        arguments<<modelfileName;//传递到exe的参数
        custom_process->start(program,arguments);
        custom_process->setCurrentReadChannel(QProcess::StandardOutput);
        custom_process->waitForStarted(500);

        custom_process->write((base + '\n' + list[depth] + '\n').toLocal8Bit());

        custom_process->waitForBytesWritten(200);
    }
}

void MainWindow::on_custom_read()
{

    QList<QString> temp_candidate_name_list;
    custom_process->waitForReadyRead(200);
    QString output = custom_process->readAllStandardOutput().data();

    qDebug()<<"my_out\n"<<output;

    if(!output.contains("Candidate")) return;

    QList<CandidateData> temp_candidate_list;

    while(1)
    {
        if(!output.contains("Candidate")) break;
        QString StrValidCandidate;
        int indexOfCandidate=output.indexOf("Candidate");
        output=output.mid(indexOfCandidate+9,output.count()-indexOfCandidate-9);
        int NextIndexOfCandidate=output.indexOf("Candidate");
        if(NextIndexOfCandidate>=0) StrValidCandidate=output.mid(0,NextIndexOfCandidate);
        else StrValidCandidate=output;
        //qDebug()<<"StrValidCandidate="<<StrValidCandidate;
        QStringList ListCandidate=StrValidCandidate.split("#");

        for(QString StrOneCandidate:ListCandidate)//test.L02.modeTransition=loose :4
        {
            if(!StrOneCandidate.contains(":")) continue;
            QStringList ListDetailInfo=StrOneCandidate.split(".");
            //if(ListDetailInfo.count()!=3) continue;
            QString StrFaultComponent;

            CandidateData data;
            for(int i=ListDetailInfo.last().indexOf(":")+1;i<ListDetailInfo.last().count();i++)
            {

                if(StrIsNumber(ListDetailInfo.last().at(i))) data.PriorVal+=ListDetailInfo.last().at(i);
                else break;
            }
            for(int i=ListDetailInfo.last().indexOf("=")+1;i<ListDetailInfo.last().count();i++)
            {
                if((ListDetailInfo.last().at(i)!="")&&(ListDetailInfo.last().at(i)!=" ")) data.modeTransition+=ListDetailInfo.last().at(i);
                else break;
            }
            for(int i=1;i<ListDetailInfo.count()-1;i++)
            {
                if(i>1) data.FaultSpur+=".";
                data.FaultSpur+=ListDetailInfo.at(i);
            }
            StrFaultComponent=data.FaultSpur+":"+data.modeTransition+"(Rank="+data.PriorVal+")";
            //计算概率和信息熵
            if(!data.FaultSpur.split('.')[0].isEmpty())
                temp_candidate_name_list.append(data.FaultSpur.split('.')[0]);

            data.FaultProbability = 1 / qPow(2, data.PriorVal.toInt());

            bool is_have = false;
            for(CandidateData& temp_data : temp_candidate_list)
            {
                if(temp_data.FaultSpur == data.FaultSpur
                        && temp_data.modeTransition == data.modeTransition
                        && temp_data.PriorVal == data.PriorVal)

                {
                    is_have = true;
                    break;
                }
            }

            if(!is_have)
                temp_candidate_list.append(data);
        }
    }
    if(temp_candidate_name_list.isEmpty())
        return;

    temp_candidate_name_list.removeDuplicates();

    //更新故障概率
    custom_module_fault_prob.clear();
    for(CandidateData& data : temp_candidate_list)
    {
        if(custom_module_fault_prob.find(data.FaultSpur.split('.')[0]) == custom_module_fault_prob.end())
        {
            custom_module_fault_prob[data.FaultSpur.split('.')[0]] = data.FaultProbability;
        }
        else
        {
            custom_module_fault_prob[data.FaultSpur.split('.')[0]] = custom_module_fault_prob[data.FaultSpur.split('.')[0]] + data.FaultProbability - data.FaultProbability * custom_module_fault_prob[data.FaultSpur.split('.')[0]];
        }

    }

    qDebug()<<"temp_candidate_name_list\n"<<temp_candidate_name_list;


    //计算达到这个结果的概率
    //对原来的module_fault_prob归一化
    QMap<QString, double> temp_module_prob = module_fault_prob;
    double all_prob = 0.0;
    for(auto it =temp_module_prob.begin(); it!=temp_module_prob.end();it++)
        all_prob += it.value();

    qDebug()<<"all_prob "<<all_prob;
    for(auto it =temp_module_prob.begin(); it!=temp_module_prob.end();it++)
    {
        *it = it.value() / all_prob;
        qDebug()<<it.value();
    }

    double result_prob = 1.0;
    for(auto it_old = temp_module_prob.begin(); it_old != temp_module_prob.end(); it_old++)
    {
        auto it_new = custom_module_fault_prob.find(it_old.key());

        if(it_new == custom_module_fault_prob.end())
        {
            result_prob *= 1-it_old.value();
        }
    }
    qDebug()<<"result_prob "<<result_prob;

    //计算新的信息熵
    double information_temp = 0.0;
    //custom_module_fault_prob归一化
    double custom_all_prob = 0.0;
    for(auto it =custom_module_fault_prob.begin(); it!=custom_module_fault_prob.end();it++)
        custom_all_prob += it.value();

    qDebug()<<"custom_all_prob "<<custom_all_prob;
    for(auto it =custom_module_fault_prob.begin(); it!=custom_module_fault_prob.end();it++)
    {
        *it = it.value() / custom_all_prob;
        qDebug()<<it.value();
    }


    for(int i=0; i<temp_candidate_name_list.count(); i++)
    {
        auto it_new = custom_module_fault_prob.find(temp_candidate_name_list[i]);

        information_temp += it_new.value() * log(1/it_new.value());
    }

    information +=  information_temp * result_prob;

    qDebug()<<"information "<<information;
    qDebug()<<"information_temp "<<information_temp;

    qDebug()<<"log test"<<log(3);
    depth++;

    custom_process->close();
    custom_process->waitForFinished();

    StartCustomProcess();
}


void MainWindow::on_toolButton_known_symptom_delete_clicked()
{
    if(ui->tableWidget_known_symptom_select->currentRow()<0) return;
    ui->tableWidget_known_symptom_select->removeRow(ui->tableWidget_known_symptom_select->currentRow());
}

void MainWindow::on_toolButton_not_exit_symptom_modify_clicked()
{
    if(ui->tableWidget_known_symptom_select->currentRow()<0) return;
    AddOrModifyExec(2,ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),0)->text(),ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),1)->text(),ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),2)->text());
}

void MainWindow::on_toolButton_known_symptom_add_clicked()
{
    AddOrModifyExec(1,"","","");
}

void MainWindow::on_BtnEndDiagnose_2_clicked()
{
    FinishDiagnose();
}

void MainWindow::on_BtnEndDiagnose_3_clicked()
{
    FinishDiagnose();
}

void MainWindow::on_toolButton_resule_OK_next_clicked()
{
    FinishDiagnose();
}

void MainWindow::on_toolButton_all_result_next_clicked()
{
    FinishDiagnose();
}

void MainWindow::FinishDiagnose()
{
    SetStackIndex(0);
    ui->label_diagnosis_TestWord->setText("请选择系统功能");
    ui->LbFunction->setText("当前诊断功能:无");
    on_BtnEndDiagnose_clicked();
    ui->stackedWidget->setCurrentIndex(0);
    ListSkipTestPoint.clear();
    QsciEdit->clear();
    ui->EdInputVal1->setText("");
}

void MainWindow::on_BtnShowMdi_clicked()
{
    ui->stackedWidget->setCurrentIndex(0);
}

//获取推荐的测点（跳过人为选择跳过的测点）
void MainWindow::GetRecommendedTestPoint()
{
    //ListSkipTestPoint.append(CurTestPointName);
    if((test_point.count()>0)&&(ui->tableWidgetDiagResult->rowCount()>1))
    {
        int RecommendedTestPointIndex=-1;
        for(int i=0;i<test_point.count();i++)
        {
            bool needSkip=false;
            for(int j=0;j<ListSkipTestPoint.count();j++)
            {
                if(test_point.at(i).point_name==ListSkipTestPoint.at(j))
                {
                    needSkip=true;
                    break;
                }
            }
            //if(test_point.at(i).calculate<0.00000001) continue;
            if(!needSkip)
            {
                RecommendedTestPointIndex=i;
                break;
            }
        }
        if(RecommendedTestPointIndex>=0)
        {
            ui->tableWidgetTestPoint->setCurrentIndex(ui->tableWidgetTestPoint->model()->index(RecommendedTestPointIndex,0));
            on_tableWidgetTestPoint_clicked(ui->tableWidgetTestPoint->model()->index(RecommendedTestPointIndex,0));
            ClearListRedEntity();
            for(int i=0;i<ui->tableWidgetDiagResult->rowCount();i++)
            {
                SetDiagResultRed(ui->tableWidgetDiagResult->item(i,0)->text());
            }
        }
    }
}

void MainWindow::on_toolButton_skip_this_test_clicked()
{
    qDebug()<<"CurTestPointName="<<CurTestPointName<<",ListSkipTestPoint="<<ListSkipTestPoint;
    //判断是否还有其他测试点
    for(int i=0;i<test_point.count();i++)
    {
        bool needSkip=false;
        if(test_point.at(i).point_name==CurTestPointName) continue;
        for(int j=0;j<ListSkipTestPoint.count();j++)
        {
            if(test_point.at(i).point_name==ListSkipTestPoint.at(j))
            {
                needSkip=true;
                break;
            }
        }
        qDebug()<<"test_point="<<test_point.at(i).point_name<<",needSkip="<<needSkip;
        if(!needSkip)
        {
            QsciEdit->append("\r\n//skip "+CurTestPointName);
            ListSkipTestPoint.append(CurTestPointName);
            ui->tableWidgetTestPoint->setCurrentIndex(ui->tableWidgetTestPoint->model()->index(i,0));
            on_tableWidgetTestPoint_clicked(ui->tableWidgetTestPoint->model()->index(i,0));
            return;
        }
    }
    QMessageBox::warning(nullptr, "提示", "没有其他测试点或其他测试点已全部跳过");
}

void MainWindow::on_toolButton_slelct_other_test_clicked()
{
    /*
    QList<QString> list_test;
    for(int i=0;i<test_point.count();i++)
    {
       list_test.append(test_point.at(i).point_name+","+QString::number(test_point.at(i).calculate)+","+QString::number(test_point.at(i).test_cost));
    }*/
    Dialog_select_another_test *dlg=new Dialog_select_another_test(this,&test_point);
    //dlg->InitTable(1);
    dlg->SetTestPreference(TestPointPreference);
    dlg->showNormal();
    dlg->setWindowTitle("候选测试点");
    dlg->setModal(true);

    int ret=dlg->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        QString test_name = dlg->get_test_name();
        SelectTestPoint(test_name);
    }
    delete dlg; //删除对话框
}

void MainWindow::SelectTestPoint(QString TestPointName)
{
    qDebug()<<"SelectTestPoint TestPointName="<<TestPointName;
    for(int i=0;i<test_point.count();i++)
    {
        if(test_point.at(i).point_name==TestPointName)
        {
            QsciEdit->append("\r\n//select "+TestPointName);
            on_tableWidgetTestPoint_clicked(ui->tableWidgetTestPoint->model()->index(i,0));
            break;
        }
    }
}

void MainWindow::on_axWidgetDiagnose_CommandEnded(const QString &sCmdName)
{
    qDebug()<<"axWidgetDiagnose sCmdName="<<sCmdName;
    if((sCmdName=="MXOCXSYS_ImpMxDrawXCommand")||(sCmdName=="MXOCXSYS_CommandInImp"))
    {
        if(FlagSetTestPointHighLight) ui->axWidgetDiagnose->dynamicCall("DoCommand(const int&)",100);
        FlagSetTestPointHighLight=false;
    }
}

void MainWindow::on_axWidgetDiagnose_ImplementCommandEvent(int iCommandId)
{
    qDebug()<<"axWidgetDiagnose on_axWidgetDiagnose_ImplementCommandEvent,iCommandId="<<iCommandId;
    if (iCommandId == 100)   DoSetTestPointHighLight();
}

//根据QsciEdit重新诊断   还需要考虑跳过和选择其他测试点的情况
void MainWindow::on_BtnLastStep_clicked()
{
    QString StrQsciEdit=QsciEdit->text();
    QString StrStepDiagnose=StrQsciEdit.remove(DiagnoseInitStr);
    //找到上一步执行的指令是什么，可能还没执行任何指令，也可能执行fc，也可能是skip或select
    StrStepDiagnose.remove("\r\nfc");
    QString StrLastCmd=StrStepDiagnose.mid(StrStepDiagnose.lastIndexOf("\r\n"),StrStepDiagnose.count()-StrStepDiagnose.lastIndexOf("\r\n")-1);
    if((!StrStepDiagnose.contains("="))&&(!StrStepDiagnose.contains("//skip"))&&(!StrStepDiagnose.contains("//select")))//上一步为选择观测现象
    {
        on_BtnEndDiagnose_clicked();
        QsciEdit->clear();
        ui->label_diagnosis_TestWord->setText("请选择一个或多个观测现象，并单击下一步");
        SetStackIndex(1);
        return;
    }
    else if(StrLastCmd.contains("="))
    {
        //去除所有的"\r\nfc"，然后去除最后一行，再加上"\r\nfc"
        StrQsciEdit=QsciEdit->text();
        StrQsciEdit.remove("\r\nfc");
        StrQsciEdit=StrQsciEdit.mid(0,StrQsciEdit.lastIndexOf("\r\n"));
        StrQsciEdit+="\r\nfc";
        qDebug()<<"//fc,ReDiagnose StrQsciEdit="<<StrQsciEdit;
        //on_BtnEndDiagnose_clicked();
        QsciEdit->clear();
        ReDiagnose(StrQsciEdit);
    }
    else if(StrLastCmd.contains("//skip"))
    {
        StrQsciEdit=QsciEdit->text();
        StrQsciEdit=StrQsciEdit.mid(0,StrQsciEdit.lastIndexOf("\r\n"));
        qDebug()<<"//skip,ReDiagnose StrQsciEdit="<<StrQsciEdit;
        //on_BtnEndDiagnose_clicked();
        QString SkipPointName=StrLastCmd.mid(StrLastCmd.indexOf("//skip")+7,StrLastCmd.count()-StrLastCmd.indexOf("//skip")-7);
        qDebug()<<"SkipPointName="<<SkipPointName;
        ListSkipTestPoint.removeAt(ListSkipTestPoint.indexOf(SkipPointName));
        QsciEdit->clear();
        ReDiagnose(StrQsciEdit);
    }
    else if(StrLastCmd.contains("//select"))
    {
        StrQsciEdit=QsciEdit->text();
        StrQsciEdit=StrQsciEdit.mid(0,StrQsciEdit.lastIndexOf("\r\n"));
        qDebug()<<"//select,ReDiagnose StrQsciEdit="<<StrQsciEdit;
        //on_BtnEndDiagnose_clicked();
        QsciEdit->clear();
        ReDiagnose(StrQsciEdit);
    }
}

void MainWindow::ReDiagnose(QString StrDiagnose)
{
    //如果StrDiagnose的最后一句是"//select"
    QString LastStr=StrDiagnose.mid(StrDiagnose.lastIndexOf("\r\n"),StrDiagnose.count()-StrDiagnose.lastIndexOf("\r\n")-1);
    qDebug()<<"ReDiagnose,LastStr="<<LastStr;
    if(LastStr.contains("//select"))
    {
        QsciEdit->append(StrDiagnose);
        QString TestPointName=LastStr.mid(LastStr.indexOf("//select ")+9,LastStr.count()-LastStr.indexOf("//select ")-9);
        SelectTestPoint(TestPointName);
    }
    else
    {
        ListSkipTestPoint.clear();
        QStringList ListStrDiagnose=StrDiagnose.split("\r\n");
        for(QString tmpStr:ListStrDiagnose)
        {
            if(tmpStr.contains("//skip ")) ListSkipTestPoint.append(tmpStr.mid(tmpStr.indexOf("//skip ")+7,tmpStr.count()-tmpStr.indexOf("//skip ")-7));
        }
        on_BtnEndDiagnose_clicked();
        StartDiagnose(StrDiagnose);
    }
}

void MainWindow::on_toolButton_known_symptom_select_last_clicked()
{
    ui->label_diagnosis_TestWord->setText("请选择系统功能");
    ui->LbFunction->setText("当前诊断功能:无");
    SetStackIndex(0);
}

void MainWindow::on_BtnLastStep_2_clicked()
{
    on_BtnLastStep_clicked();
}

//清空ListRedEntity
void MainWindow::ClearListRedEntity()
{
    for(QString RedEntityHandle:ListRedEntity)
    {
        IMxDrawEntity *Enty=(IMxDrawEntity *)(ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",RedEntityHandle.split(",").at(0)));
        if(Enty==nullptr) continue;

        if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
        {
            IMxDrawBlockReference* blkEnty=(IMxDrawBlockReference*)Enty;
            for (int  j = 0; j < blkEnty->dynamicCall("AttributeCount()").toInt(); j++)
            {
                // 得到块引用中所有的属性
                IMxDrawAttribute *attrib = (IMxDrawAttribute *)blkEnty->querySubObject("AttributeItem(int)",j);
                //qDebug()<<"tag="<<attrib->dynamicCall("Tag()").toString();
                if((attrib->dynamicCall("Tag()").toString()=="设备标识符(显示)")||(attrib->dynamicCall("Tag()").toString()=="连接代号"))
                {
                    if(blkEnty->dynamicCall("GetBlockName()").toString()=="SPS_CDP")
                        attrib->dynamicCall("setColorIndex(int)",McColor::mcGreen);
                    else
                        attrib->dynamicCall("setColorIndex(int)",McColor::mcCyan);
                    break;
                }
            }
            blkEnty->dynamicCall("AssertWriteEnabled()");
        }
        else if(Enty->dynamicCall("ObjectName()").toString()=="McDbMText")
        {
            Enty->dynamicCall("setColorIndex(int)",McColor::mcCyan);
        }
        //formaxwidget *formMxdraw=GetOpenedDwgaxwidget(RedEntityHandle.split(",").at(0),RedEntityHandle.split(",").at(1).toInt());
        //if(formMxdraw==nullptr) continue;
        /*
        IMxDrawEntity *Enty=(IMxDrawEntity *)(ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",RedEntityHandle.split(",").at(0)));
        ui->axWidgetDiagnose->dynamicCall("StopTwinkeEnt (QString)",Enty->ObjectID());
        ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
        */
    }
    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
    ListRedEntity.clear();
}

//诊断可视化用，将块变红色
bool MainWindow::SetEntityRed(QString Handle)
{
    //qDebug()<<"SetEntityRed,Handle="<<Handle;
    IMxDrawEntity *Enty=(IMxDrawEntity *)ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",Handle);
    if(Enty==nullptr) return false;
    //Enty->dynamicCall("setColorIndex(int)",McColor::mcRed);

    if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
    {
        IMxDrawBlockReference* blkEnty=(IMxDrawBlockReference*)Enty;
        for (int  j = 0; j < blkEnty->dynamicCall("AttributeCount()").toInt(); j++)
        {
            // 得到块引用中所有的属性
            IMxDrawAttribute *attrib = (IMxDrawAttribute *)blkEnty->querySubObject("AttributeItem(int)",j);
            //qDebug()<<"attrib->dynamicCall(Tag()).toString()"<<attrib->dynamicCall("Tag()").toString();
            if((attrib->dynamicCall("Tag()").toString()=="设备标识符(显示)")||(attrib->dynamicCall("Tag()").toString()=="连接代号"))
            {
                attrib->dynamicCall("setColorIndex(int)",McColor::mcRed);
                break;
            }
        }
        blkEnty->dynamicCall("AssertWriteEnabled()");
    }
    else if(Enty->dynamicCall("ObjectName()").toString()=="McDbMText")
    {
        Enty->dynamicCall("setColorIndex(int)",McColor::mcRed);
    }
    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
    /*
qDebug()<<"SetEntityRed,Handle="<<Handle;
    int OriginalColor=0xFFFFFF;
    IMxDrawEntity *Enty=(IMxDrawEntity *)ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",Handle);
    if(Enty==nullptr) return false;
    if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
    {
        IMxDrawBlockReference* blkEnty=(IMxDrawBlockReference*)Enty;
        if(blkEnty->dynamicCall("GetBlockName()").toString()=="SPS_CDP") OriginalColor=0x00FF00;//导线定义 绿色
        else OriginalColor=0xFFFFFF;//白色
    }
    else OriginalColor=0x00FF00;//导线 绿色

    OriginalColor=0x00FF00;//导线 绿色
//qDebug()<<"OriginalColor="<<OriginalColor;
    // 准备闪烁颜色.
    MxDrawResbuf* colors = new MxDrawResbuf();
    colors->AddLong(255);
    colors->AddLong(0);
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeColor(QVariant)",colors->asVariant());
    // 设置闪烁间隔的时间
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeTime(int)",500);
    // 开始闪烁
    ui->axWidgetDiagnose->dynamicCall("TwinkeEnt(QString)",Enty->ObjectID());
*/
    return true;
}

void MainWindow::on_BtnFlurUnits_clicked()
{
    FlurWndIsActive=true;
    qDebug()<<"on_BtnFlurUnits_clicked()";
    QList<QString> list_test;
    for(int i=0;i<ui->tableWidgetDiagResult->rowCount();i++)
    {
        list_test.append(ui->tableWidgetDiagResult->item(i,0)->text());
    }
    DialogFlurUnit *dlg=new DialogFlurUnit(this,&list_test);
    dlg->InitTable(2);
    dlg->showNormal();
    dlg->setWindowTitle("模糊组");
    dlg->setModal(true);

    dlg->exec();// 以模态方式显示对话框
    FlurWndIsActive=false;
    if (dlg->RetCode>0) //诊断完成被按下
    {
        SetStackIndex(6);
        ui->label_diagnosis_TestWord->setText("诊断结束");
        QString StrResult;
        for(int i=0;i<dlg->RetDiagnoseList.count();i++)
        {
            if(StrResult!="") StrResult+=" , ";
            StrResult+=dlg->RetDiagnoseList.at(i);
        }

        ui->tableWidget_DiagResult->setRowCount(0);
        QStringList ListFaultInfo=StrResult.split(",");
        for(int i=0;i<ListFaultInfo.count();i++)
        {
            ui->tableWidget_DiagResult->setRowCount(ui->tableWidget_DiagResult->rowCount()+1);
            QString DT,Gaoceng,Pos,Name,SubDT,Daihao,ModeType,RepairPlan,RepairResource;
            Daihao=ListFaultInfo.at(i).mid(0,ListFaultInfo.at(i).indexOf(":")).remove(" ");
            if(Daihao.contains("."))
            {
                DT=Daihao.mid(0,Daihao.indexOf("."));
                SubDT=Daihao.mid(Daihao.indexOf(".")+1,Daihao.count()-Daihao.indexOf(".")-1);
            }
            else DT=Daihao;

            ModeType=ListFaultInfo.at(i).mid(ListFaultInfo.at(i).indexOf(":")+1,ListFaultInfo.at(i).indexOf("(")-ListFaultInfo.at(i).indexOf(":")-1);
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                GetUnitTermimalGaocengAndPos(0,QueryEquipment.value("Equipment_ID").toInt(),Gaoceng,Pos);
                Name=QueryEquipment.value("Name").toString();
                QStringList ListRepairInfo=QueryEquipment.value("RepairInfo").toString().split("￤￤");
                for(int j=0;j<ListRepairInfo.count();j++)
                {
                    if(SubDT!="")
                    {
                        if(ListRepairInfo.at(j).split("￤").at(0).contains(SubDT)&&(ListRepairInfo.at(j).split("￤").at(1)==ModeType))
                        {
                            RepairPlan=ListRepairInfo.at(j).split("￤").at(2);
                            RepairResource=ListRepairInfo.at(j).split("￤").at(3);
                            break;
                        }
                    }
                    else
                    {
                        if((ListRepairInfo.at(j).split("￤").at(0)=="mode")&&(ListRepairInfo.at(j).split("￤").at(1)==ModeType))
                        {
                            RepairPlan=ListRepairInfo.at(j).split("￤").at(2);
                            RepairResource=ListRepairInfo.at(j).split("￤").at(3);
                            break;
                        }
                    }
                }
            }
            else//导线
            {
                Name="导线";
                QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                QString SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+DT+"'";
                QueryJXB.exec(SqlStr);
                if(QueryJXB.next())
                {
                    GetPageGaocengAndPos(QueryJXB.value("Page_ID").toInt(),Gaoceng,Pos);
                    if(ModeType=="loose")
                    {
                        RepairPlan="紧固导线";
                        RepairResource="十字螺丝刀";
                    }
                    else if(ModeType=="broken")
                    {
                        RepairPlan="更换导线";
                        RepairResource="导线,十字螺丝刀";
                    }
                }
            }
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,0,new QTableWidgetItem(Gaoceng+"-"+Pos));//位置
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,1,new QTableWidgetItem(Name));//名称
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,2,new QTableWidgetItem(Daihao));//代号
            ModeType.replace("loose","接触不良");
            ModeType.replace("tripped","接触不良");
            ModeType.replace("blown","器件失效");
            ModeType.replace("broken","器件失效");
            ModeType.replace("unknownFault","未知故障");
            ModeType.replace("malFunction","器件失效");
            ModeType.replace("stuckOpen","卡滞");
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,3,new QTableWidgetItem(ModeType));//故障模式
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,4,new QTableWidgetItem(RepairPlan));//维修方法
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,5,new QTableWidgetItem(RepairResource));//所需资源
        }
        ui->tableWidget_DiagResult->resizeRowsToContents();
        StrResult.replace("KA_cd1","触点");
        StrResult.replace("KA_xq1","线圈");
        StrResult.replace("loose","接触不良");
        StrResult.replace("tripped","接触不良");
        StrResult.replace("blown","器件失效");
        StrResult.replace("broken","器件失效");
        StrResult.replace("unknownFault","未知故障");
        StrResult.replace("malFunction","器件失效");
        StrResult.replace("stuckOpen","卡滞");
        ui->label_result_2->setText("故障器件："+StrResult);
    }
    delete dlg; //删除对话框
}

//获取测试点的测试代价 testpointName:HL01.ePort_in_1_2
double MainWindow::GetTestCost(QString testpointName)
{
    double RetTestCost=0;
    QStringList ListTermID=GetTestPointTermID(testpointName.mid(0,testpointName.indexOf(".")),testpointName.mid(testpointName.indexOf(".")+1,testpointName.count()-testpointName.indexOf(".")-1));
    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    for(int i=0;i<ListTermID.count();i++)
    {
        QString TermID=ListTermID.at(i).split(",").at(0);
        SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+TermID;
        QuerySymb2TermInfo.exec(SqlStr);
        if(QuerySymb2TermInfo.next())
        {
            QString TestCost=QuerySymb2TermInfo.value("TestCost").toString().remove(" ");
            if(StrIsDouble(TestCost)) RetTestCost+=TestCost.toDouble();
        }//end of if(QuerySymb2TermInfo.next())
    }//end of for(int i=0;i<ListTermID.count();i++)

    return RetTestCost;
}

void MainWindow::on_BtnSetTestPreference_clicked()
{
    DialogSetTestPreference *dlg =new DialogSetTestPreference(this);
    dlg->SetPreference(TestPointPreference);
    dlg->show();
    dlg->setModal(true);
    dlg->exec();
    if(!dlg->Canceled) TestPointPreference=dlg->TestPointPreference;
    delete dlg;
}

void MainWindow::on_BtnUserTest_clicked()
{
    qDebug()<<"ListUserTest="<<ListUserTest;
    DialogDiagUserTest *dlg=new DialogDiagUserTest();
    dlg->setWindowTitle("自定义测试选择");
    dlg->LoadTestList(ListUserTest);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        qDebug()<<"dlg->CmdStr="<<dlg->CmdStr;
        dlg->CmdStr+="\r\nfc";
        SendCmd(dlg->CmdStr,true);
    }
    delete dlg;
}

//自动上端子
void MainWindow::on_Btn_SetTerminal_clicked()
{
    DialogAddTerminal *dlg=new DialogAddTerminal();
    dlg->setWindowTitle("上端子");
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        //绘制端子
        formaxwidget *formMdi;
        if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
        {
            formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
            if(formMdi==nullptr) return;

            QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString tempSQL="SELECT * FROM TerminalStrip WHERE DT = '"+dlg->DT+"'";
            QueryVar.exec(tempSQL);
            if(QueryVar.next())
            {
                tempSQL="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryVar.value("TerminalStrip_ID").toString()+"' AND Designation = '"+QString::number(dlg->Designation)+"'";
                QueryVar.exec(tempSQL);
                if(QueryVar.next())
                {
                    //formMdi->AddTerminalTag=dlg->DT;
                    //formMdi->AddTerminalDesignation=dlg->Designation;
                    formMdi->TerminalAdd(QueryVar.value("Terminal_ID").toString());
                }
            }
        }
    }
    delete dlg;
}

void MainWindow::on_BtnDataAnalyse_clicked()
{
    int wT = 200;
    if(CurProjectName=="双电机拖曳收放装置") wT=4200;
    else if(CurProjectName=="收放存储装置") wT=975;
    else if(CurProjectName=="尾轴密封试验装置") wT=240;
    else if(CurProjectName=="集中油源动力系统") wT=5100;

    // 创建对话框并设置样式
    QDialog *waitDialog = new QDialog(this, Qt::FramelessWindowHint | Qt::Dialog);
    waitDialog->setStyleSheet("background-color: #D3D3D3; color: black;font: 75 12pt;"); // 设置灰底黑字的样式
    waitDialog->setFixedSize(400, 100); // 设置对话框的大小

    // 创建布局和标签
    QVBoxLayout *layout = new QVBoxLayout(waitDialog);
    QLabel *label = new QLabel("正在分析计算测试性评价指标，请稍候...");
    //label->setFont(QFont("Arial", 10)); // 设置字体大小
    label->setAlignment(Qt::AlignCenter); // 文本居中
    layout->addWidget(label);
    waitDialog->setLayout(layout);

    // 设置对话框为模态
    waitDialog->setWindowModality(Qt::WindowModal);

    // 记录开始时间戳
    qint64 startTimestamp = QDateTime::currentMSecsSinceEpoch();

    // 显示对话框
    waitDialog->show();

    QTimer::singleShot(wT, this, [this, waitDialog, startTimestamp]() {
        waitDialog->accept();
        waitDialog->deleteLater();

        const TestReportMetrics metrics = buildTestReportMetrics();
        DialogTestReport *dlg = new DialogTestReport(metrics, startTimestamp); // 传递开始时间戳进行计时
        dlg->setWindowTitle("系统统计信息");
        dlg->setModal(true);
        dlg->exec();
        delete dlg;
    });
}


void MainWindow::on_BtnMultiLibManage_clicked()
{
    DialogMultiLib *dlg=new DialogMultiLib(this);
    dlg->setWindowTitle("多端元件库");
    dlg->setModal(true);
    dlg->show();
    dlg->exec();

    if(dlg->Canceled) return;
    if(dlg->RetCode==1) //修改符号
    {
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this);
        formMxdraw->setWindowTitle(dlg->OpenFilePath);
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        formMxdraw->IsDrawingMultiLib=true;
        formMxdraw->EditMultiLib(dlg->OpenFilePath);
    }
    else if(dlgDialogSymbols->RetCode==3) //增加库文件
    {
        //在现有的窗口中选择图形
        if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
        {
            formaxwidget *formMdi;
            formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
            if(formMdi!=nullptr)
            {
                connect(formMdi,SIGNAL(SignalSelectDone(int)),this,SLOT(SlotNewSymbol(int)));
                formMdi->NewSymbolDwgName=dlgDialogSymbols->Symb2_Name+".dwg";
                formMdi->SelectEntitys();
            }
        }
        else//没有打开的主窗口，直接新建
        {
            qDebug()<<"没有打开的主窗口，直接新建";
            QString SourceFileName="C:/TBD/data/SymbolTemplate.dwg";
            QString DestinationFileName="C:/TBD/SYMB2LIB/"+dlgDialogSymbols->Symb2_Name+".dwg";
            QFile::copy(SourceFileName,DestinationFileName);
            SlotNewSymbol(1);
        }
    }

    delete dlg;
}

TestReportMetrics MainWindow::buildTestReportMetrics() const
{
    TestReportMetrics metrics;
    if (ui == nullptr || ui->tableWidgetUnit == nullptr) {
        return metrics;
    }

    const int rowCount = ui->tableWidgetUnit->rowCount();
    metrics.componentCount = rowCount;

    struct ComponentAggregate {
        int totalPorts = 0;
        int measurablePorts = 0;
        int groupSize = 1;
    };

    QHash<int, ComponentAggregate> aggregates;
    QVector<int> componentOrder;
    componentOrder.reserve(rowCount);
    int syntheticSeed = -1;

    for (int row = 0; row < rowCount; ++row) {
        int equipmentId = 0;
        if (auto *item = ui->tableWidgetUnit->item(row, 0)) {
            equipmentId = item->data(Qt::UserRole).toInt();
        }
        if (equipmentId == 0) {
            equipmentId = syntheticSeed--;
        }
        componentOrder.append(equipmentId);
        if (!aggregates.contains(equipmentId)) {
            aggregates.insert(equipmentId, ComponentAggregate());
        }
    }

    QHash<int, int> portToComponent;
    QHash<int, bool> portMeasurable;

    if (T_ProjectDatabase.isValid() && T_ProjectDatabase.isOpen()) {
        QSqlQuery portQuery(T_ProjectDatabase);
        if (portQuery.exec(QStringLiteral("SELECT s.Equipment_ID, t.Symb2TermInfo_ID, t.TestCost "
                                          "FROM Symb2TermInfo t "
                                          "JOIN Symbol s ON t.Symbol_ID = s.Symbol_ID"))) {
            while (portQuery.next()) {
                const int equipmentId = portQuery.value(0).toInt();
                auto it = aggregates.find(equipmentId);
                if (it == aggregates.end())
                    continue;

                const int portId = portQuery.value(1).toInt();
                const double cost = parseTestCost(portQuery.value(2));
                const bool measurable = cost <= kTestCostThreshold;

                it->totalPorts += 1;
                if (measurable) {
                    it->measurablePorts += 1;
                }
                portToComponent.insert(portId, equipmentId);
                portMeasurable.insert(portId, measurable);
            }
        } else {
            qWarning() << "[TestReport] query Symb2TermInfo failed:" << portQuery.lastError();
        }
    } else {
        qWarning() << "[TestReport] project database is not available when collecting statistics";
    }

    metrics.testPointCount = 0;
    int measurablePorts = 0;
    for (auto it = aggregates.constBegin(); it != aggregates.constEnd(); ++it) {
        metrics.testPointCount += it.value().totalPorts;
        measurablePorts += it.value().measurablePorts;
    }
    metrics.faultDetectionRate = (metrics.testPointCount > 0)
            ? static_cast<double>(measurablePorts) / metrics.testPointCount
            : 0.0;
    if (metrics.faultDetectionRate < 0.0) {
        metrics.faultDetectionRate = 0.0;
    } else if (metrics.faultDetectionRate > 1.0) {
        metrics.faultDetectionRate = 1.0;
    }

    QHash<int, QSet<int>> adjacency;
    if (T_ProjectDatabase.isValid() && T_ProjectDatabase.isOpen()) {
        QSqlQuery connQuery(T_ProjectDatabase);
        if (connQuery.exec(QStringLiteral("SELECT Symb1_ID, Symb2_ID, Symb1_Category, Symb2_Category FROM JXB"))) {
            while (connQuery.next()) {
                const QString symb1 = connQuery.value(0).toString();
                const QString symb2 = connQuery.value(1).toString();
                if (symb1.isEmpty() || symb2.isEmpty())
                    continue;
                if (shouldSkipConnectionId(symb1) || shouldSkipConnectionId(symb2))
                    continue;

                metrics.connectionCount += 1;

                const int category1 = connQuery.value(2).toInt();
                const int category2 = connQuery.value(3).toInt();
                if (category1 != 0 || category2 != 0)
                    continue;

                bool ok1 = false;
                bool ok2 = false;
                const int portId1 = parsePortId(symb1, &ok1);
                const int portId2 = parsePortId(symb2, &ok2);
                if (!ok1 || !ok2)
                    continue;

                if (!portToComponent.contains(portId1) || !portToComponent.contains(portId2))
                    continue;

                if (portMeasurable.value(portId1, true) && portMeasurable.value(portId2, true))
                    continue;

                const int component1 = portToComponent.value(portId1);
                const int component2 = portToComponent.value(portId2);
                if (component1 == component2)
                    continue;

                adjacency[component1].insert(component2);
                adjacency[component2].insert(component1);
            }
        } else {
            qWarning() << "[TestReport] query JXB failed:" << connQuery.lastError();
        }
    }

    QSet<int> visited;
    for (auto it = aggregates.begin(); it != aggregates.end(); ++it) {
        const int componentId = it.key();
        if (visited.contains(componentId))
            continue;

        QVector<int> stack;
        stack.append(componentId);
        QSet<int> groupMembers;

        while (!stack.isEmpty()) {
            const int current = stack.takeLast();
            if (visited.contains(current))
                continue;
            visited.insert(current);
            groupMembers.insert(current);
            const auto neighbors = adjacency.value(current);
            for (int neighbor : neighbors) {
                if (!visited.contains(neighbor)) {
                    stack.append(neighbor);
                }
            }
        }

        const int groupSize = groupMembers.isEmpty() ? 1 : groupMembers.size();
        for (int member : groupMembers) {
            aggregates[member].groupSize = groupSize;
        }
        if (groupMembers.isEmpty()) {
            aggregates[componentId].groupSize = 1;
        }
    }

    QMap<int, int> fuzzyCounts;
    for (int componentId : componentOrder) {
        const auto aggIt = aggregates.constFind(componentId);
        const int size = (aggIt != aggregates.constEnd()) ? aggIt.value().groupSize : 1;
        fuzzyCounts[size] += 1;
    }

    int iso1Count = 0;
    int iso2Count = 0;
    int iso3Count = 0;
    for (auto it = fuzzyCounts.constBegin(); it != fuzzyCounts.constEnd(); ++it) {
        const int size = it.key();
        const int count = it.value();
        if (size <= 1) {
            iso1Count += count;
        }
        if (size <= 2) {
            iso2Count += count;
        }
        if (size <= 3) {
            iso3Count += count;
        }
    }

    const double denominator = metrics.componentCount > 0
            ? static_cast<double>(metrics.componentCount)
            : 1.0;
    metrics.faultIsolationRate1 = iso1Count / denominator;
    metrics.faultIsolationRate2 = iso2Count / denominator;
    metrics.faultIsolationRate3 = iso3Count / denominator;

    auto clampRate = [](double value) {
        if (value < 0.0) return 0.0;
        if (value > 1.0) return 1.0;
        return value;
    };
    metrics.faultIsolationRate1 = clampRate(metrics.faultIsolationRate1);
    metrics.faultIsolationRate2 = clampRate(metrics.faultIsolationRate2);
    metrics.faultIsolationRate3 = clampRate(metrics.faultIsolationRate3);

    metrics.faultSetSize = metrics.componentCount + metrics.connectionCount;
    metrics.mtbfHours = computeMtbf(metrics.componentCount, metrics.connectionCount);
    metrics.mttrHours = computeMttr(metrics.componentCount, metrics.connectionCount);
    metrics.fuzzyGroupComponentCounts = fuzzyCounts;

    if (T_ProjectDatabase.isValid() && T_ProjectDatabase.isOpen()) {
        FunctionRepository repo(T_ProjectDatabase);
        if (repo.ensureTables()) {
            metrics.functionCount = repo.fetchAll().size();
        } else {
            qWarning() << "[TestReport] ensure Function tables failed";
        }
    }

    return metrics;
}

void MainWindow::on_BtnSetCentrePoint_clicked()
{
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            if(formMdi->IsDrawingMultiLib)
                formMdi->GetAxWidget()->dynamicCall("DoCommand(const int&)",104);
        }
    }
}

void MainWindow::on_mdiArea_subWindowActivated(QMdiSubWindow *arg1)
{
    if(arg1==nullptr) return;
    bool IsMultiLib=false;
    if(arg1->windowTitle().contains(".dwg"))
    {
        formaxwidget *formMdi=(formaxwidget*)arg1;
        if(formMdi->IsDrawingMultiLib) IsMultiLib=true;
    }
    if(IsMultiLib)
    {
        ui->BtnSetCentrePoint->setEnabled(true);
        ui->Btn_MultiLine->setEnabled(false);
        ui->Btn_SetTerminal->setEnabled(false);
        ui->Btn_BlackBox->setEnabled(true);
        ui->Btn_StructBox->setEnabled(false);
        ui->Btn_TypicalDwg->setEnabled(false);
        ui->Btn_LineDefine->setEnabled(false);
        ui->Btn_CableDefine->setEnabled(false);
    }
    else
    {
        ui->BtnSetCentrePoint->setEnabled(false);
        ui->Btn_MultiLine->setEnabled(true);
        ui->Btn_SetTerminal->setEnabled(true);
        ui->Btn_BlackBox->setEnabled(true);
        ui->Btn_StructBox->setEnabled(true);
        ui->Btn_TypicalDwg->setEnabled(true);
        ui->Btn_LineDefine->setEnabled(true);
        ui->Btn_CableDefine->setEnabled(true);
    }
}

//放置文字
void MainWindow::on_BtnPutText_clicked()
{
    QDialog *dialogTextStr =new QDialog();
    dialogTextStr->setWindowTitle("请输入插入的文字内容");
    dialogTextStr->setMinimumSize(QSize(300,60));
    QFormLayout *formlayoutDesignation = new QFormLayout(dialogTextStr);
    QLineEdit *m_LineEdit = new QLineEdit(dialogTextStr);

    QHBoxLayout *layoutBtn = new QHBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogTextStr);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel = new QPushButton(dialogTextStr);
    pushbuttonCancel->setText("取消");
    layoutBtn->addWidget(pushbuttonOK);
    layoutBtn->addWidget(pushbuttonCancel);
    formlayoutDesignation->addRow(m_LineEdit);
    formlayoutDesignation->addRow(layoutBtn);
    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogTextStr,SLOT(accept()));
    if (dialogTextStr->exec()!=QDialog::Accepted) return;

    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->LoadText(m_LineEdit->text());
    }
}

void MainWindow::on_BtnClearDB_clicked()
{
    QSqlQuery QueryPage=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Page ORDER BY Page_ID ASC";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) continue;
        GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath);
        QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
        QSqlQuery QueryDELETE=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM TerminalInstance WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"'";
        QueryTerminalInstance.exec(SqlStr);
        while(QueryTerminalInstance.next())
        {
            IMxDrawEntity *BlkSearch=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryTerminalInstance.value("Handle").toString());
            qDebug()<<"QueryTerminalInstance.value(Handle).toString()="<<QueryTerminalInstance.value("Handle").toString();
            if((BlkSearch==nullptr)||EntyIsErased(GlobalBackAxWidget,BlkSearch))
            {
                qDebug()<<"delete "<<QueryTerminalInstance.value("Handle").toString();
                SqlStr =  "DELETE FROM TerminalInstance WHERE TerminalInstanceID = "+QueryTerminalInstance.value("TerminalInstanceID").toString();
                QueryDELETE.exec(SqlStr);
            }
        }

        QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Connector WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"'";
        QueryConnector.exec(SqlStr);
        while(QueryConnector.next())
        {
            IMxDrawEntity *BlkSearch=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryConnector.value("Connector_Handle").toString());
            if((BlkSearch==nullptr)||EntyIsErased(GlobalBackAxWidget,BlkSearch))
            {
                SqlStr =  "DELETE FROM Connector WHERE Connector_ID = "+QueryConnector.value("Connector_ID").toString();
                QueryDELETE.exec(SqlStr);
            }
        }

        QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Wires WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"'";
        QueryWires.exec(SqlStr);
        while(QueryWires.next())
        {
            IMxDrawEntity *BlkSearch=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryWires.value("Handle").toString());
            if((BlkSearch==nullptr)||EntyIsErased(GlobalBackAxWidget,BlkSearch))
            {
                SqlStr =  "DELETE FROM Wires WHERE Wires_ID = "+QueryWires.value("Wires_ID").toString();
                QueryDELETE.exec(SqlStr);
            }
        }
        //清除重叠的连线
        IMxDrawSelectionSet *ssLINE= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filterLINE=(IMxDrawResbuf *)GlobalBackAxWidget->querySubObject("NewResbuf()");
        filterLINE->AddStringEx("LINE",5020);
        filterLINE->AddStringEx("CONNECT", 8);
        ssLINE->dynamicCall("AllSelect(QVariant)",filterLINE->asVariant());
        int Cnt=ssLINE->dynamicCall("Count()").toInt();
        for(int LineIndex=0;LineIndex<Cnt;LineIndex++)
        {
            IMxDrawLine *mLine= (IMxDrawLine *)ssLINE->querySubObject("Item(int)",LineIndex);
            if(EntyIsErased(GlobalBackAxWidget,(IMxDrawEntity *)mLine)) continue;//去除erase的实体
            IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
            //创建过滤对象
            MxDrawResbuf* filter =new MxDrawResbuf();
            filter->AddStringEx("LINE",5020);
            filter->AddStringEx("CONNECT", 8);
            for(int k=0;k<2;k++)
            {
                if(k==0) ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->asVariant(),filter->asVariant());
                if(k==1) ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->asVariant(),filter->asVariant());
                qDebug()<<"ss.Count()="<<ss->Count();
                for (int i = 0; i < ss->Count(); i++)
                {
                    IMxDrawLine* mLineCross = (IMxDrawLine *)ss->querySubObject("Item(int)",i);
                    if(EntyIsErased(GlobalBackAxWidget,(IMxDrawEntity *)mLineCross)) continue;//去除erase的实体
                    if(mLineCross->dynamicCall("handle()").toString()==mLine->dynamicCall("handle()").toString()) continue;//排除自身
                    //mLineCross是mLine的子线段（被包含）
                    double mLineStartx=((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->x();
                    double mLineStarty=((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->y();
                    double mLineEndx=((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x();
                    double mLineEndy=((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->y();
                    double mLineCrossStartx=((IMxDrawPoint *)mLineCross->querySubObject("StartPoint()"))->x();
                    double mLineCrossStarty=((IMxDrawPoint *)mLineCross->querySubObject("StartPoint()"))->y();
                    double mLineCrossEndx=((IMxDrawPoint *)mLineCross->querySubObject("EndPoint()"))->x();
                    double mLineCrossEndy=((IMxDrawPoint *)mLineCross->querySubObject("EndPoint()"))->y();
                    bool ShouldErase=false;

                    if((GetLineDir(mLine)=="水平")&&(GetLineDir(mLineCross)=="水平"))
                    {
                        if(mLineStartx<mLineEndx)
                        {
                            if((mLineStartx<=mLineCrossStartx)&&(mLineStartx<=mLineCrossEndx)&&(mLineEndx>=mLineCrossStartx)&&(mLineEndx>=mLineCrossEndx)) ShouldErase=true;
                        }
                        else
                        {
                            if((mLineStartx>=mLineCrossStartx)&&(mLineStartx>=mLineCrossEndx)&&(mLineEndx<=mLineCrossStartx)&&(mLineEndx<=mLineCrossEndx)) ShouldErase=true;
                        }
                    }
                    else if((GetLineDir(mLine)=="垂直")&&(GetLineDir(mLineCross)=="垂直"))
                    {
                        if(mLineStarty<mLineEndy)
                        {
                            if((mLineStarty<=mLineCrossStarty)&&(mLineStarty<=mLineCrossEndy)&&(mLineEndy>=mLineCrossStarty)&&(mLineEndy>=mLineCrossEndy)) ShouldErase=true;
                        }
                        else
                        {
                            if((mLineStarty>=mLineCrossStarty)&&(mLineStarty>=mLineCrossEndy)&&(mLineEndy<=mLineCrossStarty)&&(mLineEndy<=mLineCrossEndy)) ShouldErase=true;
                        }
                    }
                    if(ShouldErase) mLineCross->dynamicCall("Erase()");
                }
            }//end of for(int k=0;k<2;k++)
        }//for(int LineIndex=0;LineIndex<Cnt;LineIndex++)
        GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
    }
}


void MainWindow::on_CbTestType_currentIndexChanged(const QString &arg1)
{
    Q_UNUSED(arg1);
    if(ui->CbTestType->currentText()=="电压") ui->LbDW->setText("V");
    else if(ui->CbTestType->currentText()=="电流") ui->LbDW->setText("A");
    else if(ui->CbTestType->currentText()=="电阻") ui->LbDW->setText("R");
}

// ============ 新诊断系统函数 ============

void MainWindow::displayCurrentTest()
{
    if (!diagnosisEngine) {
        qCritical() << "DiagnosisEngine is null in displayCurrentTest";
        return;
    }
    
    DiagnosisTreeNode* currentTest = diagnosisEngine->getCurrentRecommendedTest();
    
    if (!currentTest) {
        qWarning() << "当前没有有效的推荐测试";
        
        // 检查是否已完成诊断
        if (diagnosisEngine->isFaultIsolated()) {
            DiagnosisTreeNode* faultNode = diagnosisEngine->getFaultConclusion();
            
            // 显示诊断结果
            ui->label_diagnosis_TestWord->setText("诊断完成");
            
            QString resultText = QString("故障定位结果:\n\n%1\n\n隔离度: %2")
                .arg(faultNode ? faultNode->faultHypothesis() : "未知")
                .arg(faultNode ? faultNode->isolationLevel() : 0);
            
            // 显示诊断路径
            QList<DiagnosisStep> path = diagnosisEngine->getDiagnosisPath();
            
            if (!path.isEmpty()) {
                resultText += "\n\n诊断路径:\n";
                for (int i = 0; i < path.size(); ++i) {
                    DiagnosisTreeNode* node = path[i].testNode;  // 使用testNode而非node
                    TestOutcome outcome = path[i].outcome;
                    QString outcomeStr = (outcome == TestOutcome::Pass) ? "通过" : "失败";
                    resultText += QString("%1. %2 -> %3\n")
                        .arg(i + 1)
                        .arg(node ? node->testDescription() : "未知测试")
                        .arg(outcomeStr);
                }
            }
            
            ui->label_test_description_1->setText(resultText);
            QMessageBox::information(nullptr, "诊断完成", resultText);
            
            // 返回功能选择页面
            FinishDiagnose();
        } else {
            QMessageBox::warning(nullptr, "错误", "诊断流程异常：无推荐测试且未完成故障定位");
            FinishDiagnose();
        }
        return;
    }
    
    // 显示当前推荐的测试信息
    QString testDesc = currentTest->testDescription();
    QString expectedResult = currentTest->expectedResult();
    QString passButtonText = currentTest->passButtonText();
    QString failButtonText = currentTest->failButtonText();
    
    // 如果按钮文本为空，使用默认值
    if (passButtonText.isEmpty()) passButtonText = "是";
    if (failButtonText.isEmpty()) failButtonText = "否";
    
    ui->label_diagnosis_TestWord->setText("执行测试");
    
    QString displayText = QString("测试描述:\n%1\n\n预期结果:\n%2\n\n请执行测试并选择测试结果:")
        .arg(testDesc.isEmpty() ? "无描述" : testDesc)
        .arg(expectedResult.isEmpty() ? "无预期结果" : expectedResult);
    
    // 添加按钮文本提示
    displayText += QString("\n\n[%1] 或 [%2]").arg(passButtonText).arg(failButtonText);
    
    ui->label_test_description_1->setText(displayText);
    
    // 尝试动态设置按钮文本（如果按钮存在）
    QPushButton* btnPass = ui->page_main_diagnosis->findChild<QPushButton*>("btnTestPass");
    QPushButton* btnFail = ui->page_main_diagnosis->findChild<QPushButton*>("btnTestFail");
    QPushButton* btnSkip = ui->page_main_diagnosis->findChild<QPushButton*>("btnSkipTest");
    
    if (btnPass) {
        btnPass->setText(passButtonText);
        btnPass->setVisible(true);
        btnPass->setEnabled(true);
    }
    if (btnFail) {
        btnFail->setText(failButtonText);
        btnFail->setVisible(true);
        btnFail->setEnabled(true);
    }
    if (btnSkip) {
        btnSkip->setText("跳过");
        btnSkip->setVisible(true);
        btnSkip->setEnabled(true);
    }
    
    qDebug() << "显示测试: node_id=" << currentTest->nodeId() 
             << ", 描述=" << testDesc
             << ", 按钮文本=[" << passButtonText << "/" << failButtonText << "]";
}

void MainWindow::recordCurrentTestResult(TestOutcome outcome)
{
    if (!diagnosisEngine) {
        qCritical() << "DiagnosisEngine is null in recordCurrentTestResult";
        return;
    }
    
    DiagnosisTreeNode* currentTest = diagnosisEngine->getCurrentRecommendedTest();
    if (!currentTest) {
        qWarning() << "当前没有有效的测试可记录结果";
        return;
    }
    
    QString outcomeStr;
    switch(outcome) {
        case TestOutcome::Pass: outcomeStr = "通过"; break;
        case TestOutcome::Fail: outcomeStr = "失败"; break;
        case TestOutcome::Skip: outcomeStr = "跳过"; break;
        default: outcomeStr = "未知"; break;
    }
    
    qDebug() << "记录测试结果: node_id=" << currentTest->nodeId() 
             << ", outcome=" << outcomeStr;
    
    // 记录测试结果并移动到下一个节点
    if (!diagnosisEngine->recordTestResult(outcome)) {
        QMessageBox::warning(nullptr, "错误", "记录测试结果失败！");
        qWarning() << "recordTestResult返回false";
        return;
    }
    
    // 显示下一个测试或诊断结果
    displayCurrentTest();
}

// ============ UI槽函数 ============

void MainWindow::on_btnTestPass_clicked()
{
    qDebug() << "用户点击: 测试通过";
    recordCurrentTestResult(TestOutcome::Pass);
}

void MainWindow::on_btnTestFail_clicked()
{
    qDebug() << "用户点击: 测试失败";
    recordCurrentTestResult(TestOutcome::Fail);
}

void MainWindow::on_btnSkipTest_clicked()
{
    qDebug() << "用户点击: 跳过测试";
    recordCurrentTestResult(TestOutcome::Skip);
}
