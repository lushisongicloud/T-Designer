#include "qxcombobox.h"

qxcombobox::qxcombobox(QWidget * parent):QComboBox(parent)
{
    this->setEditable(true);
}

void qxcombobox::UpdateExecStateItems(QString ExecName)
{

    DT=ExecName.mid(0,ExecName.lastIndexOf("."));
    QStringList ListSpurName=ExecName.mid(ExecName.lastIndexOf(".")+1,ExecName.count()-ExecName.lastIndexOf(".")-1).remove(" ").split("￤");
qDebug()<<"UpdateExecStateItems,ExecName="<<ExecName<<",DT="<<DT<<",ListSpurName="<<ListSpurName;
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
       QString StrUnitDesc=QueryEquipment.value("TModel").toString();
       QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
       this->clear();
       for(QString StrStructure:ListStructure)
       {
           if(StrStructure.split(",").at(2)=="Observable") this->addItem(StrStructure.split(",").at(0));
       }
    }
    else//导线
    {
        this->clear();
        this->addItem("ePort_in_1_2");
        this->addItem("ePort_out_1_2");
    }
}

void qxcombobox::UpdateExecStateValueItems(QString ExecState)
{
    qxcombobox *m_combobox=(qxcombobox *)sender();
    DT=m_combobox->DT;
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        //可以添加的器件是含有cmdIn变量或源的currentIn
       QString StrUnitDesc=QueryEquipment.value("TModel").toString();
       //提取Enum
       QStringList ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal;
       CompileStructure(StrUnitDesc,"",ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal);
       for(QString StrEnumName:ListEnumName)
       {
           if(StrEnumName.contains(ExecState))
           {
               this->clear();
               QString ExecStateVal=ListEnumVal.at(ListEnumName.indexOf(StrEnumName));
qDebug()<<"ExecStateVal="<<ExecStateVal;
               ExecStateVal.remove(",undefined").remove(",default");
               this->addItems(ExecStateVal.split(","));
               break;
           }
       }
    }
    else//导线
    {
        this->clear();
        this->addItem("on");
        this->addItem("off");
    }
}

//用于自定义测试新增条件
//RbMode=1: RbIncludeUnit
//RbMode=2: RbBelongLink
//RbMode=3: RbModeType
void qxcombobox::UpdateUnitSpurItems(QString DT)
{
    this->clear();
    this->setEnabled(true);
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;

    if(DT.contains(".")) SqlStr= "SELECT * FROM Equipment WHERE DT = '"+DT.mid(0,DT.indexOf("."))+"'";
    else  SqlStr= "SELECT * FROM Equipment WHERE DT = '"+DT+"'";

    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {

        if(RbMode==1)
        {
            QStringList SubComponentList=GetSubComponentList(QueryEquipment.value("TModel").toString());
            if(SubComponentList.count()==0) this->setEnabled(false);
            else
            {
                for(int i=0;i<SubComponentList.count();i++)
                  this->addItem(SubComponentList.at(i).split(",").at(1));
            }
        }
        else if(RbMode==2)
        {
            QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
            QuerySymbol.exec(SqlStr);
            this->clear();
            while(QuerySymbol.next())
            {
                this->addItem(GetUnitSpurStrBySymbol_ID(QuerySymbol));
            }
        }
        else if(RbMode==3)
        {
            QString StrUnitDesc=QueryEquipment.value("TModel").toString();
            QStringList ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal;
            CompileStructure(StrUnitDesc,"",ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal);
            //添加子器件的enum
            QStringList SubComponentList=GetSubComponentList(QueryEquipment.value("TModel").toString());
            for(QString StrSubComponent:SubComponentList)
            {
                QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
                QString StrSql="SELECT * FROM FunctionDefineClass WHERE TClassName = '"+StrSubComponent.split(",").at(0)+"'";
                QueryFunctionDefineClass.exec(StrSql);
                if(QueryFunctionDefineClass.next())
                {
                   QString SubModuleTModel=QueryFunctionDefineClass.value("TModel").toString();
                   CompileStructure(SubModuleTModel,StrSubComponent.split(",").at(1),ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal);
                }
            }
            for(int i=0;i<ListEnumTypeName.count();i++)
            {
                if(ListEnumTypeName.at(i)=="ModeType")
                {
                    if(DT.contains("."))
                    {
                        if(ListEnumName.at(i).contains("."))
                        {
                           if(ListEnumName.at(i).contains(DT.mid(DT.lastIndexOf(".")+1,DT.count()-DT.lastIndexOf(".")-1)))
                               this->addItems(ListEnumVal.at(i).split(","));
                        }
                    }
                    else
                        this->addItems(ListEnumVal.at(i).split(","));
                }
            }
        }
    }
    else
    {
        if(RbMode!=3)  this->setEnabled(false);
        else this->addItems({"nominal","loose","broken","unknownFault"});
    }
}

void qxcombobox::UpdateExecItems(QString DT)
{
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
        QuerySymbol.exec(SqlStr);
        this->clear();
        while(QuerySymbol.next())
        {
            if(QuerySymbol.value("ExecConn").toBool()) this->addItem(GetUnitSpurStrBySymbol_ID(QuerySymbol));
        }
    }
}

//解析Name对应的状态值
void qxcombobox::UpdateCmdItems(QString Name)
{
qDebug()<<"slot UpdateItems,Name="<<Name;
    QString EnumName=Name.mid(Name.lastIndexOf(".")+1,Name.count()-Name.lastIndexOf(".")-1);
    QString DT=Name.mid(0,Name.lastIndexOf("."));
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        //可以添加的器件是含有cmdIn变量或源的currentIn
       QString StrUnitDesc=QueryEquipment.value("TModel").toString();
       //提取Enum
       QStringList ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal;
       CompileStructure(StrUnitDesc,"",ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal);
       if(ListEnumName.contains(EnumName))
       {
           this->clear();
           this->addItems(ListEnumVal.at(ListEnumName.indexOf(EnumName)).split(","));
           this->addItem("undefined");
           this->addItem("default");
       }
    }
}

void qxcombobox::UpdateObserveItems(bool OnlyExec)
{

}

void qxcombobox::UpdateItems(bool OnlyExec)
{
    QString Original=this->currentText();
    this->clear();
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+CurFunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
       QStringList ExecsList;
       if(OnlyExec) ExecsList=QueryFunction.value("ExecsList").toString().split(",");
       else
       {
           QString tmpStr=StrSystemDefine;
           ExecsList=tmpStr.remove("\r\n").split(";");
           for(int i=0;i<ExecsList.count();i++)
           {
               ExecsList[i]=ExecsList.at(i).split(" ").last();
               if(ExecsList[i]=="") ExecsList.removeAt(i);
           }
       }
       for(QString StrExec:ExecsList)
       {
           bool skip=false;
           if(Mode==1)
           {
               for(int i=0;i<ExistedUnits.count();i++)
               {
                   if(StrExec.mid(0,StrExec.indexOf("."))==ExistedUnits.at(i))
                   {
                       skip=true;
                       break;
                   }
               }
           }
           if(!skip) this->addItem(StrExec.mid(0,StrExec.indexOf(".")));
       }
    }
    this->setCurrentText(Original);
}

void qxcombobox::UpdateUserItems(bool OnlyExec)
{
qDebug()<<"UpdateUserItems,CurExecsList="<<CurExecsList;
    QString Original=this->currentText();
    this->clear();
    QStringList ExecsList;
    if(OnlyExec) ExecsList=CurExecsList;
    else
    {
        QString tmpStr=StrSystemDefine;
        ExecsList=tmpStr.remove("\r\n").split(";");
        for(int i=0;i<ExecsList.count();i++)
        {
            ExecsList[i]=ExecsList.at(i).split(" ").last();
            if(ExecsList[i]=="") ExecsList.removeAt(i);
        }
    }
    for(QString StrExec:ExecsList)
    {
        bool skip=false;
        if(Mode==1)
        {
            for(int i=0;i<ExistedUnits.count();i++)
            {
                if(StrExec.mid(0,StrExec.indexOf("."))==ExistedUnits.at(i))
                {
                    skip=true;
                    break;
                }
            }
        }
        if(!skip) this->addItem(StrExec.mid(0,StrExec.indexOf(".")));
    }
    this->setCurrentText(Original);
}

void qxcombobox::UpdateUnitPara(QString UnitName)
{
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM Equipment WHERE DT = '"+UnitName+"'";
    QueryEquipment.exec(temp);
    QStringList ListTModelPara;
    if(QueryEquipment.next())
    {
        QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
        for(int i=0;i<ListStructure.count();i++)
        {
            if(ListStructure.at(i).contains(","))
               ListTModelPara.append(ListStructure.at(i).split(",").at(0));
        }
    }
    this->addItems(ListTModelPara);
}


