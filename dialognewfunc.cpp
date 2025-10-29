#include "dialognewfunc.h"
#include "ui_dialognewfunc.h"

DialogNewFunc::DialogNewFunc(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogNewFunc)
{
    ui->setupUi(this);
    InitTEdit();
    Canceled=true;
}

DialogNewFunc::~DialogNewFunc()
{
    delete ui;
}

void DialogNewFunc::InitTEdit()
{
    QsciEdit = new QsciScintilla();
    ui->TEditLayout->addWidget(QsciEdit);
    ui->frame_Edit->setLayout(ui->TEditLayout);
    //connect(QsciEdit, SIGNAL(textChanged()),this, SLOT(ModelWasModified()));
    //setCurrentFile("");
    //设置字体
    QFont font("Courier", 10, QFont::Normal);
    QsciEdit->setFont(font);
    QsciEdit->setMarginsFont(font);
    QFontMetrics fontmetrics = QFontMetrics(font);
    //设置左侧行号栏宽度等
    QsciEdit->setMarginWidth(0, fontmetrics.width("000"));
    QsciEdit->setMarginLineNumbers(0, true);
    QsciEdit->setBraceMatching(QsciScintilla::SloppyBraceMatch);
    QsciEdit->setTabWidth(4);
    //设置括号等自动补全
    QsciEdit->setAutoIndent(true);
    //初始设置c++解析器
    //textEdit->setLexer(new QsciLexerCPP(this));
    QscilexerCppAttach *textLexer = new QscilexerCppAttach;
    textLexer->setColor(QColor(Qt:: yellow),QsciLexerCPP::CommentLine);    //设置自带的注释行为绿色
    textLexer->setColor(QColor(Qt::red),QsciLexerCPP::KeywordSet2);
    QsciEdit->setLexer(textLexer);
    //设置自动补全

    QsciAPIs *apis = new QsciAPIs(textLexer);
    apis->add(QString("DEF"));
    apis->add(QString("PORT"));
    apis->add(QString("METER"));
    apis->add(QString("METER_PIC"));
    apis->add(QString("METER_MODE"));

    apis->prepare();

    QFont font1("Courier", 10, QFont::Normal);
    //    this->setFont(font1);

    QsciEdit->setAutoCompletionSource(QsciScintilla::AcsAll);   //设置源，自动补全所有地方出现的
    QsciEdit->setAutoCompletionCaseSensitivity(true);   //设置自动补全大小写敏感
    QsciEdit->setAutoCompletionThreshold(2);    //设置每输入2个字符就会出现自动补全的提示

    QsciEdit->setCaretLineVisible(true);
    //设置光标所在行背景色
    QsciEdit->setCaretLineBackgroundColor(Qt::lightGray);

    // ui->textEdit->setCursorPosition(2,2);
    //int markerDefine(MarkerSymbol sym, int markerNumber = -1);
    QsciEdit->SendScintilla(QsciScintilla::SCI_SETCODEPAGE,QsciScintilla::SC_CP_UTF8);//设置编码为UTF-8
    //得到光标位置
    int line,col;
    QsciEdit->getCursorPosition(&line,&col);

    //设置显示字体
    QsciEdit->setFont(QFont("Courier New"));
    //设置编码方式
    QsciEdit->SendScintilla(QsciScintilla::SCI_SETCODEPAGE,QsciScintilla::SC_CP_UTF8);//设置编码为UTF-8
}

void DialogNewFunc::LoadInfo(QString FunctionDefineClass_ID)
{
    this->FunctionDefineClass_ID=FunctionDefineClass_ID;
    QSqlQuery QueryFunctionDefineClass= QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+FunctionDefineClass_ID+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    if(QueryFunctionDefineClass.next())
    {
        ui->EdFuncName->setText(QueryFunctionDefineClass.value("FunctionDefineName").toString());
        QString DefaultSymbol=QueryFunctionDefineClass.value("DefaultSymbol").toString();
        if(DefaultSymbol.contains("_S_")) ui->RbSingleTerm->setChecked(true);
        else ui->RbMultiTerm->setChecked(true);

        if(DefaultSymbol.count()>6) ui->EbLibFileName->setText(DefaultSymbol.mid(6,DefaultSymbol.lastIndexOf("-")));//去除SPS_M_
        QString PathDwg;
        if(DefaultSymbol.contains("ES2_")) PathDwg+="C:/TBD/SYMB2LIB/"+DefaultSymbol+".dwg";
        else if(DefaultSymbol.contains("SPS_")) PathDwg+="C:/TBD/SPS/"+DefaultSymbol+".dwg";
        UnitSymbolsView(PathDwg,"C:/TBD/data/TempImage/"+DefaultSymbol+".jpg",ui->LbSPSPic,true);
        FilePath=PathDwg;
        ui->CbFuncType->setCurrentText(QueryFunctionDefineClass.value("FuncType").toString());
        QsciEdit->setText(QueryFunctionDefineClass.value("TModel").toString());
        ui->EbTModelClass->setText(QueryFunctionDefineClass.value("TClassName").toString());
    }
    ui->EbLibFileName->setEnabled(false);
}

void DialogNewFunc::on_BtnOK_clicked()
{
    if(ui->EdFuncName->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", " 功能名称不能为空");
        return;
    }
    if(ui->EbLibFileName->text()!="")
    {
        QString NewPath;
        if(ui->RbSingleTerm->isChecked())
        {
            NewPath="C:/TBD/SPS/SPS_S_"+ui->EbLibFileName->text()+"-1.dwg";
            FileName="SPS_S_"+ui->EbLibFileName->text()+"-1";
        }
        else
        {
            NewPath="C:/TBD/SPS/SPS_M_"+ui->EbLibFileName->text()+"-1.dwg";
            FileName="SPS_M_"+ui->EbLibFileName->text()+"-1";
        }
        QFile file(NewPath);
        if(!file.exists())
        {
            //复制符号文件到SPS文件夹
            if(FilePath!="")
            {
                for(int i=0;i<8;i++)
                {
                    QFile file(FilePath.mid(0,FilePath.lastIndexOf("-"))+"-"+QString::number(i+1)+".dwg");
                    if(file.exists())
                    {
                        if(ui->RbSingleTerm->isChecked())
                            NewPath="C:/TBD/SPS/SPS_S_"+ui->EbLibFileName->text()+"-"+QString::number(i+1)+".dwg";
                        else
                            NewPath="C:/TBD/SPS/SPS_M_"+ui->EbLibFileName->text()+"-"+QString::number(i+1)+".dwg";
                        QFile::copy(file.fileName(),NewPath);
                    }
                }
            }
        }

    }



    if(Mode==0)//新建
    {
        //insert数据库记录
        int MaxFunctionDefineClass_ID=(ParentNo+"00").toInt();
        QSqlQuery QueryID = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString tempQueryID = "SELECT FunctionDefineClass_ID FROM FunctionDefineClass WHERE Level = 4 AND ParentNo = '"+ParentNo+"'";
        QueryID.exec(tempQueryID);
        while(QueryID.next())
        {
            if(QueryID.value(0).toInt()>=MaxFunctionDefineClass_ID) MaxFunctionDefineClass_ID=QueryID.value(0).toInt()+1;
        }
        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString tempSQL = "INSERT INTO FunctionDefineClass (FunctionDefineClass_ID,ParentNo,Level,Desc,_Order,FunctionDefineName,FunctionDefineCode,DefaultSymbol,FuncType,TModel,TClassName)"
                          "VALUES (:FunctionDefineClass_ID,:ParentNo,:Level,:Desc,:_Order,:FunctionDefineName,:FunctionDefineCode,:DefaultSymbol,:FuncType,:TModel,:TClassName)";
        QueryVar.prepare(tempSQL);
        this->FunctionDefineClass_ID=QString::number(MaxFunctionDefineClass_ID);
        QueryVar.bindValue(":FunctionDefineClass_ID",QString::number(MaxFunctionDefineClass_ID));
        QueryVar.bindValue(":ParentNo",ParentNo);
        QueryVar.bindValue(":Level",4);
        QueryVar.bindValue(":Desc","");
        QSqlQuery Query_Order = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        tempSQL = QString("SELECT * FROM FunctionDefineClass WHERE Level = 4 AND ParentNo = '"+ParentNo+"' ORDER BY _Order DESC");
        Query_Order.exec(tempSQL);
        if(Query_Order.next()) QueryVar.bindValue(":_Order",Query_Order.value("_Order").toInt()+1);
        else  QueryVar.bindValue(":_Order",1);
        QueryVar.bindValue(":FunctionDefineName",ui->EdFuncName->text());
        //自动生成功能码
        int MaxCode=1;
        QSqlQuery QueryFunctionDefineCode = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr = "SELECT * FROM FunctionDefineClass WHERE Level = 4 AND ParentNo = '"+ParentNo+"'";
        QueryFunctionDefineCode.exec(SqlStr);
        while(QueryFunctionDefineCode.next())
        {
           QString FunctionDefineCode=QueryFunctionDefineCode.value("FunctionDefineCode").toString();
           if(FunctionDefineCode.mid(FunctionDefineCode.lastIndexOf(".")+1,FunctionDefineCode.count()-FunctionDefineCode.lastIndexOf(".")-1).toInt()>=MaxCode)
               MaxCode=FunctionDefineCode.mid(FunctionDefineCode.lastIndexOf(".")+1,FunctionDefineCode.count()-FunctionDefineCode.lastIndexOf(".")-1).toInt()+1;
        }
        SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ParentNo+"'";
        QueryFunctionDefineCode.exec(SqlStr);
        if(QueryFunctionDefineCode.next()) QueryVar.bindValue(":FunctionDefineCode",QueryFunctionDefineCode.value("FunctionDefineCode").toString()+"."+QString::number(MaxCode));
        else QueryVar.bindValue(":FunctionDefineCode","");

        if(ui->EbLibFileName->text()!="")
        {
            if(ui->RbSingleTerm->isChecked())
              QueryVar.bindValue(":DefaultSymbol","SPS_S_"+ui->EbLibFileName->text()+"-1");
            else
              QueryVar.bindValue(":DefaultSymbol","SPS_M_"+ui->EbLibFileName->text()+"-1");
        }
        else QueryVar.bindValue(":DefaultSymbol","");
        QueryVar.bindValue(":FuncType",ui->CbFuncType->currentText());
        QueryVar.bindValue(":TModel",QsciEdit->text());
        QueryVar.bindValue(":TClassName",ui->EbTModelClass->text());
        QueryVar.exec();
    }//if(Mode==0)//新建
    else if(Mode==1)//修改
    {
        QSqlQuery QueryUpdate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr="UPDATE FunctionDefineClass SET FunctionDefineName=:FunctionDefineName,FuncType=:FuncType,TModel=:TModel,TClassName=:TClassName WHERE FunctionDefineClass_ID = '"+FunctionDefineClass_ID+"'";
        QueryUpdate.prepare(SqlStr);
        QueryUpdate.bindValue(":FunctionDefineName",ui->EdFuncName->text());
        QueryUpdate.bindValue(":FuncType",ui->CbFuncType->currentText());
        QueryUpdate.bindValue(":TModel",QsciEdit->text());
        QueryUpdate.bindValue(":TClassName",ui->EbTModelClass->text());
        QueryUpdate.exec();
    }

    Canceled=false;    
    this->close();
}

void DialogNewFunc::SetUIEnabled(QString Level)
{
    if(Level!="4")
    {
        ui->RbSingleTerm->setEnabled(false);
        ui->RbMultiTerm->setEnabled(false);
        ui->EdFuncName->setEnabled(false);
        ui->EbLibFileName->setEnabled(false);
        ui->CbFuncType->setEnabled(false);
        ui->BtnDelFuncSymbol->setEnabled(false);
        ui->BtnFuncSymbolSet->setEnabled(false);
    }
}

void DialogNewFunc::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}

void DialogNewFunc::on_BtnFuncSymbolSet_clicked()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("选择文件"));
    fileDialog.setDirectory("C:/TBD/SPS");
    fileDialog.setNameFilter(tr("dwg(*.dwg)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    //检查端数
    if((GetDwgTermCount(fileNames.at(0),"CHECK")==1)&&ui->RbMultiTerm->isChecked())
    {
        QMessageBox::warning(nullptr, "提示", "选择文件为单端符号，当前功能定义为多端符号");
        return;
    }
    if((GetDwgTermCount(fileNames.at(0),"CHECK")>1)&&ui->RbSingleTerm->isChecked())
    {
        QMessageBox::warning(nullptr, "提示", "选择文件为多端符号，当前功能定义为单端符号");
        return;
    }
    FilePath=fileNames.at(0);
    QPixmap p=QPixmap(fileNames.at(0));
    QFileInfo file(fileNames.at(0));
    QString StampJpgName=file.fileName();
    StampJpgName.replace("dwg","jpg");
    UnitSymbolsView(FilePath,"C:/TBD/data/TempImage/"+StampJpgName,ui->LbSPSPic,true);
}

void DialogNewFunc::on_BtnDelFuncSymbol_clicked()
{
    QPixmap p=QPixmap("");
    ui->LbSPSPic->setPixmap(p.scaled(ui->LbSPSPic->width(),ui->LbSPSPic->height()));
    ui->LbSPSPic->setText("");
    FilePath="";
}

void DialogNewFunc::on_RbSingleTerm_clicked(bool checked)
{
    //检查端数
    if((GetDwgTermCount(FilePath,"CHECK")==1)&&ui->RbMultiTerm->isChecked())
    {
        QMessageBox::warning(nullptr, "提示", "选择文件为单端符号!");
        ui->RbSingleTerm->setChecked(true);
        return;
    }
    if((GetDwgTermCount(FilePath,"CHECK")>1)&&ui->RbSingleTerm->isChecked())
    {
        QMessageBox::warning(nullptr, "提示", "选择文件为多端符号!");
        ui->RbMultiTerm->setChecked(true);
        return;
    }
}
