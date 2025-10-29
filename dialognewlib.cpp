#include "dialognewlib.h"
#include "ui_dialognewlib.h"

DialogNewLib::DialogNewLib(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogNewLib)
{
    ui->setupUi(this);
    Canceled=true;  
    //this->setGeometry(this->x(),this->y(),this->width(),this->height()-ui->EdPageName->height());
}

DialogNewLib::~DialogNewLib()
{
    delete ui;
}

//Mode=0:新建  Mode=1:复制  Mode=2:移动
void DialogNewLib::LoadMode(int Mode,int Level,QString DefaultFunctionDefineClass_ID,int TermCount)
{
    this->FunctionDefineClass_ID=DefaultFunctionDefineClass_ID;
    if((Mode==1)||(Mode==2))//复制 移动
    {
       ui->RbMultiTerm->setVisible(false);
       ui->RbSingleTerm->setVisible(false);
       ui->CbPattern->setVisible(false);
       ui->LbPattern->setVisible(false);
       ui->BtnOK->setGeometry(ui->BtnOK->x(),ui->BtnOK->y()-20,ui->BtnOK->width(),ui->BtnOK->height());
       ui->BtnCancel->setGeometry(ui->BtnCancel->x(),ui->BtnCancel->y()-20,ui->BtnCancel->width(),ui->BtnCancel->height());
       if(Mode==1)
       {
         if(TermCount>1) ui->RbMultiTerm->setChecked(true);
         else ui->RbSingleTerm->setChecked(true);
       }
    }
    if(Mode==2)//移动
    {
       ui->BtnOK->setGeometry(ui->BtnOK->x(),ui->BtnOK->y()-40,ui->BtnOK->width(),ui->BtnOK->height());
       ui->BtnCancel->setGeometry(ui->BtnCancel->x(),ui->BtnCancel->y()-40,ui->BtnCancel->width(),ui->BtnCancel->height());
       ui->LbFileName->setVisible(false);
       ui->EbLibFileName->setVisible(false);
    }
    ValidLevel=Level;
    this->Mode=Mode;
}

void DialogNewLib::on_BtnFuncSet_clicked()
{
    dlgFuncDefine.setModal(true);
    dlgFuncDefine.ValidLevel=ValidLevel;
    dlgFuncDefine.SetCurrentIndex(FunctionDefineClass_ID);
    dlgFuncDefine.exec();
    if(dlgFuncDefine.Canceled) return;
    ui->LbFuncDefine->setText(dlgFuncDefine.FunctionDefineName);
    FunctionDefineClass_ID=dlgFuncDefine.FunctionDefineClass_ID;
    SymbolType=dlgFuncDefine.FunctionType;
}

void DialogNewLib::on_BtnOK_clicked()
{
    if(ui->LbFuncDefine->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", " 功能定义不能为空");
        return;
    }
    if(ui->EbLibFileName->text()==""&&(Mode!=2))
    {
        QMessageBox::warning(nullptr, "提示", " 库文件名不能为空");
        return;
    }
    if((Mode==0)||(Mode==1))//新建 或复制
    {
        //查看库文件名是否存在
        QString Path;
        if(ui->RbSingleTerm->isChecked())
        {
            Path="C:/TBD/SYMB2LIB/ES2_S_"+ui->EbLibFileName->text()+"-"+ui->CbPattern->currentText()+".dwg";
            FileName="ES2_S_"+ui->EbLibFileName->text()+"-"+ui->CbPattern->currentText();
        }
        else
        {
            Path="C:/TBD/SYMB2LIB/ES2_M_"+ui->EbLibFileName->text()+"-"+ui->CbPattern->currentText()+".dwg";
            FileName="ES2_M_"+ui->EbLibFileName->text()+"-"+ui->CbPattern->currentText();
        }

        QFile file(Path);
        if(file.exists())
        {
            QMessageBox::warning(nullptr, "提示", " 库文件名已存在");
            return;
        }
    }

    Canceled=false;
    this->close();
}

void DialogNewLib::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}
