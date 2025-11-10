#include "dialogaddterminal.h"
#include "ui_dialogaddterminal.h"

DialogAddTerminal::DialogAddTerminal(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogAddTerminal)
{
    ui->setupUi(this);
    Canceled=true;
    /*
    //自动生成默认的端子排代号
    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    int Index=100;
    while(1)
    {
        QString SqlStr = "SELECT * FROM TerminalStrip WHERE DT = 'T"+QString::number(Index)+"'";
        QueryTerminalStrip.exec(SqlStr);
        if(QueryTerminalStrip.next())
        {
            Index++;
        }
        else break;
    }

    ui->EdTerminalTag->setText("T"+QString::number(Index));*/

    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM TerminalStrip";
    QueryTerminalStrip.exec(SqlStr);
    while(QueryTerminalStrip.next())
    {
        ui->CbTerminalStripTag->addItem(QueryTerminalStrip.value("DT").toString());
    }
}

DialogAddTerminal::~DialogAddTerminal()
{
    delete ui;
}

void DialogAddTerminal::on_BtnTerminalStripSet_clicked()
{/*
    QDialog *dialogTerminalStrip =new QDialog();
    dialogTerminalStrip->setWindowTitle("已有端子排");

    dialogTerminalStrip->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutdlg = new QFormLayout(dialogTerminalStrip);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogTerminalStrip);
    pushbuttonOK->setText("确认");

    QListWidget *m_ListWidget = new QListWidget(dialogTerminalStrip);


    layout->addWidget(m_ListWidget);
    layout->addWidget(pushbuttonOK);
    formlayoutdlg->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogTerminalStrip,SLOT(accept()));


    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM TerminalStrip";
    QueryTerminalStrip.exec(SqlStr);
    while(QueryTerminalStrip.next())
    {
        m_ListWidget->addItem(QueryTerminalStrip.value("DT").toString());
    }
    if(dialogTerminalStrip->exec()==QDialog::Accepted)
    {
        //载入已选择的端子排
        ui->EdTerminalTag->setText(m_ListWidget->item(m_ListWidget->currentRow())->text());
    }
    delete dialogTerminalStrip;*/
}

void DialogAddTerminal::on_BtnOK_clicked()
{
    Canceled=false;
    QString StrDesignation=ui->CbDesignation->currentText();
    StrDesignation.remove("√").remove("*");
    if(StrIsNumber(StrDesignation)) Designation=StrDesignation.toInt();
    else
    {
        QMessageBox::warning(nullptr, "提示", " 端子序号必须为数字！");
        return;
    }
    DT=ui->CbTerminalStripTag->currentText();
    this->close();
}

void DialogAddTerminal::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}

void DialogAddTerminal::on_CbDesignation_currentTextChanged(const QString &arg1)
{

}

void DialogAddTerminal::on_EdTerminalTag_textChanged(const QString &arg1)
{

}

void DialogAddTerminal::on_CbTerminalStripTag_currentTextChanged(const QString &arg1)
{
    QString SqlStr = "SELECT * FROM TerminalStrip WHERE DT = '"+arg1+"'";
    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QueryTerminalStrip.exec(SqlStr);
    if(QueryTerminalStrip.next())
    {
        //序号自动加1
        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryTerminalStrip.value("TerminalStrip_ID").toString()+"'";
        QueryTerminal.exec(SqlStr);
        //int MaxDesignation=1;
        ui->CbDesignation->clear();
        while(QueryTerminal.next())
        {
           if(StrIsNumber(QueryTerminal.value("Designation").toString()))
           {
               QString ItemStr=QueryTerminal.value("ShortJumper").toString()+QueryTerminal.value("Designation").toString();
               QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
               QueryTerminalInstance.exec(SqlStr);
               if(QueryTerminalInstance.next()) ItemStr="√"+ItemStr;
               ui->CbDesignation->addItem(ItemStr);
           }
        }

        ui->LbProTag->setText(GetProjectStructureStrByProjectStructureID(QueryTerminalStrip.value("ProjectStructure_ID").toInt()));
    }
}
