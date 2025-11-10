#include "dialogvariabledefine.h"
#include "ui_dialogvariabledefine.h"
#include <QMessageBox>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

DialogVariableDefine::DialogVariableDefine(QWidget *parent,myQSqlDatabase *TMATE_Database,DataBase::Str_Signal signal,bool isCreatSignal) :
    QDialog(parent),ui(new Ui::DialogVariableDefine),m_Database(TMATE_Database),m_signal(signal),m_isCreatSignal(isCreatSignal)
{
    ui->setupUi(this);
    this->setWindowFlags(Qt::Dialog| Qt::FramelessWindowHint);//隐藏窗口边框
    this->setAttribute(Qt::WA_TranslucentBackground);//背景透明
    setWindowTitle(tr("Add New Account"));

    if(m_signal.Name==""){
        ui->btn_OK->setEnabled(false);
        ui->label_warning->setText("用户名不得为空");
    }

    ui->lineEdit_name->setText(m_signal.Name);
    ui->comboBox_SignalType->setCurrentText(m_signal.SignalType);
    ui->comboBox_VariableType->setCurrentText(m_signal.DataType);
    ui->comboBox_unit->setCurrentText(m_signal.Unit);
    ui->lineEdit_detail->setText(m_signal.Detail);
    ui->lineEdit_note->setText(m_signal.Note);
    ui->comboBox_signalpos->setCurrentText(m_signal.SignalPos);
    ui->comboBox_multipos->addItems(m_signal.MultiPos);
}

DialogVariableDefine::~DialogVariableDefine()
{
    delete ui;
}

void DialogVariableDefine::on_btn_OK_clicked()
{
    QString OraginName = m_signal.Name;

    m_signal.Name = ui->lineEdit_name->text();
    m_signal.SignalType = ui->comboBox_SignalType->currentText();
    m_signal.DataType = ui->comboBox_VariableType->currentText();
    m_signal.Unit = ui->comboBox_unit->currentText();
    m_signal.Detail= ui->lineEdit_detail->text();
    m_signal.Note = ui->lineEdit_note->text();
    m_signal.SignalPos = ui->comboBox_signalpos->currentText();
    m_signal.MultiPos.clear();
    for(int i=0;i<ui->comboBox_multipos->count();i++)
    {
        if(ui->comboBox_multipos->itemText(i)=="NULL") continue;
        m_signal.MultiPos.push_back(ui->comboBox_multipos->itemText(i));
    }
    qDebug()<<m_signal.MultiPos;
    if(m_signal.Name=="")
    {
        QMessageBox::warning(nullptr, "提示", "请将信息填写完整");
        return;
    }

    if(m_Database->IsSignalExist(m_signal.Name)){
        //若存在该名称且此时为新建变量;或当前为修改变量但是修改后的变量名称存在则不可创建
        if(m_isCreatSignal||m_signal.Name!=OraginName){
            QMessageBox::warning(nullptr, "提示", "信号名称已存在");
            return;
        }
    }

    this->accept();
}

void DialogVariableDefine::on_lineEdit_name_textChanged(const QString &arg1)
{
    if(arg1==""){
        ui->btn_OK->setEnabled(false);
        ui->label_warning->setText("用户名不得为空");
    }
    else
    {
        ui->label_warning->setText("");
        ui->btn_OK->setEnabled(true);
    }
}

void DialogVariableDefine::on_comboBox_SignalType_currentIndexChanged(const QString &arg1)
{//设置故障信号和报警信号只能为布尔值
    if(arg1=="故障信号"||arg1=="报警信号"){
        ui->comboBox_VariableType->setCurrentText("BOOL");
        ui->comboBox_unit->setCurrentText("NULL");
        ui->comboBox_VariableType->setEnabled(false);
        ui->comboBox_unit->setEnabled(false);
    }
    else{
        ui->comboBox_VariableType->setEnabled(true);
        ui->comboBox_unit->setEnabled(true);
    }
}

void DialogVariableDefine::on_btn_AddNewMultiPos_clicked()
{
   QDialog *dialogNewMultiPos =new QDialog();
   dialogNewMultiPos->setWindowTitle("添加模糊组故障点");
   dialogNewMultiPos->setMinimumSize(QSize(1000,200));
   QFormLayout *formlayoutNewMultiPos = new QFormLayout(dialogNewMultiPos);

   QLineEdit *lineeditNewMultiPos = new QLineEdit(dialogNewMultiPos);
   lineeditNewMultiPos->setText("");
   formlayoutNewMultiPos->addRow(lineeditNewMultiPos);

   QHBoxLayout *layout = new QHBoxLayout(nullptr);
   QPushButton *pushbuttonOK= new QPushButton(dialogNewMultiPos);
   pushbuttonOK->setText("确认");
   QPushButton *pushbuttonCancel= new QPushButton(dialogNewMultiPos);
   pushbuttonCancel->setText("取消");
   layout->addWidget(pushbuttonOK);
   layout->addWidget(pushbuttonCancel);
   formlayoutNewMultiPos->addRow(layout);

   QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewMultiPos,SLOT(accept()));
   QObject::connect(pushbuttonCancel,SIGNAL(clicked()),dialogNewMultiPos,SLOT(close()));

   if(dialogNewMultiPos->exec()==QDialog::Accepted)
   {
     ui->comboBox_multipos->addItem(lineeditNewMultiPos->text());
     ui->comboBox_multipos->setCurrentText(lineeditNewMultiPos->text());
   }

   delete layout;
   delete dialogNewMultiPos;
}

void DialogVariableDefine::on_btn_DelMultiPos_clicked()
{
    ui->comboBox_multipos->removeItem(ui->comboBox_multipos->currentIndex());
}

void DialogVariableDefine::on_btn_ModMultiPos_clicked()
{
    QDialog *dialogNewMultiPos =new QDialog();
    dialogNewMultiPos->setWindowTitle("修改模糊组故障点");
    dialogNewMultiPos->setMinimumSize(QSize(1000,200));
    QFormLayout *formlayoutNewMultiPos = new QFormLayout(dialogNewMultiPos);

    QLineEdit *lineeditNewMultiPos = new QLineEdit(dialogNewMultiPos);
    lineeditNewMultiPos->setText(ui->comboBox_multipos->currentText());
    formlayoutNewMultiPos->addRow(lineeditNewMultiPos);

    QHBoxLayout *layout = new QHBoxLayout(nullptr);
    QPushButton *pushbuttonOK= new QPushButton(dialogNewMultiPos);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel= new QPushButton(dialogNewMultiPos);
    pushbuttonCancel->setText("取消");
    layout->addWidget(pushbuttonOK);
    layout->addWidget(pushbuttonCancel);
    formlayoutNewMultiPos->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewMultiPos,SLOT(accept()));
    QObject::connect(pushbuttonCancel,SIGNAL(clicked()),dialogNewMultiPos,SLOT(close()));

    if(dialogNewMultiPos->exec()==QDialog::Accepted)
    {
      ui->comboBox_multipos->setItemText(ui->comboBox_multipos->currentIndex(),lineeditNewMultiPos->text());
    }

    delete layout;
    delete dialogNewMultiPos;
}
