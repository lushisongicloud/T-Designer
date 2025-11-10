#include "dlgmessage.h"
#include "ui_dlgmessage.h"

dlgMessage::dlgMessage(QWidget *parent) :
    QGroupBox(parent),
    ui(new Ui::dlgMessage)
{
    ui->setupUi(this);
    this->setMinimumSize(400, 300);
}

dlgMessage::~dlgMessage()
{
    delete ui;
}

void dlgMessage::on_BtnExit_clicked()
{
    this->close();
}

void dlgMessage::SetResult(QString Str)
{
    ui->LbResult->setWordWrap(true);
    ui->LbResult->setText(Str);
}
