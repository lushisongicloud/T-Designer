#include "dlgtestprio.h"
#include "ui_dlgtestprio.h"

DlgTestPrio::DlgTestPrio(QWidget *parent) :
    QGroupBox(parent),
    ui(new Ui::DlgTestPrio)
{
    ui->setupUi(this);
}

DlgTestPrio::~DlgTestPrio()
{
    delete ui;
}

void DlgTestPrio::on_BtnExit_clicked()
{
    this->close();
}
