#include "dialogtermbatchmark.h"
#include "ui_dialogtermbatchmark.h"

DialogTermBatchMark::DialogTermBatchMark(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogTermBatchMark)
{
    ui->setupUi(this);
}

DialogTermBatchMark::~DialogTermBatchMark()
{
    delete ui;
}
