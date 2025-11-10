#include "dialog_wait.h"
#include "ui_dialog_wait.h"
#include <QTime>
#include <QMovie>

Dialog_wait::Dialog_wait(QWidget *parent) :
    QDialog(parent,Qt::FramelessWindowHint),
    ui(new Ui::Dialog_wait)
{
    ui->setupUi(this);
    //QMovie* movie = new QMovie(":/new/prefix1/Diagnosis_Image/loading.gif");
    QMovie* movie = new QMovie(":/new/prefix1/Diagnosis_Image/loading_0.gif");
    //movie->setScaledSize(ui->label->size());

    ui->label->setScaledContents(true);
    ui->label->setMovie(movie);
    movie->start();
    ui->label->show();
}

Dialog_wait::~Dialog_wait()
{
    delete ui;
}

void Dialog_wait::CloseWindow()
{
    this->hide();
}



