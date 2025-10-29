#include "formcreatnewcomponent.h"
#include "ui_formcreatnewcomponent.h"

FormCreatNewComponent::FormCreatNewComponent(QWidget *parent) :
    QWidget(parent),
    ui(new Ui::FormCreatNewComponent)
{
    ui->setupUi(this);
}

FormCreatNewComponent::~FormCreatNewComponent()
{
    delete ui;
}
