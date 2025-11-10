#include "dialogattrdefset.h"
#include "ui_dialogattrdefset.h"

DialogAttrDefSet::DialogAttrDefSet(QWidget *parent,IMxDrawAttributeDefinition *AttrDef,IMxDrawAttribute *Attr,IMxDrawMText *Text) :
    QDialog(parent),mAttrDef(AttrDef),mAttr(Attr),mText(Text),
    ui(new Ui::DialogAttrDefSet)
{
    ui->setupUi(this);
    if(mAttrDef!=nullptr)
    {
        ui->EdTag->setText(mAttrDef->dynamicCall("Tag()").toString());
        if(mAttrDef->horizontalMode()==mcHorizontalAlignmentLeft) ui->CbAlignment->setCurrentIndex(0);
        else if(mAttrDef->horizontalMode()==mcHorizontalAlignmentCenter) ui->CbAlignment->setCurrentIndex(1);
        else if(mAttrDef->horizontalMode()==mcHorizontalAlignmentRight) ui->CbAlignment->setCurrentIndex(2);
        ui->EdHeight->setText(mAttrDef->dynamicCall("Height()").toString());
        ui->EdWidth->setText(mAttrDef->dynamicCall("WidthFactor()").toString());
        if(fabs(mAttrDef->dynamicCall("Rotation()").toDouble()-0)<0.1) ui->CbRotation->setCurrentIndex(0);
        else if(fabs(mAttrDef->dynamicCall("Rotation()").toDouble()-PI/2.0)<0.1) ui->CbRotation->setCurrentIndex(1);
        else if(fabs(mAttrDef->dynamicCall("Rotation()").toDouble()-PI)<0.1) ui->CbRotation->setCurrentIndex(2);
        else if(fabs(mAttrDef->dynamicCall("Rotation()").toDouble()-PI*3/2.0)<0.1) ui->CbRotation->setCurrentIndex(3);
        ui->EdTag->setEnabled(false);
        if(mAttrDef->dynamicCall("colorIndex()").toInt()==McColor::mcWhite) ui->CbColour->setCurrentIndex(0);
        else if(mAttrDef->dynamicCall("colorIndex()").toInt()==McColor::mcBlue) ui->CbColour->setCurrentIndex(1);
        else if(mAttrDef->dynamicCall("colorIndex()").toInt()==McColor::mcCyan) ui->CbColour->setCurrentIndex(2);
        else if(mAttrDef->dynamicCall("colorIndex()").toInt()==McColor::mcGreen) ui->CbColour->setCurrentIndex(3);
        else if(mAttrDef->dynamicCall("colorIndex()").toInt()==McColor::mcMagenta) ui->CbColour->setCurrentIndex(4);
        else if(mAttrDef->dynamicCall("colorIndex()").toInt()==McColor::mcRed) ui->CbColour->setCurrentIndex(5);
        else if(mAttrDef->dynamicCall("colorIndex()").toInt()==McColor::mcYellow) ui->CbColour->setCurrentIndex(6);
    }
    else if(mAttr!=nullptr)
    {
        ui->EdTag->setText(mAttr->dynamicCall("TextString()").toString());
        if(mAttr->horizontalMode()==mcHorizontalAlignmentLeft) ui->CbAlignment->setCurrentIndex(0);
        else if(mAttr->horizontalMode()==mcHorizontalAlignmentCenter) ui->CbAlignment->setCurrentIndex(1);
        else if(mAttr->horizontalMode()==mcHorizontalAlignmentRight) ui->CbAlignment->setCurrentIndex(2);
        ui->EdHeight->setText(mAttr->dynamicCall("Height()").toString());
        ui->EdWidth->setText(mAttr->dynamicCall("WidthFactor()").toString());
        if(fabs(mAttr->dynamicCall("Rotation()").toDouble()-0)<0.1) ui->CbRotation->setCurrentIndex(0);
        else if(fabs(mAttr->dynamicCall("Rotation()").toDouble()-PI/2.0)<0.1) ui->CbRotation->setCurrentIndex(1);
        else if(fabs(mAttr->dynamicCall("Rotation()").toDouble()-PI)<0.1) ui->CbRotation->setCurrentIndex(2);
        else if(fabs(mAttr->dynamicCall("Rotation()").toDouble()-PI*3/2.0)<0.1) ui->CbRotation->setCurrentIndex(3);
        if(mAttr->dynamicCall("colorIndex()").toInt()==McColor::mcWhite) ui->CbColour->setCurrentIndex(0);
        else if(mAttr->dynamicCall("colorIndex()").toInt()==McColor::mcBlue) ui->CbColour->setCurrentIndex(1);
        else if(mAttr->dynamicCall("colorIndex()").toInt()==McColor::mcCyan) ui->CbColour->setCurrentIndex(2);
        else if(mAttr->dynamicCall("colorIndex()").toInt()==McColor::mcGreen) ui->CbColour->setCurrentIndex(3);
        else if(mAttr->dynamicCall("colorIndex()").toInt()==McColor::mcMagenta) ui->CbColour->setCurrentIndex(4);
        else if(mAttr->dynamicCall("colorIndex()").toInt()==McColor::mcRed) ui->CbColour->setCurrentIndex(5);
        else if(mAttr->dynamicCall("colorIndex()").toInt()==McColor::mcYellow) ui->CbColour->setCurrentIndex(6);
    }
    else if(mText!=nullptr)
    {
        ui->EdTag->setText(mText->dynamicCall("Contents()").toString());
        if(mText->Attachment()==mcAttachmentPointTopLeft) ui->CbAlignment->setCurrentIndex(0);
        else if(mText->Attachment()==mcAttachmentPointTopCenter) ui->CbAlignment->setCurrentIndex(1);
        else if(mText->Attachment()==mcAttachmentPointTopRight) ui->CbAlignment->setCurrentIndex(2);
        ui->EdHeight->setText(mText->dynamicCall("TextHeight()").toString());
        ui->EdWidth->setText(mText->dynamicCall("Width()").toString());
        if(fabs(mText->dynamicCall("Rotation()").toDouble()-0)<0.1) ui->CbRotation->setCurrentIndex(0);
        else if(fabs(mText->dynamicCall("Rotation()").toDouble()-PI/2.0)<0.1) ui->CbRotation->setCurrentIndex(1);
        else if(fabs(mText->dynamicCall("Rotation()").toDouble()-PI)<0.1) ui->CbRotation->setCurrentIndex(2);
        else if(fabs(mText->dynamicCall("Rotation()").toDouble()-PI*3/2.0)<0.1) ui->CbRotation->setCurrentIndex(3);
        if(mText->dynamicCall("colorIndex()").toInt()==McColor::mcWhite) ui->CbColour->setCurrentIndex(0);
        else if(mText->dynamicCall("colorIndex()").toInt()==McColor::mcBlue) ui->CbColour->setCurrentIndex(1);
        else if(mText->dynamicCall("colorIndex()").toInt()==McColor::mcCyan) ui->CbColour->setCurrentIndex(2);
        else if(mText->dynamicCall("colorIndex()").toInt()==McColor::mcGreen) ui->CbColour->setCurrentIndex(3);
        else if(mText->dynamicCall("colorIndex()").toInt()==McColor::mcMagenta) ui->CbColour->setCurrentIndex(4);
        else if(mText->dynamicCall("colorIndex()").toInt()==McColor::mcRed) ui->CbColour->setCurrentIndex(5);
        else if(mText->dynamicCall("colorIndex()").toInt()==McColor::mcYellow) ui->CbColour->setCurrentIndex(6);
    }
    Canceled=true;
}

DialogAttrDefSet::~DialogAttrDefSet()
{
    delete ui;
}

void DialogAttrDefSet::on_BtnOk_clicked()
{
  if(!StrIsDouble(ui->EdHeight->text()))
  {
      QMessageBox::warning(nullptr, "提示", "请正确输入字高！");
      return;
  }
  if(!StrIsDouble(ui->EdWidth->text()))
  {
      QMessageBox::warning(nullptr, "提示", "请正确输入字宽！");
      return;
  }
  if(mAttrDef!=nullptr)
  {
      if(ui->CbAlignment->currentIndex()==0) mAttrDef->setHorizontalMode(mcHorizontalAlignmentLeft);
      else if(ui->CbAlignment->currentIndex()==1) mAttrDef->setHorizontalMode(mcHorizontalAlignmentCenter);
      else if(ui->CbAlignment->currentIndex()==2) mAttrDef->setHorizontalMode(mcHorizontalAlignmentRight);

      mAttrDef->dynamicCall("SetHeight(double)",ui->EdHeight->text().toDouble());
      mAttrDef->dynamicCall("SetWidthFactor(double)",ui->EdWidth->text().toDouble());
      mAttrDef->dynamicCall("SetRotation(double)",ui->CbRotation->currentIndex()*90*PI/180.0);
      if(ui->CbColour->currentIndex()==0) mAttrDef->dynamicCall("setColorIndex(int)",McColor::mcWhite);
      else if(ui->CbColour->currentIndex()==1) mAttrDef->dynamicCall("setColorIndex(int)",McColor::mcBlue);
      else if(ui->CbColour->currentIndex()==2) mAttrDef->dynamicCall("setColorIndex(int)",McColor::mcCyan);
      else if(ui->CbColour->currentIndex()==3) mAttrDef->dynamicCall("setColorIndex(int)",McColor::mcGreen);
      else if(ui->CbColour->currentIndex()==4) mAttrDef->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
      else if(ui->CbColour->currentIndex()==5) mAttrDef->dynamicCall("setColorIndex(int)",McColor::mcRed);
      else if(ui->CbColour->currentIndex()==6) mAttrDef->dynamicCall("setColorIndex(int)",McColor::mcYellow);
  }
  else if(mAttr!=nullptr)
  {
      if(ui->CbAlignment->currentIndex()==0) mAttr->setHorizontalMode(mcHorizontalAlignmentLeft);
      else if(ui->CbAlignment->currentIndex()==1) mAttr->setHorizontalMode(mcHorizontalAlignmentCenter);
      else if(ui->CbAlignment->currentIndex()==2) mAttr->setHorizontalMode(mcHorizontalAlignmentRight);

      mAttr->dynamicCall("SetHeight(double)",ui->EdHeight->text().toDouble());
      mAttr->dynamicCall("SetWidthFactor(double)",ui->EdWidth->text().toDouble());
      mAttr->dynamicCall("SetRotation(double)",ui->CbRotation->currentIndex()*90*PI/180.0);
      mAttr->dynamicCall("SetTextString(QString)",ui->EdTag->text());
      if(ui->CbColour->currentIndex()==0) mAttr->dynamicCall("setColorIndex(int)",McColor::mcWhite);
      else if(ui->CbColour->currentIndex()==1) mAttr->dynamicCall("setColorIndex(int)",McColor::mcBlue);
      else if(ui->CbColour->currentIndex()==2) mAttr->dynamicCall("setColorIndex(int)",McColor::mcCyan);
      else if(ui->CbColour->currentIndex()==3) mAttr->dynamicCall("setColorIndex(int)",McColor::mcGreen);
      else if(ui->CbColour->currentIndex()==4) mAttr->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
      else if(ui->CbColour->currentIndex()==5) mAttr->dynamicCall("setColorIndex(int)",McColor::mcRed);
      else if(ui->CbColour->currentIndex()==6) mAttr->dynamicCall("setColorIndex(int)",McColor::mcYellow);
  }
  else if(mText!=nullptr)
  {
      if(ui->CbAlignment->currentIndex()==0) mText->SetAttachment(mcAttachmentPointTopLeft);
      else if(ui->CbAlignment->currentIndex()==1) mText->SetAttachment(mcAttachmentPointTopCenter);
      else if(ui->CbAlignment->currentIndex()==2) mText->SetAttachment(mcAttachmentPointTopRight);
      mText->dynamicCall("SetTextHeight(double)",ui->EdHeight->text().toDouble());
      mText->dynamicCall("SetWidth(double)",ui->EdWidth->text().toDouble());
      mText->dynamicCall("SetRotation(double)",ui->CbRotation->currentIndex()*90*PI/180.0);
      mText->dynamicCall("SetContents(QString)",ui->EdTag->text());
      if(ui->CbColour->currentIndex()==0) mText->dynamicCall("setColorIndex(int)",McColor::mcWhite);
      else if(ui->CbColour->currentIndex()==1) mText->dynamicCall("setColorIndex(int)",McColor::mcBlue);
      else if(ui->CbColour->currentIndex()==2) mText->dynamicCall("setColorIndex(int)",McColor::mcCyan);
      else if(ui->CbColour->currentIndex()==3) mText->dynamicCall("setColorIndex(int)",McColor::mcGreen);
      else if(ui->CbColour->currentIndex()==4) mText->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
      else if(ui->CbColour->currentIndex()==5) mText->dynamicCall("setColorIndex(int)",McColor::mcRed);
      else if(ui->CbColour->currentIndex()==6) mText->dynamicCall("setColorIndex(int)",McColor::mcYellow);
  }

  Canceled=false;
  this->close();
}

void DialogAttrDefSet::on_BtnCancel_clicked()
{
  Canceled=true;
  this->close();
}
