#include "qxlabel.h"
#include <QMessageBox>

QXlabel::QXlabel(QWidget * parent):QLabel(parent)
{

}
void QXlabel::mousePressEvent(QMouseEvent * event)
{
     //QMessageBox::information(this,"DEBUD","CLICKED LABEL");
    emit Clicked(ID);
}
void QXlabel::mouseDoubleClickEvent(QMouseEvent * event)
{
   //QMessageBox::information(this,"DEBUD","DOUBLECLICKED LABEL");
    emit doubleClicked(ID);
}
