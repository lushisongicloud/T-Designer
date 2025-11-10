#ifndef QXLABEL_H
#define QXLABEL_H

#include <QWidget>
#include <QLabel>
#include <QMouseEvent>
class QXlabel : public QLabel
{
    Q_OBJECT
public:
    QXlabel(QWidget * parent = 0);
    int ID;
    QString UsrData;
    QString PicPath,PicName;
private:
protected:
    virtual void mousePressEvent(QMouseEvent * event);
    virtual void mouseDoubleClickEvent(QMouseEvent * event);
signals:
    void Clicked(int);
    void doubleClicked(int);
};

#endif // QXLABEL_H
