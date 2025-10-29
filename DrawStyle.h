#ifndef DRAWSTYLE_H
#define DRAWSTYLE_H

#include <QString>
#include <QColor>

#define AngToRad  3.14159265/180.0
//画图使用的一些结构体
struct stPoint  //对应CAD中IMxDrawPoint
{
    double x;
    double y;

};
extern int  QColorToInt(const QColor &color);
extern QColor IntToQColor(const int &intColor);



#endif // DRAWSTYLE_H
