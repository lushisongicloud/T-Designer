#include "drawstyle.h"
int QColorToInt(const QColor &color)
{
    //将Color 从QColor 转换成 int，注意转成ARBG形式，这是CAD里面用的顺序

    return   (int)(((unsigned int)color.alpha()<< 24) |(((unsigned int)color.red()<< 16) | (unsigned short)(((unsigned short)color.green()<< 8) | color.blue())));
}
QColor IntToQColor(const int &intColor)
{
    //将Color 从int 转换成 QColor
    int blue = intColor & 255;
    int green = intColor >> 8 & 255;
    int red = intColor >> 16 & 255;
    int alpha = intColor >> 24 & 255;
    return QColor(red, green, blue,alpha);
}
