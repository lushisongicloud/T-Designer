#ifndef BINARYBOOLCALCUTE_H
#define BINARYBOOLCALCUTE_H

/*
 * 这个是二进制计数器，实现任意位数的二进制计算，返回对应bool值
 *
 *
 *
 *
 *
 */

#include <QVector>


class BinaryBoolCalcute
{
public:
    BinaryBoolCalcute();
    BinaryBoolCalcute(int t);

    void SetDigit(int t);   //设定位数

    void AddOne();      //加上1

    QVector<bool>   Result;


};

#endif // BINARYBOOLCALCUTE_H
