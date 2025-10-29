#include "binaryboolcalcute.h"

BinaryBoolCalcute::BinaryBoolCalcute()
{

}
BinaryBoolCalcute::BinaryBoolCalcute(int t)
{
    SetDigit(t);
}

void BinaryBoolCalcute::SetDigit(int t)
{
    Result.clear();
    for(int i=0; i<t; i++)
        Result.append(false);
}

void BinaryBoolCalcute::AddOne()
{

}
