#ifndef TMODELCHECKSERVICE_H
#define TMODELCHECKSERVICE_H

#include <QList>
#include <QString>

#include "BO/function/tmodelvalidator.h"

class QWidget;

class TModelCheckService
{
public:
    static void run(QWidget *parent,
                    const QString &modelText,
                    const QList<PortInfo> &ports);
};

#endif // TMODELCHECKSERVICE_H
