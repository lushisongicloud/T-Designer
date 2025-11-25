#include "component.h"
#include<QDebug>
#include <QDomDocument>

component::component()
{

}

void component::setFailureMode(QString strFailureMode) {
    // 初始值设定
    double UnknownProbability = 0.0000001;
    double defaultKnownProbability = 0.00001;
    QString defaultFaultName = "未命名故障";
    QString defaultDescribe = "";
    QString commonText = "";

    strFailureMode.remove('\n');

    // 获取<common>标签的文本
    int commonStart = strFailureMode.indexOf("<common>");
    if(commonStart != -1){
        int commonEnd = strFailureMode.indexOf("</common>", commonStart);
        if(commonEnd != -1){
            commonText = strFailureMode.mid(commonStart + 8, commonEnd - commonStart - 8).trimmed();
        }
    }

    // 获取<unknownfault>标签的文本
    int unknownfaultStart = strFailureMode.indexOf("<unknownfault>");
    if (unknownfaultStart != -1) {
        int unknownfaultEnd = strFailureMode.indexOf("</unknownfault>", unknownfaultStart);
        if(unknownfaultEnd != -1){
            QString unknownFaultContent = strFailureMode.mid(unknownfaultStart + 14, unknownfaultEnd - unknownfaultStart - 14);
            int pStart = unknownFaultContent.indexOf("<p>");
            if(pStart != -1){
                int pEnd = unknownFaultContent.indexOf("</p>", pStart);
                if(pEnd != -1){
                    QString unknownProbabilityStr = unknownFaultContent.mid(pStart + 3, pEnd - pStart - 3).trimmed();
                    bool ok;
                    double d = unknownProbabilityStr.toDouble(&ok);
                    if(ok) UnknownProbability = d;
                }
            }
        }
    }
    FailureMode unknownfault(UnknownProbability);
    ListFailureMode.append(unknownfault);

    // 为每个<fault>创建一个FailureMode
    int faultStart = strFailureMode.indexOf("<fault>");
    while (faultStart != -1) {
        int faultEnd = strFailureMode.indexOf("</fault>", faultStart);
        // 如果不存在配对的"</fault>"，则跳出循环
        if (faultEnd == -1) {
            break;
        }
        if(faultEnd != -1){
            QString faultStr = strFailureMode.mid(faultStart + 7, faultEnd - faultStart - 7);
            // 默认值
            QString name = defaultFaultName;
            QString describe = defaultDescribe;
            double probability = defaultKnownProbability;

            // name
            int nameStart = faultStr.indexOf("<name>");
            if(nameStart != -1){
                int nameEnd = faultStr.indexOf("</name>", nameStart);
                if(nameEnd != -1){
                    name = faultStr.mid(nameStart + 6, nameEnd - nameStart - 6).trimmed();
                }
            }

            // describe
            int describeStart = faultStr.indexOf("<describe>");
            if(describeStart != -1){
                int describeEnd = faultStr.indexOf("</describe>", describeStart);
                if(describeEnd != -1){
                    describe = faultStr.mid(describeStart + 10, describeEnd - describeStart - 10).trimmed();
                    describe = commonText + describe;
                }
            }

            // probability
            int pStart = faultStr.indexOf("<p>");
            if(pStart != -1){
                int pEnd = faultStr.indexOf("</p>", pStart);
                if(pEnd != -1){
                    QString probabilityStr = faultStr.mid(pStart + 3, pEnd - pStart - 3).trimmed();
                    probability = probabilityStr.toDouble();
                }
            }

            // 创建FailureMode并添加到ListFailureMode
            FailureMode fault(name, describe, probability);
            ListFailureMode.append(fault);

            // 寻找下一个<fault>
            faultStart = strFailureMode.indexOf("<fault>", faultEnd);
        }
    }
}

void component::setFailureProbability(QList<FailureMode> ListFailureMode) {
    double probabilityProduct = 1.0;
    for(const FailureMode& mode : ListFailureMode) {
        probabilityProduct *= (1-mode.getProbability());
//        qDebug()<<"mode.getProbability()"<<mode.getProbability();
//        qDebug()<<"probabilityProduct"<<probabilityProduct;
    }
    failureProbability =1.0 - probabilityProduct;
}


