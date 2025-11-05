#ifndef TMODELCHECKSERVICE_H
#define TMODELCHECKSERVICE_H

#include <QList>
#include <QString>

#include "BO/function/tmodelvalidator.h"

class QWidget;

class TModelCheckService
{
public:
    /**
     * @brief 执行完整的T语言模型校验
     * @param parent 父窗口
     * @param modelText T语言模型原始文本
     * @param ports 端口信息列表
     * @param context 校验上下文（器件名称、常量表、故障模式概率表）
     * 
     * 执行的校验项包括：
     * 1. SMT语法校验（通过Z3）
     * 2. 器件名称占位符检查
     * 3. 常量定义检查
     * 4. 端口变量一致性检查
     * 5. 模型结构完整性检查
     * 6. 故障模式概率检查（warning）
     */
    static void run(QWidget *parent,
                    const QString &modelText,
                    const QList<PortInfo> &ports,
                    const TModelValidationContext &context = TModelValidationContext());
};

#endif // TMODELCHECKSERVICE_H
