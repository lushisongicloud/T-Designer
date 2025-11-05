#ifndef TMODELVALIDATOR_H
#define TMODELVALIDATOR_H

#include <QList>
#include <QMap>
#include <QSet>
#include <QString>
#include <QStringList>
#include <QVector>

struct PortInfo
{
    QString connNum;
    QString symbolId;
    QString symb2TermInfoId;
    QString description;
    QString functionBlock;
    QString portType;
    QStringList variableNames;
};

struct PortVariableBinding
{
    PortInfo port;
    QSet<QString> declaredDirections;
    QSet<QString> referencedDirections;
    QSet<QString> tokens;
    QSet<QString> expectedDirections;
    QSet<QString> alternativeDirections;
    QString alternativeLabel;
    QStringList expectedDisplayOrder;
};

/**
 * @brief T语言模型校验的上下文信息
 * 包含执行校验所需的所有数据
 */
struct TModelValidationContext
{
    QString componentName;                    // 器件名称，用于检查是否使用%Name%
    QMap<QString, QString> constants;         // 常量表：常量名 -> 值
    QMap<QString, QString> faultModeProbabilities; // 故障模式概率表：故障模式名 -> 概率
};

struct TModelValidationResult
{
    QVector<PortVariableBinding> bindings;
    QStringList missingDeclarations;
    QStringList undefinedVariables;
    QStringList unusedPorts;
    QStringList formatErrors;
    QStringList hints;
    QStringList warnings;  // 警告信息（如故障模式概率未定义）

    bool isValid() const
    {
        return missingDeclarations.isEmpty()
                && undefinedVariables.isEmpty()
                && formatErrors.isEmpty();
    }
};

class TModelValidator
{
public:
    /**
     * @brief 完整的T语言模型校验
     * @param tmodelText T语言模型原始文本
     * @param ports 端口信息列表
     * @param context 校验上下文（器件名称、常量表、故障模式概率表）
     * @return 校验结果
     * 
     * 执行6项校验：
     * 1. 器件名称检查：是否使用%Name%占位符
     * 2. 常量检查：所有常量是否在常量表中有定义
     * 3. 端口变量一致性：端口变量定义是否与端口配置一致
     * 4. 模型结构完整性：是否包含必需的部分（端口变量定义、正常模式等）
     * 5. 故障模式概率检查：故障模式的概率是否在维修信息中定义（warning）
     * 6. SMT语法检查：由外部SmtSyntaxChecker完成
     */
    TModelValidationResult validate(const QString &tmodelText,
                                    const QList<PortInfo> &ports,
                                    const TModelValidationContext &context = TModelValidationContext()) const;
};

#endif // TMODELVALIDATOR_H
