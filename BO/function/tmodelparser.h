#ifndef TMODELPARSER_H
#define TMODELPARSER_H

#include <QString>
#include <QStringList>
#include <QMap>
#include <QDebug>

/**
 * @brief T语言模型解析器
 * 
 * 解析T语言模型文本，识别特殊注释行标记的各个部分：
 * - ;;端口变量定义
 * - ;;内部变量定义  
 * - ;;正常模式
 * - ;;故障模式
 * - ;;公共开始
 * - ;;公共结束
 * - ;;"故障模式名"
 */
class TModelParser
{
public:
    struct FailureMode {
        QString name;           // 故障模式名称
        QString description;    // 故障模式约束描述
        QString commonPart;     // 公共约束部分（可能来自多个公共块）
    };

    TModelParser();
    
    /**
     * @brief 解析T语言模型文本
     * @param tmodelText T语言模型原始文本
     * @return 是否解析成功
     */
    bool parse(const QString &tmodelText);
    
    /**
     * @brief 获取端口变量定义部分
     */
    QString getPortVariables() const { return m_portVariables; }
    
    /**
     * @brief 获取内部变量定义部分
     */
    QString getInternalVariables() const { return m_internalVariables; }
    
    /**
     * @brief 获取正常模式约束部分
     */
    QString getNormalMode() const { return m_normalMode; }
    
    /**
     * @brief 获取故障模式列表
     */
    QList<FailureMode> getFailureModes() const { return m_failureModes; }
    
    /**
     * @brief 编译展开后的完整描述（替换占位符、展开公共约束）
     * @param componentName 器件实例名（替换%Name%）
     * @param constants 常量映射（常量名->值）
     * @param portVars 输出端口变量定义（展开后）
     * @param internalVars 输出内部变量定义（展开后）
     * @param normalMode 输出正常模式约束（展开后）
     * @param failureModes 输出故障模式列表（展开后，包含公共约束）
     * @return 是否编译成功
     */
    bool compile(const QString &componentName,
                 const QMap<QString, QString> &constants,
                 QString &portVars,
                 QString &internalVars,
                 QString &normalMode,
                 QList<FailureMode> &failureModes) const;
    
    /**
     * @brief 从文本中提取常量占位符
     * @param text 要分析的文本
     * @return 常量名列表（不包含%%）
     */
    static QStringList extractConstants(const QString &text);
    
    /**
     * @brief 替换文本中的占位符
     * @param text 原始文本
     * @param componentName 器件名（替换%Name%）
     * @param constants 常量映射
     * @return 替换后的文本
     */
    static QString replacePlaceholders(const QString &text,
                                      const QString &componentName,
                                      const QMap<QString, QString> &constants);

private:
    QString m_portVariables;        // 端口变量定义
    QString m_internalVariables;    // 内部变量定义
    QString m_normalMode;           // 正常模式约束
    QList<FailureMode> m_failureModes;  // 故障模式列表
    
    /**
     * @brief 判断是否是特殊标记行
     */
    enum SectionType {
        SECTION_NONE,
        SECTION_PORT_VARIABLES,      // ;;端口变量定义
        SECTION_INTERNAL_VARIABLES,  // ;;内部变量定义
        SECTION_NORMAL_MODE,         // ;;正常模式
        SECTION_FAILURE_MODE,        // ;;故障模式
        SECTION_COMMON_BEGIN,        // ;;公共开始
        SECTION_COMMON_END,          // ;;公共结束
        SECTION_FAILURE_MODE_NAME    // ;;"具体故障模式名"
    };
    
    SectionType detectSectionType(const QString &line, QString &faultName) const;
};

#endif // TMODELPARSER_H
