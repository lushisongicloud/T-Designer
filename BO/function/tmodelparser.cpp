#include "tmodelparser.h"
#include <QRegularExpression>
#include <QDebug>

TModelParser::TModelParser()
{
}

bool TModelParser::parse(const QString &tmodelText)
{
    // 清空之前的解析结果
    m_portVariables.clear();
    m_internalVariables.clear();
    m_normalMode.clear();
    m_failureModes.clear();
    
    QStringList lines = tmodelText.split('\n');
    SectionType currentSection = SECTION_NONE;
    QString currentContent;
    QString currentFaultName;
    QString currentCommonBlock;  // 当前公共块内容
    bool inCommonBlock = false;
    bool inFaultModeSection = false;  // 是否在故障模式区域
    
    for (const QString &line : lines) {
        QString trimmedLine = line.trimmed();
        
        // 检测是否是特殊标记行
        QString detectedFaultName;
        SectionType newSection = detectSectionType(trimmedLine, detectedFaultName);
        
        if (newSection != SECTION_NONE) {
            // 保存之前的内容
            if (currentSection == SECTION_PORT_VARIABLES) {
                m_portVariables = currentContent.trimmed();
                currentContent.clear();
            } else if (currentSection == SECTION_INTERNAL_VARIABLES) {
                m_internalVariables = currentContent.trimmed();
                currentContent.clear();
            } else if (currentSection == SECTION_NORMAL_MODE) {
                m_normalMode = currentContent.trimmed();
                currentContent.clear();
            } else if (currentSection == SECTION_FAILURE_MODE_NAME) {
                // 保存故障模式（包含当前公共块）
                FailureMode fm;
                fm.name = currentFaultName;
                fm.description = currentContent.trimmed();
                fm.commonPart = currentCommonBlock;  // 使用当前激活的公共块
                m_failureModes.append(fm);
                
                // 调试信息
                qDebug() << "保存故障模式:" << currentFaultName;
                qDebug() << "  commonPart长度:" << currentCommonBlock.length();
                qDebug() << "  description长度:" << currentContent.length();
                qDebug() << "  description内容:" << currentContent.left(100);
                
                currentContent.clear();  // 清空当前内容，避免累积到下一个故障模式
            }
            
            // 处理新标记
            if (newSection == SECTION_PORT_VARIABLES ||
                newSection == SECTION_INTERNAL_VARIABLES ||
                newSection == SECTION_NORMAL_MODE) {
                // 退出故障模式区域
                inFaultModeSection = false;
                inCommonBlock = false;
                currentCommonBlock.clear();
            } else if (newSection == SECTION_FAILURE_MODE) {
                // 进入故障模式区域
                inFaultModeSection = true;
                inCommonBlock = false;
                currentCommonBlock.clear();
            } else if (newSection == SECTION_COMMON_BEGIN) {
                // 开始新的公共块
                inCommonBlock = true;
                currentCommonBlock.clear();
            } else if (newSection == SECTION_COMMON_END) {
                // 结束公共块，公共块内容已收集在currentCommonBlock中
                inCommonBlock = false;
            } else if (newSection == SECTION_FAILURE_MODE_NAME) {
                // 遇到故障模式名，退出公共块模式
                inCommonBlock = false;
                currentFaultName = detectedFaultName;
            }
            
            currentSection = newSection;
            continue;
        }
        
        // 非标记行，追加到当前内容
        if (inCommonBlock) {
            // 在公共块内，累积公共内容
            currentCommonBlock += line + "\n";
        } else if (currentSection == SECTION_FAILURE_MODE_NAME) {
            // 在故障模式内，累积故障特有内容
            currentContent += line + "\n";
        } else {
            // 其他部分的内容
            currentContent += line + "\n";
        }
    }
    
    // 处理最后一个section
    if (currentSection == SECTION_PORT_VARIABLES) {
        m_portVariables = currentContent.trimmed();
    } else if (currentSection == SECTION_INTERNAL_VARIABLES) {
        m_internalVariables = currentContent.trimmed();
    } else if (currentSection == SECTION_NORMAL_MODE) {
        m_normalMode = currentContent.trimmed();
    } else if (currentSection == SECTION_FAILURE_MODE_NAME) {
        FailureMode fm;
        fm.name = currentFaultName;
        fm.description = currentContent.trimmed();
        fm.commonPart = currentCommonBlock;
        m_failureModes.append(fm);
    }
    
    return true;
}

TModelParser::SectionType TModelParser::detectSectionType(const QString &line, QString &faultName) const
{
    QString trimmed = line.trimmed();
    
    // 必须以两个分号开始
    if (!trimmed.startsWith(";;")) {
        return SECTION_NONE;
    }
    
    // 移除前导;;后的内容
    QString content = trimmed.mid(2).trimmed();
    
    if (content == "端口变量定义") {
        return SECTION_PORT_VARIABLES;
    } else if (content == "内部变量定义") {
        return SECTION_INTERNAL_VARIABLES;
    } else if (content == "正常模式") {
        return SECTION_NORMAL_MODE;
    } else if (content == "故障模式") {
        return SECTION_FAILURE_MODE;
    } else if (content == "公共开始") {
        return SECTION_COMMON_BEGIN;
    } else if (content == "公共结束") {
        return SECTION_COMMON_END;
    } else {
        // 所有其他以;;开头但不是固定关键字的行，都视为故障模式名
        // 例如：;;故障模式名a、;;broken、;;电阻开路、;;断路等
        // 完整的内容就是故障模式名称
        if (!content.isEmpty()) {
            faultName = content;
            return SECTION_FAILURE_MODE_NAME;
        }
    }
    
    return SECTION_NONE;
}

bool TModelParser::compile(const QString &componentName,
                           const QMap<QString, QString> &constants,
                           QString &portVars,
                           QString &internalVars,
                           QString &normalMode,
                           QList<FailureMode> &failureModes) const
{
    // 替换占位符
    portVars = replacePlaceholders(m_portVariables, componentName, constants);
    internalVars = replacePlaceholders(m_internalVariables, componentName, constants);
    normalMode = replacePlaceholders(m_normalMode, componentName, constants);
    
    // 展开故障模式（包含公共约束）
    failureModes.clear();
    for (const FailureMode &fm : m_failureModes) {
        FailureMode compiledFm;
        compiledFm.name = fm.name;
        
        // 先展开公共部分，再展开故障特有部分
        QString expandedCommon = replacePlaceholders(fm.commonPart, componentName, constants);
        QString expandedDesc = replacePlaceholders(fm.description, componentName, constants);
        
        // 合并公共部分和特有部分
        if (!expandedCommon.isEmpty()) {
            compiledFm.description = expandedCommon;
            if (!expandedDesc.isEmpty()) {
                compiledFm.description += "\n" + expandedDesc;
            }
        } else {
            compiledFm.description = expandedDesc;
        }
        
        failureModes.append(compiledFm);
    }
    
    return true;
}

QStringList TModelParser::extractConstants(const QString &text)
{
    QStringList constants;
    QRegularExpression re("%([^%]+)%");
    QRegularExpressionMatchIterator it = re.globalMatch(text);
    
    while (it.hasNext()) {
        QRegularExpressionMatch match = it.next();
        QString constantName = match.captured(1);
        
        // 排除特殊占位符 %Name%
        if (constantName != "Name" && !constants.contains(constantName)) {
            constants.append(constantName);
        }
    }
    
    return constants;
}

QString TModelParser::replacePlaceholders(const QString &text,
                                         const QString &componentName,
                                         const QMap<QString, QString> &constants)
{
    QString result = text;
    
    // 替换 %Name%
    result.replace("%Name%", componentName);
    
    // 替换常量
    for (auto it = constants.begin(); it != constants.end(); ++it) {
        QString placeholder = "%" + it.key() + "%";
        result.replace(placeholder, it.value());
    }
    
    return result;
}
