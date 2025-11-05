#ifndef TMODELHELPER_H
#define TMODELHELPER_H

#include <QString>
#include <QStringList>
#include <QMap>
#include <QTableWidget>
#include <QJsonDocument>
#include <QJsonArray>
#include <QJsonObject>

/**
 * @brief T语言模型辅助工具类
 * 提供端口变量生成、故障模式提取等功能
 * 用于dialogunitmanage和dialogUnitAttr复用代码
 */
class TModelHelper
{
public:
    /**
     * @brief 从端口表格生成端口变量定义的SMT语句
     * @param tableTerm 端口表格（列：子块代号、端号、描述、变量、测试代价、已标注、图片路径）
     * @param componentName 元件名称（用于替换%Name%占位符）
     * @return 生成的SMT端口变量定义语句
     */
    static QString generatePortVariablesFromTable(QTableWidget *tableTerm, const QString &componentName = "%Name%");
    
    /**
     * @brief 从T语言模型文本中提取故障模式列表
     * @param tmodelText T语言模型文本
     * @return 故障模式名称列表
     */
    static QStringList extractFaultModesFromTModel(const QString &tmodelText);
    
    /**
     * @brief 更新T语言模型文本中的端口变量定义部分
     * @param tmodelText 原始T语言模型文本
     * @param newPortVariables 新的端口变量定义
     * @return 更新后的T语言模型文本
     */
    static QString updatePortVariablesInTModel(const QString &tmodelText, const QString &newPortVariables);
    
    /**
     * @brief 解析RepairInfo字段为故障列表
     * @param repairInfoStr RepairInfo字段字符串（JSON格式数组）
     * @return 故障模式到其他信息的映射（若解析失败则返回空映射并清空数据）
     */
    static QMap<QString, QStringList> parseRepairInfo(const QString &repairInfoStr);
    
    /**
     * @brief 将故障列表序列化为RepairInfo字段
     * @param faultMap 故障模式映射（key=故障模式, value=[故障概率,解决方案,所需资源]）
     * @return RepairInfo字段字符串（JSON格式）
     */
    static QString serializeRepairInfo(const QMap<QString, QStringList> &faultMap);
    
    /**
     * @brief 加载RepairInfo到表格
     * @param tableRepairInfo 维修信息表格
     * @param repairInfoStr RepairInfo字段字符串
     */
    static void loadRepairInfoToTable(QTableWidget *tableRepairInfo, const QString &repairInfoStr);
    
    /**
     * @brief 从表格保存RepairInfo
     * @param tableRepairInfo 维修信息表格
     * @return RepairInfo字段字符串
     */
    static QString saveRepairInfoFromTable(QTableWidget *tableRepairInfo);
    
    /**
     * @brief 从T语言模型自动获取故障模式并更新表格
     * @param tableRepairInfo 维修信息表格
     * @param tmodelText T语言模型文本
     * @return 新增的故障模式数量
     */
    static int autoFillFaultModesFromTModel(QTableWidget *tableRepairInfo, const QString &tmodelText);
};

#endif // TMODELHELPER_H
