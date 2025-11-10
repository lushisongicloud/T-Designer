#ifndef SYSTEMSTRUCTURESERVICE_H
#define SYSTEMSTRUCTURESERVICE_H

#include <QList>
#include <QSet>
#include <QString>
#include <QStringList>

struct SystemCropResult
{
    bool isConsistent = false;
    QString croppedSystemDescription;
    QStringList boundaryComponents;
    QStringList deviceLines;
    QStringList connectionLines;
    QList<QStringList> connectionPortLists;
    QSet<QString> devicesInDefinition;
    QSet<QString> componentsInConnection;
};

class SystemStructureService
{
public:
    /**
     * @brief 分析系统描述与功能链路，返回裁剪结果与边界信息。
     * @param systemDescription 原始系统 DEF/CONNECT 描述
     * @param linkText 功能链路（逗号分隔的器件/端口集合，可为空）
     */
    static SystemCropResult analyze(const QString &systemDescription,
                                    const QString &linkText);

    /**
     * @brief 获取裁剪后的系统描述，若不自洽则返回原描述。
     * @param isConsistent 可选输出，返回系统描述是否自洽
     */
    static QString cropSystemDescription(const QString &systemDescription,
                                         const QString &linkText,
                                         bool *isConsistent = nullptr);

    /**
     * @brief 获取边界器件列表，若不自洽则返回空列表。
     * @param isConsistent 可选输出，返回系统描述是否自洽
     */
    static QStringList boundaryComponents(const QString &systemDescription,
                                          const QString &linkText,
                                          bool *isConsistent = nullptr);
};

#endif // SYSTEMSTRUCTURESERVICE_H
