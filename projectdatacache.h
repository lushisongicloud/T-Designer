#ifndef PROJECTDATACACHE_H
#define PROJECTDATACACHE_H

#include <QString>
#include <QHash>
#include <QVector>
#include <QPair>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QDebug>

/**
 * @brief ProjectDataCache 提供项目数据的内存缓存，避免重复数据库查询
 * 
 * 这个类在项目加载时一次性读取常用数据到内存中，
 * 后续通过 O(1) 的 Hash 查找替代多次数据库查询。
 * 
 * 使用场景：
 * - 替代 GetUnitTermimalGaocengAndPos() 中的 6 次查询
 * - 替代 LoadModelLineDT 中的 ProjectStructure 查询
 * - 替代 LoadProjectUnits 中的 Symbol 和 Symb2TermInfo 查询
 * 
 * 注意：
 * - 缓存数据在 loadAll() 调用后是只读的
 * - 如果数据库内容变化，需要重新创建缓存对象
 * - 所有查询失败会返回默认值，不会崩溃
 */
class ProjectDataCache
{
public:
    /**
     * @brief 位置信息结构
     */
    struct LocationInfo {
        QString gaoceng;           // 高层名称
        QString pos;               // 位置名称
        int projectStructureId;    // ProjectStructure_ID
        
        LocationInfo() : projectStructureId(0) {}
        LocationInfo(const QString &g, const QString &p, int id = 0)
            : gaoceng(g), pos(p), projectStructureId(id) {}
        
        bool isValid() const { return !pos.isEmpty(); }
    };
    
    /**
     * @brief Symbol 信息结构
     */
    struct SymbolInfo {
        int symbolId;
        int equipmentId;
        QString designation;
        QStringList connNums;      // 从 Symb2TermInfo 获取的连接点列表
        
        SymbolInfo() : symbolId(0), equipmentId(0) {}
        
        bool isValid() const { return symbolId > 0; }
    };

    ProjectDataCache();
    ~ProjectDataCache();

    /**
     * @brief 加载所有缓存数据
     * @param db 数据库连接
     * @return 成功返回 true，失败返回 false
     */
    bool loadAll(QSqlDatabase &db);

    /**
     * @brief 检查缓存是否已加载
     */
    bool isLoaded() const { return m_loaded; }

    /**
     * @brief 获取缓存的统计信息（用于调试）
     */
    QString getStatistics() const;

    // ============ 核心查询接口 ============

    /**
     * @brief 根据 Equipment_ID 获取位置信息
     * 替代: GetUnitTermimalGaocengAndPos() 中对 Equipment 的查询
     */
    LocationInfo getEquipmentLocation(int equipmentId) const;

    /**
     * @brief 根据 Symbol_ID 获取对应的 Equipment 位置信息
     * 用于: LoadModelLineByUnits 中根据 Symb1_ID/Symb2_ID 获取位置
     */
    LocationInfo getEquipmentLocationBySymbolId(int symbolId) const;

    /**
     * @brief 根据 TerminalStrip_ID 获取位置信息
     * 替代: GetUnitTermimalGaocengAndPos() 中对 TerminalStrip 的查询
     */
    LocationInfo getTerminalStripLocation(int terminalStripId) const;

    /**
     * @brief 根据 ProjectStructure_ID 获取位置信息
     * 替代: LoadModelLineDT 中的 ProjectStructure 查询
     */
    LocationInfo getStructureLocation(int projectStructureId) const;

    /**
     * @brief 根据 Symbol_ID 获取 Symbol 信息（包含 Symb2TermInfo）
     * 替代: GetUnitSpurStrBySymbol_ID() 中的查询
     */
    SymbolInfo getSymbolInfo(int symbolId) const;

    /**
     * @brief 根据 Equipment_ID 获取所有 Symbol_ID 列表
     * 替代: LoadProjectUnits 中对每个 Equipment 查询 Symbol
     */
    QVector<int> getSymbolIdsByEquipment(int equipmentId) const;

    /**
     * @brief 根据 Symb2TermInfo_ID 获取 Symbol_ID
     * 用于: GetUnitStripIDByTermID 中的查询链
     */
    int getSymbolIdByTermInfoId(int termInfoId) const;

    /**
     * @brief 根据 Symbol_ID 获取 Equipment_ID
     */
    int getEquipmentIdBySymbolId(int symbolId) const;

private:
    bool m_loaded;
    
    // ============ 缓存数据结构 ============
    
    // ProjectStructure 缓存 (key: ProjectStructure_ID)
    QHash<int, LocationInfo> m_structures;
    
    // Equipment 位置缓存 (key: Equipment_ID)
    QHash<int, LocationInfo> m_equipmentLocations;
    
    // TerminalStrip 位置缓存 (key: TerminalStrip_ID)
    QHash<int, LocationInfo> m_terminalStripLocations;
    
    // Symbol 信息缓存 (key: Symbol_ID)
    QHash<int, SymbolInfo> m_symbols;
    
    // Equipment -> Symbols 映射 (key: Equipment_ID, value: Symbol_ID列表)
    QHash<int, QVector<int>> m_equipmentSymbols;
    
    // Symb2TermInfo_ID -> Symbol_ID 映射
    QHash<int, int> m_termInfoToSymbol;
    
    // Symbol_ID -> Equipment_ID 映射
    QHash<int, int> m_symbolToEquipment;

    // ============ 内部加载函数 ============
    
    /**
     * @brief 加载 ProjectStructure 表
     * 构建完整的层次结构（高层-位置映射）
     */
    bool loadStructures(QSqlDatabase &db);
    
    /**
     * @brief 加载 Equipment 表及其位置信息
     */
    bool loadEquipments(QSqlDatabase &db);
    
    /**
     * @brief 加载 TerminalStrip 表及其位置信息
     */
    bool loadTerminalStrips(QSqlDatabase &db);
    
    /**
     * @brief 加载 Symbol 表
     */
    bool loadSymbols(QSqlDatabase &db);
    
    /**
     * @brief 加载 Symb2TermInfo 表并关联到 Symbol
     */
    bool loadSymb2TermInfo(QSqlDatabase &db);

    /**
     * @brief 根据 ProjectStructure_ID 递归查找高层和位置
     */
    LocationInfo buildLocationInfo(int projectStructureId) const;
};

#endif // PROJECTDATACACHE_H
