#ifndef PROJECTDATAMODEL_H
#define PROJECTDATAMODEL_H

#include <QString>
#include <QHash>
#include <QVector>
#include <QList>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSharedPointer>
#include <QDebug>

/**
 * @brief ProjectDataModel - 完整的项目内存数据模型
 * 
 * 设计目标:
 * 1. 一次性加载所有核心数据到内存 (预计50-100ms)
 * 2. 提供O(1)快速查询接口
 * 3. 支持UI按需加载
 * 4. 支持诊断分析功能
 * 
 * 性能预期:
 * - 加载时间: 50-100ms (vs 当前225秒)
 * - 内存占用: ~50-100MB (4924个器件)
 * - 查询速度: O(1) Hash查找
 */

// ============ 核心数据结构 ============

/**
 * @brief Structure - 结构层次信息
 */
struct StructureData {
    int id;                    // ProjectStructure_ID
    int structureId;           // Structure_ID
    QString structureInt;      // Structure_INT (用户输入名称)
    QString structureName;     // Structure_Name (类型: 高层代号/位置代号)
    int parentId;              // Parent_ID
    QString desc;              // Struct_Desc
    
    // 运行时计算的字段
    QString fullPath;          // 完整路径: "高层/位置"
    QVector<int> children;     // 子节点ID列表
    
    StructureData() : id(0), structureId(0), parentId(0) {}
    bool isValid() const { return id > 0; }
    bool isGaoceng() const { return structureName == "高层代号"; }
    bool isPos() const { return structureName == "位置代号"; }
};

/**
 * @brief Equipment - 器件信息
 */
struct EquipmentData {
    int id;                    // Equipment_ID
    QString dt;                // DT (器件标签)
    int structureId;           // ProjectStructure_ID
    QString type;              // Type
    QString name;              // Name
    QString spec;              // Spec
    QString partCode;          // PartCode
    QString tModel;            // TModel
    QString tModelDiag;        // TModelDiag (诊断模型)
    QString factory;           // Factory
    QString remark;            // Remark
    
    // 关联数据
    QVector<int> symbolIds;    // 关联的Symbol_ID列表
    
    // 运行时字段
    QString displayText;       // 显示文本: "DT(Type,Name)"
    QString gaoceng;           // 所属高层
    QString pos;               // 所属位置
    
    EquipmentData() : id(0), structureId(0) {}
    bool isValid() const { return id > 0; }
};

/**
 * @brief Symbol - 功能子块信息
 */
struct SymbolData {
    int id;                    // Symbol_ID
    int pageId;                // Page_ID
    int equipmentId;           // Equipment_ID
    QString symbol;            // Symbol (图块名称)
    QString symbolHandle;      // Symbol_Handle
    QString designation;       // Designation
    QString funDefine;         // FunDefine
    int structureId;           // ProjectStructure_ID
    bool execConn;             // ExecConn (可执行连接)
    bool sourceConn;           // SourceConn (信号源)
    
    // 关联数据
    QStringList connNums;      // 从Symb2TermInfo获取的ConnNum列表
    
    // 运行时字段
    QString displayText;       // 显示文本: "Designation:ConnNums-FunDefine"
    QString iconType;          // 图标类型: "已插入"/"未插入"/"不可插入"
    QString pageName;          // 页面名称 (缓存)
    
    SymbolData() : id(0), pageId(0), equipmentId(0), structureId(0), 
                   execConn(false), sourceConn(false) {}
    bool isValid() const { return id > 0; }
    bool isInserted() const { return !symbolHandle.isEmpty(); }
};

/**
 * @brief Page - 页面信息
 */
struct PageData {
    int id;                    // Page_ID
    int structureId;           // ProjectStructure_ID
    QString pageDesc;          // Page_Desc
    QString pageType;          // PageType
    int pageNum;               // PageNum
    QString pageName;          // PageName
    
    // 运行时字段
    QString fullName;          // 完整名称: "高层/位置/PageName"
    QString gaoceng;           // 所属高层
    QString pos;               // 所属位置
    
    PageData() : id(0), structureId(0), pageNum(0) {}
    bool isValid() const { return id > 0; }
};

/**
 * @brief Connection - 连线信息 (JXB)
 */
struct ConnectionData {
    int id;                    // JXB_ID
    int structureId;           // ProjectStructure_ID
    int pageId;                // Page_ID
    QString connectionNumber;  // ConnectionNumber (线号)
    QString symb1Id;           // Symb1_ID / Start_Symbol_ID
    QString symb2Id;           // Symb2_ID / End_Symbol_ID
    QString symb1Category;     // Symb1_Category
    QString symb2Category;     // Symb2_Category
    QString category;          // Category
    QString wiresType;         // Wires_Type
    QString wiresColor;        // Wires_Color
    QString tModel;            // TModel
    
    // 运行时字段
    QString startStr;          // 起点描述字符串
    QString endStr;            // 终点描述字符串
    QString displayText;       // 显示文本: "ConnectionNumber (起点 → 终点)"
    QString gaoceng;           // 所属高层
    QString pos;               // 所属位置
    
    ConnectionData() : id(0), structureId(0), pageId(0) {}
    bool isValid() const { return id > 0; }
};

/**
 * @brief Terminal - 端子信息
 */
struct TerminalData {
    int id;                    // Terminal_ID
    int terminalStripId;       // TerminalStrip_ID
    int pageId;                // Page_ID
    int structureId;           // ProjectStructure_ID
    QString designation;       // Designation
    QString position;          // Position
    QString funDefine;         // FunDefine
    
    // 运行时字段
    QString displayText;       // 显示文本
    
    TerminalData() : id(0), terminalStripId(0), pageId(0), structureId(0) {}
    bool isValid() const { return id > 0; }
};

/**
 * @brief TerminalStrip - 端子排信息
 */
struct TerminalStripData {
    int id;                    // TerminalStrip_ID (DzbName_ID)
    int structureId;           // ProjectStructure_ID
    QString designation;       // Designation
    QString type;              // Type
    
    // 关联数据
    QVector<int> terminalIds;  // 关联的Terminal_ID列表
    
    TerminalStripData() : id(0), structureId(0) {}
    bool isValid() const { return id > 0; }
};

// ============ 数据管理器 ============

/**
 * @brief StructureManager - 管理结构层次
 */
class StructureManager {
public:
    StructureManager() {}
    
    // 加载数据
    bool load(QSqlDatabase &db);
    
    // 查询接口
    const StructureData* getStructure(int id) const;
    QString getFullPath(int id) const;  // 获取完整路径 "高层/位置"
    QVector<int> getChildren(int parentId) const;
    QVector<int> getRootNodes() const;  // 获取顶层节点
    
    // 快速查询
    QString getGaoceng(int id) const;   // 获取高层名称
    QString getPos(int id) const;       // 获取位置名称
    
    // 统计信息
    int count() const { return m_structures.size(); }
    QString getStatistics() const;
    
private:
    void buildHierarchy();              // 构建层次关系
    void buildFullPaths();              // 构建完整路径
    
    QHash<int, StructureData> m_structures;     // key: ProjectStructure_ID
    QHash<int, QVector<int>> m_childrenMap;     // key: Parent_ID
    QVector<int> m_rootNodes;                   // 根节点列表
};

/**
 * @brief EquipmentManager - 管理器件数据
 */
class EquipmentManager {
public:
    EquipmentManager(StructureManager *structureMgr) 
        : m_structureMgr(structureMgr) {}
    
    // 加载数据
    bool load(QSqlDatabase &db);
    
    // 查询接口
    const EquipmentData* getEquipment(int id) const;
    const EquipmentData* getEquipmentByDT(const QString &dt) const;
    QVector<int> getEquipmentsByStructure(int structureId) const;
    QVector<int> getAllEquipmentIds() const;
    
    // 关联Symbol
    void addSymbol(int equipmentId, int symbolId);
    
    // 统计信息
    int count() const { return m_equipments.size(); }
    QString getStatistics() const;
    
private:
    void buildLocationInfo();           // 构建位置信息
    void buildDisplayText();            // 构建显示文本
    
    StructureManager *m_structureMgr;
    QHash<int, EquipmentData> m_equipments;         // key: Equipment_ID
    QHash<QString, int> m_dtIndex;                  // key: DT
    QHash<int, QVector<int>> m_structureIndex;      // key: ProjectStructure_ID
};

/**
 * @brief SymbolManager - 管理功能子块数据
 */
class SymbolManager {
public:
    SymbolManager(EquipmentManager *equipmentMgr) 
        : m_equipmentMgr(equipmentMgr) {}
    
    // 加载数据
    bool loadSymbols(QSqlDatabase &db);
    bool loadSymb2TermInfo(QSqlDatabase &db);
    
    // 查询接口
    const SymbolData* getSymbol(int id) const;
    QVector<int> getSymbolsByEquipment(int equipmentId) const;
    QVector<int> getAllSymbolIds() const;
    
    // 统计信息
    int symbolCount() const { return m_symbols.size(); }
    int termInfoCount() const { return m_totalTermInfos; }
    QString getStatistics() const;
    
private:
    void buildDisplayText();            // 构建显示文本
    
    EquipmentManager *m_equipmentMgr;
    QHash<int, SymbolData> m_symbols;               // key: Symbol_ID
    QHash<int, QVector<int>> m_equipmentIndex;      // key: Equipment_ID
    int m_totalTermInfos;
};

/**
 * @brief PageManager - 管理页面数据
 */
class PageManager {
public:
    PageManager(StructureManager *structureMgr) 
        : m_structureMgr(structureMgr) {}
    
    // 加载数据
    bool load(QSqlDatabase &db);
    
    // 查询接口
    const PageData* getPage(int id) const;
    QString getPageFullName(int id) const;  // 获取完整页面名称
    QVector<int> getPagesByType(const QString &type) const;
    QVector<int> getAllPageIds() const;
    
    // 获取唯一的高层/位置列表(用于ComboBox)
    QStringList getUniqueGaocengList() const;
    QStringList getUniquePosList() const;
    
    // 统计信息
    int count() const { return m_pages.size(); }
    QString getStatistics() const;
    
private:
    void buildFullNames();              // 构建完整名称
    
    StructureManager *m_structureMgr;
    QHash<int, PageData> m_pages;                   // key: Page_ID
    QHash<QString, QVector<int>> m_typeIndex;       // key: PageType
};

/**
 * @brief ConnectionManager - 管理连线数据 (JXB)
 */
class ConnectionManager {
public:
    ConnectionManager(StructureManager *structureMgr, 
                     PageManager *pageMgr,
                     SymbolManager *symbolMgr)
        : m_structureMgr(structureMgr),
          m_pageMgr(pageMgr),
          m_symbolMgr(symbolMgr) {}
    
    // 加载数据
    bool load(QSqlDatabase &db);
    
    // 查询接口
    const ConnectionData* getConnection(int id) const;
    QVector<int> getConnectionsByStructure(int structureId) const;
    QVector<int> getConnectionsByNumber(const QString &number) const;
    QVector<int> getAllConnectionIds() const;
    
    // 统计信息
    int count() const { return m_connections.size(); }
    QString getStatistics() const;
    
private:
    void buildDisplayText();            // 构建显示文本
    QString buildSymbStr(const QString &symbId, const QString &category) const;
    
    StructureManager *m_structureMgr;
    PageManager *m_pageMgr;
    SymbolManager *m_symbolMgr;
    QHash<int, ConnectionData> m_connections;           // key: JXB_ID
    QHash<int, QVector<int>> m_structureIndex;          // key: ProjectStructure_ID
    QHash<QString, QVector<int>> m_connectionNumIndex;  // key: ConnectionNumber
};

// ============ 主模型类 ============

/**
 * @brief ProjectDataModel - 主数据模型
 * 
 * 使用方法:
 * ```cpp
 * ProjectDataModel model;
 * if (model.loadAll(database)) {
 *     // 查询器件
 *     const EquipmentData* eq = model.getEquipment(id);
 *     
 *     // 查询Symbol
 *     QVector<int> symbolIds = model.getSymbolsByEquipment(equipmentId);
 *     
 *     // 查询连线
 *     QVector<int> connIds = model.getConnectionsByStructure(structureId);
 * }
 * ```
 */
class ProjectDataModel {
public:
    ProjectDataModel();
    ~ProjectDataModel();
    
    /**
     * @brief 一次性加载所有数据
     * @param db 数据库连接
     * @return 成功返回true
     */
    bool loadAll(QSqlDatabase &db);
    
    /**
     * @brief 检查是否已加载
     */
    bool isLoaded() const { return m_loaded; }
    
    /**
     * @brief 清空所有数据
     */
    void clear();
    
    // ============ 访问各Manager ============
    
    StructureManager* structureManager() { return m_structureMgr; }
    EquipmentManager* equipmentManager() { return m_equipmentMgr; }
    SymbolManager* symbolManager() { return m_symbolMgr; }
    PageManager* pageManager() { return m_pageMgr; }
    ConnectionManager* connectionManager() { return m_connMgr; }
    
    const StructureManager* structureManager() const { return m_structureMgr; }
    const EquipmentManager* equipmentManager() const { return m_equipmentMgr; }
    const SymbolManager* symbolManager() const { return m_symbolMgr; }
    const PageManager* pageManager() const { return m_pageMgr; }
    const ConnectionManager* connectionManager() const { return m_connMgr; }
    
    // ============ 便捷查询接口 ============
    
    // Structure
    const StructureData* getStructure(int id) const;
    QString getFullPath(int id) const;
    
    // Equipment
    const EquipmentData* getEquipment(int id) const;
    QVector<int> getEquipmentsByStructure(int structureId) const;
    
    // Symbol
    const SymbolData* getSymbol(int id) const;
    QVector<int> getSymbolsByEquipment(int equipmentId) const;
    
    // Page
    const PageData* getPage(int id) const;
    QString getPageFullName(int id) const;
    
    // Connection
    const ConnectionData* getConnection(int id) const;
    QVector<int> getConnectionsByStructure(int structureId) const;
    
    // ============ 统计信息 ============
    
    QString getStatistics() const;
    
private:
    bool m_loaded;
    
    StructureManager *m_structureMgr;
    EquipmentManager *m_equipmentMgr;
    SymbolManager *m_symbolMgr;
    PageManager *m_pageMgr;
    ConnectionManager *m_connMgr;
};

#endif // PROJECTDATAMODEL_H
