#include "projectdatamodel.h"
#include "performancetimer.h"
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QSqlRecord>
#include <QDebug>
#include <QSet>
#include <functional>

// ============ StructureManager Implementation ============

bool StructureManager::load(QSqlDatabase &db)
{
    PERF_TIMER("StructureManager::load");
    
    m_structures.clear();
    m_childrenMap.clear();
    m_rootNodes.clear();
    
    QSqlQuery query(db);
    QString sql = "SELECT ps.ProjectStructure_ID, ps.Structure_ID, ps.Structure_INT, "
                  "ps.Parent_ID, ps.Struct_Desc, s.Structure_Name "
                  "FROM ProjectStructure ps "
                  "LEFT JOIN Structure s ON ps.Structure_ID = s.Structure_ID "
                  "ORDER BY ps.Parent_ID, ps.ProjectStructure_ID";
    
    if (!query.exec(sql)) {
        qWarning() << "[StructureManager] Failed to load:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        StructureData data;
        data.id = query.value(0).toInt();
        data.structureId = query.value(1).toInt();
        data.structureInt = query.value(2).toString();
        data.parentId = query.value(3).toInt();
        data.desc = query.value(4).toString();
        data.structureName = query.value(5).toString();
        
        m_structures[data.id] = data;
    }
    
    // 构建层次关系和完整路径
    buildHierarchy();
    buildFullPaths();
    
    qDebug() << QString("[StructureManager] Loaded %1 structures").arg(m_structures.size());
    return true;
}

const StructureData* StructureManager::getStructure(int id) const
{
    auto it = m_structures.find(id);
    return it != m_structures.end() ? &(*it) : nullptr;
}

QString StructureManager::getFullPath(int id) const
{
    auto it = m_structures.find(id);
    return it != m_structures.end() ? it->fullPath : QString();
}

QVector<int> StructureManager::getChildren(int parentId) const
{
    auto it = m_childrenMap.find(parentId);
    return it != m_childrenMap.end() ? *it : QVector<int>();
}

QVector<int> StructureManager::getRootNodes() const
{
    return m_rootNodes;
}

QString StructureManager::getGaoceng(int id) const
{
    const StructureData *data = getStructure(id);
    if (!data) return QString();
    
    if (data->isGaoceng()) {
        return data->structureInt;
    }
    
    // 向上查找父节点
    if (data->parentId > 0) {
        return getGaoceng(data->parentId);
    }
    
    return QString();
}

QString StructureManager::getPos(int id) const
{
    const StructureData *data = getStructure(id);
    if (!data) return QString();
    
    if (data->isPos()) {
        return data->structureInt;
    }
    
    return QString();
}

QString StructureManager::getStatistics() const
{
    int gaocengCount = 0;
    int posCount = 0;
    
    for (auto it = m_structures.begin(); it != m_structures.end(); ++it) {
        if (it->isGaoceng()) gaocengCount++;
        else if (it->isPos()) posCount++;
    }
    
    return QString("Structures=%1 (高层=%2, 位置=%3)")
           .arg(m_structures.size())
           .arg(gaocengCount)
           .arg(posCount);
}

void StructureManager::buildHierarchy()
{
    m_childrenMap.clear();
    m_rootNodes.clear();
    
    for (auto it = m_structures.begin(); it != m_structures.end(); ++it) {
        int id = it->id;
        int parentId = it->parentId;
        
        if (parentId == 0 || parentId == id) {
            // 根节点
            m_rootNodes.append(id);
        } else {
            // 添加到父节点的children列表
            m_childrenMap[parentId].append(id);
        }
    }
}

void StructureManager::buildFullPaths()
{
    // 递归构建完整路径
    std::function<QString(int)> buildPath = [&](int id) -> QString {
        auto it = m_structures.find(id);
        if (it == m_structures.end()) return QString();
        
        // 如果已经计算过,直接返回
        if (!it->fullPath.isEmpty()) {
            return it->fullPath;
        }
        
        QString path = it->structureInt;
        
        if (it->parentId > 0 && it->parentId != id) {
            QString parentPath = buildPath(it->parentId);
            if (!parentPath.isEmpty()) {
                path = parentPath + "/" + path;
            }
        }
        
        // 缓存结果
        it->fullPath = path;
        return path;
    };
    
    // 为所有节点构建路径
    for (auto it = m_structures.begin(); it != m_structures.end(); ++it) {
        if (it->fullPath.isEmpty()) {
            buildPath(it->id);
        }
    }
}

// ============ EquipmentManager Implementation ============

bool EquipmentManager::load(QSqlDatabase &db)
{
    PERF_TIMER("EquipmentManager::load");
    
    m_equipments.clear();
    m_dtIndex.clear();
    m_structureIndex.clear();
    
    QSqlQuery query(db);
    QString sql = "SELECT Equipment_ID, DT, ProjectStructure_ID, Type, Name, "
                  "Spec, PartCode, TModel, TModelDiag, Factory, Remark "
                  "FROM Equipment "
                  "ORDER BY DT";
    
    if (!query.exec(sql)) {
        qWarning() << "[EquipmentManager] Failed to load:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        EquipmentData data;
        data.id = query.value(0).toInt();
        data.dt = query.value(1).toString();
        data.structureId = query.value(2).toInt();
        data.type = query.value(3).toString();
        data.name = query.value(4).toString();
        data.spec = query.value(5).toString();
        data.partCode = query.value(6).toString();
        data.tModel = query.value(7).toString();
        data.tModelDiag = query.value(8).toString();
        data.factory = query.value(9).toString();
        data.remark = query.value(10).toString();
        
        m_equipments[data.id] = data;
        
        // 建立索引
        if (!data.dt.isEmpty()) {
            m_dtIndex[data.dt] = data.id;
        }
        m_structureIndex[data.structureId].append(data.id);
    }
    
    // 构建位置信息和显示文本
    buildLocationInfo();
    buildDisplayText();
    
    qDebug() << QString("[EquipmentManager] Loaded %1 equipments").arg(m_equipments.size());
    return true;
}

const EquipmentData* EquipmentManager::getEquipment(int id) const
{
    auto it = m_equipments.find(id);
    return it != m_equipments.end() ? &(*it) : nullptr;
}

const EquipmentData* EquipmentManager::getEquipmentByDT(const QString &dt) const
{
    auto it = m_dtIndex.find(dt);
    if (it != m_dtIndex.end()) {
        return getEquipment(*it);
    }
    return nullptr;
}

QVector<int> EquipmentManager::getEquipmentsByStructure(int structureId) const
{
    auto it = m_structureIndex.find(structureId);
    return it != m_structureIndex.end() ? *it : QVector<int>();
}

QVector<int> EquipmentManager::getAllEquipmentIds() const
{
    QVector<int> ids;
    ids.reserve(m_equipments.size());
    for (auto it = m_equipments.begin(); it != m_equipments.end(); ++it) {
        ids.append(it->id);
    }
    return ids;
}

void EquipmentManager::addSymbol(int equipmentId, int symbolId)
{
    auto it = m_equipments.find(equipmentId);
    if (it != m_equipments.end()) {
        it->symbolIds.append(symbolId);
    }
}

QString EquipmentManager::getStatistics() const
{
    return QString("Equipments=%1").arg(m_equipments.size());
}

void EquipmentManager::buildLocationInfo()
{
    if (!m_structureMgr) return;
    
    for (auto it = m_equipments.begin(); it != m_equipments.end(); ++it) {
        it->gaoceng = m_structureMgr->getGaoceng(it->structureId);
        it->pos = m_structureMgr->getPos(it->structureId);
    }
}

void EquipmentManager::buildDisplayText()
{
    for (auto it = m_equipments.begin(); it != m_equipments.end(); ++it) {
        QString text = it->dt;
        
        if (!it->type.isEmpty() || !it->name.isEmpty()) {
            text += "(";
            if (!it->type.isEmpty()) {
                text += it->type;
            }
            if (!it->name.isEmpty()) {
                if (!it->type.isEmpty()) text += ",";
                text += it->name;
            }
            text += ")";
        }
        
        it->displayText = text;
    }
}

// ============ SymbolManager Implementation ============

bool SymbolManager::loadSymbols(QSqlDatabase &db)
{
    PERF_TIMER("SymbolManager::loadSymbols");
    
    m_symbols.clear();
    m_equipmentIndex.clear();
    m_totalTermInfos = 0;
    
    QSqlQuery query(db);
    QString sql = "SELECT Symbol_ID, Page_ID, Equipment_ID, Symbol, Symbol_Handle, "
                  "Designation, FunDefine, ProjectStructure_ID, ExecConn, SourceConn "
                  "FROM Symbol "
                  "ORDER BY Equipment_ID, Symbol_ID";
    
    if (!query.exec(sql)) {
        qWarning() << "[SymbolManager] Failed to load symbols:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        SymbolData data;
        data.id = query.value(0).toInt();
        data.pageId = query.value(1).toInt();
        data.equipmentId = query.value(2).toInt();
        data.symbol = query.value(3).toString();
        data.symbolHandle = query.value(4).toString();
        data.designation = query.value(5).toString();
        data.funDefine = query.value(6).toString();
        data.structureId = query.value(7).toInt();
        data.execConn = query.value(8).toBool();
        data.sourceConn = query.value(9).toBool();
        
        m_symbols[data.id] = data;
        
        // 建立索引
        m_equipmentIndex[data.equipmentId].append(data.id);
        
        // 关联到Equipment
        if (m_equipmentMgr) {
            m_equipmentMgr->addSymbol(data.equipmentId, data.id);
        }
    }
    
    qDebug() << QString("[SymbolManager] Loaded %1 symbols").arg(m_symbols.size());
    return true;
}

bool SymbolManager::loadSymb2TermInfo(QSqlDatabase &db)
{
    PERF_TIMER("SymbolManager::loadSymb2TermInfo");
    
    QSqlQuery query(db);
    QString sql = "SELECT Symbol_ID, ConnNum "
                  "FROM Symb2TermInfo "
                  "ORDER BY Symbol_ID, ConnNum";
    
    if (!query.exec(sql)) {
        qWarning() << "[SymbolManager] Failed to load Symb2TermInfo:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        int symbolId = query.value(0).toInt();
        QString connNum = query.value(1).toString();
        
        auto it = m_symbols.find(symbolId);
        if (it != m_symbols.end()) {
            it->connNums.append(connNum);
            m_totalTermInfos++;
        }
    }
    
    // 构建显示文本
    buildDisplayText();
    
    qDebug() << QString("[SymbolManager] Loaded %1 TermInfo mappings").arg(m_totalTermInfos);
    return true;
}

const SymbolData* SymbolManager::getSymbol(int id) const
{
    auto it = m_symbols.find(id);
    return it != m_symbols.end() ? &(*it) : nullptr;
}

QVector<int> SymbolManager::getSymbolsByEquipment(int equipmentId) const
{
    auto it = m_equipmentIndex.find(equipmentId);
    return it != m_equipmentIndex.end() ? *it : QVector<int>();
}

QVector<int> SymbolManager::getAllSymbolIds() const
{
    QVector<int> ids;
    ids.reserve(m_symbols.size());
    for (auto it = m_symbols.begin(); it != m_symbols.end(); ++it) {
        ids.append(it->id);
    }
    return ids;
}

QString SymbolManager::getStatistics() const
{
    return QString("Symbols=%1, TermInfos=%2").arg(m_symbols.size()).arg(m_totalTermInfos);
}

void SymbolManager::buildDisplayText()
{
    for (auto it = m_symbols.begin(); it != m_symbols.end(); ++it) {
        QString text;
        
        // Designation:ConnNums
        if (!it->designation.isEmpty()) {
            text += it->designation + ":";
        }
        
        // 拼接ConnNums
        for (int i = 0; i < it->connNums.size(); ++i) {
            if (i > 0) text += " ￤ ";
            text += it->connNums[i];
        }
        
        // FunDefine
        if (!it->funDefine.isEmpty()) {
            if (!text.isEmpty()) text += "-";
            text += it->funDefine;
        }
        
        it->displayText = text;
        
        // 确定图标类型
        if (it->symbol.isEmpty() && it->funDefine != "黑盒" && it->funDefine != "PLC 盒子") {
            it->iconType = "不可插入";
        } else if (it->isInserted()) {
            it->iconType = "已插入";
        } else {
            it->iconType = "未插入";
        }
    }
}

// ============ PageManager Implementation ============

bool PageManager::load(QSqlDatabase &db)
{
    PERF_TIMER("PageManager::load");
    
    m_pages.clear();
    m_typeIndex.clear();
    
    QSqlQuery query(db);
    QString sql = "SELECT Page_ID, ProjectStructure_ID, Page_Desc, PageType, "
                  "PageNum, PageName "
                  "FROM Page "
                  "ORDER BY ProjectStructure_ID, PageNum";
    
    if (!query.exec(sql)) {
        qWarning() << "[PageManager] Failed to load:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        PageData data;
        data.id = query.value(0).toInt();
        data.structureId = query.value(1).toInt();
        data.pageDesc = query.value(2).toString();
        data.pageType = query.value(3).toString();
        data.pageNum = query.value(4).toInt();
        data.pageName = query.value(5).toString();
        
        m_pages[data.id] = data;
        
        // 建立索引
        m_typeIndex[data.pageType].append(data.id);
    }
    
    // 构建完整名称
    buildFullNames();
    
    qDebug() << QString("[PageManager] Loaded %1 pages").arg(m_pages.size());
    return true;
}

const PageData* PageManager::getPage(int id) const
{
    auto it = m_pages.find(id);
    return it != m_pages.end() ? &(*it) : nullptr;
}

QString PageManager::getPageFullName(int id) const
{
    auto it = m_pages.find(id);
    return it != m_pages.end() ? it->fullName : QString();
}

QVector<int> PageManager::getPagesByType(const QString &type) const
{
    auto it = m_typeIndex.find(type);
    return it != m_typeIndex.end() ? *it : QVector<int>();
}

QVector<int> PageManager::getAllPageIds() const
{
    QVector<int> ids;
    ids.reserve(m_pages.size());
    for (auto it = m_pages.begin(); it != m_pages.end(); ++it) {
        ids.append(it->id);
    }
    return ids;
}

QString PageManager::getStatistics() const
{
    return QString("Pages=%1").arg(m_pages.size());
}

void PageManager::buildFullNames()
{
    if (!m_structureMgr) return;
    
    for (auto it = m_pages.begin(); it != m_pages.end(); ++it) {
        it->gaoceng = m_structureMgr->getGaoceng(it->structureId);
        it->pos = m_structureMgr->getPos(it->structureId);
        
        QString path = m_structureMgr->getFullPath(it->structureId);
        if (!path.isEmpty()) {
            it->fullName = path + "/" + it->pageName;
        } else {
            it->fullName = it->pageName;
        }
    }
}

QStringList PageManager::getUniqueGaocengList() const
{
    QSet<QString> gaocengSet;
    for (auto it = m_pages.begin(); it != m_pages.end(); ++it) {
        // 包含空字符串(对应高层为空的页面)
        gaocengSet.insert(it->gaoceng);
    }
    
    QStringList result = gaocengSet.values();
    std::sort(result.begin(), result.end());
    return result;
}

QStringList PageManager::getUniquePosList() const
{
    QSet<QString> posSet;
    for (auto it = m_pages.begin(); it != m_pages.end(); ++it) {
        // 包含空字符串(对应位置为空的页面)
        posSet.insert(it->pos);
    }
    
    QStringList result = posSet.values();
    std::sort(result.begin(), result.end());
    return result;
}

// ============ ConnectionManager Implementation ============

bool ConnectionManager::load(QSqlDatabase &db)
{
    PERF_TIMER("ConnectionManager::load");
    
    m_connections.clear();
    m_structureIndex.clear();
    m_connectionNumIndex.clear();

    auto collectColumns = [&db](const QString &tableName) -> QSet<QString> {
        QSet<QString> columns;
        QSqlQuery schemaQuery(db);
        if (schemaQuery.exec(QString("PRAGMA table_info(%1)").arg(tableName))) {
            while (schemaQuery.next()) {
                columns.insert(schemaQuery.value(1).toString());
            }
        } else {
            qWarning() << "[ConnectionManager] Failed to inspect schema for" << tableName << ":" << schemaQuery.lastError().text();
        }
        return columns;
    };
    
    const QSet<QString> columnSet = collectColumns(QString("JXB"));
    auto resolveColumn = [&columnSet](const QString &preferred, const QString &fallback) -> QString {
        if (columnSet.contains(preferred)) {
            return preferred;
        }
        if (columnSet.contains(fallback)) {
            return fallback;
        }
        return QString();
    };
    
    const QString symb1Column = resolveColumn(QString("Start_Symbol_ID"), QString("Symb1_ID"));
    const QString symb2Column = resolveColumn(QString("End_Symbol_ID"), QString("Symb2_ID"));
    if (symb1Column.isEmpty() || symb2Column.isEmpty()) {
        qWarning() << "[ConnectionManager] Missing Symb1_ID/Symb2_ID columns in JXB table, skip connection loading.";
        return true;
    }

    // 动态构建SELECT列列表，只包含存在的列
    QStringList selectColumns;
    selectColumns << "JXB_ID";
    selectColumns << QString("%1 AS Symb1_ID").arg(symb1Column);
    selectColumns << QString("%1 AS Symb2_ID").arg(symb2Column);

    // 必要列（通常存在）
    if (columnSet.contains("ConnectionNumber")) {
        selectColumns << "ConnectionNumber";
    }
    if (columnSet.contains("Page_ID")) {
        selectColumns << "Page_ID";
    }
    if (columnSet.contains("ProjectStructure_ID")) {
        selectColumns << "ProjectStructure_ID";
    }

    // 可选列（可能不存在）
    if (columnSet.contains("Category")) {
        selectColumns << "Category";
    }
    if (columnSet.contains("Wires_Type")) {
        selectColumns << "Wires_Type";
    }
    if (columnSet.contains("Wires_Color")) {
        selectColumns << "Wires_Color";
    }
    if (columnSet.contains("TModel")) {
        selectColumns << "TModel";
    }
    if (columnSet.contains("Symb1_Category")) {
        selectColumns << "Symb1_Category";
    }
    if (columnSet.contains("Symb2_Category")) {
        selectColumns << "Symb2_Category";
    }

    QSqlQuery query(db);
    QString sql = QString("SELECT %1 FROM JXB ORDER BY ProjectStructure_ID, ConnectionNumber")
                      .arg(selectColumns.join(", "));

    qDebug() << "[ConnectionManager] Executing SQL:" << sql;
    
    if (!query.exec(sql)) {
        qWarning() << "[ConnectionManager] Failed to load:" << query.lastError().text();
        return false;
    }

    // 记录每个字段的位置索引
    QMap<QString, int> fieldIndex;
    for (int i = 0; i < selectColumns.size(); ++i) {
        QString fieldName = selectColumns[i];
        // 移除AS别名，使用原始列名
        if (fieldName.contains(" AS ")) {
            QStringList parts = fieldName.split(" AS ");
            fieldName = parts[1].trimmed();
        }
        fieldIndex[fieldName] = i;
    }

    while (query.next()) {
        ConnectionData data;

        // 按索引顺序读取数据
        data.id = query.value(0).toInt();  // JXB_ID
        data.symb1Id = query.value(1).toString();  // Symb1_ID
        data.symb2Id = query.value(2).toString();  // Symb2_ID

        // 可选字段：检查列是否存在再读取
        if (fieldIndex.contains("ConnectionNumber")) {
            data.connectionNumber = query.value(fieldIndex["ConnectionNumber"]).toString();
        }
        if (fieldIndex.contains("Category")) {
            data.category = query.value(fieldIndex["Category"]).toString();
        }
        if (fieldIndex.contains("Page_ID")) {
            data.pageId = query.value(fieldIndex["Page_ID"]).toInt();
        }
        if (fieldIndex.contains("ProjectStructure_ID")) {
            data.structureId = query.value(fieldIndex["ProjectStructure_ID"]).toInt();
        }
        if (fieldIndex.contains("Wires_Type")) {
            data.wiresType = query.value(fieldIndex["Wires_Type"]).toString();
        }
        if (fieldIndex.contains("Wires_Color")) {
            data.wiresColor = query.value(fieldIndex["Wires_Color"]).toString();
        }
        if (fieldIndex.contains("TModel")) {
            data.tModel = query.value(fieldIndex["TModel"]).toString();
        }
        if (fieldIndex.contains("Symb1_Category")) {
            data.symb1Category = query.value(fieldIndex["Symb1_Category"]).toString();
        }
        if (fieldIndex.contains("Symb2_Category")) {
            data.symb2Category = query.value(fieldIndex["Symb2_Category"]).toString();
        }

        m_connections[data.id] = data;

        // 建立索引
        m_structureIndex[data.structureId].append(data.id);
        m_connectionNumIndex[data.connectionNumber].append(data.id);
    }
    
    // 构建显示文本
    buildDisplayText();
    
    qDebug() << QString("[ConnectionManager] Loaded %1 connections").arg(m_connections.size());
    return true;
}

const ConnectionData* ConnectionManager::getConnection(int id) const
{
    auto it = m_connections.find(id);
    return it != m_connections.end() ? &(*it) : nullptr;
}

QVector<int> ConnectionManager::getConnectionsByStructure(int structureId) const
{
    auto it = m_structureIndex.find(structureId);
    return it != m_structureIndex.end() ? *it : QVector<int>();
}

QVector<int> ConnectionManager::getConnectionsByNumber(const QString &number) const
{
    auto it = m_connectionNumIndex.find(number);
    return it != m_connectionNumIndex.end() ? *it : QVector<int>();
}

QVector<int> ConnectionManager::getAllConnectionIds() const
{
    QVector<int> ids;
    ids.reserve(m_connections.size());
    for (auto it = m_connections.begin(); it != m_connections.end(); ++it) {
        ids.append(it->id);
    }
    return ids;
}

QString ConnectionManager::getStatistics() const
{
    return QString("Connections=%1").arg(m_connections.size());
}

void ConnectionManager::buildDisplayText()
{
    for (auto it = m_connections.begin(); it != m_connections.end(); ++it) {
        QString gaoceng, pos;
        if (m_structureMgr) {
            gaoceng = m_structureMgr->getGaoceng(it->structureId);
            pos = m_structureMgr->getPos(it->structureId);
        }
        it->gaoceng = gaoceng;
        it->pos = pos;
        
        // 构建起点和终点字符串
        it->startStr = buildSymbStr(it->symb1Id, it->category);
        it->endStr = buildSymbStr(it->symb2Id, it->category);
        
        // 构建完整显示文本: ConnectionNumber (起点 → 终点)
        QString display = it->connectionNumber;
        if (!it->startStr.isEmpty() || !it->endStr.isEmpty()) {
            display += " (";
            display += it->startStr;
            display += " → ";
            display += it->endStr;
            display += ")";
        }
        it->displayText = display;
    }
}

QString ConnectionManager::buildSymbStr(const QString &symbIdStr, const QString &category) const
{
    if (symbIdStr.isEmpty() || !m_symbolMgr) {
        return QString();
    }
    
    bool ok;
    int symbolId = symbIdStr.toInt(&ok);
    if (!ok) return QString();
    
    const SymbolData *symbol = m_symbolMgr->getSymbol(symbolId);
    if (!symbol) return QString();
    
    // 根据Category决定返回什么
    if (category == "Start" || category == "End") {
        return symbol->designation;
    } else {
        // 默认返回 Designation:ConnNums
        QString result = symbol->designation;
        if (!symbol->connNums.isEmpty()) {
            result += ":";
            result += symbol->connNums.join(" ￤ ");
        }
        return result;
    }
}

// ============ ProjectDataModel Implementation ============

ProjectDataModel::ProjectDataModel()
    : m_loaded(false)
{
    m_structureMgr = new StructureManager();
    m_equipmentMgr = new EquipmentManager(m_structureMgr);
    m_symbolMgr = new SymbolManager(m_equipmentMgr);
    m_pageMgr = new PageManager(m_structureMgr);
    m_connMgr = new ConnectionManager(m_structureMgr, m_pageMgr, m_symbolMgr);
}

ProjectDataModel::~ProjectDataModel()
{
    delete m_connMgr;
    delete m_pageMgr;
    delete m_symbolMgr;
    delete m_equipmentMgr;
    delete m_structureMgr;
}

bool ProjectDataModel::loadAll(QSqlDatabase &db)
{
    PERF_TIMER("ProjectDataModel::loadAll");
    
    clear();
    
    qDebug() << "[ProjectDataModel] === 开始加载项目数据到内存 ===";
    
    // 1. 加载Structure (层次结构)
    qDebug() << "[ProjectDataModel] 步骤1: 加载结构层次 (Structure)...";
    if (!m_structureMgr->load(db)) {
        qCritical() << "[ProjectDataModel] 步骤1失败: 无法加载结构层次数据!";
        qCritical() << "[ProjectDataModel] 错误详情:" << db.lastError().text();
        return false;
    }
    qDebug() << "[ProjectDataModel] 步骤1完成: 已加载" << m_structureMgr->count() << "个结构节点";
    qDebug() << "[ProjectDataModel] 统计:" << m_structureMgr->getStatistics();

    // 2. 加载Equipment (器件)
    qDebug() << "[ProjectDataModel] 步骤2: 加载器件数据 (Equipment)...";
    if (!m_equipmentMgr->load(db)) {
        qCritical() << "[ProjectDataModel] 步骤2失败: 无法加载器件数据!";
        qCritical() << "[ProjectDataModel] 错误详情:" << db.lastError().text();
        return false;
    }
    qDebug() << "[ProjectDataModel] 步骤2完成: 已加载" << m_equipmentMgr->count() << "个器件";
    qDebug() << "[ProjectDataModel] 统计:" << m_equipmentMgr->getStatistics();

    // 3. 加载Symbol (功能子块)
    qDebug() << "[ProjectDataModel] 步骤3: 加载功能子块 (Symbol)...";
    if (!m_symbolMgr->loadSymbols(db)) {
        qCritical() << "[ProjectDataModel] 步骤3失败: 无法加载功能子块!";
        qCritical() << "[ProjectDataModel] 错误详情:" << db.lastError().text();
        return false;
    }
    qDebug() << "[ProjectDataModel] 步骤3完成: 已加载" << m_symbolMgr->symbolCount() << "个功能子块";

    // 4. 加载Symb2TermInfo (端子信息)
    qDebug() << "[ProjectDataModel] 步骤4: 加载端子信息 (Symb2TermInfo)...";
    if (!m_symbolMgr->loadSymb2TermInfo(db)) {
        qCritical() << "[ProjectDataModel] 步骤4失败: 无法加载端子信息!";
        qCritical() << "[ProjectDataModel] 错误详情:" << db.lastError().text();
        return false;
    }
    qDebug() << "[ProjectDataModel] 步骤4完成: 已加载" << m_symbolMgr->termInfoCount() << "条端子信息";

    // 5. 加载Page (页面)
    qDebug() << "[ProjectDataModel] 步骤5: 加载页面数据 (Page)...";
    if (!m_pageMgr->load(db)) {
        qCritical() << "[ProjectDataModel] 步骤5失败: 无法加载页面数据!";
        qCritical() << "[ProjectDataModel] 错误详情:" << db.lastError().text();
        return false;
    }
    qDebug() << "[ProjectDataModel] 步骤5完成: 已加载" << m_pageMgr->count() << "个页面";

    // 6. 加载Connection (连线)
    qDebug() << "[ProjectDataModel] 步骤6: 加载连线数据 (Connection)...";
    if (!m_connMgr->load(db)) {
        qCritical() << "[ProjectDataModel] 步骤6失败: 无法加载连线数据!";
        qCritical() << "[ProjectDataModel] 错误详情:" << db.lastError().text();
        return false;
    }
    qDebug() << "[ProjectDataModel] 步骤6完成: 已加载" << m_connMgr->count() << "条连线";
    
    // TODO: 7. 加载Terminal (端子)
    
    m_loaded = true;
    
    qDebug() << "[ProjectDataModel] === 数据加载完成 ===";
    qDebug() << "[ProjectDataModel] " << getStatistics();
    
    return true;
}

void ProjectDataModel::clear()
{
    m_loaded = false;
    // Managers会在各自的load()中清空数据
}

// ============ 便捷查询接口 ============

const StructureData* ProjectDataModel::getStructure(int id) const
{
    return m_structureMgr ? m_structureMgr->getStructure(id) : nullptr;
}

QString ProjectDataModel::getFullPath(int id) const
{
    return m_structureMgr ? m_structureMgr->getFullPath(id) : QString();
}

const EquipmentData* ProjectDataModel::getEquipment(int id) const
{
    return m_equipmentMgr ? m_equipmentMgr->getEquipment(id) : nullptr;
}

QVector<int> ProjectDataModel::getEquipmentsByStructure(int structureId) const
{
    return m_equipmentMgr ? m_equipmentMgr->getEquipmentsByStructure(structureId) : QVector<int>();
}

const SymbolData* ProjectDataModel::getSymbol(int id) const
{
    return m_symbolMgr ? m_symbolMgr->getSymbol(id) : nullptr;
}

QVector<int> ProjectDataModel::getSymbolsByEquipment(int equipmentId) const
{
    return m_symbolMgr ? m_symbolMgr->getSymbolsByEquipment(equipmentId) : QVector<int>();
}

const PageData* ProjectDataModel::getPage(int id) const
{
    return m_pageMgr ? m_pageMgr->getPage(id) : nullptr;
}

QString ProjectDataModel::getPageFullName(int id) const
{
    return m_pageMgr ? m_pageMgr->getPageFullName(id) : QString();
}

const ConnectionData* ProjectDataModel::getConnection(int id) const
{
    return m_connMgr ? m_connMgr->getConnection(id) : nullptr;
}

QVector<int> ProjectDataModel::getConnectionsByStructure(int structureId) const
{
    return m_connMgr ? m_connMgr->getConnectionsByStructure(structureId) : QVector<int>();
}

QString ProjectDataModel::getStatistics() const
{
    QString stats;
    
    if (m_structureMgr) {
        stats += m_structureMgr->getStatistics() + ", ";
    }
    if (m_equipmentMgr) {
        stats += m_equipmentMgr->getStatistics() + ", ";
    }
    if (m_symbolMgr) {
        stats += m_symbolMgr->getStatistics() + ", ";
    }
    if (m_pageMgr) {
        stats += m_pageMgr->getStatistics() + ", ";
    }
    if (m_connMgr) {
        stats += m_connMgr->getStatistics();
    }
    
    return stats;
}
