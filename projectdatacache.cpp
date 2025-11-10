#include "projectdatacache.h"
#include "performancetimer.h"

ProjectDataCache::ProjectDataCache()
    : m_loaded(false)
{
}

ProjectDataCache::~ProjectDataCache()
{
}

bool ProjectDataCache::loadAll(QSqlDatabase &db)
{
    PERF_TIMER("ProjectDataCache::loadAll");
    
    if (m_loaded) {
        qDebug() << "[Cache] Already loaded, skipping";
        return true;
    }
    
    // 清空现有数据
    m_structures.clear();
    m_equipmentLocations.clear();
    m_terminalStripLocations.clear();
    m_symbols.clear();
    m_equipmentSymbols.clear();
    m_termInfoToSymbol.clear();
    m_symbolToEquipment.clear();
    
    // 按依赖顺序加载
    if (!loadStructures(db)) {
        qWarning() << "[Cache] Failed to load structures";
        return false;
    }
    
    if (!loadEquipments(db)) {
        qWarning() << "[Cache] Failed to load equipments";
        return false;
    }
    
    if (!loadTerminalStrips(db)) {
        qWarning() << "[Cache] Failed to load terminal strips";
        return false;
    }
    
    if (!loadSymbols(db)) {
        qWarning() << "[Cache] Failed to load symbols";
        return false;
    }
    
    if (!loadSymb2TermInfo(db)) {
        qWarning() << "[Cache] Failed to load Symb2TermInfo";
        return false;
    }
    
    m_loaded = true;
    qDebug() << "[Cache] Load complete:" << getStatistics();
    return true;
}

QString ProjectDataCache::getStatistics() const
{
    return QString("Structures=%1, Equipments=%2, TerminalStrips=%3, Symbols=%4, TermInfoMappings=%5")
        .arg(m_structures.size())
        .arg(m_equipmentLocations.size())
        .arg(m_terminalStripLocations.size())
        .arg(m_symbols.size())
        .arg(m_termInfoToSymbol.size());
}

bool ProjectDataCache::loadStructures(QSqlDatabase &db)
{
    PERF_TIMER("ProjectDataCache::loadStructures");
    
    QSqlQuery query(db);
    // 使用 JOIN 获取 ProjectStructure 及其 Structure 类型信息
    QString sql = "SELECT ps.ProjectStructure_ID, ps.Structure_ID, ps.Structure_INT, "
                  "ps.Parent_ID, s.Structure_Name "
                  "FROM ProjectStructure ps "
                  "LEFT JOIN Structure s ON ps.Structure_ID = s.Structure_ID "
                  "ORDER BY ps.Parent_ID";
    
    if (!query.exec(sql)) {
        qWarning() << "[Cache] Failed to load structures:" << query.lastError().text();
        return false;
    }
    
    // 第一遍：收集所有记录
    struct TempStructure {
        int id;
        int structureId;
        QString structureInt;  // 用户输入的名称
        QString parentId;
        QString structureName; // Structure 表中的类型名称（如"高层代号"、"位置代号"）
    };
    QVector<TempStructure> tempStructures;
    
    while (query.next()) {
        TempStructure temp;
        temp.id = query.value(0).toInt();
        temp.structureId = query.value(1).toInt();
        temp.structureInt = query.value(2).toString();
        temp.parentId = query.value(3).toString();
        temp.structureName = query.value(4).toString();
        tempStructures.append(temp);
    }
    
    // 第二遍：构建位置信息和详细信息
    // Structure_Name="高层代号" 是高层，"位置代号" 是位置
    QHash<int, QString> gaocengNames;  // 高层 ID -> 名称
    
    for (const TempStructure &temp : tempStructures) {
        // 构建 StructureInfo (用于 LoadModelLineDT)
        StructureInfo detailInfo(temp.id, temp.structureInt, temp.parentId.toInt());
        m_structureDetails[temp.id] = detailInfo;
        
        if (temp.structureName == "高层代号") {
            // 这是高层
            gaocengNames[temp.id] = temp.structureInt;
            LocationInfo info(temp.structureInt, "", temp.id);
            m_structures[temp.id] = info;
        }
    }
    
    for (const TempStructure &temp : tempStructures) {
        if (temp.structureName == "位置代号") {
            // 这是位置，查找其父高层
            int pid = temp.parentId.toInt();
            QString gaocengName = gaocengNames.value(pid, "");
            LocationInfo info(gaocengName, temp.structureInt, temp.id);
            m_structures[temp.id] = info;
        } else if (temp.structureName != "高层代号") {
            // 其他类型（如"文档类型"），也存储但可能不完整
            LocationInfo info("", temp.structureInt, temp.id);
            m_structures[temp.id] = info;
        }
    }
    
    qDebug() << QString("[Cache] Loaded %1 structures").arg(m_structures.size());
    return true;
}

bool ProjectDataCache::loadEquipments(QSqlDatabase &db)
{
    PERF_TIMER("ProjectDataCache::loadEquipments");
    
    QSqlQuery query(db);
    // Equipment 通过 ProjectStructure_ID 关联，直接使用已缓存的结构信息
    QString sql = "SELECT Equipment_ID, ProjectStructure_ID FROM Equipment";
    
    if (!query.exec(sql)) {
        qWarning() << "[Cache] Failed to load equipments:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        int equipmentId = query.value(0).toInt();
        int projectStructureId = query.value(1).toInt();
        
        // 从已加载的 structures 缓存中获取位置信息
        LocationInfo info = m_structures.value(projectStructureId, LocationInfo());
        m_equipmentLocations[equipmentId] = info;
    }
    
    qDebug() << QString("[Cache] Loaded %1 equipment locations").arg(m_equipmentLocations.size());
    return true;
}

bool ProjectDataCache::loadTerminalStrips(QSqlDatabase &db)
{
    PERF_TIMER("ProjectDataCache::loadTerminalStrips");
    
    QSqlQuery query(db);
    // TerminalStrip 通过 ProjectStructure_ID 关联
    QString sql = "SELECT TerminalStrip_ID, ProjectStructure_ID FROM TerminalStrip";
    
    if (!query.exec(sql)) {
        qWarning() << "[Cache] Failed to load terminal strips:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        int terminalStripId = query.value(0).toInt();
        int projectStructureId = query.value(1).toInt();
        
        // 从已加载的 structures 缓存中获取位置信息
        LocationInfo info = m_structures.value(projectStructureId, LocationInfo());
        m_terminalStripLocations[terminalStripId] = info;
    }
    
    qDebug() << QString("[Cache] Loaded %1 terminal strip locations").arg(m_terminalStripLocations.size());
    return true;
}

bool ProjectDataCache::loadSymbols(QSqlDatabase &db)
{
    PERF_TIMER("ProjectDataCache::loadSymbols");
    
    QSqlQuery query(db);
    QString sql = "SELECT Symbol_ID, Equipment_ID, Designation FROM Symbol";
    
    if (!query.exec(sql)) {
        qWarning() << "[Cache] Failed to load symbols:" << query.lastError().text();
        return false;
    }
    
    while (query.next()) {
        int symbolId = query.value(0).toInt();
        int equipmentId = query.value(1).toInt();
        QString designation = query.value(2).toString();
        
        SymbolInfo info;
        info.symbolId = symbolId;
        info.equipmentId = equipmentId;
        info.designation = designation;
        
        m_symbols[symbolId] = info;
        m_symbolToEquipment[symbolId] = equipmentId;
        
        // 构建 Equipment -> Symbols 映射
        m_equipmentSymbols[equipmentId].append(symbolId);
    }
    
    qDebug() << QString("[Cache] Loaded %1 symbols").arg(m_symbols.size());
    return true;
}

bool ProjectDataCache::loadSymb2TermInfo(QSqlDatabase &db)
{
    PERF_TIMER("ProjectDataCache::loadSymb2TermInfo");
    
    QSqlQuery query(db);
    // 使用 GROUP_CONCAT 一次性获取每个 Symbol 的所有 ConnNum
    QString sql = "SELECT Symbol_ID, Symb2TermInfo_ID, ConnNum "
                  "FROM Symb2TermInfo "
                  "ORDER BY Symbol_ID, ConnNum";
    
    if (!query.exec(sql)) {
        qWarning() << "[Cache] Failed to load Symb2TermInfo:" << query.lastError().text();
        return false;
    }
    
    int lastSymbolId = -1;
    while (query.next()) {
        int symbolId = query.value(0).toInt();
        int termInfoId = query.value(1).toInt();
        QString connNum = query.value(2).toString();
        
        // 建立 TermInfo -> Symbol 映射
        m_termInfoToSymbol[termInfoId] = symbolId;
        
        // 将 ConnNum 添加到对应 Symbol
        if (m_symbols.contains(symbolId)) {
            m_symbols[symbolId].connNums.append(connNum);
        }
        
        if (lastSymbolId != symbolId && lastSymbolId != -1) {
            // 新的 Symbol，可以在这里做额外处理（如排序）
        }
        lastSymbolId = symbolId;
    }
    
    qDebug() << QString("[Cache] Loaded %1 TermInfo mappings").arg(m_termInfoToSymbol.size());
    return true;
}

// ============ 查询接口实现 ============

ProjectDataCache::LocationInfo ProjectDataCache::getEquipmentLocation(int equipmentId) const
{
    return m_equipmentLocations.value(equipmentId, LocationInfo());
}

ProjectDataCache::LocationInfo ProjectDataCache::getEquipmentLocationBySymbolId(int symbolId) const
{
    int equipmentId = m_symbolToEquipment.value(symbolId, 0);
    if (equipmentId == 0) {
        return LocationInfo();
    }
    return m_equipmentLocations.value(equipmentId, LocationInfo());
}

ProjectDataCache::LocationInfo ProjectDataCache::getTerminalStripLocation(int terminalStripId) const
{
    return m_terminalStripLocations.value(terminalStripId, LocationInfo());
}

ProjectDataCache::LocationInfo ProjectDataCache::getStructureLocation(int projectStructureId) const
{
    return m_structures.value(projectStructureId, LocationInfo());
}

ProjectDataCache::StructureInfo ProjectDataCache::getStructureInfo(int projectStructureId) const
{
    return m_structureDetails.value(projectStructureId, StructureInfo());
}

ProjectDataCache::SymbolInfo ProjectDataCache::getSymbolInfo(int symbolId) const
{
    return m_symbols.value(symbolId, SymbolInfo());
}

QStringList ProjectDataCache::getTermInfos(int symbolId) const
{
    SymbolInfo info = m_symbols.value(symbolId, SymbolInfo());
    return info.connNums;
}

QVector<int> ProjectDataCache::getSymbolIdsByEquipment(int equipmentId) const
{
    return m_equipmentSymbols.value(equipmentId, QVector<int>());
}

int ProjectDataCache::getSymbolIdByTermInfoId(int termInfoId) const
{
    return m_termInfoToSymbol.value(termInfoId, 0);
}

int ProjectDataCache::getEquipmentIdBySymbolId(int symbolId) const
{
    return m_symbolToEquipment.value(symbolId, 0);
}

ProjectDataCache::LocationInfo ProjectDataCache::buildLocationInfo(int projectStructureId) const
{
    // 这个函数保留用于特殊情况，通常不需要调用
    // 因为我们在加载时已经构建好了所有位置信息
    return m_structures.value(projectStructureId, LocationInfo());
}
