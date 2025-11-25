#include "macrofamilyrepository.h"

// MacroFamily implementation
ConnectionMacro MacroFamily::getMacroByArity(int arity) const
{
    return macros.value(arity, ConnectionMacro());
}

bool MacroFamily::loadMacrosFromJson(const QString &json, QString *errorMsg)
{
    macros.clear();
    
    QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8());
    if (!doc.isArray()) {
        if (errorMsg) *errorMsg = "宏定义必须是JSON数组";
        return false;
    }
    
    QJsonArray arr = doc.array();
    for (const QJsonValue &val : arr) {
        if (!val.isObject()) continue;
        
        QJsonObject obj = val.toObject();
        ConnectionMacro macro;
        macro.arity = obj["arity"].toInt();
        macro.macroName = obj["macro_name"].toString();
        macro.expansionTemplate = obj["expansion"].toString();
        
        if (macro.isValid()) {
            macros.insert(macro.arity, macro);
        }
    }
    
    return !macros.isEmpty();
}

QString MacroFamily::exportMacrosToJson() const
{
    QJsonArray arr;
    for (auto it = macros.constBegin(); it != macros.constEnd(); ++it) {
        const ConnectionMacro &macro = it.value();
        QJsonObject obj;
        obj["arity"] = macro.arity;
        obj["macro_name"] = macro.macroName;
        obj["expansion"] = macro.expansionTemplate;
        arr.append(obj);
    }
    
    QJsonDocument doc(arr);
    return QString::fromUtf8(doc.toJson(QJsonDocument::Compact));
}

// MacroFamilyRepository implementation
MacroFamilyRepository::MacroFamilyRepository(const QSqlDatabase &db)
    : m_db(db)
{
}

bool MacroFamilyRepository::ensureSchema()
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        return false;
    }
    
    // Schema should already exist from project.db template
    return true;
}

bool MacroFamilyRepository::macroFamilyExists(const QString &familyName)
{
    QSqlQuery query(m_db);
    query.prepare("SELECT COUNT(*) FROM port_connect_macro_family WHERE family_name = ?");
    query.addBindValue(familyName);
    
    if (query.exec() && query.next()) {
        return query.value(0).toInt() > 0;
    }
    
    return false;
}

MacroFamily MacroFamilyRepository::createElectricConnectFamily()
{
    MacroFamily family;
    family.familyName = "electric-connect";
    family.domain = "electric";
    family.description = "内置电气连接宏族，生成电流守恒与电压等势约束";
    family.isBuiltin = true;
    
    // connect2e: 2端口电气连接
    ConnectionMacro macro2;
    macro2.arity = 2;
    macro2.macroName = "connect2e";
    macro2.expansionTemplate = "(assert (= (+ %1.i %2.i) 0))\n(assert (= %1.u %2.u))";
    family.macros.insert(2, macro2);
    
    // connect3e: 3端口电气连接
    ConnectionMacro macro3;
    macro3.arity = 3;
    macro3.macroName = "connect3e";
    macro3.expansionTemplate = "(assert (= (+ %1.i %2.i %3.i) 0))\n(assert (= %1.u %2.u))\n(assert (= %2.u %3.u))";
    family.macros.insert(3, macro3);
    
    // connect4e: 4端口电气连接
    ConnectionMacro macro4;
    macro4.arity = 4;
    macro4.macroName = "connect4e";
    macro4.expansionTemplate = "(assert (= (+ %1.i %2.i %3.i %4.i) 0))\n(assert (= %1.u %2.u))\n(assert (= %2.u %3.u))\n(assert (= %3.u %4.u))";
    family.macros.insert(4, macro4);
    
    return family;
}

MacroFamily MacroFamilyRepository::createHydraulicConnectFamily()
{
    MacroFamily family;
    family.familyName = "hydraulic-connect";
    family.domain = "hydraulic";
    family.description = "内置液压连接宏族，生成流量守恒与压力等势约束";
    family.isBuiltin = true;
    
    // connect2h: 2端口液压连接
    ConnectionMacro macro2;
    macro2.arity = 2;
    macro2.macroName = "connect2h";
    macro2.expansionTemplate = "(assert (= (+ %1.q %2.q) 0))\n(assert (= %1.p %2.p))";
    family.macros.insert(2, macro2);
    
    // connect3h: 3端口液压连接
    ConnectionMacro macro3;
    macro3.arity = 3;
    macro3.macroName = "connect3h";
    macro3.expansionTemplate = "(assert (= (+ %1.q %2.q %3.q) 0))\n(assert (= %1.p %2.p))\n(assert (= %2.p %3.p))";
    family.macros.insert(3, macro3);
    
    // connect4h: 4端口液压连接
    ConnectionMacro macro4;
    macro4.arity = 4;
    macro4.macroName = "connect4h";
    macro4.expansionTemplate = "(assert (= (+ %1.q %2.q %3.q %4.q) 0))\n(assert (= %1.p %2.p))\n(assert (= %2.p %3.p))\n(assert (= %3.p %4.p))";
    family.macros.insert(4, macro4);
    
    return family;
}

MacroFamily MacroFamilyRepository::createMechanicalConnectFamily()
{
    MacroFamily family;
    family.familyName = "mechanical-connect";
    family.domain = "mechanical";
    family.description = "内置机械连接宏族，生成力守恒与位移等势约束";
    family.isBuiltin = true;
    
    // connect2m: 2端口机械连接
    ConnectionMacro macro2;
    macro2.arity = 2;
    macro2.macroName = "connect2m";
    macro2.expansionTemplate = "(assert (= (+ %1.F %2.F) 0))\n(assert (= %1.x %2.x))";
    family.macros.insert(2, macro2);
    
    // connect3m: 3端口机械连接
    ConnectionMacro macro3;
    macro3.arity = 3;
    macro3.macroName = "connect3m";
    macro3.expansionTemplate = "(assert (= (+ %1.F %2.F %3.F) 0))\n(assert (= %1.x %2.x))\n(assert (= %2.x %3.x))";
    family.macros.insert(3, macro3);
    
    // connect4m: 4端口机械连接
    ConnectionMacro macro4;
    macro4.arity = 4;
    macro4.macroName = "connect4m";
    macro4.expansionTemplate = "(assert (= (+ %1.F %2.F %3.F %4.F) 0))\n(assert (= %1.x %2.x))\n(assert (= %2.x %3.x))\n(assert (= %3.x %4.x))";
    family.macros.insert(4, macro4);
    
    return family;
}

bool MacroFamilyRepository::initializeBuiltinMacroFamilies(QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    // Initialize electric-connect family
    if (!macroFamilyExists("electric-connect")) {
        MacroFamily electricFamily = createElectricConnectFamily();
        if (!saveMacroFamily(electricFamily, errorMsg)) {
            return false;
        }
    }
    
    // Initialize hydraulic-connect family
    if (!macroFamilyExists("hydraulic-connect")) {
        MacroFamily hydraulicFamily = createHydraulicConnectFamily();
        if (!saveMacroFamily(hydraulicFamily, errorMsg)) {
            return false;
        }
    }
    
    // Initialize mechanical-connect family
    if (!macroFamilyExists("mechanical-connect")) {
        MacroFamily mechanicalFamily = createMechanicalConnectFamily();
        if (!saveMacroFamily(mechanicalFamily, errorMsg)) {
            return false;
        }
    }
    
    return true;
}

QList<MacroFamily> MacroFamilyRepository::getAllMacroFamilies(QString *errorMsg)
{
    QList<MacroFamily> families;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return families;
    }
    
    QSqlQuery query(m_db);
    if (!query.exec("SELECT family_id, family_name, domain, description, is_builtin, macros_json "
                    "FROM port_connect_macro_family ORDER BY is_builtin DESC, family_name")) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return families;
    }
    
    while (query.next()) {
        MacroFamily family;
        family.familyId = query.value(0).toInt();
        family.familyName = query.value(1).toString();
        family.domain = query.value(2).toString();
        family.description = query.value(3).toString();
        family.isBuiltin = query.value(4).toInt() != 0;
        
        QString macrosJson = query.value(5).toString();
        family.loadMacrosFromJson(macrosJson);
        
        families.append(family);
    }
    
    return families;
}

QList<MacroFamily> MacroFamilyRepository::getBuiltinMacroFamilies(QString *errorMsg)
{
    QList<MacroFamily> families;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return families;
    }
    
    QSqlQuery query(m_db);
    if (!query.exec("SELECT family_id, family_name, domain, description, is_builtin, macros_json "
                    "FROM port_connect_macro_family WHERE is_builtin = 1 ORDER BY family_name")) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return families;
    }
    
    while (query.next()) {
        MacroFamily family;
        family.familyId = query.value(0).toInt();
        family.familyName = query.value(1).toString();
        family.domain = query.value(2).toString();
        family.description = query.value(3).toString();
        family.isBuiltin = true;
        
        QString macrosJson = query.value(5).toString();
        family.loadMacrosFromJson(macrosJson);
        
        families.append(family);
    }
    
    return families;
}

QList<MacroFamily> MacroFamilyRepository::getUserMacroFamilies(QString *errorMsg)
{
    QList<MacroFamily> families;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return families;
    }
    
    QSqlQuery query(m_db);
    if (!query.exec("SELECT family_id, family_name, domain, description, is_builtin, macros_json "
                    "FROM port_connect_macro_family WHERE is_builtin = 0 ORDER BY family_name")) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return families;
    }
    
    while (query.next()) {
        MacroFamily family;
        family.familyId = query.value(0).toInt();
        family.familyName = query.value(1).toString();
        family.domain = query.value(2).toString();
        family.description = query.value(3).toString();
        family.isBuiltin = false;
        
        QString macrosJson = query.value(5).toString();
        family.loadMacrosFromJson(macrosJson);
        
        families.append(family);
    }
    
    return families;
}

MacroFamily MacroFamilyRepository::getMacroFamily(int familyId, QString *errorMsg)
{
    MacroFamily family;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return family;
    }
    
    QSqlQuery query(m_db);
    query.prepare("SELECT family_id, family_name, domain, description, is_builtin, macros_json "
                  "FROM port_connect_macro_family WHERE family_id = ?");
    query.addBindValue(familyId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return family;
    }
    
    if (query.next()) {
        family.familyId = query.value(0).toInt();
        family.familyName = query.value(1).toString();
        family.domain = query.value(2).toString();
        family.description = query.value(3).toString();
        family.isBuiltin = query.value(4).toInt() != 0;
        
        QString macrosJson = query.value(5).toString();
        family.loadMacrosFromJson(macrosJson);
    } else {
        if (errorMsg) *errorMsg = "未找到宏族";
    }
    
    return family;
}

MacroFamily MacroFamilyRepository::getMacroFamilyByName(const QString &familyName, QString *errorMsg)
{
    MacroFamily family;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return family;
    }
    
    QSqlQuery query(m_db);
    query.prepare("SELECT family_id, family_name, domain, description, is_builtin, macros_json "
                  "FROM port_connect_macro_family WHERE family_name = ?");
    query.addBindValue(familyName);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return family;
    }
    
    if (query.next()) {
        family.familyId = query.value(0).toInt();
        family.familyName = query.value(1).toString();
        family.domain = query.value(2).toString();
        family.description = query.value(3).toString();
        family.isBuiltin = query.value(4).toInt() != 0;
        
        QString macrosJson = query.value(5).toString();
        family.loadMacrosFromJson(macrosJson);
    }
    
    return family;
}

bool MacroFamilyRepository::saveMacroFamily(MacroFamily &family, QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    QString macrosJson = family.exportMacrosToJson();
    
    QSqlQuery query(m_db);
    query.prepare(
        "INSERT OR REPLACE INTO port_connect_macro_family "
        "(family_name, domain, description, is_builtin, macros_json, created_at) "
        "VALUES (?, ?, ?, ?, ?, datetime('now'))"
    );
    query.addBindValue(family.familyName);
    query.addBindValue(family.domain);
    query.addBindValue(family.description);
    query.addBindValue(family.isBuiltin ? 1 : 0);
    query.addBindValue(macrosJson);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "保存失败: " + query.lastError().text();
        return false;
    }
    
    if (family.familyId <= 0) {
        family.familyId = query.lastInsertId().toInt();
    }
    
    return true;
}

bool MacroFamilyRepository::updateMacroFamily(const MacroFamily &family, QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    if (family.familyId <= 0) {
        if (errorMsg) *errorMsg = "无效的family_id";
        return false;
    }
    
    QString macrosJson = family.exportMacrosToJson();
    
    QSqlQuery query(m_db);
    query.prepare(
        "UPDATE port_connect_macro_family SET "
        "domain = ?, description = ?, macros_json = ? "
        "WHERE family_id = ?"
    );
    query.addBindValue(family.domain);
    query.addBindValue(family.description);
    query.addBindValue(macrosJson);
    query.addBindValue(family.familyId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "更新失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}

bool MacroFamilyRepository::deleteMacroFamily(int familyId, QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    // Check if it's a builtin family
    QSqlQuery checkQuery(m_db);
    checkQuery.prepare("SELECT is_builtin FROM port_connect_macro_family WHERE family_id = ?");
    checkQuery.addBindValue(familyId);
    
    if (checkQuery.exec() && checkQuery.next()) {
        bool isBuiltin = checkQuery.value(0).toInt() != 0;
        if (isBuiltin) {
            if (errorMsg) *errorMsg = "不能删除内置宏族";
            return false;
        }
    }
    
    QSqlQuery query(m_db);
    query.prepare("DELETE FROM port_connect_macro_family WHERE family_id = ?");
    query.addBindValue(familyId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "删除失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}

QString MacroFamilyRepository::expandMacro(const QString &familyName, int arity, 
                                          const QStringList &ports, QString *errorMsg)
{
    if (ports.size() != arity) {
        if (errorMsg) *errorMsg = QString("端口数量(%1)与arity(%2)不匹配").arg(ports.size()).arg(arity);
        return QString();
    }
    
    MacroFamily family = getMacroFamilyByName(familyName, errorMsg);
    if (!family.isValid()) {
        return QString();
    }
    
    ConnectionMacro macro = family.getMacroByArity(arity);
    if (!macro.isValid()) {
        if (errorMsg) *errorMsg = QString("宏族%1不支持%2个端口").arg(familyName).arg(arity);
        return QString();
    }
    
    // Expand the template by replacing %1, %2, %3, etc. with actual port names
    QString expanded = macro.expansionTemplate;
    for (int i = 0; i < ports.size(); ++i) {
        QString placeholder = "%" + QString::number(i + 1);
        expanded.replace(placeholder, ports[i]);
    }
    
    return expanded;
}
