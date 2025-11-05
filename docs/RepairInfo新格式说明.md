# RepairInfo 新格式说明

## 格式变更

### 旧格式（已废弃）
```
故障模式名a￤0.002￤￤￤￤故障模式名c￤0.003￤￤￤￤...
```
问题：
- 使用全角字符￤作为分隔符，容易产生解析歧义
- 无法正确处理字段中的特殊字符
- 无法处理换行符
- 格式脆弱，易出错

### 新格式（JSON数组）
```json
[
  {
    "fault": "故障模式",
    "prob": "故障概率",
    "solution": "解决方案",
    "resource": "所需资源"
  },
  ...
]
```

优势：
- ✅ 标准JSON格式，可靠性高
- ✅ 自动处理所有特殊字符（引号、反斜杠、换行等）
- ✅ 易于扩展（可添加新字段）
- ✅ 易于调试和查看
- ✅ 紧凑模式节省空间

## 数据迁移

### 自动迁移策略
当打开对话框加载RepairInfo时：
1. 尝试解析为JSON格式
2. 如果解析失败（旧格式或格式错误），**清空数据**
3. 表格显示为空，用户可重新输入

### 不需要手动迁移
- 旧格式数据在首次打开时会被清空
- 用户重新编辑并保存后，将使用新格式

## 示例数据

### 包含换行的方案
```json
[
  {
    "fault": "电机开路",
    "prob": "0.05",
    "solution": "步骤1：断电检查\n步骤2：更换电机\n步骤3：测试运行",
    "resource": "电机×1\n万用表\n绝缘测试仪"
  }
]
```

### 包含特殊字符
```json
[
  {
    "fault": "轴承|损坏",
    "prob": "0.02",
    "solution": "方案：A\\B\\C\n备选：D|E|F",
    "resource": "资源：X|Y|Z"
  }
]
```

### 空字段处理
```json
[
  {
    "fault": "未知故障",
    "prob": "",
    "solution": "",
    "resource": ""
  }
]
```

## 代码实现

### 序列化（保存）
```cpp
QJsonArray array;
for (auto it = faultMap.begin(); it != faultMap.end(); ++it) {
    QJsonObject obj;
    obj["fault"] = it.key();
    obj["prob"] = info[0];
    obj["solution"] = info[1];
    obj["resource"] = info[2];
    array.append(obj);
}
QJsonDocument doc(array);
QString json = QString::fromUtf8(doc.toJson(QJsonDocument::Compact));
```

### 反序列化（加载）
```cpp
QJsonDocument doc = QJsonDocument::fromJson(repairInfoStr.toUtf8());
if (!doc.isArray()) {
    // 格式错误，清空数据
    return QMap<QString, QStringList>();
}
QJsonArray array = doc.array();
for (int i = 0; i < array.size(); ++i) {
    QJsonObject obj = array[i].toObject();
    QString fault = obj.value("fault").toString();
    // ...
}
```

## 调试信息

### 保存时的日志
```
[TModelHelper::saveRepairInfoFromTable] 表格行数: 2
[TModelHelper::saveRepairInfoFromTable] 行0: 故障模式="电机开路", 概率="0.05", ...
[TModelHelper::serializeRepairInfo] 序列化2条记录，结果长度:XXX
Equipment updated successfully
```

### 加载时的日志
```
[TModelHelper::loadRepairInfoToTable] RepairInfo长度: XXX
[TModelHelper::parseRepairInfo] 成功解析JSON数组，包含2条记录
[TModelHelper::parseRepairInfo] 记录0: 故障模式=电机开路
[TModelHelper::parseRepairInfo] 最终解析出2条有效记录
[TModelHelper::loadRepairInfoToTable] 加载行0: 故障模式=电机开路
```

### 旧格式检测日志
```
[TModelHelper::parseRepairInfo] JSON解析失败: illegal value
[TModelHelper::parseRepairInfo] 检测到旧格式数据，将被清空
```

## 测试验证

运行测试脚本：
```bash
python tools/test_json_format.py
```

测试内容：
- ✅ 各种特殊字符（引号、反斜杠、竖线等）
- ✅ 换行符处理
- ✅ 空字段处理
- ✅ 数据一致性（序列化→反序列化）
- ✅ 旧格式拒绝

## 数据库验证

查看数据库中的新格式：
```bash
sqlite3 "ref/LdMainData.db" "SELECT Equipment_ID, Name, RepairInfo FROM Equipment WHERE Equipment_ID=10716;"
```

新格式示例：
```
10716|三相电机|[{"fault":"电机开路","prob":"0.05","solution":"更换电机","resource":"电机×1"}]
```

## 注意事项

1. **首次使用警告**
   - 首次打开包含旧格式数据的元件时，维修信息会被清空
   - 这是预期行为，不是bug
   - 请重新输入维修信息

2. **字段内容限制**
   - 故障模式：必填，不能为空
   - 其他字段：可选，可为空
   - 所有字段支持任意Unicode字符和换行

3. **数据库字段大小**
   - RepairInfo字段类型：VARCHAR(2000)
   - JSON格式略大于旧格式，但仍在限制内
   - 如果数据量大，考虑增加字段长度

4. **向后兼容性**
   - **不支持向后兼容**
   - 旧版本软件无法读取新格式数据
   - 请确保所有用户升级到新版本

## 常见问题

### Q: 为什么我的维修信息变空了？
A: 你打开了包含旧格式数据的元件。新版本自动清空了旧格式数据。请重新输入。

### Q: 可以恢复旧数据吗？
A: 如果有数据库备份，可以从备份中查看旧数据，然后手动重新输入。

### Q: 解决方案中可以使用换行吗？
A: 可以！在表格单元格中按 Shift+Enter 可以输入换行。

### Q: 字段中可以包含特殊字符吗？
A: 可以！JSON格式会自动转义所有特殊字符。

## 修改文件

- `BO/function/tmodelhelper.h` - 添加QJson相关头文件
- `BO/function/tmodelhelper.cpp` - 更新parseRepairInfo和serializeRepairInfo函数
- `tools/test_json_format.py` - JSON格式测试脚本（新增）

## 版本信息

- 变更日期：2025-10-31
- 变更原因：解决旧格式解析问题，支持特殊字符和换行
- 影响范围：所有使用维修信息功能的元件
- 兼容性：不向后兼容，旧格式数据会被清空
