#include "widget/functioneditdialog.h"
#include "ui_functioneditdialog.h"

#include "widget/functionsymbolpickerdialog.h"
#include "widget/functionvariablevaluedialog.h"

#include <QMessageBox>
#include <QSqlQuery>
#include <QSqlError>
#include <QTableWidgetItem>
#include <QSet>
#include <QtDebug>
#include <QDomDocument>
#include <QtGlobal>
#include "BO/systementity.h"
#include "DO/model.h"
#include "testability/constraint_utils.h"

using functionvalues::FunctionVariableRow;

FunctionEditDialog::FunctionEditDialog(const QSqlDatabase &db, QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::FunctionEditDialog)
    , m_db(db)
    , m_analysisService(db)
{
    ui->setupUi(this);
    ui->tableInputs->setColumnCount(2);
    ui->tableInputs->setHorizontalHeaderLabels({tr("变量"), tr("目标值")});
    ui->tableInputs->horizontalHeader()->setStretchLastSection(true);
    ui->tableInputs->verticalHeader()->setVisible(false);
    ui->tableInputs->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->tableInputs->setSelectionBehavior(QAbstractItemView::SelectRows);

    connect(ui->btnSelectSymbol, &QPushButton::clicked, this, &FunctionEditDialog::onSelectSymbol);
    connect(ui->btnAddInput, &QPushButton::clicked, this, &FunctionEditDialog::onAddInput);
    connect(ui->btnRemoveInput, &QPushButton::clicked, this, &FunctionEditDialog::onRemoveInput);
    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &FunctionEditDialog::onAccepted);
    connect(ui->listExecs, &QListWidget::itemChanged, this, &FunctionEditDialog::updateExecList);
    connect(ui->btnAutoAnalyze, &QPushButton::clicked, this, &FunctionEditDialog::onAutoAnalyze);
    connect(ui->btnAutoLink, &QPushButton::clicked, this, &FunctionEditDialog::onAutoLink);
    connect(ui->btnVariableValues, &QPushButton::clicked, this, &FunctionEditDialog::onEditVariableValues);

    ui->btnAutoAnalyze->setEnabled(false);
}

void FunctionEditDialog::setInitialRecord(const FunctionRecord &record)
{
    m_record = record;
    ui->editName->setText(record.name);
    ui->plainRemark->setPlainText(record.remark);
    if (record.symbolId > 0)
        setSymbol(record.symbolId, record.symbolName);
    populateInputs(record.cmdValList);
    const QStringList execs = record.execsList.split(',', QString::SkipEmptyParts);
    for (int i = 0; i < ui->listExecs->count(); ++i) {
        QListWidgetItem *item = ui->listExecs->item(i);
        if (execs.contains(item->text()))
            item->setCheckState(Qt::Checked);
        else
            item->setCheckState(Qt::Unchecked);
    }
    ui->editLink->setText(record.link);
    ui->editComponentDependency->setText(record.componentDependency);
    ui->editAllComponents->setText(record.allComponents);
    ui->editFunctionDependency->setText(record.functionDependency);
    ui->checkPersistent->setChecked(record.persistent);
    ui->spinFaultProbability->setValue(record.faultProbability);
    ui->btnAutoAnalyze->setEnabled(record.symbolId > 0);

    setCurrentVariableConfig(variableConfigFromXml(record.variableConfigXml));
}

void FunctionEditDialog::setSymbol(int symbolId, const QString &symbolName)
{
    if (symbolId <= 0)
        return;
    m_record.symbolId = symbolId;
    m_record.symbolName = symbolName;
    ui->editSymbol->setText(symbolName);
    loadSymbolPorts();
    ui->btnAutoAnalyze->setEnabled(true);
}

void FunctionEditDialog::onSelectSymbol()
{
    FunctionSymbolPickerDialog picker(m_db, this);
    if (picker.exec() != QDialog::Accepted)
        return;
    if (picker.selectedSymbolId() == 0)
        return;

    setSymbol(picker.selectedSymbolId(), picker.selectedSymbolName());
    onAutoAnalyze();
}

void FunctionEditDialog::loadSymbolPorts()
{
    m_ports.clear();
    ui->listExecs->clear();
    if (!m_db.isOpen() || m_record.symbolId == 0)
        return;

    QSqlQuery query(m_db);
    query.prepare(QString("SELECT ConnNum, ConnDesc FROM Symb2TermInfo WHERE Symbol_ID = :sid ORDER BY ConnNum"));
    query.bindValue(":sid", m_record.symbolId);
    if (!query.exec()) {
        qWarning() << "FunctionEditDialog" << query.lastError();
        return;
    }

    while (query.next()) {
        PortOption option;
        option.portName = query.value(0).toString();
        option.description = query.value(1).toString();
        m_ports.append(option);

        QListWidgetItem *item = new QListWidgetItem(option.portName, ui->listExecs);
        item->setFlags(item->flags() | Qt::ItemIsUserCheckable);
        item->setCheckState(Qt::Unchecked);
        if (!option.description.isEmpty())
            item->setToolTip(option.description);
    }
}

void FunctionEditDialog::onAddInput()
{
    const int row = ui->tableInputs->rowCount();
    ui->tableInputs->insertRow(row);
    ui->tableInputs->setItem(row, 0, new QTableWidgetItem);
    ui->tableInputs->setItem(row, 1, new QTableWidgetItem);
    ui->tableInputs->editItem(ui->tableInputs->item(row, 0));
}

void FunctionEditDialog::onRemoveInput()
{
    int row = ui->tableInputs->currentRow();
    if (row >= 0)
        ui->tableInputs->removeRow(row);
}

void FunctionEditDialog::applyAnalysis(const FunctionModelResult &result)
{
    if (ui->editName->text().trimmed().isEmpty() && !result.record.name.trimmed().isEmpty())
        ui->editName->setText(result.record.name.trimmed());

    if (!result.record.link.isEmpty())
        ui->editLink->setText(result.record.link);
    if (!result.record.componentDependency.isEmpty())
        ui->editComponentDependency->setText(result.record.componentDependency);
    if (!result.record.allComponents.isEmpty())
        ui->editAllComponents->setText(result.record.allComponents);
    ui->editFunctionDependency->setText(result.record.functionDependency);
    ui->checkPersistent->setChecked(result.record.persistent);
    ui->spinFaultProbability->setValue(result.record.faultProbability);

    const QStringList execItems = result.record.execsList.split(',', QString::SkipEmptyParts);
    QSet<QString> portSet;
    for (const QString &entry : execItems) {
        QString port = entry.trimmed();
        const int dotIndex = port.lastIndexOf('.');
        if (dotIndex >= 0)
            port = port.mid(dotIndex + 1);
        if (!port.isEmpty())
            portSet.insert(port);
    }
    if (!portSet.isEmpty()) {
        for (int i = 0; i < ui->listExecs->count(); ++i) {
            QListWidgetItem *item = ui->listExecs->item(i);
            if (portSet.contains(item->text()))
                item->setCheckState(Qt::Checked);
            else
                item->setCheckState(Qt::Unchecked);
        }
    }
}

void FunctionEditDialog::populateInputs(const QString &cmdValList)
{
    ui->tableInputs->setRowCount(0);
    const QStringList pairs = cmdValList.split(',', QString::SkipEmptyParts);
    for (const QString &pair : pairs) {
        const QStringList parts = pair.split('=');
        if (parts.size() != 2) continue;
        const int row = ui->tableInputs->rowCount();
        ui->tableInputs->insertRow(row);
        ui->tableInputs->setItem(row, 0, new QTableWidgetItem(parts.at(0).trimmed()));
        ui->tableInputs->setItem(row, 1, new QTableWidgetItem(parts.at(1).trimmed()));
    }
}

QMap<QString, QString> FunctionEditDialog::currentConstraintMap() const
{
    QMap<QString, QString> map;
    for (int row = 0; row < ui->tableInputs->rowCount(); ++row) {
        QTableWidgetItem *varItem = ui->tableInputs->item(row, 0);
        QTableWidgetItem *valItem = ui->tableInputs->item(row, 1);
        const QString variable = varItem ? varItem->text().trimmed() : QString();
        const QString value = valItem ? valItem->text().trimmed() : QString();
        if (variable.isEmpty())
            continue;
        map.insert(variable, value);
    }
    return map;
}

QStringList FunctionEditDialog::variableSuggestions() const
{
    QStringList suggestions;
    const QMap<QString, QString> constraintMap = currentConstraintMap();
    for (auto it = constraintMap.constBegin(); it != constraintMap.constEnd(); ++it) {
        if (!it.key().trimmed().isEmpty())
            suggestions.append(it.key().trimmed());
    }

    const QStringList execs = m_record.execsList.split(',', QString::SkipEmptyParts);
    for (const QString &exec : execs) {
        const QString trimmed = exec.trimmed();
        if (!trimmed.isEmpty())
            suggestions.append(trimmed);
    }

    for (const QString &variable : m_variableConfig.variableNames()) {
        suggestions.append(variable);
    }

    suggestions.removeDuplicates();
    return suggestions;
}

QVector<FunctionVariableRow> FunctionEditDialog::collectVariableRows() const
{
    QVector<FunctionVariableRow> rows;
    QSet<QString> seen;
    const QStringList variables = m_variableConfig.variableNames();
    for (const QString &variable : variables) {
        FunctionVariableRow row;
        row.variable = variable;
        const auto entry = m_variableConfig.entry(variable);
        row.typeKey = entry.type;
        row.constraintValue = entry.constraintValue;
        row.typicalValues = entry.typicalValues;
        row.valueRange = entry.valueRange;
        row.satSamples = entry.satSamples;
        rows.append(row);
        seen.insert(variable);
    }

    const QMap<QString, QString> constraints = currentConstraintMap();
    for (auto it = constraints.constBegin(); it != constraints.constEnd(); ++it) {
        const QString variable = it.key().trimmed();
        if (variable.isEmpty() || seen.contains(variable))
            continue;
        FunctionVariableRow row;
        row.variable = variable;
        row.constraintValue = it.value();
        rows.append(row);
        seen.insert(variable);
    }

    return rows;
}

QString FunctionEditDialog::buildCmdValList() const
{
    QStringList pairs;
    for (int row = 0; row < ui->tableInputs->rowCount(); ++row) {
        const QString key = ui->tableInputs->item(row, 0) ? ui->tableInputs->item(row, 0)->text().trimmed() : QString();
        const QString value = ui->tableInputs->item(row, 1) ? ui->tableInputs->item(row, 1)->text().trimmed() : QString();
        if (key.isEmpty() || value.isEmpty()) continue;
        pairs.append(QString("%1=%2").arg(key, value));
    }
    return pairs.join(',');
}

QString FunctionEditDialog::buildExecList() const
{
    QStringList execs;
    for (int i = 0; i < ui->listExecs->count(); ++i) {
        QListWidgetItem *item = ui->listExecs->item(i);
        if (item->checkState() == Qt::Checked) {
            const QString port = item->text();
            if (!m_record.symbolName.isEmpty())
                execs.append(QString("%1.%2").arg(m_record.symbolName, port));
            else
                execs.append(port);
        }
    }
    execs.removeDuplicates();
    return execs.join(',');
}

void FunctionEditDialog::updateExecList()
{
    Q_UNUSED(this);
}

void FunctionEditDialog::setCurrentVariableConfig(const functionvalues::FunctionVariableConfig &config)
{
    m_variableConfig = config;
}

functionvalues::FunctionVariableConfig FunctionEditDialog::variableConfigFromXml(const QString &xml) const
{
    functionvalues::FunctionVariableConfig config;
    const QString trimmed = xml.trimmed();
    if (trimmed.isEmpty())
        return config;

    QDomDocument doc;
    if (!doc.setContent(trimmed)) {
        const QString wrapped = QString("<root>%1</root>").arg(trimmed);
        if (!doc.setContent(wrapped))
            return config;
        QDomElement wrapper = doc.documentElement();
        return functionvalues::FunctionVariableConfig::fromXml(wrapper.firstChildElement(QString("variableValueConfig")));
    }
    QDomElement root = doc.documentElement();
    if (root.tagName() == QString("variableValueConfig")) {
        return functionvalues::FunctionVariableConfig::fromXml(root);
    }
    return functionvalues::FunctionVariableConfig::fromXml(root.firstChildElement(QString("variableValueConfig")));
}

QString FunctionEditDialog::variableConfigToXml(const functionvalues::FunctionVariableConfig &config) const
{
    if (config.isEmpty())
        return QString();
    QDomDocument doc(QString("VariableValueConfig"));
    QDomElement root = config.toXml(doc);
    doc.appendChild(root);
    return doc.toString(2);
}

void FunctionEditDialog::onAutoAnalyze()
{
    if (m_record.symbolId == 0) {
        QMessageBox::information(this, tr("提示"), tr("请先选择功能子块"));
        return;
    }

    const FunctionModelResult result = m_analysisService.analyzeSymbol(m_record.symbolId, ui->editName->text().trimmed());
    if (!result.warnings.isEmpty())
        QMessageBox::information(this, tr("提示"), result.warnings.join("\n"));
    applyAnalysis(result);
}

void FunctionEditDialog::onAutoLink()
{
    if (m_record.symbolId == 0) {
        QMessageBox::information(this, tr("提示"), tr("请先选择功能子块"));
        return;
    }
    const FunctionModelResult result = m_analysisService.analyzeSymbol(m_record.symbolId, ui->editName->text().trimmed());
    if (result.record.link.trimmed().isEmpty()) {
        QMessageBox::information(this, tr("提示"), tr("未能自动推导链路，请手动填写。"));
        return;
    }
    const QString current = ui->editLink->text().trimmed();
    ui->editLink->setText(result.record.link);
    ui->editComponentDependency->setText(result.record.componentDependency);
    ui->editAllComponents->setText(result.record.allComponents);
    if (!current.isEmpty() && current != result.record.link) {
        QMessageBox::information(this, tr("提示"), tr("已填入自动推导链路：%1\n原链路：%2").arg(result.record.link, current));
    }
}

void FunctionEditDialog::analyzeCurrentSymbol()
{
    onAutoAnalyze();
}

void FunctionEditDialog::setSystemContext(SystemEntity *systemEntity, const QString &systemDescription)
{
    m_systemEntity = systemEntity;
    m_systemDescription = systemDescription;
}

void FunctionEditDialog::onEditVariableValues()
{
    QVector<FunctionVariableRow> rows = collectVariableRows();
    auto solver = [this](const QString &variable,
                         const QString &typeKey,
                         const QStringList &typicalValues,
                         QString &errorMessage) {
        return solveVariableRange(variable, typeKey, typicalValues, errorMessage);
    };
    FunctionVariableValueDialog dialog(rows, solver, this);
    if (dialog.exec() != QDialog::Accepted) {
        return;
    }

    const QVector<FunctionVariableRow> resultRows = dialog.resultRows();
    functionvalues::FunctionVariableConfig config;
    for (const FunctionVariableRow &row : resultRows) {
        const QString variable = row.variable.trimmed();
        if (variable.isEmpty())
            continue;
        functionvalues::VariableEntry entry;
        entry.type = row.typeKey;
        if (!row.constraintLocked) {
            entry.constraintValue = row.constraintValue;
        }
        entry.typicalValues = row.typicalValues;
        entry.valueRange = row.valueRange;
        entry.satSamples = row.satSamples;
        config.setEntry(variable, entry);
    }
    setCurrentVariableConfig(config);
}

void FunctionEditDialog::onAccepted()
{
    if (ui->editName->text().trimmed().isEmpty()) {
        QMessageBox::warning(this, tr("提示"), tr("功能名称不能为空"));
        return;
    }
    m_record.name = ui->editName->text().trimmed();
    m_record.remark = ui->plainRemark->toPlainText();
    m_record.execsList = buildExecList();
    m_record.cmdValList = buildCmdValList();
    m_record.link = ui->editLink->text().trimmed();
    m_record.componentDependency = ui->editComponentDependency->text().trimmed();
    m_record.allComponents = ui->editAllComponents->text().trimmed();
    m_record.functionDependency = ui->editFunctionDependency->text().trimmed();
    m_record.persistent = ui->checkPersistent->isChecked();
    m_record.faultProbability = ui->spinFaultProbability->value();
    m_record.variableConfigXml = variableConfigToXml(m_variableConfig);

    accept();
}

QList<TestItem> FunctionEditDialog::buildBaseTestItems() const
{
    QList<TestItem> items;
    const QMap<QString, QString> constraints = currentConstraintMap();
    for (auto it = constraints.constBegin(); it != constraints.constEnd(); ++it) {
        TestItem item;
        item.variable = it.key().trimmed();
        item.value = it.value().trimmed();
        item.testType = QString("一般变量");
        item.checkState = Qt::Checked;
        item.confidence = 1.0;
        items.append(item);
    }
    return items;
}

TestItem FunctionEditDialog::makeVariableSetterItem(const QString &variable, const QString &valueExpression) const
{
    TestItem setter;
    setter.variable = variable;
    setter.testType = QString("一般变量");
    setter.confidence = 1.0;
    setter.checkState = Qt::Checked;
    const QString trimmed = valueExpression.trimmed();
    const QString lowered = trimmed.toLower();
    if (lowered == QString("true") || lowered == QString("false")) {
        setter.value = lowered;
    } else if (trimmed.startsWith(QString("smt("), Qt::CaseInsensitive)) {
        setter.value = trimmed;
    } else {
        setter.value = QString("smt(= %1 %2)").arg(variable, trimmed);
    }
    return setter;
}

QString FunctionEditDialog::solveVariableRange(const QString &variable,
                                               const QString &typeKey,
                                               const QStringList &typicalValues,
                                               QString &errorMessage) const
{
    errorMessage.clear();
    if (!m_systemEntity) {
        errorMessage = QString("未设置系统求解上下文，无法求解变量范围");
        return QString();
    }

    const QString trimmedVariable = variable.trimmed();
    if (trimmedVariable.isEmpty()) {
        errorMessage = QString("变量名称为空");
        return QString();
    }

    QString linkText = ui->editLink->text().trimmed();
    SystemStructure structure(m_systemDescription, linkText);
    if (!structure.isSystemConsistent()) {
        errorMessage = QString("当前功能链路或系统描述不自洽");
        return QString();
    }
    const QString croppedDescription = structure.getCroppedSystemDescription();
    if (croppedDescription.isEmpty()) {
        errorMessage = QString("无法构建裁剪后的系统描述");
        return QString();
    }

    const QList<TestItem> baseItems = buildBaseTestItems();
    const QString normalizedTypeKey = typeKey.trimmed();

    auto buildItemsWithValue = [&](const QString &valueExpr) {
        QList<TestItem> items = baseItems;
        // remove existing setters for same variable
        for (int i = items.size() - 1; i >= 0; --i) {
            if (items.at(i).variable.trimmed() == trimmedVariable) {
                items.removeAt(i);
            }
        }
        items.append(makeVariableSetterItem(trimmedVariable, valueExpr));
        return items;
    };

    auto checkSat = [&](const QString &valueExpr, QMap<QString, QString> *modelOut = nullptr) {
        const QList<TestItem> items = buildItemsWithValue(valueExpr);
        return m_systemEntity->satisfiabilitySolve(croppedDescription,
                                                   items,
                                                   QStringList() << trimmedVariable,
                                                   modelOut);
    };

    const auto isBoolToken = [](const QString &text) {
        const QString lowered = text.trimmed().toLower();
        return lowered == QString("true") || lowered == QString("false");
    };

    bool looksBool = normalizedTypeKey.compare(QString("Bool"), Qt::CaseInsensitive) == 0;
    if (!looksBool) {
        for (const QString &val : typicalValues) {
            if (isBoolToken(val)) {
                looksBool = true;
            } else {
                looksBool = false;
                break;
            }
        }
    }

    if (looksBool) {
        QStringList boolTypicals;
        for (const QString &val : typicalValues) {
            if (isBoolToken(val)) {
                boolTypicals.append(val.trimmed().toLower());
            }
        }
        if (boolTypicals.isEmpty()) {
            boolTypicals << QString("true") << QString("false");
        }
        for (const QString &typ : boolTypicals) {
            if (!checkSat(typ)) {
                errorMessage = QString("变量 %1 在典型值 %2 下无法满足约束").arg(trimmedVariable, typ);
                return QString();
            }
        }
        QStringList feasible;
        for (const QString &candidate : QStringList() << QString("true") << QString("false")) {
            if (checkSat(candidate)) {
                feasible.append(candidate);
            }
        }
        feasible.removeDuplicates();
        if (feasible.isEmpty()) {
            errorMessage = QString("变量 %1 在所有布尔取值下均无法满足约束").arg(trimmedVariable);
            return QString();
        }
        if (feasible.size() == 2) {
            return QString("true;false");
        }
        return feasible.join(QString(";"));
    }

    QVector<double> typicalNumbers;
    for (const QString &val : typicalValues) {
        bool ok = false;
        double num = val.trimmed().toDouble(&ok);
        if (!ok) {
            errorMessage = QString("变量 %1 的典型值 %2 不是数值").arg(trimmedVariable, val.trimmed());
            return QString();
        }
        typicalNumbers.append(num);
    }
    if (typicalNumbers.isEmpty()) {
        errorMessage = QString("变量 %1 缺少数值典型值").arg(trimmedVariable);
        return QString();
    }

    QMap<QString, QString> satModel;
    if (!checkSat(QString::number(typicalNumbers.first(), 'g', 12), &satModel)) {
        errorMessage = QString("变量 %1 在典型值 %2 下无法满足约束")
                .arg(trimmedVariable, QString::number(typicalNumbers.first(), 'g', 12));
        return QString();
    }

    rangeconfig::RangeValue baseRange = m_systemEntity->variableRangeConfigRef()
            .effectiveRange(normalizedTypeKey, trimmedVariable);
    if (!baseRange.isValid()) {
        baseRange = rangeconfig::VariableRangeConfig::defaultRange();
    }
    if (baseRange.lower > baseRange.upper) {
        std::swap(baseRange.lower, baseRange.upper);
    }

    auto isSatForValue = [&](double candidate, QString &failureMessage) {
        const QString candidateText = QString::number(candidate, 'g', 12);
        return checkSat(candidateText, nullptr) ? true : (failureMessage.clear(), false);
    };

    const double tolerance = 0.1;
    const int iterations = 24;
    QStringList intervals;

    for (double typical : typicalNumbers) {
        double clampedTypical = qBound(baseRange.lower, typical, baseRange.upper);

        QString typicalError;
        if (!isSatForValue(clampedTypical, typicalError)) {
            if (!typicalError.isEmpty()) {
                errorMessage = typicalError;
            } else {
                errorMessage = QString("变量 %1 在典型值 %2 下无法满足约束")
                                   .arg(trimmedVariable, QString::number(clampedTypical, 'g', 12));
            }
            return QString();
        }

        double lowerBound = clampedTypical;
        double upperBound = clampedTypical;

        QString boundaryError;
        if (isSatForValue(baseRange.lower, boundaryError)) {
            lowerBound = baseRange.lower;
        } else {
            double low = baseRange.lower;
            double high = clampedTypical;
            for (int i = 0; i < iterations && (high - low) > tolerance; ++i) {
                const double mid = (low + high) * 0.5;
                QString midError;
                if (isSatForValue(mid, midError)) {
                    lowerBound = mid;
                    high = mid;
                } else {
                    low = mid;
                }
            }
        }

        boundaryError.clear();
        if (isSatForValue(baseRange.upper, boundaryError)) {
            upperBound = baseRange.upper;
        } else {
            double low = clampedTypical;
            double high = baseRange.upper;
            for (int i = 0; i < iterations && (high - low) > tolerance; ++i) {
                const double mid = (low + high) * 0.5;
                QString midError;
                if (isSatForValue(mid, midError)) {
                    upperBound = mid;
                    low = mid;
                } else {
                    high = mid;
                }
            }
        }

        if (lowerBound > upperBound) {
            std::swap(lowerBound, upperBound);
        }
        intervals.append(QString("[%1, %2]").arg(QString::number(lowerBound, 'g', 6),
                                                 QString::number(upperBound, 'g', 6)));
    }

    return intervals.join(QString(";"));
}
