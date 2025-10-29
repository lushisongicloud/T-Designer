#include "selectfunctiondialog.h"
#include "ui_selectfunctiondialog.h"
#include "testability/constraint_utils.h"
#include "testability/function_catalog.h"
#include "variablerangedialog.h"

#include <QMessageBox>
#include <QPlainTextEdit>
#include <QSignalBlocker>
#include <QTextEdit>

#include <algorithm>
#include <cmath>
#include <QtGlobal>
#include <QSet>
#include <QTextDocument>

namespace {

QStringList splitComponents(const QString &text)
{
    QString normalized = text;
    normalized.replace('\n', ',');
    normalized.replace('\r', ',');
    const QStringList rawParts = normalized.split(',', QString::SkipEmptyParts);

    QStringList ordered;
    QSet<QString> seen;
    for (const QString &part : rawParts) {
        const QString trimmed = part.trimmed();
        if (trimmed.isEmpty() || seen.contains(trimmed)) {
            continue;
        }
        ordered.append(trimmed);
        seen.insert(trimmed);
    }
    return ordered;
}

QString joinComponents(const QStringList &components)
{
    return components.join(QString(","));
}

} // namespace

SelectFunctionDialog::SelectFunctionDialog(SystemEntity* systemEntity,const QString& systemDescription, const QString& functionDescription, QWidget *parent) :
    QDialog(parent),
    systemEntity(systemEntity),
    systemDescription(systemDescription),
    localFunctionDescription(functionDescription),  // Assign the functionDescription to localFunctionDescription
    mainWindow(static_cast<MainWindow *>(parent)), // 获取 MainWindow 的指针
    ui(new Ui::SelectFunctionDialog)
{
    ui->setupUi(this);
    currentConstraintIntegrityStatus = QString("未检查");
    updateConstraintIntegrityLabel(currentConstraintIntegrityStatus);
    ui->table_test->setColumnWidth(0,210);
    ui->table_test->setColumnWidth(1,220);
    ui->table_test->setColumnWidth(2,50);
    ui->table_test->setColumnWidth(3,90);
    //ui->table_test->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);
    updateFunctionTree();
    systemEntity->updateObsVarsMap(systemEntity->prepareModel(systemDescription));

    connect(ui->functionTree, &QTreeWidget::itemClicked, this, &SelectFunctionDialog::on_functionTree_itemClicked);

    ui->functionTree->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->functionTree, &QTreeWidget::customContextMenuRequested,
            this, &SelectFunctionDialog::on_contextMenuRequested);
    ui->table_FunctionDependency->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->table_FunctionDependency, &QTableWidget::customContextMenuRequested,
            this, &SelectFunctionDialog::onTableFunctionDependencyContextMenu);
    ui->textEditComponentDependency->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->textEditComponentDependency, &QWidget::customContextMenuRequested,
            this, &SelectFunctionDialog::onTextEditComponentDependencyContextMenu);

    //更新求解进度及结果
    connect(systemEntity, &SystemEntity::solvingStarted, this, &SelectFunctionDialog::onSolvingStarted);
    connect(systemEntity, &SystemEntity::solvingFinished, this, &SelectFunctionDialog::onSolvingFinished);
    connect(systemEntity, &SystemEntity::progressUpdated, this, &SelectFunctionDialog::onProgressUpdated);
    connect(systemEntity, &SystemEntity::resultEntityListUpdated, this, &SelectFunctionDialog::onResultEntityListUpdated);
    connect(systemEntity, &SystemEntity::outlierObsUpdated, this, &SelectFunctionDialog::onOutlierObsUpdated);

    connect(ui->btn_VariableRanges, &QPushButton::clicked, this, &SelectFunctionDialog::showVariableRangeDialog);
    connect(ui->btn_VariableValueSolve, &QPushButton::clicked, this, &SelectFunctionDialog::showFunctionVariableValueDialog);
    connect(ui->textEditFunctionDescription, &QPlainTextEdit::textChanged, this, [this]() {
        if (!isLoading) markConstraintIntegrityUnknown();
    });
    connect(ui->textEditLink, &QPlainTextEdit::textChanged, this, [this]() {
        if (!isLoading) markConstraintIntegrityUnknown();
    });
    connect(ui->textEditComponentDependency->document(), &QTextDocument::contentsChanged, this, [this]() {
        if (!isLoading) markConstraintIntegrityUnknown();
    });
    connect(ui->textEditAllComponent, &QPlainTextEdit::textChanged, this, [this]() {
        if (!isLoading) markConstraintIntegrityUnknown();
    });
}

//SelectFunctionDialog::~SelectFunctionDialog()
//{
//    delete ui;
//}
void SelectFunctionDialog::keyPressEvent(QKeyEvent* event) {
    if (event->key() == Qt::Key_Delete) {
        QItemSelectionModel *select = ui->table_FunctionDependency->selectionModel();
        if (select->hasSelection())
        {
            QModelIndexList selectedRows = select->selectedRows();
            for (const auto& index : selectedRows) {
                ui->table_FunctionDependency->removeRow(index.row());
            }
        }
        QItemSelectionModel *selectConstraint = ui->table_test->selectionModel();
        if (selectConstraint->hasSelection())
        {
            QModelIndexList selectedRows = selectConstraint->selectedRows();
            for (const auto& index : selectedRows) {
                ui->table_test->removeRow(index.row());
            }
        }
    }
    else {
        QDialog::keyPressEvent(event);
    }
}

void SelectFunctionDialog::resultProcessAndUpdateColor(){
    ui->table_result->setUpdatesEnabled(false); // Disable updates
    //根据诊断结果设置行的背景色
    bool hasYellowRows = false;
    int rows = ui->table_result->rowCount();
    QColor yellowBackground(255, 255, 0); // 黄色背景

    // 对所有的行进行遍历
    for(int i = 0; i < rows; ++i) {
        // 获取第一列、第二列和第三列的文本
        QString firstColumnText = ui->table_result->item(i, 0)->text();
        QString secondColumnText = ui->table_result->item(i, 1)->text();
        QString thirdColumnText = ui->table_result->item(i, 2)->text();

        // 如果第一列按逗号分隔后只有一部分，且第二列不包含"未知"
        if(firstColumnText.split(',').size() == 1 && !secondColumnText.contains("未知")) {
            hasYellowRows = true;

            // 将第三列的文本转换为概率值
            double probability = thirdColumnText.toDouble();

            // 计算颜色深度
            int depth = static_cast<int>((probability - 1.0e-7) / (1.0e-4 - 1.0e-7) * 255);
            depth = std::max(0, std::min(255, depth));  // 确保在0到255之间

            // 创建一个根据概率深度的黄色背景色
            QColor yellowBackground(255, 255 - depth, 0);

            // 将该行背景色改为黄色
            for(int j = 0; j < ui->table_result->columnCount(); ++j) {
                ui->table_result->item(i, j)->setBackgroundColor(yellowBackground);
            }
        }
    }
    ui->table_result->setUpdatesEnabled(true); // Re-enable updates
}

void SelectFunctionDialog::onProgressUpdated(int progress) {
    ui->progressBar->setValue(progress);
}

void SelectFunctionDialog::onResultEntityListUpdated(const QList<resultEntity>& resultEntityList) {
    ui->table_result->setUpdatesEnabled(false); // Disable updates

    for (int i = lastResultEntityIndex; i < resultEntityList.size(); ++i) {
        const resultEntity& result = resultEntityList[i];
        insertIntoResultTable(result.getComponentNames(),result.getFailureModes(),result.getProbability());
    }
    ui->table_result->resizeColumnsToContents();//调整列宽
    ui->table_result->sortItems(2, Qt::DescendingOrder);//按概率对结果排序

    lastResultEntityIndex = resultEntityList.size(); // Update the last index
    ui->table_result->setUpdatesEnabled(true); // Re-enable updates
}

void SelectFunctionDialog::onOutlierObsUpdated(const QMap<QString, double>& outlierObs)
{

}

void SelectFunctionDialog::onSolvingStarted() {
    ui->progressBar->setValue(0);

    // 清空表格
    ui->table_result->setRowCount(0);
    lastResultEntityIndex =0;
}

void SelectFunctionDialog::onSolvingFinished(QStringList ans) {
    for (QStringList::iterator it = ans.begin();
         it != ans.end(); ++it) {
        QString current = *it;
        //ui->textEditConflictSets->append(current);
    }

    if(ans.size()==0){
        //ui->textEditConflictSets->append("系统正常");
    }
    resultProcessAndUpdateColor();

    //对localResultEntityList按概率由高到低排序
    //    std::sort(localResultEntityList.begin(), localResultEntityList.end(),
    //              [](const resultEntity &a, const resultEntity &b) {
    //        return a.getProbability() > b.getProbability();
    //    });

    //labViewCord->setText("求解时间：" + QString::number(timeSlove.elapsed()/1000.0));
}

void SelectFunctionDialog::checkDuplicateAndUpdateColor() {
    for (int i = 0; i < ui->table_test->rowCount(); ++i) {
        MyComboBox *cb = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(i, 0));
        if (cb != nullptr) {
            QString variable = cb->currentText();
            bool duplicateFound = false;

            for (int j = 0; j < testItemList.size(); ++j) {
                if (i != j && testItemList[j].variable == variable) {
                    duplicateFound = true;
                    MyComboBox *cbJ = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(j, 0));
                    if (cbJ) {
                        cbJ->setStyleSheet("QComboBox { background-color: red; }");
                        cb->setStyleSheet("QComboBox { background-color: red; }");
                    }
                    break;
                }
            }

            QString style = cb->styleSheet();
            if (!duplicateFound && style.contains("background-color: red")) {
                cb->setStyleSheet("QComboBox { background-color: white; }");
            }
        }
    }
}

QString SelectFunctionDialog::generateQStringFromFunctionDependencyTable() {
    QStringList functionDependencyList;
    for (int row = 0; row < ui->table_FunctionDependency->rowCount(); ++row) {
        MyComboBox* cbComponent = qobject_cast<MyComboBox*>(ui->table_FunctionDependency->cellWidget(row, 0));
        MyComboBox* cbFunction = qobject_cast<MyComboBox*>(ui->table_FunctionDependency->cellWidget(row, 1));
        QTableWidgetItem* relativePortItem = ui->table_FunctionDependency->item(row, 2); // 获取第三列的相关端口

        if (cbComponent && cbFunction && relativePortItem) {
            // 添加器件名称、功能名称和相关端口到结果字符串中
            functionDependencyList.append(cbComponent->currentText() + "," + cbFunction->currentText() + "," + relativePortItem->text());
        }
    }
    return functionDependencyList.join(";");
}

void SelectFunctionDialog::updateFunctionDependencyTable(const QString &componentAndFunctionString) {
    ui->table_FunctionDependency->setUpdatesEnabled(false); // Disable updates

    ui->table_FunctionDependency->setRowCount(0);

    QStringList tuples = componentAndFunctionString.split(';', QString::SkipEmptyParts);
    for(const QString& tuple : tuples) {
        insertIntoFunctionDependencyTable(tuple);
    }

    ui->table_FunctionDependency->resizeColumnsToContents();
    ui->table_FunctionDependency->setUpdatesEnabled(true); // Re-enable updates
}

void SelectFunctionDialog::insertIntoFunctionDependencyTable(const QString &componentAndFunctionString){
    QStringList components = componentAndFunctionString.split(',');
    if (components.size() < 2 || (components[0].isEmpty() && components[1].isEmpty()))
    {
        // 错误处理：如果该三元组没有至少两个元素，或两个元素都为空，则继续处理下一个
        return;
    }
    QString component = components[0];
    QString function = components[1];
    QString relativePorts = components.size() > 2 ? components[2] : "";

    int crrRow = ui->table_FunctionDependency->rowCount();
    ui->table_FunctionDependency->insertRow(crrRow);

    MyComboBox *cbComponentName = new MyComboBox();
    cbComponentName->setList(systemEntity->componentNameList);
    cbComponentName->setMyCurrentText(component);
    cbComponentName->setStyleSheet("QComboBox { background-color: white; }");
    QTableWidgetItem* item = new QTableWidgetItem(component);
    cbComponentName->setTableItem(item);
    ui->table_FunctionDependency->setItem(crrRow, 0, item);
    ui->table_FunctionDependency->setCellWidget(crrRow, 0, cbComponentName);

    // 使cbFunctionName->setList()为当前cbComponentName选中的器件所对应的所有功能（通过查询functionActuatorNameMap可知）
    // 如果当前cbComponentName选中的器件在functionActuatorNameMap没有对应的功能，则使cbFunctionName->setList()为全部所有功能(functionNameList)
    MyComboBox *cbFunctionName = new MyComboBox();
    QStringList functionList = functionActuatorNameMap.keys(component);
    if(!functionList.isEmpty()){
        cbFunctionName->setList(functionList);
    } else {
        cbFunctionName->setList(functionNameList);
    }
    QString functionTooltip=functionActuatorConstraintMap.value(function).join(" = ");//功能提示：所选功能变量约束(constraint)中类型(type)为“功能执行器”项的值（value）
    cbFunctionName->setMyCurrentText(function);
    cbFunctionName->setStyleSheet("QComboBox { background-color: white; }");
    QTableWidgetItem* item2 = new QTableWidgetItem(function);
    item2->setToolTip(functionTooltip); // 设置功能的悬停提示
    cbFunctionName->setTableItem(item2);
    ui->table_FunctionDependency->setItem(crrRow, 1, item2);
    ui->table_FunctionDependency->setCellWidget(crrRow, 1, cbFunctionName);

    // 处理新添加的相关端口部分
    QTableWidgetItem *relativePortItem = new QTableWidgetItem(relativePorts);
    ui->table_FunctionDependency->setItem(crrRow, 2, relativePortItem);
}

void SelectFunctionDialog::insertIntoResultTable(const QString& componentNames, const QString& failureModes, const double& probability)
{
    // Insert a new row at the end of the table
    int newRow = ui->table_result->rowCount();
    ui->table_result->insertRow(newRow);

    // Create new items
    QTableWidgetItem *item1 = new QTableWidgetItem(componentNames);
    QTableWidgetItem *item2 = new QTableWidgetItem(failureModes);
    NumericTableWidgetItem *item3 = new NumericTableWidgetItem(QString::number(probability, 'e', 1));
    //item3->setData(Qt::DisplayRole, pFailure);

    // Set the items in the table
    ui->table_result->setItem(newRow, 0, item1);
    ui->table_result->setItem(newRow, 1, item2);
    ui->table_result->setItem(newRow, 2, item3);

    //    resultEntity resultItem;
    //    resultItem.setResult(componentNames,failureModes,probability);
    //    localResultEntityList.append(resultItem);
}

void SelectFunctionDialog::insertIntoFunctionTable(const QString& variable, const QString& value, const double& confidence, const QString& constrainType)
{
    ui->table_test->disconnect(SIGNAL(itemChanged(QTableWidgetItem*)));

    int crrRow = ui->table_test->rowCount();
    ui->table_test->insertRow(crrRow);

    MyComboBox *CbTestVal = new MyComboBox(); // variable
    MyComboBox *CbTestVal2 = new MyComboBox();  // value
    double mConfidence = confidence;
    QString varType = "";
    QString variableTooltip="";
    QString valueTooltip="";

    CbTestVal->setStyleSheet("QComboBox { background-color: white; }");
    if(constrainType=="依赖功能")
    {
        CbTestVal->setList(functionNameList);
        CbTestVal->setMyCurrentText(variable);
        varType = "function";
        CbTestVal2->setList({"功能正常","功能异常"});

        if(value!="功能正常" && value!="功能异常")CbTestVal2->setCurrentText("功能正常");
        else CbTestVal2->setCurrentText(value);

        CbTestVal->lineEdit()->home(false);// 设置光标到行编辑的开始位置,避免功能名称太长只显示尾部

        variableTooltip=functionActuatorConstraintMap.value(variable).join(" = ");//功能提示：所选功能变量约束(constraint)中类型(type)为“功能执行器”项的值（value）
        valueTooltip=variableTooltip;
    }
    else
    {
        CbTestVal->setList(systemEntity->obsVarsList);
        varType = systemEntity->obsVarsMap[variable];
        CbTestVal->setMyCurrentText(variable);

        if (varType == "Bool") {
            CbTestVal2->setList(QStringList({"true", "false"}));
            CbTestVal2->setCurrentText(value);

        } else if (varType == "(Array Int Real)") {
            if(CbTestVal->currentText().endsWith("u")) CbTestVal2->setList(MainWindow::obsTemplates["AC380_3P_u"]);
            if(CbTestVal->currentText().endsWith("i")) CbTestVal2->setList(MainWindow::obsTemplates["AC380_3P_i"]);
            CbTestVal2->setCurrentText(value);
        } else if (varType == "Real") {
            if(CbTestVal->currentText().endsWith("u")) CbTestVal2->setList(MainWindow::obsTemplates["AC220_1P_u"]);
            if(CbTestVal->currentText().endsWith("i")) CbTestVal2->setList(MainWindow::obsTemplates["AC220_1P_i"]);
            if(CbTestVal->currentText().endsWith("p")) CbTestVal2->setList(MainWindow::obsTemplates["Hydro_p"]);
            if(CbTestVal->currentText().endsWith("f")) CbTestVal2->setList(MainWindow::obsTemplates["Hydro_f"]);
            CbTestVal2->setCurrentText(value);
        } else {
            CbTestVal2->setList(QStringList({value}));
            CbTestVal2->setCurrentText(value);
        }
    }
    if(confidence ==0.0)
    {
        if(varType == "Bool")
        {
            if(constrainType == "功能执行器" )mConfidence=1.0;
            if(constrainType != "功能执行器" )mConfidence=0.5;
        }
        //ToDo
        else if(varType == "function")//约束描述类型为"依赖功能"的，先暂定置信度为0.5  //TODO 后面改为根据功能的失效概率计算初始置信度
        {
            mConfidence=0.1;
        }
        else
        {
            if(constrainType == "功能执行器" )mConfidence=1.0;
            if(constrainType != "功能执行器" )mConfidence=0.1;
        }
    }
    QTableWidgetItem* item = new QTableWidgetItem(variable);
    if(variableTooltip!="")item->setToolTip(variableTooltip); // 设置变量的悬停提示
    CbTestVal->setTableItem(item);
    ui->table_test->setItem(crrRow, 0, item); // Set QTableWidgetItem before QComboBox
    ui->table_test->setCellWidget(crrRow, 0, CbTestVal); // Set QComboBox after QTableWidgetItem
    connect(CbTestVal, &MyComboBox::editFinish, this, &SelectFunctionDialog::onTableFunctionItemChanged);

    QTableWidgetItem* item2 = new QTableWidgetItem(value);
    if(valueTooltip!="")item2->setToolTip(valueTooltip); // 设置值的悬停提示
    CbTestVal2->setTableItem(item2);
    ui->table_test->setItem(crrRow, 1, item2);
    ui->table_test->setCellWidget(crrRow, 1, CbTestVal2);
    connect(CbTestVal2, &MyComboBox::editFinish, this, &SelectFunctionDialog::onTableFunctionItemChanged);

    ui->table_test->setItem(crrRow,2,new QTableWidgetItem(QString::number(mConfidence)));

    // 创建下拉框
    MyComboBox *CbTestType = new MyComboBox();  // create a new MyComboBox
    CbTestType->setList(QStringList({ "一般变量", "功能执行器","边界条件","依赖功能" }));
    CbTestType->setCurrentText(constrainType);
    QTableWidgetItem* item3 = new QTableWidgetItem(constrainType);
    CbTestType->setTableItem(item3);
    ui->table_test->setItem(crrRow, 3, item3);
    ui->table_test->setCellWidget(crrRow, 3, CbTestType);
    connect(CbTestType, &MyComboBox::editFinish, this, &SelectFunctionDialog::onTableFunctionItemChanged);

    TestItem newItem;
    newItem.variable = variable;
    newItem.value = value;
    newItem.confidence = mConfidence;
    newItem.testType = constrainType;
   newItem.checkState = (constrainType == "功能执行器") ? Qt::Checked : Qt::Unchecked;
   testItemList.append(newItem);

   if(variable!="")checkDuplicateAndUpdateColor();
    if (!isLoading) {
        markConstraintIntegrityUnknown();
    }
}
void SelectFunctionDialog::onTableFunctionItemChanged(QTableWidgetItem* item) {
    ui->table_test->disconnect(SIGNAL(itemChanged(QTableWidgetItem*)));

    int row = item->row();
    //qDebug()<<"onTableFunctionItemChanged row: "<<row;
    MyComboBox *CbTestVal1 = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 0));
    MyComboBox *CbTestVal2 = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 1));
    MyComboBox *CbTestVal4 = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 3));

    QString varType =  systemEntity->obsVarsMap[testItemList[row].variable];

    if(row < testItemList.size()) {
        switch(item->column()) {
        case 0:
            if(testItemList[row].variable == CbTestVal1->currentText())break;
            testItemList[row].variable = CbTestVal1->currentText();
            varType =  systemEntity->obsVarsMap[testItemList[row].variable];
            //qDebug()<<"TableTestItemChanged    current variable:"<<testItemList[row].variable;
            // Based on the new variable, update the second column.
            //qDebug()<<"type:"<<type;

            if(CbTestVal4->currentText()=="依赖功能")
            {
                if(CbTestVal2->currentText()!="功能正常" && CbTestVal2->currentText()!="功能异常")
                {
                    CbTestVal2->setList({"功能正常","功能异常"});
                    CbTestVal2->setCurrentText("功能正常");
                }
                CbTestVal1->lineEdit()->home(false);// 设置光标到行编辑的开始位置,避免功能名称太长只显示尾部
                testItemList[row].confidence = 0.1;
            }
            else
            {
                if (varType == "Bool") {
                    CbTestVal2->setList(QStringList({"true", "false"}));
                    if(testItemList[row].checkState == Qt::Checked) testItemList[row].confidence = 1.0;
                    if(testItemList[row].checkState == Qt::Unchecked) testItemList[row].confidence = 0.5;
                } else if (varType == "(Array Int Real)") {
                    if(testItemList[row].variable.endsWith("u")) CbTestVal2->setList(MainWindow::obsTemplates["AC380_3P_u"]);
                    if(testItemList[row].variable.endsWith("i")) CbTestVal2->setList(MainWindow::obsTemplates["AC380_3P_i"]);
                    if(testItemList[row].checkState == Qt::Checked) testItemList[row].confidence = 1.0;
                    if(testItemList[row].checkState == Qt::Unchecked) testItemList[row].confidence = 0.1;
                } else if (varType == "Real") {
                    if(testItemList[row].variable.endsWith("u")) CbTestVal2->setList(MainWindow::obsTemplates["AC220_1P_u"]);
                    if(testItemList[row].variable.endsWith("i")) CbTestVal2->setList(MainWindow::obsTemplates["AC220_1P_i"]);
                    if(testItemList[row].variable.endsWith("p")) CbTestVal2->setList(MainWindow::obsTemplates["Hydro_p"]);
                    if(testItemList[row].variable.endsWith("f")) CbTestVal2->setList(MainWindow::obsTemplates["Hydro_f"]);
                    if(testItemList[row].checkState == Qt::Checked) testItemList[row].confidence = 1.0;
                    if(testItemList[row].checkState == Qt::Unchecked) testItemList[row].confidence = 0.1;
                } else {
                    CbTestVal2->setList(QStringList({""}));
                }
            }
            ui->table_test->item(row, 2)->setText(QString::number(testItemList[row].confidence));
            checkDuplicateAndUpdateColor();

            break;
        case 1:
            testItemList[row].value = CbTestVal2->currentText();
            //qDebug()<<"testItemList[row].value:"<<testItemList[row].value;
            break;
        case 2:
            testItemList[row].confidence = item->text().toDouble();
            break;
        case 3:
            if(testItemList[row].testType == CbTestVal4->currentText())break;
            testItemList[row].testType = CbTestVal4->currentText();
            //如果类型为"依赖功能"，则："变量"改为功能列表;"约束值"改为"功能正常"，"功能异常"
            if(testItemList[row].testType == "依赖功能")
            {
                CbTestVal1->setList(functionNameList); //"变量"改为功能列表
                CbTestVal2->setList({"功能正常","功能异常"});
            }
            else
            {
                CbTestVal1->setList(systemEntity->obsVarsList);
                CbTestVal2->setList({});
            }
            testItemList[row].variable = CbTestVal1->currentText();
            varType =  systemEntity->obsVarsMap[testItemList[row].variable];
            testItemList[row].checkState = (testItemList[row].testType == "功能执行器") ? Qt::Checked : Qt::Unchecked;
            if(testItemList[row].checkState == Qt::Checked)
            {
                if(varType == "Bool")testItemList[row].confidence = 1.0;
                else testItemList[row].confidence = 1.0;
            }
            else
            {
                if(varType == "Bool")testItemList[row].confidence = 0.5;
                else testItemList[row].confidence = 0.1;
            }
            ui->table_test->item(row, 2)->setText(QString::number(testItemList[row].confidence));
            break;
        }
    }
    connect(ui->table_test, SIGNAL(itemChanged(QTableWidgetItem*)), this, SLOT(onTableFunctionItemChanged(QTableWidgetItem*)));
    QString tooltip;
    if(testItemList[row].value=="功能正常")tooltip=functionActuatorConstraintMap.value(testItemList[row].variable).join(" = ");//功能提示：所选功能变量约束(constraint)中类型(type)为“功能执行器”项的值（value）
    if(testItemList[row].value=="功能异常")tooltip=functionActuatorConstraintMap.value(testItemList[row].variable).join(" != ");//功能提示：所选功能变量约束(constraint)中类型(type)为“功能执行器”项的值（value）
    if(tooltip!="")
    {
        CbTestVal1->tableItem->setToolTip(tooltip); // 设置值的悬停提示
        CbTestVal2->tableItem->setToolTip(tooltip);
    }
    if (!isLoading) {
        markConstraintIntegrityUnknown();
    }
}

void SelectFunctionDialog::on_btn_AddObs_clicked() {
    insertIntoFunctionTable("","", 0.0,"一般变量");
    if (!isLoading) {
        markConstraintIntegrityUnknown();
    }
    //ui->table_test->resizeColumnsToContents();
}

void SelectFunctionDialog::on_btn_DelObs_clicked() {
    QItemSelectionModel *select = ui->table_test->selectionModel();

    if(select->hasSelection())
    {
        QModelIndexList selectedRows = select->selectedRows();
        bool redRowDeleted = false;

        QList<int> rowsToDelete;
        for(const auto& index : selectedRows) {
            rowsToDelete.append(index.row());
        }

        std::sort(rowsToDelete.begin(), rowsToDelete.end(), std::greater<int>());

        for(int row : rowsToDelete) {
            MyComboBox *cb = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 0));
            if (cb) {
                if (cb->styleSheet().contains("background-color: red")) {
                    redRowDeleted = true;
                }
            }

            ui->table_test->removeRow(row);
            testItemList.removeAt(row);
        }

        if (redRowDeleted) {
            checkDuplicateAndUpdateColor();
        }
    }
    if (!isLoading) {
        markConstraintIntegrityUnknown();
    }
}

void SelectFunctionDialog::on_functionTree_itemClicked(QTreeWidgetItem *item, int column) {
    // 这个函数会在用户点击树形列表中的一个节点时被调用。
    saveCurrentVariableConfigToMap();
    currentFunctionName = item->text(0);
    ensureFunctionVariableConfig(currentFunctionName);
    currentFunctionVariableConfig = functionVariableConfigMap.value(currentFunctionName);
    // 获取节点数据
    QString functionData = item->data(0, Qt::UserRole).toString();

    // 用数据更新界面
    QDomDocument doc;
    if (!doc.setContent(functionData)) {
        qDebug() << "Failed to parse function data";
        qDebug()<<"functionData:"<<qPrintable(functionData);
        return;
    }
    isLoading = true;

    QDomElement functionDefine = doc.firstChildElement(QString("functiondefine"));
    if (!functionDefine.isNull()) {
        currentFunctionVariableConfig = functionvalues::FunctionVariableConfig::fromXml(
                    functionDefine.firstChildElement(QStringLiteral("variableValueConfig")));
        functionVariableConfigMap.insert(currentFunctionName, currentFunctionVariableConfig);
    }

    // 更新函数描述
    QString functionDesc = functionDefine.firstChildElement("describe").text();
    ui->textEditFunctionDescription->setPlainText(functionDesc);

    // 更新求解空间
    QString link = functionDefine.firstChildElement("link").text();
    ui->textEditLink->setPlainText(link);

    // 更新依赖信息
    QString functionDependency = functionDefine.firstChildElement("dependency").firstChildElement("function").text();
    QString componentDependency = functionDefine.firstChildElement("dependency").firstChildElement("component").text();
    ui->textEditComponentDependency->setPlainText(componentDependency);
    //functionDependency格式：器件、功能、相关端口之间用逗号分隔，相关端口之间用空格分隔，器件功能端口三元组之间用分号分隔，且器件功能端口三元组之中的componentName或者functionName其中一个可以为空，不能两个同时为空
    //例子："componentName1,functionName1,relativePort1  relativePort2 relativePort3 ...;componentName2,functionName2,relativePort1  relativePort2 ...; , , ,;......"
    updateFunctionDependencyTable(functionDependency);
    //ui->textEditFunctionDependency->setPlainText(functionDependency);

    //更新全部相关器件
    QString allComponent = functionDefine.firstChildElement("dependency").firstChildElement("allComponent").text();
    ui->textEditAllComponent->setPlainText(allComponent);

    //更新故障属性
    QString attributeString = doc.firstChildElement("functiondefine").firstChildElement("attribute").text();
    QStringList attributeList = attributeString.split(",");
    bool persistent = true;
    QString faultProbability;
    int index = 0;
    for(const QString &attribute : attributeList) {
        if(index==0)persistent = (attribute == "NotPersistent") ? false : true;
        if(index==1)faultProbability =attribute;
        index++;
    }
    if(persistent)ui->checkBoxPersistent->setCheckState(Qt::Checked);
    else ui->checkBoxPersistent->setCheckState(Qt::Unchecked);
    ui->textEditFaultProbability->setPlainText(faultProbability);

    // 更新约束表格
    testItemList.clear();
    ui->table_test->setRowCount(0);
    QDomElement constraint = functionDefine.firstChildElement(QString("constraint"));
    while (!constraint.isNull()) {

        // 解析信任度
        double confidence = constraint.firstChildElement("confidence").text().toDouble();

        QStringList validTypes = QStringList({"一般变量", "功能执行器", "边界条件", "依赖功能"});
        QString constrainType = constraint.firstChildElement("type").text();
        if (!validTypes.contains(constrainType)) {
            constrainType = "一般变量";
        }
        // 插入到表格中
        insertIntoFunctionTable(constraint.firstChildElement("variable").text(),
                                constraint.firstChildElement("value").text(),
                                confidence,
                                constrainType);

        constraint = constraint.nextSiblingElement(QString("constraint"));
    }

    //更新离线求解结果表格
    localResultEntityList.clear();
    ui->table_result->setRowCount(0);
    QDomNodeList results = doc.firstChildElement("functiondefine").elementsByTagName("offlineSolveResult");
    //qDebug()<<"results.size():"<<results.size();
    for (int i = 0; i < results.size(); ++i) {
        QDomElement result = results.at(i).toElement();
        //qDebug().noquote().nospace()<<"offlineSolveResult for insertIntoResultTable:"<<result.text();

        // 解析信任度
        double probability = result.firstChildElement("probability").text().toDouble();

        // 插入到表格中
        insertIntoResultTable(result.firstChildElement("componentNames").text(),
                              result.firstChildElement("failureModes").text(),
                              probability);

        //更新localResultEntityList
        resultEntity resultItem;
        resultItem.setResult(result.firstChildElement("componentNames").text(),
                             result.firstChildElement("failureModes").text(),
                             probability);
        localResultEntityList.append(resultItem);
    }
    resultProcessAndUpdateColor();
    isLoading = false;

    currentConstraintIntegrityStatus = functionConstraintIntegrityMap.value(currentFunctionName, QString("未检查"));
    updateConstraintIntegrityLabel(currentConstraintIntegrityStatus);
}


QDomDocument createFunctionXML(const QString& functionName,
                               const QString& functionDesc,
                               const QString& link,
                               const QString& functionDependency,
                               const QString& componentDependency,
                               const QString& allComponent,
                               const QString& attributeString,
                               const QString& constraintIntegrity,
                               const QList<TestItem>& testItemList,
                               const QList<resultEntity>& resultEntityList,
                               const functionvalues::FunctionVariableConfig &variableConfig)
{
    QDomDocument doc;
    QDomElement functionElement = doc.createElement("functiondefine");

    // 添加功能名称
    QDomElement nameElement = doc.createElement("name");
    nameElement.appendChild(doc.createTextNode(functionName));
    functionElement.appendChild(nameElement);

    // 添加求解空间
    QDomElement linkElement = doc.createElement("link");
    linkElement.appendChild(doc.createTextNode(link));
    functionElement.appendChild(linkElement);

    // 添加依赖功能
    QDomElement dependencyElement = doc.createElement("dependency");
    QDomElement functionDependencyElement = doc.createElement("function");//添加依赖功能
    functionDependencyElement.appendChild(doc.createTextNode(functionDependency));
    dependencyElement.appendChild(functionDependencyElement);
    QDomElement componentDependencyElement = doc.createElement("component");//添加功能主链相关器件
    componentDependencyElement.appendChild(doc.createTextNode(componentDependency));
    dependencyElement.appendChild(componentDependencyElement);
    QDomElement allComponentDependencyElement = doc.createElement("allComponent");//添加功能所有相关器件
    allComponentDependencyElement.appendChild(doc.createTextNode(allComponent));
    dependencyElement.appendChild(allComponentDependencyElement);
    functionElement.appendChild(dependencyElement);

    // 添加功能描述
    QDomElement describeElement = doc.createElement("describe");
    describeElement.appendChild(doc.createTextNode(functionDesc));
    functionElement.appendChild(describeElement);

    //添加功能属性
    QDomElement attributeElement = doc.createElement("attribute");
    attributeElement.appendChild(doc.createTextNode(attributeString));
    functionElement.appendChild(attributeElement);

    QDomElement integrityElement = doc.createElement("constraintIntegrity");
    integrityElement.appendChild(doc.createTextNode(constraintIntegrity));
    functionElement.appendChild(integrityElement);

    // 添加每个约束
    for (const auto &item : testItemList) {
        QDomElement constraintElement = doc.createElement("constraint");

        // 添加变量名称
        QDomElement variableElement = doc.createElement("variable");
        variableElement.appendChild(doc.createTextNode(item.variable));
        constraintElement.appendChild(variableElement);

        // 添加约束关系
        QDomElement valueElement = doc.createElement("value");
        valueElement.appendChild(doc.createTextNode(item.value));
        constraintElement.appendChild(valueElement);

        // 添加置信度
        QDomElement confidenceElement = doc.createElement("confidence");
        confidenceElement.appendChild(doc.createTextNode(QString::number(item.confidence)));
        constraintElement.appendChild(confidenceElement);

        // 添加执行器
        //        QDomElement actuatorElement = doc.createElement("actuator");
        //        actuatorElement.appendChild(doc.createTextNode(item.checkState ? "true" : "false"));
        //        constraintElement.appendChild(actuatorElement);

        //添加变量类型 0-一般变量 1-功能执行器 2-边界条件 3-依赖功能
        QDomElement typeElement = doc.createElement("type");
        typeElement.appendChild(doc.createTextNode(item.testType));
        constraintElement.appendChild(typeElement);

        // 将约束元素添加到功能元素
        functionElement.appendChild(constraintElement);
    }

    //添加离线求解结果
    for (const auto& result : resultEntityList) {
        QDomElement resultElement = doc.createElement("offlineSolveResult");

        // 添加器件名称
        QDomElement componentNamesElement = doc.createElement("componentNames");
        componentNamesElement.appendChild(doc.createTextNode(result.getComponentNames()));
        resultElement.appendChild(componentNamesElement);

        // 添加故障模式
        QDomElement failureModesElement = doc.createElement("failureModes");
        failureModesElement.appendChild(doc.createTextNode(result.getFailureModes()));
        resultElement.appendChild(failureModesElement);

        // 添加故障概率
        QDomElement probabilityElement = doc.createElement("probability");
        probabilityElement.appendChild(doc.createTextNode(QString::number(result.getProbability())));
        resultElement.appendChild(probabilityElement);

        // 将约束元素添加到功能元素
        functionElement.appendChild(resultElement);
    }

    // 添加变量取值配置
    QDomElement variableConfigElement = variableConfig.toXml(doc);
    if (!variableConfigElement.isNull() && variableConfigElement.hasChildNodes()) {
        functionElement.appendChild(variableConfigElement);
    }

    // 将功能元素添加到文档
    doc.appendChild(functionElement);

    return doc;
}

void SelectFunctionDialog::getAllFunctionNames(QTreeWidgetItem *item, QStringList &functionNames)
{
    functionNames << item->text(0);
    //    for (int i = 0; i < item->childCount(); ++i) {
    //        getAllFunctionNames(item->child(i), functionNames);
    //    }
}

void SelectFunctionDialog::addFunction(bool isSubFunction) {
    if(isSubFunction){
        // 检查是否选中了一个节点
        if (!ui->functionTree->currentItem()) {
            QMessageBox::warning(this, "提示", "未选中父节点");
            return;
        }
    }

    // 获取所有的功能名称以检查是否重复并获取当前的功能数量
    QStringList functionNames;
    for (int i = 0; i < ui->functionTree->topLevelItemCount(); ++i) {
        getAllFunctionNames(ui->functionTree->topLevelItem(i), functionNames);
    }

    // 自动生成功能名称
    QString functionName = "功能" + QString::number(functionNames.count() + 1)+"_";

    // 创建并设置输入对话框
    QInputDialog *inputDialog = new QInputDialog(this);
    inputDialog->setLabelText(tr("功能名称:"));
    inputDialog->setTextValue(functionName);
    inputDialog->setWindowTitle(tr("输入功能名称"));
    inputDialog->setWindowFlags(inputDialog->windowFlags() & ~Qt::WindowContextHelpButtonHint);
    if (inputDialog->exec() != QDialog::Accepted || inputDialog->textValue().isEmpty())
    {
        delete inputDialog;
        return; // 如果用户点击了取消或输入的名称为空，那么直接返回
    }
    functionName = inputDialog->textValue();
    delete inputDialog;

    // 检查新的功能名称是否重复
    if (functionNames.contains(functionName)) {
        // 如果名称重复，可以弹出警告对话框并返回
        QMessageBox::warning(this, "提示", "功能名已存在");
        return;
    }

    // 获取当前的功能描述、依赖和测试项列表
    QString functionDesc = ui->textEditFunctionDescription->toPlainText();
    QString link = ui->textEditLink->toPlainText();
    //QString dependency = ui->textEditDependency->toPlainText();
    QString functionDependency = generateQStringFromFunctionDependencyTable();
    QString componentDependency = ui->textEditComponentDependency->toPlainText();
    QString allComponentDependency = ui->textEditAllComponent->toPlainText();
    // 获取 checkBoxPersistent 的状态并转换为字符串
    QString attributeString = ui->checkBoxPersistent->isChecked() ? "Persistent" : "NotPersistent";
    attributeString+= ","+ui->textEditFaultProbability->toPlainText();

    // 创建新的功能并添加到选中的节点下
    QTreeWidgetItem *newItem = new QTreeWidgetItem();
    newItem->setText(0, functionName);

    QString constraintStatus = QString("未检查");
    functionConstraintIntegrityMap.insert(functionName, constraintStatus);
    if (functionInfoMap.contains(functionName)) {
        functionInfoMap[functionName].constraintIntegrity = constraintStatus;
    }
    functionvalues::FunctionVariableConfig emptyConfig;
    functionVariableConfigMap.insert(functionName, emptyConfig);
    // 使用createFunctionXML生成QDomDocument
    QDomDocument doc = createFunctionXML(functionName,
                                         functionDesc,
                                         link,
                                         functionDependency,
                                         componentDependency,
                                         allComponentDependency,
                                         attributeString,
                                         constraintStatus,
                                         testItemList,
                                         localResultEntityList,
                                         emptyConfig);

    // 将XML保存到树形列表节点的data中
    newItem->setData(0, Qt::UserRole, doc.toString());


    if(isSubFunction)ui->functionTree->currentItem()->addChild(newItem);
    else ui->functionTree->addTopLevelItem(newItem);
}

void SelectFunctionDialog::on_btn_AddFunc_clicked()
{
    addFunction(false);
}

void SelectFunctionDialog::on_btn_UpdateSubFunc_clicked()
{
    //初始化变量
    functionNameList.clear();
    functionActuatorNameMap.clear();
    functionConstraintsMap.clear();
    functionLinkMap.clear();
    functionComponentDependencyMap.clear();
    functionAllComponentMap.clear();
    functionDependencyMap.clear();
    functionFaultProbabilityMap.clear();
    functionInfoMap.clear();
    functionVariableConfigMap.clear();

    // 遍历所有的顶级项目并处理
    for (int i = 0; i < ui->functionTree->topLevelItemCount(); ++i) {
        QTreeWidgetItem *item = ui->functionTree->topLevelItem(i);
        item->takeChildren(); //先清除其所有子节点
        processTreeItem(item);
        FunctionInfo mFunc;
        mFunc.functionName = item->text(0);
        functionNameList.append(mFunc.functionName); //遍历所有顶级项目，并将节点名称加入FunctionNameList
        //将每个功能的testItemList中type=="功能执行器"的变量名称作为actuatorNameList的项
        // 获取功能的XML文档
        QDomDocument doc;
        doc.setContent(item->data(0, Qt::UserRole).toString());

        //更新功能相关信息
        QDomElement functionDefine = doc.firstChildElement("functiondefine");
        loadFunctionVariableConfig(mFunc.functionName, functionDefine);

        QString link = functionDefine.firstChildElement("link").text();
        mFunc.link = link;
        functionLinkMap.insert(mFunc.functionName, link);

        QString componentDependency = functionDefine.firstChildElement("dependency").firstChildElement("component").text();
        mFunc.componentDependency = componentDependency;
        functionComponentDependencyMap.insert(mFunc.functionName, componentDependency);

        QString allComponent = functionDefine.firstChildElement("dependency").firstChildElement("allComponent").text();
        mFunc.allRelatedComponent = allComponent;
        const QStringList parsedAll = splitComponents(allComponent);
        if (!parsedAll.isEmpty()) {
            mFunc.allComponentList = parsedAll;
        } else {
            const QStringList fallback = splitComponents(functionDefine.firstChildElement("dependency").firstChildElement("component").text());
            if (!fallback.isEmpty()) {
                mFunc.allComponentList = fallback;
            } else {
                mFunc.allComponentList = splitComponents(link);
            }
        }
        functionAllComponentMap.insert(mFunc.functionName, joinComponents(mFunc.allComponentList));

        //functionDependency格式为:器件、功能、相关端口之间用逗号分隔，相关端口之间用空格分隔，器件功能端口三元组之间用分号分隔，且器件功能端口三元组之中的componentName或者functionName其中一个可以为空，不能两个同时为空
        //例如："componentName1,functionName1,relativePort1  relativePort2 relativePort3 ...;componentName2,functionName2,relativePort1  relativePort2 ...; , , ,;......"
        QString functionDependency = functionDefine.firstChildElement("dependency").firstChildElement("function").text();
        mFunc.functionDependency = functionDependency;
        functionDependencyMap.insert(mFunc.functionName, functionDependency);

        QString attributeString = functionDefine.firstChildElement("attribute").text();
        QStringList attributeList = attributeString.split(",");
        QString faultProbability;
        bool persistent = true;
        if(attributeList.size() > 1){
            faultProbability = attributeList.at(1);
            persistent = (attributeList.at(0) == "NotPersistent") ? false : true;
        }else qDebug()<<"Error: UpdateSubFunc attributeList.size() <= 1";
        mFunc.persistent = persistent;
        mFunc.faultProbability = faultProbability.toDouble();
        functionFaultProbabilityMap.insert(mFunc.functionName, mFunc.faultProbability);
        QString integrityText = functionDefine.firstChildElement("constraintIntegrity").text().trimmed();
        if (integrityText.isEmpty()) {
            integrityText = QString("未检查");
        }
        functionConstraintIntegrityMap.insert(mFunc.functionName, integrityText);
        mFunc.constraintIntegrity = integrityText;

        // 获取constraints
        QDomNodeList constraints = doc.elementsByTagName("constraint");
        QList<TestItem> functionTestItemList;
        //遍历constraint
        for (int i = 0; i < constraints.size(); i++) {
            QDomElement constraint = constraints.at(i).toElement();
            //将每个功能的testItem存到functionConstraintsMap中
            TestItem functionTestItem;
            functionTestItem.variable = constraint.firstChildElement("variable").text();
            functionTestItem.value = constraint.firstChildElement("value").text();
            functionTestItem.testType = constraint.firstChildElement("type").text();
            functionTestItem.checkState  = (functionTestItem.testType == "功能执行器") ? Qt::Checked : Qt::Unchecked;
            functionTestItem.confidence = constraint.firstChildElement("confidence").text().toDouble();
            functionTestItemList.append(functionTestItem);

            // 将每个功能的testItemList中type=="功能执行器"的变量名称作为actuatorNameList的项
            if (functionTestItem.testType == "功能执行器") {
                QString componentName = functionTestItem.variable;
                if(componentName.startsWith("."))continue;
                componentName = componentName.contains(".") ? componentName.split(".")[0] : componentName;
                // 在functionActuatorNameMap中添加功能-执行器对
                mFunc.actuatorName = componentName;
                functionActuatorNameMap.insert(mFunc.functionName, componentName);
                QStringList constraintMeta;
                constraintMeta.append(functionTestItem.variable);
                constraintMeta.append(functionTestItem.value);
                mFunc.actuatorConstraint = functionTestItem;
                functionActuatorConstraintMap.insert(mFunc.functionName,constraintMeta);
            }
        }
        mFunc.constraintList = functionTestItemList;
        functionConstraintsMap.insert(mFunc.functionName,functionTestItemList);
        mFunc.variableConfig = functionVariableConfigMap.value(mFunc.functionName);
        functionInfoMap.insert(mFunc.functionName,mFunc);
    }
    //    qDebug()<<"functionNameList"<<functionNameList;
    //    qDebug()<<"functionActuatorNameMap"<<functionActuatorMap;
}

// 检查项目的祖先中是否存在相同的名称
bool checkAncestorForSameName(QTreeWidgetItem *item, const QString &name) {
    while(item) {
        if(item->text(0) == name) {
            return true;
        }
        item = item->parent();
    }
    return false;
}

void SelectFunctionDialog::processTreeItem(QTreeWidgetItem *item) {
    QDomDocument doc;
    doc.setContent(item->data(0, Qt::UserRole).toString());
    QDomElement functionDependency = doc.firstChildElement("functiondefine").firstChildElement("dependency").firstChildElement("function");
    if(!functionDependency.isNull()) {
        QString dependencies = functionDependency.text();
        QStringList pairs = dependencies.split(";");
        QSet<QString> functionNames;
        for(const QString &pair : pairs) {
            QStringList components = pair.split(",");
            // 现在我们的数据包括三个部分：器件名称、功能名称和相关端口
            // 因此我们要确保components的大小至少为2，即至少包括器件名称和功能名称
            if (components.size() >= 2) {
                QString function = components[1];
                functionNames.insert(function);
            }
        }

        for(const QString &name : functionNames) {
            // 检查此名称是否已经是当前项或其任何祖先的子项
            bool alreadyExists = checkAncestorForSameName(item, name);
            if(alreadyExists)break;
            for(QTreeWidgetItem *p = item; p; p = p->parent()) {
                for(int i = 0; i < p->childCount(); i++) {
                    if(p->child(i)->text(0) == name) {
                        alreadyExists = true;
                        break;
                    }
                }
            }

            // 检查这个名字是否是根级函数（排除当前项目的父项目）
            bool isRootFunc = false;
            QTreeWidgetItem *rootItemData = nullptr;
            for(int i = 0; i < ui->functionTree->topLevelItemCount(); i++) {
                QTreeWidgetItem *rootItem = ui->functionTree->topLevelItem(i);
                if(rootItem->text(0) == name && rootItem != item->parent()) {
                    isRootFunc = true;
                    rootItemData = rootItem;
                    break;
                }
            }
            // 如果满足条件，添加子项目并复制数据
            if(!alreadyExists && isRootFunc) {
                QTreeWidgetItem *newItem = new QTreeWidgetItem(item);
                newItem->setText(0, name);
                newItem->setData(0, Qt::UserRole, rootItemData->data(0, Qt::UserRole).toString());
            }
        }
    }
    // 处理子项目
    for(int i = 0; i < item->childCount(); i++) {
        processTreeItem(item->child(i));
    }
}

//更新树形节点
void SelectFunctionDialog::updateFunctionTree()
{
    QDomDocument doc;
    //qDebug()<<"updateFunctionTree localFunctionDescription:"<<qPrintable(localFunctionDescription);
    //qDebug()<<"doc.setContent(localFunctionDescription):"<<doc.setContent(localFunctionDescription);
    doc.setContent(localFunctionDescription);
    // Clear the tree first
    ui->functionTree->clear();
    functionConstraintIntegrityMap.clear();

    // Traverse the QDomDocument and update the functionTree accordingly
    QDomElement root = doc.firstChildElement("root");
    loadVariableRangeConfig(doc);

    // Create tree structure
    QDomElement treeStructElement = root.firstChildElement("treestruct");
    for(QDomNode n = treeStructElement.firstChild(); !n.isNull(); n = n.nextSibling()) {
        QDomElement e = n.toElement();
        if (!e.isNull() && e.tagName() == "item") {
            addTreeItemsFromXML(e, ui->functionTree->invisibleRootItem(), root);
        }
    }
    on_btn_UpdateSubFunc_clicked();
}

//从xml描述中构建树形节点
void SelectFunctionDialog::addTreeItemsFromXML(QDomElement &element, QTreeWidgetItem *parentItem, QDomElement &root) {
    QTreeWidgetItem *newItem = new QTreeWidgetItem(parentItem);
    newItem->setText(0, element.attribute("name"));

    // Look for the corresponding function and set the data
    QDomNodeList functions = root.elementsByTagName("functiondefine");
    for(int i = 0; i < functions.count(); i++) {
        QDomElement functionElement = functions.at(i).toElement();
        if(functionElement.firstChildElement("name").text() == element.attribute("name")) {
            QString functionName = functionElement.firstChildElement("name").text();
            QString functionDesc = functionElement.firstChildElement("describe").text();
            QString link = functionElement.firstChildElement("link").text();
            QDomElement dependencyElement = functionElement.firstChildElement("dependency");

            //考虑缺失子项的情况
            QDomElement functionDependencyElement = dependencyElement.firstChildElement("function");
            if(functionDependencyElement.isNull()) {
                functionDependencyElement = functionElement.ownerDocument().createElement("function");
                functionDependencyElement.appendChild(functionElement.ownerDocument().createTextNode(""));
                dependencyElement.appendChild(functionDependencyElement);
            }

            QDomElement componentDependencyElement = dependencyElement.firstChildElement("component");
            if(componentDependencyElement.isNull()) {
                componentDependencyElement = functionElement.ownerDocument().createElement("component");
                componentDependencyElement.appendChild(functionElement.ownerDocument().createTextNode(""));
                dependencyElement.appendChild(componentDependencyElement);
            }

            QDomElement allComponentDependencyElement = dependencyElement.firstChildElement("allComponent");
            if(allComponentDependencyElement.isNull()) {
                allComponentDependencyElement = functionElement.ownerDocument().createElement("allComponent");
                allComponentDependencyElement.appendChild(functionElement.ownerDocument().createTextNode(""));
                dependencyElement.appendChild(allComponentDependencyElement);
            }

            QString functionDependency = functionDependencyElement.text();
            QString componentDependency = componentDependencyElement.text();
            QString allComponentDependency = allComponentDependencyElement.text();

            QString attributeString = functionElement.firstChildElement("attribute").text();
            QString constraintIntegrity = functionElement.firstChildElement("constraintIntegrity").text().trimmed();
            if (constraintIntegrity.isEmpty()) {
                constraintIntegrity = QString("未检查");
            }
            functionConstraintIntegrityMap.insert(functionName, constraintIntegrity);
            loadFunctionVariableConfig(functionName, functionElement);

            QList<TestItem> testItemList;
            QDomNodeList constraints = functionElement.elementsByTagName("constraint");
            for (int i = 0; i < constraints.size(); i++) {
                QDomElement constraint = constraints.at(i).toElement();
                TestItem item;
                item.variable = constraint.firstChildElement("variable").text();
                item.value = constraint.firstChildElement("value").text();
                item.confidence = constraint.firstChildElement("confidence").text().toDouble();
                item.testType = (constraint.firstChildElement("type").text());
                item.checkState = (item.testType == "功能执行器") ? Qt::Checked : Qt::Unchecked;
                testItemList.append(item);
            }

            QList<resultEntity> resultEntityList;
            QDomNodeList results = functionElement.elementsByTagName("offlineSolveResult");
            for (int i = 0; i < results.size(); i++) {
                QDomElement result = results.at(i).toElement();
                resultEntity item;
                item.setResult(result.firstChildElement("componentNames").text(),result.firstChildElement("failureModes").text(),result.firstChildElement("probability").text().toDouble());
                resultEntityList.append(item);
            }

            // 使用createFunctionXML生成QDomDocument
            QDomDocument doc = createFunctionXML(functionName,
                                                 functionDesc,
                                                 link,
                                                 functionDependency,
                                                 componentDependency,
                                                 allComponentDependency,
                                                 attributeString,
                                                 constraintIntegrity,
                                                 testItemList,
                                                 resultEntityList,
                                                 functionVariableConfigMap.value(functionName));

            // 将XML保存到树形列表节点的data中
            newItem->setData(0, Qt::UserRole, doc.toString());

            break;
        }
    }
    for(QDomNode n = element.firstChild(); !n.isNull(); n = n.nextSibling()) {
        QDomElement e = n.toElement();
        if (!e.isNull() && e.tagName() == "item") {
            addTreeItemsFromXML(e, newItem, root);
        }
    }
}


void SelectFunctionDialog::on_btn_DelFunc_clicked()
{
    // 获取所有的功能名称以检查是否重复并获取当前的功能数量
    QStringList functionNames;
    foreach(QTreeWidgetItem *item, ui->functionTree->selectedItems()) {
        getAllFunctionNames(item, functionNames);
    }

    int count = functionNames.count();
    if(count == 0)
        return; // 直接返回，如果没有选择任何功能

    // 创建确认删除的对话框
    QMessageBox::StandardButton reply;
    QString dialogText;
    if(count > 1) {
        dialogText = QString("将删除多个功能，功能数：%1 \n是否继续删除？").arg(count);
        reply = QMessageBox::warning(this, "警告", dialogText, QMessageBox::Yes|QMessageBox::No);
    } else {
        dialogText = QString("将删除功能：%1 \n是否继续删除？").arg(functionNames.at(0));
        reply = QMessageBox::information(this, "提示", dialogText, QMessageBox::Yes|QMessageBox::No);
    }

    // 如果用户点击"No"，则不进行删除操作
    if (reply == QMessageBox::No)
        return;

    for (const QString &name : functionNames) {
        functionConstraintIntegrityMap.remove(name);
        functionVariableConfigMap.remove(name);
        functionInfoMap.remove(name);
    }

    // 执行删除操作
    foreach(QTreeWidgetItem *item, ui->functionTree->selectedItems()) {
        delete item;
    }
    currentFunctionName.clear();
    currentConstraintIntegrityStatus = QString("未检查");
    currentFunctionVariableConfig.clear();
    updateConstraintIntegrityLabel(currentConstraintIntegrityStatus);
}

void SelectFunctionDialog::on_btn_Ok_clicked() {
    for (auto it = functionConstraintIntegrityMap.constBegin(); it != functionConstraintIntegrityMap.constEnd(); ++it) {
        updateFunctionIntegrityEntry(it.key(), it.value());
    }
    saveCurrentVariableConfigToMap();
    // 创建一个QDomDocument来保存所有的功能
    QDomDocument doc;

    // 添加一个根元素来包含所有其他元素
    QDomElement rootElement = doc.createElement("root");
    doc.appendChild(rootElement);

    // 添加功能树的结构
    QDomElement treeStructElement = doc.createElement("treestruct");
    rootElement.appendChild(treeStructElement);

    // 这里不再对 invisibleRootItem 处理，直接处理其子项目
    for (int i = 0; i < ui->functionTree->invisibleRootItem()->childCount(); ++i) {
        addTreeStructureToXML(ui->functionTree->invisibleRootItem()->child(i), treeStructElement, doc);
    }

    // 添加每个功能
    for (int i = 0; i < ui->functionTree->topLevelItemCount(); ++i) {
        addFunctionToXML(ui->functionTree->topLevelItem(i), rootElement, doc);
    }

    QDomNodeList functionNodes = rootElement.elementsByTagName(QString("functiondefine"));
    for (int idx = 0; idx < functionNodes.size(); ++idx) {
        const QDomElement func = functionNodes.at(idx).toElement();
        const QString functionName = func.firstChildElement(QString("name")).text().trimmed();
        QDomElement dependency = func.firstChildElement(QString("dependency"));
        QString rawAll;
        QStringList parsedAll;
        if (!dependency.isNull()) {
            rawAll = dependency.firstChildElement(QString("allComponent")).text();
            parsedAll = splitComponents(rawAll);
        }
        qDebug().noquote() << "[FunctionDialog] allComponent raw for" << functionName << ":" << rawAll;
        qDebug().noquote() << "[FunctionDialog] allComponent list for" << functionName << ":" << parsedAll;
    }

    QDomElement existing = rootElement.firstChildElement(QString("variableRangeConfig"));
    if (!existing.isNull()) {
        rootElement.removeChild(existing);
    }
    if (!variableRangeConfig.isEmpty()) {
        QDomElement configElement = variableRangeConfig.toXml(doc);
        rootElement.appendChild(configElement);
    }

    //获取functionTree当前选中项的节点名称
    QList<QTreeWidgetItem *> selectedItems = ui->functionTree->selectedItems();
    if (!selectedItems.isEmpty()) {
        currentFunctionName = selectedItems.first()->text(0);
    } else {
        // 如果没有选中任何项目，可以设置一个默认值或处理这种情况
        currentFunctionName = ""; //或者其他默认值
    }
    qDebug()<<"currentFunctionName:"<<currentFunctionName;

    // 保存到localFunctionDescription中
    localFunctionDescription = doc.toString();

    functionInfoMap = testability::FunctionCatalog::parse(localFunctionDescription);
    functionAllComponentMap.clear();
    for (auto it = functionInfoMap.constBegin(); it != functionInfoMap.constEnd(); ++it) {
        functionAllComponentMap.insert(it.key(), joinComponents(it.value().allComponentList));
    }

    //    //链路信息
    //    localLink = ui->textEditLink->toPlainText();

    //qDebug()<<"Dialog Accept localFunctionDescription:"<<qPrintable(localFunctionDescription);;

    // 关闭对话框
    accept();
}

// 用于递归处理所有的项目和子项目
void SelectFunctionDialog::addFunctionToXML(QTreeWidgetItem *item, QDomElement &parentElement, QDomDocument &doc) {
    QString functionData = item->data(0, Qt::UserRole).toString();
    QDomDocument functionDoc;
    functionDoc.setContent(functionData);
    parentElement.appendChild(functionDoc.documentElement().cloneNode(true));

    //    // 添加这个项目的所有子项目
    //    for (int i = 0; i < item->childCount(); ++i) {
    //        addFunctionToXML(item->child(i), parentElement, doc);
    //    }
}

void SelectFunctionDialog::addTreeStructureToXML(QTreeWidgetItem *item, QDomElement &parentElement, QDomDocument &doc) {
    //qDebug() << "Adding tree structure for item:" << item->text(0);
    // 创建一个新元素表示这个项目
    QDomElement itemElement = doc.createElement("item");
    itemElement.setAttribute("name", item->text(0)); // 设置'name'属性为item的文本
    parentElement.appendChild(itemElement);

    // 添加这个项目的所有子项目
    for (int i = 0; i < item->childCount(); ++i) {
        addTreeStructureToXML(item->child(i), itemElement, doc);
    }
}

void SelectFunctionDialog::on_btn_Cancel_clicked() {
    QMessageBox::StandardButton reply;
    reply = QMessageBox::question(this, "是否保存修改", "将放弃对功能列表的修改，是否继续?",
                                  QMessageBox::Yes|QMessageBox::No);
    if (reply == QMessageBox::Yes) {
        // 点击“是”，关闭对话框
        reject();
    }
}

//点击界面上的"保存修改"按钮执行
//将界面上的内容转化为xml描述，并保存到树形节点中
void SelectFunctionDialog::on_btn_SaveFunc_clicked()
{
    QTreeWidgetItem* currentItem = ui->functionTree->currentItem();
    if(currentItem == nullptr) {
        QMessageBox::warning(this, "Warning", "没有选中功能节点.");
        return;
    }
    qDebug()<<"on_btn_SaveFunc_clicked";
    QString functionName = currentItem->text(0);
    QString constraintStatus = functionConstraintIntegrityMap.value(functionName, QString("未检查"));
    functionConstraintIntegrityMap.insert(functionName, constraintStatus);
    saveCurrentVariableConfigToMap();
}
void SelectFunctionDialog::onTextEditComponentDependencyContextMenu(const QPoint& pos)
{
    QMenu contextMenu(tr("Context menu"), this);

    QAction* actionCal = contextMenu.addAction("计算依赖器件");

    // 创建标准操作(复制、粘贴等)
    QMenu* standardMenu = ui->textEditComponentDependency->createStandardContextMenu();
    QList<QAction*> standardActions = standardMenu->actions();
    contextMenu.addSeparator();
    for(QAction* action : standardActions) {
        contextMenu.addAction(action);
    }
    QAction* selectedItem = contextMenu.exec(ui->textEditComponentDependency->mapToGlobal(pos));
    if(selectedItem == actionCal)
    {
        ui->textEditComponentDependency->setPlainText(CalComponentDependency(ui->textEditLink->toPlainText(),ui->textEditAllComponent->toPlainText()));
    }
}


// 实现功能依赖表格的鼠标右键菜单槽函数
void SelectFunctionDialog::onTableFunctionDependencyContextMenu(const QPoint& pos) {
    // 注意这里使用了QCursor::pos()来获取鼠标的全局位置
    QPoint globalPos = QCursor::pos();

    QMenu menu(this);
    QAction* actionFind = menu.addAction("自动查找依赖功能");
    menu.addSeparator(); // 添加一个分隔符
    QAction* actionAdd = menu.addAction("新增");
    menu.addSeparator(); // 添加一个分隔符
    QAction* actionClear = menu.addAction("清空");
    menu.addSeparator(); // 添加一个分隔符
    QAction* actionAddToConstraint = menu.addAction("添加到变量约束中");
    QAction* selectedItem = menu.exec(globalPos);

    if (selectedItem == actionAdd) {
        insertIntoFunctionDependencyTable(",");
    }
    if(selectedItem == actionClear)
    {
        // 表格行数大于1，弹出确认对话框
        int rowCount = ui->table_FunctionDependency->rowCount();
        if (rowCount > 1) {
            QMessageBox::StandardButton reply = QMessageBox::question(this, "确认清空", "是否确定要清空表格中的所有行？",
                                                                      QMessageBox::Yes | QMessageBox::No);
            if (reply != QMessageBox::Yes) {
                return; // 用户选择不清空，直接返回
            }
        }

        // 删除全部行
        ui->table_FunctionDependency->setRowCount(0);
    }
    if(selectedItem == actionAddToConstraint)
    {
        //遍历ui->table_FunctionDependency的所有行，将其第2列内容（功能名称）添加到ui->table_test约束描述表格中
        int rowCount = ui->table_FunctionDependency->rowCount();
        for (int i = 0; i < rowCount; ++i) {
            MyComboBox *cb = qobject_cast<MyComboBox*>(ui->table_FunctionDependency->cellWidget(i, 1));
            if (cb) {
                QString functionName = cb->currentText(); // 获取功能名称
                // 调用函数将功能名称、"功能正常"、0.0和"依赖功能"添加到ui->table_test中
                insertIntoFunctionTable(functionName, "功能正常", 0.0, "依赖功能");
            }
        }
    }
    if(selectedItem == actionFind)
    {
        CalFunctionDependency();
    }
}

void SelectFunctionDialog::on_contextMenuRequested(const QPoint &pos)
{
    QTreeWidgetItem *item = ui->functionTree->itemAt(pos);
    if (!item)
        return;

    QMenu contextMenu(this);

    QAction *renameAction = contextMenu.addAction("重命名");
    contextMenu.addSeparator(); // 添加一个分隔符
    QAction *deleteAction = contextMenu.addAction("删除");

    connect(renameAction, &QAction::triggered, this, [=]() {
        // 弹出QInputDialog来获取新的名称
        QString prevName = item->text(0);
        bool ok;
        QString newName = QInputDialog::getText(this, tr("重命名"),
                                                tr("新的名称:"), QLineEdit::Normal, prevName, &ok);
        if (!ok || newName.isEmpty() || newName==prevName)
            return;

        // 检查新的名称是否重复
        QStringList functionNames;
        for (int i = 0; i < ui->functionTree->topLevelItemCount(); ++i) {
            getAllFunctionNames(ui->functionTree->topLevelItem(i), functionNames);
        }
        if (functionNames.contains(newName)) {
            QMessageBox::warning(this, "提示", "功能名已存在");
            return;
        }

        // 设置新的名称
        item->setText(0, newName);

        // 获取树节点的数据并将其解析为QDomDocument
        QString functionXml = item->data(0, Qt::UserRole).toString();
        QDomDocument doc;
        doc.setContent(functionXml);

        // 找到名称元素并设置新的名称
        QDomElement nameElement = doc.firstChildElement("functiondefine").firstChildElement("name");
        nameElement.firstChild().setNodeValue(newName);

        // 将更新后的XML保存到树形列表节点的data中
        item->setData(0, Qt::UserRole, doc.toString());
    });

    //删除功能
    connect(deleteAction, &QAction::triggered, this, [=]() {

        on_btn_DelFunc_clicked();
    });

    contextMenu.exec(ui->functionTree->mapToGlobal(pos));
}
//递归添加功能约束以及递归更新当前链路信息
void SelectFunctionDialog::recursiveAdd(QList<TestItem> &testItemListToCheck, TestItem item,QString& functionLinks, bool isTopLevel) {
    QString varType = systemEntity->obsVarsMap[item.variable];
    TestItem newItem = item;
    // 只加入顶级功能的功能执行器约束，且加入前将其值取反
    if (isTopLevel && newItem.testType == "功能执行器") {
        if (varType == "Bool") {
            if (newItem.value == "true")
                newItem.value = "false";
            else
                newItem.value = "true";
        } else {
            //qDebug() << "暂不支持的功能执行器变量类型：" << varType;
            qDebug()<<"取反前 变量值："<<newItem.value;
            newItem.value = negateRange(newItem.value);
            qDebug()<<"取反后 变量值："<<newItem.value;
        }
    }
    if (newItem.testType != "依赖功能")
        testItemListToCheck.append(newItem);

    if (newItem.testType == "依赖功能") {
        // 添加对应的链路信息
        //链路信息（linkText）是由逗号","分隔的元素列表，其中每个元素表示一个器件或多级嵌套的器件端口；元素无"."表示器件及其所有端口，含"."则表示具体的器件端口，更深层的"."表示从属于上一级端口的端口，形成了一个包含与被包含的层级关系。
        //追加规则：逐个元素进行处理，重复的不添加，范围大的包含范围小的；下面举例说明应如何对functionLinks进行内容追加
        //例如当前functionLinks="T,QS,L1,KM.1,KM.2,FR.1.A,FR.1.B,FR.2.A,M"，待处理功能的link="T,QS.1,KM.A1_A2,FR.1,L2,L21.1,M.A_B.1"
        //T：由于在functionLinks中已存在，故不添加
        //QS.1：由于在functionLinks中已存在QS,QS包含QS.1，故不添加
        //KM.A1_A2：由于在functionLinks中不存在KM.A1_A2的父级，也不存在相同的元素，故添加，functionLinks更新为："T,QS,L1,KM.1,KM.2,FR.1.A,FR.1.B,FR.2.A,M,KM.A1_A2"
        //FR.1：由于在functionLinks不存在FR.1的父级,也不存在相同的元素，故添加，但functionLinks中存在FR.1的子级FR.1.A,FR.1.B，故需要对其进行吸收，functionLinks更新为："T,QS,L1,KM.1,KM.2,FR.1,FR.2.A,M,KM.A1_A2"
        //L2：由于在functionLinks不存在L2的父级,也不存在相同的元素，故添加，functionLinks更新为："T,QS,L1,KM.1,KM.2,FR.1,FR.2.A,M,KM.A1_A2,L2"
        //L21.1：由于在functionLinks不存在L21.1的父级,也不存在相同的元素，故添加，functionLinks更新为："T,QS,L1,KM.1,KM.2,FR.1,FR.2.A,M,KM.A1_A2,L2,L21.1"
        //M.A_B.1：由于在functionLinks存在M.A_B.1的祖先M（父级的父级）,故不添加
        //故最终functionLinks更新为："T,QS,L1,KM.1,KM.2,FR.1,FR.2.A,M,KM.A1_A2,L2,L21.1"
        QString link = functionLinkMap.value(newItem.variable);
        if(!link.isEmpty()) {
            QStringList linkElements = link.split(",");
            QStringList existingElements = functionLinks.split(",");

            for (const QString &linkElement : linkElements) {
                bool addElement = true;
                for (int i = 0; i < existingElements.size(); ++i) {
                    QString existingElement = existingElements.at(i);

                    if (linkElement == existingElement) {
                        addElement = false; // 相同元素，不添加
                        break;
                    } else if (linkElement.startsWith(existingElement + ".")) {
                        addElement = false; // 已存在父元素，不添加
                        break;
                    } else if (existingElement.startsWith(linkElement + ".")) {
                        // 存在子元素，移除子元素，添加当前元素
                        existingElements.removeAt(i);
                        i--;
                    }
                }
                if (addElement) {
                    existingElements.append(linkElement);
                }
            }
            functionLinks = existingElements.join(",");
        }
        QList<TestItem> relatedItems = functionConstraintsMap.value(newItem.variable);
        for (const TestItem &relatedItem : relatedItems) {
            if (relatedItem.testType != "功能执行器") {
                recursiveAdd(testItemListToCheck, relatedItem, functionLinks,false);
            }
        }
    }
}
QList<TestItem> SelectFunctionDialog::processTestItemListForPenetrativeSolve(QList<TestItem> &currentTestItemList, QString& LinkText)
{
    // 创建新列表，用于检查测试项
    QList<TestItem> initialTestItemList;

    // 复制测试项列表，如果项类型为“功能执行器”，则取反其值,同时递归添加功能的所有约束
    // 在过程中更新LinkText
    for (const TestItem &item : currentTestItemList) {
        recursiveAdd(initialTestItemList, item, LinkText,true);
    }
    qDebug().noquote().nospace() << "recursiveLinkText:" << LinkText;

    // 1. 将initialTestItems分为包含和不包含“边界条件”的两部分
    QList<TestItem> boundaryTestItems, nonBoundaryTestItems;
    for (const TestItem &item : initialTestItemList) {
        if (item.testType == "边界条件") {
            boundaryTestItems.append(item);
        } else {
            nonBoundaryTestItems.append(item);
        }
    }

    // 2. 计算所需的边界条件，并与boundaryTestItems比对，如果boundaryTestItems中的项不包含在所需的边界条件中，就从boundaryTestItems中移除
    SystemStructure currentSystemStructure(systemDescription,LinkText);
    QStringList requiredBoundaryConditions = currentSystemStructure.getBoundaryComponentList();
    qDebug()<<"requiredBoundaryConditions:"<<requiredBoundaryConditions;
    boundaryTestItems.erase(std::remove_if(boundaryTestItems.begin(), boundaryTestItems.end(),[&](const TestItem &item) {
        bool itemInRequired = false;
        for (const QString &cond : requiredBoundaryConditions) {
            if (item.variable == cond || item.variable.startsWith(cond + ".")) {
                itemInRequired = true;
                break;
            }
        }
        return !itemInRequired;
    }), boundaryTestItems.end());

    // 3. 使用nonBoundaryTestItems与新的boundaryTestItems构成新的initialTestItems
    initialTestItemList = nonBoundaryTestItems + boundaryTestItems;

    // 4. 使用 QVector 去重和保留用户选择的项
    QVector<TestItem> uniqueItemsVec;
    QSet<QString> uniqueKeys;
    for (const TestItem &item : initialTestItemList) {
        if (uniqueKeys.contains(item.variable)) {
            // find the existing item with the same variable
            auto it = std::find_if(uniqueItemsVec.begin(), uniqueItemsVec.end(), [&](const TestItem &uniqueItem){
                return uniqueItem.variable == item.variable;
            });
            if(it != uniqueItemsVec.end()){
                // 对比现有项和新项的 value 是否相同，如果不同则弹出提示框让用户选择
                if (it->value != item.value) {
                    QMessageBox msgBox;
                    msgBox.setWindowTitle("冲突的测试项");
                    msgBox.setText(QString("变量 %1 有冲突的值。请选择要保留的项。").arg(item.variable));
                    msgBox.addButton(QString("保留现有项：%1").arg(it->value), QMessageBox::YesRole);
                    QAbstractButton* pBtnNo = msgBox.addButton(QString("替换为新项：%1").arg(item.value), QMessageBox::NoRole);
                    msgBox.exec();
                    if (msgBox.clickedButton() == pBtnNo) {
                        // replace the item
                        *it = item;
                    }
                }
            }
        } else {
            uniqueItemsVec.append(item);
            uniqueKeys.insert(item.variable);
        }
    }

    // 重新创建 initialTestItems，只包含唯一的项
    initialTestItemList = uniqueItemsVec.toList();
    qDebug().noquote().nospace() << "initialTestItemList:" << initialTestItemList;
    return initialTestItemList;
}

//采用穿透式诊断进行离线求解
//输入：功能树及各功能的描述；输出：当前功能的完整全局求解结果，全部相关器件，功能失效概率（根据所有相关器件的先验失效概率进行计算）；
//1-将功能执行器的value取反
//2-逐级加载所依赖功能的约束(功能列表及对应的约束描述记录在functionConstraintsMap的QMap<QString, QList<TestItem>>中)
//3-合并variable与value均相同的约束
//4-检查所有边界条件，去掉不再是边界条件的约束
//5-请用户解决variable相同但value不相同的约束
// 通过穿透式诊断进行离线求解
void SelectFunctionDialog::on_btn_OfflineSolve_clicked()
{
    if (currentConstraintIntegrityStatus == QString("未检查")) {
        on_btn_CheckConstraints_clicked();
        if (currentConstraintIntegrityStatus == QString("未检查")) {
            return;
        }
    }

    // 使用全局系统描述初始化模型
    //systemEntity->prepareModel(systemDescription);
    QString currentLinkText = ui->textEditLink->toPlainText();
    QList<TestItem> processedTestItemList = processTestItemListForPenetrativeSolve(testItemList,currentLinkText);

    SystemStructure currentSystemStructure(systemDescription,currentLinkText);
    QString croppedSystemDescription = currentSystemStructure.getCroppedSystemDescription();
    int solveMode = ui->comboBoxSolveMode->currentIndex();
    if(!currentSystemStructure.isSystemConsistent())
    {
        QMessageBox::warning(this,"错误","系统描述错误");
    }
    else
    {
        QList<resultEntity> functionResultEntity = systemEntity->completeSolve(croppedSystemDescription, processedTestItemList, solveMode, false);

        localResultEntityList.clear();
        localResultEntityList = functionResultEntity;

        QString functionAllComponent;//该功能所有相关器件
        double functionFaultProbability=1.0;//该功能的综合失效概率

        // 用于存储器件名称并保持顺序，确保不重复
        QStringList componentList;
        auto appendComponent = [&](const QString &component) {
            const QString trimmed = component.trimmed();
            if (trimmed.isEmpty() || componentList.contains(trimmed)) {
                return;
            }
            componentList.append(trimmed);
        };

        // 遍历每个结果实体
        for(const resultEntity &res : functionResultEntity) {
            // 计算当前功能的故障概率
            functionFaultProbability *= (1.0-res.getProbability());

            // 获取该实体包含的所有器件名称
            QString componentsInEntityString = res.getComponentNames();

            // 检查是否存在多个器件故障
            if(componentsInEntityString.contains(",")) {
                // 把","替换成空格，并用括号括起来
                const QString cleaned = componentsInEntityString.replace(",", " ").trimmed();
                appendComponent(QStringLiteral("(%1)").arg(cleaned));
            } else {
                // 单个器件故障，直接加入到componentSet中
                appendComponent(componentsInEntityString);
            }
        }

        if (componentList.isEmpty()) {
            componentList = splitComponents(ui->textEditAllComponent->toPlainText());
        }
        functionAllComponent = joinComponents(componentList);
        functionFaultProbability = 1.0 - functionFaultProbability;

        const bool prevLoading = isLoading;
        isLoading = true;
        {
            QSignalBlocker blocker(ui->textEditAllComponent);
            ui->textEditAllComponent->setPlainText(functionAllComponent);
        }
        {
            QSignalBlocker blocker(ui->textEditFaultProbability);
            ui->textEditFaultProbability->setPlainText(QString::number(functionFaultProbability,'e',3));
        }
        isLoading = prevLoading;

    }
}


//从ui->textEditLink->toPlainText()计算ui->textEditComponentDependency->setPlainText()
//计算规则：
//textEditLink中元素均以逗号","分隔；其中元素如果带点"."则为器件端口，"."之前为器件名称，"."之后为端口名称；其中元素如果不带点"."则为器件名称；
//找到所有的器件名称，并去掉重复的部分。
//一个可能的例子：
//ui->textEditLink->toPlainText()="T,QS,L1,L2,FU,L7,L8,KM.1,KM.2,KM.3,KM.4,FR.1,FR.2,FR.3,FR.4,M"
//ui->textEditComponentDependency->setPlainText("T,QS,L1,L2,FU,L7,L8,KM,FR,M")
QString SelectFunctionDialog::CalComponentDependency(QString linkText,  QString allComponent )
{
    QStringList allComponentList = splitComponents(allComponent);
    QStringList linkComponentList = splitComponents(linkText);
    QStringList sortedComponentList;
    if(!allComponentList.isEmpty())
    {
        //allComponent不为空的情况
        //将allComponentList中的器件按linkComponentList中的器件排序

        for (const QString &linkComponent : linkComponentList)
        {
            QString component = linkComponent.contains(".") ? linkComponent.section('.', 0, 0) : linkComponent;
            if (allComponentList.contains(component) && !sortedComponentList.contains(component))
            {
                sortedComponentList.push_back(component);
            }
        }
    }
    else
    {
        //allComponent为空的情况
        for (const auto& s : linkComponentList)
        {
            if(s.startsWith("."))continue;
            QString component = s.contains(".") ? s.section('.', 0, 0) : s;
            if (!sortedComponentList.contains(component)) //检查器件是否已存在
            {
                sortedComponentList.push_back(component);
            }
        }
    }

    // 检查linkComponentList中的最后一个器件是否在sortedComponentList中
    // 如果在的话，则把该器件挪到sortedComponentList的最后
    if (!linkComponentList.isEmpty()) {
        QString lastLinkComponent = linkComponentList.last();
        QString lastComponent = lastLinkComponent.contains(".") ? lastLinkComponent.section('.', 0, 0) : lastLinkComponent;
        if (sortedComponentList.contains(lastComponent))
        {
            sortedComponentList.removeAll(lastComponent);
            sortedComponentList.push_back(lastComponent);
        }
    }
    return joinComponents(sortedComponentList);
}


//componentAndFunctionString格式为"componentName1,functionName1;componentName2,functionName2......"
//查找ui->textEditComponentDependency->toPlainText()中是否有functionActuatorNameMap中的器件,如果有，且与当前功能的执行器不同，则进行以下步骤：
//如果对应的器件之前不存在于componentAndFunctionString中，且在functionActuatorNameMap中只有唯一的功能与其匹配，则将器件功能对一起追加到componentAndFunctionString，否则，仅添加器件名，功能名设为空（比如有多个功能对应这个器件）
//如果componentAndFunctionString中已包含待添加的器件，且存在对应的不为空的功能，则不作修改；
//如果componentAndFunctionString中已包含待添加的器件，但对应的功能为空，且待添加器件在functionActuatorNameMap中只有唯一的功能与其匹配，则修改添加的器件在componentAndFunctionString中对应的功能为functionActuatorMap中唯一匹配的功能。
QString SelectFunctionDialog::CalFunctionDependency()
{
    QString componentAndFunctionString = generateQStringFromFunctionDependencyTable();
    QStringList functionDependencyList = componentAndFunctionString.split(';');
    QSet<QString> addedComponents; // 存储已经添加到 functionDependencyList 的器件

    // 从 ui->textEditComponentDependency->toPlainText() 获取器件列表
    QStringList componentList = ui->textEditComponentDependency->toPlainText().split(",", QString::SkipEmptyParts);

    // 获取当前功能的执行器
    QTreeWidgetItem *selectedItem = ui->functionTree->currentItem(); // 获取当前选中的节点
    if (selectedItem) {
        QString currentFunction = selectedItem->text(0); // 获取当前选中节点的名称
        QString crrFunctionActuator = functionActuatorNameMap.value(currentFunction); // 在 functionActuatorNameMap 中查询对应的执行器名称

        // 遍历器件列表
        for (const QString &component : componentList) {
            // 检查这个器件是否存在于 functionActuatorNameMap 中，并且与当前功能的执行器不同
            if (functionActuatorNameMap.values().contains(component) && component != crrFunctionActuator) {
                // 如果是，获取作为该器件执行器的功能
                QList<QString> functions = functionActuatorNameMap.keys(component);
                QStringList relativePortList;// 用于存储相关端口
                if (!addedComponents.contains(component)) {
                    // 从 ui->textEditLink 获取链路器件或链路器件端口
                    QStringList linkComponents = ui->textEditLink->toPlainText().split(",", QString::SkipEmptyParts);
                    for (const QString &linkComponent : linkComponents) {
                        if (linkComponent.contains(component)) {
                            relativePortList.append(linkComponent);
                        }
                    }
                }

                // 检查这个器件是否已经存在于 functionDependencyList 中
                bool isComponentExist = false;
                for (const QString &tuple : functionDependencyList) {
                    QStringList parts = tuple.split(",");
                    if (parts[0] == component) {
                        isComponentExist = true;
                        if (parts[1].isEmpty() && functions.size() == 1) {
                            // 如果功能为空，并且 functionActuatorNameMap 中该器件只有一个对应的功能，
                            // 用 functionActuatorNameMap 中的功能替换它
                            functionDependencyList.removeOne(tuple);
                            functionDependencyList.append(component + "," + functions.first() + ",");
                        }
                        break;
                    }
                }
                if (!isComponentExist && functions.size() == 1) {
                    // 如果器件不存在于 functionDependencyList 中，并且 functionActuatorNameMap 中该器件只有一个对应的功能，
                    // 用 functionActuatorNameMap 中的功能添加它
                    functionDependencyList.append(component + "," + functions.first() + ","+relativePortList.join(" "));
                } else if (!isComponentExist) {
                    // 如果器件不存在于 functionDependencyList 中，并且 functionActuatorNameMap 中该器件有多个对应的功能，
                    // 添加器件，但功能为空
                    functionDependencyList.append(component + ",,"+relativePortList.join(" "));
                }
                addedComponents.insert(component);
            }
        }
    }

    // 将 functionDependencyList 转换回字符串
    componentAndFunctionString = functionDependencyList.join(";");
    updateFunctionDependencyTable(componentAndFunctionString);
    return componentAndFunctionString;
}

QStringList SelectFunctionDialog::boundaryDeviceToAddList(const QStringList &boundaryDeviceList, QList<TestItem>& currentTestItemList)
{
    QStringList boundaryDeviceToAddList;

    for (const QString &device : boundaryDeviceList) {
        bool isContained = false;
        QString containingVariable;
        for (const auto& item : currentTestItemList) {
            if (item.variable.contains(device)) {
                isContained = true;
                containingVariable = item.variable;
                break;
            }
        }
        if (!isContained) {
            boundaryDeviceToAddList.append(device);
        } else {
            qDebug() << "Variable " << device << " already defined in testItemList, corresponding variable is "<<containingVariable;
        }
    }
    return boundaryDeviceToAddList;
}

//查找边界条件（从链路信息ui->textEditLink->toPlainText()以及systemDescription计算所需的边界条件）
//计算方法：
//1.从systemDescription取出描述连接的语句，并从其中找出包含链路信息的部分连接描述语句（找到最小的连接描述语句集合，使其完全覆盖当前功能的链路信息）
//2.找出连接描述语句中未被链路信息中器件或器件端口所未覆盖的内容，找到其对应的变量作为边界条件的变量（找到最小的连接描述语句集合中未被当前功能的链路信息覆盖的部分，且上一级可覆盖下一级的内容，比如链路信息中的FU可覆盖连接描述中的FU.1、FU.2,FU.1可覆盖FU.1.u）
//3.将找到的边界条件的变量加入到ui->table_test中(调用insertIntoFunctionTable方法)
//说明：
//链路信息ui->textEditLink->toPlainText()类型为QString，用于描述链路的结构，具体内容为全部器件端口，其中的元素以","分隔，单个元素格式为"componentName.portName"（portName还可以游下一级的portName，如果该器件全部端口均相关，则可直接写器件名称，不写端口）
//systemDescription分为两部分，器件定义与连接描述
void SelectFunctionDialog::on_btn_CalBoundaryConditions_clicked()
{
    SystemStructure currentSystemStructure(systemDescription,ui->textEditLink->toPlainText());
    if(!currentSystemStructure.isSystemConsistent())
    {
        QMessageBox::warning(this,"错误","模型描述错误");
        return;
    }

    QStringList boundaryDeviceList = currentSystemStructure.getBoundaryComponentList();

    // 使用boundaryDeviceToAddList函数找出需要添加的
    QStringList boundaryDevicesToAdd = boundaryDeviceToAddList(boundaryDeviceList, testItemList);

    if (boundaryDevicesToAdd.empty()) {
        QString messageText;

        // 没有找到边界条件
        if (boundaryDeviceList.empty()) {
            messageText = "没有找到所需的边界条件。";
        }
        // 所有的边界条件已经存在
        else {
            messageText = "已经存在所有的边界条件，没有新变量需要添加。已存在的边界条件如下：\n";
            for (const QString &device : boundaryDeviceList) {
                messageText += device + "\n";
            }
        }

        QMessageBox::information(this, "边界条件", messageText);
    } else {
        QString messageText = "发现以下变量作为新的边界条件，是否添加？\n";
        for (const QString &device : boundaryDevicesToAdd) {
            messageText += device + "\n";
        }

        QMessageBox::StandardButton reply;
        reply = QMessageBox::question(this, "新的边界条件", messageText,
                                      QMessageBox::Yes|QMessageBox::No);

        if (reply == QMessageBox::Yes) {
            // 对于每个需要添加的变量，将其添加到表中作为边界条件
            for (const QString &device : boundaryDevicesToAdd) {
                insertIntoFunctionTable(device, "", 0.0, "边界条件");
            }
        }
    }
}

void SelectFunctionDialog::on_btn_CheckConstraints_clicked()
{
    SystemStructure currentSystemStructure(systemDescription, ui->textEditLink->toPlainText());
    if (!currentSystemStructure.isSystemConsistent()) {
        QMessageBox::warning(this, "错误", "模型描述错误");
        return;
    }
    QString croppedSystemDescription = currentSystemStructure.getCroppedSystemDescription();
    systemEntity->prepareModel(croppedSystemDescription);
    QList<TestItem> positiveItems = buildConstraintCheckItems(false);
    const QStringList componentElements = currentAllComponentElements();
    const QStringList variableWhitelist = collectFunctionVariables(componentElements);
    QMap<QString, QString> satModel;
    bool positiveSat = systemEntity->satisfiabilitySolve(croppedSystemDescription, positiveItems, variableWhitelist, &satModel);

    QString status;
    if (!positiveSat) {
        status = QString("不正确");
        QMessageBox::warning(this, QString("检查约束完整性"), status);
    } else {
        QList<TestItem> negativeItems = buildConstraintCheckItems(true);
        bool negativeSat = systemEntity->satisfiabilitySolve(croppedSystemDescription, negativeItems, variableWhitelist);
        if (negativeSat) {
            status = QString("不完整");
            QMessageBox::warning(this, QString("检查约束完整性"), status);
        } else {
            status = QString("完整");
            QMessageBox::information(this, QString("检查约束完整性"), status);
            if (!satModel.isEmpty()) {
                updateSatSamplesFromModel(satModel, componentElements);
            } else {
                QMessageBox::information(this, QString("提示"), QString("根据当前约束未能获取SAT模型可行解。"));
            }
        }
    }

    currentConstraintIntegrityStatus = status;
    updateConstraintIntegrityLabel(status);
    if (!currentFunctionName.isEmpty()) {
        functionConstraintIntegrityMap.insert(currentFunctionName, status);
        updateFunctionIntegrityEntry(currentFunctionName, status);
        if (functionInfoMap.contains(currentFunctionName)) {
            functionInfoMap[currentFunctionName].constraintIntegrity = status;
        }
    }
}

QList<TestItem> SelectFunctionDialog::getLocalTestItemList(){
    QList<TestItem> retTestItemList;
    if (!mainWindow->getIsPenetrativeSolve()) {
        retTestItemList = testItemList;
        for (TestItem &item : retTestItemList)
        {
            // 检查每一项的类型是否为"功能执行器"
            if (item.testType == "功能执行器") {
                QString variableType = systemEntity->obsVarsMap[item.variable];
                //将其value取反,需要分情况讨论
                if (variableType == "Bool") {
                    if(item.value == "true")item.value="false";
                    else item.value="true";
                }else
                {
                    //qDebug()<<"暂不支持的功能执行器变量类型："<<variableType;
                    qDebug()<<"取反前 变量值："<<item.value;
                    item.value = negateRange(item.value);
                    qDebug()<<"取反后 变量值："<<item.value;
                }
            }
        }
        localLink = ui->textEditLink->toPlainText();
    }
    else
    {
        QString currentLinkText = ui->textEditLink->toPlainText();
        QList<TestItem> processedTestItemList = processTestItemListForPenetrativeSolve(testItemList,currentLinkText);
        SystemStructure currentSystemStructure(systemDescription,currentLinkText);
        QString croppedSystemDescription = currentSystemStructure.getCroppedSystemDescription();
        if(!currentSystemStructure.isSystemConsistent())
        {
            QMessageBox::warning(this,"错误","系统描述错误");
            retTestItemList.clear();
            localLink = "";
        }
        else
        {
            retTestItemList = processedTestItemList;
            localLink = currentLinkText;
        }
    }
    return retTestItemList;
}

QString SelectFunctionDialog::negateRange(const QString &input) const {
    return testability::negateRange(input);
}

void SelectFunctionDialog::updateConstraintIntegrityLabel(const QString &status)
{
    QString display = status.trimmed();
    if (display.isEmpty()) {
        display = QString("未检查");
    }
    ui->labelConstraintIntegrityValue->setText(display);
}

void SelectFunctionDialog::markConstraintIntegrityUnknown()
{
    const QString unknown = QString("未检查");
    currentConstraintIntegrityStatus = unknown;
    if (!currentFunctionName.isEmpty()) {
        functionConstraintIntegrityMap.insert(currentFunctionName, unknown);
        updateFunctionIntegrityEntry(currentFunctionName, unknown);
        if (functionInfoMap.contains(currentFunctionName)) {
            functionInfoMap[currentFunctionName].constraintIntegrity = unknown;
        }
    }
    updateConstraintIntegrityLabel(unknown);
}

QList<TestItem> SelectFunctionDialog::buildConstraintCheckItems(bool invertActuator) const
{
    QList<TestItem> assembled;
    for (const TestItem &item : testItemList) {
        TestItem newItem = item;
        if (newItem.testType == QString("依赖功能")) {
            if (newItem.value == QString("功能正常")) {
                if (functionActuatorConstraintMap.contains(item.variable)) {
                    const QStringList meta = functionActuatorConstraintMap.value(item.variable);
                    if (meta.size() == 2) {
                        newItem.variable = meta.at(0);
                        newItem.value = meta.at(1);
                        newItem.testType = QString("一般变量");
                        assembled.append(newItem);
                    }
                }
            }
            continue;
        }

        if (invertActuator && newItem.testType == QString("功能执行器")) {
            const QString type = systemEntity->obsVarsMap.value(newItem.variable);
            if (type == QString("Bool")) {
                newItem.value = (newItem.value == QString("true")) ? QString("false") : QString("true");
            } else {
                newItem.value = negateRange(newItem.value);
            }
        }
        assembled.append(newItem);
    }
    return assembled;
}

void SelectFunctionDialog::showVariableRangeDialog()
{
    QMap<QString, QStringList> typeMap;
    for (auto it = systemEntity->obsVarsMap.constBegin(); it != systemEntity->obsVarsMap.constEnd(); ++it) {
        const QString &variable = it.key();
        const QString &declType = it.value();
        QString typeKey = rangeconfig::VariableRangeConfig::inferTypeKey(variable, declType);
        if (typeKey.isEmpty()) {
            continue;
        }
        typeMap[typeKey].append(variable);
    }

    if (typeMap.isEmpty()) {
        QMessageBox::information(this, QString("变量取值范围"), QString("当前模型中没有可配置的变量。"));
        return;
    }

    for (auto it = typeMap.begin(); it != typeMap.end(); ++it) {
        it.value().removeDuplicates();
        std::sort(it.value().begin(), it.value().end());
    }

    VariableRangeDialog dialog(typeMap, variableRangeConfig, this);
    if (dialog.exec() == QDialog::Accepted) {
        variableRangeConfig = dialog.config();
        markConstraintIntegrityUnknown();
    }
}

void SelectFunctionDialog::loadVariableRangeConfig(const QDomDocument &doc)
{
    QDomElement root = doc.firstChildElement(QString("root"));
    if (root.isNull()) {
        variableRangeConfig.clear();
        return;
    }
    QDomElement configElement = root.firstChildElement(QString("variableRangeConfig"));
    variableRangeConfig = rangeconfig::VariableRangeConfig::fromXml(configElement);
}

void SelectFunctionDialog::loadFunctionVariableConfig(const QString &functionName, const QDomElement &functionElement)
{
    if (functionName.trimmed().isEmpty()) {
        return;
    }
    functionvalues::FunctionVariableConfig config =
            functionvalues::FunctionVariableConfig::fromXml(functionElement.firstChildElement(QString("variableValueConfig")));
    functionVariableConfigMap.insert(functionName, config);
}

void SelectFunctionDialog::saveCurrentVariableConfigToMap()
{
    if (currentFunctionName.isEmpty()) {
        return;
    }
    functionVariableConfigMap.insert(currentFunctionName, currentFunctionVariableConfig);
    if (functionInfoMap.contains(currentFunctionName)) {
        functionInfoMap[currentFunctionName].variableConfig = currentFunctionVariableConfig;
    }
    writeFunctionXml(currentFunctionName, currentFunctionVariableConfig);
}

void SelectFunctionDialog::ensureFunctionVariableConfig(const QString &functionName)
{
    if (functionName.trimmed().isEmpty()) {
        return;
    }
    if (!functionVariableConfigMap.contains(functionName)) {
        functionVariableConfigMap.insert(functionName, functionvalues::FunctionVariableConfig());
    }
}

QStringList SelectFunctionDialog::currentLinkElements() const
{
    QStringList elements;
    const QString rawLink = ui->textEditLink->toPlainText();
    for (const QString &item : rawLink.split(",", QString::SkipEmptyParts)) {
        const QString trimmed = item.trimmed();
        if (!trimmed.isEmpty()) {
            elements.append(trimmed);
        }
    }
    return elements;
}

QStringList SelectFunctionDialog::currentAllComponentElements() const
{
    const QStringList elements = splitComponents(ui->textEditAllComponent->toPlainText());
    if (!elements.isEmpty()) {
        return elements;
    }
    return currentLinkElements();
}

bool SelectFunctionDialog::variableMatchesLink(const QString &variable, const QStringList &linkElements) const
{
    if (variable.trimmed().isEmpty() || linkElements.isEmpty()) {
        return false;
    }
    const QStringList varParts = variable.split(".", QString::SkipEmptyParts);
    for (const QString &linkElement : linkElements) {
        const QStringList linkParts = linkElement.split(".", QString::SkipEmptyParts);
        if (linkParts.isEmpty()) {
            continue;
        }
        if (linkParts.size() > varParts.size()) {
            continue;
        }
        bool match = true;
        for (int i = 0; i < linkParts.size(); ++i) {
            if (!QString::compare(linkParts.at(i), varParts.at(i), Qt::CaseInsensitive)) {
                continue;
            }
            match = false;
            break;
        }
        if (match) {
            return true;
        }
    }
    return false;
}

QString SelectFunctionDialog::formatModelSample(const QString &valueText) const
{
    QString trimmed = valueText.trimmed();
    if (trimmed.isEmpty()) {
        return trimmed;
    }
    bool ok = false;
    double numeric = trimmed.toDouble(&ok);
    if (ok) {
        return QString::number(numeric, 'g', 12);
    }
    return trimmed;
}

QMap<QString, QString> SelectFunctionDialog::currentConstraintValueMap() const
{
    QMap<QString, QString> map;
    for (const TestItem &item : testItemList) {
        if (item.variable.trimmed().isEmpty()) {
            continue;
        }
        map.insert(item.variable, item.value);
    }
    return map;
}

void SelectFunctionDialog::updateSatSamplesFromModel(const QMap<QString, QString> &model,
                                                     const QStringList &componentElements)
{
    if (currentFunctionName.isEmpty() || model.isEmpty()) {
        return;
    }
    ensureFunctionVariableConfig(currentFunctionName);
    QMap<QString, QString> constraintMap = currentConstraintValueMap();
    for (auto it = model.constBegin(); it != model.constEnd(); ++it) {
        const QString variable = it.key();
        const bool matchesLink = variableMatchesLink(variable, componentElements);
        if (!matchesLink && !constraintMap.contains(variable)) {
            continue;
        }
        const QString formattedValue = formatModelSample(it.value());
        if (formattedValue.isEmpty()) {
            continue;
        }
        functionvalues::VariableEntry entry = currentFunctionVariableConfig.entry(variable);
        if (entry.type.trimmed().isEmpty()) {
            const QString declType = systemEntity->obsVarsMap.value(variable);
            const QString inferredType = rangeconfig::VariableRangeConfig::inferTypeKey(variable, declType);
            if (!inferredType.isEmpty()) {
                entry.type = inferredType;
            }
        }
        if (constraintMap.contains(variable)) {
            entry.constraintValue = constraintMap.value(variable);
        }
        entry.satSamples.clear();
        entry.satSamples.append(formattedValue);
        currentFunctionVariableConfig.setEntry(variable, entry);
    }
    saveCurrentVariableConfigToMap();
}

QStringList SelectFunctionDialog::collectFunctionVariables(const QStringList &componentElements) const
{
    qDebug().noquote() << "[VariableRange] collectFunctionVariables start — componentElements:" << componentElements;
    const QMap<QString, QString> constraintMap = currentConstraintValueMap();
    QSet<QString> variables;
    for (auto it = systemEntity->obsVarsMap.constBegin(); it != systemEntity->obsVarsMap.constEnd(); ++it) {
        if (variableMatchesLink(it.key(), componentElements)) {
            variables.insert(it.key());
        }
    }
    qDebug().noquote() << "[VariableRange] matched obsVarsMap variables:" << variables.size();

    const QStringList configVariables = currentFunctionVariableConfig.variableNames();
    for (const QString &variable : configVariables) {
        if (!componentElements.isEmpty()
            && !variableMatchesLink(variable, componentElements)
            && !constraintMap.contains(variable)) {
            continue;
        }
        variables.insert(variable);
    }
    qDebug().noquote() << "[VariableRange] variables after merging FunctionVariableConfig:" << variables.size();

    for (const TestItem &item : testItemList) {
        const QString variable = item.variable.trimmed();
        if (variable.isEmpty()) {
            continue;
        }
        const QString trimmedType = item.testType.trimmed();
        const bool isBoundaryCondition = (trimmedType == QStringLiteral("边界条件"));
        const bool hasConstraint = constraintMap.contains(variable);
        if (!componentElements.isEmpty()
            && !variableMatchesLink(variable, componentElements)
            && !isBoundaryCondition
            && !hasConstraint) {
                continue;
        }
        variables.insert(variable);
    }
    qDebug().noquote() << "[VariableRange] variables after merging testItemList:" << variables.size();

    QStringList sorted = variables.values();
    std::sort(sorted.begin(), sorted.end());
    qDebug().noquote() << "[VariableRange] final variable list size:" << sorted.size();
    return sorted;
}

QVector<functionvalues::FunctionVariableRow> SelectFunctionDialog::assembleVariableRows(const QStringList &linkElements) const
{
    QVector<functionvalues::FunctionVariableRow> rows;
    const QStringList variables = collectFunctionVariables(linkElements);
    QMap<QString, QString> constraintMap = currentConstraintValueMap();
    qDebug().noquote() << "[VariableRange] assembleVariableRows — constraintMap keys:" << constraintMap.keys();
    for (const QString &variable : variables) {
        functionvalues::FunctionVariableRow row;
        row.variable = variable;

        const functionvalues::VariableEntry entry = currentFunctionVariableConfig.entry(variable);
        if (!entry.type.trimmed().isEmpty()) {
            row.typeKey = entry.type.trimmed();
        } else {
            const QString declType = systemEntity->obsVarsMap.value(variable);
            row.typeKey = rangeconfig::VariableRangeConfig::inferTypeKey(variable, declType);
        }

        if (constraintMap.contains(variable)) {
            row.constraintValue = constraintMap.value(variable);
            row.constraintLocked = true;
            row.typeLocked = true;
        } else {
            row.constraintValue = entry.constraintValue;
        }

        row.typicalValues = entry.typicalValues;
        row.valueRange = entry.valueRange;
        row.satSamples = entry.satSamples;

        rows.append(row);
    }
    return rows;
}

QString SelectFunctionDialog::formatInterval(double lower, double upper) const
{
    auto formatDouble = [](double value) {
        if (std::fabs(value) < 1e-12) {
            value = 0.0;
        }
        QString text = QString::number(value, 'f', 3);
        if (text.contains(QLatin1Char('.'))) {
            while (text.endsWith(QLatin1Char('0'))) {
                text.chop(1);
            }
            if (text.endsWith(QLatin1Char('.'))) {
                text.chop(1);
            }
        }
        if (text == QString("-0")) {
            text = QString("0");
        }
        return text;
    };
    return QString("[%1, %2]").arg(formatDouble(lower), formatDouble(upper));
}

QList<TestItem> SelectFunctionDialog::buildPositiveSolveItems() const
{
    return buildConstraintCheckItems(false);
}

QList<TestItem> SelectFunctionDialog::buildVariableSolveItems(const QList<TestItem> &baseItems,
                                                              const QString &variable,
                                                              const QString &valueExpression) const
{
    QList<TestItem> items = baseItems;
    for (int i = items.size() - 1; i >= 0; --i) {
        if (items.at(i).variable.trimmed() == variable) {
            items.removeAt(i);
        }
    }

    TestItem setter = makeVariableSetterItem(variable, valueExpression);
    items.append(setter);
    return items;
}

TestItem SelectFunctionDialog::makeVariableSetterItem(const QString &variable, const QString &valueExpression) const
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

bool SelectFunctionDialog::checkSatisfiable(const QString &systemDescription,
                                            const QList<TestItem> &items)
{
    return systemEntity->satisfiabilitySolve(systemDescription, items);
}

QString SelectFunctionDialog::croppedSystemDescriptionForCurrentLink(const QStringList &linkElements) const
{
    const QString linkText = linkElements.join(QString(","));
    SystemStructure structure(systemDescription, linkText);
    if (!structure.isSystemConsistent()) {
        return QString();
    }
    return structure.getCroppedSystemDescription();
}

QString SelectFunctionDialog::solveVariableFeasibleRange(const QString &variable,
                                                         const QString &typeKey,
                                                         const QStringList &typicalValues,
                                                         QString &errorMessage)
{
    errorMessage.clear();
    const QString trimmedVariable = variable.trimmed();
    if (trimmedVariable.isEmpty()) {
        errorMessage = QString("变量名称为空");
        return QString();
    }
    if (currentConstraintIntegrityStatus != QString("完整")
        && currentConstraintIntegrityStatus != QString("不完整")) {
        errorMessage = QString("请先检查约束完整性，确认为\"完整\"或\"不完整\"后再求解");
        return QString();
    }
    if (typicalValues.isEmpty()) {
        errorMessage = QString("变量 %1 缺少典型值").arg(trimmedVariable);
        return QString();
    }

    const auto isBoolToken = [](const QString &text) {
        const QString lowered = text.trimmed().toLower();
        return lowered == QString("true") || lowered == QString("false");
    };

    const QString normalizedTypeKey = typeKey.trimmed();
    QString resolvedTypeKey = normalizedTypeKey;

    bool typicalLooksBool = true;
    for (const QString &valueText : typicalValues) {
        if (!isBoolToken(valueText)) {
            typicalLooksBool = false;
            break;
        }
    }

    bool declaredBool = false;
    if (systemEntity) {
        const QString declared = systemEntity->obsVarsMap.value(trimmedVariable);
        if (!declared.trimmed().isEmpty()
            && declared.trimmed().compare(QString("Bool"), Qt::CaseInsensitive) == 0) {
            declaredBool = true;
        }
    }

    bool isBoolType = normalizedTypeKey.compare(QString("Bool"), Qt::CaseInsensitive) == 0
            || typicalLooksBool
            || declaredBool;
    if (isBoolType && resolvedTypeKey.isEmpty()) {
        resolvedTypeKey = QString("Bool");
    }

    QVector<double> typicalNumbers;
    QStringList boolTypicalValues;
    if (isBoolType) {
        for (const QString &valueText : typicalValues) {
            const QString trimmed = valueText.trimmed();
            if (trimmed.compare(QString("true"), Qt::CaseInsensitive) == 0) {
                boolTypicalValues.append(QString("true"));
            } else if (trimmed.compare(QString("false"), Qt::CaseInsensitive) == 0) {
                boolTypicalValues.append(QString("false"));
            } else {
                errorMessage = QString("变量 %1 的典型值 %2 不是布尔值")
                                   .arg(trimmedVariable, trimmed);
                return QString();
            }
        }
        boolTypicalValues.removeDuplicates();
    } else {
        for (const QString &valueText : typicalValues) {
            bool ok = false;
            const double number = valueText.trimmed().toDouble(&ok);
            if (!ok) {
                errorMessage = QString("变量 %1 的典型值 %2 不是数值")
                                   .arg(trimmedVariable, valueText.trimmed());
                return QString();
            }
            typicalNumbers.append(number);
        }
    }

    const QStringList linkElements = currentLinkElements();
    const QString croppedDescription = croppedSystemDescriptionForCurrentLink(linkElements);
    if (croppedDescription.isEmpty()) {
        errorMessage = QString("无法构建当前功能的裁剪模型");
        return QString();
    }

    const QList<TestItem> baseItems = buildPositiveSolveItems();

    auto assertionsForSetter = [this](const TestItem &setter) {
        QList<TestItem> items;
        items.append(setter);
        const QList<obsEntity> obsList = systemEntity->buildObsEntityList(items);
        QStringList assertions;
        for (const auto &obs : obsList) {
            assertions.append(obs.getDescription());
        }
        return assertions;
    };

    if (isBoolType) {
        const QStringList canonicalOrder{QString("true"), QString("false")};
        QStringList feasibleValues;

        auto isSatisfiableDirect = [&](const QString &candidate) {
            QList<TestItem> items = buildVariableSolveItems(baseItems, trimmedVariable, candidate);
            return checkSatisfiable(croppedDescription, items);
        };

        for (const QString &typical : boolTypicalValues) {
            if (!isSatisfiableDirect(typical)) {
                errorMessage = QString("变量 %1 在典型值 %2 下无法满足约束")
                                   .arg(trimmedVariable, typical);
                return QString();
            }
        }

        for (const QString &candidate : canonicalOrder) {
            if (isSatisfiableDirect(candidate)) {
                feasibleValues.append(candidate);
            }
        }

        if (feasibleValues.isEmpty()) {
            errorMessage = QString("变量 %1 在所有布尔取值下均无法满足约束")
                               .arg(trimmedVariable);
            return QString();
        }

        if (feasibleValues.contains(QString("true")) && feasibleValues.contains(QString("false"))) {
            return QStringLiteral("true;false");
        }

        return feasibleValues.join(QString(";"));
    }

    QString sessionError;
    SystemEntity::IncrementalSolveSession incrementalSession = systemEntity->createIncrementalSolveSession(croppedDescription,
                                                                                                          baseItems,
                                                                                                          QStringList(),
                                                                                                          sessionError);
    if (!incrementalSession.valid) {
        if (sessionError.isEmpty()) {
            errorMessage = QString("无法初始化Z3增量求解会话");
        } else {
            errorMessage = sessionError;
        }
        return QString();
    }

    rangeconfig::RangeValue baseRange = variableRangeConfig.effectiveRange(resolvedTypeKey, trimmedVariable);
    if (baseRange.lower > baseRange.upper) {
        std::swap(baseRange.lower, baseRange.upper);
    }

    auto isSatisfiableForValue = [&](double candidate, QString &failureMessage) {
        const QString candidateText = QString::number(candidate, 'g', 12);
        const TestItem setter = makeVariableSetterItem(trimmedVariable, candidateText);
        const QStringList assertions = assertionsForSetter(setter);
        return systemEntity->checkIncrementalSession(incrementalSession, assertions, failureMessage);
    };

    const double tolerance = 0.1;
    const int iterations = 24;
    QStringList intervals;

    for (double typical : typicalNumbers) {
        const double clampedTypical = qBound(baseRange.lower, typical, baseRange.upper);

        QString typicalError;
        if (!isSatisfiableForValue(clampedTypical, typicalError)) {
            if (!typicalError.isEmpty()) {
                errorMessage = typicalError;
            } else {
                errorMessage = QString("变量 %1 在典型值 %2 下无法满足约束")
                                   .arg(trimmedVariable, QString::number(typical, 'g', 12));
            }
            return QString();
        }

        double lowerBound = clampedTypical;
        double upperBound = clampedTypical;

        QString boundaryError;
        if (isSatisfiableForValue(baseRange.lower, boundaryError)) {
            lowerBound = baseRange.lower;
        } else {
            if (!boundaryError.isEmpty()) {
                errorMessage = boundaryError;
                return QString();
            }
            double low = baseRange.lower;
            double high = clampedTypical;
            for (int i = 0; i < iterations && (high - low) > tolerance; ++i) {
                const double mid = (low + high) * 0.5;
                QString midError;
                if (isSatisfiableForValue(mid, midError)) {
                    lowerBound = mid;
                    high = mid;
                } else {
                    if (!midError.isEmpty()) {
                        errorMessage = midError;
                        return QString();
                    }
                    low = mid;
                }
            }
        }

        boundaryError.clear();
        if (isSatisfiableForValue(baseRange.upper, boundaryError)) {
            upperBound = baseRange.upper;
        } else {
            if (!boundaryError.isEmpty()) {
                errorMessage = boundaryError;
                return QString();
            }
            double low = clampedTypical;
            double high = baseRange.upper;
            for (int i = 0; i < iterations && (high - low) > tolerance; ++i) {
                const double mid = (low + high) * 0.5;
                QString midError;
                if (isSatisfiableForValue(mid, midError)) {
                    upperBound = mid;
                    low = mid;
                } else {
                    if (!midError.isEmpty()) {
                        errorMessage = midError;
                        return QString();
                    }
                    high = mid;
                }
            }
        }

        if (lowerBound > upperBound) {
            std::swap(lowerBound, upperBound);
        }
        intervals.append(formatInterval(lowerBound, upperBound));
    }

    return intervals.join(QString(";"));
}

void SelectFunctionDialog::applyVariableRowsToConfig(const QVector<functionvalues::FunctionVariableRow> &rows)
{
    for (const auto &row : rows) {
        functionvalues::VariableEntry entry = currentFunctionVariableConfig.entry(row.variable);
        entry.type = row.typeKey.trimmed();
        if (row.constraintLocked) {
            entry.constraintValue.clear();
        } else {
            entry.constraintValue = row.constraintValue.trimmed();
        }
        entry.typicalValues = row.typicalValues.trimmed();
        entry.valueRange = row.valueRange.trimmed();
        entry.satSamples = row.satSamples;
        currentFunctionVariableConfig.setEntry(row.variable, entry);
    }
    saveCurrentVariableConfigToMap();
}

void SelectFunctionDialog::showFunctionVariableValueDialog()
{
    if (currentFunctionName.isEmpty()) {
        QMessageBox::information(this, QString("提示"), QString("请先选择功能"));
        return;
    }

    if (currentConstraintIntegrityStatus == QString("不正确")) {
        QMessageBox::warning(this, QString("提示"), QString("当前功能约束完整性为\"不正确\"，请先修正约束后再求解变量范围"));
        return;
    }

    const QStringList linkElements = currentLinkElements();
    const QString linkText = linkElements.join(QStringLiteral(","));
    SystemStructure currentSystemStructure(systemDescription, linkText);
    if (!currentSystemStructure.isSystemConsistent()) {
        QMessageBox::warning(this, QStringLiteral("提示"), QStringLiteral("当前功能关联的系统描述不自洽，请检查功能链路或系统描述。"));
        return;
    }

    const QString croppedDescription = currentSystemStructure.getCroppedSystemDescription();
    systemEntity->prepareModel(croppedDescription);
    qDebug().noquote() << "[VariableRange] prepared cropped model — obsVarsMap size:" << systemEntity->obsVarsMap.size();

    const QStringList componentElements = currentAllComponentElements();
    QVector<functionvalues::FunctionVariableRow> rows = assembleVariableRows(componentElements);
    if (rows.isEmpty()) {
        QMessageBox::information(this, QString("提示"), QString("当前功能没有可配置的变量"));
        return;
    }

    auto solver = [this](const QString &variable,
                         const QString &typeKey,
                         const QStringList &typicalValues,
                         QString &errorMessage) {
        return solveVariableFeasibleRange(variable, typeKey, typicalValues, errorMessage);
    };

    FunctionVariableValueDialog dialog(rows, solver, this);
    if (dialog.exec() == QDialog::Accepted) {
        applyVariableRowsToConfig(dialog.resultRows());
    }
}

void SelectFunctionDialog::updateCurrentFunctionXml()
{
    if (currentFunctionName.isEmpty()) {
        return;
    }
    writeFunctionXml(currentFunctionName, currentFunctionVariableConfig);
}

QList<QTreeWidgetItem*> SelectFunctionDialog::findFunctionTreeItems(const QString &functionName) const
{
    if (functionName.isEmpty()) {
        return {};
    }
    return ui->functionTree->findItems(functionName, Qt::MatchExactly | Qt::MatchRecursive);
}

void SelectFunctionDialog::writeFunctionXml(const QString &functionName,
                                            const functionvalues::FunctionVariableConfig &config)
{
    const QList<QTreeWidgetItem*> items = findFunctionTreeItems(functionName);
    if (items.isEmpty()) {
        return;
    }

    QString attributeString = ui->checkBoxPersistent->isChecked() ? QString("Persistent") : QString("NotPersistent");
    attributeString += QStringLiteral(",") + ui->textEditFaultProbability->toPlainText();

    const QString constraintStatus = functionConstraintIntegrityMap.value(functionName, QString("未检查"));

    QDomDocument doc = createFunctionXML(functionName,
                                         ui->textEditFunctionDescription->toPlainText(),
                                         ui->textEditLink->toPlainText(),
                                         generateQStringFromFunctionDependencyTable(),
                                         ui->textEditComponentDependency->toPlainText(),
                                         ui->textEditAllComponent->toPlainText(),
                                         attributeString,
                                         constraintStatus,
                                         testItemList,
                                         localResultEntityList,
                                         config);

    const QString xmlString = doc.toString();
    for (QTreeWidgetItem *item : items) {
        if (item) {
            item->setData(0, Qt::UserRole, xmlString);
        }
    }
}

void SelectFunctionDialog::updateFunctionIntegrityEntry(const QString &functionName, const QString &status)
{
    if (functionName.isEmpty()) {
        return;
    }
    const QString trimmedStatus = status.trimmed().isEmpty() ? QString("未检查") : status.trimmed();
    const auto items = ui->functionTree->findItems(functionName, Qt::MatchExactly | Qt::MatchRecursive);
    for (QTreeWidgetItem *item : items) {
        if (!item) {
            continue;
        }
        QDomDocument doc;
        if (!doc.setContent(item->data(0, Qt::UserRole).toString())) {
            continue;
        }
        QDomElement functionElement = doc.firstChildElement(QString("functiondefine"));
        if (functionElement.isNull()) {
            continue;
        }
        QDomElement integrityElement = functionElement.firstChildElement(QString("constraintIntegrity"));
        if (integrityElement.isNull()) {
            integrityElement = doc.createElement(QString("constraintIntegrity"));
            functionElement.appendChild(integrityElement);
        }
        while (!integrityElement.firstChild().isNull()) {
            integrityElement.removeChild(integrityElement.firstChild());
        }
        integrityElement.appendChild(doc.createTextNode(trimmedStatus));
        item->setData(0, Qt::UserRole, doc.toString());
    }
}
