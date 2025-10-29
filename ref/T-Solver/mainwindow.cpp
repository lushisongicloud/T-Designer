#include "mainwindow.h"
#include "widget/selectfunctiondialog.h"
#include "ui_mainwindow.h"

#include <QApplication>
#include <QFormLayout>
#include <QListWidget>
#include <QLineEdit>
#include <QTime>
#include <QCompleter>
#include <QDir>
#include <QFile>
#include <QFileInfo>
#include <QSet>
#include <QFileDialog>
#include <QMessageBox>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QTextStream>
#include <QHash>
#include <QObject>
#include <QDomDocument>

#include "testability/d_matrix_builder.h"
#include "testability/function_catalog.h"
#include "testability/smt_facade.h"
#include "widget/dmatrixoptionsdialog.h"
#include "widget/dmatrixviewerdialog.h"

extern int ProgressNum;
namespace {

QStringList splitCsvLine(const QString &line)
{
    QStringList parts;
    QString current;
    bool inQuotes = false;
    for (int i = 0; i < line.size(); ++i) {
        const QChar ch = line.at(i);
        if (inQuotes) {
            if (ch == QLatin1Char('"')) {
                if (i + 1 < line.size() && line.at(i + 1) == QLatin1Char('"')) {
                    current.append(QLatin1Char('"'));
                    ++i;
                } else {
                    inQuotes = false;
                }
            } else if (ch != QLatin1Char('\n')) {
                current.append(ch);
            }
        } else {
            if (ch == QLatin1Char('"')) {
                inQuotes = true;
            } else if (ch == QLatin1Char(',')) {
                parts.append(current);
                current.clear();
            } else if (ch != QLatin1Char('\n')) {
                current.append(ch);
            }
        }
    }
    parts.append(current);
    if (!parts.isEmpty() && !parts.first().isEmpty() && parts.first().front().unicode() == 0xFEFF) {
        parts.first().remove(0, 1);
    }
    return parts;
}

testability::FaultKind faultKindFromString(const QString &value)
{
    const QString lower = value.trimmed().toLower();
    if (lower == QLatin1String("component")) {
        return testability::FaultKind::Component;
    }
    return testability::FaultKind::Function;
}

testability::TestKind testKindFromString(const QString &value)
{
    const QString lower = value.trimmed().toLower();
    if (lower == QLatin1String("function")) {
        return testability::TestKind::Function;
    }
    if (lower == QLatin1String("mode")) {
        return testability::TestKind::Mode;
    }
    return testability::TestKind::Signal;
}

testability::DetectMode detectModeFromString(const QString &value)
{
    const QString lower = value.trimmed().toLower();
    if (lower == QLatin1String("exists")) {
        return testability::DetectMode::Exists;
    }
    return testability::DetectMode::Guaranteed;
}

bool loadDMatrixFromFiles(const QString &metadataPath,
                          testability::DMatrixBuildResult *result,
                          testability::DMatrixBuildOptions *options,
                          QString *csvPathOut)
{
    if (!result) {
        return false;
    }

    QFile metaFile(metadataPath);
    if (!metaFile.open(QIODevice::ReadOnly | QIODevice::Text)) {
        return false;
    }

    QJsonParseError parseError;
    const QJsonDocument doc = QJsonDocument::fromJson(metaFile.readAll(), &parseError);
    if (doc.isNull() || !doc.isObject()) {
        return false;
    }

    const QJsonObject root = doc.object();

    result->faults.clear();
    result->tests.clear();
    result->cells.clear();

    const QJsonArray faultsArray = root.value(QStringLiteral("faults")).toArray();
    for (const QJsonValue &faultValue : faultsArray) {
        const QJsonObject obj = faultValue.toObject();
        testability::FaultDefinition fault;
        fault.id = obj.value(QStringLiteral("id")).toString();
        fault.name = obj.value(QStringLiteral("name")).toString();
        fault.kind = faultKindFromString(obj.value(QStringLiteral("kind")).toString());
        fault.relatedFunction = obj.value(QStringLiteral("function")).toString();
        fault.inputAssertions.clear();
        fault.faultAssertions.clear();
        for (const QJsonValue &value : obj.value(QStringLiteral("inputAssertions")).toArray()) {
            fault.inputAssertions.append(value.toString());
        }
        for (const QJsonValue &value : obj.value(QStringLiteral("faultAssertions")).toArray()) {
            fault.faultAssertions.append(value.toString());
        }
        fault.actuatorAssertions.clear();
        for (const QJsonValue &value : obj.value(QStringLiteral("actuatorAssertions")).toArray()) {
            fault.actuatorAssertions.append(value.toString());
        }
        fault.constraintIntegrity = obj.value(QStringLiteral("constraintIntegrity")).toString();
        fault.linkElements.clear();
        for (const QJsonValue &value : obj.value(QStringLiteral("linkElements")).toArray()) {
            fault.linkElements.append(value.toString());
        }
        fault.dependencyClosure.clear();
        for (const QJsonValue &value : obj.value(QStringLiteral("dependencyClosure")).toArray()) {
            const QString dependency = value.toString();
            if (!dependency.isEmpty()) {
                fault.dependencyClosure.insert(dependency);
            }
        }
        fault.offlineModeMap.clear();
        const QJsonObject offlineObj = obj.value(QStringLiteral("offlineModes")).toObject();
        for (auto offlineIt = offlineObj.constBegin(); offlineIt != offlineObj.constEnd(); ++offlineIt) {
            QSet<QString> modes;
            for (const QJsonValue &modeValue : offlineIt.value().toArray()) {
                modes.insert(modeValue.toString());
            }
            fault.offlineModeMap.insert(offlineIt.key(), modes);
        }
        fault.enabled = obj.value(QStringLiteral("enabled")).toBool(true);
        result->faults.append(fault);
    }

    const QJsonArray testsArray = root.value(QStringLiteral("tests")).toArray();
    for (const QJsonValue &testValue : testsArray) {
        const QJsonObject obj = testValue.toObject();
        testability::TestDefinition test;
        test.id = obj.value(QStringLiteral("id")).toString();
        test.name = obj.value(QStringLiteral("name")).toString();
        test.kind = testKindFromString(obj.value(QStringLiteral("kind")).toString());
        test.predicate = obj.value(QStringLiteral("predicate")).toString();
        test.negatedPredicate = obj.value(QStringLiteral("negatedPredicate")).toString();
        test.sourceItem.variable = obj.value(QStringLiteral("sourceVariable")).toString();
        test.sourceItem.value = obj.value(QStringLiteral("sourceValue")).toString();
        test.note = obj.value(QStringLiteral("note")).toString();
        test.relatedFunction = obj.value(QStringLiteral("relatedFunction")).toString();
        test.componentName = obj.value(QStringLiteral("component")).toString();
        test.failureModeName = obj.value(QStringLiteral("failureMode")).toString();
        test.signalVariable = obj.value(QStringLiteral("signalVariable")).toString();
        test.enabled = obj.value(QStringLiteral("enabled")).toBool(true);
        result->tests.append(test);
    }

    const int faultCount = result->faults.size();
    const int testCount = result->tests.size();
    result->cells.resize(faultCount);
    for (auto &row : result->cells) {
        row.resize(testCount);
    }

    if (options) {
        options->mode = detectModeFromString(root.value(QStringLiteral("mode")).toString());
        options->timeoutMs = root.value(QStringLiteral("timeoutMs")).toInt(-1);
        options->autoRange = root.value(QStringLiteral("autoRange")).toBool(true);
        options->fallbackToTemplate = root.value(QStringLiteral("fallbackToTemplate")).toBool(true);
        options->rangeTolerance = root.value(QStringLiteral("rangeTolerance")).toDouble(0.02);
        options->searchMaxAbs = root.value(QStringLiteral("searchMaxAbs")).toDouble(100000.0);
        options->includeFunctionInputs = root.value(QStringLiteral("includeFunctionInputs")).toBool(false);
        options->outputDirectory = QFileInfo(metadataPath).absolutePath();
    }

    QFileInfo metaInfo(metadataPath);
    const QString csvPath = metaInfo.absolutePath() + QLatin1Char('/') + metaInfo.completeBaseName() + QStringLiteral(".csv");
    if (csvPathOut) {
        *csvPathOut = csvPath;
    }

    QFile csvFile(csvPath);
    if (!csvFile.open(QIODevice::ReadOnly | QIODevice::Text)) {
        return false;
    }

    QTextStream csvStream(&csvFile);
    csvStream.setCodec("UTF-8");

    const QString headerLine = csvStream.readLine();
    if (headerLine.isNull()) {
        return false;
    }
    const QStringList headerParts = splitCsvLine(headerLine);
    if (headerParts.size() < 2) {
        return false;
    }

    QHash<QString, int> faultIndex;
    for (int i = 1; i < headerParts.size(); ++i) {
        faultIndex.insert(headerParts.at(i), i - 1);
    }

    QHash<QString, int> testIndex;
    for (int i = 0; i < result->tests.size(); ++i) {
        testIndex.insert(result->tests.at(i).id, i);
    }

    while (!csvStream.atEnd()) {
        const QString line = csvStream.readLine();
        if (line.trimmed().isEmpty()) {
            continue;
        }
        const QStringList parts = splitCsvLine(line);
        if (parts.isEmpty()) {
            continue;
        }
        const QString testId = parts.first();
        const int tIndex = testIndex.value(testId, -1);
        if (tIndex < 0) {
            continue;
        }
        for (int col = 1; col < parts.size(); ++col) {
            const QString faultId = headerParts.value(col);
            const int fIndex = faultIndex.value(faultId, -1);
            if (fIndex < 0 || fIndex >= result->cells.size()) {
                continue;
            }
            const QString value = parts.at(col).trimmed();
            testability::DetectabilityResult &cell = result->cells[fIndex][tIndex];
            cell.detected = (value == QLatin1String("1"));
            if (options && options->mode == testability::DetectMode::Guaranteed) {
                cell.guaranteed = cell.detected;
            }
        }
    }

    const QJsonArray cellMetadata = root.value(QStringLiteral("cellMetadata")).toArray();
    for (const QJsonValue &cellValue : cellMetadata) {
        const QJsonObject obj = cellValue.toObject();
        const QString faultId = obj.value(QStringLiteral("faultId")).toString();
        const QString testId = obj.value(QStringLiteral("testId")).toString();
        const int fIndex = faultIndex.value(faultId, -1);
        const int tIndex = testIndex.value(testId, -1);
        if (fIndex < 0 || tIndex < 0 || fIndex >= result->cells.size() || tIndex >= result->tests.size()) {
            continue;
        }
        testability::DetectabilityResult &cell = result->cells[fIndex][tIndex];
        cell.detected = obj.value(QStringLiteral("detected")).toBool(cell.detected);
        cell.guaranteed = obj.value(QStringLiteral("guaranteed")).toBool(cell.guaranteed);
        cell.method = obj.value(QStringLiteral("method")).toString(cell.method);
        cell.detail = obj.value(QStringLiteral("detail")).toString(cell.detail);
        if (obj.contains(QStringLiteral("metric"))) {
            cell.metric = obj.value(QStringLiteral("metric")).toDouble();
        }
    }

    return true;
}

} // namespace

QMap<QString, QStringList> MainWindow::obsTemplates = {
    {"AC380_3P_u", {"AC380.u", "( 0 , 0 , 0 )", "( 380 , 0 , 0 )", "( 0 , 380 , 0 )", "( 0 , 0 , 380 )", "( 380 , 380 , 0 )", "( 380 , 0 , 380 )", "( 0 , 380 , 380 )", "( 380 , 380 , 380 )"}},
    {"AC380_3P_i", {"( 1.0 , 1.0 , 1.0 )", "( 0 , 0 , 0 )", "( 1.0 , 0 , 0 )", "( 0 , 1.0 , 0 )", "( 0 , 0 , 1.0 )", "( 1.0 , 1.0 , 0 )", "( 1.0 , 0 , 1.0 )", "( 0 , 1.0 , 1.0 )"}},
    {"AC380_1P_u", {"380","0"}},
    {"AC380_1P_i", {"1.0","0"}},
    {"AC220_1P_u", {"220","0","[210,230]","(200,240]",">200.2","<=1.2","smt(> %1 (* L7.1.i 1000))"}},
    {"AC220_1P_i", {"1.0","0","[0.5,1.5]","(0,2.0]",">0.5","<=0.5","smt(> L7.1.u (* %1 1000))"}},
    {"Hydro_p", {"1.0","0","[0.0,0.5]","(0,1.0]",">0.5","<=32.5","smt(or (> %1 10) (< %1 -10))","smt(> %1 12)","smt(< (+ %1 1) 0)"}},
    {"Hydro_f", {"1.0","0","[-0.1,0.1]","(0,0.5]",">0.5","<=40","smt(or (> %1 10) (< %1 -10))","smt(< (* %1 1000) 40)","smt(< (+ %1 1) 0)"}}
};


QDebug operator<<(QDebug dbg, const TestItem& item) {
    dbg.nospace() << "TestItem(variable: " << item.variable
                  << ", value: " << item.value
                  << ", confidence: " << item.confidence
                  << ", type: " << item.testType
                  << ", checkState: " << item.checkState << ")\n";
    return dbg.space();
}
QDebug operator<<(QDebug dbg, const QList<TestItem>& list) {
    dbg.nospace() << "[";
    for(const auto& item: list){
        dbg.nospace() << item;
    }
    dbg.nospace() << "]";
    return dbg.space();
}

MainWindow::MainWindow(QWidget *parent) :
    QMainWindow(parent),
    ui(new Ui::MainWindow)
{
    ui->setupUi(this);
    this->setWindowTitle("故障诊断冲突求解器");

    lastDMatrixOptions.mode = testability::DetectMode::Guaranteed;
    lastDMatrixOptions.timeoutMs = -1;
    lastDMatrixOptions.autoRange = true;
    lastDMatrixOptions.fallbackToTemplate = true;
    lastDMatrixOptions.rangeTolerance = 0.05;
    lastDMatrixOptions.searchMaxAbs = 10000.0;
    lastDMatrixOptions.outputDirectory = QDir::current().filePath(QStringLiteral("output"));

    labViewCord = new QLabel("求解时间："); //创建状态栏标签
    labViewCord->setMinimumWidth(200);
    ui->statusBar->addWidget(labViewCord);

    //连接数据库
    databaseConnect();
    systemEntity = new SystemEntity(database);
    systemEntity->setMainWindow(this);
    qDebug()<<"连接数据库完成";

    systemEntity->setCurrentModel(&currentModel);
    //初始化界面
    initUI();
    qDebug()<<"initUI 完成";

    TimerUpdateUI=new QTimer(this);
    connect(TimerUpdateUI,SIGNAL(timeout()),this,SLOT(UpdateUI()));
    TimerUpdateUI->start(200);

    //修改测试表格内容时自动更新testitemlist
    connect(ui->table_test, &QTableWidget::itemChanged, this, &MainWindow::onTableTestItemChanged);

    //更新求解进度及结果
    connect(systemEntity, &SystemEntity::solvingStarted, this, &MainWindow::onSolvingStarted);
    connect(systemEntity, &SystemEntity::solvingFinished, this, &MainWindow::onSolvingFinished);
    connect(systemEntity, &SystemEntity::progressUpdated, this, &MainWindow::onProgressUpdated);
    connect(systemEntity, &SystemEntity::resultEntityListUpdated, this, &MainWindow::onResultEntityListUpdated);
    connect(systemEntity, &SystemEntity::outlierObsUpdated, this, &MainWindow::onOutlierObsUpdated);
}

MainWindow::~MainWindow()
{
    delete ui;
    if(database) delete database;
    if(labViewCord) delete labViewCord;

}

void MainWindow::UpdateUI()
{
    ui->progressBar->setValue(ProgressNum);

}

void MainWindow::initUI()
{
    ui->progressBar->setValue(0);
    ui->textEditConflictSets->clear();
    ui->textEditSystemDiscription->clear();
    ui->textEditTestDiscription->clear();
    ui->table_test->setColumnWidth(0, 120); // 设置第0列"变量"的宽度
    ui->table_test->setColumnWidth(1, 190); // 设置第1列"观测值"的宽度
    ui->table_test->setColumnWidth(2, 45); // 设置第2列"执行度"的宽度
    ui->table_test->setColumnWidth(3, 45); // 设置第3列"已实行"的宽度
    ui->table_test->setColumnWidth(4, 70); // 设置第4列"类型"的宽度

    ui->table_outlierObs->setColumnWidth(0,50);
    ui->table_outlierObs->setColumnWidth(1,100);
    ui->table_outlierObs->setColumnWidth(3,40);

}

void MainWindow::databaseConnect()
{
    //连接数据库
    database = new SQliteDatabase("Model.db");
    if(!database->connect()){
        ui->actionOpenModel->setEnabled(false);
        ui->actionSaveModel->setEnabled(false);
        QMessageBox::information(nullptr, "Tips", "数据库连接失败！",QMessageBox::Yes);
    }
}

void MainWindow::openModel(QString modelName)
{
    this->setWindowTitle(QString("故障诊断冲突求解器-[%1]").arg(modelName));
    currentModelName = modelName;
    currentModel = database->selectModelByName(modelName);
    ui->textEditSystemDiscription->setText(currentModel.getSystemDescription());
    ui->progressBar->setValue(0);
    ui->textEditConflictSets->clear();

    functionDescription = currentModel.getFunctionDiscription();
    QString savedObsCode= currentModel.getTestDiscription();
    ui->textEditTestDiscription->setText(savedObsCode);

    MainWindow::on_actionParseModel_triggered();
    refreshFunctionStateFromModel();

    //    //解析savedObsCode，将其内容填到table_test中，savedObsCode格式如下：(= T.A1_B1_C1.u AC380.u)
    //    ui->table_result->setRowCount(0);
    //    QRegularExpression re("\\(= (.+?) (.+?)\\)");
    //    QRegularExpressionMatchIterator i = re.globalMatch(savedObsCode);
    //    while (i.hasNext()) {
    //        QRegularExpressionMatch match = i.next();

    //        QString variable = match.captured(1); // captures the variable
    //        QString value = match.captured(2); // captures the value

    //        insertIntoTestTable(variable, value, 0, Qt::Unchecked);
    //    }
}

void MainWindow::on_actionOpenModel_triggered()
{
    QDialog *dialogModelNameSelect =new QDialog();
    dialogModelNameSelect->setWindowTitle("选择模型");
    dialogModelNameSelect->setMinimumSize(QSize(250,100));
    QFormLayout *formlayoutModelNameSelect = new QFormLayout(dialogModelNameSelect);


    QListWidget * listWidgetModelName = new QListWidget(dialogModelNameSelect);

    QStringList listModelName = database->selectAllModelName();

    listWidgetModelName->addItems(listModelName);

    formlayoutModelNameSelect->addRow(listWidgetModelName);

    QHBoxLayout *layout = new QHBoxLayout(dialogModelNameSelect);
    QPushButton *pushbuttonOK = new QPushButton(dialogModelNameSelect);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel = new QPushButton(dialogModelNameSelect);
    pushbuttonCancel->setText("取消");
    layout->addWidget(pushbuttonOK);
    layout->addWidget(pushbuttonCancel);
    formlayoutModelNameSelect->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogModelNameSelect,SLOT(accept()));
    QObject::connect(pushbuttonCancel,SIGNAL(clicked()),dialogModelNameSelect,SLOT(close()));

    listWidgetModelName->setCurrentItem(listWidgetModelName->item(0));

    if (dialogModelNameSelect->exec()==QDialog::Accepted){
        openModel(listWidgetModelName->currentItem()->text());
    }

    delete layout;
    delete dialogModelNameSelect;
}

void MainWindow::on_actionSaveModel_triggered()
{
    if (currentModelName.isEmpty()) {
        QMessageBox::warning(nullptr, "错误", "没有打开的模型",
                             QMessageBox::Ok, QMessageBox::NoButton);
        return;
    }
    currentModel.setSystemDescription(ui->textEditSystemDiscription->toPlainText());
    currentModel.setTestDiscription(ui->textEditTestDiscription->toPlainText());
    currentModel.setFunctionDiscription(functionDescription);
    if(database->updateModel(currentModel))
        QMessageBox::information(nullptr, "通知", "保存成功","确定");
    else
        QMessageBox::warning(nullptr, "通知", "保存失败","确定");

}

void MainWindow::on_actionParseModel_triggered()
{
    systemEntity->updateObsVarsMap(systemEntity->prepareModel(ui->textEditSystemDiscription->toPlainText()));
}

void MainWindow::on_actionCheckModel_triggered()
{


}

void MainWindow::on_pushButtonSolve_clicked()
{

}

void MainWindow::on_actionCreatNewComponent_triggered()
{
    QDialog *dialogCreatNewModule =new QDialog();
    dialogCreatNewModule->setWindowTitle("创建新元件");
    dialogCreatNewModule->setMinimumSize(QSize(700,400));

    QFormLayout *formlayout = new QFormLayout(dialogCreatNewModule);

    QLineEdit lineEditModuleType(dialogCreatNewModule);
    QLineEdit lineEditModuleMark(dialogCreatNewModule);
    QLineEdit lineEditModuleParameter(dialogCreatNewModule);
    QTextEdit textEditModuleVariable(dialogCreatNewModule);
    QTextEdit textEditModuleDescription(dialogCreatNewModule);

    QHBoxLayout layout(nullptr);
    QPushButton pushbuttonOK(dialogCreatNewModule);
    pushbuttonOK.setText("确认");
    QPushButton pushbuttonCancel(dialogCreatNewModule);
    pushbuttonCancel.setText("取消");
    layout.addWidget(&pushbuttonOK);
    layout.addWidget(&pushbuttonCancel);

    formlayout->addRow("元件类型:", &lineEditModuleType);
    formlayout->addRow("元件代号:", &lineEditModuleMark);
    formlayout->addRow("元件参数及默认值:", &lineEditModuleParameter);
    formlayout->addRow("元件变量定义代码:", &textEditModuleVariable);
    formlayout->addRow("元件约束定义代码:", &textEditModuleDescription);
    formlayout->addRow(&layout);

    QObject::connect(&pushbuttonOK,SIGNAL(clicked()),dialogCreatNewModule,SLOT(accept()));
    QObject::connect(&pushbuttonCancel,SIGNAL(clicked()),dialogCreatNewModule,SLOT(close()));

    if (dialogCreatNewModule->exec()==QDialog::Accepted)
    {
        if(lineEditModuleMark.text() == "")
        {
            QMessageBox::warning(nullptr, "错误",
                                 "元件代号不可为空",
                                 QMessageBox::Ok,QMessageBox::NoButton);
        }
        else if(database->componentMarkExist(lineEditModuleMark.text()))
        {
            QMessageBox::warning(nullptr, "错误", "元件代号已存在",
                                 QMessageBox::Ok,QMessageBox::NoButton);
        }
        else
        {
            component c;
            c.setType(lineEditModuleType.text());
            c.setMark(lineEditModuleMark.text());
            c.setParameter(lineEditModuleParameter.text());
            c.setVariable(textEditModuleVariable.toPlainText());
            c.setDescription(textEditModuleDescription.toPlainText());
            if(database->insertNewComponent(c)){
                QMessageBox::information(nullptr, "Tips", "元件创建成功！",QMessageBox::Yes);
            }
        }
    }
    dialogCreatNewModule->close();
}
void MainWindow::on_comboBox_Solve_Type_currentIndexChanged(int index)
{
    if(index == 0)
        systemEntity->SetType(0);
    else if(index == 1)
        systemEntity->SetType(1);
}

void MainWindow::on_actionSaveAs_triggered()
{
    QDialog *dialogCreatNewModel =new QDialog();
    dialogCreatNewModel->setWindowTitle("保存当前模型");
    dialogCreatNewModel->setMinimumSize(QSize(250,100));

    QFormLayout *formlayoutEnter = new QFormLayout(dialogCreatNewModel);

    QLineEdit *lineEditModelName = new QLineEdit(dialogCreatNewModel);

    QHBoxLayout *layout = new QHBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogCreatNewModel);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel = new QPushButton(dialogCreatNewModel);
    pushbuttonCancel->setText("取消");
    layout->addWidget(pushbuttonOK);
    layout->addWidget(pushbuttonCancel);

    formlayoutEnter->addRow("模型名称:", lineEditModelName);
    formlayoutEnter->addRow(layout);
    lineEditModelName->setText(currentModelName);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogCreatNewModel,SLOT(accept()));
    QObject::connect(pushbuttonCancel,SIGNAL(clicked()),dialogCreatNewModel,SLOT(close()));

    if (dialogCreatNewModel->exec()==QDialog::Accepted)
    {
        if(lineEditModelName->text() == "")
        {
            QMessageBox::warning(nullptr, "错误", "模型名称不可为空",
                                 QMessageBox::Ok,QMessageBox::NoButton);
        }
        else if(database->modelExist(lineEditModelName->text()))
        {
            QMessageBox::warning(nullptr, "错误", "模型已存在",
                                 QMessageBox::Ok,QMessageBox::NoButton);
        }
        else
        {
            model newModel;
            newModel.setName(lineEditModelName->text());
            newModel.setSystemDescription(ui->textEditSystemDiscription->toPlainText());
            newModel.setTestDiscription(ui->textEditTestDiscription->toPlainText());
            newModel.setFunctionDiscription(functionDescription);
            if(database->saveModel(newModel)){
                QMessageBox::information(nullptr, "Tips", "模型保存成功！",QMessageBox::Yes);
                currentModelName = lineEditModelName->text();
            }
        }
    }
    delete layout;
    delete dialogCreatNewModel;
}

void MainWindow::checkDuplicateAndUpdateColor() {
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
// 获取连接行中的设备名
QStringList getDeviceNames(const QString &line) {
    QRegExp rx("\\(([^)]*)\\)");
    QStringList devices;
    int pos = 0;
    while ((pos = rx.indexIn(line, pos)) != -1) {
        devices << rx.cap(1).split(",");
        pos += rx.matchedLength();
    }
    //qDebug()<<"devices:"<<devices;
    return devices;
}

// 确定是否匹配设备名
bool isDeviceMatched(const QStringList &devicesInLine, const QSet<QString> &functionDevices) {
    for (const QString &deviceInLine : devicesInLine) {
        //qDebug()<<"deviceInLine:"<<deviceInLine;
        for (const QString &device : functionDevices) {
            if (device.contains(".") && device == deviceInLine) {
                return true;
            } else if (!device.contains(".") && deviceInLine.split(".")[0].trimmed() == device) {
                return true;
            }
        }
    }
    return false;
}

void MainWindow::on_Btn_selectFunction_clicked()
{
    //断开连接
    disconnect(systemEntity, &SystemEntity::solvingStarted, this, &MainWindow::onSolvingStarted);
    disconnect(systemEntity, &SystemEntity::solvingFinished, this, &MainWindow::onSolvingFinished);
    disconnect(systemEntity, &SystemEntity::progressUpdated, this, &MainWindow::onProgressUpdated);
    disconnect(systemEntity, &SystemEntity::resultEntityListUpdated, this, &MainWindow::onResultEntityListUpdated);
    disconnect(systemEntity, &SystemEntity::outlierObsUpdated, this, &MainWindow::onOutlierObsUpdated);

    QString systemDescription = currentModel.getSystemDescription();
    SelectFunctionDialog dialog(systemEntity, systemDescription,functionDescription, this); // Pass systemEntity here
    if (dialog.exec() == QDialog::Accepted) {
        // 将待诊断功能的相关数据传递到MainWindow中
        ui->table_result->setRowCount(0);
        testItemList.clear();
        ui->table_test->setRowCount(0);
        ui->table_outlierObs->setRowCount(0);
        functionInfoMap = dialog.getFunctionInfoMap();
        systemEntity->setFunctionInfoMap(functionInfoMap);
        variableRangeConfig = dialog.getVariableRangeConfig();
        systemEntity->setVariableRangeConfig(variableRangeConfig);
        //功能必要条件作为初始观测（假定这些条件都满足作为"未实行"的初始观测）
        for (const TestItem &item : dialog.getLocalTestItemList()) {
            insertIntoTestTable(item.variable, item.value, item.confidence, item.checkState,item.testType);
        }
        //要在getLocalTestItemList之后调用getLocalLink
        currentFunctionName = dialog.getCurrentfunctionName();
        currentFunctionLink = dialog.getLocalLink();//根据所选择的"功能穿透"/"逐级求解"会返回不同的结果

        //qDebug()<<"functionInfoMap"<<functionInfoMap.keys();
        SystemStructure currentFunctionStructure(ui->textEditSystemDiscription->toPlainText(),currentFunctionLink);
        //        qDebug()<<"\ngetCurrentfunctionName:"<<dialog.getCurrentfunctionName();
        //        qDebug()<<"\ngetFunctionLinkMap:"<<dialog.getFunctionLinkMap();
        //        qDebug()<<"\ngetFunctionDependencyMap:"<<dialog.getFunctionDependencyMap();
        //        qDebug()<<"\ngetFunctionComponentDependencyMap:"<<dialog.getFunctionComponentDependencyMap();
        //        qDebug()<<"\ncomponentFailureProbability:"<<systemEntity->componentFailureProbability;
        //qDebug()<<"\ngetPortListInConnectionList:"<<currentFunctionStructure.getPortListInConnectionList();
        qDebug()<<"\ngetCroppedSystemDescription:"<<currentFunctionStructure.getCroppedSystemDescription();

        diagnosisGraph = new DiagnosisGraph();
        // 使用提供的数据构建图
        diagnosisGraph->buildGraph(
                    currentFunctionName,
                    functionInfoMap,
                    currentFunctionStructure.getPortListInConnectionList(),
                    systemEntity->componentFailureProbability);
        qDebug()<<"currentFunctionRoute:\n"<<diagnosisGraph->funcNameToRouteMap[currentFunctionName];

        //更新离线诊断结果表格
        completeResultEntityList = dialog.getLocalResultEntityList();
        currentResultEntityList = completeResultEntityList;
        for (int i = 0; i < completeResultEntityList.size(); ++i) {
            const resultEntity& result = completeResultEntityList[i];
            insertIntoResultTable(result.getComponentNames(),result.getFailureModes(),result.getProbability());
        }
        ui->table_result->resizeColumnsToContents();//调整列宽
        resultProcessAndUpdateColor();

        //保存系统功能到数据库
        functionDescription = dialog.getLocalFunctionDescription();
        if (currentModelName.isEmpty()) {
            QMessageBox::warning(nullptr, "错误", "没有打开的模型",
                                 QMessageBox::Ok, QMessageBox::NoButton);
            return;
        }
        currentModel.setFunctionDiscription(functionDescription);

        //        QMessageBox::StandardButton reply;
        //        reply = QMessageBox::question(this, "是否保存到数据库", "是否将系统模型及功能保存到数据库", QMessageBox::Yes|QMessageBox::No);
        //        if (reply == QMessageBox::No)
        //            return;
        //        if(!database->updateModel(currentModel))
        //            QMessageBox::warning(nullptr, "通知", "保存功能失败","确定");
        //        else
        //            QMessageBox::information(nullptr, "通知", "保存系统模型及功能成功","确定");
    }

    //重建连接
    connect(systemEntity, &SystemEntity::solvingStarted, this, &MainWindow::onSolvingStarted);
    connect(systemEntity, &SystemEntity::solvingFinished, this, &MainWindow::onSolvingFinished);
    connect(systemEntity, &SystemEntity::progressUpdated, this, &MainWindow::onProgressUpdated);
    connect(systemEntity, &SystemEntity::resultEntityListUpdated, this, &MainWindow::onResultEntityListUpdated);
    connect(systemEntity, &SystemEntity::outlierObsUpdated, this, &MainWindow::onOutlierObsUpdated);
}
void MainWindow::insertIntoResultTable(const QString& componentNames, const QString& failureModes, const double& probability)
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
}

void MainWindow::insertIntoTestTable(const QString& variable, const QString& value, const double& confidence, Qt::CheckState checkState, const QString& obsType)
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

    //CbTestVal->setList(systemEntity->obsVarsList);
    //CbTestVal->setMyCurrentText(variable);
    if(obsType=="依赖功能" || obsType=="参照功能")
    {
        qDebug()<<"obsType:"<<obsType;
        CbTestVal->setList(functionInfoMap.keys());
        CbTestVal->setMyCurrentText(variable);
        varType = "function";
        CbTestVal2->setList({"功能正常","功能异常"});
        QString connector = " = ";
        if(value!="功能正常" && value!="功能异常"){CbTestVal2->setCurrentText("功能正常");connector = " != ";}
        else CbTestVal2->setCurrentText(value);

        CbTestVal->lineEdit()->home(false);// 设置光标到行编辑的开始位置,避免功能名称太长只显示尾部
        TestItem actC = functionInfoMap.value(variable).actuatorConstraint;
        variableTooltip=actC.variable + connector + actC.value;//功能提示：所选功能变量约束(constraint)中类型(type)为“功能执行器”项的值（value）
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
            if(CbTestVal->currentText().endsWith("u")) CbTestVal2->setList(obsTemplates["AC380_3P_u"]);
            if(CbTestVal->currentText().endsWith("i")) CbTestVal2->setList(obsTemplates["AC380_3P_i"]);
            CbTestVal2->setCurrentText(value);
        } else if (varType == "Real") {
            if(CbTestVal->currentText().endsWith("u")) CbTestVal2->setList(obsTemplates["AC220_1P_u"]);
            if(CbTestVal->currentText().endsWith("i")) CbTestVal2->setList(obsTemplates["AC220_1P_i"]);
            if(CbTestVal->currentText().endsWith("f")) CbTestVal2->setList(obsTemplates["Hydro_f"]);
            if(CbTestVal->currentText().endsWith("p")) CbTestVal2->setList(obsTemplates["Hydro_p"]);
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
            if(checkState == Qt::Checked )mConfidence=0.9;
            if(checkState == Qt::Unchecked )mConfidence=0.5;
        }
        else if(varType == "function")//约束描述类型为"依赖功能"或"参照功能"的，先暂定置信度为0.5  //TODO 后面改为根据功能的失效概率计算初始置信度
        {
            if(checkState == Qt::Checked )mConfidence=0.5;
            if(checkState == Qt::Unchecked )mConfidence=0.1;
        }
        else
        {
            if(checkState == Qt::Checked )mConfidence=0.85;
            if(checkState == Qt::Unchecked )mConfidence=0.1;
        }
    }
    CbTestVal->setStyleSheet("QComboBox { background-color: white; }");
    QTableWidgetItem* item = new QTableWidgetItem(variable);
    if(variableTooltip!="")item->setToolTip(variableTooltip); // 设置变量的悬停提示
    CbTestVal->setTableItem(item);
    ui->table_test->setItem(crrRow, 0, item); // Set QTableWidgetItem before QComboBox
    ui->table_test->setCellWidget(crrRow, 0, CbTestVal); // Set QComboBox after QTableWidgetItem
    connect(CbTestVal, &MyComboBox::editFinish, this, &MainWindow::onTableTestItemChanged);

    //第2列：变量值
    QTableWidgetItem* item2 = new QTableWidgetItem(value);
    if(valueTooltip!="")item2->setToolTip(valueTooltip); // 设置值的悬停提示
    CbTestVal2->setTableItem(item2);
    ui->table_test->setItem(crrRow, 1, item2);
    ui->table_test->setCellWidget(crrRow, 1, CbTestVal2);
    connect(CbTestVal2, &MyComboBox::editFinish, this, &MainWindow::onTableTestItemChanged);

    //第3列：置信度
    ui->table_test->setItem(crrRow,2,new QTableWidgetItem(QString::number(mConfidence)));

    //第4列：是否已实行
    QTableWidgetItem *Cb_ObsExecuted=new QTableWidgetItem();
    Cb_ObsExecuted->setCheckState(checkState);
    ui->table_test->setItem(crrRow,3,Cb_ObsExecuted);

    // 添加obsType到第5列：变量类型
    QStringList const OBSTYPE={ "一般变量", "功能执行器","边界条件","依赖功能","参照功能"};
    if(OBSTYPE.contains(obsType))
    {
        ui->table_test->setItem(crrRow, 4, new QTableWidgetItem(obsType));
    }
    else{//如果没有预设观测类型，则创建下拉框
        MyComboBox *CbTestType = new MyComboBox();
        CbTestType->setList(OBSTYPE);
        CbTestType->setCurrentText(OBSTYPE[0]);
        QTableWidgetItem* item3 = new QTableWidgetItem(OBSTYPE[0]);
        CbTestType->setTableItem(item3);
        ui->table_test->setItem(crrRow, 4, item3);
        ui->table_test->setCellWidget(crrRow, 4, CbTestType);
        connect(CbTestType, &MyComboBox::editFinish, this, &MainWindow::onTableTestItemChanged);
    }

    connect(ui->table_test, &QTableWidget::itemChanged, this, &MainWindow::onTableTestItemChanged);

    TestItem newItem;
    newItem.variable = variable;
    newItem.value = value;
    newItem.confidence = mConfidence;
    newItem.checkState = checkState;
    newItem.testType = obsType;
    testItemList.append(newItem);

    if(variable!="")checkDuplicateAndUpdateColor();
}


void MainWindow::onTableTestItemChanged(QTableWidgetItem* item) {
    ui->table_test->disconnect(SIGNAL(itemChanged(QTableWidgetItem*)));
    int row = item->row();
    MyComboBox *CbTestVal1 = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 0));
    MyComboBox *CbTestVal2 = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 1));
    MyComboBox *CbTestVal4 = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 4));
    //qDebug()<<"onTableTestItemChanged row: "<<row<< " col:"<<item->column();
    QString varType =  systemEntity->obsVarsMap[testItemList[row].variable];

    if(row < testItemList.size()) {
        switch(item->column()) {
        case 0:
            if(testItemList[row].variable == CbTestVal1->currentText())break;
            testItemList[row].variable = CbTestVal1->currentText();
            varType = systemEntity->obsVarsMap[testItemList[row].variable];
            if(testItemList[row].testType.contains("功能"))varType="function";

            if(varType=="function")
            {
                if(CbTestVal2->currentText()!="功能正常" && CbTestVal2->currentText()!="功能异常")
                {
                    CbTestVal2->setList({"功能正常","功能异常"});
                    CbTestVal2->setCurrentText("功能正常");
                }
                CbTestVal1->lineEdit()->home(false);// 设置光标到行编辑的开始位置,避免功能名称太长只显示尾部
                if(testItemList[row].checkState == Qt::Checked)testItemList[row].confidence = 0.9;
                else testItemList[row].confidence = 0.5;
            }
            else
            {
                if (varType == "Bool") {
                    CbTestVal2->setList(QStringList({"true", "false"}));
                    if(testItemList[row].checkState == Qt::Checked) testItemList[row].confidence = 0.9;
                    if(testItemList[row].checkState == Qt::Unchecked) testItemList[row].confidence = 0.5;
                } else if (varType == "(Array Int Real)") {
                    if(testItemList[row].variable.endsWith("u")) CbTestVal2->setList(MainWindow::obsTemplates["AC380_3P_u"]);
                    if(testItemList[row].variable.endsWith("i")) CbTestVal2->setList(MainWindow::obsTemplates["AC380_3P_i"]);
                    if(testItemList[row].checkState == Qt::Checked) testItemList[row].confidence = 0.85;
                    if(testItemList[row].checkState == Qt::Unchecked) testItemList[row].confidence = 0.1;
                } else if (varType == "Real") {
                    if(testItemList[row].variable.endsWith("u")) CbTestVal2->setList(MainWindow::obsTemplates["AC220_1P_u"]);
                    if(testItemList[row].variable.endsWith("i")) CbTestVal2->setList(MainWindow::obsTemplates["AC220_1P_i"]);
                    if(testItemList[row].variable.endsWith("p")) CbTestVal2->setList(MainWindow::obsTemplates["Hydro_p"]);
                    if(testItemList[row].variable.endsWith("f")) CbTestVal2->setList(MainWindow::obsTemplates["Hydro_f"]);
                    if(testItemList[row].checkState == Qt::Checked) testItemList[row].confidence = 0.85;
                    if(testItemList[row].checkState == Qt::Unchecked) testItemList[row].confidence = 0.1;
                } else {
                    CbTestVal2->setList(QStringList({""}));
                }
            }
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
            testItemList[row].checkState = item->checkState();
            if(testItemList[row].testType.contains("功能"))varType="function";
            if(testItemList[row].checkState == Qt::Checked)
            {
                if(varType == "Bool" )testItemList[row].confidence = 0.9;
                else testItemList[row].confidence = 0.85;
                if(varType == "function" )testItemList[row].confidence = 0.5;
            }
            else
            {
                if(varType == "Bool")testItemList[row].confidence = 0.5;
                else testItemList[row].confidence = 0.1;
                if(varType == "function" )testItemList[row].confidence = 0.1;
            }
            break;
        case 4:
            if(testItemList[row].testType == CbTestVal4->currentText())break;
            testItemList[row].testType = CbTestVal4->currentText();
            if(testItemList[row].testType.contains("功能"))varType="function";
            //如果类型为"依赖功能"，则："变量"改为功能列表;"约束值"改为"功能正常"，"功能异常"
            if(varType=="function")
            {
                CbTestVal1->setList(functionInfoMap.keys()); //"变量"改为功能列表
                CbTestVal2->setList({"功能正常","功能异常"});
            }
            else
            {
                CbTestVal1->setList(systemEntity->obsVarsList);
                CbTestVal2->setList({});
            }
            testItemList[row].variable = CbTestVal1->currentText();
            varType =  systemEntity->obsVarsMap[testItemList[row].variable];
            if(testItemList[row].checkState == Qt::Checked)
            {
                if(varType == "Bool" || varType == "function")testItemList[row].confidence = 0.9;
                else testItemList[row].confidence = 0.85;
            }
            else
            {
                if(varType == "Bool"|| varType == "function")testItemList[row].confidence = 0.5;
                else testItemList[row].confidence = 0.1;
            }
            break;
        }
        ui->table_test->item(row, 2)->setText(QString::number(testItemList[row].confidence));
        QString tooltip;
        TestItem actC = functionInfoMap.value(testItemList[row].variable).actuatorConstraint;
        if(testItemList[row].value=="功能正常")tooltip=actC.variable+ " = " +actC.value;//功能提示：所选功能变量约束(constraint)中类型(type)为“功能执行器”项的值（value）
        if(testItemList[row].value=="功能异常")tooltip=actC.variable+ " != " +actC.value;//功能提示：所选功能变量约束(constraint)中类型(type)为“功能执行器”项的值（value）
        if(tooltip!="")
        {
            CbTestVal1->tableItem->setToolTip(tooltip); // 设置值的悬停提示
            CbTestVal2->tableItem->setToolTip(tooltip);
        }

    }
    connect(ui->table_test, SIGNAL(itemChanged(QTableWidgetItem*)), this, SLOT(onTableTestItemChanged(QTableWidgetItem*)));
}

void MainWindow::on_Btn_DelObs_clicked()
{
    QItemSelectionModel *select = ui->table_test->selectionModel();

    // 如果有选中的行，则删除
    if(select->hasSelection())
    {
        //重置当前结果为完整求解结果
        currentResultEntityList = completeResultEntityList;

        QModelIndexList selectedRows = select->selectedRows();
        // 记录是否存在红色背景的行被删除
        bool redRowDeleted = false;

        // 首先将所有要删除的行号保存在一个列表中
        QList<int> rowsToDelete;
        for(const auto& index : selectedRows) {
            rowsToDelete.append(index.row());
        }

        // 按照行号从大到小排序，这样我们可以从后往前删除，避免影响尚未删除的行的行号
        std::sort(rowsToDelete.begin(), rowsToDelete.end(), std::greater<int>());

        // 从后向前删除选中的行
        for(int row : rowsToDelete) {
            // Get the MyComboBox from the first column
            MyComboBox *cb = qobject_cast<MyComboBox*>(ui->table_test->cellWidget(row, 0));
            if (cb) {
                if (cb->styleSheet().contains("background-color: red")) {
                    redRowDeleted = true;
                }
            }
            // 删除ui->table_test中的行
            ui->table_test->removeRow(row);
            // 删除testItemList中对应的项
            testItemList.removeAt(row);
        }

        // 如果删除了红色背景的行，重新检查剩余的行，更新它们的背景色
        if (redRowDeleted) {
            checkDuplicateAndUpdateColor();
        }
    }
}
void MainWindow::on_Btn_AddObs_clicked()
{
    // 插入新的行到ui->table_test
    //insertIntoTestTable("","", 0.0,Qt::Checked,"一般变量");
    insertIntoTestTable("","", 0.0,Qt::Checked,"");
}
void MainWindow::on_Btn_RecommendObs_clicked()
{
    if (!currentFunctionName.isEmpty() && !currentResultEntityList.isEmpty())
    {
        QList<TestItem> recommendObs = diagnosisGraph->getRecommendTestItemList(currentFunctionName, currentResultEntityList, isPenetrativeSolve);

        // 将testItemList中的变量放入QSet
        QSet<QString> existingVariables;
        for (const TestItem &item : testItemList) {
            existingVariables.insert(item.variable.trimmed());
        }

        QDialog dialog(this);
        dialog.resize(300, 500);
        dialog.setWindowTitle("选择进一步的观测");

        QTableWidget *tableWidget = new QTableWidget(&dialog);
        tableWidget->setColumnCount(2);
        tableWidget->setHorizontalHeaderLabels(QStringList() << "观测量" << "信息熵");
        tableWidget->horizontalHeader()->setStretchLastSection(true);
        tableWidget->setSelectionBehavior(QAbstractItemView::SelectRows);
        tableWidget->setSelectionMode(QAbstractItemView::SingleSelection);

        int row = 0;
        bool firstCheckedRowFound = false;  // 用于跟踪是否已经找到第一个 item.checkState == Qt::Checked 的项
        for (const TestItem &item : recommendObs) {
            if (existingVariables.contains(item.variable.trimmed())) continue;
            tableWidget->insertRow(row);
            QTableWidgetItem *newItem1 = new QTableWidgetItem(item.variable);
            QTableWidgetItem *newItem2 = new QTableWidgetItem(QString::number(item.confidence, 'f', 3));
            // 检查 item 的 checkState，并设置背景色
            if (item.checkState == Qt::Checked) {
                int adj =220-item.level*40;
                if(adj>255)adj=255;
                if(adj<0)adj=0;
                QColor lightGreen(140, adj, 140);  // 定义淡绿色
                newItem1->setBackgroundColor(lightGreen);
                newItem2->setBackgroundColor(lightGreen);

                // 如果这是第一个 item.checkState == Qt::Checked 的项，则选中它
                if (!firstCheckedRowFound) {
                    tableWidget->selectRow(row);
                    firstCheckedRowFound = true;  // 更新标志
                }

            }
            tableWidget->setItem(row, 0, newItem1);
            tableWidget->setItem(row, 1, newItem2);

            row++;
        }
        //if(row > 0) tableWidget->selectRow(0);

        QPushButton *button = new QPushButton("确定", &dialog);
        connect(button, &QPushButton::clicked, &dialog, &QDialog::accept);

        QVBoxLayout *layout = new QVBoxLayout(&dialog);
        layout->addWidget(tableWidget);
        layout->addWidget(button);

        if (dialog.exec() == QDialog::Accepted) {
            int selectedRow = tableWidget->currentRow();
            if (selectedRow != -1) {
                QTableWidgetItem *selectedItem = tableWidget->item(selectedRow, 0);
                if (selectedItem) { // 确保所选项不为空
                    QString variable = selectedItem->text();
                    insertIntoTestTable(variable.trimmed(), "", 0.0, Qt::Checked, "一般变量");
                }
            }
        }

    }
}

void MainWindow::onConfirmButtonClicked()
{
    QPushButton* senderBtn = qobject_cast<QPushButton*>(sender()); // get the button that emitted the signal
    if (senderBtn) {
        int obsRow = senderBtn->property("obsRow").toInt(); // get the obs row number

        QTableWidgetItem* itemCheck = ui->table_test->item(obsRow, 3);
        if (itemCheck->checkState() == Qt::Unchecked) {
            itemCheck->setCheckState(Qt::Checked);
        }
        else if (itemCheck->checkState() == Qt::Checked) {
            QTableWidgetItem* itemConfidence = ui->table_test->item(obsRow, 2);
            double confidence = itemConfidence->text().toDouble();
            //计算确认后的置信度
            // 当 confidence >= 0.95 时，每按一次增加0.1，最多增加到 1.0
            if (confidence >= 0.95 && confidence < 1.0) {
                confidence += 0.04;
                if (confidence > 1.0) {
                    confidence = 1.0;
                }
            }
            else if(confidence<0.95)
            {
                confidence = 0.95;
            }
            itemConfidence->setText(QString::number(confidence));
        }
    }
}
//完整求解按钮
void MainWindow::on_Btn_SolveAns_clicked()
{
    qDebug()<<testItemList;
    int solveMode = ui->comboBoxSolveMode->currentIndex();
    completeResultEntityList = systemEntity->completeSolve(ui->textEditSystemDiscription->toPlainText(), testItemList,solveMode);
    currentResultEntityList = completeResultEntityList;
}

void testMatch(QString value, QString variable = "M.A1_A2.u") {
    QRegularExpression re("([\\[\\(])?\\s*([\\d\\.]+)?\\s*,\\s*([\\d\\.]+)?\\s*([\\]\\)])?|(<=|>=|<|>)\\s*([\\d\\.]+)|(smt\\(\\S+.+\\))");
    QRegularExpressionMatch match = re.match(value.trimmed());
    QString description;
    if(match.hasMatch()) {
        if(match.captured(1).length() > 0 && match.captured(4).length() > 0) {
            QString startCompare = match.captured(1) == "[" ? ">=" : ">";
            QString endCompare = match.captured(4) == "]" ? "<=" : "<";
            double startValue = match.captured(2).toDouble();
            double endValue = match.captured(3).toDouble();
            description = QString("(assert (and (%1 %2 %3)(%4 %2 %5)))")
                    .arg(startCompare)
                    .arg(variable)
                    .arg(QString::number(startValue, 'g'))
                    .arg(endCompare)
                    .arg(QString::number(endValue, 'g'));
        } else if(match.captured(5).length() > 0) {
            QString compare = match.captured(5);
            double compareValue = match.captured(6).toDouble();
            description = QString("(assert (%1 %2 %3))")
                    .arg(compare)
                    .arg(variable)
                    .arg(QString::number(compareValue, 'g'));
        } else if(match.captured(7).length() > 0) {
            QString smtCode = match.captured(7).trimmed().remove("smt").replace("%1", variable);
            description = QString("(assert %1)").arg(smtCode);
        }
    }
    qDebug() << value << ":" << description;
}

void MainWindow::onProgressUpdated(int progress) {
    ui->progressBar->setValue(progress);
}

void MainWindow::onResultEntityListUpdated(const QList<resultEntity>& resultEntityList) {
    ui->table_result->setUpdatesEnabled(false); // Disable updates

    for (int i = lastResultEntityIndex; i < resultEntityList.size(); ++i) {
        const resultEntity& result = resultEntityList[i];
        insertIntoResultTable(result.getComponentNames(),result.getFailureModes(),result.getProbability());
        currentResultEntityList.append(result);
    }
    ui->table_result->resizeColumnsToContents();//调整列宽
    ui->table_result->sortItems(2, Qt::DescendingOrder);//按概率对结果排序

    lastResultEntityIndex = resultEntityList.size(); // Update the last index
    ui->table_result->setUpdatesEnabled(true); // Re-enable updates
}

void MainWindow::onOutlierObsUpdated(const QMap<QString, double>& outlierObs)
{
    QMap<QString, QPair<QString, double>> tableData;
    // 合并相同观测的原因和概率
    for (auto it = outlierObs.begin(); it != outlierObs.end(); ++it) {
        QStringList splitKey = it.key().split(',');
        QString obsComponent = splitKey[0];
        QString reason = splitKey[1];
        if (tableData.contains(obsComponent)) {
            // 如果观测已经存在，更新原因和概率
            auto& data = tableData[obsComponent];
            if (!data.first.contains(reason)) {
                data.first += "," + reason;
            }
            data.second += it.value();
        } else {
            // 如果观测不存在，添加到tableData中
            tableData.insert(obsComponent, qMakePair(reason, it.value()));
        }
    }
    // 转换为QVector并排序
    QVector<QPair<QString, QPair<QString, double>>> sortedData;
    for (auto it = tableData.begin(); it != tableData.end(); ++it) {
        sortedData.append(qMakePair(it.key(), it.value()));
    }
    std::sort(sortedData.begin(), sortedData.end(), [](const QPair<QString, QPair<QString, double>>& a, const QPair<QString, QPair<QString, double>>& b) {
        return a.second.second > b.second.second;
    });
    // 插入到表格中
    for (auto& data : sortedData) {
        int newRow = ui->table_outlierObs->rowCount();
        ui->table_outlierObs->insertRow(newRow);
        ui->table_outlierObs->setItem(newRow, 0, new QTableWidgetItem(data.first));

        //检查reasonList中是否存在观测阻滞，如果存在，则将其移到最前面来
        QStringList reasonList=data.second.first.simplified().split(",");
        if (reasonList.contains("观测阻滞")) {
            reasonList.removeAll("观测阻滞");  // 删除所有"观测阻滞"项
            reasonList.prepend("观测阻滞");  // 将"观测阻滞"添加到最前面
        }
        ui->table_outlierObs->setItem(newRow, 1, new QTableWidgetItem(reasonList.join(",")));
        ui->table_outlierObs->setItem(newRow, 2, new NumericTableWidgetItem(QString::number(data.second.second,'e',2)));
        // 创建确认按钮，并添加到表格中
        QPushButton* btn_confirm = new QPushButton();
        btn_confirm->setText("确认");
        QString obsKey = data.first.split(",")[0];
        obsKey.remove(0, 3);
        btn_confirm->setProperty("obsRow", obsKey.toInt()-1);
        ui->table_outlierObs->setCellWidget(newRow, 3, btn_confirm);
        connect(btn_confirm, &QPushButton::clicked, this, &MainWindow::onConfirmButtonClicked);
    }
    // 调整列宽以适应内容
    ui->table_outlierObs->resizeColumnsToContents();
    ui->table_outlierObs->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);
}

void MainWindow::onSolvingStarted() {
    timeSlove.restart();
    ui->progressBar->setValue(0);
    ui->textEditConflictSets->clear();

    // 清空表格
    ui->table_result->setRowCount(0);
    currentResultEntityList.clear();
    ui->table_outlierObs->setRowCount(0);
    lastResultEntityIndex =0;

}

void MainWindow::onSolvingFinished(QStringList ans) {
    for (QStringList::iterator it = ans.begin();
         it != ans.end(); ++it) {
        QString current = *it;
        ui->textEditConflictSets->append(current);
    }

    if(ans.size()==0){
        ui->textEditConflictSets->append("系统正常");
    }
    resultProcessAndUpdateColor();
    labViewCord->setText("求解时间：" + QString::number(timeSlove.elapsed()/1000.0));
}

void MainWindow::resultProcessAndUpdateColor(){
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

    // 更新异常观测的表格
    // 当没有黄色背景行时改变table_outlierObs中的行背景色
    if (!hasYellowRows) {
        int rows = ui->table_outlierObs->rowCount();
        double maxP=sqrt(1.0e-4);
        double minP=sqrt(1.0e-8);
        if(rows > 1)
        {
            maxP=  sqrt(ui->table_outlierObs->item(0, 2)->text().toDouble());
            minP=  sqrt(ui->table_outlierObs->item(rows-1, 2)->text().toDouble());
        }
        double rangeP = 255/(maxP - minP);
        minP*=0.9;
        //        bool containsObstructionItem = false;
        //        // 首先检查第2列是否有包含"观测阻滞"的项
        //        for (int i = 0; i < rows; ++i) {
        //            QString secondColumnText = ui->table_outlierObs->item(i, 1)->text();
        //            if (secondColumnText.contains("观测阻滞")) {
        //                containsObstructionItem = true;
        //                break;
        //            }
        //        }
        for (int i = 0; i < rows; ++i) {
            //            // 如果第2列中存在包含"观测阻滞"的项，对这些项进行操作
            //            if (containsObstructionItem) {
            //                QString secondColumnText = ui->table_outlierObs->item(i, 1)->text();
            //                if (!secondColumnText.contains("观测阻滞")) {
            //                    continue;
            //                }
            //            }
            // 获取第三列的文本（异常概率）并转换为double类型
            QString thirdColumnText = ui->table_outlierObs->item(i, 2)->text();
            double probability = thirdColumnText.toDouble();

            // 计算颜色深度
            //int depth = static_cast<int>((probability - 1.0e-8) / (1.0e-4 - 1.0e-8) * 255);
            int depth = static_cast<int>((sqrt(probability) - minP) * rangeP);
            depth = std::max(0, std::min(255, depth));  // 确保在0到255之间
            int green = 0;int blue = 0;

            if (depth >= 128) green = 510 - depth*2;
            else {green = 255;blue = 255 - depth * 2;}

            // 创建一个根据概率深度的黄色背景色
            QColor yellowBackground(255, green, blue);

            // 将该行背景色改为colorBackground
            for(int j = 0; j < ui->table_outlierObs->columnCount()-1; ++j) {
                ui->table_outlierObs->item(i, j)->setBackgroundColor(yellowBackground);
            }
        }
    }
}

void MainWindow::applyVariableRangeConfigFromString(const QString &functionXml)
{
    variableRangeConfig.clear();
    if (functionXml.trimmed().isEmpty()) {
        systemEntity->setVariableRangeConfig(variableRangeConfig);
        return;
    }

    QDomDocument doc;
    if (!doc.setContent(functionXml)) {
        systemEntity->setVariableRangeConfig(variableRangeConfig);
        return;
    }

    QDomElement root = doc.firstChildElement(QString("root"));
    if (!root.isNull()) {
        variableRangeConfig = rangeconfig::VariableRangeConfig::fromXml(root.firstChildElement(QString("variableRangeConfig")));
    }

    systemEntity->setVariableRangeConfig(variableRangeConfig);
}

void MainWindow::refreshFunctionStateFromModel()
{
    const QString funcDesc = currentModel.getFunctionDiscription();
    functionInfoMap = testability::FunctionCatalog::parse(funcDesc);
    systemEntity->setFunctionInfoMap(functionInfoMap);
    applyVariableRangeConfigFromString(funcDesc);
}

void MainWindow::on_radioButton_Penetrative_toggled(bool checked)
{
    if(ui->radioButton_Penetrative->isChecked())isPenetrativeSolve=true;
    else isPenetrativeSolve = false;
}

void MainWindow::on_Btn_IncrementalSolve_clicked()
{
    qDebug()<<"**************************开始进行增量求解**************************";
    QList<resultEntity> excludedResults;
    ui->table_result->setUpdatesEnabled(false); // Disable updates
    ui->table_result->setRowCount(0);
    SystemStructure currentFunctionStructure(ui->textEditSystemDiscription->toPlainText(),currentFunctionLink);
    qDebug()<<"currentFunctionLink:"<<currentFunctionLink;
    qDebug().noquote().nospace()<<"CroppedSystemDescription:\n"<<currentFunctionStructure.getCroppedSystemDescription();
    systemEntity->incrementalSolve(currentFunctionStructure.getCroppedSystemDescription(), testItemList, currentResultEntityList, excludedResults);
    int finalSize = currentResultEntityList.size(); // 记录增量求解后的候选解数量
    for (int i = 0; i < finalSize; ++i) {
        const resultEntity& result = currentResultEntityList[i];
        insertIntoResultTable(result.getComponentNames(),result.getFailureModes(),result.getProbability());
    }
    ui->table_result->resizeColumnsToContents();//调整列宽
    //ui->table_result->sortItems(2, Qt::DescendingOrder);//按概率对结果排序
    resultProcessAndUpdateColor();
    ui->table_result->setUpdatesEnabled(true); // Enable updates

    // 显示排除的候选解
    int excludedCount = excludedResults.size();
    QMessageBox messageBox;
    messageBox.setWindowTitle("增量求解结果");
    messageBox.setText(QString("本次增量求解排除了%1个候选诊断解").arg(excludedCount));
    if (excludedCount > 0) {
        // 创建一个详细信息文本，其中包括被排除的候选解
        QString details;
        for (const resultEntity& result : excludedResults) {
            // 自定义格式化被排除的候选解
            details += result.getComponentNames() + ": " + result.getFailureModes() + "\n";
        }
        messageBox.setDetailedText(details); // 设置详细文本
    }
    messageBox.exec();
}

void MainWindow::on_actionGenerateDMatrix_triggered()
{
    if (!systemEntity) {
        QMessageBox::warning(this, tr("提示"), tr("请先加载模型"));
        return;
    }

    const QString systemDescription = currentModel.getSystemDescription();
    if (systemDescription.trimmed().isEmpty()) {
        QMessageBox::warning(this, tr("提示"), tr("系统描述为空，无法生成D矩阵"));
        return;
    }

    if (functionInfoMap.isEmpty() && !currentModel.getFunctionDiscription().isEmpty()) {
        refreshFunctionStateFromModel();
    } else {
        systemEntity->setVariableRangeConfig(variableRangeConfig);
    }

    DMatrixOptionsDialog optionsDialog(this);
    optionsDialog.setWindowTitle(tr("生成D矩阵"));
    optionsDialog.setOptions(lastDMatrixOptions);
    if (optionsDialog.exec() != QDialog::Accepted) {
        return;
    }

    testability::DMatrixBuildOptions options = optionsDialog.options();
    lastDMatrixOptions = options;

    testability::DMatrixBuilder builder(systemEntity);
    builder.setFunctionInfoMap(functionInfoMap);

    qDebug().noquote() << "[DMatrix] Function map size =" << functionInfoMap.size();
    for (auto it = functionInfoMap.constBegin(); it != functionInfoMap.constEnd(); ++it) {
        const FunctionInfo &info = it.value();
        qDebug().noquote() << "  function" << info.functionName
                           << "rawAll=" << info.allRelatedComponent
                           << "parsedAll=" << info.allComponentList;
    }

    QVector<testability::FaultDefinition> faults = builder.collectFunctionFaults();
    if (faults.isEmpty()) {
        QMessageBox::warning(this, tr("提示"), tr("未找到功能故障定义"));
        return;
    }

    testability::SmtFacade smt = testability::SmtFacade::fromSystemDescription(*systemEntity, systemDescription);

    QVector<testability::TestDefinition> tests;
    QSet<QString> seenIds;

    auto appendTests = [&](const QVector<testability::TestDefinition> &list) {
        for (const auto &test : list) {
            if (seenIds.contains(test.id)) {
                continue;
            }
            seenIds.insert(test.id);
            tests.append(test);
        }
    };

    appendTests(builder.collectFunctionTests());
    appendTests(builder.collectModeTests(smt));
    appendTests(builder.collectSignalTests(smt, options));

    if (tests.isEmpty()) {
        QMessageBox::warning(this, tr("提示"), tr("未生成任何测试"));
        return;
    }

    QApplication::setOverrideCursor(Qt::BusyCursor);
    testability::DMatrixBuildResult matrix = builder.buildDMatrix(faults, tests, smt, options);
    QApplication::restoreOverrideCursor();

    QString outputDir = options.outputDirectory.trimmed();
    if (outputDir.isEmpty()) {
        outputDir = QDir::current().filePath(QStringLiteral("output"));
    }

    QString csvPath;
    QString metadataPath;

    QDir dir(outputDir);
    if (!dir.exists()) {
        if (!dir.mkpath(QStringLiteral("."))) {
            QMessageBox::warning(this,
                                 tr("导出失败"),
                                 tr("无法创建目录 %1").arg(QDir::toNativeSeparators(outputDir)));
            outputDir.clear();
        }
    }

    bool exported = false;
    if (!outputDir.isEmpty()) {
        options.outputDirectory = dir.absolutePath();
        exported = builder.exportDMatrix(matrix, currentModelName, options, options.outputDirectory, &csvPath, &metadataPath);
        if (!exported) {
            QMessageBox::warning(this,
                                 tr("导出失败"),
                                 tr("无法写入 D 矩阵文件到 %1").arg(QDir::toNativeSeparators(options.outputDirectory)));
        }
    } else {
        options.outputDirectory.clear();
    }

    lastDMatrixOptions = options;

    auto *viewer = new DMatrixViewerDialog(this);
    viewer->setAttribute(Qt::WA_DeleteOnClose);
    viewer->setMatrix(matrix, options, csvPath, metadataPath);
    viewer->setWindowTitle(tr("D矩阵查看器"));
    viewer->resize(900, 600);
    viewer->show();
}

void MainWindow::on_actionOpenDMatrix_triggered()
{
    QString baseDir = lastDMatrixOptions.outputDirectory;
    if (baseDir.isEmpty()) {
        baseDir = QDir::current().filePath(QStringLiteral("output"));
    }

    const QString metadataPath = QFileDialog::getOpenFileName(this, tr("打开D矩阵文件"), baseDir, tr("D矩阵元数据 (*.json)"));
    if (metadataPath.isEmpty()) {
        return;
    }

    testability::DMatrixBuildResult matrix;
    testability::DMatrixBuildOptions options = lastDMatrixOptions;
    QString csvPath;
    if (!loadDMatrixFromFiles(metadataPath, &matrix, &options, &csvPath)) {
        QMessageBox::warning(this, tr("打开失败"), tr("无法读取所选 D 矩阵文件"));
        return;
    }

    lastDMatrixOptions = options;

    auto *viewer = new DMatrixViewerDialog(this);
    viewer->setAttribute(Qt::WA_DeleteOnClose);
    viewer->setMatrix(matrix, options, csvPath, metadataPath);
    viewer->setWindowTitle(tr("D矩阵查看器"));
    viewer->resize(900, 600);
    viewer->show();
}

