#include "widget/testeditdialog.h"
#include "ui_testeditdialog.h"

#include <QJsonDocument>
#include <QJsonObject>
#include <QMessageBox>
#include <QUuid>

#pragma execution_character_set("utf-8")

TestEditDialog::TestEditDialog(QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::TestEditDialog)
{
    ui->setupUi(this);
    populateCategory();
    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &TestEditDialog::onAccepted);
    connect(ui->buttonBox, &QDialogButtonBox::rejected, this, &QDialog::reject);
}

TestEditDialog::~TestEditDialog()
{
    delete ui;
}

void TestEditDialog::populateCategory()
{
    ui->comboCategory->addItem(tr("信号测试"), static_cast<int>(TestCategory::Signal));
    ui->comboCategory->addItem(tr("功能测试"), static_cast<int>(TestCategory::Function));
    ui->comboCategory->addItem(tr("故障模式测试"), static_cast<int>(TestCategory::FaultMode));
}

void TestEditDialog::setTest(const GeneratedTest &test)
{
    m_test = test;
    const int categoryIndex = ui->comboCategory->findData(static_cast<int>(test.category));
    if (categoryIndex >= 0)
        ui->comboCategory->setCurrentIndex(categoryIndex);
    ui->editName->setText(test.name);
    ui->editTarget->setText(test.targetId);
    ui->editDetectable->setText(test.detectableFaults.join(QStringLiteral(", ")));
    ui->editIsolatable->setText(test.isolatableFaults.join(QStringLiteral(", ")));
    ui->doubleCost->setValue(test.estimatedCost);
    ui->doubleDuration->setValue(test.estimatedDuration);
    ui->plainDescription->setPlainText(test.description);

    if (test.metrics.isEmpty()) {
        ui->plainMetrics->clear();
    } else {
        QJsonObject obj = QJsonObject::fromVariantMap(test.metrics);
        QJsonDocument doc(obj);
        ui->plainMetrics->setPlainText(QString::fromUtf8(doc.toJson(QJsonDocument::Indented)));
    }
}

GeneratedTest TestEditDialog::test() const
{
    return m_test;
}

void TestEditDialog::onAccepted()
{
    GeneratedTest updated = m_test;

    updated.category = static_cast<TestCategory>(ui->comboCategory->currentData().toInt());
    updated.name = ui->editName->text().trimmed();
    if (updated.name.isEmpty()) {
        QMessageBox::warning(this, tr("提示"), tr("名称不能为空"));
        return;
    }

    updated.targetId = ui->editTarget->text().trimmed();
    updated.description = ui->plainDescription->toPlainText();

    auto parseList = [](const QString &text) {
        QStringList list;
        const QStringList parts = text.split(',', QString::SkipEmptyParts);
        for (const QString &part : parts) {
            const QString item = part.trimmed();
            if (!item.isEmpty())
                list.append(item);
        }
        return list;
    };

    updated.detectableFaults = parseList(ui->editDetectable->text());
    updated.isolatableFaults = parseList(ui->editIsolatable->text());

    updated.estimatedCost = ui->doubleCost->value();
    updated.estimatedDuration = ui->doubleDuration->value();

    const QString metricsText = ui->plainMetrics->toPlainText().trimmed();
    if (metricsText.isEmpty()) {
        updated.metrics.clear();
    } else {
        QJsonParseError error;
        const QJsonDocument doc = QJsonDocument::fromJson(metricsText.toUtf8(), &error);
        if (error.error != QJsonParseError::NoError || !doc.isObject()) {
            QMessageBox::warning(this, tr("提示"), tr("指标字段需要是 JSON 对象"));
            return;
        }
        updated.metrics = doc.object().toVariantMap();
    }

    if (updated.id.isEmpty())
        updated.id = QStringLiteral("user:%1").arg(QUuid::createUuid().toString(QUuid::WithoutBraces));

    m_test = updated;
    accept();
}
