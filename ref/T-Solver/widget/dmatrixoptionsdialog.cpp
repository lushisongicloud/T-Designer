#include "dmatrixoptionsdialog.h"
#include "ui_dmatrixoptionsdialog.h"

#include <QDialogButtonBox>
#include <QDir>
#include <QFileDialog>
#include <QLineEdit>
#include <QToolButton>

DMatrixOptionsDialog::DMatrixOptionsDialog(QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::DMatrixOptionsDialog)
{
    ui->setupUi(this);
    outputDirEdit = findChild<QLineEdit*>(QStringLiteral("lineOutputDir"));
    QToolButton *browseButton = findChild<QToolButton*>(QStringLiteral("btnBrowseOutputDir"));

    ui->comboMode->addItem(tr("保证检测"), QVariant::fromValue(static_cast<int>(testability::DetectMode::Guaranteed)));
    ui->comboMode->addItem(tr("存在检测"), QVariant::fromValue(static_cast<int>(testability::DetectMode::Exists)));

    ui->spinTimeout->setSpecialValueText(tr("无限制"));
    ui->spinTimeout->setMinimum(-1);
    ui->spinTimeout->setMaximum(600000);

    ui->spinTolerance->setSuffix(QStringLiteral("%"));
    ui->spinTolerance->setDecimals(2);
    ui->spinTolerance->setSingleStep(0.5);
    ui->spinTolerance->setRange(0.0, 100.0);

    ui->spinMaxAbs->setMinimum(1.0);
    ui->spinMaxAbs->setMaximum(1000000.0);
    ui->spinMaxAbs->setDecimals(1);

    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &QDialog::accept);
    connect(ui->buttonBox, &QDialogButtonBox::rejected, this, &QDialog::reject);
    if (browseButton) {
        connect(browseButton, &QToolButton::clicked, this, [this]() {
            const QString current = outputDirEdit ? outputDirEdit->text().trimmed() : QString();
            const QString startDir = current.isEmpty() ? QDir::currentPath() : current;
            const QString selected = QFileDialog::getExistingDirectory(this, tr("选择输出目录"), startDir);
            if (!selected.isEmpty() && outputDirEdit) {
                outputDirEdit->setText(QDir(selected).absolutePath());
            }
        });
    }

    setOptions(testability::DMatrixBuildOptions());
}

DMatrixOptionsDialog::~DMatrixOptionsDialog()
{
    delete ui;
}

void DMatrixOptionsDialog::setOptions(const testability::DMatrixBuildOptions &options)
{
    const int modeIndex = options.mode == testability::DetectMode::Guaranteed ? 0 : 1;
    ui->comboMode->setCurrentIndex(modeIndex);
    ui->spinTimeout->setValue(options.timeoutMs < 0 ? -1 : options.timeoutMs);
    ui->checkAutoRange->setChecked(options.autoRange);
    ui->checkTemplateFallback->setChecked(options.fallbackToTemplate);
    ui->spinTolerance->setValue(options.rangeTolerance * 100.0);
    ui->spinMaxAbs->setValue(options.searchMaxAbs);
    ui->checkIncludeInputs->setChecked(options.includeFunctionInputs);

    QString dir = options.outputDirectory;
    if (dir.isEmpty()) {
        dir = QDir::current().filePath(QStringLiteral("output"));
    }
    if (outputDirEdit) {
        outputDirEdit->setText(QDir(dir).absolutePath());
    }
}

testability::DMatrixBuildOptions DMatrixOptionsDialog::options() const
{
    testability::DMatrixBuildOptions opts;
    opts.mode = ui->comboMode->currentIndex() == 0 ? testability::DetectMode::Guaranteed
                                                   : testability::DetectMode::Exists;
    const int timeout = ui->spinTimeout->value();
    opts.timeoutMs = timeout < 0 ? -1 : timeout;
    opts.autoRange = ui->checkAutoRange->isChecked();
    opts.fallbackToTemplate = ui->checkTemplateFallback->isChecked();
    opts.rangeTolerance = ui->spinTolerance->value() / 100.0;
    opts.searchMaxAbs = ui->spinMaxAbs->value();
    opts.includeFunctionInputs = ui->checkIncludeInputs->isChecked();
    if (outputDirEdit) {
        const QString dir = outputDirEdit->text().trimmed();
        if (!dir.isEmpty()) {
            opts.outputDirectory = QDir(dir).absolutePath();
        }
    }
    return opts;
}
