#include "aimodelgeneratordialog.h"
#include <QGroupBox>
#include <QSplitter>

AiModelGeneratorDialog::AiModelGeneratorDialog(QWidget *parent)
    : QDialog(parent)
{
    setWindowTitle("AI模型自动生成");
    setMinimumSize(1000, 700);
    
    // 创建主布局
    QVBoxLayout *mainLayout = new QVBoxLayout(this);
    
    // 顶部信息区
    QGroupBox *infoGroup = new QGroupBox("处理信息");
    QVBoxLayout *infoLayout = new QVBoxLayout(infoGroup);
    
    m_componentLabel = new QLabel("准备开始...");
    m_componentLabel->setStyleSheet("font-weight: bold; font-size: 12pt;");
    infoLayout->addWidget(m_componentLabel);
    
    m_statusLabel = new QLabel("状态: 等待");
    infoLayout->addWidget(m_statusLabel);
    
    m_progressBar = new QProgressBar();
    m_progressBar->setRange(0, 100);
    m_progressBar->setValue(0);
    infoLayout->addWidget(m_progressBar);
    
    mainLayout->addWidget(infoGroup);
    
    // 创建分割器用于三个文本编辑区域
    QSplitter *splitter = new QSplitter(Qt::Vertical);
    
    // 输入信息区
    QGroupBox *inputGroup = new QGroupBox("发送给大模型的原始输入");
    QVBoxLayout *inputLayout = new QVBoxLayout(inputGroup);
    m_inputEdit = new QTextEdit();
    m_inputEdit->setReadOnly(true);
    m_inputEdit->setStyleSheet("background-color: #f0f0f0; font-family: Consolas, monospace;");
    inputLayout->addWidget(m_inputEdit);
    splitter->addWidget(inputGroup);
    
    // 思考内容区
    QGroupBox *reasoningGroup = new QGroupBox("大模型思考内容");
    QVBoxLayout *reasoningLayout = new QVBoxLayout(reasoningGroup);
    m_reasoningEdit = new QTextEdit();
    m_reasoningEdit->setReadOnly(true);
    m_reasoningEdit->setStyleSheet("background-color: #fff8e1; font-family: Consolas, monospace;");
    reasoningLayout->addWidget(m_reasoningEdit);
    splitter->addWidget(reasoningGroup);
    
    // 输出内容区
    QGroupBox *outputGroup = new QGroupBox("大模型最终输出");
    QVBoxLayout *outputLayout = new QVBoxLayout(outputGroup);
    m_outputEdit = new QTextEdit();
    m_outputEdit->setReadOnly(true);
    m_outputEdit->setStyleSheet("background-color: #e8f5e9; font-family: Consolas, monospace;");
    outputLayout->addWidget(m_outputEdit);
    splitter->addWidget(outputGroup);
    
    // 设置初始大小比例
    splitter->setStretchFactor(0, 2);
    splitter->setStretchFactor(1, 3);
    splitter->setStretchFactor(2, 2);
    
    mainLayout->addWidget(splitter);
    
    // 底部按钮
    m_closeButton = new QPushButton("关闭");
    m_closeButton->setEnabled(false);  // 初始禁用，处理完成后启用
    connect(m_closeButton, &QPushButton::clicked, this, &QDialog::accept);
    mainLayout->addWidget(m_closeButton);
    
    setLayout(mainLayout);
}

AiModelGeneratorDialog::~AiModelGeneratorDialog()
{
}

void AiModelGeneratorDialog::appendInput(const QString &text)
{
    m_inputEdit->append(text);
    m_inputEdit->moveCursor(QTextCursor::End);
}

void AiModelGeneratorDialog::appendReasoning(const QString &text)
{
    m_reasoningEdit->append(text);
    m_reasoningEdit->moveCursor(QTextCursor::End);
}

void AiModelGeneratorDialog::appendOutput(const QString &text)
{
    m_outputEdit->append(text);
    m_outputEdit->moveCursor(QTextCursor::End);
}

void AiModelGeneratorDialog::setCurrentComponent(const QString &name, int current, int total)
{
    m_componentLabel->setText(QString("正在处理: %1 (%2/%3)").arg(name).arg(current).arg(total));
    if (total > 0) {
        m_progressBar->setValue(current * 100 / total);
    }
}

void AiModelGeneratorDialog::setStatus(const QString &status)
{
    m_statusLabel->setText("状态: " + status);
}

void AiModelGeneratorDialog::clearAll()
{
    m_inputEdit->clear();
    m_reasoningEdit->clear();
    m_outputEdit->clear();
    m_componentLabel->setText("准备开始...");
    m_statusLabel->setText("状态: 等待");
    m_progressBar->setValue(0);
    m_closeButton->setEnabled(false);
}

void AiModelGeneratorDialog::enableCloseButton()
{
    m_closeButton->setEnabled(true);
}
