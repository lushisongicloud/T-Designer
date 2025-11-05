#include "tmodelcompiledisplaydialog.h"
#include <QScrollArea>

TModelCompileDisplayDialog::TModelCompileDisplayDialog(QWidget *parent)
    : QDialog(parent)
{
    setupUi();
    setWindowTitle("T语言模型编译结果");
    resize(800, 600);
}

TModelCompileDisplayDialog::~TModelCompileDisplayDialog()
{
}

void TModelCompileDisplayDialog::setupUi()
{
    QVBoxLayout *mainLayout = new QVBoxLayout(this);
    
    // 创建主标签页
    m_mainTabWidget = new QTabWidget(this);
    
    // 1. 端口变量定义
    m_portVarsEdit = new QTextEdit(this);
    m_portVarsEdit->setReadOnly(true);
    m_portVarsEdit->setFont(QFont("Courier", 10));
    m_mainTabWidget->addTab(m_portVarsEdit, "端口变量定义");
    
    // 2. 内部变量定义
    m_internalVarsEdit = new QTextEdit(this);
    m_internalVarsEdit->setReadOnly(true);
    m_internalVarsEdit->setFont(QFont("Courier", 10));
    m_mainTabWidget->addTab(m_internalVarsEdit, "内部变量定义");
    
    // 3. 正常模式
    m_normalModeEdit = new QTextEdit(this);
    m_normalModeEdit->setReadOnly(true);
    m_normalModeEdit->setFont(QFont("Courier", 10));
    m_mainTabWidget->addTab(m_normalModeEdit, "正常模式");
    
    // 4. 故障模式（使用嵌套标签页）
    m_failureModesTabWidget = new QTabWidget(this);
    m_mainTabWidget->addTab(m_failureModesTabWidget, "故障模式");
    
    mainLayout->addWidget(m_mainTabWidget);
    
    // 关闭按钮
    QHBoxLayout *buttonLayout = new QHBoxLayout();
    buttonLayout->addStretch();
    m_closeButton = new QPushButton("关闭", this);
    m_closeButton->setMinimumWidth(100);
    connect(m_closeButton, &QPushButton::clicked, this, &QDialog::accept);
    buttonLayout->addWidget(m_closeButton);
    buttonLayout->addStretch();
    
    mainLayout->addLayout(buttonLayout);
}

void TModelCompileDisplayDialog::setCompileResult(const QString &portVars,
                                                 const QString &internalVars,
                                                 const QString &normalMode,
                                                 const QList<TModelParser::FailureMode> &failureModes)
{
    // 设置各部分内容
    m_portVarsEdit->setPlainText(portVars);
    m_internalVarsEdit->setPlainText(internalVars);
    m_normalModeEdit->setPlainText(normalMode);
    
    // 清空并重建故障模式标签页
    while (m_failureModesTabWidget->count() > 0) {
        QWidget *w = m_failureModesTabWidget->widget(0);
        m_failureModesTabWidget->removeTab(0);
        delete w;
    }
    
    // 添加每个故障模式
    if (failureModes.isEmpty()) {
        QTextEdit *emptyEdit = new QTextEdit(this);
        emptyEdit->setReadOnly(true);
        emptyEdit->setPlainText("（无故障模式）");
        m_failureModesTabWidget->addTab(emptyEdit, "无");
    } else {
        for (const TModelParser::FailureMode &fm : failureModes) {
            QTextEdit *fmEdit = new QTextEdit(this);
            fmEdit->setReadOnly(true);
            fmEdit->setFont(QFont("Courier", 10));
            fmEdit->setPlainText(fm.description);
            
            QString tabTitle = fm.name;
            if (tabTitle.isEmpty()) {
                tabTitle = "未命名";
            }
            // 限制标签页标题长度
            if (tabTitle.length() > 15) {
                tabTitle = tabTitle.left(12) + "...";
            }
            
            m_failureModesTabWidget->addTab(fmEdit, tabTitle);
        }
    }
}
