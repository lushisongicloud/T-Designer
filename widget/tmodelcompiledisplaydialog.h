#ifndef TMODELCOMPILEDISPLAYDIALOG_H
#define TMODELCOMPILEDISPLAYDIALOG_H

#include <QDialog>
#include <QTextEdit>
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QLabel>
#include <QPushButton>
#include <QTabWidget>
#include "BO/function/tmodelparser.h"

/**
 * @brief T语言模型编译结果显示对话框
 * 
 * 分4个标签页显示编译后的完整SMT描述：
 * 1. 端口变量定义
 * 2. 内部变量定义
 * 3. 正常模式
 * 4. 故障模式（每个故障模式一个子标签页）
 */
class TModelCompileDisplayDialog : public QDialog
{
    Q_OBJECT

public:
    explicit TModelCompileDisplayDialog(QWidget *parent = nullptr);
    ~TModelCompileDisplayDialog();
    
    /**
     * @brief 设置编译结果并显示
     * @param portVars 端口变量定义
     * @param internalVars 内部变量定义
     * @param normalMode 正常模式
     * @param failureModes 故障模式列表
     */
    void setCompileResult(const QString &portVars,
                         const QString &internalVars,
                         const QString &normalMode,
                         const QList<TModelParser::FailureMode> &failureModes);

private:
    QTabWidget *m_mainTabWidget;
    QTextEdit *m_portVarsEdit;
    QTextEdit *m_internalVarsEdit;
    QTextEdit *m_normalModeEdit;
    QTabWidget *m_failureModesTabWidget;  // 故障模式的子标签页
    QPushButton *m_closeButton;
    
    void setupUi();
};

#endif // TMODELCOMPILEDISPLAYDIALOG_H
