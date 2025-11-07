#ifndef AIMODELGENERATORDIALOG_H
#define AIMODELGENERATORDIALOG_H

#include <QDialog>
#include <QTextEdit>
#include <QVBoxLayout>
#include <QLabel>
#include <QPushButton>
#include <QProgressBar>

namespace Ui {
class AiModelGeneratorDialog;
}

class AiModelGeneratorDialog : public QDialog
{
    Q_OBJECT

public:
    explicit AiModelGeneratorDialog(QWidget *parent = nullptr);
    ~AiModelGeneratorDialog();

    // 添加输入信息
    void appendInput(const QString &text);
    
    // 添加思考内容
    void appendReasoning(const QString &text);
    
    // 添加输出内容
    void appendOutput(const QString &text);
    
    // 设置当前处理的器件信息
    void setCurrentComponent(const QString &name, int current, int total);
    
    // 设置状态信息
    void setStatus(const QString &status);
    
    // 清空所有内容
    void clearAll();
    
    // 启用关闭按钮
    void enableCloseButton();

private:
    Ui::AiModelGeneratorDialog *ui;
    QTextEdit *m_inputEdit;
    QTextEdit *m_reasoningEdit;
    QTextEdit *m_outputEdit;
    QLabel *m_componentLabel;
    QLabel *m_statusLabel;
    QProgressBar *m_progressBar;
    QPushButton *m_closeButton;
};

#endif // AIMODELGENERATORDIALOG_H
