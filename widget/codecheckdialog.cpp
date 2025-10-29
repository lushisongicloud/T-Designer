#include "codecheckdialog.h"

CodeCheckDialog::CodeCheckDialog(QWidget *parent) : QDialog(parent), m_detailsShown(true)
{
    setWindowTitle("模型校验");
    resize(500, 400);
    QVBoxLayout *mainLayout = new QVBoxLayout(this);
    m_summaryLabel = new QLabel(this);
    mainLayout->addWidget(m_summaryLabel);

    QHBoxLayout *buttonLayout = new QHBoxLayout();
    m_okButton = new QPushButton("确定", this);
    connect(m_okButton, &QPushButton::clicked, this, &QDialog::accept);
    buttonLayout->addWidget(m_okButton);

    m_detailsButton = new QPushButton("隐藏详情", this);
    connect(m_detailsButton, &QPushButton::clicked, this, &CodeCheckDialog::toggleDetails);
    buttonLayout->addWidget(m_detailsButton);
    mainLayout->addLayout(buttonLayout);

    m_scrollArea = new QScrollArea(this);
    m_textBrowser = new QTextBrowser();
    m_textBrowser->setOpenLinks(false);
    m_textBrowser->setWordWrapMode(QTextOption::NoWrap);
    m_textBrowser->setReadOnly(true);
    m_scrollArea->setWidget(m_textBrowser);
    m_scrollArea->setWidgetResizable(true);
    m_scrollArea->setVisible(m_detailsShown);
    mainLayout->addWidget(m_scrollArea);
}

void CodeCheckDialog::setCheckResult(const QVector<CodeError> &errors)
{
    QString htmlContent;
    foreach(const CodeError &error, errors) {
        htmlContent += QString("<p>Line %1: <span style='color:red'>%2</span></p><p>错误原因: %3</p>")
            .arg(error.lineNumber).arg(error.codeSegment).arg(error.reason);
    }
    m_summaryLabel->setText(QString("共发现 %1 处错误").arg(errors.count()));
    m_textBrowser->setHtml(htmlContent);
}

void CodeCheckDialog::toggleDetails()
{
    m_detailsShown = !m_detailsShown;
    m_scrollArea->setVisible(m_detailsShown);
    m_detailsButton->setText(m_detailsShown ? "隐藏详情" : "查看详情");
}


//======================CodeChecker===========================
CodeChecker::CodeChecker(const QString& code) : code_(code) {
    // 初始化关键字
    keywords_ << "DEF" << "PORT_DEF_BEGIN" << "PORT_DEF_END" << "ELECTRIC_PORT" << "HYDROLIC_PORT" << "MACHINE_PORT";
    // 初始化正则表达式
    //portDefRegex_ = QRegExp("^DEF (ELECTRIC_PORT|HYDROLIC_PORT|MACHINE_PORT) \"\\d+\" \"\\d\" AS \"\\w+\"$");
    //portDefRegex_ = QRegExp("^DEF (ELECTRIC_PORT|HYDROLIC_PORT|MACHINE_PORT) \".+\" \".+\" AS \"\\w+\"$");
    portDefRegex_ = QRegExp("^\\s*DEF\\s+(ELECTRIC_PORT|HYDROLIC_PORT|MACHINE_PORT)\\s+\".+\"\\s+\".+\"\\s+AS\\s+\"\\w+\"\\s*$");
    variateDefRegex_ = QRegExp("^DEF (VARIATE|PROPERTY) .+;?$");
    functionDefRegex_ = QRegExp("^DEF FUNCTION \\w+\\(.*\\)\\s*\\{");
}

QVector<CodeError> CodeChecker::check() {
    QVector<CodeError> errors;
    QStringList lines = code_.split('\n');
    QSet<QString> portIds;
    QSet<QString> definedVariables;
    QStack<int> braceStack; // Stack to keep track of open braces '{'
    int lineNumber = 0;

    // Brackets and parenthesis checking
    checkBrackets(code_, errors);
    for (const QString& line : lines) {
        lineNumber++;
        QString trimmedLine = line.trimmed();
        if (trimmedLine.startsWith("DEF")) {
            // Collect variable definitions
            if (trimmedLine.startsWith("DEF VARIATE") || trimmedLine.startsWith("DEF PROPERTY")) {
                collectVariables(trimmedLine, definedVariables);
            }

            // Check port definition
            if (trimmedLine.contains("PORT") && !portDefRegex_.exactMatch(trimmedLine)) {
                errors.append({lineNumber, trimmedLine, "无效的端口定义"});
            }
            // Check if port ID is repeated
            QRegExp portIdRegex("\"(\\d+)\" \"\\d{14}\"");
            if (portIdRegex.indexIn(trimmedLine) != -1) {
                QString portId = portIdRegex.cap(1);
                if (portIds.contains(portId)) {
                    errors.append({lineNumber, trimmedLine, "端口定义重复"});
                }
                portIds.insert(portId);
            }

            // Check variate and property definitions
            if ((trimmedLine.startsWith("DEF VARIATE") || trimmedLine.startsWith("DEF PROPERTY")) && !variateDefRegex_.exactMatch(trimmedLine)) {
                errors.append({lineNumber, trimmedLine, "变量定义语法错误"});
            }
        }
    }

    return errors;
}

//void CodeChecker::checkBrackets(const QString &code, int lineNumber2,QVector<CodeError> &errors,QStack<int> &braceStack) {
//    QStack<char> stack;
//    QStack<int> lineStack; // To track line numbers for each opening brace
//    int lineNumber = 1;
//    QStringList lines = code.split('\n');

//    for (const QString &line : lines) {
//        for (int i = 0; i < line.length(); i++) {
//            char c = line[i].toLatin1();
//            switch (c) {
//                case '(': case '[': case '{':
//                    stack.push(c);
//                    lineStack.push(lineNumber); // Push current line number
//                    break;
//                case ')':
//                    if (!stack.isEmpty() && stack.top() == '(') {
//                        stack.pop();
//                        lineStack.pop(); // Correctly matched, so pop the line number
//                    } else {
//                        errors.append({lineNumber, line, "圆括号未配对"});
//                    }
//                    break;
//                case ']':
//                    if (!stack.isEmpty() && stack.top() == '[') {
//                        stack.pop();
//                        lineStack.pop(); // Correctly matched, so pop the line number
//                    } else {
//                        errors.append({lineNumber, line, "方括号未配对"});
//                    }
//                    break;
//                case '}':
//                    if (!stack.isEmpty() && stack.top() == '{') {
//                        stack.pop();
//                        lineStack.pop(); // Correctly matched, so pop the line number
//                    } else {
//                        errors.append({lineNumber, line, "大括号未配对"});
//                    }
//                    break;
//            }
//        }
//        lineNumber++; // Increment the line number after processing each line
//    }

//    // Handle any unmatched opening braces remaining in the stack
//    while (!stack.isEmpty()) {
//        char c = stack.pop();
//        int lineNum = lineStack.pop(); // Get the line number where the unmatched brace was found
//        QString errorMessage;
//        if (c == '(') {
//            errorMessage = "圆括号未正确关闭";
//        } else if (c == '[') {
//            errorMessage = "方括号未正确关闭";
//        } else if (c == '{') {
//            errorMessage = "大括号未正确关闭";
//        }
//        errors.append({lineNum, lines[lineNum - 1], errorMessage}); // Use the actual line content
//    }
//}
void CodeChecker::checkBrackets(const QString &code, QVector<CodeError> &errors) {
    QStack<char> stack;
    QStack<int> lineStack; // To track line numbers for each opening brace
    int lineNumber = 1;
    QStringList lines = code.split('\n');

    for (const QString &line : lines) {
        for (int i = 0; i < line.length(); i++) {
            char c = line[i].toLatin1();
            switch (c) {
                case '(': case '[': case '{':
                    stack.push(c);
                    lineStack.push(lineNumber); // Push current line number
                    break;
                case ')':
                    if (stack.isEmpty() || stack.pop() != '(')
                        errors.append({lineNumber, line, "圆括号未配对"});
                    else
                        lineStack.pop(); // Correctly matched, so pop the line number
                    break;
                case ']':
                    if (stack.isEmpty() || stack.pop() != '[')
                        errors.append({lineNumber, line, "方括号未配对"});
                    else
                        lineStack.pop(); // Correctly matched, so pop the line number
                    break;
                case '}':
                    if (stack.isEmpty() || stack.pop() != '{')
                        errors.append({lineNumber, line, "大括号未配对"});
                    else
                        lineStack.pop(); // Correctly matched, so pop the line number
                    break;
            }
        }
        lineNumber++; // Increment the line number after processing each line
    }

    // Handle any unmatched opening braces remaining in the stack
    while (!stack.isEmpty()) {
        char c = stack.pop();
        int lineNum = lineStack.pop(); // Get the line number where the unmatched brace was found
        QString errorMessage;
        if (c == '(') {
            errorMessage = "圆括号未正确关闭";
        } else if (c == '[') {
            errorMessage = "方括号未正确关闭";
        } else if (c == '{') {
            errorMessage = "大括号未正确关闭";
        }
        errors.append({lineNum, lines[lineNum - 1], errorMessage}); // Use the actual line content
    }
}



void CodeChecker::collectVariables(const QString &line, QSet<QString> &definedVariables) {
    QRegExp varRegex("\\b\\w+=\\w+\\b");
    int pos = 0;
    while ((pos = varRegex.indexIn(line, pos)) != -1) {
        QString var = varRegex.cap(0).split('=').first();
        definedVariables.insert(var);
        pos += varRegex.matchedLength();
    }
}

