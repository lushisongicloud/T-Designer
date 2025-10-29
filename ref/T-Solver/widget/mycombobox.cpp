#include "mycombobox.h"
#include <QDebug>

MatchOnlyProxyModel::MatchOnlyProxyModel(QObject *parent) : QSortFilterProxyModel(parent)
{}

bool MatchOnlyProxyModel::filterAcceptsRow(int sourceRow, const QModelIndex &sourceParent) const
{
    QModelIndex index = sourceModel()->index(sourceRow, 0, sourceParent);
    return sourceModel()->data(index).toString().startsWith(filterRegExp().pattern(), Qt::CaseInsensitive);
}

MyComboBox::MyComboBox(QWidget *parent) :
    QComboBox(parent),
    m_model(new QStringListModel(this)),
    m_proxyModel(new MatchOnlyProxyModel(this)),
    tableItem(nullptr)
{
    setEditable(true);
    setModel(m_model);
    setInsertPolicy(QComboBox::NoInsert); // 禁止自动插入用户输入到下拉列表
    m_completer = new QCompleter(this);
    m_completer->setCompletionMode(QCompleter::PopupCompletion);
    m_completer->setCaseSensitivity(Qt::CaseInsensitive);

    m_proxyModel->setSourceModel(m_model);
    m_completer->setModel(m_proxyModel);


    lineEdit()->setCompleter(m_completer);

    connect(m_completer, static_cast<void(QCompleter::*)(const QString&)>(&QCompleter::highlighted),
            this, &MyComboBox::onCompleterActivated);
    connect(this, SIGNAL(activated(int)), this, SLOT(onActivated(int)));

}

void MyComboBox::setList(const QStringList &list)
{
    m_model->setStringList(list);
}

void MyComboBox::setTableItem(QTableWidgetItem* item) {
    tableItem = item;
}

void MyComboBox::setMyCurrentText(const QString &text)
{
    this->setCurrentText(text);
    m_previousIndex = this->currentIndex();
    str_previoustext = text;
}

void MyComboBox::keyPressEvent(QKeyEvent *e)
{
    QComboBox::keyPressEvent(e);
    if (e->key() == Qt::Key_Return || e->key() == Qt::Key_Enter)
    {
        if(m_chosenCompletion=="")
        {
            setCurrentIndex(findText(m_completer->currentCompletion()));
        }
        else
        {
            setCurrentIndex(findText(m_chosenCompletion));
            m_completer->setCompletionPrefix(m_chosenCompletion);
            m_chosenCompletion.clear();
        }
        if (this->currentIndex() != m_previousIndex)  // Compare the current index with the previous one
        {
            emit editFinish(tableItem);
        }
    }
    else
    {
        m_completer->complete(); // 手动触发下拉列表
    }
}

void MyComboBox::focusInEvent(QFocusEvent *e)
{
    //qDebug()<<"focusInEvent,str_previoustext:"<<str_previoustext<<"m_previousIndex:"<<m_previousIndex;
    if(this->currentText() != str_previoustext ||  this->currentIndex() != m_previousIndex )
    {
        //qDebug()<<"this->currentText():"<<this->currentText()<<"this->currentIndex():"<<this->currentIndex();
        if(this->currentText() != str_previoustext)emit editFinish(tableItem);
        m_previousIndex = this->currentIndex();
        str_previoustext = this->currentText();

    }

    if (e->reason() != Qt::MouseFocusReason)
    {
        m_completer->complete(); // 手动触发下拉列表
    }


    QComboBox::focusInEvent(e);
}

// 重写 focusOutEvent 方法
void MyComboBox::focusOutEvent(QFocusEvent *event)
{
//    qDebug()<<"str_previoustext"<<str_previoustext;
//    qDebug()<<"this->currentText()"<<this->currentText();
    if(this->currentText() != str_previoustext )
    {
        emit editFinish(tableItem);
    }
    QComboBox::focusOutEvent(event);
}

void MyComboBox::onCompleterActivated(const QString &text)
{
    m_chosenCompletion = text;
}

void MyComboBox::onActivated(int index)
{
    if (index != m_previousIndex)  // Compare the current index with the previous one
    {
        //emit editFinish(m_item);
        m_previousIndex =index; // Update the previous index
    }
    // 设置光标到行编辑的开始位置
    //lineEdit()->home(false);
}
