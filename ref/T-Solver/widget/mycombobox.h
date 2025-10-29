#ifndef MYCOMBOBOX_H
#define MYCOMBOBOX_H

#include <QObject>
#include <QComboBox>
#include <QLineEdit>
#include <QStringListModel>
#include <QCompleter>
#include <QSortFilterProxyModel>
#include <QKeyEvent>
#include <QFocusEvent>
#include <QTableWidgetItem>

class MatchOnlyProxyModel : public QSortFilterProxyModel
{
public:
    MatchOnlyProxyModel(QObject *parent = nullptr);

protected:
    bool filterAcceptsRow(int sourceRow, const QModelIndex &sourceParent) const override;
};

class MyComboBox : public QComboBox
{
    Q_OBJECT

public:
    explicit MyComboBox(QWidget *parent = nullptr);
    void setList(const QStringList &list);
    void setTableItem(QTableWidgetItem* item);
    void setMyCurrentText(const QString &text);
    QTableWidgetItem* tableItem;

signals:
    void editFinish(QTableWidgetItem* item);

protected:
    void keyPressEvent(QKeyEvent *e) override;
    void focusInEvent(QFocusEvent *e) override;
    void focusOutEvent(QFocusEvent *event) override;

private slots:
    void onCompleterActivated(const QString &text);
    void onActivated(int index);
private:
    QString m_chosenCompletion;
    QStringListModel *m_model;
    QCompleter *m_completer;
    MatchOnlyProxyModel *m_proxyModel;
    int m_previousIndex = -1;
    QString  str_previoustext = "";
};

#endif // MYCOMBOBOX_H
