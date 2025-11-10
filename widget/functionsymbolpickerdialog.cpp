#include "widget/functionsymbolpickerdialog.h"

#include <QDialogButtonBox>
#include <QSqlQuery>
#include <QSqlError>
#include <QVBoxLayout>
#include <QHeaderView>
#include <QDebug>
#include <QPushButton>

FunctionSymbolPickerDialog::FunctionSymbolPickerDialog(const QSqlDatabase &db, QWidget *parent)
    : QDialog(parent)
    , m_db(db)
    , m_tree(new QTreeWidget(this))
{
    setWindowTitle(tr("选择功能子块"));
    resize(420, 500);

    m_tree->setColumnCount(2);
    QStringList headers;
    headers << tr("名称") << tr("类型");
    m_tree->setHeaderLabels(headers);
    m_tree->setSelectionMode(QAbstractItemView::SingleSelection);
    m_tree->setSelectionBehavior(QAbstractItemView::SelectRows);
    m_tree->header()->setSectionResizeMode(0, QHeaderView::Stretch);
    m_tree->header()->setSectionResizeMode(1, QHeaderView::ResizeToContents);

    connect(m_tree, &QTreeWidget::itemActivated,
            this, &FunctionSymbolPickerDialog::onItemActivated);
    connect(m_tree, &QTreeWidget::itemSelectionChanged,
            this, &FunctionSymbolPickerDialog::onSelectionChanged);

    auto *buttonBox = new QDialogButtonBox(QDialogButtonBox::Ok | QDialogButtonBox::Cancel, this);
    m_okButton = buttonBox->button(QDialogButtonBox::Ok);
    m_okButton->setEnabled(false);
    connect(buttonBox, &QDialogButtonBox::accepted, this, &FunctionSymbolPickerDialog::acceptSelection);
    connect(buttonBox, &QDialogButtonBox::rejected, this, &FunctionSymbolPickerDialog::reject);

    auto *layout = new QVBoxLayout(this);
    layout->addWidget(m_tree);
    layout->addWidget(buttonBox);

    loadData();
}

void FunctionSymbolPickerDialog::loadData()
{
    m_tree->clear();
    if (!m_db.isOpen())
        return;

    QSqlQuery equipmentQuery(m_db);
    if (!equipmentQuery.exec(QString("SELECT Equipment_ID, DT FROM Equipment ORDER BY DT"))) {
        qWarning() << "FunctionSymbolPickerDialog equipment" << equipmentQuery.lastError();
        return;
    }

    while (equipmentQuery.next()) {
        QTreeWidgetItem *equipItem = new QTreeWidgetItem(m_tree);
        const int equipmentId = equipmentQuery.value(0).toInt();
        equipItem->setText(0, equipmentQuery.value(1).toString());
        equipItem->setText(1, tr("元件"));
        equipItem->setData(0, Qt::UserRole, equipmentId);
        equipItem->setExpanded(true);

        QSqlQuery symbolQuery(m_db);
        symbolQuery.prepare(QString("SELECT Symbol_ID, Show_DT, Symbol_Category FROM Symbol WHERE Equipment_ID=:eid ORDER BY Symbol_ID"));
        symbolQuery.bindValue(":eid", equipmentId);
        if (!symbolQuery.exec()) {
            qWarning() << "FunctionSymbolPickerDialog symbol" << symbolQuery.lastError();
            continue;
        }

        while (symbolQuery.next()) {
            QTreeWidgetItem *symbolItem = new QTreeWidgetItem(equipItem);
            symbolItem->setText(0, symbolQuery.value(1).toString());
            symbolItem->setText(1, symbolQuery.value(2).toString());
            symbolItem->setData(0, Qt::UserRole, symbolQuery.value(0).toInt());
        }
    }
    m_tree->expandToDepth(0);
}

void FunctionSymbolPickerDialog::onItemActivated(QTreeWidgetItem *item, int column)
{
    Q_UNUSED(column);
    if (!item) return;
    if (item->parent() == nullptr)
        return;
    m_selectedSymbolId = item->data(0, Qt::UserRole).toInt();
    m_selectedSymbolName = item->text(0);
    accept();
}

void FunctionSymbolPickerDialog::onSelectionChanged()
{
    QTreeWidgetItem *item = m_tree->currentItem();
    if (!item || item->parent() == nullptr) {
        m_selectedSymbolId = 0;
        m_selectedSymbolName.clear();
        m_okButton->setEnabled(false);
        return;
    }
    m_selectedSymbolId = item->data(0, Qt::UserRole).toInt();
    m_selectedSymbolName = item->text(0);
    m_okButton->setEnabled(m_selectedSymbolId != 0);
}

void FunctionSymbolPickerDialog::acceptSelection()
{
    if (m_selectedSymbolId == 0)
        return;
    accept();
}
