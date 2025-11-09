#include "TextEditDelegate.h"

#include <QSpinBox>
#include <QDoubleSpinBox>
#include <QComboBox>
#include <QStandardItemModel>
#include <QCompleter>
#include <QTreeView>
#include <QHeaderView>
#include <QTextEdit>
#include <QPainter>


TextEditDelegate::TextEditDelegate( QObject *parent)
{
}

void TextEditDelegate::paint(QPainter *painter, const QStyleOptionViewItem &option, const QModelIndex &index) const
{
    QString value = index.model()->data(index, Qt::EditRole).toString();
        QPen pen;
        if (option.state & QStyle::State_Selected ) {
            if( option.state & QStyle::State_HasFocus )
            {
                painter->fillRect(option.rect, option.palette.highlight());
                pen.setColor( Qt::white );

            }
            else
            {
                painter->fillRect(option.rect, option.palette.base() );
                pen.setColor( Qt::black );
            }
        }
        else
        {
            painter->fillRect(option.rect, option.palette.base() );
            pen.setColor( Qt::black );
        }

        painter->setPen( pen );
        painter->drawText(option.rect,Qt::TextWrapAnywhere,value);
}

QWidget *TextEditDelegate::createEditor(QWidget *parent, const QStyleOptionViewItem &option,
                                        const QModelIndex &index) const
{
    QTextEdit *editor = new QTextEdit(parent);
    return editor;
}

void TextEditDelegate::setEditorData(QWidget *editor, const QModelIndex &index) const
{
    QString value = index.model()->data(index, Qt::EditRole).toString();

    QTextEdit *ComboBox = static_cast<QTextEdit*>(editor);

    ComboBox->setPlainText( value );


}

void TextEditDelegate::setModelData(QWidget *editor, QAbstractItemModel *model, const QModelIndex &index) const
{
    QTextEdit *ComboBox = static_cast<QTextEdit*>(editor);

    //spinBox->interpretText();
    QString value = ComboBox->toPlainText();

    model->setData(index, value, Qt::EditRole);
}

void TextEditDelegate::updateEditorGeometry(QWidget *editor, const QStyleOptionViewItem &option, const QModelIndex &index) const
{
    editor->setGeometry(option.rect);
}
