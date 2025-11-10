#ifndef DIALOGTERMBATCHMARK_H
#define DIALOGTERMBATCHMARK_H

#include <QDialog>

namespace Ui {
class DialogTermBatchMark;
}

class DialogTermBatchMark : public QDialog
{
    Q_OBJECT

public:
    explicit DialogTermBatchMark(QWidget *parent = nullptr);
    ~DialogTermBatchMark();

private:
    Ui::DialogTermBatchMark *ui;
};

#endif // DIALOGTERMBATCHMARK_H
