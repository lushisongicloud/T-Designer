#ifndef DIALOGMULTILINE_H
#define DIALOGMULTILINE_H

#include <QDialog>

namespace Ui {
class DialogMultiLine;
}

class DialogMultiLine : public QDialog
{
    Q_OBJECT

public:
    explicit DialogMultiLine(QWidget *parent = nullptr);
    ~DialogMultiLine();
    bool Canceled;
    int LineCount;
    int LineGap;
    int Mode;

private slots:
    void on_BtnDraw_clicked();

private:
    Ui::DialogMultiLine *ui;
};

#endif // DIALOGMULTILINE_H
