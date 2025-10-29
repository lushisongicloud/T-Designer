#ifndef DIALOGSETTESTPREFERENCE_H
#define DIALOGSETTESTPREFERENCE_H

#include <QDialog>

namespace Ui {
class DialogSetTestPreference;
}

class DialogSetTestPreference : public QDialog
{
    Q_OBJECT

public:
    explicit DialogSetTestPreference(QWidget *parent = nullptr);
    ~DialogSetTestPreference();
    void SetPreference(int Preference);
    int TestPointPreference;
    bool Canceled;

private slots:

    void on_BtnOK_clicked();

    void on_BtnCanceled_clicked();

private:
    Ui::DialogSetTestPreference *ui;
};

#endif // DIALOGSETTESTPREFERENCE_H
