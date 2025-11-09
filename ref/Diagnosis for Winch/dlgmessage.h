#ifndef DLGMESSAGE_H
#define DLGMESSAGE_H

#include <QGroupBox>

namespace Ui {
class dlgMessage;
}

class dlgMessage : public QGroupBox
{
    Q_OBJECT

public:
    explicit dlgMessage(QWidget *parent = nullptr);
    ~dlgMessage();
    void SetResult(QString Str);

private slots:

    void on_BtnExit_clicked();

private:
    Ui::dlgMessage *ui;
};

#endif // DLGMESSAGE_H
