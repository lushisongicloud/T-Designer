#ifndef DIALOGNEWPROJECT_H
#define DIALOGNEWPROJECT_H

#include <QDialog>
#include "common.h"
namespace Ui {
class DialogNewProject;
}

class DialogNewProject : public QDialog
{
    Q_OBJECT

public:
    explicit DialogNewProject(QWidget *parent = nullptr);
    ~DialogNewProject();
    bool Canceled;
    QString ProjectPath,ProjectName;
private slots:
    void on_BtnBrowse_clicked();

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

private:
    Ui::DialogNewProject *ui;
};

#endif // DIALOGNEWPROJECT_H
