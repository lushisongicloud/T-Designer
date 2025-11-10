#ifndef FORMCREATNEWCOMPONENT_H
#define FORMCREATNEWCOMPONENT_H

#include <QWidget>

namespace Ui {
class FormCreatNewComponent;
}

class FormCreatNewComponent : public QWidget
{
    Q_OBJECT

public:
    explicit FormCreatNewComponent(QWidget *parent = nullptr);
    ~FormCreatNewComponent();

private:
    Ui::FormCreatNewComponent *ui;
};

#endif // FORMCREATNEWCOMPONENT_H
