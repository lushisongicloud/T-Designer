#ifndef DIALOGTAG_H
#define DIALOGTAG_H

#include <QWidget>

namespace Ui {
class dialogTag;
}
enum TagColor{red,orange,yellow,green,blue,darkblue,purple};
enum TagShape{rectange,circle};
class dialogTag : public QWidget
{
    Q_OBJECT

public:
    explicit dialogTag(QWidget *parent = nullptr);
    ~dialogTag();
    enum TagColor CurTagColor=TagColor::red;
    enum TagShape CurShape=TagShape::rectange;

private slots:
    void on_BtnRed_clicked();

    void on_BtnOriange_clicked();

    void on_BtnYellow_clicked();

    void on_BtnGreen_clicked();

    void on_BtnBlue_clicked();

    void on_BtnDarkBlue_clicked();

    void on_BtnPurple_clicked();

    void on_BtnRec_clicked();

    void on_BtnCircle_clicked();

    void on_BtnPolygon_clicked();

private:
    Ui::dialogTag *ui;
    void ResetBtn();
signals:
    void DrawTag(int Type,QColor mColor);
    void ChangeColor(QColor mColor);
};

#endif // DIALOGTAG_H
