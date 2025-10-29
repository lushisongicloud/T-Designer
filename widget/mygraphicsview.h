#ifndef MYGRAPHICSVIEW_H
#define MYGRAPHICSVIEW_H

#include <QGraphicsView>
#include <QWheelEvent>
#include "bqgraphicsitem.h"
#include <QVBoxLayout>
#include <QDialog>

class MyGraphicsView : public QGraphicsView
{
    Q_OBJECT

public:
    explicit MyGraphicsView(QWidget *parent = nullptr);
    void updateScale(qreal scaleFactor); // 增加的更新显示比例的函数
    void ScaleToWidget(); //更具空间尺寸修改缩放比例
    qreal scale_m; // 用于保存当前的缩放比例
    int curLineWidth=2;
protected:
    bool eventFilter(QObject *watched, QEvent *event) override;

    void wheelEvent(QWheelEvent *event) override;

    void mousePressEvent(QMouseEvent *event) override;
    void mouseReleaseEvent(QMouseEvent *event) override;
    void mouseMoveEvent(QMouseEvent *event) override;
    void mouseDoubleClickEvent(QMouseEvent *event) override;
private:
    bool fullscreenDialogOpened = false;
    QDialog *fullscreenDialog = nullptr; // 持有全屏对话框的指针
};

#endif // MYGRAPHICSVIEW_H
