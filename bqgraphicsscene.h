#ifndef BQGRAPHICSSCENE_H
#define BQGRAPHICSSCENE_H

#include <QGraphicsScene>
#include "bpointitem.h"
#include "bqgraphicsitem.h"

class BQGraphicsScene : public QGraphicsScene
{
    Q_OBJECT

public:
    BQGraphicsScene(QObject *parent = nullptr);

    void startCreate();
    void saveItemToConfig();
    void loadItemToScene();
    qreal SetBackGroundImage(QPixmap pix, int width, int height);
    bool SetBackGroundImage(QPixmap pix);
    double m_scaleFactor=1.0; // 用于保存缩放比例的成员变量
    QSize m_originalImageSize; // 用于保存原始图片尺寸的成员变量
    QPointF m_offset=QPointF(0.0, 0.0); // 用于保存图片居中时的偏移量
protected:
    virtual void mousePressEvent(QGraphicsSceneMouseEvent *event);

signals:
    void updatePoint(QPointF p, QList<QPointF> list, bool isCenter);
    void createFinished();

protected:
    QList<QPointF> m_list;
    bool is_creating_BPolygon;
};

#endif // BQGRAPHICSSCENE_H
