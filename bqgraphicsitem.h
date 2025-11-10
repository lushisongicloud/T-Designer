#ifndef BQGRAPHICSITEM_H
#define BQGRAPHICSITEM_H

#include <QObject>
#include "bpointitem.h"

#define PI 3.1415926

// 自定义图元 - 基础类
class BGraphicsItem : public QObject, public QAbstractGraphicsShapeItem
{
    Q_OBJECT

public:
    enum ItemType {
        Circle = 0,         // 圆 0
        Ellipse,            // 椭圆 1
        Concentric_Circle,  // 同心圆 2
        Pie,                // 饼 3
        Chord,              // 和弦 4
        Rectangle,          // 矩形 5
        Square,             // 正方形 6
        Polygon,            // 多边形 7
        Round_End_Rectangle,// 圆端矩形 8
        Rounded_Rectangle   // 圆角矩形 9
    };

    QPointF getCenter() { return m_center; }
    void setCenter(QPointF p) { m_center = p; }

    QPointF getEdge() { return m_edge; }
    void setEdge(QPointF p) { m_edge = p; }

    ItemType getType() { return m_type; }

protected:
    BGraphicsItem(QPointF center, QPointF edge, ItemType type);

    virtual void mousePressEvent(QGraphicsSceneMouseEvent *event) override;
    virtual void mouseMoveEvent(QGraphicsSceneMouseEvent *event) override;
    virtual void mouseReleaseEvent(QGraphicsSceneMouseEvent *event) override;

    //virtual void focusInEvent(QFocusEvent *event) override;
    //virtual void focusOutEvent(QFocusEvent *event) override;

public:
    QPointF m_center;
    QPointF m_edge;
    ItemType m_type;
    BPointItemList m_pointList;

    //QPen m_pen_isSelected;
    QPen m_pen_noSelected;
public slots:
    void updateColor(QColor color);
    void updateLineWidth(int lineWidth);
};

//------------------------------------------------------------------------------

// 多边形
class BPolygon : public BGraphicsItem
{
    Q_OBJECT

public:
    BPolygon(ItemType type);
    BPolygon(const QList<QPointF> &points, ItemType type, const QPen &pen);
    BPolygon(qreal x, qreal y, qreal width, qreal height, ItemType type, const QPen& pen);// 新增的构造函数，用于直接创建四边形

    QPointF getCentroid(QList<QPointF> list);
    void getMaxLength();
    void updatePolygon(QPointF origin, QPointF end);

public slots:
    void pushPoint(QPointF p, QList<QPointF> list, bool isCenter);

protected:
    virtual QRectF boundingRect() const override;

    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

public:
    qreal m_radius;
    bool is_create_finished;
};

//------------------------------------------------------------------------------
// 矩形 5
class BRectangle : public BGraphicsItem
{
public:
    BRectangle(qreal x, qreal y, qreal width, qreal height, ItemType type, QPen pen);
    BRectangle(qreal x, qreal y, qreal width, qreal height, ItemType type);
protected:
    virtual QRectF boundingRect() const override;

    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

    //virtual void contextMenuEvent(QGraphicsSceneContextMenuEvent *event) override;
};
//------------------------------------------------------------------------------

// 椭圆 1
class BEllipse : public BGraphicsItem
{
    Q_OBJECT

public:
    BEllipse(qreal x, qreal y, qreal width, qreal height, ItemType type, QPen pen);
    BEllipse(qreal x, qreal y, qreal width, qreal height, ItemType type);

protected:
    virtual QRectF boundingRect() const override;

    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

    //virtual void contextMenuEvent(QGraphicsSceneContextMenuEvent *event) override;
};

//------------------------------------------------------------------------------

// 圆
class BCircle : public BEllipse
{
public:
    BCircle(qreal x, qreal y, qreal radius, ItemType type);

    void updateRadius();

protected:
    virtual QRectF boundingRect() const override;

    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

    virtual void contextMenuEvent(QGraphicsSceneContextMenuEvent *event) override;

public:
    qreal m_radius;
};

//------------------------------------------------------------------------------

// 同心圆
class BConcentricCircle : public BCircle
{
public:
    BConcentricCircle(qreal x, qreal y, qreal radius1, qreal radius2, ItemType type);

    void updateOtherRadius();
    void setAnotherEdge(QPointF p);

protected:
    virtual QRectF boundingRect() const override;

    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

    virtual void contextMenuEvent(QGraphicsSceneContextMenuEvent *event) override;

public:
    QPointF m_another_edge;
    qreal m_another_radius;
};

//------------------------------------------------------------------------------

// 饼
class BPie : public BCircle
{
public:
    BPie(qreal x, qreal y, qreal radius, qreal angle, ItemType type);

    void updateAngle();

protected:
    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

public:
    qreal m_angle;
};

//------------------------------------------------------------------------------

// 和弦
class BChord : public BPie
{
public:
    BChord(qreal x, qreal y, qreal radius, qreal angle, ItemType type);

    void updateEndAngle();

protected:
    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

public:
    qreal m_end_angle;
};


//------------------------------------------------------------------------------
// 正方形
class BSquare : public BRectangle
{
public:
    BSquare(qreal x, qreal y, qreal width, ItemType type);

protected:
    virtual void contextMenuEvent(QGraphicsSceneContextMenuEvent *event) override;
};

//------------------------------------------------------------------------------

// 圆端矩形
class BRound_End_Rectangle : public BRectangle
{
public:
    BRound_End_Rectangle(qreal x, qreal y, qreal width, qreal height, ItemType type);

protected:
    virtual QRectF boundingRect() const override;

    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;
};

//------------------------------------------------------------------------------

// 圆角矩形
class BRounded_Rectangle : public BRectangle
{
public:
    BRounded_Rectangle(qreal x, qreal y, qreal width, qreal height, ItemType type);

    void updateRadius();
    void updateAnotherEdge(QPointF p);
    qreal getRadius();
    QPointF getAnotherEdge();
    void setAnotherEdge(QPointF p);

protected:
    virtual void paint(QPainter *painter,
                       const QStyleOptionGraphicsItem *option,
                       QWidget *widget) override;

    virtual void contextMenuEvent(QGraphicsSceneContextMenuEvent *event) override;

public:
    QPointF m_another_edge;
    qreal m_radius;
};

//------------------------------------------------------------------------------

#endif // BQGRAPHICSITEM_H
