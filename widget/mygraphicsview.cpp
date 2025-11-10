#include "mygraphicsview.h"
#include <QDebug>
#include <QTimer>

MyGraphicsView::MyGraphicsView(QWidget *parent)
    : QGraphicsView(parent), scale_m(1.0) // 初始化scale_m为1
{
    setDragMode(QGraphicsView::ScrollHandDrag);
    setStyleSheet("padding: 0px; border: 0px;");
    setMouseTracking(true);
    setHorizontalScrollBarPolicy(Qt::ScrollBarAlwaysOff);
    setVerticalScrollBarPolicy(Qt::ScrollBarAlwaysOff);
    setTransformationAnchor(QGraphicsView::AnchorUnderMouse);
    setResizeAnchor(QGraphicsView::AnchorUnderMouse);
}
void MyGraphicsView::updateScale(qreal scaleFactor)
{
    if (!scene()) return; // 如果没有设置场景，直接返回
    // 更新缩放比例
    scale(scaleFactor, scaleFactor); // 应用缩放
    // 计算新的缩放比例
    scale_m = this->transform().m11(); // Qt5之后使用transform().m11()代替matrix().m11()
    if(scale_m<0.000001)scale_m=0.000001;
    int lineWidth = static_cast<int>(ceil(2.0 / scale_m)); // 计算新的线宽，保证最终显示为2个像素宽
    if(lineWidth<1)lineWidth=1;
    if(lineWidth!=curLineWidth){
        curLineWidth = lineWidth;
        foreach(QGraphicsItem *item, scene()->items()) {
            BGraphicsItem *bItem = dynamic_cast<BGraphicsItem*>(item);
            if(bItem) bItem->updateLineWidth(lineWidth);
        }
    }
    update(); // 更新视图
}
void MyGraphicsView::ScaleToWidget()
{
    if (!scene()) return; // 如果没有设置场景，直接返回
    // 获取场景的边界矩形
    QRectF sceneRect = scene()->sceneRect();
    // 获取视图的大小
    QSizeF viewSize = viewport()->size();
    qDebug()<<"viewSize:"<<viewSize;

    // 计算水平和垂直方向上的缩放比例
    qreal scaleX = viewSize.width() / sceneRect.width();
    qreal scaleY = viewSize.height() / sceneRect.height();

    resetTransform();
    // 取较小的缩放比例，以保证整个场景都能显示在视图
    updateScale(qMin(scaleX, scaleY));
}
void MyGraphicsView::wheelEvent(QWheelEvent *event) {
    if (event->buttons() & Qt::RightButton) { // 检查是否按下了鼠标右键
        int wheelDeltaValue = event->angleDelta().y();
        // 设置缩放的极限条件
        if ((wheelDeltaValue > 0) && (scale_m >= 50))return;
        else if ((wheelDeltaValue < 0) && (scale_m <= 0.01))return;
        qreal factor = (wheelDeltaValue > 0) ? 1.2 : 0.833; // 根据滚轮的方向决定是放大还是缩小
        updateScale(factor); // 更新缩放比例
    } else {
        QGraphicsView::wheelEvent(event); // 如果没有按下鼠标右键，调用基类的wheelEvent处理其他滚轮事件
    }
}

void MyGraphicsView::mousePressEvent(QMouseEvent *event) {
    if (event->button() == Qt::RightButton) {
        QGraphicsItem* itemUnderCursor = itemAt(event->pos());
        if (itemUnderCursor) {
            // 尝试将项转换为QGraphicsPixmapItem
            QGraphicsPixmapItem* pixmapItem = dynamic_cast<QGraphicsPixmapItem*>(itemUnderCursor);
            if (pixmapItem) {
                // 如果点击位置是QGraphicsPixmapItem（背景图片），则模拟左键按下以激活滚动手拖动效果
                QMouseEvent simulatedEvent(QEvent::MouseButtonPress, event->pos(), Qt::LeftButton, Qt::LeftButton, event->modifiers());
                setDragMode(QGraphicsView::ScrollHandDrag);
                QGraphicsView::mousePressEvent(&simulatedEvent); // 使用模拟事件
            } else {
                // 如果点击位置不是QGraphicsPixmapItem，则正常处理右键点击事件
                QGraphicsView::mousePressEvent(event);
            }
        } else {
            // 如果没有图形项，也正常处理事件（可能点击的是空白区域）
            QGraphicsView::mousePressEvent(event);
        }
    } else {
        // 对于非右键点击，正常处理事件
        QGraphicsView::mousePressEvent(event);
    }
}

void MyGraphicsView::mouseMoveEvent(QMouseEvent *event) {
    // 仅当非BGraphicsItem上按下右键时才模拟鼠标移动事件
    if (event->buttons() & Qt::RightButton && dragMode() == QGraphicsView::ScrollHandDrag) {
        QMouseEvent simulatedEvent(QEvent::MouseMove, event->pos(), Qt::LeftButton, Qt::LeftButton, event->modifiers());
        QGraphicsView::mouseMoveEvent(&simulatedEvent); // 使用模拟事件
    } else {
        QGraphicsView::mouseMoveEvent(event);
    }
}

void MyGraphicsView::mouseReleaseEvent(QMouseEvent *event) {
    if (event->button() == Qt::RightButton && dragMode() == QGraphicsView::ScrollHandDrag) {
        // 模拟左键释放以停用滚动手拖动效果
        QMouseEvent simulatedEvent(QEvent::MouseButtonRelease, event->pos(), Qt::LeftButton, Qt::NoButton, event->modifiers());
        QGraphicsView::mouseReleaseEvent(&simulatedEvent); // 使用模拟事件
        setDragMode(QGraphicsView::NoDrag);
    } else {
        QGraphicsView::mouseReleaseEvent(event);
    }
}

bool MyGraphicsView::eventFilter(QObject *watched, QEvent *event) {
    if (event->type() == QEvent::Resize) {
        ScaleToWidget();  // 当全屏对话框尺寸变化时，调整 MyGraphicsView 的缩放比例
    }
    return QGraphicsView::eventFilter(watched, event);  // 传递事件到基类的事件过滤器
}

void MyGraphicsView::mouseDoubleClickEvent(QMouseEvent *event) {
    if (event->button() == Qt::LeftButton) {
        if (!fullscreenDialog) { // 如果对话框未打开，则打开
            fullscreenDialog = new QDialog();  // 创建全屏对话框
            fullscreenDialog->setModal(true);
            fullscreenDialog->setWindowFlags(Qt::Window | Qt::WindowTitleHint | Qt::WindowSystemMenuHint | Qt::WindowMaximizeButtonHint | Qt::WindowCloseButtonHint);
            fullscreenDialog->showMaximized();  // 最大化显示对话框

            // 将 MyGraphicsView 从原父窗口中移除并添加到全屏对话框中
            QWidget* parentWidget = this->parentWidget();
            this->setParent(fullscreenDialog);
            QVBoxLayout *layout = new QVBoxLayout(fullscreenDialog);
            layout->addWidget(this);
            fullscreenDialog->setLayout(layout);
            fullscreenDialog->installEventFilter(this);  // 安装事件过滤器
            connect(fullscreenDialog, &QDialog::finished, [this, parentWidget]() {
                fullscreenDialog->removeEventFilter(this);  // 移除事件过滤器
                this->setParent(parentWidget); // 将 MyGraphicsView 移回原父窗口
                if (parentWidget->layout()) parentWidget->layout()->addWidget(this); // 将 MyGraphicsView 重新添加到原布局中
                this->show();  // 确保控件可见
                ScaleToWidget();  // 重新调整缩放比例以适应原窗口大小
                fullscreenDialog->deleteLater();
                fullscreenDialog = nullptr; // 重置全屏对话框指针
            });
            fullscreenDialog->exec();  // 显示全屏对话框
        } else { // 如果对话框已经打开，则关闭
            fullscreenDialog->accept(); // 关闭对话框
        }
    }
}
