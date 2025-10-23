#include "common.h"

QString m_dragText;
common::common()
{

}

//搜索图片
QStringList findImagesInDir(const QDir &dir, QStringList &imageNames) {
    QStringList foundPaths;
    if (imageNames.isEmpty() || !dir.exists()) return foundPaths;
    // 获取目录下的所有文件
    QStringList allFiles = dir.entryList(QDir::Files);
    QStringList remainingImageNames = imageNames;
    for (const QString &imageName : imageNames) {
        // 检查文件名是否存在于allFiles中
        if (allFiles.contains(imageName)) {
            foundPaths.append(dir.absoluteFilePath(imageName));
            remainingImageNames.removeAll(imageName);  // 从列表中移除已找到的图片
        }
    }
    imageNames = remainingImageNames;
    if(imageNames.isEmpty()) return foundPaths;
    // 递归搜索子目录
    QStringList subDirs = dir.entryList(QDir::Dirs | QDir::NoDotAndDotDot);
    for (const QString &subDirName : subDirs) {
        QDir subDir(dir.absoluteFilePath(subDirName));
        QStringList subDirFound = findImagesInDir(subDir, imageNames);
        foundPaths.append(subDirFound);
    }
    return foundPaths;
}
//
void processPictureInfo(const QString &picture, const QString &supplier, const QStringList &searchDirs,
                        QMap<QString, QString> &imagePaths, QMap<QString, QString> &tagInfos)
{
    QStringList listPictureInfo = picture.split("||");

    // 提取所有图片文件名及标注信息
    for (const QString &picInfo : listPictureInfo) {
        QStringList picParts = picInfo.split("*");
        QString filePath = picParts.first();
        QFileInfo fileInfo(filePath);
        QString fileName = fileInfo.isAbsolute() ? fileInfo.fileName() : filePath;

        imagePaths[fileName] = QString(); // 初始化路径映射
        tagInfos[fileName] = picParts.count() > 1 ? picParts.last() : QString(); // 初始化标注信息映射
    }

    // 在各目录中搜索图片，并更新映射
    for (const QString &dirPath : searchDirs) {
        QDir dir(dirPath);
        QStringList remainingNames = imagePaths.keys();
        QStringList foundInDir = findImagesInDir(dir, remainingNames);
        for (const QString &foundPath : foundInDir) {
            QFileInfo fileInfo(foundPath);
            imagePaths[fileInfo.fileName()] = foundPath;
        }
        if (remainingNames.isEmpty()) break; // 如果所有图片都找到了，提前退出循环
    }
}

bool isTagInfoValid(const QString &strTagInfo){
    // 判断StrTagInfo是否符合规范：包含三个斜线且每个部分不为空
    QStringList tagParts = strTagInfo.split("/");
    bool isTagInfoValid = tagParts.size() == 4 && !tagParts.contains("");
    if(!strTagInfo.isEmpty() && !isTagInfoValid )qDebug()<<"Strange StrTagInfo:"<<strTagInfo;
    return isTagInfoValid;
}

//从m_Scene画布生成strTagInfo
QString genTagInfoFromScene(const BQGraphicsScene &scene, int tagColor) {
    QString strTagInfo;
    QList<QGraphicsItem *> list = scene.items();
    qDebug() << "list.count():" << list.count();
    if (!list.isEmpty()) {
        for (QGraphicsItem *item : list) {
            if (item->type() == QGraphicsItem::UserType) {
                BGraphicsItem *bItem = static_cast<BGraphicsItem *>(item);
                BGraphicsItem::ItemType type = bItem->getType();

                if (type == BGraphicsItem::ItemType::Ellipse || type == BGraphicsItem::ItemType::Rectangle
                        || type == BGraphicsItem::ItemType::Polygon) {
                    qreal posX = (bItem->x());
                    qreal posY = (bItem->y());
                    double CheckSum = posX + posY;
                    QString posStr = QString::number(posX, 'f', 2) + "," + QString::number(posY, 'f', 2);

                    QString edgeStr;
                    if (type == BGraphicsItem::ItemType::Ellipse) {
                        BEllipse *ellipse = static_cast<BEllipse *>(bItem);
                        qreal edgeX = ellipse->getEdge().x();
                        qreal edgeY = ellipse->getEdge().y();
                        edgeStr = QString::number(edgeX, 'f', 2) + "," + QString::number(edgeY, 'f', 2);
                    } else if (type == BGraphicsItem::ItemType::Rectangle) {
                        BRectangle *rectangle = static_cast<BRectangle *>(bItem);
                        qreal edgeX = rectangle->getEdge().x();
                        qreal edgeY = rectangle->getEdge().y();
                        edgeStr = QString::number(edgeX, 'f', 2) + "," + QString::number(edgeY, 'f', 2);
                    }
                    else if (type == BGraphicsItem::ItemType::Polygon) {
                        BPolygon *polygon = static_cast<BPolygon *>(bItem);
                        BPointItemList list = polygon->m_pointList;

                        // 构造多边形各个顶点的字符串表示
                        QStringList pointsStrList;
                        for ( int j = 0; j < list.size() - 1; j++ )
                        {
                            QPointF pointPos = list.at(j)->pos();  // 获取控制点的位置
                            QString pointStr = QString::number(pointPos.x(), 'f', 2) + "," + QString::number(pointPos.y(), 'f', 2);
                            pointsStrList.append(pointStr);
                        }
                        edgeStr = pointsStrList.join(";");  // 使用分号分隔各个顶点
                    }
                    if(CheckSum > 1.0)strTagInfo = QString::number(static_cast<int>(type)) + "/" + QString::number(tagColor) + "/" + posStr + "/" + edgeStr ;// 过滤掉太小的图形项
                }
            }
        }
    }
    qDebug()<<"strTagInfo:"<<strTagInfo;
    return strTagInfo;
}

void LoadPicTag(QString StrTag, MyGraphicsView *graphicsView) {
    if (!graphicsView || !graphicsView->scene()) return;
    auto scene = dynamic_cast<BQGraphicsScene*>(graphicsView->scene());
    if (!scene) return;
    qDebug() << "StrTag:" << StrTag;
    if(StrTag.split("/").count() == 4) {
        QString TagType = StrTag.split("/").at(0);
        int TagColorVal = StrTag.split("/").at(1).toInt();

        QString TagPos = StrTag.split("/").at(2);

        float TagPosx = TagPos.split(",").at(0).toFloat();
        float TagPosy = TagPos.split(",").at(1).toFloat();

        QString TagEdge = StrTag.split("/").at(3);

        float TagEdgex = TagEdge.split(",").at(0).toFloat() ;
        float TagEdgey = TagEdge.split(",").at(1).toFloat() ;

        int lineWidth = 2.0 / graphicsView->scale_m;
        if(lineWidth<2)lineWidth=2;
        QPen pen(ListTagColor[TagColorVal]);
        pen.setWidth(lineWidth); // 根据缩放比例调整线宽

        // 根据类型创建相应的图形项并应用缩放和偏移
        if(TagType == "1") { // Ellipse
            BEllipse *ellipse = new BEllipse(0, 0, TagEdgex * 2, TagEdgey * 2, BGraphicsItem::ItemType::Ellipse, pen);
            ellipse->setPos(TagPosx, TagPosy);
            ellipse->setPen(pen);
            scene->addItem(ellipse);
        } else if(TagType == "5") { // Rectangle
            BRectangle *rectangle = new BRectangle(0, 0, TagEdgex * 2, TagEdgey * 2, BGraphicsItem::ItemType::Rectangle, pen);
            rectangle->setPos(TagPosx, TagPosy);
            rectangle->setPen(pen);
            scene->addItem(rectangle);
        } else if(TagType == "7") { // Polygon
            // 解析顶点坐标
            QStringList pointStrList = TagEdge.split(";");
            QList<QPointF> points;
            for (const QString& pointStr : pointStrList) {
                QStringList xy = pointStr.split(",");
                if (xy.size() == 2) {
                    qreal x = xy.at(0).toFloat();
                    qreal y = xy.at(1).toFloat();
                    points.append(QPointF(x, y));
                }
            }
            // 确保有足够的顶点构成多边形
            if (points.size() >= 4) {
                // 创建多边形对象并设置属性
                BPolygon *polygon = new BPolygon(points, BGraphicsItem::ItemType::Polygon, pen);
                polygon->setPen(pen);
                polygon->setPos(TagPosx, TagPosy);
                scene->addItem(polygon);
            }
        }
    }
}

QString copyImageToDirectory(const QString &sourceImagePath, const QString &baseDirPath, const QString &subDirName) {
    QFileInfo fileInfo(sourceImagePath);
    QDir baseDir(baseDirPath);
    if (!baseDir.isAbsolute()) {
        baseDir.makeAbsolute();
    }

    QString dirPath = fileInfo.absolutePath();
    QString fileName = fileInfo.fileName();

    QDir targetDir;
    if (!subDirName.isNull() && !subDirName.isEmpty()) {
        targetDir.setPath(baseDir.filePath(subDirName));
    } else {
        targetDir = baseDir;
    }

    if (!targetDir.exists()) {
        targetDir.mkpath(".");
    }

    QString newImgPath = targetDir.filePath(fileName);

    if (!dirPath.startsWith(baseDir.absolutePath(), Qt::CaseInsensitive) && !QFile::exists(newImgPath)) {
        // 弹出对话框询问用户是否复制图片
        QMessageBox::StandardButton reply = QMessageBox::question(nullptr, "复制图片",
                                                                  "是否将图片复制到目录：" + newImgPath + "？",
                                                                  QMessageBox::Yes | QMessageBox::No);

        if (reply == QMessageBox::Yes) {
            if (QFile::copy(sourceImagePath, newImgPath)) {
                QMessageBox::information(nullptr, "复制成功", "图片成功复制到：" + newImgPath);
                return newImgPath;  // 返回新的图片路径
            } else {
                QMessageBox::warning(nullptr, "复制失败", "无法复制图片到：" + newImgPath);
            }
        }
    }

    // 如果不需要复制或用户选择不复制或复制失败，返回原始图片路径
    return fileInfo.absoluteFilePath();
}
void SlotDrawTag(MyGraphicsView *graphicsView, int Type, QColor mColor) {
    if (!graphicsView || !graphicsView->scene()) return;
    if(graphicsView->scene()->items().isEmpty()) return;
    auto scene = dynamic_cast<BQGraphicsScene*>(graphicsView->scene());
    if (!scene) return;

    if(scene->items().count() > 1) {
        QMessageBox::warning(nullptr, "提示", "已标注过！请删除当前标注后重试");
        return;
    }

    int lineWidth = 2.0 / graphicsView->scale_m;  // 根据缩放比例调整线宽
    if(lineWidth < 2) lineWidth = 2;
    QPen pen(mColor);
    pen.setWidth(lineWidth);

    // 获取视图中心在场景中的坐标
    QPointF centerPoint = graphicsView->mapToScene(graphicsView->viewport()->rect().center());

    // 根据视图的viewport大小和缩放比例来确定矩形的尺寸
    qreal rectWidth = 0.2 * graphicsView->viewport()->width() / graphicsView->scale_m;
    qreal rectHeight= 0.2 * graphicsView->viewport()->height() / graphicsView->scale_m;

    if(Type == 5) {
        // 将矩形的位置设置为视图中心
        BRectangle *m_rectangle = new BRectangle(0, 0, rectWidth, rectHeight, BGraphicsItem::ItemType::Rectangle, pen);
        m_rectangle->setPos(centerPoint.x(), centerPoint.y());
        m_rectangle->setPen(pen);
        scene->addItem(m_rectangle);
    } else if(Type == 1) {
        // 将椭圆的位置设置为视图中心
        BEllipse *m_ellipse = new BEllipse(0, 0, rectWidth, rectHeight, BGraphicsItem::ItemType::Ellipse, pen);
        m_ellipse->setPos(centerPoint.x(), centerPoint.y());
        m_ellipse->setPen(pen);
        scene->addItem(m_ellipse);
    }else if(Type == 7) {//多边形
        BPolygon *m_polygon = new BPolygon(0, 0, rectWidth, rectHeight, BGraphicsItem::ItemType::Polygon, pen);
        m_polygon->setPos(centerPoint.x(), centerPoint.y());
        m_polygon->setPen(pen);
        scene->addItem(m_polygon);
    }

}
void SlotChangeColor(MyGraphicsView *graphicsView, QColor mColor)
{
    if (!graphicsView || !graphicsView->scene()) return;
    auto scene = dynamic_cast<BQGraphicsScene*>(graphicsView->scene());
    if (!scene) return;
    if(scene->items().count()<2)
    {
        //QMessageBox::warning(nullptr, "提示", "场景中没有图形项！");
        return;
    }
    foreach(QGraphicsItem *item, scene->items())
    {
        BGraphicsItem *bItem = dynamic_cast<BGraphicsItem*>(item);
        if(bItem)bItem->updateColor(mColor);
    }
}

void LoadLbPicture(QLabel *pLabel,QString Path)
{
    QFile mfile(Path);
    if(!mfile.exists())
    {
        QPixmap photonull("");
        pLabel->setPixmap(photonull);
        return;
    }
    QPixmap photo(Path);
    pLabel->setScaledContents(true);
    int wLabel=pLabel->width();
    int hLabel=pLabel->height();
    //pLabel->setScaledContents(false);
    int wPhoto=photo.width();
    int hPhoto=photo.height();
    int Finalw,Finalh;
    if((wPhoto>=wLabel)&&(hPhoto>=hLabel))
    {
        if((wPhoto/hPhoto)>(wLabel/hLabel))
        {
            Finalw=wLabel;
            Finalh=wLabel*hPhoto/wPhoto;
        }
        else
        {
            Finalh=hLabel;
            Finalw=hLabel*wPhoto/hPhoto;
        }
    }
    else if((wPhoto>=wLabel)&&(hPhoto<=hLabel))
    {
        Finalw=wLabel;
        Finalh=wLabel*hPhoto/wPhoto;
    }
    else if((wPhoto<=wLabel)&&(hPhoto>=hLabel))
    {
        Finalh=hLabel;
        Finalw=hLabel*wPhoto/hPhoto;
    }
    else
    {
        Finalw=wPhoto;
        Finalh=hPhoto;
    }
    //pLabel->move(0,0);
    pLabel->resize(Finalw,Finalh);
    pLabel->setPixmap(photo.scaled(Finalw,Finalh));
}

//用户自定义的全局数据，通过扩展记录方式写到DWG图中
void wirteGlobalVer(QAxWidget* tmp_MxDrawWidget,QString DicName,QString sName, IMxDrawResbuf* res)
{
    // 得到CAD数据库
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    // 得到全局字典
    IMxDrawDictionary* dict = (IMxDrawDictionary*)database->querySubObject("GetNamedObjectsDictionary()");
    // 得到用户自定义字典，MyExDataDictName是字典名称
    IMxDrawDictionary* myDict = (IMxDrawDictionary*)dict->querySubObject("GetAt(QString)",DicName);
    if (myDict == nullptr)
    {
        // 如果没有，就添加一个字典。
        myDict = (IMxDrawDictionary*)dict->querySubObject("AddObject(QString,QString)",DicName, "McDbDictionary");
    }
    // 得到字典中的扩展记录数据。
    IMxDrawXRecord* rec = (IMxDrawXRecord*)myDict->querySubObject("GetAt(QString)",sName);
    if (rec == nullptr)
    {
        // 如果没有就，添加一个扩展记录.
        rec = (IMxDrawXRecord*)myDict->querySubObject("AddXRecord(QString)",sName);
    }
    rec->dynamicCall("SetXRecordData(QVariant)",res->asVariant());//返回的是数
}

IMxDrawResbuf* readGlobalVar(QAxWidget* tmp_MxDrawWidget,QString DicName,QString sName)
{    
    // 得到CAD数据库
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    // 得到全局字典
    IMxDrawDictionary* dict = (IMxDrawDictionary*)database->querySubObject("GetNamedObjectsDictionary()");
    // 得到用户自定义字典，MyExDataDictName是字典名称
    IMxDrawDictionary* myDict = (IMxDrawDictionary*)dict->querySubObject("GetAt(QString)",DicName);
    if (myDict == nullptr)
    {
        // 没有数据。
        return nullptr;
    }
    // 得到字典中的扩展记录数据。
    IMxDrawXRecord* rec = (IMxDrawXRecord*)myDict->querySubObject("GetAt(QString,bool)",sName,false);
    if (rec == nullptr)
    {
        // 没有数据。
        return nullptr;
    }
    // 得到记录中的数据链表。
    return (IMxDrawResbuf*)rec->querySubObject("GetXRecordData()");
}

IMxDrawPoint* GetSymbolBlockTermPos(QAxWidget *mAxwidget,IMxDrawBlockReference *BlkEnty,QString LD_SYMB1LIB_TERMPOINT)
{
    MxDrawPoint* pt= new MxDrawPoint();
    IMxDrawPoint *ptx=(IMxDrawPoint *)pt;
    QList<IMxDrawPolyline*> listTermEnty=GetTermEnty(mAxwidget,BlkEnty->dynamicCall("GetBlockName()").toString());
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
    for(int i=0;i<listTermEnty.count();i++)
    {
        if(listTermEnty.at(i)->dynamicCall("GetxDataString2(QString,int)","LD_SYMB1LIB_TERMPOINT",0).toString()==LD_SYMB1LIB_TERMPOINT)
        {
            int VCnt=listTermEnty.at(i)->property("NumVerts").toInt();
            if(VCnt!=2) continue;
            double x=0;
            double y=0;
            for(int k=0;k<VCnt;k++)
            {
                IMxDrawPoint* pt= (IMxDrawPoint*) listTermEnty.at(i)->querySubObject("GetPointAt(int)",k);
                x+=pt->x()/2;
                y+=pt->y()/2;
            }
            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+x-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+y-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
            break;
        }
    }
    return ptx;
}
QList<IMxDrawPolyline*> GetTermEnty(QAxWidget *mAxwidget,QString BlkName)
{
    QList<IMxDrawPolyline*> listTermEnty;
    listTermEnty.clear();
    IMxDrawDatabase* database = (IMxDrawDatabase*)mAxwidget->querySubObject("GetDatabase()");
    IMxDrawBlockTable* blkTable = (IMxDrawBlockTable*)database->querySubObject("GetBlockTable()");
    //IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )Enty->querySubObject("BlockTableRecord()"); //blkTable->querySubObject("GetAt(QString,bool)",BlkName ,true);
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* ) blkTable->querySubObject("GetAt(QString,bool)",BlkName ,true);

    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    // 循环得到所有实体
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(mAxwidget,ent)) continue;//去除erase的实体

        if(ent->dynamicCall("ObjectName()").toString()=="McDbPolyline")//是否为端口
        {
            ent->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString();
            if(mAxwidget->dynamicCall("IsOk()").toString()!="true") continue;
            IMxDrawPolyline *EntyTerm=(IMxDrawPolyline *)ent;
            listTermEnty.append(EntyTerm);
        }
    }
    return listTermEnty;
}

QList<IMxDrawPolyline*> GetCurrentSpaceTerms(QAxWidget *mAxwidget)
{
    QList<IMxDrawPolyline*> listTermEnty;
    listTermEnty.clear();
    IMxDrawDatabase* database = (IMxDrawDatabase*)mAxwidget->querySubObject("GetDatabase()");
    // 得到当前图纸空间
    IMxDrawBlockTableRecord* blkRec = (IMxDrawBlockTableRecord*)database->querySubObject("CurrentSpace()");
    // 创建一个用于遍历当前图纸空间的遍历器
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    // 循环得到所有实体
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(mAxwidget,ent)) continue;//去除erase的实体
        if(ent->dynamicCall("ObjectName()").toString()=="McDbPolyline")//是否为端口
        {
            ent->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString();
            if(mAxwidget->dynamicCall("IsOk()").toString()!="true") continue;
            IMxDrawPolyline *EntyTerm=(IMxDrawPolyline *)ent;
            listTermEnty.append(EntyTerm);
        }
    }
    return listTermEnty;
}
bool EntyIsErased(QAxWidget *mAxwidget,IMxDrawEntity *Enty)
{
    //去除erase的实体
    IMxDrawResbuf *resp=(IMxDrawResbuf *)mAxwidget->querySubObject("NewResbuf()");
    resp->AddObjectId(Enty->ObjectID());
    if(((IMxDrawResbuf *)mAxwidget->querySubObject("CallEx(const QString&,QVariant)","Mx_IsErased",resp->asVariant()))->AtString(0)=="Ok") return true;
    return false;
}
bool SetCurLayerVisible(QAxWidget* tmp_MxDrawWidget,QString sLayerName,bool Visible)
{
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    IMxDrawLayerTable* layerTable =(IMxDrawLayerTable*)database->querySubObject("GetLayerTable()");
    IMxDrawLayerTableRecord* layer =(IMxDrawLayerTableRecord*)layerTable->querySubObject("GetAt(QString, true)",sLayerName,false);
    if (layer == nullptr) return false;
    if(Visible) layer->setProperty("IsOff",false);
    else layer->setProperty("IsOff",true);
    tmp_MxDrawWidget->dynamicCall("UpdateDisplay()");
    return true;
}
void SetCurLayer(QAxWidget* tmp_MxDrawWidget,QString sLayerName)
{
    //得到数据库对象
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    // 得到层表.
    IMxDrawLayerTable* layerTable =(IMxDrawLayerTable*)database->querySubObject("GetLayerTable()");

    // 得到层。
    IMxDrawLayerTableRecord* layer =(IMxDrawLayerTableRecord*)layerTable->querySubObject("GetAt(QString, true)",sLayerName,false);
    if (layer == nullptr)
    {
        // 如果没有层，就新建一个层。
        layerTable->querySubObject("Add(QString)",sLayerName);
    }
    else
    {
        // 如果层被删除，就反删除。
        layerTable->setProperty("unErase",true);
    }
    // 设置实体层名到指定层上。
    database->setProperty("CurrentlyLayerName", sLayerName);
}

MyCheckBox::MyCheckBox(QString text,QWidget *parent)
    : QCheckBox(text,parent)
{

}

MyCheckBox::MyCheckBox(QWidget *parent)
    : QCheckBox(parent)
{

}

void MyCheckBox::mouseReleaseEvent(QMouseEvent *e)
{
    setChecked(!isChecked());
    emit clicked(isChecked());
}

void UnitSymbolsView(QString PathDwg,QString PathJpg,QLabel *mLabel,bool Reload)
{
    qDebug()<<"PathDwg:"<<PathDwg;
    qDebug()<<"PathJpg:"<<PathJpg;
    //如果不存在dwg对应的jpg文件，则创建jpg文件
    QFileInfo filedwg(PathDwg);
    if(!filedwg.exists()) {mLabel->setPixmap(QPixmap("").scaled(mLabel->width(),mLabel->height()));return;}


    mLabel->setStyleSheet("background-color: rgb(0, 0, 0)");
    mLabel->setScaledContents(false);
    mLabel->setFrameShape(QFrame::Panel);
    mLabel->setFrameShadow(QFrame::Sunken);
    mLabel->setLineWidth(3);
    mLabel->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);

    QFile filejpg(PathJpg);
    if(filejpg.exists()&&Reload)
    {
        //filejpg.remove();
    }
    if(!filejpg.exists()||Reload)//如果不存在dwg对应的jpg文件，则创建jpg文件
        qDebug()<<"由dwg创建jpg"<<pApp->dynamicCall("DwgToJpg(QString,QString,int,int)",PathDwg,PathJpg,(int)mLabel->width()-10,(int)mLabel->height()-5);
    QPixmap p=QPixmap(PathJpg);
    mLabel->setPixmap(p);
}

int GetTagIdx(QString Tag)
{
    int LeftIdx=-1,RightIdx=-1;
    int TagNum=-1;
    for(int j=0;j<Tag.size();j++)
    {
        QChar aa=Tag.at(j);
        if((aa<'0')||(aa>'9')) {LeftIdx=j;break;}
    }
    for(int j=Tag.size()-1;j>=0;j--)
    {
        QChar aa=Tag.at(j);
        if((aa<'0')||(aa>'9')) {RightIdx=j;break;}
    }
    if((LeftIdx<0)||(RightIdx<0))//全是数字，应该不存在此种情况
    {
        TagNum=Tag.toInt();
    }
    else//查看左下标和右下标是否存在，若存在右下标则使用右下标
    {
        if(RightIdx!=(Tag.count()-1))//存在右下标
            TagNum=Tag.mid(RightIdx+1,Tag.count()-RightIdx).toInt();
        else
        {
            if(LeftIdx!=0) TagNum=Tag.mid(0,LeftIdx).toInt();
            else TagNum=-1;
        }
    }
    return TagNum;
}
//比较TagA和TagB的数字下标，如果TagA下标比TagB大则返回true，反之返回false，无下标的比有下标的小
bool TagABigerThanTagB(QString TagA,QString TagB)
{
    int TagANum,TagBNum;
    TagANum=GetTagIdx(TagA);
    TagBNum=GetTagIdx(TagB);
    if(TagANum>TagBNum) return true;
    else return false;
}

bool StrIsNumber(QString Str)
{
    if(Str=="") return false;
    for(int i=0;i<Str.count();i++)
    {
        if((Str.at(i)<"0")||(Str.at(i)>"9")) return false;
    }
    return true;
}

bool StrIsDouble(QString Str)
{
    if(Str=="") return false;
    int DotNum=0;
    for(int i=0;i<Str.count();i++)
    {
        if(Str.at(i)==".")
        {
            if(DotNum>=1) return false;
            DotNum++;
            continue;
        }
        if((Str.at(i)<"0")||(Str.at(i)>"9")) return false;
    }
    return true;
}

QString GetAttrDefTextString(QAxWidget* tmp_MxDrawWidget,QString Tag)
{
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)tmp_MxDrawWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)tmp_MxDrawWidget->querySubObject("NewResbuf()");
    //filter->AddStringEx("LY_Attdef",8);  // 筛选图层
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    for(int i=0;i<Cnt;i++)
    {
        IMxDrawEntity *Enty = (IMxDrawEntity*)ss1->querySubObject("Item(int)",i);
        if(EntyIsErased(tmp_MxDrawWidget,Enty)) continue;//去除erase的实体
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
        {
            IMxDrawAttributeDefinition *AttrDef=(IMxDrawAttributeDefinition *)Enty;
            if(AttrDef->dynamicCall("Tag()").toString()==Tag)
            {
                return AttrDef->dynamicCall("TextString()").toString();
            }
        }
    }
    return "未找到";
}

void GetDwgRange(QAxWidget* tmp_MxDrawWidget,double &xmin,double &xmax,double &ymin,double &ymax)
{
    bool FirstEnty=true;
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    // 得到当前图纸空间
    IMxDrawBlockTableRecord* blkRec = (IMxDrawBlockTableRecord*)database->querySubObject("CurrentSpace()");
    // 创建一个用于遍历当前图纸空间的遍历器
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    if (iter == nullptr) return;// 循环得到所有实体
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        qDebug()<<"iter";
        IMxDrawEntity* Enty = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(tmp_MxDrawWidget,Enty)) continue;//去除erase的实体
        if (Enty == nullptr)  continue;
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference") continue;
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbText") continue;
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition") continue;
        IMxDrawPoints* pts=(IMxDrawPoints*)Enty->querySubObject("GetBoundingBox2()");
        for(int j=0;j<pts->Count();j++)
        {
            IMxDrawPoint* pt = (IMxDrawPoint*)pts->querySubObject("Item(int)",j);
            if(pt==nullptr) continue;
            qDebug()<<pt->dynamicCall("x()").toDouble()<<" "<<pt->dynamicCall("y()").toDouble();
            if(FirstEnty)
            {
                FirstEnty=false;
                xmin= pt->x();xmax= pt->x();
                ymin= pt->y();ymax= pt->y();
            }
            else
            {
                xmin=xmin<pt->x()?xmin:pt->x();
                xmax=xmax>pt->x()?xmax:pt->x();
                ymin=ymin<pt->y()?ymin:pt->y();
                ymax=ymax>pt->y()?ymax:pt->y();
            }
        }
    }
}

void SetAllAttrDefPos(QAxWidget* tmp_MxDrawWidget,double basex,double basey)
{
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)tmp_MxDrawWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)tmp_MxDrawWidget->querySubObject("NewResbuf()");
    //filter->AddStringEx("LY_Attdef",8);  // 筛选图层
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    qDebug()<<"Cnt="<<Cnt;
    QList<IMxDrawPolyline*> ListTerm=GetCurrentSpaceTerms(tmp_MxDrawWidget);
    int AttriDefNum=0;
    for(int i=0;i<Cnt;i++)
    {
        IMxDrawEntity *Enty = (IMxDrawEntity*)ss1->querySubObject("Item(int)",i);
        if(EntyIsErased(tmp_MxDrawWidget,Enty)) continue;//去除erase的实体
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
        {
            IMxDrawAttributeDefinition *AttrDef=(IMxDrawAttributeDefinition *)Enty;
            IMxDrawPoint *PtPos=(IMxDrawPoint *)AttrDef->querySubObject("Position()");
            if(StrIsNumber(AttrDef->dynamicCall("Tag()").toString())||AttrDef->dynamicCall("Tag()").toString().contains("符号的连接点描述"))//如果是端号，则根据最近的Polyline端口的接线方向确定端号的align和位置
            {
                QString CurTermIndex;
                if(StrIsNumber(AttrDef->dynamicCall("Tag()").toString())) CurTermIndex=AttrDef->dynamicCall("Tag()").toString();
                else
                {
                    QString StrAttrDef=AttrDef->dynamicCall("Tag()").toString();
                    CurTermIndex=StrAttrDef.mid(StrAttrDef.lastIndexOf("[")+1,StrAttrDef.lastIndexOf("]")-StrAttrDef.lastIndexOf("[")-1);
                }
                for(int j=0;j<ListTerm.count();j++)
                {
                    if(ListTerm.at(j)->dynamicCall("GetxDataString2(QString,int)","LD_SYMB1LIB_TERMPOINT",0).toString()==CurTermIndex)
                    {
                        int VCnt=ListTerm.at(j)->property("NumVerts").toInt();
                        if(VCnt!=2) continue;
                        double ptx=0;
                        double pty=0;
                        for(int k=0;k<VCnt;k++)
                        {
                            IMxDrawPoint* pt= (IMxDrawPoint*)ListTerm.at(j)->querySubObject("GetPointAt(int)",k);
                            ptx+=pt->x()/2;
                            pty+=pt->y()/2;
                        }
                        QString LD_PARTLIB_DOTCONDIRECT=ListTerm.at(j)->dynamicCall("GetxDataString2(QString,int)","LD_PARTLIB_DOTCONDIRECT",0).toString();
                        if((LD_PARTLIB_DOTCONDIRECT=="向上")||(LD_PARTLIB_DOTCONDIRECT=="向下"))//端口代号在Term右侧,AlignLeft
                        {
                            PtPos->setX(ptx+1);
                            if(StrIsNumber(AttrDef->dynamicCall("Tag()").toString()))
                            {
                                PtPos->setY(pty-1);
                            }
                            else
                            {
                                if(LD_PARTLIB_DOTCONDIRECT=="向上") PtPos->setY(pty+1.5);
                                else PtPos->setY(pty-3.5);
                            }
                            //if(PtPos->x()<ClosestTermx) PtPos->setX(ClosestTermx+ClosestTermx-PtPos->x());
                            AttrDef->setHorizontalMode(mcHorizontalAlignmentLeft);
                        }
                        else//端口代号在Term上侧
                        {
                            PtPos->setX(ptx);
                            if(StrIsNumber(AttrDef->dynamicCall("Tag()").toString()))
                            {
                                PtPos->setY(pty+1);
                            }
                            else
                            {
                                PtPos->setY(pty-3);
                            }
                            //if(PtPos->y()<ClosestTermy) PtPos->setY(ClosestTermy+ClosestTermy-PtPos->y());
                            if(PtPos->x()<basex) AttrDef->setHorizontalMode(mcHorizontalAlignmentRight);
                            else AttrDef->setHorizontalMode(mcHorizontalAlignmentLeft);
                        }
                        break;
                    }
                }//for(int j=0;j<ListTerm.count();j++)
            }//if(StrIsNumber
            else//如果符号垂直则放到左侧，如果符号水平则放到上侧中间
            {
                double xmin,xmax,ymin,ymax;
                GetDwgRange(tmp_MxDrawWidget,xmin,xmax,ymin,ymax);
                qDebug()<<"xmin="<<xmin<<",xmax="<<xmax<<",ymin="<<ymin<<",ymax="<<ymax;
                if(ListTerm.count()>0)
                {
                    QString LD_PARTLIB_DOTCONDIRECT=ListTerm.at(0)->dynamicCall("GetxDataString2(QString,int)","LD_PARTLIB_DOTCONDIRECT",0).toString();
                    if((LD_PARTLIB_DOTCONDIRECT=="向左")||(LD_PARTLIB_DOTCONDIRECT=="向右"))//设备标识符放上面，其他放下面
                    {
                        AttrDef->setHorizontalMode(mcHorizontalAlignmentCenter);
                        PtPos->setX((xmin+xmax)/2);
                        if(AttrDef->dynamicCall("Tag()").toString().contains("设备标识符"))
                        {
                            PtPos->setY(ymax+2);
                        }
                        else
                        {
                            AttriDefNum++;
                            PtPos->setY(ymin-3*AttriDefNum);
                        }
                    }//if((LD_PARTLIB_DOTCONDIRECT=="向左")||(LD_PARTLIB_DOTCONDIRECT=="向右"))
                    else//放到左侧
                    {
                        AttrDef->setHorizontalMode(mcHorizontalAlignmentRight);
                        PtPos->setX(xmin-1);
                        AttriDefNum++;
                        PtPos->setY((ymax+ymin)/2-3*(AttriDefNum-1)-1);
                    }
                }
            }
            AttrDef->dynamicCall("SetPosition(QAxObject*)",PtPos->asVariant());
            if(AttrDef->horizontalMode()!=mcHorizontalAlignmentLeft) AttrDef->dynamicCall("SetAlignmentPoint(QAxObject*)",PtPos->asVariant());
            AttrDef->dynamicCall("SetRotation(double)",0);
        }
    }
}



qlonglong DrawAttrDef(QAxWidget* tmp_MxDrawWidget,double dInsertionPointX,double dInsertionPointY,QString Tag,QString Text)
{
    //块属性定义文字高度  属性标志 插入图块时，属性提示文字 属性文字插入点x  属性文字插入点y  属性标签字符串 属性文字内容
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    // 得到当前图纸空间
    IMxDrawBlockTableRecord* blkRec = (IMxDrawBlockTableRecord*)database->querySubObject("CurrentSpace()");

    //如果是连接点代号，则放置LY_AttTerm图层，反之则放置LY_Attdef图层
    if(StrIsNumber(Tag)) SetCurLayer(tmp_MxDrawWidget,"LY_AttTerm");
    else SetCurLayer(tmp_MxDrawWidget,"LY_Attdef");
    tmp_MxDrawWidget->setProperty("DrawCADColor", QColorToInt(QColor(255,255,0)));
    IMxDrawAttributeDefinition *AttrDef=(IMxDrawAttributeDefinition *)blkRec->querySubObject("AddAttributeDef(double,MxDrawXLib::McAttributeMode,const QString&,double,double,const QString&,const QString&)",
                                                                                             2.5,0,"",dInsertionPointX,dInsertionPointY,Tag,Text);
    AttrDef->dynamicCall("SetWidthFactor(double)",0.8);
    if(Tag.contains("设备标识符"))
    {
        AttrDef->dynamicCall("setColorIndex(int)",McColor::mcRed);
    }
    else
    {
        AttrDef->dynamicCall("SetHeight(double)",2);
        AttrDef->dynamicCall("setColorIndex(int)",McColor::mcYellow);
    }
    AttrDef->setVerticalMode(mcVerticalAlignmentBaseline);
    SetCurLayer(tmp_MxDrawWidget,"0");
    return AttrDef->ObjectID();
}

void DeleteAttrDef(QAxWidget* tmp_MxDrawWidget,QString Tag)
{
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)tmp_MxDrawWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)tmp_MxDrawWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("LY_Attdef",8);  // 筛选图层
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    qDebug()<<"Cnt="<<Cnt;
    for(int i=0;i<Cnt;i++)
    {
        IMxDrawEntity *Enty = (IMxDrawEntity*)ss1->querySubObject("Item(int)",i);
        if(EntyIsErased(tmp_MxDrawWidget,Enty)) continue;//去除erase的实体
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
        {
            IMxDrawAttributeDefinition *AttrDef=(IMxDrawAttributeDefinition *)Enty;
            if(AttrDef->dynamicCall("Tag()").toString()==Tag)
            {
                AttrDef->dynamicCall("Erase()");
                return ;
            }
        }
    }
}
QString GetTypeBySymb2Class_ID(QString Symb2Class_ID)
{
    QSqlQuery QueryClass=QSqlQuery(T_LibDatabase);
    QString sqlStr=QString("SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+Symb2Class_ID+"'");
    QueryClass.exec(sqlStr);
    if(!QueryClass.next()) return "";
    if(QueryClass.value("Level").toString()=="4")
    {
        QString Parent_ID=QueryClass.value("Parent_ID").toString();
        sqlStr=QString("SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+Parent_ID+"'");//3
        QueryClass.exec(sqlStr);
        if(!QueryClass.next()) return "";
        Parent_ID=QueryClass.value("Parent_ID").toString();
        sqlStr=QString("SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+Parent_ID+"'");//2
        if(!QueryClass.next()) return "";
        return QueryClass.value("Desc").toString();
    }
    else if(QueryClass.value("Level").toString()=="3")
    {
        QString Parent_ID=QueryClass.value("Parent_ID").toString();
        sqlStr=QString("SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+Parent_ID+"'");//2
        QueryClass.exec(sqlStr);
        if(!QueryClass.next()) return "";
        return QueryClass.value("Desc").toString();
    }
    else if(QueryClass.value("Level").toString()=="2")
        return QueryClass.value("Desc").toString();
    return "";
}
void FindAttrDefAndAddAttrToBlock(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkEnty,QString ConnNum_Logic,QString ConnNum)
{
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    // 循环得到所有实体
    //qDebug()<<"ConnNum_Logic="<<ConnNum_Logic<<" ConnNum="<<ConnNum;
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(tmp_MxDrawWidget,ent)) continue;//去除erase的实体
        if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
        {
            IMxDrawAttributeDefinition *attrib=(IMxDrawAttributeDefinition *)ent;
            //根据符号的属性定义对象确定符号标号和端号的内容和位置
            //qDebug()<<"attrib->dynamicCall(Tag()).toString()="<<attrib->dynamicCall("Tag()").toString();
            if(attrib->dynamicCall("Tag()").toString()==ConnNum_Logic)
            {
                //qDebug()<<"attrib->dynamicCall(Tag()).toString()==ConnNum_Logic";
                AddAttrToBlock(tmp_MxDrawWidget,BlkEnty,attrib,ConnNum);
                break;
            }
        }
    }
}
void SetBlockAttrPos(IMxDrawBlockReference *BlkEnty,IMxDrawAttribute *attrib,QString Tag)
{
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
        {
            IMxDrawAttributeDefinition *attribdef=(IMxDrawAttributeDefinition *)ent;
            if(attribdef->dynamicCall("Tag()").toString()==Tag)
            {
                MxDrawPoint* pt= new MxDrawPoint();
                IMxDrawPoint *ptx=(IMxDrawPoint *)pt;

                if(fabs(((IMxDrawPoint *)attribdef->querySubObject("AlignmentPoint()"))->x())>0.01)
                {
                    ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attribdef->querySubObject("AlignmentPoint()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                    ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attribdef->querySubObject("AlignmentPoint()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                    attrib->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
                    attrib->dynamicCall("SetAlignmentPoint(QAxObject*)",ptx->asVariant());
                }
                else
                {
                    ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attribdef->querySubObject("Position()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                    ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attribdef->querySubObject("Position()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                    attrib->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
                }
                BlkEnty->dynamicCall("AssertWriteEnabled()");
                break;
            }
        }
    }
}
void UpdateBlockAttr(IMxDrawBlockReference *BlkEnty,QString TagStr,QString TextStr)
{
    //qDebug()<<"UpdateBlockAttr.TagStr="<<TagStr<<",TextStr="<<TextStr;
    for (int  j = 0; j < BlkEnty->dynamicCall("AttributeCount()").toInt(); j++)
    {
        // 得到块引用中所有的属性
        IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEnty->querySubObject("AttributeItem(int)",j);
        //qDebug()<<"tag="<<attrib->dynamicCall("Tag()").toString();
        if(attrib->dynamicCall("Tag()").toString()==TagStr)
        {
            attrib->dynamicCall("SetTextString(QString)",TextStr);
            if(TagStr=="设备标识符(显示)") attrib->dynamicCall("setColorIndex(int)",McColor::mcCyan);
            SetBlockAttrPos(BlkEnty,attrib,TagStr);
            break;
        }
    }
    BlkEnty->dynamicCall("AssertWriteEnabled()");
}

QString GetBlockAttrTextString(IMxDrawBlockReference *BlkEnty,QString Tag)
{
    for (int  j = 0; j < BlkEnty->dynamicCall("AttributeCount()").toInt(); j++)
    {
        // 得到块引用中所有的属性
        IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEnty->querySubObject("AttributeItem(int)",j);
        if(attrib->dynamicCall("Tag()").toString()==Tag)
        {
            return attrib->dynamicCall("TextString()").toString();
        }
    }
    return "";
}

IMxDrawPoint* GetBlockAttrPos(IMxDrawBlockReference *BlkEnty,QString Tag)
{
    for (int  j = 0; j < BlkEnty->dynamicCall("AttributeCount()").toInt(); j++)
    {
        // 得到块引用中所有的属性
        IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEnty->querySubObject("AttributeItem(int)",j);
        if(attrib->dynamicCall("Tag()").toString()==Tag)
        {
            return (IMxDrawPoint *)attrib->querySubObject("Position()");
        }
    }
}
void AddAttrToWireBlock(IMxDrawBlockReference *BlkEnty,int Mode,QString ConnectionNumber,QString Wires_Color,QString Wires_Diameter)
{
    IMxDrawAttribute *attribConnectionNumber;
    IMxDrawAttribute *attribWires_Color;
    IMxDrawAttribute *attribWires_Diameter;
    //查看连接代号属性块是否存在
    bool ConnectionNumberFind=false,Wires_ColorFind=false,Wires_DiameterFind=false;
    for (int  j = 0; j < BlkEnty->dynamicCall("AttributeCount()").toInt(); j++)
    {
        // 得到块引用中所有的属性
        IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEnty->querySubObject("AttributeItem(int)",j);
        if(attrib->dynamicCall("Tag()").toString()=="连接代号")
        {
            attribConnectionNumber=attrib;
            ConnectionNumberFind=true;
        }
        if(attrib->dynamicCall("Tag()").toString()=="导线颜色")
        {
            attribWires_Color=attrib;
            Wires_ColorFind=true;
        }
        if(attrib->dynamicCall("Tag()").toString()=="连接:截面积/直径")
        {
            attribWires_Diameter=attrib;
            Wires_DiameterFind=true;
        }
    }
    if(!ConnectionNumberFind) attribConnectionNumber=(IMxDrawAttribute *)BlkEnty->querySubObject("AppendAttribute()");
    attribConnectionNumber->dynamicCall("setColorIndex(int)",McColor::mcGreen);
    attribConnectionNumber->dynamicCall("SetHeight(double)",2.2);
    attribConnectionNumber->dynamicCall("SetWidthFactor(double)",0.8);
    attribConnectionNumber->dynamicCall("SetTextString(QString)",ConnectionNumber);
    attribConnectionNumber->dynamicCall("SetTag(QString)","连接代号");
    attribConnectionNumber->dynamicCall("SetIsInvisible(bool)",false);
    attribConnectionNumber->dynamicCall("SetLayer(QString)","LY_Attdef");
    MxDrawPoint* pt= new MxDrawPoint();
    IMxDrawPoint *ptx=(IMxDrawPoint *)pt;
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
    if(Mode==0) //水平排列
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+1.5-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+0.66-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==1) //RotateAngle=0,SingleOrMutiLine=1
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+1.5-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+6.66-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==2) //RotateAngle=1,SingleOrMutiLine=0
    {
        attribConnectionNumber->dynamicCall("SetRotation(double)",PI/2.0);
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()-7-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+3-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==3) //RotateAngle=1,SingleOrMutiLine=1
    {
        attribConnectionNumber->dynamicCall("SetRotation(double)",PI/2.0);
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()-1-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+3-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    attribConnectionNumber->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
    attribConnectionNumber->dynamicCall("SetAlignmentPoint(QAxObject*)",ptx->asVariant());

    if(!Wires_ColorFind) attribWires_Color=(IMxDrawAttribute *)BlkEnty->querySubObject("AppendAttribute()");
    attribWires_Color->dynamicCall("setColorIndex(int)",McColor::mcGreen);
    attribWires_Color->dynamicCall("SetHeight(double)",2.2);
    attribWires_Color->dynamicCall("SetWidthFactor(double)",0.4);
    attribWires_Color->dynamicCall("SetTextString(QString)",Wires_Color);
    attribWires_Color->dynamicCall("SetTag(QString)","导线颜色");
    attribWires_Color->dynamicCall("SetIsInvisible(bool)",false);
    attribWires_Color->dynamicCall("SetLayer(QString)","LY_Attdef");
    if(Mode==0) //水平排列
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+2.5+ConnectionNumber.count()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+0.66-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==1) //RotateAngle=0,SingleOrMutiLine=1
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+1.5-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+3.66-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==2) //RotateAngle=1,SingleOrMutiLine=0
    {
        attribConnectionNumber->dynamicCall("SetRotation(double)",PI/2.0);
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()-4-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+3-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==3) //RotateAngle=1,SingleOrMutiLine=1
    {
        attribConnectionNumber->dynamicCall("SetRotation(double)",PI/2.0);
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()-1-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+3+ConnectionNumber.count()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    attribWires_Color->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
    attribWires_Color->dynamicCall("SetAlignmentPoint(QAxObject*)",ptx->asVariant());

    if(!Wires_DiameterFind) attribWires_Diameter=(IMxDrawAttribute *)BlkEnty->querySubObject("AppendAttribute()");
    attribWires_Diameter->dynamicCall("setColorIndex(int)",McColor::mcGreen);
    attribWires_Diameter->dynamicCall("SetHeight(double)",2.2);
    attribWires_Diameter->dynamicCall("SetWidthFactor(double)",0.4);
    attribWires_Diameter->dynamicCall("SetTextString(QString)",Wires_Diameter);
    attribWires_Diameter->dynamicCall("SetTag(QString)","连接:截面积/直径");
    attribWires_Diameter->dynamicCall("SetIsInvisible(bool)",false);
    attribWires_Diameter->dynamicCall("SetLayer(QString)","LY_Attdef");
    if(Mode==0) //水平排列
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+3+ConnectionNumber.count()+Wires_Color.count()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+0.66-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==1) //RotateAngle=0,SingleOrMutiLine=1
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+1.5-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+0.66-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==2) //RotateAngle=1,SingleOrMutiLine=0
    {
        attribConnectionNumber->dynamicCall("SetRotation(double)",PI/2.0);
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()-1-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+3-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    else if(Mode==3) //RotateAngle=1,SingleOrMutiLine=1
    {
        attribConnectionNumber->dynamicCall("SetRotation(double)",PI/2.0);
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()-1-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+4+ConnectionNumber.count()+Wires_Color.count()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
    }
    attribWires_Diameter->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
    attribWires_Diameter->dynamicCall("SetAlignmentPoint(QAxObject*)",ptx->asVariant());

    BlkEnty->dynamicCall("AssertWriteEnabled()");
}

void AddAttrToBlockBesideDefAttr(QAxWidget* tmp_MxDrawWidget,int Direction,IMxDrawBlockReference *BlkEnty,QString TagDef,QString TagNew,QString TextStr,McColor mccolor)
{
    qDebug()<<"AddAttrToBlockBesideDefAttr,Direction="<<Direction;
    double Kcoef=33/3.5;//1.1;
    QFontMetrics font(QFont("Arial"));
    for (int  j = 0; j < BlkEnty->dynamicCall("AttributeCount()").toInt(); j++)
    {
        qDebug()<<"j="<<j;
        // 得到块引用中所有的属性
        IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEnty->querySubObject("AttributeItem(int)",j);
        if(EntyIsErased(tmp_MxDrawWidget,(IMxDrawEntity *)attrib)) continue;
        if(attrib->dynamicCall("Tag()").toString()==TagDef)
        {
            qDebug()<<"Tag find";
            IMxDrawAttribute *attribNew=(IMxDrawAttribute *)BlkEnty->querySubObject("AppendAttribute()");
            attribNew->dynamicCall("SetLayer(QString)","LY_Attdef");
            attribNew->dynamicCall("SetRotation(double)",attrib->dynamicCall("Rotation()").toDouble());
            attribNew->dynamicCall("setColorIndex(int)",mccolor);
            attribNew->dynamicCall("SetHeight(double)",attrib->dynamicCall("Height()").toDouble());
            attribNew->dynamicCall("SetWidthFactor(double)",attrib->dynamicCall("WidthFactor()").toDouble());
            attribNew->dynamicCall("SetTextString(QString)",TextStr);
            attribNew->dynamicCall("SetTag(QString)",TagNew);
            attribNew->dynamicCall("SetIsInvisible(bool)",false);
            attribNew->dynamicCall("SetLayer(QString)","LY_Attdef");
            attribNew->setHorizontalMode(attrib->horizontalMode());
            attribNew->setVerticalMode(attrib->verticalMode());
            MxDrawPoint* pt= new MxDrawPoint();
            IMxDrawPoint *ptx=(IMxDrawPoint *)pt;
            qDebug()<<"233";
            if(fabs(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->x())>0.01)
            {
                qDebug()<<"344";
                if(Direction==1)
                {
                    if(attrib->horizontalMode()==mcHorizontalAlignmentLeft)  ptx->setX(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->x()+1+font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);//attrib->dynamicCall("TextString()").toString().count()*2
                    else ptx->setX(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->x()+1+font.width(TextStr)/Kcoef);
                    ptx->setY(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->y());
                }
                else if(Direction==2)
                {
                    ptx->setX(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->x());
                    if(attrib->horizontalMode()==mcHorizontalAlignmentLeft) ptx->setY(((IMxDrawPoint *)attrib->querySubObject("Position()"))->y()+1+font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);
                    else ptx->setY(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->y()+1+font.width(TextStr)/Kcoef);
                }
                else if(Direction==3)
                {
                    if(attrib->horizontalMode()==mcHorizontalAlignmentRight)  ptx->setX(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->x()-1-font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);
                    else ptx->setX(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->x()-1-font.width(TextStr)/Kcoef);
                    ptx->setY(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->y());
                }
                else if(Direction==4)
                {
                    ptx->setX(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->x());
                    if(attrib->horizontalMode()==mcHorizontalAlignmentRight) ptx->setY(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->y()-1-font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);
                    else ptx->setY(((IMxDrawPoint *)attrib->querySubObject("AlignmentPoint()"))->y()-1-font.width(TextStr)/Kcoef);
                }
                attribNew->dynamicCall("SetAlignmentPoint(QAxObject*)",ptx->asVariant());
            }
            else
            {
                qDebug()<<"23345";
                if(Direction==1)
                {
                    if(attrib->horizontalMode()==mcHorizontalAlignmentLeft)  ptx->setX(((IMxDrawPoint *)attrib->querySubObject("Position()"))->x()+1+font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);
                    else ptx->setX(((IMxDrawPoint *)attrib->querySubObject("Position()"))->x()+1+font.width(TextStr)/Kcoef);
                    ptx->setY(((IMxDrawPoint *)attrib->querySubObject("Position()"))->y());
                }
                else if(Direction==2)
                {
                    ptx->setX(((IMxDrawPoint *)attrib->querySubObject("Position()"))->x());
                    if(attrib->horizontalMode()==mcHorizontalAlignmentLeft) ptx->setY(((IMxDrawPoint *)attrib->querySubObject("Position()"))->y()+1+font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);
                    else ptx->setY(((IMxDrawPoint *)attrib->querySubObject("Position()"))->y()+1+font.width(TextStr)/Kcoef);
                }
                else if(Direction==3)
                {
                    if(attrib->horizontalMode()==mcHorizontalAlignmentRight)  ptx->setX(((IMxDrawPoint *)attrib->querySubObject("Position()"))->x()-1-font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);
                    else ptx->setX(((IMxDrawPoint *)attrib->querySubObject("Position()"))->x()-1-font.width(TextStr)/Kcoef);
                    ptx->setY(((IMxDrawPoint *)attrib->querySubObject("Position()"))->y());
                }
                else if(Direction==4)
                {
                    ptx->setX(((IMxDrawPoint *)attrib->querySubObject("Position()"))->x());
                    if(attrib->horizontalMode()==mcHorizontalAlignmentRight) ptx->setY(((IMxDrawPoint *)attrib->querySubObject("Position()"))->y()-1-font.width(attrib->dynamicCall("TextString()").toString())/Kcoef);
                    else ptx->setY(((IMxDrawPoint *)attrib->querySubObject("Position()"))->y()-1-font.width(TextStr)/Kcoef);
                }
                attribNew->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
            }
            BlkEnty->dynamicCall("AssertWriteEnabled()");
            break;
        }
    }
}

void CopyAttr(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkEntyOld,IMxDrawBlockReference *BlkEntyNew)
{
    for (int  j = 0; j < BlkEntyOld->dynamicCall("AttributeCount()").toInt(); j++)
    {
        // 得到块引用中所有的属性
        IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEntyOld->querySubObject("AttributeItem(int)",j);
        IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEntyOld->querySubObject("BlockTableRecord()");
        IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
        for (; !iter->Done(); iter->Step(true, false))
        {
            // 得到遍历器当前的实体
            IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
            if(EntyIsErased(tmp_MxDrawWidget,ent)) continue;//去除erase的实体
            if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
            {
                IMxDrawAttributeDefinition *attribdef=(IMxDrawAttributeDefinition *)ent;
                if(attribdef->dynamicCall("Tag()").toString()==attrib->dynamicCall("Tag()").toString())
                {
                    AddAttrToBlock(tmp_MxDrawWidget,BlkEntyNew,attribdef,attrib->dynamicCall("TextString()").toString());
                    break;
                }
            }
        }
    }
}


void AddAttrToBlock(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkEnty,IMxDrawAttributeDefinition *attrdef,QString TextStr)
{
    IMxDrawAttribute *attrib=(IMxDrawAttribute *)BlkEnty->querySubObject("AppendAttribute()");
    attrib->dynamicCall("SetRotation(double)",attrdef->dynamicCall("Rotation()").toDouble());
    if(attrdef->dynamicCall("Tag()").toString()=="设备标识符(显示)")
    {
        if((TextStr!="+")&&(TextStr!="-"))
            attrib->dynamicCall("setColorIndex(int)",McColor::mcCyan);
        else
            attrib->dynamicCall("setColorIndex(int)",McColor::mcRed);
    }
    else attrib->dynamicCall("setColorIndex(int)",attrdef->dynamicCall("colorIndex()").toInt());
    attrib->dynamicCall("SetHeight(double)",attrdef->dynamicCall("Height()").toDouble());
    attrib->dynamicCall("SetWidthFactor(double)",attrdef->dynamicCall("WidthFactor()").toDouble());
    attrib->dynamicCall("SetTextString(QString)",TextStr);
    attrib->dynamicCall("SetTag(QString)",attrdef->dynamicCall("Tag()").toString());
    attrib->dynamicCall("SetIsInvisible(bool)",false);
    attrib->dynamicCall("SetLayer(QString)","LY_Attdef");
    attrib->setHorizontalMode(attrdef->horizontalMode());
    attrib->setVerticalMode(attrdef->verticalMode());
    MxDrawPoint* pt= new MxDrawPoint();
    IMxDrawPoint *ptx=(IMxDrawPoint *)pt;
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
    if(fabs(((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x())>0.01)
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
        attrib->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
        attrib->dynamicCall("SetAlignmentPoint(QAxObject*)",ptx->asVariant());
    }
    else
    {
        ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
        ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
        attrib->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
    }
    BlkEnty->dynamicCall("AssertWriteEnabled()");
}
QString GetGaoCengNameByPageID(int Page_ID)
{
    QString PageName="";
    QSqlQuery query=QSqlQuery(T_ProjectDatabase);
    QString sqlstr=QString("SELECT * FROM Page WHERE Page_ID = "+QString::number(Page_ID));
    query.exec(sqlstr);
    if(!query.next()) return "";
    int ProjectStructure_ID=query.value("ProjectStructure_ID").toInt();
    QSqlQuery queryPageStru=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QString::number(ProjectStructure_ID));
    queryPageStru.exec(sqlstr);
    if(!queryPageStru.next()) return "";
    QSqlQuery queryPagePos=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPageStru.value("Parent_ID").toString());
    queryPagePos.exec(sqlstr);
    if(!queryPagePos.next()) return "";
    QSqlQuery queryPageGaoceng=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPagePos.value("Parent_ID").toString());
    queryPageGaoceng.exec(sqlstr);
    if(!queryPageGaoceng.next()) return "";
    return queryPageGaoceng.value("Structure_INT").toString();
}
QString GetPageNameByPageID(int Page_ID)
{
    QString PageName="";
    QSqlQuery query=QSqlQuery(T_ProjectDatabase);
    QString sqlstr=QString("SELECT * FROM Page WHERE Page_ID = "+QString::number(Page_ID));
    query.exec(sqlstr);
    if(!query.next()) return "";
    int ProjectStructure_ID=query.value("ProjectStructure_ID").toInt();
    QSqlQuery queryPageStru=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QString::number(ProjectStructure_ID));
    queryPageStru.exec(sqlstr);
    if(!queryPageStru.next()) return "";
    QSqlQuery queryPagePos=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPageStru.value("Parent_ID").toString());
    queryPagePos.exec(sqlstr);
    if(!queryPagePos.next()) return "";
    QSqlQuery queryPageGaoceng=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPagePos.value("Parent_ID").toString());
    queryPageGaoceng.exec(sqlstr);
    if(!queryPageGaoceng.next()) return "";
    if(queryPageGaoceng.value("Structure_INT").toString()!="") PageName+="="+queryPageGaoceng.value("Structure_INT").toString();
    if(queryPagePos.value("Structure_INT").toString()!="") PageName+="+"+queryPagePos.value("Structure_INT").toString();
    if(queryPageStru.value("Structure_INT").toString()!="") PageName+="&"+queryPageStru.value("Structure_INT").toString();
    if(PageName!="")  PageName+="·"+query.value("PageName").toString();
    else PageName+=query.value("PageName").toString();
    return PageName;
}

QString ExtractPagePrefix(const QString &fullName)
{
    int dotIndex = fullName.indexOf(QChar(0x00B7));
    if (dotIndex < 0) return QString();
    return fullName.left(dotIndex).trimmed();
}

QString ExtractPageBaseName(const QString &fullName)
{
    int dotIndex = fullName.indexOf(QChar(0x00B7));
    if (dotIndex < 0) return fullName.trimmed();
    return fullName.mid(dotIndex + 1).trimmed();
}

QString BuildCanonicalPagePrefix(const QString &rawPrefix, const QString &pageCode)
{
    QString prefix = rawPrefix.trimmed();
    int dotIndex = prefix.indexOf(QChar(0x00B7));
    if (dotIndex >= 0) {
        prefix = prefix.left(dotIndex).trimmed();
    }

    int ampIndex = prefix.indexOf('&');
    if (ampIndex >= 0) {
        QString head = prefix.left(ampIndex).trimmed();
        QString existingCode = prefix.mid(ampIndex + 1).trimmed();
        QString effectiveCode = pageCode.trimmed().isEmpty() ? existingCode : pageCode.trimmed();
        if (!head.isEmpty())
            return head + "&" + effectiveCode;
        return "&" + effectiveCode;
    }

    // 没有现成的页号时，不强制追加
    return prefix;
}

QString BuildCanonicalPageName(const QString &rawPrefix, const QString &pageCode, const QString &baseName)
{
    const QString canonicalPrefix = BuildCanonicalPagePrefix(rawPrefix, pageCode);
    QString trimmedBase = baseName.trimmed();
    if (trimmedBase.isEmpty())
        trimmedBase = baseName;

    if (canonicalPrefix.isEmpty()) {
        const QString head = rawPrefix.trimmed();
        if (head.isEmpty())
            return trimmedBase;
        return head + QChar(0x00B7) + trimmedBase;
    }

    return canonicalPrefix + QChar(0x00B7) + trimmedBase;
}

void SplitPagePrefix(const QString &prefix, QString *gaoceng, QString *pos, QString *pageCode)
{
    if (gaoceng) gaoceng->clear();
    if (pos) pos->clear();
    if (pageCode) pageCode->clear();

    const int eqIndex = prefix.indexOf('=');
    const int plusIndex = prefix.indexOf('+');
    const int ampIndex = prefix.indexOf('&');

    if (gaoceng && eqIndex >= 0) {
        int end = prefix.length();
        if (plusIndex > eqIndex && (ampIndex < 0 || plusIndex < ampIndex))
            end = plusIndex;
        else if (ampIndex > eqIndex)
            end = ampIndex;
        *gaoceng = prefix.mid(eqIndex + 1, end - eqIndex - 1).trimmed();
    }

    if (pos && plusIndex >= 0) {
        int end = (ampIndex > plusIndex) ? ampIndex : prefix.length();
        *pos = prefix.mid(plusIndex + 1, end - plusIndex - 1).trimmed();
    }

    if (pageCode && ampIndex >= 0)
        *pageCode = prefix.mid(ampIndex + 1).trimmed();
}

QStringList PageNameCandidates(const QString &fullName)
{
    QStringList candidates;
    if (!fullName.isEmpty())
        candidates << fullName;
    const QString base = ExtractPageBaseName(fullName);
    if (!base.isEmpty() && base != fullName)
        candidates << base;
    candidates.removeDuplicates();
    return candidates;
}

QString IncrementPageBaseName(const QString &baseName)
{
    if (baseName.isEmpty())
        return "1";
    
    const QString trimmed = baseName.trimmed();
    if (trimmed.isEmpty())
        return "1";
    
    // 规则3：以数字结尾的，取尾部数字递增
    QRegExp digitPattern("(\\d+)$");
    if (digitPattern.indexIn(trimmed) >= 0) {
        const QString numStr = digitPattern.cap(1);
        const int pos = digitPattern.indexIn(trimmed);
        const QString prefix = trimmed.left(pos);
        bool ok;
        int num = numStr.toInt(&ok);
        if (ok) {
            num++;
            // 保持与原数字相同的宽度（前导零）
            QString newNum = QString::number(num);
            if (numStr.length() > newNum.length() && numStr.startsWith('0')) {
                newNum = newNum.rightJustified(numStr.length(), '0');
            }
            return prefix + newNum;
        }
    }
    
    // 规则1：以英文字母结尾的，最后一个字符递增
    QChar lastChar = trimmed.at(trimmed.length() - 1);
    if ((lastChar >= 'a' && lastChar <= 'z') || (lastChar >= 'A' && lastChar <= 'Z')) {
        QString prefix = trimmed.left(trimmed.length() - 1);
        QChar nextChar = lastChar;
        
        // 处理小写字母
        if (lastChar >= 'a' && lastChar <= 'z') {
            if (lastChar == 'z') {
                // z 变 aa, az 变 ba
                return trimmed + 'a';
            } else {
                nextChar = QChar(lastChar.unicode() + 1);
                return prefix + nextChar;
            }
        }
        
        // 处理大写字母
        if (lastChar >= 'A' && lastChar <= 'Z') {
            if (lastChar == 'Z') {
                // Z 变 AA, AZ 变 BA
                return trimmed + 'A';
            } else {
                nextChar = QChar(lastChar.unicode() + 1);
                return prefix + nextChar;
            }
        }
    }
    
    // 规则2：中文或其他字符结尾的，后面加字符'1'
    return trimmed + "1";
}

int FindFirstPageIDUnderStructure(int projectStructureId)
{
    // 首先检查该结构节点下是否直接有图纸
    QSqlQuery queryPage(T_ProjectDatabase);
    queryPage.prepare("SELECT Page_ID FROM Page WHERE ProjectStructure_ID = :psid ORDER BY Page_ID LIMIT 1");
    queryPage.bindValue(":psid", projectStructureId);
    if (queryPage.exec() && queryPage.next()) {
        return queryPage.value("Page_ID").toInt();
    }
    
    // 如果没有，递归查找子结构节点
    QSqlQuery queryChildren(T_ProjectDatabase);
    queryChildren.prepare("SELECT ProjectStructure_ID FROM ProjectStructure WHERE Parent_ID = :pid ORDER BY ProjectStructure_ID");
    queryChildren.bindValue(":pid", projectStructureId);
    if (queryChildren.exec()) {
        while (queryChildren.next()) {
            int childId = queryChildren.value("ProjectStructure_ID").toInt();
            int pageId = FindFirstPageIDUnderStructure(childId);
            if (pageId > 0) {
                return pageId;
            }
        }
    }
    
    return -1; // 未找到
}

bool UpdateProjectStructureDesc(const QString &structureId, const QString &structureInt, const QString &desc, int parentId)
{
    if (structureInt.trimmed().isEmpty()) {
        return false;
    }
    
    // 首先查找是否已存在该记录
    QSqlQuery queryCheck(T_ProjectDatabase);
    queryCheck.prepare("SELECT ProjectStructure_ID FROM ProjectStructure WHERE Structure_ID = :sid AND Structure_INT = :sint");
    queryCheck.bindValue(":sid", structureId);
    queryCheck.bindValue(":sint", structureInt.trimmed());
    
    if (queryCheck.exec() && queryCheck.next()) {
        // 记录已存在，更新描述
        QSqlQuery queryUpdate(T_ProjectDatabase);
        queryUpdate.prepare("UPDATE ProjectStructure SET Struct_Desc = :desc WHERE Structure_ID = :sid AND Structure_INT = :sint");
        queryUpdate.bindValue(":desc", desc.trimmed());
        queryUpdate.bindValue(":sid", structureId);
        queryUpdate.bindValue(":sint", structureInt.trimmed());
        return queryUpdate.exec();
    } else {
        // 记录不存在，插入新记录
        // 对于高层节点(Structure_ID=3)，Parent_ID为1(项目节点)
        // 对于位置和分组节点，需要指定正确的Parent_ID
        if (structureId == "3") {
            // 高层节点，Parent_ID固定为1
            QSqlQuery queryInsert(T_ProjectDatabase);
            queryInsert.prepare("INSERT INTO ProjectStructure (Structure_ID, Structure_INT, Struct_Desc, Parent_ID) VALUES (:sid, :sint, :desc, 1)");
            queryInsert.bindValue(":sid", structureId);
            queryInsert.bindValue(":sint", structureInt.trimmed());
            queryInsert.bindValue(":desc", desc.trimmed());
            return queryInsert.exec();
        } else {
            // 位置或分组节点，暂不自动创建（需要明确的父节点关系）
            return false;
        }
    }
}

void RemoveEmptyStructureNodes(int projectStructureId)
{
    // 检查该结构节点下是否还有图纸
    QSqlQuery queryPages(T_ProjectDatabase);
    queryPages.prepare("SELECT COUNT(*) as page_count FROM Page WHERE ProjectStructure_ID = :psid");
    queryPages.bindValue(":psid", projectStructureId);
    
    if (!queryPages.exec() || !queryPages.next()) {
        return;
    }
    
    int pageCount = queryPages.value("page_count").toInt();
    
    // 检查是否有子结构节点
    QSqlQuery queryChildren(T_ProjectDatabase);
    queryChildren.prepare("SELECT COUNT(*) as child_count FROM ProjectStructure WHERE Parent_ID = :pid");
    queryChildren.bindValue(":pid", projectStructureId);
    
    if (!queryChildren.exec() || !queryChildren.next()) {
        return;
    }
    
    int childCount = queryChildren.value("child_count").toInt();
    
    // 如果既没有图纸也没有子节点,删除该节点
    if (pageCount == 0 && childCount == 0) {
        // 获取父节点ID
        QSqlQuery queryNode(T_ProjectDatabase);
        queryNode.prepare("SELECT Parent_ID, Structure_ID FROM ProjectStructure WHERE ProjectStructure_ID = :psid");
        queryNode.bindValue(":psid", projectStructureId);
        
        if (!queryNode.exec() || !queryNode.next()) {
            return;
        }
        
        int parentId = queryNode.value("Parent_ID").toInt();
        int structureId = queryNode.value("Structure_ID").toInt();
        
        // 删除该节点(但不要删除项目根节点,Structure_ID=1)
        if (structureId != 1) {
            QSqlQuery queryDelete(T_ProjectDatabase);
            queryDelete.prepare("DELETE FROM ProjectStructure WHERE ProjectStructure_ID = :psid");
            queryDelete.bindValue(":psid", projectStructureId);
            queryDelete.exec();
            
            // 递归检查父节点
            if (parentId > 0) {
                RemoveEmptyStructureNodes(parentId);
            }
        }
    }
}

//Structure_ID=5
bool CheckProjectStructure_IDSameOrNot(QString PageProjectStructure_ID1,QString UnitProjectStructure_ID2)
{
    QSqlQuery queryPagePos=QSqlQuery(T_ProjectDatabase);
    QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+PageProjectStructure_ID1);
    queryPagePos.exec(sqlstr);
    if(!queryPagePos.next()) return false;
    QSqlQuery queryPageGaoceng=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPagePos.value("Parent_ID").toString());
    queryPageGaoceng.exec(sqlstr);
    if(!queryPageGaoceng.next()) return false;

    QSqlQuery queryUnitPos=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+UnitProjectStructure_ID2);
    queryUnitPos.exec(sqlstr);
    if(!queryUnitPos.next()) return false;
    QSqlQuery queryUnitGaoceng=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryUnitPos.value("Parent_ID").toString());
    queryUnitGaoceng.exec(sqlstr);
    if(!queryUnitGaoceng.next()) return false;

    qDebug()<<"PageGaoceng="<<queryPageGaoceng.value("Structure_INT").toString()<<",UnitGaoceng="<<queryUnitGaoceng.value("Structure_INT").toString();
    qDebug()<<"PagePos="<<queryPagePos.value("Structure_INT").toString()<<",UnitPos="<<queryUnitPos.value("Structure_INT").toString();
    if(queryPageGaoceng.value("Structure_INT").toString()!=queryUnitGaoceng.value("Structure_INT").toString()) return false;
    if(queryPagePos.value("Structure_INT").toString()!=queryUnitPos.value("Structure_INT").toString()) return false;
    return true;
}

QString GetPosProjectStructure_IDByGaocengAndPos(QString GaocengStr,QString PosStr)
{
    qDebug()<<"GetProjectStructure_IDByGaocengAndPos";
    QSqlQuery QueryProjectStructure(T_ProjectDatabase);
    QString StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+PosStr+"'";
    QueryProjectStructure.exec(StrSql);
    while(QueryProjectStructure.next())
    {
        QSqlQuery QuerySearch(T_ProjectDatabase);
        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryProjectStructure.value("Parent_ID").toString()+" AND Structure_INT = '"+GaocengStr+"'";
        QuerySearch.exec(StrSql);
        if(QuerySearch.next())
        {
            return QueryProjectStructure.value("ProjectStructure_ID").toString();
        }
    }
    return "";
}
QString GetPageProjectStructure_IDByGaocengAndPos(QString GaocengStr,QString PosStr,QString PageInt)
{
    qDebug()<<"GetProjectStructure_IDByGaocengAndPos,GaocengStr="<<GaocengStr<<",PosStr="<<PosStr<<",PageInt="<<PageInt;;
    QSqlQuery QueryProjectStructure(T_ProjectDatabase);
    QString StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+PosStr+"'";
    QueryProjectStructure.exec(StrSql);
    while(QueryProjectStructure.next())
    {
        QSqlQuery QuerySearch(T_ProjectDatabase);
        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryProjectStructure.value("Parent_ID").toString()+" AND Structure_INT = '"+GaocengStr+"'";
        QuerySearch.exec(StrSql);
        if(QuerySearch.next())
        {
            StrSql="SELECT * FROM ProjectStructure WHERE Parent_ID = '"+QueryProjectStructure.value("ProjectStructure_ID").toString()+"' AND Structure_INT = '"+PageInt+"'";
            QuerySearch.exec(StrSql);
            if(QuerySearch.next()) return QuerySearch.value("ProjectStructure_ID").toString();
        }
    }
    return "";
}

QString GetProjectStructureIDByPageID(int Page_ID)//Structure_ID=5
{
    qDebug()<<"Page_ID="<<Page_ID;
    //得到当前Page所在的位置的ProjectStructure_ID
    QSqlQuery QueryPage(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Page WHERE Page_ID= "+QString::number(Page_ID);
    QueryPage.exec(StrSql);
    if(QueryPage.next())
    {
        QSqlQuery QueryProjectStructure(T_ProjectDatabase);
        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("ProjectStructure_ID").toString();
        QueryProjectStructure.exec(StrSql);
        if(QueryProjectStructure.next())
        {
            StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryProjectStructure.value("Parent_ID").toString();
            QueryProjectStructure.exec(StrSql);
            if(QueryProjectStructure.next())
            {
                QString PosStr=QueryProjectStructure.value("Structure_INT").toString();
                StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryProjectStructure.value("Parent_ID").toString();
                QueryProjectStructure.exec(StrSql);
                if(QueryProjectStructure.next())
                {
                    QString GaocengStr=QueryProjectStructure.value("Structure_INT").toString();
                    return QString::number(InsertRecordToProjectStructure(0,GaocengStr,PosStr,""));
                }
            }
        }
    }
    return "";
}

int GetSymbolIDByTermID(int Type,QString TermID)
{
    QSqlQuery QuerySearchTerm(T_ProjectDatabase);
    QString StrSql;
    if(Type==0) StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+TermID;
    else if(Type==1) StrSql="SELECT * FROM TerminalInstance WHERE TerminalInstanceID= "+TermID.mid(0,TermID.indexOf("."));
    QuerySearchTerm.exec(StrSql);
    if(QuerySearchTerm.next())
    {
        if(Type==0) return QuerySearchTerm.value("Symbol_ID").toInt();
        else if(Type==1) return QuerySearchTerm.value("Terminal_ID").toInt();
    }
    return 0;
}

QString GetLibIDBySymbolID(int SymbolID)
{
    QSqlQuery QuerySearchUnit(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(SymbolID);
    QuerySearchUnit.exec(StrSql);
    if(QuerySearchUnit.next())
    {
        QString Type=QuerySearchUnit.value("Type").toString();
        QString PartCode=QuerySearchUnit.value("PartCode").toString();
        QSqlQuery QuerySearchLib(T_LibDatabase);
        StrSql="SELECT * FROM Equipment WHERE Type= '"+Type+"' AND PartCode='"+PartCode+"'";
        QuerySearchLib.exec(StrSql);
        if(QuerySearchLib.next())
        {
            return QuerySearchLib.value("Equipment_ID").toString();
        }
    }
    return "";
}

QString GetComponentDTBySymbolID(QString SymbolID,int Type)
{
    QString DT;
    if(Type==0)
    {
        QSqlQuery QuerySearchUnit(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+SymbolID;
        QuerySearchUnit.exec(StrSql);
        if(QuerySearchUnit.next())
        {
            QSqlQuery QueryEquipment(T_ProjectDatabase);
            StrSql="SELECT * FROM Equipment WHERE Equipment_ID= "+QuerySearchUnit.value("Equipment_ID").toString();
            QueryEquipment.exec(StrSql);
            if(QueryEquipment.next()) DT=QueryEquipment.value("DT").toString();
            return DT;
        }
    }
    else if(Type==1)
    {
        QSqlQuery QuerySearchStrip(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Terminal WHERE Terminal_ID= "+SymbolID;
        QuerySearchStrip.exec(StrSql);
        if(QuerySearchStrip.next())
        {
            QSqlQuery QueryTerminalStrip(T_ProjectDatabase);
            StrSql="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QuerySearchStrip.value("TerminalStrip_ID").toString();
            QueryTerminalStrip.exec(StrSql);
            if(QueryTerminalStrip.next()) DT=QueryTerminalStrip.value("DT").toString();
            return DT;
        }
    }
    else if(Type==2)
    {
        QSqlQuery QueryJXB(T_ProjectDatabase);
        QString StrSql="SELECT * FROM JXB WHERE JXB_ID= "+SymbolID;
        QueryJXB.exec(StrSql);
        if(QueryJXB.next())
        {
            return QueryJXB.value("ConnectionNumber").toString();
        }
    }
    else if(Type==3)//短接片
    {
        return SymbolID;
    }
    return "";
}

int GetTerminal_IDByTerminalInstanceID(int TerminalInstanceID)
{
    QSqlQuery QueryTerminalInstance(T_ProjectDatabase);
    QString StrSql="SELECT * FROM TerminalInstance WHERE TerminalInstanceID= "+QString::number(TerminalInstanceID);
    QueryTerminalInstance.exec(StrSql);
    if(QueryTerminalInstance.next())
    {
        return QueryTerminalInstance.value("Terminal_ID").toInt();
    }
    return 0;
}

int GetUnitStripIDBySymbolID(QString SymbolID,int Type)
{
    if(Type==0)
    {
        QSqlQuery QuerySearchUnit(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+SymbolID;
        QuerySearchUnit.exec(StrSql);
        if(QuerySearchUnit.next())
        {
            return QuerySearchUnit.value("Equipment_ID").toInt();
        }
    }
    else if(Type==1)
    {
        QSqlQuery QuerySearchStrip(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Terminal WHERE Terminal_ID= "+SymbolID;
        QuerySearchStrip.exec(StrSql);
        if(QuerySearchStrip.next())
        {
            return QuerySearchStrip.value("TerminalStrip_ID").toInt();
        }
    }
    return -1;
}

int GetUnitStripIDByTermID(int Type,int TermID,QString &DT)
{
    QSqlQuery QuerySearchTerm(T_ProjectDatabase);
    QString StrSql;
    if(Type==0) StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+QString::number(TermID);
    else if(Type==1) StrSql="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+QString::number(TermID);
    QuerySearchTerm.exec(StrSql);
    if(QuerySearchTerm.next())
    {
        QSqlQuery QuerySearchUnitTermimal(T_ProjectDatabase);
        if(Type==0)  StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+QuerySearchTerm.value("Symbol_ID").toString();
        else if(Type==1) StrSql="SELECT * FROM Terminal WHERE Terminal_ID= "+QuerySearchTerm.value("Terminal_ID").toString();
        QuerySearchUnitTermimal.exec(StrSql);
        if(QuerySearchUnitTermimal.next())
        {
            QSqlQuery QuerySearch(T_ProjectDatabase);
            if(Type==0)  StrSql="SELECT * FROM Equipment WHERE Equipment_ID= "+QuerySearchUnitTermimal.value("Equipment_ID").toString();
            else if(Type==1) StrSql="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QuerySearchUnitTermimal.value("TerminalStrip_ID").toString();
            QuerySearch.exec(StrSql);
            if(QuerySearch.next()) DT=QuerySearch.value("DT").toString();

            if(Type==0)   return QuerySearchUnitTermimal.value("Equipment_ID").toInt();
            else if(Type==1)   return QuerySearchUnitTermimal.value("TerminalStrip_ID").toInt();
        }
    }
    return 0;
}

//Type=0:Unit  Type=1:Terminal 根据端子ID查找元件的高层和位置
void GetUnitTermimalGaocengAndPos(int Type,int ID,QString &Gaoceng,QString &Pos)
{
    QString StrSql,DT;
    int UnitStripID=GetUnitStripIDByTermID(Type,ID,DT);
    QSqlQuery QuerySearch(T_ProjectDatabase);
    if(Type==0)  StrSql="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(UnitStripID);
    else if(Type==1) StrSql="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QString::number(UnitStripID);
    QuerySearch.exec(StrSql);
    if(QuerySearch.next())
    {
        QSqlQuery QueryProjectStructure(T_ProjectDatabase);
        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QuerySearch.value("ProjectStructure_ID").toString();//level=5
        QueryProjectStructure.exec(StrSql);
        if(QueryProjectStructure.next())
        {
            Pos=QueryProjectStructure.value("Structure_INT").toString();
            StrSql=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryProjectStructure.value("Parent_ID").toString());
            QueryProjectStructure.exec(StrSql);
            if(QueryProjectStructure.next())
            {
                Gaoceng=QueryProjectStructure.value("Structure_INT").toString();
            }
        }
    }
}

void GetPageGaocengAndPos(int PageID,QString &Gaoceng,QString &Pos)
{
    QSqlQuery QueryPage(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Page WHERE Page_ID= "+QString::number(PageID);
    QueryPage.exec(StrSql);
    if(QueryPage.next())
    {
        QSqlQuery QueryProjectStructure(T_ProjectDatabase);
        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("ProjectStructure_ID").toString();
        QueryProjectStructure.exec(StrSql);
        if(QueryProjectStructure.next())
        {
            StrSql=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryProjectStructure.value("Parent_ID").toString());
            QueryProjectStructure.exec(StrSql);
            if(QueryProjectStructure.next())
            {
                Pos=QueryProjectStructure.value("Structure_INT").toString();
                StrSql=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryProjectStructure.value("Parent_ID").toString());
                QueryProjectStructure.exec(StrSql);
                if(QueryProjectStructure.next())
                {
                    Gaoceng=QueryProjectStructure.value("Structure_INT").toString();
                }
            }
        }
    }
}
QString GetProjectStructureStrByProjectStructureID(int ProjectStructure_ID)//从Structure_ID=5开始检索
{
    QString ProjectStructureStr;
    QSqlQuery queryPos=QSqlQuery(T_ProjectDatabase);
    QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QString::number(ProjectStructure_ID));
    queryPos.exec(sqlstr);
    if(!queryPos.next()) return "";
    QSqlQuery queryPageGaoceng=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPos.value("Parent_ID").toString());
    queryPageGaoceng.exec(sqlstr);
    if(!queryPageGaoceng.next()) return "";
    ProjectStructureStr+="="+queryPageGaoceng.value("Structure_INT").toString();
    ProjectStructureStr+="+"+queryPos.value("Structure_INT").toString();
    return ProjectStructureStr;
}

//Mode=0添加units记录   Mode=1 添加page记录 Mode=2 添加Terminal记录
int InsertRecordToProjectStructure(int Mode,QString GaocengStr,QString PosStr,QString PageStr)
{
    qDebug()<<"InsertRecordToProjectStructure,Mode="<<Mode<<"GaocengStr="<<GaocengStr<<"PosStr="<<PosStr<<"PageStr="<<PageStr;
    auto nextProjectStructureId = [&]() -> int {
        return GetMaxIDOfDB(T_ProjectDatabase, "ProjectStructure", "ProjectStructure_ID");
    };

    auto insertStructureRecord = [&](int id, const QString &structureId, const QString &structureInt, int parentId) {
        QSqlQuery insertQuery(T_ProjectDatabase);
        insertQuery.prepare(QString("INSERT INTO ProjectStructure (ProjectStructure_ID,Structure_ID,Structure_INT,Parent_ID,Struct_Desc) "
                                           "VALUES (:ProjectStructure_ID,:Structure_ID,:Structure_INT,:Parent_ID,:Struct_Desc)"));
        insertQuery.bindValue(QString(":ProjectStructure_ID"), id);
        insertQuery.bindValue(QString(":Structure_ID"), structureId);
        insertQuery.bindValue(QString(":Structure_INT"), structureInt);
        insertQuery.bindValue(QString(":Parent_ID"), parentId);
        insertQuery.bindValue(QString(":Struct_Desc"), QString());
        insertQuery.exec();
    };

    auto findGaocengId = [&](const QString &name) -> int {
        if (name.isEmpty())
            return 1001;
        QSqlQuery q(T_ProjectDatabase);
        q.prepare(QString("SELECT ProjectStructure_ID FROM ProjectStructure "
                                 "WHERE Structure_ID='3' AND Structure_INT=:Structure_INT AND Parent_ID=1001"));
        q.bindValue(QString(":Structure_INT"), name);
        if (q.exec() && q.next())
            return q.value(0).toInt();
        return -1;
    };

    auto ensureGaocengId = [&](const QString &name) -> int {
        if (name.isEmpty())
            return 1001;
        int existingId = findGaocengId(name);
        if (existingId != -1)
            return existingId;
        const int newId = nextProjectStructureId();
        insertStructureRecord(newId, QString("3"), name, 1001);
        return newId;
    };

    auto findPosId = [&](int parentId, const QString &name) -> int {
        if (name.isEmpty())
            return parentId;
        QSqlQuery q(T_ProjectDatabase);
        q.prepare(QString("SELECT ProjectStructure_ID FROM ProjectStructure "
                                 "WHERE Structure_ID='5' AND Structure_INT=:Structure_INT AND Parent_ID=:Parent_ID"));
        q.bindValue(QString(":Structure_INT"), name);
        q.bindValue(QString(":Parent_ID"), parentId);
        if (q.exec() && q.next())
            return q.value(0).toInt();
        return -1;
    };

    auto ensurePosId = [&](int parentId, const QString &name) -> int {
        if (name.isEmpty())
            return parentId;
        int existingId = findPosId(parentId, name);
        if (existingId != -1)
            return existingId;
        const int newId = nextProjectStructureId();
        insertStructureRecord(newId, QString("5"), name, parentId);
        return newId;
    };

    auto findPageStructId = [&](int parentId, const QString &pageInt) -> int {
        QSqlQuery q(T_ProjectDatabase);
        q.prepare(QString("SELECT ProjectStructure_ID FROM ProjectStructure "
                                 "WHERE Structure_ID='6' AND Structure_INT=:Structure_INT AND Parent_ID=:Parent_ID"));
        q.bindValue(QString(":Structure_INT"), pageInt);
        q.bindValue(QString(":Parent_ID"), parentId);
        if (q.exec() && q.next())
            return q.value(0).toInt();
        return -1;
    };

    auto createPageStructId = [&](int parentId, const QString &pageInt) -> int {
        const int newId = nextProjectStructureId();
        insertStructureRecord(newId, QString("6"), pageInt, parentId);
        return newId;
    };

    if (Mode == 0) {
        const int gaocengId = ensureGaocengId(GaocengStr);
        const int posId = ensurePosId(gaocengId, PosStr);
        return posId;
    }

    if (Mode == 2) {
        const int gaocengId = ensureGaocengId(GaocengStr);
        const int posId = ensurePosId(gaocengId, PosStr);
        return posId;
    }

    // Mode == 1
    const int gaocengId = ensureGaocengId(GaocengStr);
    const int posId = ensurePosId(gaocengId, PosStr);
    int pageStructId = findPageStructId(posId, PageStr);
    if (pageStructId != -1)
        return pageStructId;
    pageStructId = createPageStructId(posId, PageStr);
    return pageStructId;
}
bool MyInsertBlock(QAxWidget *mAxwidget,QString BlkPath,QString BlkName)//通过dwg文件导入块
{
    qDebug()<<"MyInsertBlock,BlkPath="<<BlkPath;
    IMxDrawResbuf *resp =(IMxDrawResbuf *) mAxwidget->querySubObject("NewResbuf()");
    QFileInfo file(BlkPath);
    if(!file.exists()) return false;

    resp->AddString(BlkPath);
    resp->AddString(BlkName);
    resp->AddLong(0);
    resp->AddString("");
    resp->AddLong(1);//重新更新该图块
    bool Ret=(bool)mAxwidget->querySubObject("CallEx(const QString&,QVariant)","Mx_InsertBlockEx",resp->asVariant());
    if(!Ret) return false;
    return true;
    /*
    double xmin,xmax,ymin,ymax;
    MxDrawPoint* origin_tmp=new MxDrawPoint();
    IMxDrawPoint* origin = (IMxDrawPoint*)origin_tmp;
    //得到块的中心点作为基点
    IMxDrawDatabase* database = (IMxDrawDatabase*)mAxwidget->querySubObject("GetDatabase()");
    IMxDrawBlockTable* blkTable = (IMxDrawBlockTable*)database->querySubObject("GetBlockTable()");
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* ) blkTable->querySubObject("GetAt(QString,bool)",BlkName ,true);
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    // 循环得到所有实体
    bool FirstGet=true;
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition") continue;
        if(EntyIsErased(mAxwidget,ent)) continue;//去除erase的实体
        if(!ent->dynamicCall("Visible()").toBool()) continue;
        IMxDrawPoints* pts=(IMxDrawPoints*)ent->querySubObject("GetBoundingBox2()");
        for(int j=0;j<pts->Count();j++)
        {
            IMxDrawPoint* pt = (IMxDrawPoint*)pts->querySubObject("Item(const qint64&)",j);
            if(FirstGet)
            {
                xmin= pt->x();xmax= pt->x();
                ymin= pt->y();ymax= pt->y();
                FirstGet=false;
            }
            else
            {
                xmin=xmin<pt->x()?xmin:pt->x();
                xmax=xmax>pt->x()?xmax:pt->x();
                ymin=ymin<pt->y()?ymin:pt->y();
                ymax=ymax>pt->y()?ymax:pt->y();
            }
        }
    }
    if(BlkName.contains("SYMB2_M_PWF_CO1"))
    {
        origin->setX(xmin);
        origin->setY(ymax);
    }
    else if(BlkName.contains("SYMB2_M_PWF_CO2"))
    {
        origin->setX(xmax);
        origin->setY(ymax);
    }
    else if(BlkName.contains("SYMB2_M_PWF_CO3"))
    {
        origin->setX(xmin);
        origin->setY(ymin);
    }
    else if(BlkName.contains("SYMB2_M_PWF_CO4"))
    {
        origin->setX(xmax);
        origin->setY(ymin);
    }
    else
    {
        origin->setX((xmin+xmax)/2);
        origin->setY((ymin+ymax)/2);
    }
    blkRec->dynamicCall("SetOrigin(QVariant)",origin->asVariant());
*/
}
QString GetDwgDicData(QString DwgPath,QString BlkName,QString ParaName)
{
    GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",DwgPath);
    IMxDrawResbuf *resp=readGlobalVar(GlobalBackAxWidget,"LD_SYMB1LIB_DICITIONARY","LD_SYMB1LIB_XRECORD");
    if(resp==nullptr) return "";
    for(int i=0;i<resp->Count();i++)
    {
        if(resp->AtString(i)==ParaName) return resp->AtString(i+1);
    }
}

QStringList GetBlockTermData(QAxWidget *mAxwidget,QString BlkName,int TermIndex)
{
    //qDebug()<<"GetBlockTermData,BlkName="<<BlkName<<",TermIndex="<<TermIndex;
    QStringList RetStrList;
    QList<IMxDrawPolyline*> listTerms=GetTermEnty(mAxwidget,BlkName);
    for(int i=0;i<listTerms.count();i++)
    {
        //qDebug()<<"i="<<i;
        QString LD_SYMB1LIB_TERMPOINT=listTerms.at(i)->dynamicCall("GetxDataString2(QString,int)","LD_SYMB1LIB_TERMPOINT",0).toString();
        if(LD_SYMB1LIB_TERMPOINT==QString::number(TermIndex))
        {
            RetStrList.append(listTerms.at(i)->dynamicCall("GetxDataString2(QString,int)","LD_PARTLIB_DOTCONDIRECT",0).toString());
            listTerms.at(i)->dynamicCall("GetxDataString2(QString,int)","LD_SYMB_CZTERM",0).toString();
            if(mAxwidget->dynamicCall("IsOk()").toString()=="true")//若存在LD_SYMB_CZTERM关键字则为不接线端
                RetStrList.append("是");
            else RetStrList.append("否");
        }
    }
    return RetStrList;
}
//返回的QStringList.at(0)为方向  QStringList.at(1)为是否为内部端
QStringList GetDwgTermData(QString DwgPath,QString BlkName,int TermIndex)
{
    //qDebug()<<"GetDwgTermData";
    QStringList RetList;
    if(!MyInsertBlock(GlobalBackAxWidget,DwgPath,BlkName)) return RetList;
    qlonglong lBlockID=GlobalBackAxWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",0,0,BlkName,1.0,0).toLongLong();
    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    if(blkEnty==nullptr) return RetList;
    return GetBlockTermData(GlobalBackAxWidget,blkEnty->dynamicCall("GetBlockName()").toString(),TermIndex);
}

int GetDwgTermCount(QString DwgPath,QString BlkName)
{
    if(!MyInsertBlock(GlobalBackAxWidget,DwgPath,BlkName)) return 0;
    qlonglong lBlockID=GlobalBackAxWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",0,0,BlkName,1.0,0).toLongLong();
    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    if(blkEnty==nullptr) return 0;
    return GetTermEnty(GlobalBackAxWidget,blkEnty->dynamicCall("GetBlockName()").toString()).count();
}

void LoadCbSymbolPattern(QString SymbolName,QComboBox *CbSymbolPattern)
{
    //检索当前符号有几种样式，目前是哪种样式
    //去掉-1，。。进行检索
    CbSymbolPattern->clear();
    QString SearchSymbol=SymbolName;
    int Index=SearchSymbol.lastIndexOf("-");
    if(Index>=0) SearchSymbol=SearchSymbol.mid(0,Index+1);
    QString SearchFilePath;
    if(SearchSymbol.contains("SPS_")) SearchFilePath="C:/TBD/SPS/";
    else SearchFilePath="C:/TBD/SYMB2LIB/";

    QStringList filters;
    filters<<QString(SearchSymbol+"*.dwg");

    //定义迭代器并设置过滤器
    QDirIterator dir_iterator(SearchFilePath, filters,QDir::Files | QDir::NoSymLinks);
    while(dir_iterator.hasNext())
    {
        dir_iterator.next();
        QFileInfo file_info = dir_iterator.fileInfo();
        int index1=file_info.fileName().lastIndexOf("-");
        int index2=file_info.fileName().lastIndexOf(".dwg");
        if(index1>=0)
            CbSymbolPattern->addItem("样式"+file_info.fileName().mid(index1+1,index2-index1-1));
        else
            CbSymbolPattern->addItem("样式1");
    }
    if(Index>=0) CbSymbolPattern->setCurrentText("样式"+SymbolName.mid(Index+1,SearchSymbol.count()-Index-1));
    else CbSymbolPattern->setCurrentText("样式1");
}

void UpdateDBSymbolInfoByBlkEnty(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *BlkModifyed,QString Page_ID,QString Equipment_ID)
{
    QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="UPDATE Symbol SET Page_ID=:Page_ID,Equipment_ID=:Equipment_ID,Symbol=:Symbol,Symbol_Category=:Symbol_Category,DT_Handle=:DT_Handle,Designation=:Designation,"
                   "Symbol_Handle=:Symbol_Handle,Symbol_Remark=:Symbol_Remark,FunDefine=:FunDefine,Box_Handle=:Box_Handle,InsertionPoint=:InsertionPoint,StructBox_ID=:StructBox_ID "
                   "WHERE Symbol_ID = "+BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
    qDebug()<<SqlStr;
    QuerySymbol.prepare(SqlStr);
    QuerySymbol.bindValue(":Page_ID",Page_ID);
    QuerySymbol.bindValue(":Equipment_ID",Equipment_ID);
    QString Symbol=BlkModifyed->dynamicCall("GetBlockName()").toString();
    QuerySymbol.bindValue(":Symbol",Symbol);
    QString Symbol_Category=BlkModifyed->dynamicCall("GetxDataString2(QString,int)","Symbol_Category",0).toString();
    QString FunDefine=BlkModifyed->dynamicCall("GetxDataString2(QString,int)","FunDefine",0).toString();
    QuerySymbol.bindValue(":Symbol_Category",Symbol_Category);
    QuerySymbol.bindValue(":DT_Handle",BlkModifyed->dynamicCall("GetxDataString2(QString,0)","LD_GROUPCPXRECT_TEXT",0).toString());
    QuerySymbol.bindValue(":Designation",BlkModifyed->dynamicCall("GetxDataString2(QString,0)","Designation",0).toString());
    QuerySymbol.bindValue(":Symbol_Handle",BlkModifyed->dynamicCall("handle()").toString());

    QString Symbol_Remark;
    IMxDrawResbuf *resp=(IMxDrawResbuf *)BlkModifyed->querySubObject("GetXData(QString)","LD_SYMB1LIB_XRECORD");
    if(resp!=nullptr)
    {
        for(int j=0;j<resp->Count();j++)
        {
            if(resp->AtString(j)=="推荐名称") {Symbol_Remark=resp->AtString(j+1);break;}
        }
    }
    QuerySymbol.bindValue(":Symbol_Remark",Symbol_Remark);
    QuerySymbol.bindValue(":FunDefine",FunDefine);
    QuerySymbol.bindValue(":Box_Handle","");
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)BlkModifyed->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)BlkModifyed->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QuerySymbol.bindValue(":InsertionPoint",InsertionPoint);
    QuerySymbol.bindValue(":StructBox_ID","");
    QuerySymbol.exec();
    //更新TermInfo
    //根据Symbol dwg文件确定连接点数量
    int TermCount=GetTermEnty(tmp_MxDrawWidget,BlkModifyed->dynamicCall("GetBlockName()").toString()).count();
    for(int i=0;i<TermCount;i++)
    {
        //更新T_ProjectDatabase数据库的Symb2TermInfo表
        QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr="UPDATE Symb2TermInfo SET ConnNum=:ConnNum,Conn_Coordinate=:Conn_Coordinate,ConnDirection=:ConnDirection,ConnDesc=:ConnDesc "
               "WHERE Symbol_ID = '"+BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString()+"' AND ConnNum_Logic = '"+QString::number(i+1)+"'";

        QuerySymb2TermInfo.prepare(SqlStr);
        QuerySymb2TermInfo.bindValue(":ConnNum",GetBlockAttrTextString(BlkModifyed,QString::number(i+1)));
        InsertionPoint=QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,BlkModifyed,QString::number(i+1))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,BlkModifyed,QString::number(i+1))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QuerySymb2TermInfo.bindValue(":Conn_Coordinate",InsertionPoint);

        //根据dwg文件确定连接点连线方向
        QStringList listTermInfo=GetBlockTermData(tmp_MxDrawWidget,BlkModifyed->dynamicCall("GetBlockName()").toString(),i+1);//GetDwgTermData(BlkPath,i+1);
        if(listTermInfo.count()==2)
        {
            QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
        }
        else
        {
            QuerySymb2TermInfo.bindValue(":ConnDirection","");
        }
        QuerySymb2TermInfo.bindValue(":ConnDesc",GetBlockAttrTextString(BlkModifyed,"符号的连接点描述["+QString::number(i+1)+"]"));
        QuerySymb2TermInfo.exec();
    }
}

int InsertDBSymbolInfoByBlkEnty(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *blkEnty,QString Page_ID,QString Equipment_ID)
{
    int Symbol_ID=0;
    QString DbId=blkEnty->dynamicCall("GetxDataString2(QString,0)","DbId",0).toString();
    if(tmp_MxDrawWidget->dynamicCall("IsOk()").toString()=="true")
    {
        //查看DbId是否在数据库中已存在
        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString StrSql="SELECT * FROM Symbol WHERE Symbol_ID = "+DbId;
        QuerySearch.exec(StrSql);
        if(!QuerySearch.next()) Symbol_ID=DbId.toInt();
    }
    if(Symbol_ID==0) Symbol_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");

    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString tempSQL = QString("INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol,Symbol_Category,Symbol_Desc,Symbol_Remark,Designation,Symbol_Handle,FunDefine,InsertionPoint,InterConnect)"
                              " VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol,:Symbol_Category,:Symbol_Desc,:Symbol_Remark,:Designation,:Symbol_Handle,:FunDefine,:InsertionPoint,:InterConnect)");
    QuerySymbol.prepare(tempSQL);
    QuerySymbol.bindValue(":Symbol_ID",Symbol_ID);
    QuerySymbol.bindValue(":Page_ID",Page_ID);
    QuerySymbol.bindValue(":Equipment_ID",Equipment_ID);
    QString Symbol=blkEnty->dynamicCall("GetBlockName()").toString();
    QuerySymbol.bindValue(":Symbol",Symbol);
    QuerySymbol.bindValue(":Symbol_Category",blkEnty->dynamicCall("GetxDataString2(QString,int)","Symbol_Category",0).toString());
    QuerySymbol.bindValue(":Symbol_Desc",blkEnty->dynamicCall("GetxDataString2(QString,int)","Symbol_Desc",0).toString());
    QuerySymbol.bindValue(":Symbol_Remark",blkEnty->dynamicCall("GetxDataString2(QString,int)","Symbol_Remark",0).toString());
    QuerySymbol.bindValue(":Designation",blkEnty->dynamicCall("GetxDataString2(QString,int)","Designation",0).toString());
    QuerySymbol.bindValue(":Symbol_Handle",blkEnty->dynamicCall("handle()").toString());
    QuerySymbol.bindValue(":FunDefine",blkEnty->dynamicCall("GetxDataString2(QString,int)","FunDefine",0).toString());
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QuerySymbol.bindValue(":InsertionPoint",InsertionPoint);
    QuerySymbol.bindValue(":InterConnect",blkEnty->dynamicCall("GetxDataString2(QString,int)","InterConnect",0).toString());
    QuerySymbol.exec();
    //将DbId写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(Symbol_ID));

    //根据Symbol dwg文件确定连接点数量
    int TermCount=GetTermEnty(tmp_MxDrawWidget,blkEnty->dynamicCall("GetBlockName()").toString()).count();
    qDebug()<<"TermCount="<<TermCount;
    //拆分ConnNumInEquipmentTemplate
    for(int i=0;i<TermCount;i++)
    {
        //更新Symb2TermInfo表
        //找到当前最大的Symb2TermInfo_ID
        int Symb2TermInfo_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symb2TermInfo","Symb2TermInfo_ID");
        //更新T_ProjectDatabase数据库的Symb2TermInfo表
        QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        tempSQL = QString("INSERT INTO Symb2TermInfo (Symb2TermInfo_ID,Symbol_ID,ConnNum_Logic,ConnNum,Conn_Coordinate,ConnDirection,Internal,ConnDesc,TestCost)"
                          "VALUES (:Symb2TermInfo_ID,:Symbol_ID,:ConnNum_Logic,:ConnNum,:Conn_Coordinate,:ConnDirection,:Internal,:ConnDesc,:TestCost)");
        QuerySymb2TermInfo.prepare(tempSQL);
        QuerySymb2TermInfo.bindValue(":Symb2TermInfo_ID",Symb2TermInfo_ID);
        QuerySymb2TermInfo.bindValue(":Symbol_ID",QString::number(Symbol_ID));
        QuerySymb2TermInfo.bindValue(":ConnNum_Logic",QString::number(i+1));
        QuerySymb2TermInfo.bindValue(":ConnNum",GetBlockAttrTextString(blkEnty,QString::number(i+1)));
        InsertionPoint=QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,blkEnty,QString::number(i+1))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,blkEnty,QString::number(i+1))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QuerySymb2TermInfo.bindValue(":Conn_Coordinate",InsertionPoint);

        //根据dwg文件确定连接点连线方向
        QStringList listTermInfo=GetBlockTermData(tmp_MxDrawWidget,blkEnty->dynamicCall("GetBlockName()").toString(),i+1);//GetDwgTermData(BlkPath,i+1);
        if(listTermInfo.count()==2)
        {
            QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
            if(listTermInfo.at(1)=="是")
                QuerySymb2TermInfo.bindValue(":Internal",1);
            else QuerySymb2TermInfo.bindValue(":Internal",0);
        }
        else
        {
            QuerySymb2TermInfo.bindValue(":ConnDirection","");
            QuerySymb2TermInfo.bindValue(":Internal",0);
        }
        QuerySymb2TermInfo.bindValue(":ConnDesc",GetBlockAttrTextString(blkEnty,"符号的连接点描述["+QString::number(i+1)+"]"));
        QuerySymb2TermInfo.bindValue(":TestCost",blkEnty->dynamicCall("GetxDataString2(QString,int)","TestCost",0).toString().split(",").at(i));
        QuerySymb2TermInfo.exec();
    }
    return Symbol_ID;
}

int UpdateTerminalInfoBySymb2Lib_ID(QString Symb2Lib_ID,QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *blkEnty,QString Page_ID,QString MaxTerminalStrip_ID,QString Designation)
{
    //更新T_ProjectDatabase数据库的Symbol表
    //找到当前最大的Symbol_ID
    int Terminal_ID=GetMaxIDOfDB(T_ProjectDatabase,"Terminal","Terminal_ID");

    QSqlQuery QuerySymb2Lib = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString tempSQL = "SELECT * FROM Symb2Lib WHERE Symb2Lib_ID = '"+Symb2Lib_ID+"'";
    QuerySymb2Lib.exec(tempSQL);
    QuerySymb2Lib.next();

    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型

    tempSQL = QString("INSERT INTO Terminal (Terminal_ID,TerminalStrip_ID,Page_ID,Designation,Symbol,Handle,Coordinate,Terminalfunction,TerminalType,TerminalName,PartCode,FunctionText,FunDefine,Factory,OrderNum) "
                      "VALUES (:Terminal_ID,:TerminalStrip_ID,:Page_ID,:Designation,:Symbol,:Handle,:Coordinate,:Terminalfunction,:TerminalType,:TerminalName,:PartCode,:FunctionText,:FunDefine,:Factory,:OrderNum)");
    QueryVar.prepare(tempSQL);
    QueryVar.bindValue(":Terminal_ID",Terminal_ID);
    QueryVar.bindValue(":TerminalStrip_ID",MaxTerminalStrip_ID);
    QueryVar.bindValue(":Page_ID",Page_ID);
    QueryVar.bindValue(":Designation",Designation);
    QString Symbol=blkEnty->dynamicCall("GetBlockName()").toString();
    QueryVar.bindValue(":Symbol",Symbol);
    QueryVar.bindValue(":Handle",blkEnty->dynamicCall("handle()").toString());
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QueryVar.bindValue(":Coordinate",InsertionPoint);
    QueryVar.bindValue(":Terminalfunction","");
    QueryVar.bindValue(":TerminalType","");
    QueryVar.bindValue(":TerminalName","");
    QueryVar.bindValue(":PartCode","");
    QueryVar.bindValue(":FunctionText","");
    if(Symb2Lib_ID!="端子") QueryVar.bindValue(":FunDefine",GetFunctionDefineNameBySymb2Lib_ID(Symb2Lib_ID));
    else QueryVar.bindValue(":FunDefine","端子");
    QueryVar.bindValue(":Factory","");
    QueryVar.bindValue(":OrderNum","");
    QueryVar.exec();
    //将DbId写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(Terminal_ID));
    //将FunDefine写入到blkEnty的拓展数据中
    if(Symb2Lib_ID!="端子")blkEnty->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,GetFunctionDefineNameBySymb2Lib_ID(Symb2Lib_ID));
    else blkEnty->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,"端子");
    //根据Symbol dwg文件确定连接点数量
    int TermCount=GetTermEnty(tmp_MxDrawWidget,blkEnty->dynamicCall("GetBlockName()").toString()).count();
    qDebug()<<"TermCount="<<TermCount;
    for(int i=0;i<TermCount;i++)
    {
        int MaxTerminalTerm_ID=GetMaxIDOfDB(T_ProjectDatabase,"TerminalTerm","TerminalTerm_ID");
        tempSQL = QString("INSERT INTO TerminalTerm (TerminalTerm_ID,Terminal_ID,ConnNum_Logic,ConnNum,Conn_Coordinate) "
                          "VALUES (:TerminalTerm_ID,:Terminal_ID,:ConnNum_Logic,:ConnNum,:Conn_Coordinate)");
        QueryVar.prepare(tempSQL);
        QueryVar.bindValue(":TerminalTerm_ID",MaxTerminalTerm_ID);
        QueryVar.bindValue(":Terminal_ID",QString::number(Terminal_ID));
        QueryVar.bindValue(":ConnNum_Logic",QString::number(i+1));
        QueryVar.bindValue(":ConnNum",QString::number(i+1));
        InsertionPoint=QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,blkEnty,QString::number(i+1))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,blkEnty,QString::number(i+1))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        qDebug()<<":Conn_Coordinate="<<InsertionPoint;
        QueryVar.bindValue(":Conn_Coordinate",InsertionPoint);
        QueryVar.exec();
    }
    return Terminal_ID;
}

int UpdateSymbolInfoBySymb2Lib_ID(QString Symb2Lib_ID,QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference *blkEnty,QString Page_ID,QString MaxEquipment_ID,QString Designation)
{
    qDebug()<<"UpdateSymbolInfoBySymb2Lib_ID,Symb2Lib_ID="<<Symb2Lib_ID<<",MaxEquipment_ID="<<MaxEquipment_ID;
    //更新T_ProjectDatabase数据库的Symbol表
    //找到当前最大的Symbol_ID
    int Symbol_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");

    QSqlQuery QuerySymb2Lib = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString tempSQL = "SELECT * FROM Symb2Lib WHERE Symb2Lib_ID = '"+Symb2Lib_ID+"'";
    QuerySymb2Lib.exec(tempSQL);
    QuerySymb2Lib.next();

    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    tempSQL = QString("INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol,Symbol_Category,Symbol_Desc,Designation,Symbol_Handle,Symbol_Remark,FunDefine,InsertionPoint,InterConnect)"
                      " VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol,:Symbol_Category,:Symbol_Desc,:Designation,:Symbol_Handle,:Symbol_Remark,:FunDefine,:InsertionPoint,:InterConnect)");
    QuerySymbol.prepare(tempSQL);
    QuerySymbol.bindValue(":Symbol_ID",Symbol_ID);
    QuerySymbol.bindValue(":Page_ID",Page_ID);
    QuerySymbol.bindValue(":Equipment_ID",MaxEquipment_ID);
    QString Symbol=blkEnty->dynamicCall("GetBlockName()").toString();
    QuerySymbol.bindValue(":Symbol",Symbol);
    //查找FunctionDefineClass中的ParentNo确定Symbol_Category
    QString Symbol_Category;//=blkEnty->dynamicCall("GetxDataString2(QString,int)","Symbol_Category",0).toString();
    QString FunDefine;//=blkEnty->dynamicCall("GetxDataString2(QString,int)","FunDefine",0).toString();

    QSqlQuery QuerySymb2Class = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    tempSQL = "SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QuerySymb2Lib.value("Symb2Class_ID").toString()+"'";
    QuerySymb2Class.exec(tempSQL);
    if(QuerySymb2Class.next())
    {
        tempSQL = "SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QuerySymb2Class.value("Parent_ID").toString()+"'";
        QuerySymb2Class.exec(tempSQL);
        if(QuerySymb2Class.next())
        {
            QSqlQuery QueryFunctionDefineClass = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            tempSQL = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+QuerySymb2Class.value("FuncDefID").toString()+"'";
            QueryFunctionDefineClass.exec(tempSQL);
            if(QueryFunctionDefineClass.next())
            {
                FunDefine=QueryFunctionDefineClass.value("FunctionDefineName").toString();
            }

            tempSQL = "SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QuerySymb2Class.value("Parent_ID").toString()+"'";
            QuerySymb2Class.exec(tempSQL);
            if(QuerySymb2Class.next())
            {
                Symbol_Category=QuerySymb2Class.value("Desc").toString();
            }
        }
    }
    QuerySymbol.bindValue(":Symbol_Category",Symbol_Category);
    QuerySymbol.bindValue(":Symbol_Desc","");
    QuerySymbol.bindValue(":Designation",Designation);
    QuerySymbol.bindValue(":Symbol_Handle",blkEnty->dynamicCall("handle()").toString());

    QString Symbol_Remark;
    IMxDrawResbuf *resp=(IMxDrawResbuf *)blkEnty->querySubObject("GetXData(QString)","LD_SYMB1LIB_XRECORD");
    if(resp!=nullptr)
    {
        for(int j=0;j<resp->Count();j++)
        {
            if(resp->AtString(j)=="推荐名称") {Symbol_Remark=resp->AtString(j+1);break;}
        }
    }
    QuerySymbol.bindValue(":Symbol_Remark",Symbol_Remark);
    QuerySymbol.bindValue(":FunDefine",FunDefine);
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QuerySymbol.bindValue(":InsertionPoint",InsertionPoint);
    QuerySymbol.bindValue(":InterConnect","");
    QuerySymbol.exec();
    //将DbId写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(Symbol_ID));
    //将FunDefine写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,FunDefine);
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Category",0,Symbol_Category);
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Remark",0,Symbol_Remark);

    //根据Symbol dwg文件确定连接点数量
    int TermCount=GetTermEnty(tmp_MxDrawWidget,blkEnty->dynamicCall("GetBlockName()").toString()).count();
    qDebug()<<"TermCount="<<TermCount;
    //拆分ConnNumInEquipmentTemplate
    for(int i=0;i<TermCount;i++)
    {
        //更新Symb2TermInfo表
        //找到当前最大的Symb2TermInfo_ID
        int Symb2TermInfo_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symb2TermInfo","Symb2TermInfo_ID");
        //更新T_ProjectDatabase数据库的Symb2TermInfo表
        QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        tempSQL = QString("INSERT INTO Symb2TermInfo (Symb2TermInfo_ID,Symbol_ID,ConnNum_Logic,ConnNum,Conn_Coordinate,ConnDirection,Internal,ConnDesc,TestCost)"
                          "VALUES (:Symb2TermInfo_ID,:Symbol_ID,:ConnNum_Logic,:ConnNum,:Conn_Coordinate,:ConnDirection,:Internal,:ConnDesc,:TestCost)");
        QuerySymb2TermInfo.prepare(tempSQL);
        QuerySymb2TermInfo.bindValue(":Symb2TermInfo_ID",Symb2TermInfo_ID);
        QuerySymb2TermInfo.bindValue(":Symbol_ID",QString::number(Symbol_ID));
        QuerySymb2TermInfo.bindValue(":ConnNum_Logic",QString::number(i+1));
        QuerySymb2TermInfo.bindValue(":ConnNum",QString::number(i+1));
        InsertionPoint=QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,blkEnty,QString::number(i+1))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(tmp_MxDrawWidget,blkEnty,QString::number(i+1))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QuerySymb2TermInfo.bindValue(":Conn_Coordinate",InsertionPoint);

        //根据dwg文件确定连接点连线方向
        QStringList listTermInfo=GetBlockTermData(tmp_MxDrawWidget,blkEnty->dynamicCall("GetBlockName()").toString(),i+1);//GetDwgTermData(BlkPath,i+1);
        if(listTermInfo.count()==2)
        {
            QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
            if(listTermInfo.at(1)=="是")
                QuerySymb2TermInfo.bindValue(":Internal",1);
            else QuerySymb2TermInfo.bindValue(":Internal",0);
        }
        else
        {
            QuerySymb2TermInfo.bindValue(":ConnDirection","");
            QuerySymb2TermInfo.bindValue(":Internal",0);
        }
        QuerySymb2TermInfo.bindValue(":ConnDesc","");
        QuerySymb2TermInfo.bindValue(":TestCost","");
        QuerySymb2TermInfo.exec();
    }
    return Symbol_ID;
}

//ListSymbolSpurInfo:SourceConn,SourcePrior,ExecConn,TestCost,InterConnect
int AddSymbTblAndSymb2TermInfoTbl(QString LibEquipment_ID,QString MaxEquipment_ID,QString EquipmentTemplate_ID,QStringList ListSymbolSpurInfo)//dataFunc 从器件库中加载数据到工程库
{
    qDebug()<<"AddSymbTblAndSymb2TermInfoTbl";
    //更新T_ProjectDatabase数据库的Symbol表
    QSqlQuery QueryEquipmentTemplate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString tempSQL;
    if(EquipmentTemplate_ID!="")
        tempSQL = QString("SELECT * FROM EquipmentTemplate WHERE EquipmentTemplate_ID = "+EquipmentTemplate_ID);
    else
        tempSQL = QString("SELECT * FROM EquipmentTemplate WHERE Equipment_ID = '"+LibEquipment_ID+"'");
    QueryEquipmentTemplate.exec(tempSQL);
    int Symbol_ID=-1;
    QStringList ListInterConnectInfo;
    QStringList ListHisSymbolID;
    while(QueryEquipmentTemplate.next())
    {
        QString connNumStr = QueryEquipmentTemplate.value("ConnNum").toString();
        QString connDescStr = QueryEquipmentTemplate.value("ConnDesc").toString();
        QString spurTestCost =QueryEquipmentTemplate.value("TestCost").toString();

        //找到当前最大的Symbol_ID
        bool FindFunctionDefineClass=false;
        Symbol_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");
        ListHisSymbolID.append(QString::number(Symbol_ID)+","+QueryEquipmentTemplate.value("EquipmentTemplate_ID").toString()+","+QueryEquipmentTemplate.value("InterConnect").toString());
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QSqlQuery QueryFunctionDefineClass = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        tempSQL = QString("SELECT * FROM FunctionDefineClass WHERE FunctionDefineCode = '"+QueryEquipmentTemplate.value("FunDefine").toString()+"'");
        QueryFunctionDefineClass.exec(tempSQL);
        if(QueryFunctionDefineClass.next()) FindFunctionDefineClass=true;

        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        tempSQL = QString("INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol,Symbol_Category,Symbol_Desc,Show_DT,Designation,Symbol_Handle,Symbol_Remark,FunDefine,FuncType,SourceConn,ExecConn,SourcePrior,InterConnect)"
                          " VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol,:Symbol_Category,:Symbol_Desc,:Show_DT,:Designation,:Symbol_Handle,:Symbol_Remark,:FunDefine,:FuncType,:SourceConn,:ExecConn,:SourcePrior,:InterConnect)");
        QuerySymbol.prepare(tempSQL);
        QuerySymbol.bindValue(":Symbol_ID",Symbol_ID);
        QuerySymbol.bindValue(":Page_ID","");
        QuerySymbol.bindValue(":Equipment_ID",MaxEquipment_ID);
        QString Symbol="";
        if(QueryEquipmentTemplate.value("Symbol").toString()=="")
        {
            if(FindFunctionDefineClass)  Symbol=QueryFunctionDefineClass.value("DefaultSymbol").toString();
        }
        else
            Symbol=QueryEquipmentTemplate.value("Symbol").toString();
        QuerySymbol.bindValue(":Symbol",Symbol);
        if(FindFunctionDefineClass)
        {
            //查找FunctionDefineClass中的ParentNo确定Symbol_Category
            QSqlQuery QuerySymbol_Category = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            tempSQL = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+QueryFunctionDefineClass.value("ParentNo").toString()+"'";
            QuerySymbol_Category.exec(tempSQL);
            if(QuerySymbol_Category.next())
            {
                tempSQL = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+QuerySymbol_Category.value("ParentNo").toString()+"'";
                QuerySymbol_Category.exec(tempSQL);
                if(QuerySymbol_Category.next()) QuerySymbol.bindValue(":Symbol_Category",QuerySymbol_Category.value("FunctionDefineName").toString());
            }
        }
        else QuerySymbol.bindValue(":Symbol_Category","虚拟端口");

        QString strSymbolDesc = QueryEquipmentTemplate.value("Desc").toString();
        if(strSymbolDesc.isEmpty())strSymbolDesc = QueryEquipmentTemplate.value("ConnDesc").toString();

        QString spurDT = QueryEquipmentTemplate.value("SpurDT").toString();
        if(spurDT=="") spurDT=connNumStr;//如果子图代号为空，则直接采用端号

        QuerySymbol.bindValue(":Symbol_Desc",strSymbolDesc);
        QuerySymbol.bindValue(":Show_DT",spurDT);
        QuerySymbol.bindValue(":Designation",QueryEquipmentTemplate.value("Designation").toString());
        QuerySymbol.bindValue(":Symbol_Handle","");
        QString Symbol_Remark;
        QString DwgPath;
        if(Symbol.contains("SPS_")) DwgPath="C:/TBD/SPS/"+Symbol+".dwg";
        else if(Symbol.contains("ES2_")) DwgPath="C:/TBD/SYMB2LIB/"+Symbol+".dwg";
        qDebug()<<"Symbol="<<Symbol;
        QuerySymbol.bindValue(":Symbol_Remark",GetDwgDicData(DwgPath,Symbol,"推荐名称"));
        qDebug()<<"Symbol_Remark="<<Symbol_Remark;
        if(FindFunctionDefineClass) QuerySymbol.bindValue(":FunDefine",QueryFunctionDefineClass.value("FunctionDefineName").toString());
        else QuerySymbol.bindValue(":FunDefine",QueryEquipmentTemplate.value("FunDefine").toString());
        QuerySymbol.bindValue(":FuncType",QueryEquipmentTemplate.value("FuncType").toString());
        QuerySymbol.bindValue(":SourceConn",QueryEquipmentTemplate.value("SourceConn").toBool());
        QuerySymbol.bindValue(":ExecConn",QueryEquipmentTemplate.value("ExecConn").toBool());
        QuerySymbol.bindValue(":SourcePrior",QueryEquipmentTemplate.value("SourcePrior").toString());
        QuerySymbol.bindValue(":InterConnect","");

        QuerySymbol.exec();

        //==========加载端口==========
        QStringList listConnNum = connNumStr.simplified().split("￤");
        QStringList connDescList = connDescStr.trimmed().split('\n');

        //根据Symbol dwg文件确定连接点数量
        int TermCount=GetDwgTermCount(DwgPath,Symbol);
        qDebug()<<"TermCount="<<TermCount;

        //拆分ConnNumInEquipmentTemplate
        bool isEquaDWGPortAndConnNum= true;
        if(listConnNum.count()!=TermCount){
            isEquaDWGPortAndConnNum =false;
            qDebug()<<"Error: listConnNum.count()!=TermCount";
        }

        for(int i=0;i<listConnNum.count();i++)
        {
            //qDebug()<<"Curi="<<i;
            //更新Symb2TermInfo表
            //找到当前最大的Symb2TermInfo_ID 自增主键，可以不定义
            //qDebug()<<"Symb2TermInfo_ID="<<Symb2TermInfo_ID;
            //更新T_ProjectDatabase数据库的Symb2TermInfo表
            QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            tempSQL = QString("INSERT INTO Symb2TermInfo (Symbol_ID,ConnNum_Logic,ConnNum,ConnDirection,Internal,ConnDesc,TestCost,TermPicPath,TagType,TagPos,TagEdge,TagColor)"
                              "VALUES (:Symbol_ID,:ConnNum_Logic,:ConnNum,:ConnDirection,:Internal,:ConnDesc,:TestCost,:TermPicPath,:TagType,:TagPos,:TagEdge,:TagColor)");
            QuerySymb2TermInfo.prepare(tempSQL);
            QuerySymb2TermInfo.bindValue(":Symbol_ID",QString::number(Symbol_ID));
            QuerySymb2TermInfo.bindValue(":ConnNum_Logic",QString::number(i+1));

            QString connNum = listConnNum[i].simplified();
            QString connDesc = "";
            if (connDescList.size() == listConnNum.size()) {
                // 如果connDescList与connNumList包含相同的字符串，则connDesc在connDescList中取与connNum序号相同
                connDesc = connDescList[i].simplified();
            } else {
                connDesc = connDescStr.simplified(); // 如果有换行符，也要去掉
            }
            QuerySymb2TermInfo.bindValue(":ConnNum",listConnNum.at(i));
            QuerySymb2TermInfo.bindValue(":ConnDesc",connDesc);

            //根据dwg文件确定连接点连线方向
            int mInternal = 0;
            QString mConnDirection;
            if(isEquaDWGPortAndConnNum){
                QStringList listTermInfo=GetDwgTermData(DwgPath,Symbol,i+1);
                //qDebug()<<"listTermInfo="<<listTermInfo;
                if(listTermInfo.count()==2)
                {
                    mConnDirection = listTermInfo.at(0);
                    if(listTermInfo.at(1)=="是")mInternal=1;
                    else mInternal=0;
                }
                else qDebug()<<"Error: listTermInfo.count()!=2";//数据不对的情况
            }
            QuerySymb2TermInfo.bindValue(":ConnDirection",mConnDirection);
            QuerySymb2TermInfo.bindValue(":Internal",mInternal);

            QSqlQuery QueryTermInfo = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempSQL = "SELECT * FROM TermInfo WHERE Equipment_ID = "+LibEquipment_ID + " AND EquipmentTemplate_ID = "+QueryEquipmentTemplate.value("EquipmentTemplate_ID").toString()+" AND TermNum = '"+listConnNum.at(i)+"'";
            QueryTermInfo.exec(tempSQL);
            QueryTermInfo.next();

            QString mTestCost = QueryTermInfo.value("TestCost").toString();
            if(mTestCost.isEmpty())mTestCost = spurTestCost;
            QuerySymb2TermInfo.bindValue(":TestCost",mTestCost);

            QuerySymb2TermInfo.bindValue(":TermPicPath",QueryTermInfo.value("TermPicPath").toString());
            QuerySymb2TermInfo.bindValue(":TagType",QueryTermInfo.value("TagType").toString());
            QuerySymb2TermInfo.bindValue(":TagPos",QueryTermInfo.value("TagPos").toString());
            QuerySymb2TermInfo.bindValue(":TagEdge",QueryTermInfo.value("TagEdge").toString());
            QuerySymb2TermInfo.bindValue(":TagColor",QueryTermInfo.value("TagColor").toString());
            QuerySymb2TermInfo.exec();
        }//end of for(int i=0;i<listConnNum.count();i++)
    }
    //==========加载端口结束

    for(int i=0;i<ListHisSymbolID.count();i++)
    {
        if(ListHisSymbolID.at(i).split(",").at(2)=="") continue;
        for(int j=0;j<ListHisSymbolID.count();j++)
        {
            if(i==j) continue;
            if(ListHisSymbolID.at(i).split(",").at(2)==ListHisSymbolID.at(j).split(",").at(1))
            {
                QSqlQuery QuerySymbol(T_ProjectDatabase);
                QString tempSQL="UPDATE Symbol SET InterConnect=:InterConnect WHERE Symbol_ID = "+ListHisSymbolID.at(i).split(",").at(0);
                QuerySymbol.prepare(tempSQL);
                QuerySymbol.bindValue(":InterConnect",ListHisSymbolID.at(j).split(",").at(0));
                QuerySymbol.exec();
                break;
            }
        }
    }
    qDebug()<<"ListHisSymbolID="<<ListHisSymbolID<<",ListSymbolSpurInfo="<<ListSymbolSpurInfo;
    if(ListSymbolSpurInfo.count()==ListHisSymbolID.count())
    {
        for(int i=0;i<ListSymbolSpurInfo.count();i++)
        {
            QSqlQuery QuerySymbol(T_ProjectDatabase);
            QString tempSQL="UPDATE Symbol SET SourceConn=:SourceConn,ExecConn=:ExecConn,SourcePrior=:SourcePrior,InterConnect=:InterConnect WHERE Symbol_ID = "+ListHisSymbolID.at(i).split(",").at(0);
            QuerySymbol.prepare(tempSQL);
            QuerySymbol.bindValue(":SourceConn",ListSymbolSpurInfo.at(i).split(",").at(0)=="Checked"?true:false);
            QuerySymbol.bindValue(":ExecConn",ListSymbolSpurInfo.at(i).split(",").at(2)=="Checked"?true:false);
            QuerySymbol.bindValue(":SourcePrior",ListSymbolSpurInfo.at(i).split(",").at(1));
            if(StrIsNumber(ListSymbolSpurInfo.at(i).split(",").at(4)))
                QuerySymbol.bindValue(":InterConnect",ListHisSymbolID.at(ListSymbolSpurInfo.at(i).split(",").at(4).toInt()-1).split(",").at(0));
            else
                QuerySymbol.bindValue(":InterConnect","");
            QuerySymbol.exec();
            QSqlQuery QuerySearch(T_ProjectDatabase);
            tempSQL="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+ListHisSymbolID.at(i).split(",").at(0)+"'";
            QuerySearch.exec(tempSQL);
            int Symb2TermIndex=0;
            while(QuerySearch.next())
            {
                if(Symb2TermIndex>=ListSymbolSpurInfo.at(i).split(",").at(3).split("￤").count()) break;
                QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
                tempSQL="UPDATE Symb2TermInfo SET TestCost=:TestCost WHERE Symb2TermInfo_ID = "+QuerySearch.value("Symb2TermInfo_ID").toString();
                QuerySymb2TermInfo.prepare(tempSQL);
                QString StrTestCost=ListSymbolSpurInfo.at(i).split(",").at(3).split("￤").at(Symb2TermIndex);
                QuerySymb2TermInfo.bindValue(":TestCost",StrTestCost.remove(" "));
                QuerySymb2TermInfo.exec();
                Symb2TermIndex++;
            }//while(QuerySearch.next())
        }//for(int i=0;i<ListSymbolSpurInfo.count();i++)
    }//if(ListSymbolSpurInfo.count()==ListHisSymbolID.count())
    return Symbol_ID;
}
void SetLayerColor(QAxWidget *mAxwidget,QString sLayerName,MxDrawMcCmColor color)
{
    IMxDrawDatabase* database =(IMxDrawDatabase*) mAxwidget->querySubObject("GetDatabase()");
    IMxDrawLayerTable *layerTable =(IMxDrawLayerTable *) database->querySubObject("GetLayerTable()");
    IMxDrawLinetypeTable*linetypetable=(IMxDrawLinetypeTable*) database->querySubObject("GetLineTypeTable()");
    IMxDrawLayerTableRecord * layerTableRec;
    layerTableRec=(IMxDrawLayerTableRecord *)layerTable->querySubObject("GetAt(QString)",sLayerName);
    if(layerTableRec!=nullptr)
    {
        layerTableRec->setProperty("Color", color.asVariant());
    }
}
void  CreateLayer(QAxWidget *mAxwidget,QString sLayerName)
{
    IMxDrawDatabase* database =(IMxDrawDatabase*) mAxwidget->querySubObject("GetDatabase()");
    IMxDrawLayerTable *layerTable =(IMxDrawLayerTable *) database->querySubObject("GetLayerTable()");
    IMxDrawLinetypeTable*linetypetable=(IMxDrawLinetypeTable*) database->querySubObject("GetLineTypeTable()");
    IMxDrawLayerTableRecord * layerTableRec;
    layerTableRec=(IMxDrawLayerTableRecord *)layerTable->querySubObject("GetAt(QString)",sLayerName);
    if(layerTableRec==nullptr)
    {
        layerTableRec=(IMxDrawLayerTableRecord *)layerTable->querySubObject("Add(QString)",sLayerName);
        MxDrawMcCmColor color;
        if(sLayerName=="TZML") color.SetRGB(0,255,255);
        else if(sLayerName=="MXB") color.SetRGB(0,255,255);
        else if(sLayerName=="JXB") color.SetRGB(0,255,255);
        else color.SetRGB(255,255,255);
        layerTableRec->setProperty("Color", color.asVariant());
    }
}

int GetMaxIDOfDB(QSqlDatabase DataBase,QString TableName,QString ColumnName)
{
    int ID=1;
    QSqlQuery QueryID = QSqlQuery(DataBase);//设置数据库选择模型
    QString tempQueryID = QString("SELECT * FROM "+TableName+" ORDER BY "+ColumnName+" DESC");
    QueryID.exec(tempQueryID);
    if(QueryID.next()) ID=QueryID.value(ColumnName).toInt()+1;
    return ID;
}

int GetMaxIDOfLibDatabaseByLevel(QSqlDatabase DataBase,QString TableName,QString ColumnName,QString Level,QString ParentNo)
{
    int ID=ParentNo.toInt()*1000+1;
    QSqlQuery QueryID = QSqlQuery(DataBase);//设置数据库选择模型
    QString tempQueryID = "SELECT "+ ColumnName +" FROM "+TableName+" WHERE Level = '"+Level+"' AND ParentNo = '"+ParentNo+"'";
    QueryID.exec(tempQueryID);
    while(QueryID.next())
    {
        if(QueryID.value(0).toInt()>=ID) ID=QueryID.value(0).toInt()+1;
    }
    return ID;
}

int GetMaxIDOfLibDatabase(QSqlDatabase DataBase,QString TableName,QString ColumnName)
{
    int ID=1;
    QSqlQuery QueryID = QSqlQuery(DataBase);//设置数据库选择模型
    QString tempQueryID = "SELECT "+ ColumnName +" FROM "+TableName;
    QueryID.exec(tempQueryID);
    while(QueryID.next())
    {
        if(QueryID.value(0).toInt()>=ID) ID=QueryID.value(0).toInt()+1;
    }
    return ID;
}

int GetStrRealLength(QString Str)
{
    if(Str.count()<=0) return 0;
    int StrLen=0;
    for(int i=0;i<Str.count();i++)
    {
        if((Str.at(i)>="0")&&(Str.at(i)<="9")) StrLen+=0.5;
    }
    return StrLen/Str.count();
}

void LoadLinkText(QAxWidget* tmp_MxDrawWidget,IMxDrawBlockReference* BlkEnty,QString RetStrLinkTag ,QString LinkText,QString RetStrLinkTextPosition,QString SymbolName)
{
    qDebug()<<"LoadLinkText";
    double Kcoef=33/3.5;//1.1;
    QFontMetrics font(QFont("Arial"));
    qDebug()<<font.width(RetStrLinkTag);
    qDebug()<<font.width("这是1234个测试");
    //先删除原来的Attribute
    for (int  i = 0; i < BlkEnty->dynamicCall("AttributeCount()").toInt(); i++)
    {
        qDebug()<<"i="<<i;
        IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEnty->querySubObject("AttributeItem(int)",i);
        attrib->dynamicCall("Erase()");
    }

    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    // 循环得到所有实体
    for (; !iter->Done(); iter->Step(true, false))
    {
        qDebug()<<"111";
        // 得到遍历器当前的实体
        IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(tmp_MxDrawWidget,ent)) continue;//去除erase的实体
        if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
        {
            IMxDrawAttributeDefinition *attrdef=(IMxDrawAttributeDefinition *)ent;
            //根据符号的属性定义对象确定符号标号和端号的内容和位置
            if(attrdef->dynamicCall("Tag()").toString()=="设备标识符（显示）")
            {
                IMxDrawAttribute *attrib=(IMxDrawAttribute *)BlkEnty->querySubObject("AppendAttribute()");
                attrib->dynamicCall("SetRotation(double)",attrdef->dynamicCall("Rotation()").toDouble());
                attrib->dynamicCall("setColorIndex(int)",attrdef->dynamicCall("colorIndex()").toInt());
                attrib->dynamicCall("SetHeight(double)",attrdef->dynamicCall("Height()").toDouble());
                attrib->dynamicCall("SetWidthFactor(double)",attrdef->dynamicCall("WidthFactor()").toDouble());
                attrib->dynamicCall("SetTextString(QString)",RetStrLinkTag);
                attrib->dynamicCall("SetTag(QString)",attrdef->dynamicCall("Tag()").toString());
                attrib->dynamicCall("SetIsInvisible(bool)",false);
                attrib->dynamicCall("SetLayer(QString)","LY_Attdef");
                attrib->setHorizontalMode(attrdef->horizontalMode());
                attrib->setVerticalMode(attrdef->verticalMode());
                MxDrawPoint* pt= new MxDrawPoint();
                IMxDrawPoint *ptx=(IMxDrawPoint *)pt;
                IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
                if(fabs(((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x())>0.01)
                {

                    ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                    ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());

                    if(RetStrLinkTextPosition=="箭尾")
                    {
                        if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点1"))
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x()-5-1-font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                        }
                        else if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点2"))
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->y()-5-1-font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());//RetStrLinkTag.count()*Kcoef
                        }
                        else if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点3"))//AlignmentPoint>0
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x()+5+1+font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                        }
                        else if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点4"))
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("AlignmentPoint()"))->y()+5+1+font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                        }
                    }
                    attrib->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
                    attrib->dynamicCall("SetAlignmentPoint(QAxObject*)",ptx->asVariant());
                }
                else
                {
                    ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                    ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                    if(RetStrLinkTextPosition=="箭尾")
                    {
                        if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点1"))
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->x()-5-1-font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                        }
                        else if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点2"))
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->y()-5-1-font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                        }
                        else if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点3"))
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->x()+5+1+font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->y()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                        }
                        else if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点4"))
                        {
                            ptx->setX(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->x()-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
                            ptx->setY(((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+((IMxDrawPoint *)attrdef->querySubObject("Position()"))->y()+5+1+font.width(RetStrLinkTag)/Kcoef-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
                        }
                    }
                    attrib->dynamicCall("SetPosition(QAxObject*)",ptx->asVariant());
                }
                BlkEnty->dynamicCall("AssertWriteEnabled()");
                break;
            }
        }
    }
    qDebug()<<"1112";
    if(LinkText!="")
    {
        int Direction;
        if(SymbolName.contains("链接点1")) {if(RetStrLinkTextPosition=="箭头") Direction=1;else Direction=3;}
        else if(SymbolName.contains("链接点2")) {if(RetStrLinkTextPosition=="箭头") Direction=2;else Direction=4;}
        else if(SymbolName.contains("链接点3")) {if(RetStrLinkTextPosition=="箭头") Direction=3;else Direction=1;}
        else if(SymbolName.contains("链接点4")) {if(RetStrLinkTextPosition=="箭头") Direction=4;else Direction=2;}
        AddAttrToBlockBesideDefAttr(tmp_MxDrawWidget,Direction,BlkEnty,"设备标识符（显示）","中断点和关联参考之间的分隔符关联参考（可配置的）","/",McColor::mcYellow);
        AddAttrToBlockBesideDefAttr(tmp_MxDrawWidget,Direction,BlkEnty,"中断点和关联参考之间的分隔符关联参考（可配置的）","关联参考（可配置的）",LinkText,McColor::mcYellow);
    }
    qDebug()<<"1113";
}
QString GetFunctionDefineNameBySymb2Lib_ID(QString Symb2Lib_ID)
{
    QSqlQuery QuerySymb2Lib = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr="SELECT * FROM Symb2Lib WHERE Symb2Lib_ID = '"+Symb2Lib_ID+"'";
    QuerySymb2Lib.exec(SqlStr);
    if(QuerySymb2Lib.next())
    {
        QSqlQuery QuerySymb2Class = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        SqlStr="SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QuerySymb2Lib.value("Symb2Class_ID").toString()+"'";
        QuerySymb2Class.exec(SqlStr);
        if(QuerySymb2Class.next())
        {
            return QuerySymb2Class.value("FunctionDefineName").toString();
        }
    }
    return "";
}
QString GetSymbolDescBySymb2Lib_ID(QString Symb2Lib_ID)
{
    //根据SymbolID找到Symb2Class数据库中对应的desc，Level=2
    QSqlQuery QuerySymb2Lib = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr="SELECT * FROM Symb2Lib WHERE Symb2Lib_ID = '"+Symb2Lib_ID+"'";
    QuerySymb2Lib.exec(SqlStr);
    if(QuerySymb2Lib.next())
    {
        QSqlQuery QuerySymb2Class = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        SqlStr="SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QuerySymb2Lib.value("Symb2Class_ID").toString()+"'";//Level=4
        QuerySymb2Class.exec(SqlStr);
        if(QuerySymb2Class.next())
        {
            SqlStr="SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QuerySymb2Class.value("Parent_ID").toString()+"'";//Level=3
            QuerySymb2Class.exec(SqlStr);
            if(QuerySymb2Class.next())
            {
                SqlStr="SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QuerySymb2Class.value("Parent_ID").toString()+"'";//Level=2
                QuerySymb2Class.exec(SqlStr);
                if(QuerySymb2Class.next())
                {
                    if(QuerySymb2Class.value("Level").toInt()==2)  return QuerySymb2Class.value("Desc").toString();
                }
            }
        }
    }
    return "";
}

QString GetStrRemoveLastNum(QString Str)
{
    for(int i=Str.count()-1;i>=0;i--)
    {
        if((Str.at(i)>='0')&&(Str.at(i)<='9')) Str.remove(i,1);
        else break;
    }
    return Str;
}
//获取字符串结尾的数字，如果结尾处不是数字则返回0
int GetStrLastNum(QString Str)
{
    QString Num;
    for(int i=Str.count()-1;i>=0;i--)
    {
        if((Str.at(i)>='0')&&(Str.at(i)<='9')) Num.insert(0,Str.at(i));
        else break;
    }
    if(Num=="") return 0;
    else return Num.toInt();
}

QString GetLineDir(IMxDrawLine *Line)
{
    qDebug()<<"GetLineDir";
    IMxDrawPoint *StartPoint=(IMxDrawPoint *)Line->querySubObject("StartPoint()");
    IMxDrawPoint *EndPoint=(IMxDrawPoint *)Line->querySubObject("EndPoint()");
    qDebug()<<"StartPointx="<<StartPoint->x()<<"StartPoint->y()"<<StartPoint->y();
    qDebug()<<"EndPointx="<<EndPoint->x()<<"EndPoint->y()"<<EndPoint->y();
    if(fabs(StartPoint->x()-EndPoint->x())<minDelta) return "垂直";
    if(fabs(StartPoint->y()-EndPoint->y())<minDelta) return "水平";
    return "其他";
}

int CheckLineCDPCross(IMxDrawLine *Line,QString Page_ID)
{
    IMxDrawPoint *StartPoint=(IMxDrawPoint *)Line->querySubObject("StartPoint()");
    IMxDrawPoint *EndPoint=(IMxDrawPoint *)Line->querySubObject("EndPoint()");
    QSqlQuery QueryWires = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    if(GetLineDir(Line)=="水平")
    {
        QString PosY=QString::number(StartPoint->y(),'f',0)+".000000";
        SqlStr="SELECT Wires_ID,Position FROM Wires WHERE Page_ID = '"+Page_ID+"' AND Position LIKE '%,"+PosY+",0.000000'";
    }
    else
    {
        QString PosX=QString::number(StartPoint->x(),'f',0)+".000000";
        SqlStr="SELECT Wires_ID,Position FROM Wires WHERE Page_ID = '"+Page_ID+"' AND Position LIKE '"+PosX+",%,0.000000'";
    }
    qDebug()<<"SqlStr="<<SqlStr;
    QueryWires.exec(SqlStr);
    while(QueryWires.next())
    {
        bool FindCDP=true;
        QString Position=QueryWires.value(1).toString();
        if(GetLineDir(Line)=="水平")
        {
            double Posx=Position.split(",").at(0).toDouble();
            if((StartPoint->x()<Posx)&&(EndPoint->x()<Posx)) FindCDP=false;
            if((StartPoint->x()>Posx)&&(EndPoint->x()>Posx)) FindCDP=false;
        }
        else
        {
            double Posy=Position.split(",").at(1).toDouble();
            if((StartPoint->y()<Posy)&&(EndPoint->y()<Posy)) FindCDP=false;
            if((StartPoint->y()>Posy)&&(EndPoint->y()>Posy)) FindCDP=false;
        }
        if(FindCDP) return QueryWires.value(0).toInt();
    }
    return 0;
}

//查看附近(同一行或者同一列)是否存在同元件的插针
bool CheckSpinBeside(int Symbol_ID,QAxWidget* tmp_MxDrawWidget)
{
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID)+" AND Symbol_Category = '插针'";
    QuerySymbol.exec(SqlStr);
    if(!QuerySymbol.next()) return false;

    QString Symbol=QuerySymbol.value("Symbol").toString();
    QString SymbolNum=Symbol.mid(Symbol.lastIndexOf("-")+1,Symbol.count()-Symbol.lastIndexOf("-")-1);
    if(!StrIsNumber(SymbolNum)) return false;
    QString Coordinate=QuerySymbol.value("InsertionPoint").toString();
    if(Coordinate.split(",").count()!=3) return false;
    QString Equipment_ID=QuerySymbol.value("Equipment_ID").toString();
    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+Equipment_ID+"' AND Symbol_ID <> "+QuerySymbol.value("Symbol_ID").toString();
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        if(QuerySearch.value("Symbol_Handle").toString()=="") continue;
        QString SymbolSearch=QuerySearch.value("Symbol").toString();
        QString SymbolSearchNum=SymbolSearch.mid(SymbolSearch.lastIndexOf("-")+1,SymbolSearch.count()-SymbolSearch.lastIndexOf("-")-1);
        if(!StrIsNumber(SymbolSearchNum)) continue;
        if((SymbolNum.toInt()%2)!=(SymbolSearchNum.toInt()%2)) continue;
        QString CoordinateSearch=QuerySearch.value("InsertionPoint").toString();
        if(CoordinateSearch.split(",").count()!=3) continue;
        if((CoordinateSearch.split(",").at(0)==Coordinate.split(",").at(0))||(CoordinateSearch.split(",").at(1)==Coordinate.split(",").at(1)))
        {
            //查看Search到的块是否有设备描述符
            IMxDrawBlockReference *BlkSearch=(IMxDrawBlockReference *)tmp_MxDrawWidget->querySubObject("HandleToObject(const QString)",QuerySearch.value("Symbol_Handle").toString());
            if(GetBlockAttrTextString(BlkSearch,"设备标识符(显示)")!="")  return true;
        }
    }
    return false;
}

//查看附近(同一行或者同一列)是否存在同端子排的端子
bool CheckTerminalBeside(int Terminal_ID,QAxWidget* tmp_MxDrawWidget)
{
    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(Terminal_ID);
    QueryTerminal.exec(SqlStr);
    if(!QueryTerminal.next()) return false;
    QString Symbol=QueryTerminal.value("Symbol").toString();
    QString SymbolNum=Symbol.mid(Symbol.lastIndexOf("-")+1,Symbol.count()-Symbol.lastIndexOf("-")-1);
    if(!StrIsNumber(SymbolNum)) return false;
    QString Coordinate=QueryTerminal.value("Coordinate").toString();
    if(Coordinate.split(",").count()!=3) return false;
    QString TerminalStrip_ID=QueryTerminal.value("TerminalStrip_ID").toString();
    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+TerminalStrip_ID+"' AND Terminal_ID <> "+QueryTerminal.value("Terminal_ID").toString();
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        if(QuerySearch.value("Handle").toString()=="") continue;
        QString SymbolSearch=QuerySearch.value("Symbol").toString();
        QString SymbolSearchNum=SymbolSearch.mid(SymbolSearch.lastIndexOf("-")+1,SymbolSearch.count()-SymbolSearch.lastIndexOf("-")-1);
        if(!StrIsNumber(SymbolSearchNum)) continue;
        if((SymbolNum.toInt()%2)!=(SymbolSearchNum.toInt()%2)) continue;
        QString CoordinateSearch=QuerySearch.value("Coordinate").toString();
        if(CoordinateSearch.split(",").count()!=3) continue;
        if((CoordinateSearch.split(",").at(0)==Coordinate.split(",").at(0))||(CoordinateSearch.split(",").at(1)==Coordinate.split(",").at(1)))
        {
            //查看Search到的块是否有设备描述符
            IMxDrawBlockReference *BlkSearch=(IMxDrawBlockReference *)tmp_MxDrawWidget->querySubObject("HandleToObject(const QString)",QuerySearch.value("Handle").toString());
            if(GetBlockAttrTextString(BlkSearch,"设备标识符(显示)")!="")  return true;
        }
    }
    return false;
}

//查看Symbol是否在黑盒内部，如果不是的话返回0，如果是并且黑盒和Symbol是同元件则返回Equipment_ID，如果是并且黑盒和Symbol是不同元件则返回-1
int CheckBlackBox(QAxWidget* tmp_MxDrawWidget,double posx,double posy,int Symbol_ID)
{
    qDebug()<<"Start CheckBlackBox";
    int Equipment_ID=0;
    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString tempSQL = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID);
    QuerySearch.exec(tempSQL);
    if(QuerySearch.next())
    {
        Equipment_ID=QuerySearch.value("Equipment_ID").toInt();
    }

    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)tmp_MxDrawWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    MxDrawResbuf* filter =new MxDrawResbuf();

    filter->AddStringEx("LWPOLYLINE",5020);
    filter->AddStringEx("0",8);
    ss->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    qDebug()<<"AllSelect,ss->Count()="<<ss->Count();
    for (int i = 0; i < ss->Count(); i++)
    {
        IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
        if(ent==nullptr) continue;
        if(EntyIsErased(tmp_MxDrawWidget,ent)) continue;
        ent->dynamicCall("GetxDataString2(QString,0)","LD_GROUPCPXRECT_TEXT",0).toString();
        if(tmp_MxDrawWidget->dynamicCall("IsOk()").toString()=="true")
        {
            //查看Symbol是否在黑盒内部
            int VCnt=((IMxDrawPolyline *)ent)->property("NumVerts").toInt();
            qDebug()<<"VCnt="<<VCnt;
            if(VCnt>=4)
            {
                IMxDrawPoint* Pt1=(IMxDrawPoint*)((IMxDrawPolyline *)ent)->querySubObject("GetPointAt(int)",0);
                IMxDrawPoint* Pt2=(IMxDrawPoint*)((IMxDrawPolyline *)ent)->querySubObject("GetPointAt(int)",2);
                bool InBoxRange=true;
                if(((posx<Pt1->x())&&(posx<Pt2->x()))||((posx>Pt1->x())&&(posx>Pt2->x()))) InBoxRange=false;
                if(((posy<Pt1->y())&&(posy<Pt2->y()))||((posy>Pt1->y())&&(posy>Pt2->y()))) InBoxRange=false;
                if(InBoxRange)
                {
                    //查看黑盒是否与功能子块属于同一个元件
                    QString tempSQL = "SELECT * FROM Symbol WHERE Symbol_ID = "+ent->dynamicCall("GetxDataString2(QString,int)","DbID",0).toString();
                    QuerySearch.exec(tempSQL);
                    if(QuerySearch.next())
                    {
                        if(Equipment_ID>0)
                        {
                            if(QuerySearch.value("Equipment_ID").toInt()==Equipment_ID) return Equipment_ID;//属于同一个元件
                            else  return -1;
                        }
                        else
                        {
                            return QuerySearch.value("Equipment_ID").toInt();
                        }
                    }
                }// end of if(InBoxRange)
            }//end of if(VCnt>=4)
        }//end of if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
    }
    return 0;
}

//查看Symbol是否在结构盒内部，如果不是的话返回0，如果是则返回1
int CheckStructBox(QAxWidget* tmp_MxDrawWidget,double posx,double posy)
{
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)tmp_MxDrawWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    MxDrawResbuf* filter =new MxDrawResbuf();

    filter->AddStringEx("LWPOLYLINE",5020);
    filter->AddStringEx("0",8);
    ss->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    qDebug()<<"AllSelect,ss->Count()="<<ss->Count();
    for (int i = 0; i < ss->Count(); i++)
    {
        IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
        if(ent==nullptr) continue;
        if(EntyIsErased(tmp_MxDrawWidget,ent)) continue;
        ent->dynamicCall("GetxDataString2(QString,0)","LD_GROUPSBXRECT_TEXT",0).toString();
        if(tmp_MxDrawWidget->dynamicCall("IsOk()").toString()=="true")
        {
            //查看Symbol是否在黑盒内部
            int VCnt=((IMxDrawPolyline *)ent)->property("NumVerts").toInt();
            qDebug()<<"VCnt="<<VCnt;
            if(VCnt>=4)
            {
                IMxDrawPoint* Pt1=(IMxDrawPoint*)((IMxDrawPolyline *)ent)->querySubObject("GetPointAt(int)",0);
                IMxDrawPoint* Pt2=(IMxDrawPoint*)((IMxDrawPolyline *)ent)->querySubObject("GetPointAt(int)",2);
                bool InBoxRange=true;
                if(((posx<Pt1->x())&&(posx<Pt2->x()))||((posx>Pt1->x())&&(posx>Pt2->x()))) InBoxRange=false;
                if(((posy<Pt1->y())&&(posy<Pt2->y()))||((posy>Pt1->y())&&(posy>Pt2->y()))) InBoxRange=false;
                if(InBoxRange) return 1;
            }//end of if(VCnt>=4)
        }//end of if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
    }
    return 0;
}

QString CheckAndInsertSymb2Class(int Level,QString FunctionDefineClass_ID3,QString FunctionDefineClass_ID2,QString FunctionDefineClass_ID1,QString FunctionDefineClass_ID0,QString FunctionDefineName3,QString FunctionDefineName2,QString FunctionDefineName1,QString FunctionDefineName0)
{
    qDebug()<<"CheckAndInsertSymb2Class,Level="<<Level<<",FunctionDefineClass_ID3="<<FunctionDefineClass_ID3<<",FunctionDefineClass_ID2="<<FunctionDefineClass_ID2<<",FunctionDefineClass_ID1="<<FunctionDefineClass_ID1<<",FunctionDefineClass_ID0="<<FunctionDefineClass_ID0;
    //如果Parent_ID为空则新建
    int Symb2Class_ID=0;
    QSqlQuery querySymb2Class(T_LibDatabase);
    QString Symb2Class_ID0,Symb2Class_ID1,Symb2Class_ID2,Symb2Class_ID3;
    QString SqlStr="SELECT * FROM Symb2Class WHERE FuncDefID = '"+FunctionDefineClass_ID0+"'";//level=0
    querySymb2Class.exec(SqlStr);
    if(querySymb2Class.next())//Symb2Class中不存在FunctionDefineClass_ID0对应的记录，新建
        Symb2Class_ID0=querySymb2Class.value("Symb2Class_ID").toString();
    else
    {
        SqlStr =  "INSERT INTO Symb2Class (Symb2Class_ID,Parent_ID,Level,Desc,_Order,FunctionDefineName,FuncDefID)"
                  "VALUES (:Symb2Class_ID,:Parent_ID,:Level,:Desc,:_Order,:FunctionDefineName,:FuncDefID)";
        querySymb2Class.prepare(SqlStr);

        QSqlQuery querySearch(T_LibDatabase);
        Symb2Class_ID=0;
        SqlStr="SELECT * FROM Symb2Class WHERE Level = 0";
        querySearch.exec(SqlStr);
        while(querySearch.next())
        {
            if(querySearch.value("Symb2Class_ID").toInt()>Symb2Class_ID)
                Symb2Class_ID=querySearch.value("Symb2Class_ID").toInt()+1;
        }
        querySymb2Class.bindValue(":Symb2Class_ID",QString::number(Symb2Class_ID));
        querySymb2Class.bindValue(":Parent_ID",0);
        querySymb2Class.bindValue(":Level",0);
        querySymb2Class.bindValue(":Desc",FunctionDefineName0);
        querySymb2Class.bindValue(":_Order",FunctionDefineClass_ID0);
        querySymb2Class.bindValue(":FunctionDefineName","");
        querySymb2Class.bindValue(":FuncDefID",FunctionDefineClass_ID0);
        querySymb2Class.exec();
        Symb2Class_ID0=QString::number(Symb2Class_ID);
    }
    if(Level==0)  return Symb2Class_ID0;


    SqlStr="SELECT * FROM Symb2Class WHERE FuncDefID = '"+FunctionDefineClass_ID1+"'";//level=1
    querySymb2Class.exec(SqlStr);
    if(querySymb2Class.next())//Symb2Class中不存在FunctionDefineClass_ID1对应的记录，新建
        Symb2Class_ID1=querySymb2Class.value("Symb2Class_ID").toString();
    else
    {
        SqlStr =  "INSERT INTO Symb2Class (Symb2Class_ID,Parent_ID,Level,Desc,_Order,FunctionDefineName,FuncDefID)"
                  "VALUES (:Symb2Class_ID,:Parent_ID,:Level,:Desc,:_Order,:FunctionDefineName,:FuncDefID)";
        querySymb2Class.prepare(SqlStr);

        QSqlQuery querySearch(T_LibDatabase);
        Symb2Class_ID=1;
        SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+Symb2Class_ID0+"'";
        querySearch.exec(SqlStr);
        while(querySearch.next())
        {
            QString SearchSymb2Class_ID=querySearch.value("Symb2Class_ID").toString();
            int LastNum=SearchSymb2Class_ID.mid(SearchSymb2Class_ID.count()-3,3).toInt();
            if(LastNum>=Symb2Class_ID)
                Symb2Class_ID=LastNum+1;
        }
        querySymb2Class.bindValue(":Symb2Class_ID",Symb2Class_ID0+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID));
        querySymb2Class.bindValue(":Parent_ID",Symb2Class_ID0);
        querySymb2Class.bindValue(":Level",1);
        querySymb2Class.bindValue(":Desc",FunctionDefineName1);
        querySymb2Class.bindValue(":_Order",FunctionDefineClass_ID1);
        querySymb2Class.bindValue(":FunctionDefineName","");
        querySymb2Class.bindValue(":FuncDefID",FunctionDefineClass_ID1);
        querySymb2Class.exec();
        Symb2Class_ID1=Symb2Class_ID0+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID);
    }
    if(Level==1)  return Symb2Class_ID1;

    SqlStr="SELECT * FROM Symb2Class WHERE FuncDefID = '"+FunctionDefineClass_ID2+"'";//level=2
    querySymb2Class.exec(SqlStr);
    if(querySymb2Class.next())//Symb2Class中不存在FunctionDefineClass_ID2对应的记录，新建
        Symb2Class_ID2=querySymb2Class.value("Symb2Class_ID").toString();
    else
    {
        SqlStr =  "INSERT INTO Symb2Class (Symb2Class_ID,Parent_ID,Level,Desc,_Order,FunctionDefineName,FuncDefID)"
                  "VALUES (:Symb2Class_ID,:Parent_ID,:Level,:Desc,:_Order,:FunctionDefineName,:FuncDefID)";
        querySymb2Class.prepare(SqlStr);

        QSqlQuery querySearch(T_LibDatabase);
        Symb2Class_ID=1;
        SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+Symb2Class_ID1+"'";
        querySearch.exec(SqlStr);
        while(querySearch.next())
        {
            QString SearchSymb2Class_ID=querySearch.value("Symb2Class_ID").toString();
            int LastNum=SearchSymb2Class_ID.mid(SearchSymb2Class_ID.count()-3,3).toInt();
            if(LastNum>=Symb2Class_ID)
                Symb2Class_ID=LastNum+1;
        }
        querySymb2Class.bindValue(":Symb2Class_ID",Symb2Class_ID1+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID));
        querySymb2Class.bindValue(":Parent_ID",Symb2Class_ID1);
        querySymb2Class.bindValue(":Level",2);
        querySymb2Class.bindValue(":Desc",FunctionDefineName2);
        querySymb2Class.bindValue(":_Order",FunctionDefineClass_ID2);
        querySymb2Class.bindValue(":FunctionDefineName","");
        querySymb2Class.bindValue(":FuncDefID",FunctionDefineClass_ID2);
        querySymb2Class.exec();
        Symb2Class_ID2=Symb2Class_ID1+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID);
    }
    if(Level==2)  return Symb2Class_ID2;

    SqlStr="SELECT * FROM Symb2Class WHERE FuncDefID = '"+FunctionDefineClass_ID3+"'";//level=3
    querySymb2Class.exec(SqlStr);
    if(querySymb2Class.next())//Symb2Class中不存在FunctionDefineClass_ID3对应的记录，新建
        Symb2Class_ID3=querySymb2Class.value("Symb2Class_ID").toString();
    else
    {
        SqlStr =  "INSERT INTO Symb2Class (Symb2Class_ID,Parent_ID,Level,Desc,_Order,FunctionDefineName,FuncDefID)"
                  "VALUES (:Symb2Class_ID,:Parent_ID,:Level,:Desc,:_Order,:FunctionDefineName,:FuncDefID)";
        querySymb2Class.prepare(SqlStr);

        QSqlQuery querySearch(T_LibDatabase);
        Symb2Class_ID=1;
        SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+Symb2Class_ID2+"'";
        querySearch.exec(SqlStr);
        while(querySearch.next())
        {
            QString SearchSymb2Class_ID=querySearch.value("Symb2Class_ID").toString();
            int LastNum=SearchSymb2Class_ID.mid(SearchSymb2Class_ID.count()-3,3).toInt();
            if(LastNum>=Symb2Class_ID)
                Symb2Class_ID=LastNum+1;
        }
        querySymb2Class.bindValue(":Symb2Class_ID",Symb2Class_ID2+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID));
        querySymb2Class.bindValue(":Parent_ID",Symb2Class_ID2);
        querySymb2Class.bindValue(":Level",3);
        querySymb2Class.bindValue(":Desc",FunctionDefineName3);
        querySymb2Class.bindValue(":_Order",FunctionDefineClass_ID3);
        querySymb2Class.bindValue(":FunctionDefineName","");
        querySymb2Class.bindValue(":FuncDefID",FunctionDefineClass_ID3);
        querySymb2Class.exec();
        Symb2Class_ID3=Symb2Class_ID2+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID);
    }
    if(Level==3)  return Symb2Class_ID3;
    return "";
}

//Mode=0:insert
//Mode=1:update
//返回Symb2Class的Symb2Class_ID
QString InsertOrUpdateSymb2Lib(int Mode,QString UpdateSymb2Class_ID,QString FunctionDefineClass_ID,QString SymbolFileName,int TermCount)
{
    //先在FunctionDefineClass表中找到FunctionDefineClass_ID对应的FunctionDefineName，level=4
    //然后在FunctionDefineClass表中找到level=3对应的FunctionDefineClass_ID，据此在Symb2Class表中找到对应的Symb2Class_ID，如果找到则在它下面新增level=4的记录
    //如果找不到则在Symb2Class表中新建level=3对应的记录（注意如果level=2不存在则根据FunctionDefineClass中level=2新建记录，以此类推）
    QSqlQuery queryFunctionDefineClass(T_LibDatabase);
    QString FunctionDefineName4,FunctionDefineName3,FunctionDefineName2,FunctionDefineName1,FunctionDefineName0;
    QString FunctionDefineClass_ID3,FunctionDefineClass_ID2,FunctionDefineClass_ID1,FunctionDefineClass_ID0,Symb2Class_ID3="";
    QString SqlStr="SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+FunctionDefineClass_ID+"'";//level=4
    queryFunctionDefineClass.exec(SqlStr);
    qDebug()<<SqlStr;
    if(queryFunctionDefineClass.next())
    {
        FunctionDefineName4=queryFunctionDefineClass.value("FunctionDefineName").toString();//level=4
        qDebug()<<"FunctionDefineName4="<<FunctionDefineName4;
        SqlStr="SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+queryFunctionDefineClass.value("ParentNo").toString()+"'";
        queryFunctionDefineClass.exec(SqlStr);
        if(queryFunctionDefineClass.next())
        {
            FunctionDefineClass_ID3=queryFunctionDefineClass.value("FunctionDefineClass_ID").toString();//level=3
            FunctionDefineName3=queryFunctionDefineClass.value("FunctionDefineName").toString();//level=3
            SqlStr="SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+queryFunctionDefineClass.value("ParentNo").toString()+"'";
            queryFunctionDefineClass.exec(SqlStr);
            if(queryFunctionDefineClass.next())
            {
                FunctionDefineClass_ID2=queryFunctionDefineClass.value("FunctionDefineClass_ID").toString();//level=2
                FunctionDefineName2=queryFunctionDefineClass.value("FunctionDefineName").toString();//level=2
                SqlStr="SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+queryFunctionDefineClass.value("ParentNo").toString()+"'";
                queryFunctionDefineClass.exec(SqlStr);
                if(queryFunctionDefineClass.next())
                {
                    FunctionDefineClass_ID1=queryFunctionDefineClass.value("FunctionDefineClass_ID").toString();//level=1
                    FunctionDefineName1=queryFunctionDefineClass.value("FunctionDefineName").toString();//level=1
                    SqlStr="SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+queryFunctionDefineClass.value("ParentNo").toString()+"'";
                    queryFunctionDefineClass.exec(SqlStr);
                    if(queryFunctionDefineClass.next())
                    {
                        FunctionDefineClass_ID0=queryFunctionDefineClass.value("FunctionDefineClass_ID").toString();//level=0
                        FunctionDefineName0=queryFunctionDefineClass.value("FunctionDefineName").toString();//level=0
                    }
                }
            }
        }
    }

    Symb2Class_ID3=CheckAndInsertSymb2Class(3,FunctionDefineClass_ID3,FunctionDefineClass_ID2,FunctionDefineClass_ID1,FunctionDefineClass_ID0,FunctionDefineName3,FunctionDefineName2,FunctionDefineName1,FunctionDefineName0);
    qDebug()<<"CheckAndInsertSymb2Class,Symb2Class_ID3="<<Symb2Class_ID3;
    if(Mode==0)
    {
        QString StrSymb2Class_ID="";
        QSqlQuery querySymb2Class(T_LibDatabase);
        SqlStr = "SELECT * FROM Symb2Class WHERE Parent_ID = '"+Symb2Class_ID3+"' AND Desc= '"+SymbolFileName.mid(6,SymbolFileName.count()-4-6-2)+"'";
        querySymb2Class.exec(SqlStr);
        if(querySymb2Class.next()) StrSymb2Class_ID=querySymb2Class.value("Symb2Class_ID").toString();
        else
        {
            SqlStr =  "INSERT INTO Symb2Class (Symb2Class_ID,Parent_ID,Level,Desc,_Order,FunctionDefineName,FuncDefID)"
                      " VALUES (:Symb2Class_ID,:Parent_ID,:Level,:Desc,:_Order,:FunctionDefineName,:FuncDefID)";
            querySymb2Class.prepare(SqlStr);

            QSqlQuery querySearch(T_LibDatabase);
            int Symb2Class_ID=1;
            int _Order=1;
            SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+Symb2Class_ID3+"'";
            qDebug()<<SqlStr;
            querySearch.exec(SqlStr);
            while(querySearch.next())
            {
                QString SearchSymb2Class_ID=querySearch.value("Symb2Class_ID").toString();
                int LastNum=SearchSymb2Class_ID.mid(SearchSymb2Class_ID.count()-3,3).toInt();
                if(LastNum>=Symb2Class_ID)
                    Symb2Class_ID=LastNum+1;
                if(querySearch.value("_Order").toInt()>=_Order)
                    _Order=querySearch.value("_Order").toInt()+1;
            }
            if(_Order==0) _Order=1;
            StrSymb2Class_ID=Symb2Class_ID3+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID);
            querySymb2Class.bindValue(":Symb2Class_ID",StrSymb2Class_ID);
            querySymb2Class.bindValue(":Parent_ID",Symb2Class_ID3);
            querySymb2Class.bindValue(":Level",4);
            querySymb2Class.bindValue(":Desc",SymbolFileName.mid(6,SymbolFileName.count()-4-6-2));
            querySymb2Class.bindValue(":_Order",_Order);
            querySymb2Class.bindValue(":FunctionDefineName",FunctionDefineName4);
            querySymb2Class.bindValue(":FuncDefID","");
            querySymb2Class.exec();
        }


        //添加Symb2Lib记录
        QSqlQuery querySymb2Lib(T_LibDatabase);
        SqlStr =  "INSERT INTO Symb2Lib (Symb2Lib_ID,Symb2_Name,Symb2Class_ID,_Order,TermCount)"
                  "VALUES (:Symb2Lib_ID,:Symb2_Name,:Symb2Class_ID,:_Order,:TermCount)";
        querySymb2Lib.prepare(SqlStr);
        int Symb2Lib_ID=GetMaxIDOfLibDatabase(T_LibDatabase,"Symb2Lib","Symb2Lib_ID");
        querySymb2Lib.bindValue(":Symb2Lib_ID",QString::number(Symb2Lib_ID));
        querySymb2Lib.bindValue(":Symb2_Name",SymbolFileName.mid(0,SymbolFileName.count()-4));
        querySymb2Lib.bindValue(":Symb2Class_ID",StrSymb2Class_ID);
        querySymb2Lib.bindValue(":_Order",SymbolFileName.mid(SymbolFileName.count()-4-1,1).toInt());
        querySymb2Lib.bindValue(":TermCount",QString::number(TermCount));
        querySymb2Lib.exec();
        return StrSymb2Class_ID;
    }//if(Mode==0)
    else//Mode=1
    {
        //QString StrSymb2Class_ID="";
        QSqlQuery querySymb2Class(T_LibDatabase);
        SqlStr = "SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+UpdateSymb2Class_ID+"'";
        querySymb2Class.exec(SqlStr);
        if(querySymb2Class.next())
        {
            if(querySymb2Class.value("Parent_ID").toString()==Symb2Class_ID3) return UpdateSymb2Class_ID;
        }

        SqlStr =  "UPDATE Symb2Class SET Symb2Class_ID=:Symb2Class_ID,Parent_ID=:Parent_ID,_Order=:_Order,FunctionDefineName=:FunctionDefineName"
                  " WHERE Symb2Class_ID = '"+UpdateSymb2Class_ID+"'";
        querySymb2Class.prepare(SqlStr);

        QSqlQuery querySearch(T_LibDatabase);
        int Symb2Class_ID=1;
        int _Order=1;
        SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+Symb2Class_ID3+"'";
        qDebug()<<SqlStr;
        querySearch.exec(SqlStr);
        while(querySearch.next())
        {
            QString SearchSymb2Class_ID=querySearch.value("Symb2Class_ID").toString();
            int LastNum=SearchSymb2Class_ID.mid(SearchSymb2Class_ID.count()-3,3).toInt();
            if(LastNum>=Symb2Class_ID)
                Symb2Class_ID=LastNum+1;
            if(querySearch.value("_Order").toInt()>=_Order)
                _Order=querySearch.value("_Order").toInt()+1;
        }
        if(_Order==0) _Order=1;
        querySymb2Class.bindValue(":Symb2Class_ID",Symb2Class_ID3+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID));
        querySymb2Class.bindValue(":Parent_ID",Symb2Class_ID3);
        querySymb2Class.bindValue(":_Order",_Order);
        querySymb2Class.bindValue(":FunctionDefineName",FunctionDefineName4);
        querySymb2Class.exec();

        SqlStr =  "UPDATE Symb2Lib SET Symb2Class_ID=:Symb2Class_ID WHERE Symb2Class_ID = '"+UpdateSymb2Class_ID+"'";
        QSqlQuery querySymb2Lib(T_LibDatabase);
        querySymb2Lib.prepare(SqlStr);
        querySymb2Lib.bindValue(":Symb2Class_ID",Symb2Class_ID3+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID));
        querySymb2Lib.exec();
        return Symb2Class_ID3+QString::number(Symb2Class_ID).sprintf("%03d",Symb2Class_ID);
    }
}

QFileInfoList GetFileList(QString path)
{
    QDir dir(path);
    QFileInfoList file_list = dir.entryInfoList(QDir::Files | QDir::Hidden | QDir::NoSymLinks);
    QFileInfoList folder_list = dir.entryInfoList(QDir::Dirs | QDir::NoDotAndDotDot);

    for(int i = 0; i != folder_list.size(); i++)
    {
        QString name = folder_list.at(i).absoluteFilePath();
        QFileInfoList child_file_list = GetFileList(name);
        file_list.append(child_file_list);
    }

    return file_list;
}

//新增端子短接排的统计
int GetNodeCountBySymb2TermInfo_ID(QString Symb_ID,int Category)
{
    int RetCount=0;

    QStringList ListSearchTerm;
    QString SqlStr;
    if(Category==1)
    {
        QSqlQuery QuerySearchTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr= "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb_ID.mid(0,Symb_ID.indexOf("."));
        QuerySearchTerminalInstance.exec(SqlStr);
        if(QuerySearchTerminalInstance.next())
        {
            SqlStr="SELECT * FROM TerminalInstance WHERE Terminal_ID = '"+QuerySearchTerminalInstance.value("Terminal_ID").toString()+"'";
            QuerySearchTerminalInstance.exec(SqlStr);
            while(QuerySearchTerminalInstance.next()) ListSearchTerm.append(QuerySearchTerminalInstance.value("Terminal_ID").toString()+Symb_ID.mid(Symb_ID.indexOf("."),Symb_ID.count()-Symb_ID.indexOf(".")));
        }
    }
    else if(Category==0)
    {
        ListSearchTerm.append(Symb_ID);
    }

    for(QString StrSymb_ID:ListSearchTerm)
    {
        QSqlQuery QueryJXB(T_ProjectDatabase);
        QString StrSql="SELECT * FROM JXB WHERE Symb1_ID = '"+StrSymb_ID+"' AND Symb1_Category = '"+QString::number(Category)+"'";
        QueryJXB.exec(StrSql);
        while(QueryJXB.next())
        {
            //if(QueryJXB.value("JXB_ID").toString()==BesidesID) continue;
            RetCount++;
        }
        StrSql="SELECT * FROM JXB WHERE Symb2_ID = '"+StrSymb_ID+"' AND Symb2_Category = '"+QString::number(Category)+"'";
        QueryJXB.exec(StrSql);
        while(QueryJXB.next())
        {
            //if(QueryJXB.value("JXB_ID").toString()==BesidesID) continue;
            RetCount++;
        }
    }

    if(Category==1)//是端子
    {
        QStringList ListShortJumpTerminalInstance=GetShortJumpTerminalInstance(Symb_ID.mid(0,Symb_ID.indexOf(".")));
        RetCount+=ListShortJumpTerminalInstance.count();
    }
    return RetCount;
}

bool IsSourceConn(QString Symb2TermInfo_ID,int Category)
{
    if(Category!=0) return false;
    QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+Symb2TermInfo_ID;
    QuerySymb2TermInfo.exec(StrSql);
    if(QuerySymb2TermInfo.next())
    {
        QSqlQuery QuerySymbol(T_ProjectDatabase);
        StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+QuerySymb2TermInfo.value("Symbol_ID").toString();
        QuerySymbol.exec(StrSql);
        if(QuerySymbol.next())
        {
            if(QuerySymbol.value("SourceConn").toBool()) return true;
        }
    }
    return false;
}

bool IsExecConn(QString Symb2TermInfo_ID,int Category)
{
    if(Category!=0) return false;
    QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+Symb2TermInfo_ID;
    QuerySymb2TermInfo.exec(StrSql);
    if(QuerySymb2TermInfo.next())
    {
        QSqlQuery QuerySymbol(T_ProjectDatabase);
        StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+QuerySymb2TermInfo.value("Symbol_ID").toString();
        QuerySymbol.exec(StrSql);
        if(QuerySymbol.next())
        {
            if(QuerySymbol.value("ExecConn").toBool()) return true;
        }
    }
    return false;
}

//最后一根导线的子块数-1，如果减1后为0则上一根导线-1，以此类推
void UpdateKnownLineValidRoadCnt(QStringList &listLinkRoad,QStringList &KnownLineValidRoadCnt)
{
    //qDebug()<<"UpdateKnownLineValidRoadCnt,KnownLineValidRoadCnt="<<KnownLineValidRoadCnt<<",listLinkRoad="<<listLinkRoad;
    if(listLinkRoad.count()<=0) return;
    if(KnownLineValidRoadCnt.count()<=0) return;
    for(int m=listLinkRoad.count()-1;m>=0;m--)
    {
        if(m==(listLinkRoad.count()-1)) listLinkRoad[m]=listLinkRoad[m].mid(0,listLinkRoad[m].lastIndexOf(",")+1)+"0";
        else  listLinkRoad[m]=listLinkRoad[m].mid(0,listLinkRoad[m].lastIndexOf(",")+1)+QString::number(listLinkRoad[m].split(",").at(2).toInt()-1);
        for(int n=0;n<KnownLineValidRoadCnt.count();n++)
        {
            if(KnownLineValidRoadCnt.at(n).mid(0,KnownLineValidRoadCnt.at(n).lastIndexOf(","))==listLinkRoad.at(m).mid(0,listLinkRoad.at(m).lastIndexOf(",")))
            {
                KnownLineValidRoadCnt[n]=listLinkRoad.at(m);
                break;
            }
        }
        //qDebug()<<"m="<<m<<",ListNodeSpurCount[m]="<<ListNodeSpurCount[m];
        if(listLinkRoad[m].split(",").at(2).toInt()>0) break;
    }
    for(int i=0;i<listLinkRoad.count();i++)
    {
        listLinkRoad[i]=listLinkRoad[i].mid(0,listLinkRoad[i].lastIndexOf(","));
    }
}

QString GetUnitSpurStrBySymbol_ID(QSqlQuery QuerySymbol)
{
    QString UnitSpurStr="";
    int Symbol_ID=QuerySymbol.value("Symbol_ID").toInt();
    //在Symb2TermInfo表中查找Symbol_ID对应的子块端点
    QSqlQuery QueryTermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QString::number(Symbol_ID)+"'");
    QueryTermInfo.exec(temp);
    if(QuerySymbol.value("Designation").toString()!="") UnitSpurStr+=QuerySymbol.value("Designation").toString()+":";
    bool FirstConnNum=true;
    while(QueryTermInfo.next())
    {
        if(FirstConnNum) UnitSpurStr+= QueryTermInfo.value("ConnNum").toString();
        else UnitSpurStr+= " ￤ "+QueryTermInfo.value("ConnNum").toString();
        FirstConnNum=false;
    }
    return UnitSpurStr;
}

int GetSourcePriorBySymbolID(QString SymbolID)
{
    QSqlQuery QuerySymbolSource(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+SymbolID;
    QuerySymbolSource.exec(StrSql);
    if(QuerySymbolSource.next())
    {
        if(!QuerySymbolSource.value("SourceConn").toBool())
            return -1;
        return QuerySymbolSource.value("SourcePrior").toInt();
    }
    return -1;
}

//根据功能子块出现的次数对每一条单链重新排序
void UpdateListFinalLinkInfoOrder(QStringList &ListFinalLinkInfo)
{
    //采用冒泡排序
    while(1)
    {
        bool Flag=false;
        for(int i=0;i<ListFinalLinkInfo.count()-1;i++)
        {
            if(ListFinalLinkInfo.at(i).split(",").at(2)==ListFinalLinkInfo.at(i+1).split(",").at(2))
            {
                if(ListFinalLinkInfo.at(i).split(",").at(4).toInt()<ListFinalLinkInfo.at(i+1).split(",").at(4).toInt())
                {
                    QString tmpstr=ListFinalLinkInfo[i];
                    ListFinalLinkInfo[i]=ListFinalLinkInfo[i+1];
                    ListFinalLinkInfo[i+1]=tmpstr;
                    Flag=true;
                }
            }
        }
        if(!Flag) break;
    }
}

//ListJmplInfo:(SymbolID,Category,LinkID,Checked,Count,+-)
//更新ListJmplInfo中相同功能子块出现的次数
void UpdateJmplInfo(QStringList &ListJmplInfo)
{
    for(int i=0;i<ListJmplInfo.count();i++)
    {
        if(ListJmplInfo.at(i).split(",").at(3)=="false")
        {
            int Count=1;
            QString SymbolID=ListJmplInfo.at(i).split(",").at(0);
            QString Category=ListJmplInfo.at(i).split(",").at(1);
            for(int j=i+1;j<ListJmplInfo.count();j++)
            {
                if((SymbolID==ListJmplInfo.at(j).split(",").at(0))&&(Category==ListJmplInfo.at(j).split(",").at(1)))
                {
                    Count++;
                }
            }
            ListJmplInfo[i]=SymbolID+","+Category+","+ListJmplInfo.at(i).split(",").at(2)+",true,"+QString::number(Count)+","+ListJmplInfo.at(i).split(",").at(5);
            for(int j=i+1;j<ListJmplInfo.count();j++)
            {
                if((SymbolID==ListJmplInfo.at(j).split(",").at(0))&&(Category==ListJmplInfo.at(j).split(",").at(1)))
                {
                    ListJmplInfo[j]=SymbolID+","+Category+","+ListJmplInfo.at(j).split(",").at(2)+",true,"+QString::number(Count)+","+ListJmplInfo.at(j).split(",").at(5);
                }
            }
        }
    }
}

//获取当前功能子块的镜像号次
int GetMirrorIndex(QStringList ListFinalLinkInfo,QString SymbolID,QString Catergory,QString LinkId)
{
    int MirrorIndex=0;

    for(int i=0;i<ListFinalLinkInfo.count();i++)
    {
        if((SymbolID==ListFinalLinkInfo.at(i).split(",").at(0))&&(Catergory==ListFinalLinkInfo.at(i).split(",").at(1))&&(LinkId!=ListFinalLinkInfo.at(i).split(",").at(2)))
        {
            if(CheckIfLinkSpurIsNew(ListFinalLinkInfo,i))  MirrorIndex++;
        }
        if(LinkId==ListFinalLinkInfo.at(i).split(",").at(2)) break;
    }
    return MirrorIndex;
}

//从T语言中提取含有Symbol的Current变量名
//INCLUDE elecPort;
//elecPort ePort_in MAP(1,2) DISCRETE{U:none(0,3),low[3,16),middle[16,26],high(26,30),infinite[30,];I:none(0,3),low[3,16),middle[16,26],high(26,30),infinite[30,];R:none(0,3),low[3,16),middle[16,26],high(26,30),infinite[30,]};
QStringList GetCurrentNameBySymbolID(QString StrTModel,QString SymbolID,QString Catergory,QString MirrorNum)
{
    //qDebug()<<"GetCurrentNameBySymbolID,StrTModel="<<StrTModel;
    QStringList ListTermName=GetTermNameListBySymbolID(SymbolID,Catergory);
    if(ListTermName.count()<1) return {};
    QString StrTermInModel;
    QString ePort_in,ePort_out;
    QStringList ListCandidate;
    //找到MAP(ListTermName.at(0))、MAP(ListTermName.at(1))、MAP(ListTermName.at(0),%,%) MAP(%,ListTermName.at(0),%)、MAP(ListTermName.at(1),%) MAP(%,ListTermName.at(1))对应的信号名称
    for(int i=0;i<2;i++)
    {
        if((i==1)&&(ListTermName.count()==1)) break;
        //qDebug()<<"ListTermName.at(i)="<<ListTermName.at(i);
        QString CpyStrTModel=StrTModel;
        while(CpyStrTModel.contains("elecPort"))
        {
            CpyStrTModel=CpyStrTModel.mid(CpyStrTModel.indexOf("elecPort"),CpyStrTModel.count()-CpyStrTModel.indexOf("elecPort"));
            //qDebug()<<"CpyStrTModel="<<CpyStrTModel;
            int StartIndex,EndIndex;
            StartIndex=CpyStrTModel.indexOf("elecPort")+8;
            EndIndex=CpyStrTModel.indexOf("MAP")-1;
            QString StrMap=CpyStrTModel.mid(CpyStrTModel.indexOf("(")+1,CpyStrTModel.indexOf(")")-CpyStrTModel.indexOf("(")-1);
            //qDebug()<<"StrMap="<<StrMap;
            if(StrMap.remove(" ").split(",").contains(ListTermName.at(i)))
            {
                QString StrCandidate=CpyStrTModel.mid(StartIndex,EndIndex-StartIndex+1).remove(" ");
                //qDebug()<<"StrCandidate="<<StrCandidate;
                ListCandidate.append(StrCandidate);
            }
            CpyStrTModel=CpyStrTModel.mid(CpyStrTModel.indexOf("elecPort")+8,CpyStrTModel.count()-CpyStrTModel.indexOf("elecPort")-8);
        }
    }
    for(QString StrCandidate:ListCandidate)
    {
        if(StrCandidate.contains("in")||StrCandidate.contains("In")||StrCandidate.contains("IN")) ePort_in=StrCandidate;
        if(StrCandidate.contains("out")||StrCandidate.contains("Out")||StrCandidate.contains("OUT")) ePort_out=StrCandidate;
    }
    return {ePort_in,ePort_out};
}

QStringList GetTermNameListBySymbolID(QString SymbolID,QString Catergory)
{
    if(Catergory=="1")  return {"1","2"};//端子
    if(Catergory=="2")  return {"1","2"};//导线
    if(Catergory=="3")  return {"1","2"};//短接片
    //查找SymbolID对应的端口名称
    QStringList ListTermName;
    QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+SymbolID+"'";
    QuerySymb2TermInfo.exec(StrSql);
    while(QuerySymb2TermInfo.next())
    {
        ListTermName.append(QuerySymb2TermInfo.value("ConnNum").toString());
    }
    return ListTermName;
}

//INCLUDE elecPort;
//elecPort ePort_in MAP(1,2) DISCRETE{none(0,3),low[3,16),middle[16,26],high(26,30),infinite[30,∞]};
QString TransformTModelToTModelDiag(QString StrTModel)
{
    while(StrTModel.contains("INCLUDE "))
    {
        QString StrInclude=StrTModel.mid(StrTModel.indexOf("INCLUDE "),StrTModel.count()-StrTModel.indexOf("INCLUDE "));
        StrInclude=StrInclude.mid(0,StrInclude.indexOf(";"));
        StrTModel.remove(StrInclude);
    }
    while(StrTModel.contains("MAP("))
    {
        QString StrMAP=StrTModel.mid(StrTModel.indexOf("MAP("),StrTModel.count()-StrTModel.indexOf("MAP("));
        if(StrMAP.mid(0,StrMAP.indexOf(";")).contains("DISCRETE")) StrMAP=StrMAP.mid(0,StrMAP.indexOf("}")+1);
        else StrMAP=StrMAP.mid(0,StrMAP.indexOf(";"));
        StrTModel.remove(StrMAP);
    }
    return StrTModel;
}

//JmplInfo:(SymbolID,Category,LinkID,Checked,Count,+-)
//镜像Count>1的SymbolID对应的元件TModelDiag描述
void UpdateEquipmentTModelDiag(QStringList ListJmplInfo)
{
    QSqlQuery QueryEquipment(T_ProjectDatabase);
    QSqlQuery QueryJXB(T_ProjectDatabase);
    QString StrSql="UPDATE Equipment SET TModelDiag=:TModelDiag";
    QueryEquipment.prepare(StrSql);
    QueryEquipment.bindValue(":TModelDiag","");
    QueryEquipment.exec();
    StrSql="UPDATE JXB SET TModelDiag=:TModelDiag";
    QueryJXB.prepare(StrSql);
    QueryJXB.bindValue(":TModelDiag","");
    QueryJXB.exec();

    for(int i=0;i<ListJmplInfo.count();i++)
    {
        ListJmplInfo[i]=ListJmplInfo.at(i).split(",").at(0)+","+ListJmplInfo.at(i).split(",").at(1)+","+ListJmplInfo.at(i).split(",").at(2)+",false,"+ListJmplInfo.at(i).split(",").at(4)+","+ListJmplInfo.at(i).split(",").at(5);
    }

    for(int i=0;i<ListJmplInfo.count();i++)
    {
        if(ListJmplInfo.at(i).split(",").at(3)=="false")
        {

            //这里需要区分元件、端子和导线，category分别是0，1，2
            if(ListJmplInfo.at(i).split(",").at(1)=="0")//元件
            {
                int UnitStripID=GetUnitStripIDBySymbolID(ListJmplInfo.at(i).split(",").at(0),ListJmplInfo.at(i).split(",").at(1).toInt());
                StrSql="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(UnitStripID);
                QueryEquipment.exec(StrSql);
                if(QueryEquipment.next())
                {
                    QString StrTModel=QueryEquipment.value("TModel").toString();
                    QString StrTModelDiag=QueryEquipment.value("TModelDiag").toString();
                    if(!CheckIfLinkSpurIsNew(ListJmplInfo,i)) {continue;}
                    //是新分支，如果不是第一次定义该分支则镜像该功能子块
                    bool FirstShow=true;
                    for(int j=0;j<i;j++)
                    {
                        if(CheckIfLinkSpurIsNew(ListJmplInfo,j))
                        {
                            if(ListJmplInfo.at(j).split(",").at(1)!="0") continue;
                            if(ListJmplInfo.at(j).split(",").at(0)==ListJmplInfo.at(i).split(",").at(0))
                            {
                                qDebug()<<"ListJmplInfo="<<ListJmplInfo<<",i="<<i<<":"<<ListJmplInfo.at(i)<<",j="<<j;
                                FirstShow=false;
                                break;
                            }
                        }
                    }
                    StrTModelDiag=TransformTModelToTModelDiag(StrTModel);//StrTModel;
                    /*
                  if(StrTModelDiag=="")
                      StrTModelDiag=StrTModel;
                  else if(!FirstShow)
                  {
                      StrTModelDiag=StrTModel;
                      //查找SymbolID对应的端口名称
                      QStringList ListTermName=GetTermNameListBySymbolID(ListJmplInfo.at(i).split(",").at(0),ListJmplInfo.at(i).split(",").at(1));

                      //找到StrTModelDiag中SymbolID对应的ePort_in和ePort_out

                      QString StrTermInModel;
                      if((ListTermName.count()==1)&&StrTModelDiag.contains("_"+ListTermName.at(0)))
                          StrTermInModel="_"+ListTermName.at(0);
                      else if((ListTermName.count()==2)&&(StrTModelDiag.contains("_"+ListTermName.at(0)+"_"+ListTermName.at(1))||StrTModelDiag.contains("_"+ListTermName.at(1)+"_"+ListTermName.at(0))))
                      {
                          if(StrTModelDiag.contains("_"+ListTermName.at(0)+"_"+ListTermName.at(1)))
                          {
                             StrTermInModel= "_"+ListTermName.at(0)+"_"+ListTermName.at(1);
                          }
                          if(StrTModelDiag.contains("_"+ListTermName.at(1)+"_"+ListTermName.at(0)))
                          {
                              StrTermInModel= "_"+ListTermName.at(1)+"_"+ListTermName.at(0);
                          }
                      }
                      else  continue;
                      StrTModelDiag=MirroredStrOneTime(StrTModelDiag,StrTermInModel);
qDebug()<<"StrTModelDiag="<<StrTModelDiag;
                  }*/
                    //更新TModelDiag
                    StrSql =  "UPDATE Equipment SET TModelDiag=:TModelDiag WHERE Equipment_ID= "+QString::number(UnitStripID);
                    QueryEquipment.prepare(StrSql);
                    QueryEquipment.bindValue(":TModelDiag",StrTModelDiag);
                    QueryEquipment.exec();
                }//end of if(QueryEquipment.next())
                ListJmplInfo[i]=ListJmplInfo.at(i).split(",").at(0)+","+ListJmplInfo.at(i).split(",").at(1)+","+ListJmplInfo.at(i).split(",").at(2)+",true,"+ListJmplInfo.at(i).split(",").at(4)+","+ListJmplInfo.at(i).split(",").at(5);
            }//end of else if(ListJmplInfo.at(i).split(",").at(1)=="0")//器件
            else if(ListJmplInfo.at(i).split(",").at(1)=="2")//导线
            {
                StrSql="SELECT * FROM JXB WHERE JXB_ID= "+ListJmplInfo.at(i).split(",").at(0);
                QueryJXB.exec(StrSql);
                if(QueryJXB.next())
                {
                    QString StrTModel;
                    QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
                    QString StrSql="SELECT * FROM FunctionDefineClass WHERE Level =1 AND FunctionDefineName = '导线新'";
                    QueryFunctionDefineClass.exec(StrSql);
                    if(QueryFunctionDefineClass.next())
                        StrTModel=QueryFunctionDefineClass.value("TModel").toString();

                    QString StrTModelDiag=QueryJXB.value("TModelDiag").toString();
                    if(!CheckIfLinkSpurIsNew(ListJmplInfo,i)) {continue;}
                    //是新分支，如果不是第一次定义该分支则镜像该功能子块
                    bool FirstShow=true;
                    for(int j=0;j<i;j++)
                    {
                        if(CheckIfLinkSpurIsNew(ListJmplInfo,j))
                        {
                            if(ListJmplInfo.at(j).split(",").at(1)!="2") continue;
                            if(ListJmplInfo.at(j).split(",").at(0)==ListJmplInfo.at(i).split(",").at(0))
                            {
                                FirstShow=false;
                                break;
                            }
                        }
                    }
                    StrTModelDiag=TransformTModelToTModelDiag(StrTModel);//StrTModel;
                    /*
                  if(StrTModelDiag=="")
                      StrTModelDiag=StrTModel;
                  else if(!FirstShow)
                  {
                      StrTModelDiag=StrTModel;
                      //查找SymbolID对应的端口名称
                      QStringList ListTermName=GetTermNameListBySymbolID(ListJmplInfo.at(i).split(",").at(0),ListJmplInfo.at(i).split(",").at(1));

                      //找到StrTModelDiag中SymbolID对应的ePort_in和ePort_out

                      QString StrTermInModel;
                      if((ListTermName.count()==1)&&StrTModelDiag.contains("_"+ListTermName.at(0)))
                          StrTermInModel="_"+ListTermName.at(0);
                      else if((ListTermName.count()==2)&&(StrTModelDiag.contains("_"+ListTermName.at(0)+"_"+ListTermName.at(1))||StrTModelDiag.contains("_"+ListTermName.at(1)+"_"+ListTermName.at(0))))
                      {
                          if(StrTModelDiag.contains("_"+ListTermName.at(0)+"_"+ListTermName.at(1)))
                          {
                             StrTermInModel= "_"+ListTermName.at(0)+"_"+ListTermName.at(1);
                          }
                          if(StrTModelDiag.contains("_"+ListTermName.at(1)+"_"+ListTermName.at(0)))
                          {
                              StrTermInModel= "_"+ListTermName.at(1)+"_"+ListTermName.at(0);
                          }
                      }
                      else  continue;
                      StrTModelDiag=MirroredStrOneTime(StrTModelDiag,StrTermInModel);
qDebug()<<"StrTModelDiag="<<StrTModelDiag;
                  }*/
                    //更新TModelDiag
                    StrSql =  "UPDATE JXB SET TModelDiag=:TModelDiag WHERE JXB_ID= "+ListJmplInfo.at(i).split(",").at(0);
                    QueryJXB.prepare(StrSql);
                    QueryJXB.bindValue(":TModelDiag",StrTModelDiag);
                    QueryJXB.exec();
                }//end of if(QueryJXB.next())
                ListJmplInfo[i]=ListJmplInfo.at(i).split(",").at(0)+","+ListJmplInfo.at(i).split(",").at(1)+","+ListJmplInfo.at(i).split(",").at(2)+",true,"+ListJmplInfo.at(i).split(",").at(4)+","+ListJmplInfo.at(i).split(",").at(5);
            }//end of else if(ListJmplInfo.at(i).split(",").at(1)=="2")//导线
        }//end of if((ListJmplInfo.at(i).split(",").at(4)!="1")&&(ListJmplInfo.at(i).split(",").at(3)=="false"))
    }//end of for(int i=0;i<ListJmplInfo.count();i++)
}

QString MirroredStrOneTime(QString StrTModelDiag,QString StrTermInModel)
{
    QString StrMirroredTModelDiag,OriginalStrTermInModel;
    QStringList ListTModelDiag=StrTModelDiag.split(";");
    //qDebug()<<"ListTModelDiag="<<ListTModelDiag;
    int maxmirror=0;
    for(int i=1;i<=10;i++)
    {
        if(StrTModelDiag.contains("_mirror"+QString::number(i))) maxmirror=i;
    }
    if(maxmirror!=0)
    {
        OriginalStrTermInModel=StrTermInModel;
        StrTermInModel=StrTermInModel+"_mirror"+QString::number(maxmirror);
    }
    for(int j=0;j<ListTModelDiag.count();j++)
    {
        if(!ListTModelDiag.at(j).contains(StrTermInModel))
        {
            StrMirroredTModelDiag+=ListTModelDiag.at(j);
            if(j!=(ListTModelDiag.count()-1)) StrMirroredTModelDiag+=";";
            continue;
        }
        //找到ePort_in和ePort_out前面的特殊符号 : { }
        int index=0;
        if(ListTModelDiag.at(j).contains(":")) index=ListTModelDiag.at(j).lastIndexOf(":");
        if(ListTModelDiag.at(j).contains("{"))
        {
            if(ListTModelDiag.at(j).lastIndexOf("{")>index)  index=ListTModelDiag.at(j).lastIndexOf("{");
        }
        if(ListTModelDiag.at(j).contains("}"))
        {
            if(ListTModelDiag.at(j).lastIndexOf("}")>index)  index=ListTModelDiag.at(j).lastIndexOf("}");
        }
        QString StrCopyed=ListTModelDiag.at(j).mid(index+1,ListTModelDiag.at(j).count()-index-1);

        QString StrMirror;
        if(maxmirror==0)
        {
            StrCopyed.replace(StrTermInModel,StrTermInModel+"_mirror0");
            for(int k=0;k<2;k++)
            {
                if(k>0) StrMirror+="\r\n";
                StrMirror+=StrCopyed.replace(StrTermInModel+"_mirror"+QString::number(k),StrTermInModel+"_mirror"+QString::number(k+1))+";";
            }
        }
        else
        {
            StrMirror=StrCopyed;
            StrMirror+=StrCopyed.replace(StrTermInModel,OriginalStrTermInModel+"_mirror"+QString::number(maxmirror+1))+";";
        }
        StrMirroredTModelDiag+=ListTModelDiag.at(j).mid(0,index+1)+StrMirror;
    }//end of for(int j=0;j<ListTModelDiag.count();j++)
    return StrMirroredTModelDiag;
}

QString GetMirroredStr(QString StrTModelDiag,QString StrTermInModel,QString MirrorCount)
{
    //qDebug()<<"StrTModelDiag="<<StrTModelDiag<<",StrTermInModel="<<StrTermInModel<<",MirrorCount="<<MirrorCount;
    if(MirrorCount=="1") return StrTModelDiag;
    QString StrMirroredTModelDiag;
    QStringList ListTModelDiag=StrTModelDiag.split(";");
    //qDebug()<<"ListTModelDiag="<<ListTModelDiag;
    for(int j=0;j<ListTModelDiag.count();j++)
    {
        if(!ListTModelDiag.at(j).contains(StrTermInModel))
        {
            StrMirroredTModelDiag+=ListTModelDiag.at(j);
            if(j!=(ListTModelDiag.count()-1)) StrMirroredTModelDiag+=";";
            continue;
        }
        //找到ePort_in和ePort_out前面的特殊符号 : { }
        int index=0;
        if(ListTModelDiag.at(j).contains(":")) index=ListTModelDiag.at(j).lastIndexOf(":");
        if(ListTModelDiag.at(j).contains("{"))
        {
            if(ListTModelDiag.at(j).lastIndexOf("{")>index)  index=ListTModelDiag.at(j).lastIndexOf("{");
        }
        if(ListTModelDiag.at(j).contains("}"))
        {
            if(ListTModelDiag.at(j).lastIndexOf("}")>index)  index=ListTModelDiag.at(j).lastIndexOf("}");
        }
        QString StrCopyed=ListTModelDiag.at(j).mid(index+1,ListTModelDiag.at(j).count()-index-1);
        StrCopyed.replace(StrTermInModel,StrTermInModel+"_mirror0");
        QString StrMirror;
        for(int k=0;k<MirrorCount.toInt();k++)
        {
            if(k>0) StrMirror+="\r\n";
            StrMirror+=StrCopyed.replace(StrTermInModel+"_mirror"+QString::number(k),StrTermInModel+"_mirror"+QString::number(k+1))+";";
        }
        StrMirroredTModelDiag+=ListTModelDiag.at(j).mid(0,index+1)+StrMirror;
    }//end of for(int j=0;j<ListTModelDiag.count();j++)
    return StrMirroredTModelDiag;
}

void GetHrnAndIniInfoOfComponent(QString &Strhrn,QString &Strini,QString StrSystemDefine)
{
    qDebug()<<"GetHrnAndIniInfoOfComponent,StrSystemDefine="<<StrSystemDefine;
    Strhrn="<mplHarness name=\"test\" version=\"1.00\">";
    Strini="<mplInit name=\"test\" version=\"1.00\">";
    QStringList ListSystemDefine=StrSystemDefine.mid(StrSystemDefine.indexOf("{")+1,StrSystemDefine.count()-StrSystemDefine.indexOf("{")-1).split(";");
    for(QString StrOneComponent:ListSystemDefine)
    {

        StrOneComponent.remove("\r\n");
        if(StrOneComponent.split(" ").count()!=2) continue;
        QString ComponentType=StrOneComponent.split(" ").at(0);
        QString DT=StrOneComponent.split(" ").at(1);
        qDebug()<<"ComponentType="<<ComponentType<<",DT="<<DT;
        if(ComponentType=="NewLine")
        {
            Strhrn+="\r\n<obs name=\"test."+DT+".ePort_in.U\"/>";
            Strhrn+="\r\n<obs name=\"test."+DT+".ePort_in.I\"/>";
            Strhrn+="\r\n<obs name=\"test."+DT+".ePort_in.R\"/>";
            Strhrn+="\r\n<obs name=\"test."+DT+".ePort_out.U\"/>";
            Strhrn+="\r\n<obs name=\"test."+DT+".ePort_out.I\"/>";
            Strhrn+="\r\n<obs name=\"test."+DT+".ePort_out.R\"/>";
            Strini+="\r\n<assign eq=\"test."+DT+".mode=nominal\"/>";
        }
        else if(ComponentType.contains("LINEMirror"))
        {
            int MirrorCount=ComponentType.mid(10,ComponentType.count()-10).toInt();
            for(int i=0;i<MirrorCount;i++)
            {
                Strhrn+="\r\n<obs name=\"test."+DT+".ePort_in_mirror"+QString::number(i+1)+"\"/>";
                Strhrn+="\r\n<obs name=\"test."+DT+".ePort_out_mirror"+QString::number(i+1)+"\"/>";
                Strini+="\r\n<assign eq=\"test."+DT+".mode=nominal\"/>";
            }
        }
        else
        {
            QSqlQuery QueryEquipment(T_ProjectDatabase);
            QString StrSql="SELECT * FROM Equipment WHERE DT = '"+DT+"' AND Type = '"+ComponentType+"'";
            QueryEquipment.exec(StrSql);
            if(QueryEquipment.next())
            {
                if(QueryEquipment.value("Structure").toString()!="")
                {
                    QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
                    for(QString StrStructure:ListStructure)
                    {
                        if(StrStructure.split(",").at(2)=="Observable") Strhrn+="\r\n<obs name=\"test."+DT+"."+StrStructure.split(",").at(0)+"\"/>";
                        if(StrStructure.split(",").at(2)=="Commandable") Strhrn+="\r\n<cmd name=\"test."+DT+"."+StrStructure.split(",").at(0)+"\"/>";
                        if((StrStructure.split(",").at(1)!="undefined")&&(StrStructure.split(",").at(1)!="default"))
                            Strini+="\r\n<assign eq=\"test."+DT+"."+StrStructure.split(",").at(0)+"="+StrStructure.split(",").at(1)+"\" />";
                    }
                }
            }
        }
    }
    Strhrn+="\r\n</mplHarness>";
    Strini+="\r\n</mplInit>";
}

//TModelType=0 返回TModel ; TModelType=1 返回TModelDiag
QString GetTModelOfComponent(QString SymbolID,QString Category,int TModelType)
{
    if(Category=="0")//器件
    {
        int UnitStripID=GetUnitStripIDBySymbolID(SymbolID,Category.toInt());
        QSqlQuery QueryEquipment(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(UnitStripID);
        QueryEquipment.exec(StrSql);
        if(QueryEquipment.next())
        {
            if(TModelType==1) return QueryEquipment.value("TModelDiag").toString();
            else return QueryEquipment.value("TModel").toString();
        }
    }
    else if(Category=="2")//导线
    {
        QSqlQuery QueryJXB(T_ProjectDatabase);
        QString StrSql="SELECT * FROM JXB WHERE JXB_ID = "+SymbolID;
        QueryJXB.exec(StrSql);
        if(QueryJXB.next())
        {
            if(TModelType==1) return QueryJXB.value("TModelDiag").toString();
            else
            {
                QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
                QString StrSql="SELECT * FROM FunctionDefineClass WHERE Level =1 AND FunctionDefineName = '导线新'";
                QueryFunctionDefineClass.exec(StrSql);
                if(QueryFunctionDefineClass.next())
                    return QueryFunctionDefineClass.value("TModel").toString();
            }
        }
    }
    else if(Category=="3")//短接排
    {
        return "class ShortageTerminal{\r\n}";
    }
}

//筛选出子器件
QStringList GetSubComponentList(QString TModelDiag)
{
    TModelDiag=TransformTModelToTModelDiag(TModelDiag);
    QStringList SubComponentList;
    QStringList ListTModelDiag=TModelDiag.split(";");
    for(QString StrOneTModelDiag:ListTModelDiag)
    {
        int index=0;
        if(StrOneTModelDiag.contains(":")) index=StrOneTModelDiag.lastIndexOf(":");
        if(StrOneTModelDiag.contains("{")) index=StrOneTModelDiag.lastIndexOf("{");
        if(StrOneTModelDiag.contains("}")) index=StrOneTModelDiag.lastIndexOf("}");
        QString ValidStrOneTModelDiag;
        if(index!=0) ValidStrOneTModelDiag=StrOneTModelDiag.mid(index+1,StrOneTModelDiag.count()-index-1);
        else ValidStrOneTModelDiag=StrOneTModelDiag;
        QStringList ListTmp=ValidStrOneTModelDiag.remove("\r\n").split(" ");
        //qDebug()<<"ListTmp="<<ListTmp;
        int ValidWordCount=0;
        QString SubModuleDefine;
        for(int i=0;i<ListTmp.count();i++)
        {
            if(ListTmp.at(i)!="")
            {
                if(ValidWordCount==0) SubModuleDefine=ListTmp.at(i);
                if(ValidWordCount==1) SubModuleDefine+=","+ListTmp.at(i);
                ValidWordCount++;
            }
        }
        if(ValidWordCount==2)
        {
            SubModuleDefine.remove("\r\n");
            //不是enum
            QSqlQuery QueryEnumerations(T_LibDatabase);
            QString StrSql="SELECT * FROM Enumerations WHERE EnumName = '"+SubModuleDefine.split(",").at(0)+"'";
            QueryEnumerations.exec(StrSql);
            if(QueryEnumerations.next()) continue;
            QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
            StrSql="SELECT * FROM FunctionDefineClass WHERE TClassName = '"+SubModuleDefine.split(",").at(0)+"'";
            QueryFunctionDefineClass.exec(StrSql);
            if(QueryFunctionDefineClass.next())
            {
                SubComponentList.append(SubModuleDefine);
            }

        }
    }
    return SubComponentList;
}

//添加器件class定义
void UpdateComponentString(QString &StrDefinedComponent,QString SymbolID,QString Category,QString MirrorCount)
{
    int UnitStripID=GetUnitStripIDBySymbolID(SymbolID,Category.toInt());
    if(Category=="0")//器件
    {
        QSqlQuery QueryEquipment(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(UnitStripID);
        QueryEquipment.exec(StrSql);
        if(QueryEquipment.next())
        {
            QString TModelDiag=QueryEquipment.value("TModelDiag").toString();
            if(!StrDefinedComponent.contains(TModelDiag))
            {
                StrDefinedComponent+="\r\n\r\n"+TModelDiag+"\r\n";
            }
            //查看TModelDiag中的子器件是否定义，若未定义则加入StrDefinedComponent
            //qDebug()<<"TModelDiag="<<TModelDiag;
            //找到ePort_in和ePort_out前面的特殊符号 : { }
            QStringList ListTModelDiag=TModelDiag.split(";");
            //qDebug()<<"ListTModelDiag="<<ListTModelDiag;
            QStringList SubComponentList=GetSubComponentList(TModelDiag);
            for(QString StrSubComponent:SubComponentList)
            {
                QString SubModuleTModel;
                QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
                QString StrSql="SELECT * FROM FunctionDefineClass WHERE TClassName = '"+StrSubComponent.split(",").at(0)+"'";
                QueryFunctionDefineClass.exec(StrSql);
                if(QueryFunctionDefineClass.next())
                {
                    SubModuleTModel=QueryFunctionDefineClass.value("TModel").toString();
                    if(!StrDefinedComponent.contains(SubModuleTModel))
                    {
                        StrDefinedComponent+="\r\n\r\n"+SubModuleTModel+"\r\n";
                    }
                }
            }
        }
    }
    else if(Category=="2")//导线
    {
        QSqlQuery QueryJXB(T_ProjectDatabase);
        QString StrSql="SELECT * FROM JXB WHERE JXB_ID = "+SymbolID;
        QueryJXB.exec(StrSql);
        if(QueryJXB.next())
        {
            QString TModelDiag=QueryJXB.value("TModelDiag").toString();
            if(!StrDefinedComponent.contains(TModelDiag))
            {
                StrDefinedComponent+="\r\n\r\n"+TModelDiag+"\r\n";
            }
        }
    }
}

//检查当前链路是否是新的子块
//ListFinalLinkInfo:(SymbolID,Category,LinkID,Checked,Count,+-)
bool CheckIfLinkSpurIsNew(QStringList ListFinalLinkInfo,int Curindex)
{
    QString CurLinkId=ListFinalLinkInfo.at(Curindex).split(",").at(2);
    QStringList ListCompare;
    int linkStartIndex,i;
    for(i=Curindex;i>=0;i--)
    {
        if(ListFinalLinkInfo.at(i).split(",").at(2)!=CurLinkId) break;
        ListCompare.append(ListFinalLinkInfo.at(i));
    }
    linkStartIndex=i+1;
    if(linkStartIndex==0) return true;
    CurLinkId=ListFinalLinkInfo.at(0).split(",").at(2);
    int RelativeIndex=0;
    bool FlagMatch=true;
    for(int j=0;j<linkStartIndex;j++)
    {
        if(ListFinalLinkInfo.at(j).split(",").at(2)!=CurLinkId)
        {
            CurLinkId=ListFinalLinkInfo.at(j).split(",").at(2);
            if(FlagMatch&&(j!=0)) return false;
            RelativeIndex=j;
            FlagMatch=true;
        }
        if((Curindex-linkStartIndex)>=(j-RelativeIndex))
        {
            if(ListFinalLinkInfo.at(j).split(",").at(0)!=ListFinalLinkInfo.at(linkStartIndex+j-RelativeIndex).split(",").at(0)) FlagMatch=false;
            if(ListFinalLinkInfo.at(j).split(",").at(1)!=ListFinalLinkInfo.at(linkStartIndex+j-RelativeIndex).split(",").at(1)) FlagMatch=false;
        }
    }
    if(FlagMatch) return false;
    return true;
}

void CompileStructure(QString StrUnitDesc,QString SubComponentName,QStringList &ListEnumName,QStringList &ListEnumTypeName,QStringList &ListEnumVal,QStringList &ListIniVal,QStringList &ListCmdObsVal)
{
    StrUnitDesc=TransformTModelToTModelDiag(StrUnitDesc);
    QStringList ListGlobalEnum;
    QSqlQuery QueryEnumerations = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr;
    SqlStr = "SELECT * FROM Enumerations";
    QueryEnumerations.exec(SqlStr);
    while(QueryEnumerations.next())
    {
        ListGlobalEnum.append(QueryEnumerations.value("EnumName").toString());
    }
    qDebug()<<"ListGlobalEnum="<<ListGlobalEnum;
    for(QString StrGlobalEnum:ListGlobalEnum)
    {
        while(1)
        {
            if(!StrUnitDesc.contains(StrGlobalEnum+" ")) break;

            SqlStr = "SELECT * FROM Enumerations WHERE EnumName= '"+StrGlobalEnum+"'";
            QueryEnumerations.exec(SqlStr);
            if(QueryEnumerations.next())
            {
                QString StrOneStructure;
                QString StrStructureName=StrUnitDesc.mid(StrUnitDesc.indexOf(StrGlobalEnum+" ")+StrGlobalEnum.length(),StrUnitDesc.length()-StrUnitDesc.indexOf(StrGlobalEnum)-StrGlobalEnum.length()+1);
                StrStructureName=StrStructureName.mid(0,StrStructureName.indexOf(";"));
                StrStructureName.remove(" ");
                StrUnitDesc.remove(StrUnitDesc.indexOf(StrGlobalEnum+" "),StrUnitDesc.indexOf(StrStructureName)+StrStructureName.length()-StrUnitDesc.indexOf(StrGlobalEnum+" "));
                if(SubComponentName!="") StrStructureName=SubComponentName+"."+StrStructureName;
                ListEnumName.append(StrStructureName);
                ListEnumTypeName.append(StrGlobalEnum);

                QString StrInitVal=QueryEnumerations.value("EnumMember").toString()+",undefined,default";
                ListEnumVal.append(StrInitVal.remove(" "));
                ListIniVal.append(QueryEnumerations.value("InitialValue").toString());
                ListCmdObsVal.append(QueryEnumerations.value("CommandOrObservable").toString());
            }
        }
    }
    //添加自定义的Enum
    if(StrUnitDesc.contains("enum"))
    {
        QString StrEnum=StrUnitDesc.mid(StrUnitDesc.indexOf("enum")+4,StrUnitDesc.length()-StrUnitDesc.indexOf("enum")-4+1);
        StrEnum=StrEnum.mid(0,StrEnum.indexOf(";"));
        QString RemovalStr=StrEnum;
        QString StrEnumMember=StrEnum.mid(StrEnum.indexOf("{")+1,StrEnum.indexOf("}")-StrEnum.indexOf("{")-1);
        StrEnum.remove("{"+StrEnumMember+"}").remove(" ");
        StrUnitDesc.remove(RemovalStr);
        while(1)
        {
            if(!StrUnitDesc.contains(StrEnum)) break;
            QString StrStructureName=StrUnitDesc.mid(StrUnitDesc.indexOf(StrEnum)+StrEnum.length(),StrUnitDesc.length()-StrUnitDesc.indexOf(StrEnum)-StrEnum.length()+1);
            StrStructureName=StrStructureName.mid(0,StrStructureName.indexOf(";"));
            StrStructureName.remove(" ");
            StrUnitDesc.remove(StrUnitDesc.indexOf(StrEnum),StrUnitDesc.indexOf(StrStructureName)+StrStructureName.length()-StrUnitDesc.indexOf(StrEnum));

            QString StrInitVal=StrEnumMember+",undefined,default";
            if(SubComponentName!="") StrStructureName=SubComponentName+"."+StrStructureName;
            ListEnumName.append(StrStructureName);
            ListEnumTypeName.append(StrEnum);
            ListEnumVal.append(StrInitVal.remove(" "));
            ListIniVal.append("undefined");
            ListCmdObsVal.append("undefined");
        }
    }
}

void SortTestPoint(QList<TestPoint> &m_TestPoint,int type)
{
    double max_information = 0.0;       //记录test_point中最大的信息熵，用来归一化

    for(int i=0; i<m_TestPoint.count(); i++)
        if(m_TestPoint[i].calculate > max_information)
            max_information = m_TestPoint[i].calculate;

    if(max_information < 1e-6)
        return ;    //max_information太小时就不排序了

    switch (type) {

    case TestPointSort::InformationEntropOnly:
        qSort(m_TestPoint.begin(),m_TestPoint.end(),TestPoint::compareTestPointInformationEntropOnly);
        break;

    case TestPointSort::TestCostOnly:
        qSort(m_TestPoint.begin(),m_TestPoint.end(),TestPoint::compareTestPointTestCostOnly);
        break;

    case TestPointSort::InformationEntropFirst:

        //计算根据偏好的结果
        for(int i=0; i<m_TestPoint.count(); i++)
            m_TestPoint[i].pref_data = m_TestPoint[i].calculate / max_information * information_pref_main/100 + m_TestPoint[i].test_cost * (1-information_pref_main/100);

        qSort(m_TestPoint.begin(),m_TestPoint.end(),TestPoint::compareTestPointPref);
        break;
    case TestPointSort::TestCostFirst:

        //计算根据偏好的结果
        for(int i=0; i<m_TestPoint.count(); i++)
            m_TestPoint[i].pref_data = m_TestPoint[i].calculate / max_information * (1-test_cost_pref_main/100) + m_TestPoint[i].test_cost * test_cost_pref_main/100;

        qSort(m_TestPoint.begin(),m_TestPoint.end(),TestPoint::compareTestPointPref);
        break;

    }
}

//判断当前链路是否是已排除的错误链路，依据是当前导线存在于错误链路列表中且是该列表的最后一个并线节点
bool CheckLinkRoad(QString LineStr,QStringList KnownLineValidRoadCnt)//QList<QStringList>ErrorlistLinkRoad,QList<QList<int>> &ErrorListNodeSpurCount)
{
    for(int i=0;i<KnownLineValidRoadCnt.count();i++)
    {
        if(KnownLineValidRoadCnt.at(i).mid(0,KnownLineValidRoadCnt.at(i).lastIndexOf(","))==LineStr)
        {
            if(KnownLineValidRoadCnt.at(i).split(",").at(2)=="0") return false;
        }
    }
    return true;
}

//查找端口所在功能子块的另一头的端口号
int GetUnitStripOtherSideTerm(QString &Symb2TermInfo_ID,int &Category)
{
    QString DT;
    if(Category==0)
    {
        QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+Symb2TermInfo_ID;
        QuerySymb2TermInfo.exec(StrSql);
        if(QuerySymb2TermInfo.next())
        {
            QString Symbol_ID=QuerySymb2TermInfo.value("Symbol_ID").toString();
            StrSql="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+Symbol_ID+"' AND Symb2TermInfo_ID <> "+Symb2TermInfo_ID;
            QuerySymb2TermInfo.exec(StrSql);
            if(QuerySymb2TermInfo.next())
            {
                Symb2TermInfo_ID=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString();
                Category=0;
                return 0;
            }
        }
    }
    else if(Category==1)
    {
        if(Symb2TermInfo_ID.contains(".1")) Symb2TermInfo_ID=Symb2TermInfo_ID.mid(0,Symb2TermInfo_ID.indexOf("."))+".2";
        else Symb2TermInfo_ID=Symb2TermInfo_ID.mid(0,Symb2TermInfo_ID.indexOf("."))+".1";
        return 0;
    }
    return -1;
}

//TerminalInstanceID1->TerminalInstanceID2
QString GetShortJumpVertualLine(QString TerminalInstanceID1,QString TerminalInstanceID2)
{
    qDebug()<<"GetShortJumpVertualLine,TerminalInstanceID1="<<TerminalInstanceID1<<",TerminalInstanceID2="<<TerminalInstanceID2;
    QString ShortJumpVertualLine;
    QString TerminalStrip_ID1,Designation1,TerminalStrip_ID2,Designation2;
    QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+TerminalInstanceID1;
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        TerminalStrip_ID1=QueryTerminalInstance.value("TerminalStrip_ID").toString();
        Designation1=QueryTerminalInstance.value("Designation").toString();
    }
    SqlStr = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+TerminalInstanceID2;
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        TerminalStrip_ID2=QueryTerminalInstance.value("TerminalStrip_ID").toString();
        Designation2=QueryTerminalInstance.value("Designation").toString();
    }
    if(TerminalStrip_ID1!=TerminalStrip_ID2) return "";
    return TerminalStrip_ID1+":"+Designation1+"-"+Designation2;
}

QStringList GetShortJumpTerminalInstance(QString TerminalInstanceID)
{
    QStringList RetList;
    QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+TerminalInstanceID;
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+QueryTerminalInstance.value("Terminal_ID").toString();
        QueryTerminal.exec(SqlStr);
        if(QueryTerminal.next())
        {
            QString ShortJumper=QueryTerminal.value("ShortJumper").toString();
            if(ShortJumper.contains("*"))
            {
                QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryTerminal.value("TerminalStrip_ID").toString()+"' AND ShortJumper = '"+ShortJumper+"' AND Terminal_ID <> "+QueryTerminal.value("Terminal_ID").toString();
                QuerySearch.exec(SqlStr);
                while(QuerySearch.next())
                {
                    QSqlQuery QuerySearchTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    SqlStr = "SELECT * FROM TerminalInstance WHERE Terminal_ID = '"+QuerySearch.value("Terminal_ID").toString()+"'";
                    QuerySearchTerminalInstance.exec(SqlStr);
                    while(QuerySearchTerminalInstance.next())
                    {
                        RetList.append(QuerySearchTerminalInstance.value("TerminalInstanceID").toString());
                    }
                }
            }//end of if(ShortJumper!="")
        }
    }
    return RetList;
}

QList<QStringList> GetLinkRoadByUnitStripID(QString Symb2TermInfo_ID)//获取端口信号链路
{
    QList<QStringList> listFinalLinkRoad;
    QStringList listLinkRoad={QString::number(GetSymbolIDByTermID(0,Symb2TermInfo_ID))+",0,"+QString::number(GetNodeCountBySymb2TermInfo_ID(Symb2TermInfo_ID,0))};
    QStringList KnownLineValidRoadCnt=listLinkRoad;
    QString DT;
    QString initSymb2TermInfo_ID=Symb2TermInfo_ID;
    int Category=0;
    while(1)
    {
        bool FindTerm=false;
        bool FindExecConn=false;
        bool FindSourceConn=false;
        int NodeSpurCount=0;
        QString StrLinkRoad="";//ID+类型 类型元件为0 端子排为1 导线为2
        //根据Symb2TermInfo_ID找到下一个端口，可以是连线的另一头，也可以是功能子块的另一头，优先找连线的另一头
        //====找连线的另一头====
        QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr;
        //如果是端子，则要查看Symb2TermInfo_ID及所有相同Terminal_ID上的TerminalInstance
        QStringList ListSearchTerm;
        if(Category==1)
        {
            QSqlQuery QuerySearchTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr= "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb2TermInfo_ID.mid(0,Symb2TermInfo_ID.indexOf("."));
            QuerySearchTerminalInstance.exec(SqlStr);
            if(QuerySearchTerminalInstance.next())
            {
                SqlStr="SELECT * FROM TerminalInstance WHERE Terminal_ID = '"+QuerySearchTerminalInstance.value("Terminal_ID").toString()+"'";
                QuerySearchTerminalInstance.exec(SqlStr);
                while(QuerySearchTerminalInstance.next())
                {
                    if(Symb2TermInfo_ID.contains(".1")||Symb2TermInfo_ID.contains(".2"))
                        ListSearchTerm.append(QuerySearchTerminalInstance.value("TerminalInstanceID").toString()+Symb2TermInfo_ID.mid(Symb2TermInfo_ID.indexOf("."),Symb2TermInfo_ID.count()-Symb2TermInfo_ID.indexOf(".")));
                    else
                    {
                        ListSearchTerm.append(QuerySearchTerminalInstance.value("TerminalInstanceID").toString()+".1");
                        ListSearchTerm.append(QuerySearchTerminalInstance.value("TerminalInstanceID").toString()+".2");
                    }
                }
            }
        }
        else if(Category==0)
        {
            ListSearchTerm.append(Symb2TermInfo_ID);
        }

        bool FindLineConnect=false;
        for(QString StrSymb2TermInfo_ID:ListSearchTerm)
        {
            SqlStr= "SELECT * FROM JXB WHERE (Symb1_Category = '"+QString::number(Category)+"' AND Symb1_ID = '"+StrSymb2TermInfo_ID+"') OR (Symb2_Category = '"+QString::number(Category)+"' AND Symb2_ID = '"+StrSymb2TermInfo_ID+"')";
            QueryJXB.exec(SqlStr);
            while(QueryJXB.next())
            {
                //不能往回检索
                bool LinkRepeated=false;
                for(int n=0;n<listLinkRoad.count();n++)
                {
                    if(listLinkRoad.at(n).mid(0,listLinkRoad.at(n).lastIndexOf(","))==(QueryJXB.value("JXB_ID").toString()+",2")) {LinkRepeated=true;break;}
                }
                if(LinkRepeated) continue;
                //判断是否是错误的路径
                if(!CheckLinkRoad(QueryJXB.value("JXB_ID").toString()+",2",KnownLineValidRoadCnt)) continue;
                if((QueryJXB.value("Symb1_Category").toString()==QString::number(Category))&&(QueryJXB.value("Symb1_ID").toString()==StrSymb2TermInfo_ID))
                {
                    Symb2TermInfo_ID=QueryJXB.value("Symb2_ID").toString();
                    Category=QueryJXB.value("Symb2_Category").toInt();
                }
                else
                {
                    Symb2TermInfo_ID=QueryJXB.value("Symb1_ID").toString();
                    Category=QueryJXB.value("Symb1_Category").toInt();
                }
                StrLinkRoad=QueryJXB.value("JXB_ID").toString()+",2";
                qDebug()<<"find line :"<<StrLinkRoad<<"Symb2TermInfo_ID="<<Symb2TermInfo_ID;
                FindLineConnect=true;
                FindTerm=true;
                break;
            }
            if(FindTerm) break;
        }//end of for(QString StrSymb2TermInfo_ID:ListSearchTerm)
        //====找连线的另一头END====

        //如果是源端口则停止搜索
        if(IsSourceConn(Symb2TermInfo_ID,Category))
        {
            qDebug()<<"line term =Source";
            FindSourceConn=true;
        }
        if(IsExecConn(Symb2TermInfo_ID,Category))
        {
            qDebug()<<"line term =Exec";
            FindExecConn=true;
        }

        //====找功能子块另一头=====
        if((!FindLineConnect)&&(!FindSourceConn)&&(!FindExecConn))
        {
            bool CheckOk=false;
            if(Category==0) CheckOk=true;
            if(Category==1)
            {
                if(Symb2TermInfo_ID.contains(".1")||Symb2TermInfo_ID.contains(".2")) CheckOk=true;
            }
            if(CheckOk)
            {
                QString SymbolID;
                if(Category==0) SymbolID=QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID));
                else if(Category==1) SymbolID=QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID));
                qDebug()<<"找功能子块另一头,Symb2TermInfo_ID="<<Symb2TermInfo_ID<<",Category="<<Category<<",SymbolID="<<SymbolID;
                //不能往回检索
                bool LinkRepeated=false;
                for(int n=0;n<listLinkRoad.count();n++)
                {
                    if(listLinkRoad.at(n).mid(0,listLinkRoad.at(n).lastIndexOf(","))==(SymbolID+","+QString::number(Category))) {LinkRepeated=true;break;}
                }
                if(!LinkRepeated)
                {
                    //查找功能子块另一端的端口之前必须检查功能子块
                    if(CheckLinkRoad(SymbolID+","+QString::number(Category),KnownLineValidRoadCnt))
                    {
                        if(GetUnitStripOtherSideTerm(Symb2TermInfo_ID,Category)>=0)
                        {
                            StrLinkRoad=SymbolID+","+QString::number(Category);
                            FindTerm=true;
                        }
                    }
                }
            }
        }
        //====找功能子块另一头END=====

        if((!FindTerm)&&(!FindSourceConn)&&(Category==1)&&(!Symb2TermInfo_ID.contains(".C")))
        {
            if(listLinkRoad.count()>0)
            {
                QString StrLastLink=listLinkRoad.at(listLinkRoad.count()-1);
                //如果已经穿过了端子，则不考虑短接
                if(StrLastLink.mid(StrLastLink.indexOf(",")+1,StrLastLink.lastIndexOf(",")-StrLastLink.indexOf(",")-1)!="1")
                    Symb2TermInfo_ID=Symb2TermInfo_ID.mid(0,Symb2TermInfo_ID.indexOf("."))+".C";
            }
        }
        //====找端子排的短接源头（接入源）
        if((!FindTerm)&&(!FindSourceConn)&&(Category==1)&&(Symb2TermInfo_ID.contains(".C")))
        {
            if(listLinkRoad.count()>0)
            {
                QString StrLastLink=listLinkRoad.at(listLinkRoad.count()-1);
                if(StrLastLink.mid(StrLastLink.indexOf(",")+1,StrLastLink.lastIndexOf(",")-StrLastLink.indexOf(",")-1)!="3")
                {
                    QStringList ListShortJumpInstance=GetShortJumpTerminalInstance(Symb2TermInfo_ID.mid(0,Symb2TermInfo_ID.indexOf(".")));
                    for(QString StrShortJumpInstance:ListShortJumpInstance)
                    {
                        SqlStr = "SELECT * FROM JXB WHERE (Symb1_Category = '1' AND Symb1_ID LIKE '"+StrShortJumpInstance+".%') OR (Symb2_Category = '1' AND Symb2_ID LIKE '"+StrShortJumpInstance+".%')";
                        QueryJXB.exec(SqlStr);
                        if(QueryJXB.next())
                        {
                            QString ShortJumpVertualLine=GetShortJumpVertualLine(Symb2TermInfo_ID.mid(0,Symb2TermInfo_ID.indexOf(".")),StrShortJumpInstance);//Symb2TermInfo_ID.mid(0,Symb2TermInfo_ID.indexOf("."))+"-"+StrShortJumpInstance;//
                            //不能往回检索
                            bool LinkRepeated=false;
                            for(int n=0;n<listLinkRoad.count();n++)
                            {
                                if(listLinkRoad.at(n).mid(0,listLinkRoad.at(n).lastIndexOf(","))==(ShortJumpVertualLine+",3")) {LinkRepeated=true;break;}
                            }
                            if(LinkRepeated) continue;
                            //判断是否是错误的路径
                            if(!CheckLinkRoad(ShortJumpVertualLine+",3",KnownLineValidRoadCnt)) continue;
                            Symb2TermInfo_ID=StrShortJumpInstance;
                            Category=1;
                            StrLinkRoad=ShortJumpVertualLine+",3";
                            qDebug()<<"find 端子排 :"<<StrLinkRoad<<"Symb2TermInfo_ID="<<Symb2TermInfo_ID;
                            FindTerm=true;
                            break;
                        }
                    }
                }//end of if(StrLastLink.mid(StrLastLink.lastIndexOf(",")+1,StrLastLink.count()-StrLastLink.lastIndexOf(",")-1)!="3")
            }//end of if(listLinkRoad.count()>0)
        }
        //====找端子排的短接源头（接入源）END====

        if(FindTerm||FindSourceConn)
        {
            //更新KnownLineValidRoadCnt，listLinkRoad和ListNodeSpurCount
            //查看ListLineItemData.at(3)节点有几条子块,优先采用KnownLineValidRoadCnt中的结果
            bool FindedInKnownLineValidRoadCnt=false;
            for(QString StrKnownLine:KnownLineValidRoadCnt)
            {
                if(StrKnownLine.mid(0,StrKnownLine.lastIndexOf(","))==StrLinkRoad)
                {
                    //NodeSpurCount=StrKnownLine.split(",").at(2).toInt();
                    NodeSpurCount=StrKnownLine.mid(StrKnownLine.lastIndexOf(",")+1,StrKnownLine.count()-StrKnownLine.lastIndexOf(",")-1).toInt();
                    StrLinkRoad=StrKnownLine;
                    FindedInKnownLineValidRoadCnt=true;
                    break;
                }
            }
            if(!FindedInKnownLineValidRoadCnt)
            {
                NodeSpurCount=GetNodeCountBySymb2TermInfo_ID(Symb2TermInfo_ID,Category);
                if(FindSourceConn) NodeSpurCount=1;
                StrLinkRoad+=","+QString::number(NodeSpurCount);
                KnownLineValidRoadCnt.append(StrLinkRoad);
                if(FindSourceConn) KnownLineValidRoadCnt.append(QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID))+","+QString::number(Category)+",1");
            }
            qDebug()<<"StrLinkRoad="<<StrLinkRoad;
            listLinkRoad.append(StrLinkRoad);
            if(FindSourceConn) listLinkRoad.append(QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID))+","+QString::number(Category)+",0");
            qDebug()<<"listLinkRoad="<<listLinkRoad;
        }
        qDebug()<<"FindExecConn="<<FindExecConn<<",FindSourceConn="<<FindSourceConn<<",NodeSpurCount="<<NodeSpurCount<<",FindTerm="<<FindTerm;

        if(Symb2TermInfo_ID==initSymb2TermInfo_ID) break;

        if(FindSourceConn||(!FindTerm))
        {
            //当前的链路不是目标链路，因为没有找到源端口或检索到了终端端口，重新搜索
            Symb2TermInfo_ID=initSymb2TermInfo_ID;
            Category=0;
            UpdateKnownLineValidRoadCnt(listLinkRoad,KnownLineValidRoadCnt);
            if(FindSourceConn)
            {
                listFinalLinkRoad.append(listLinkRoad);
            }
            //else qDebug()<<"错误，找到终端端口";
            qDebug()<<"KnownLineValidRoadCnt="<<KnownLineValidRoadCnt;
            listLinkRoad.clear();
            listLinkRoad.append(QString::number(GetSymbolIDByTermID(0,initSymb2TermInfo_ID))+",0,"+QString::number(GetNodeCountBySymb2TermInfo_ID(initSymb2TermInfo_ID,0)));
        }
    }//end of while(1)
    qDebug()<<"执行器链路检索完成："<<listFinalLinkRoad;
    return listFinalLinkRoad;
}

QString GetLinkRoadBySymbol(int Symbol_ID)//获取信号链路(针对功能子块)
{
    qDebug()<<"GetLinkRoadBySymbol Symbol_ID="<<Symbol_ID;
    QString FinalLinkRoad="";
    //QList<QList<QStringList>> AllLinkRoad;
    //获取功能子块下的端口ID提取信号链路
    QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QuerySymb2TermInfo.exec(StrSql);
    while(QuerySymb2TermInfo.next())
    {
        QList<QStringList> listFinalLinkRoad=GetLinkRoadByUnitStripID(QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString());
        //AllLinkRoad.append(listFinalLinkRoad);

        for(QStringList ListLinkRoad:listFinalLinkRoad)
        {
            FinalLinkRoad+="[";
            for(QString StrLinkRoad:ListLinkRoad)
                FinalLinkRoad+=StrLinkRoad+";";
            FinalLinkRoad.remove(FinalLinkRoad.count()-1,1);
            FinalLinkRoad+="]";
        }
    }


    //存储到数据库中
    QString SqlStr =  "UPDATE Symbol SET LinkRoad=:LinkRoad WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QSqlQuery querySymbol(T_ProjectDatabase);
    querySymbol.prepare(SqlStr);
    querySymbol.bindValue(":LinkRoad",FinalLinkRoad);
    querySymbol.exec();
    return FinalLinkRoad;
}

QStringList GetListSpurLinkRoad(QString StrSpurLinkRoad)
{
    QStringList ListSpurLinkRoad;
    while(StrSpurLinkRoad.contains("[")&&StrSpurLinkRoad.contains("]"))
    {
        ListSpurLinkRoad.append(StrSpurLinkRoad.mid(StrSpurLinkRoad.indexOf("[")+1,StrSpurLinkRoad.indexOf("]")-StrSpurLinkRoad.indexOf("[")-1));
        StrSpurLinkRoad.remove(StrSpurLinkRoad.indexOf("["),StrSpurLinkRoad.indexOf("]")-StrSpurLinkRoad.indexOf("[")+1);
    }
    return ListSpurLinkRoad;
}

//"[220,0;59,2;1:3-1,3;7,2;86,0;6,2;15,0]  [221,0;70,2;1:7-5,3;8,2;16,0][221,0;70,2;1:7-8,3;105,2;90,0]"
//优先使用同一器件输出的源,删除非同一器件的链路
QString UpdateStrLinkRoad(QStringList ListLinkRoad)
{
    qDebug()<<"ListLinkRoad="<<ListLinkRoad;
    QString RetStr;
    for(int i=0;i<ListLinkRoad.count();i++)
    {
        QStringList ListSpurLinkRoad=GetListSpurLinkRoad(ListLinkRoad.at(i));
        qDebug()<<"ListSpurLinkRoad="<<ListSpurLinkRoad;
        for(int j=0;j<ListSpurLinkRoad.count();j++)
        {
            QString StrOneLinkRoad=ListSpurLinkRoad.at(j);
            int Equipment_ID=GetUnitStripIDBySymbolID(StrOneLinkRoad.mid(StrOneLinkRoad.lastIndexOf(";")+1,StrOneLinkRoad.lastIndexOf(",")-StrOneLinkRoad.lastIndexOf(";")-1),0);
            bool CheckUnit=true;
            for(int m=i+1;m<ListLinkRoad.count();m++)
            {
                QStringList ListOtherSpurLinkRoad=GetListSpurLinkRoad(ListLinkRoad.at(m));
                bool FindUnitInOne=false;
                for(int n=0;n<ListOtherSpurLinkRoad.count();n++)
                {
                    StrOneLinkRoad=ListOtherSpurLinkRoad.at(n);
                    if(Equipment_ID==GetUnitStripIDBySymbolID(StrOneLinkRoad.mid(StrOneLinkRoad.lastIndexOf(";")+1,StrOneLinkRoad.lastIndexOf(",")-StrOneLinkRoad.lastIndexOf(";")-1),0))
                    {
                        FindUnitInOne=true;
                        break;
                    }
                }
                if(!FindUnitInOne){CheckUnit=false;break;}
            }
            for(int m=0;m<i;m++)
            {
                QStringList ListOtherSpurLinkRoad=GetListSpurLinkRoad(ListLinkRoad.at(m));
                bool FindUnitInOne=false;
                for(int n=0;n<ListOtherSpurLinkRoad.count();n++)
                {
                    StrOneLinkRoad=ListOtherSpurLinkRoad.at(n);
                    if(Equipment_ID==GetUnitStripIDBySymbolID(StrOneLinkRoad.mid(StrOneLinkRoad.lastIndexOf(";")+1,StrOneLinkRoad.lastIndexOf(",")-StrOneLinkRoad.lastIndexOf(";")-1),0))
                    {
                        FindUnitInOne=true;
                        break;
                    }
                }
                if(!FindUnitInOne){CheckUnit=false;break;}
            }
            if(!CheckUnit) {qDebug()<<"CheckUnit="<<CheckUnit;ListSpurLinkRoad.removeAt(j);j=j-1;}
            else RetStr+="["+ListSpurLinkRoad.at(j)+"]";
        }
    }
    return RetStr;
}

QStringList MakeListFinalLinkInfo(QStringList ListExecSpurID)
{
    QStringList RetListFinalLinkInfo;
    //ListFinalLinkInfo.clear();
    int Linkid=0;
    for(int i=0;i<ListExecSpurID.count();i++)
    {
        Linkid++;
        qDebug()<<"GetLinkRoadBySymbol";
        QString StrLinkRoad;
        QStringList ListLinkRoad;
        for(int j=0;j<ListExecSpurID.at(i).split(",").count();j++)
        {
            //StrLinkRoad+=GetLinkRoadBySymbol(ListExecSpurID.at(i).split(",").at(j).toInt());
            ListLinkRoad.append(GetLinkRoadBySymbol(ListExecSpurID.at(i).split(",").at(j).toInt()));
        }
        StrLinkRoad=UpdateStrLinkRoad(ListLinkRoad);
        qDebug()<<"StrLinkRoad="<<StrLinkRoad;
        //StrLinkRoad:"[146,0;41,2;15,1;64,2;205,0;15,2;123,0;95,2;98,0][147,0;39,2;13,1;62,2;203,0;13,2;121,0;93,2;99,0][151,0;40,2;14,1;63,2;204,0;14,2;122,0;94,2;103,0]"

        QStringList ListAllLinkRoad;
        while(1)
        {
            if(!(StrLinkRoad.contains("[")&&StrLinkRoad.contains("]"))) break;
            int index1=StrLinkRoad.indexOf("[");
            int index2=StrLinkRoad.indexOf("]");
            ListAllLinkRoad.append(StrLinkRoad.mid(index1+1,index2-index1-1));
            StrLinkRoad=StrLinkRoad.mid(index2+1,StrLinkRoad.count()-index2-1);
        }


        //根据GetLinkRoadBySymbol得到的链路查看是否有关联的执行器，若有的话则将其添加到ListExecSpurID中去
        for(QString StrOneLinkRoad:ListAllLinkRoad)
        {
            QStringList ListOneLinkSpur=StrOneLinkRoad.split(";");
            for(QString StrOneSpur:ListOneLinkSpur)
            {
                if(StrOneSpur.split(",").count()==2)
                {
                    if(StrOneSpur.split(",").at(1)=="0")
                    {
                        //查看是否有关联的执行器
                        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        QString StrSql="SELECT * FROM Symbol WHERE Symbol_ID = "+StrOneSpur.split(",").at(0);
                        QuerySymbol.exec(StrSql);
                        if(QuerySymbol.next())
                        {
                            if(QuerySymbol.value("InterConnect").toString()!="")//(94,95);(109,110)
                            {
                                QStringList ListInterConnect=QuerySymbol.value("InterConnect").toString().split(";");
                                for(QString StrInterConnect:ListInterConnect)
                                {
                                    //查看ListExecSpurID中是否包含StrInterConnect的排列
                                    StrInterConnect.remove("(").remove(")");
                                    if(StrInterConnect.split(",").count()==1)
                                        ListExecSpurID.append(StrInterConnect);
                                    else if(StrInterConnect.split(",").count()==2)
                                    {
                                        bool CheckOk=true;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(0)+","+StrInterConnect.split(",").at(1))) CheckOk=false;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(1)+","+StrInterConnect.split(",").at(0))) CheckOk=false;
                                        if(CheckOk)  ListExecSpurID.append(StrInterConnect);
                                    }
                                    else if(StrInterConnect.split(",").count()==3)
                                    {
                                        bool CheckOk=true;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(0)+","+StrInterConnect.split(",").at(1)+","+StrInterConnect.split(",").at(2))) CheckOk=false;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(0)+","+StrInterConnect.split(",").at(2)+","+StrInterConnect.split(",").at(1))) CheckOk=false;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(1)+","+StrInterConnect.split(",").at(0)+","+StrInterConnect.split(",").at(2))) CheckOk=false;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(1)+","+StrInterConnect.split(",").at(2)+","+StrInterConnect.split(",").at(0))) CheckOk=false;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(2)+","+StrInterConnect.split(",").at(0)+","+StrInterConnect.split(",").at(1))) CheckOk=false;
                                        if(ListExecSpurID.contains(StrInterConnect.split(",").at(2)+","+StrInterConnect.split(",").at(1)+","+StrInterConnect.split(",").at(0))) CheckOk=false;
                                        if(CheckOk)  ListExecSpurID.append(StrInterConnect);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        qDebug()<<"update ListExecSpurID="<<ListExecSpurID;
        qDebug()<<"while(1) ListAllLinkRoad="<<ListAllLinkRoad;
        if(ListAllLinkRoad.count()>=2)//正负两条链路
        {
            //将优先级高的链路放在ListAllLinkRoad前面
            for(int j=0;j<ListAllLinkRoad.count();j++)
            {
                QString StrSourceConn=ListAllLinkRoad.at(j).split(";").last();
                qDebug()<<"StrSourceConn="<<StrSourceConn;
                if((StrSourceConn.split(",").count()!=2)||(StrSourceConn.split(",").at(1)!="0"))
                {
                    ListAllLinkRoad.removeAt(j);
                    continue;
                }
                int SourcePrior=GetSourcePriorBySymbolID(StrSourceConn.split(",").at(0));
                qDebug()<<"SourcePrior="<<SourcePrior;
                if(SourcePrior<0)
                {
                    ListAllLinkRoad.removeAt(j);
                    continue;
                }
                for(int k=j;k<ListAllLinkRoad.count();k++)
                {
                    QString StrCompareSourceConn=ListAllLinkRoad.at(k).split(";").last();
                    if((StrCompareSourceConn.split(",").count()!=2)||(StrCompareSourceConn.split(",").at(1)!="0")) continue;
                    int CompareSourcePrior=GetSourcePriorBySymbolID(StrCompareSourceConn.split(",").at(0));
                    if(SourcePrior>CompareSourcePrior)//数字小的优先级高
                    {
                        //j k 互换
                        QString tmpStr=ListAllLinkRoad[j];
                        ListAllLinkRoad[j]=ListAllLinkRoad[k];
                        ListAllLinkRoad[k]=tmpStr;
                    }
                }
                qDebug()<<"ListAllLinkRoad="<<ListAllLinkRoad;
            }//将优先级高的链路放在ListAllLinkRoad前面
            qDebug()<<"排序完成 ListAllLinkRoad="<<ListAllLinkRoad;
            //根据ListAllLinkRoad生成诊断文件CurProjectName.jmpl
            for(int m=0;m<ListAllLinkRoad.count();m++)
            {
                QStringList ListLinkRoad=ListAllLinkRoad.at(m).split(";");
                if(m==0) RetListFinalLinkInfo.append(ListLinkRoad.at(ListLinkRoad.count()-1)+","+QString::number(Linkid)+",false,1,0");
                for(int k=ListLinkRoad.count()-2;k>0;k--)
                    RetListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1,"+QString::number(m+1));
            }
            /*
            QStringList ListLinkRoad=ListAllLinkRoad.at(0).split(";");
            RetListFinalLinkInfo.append(ListLinkRoad.at(ListLinkRoad.count()-1)+","+QString::number(Linkid)+",false,1,0");

            for(int k=ListLinkRoad.count()-2;k>=0;k--)
            {
                //if((j>0)&&(k==(ListLinkRoad.count()-1))) continue;//源只统计一次
                if(k==0) continue;//执行器只统计一次
                //if((j!=(ListAllLinkRoad.count()-1))&&(k==0)) continue;//执行器只统计一次
                RetListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1,1");
            }
            ListLinkRoad=ListAllLinkRoad.at(1).split(";");
            for(int k=ListLinkRoad.count()-1;k>0;k--)
            {
                if(k==(ListLinkRoad.count()-1)) continue;//源只统计一次
                RetListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1,2");
            }*/
            RetListFinalLinkInfo.append(ListAllLinkRoad.at(ListAllLinkRoad.count()-1).split(";").at(0)+","+QString::number(Linkid)+",false,1,3");
            /*
                for(int j=0;j<ListAllLinkRoad.count();j++)
                {
                    QStringList ListLinkRoad=ListAllLinkRoad.at(j).split(";");
                    for(int k=ListLinkRoad.count()-1;k>=0;k--)
                    {
                        if((j>0)&&(k==(ListLinkRoad.count()-1))) continue;//源只统计一次
                        if((j!=(ListAllLinkRoad.count()-1))&&(k==0)) continue;//执行器只统计一次
                        ListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1");
                    }
                }
*/
        }//end of if(ListAllLinkRoad.count()==2)//正负两条链路
    }//end of for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    //qDebug()<<"ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateJmplInfo(RetListFinalLinkInfo);//更新ListJmplInfo中相同功能子块出现的次数
    qDebug()<<"重新排序前a，RetListFinalLinkInfo="<<RetListFinalLinkInfo;
    UpdateListFinalLinkInfoOrder(RetListFinalLinkInfo);//根据功能子块出现的次数对每一条单链重新排序
    return RetListFinalLinkInfo;
}

QString GetSubUnitBySymbolID(QString SymbolID,QString Catergory)
{
    QStringList TermNameList=GetTermNameListBySymbolID(SymbolID,Catergory);
    if(Catergory=="0")
    {
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+SymbolID;
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                QStringList SubComponentList=GetSubComponentList(QueryEquipment.value("TModel").toString());
                if(SubComponentList.count()==0)
                    return QueryEquipment.value("DT").toString();
                else
                {
                    //这里要找到与功能子块对应的Sub器件，只能根据TModel来解析
                    for(int i=0;i<SubComponentList.count();i++)
                    {
                        if(TermNameList.count()==2)
                        {
                            QString TModel=QueryEquipment.value("TModel").toString();
                            if(TModel.remove(" ").contains("_"+TermNameList.at(0)+"_"+TermNameList.at(1)+"="+SubComponentList.at(i).split(",").at(1)))
                                return QueryEquipment.value("DT").toString()+"."+SubComponentList.at(i).split(",").at(1);
                            if(TModel.remove(" ").contains("_"+TermNameList.at(1)+"_"+TermNameList.at(0)+"="+SubComponentList.at(i).split(",").at(1)))
                                return QueryEquipment.value("DT").toString()+"."+SubComponentList.at(i).split(",").at(1);
                        }
                    }
                }
            }
        }
    }

}

bool PointsIsCovered(IMxDrawPoint *Point1,IMxDrawPoint *Point2)
{
    if((Point1==nullptr)||(Point2==nullptr)) return false;
    if(fabs(Point1->x()-Point2->x())>0.1) return false;
    if(fabs(Point1->y()-Point2->y())>0.1) return false;
    return true;
}

bool CheckExistTerminal(IMxDrawPoint *Point,int Page_ID)
{
    QString Coordination=QString::number(Point->x(),'f',0)+".000000,"+QString::number(Point->y(),'f',0)+".000000,0.000000";
    QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE Page_ID = '"+QString::number(Page_ID)+"' AND Coordinate = '"+Coordination+"'";
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        return true;
    }
    return false;
}

QStringList GetListTermNameByTModel(QString TModel,QString CurrentInOutName)
{
    QString CpyStrTModel=TModel;
    while(CpyStrTModel.contains("elecPort"))
    {
        CpyStrTModel=CpyStrTModel.mid(CpyStrTModel.indexOf("elecPort"),CpyStrTModel.count()-CpyStrTModel.indexOf("elecPort"));
        //qDebug()<<"CpyStrTModel="<<CpyStrTModel;
        int StartIndex,EndIndex;
        StartIndex=CpyStrTModel.indexOf("elecPort")+8;
        EndIndex=CpyStrTModel.indexOf("MAP")-1;
        QString StrMap=CpyStrTModel.mid(CpyStrTModel.indexOf("(")+1,CpyStrTModel.indexOf(")")-CpyStrTModel.indexOf("(")-1);
        //qDebug()<<"StrMap="<<StrMap;
        QString StrCandidate=CpyStrTModel.mid(StartIndex,EndIndex-StartIndex+1).remove(" ");
        if(StrCandidate==CurrentInOutName)
        {
            return StrMap.remove(" ").split(",");
        }
        CpyStrTModel=CpyStrTModel.mid(CpyStrTModel.indexOf("elecPort")+8,CpyStrTModel.count()-CpyStrTModel.indexOf("elecPort")-8);
    }
    return {};
}

//elecPort ePort_in MAP(1,2) DISCRETE{U:none(0,3),low[3,16),middle[16,26],high(26,30),infinite[30,];I:none(0,0.01),low[0.01,0.5),middle[0.5,2],high(2,5),infinite[5,];R:none(0,0.1),low[0.1,8),middle[8,52],high(52,100),infinite[100,]};
QString GetRangeValByTModel(QString TModel,QString CurrentInOutName,QString Val,QString Type)
{
    qDebug()<<"GetRangeValByTModel,TModel="<<TModel<<",CurrentInOutName="<<CurrentInOutName<<",Val="<<Val<<",Type="<<Type;
    if(!StrIsDouble(Val)) return "";
    QString CpyStrTModel=TModel;
    while(CpyStrTModel.contains("elecPort"))
    {
        CpyStrTModel=CpyStrTModel.mid(CpyStrTModel.indexOf("elecPort"),CpyStrTModel.count()-CpyStrTModel.indexOf("elecPort"));
        //qDebug()<<"CpyStrTModel="<<CpyStrTModel;
        int StartIndex,EndIndex,DisIndex;
        StartIndex=CpyStrTModel.indexOf("elecPort")+8;
        EndIndex=CpyStrTModel.indexOf("MAP")-1;
        DisIndex=CpyStrTModel.indexOf("DISCRETE");
        //QString StrMap=CpyStrTModel.mid(CpyStrTModel.indexOf("(")+1,CpyStrTModel.indexOf(")")-CpyStrTModel.indexOf("(")-1);
        //qDebug()<<"StrMap="<<StrMap;
        QString StrCandidate=CpyStrTModel.mid(StartIndex,EndIndex-StartIndex+1).remove(" ");
        if(StrCandidate==CurrentInOutName)
        {
            QString StrDISCRETE=CpyStrTModel.mid(DisIndex,CpyStrTModel.count()-DisIndex);
            StrDISCRETE=StrDISCRETE.mid(StrDISCRETE.indexOf("{")+1,StrDISCRETE.indexOf("}")-StrDISCRETE.indexOf("{")-1);
            if(Type=="电压")
            {
                if(!StrDISCRETE.contains("U:")) return "";
                StrDISCRETE=StrDISCRETE.mid(StrDISCRETE.indexOf("U:"),StrDISCRETE.count()-StrDISCRETE.indexOf("U:"));
            }
            else if(Type=="电流")
            {
                if(!StrDISCRETE.contains("I:")) return "";
                StrDISCRETE=StrDISCRETE.mid(StrDISCRETE.indexOf("U:"),StrDISCRETE.count()-StrDISCRETE.indexOf("I:"));
            }
            if(Type=="电阻")
            {
                if(!StrDISCRETE.contains("R:")) return "";
                StrDISCRETE=StrDISCRETE.mid(StrDISCRETE.indexOf("U:"),StrDISCRETE.count()-StrDISCRETE.indexOf("R:"));
            }
            qDebug()<<"StrDISCRETE="<<StrDISCRETE;
            QString StrRange;
            for(int i=0;i<5;i++)
            {
                qDebug()<<"i="<<i;
                if(i==0)
                {
                    if(!StrDISCRETE.contains("none")) continue;
                    StrRange=StrDISCRETE.mid(StrDISCRETE.indexOf("none"),StrDISCRETE.count()-StrDISCRETE.indexOf("none"));
                }
                if(i==1)
                {
                    if(!StrDISCRETE.contains("low")) continue;
                    StrRange=StrDISCRETE.mid(StrDISCRETE.indexOf("low"),StrDISCRETE.count()-StrDISCRETE.indexOf("none"));
                }
                if(i==2)
                {
                    if(!StrDISCRETE.contains("middle")) continue;
                    StrRange=StrDISCRETE.mid(StrDISCRETE.indexOf("middle"),StrDISCRETE.count()-StrDISCRETE.indexOf("none"));
                }
                if(i==3)
                {
                    if(!StrDISCRETE.contains("high")) continue;
                    StrRange=StrDISCRETE.mid(StrDISCRETE.indexOf("high"),StrDISCRETE.count()-StrDISCRETE.indexOf("none"));
                }
                if(i==4)
                {
                    if(!StrDISCRETE.contains("infinite")) continue;
                    StrRange=StrDISCRETE.mid(StrDISCRETE.indexOf("infinite"),StrDISCRETE.count()-StrDISCRETE.indexOf("none"));
                }
                qDebug()<<"StrRange="<<StrRange;
                int LeftIndex,RightIndex;
                int index1;
                if(StrRange.contains("(")) index1=StrRange.indexOf("(");
                else index1=1000;
                int index2;
                if(StrRange.contains("[")) index2=StrRange.indexOf("[");
                else index2=1000;
                if(index1<=index2) LeftIndex=index1;
                else LeftIndex=index2;
                StrRange=StrRange.mid(LeftIndex,StrRange.count()-LeftIndex);

                if(StrRange.contains(")")) index1=StrRange.indexOf(")");
                else index1=1000;
                if(StrRange.contains("]")) index2=StrRange.indexOf("]");
                else index2=1000;
                if(index1<=index2) RightIndex=index1;
                else RightIndex=index2;
                StrRange=StrRange.mid(0,RightIndex+1);
                qDebug()<<"StrRange="<<StrRange;
                if(StrRange.split(",").count()==2)
                {
                    QString minVal=StrRange.mid(1,StrRange.indexOf(",")-1);
                    if((!StrIsDouble(minVal))&&(minVal!="")) return "";
                    QString maxVal=StrRange.mid(StrRange.indexOf(",")+1,StrRange.count()-StrRange.indexOf(",")-2);
                    if((!StrIsDouble(maxVal))&&(maxVal!="")) return "";
                    bool Check=true;
                    if(StrRange.at(0)=="(") { if((minVal!="")&&(Val.toDouble()<=minVal.toDouble())) Check=false;}
                    if(StrRange.at(0)=="[") { if((minVal!="")&&(Val.toDouble()<minVal.toDouble())) Check=false;}
                    if(StrRange.at(StrRange.count()-1)==")") { if((maxVal!="")&&(Val.toDouble()>=maxVal.toDouble())) Check=false;}
                    if(StrRange.at(StrRange.count()-1)=="]") { if((maxVal!="")&&(Val.toDouble()>maxVal.toDouble())) Check=false;}
                    qDebug()<<"Check="<<Check;
                    if(Check)
                    {
                        if(i==0) return "none";
                        else if(i==1) return "low";
                        else if(i==2) return "middle";
                        else if(i==3) return "high";
                        else if(i==4) return "infinite";
                    }
                }
            }//end of for(int i=0;i<5;i++)
        }//end of if(StrCandidate==CurrentInOutName)
        CpyStrTModel=CpyStrTModel.mid(CpyStrTModel.indexOf("elecPort")+8,CpyStrTModel.count()-CpyStrTModel.indexOf("elecPort")-8);
    }
    return "";
}

/*
函数功能：通过Qt实现在一个目录下查找指定文件
参数：strFilePath,要搜索的路径
filename,要搜索的文件名
*/
QString FindLocalFileFromPath(const QString &strFilePath, const QString filename)
{
    //QStringList m_Filelist;//找到的文件存入此队列
    if (strFilePath.isEmpty() || filename.isEmpty())
    {
        return "";
    }

    QDir dir;
    QStringList filters;

    filters << filename;//过滤条件，可以添加多个选项，可以匹配文件后缀等。我这里只是找指定文件
    dir.setPath(strFilePath);
    dir.setNameFilters(filters);//添加过滤器
    //QDirIterator 此类可以很容易的返回指定目录的所有文件及文件夹，可以再递归遍历，也可以自动查找指定的文件
    QDirIterator iter(dir,QDirIterator::Subdirectories);

    while (iter.hasNext())
    {
        iter.next();
        QFileInfo info=iter.fileInfo();
        if (info.isFile())
        {
            return info.absoluteFilePath();
        }
    }
    return "";
}
