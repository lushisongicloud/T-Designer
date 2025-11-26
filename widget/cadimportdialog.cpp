#include "cadimportdialog.h"
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QDialogButtonBox>
#include <QHeaderView>
#include <QMessageBox>
#include <QFile>
#include <QSet>
#include <QMap>
#include <QCheckBox>

using namespace MxDrawXLib;

namespace {
constexpr const char *kMxDrawClsid = "{74a777f8-7a8f-4e7c-af47-7074828086e2}";
}

CadImportDialog::CadImportDialog(const QString &sourcePath,
                                 std::function<bool(const QString &, QString *, int *)> pagePreparation,
                                 QWidget *parent)
    : QDialog(parent),
      m_sourcePath(sourcePath),
      m_preparePage(std::move(pagePreparation))
{
    setWindowTitle("导入图纸");
    resize(980, 720);
    buildUi();
    loadDrawing();
    scanCandidates();
}

CadImportDialog::~CadImportDialog()
{
    clearHighlights();
}

void CadImportDialog::buildUi()
{
    m_axWidget = new QAxWidget(this);
    m_axWidget->setControl(kMxDrawClsid);
    m_axWidget->setProperty("ShowCommandWindow", false);
    m_axWidget->setProperty("ShowMenuBar", false);
    m_axWidget->setProperty("ShowToolBars", false);
    m_axWidget->setProperty("ShowStatusBar", false);
    m_axWidget->setProperty("ShowModelBar", false);
    m_axWidget->setProperty("ShowPropertyWindow", false);
    m_axWidget->setProperty("ShowRulerWindow", false);
    m_axWidget->setMinimumHeight(420);

    m_table = new QTableWidget(this);
    m_table->setColumnCount(4);
    QStringList headers;
    headers << "序号" << "DbId" << "标识/型号" << "块名";
    m_table->setHorizontalHeaderLabels(headers);
    m_table->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);
    m_table->setSelectionBehavior(QAbstractItemView::SelectRows);
    m_table->setSelectionMode(QAbstractItemView::SingleSelection);
    m_table->setEditTriggers(QAbstractItemView::NoEditTriggers);
    connect(m_table, &QTableWidget::itemSelectionChanged, this, &CadImportDialog::onSelectionChanged);

    m_statusLabel = new QLabel(this);
    m_rescanButton = new QPushButton("重新识别", this);
    connect(m_rescanButton, &QPushButton::clicked, this, &CadImportDialog::onRescan);

    m_importAllCheck = new QCheckBox("导入所有", this);
    m_importAllCheck->setChecked(false);
    connect(m_importAllCheck, &QCheckBox::stateChanged, this, &CadImportDialog::onImportAllToggled);

    QHBoxLayout *statusLayout = new QHBoxLayout;
    statusLayout->addWidget(m_statusLabel);
    statusLayout->addStretch();
    statusLayout->addWidget(m_importAllCheck);
    statusLayout->addWidget(m_rescanButton);

    QDialogButtonBox *buttonBox = new QDialogButtonBox(QDialogButtonBox::Ok | QDialogButtonBox::Cancel, this);
    connect(buttonBox, &QDialogButtonBox::accepted, this, &CadImportDialog::accept);
    connect(buttonBox, &QDialogButtonBox::rejected, this, &CadImportDialog::reject);

    QVBoxLayout *rootLayout = new QVBoxLayout(this);
    rootLayout->addWidget(m_axWidget, 5);
    rootLayout->addWidget(m_table, 2);
    rootLayout->addLayout(statusLayout);
    rootLayout->addWidget(buttonBox);

    setLayout(rootLayout);
}

void CadImportDialog::loadDrawing()
{
    if (!QFile::exists(m_sourcePath)) {
        QMessageBox::warning(this, "提示", "DWG 文件不存在，无法打开。");
        return;
    }
    m_axWidget->dynamicCall("OpenDwgFile(QString)", m_sourcePath);
    m_axWidget->dynamicCall("ZoomAll()");
}

void CadImportDialog::clearHighlights()
{
    for (const QString &h : m_overlayHandles) {
        if (!m_axWidget)
            continue;
        IMxDrawEntity *ent = (IMxDrawEntity *)m_axWidget->querySubObject("HandleToObject(const QString)", h);
        if (ent)
            ent->dynamicCall("Erase()");
    }
    m_overlayHandles.clear();

    for (const Candidate &c : m_candidates) {
        if (!m_axWidget)
            continue;
        IMxDrawEntity *ent = (IMxDrawEntity *)m_axWidget->querySubObject("HandleToObject(const QString)", c.handle);
        if (ent)
            ent->dynamicCall("Highlight(bool)", false);
    }
}

void CadImportDialog::scanCandidates()
{
    clearHighlights();
    m_candidates.clear();
    m_table->setRowCount(0);

    if (!m_axWidget)
        return;

    IMxDrawSelectionSet *ss = (IMxDrawSelectionSet *)m_axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter = (IMxDrawResbuf *)m_axWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("INSERT", 5020);
    ss->dynamicCall("AllSelect(QVariant)", filter->asVariant());
    int count = ss->dynamicCall("Count()").toInt();

    for (int i = 0; i < count; ++i) {
        IMxDrawEntity *ent = (IMxDrawEntity *)ss->querySubObject("Item(int)", i);
        if (!ent)
            continue;
        if (EntyIsErased(m_axWidget, ent))
            continue;
        if (ent->dynamicCall("ObjectName()").toString() != "McDbBlockReference")
            continue;
        QString dbId = ent->dynamicCall("GetxDataString2(QString,int)", "DbId", 0).toString();
        if (dbId.isEmpty())
            dbId = ent->dynamicCall("GetxDataString2(QString,int)", "DbID", 0).toString();
        if (dbId.isEmpty())
            continue;
        Candidate c;
        c.handle = ent->dynamicCall("handle()").toString();
        c.dbId = dbId;
        c.designation = ent->dynamicCall("GetxDataString2(QString,int)", "Designation", 0).toString();
        c.blockName = ent->dynamicCall("GetBlockName()").toString();
        if (c.designation.trimmed().isEmpty()) {
            QString attr = GetBlockAttrTextString((IMxDrawBlockReference *)ent, "设备标识符(显示)");
            if (!attr.trimmed().isEmpty())
                c.designation = attr;
        }
        c.partCode = ent->dynamicCall("GetxDataString2(QString,int)", "PartCode", 0).toString();
        if (c.partCode.trimmed().isEmpty()) {
            QString attr = GetBlockAttrTextString((IMxDrawBlockReference *)ent, "物料编码");
            if (attr.trimmed().isEmpty())
                attr = GetBlockAttrTextString((IMxDrawBlockReference *)ent, "编号");
            if (!attr.trimmed().isEmpty())
                c.partCode = attr;
        }
        m_candidates.append(c);

        int row = m_table->rowCount();
        m_table->insertRow(row);
        m_table->setItem(row, 0, new QTableWidgetItem(QString::number(row + 1)));
        m_table->setItem(row, 1, new QTableWidgetItem(c.dbId));
        m_table->setItem(row, 2, new QTableWidgetItem(c.designation));
        m_table->setItem(row, 3, new QTableWidgetItem(c.blockName + (c.partCode.isEmpty() ? "" : " (" + c.partCode + ")")));
    }

    m_statusLabel->setText(QString("已识别元件：%1").arg(m_candidates.size()));
    m_axWidget->dynamicCall("ZoomAll()");
    if (!m_candidates.isEmpty()) {
        m_table->selectRow(0);
        onSelectionChanged();
    }
    // 根据“导入所有”切换块名列显示
    m_table->setColumnHidden(3, !m_importAllCheck->isChecked());
}

void CadImportDialog::drawHighlightBox(IMxDrawBlockReference *blk)
{
    if (!blk || !m_axWidget)
        return;
    IMxDrawPoint *pos = (IMxDrawPoint *)blk->querySubObject("Position()");
    double cx = pos ? pos->x() : 0.0;
    double cy = pos ? pos->y() : 0.0;
    // 自适应方框：尝试获取块的几何范围，失败时使用默认尺寸
    double minx = cx - 10.0;
    double maxx = cx + 10.0;
    double miny = cy - 10.0;
    double maxy = cy + 10.0;

    QAxObject *geom = blk->querySubObject("GetGeomExtents");
    if (geom) {
        IMxDrawPoint *minPt = (IMxDrawPoint *)geom->querySubObject("MinPoint");
        IMxDrawPoint *maxPt = (IMxDrawPoint *)geom->querySubObject("MaxPoint");
        if (minPt && maxPt) {
            minx = minPt->x() - 2.0;
            miny = minPt->y() - 2.0;
            maxx = maxPt->x() + 2.0;
            maxy = maxPt->y() + 2.0;
        }
    }

    m_axWidget->dynamicCall("PathMoveTo(double,double)", minx, miny);
    m_axWidget->dynamicCall("PathLineTo(double,double)", maxx, miny);
    m_axWidget->dynamicCall("PathLineTo(double,double)", maxx, maxy);
    m_axWidget->dynamicCall("PathLineTo(double,double)", minx, maxy);
    m_axWidget->dynamicCall("PathLineTo(double,double)", minx, miny);
    qlonglong lID = m_axWidget->dynamicCall("DrawPathToPolyline()", QVariantList()).toLongLong();
    IMxDrawPolyline *poly = (IMxDrawPolyline *)m_axWidget->querySubObject("ObjectIdToObject(const qlonglong)", lID);
    if (poly) {
        poly->dynamicCall("setColorIndex(int)", McColor::mcRed);
        poly->dynamicCall("SetLineType(QString)", "Continuous");
        poly->dynamicCall("SetLineWeight(int)", 30);
        m_overlayHandles.append(poly->dynamicCall("handle()").toString());
    }
    m_axWidget->dynamicCall("UpdateDisplay()");
}

int CadImportDialog::ensureEquipment(const Candidate &candidate)
{
    QString dt = candidate.designation;
    if (dt.trimmed().isEmpty())
        dt = candidate.blockName;
    const QString partCode = candidate.partCode.trimmed();

    QSqlQuery query(T_ProjectDatabase);
    if (!partCode.isEmpty()) {
        query.prepare("SELECT Equipment_ID FROM Equipment WHERE PartCode = :pc");
        query.bindValue(":pc", partCode);
        if (query.exec() && query.next())
            return query.value(0).toInt();
    }
    query.prepare("SELECT Equipment_ID FROM Equipment WHERE DT = :dt");
    query.bindValue(":dt", dt);
    if (query.exec() && query.next())
        return query.value(0).toInt();

    // 如果有物料编码，优先从本地物料库复制属性，并用库中的元件代号填充
    QString type, spec, name, desc, orderNum, factory, remark, tvariable, tmodel, libDt;
    if (!partCode.isEmpty()) {
        QSqlQuery qLib(T_LibDatabase);
        qLib.prepare("SELECT Type,Spec,Name,`Desc`,OrderNum,Factory,Remark,TVariable,TModel,DT FROM Equipment WHERE PartCode = :pc");
        qLib.bindValue(":pc", partCode);
        if (qLib.exec() && qLib.next()) {
            type = qLib.value(0).toString();
            spec = qLib.value(1).toString();
            name = qLib.value(2).toString();
            desc = qLib.value(3).toString();
            orderNum = qLib.value(4).toString();
            factory = qLib.value(5).toString();
            remark = qLib.value(6).toString();
            tvariable = qLib.value(7).toString();
            tmodel = qLib.value(8).toString();
            libDt = qLib.value(9).toString();
        }
        if (dt.trimmed().isEmpty() && !libDt.trimmed().isEmpty())
            dt = libDt; // 用库里的代号填充
    }
    if (dt.trimmed().isEmpty() && !libDt.trimmed().isEmpty())
        dt = libDt;
    if (dt.trimmed().isEmpty() && !partCode.isEmpty())
        dt = partCode; // 兜底，用物料编码作为代号

    const int newId = GetMaxIDOfDB(T_ProjectDatabase, "Equipment", "Equipment_ID");
    QSqlQuery insert(T_ProjectDatabase);
    insert.prepare("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Spec,Eqpt_Category,Name,Desc,PartCode,OrderNum,Factory,Remark,TVariable,TModel)"
                  " VALUES (:id,:dt,:ps,:type,:spec,:cat,:name,:desc,:pc,:ord,:factory,:remark,:tvariable,:tmodel)");
    insert.bindValue(":id", newId);
    insert.bindValue(":dt", dt);
    insert.bindValue(":ps", GetProjectStructureIDByPageID(m_pageId));
    insert.bindValue(":type", type);
    insert.bindValue(":spec", spec);
    insert.bindValue(":cat", "组合元件");
    insert.bindValue(":name", name);
    insert.bindValue(":desc", desc);
    insert.bindValue(":pc", partCode);
    insert.bindValue(":ord", orderNum);
    insert.bindValue(":factory", factory);
    insert.bindValue(":remark", remark);
    insert.bindValue(":tvariable", tvariable);
    insert.bindValue(":tmodel", tmodel);
    insert.exec();
    return newId;
}

bool CadImportDialog::importSymbols()
{
    if (!m_preparePage) {
        QMessageBox::warning(this, "提示", "未配置页创建回调，无法导入。");
        return false;
    }

    if (m_pageId < 0) {
        if (!m_preparePage(m_sourcePath, &m_targetPath, &m_pageId))
            return false;
    }

    // 使用后台全局控件写入，避免前端控件初始化导致崩溃
    QAxWidget *ax = GlobalBackAxWidget;
    if (!ax) {
        ax = new QAxWidget();
        ax->setControl(kMxDrawClsid);
        GlobalBackAxWidget = ax;
    }

    const QString loadPath = m_targetPath.isEmpty() ? m_sourcePath : m_targetPath;
    bool ok = ax->dynamicCall("OpenDwgFile(QString)", loadPath).toBool();
    if (!ok) {
        QMessageBox::warning(this, "提示", "后台打开 DWG 失败，导入中止。");
        return false;
    }
    ax->dynamicCall("ZoomAll()");

    // 建立 DbId -> block 引用映射，只处理有 DbId 的块
    QSet<QString> wantedIds;
    for (const Candidate &c : m_candidates)
        wantedIds.insert(c.dbId);

    QMap<QString, IMxDrawBlockReference *> blkById;
    IMxDrawSelectionSet *ss = (IMxDrawSelectionSet *)ax->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter = (IMxDrawResbuf *)ax->querySubObject("NewResbuf()");
    filter->AddStringEx("INSERT", 5020);
    ss->dynamicCall("AllSelect(QVariant)", filter->asVariant());
    int count = ss->dynamicCall("Count()").toInt();
    for (int i = 0; i < count; ++i) {
        IMxDrawEntity *ent = (IMxDrawEntity *)ss->querySubObject("Item(int)", i);
        if (!ent)
            continue;
        if (EntyIsErased(ax, ent))
            continue;
        if (ent->dynamicCall("ObjectName()").toString() != "McDbBlockReference")
            continue;
        QString dbId = ent->dynamicCall("GetxDataString2(QString,int)", "DbId", 0).toString();
        if (dbId.isEmpty())
            dbId = ent->dynamicCall("GetxDataString2(QString,int)", "DbID", 0).toString();
        if (dbId.isEmpty())
            continue;
        if (!wantedIds.contains(dbId))
            continue;
        blkById.insert(dbId, (IMxDrawBlockReference *)ent);
    }

    for (const Candidate &c : m_candidates) {
        IMxDrawBlockReference *blk = blkById.value(c.dbId, nullptr);
        if (!blk)
            continue;
        if (!m_importAllCheck->isChecked()) {
            // 严格模式：必须有物料编码且能在库中找到模板
            if (c.partCode.trimmed().isEmpty())
                continue;
            QSqlQuery qLib(T_LibDatabase);
            qLib.prepare("SELECT Equipment_ID FROM Equipment WHERE PartCode = :pc");
            qLib.bindValue(":pc", c.partCode);
            if (!qLib.exec() || !qLib.next())
                continue;
        }
        const int equipmentId = ensureEquipment(c);
        if (!c.designation.isEmpty())
            blk->dynamicCall("SetxDataString(QString,int,QString)", "Designation", 0, c.designation);
        if (!c.partCode.isEmpty())
            blk->dynamicCall("SetxDataString(QString,int,QString)", "PartCode", 0, c.partCode);
        InsertDBSymbolInfoByBlkEnty(ax, blk, QString::number(m_pageId), QString::number(equipmentId));
    }

    QString savePath = m_targetPath.isEmpty() ? m_sourcePath : m_targetPath;
    ax->dynamicCall("SaveDwgFile(QString)", savePath);
    return true;
}

void CadImportDialog::accept()
{
    if (!importSymbols())
        return;
    QDialog::accept();
}

void CadImportDialog::onRescan()
{
    scanCandidates();
}

void CadImportDialog::onSelectionChanged()
{
    clearHighlights();
    QModelIndexList rows = m_table->selectionModel()->selectedRows();
    if (rows.isEmpty())
        return;
    int row = rows.first().row();
    if (row < 0 || row >= m_candidates.size())
        return;
    IMxDrawBlockReference *blk = (IMxDrawBlockReference *)m_axWidget->querySubObject("HandleToObject(const QString)", m_candidates.at(row).handle);
    if (!blk)
        return;
    blk->dynamicCall("Highlight(bool)", true);
    drawHighlightBox(blk);
    IMxDrawPoint *pos = (IMxDrawPoint *)blk->querySubObject("Position()");
    if (pos)
        m_axWidget->dynamicCall("ZoomCenter(double,double)", pos->x(), pos->y());
}

void CadImportDialog::onImportAllToggled(int state)
{
    Q_UNUSED(state);
    m_table->setColumnHidden(3, !m_importAllCheck->isChecked());
}
