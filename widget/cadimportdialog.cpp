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
#include <QSplitter>
#include <QLineEdit>
#include <QFormLayout>
#include <QComboBox>
#include <QGroupBox>
#include <QTimer>
#include <QFileInfo>
#include <QtMath>
#include <QStringList>
#include <QVariant>
#include <QToolButton>
#include <QEvent>

using namespace MxDrawXLib;

namespace {
constexpr const char *kMxDrawClsid = "{74a777f8-7a8f-4e7c-af47-7074828086e2}";
}

QString CadImportDialog::LibraryMatch::displayText() const
{
    QStringList parts;
    if (!partCode.trimmed().isEmpty())
        parts << partCode;
    if (!dt.trimmed().isEmpty())
        parts << dt;
    if (!name.trimmed().isEmpty())
        parts << name;
    if (!spec.trimmed().isEmpty())
        parts << spec;
    return parts.join(" / ");
}

CadImportDialog::CadImportDialog(const QString &sourcePath,
                                 std::function<bool(const QString &, QString *, int *)> pagePreparation,
                                 QWidget *parent)
    : QDialog(parent),
      m_sourcePath(sourcePath),
      m_preparePage(std::move(pagePreparation))
{
    setWindowTitle("导入图纸");
    setWindowFlags(windowFlags() | Qt::WindowMinMaxButtonsHint | Qt::WindowSystemMenuHint);
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
    setMinimumSize(960, 660);

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
    m_table->setColumnCount(6);
    QStringList headers;
    headers << "导入" << "序号" << "标识/型号" << "物料编码" << "块名" << "匹配/来源";
    m_table->setHorizontalHeaderLabels(headers);
    m_table->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);
    m_table->horizontalHeader()->setSectionResizeMode(0, QHeaderView::ResizeToContents);
    m_table->horizontalHeader()->setSectionResizeMode(1, QHeaderView::ResizeToContents);
    m_table->horizontalHeader()->setStretchLastSection(true);
    m_table->setSelectionBehavior(QAbstractItemView::SelectRows);
    m_table->setSelectionMode(QAbstractItemView::SingleSelection);
    m_table->setEditTriggers(QAbstractItemView::NoEditTriggers);
    m_table->setAlternatingRowColors(true);
    connect(m_table, &QTableWidget::itemSelectionChanged, this, &CadImportDialog::onSelectionChanged);
    connect(m_table, &QTableWidget::itemChanged, this, [this](QTableWidgetItem *item) {
        if (!item || m_updatingSelection || item->column() != 0)
            return;
        const int row = item->row();
        if (row < 0 || row >= m_candidates.size())
            return;
        m_candidates[row].selected = (item->checkState() == Qt::Checked);
        refreshOverlayStyle(m_candidates[row], row == m_currentRow);
        updateSummary();
    });

    m_statusLabel = new QLabel(this);
    m_summaryLabel = new QLabel(this);
    m_fileLabel = new QLabel(QString("源文件：%1").arg(QFileInfo(m_sourcePath).fileName()), this);
    m_maximizeButton = new QToolButton(this);
    m_maximizeButton->setText("最大化");
    m_maximizeButton->setToolButtonStyle(Qt::ToolButtonTextOnly);
    connect(m_maximizeButton, &QToolButton::clicked, this, &CadImportDialog::onToggleMaximize);

    m_rescanButton = new QPushButton("重新识别", this);
    connect(m_rescanButton, &QPushButton::clicked, this, &CadImportDialog::onRescan);

    m_importAllCheck = new QCheckBox("放宽导入（无库匹配也生成）", this);
    m_importAllCheck->setChecked(true);
    connect(m_importAllCheck, &QCheckBox::stateChanged, this, &CadImportDialog::onImportAllToggled);

    m_autoZoomCheck = new QCheckBox("选中时居中", this);
    m_autoZoomCheck->setChecked(true);
    m_overlayToggle = new QCheckBox("显示框线", this);
    m_overlayToggle->setChecked(true);
    connect(m_overlayToggle, &QCheckBox::stateChanged, this, [this](int) { renderOverlays(); });

    m_filterEdit = new QLineEdit(this);
    m_filterEdit->setPlaceholderText("按标识/物料编码/块名过滤");
    connect(m_filterEdit, &QLineEdit::textChanged, this, &CadImportDialog::onFilterTextChanged);

    m_selectAllButton = new QPushButton("全选", this);
    m_clearSelectionButton = new QPushButton("全不选", this);
    connect(m_selectAllButton, &QPushButton::clicked, this, &CadImportDialog::onSelectAll);
    connect(m_clearSelectionButton, &QPushButton::clicked, this, &CadImportDialog::onSelectNone);

    m_detailGroup = new QGroupBox("当前元件", this);
    QFormLayout *detailForm = new QFormLayout(m_detailGroup);
    m_designationEdit = new QLineEdit(m_detailGroup);
    m_partCodeEdit = new QLineEdit(m_detailGroup);
    m_blockNameEdit = new QLineEdit(m_detailGroup);
    m_blockNameEdit->setReadOnly(true);
    m_sourceLabel = new QLabel(m_detailGroup);
    m_matchCombo = new QComboBox(m_detailGroup);
    m_matchCombo->setSizeAdjustPolicy(QComboBox::AdjustToContents);
    QPushButton *applyDetailButton = new QPushButton("应用修改", m_detailGroup);
    QPushButton *applyMatchButton = new QPushButton("采用匹配", m_detailGroup);
    connect(applyDetailButton, &QPushButton::clicked, this, &CadImportDialog::onApplyDetailChanges);
    connect(applyMatchButton, &QPushButton::clicked, this, &CadImportDialog::onApplyMatchSelection);

    detailForm->addRow("标识/型号", m_designationEdit);
    detailForm->addRow("物料编码", m_partCodeEdit);
    detailForm->addRow("块名", m_blockNameEdit);
    detailForm->addRow("识别依据", m_sourceLabel);
    QHBoxLayout *matchRow = new QHBoxLayout;
    matchRow->addWidget(m_matchCombo, 1);
    matchRow->addWidget(applyMatchButton);
    detailForm->addRow("库匹配", matchRow);
    detailForm->addRow(applyDetailButton);

    QHBoxLayout *headerLayout = new QHBoxLayout;
    headerLayout->addWidget(m_fileLabel);
    headerLayout->addStretch();
    headerLayout->addWidget(m_maximizeButton);
    headerLayout->addWidget(m_statusLabel);

    QHBoxLayout *toolbarLayout = new QHBoxLayout;
    toolbarLayout->addWidget(m_importAllCheck);
    toolbarLayout->addWidget(m_autoZoomCheck);
    toolbarLayout->addWidget(m_overlayToggle);
    toolbarLayout->addWidget(m_selectAllButton);
    toolbarLayout->addWidget(m_clearSelectionButton);
    toolbarLayout->addWidget(m_rescanButton);

    QHBoxLayout *filterLayout = new QHBoxLayout;
    filterLayout->addWidget(m_filterEdit);
    filterLayout->addWidget(m_summaryLabel);

    QWidget *rightPanel = new QWidget(this);
    QVBoxLayout *rightLayout = new QVBoxLayout(rightPanel);
    rightLayout->addLayout(filterLayout);
    rightLayout->addWidget(m_table);
    rightLayout->addWidget(m_detailGroup);
    rightPanel->setMinimumWidth(360);

    QSplitter *splitter = new QSplitter(Qt::Horizontal, this);
    splitter->addWidget(m_axWidget);
    splitter->addWidget(rightPanel);
    splitter->setStretchFactor(0, 2);
    splitter->setStretchFactor(1, 1);

    QDialogButtonBox *buttonBox = new QDialogButtonBox(QDialogButtonBox::Ok | QDialogButtonBox::Cancel, this);
    connect(buttonBox, &QDialogButtonBox::accepted, this, &CadImportDialog::accept);
    connect(buttonBox, &QDialogButtonBox::rejected, this, &CadImportDialog::reject);

    QVBoxLayout *rootLayout = new QVBoxLayout(this);
    rootLayout->addLayout(headerLayout);
    rootLayout->addLayout(toolbarLayout);
    rootLayout->addWidget(splitter, 1);
    rootLayout->addWidget(buttonBox);
    setLayout(rootLayout);
    updateMaximizeButton();
}

void CadImportDialog::loadDrawing()
{
    if (!m_axWidget)
        return;
    if (!QFile::exists(m_sourcePath)) {
        QMessageBox::warning(this, "提示", "DWG 文件不存在，无法打开。");
        m_statusLabel->setText("未找到文件");
        return;
    }
    bool ok = m_axWidget->dynamicCall("OpenDwgFile(QString)", m_sourcePath).toBool();
    if (!ok) {
        QMessageBox::warning(this, "提示", "DWG 打开失败，请检查文件是否有效。");
        m_statusLabel->setText("文件打开失败");
        return;
    }
    m_axWidget->dynamicCall("ZoomAll()");
}

void CadImportDialog::clearHighlights()
{
    if (m_axWidget) {
        for (const QString &h : m_overlayHandles) {
            IMxDrawEntity *ent = (IMxDrawEntity *)m_axWidget->querySubObject("HandleToObject(const QString)", h);
            if (ent)
                ent->dynamicCall("Erase()");
        }
        for (const Candidate &c : m_candidates) {
            IMxDrawEntity *ent = (IMxDrawEntity *)m_axWidget->querySubObject("HandleToObject(const QString)", c.handle);
            if (ent)
                ent->dynamicCall("Highlight(bool)", false);
        }
        m_axWidget->dynamicCall("UpdateDisplay()");
    }
    m_overlayHandles.clear();
    for (Candidate &c : m_candidates)
        c.overlayHandle.clear();
}

void CadImportDialog::scanCandidates()
{
    clearHighlights();
    m_candidates.clear();
    m_table->setRowCount(0);
    m_currentRow = -1;

    if (!m_axWidget)
        return;

    IMxDrawSelectionSet *ss = (IMxDrawSelectionSet *)m_axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter = (IMxDrawResbuf *)m_axWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("INSERT", 5020);
    ss->dynamicCall("AllSelect(QVariant)", filter->asVariant());
    int count = ss->dynamicCall("Count()").toInt();

    QSet<QString> seenHandles;
    for (int i = 0; i < count; ++i) {
        IMxDrawEntity *ent = (IMxDrawEntity *)ss->querySubObject("Item(int)", i);
        if (!ent)
            continue;
        if (EntyIsErased(m_axWidget, ent))
            continue;
        if (ent->dynamicCall("ObjectName()").toString() != "McDbBlockReference")
            continue;
        Candidate c;
        c.handle = ent->dynamicCall("handle()").toString();
        if (seenHandles.contains(c.handle))
            continue;
        seenHandles.insert(c.handle);

        c.dbId = ent->dynamicCall("GetxDataString2(QString,int)", "DbId", 0).toString();
        if (c.dbId.isEmpty())
            c.dbId = ent->dynamicCall("GetxDataString2(QString,int)", "DbID", 0).toString();
        c.hasDbId = !c.dbId.isEmpty();
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
        c.source = c.hasDbId ? "结构化标记" : ((!c.partCode.isEmpty() || !c.designation.isEmpty()) ? "标注/文字" : "块名");
        c.libMatch = findBestLibraryMatch(c);
        if (c.partCode.trimmed().isEmpty() && c.libMatch.valid() && !c.libMatch.partCode.isEmpty()) {
            c.partCode = c.libMatch.partCode;
            c.libMatch = findBestLibraryMatch(c);
        }
        if (c.designation.trimmed().isEmpty() && c.libMatch.valid() && !c.libMatch.dt.isEmpty())
            c.designation = c.libMatch.dt;
        m_candidates.append(c);
    }

    m_updatingSelection = true;
    for (int row = 0; row < m_candidates.size(); ++row) {
        const Candidate &c = m_candidates.at(row);
        m_table->insertRow(row);

        QTableWidgetItem *chk = new QTableWidgetItem;
        chk->setFlags((chk->flags() | Qt::ItemIsUserCheckable) & ~Qt::ItemIsEditable);
        chk->setCheckState(Qt::Checked);
        m_table->setItem(row, 0, chk);

        m_table->setItem(row, 1, new QTableWidgetItem(QString::number(row + 1)));
        m_table->setItem(row, 2, new QTableWidgetItem(c.designation));
        m_table->setItem(row, 3, new QTableWidgetItem(c.partCode));
        m_table->setItem(row, 4, new QTableWidgetItem(c.blockName));
        QString matchDesc = c.libMatch.valid() ? c.libMatch.displayText() : QString("未匹配 · %1").arg(c.source);
        m_table->setItem(row, 5, new QTableWidgetItem(matchDesc));
    }
    m_updatingSelection = false;

    m_statusLabel->setText(QString("已识别元件：%1").arg(m_candidates.size()));
    m_axWidget->dynamicCall("ZoomAll()");
    renderOverlays();
    applyFilter();
    if (!m_candidates.isEmpty()) {
        m_table->selectRow(0);
        applySelectionRow(0);
    }
    updateSummary();
}

QString CadImportDialog::drawHighlightBox(IMxDrawBlockReference *blk, bool selected)
{
    if (!blk || !m_axWidget)
        return QString();
    IMxDrawPoint *pos = (IMxDrawPoint *)blk->querySubObject("Position()");
    double cx = pos ? pos->x() : 0.0;
    double cy = pos ? pos->y() : 0.0;
    double minx = cx - 8.0;
    double maxx = cx + 8.0;
    double miny = cy - 8.0;
    double maxy = cy + 8.0;

    QAxObject *geom = blk->querySubObject("GetGeomExtents");
    if (geom) {
        IMxDrawPoint *minPt = (IMxDrawPoint *)geom->querySubObject("MinPoint");
        IMxDrawPoint *maxPt = (IMxDrawPoint *)geom->querySubObject("MaxPoint");
        if (minPt && maxPt) {
            minx = minPt->x();
            miny = minPt->y();
            maxx = maxPt->x();
            maxy = maxPt->y();
        }
    }

    const double width = qAbs(maxx - minx);
    const double height = qAbs(maxy - miny);
    // 适度留白，避免框体过大或过小
    double margin = qMin(width, height) * 0.12;
    if (qFuzzyIsNull(margin) || margin < 4.0)
        margin = 6.0;
    if (margin > 16.0)
        margin = 16.0;
    minx -= margin;
    miny -= margin;
    maxx += margin;
    maxy += margin;

    m_axWidget->dynamicCall("PathMoveTo(double,double)", minx, miny);
    m_axWidget->dynamicCall("PathLineTo(double,double)", maxx, miny);
    m_axWidget->dynamicCall("PathLineTo(double,double)", maxx, maxy);
    m_axWidget->dynamicCall("PathLineTo(double,double)", minx, maxy);
    m_axWidget->dynamicCall("PathLineTo(double,double)", minx, miny);
    qlonglong lID = m_axWidget->dynamicCall("DrawPathToPolyline()", QVariantList()).toLongLong();
    IMxDrawPolyline *poly = (IMxDrawPolyline *)m_axWidget->querySubObject("ObjectIdToObject(const qlonglong)", lID);
    if (poly) {
        poly->dynamicCall("setColorIndex(int)", selected ? McColor::mcRed : 8);
        poly->dynamicCall("SetLineType(QString)", selected ? "Continuous" : "DASHED");
        poly->dynamicCall("SetLineWeight(int)", selected ? 40 : 16);
        QString handle = poly->dynamicCall("handle()").toString();
        m_overlayHandles.append(handle);
        return handle;
    }
    return QString();
}

void CadImportDialog::renderOverlays()
{
    clearHighlights();
    if (!m_axWidget)
        return;

    if (!m_overlayToggle || !m_overlayToggle->isChecked()) {
        if (m_currentRow >= 0 && m_currentRow < m_candidates.size()) {
            IMxDrawBlockReference *blk = (IMxDrawBlockReference *)m_axWidget->querySubObject("HandleToObject(const QString)", m_candidates[m_currentRow].handle);
            if (blk)
                blk->dynamicCall("Highlight(bool)", true);
        }
        return;
    }

    for (int i = 0; i < m_candidates.size(); ++i) {
        Candidate &c = m_candidates[i];
        IMxDrawBlockReference *blk = (IMxDrawBlockReference *)m_axWidget->querySubObject("HandleToObject(const QString)", c.handle);
        if (!blk)
            continue;
        c.overlayHandle = drawHighlightBox(blk, i == m_currentRow);
    }
    if (m_currentRow >= 0 && m_currentRow < m_candidates.size()) {
        IMxDrawBlockReference *blk = (IMxDrawBlockReference *)m_axWidget->querySubObject("HandleToObject(const QString)", m_candidates[m_currentRow].handle);
        if (blk)
            blk->dynamicCall("Highlight(bool)", true);
    }
    m_axWidget->dynamicCall("UpdateDisplay()");
}

void CadImportDialog::refreshOverlayStyle(Candidate &c, bool selected)
{
    if (!m_axWidget || !m_overlayToggle || !m_overlayToggle->isChecked() || c.overlayHandle.isEmpty())
        return;
    IMxDrawPolyline *poly = (IMxDrawPolyline *)m_axWidget->querySubObject("HandleToObject(const QString)", c.overlayHandle);
    if (!poly)
        return;
    poly->dynamicCall("setColorIndex(int)", selected ? McColor::mcRed : 8);
    poly->dynamicCall("SetLineType(QString)", selected ? "Continuous" : "DASHED");
    poly->dynamicCall("SetLineWeight(int)", selected ? 42 : 16);
    m_axWidget->dynamicCall("UpdateDisplay()");
}

void CadImportDialog::pulseSelectionBox(const QString &handle)
{
    if (!m_axWidget || handle.isEmpty())
        return;
    IMxDrawPolyline *poly = (IMxDrawPolyline *)m_axWidget->querySubObject("HandleToObject(const QString)", handle);
    if (!poly)
        return;
    poly->dynamicCall("setColorIndex(int)", 2); // bright yellow
    poly->dynamicCall("SetLineWeight(int)", 60);
    m_axWidget->dynamicCall("UpdateDisplay()");
    QTimer::singleShot(140, this, [this, handle]() {
        for (int i = 0; i < m_candidates.size(); ++i) {
            if (m_candidates[i].overlayHandle == handle) {
                refreshOverlayStyle(m_candidates[i], i == m_currentRow);
                break;
            }
        }
    });
}

void CadImportDialog::applySelectionRow(int row)
{
    if (m_updatingSelection)
        return;
    if (row < 0 || row >= m_candidates.size()) {
        m_currentRow = -1;
        return;
    }

    if (m_axWidget && m_currentRow >= 0 && m_currentRow < m_candidates.size()) {
        IMxDrawEntity *prev = (IMxDrawEntity *)m_axWidget->querySubObject("HandleToObject(const QString)", m_candidates[m_currentRow].handle);
        if (prev)
            prev->dynamicCall("Highlight(bool)", false);
    }

    m_currentRow = row;
    Candidate &c = m_candidates[row];
    if (m_axWidget) {
        IMxDrawBlockReference *blk = (IMxDrawBlockReference *)m_axWidget->querySubObject("HandleToObject(const QString)", c.handle);
        if (blk) {
            blk->dynamicCall("Highlight(bool)", true);
            if (m_autoZoomCheck && m_autoZoomCheck->isChecked()) {
                IMxDrawPoint *pos = (IMxDrawPoint *)blk->querySubObject("Position()");
                if (pos)
                    m_axWidget->dynamicCall("ZoomCenter(double,double)", pos->x(), pos->y());
            }
        }
    }

    for (int i = 0; i < m_candidates.size(); ++i)
        refreshOverlayStyle(m_candidates[i], i == m_currentRow);
    pulseSelectionBox(c.overlayHandle);
    syncDetailPanel(c);
}

void CadImportDialog::syncDetailPanel(const Candidate &c)
{
    if (!m_detailGroup)
        return;
    m_designationEdit->setText(c.designation);
    m_partCodeEdit->setText(c.partCode);
    m_blockNameEdit->setText(c.blockName);
    m_sourceLabel->setText(c.source);

    m_matchCombo->clear();
    QList<LibraryMatch> matches = findFuzzyMatches(c);
    if (c.libMatch.valid())
        matches.prepend(c.libMatch);

    QSet<QString> seen;
    for (const LibraryMatch &m : matches) {
        QString key = m.partCode + "|" + m.dt;
        if (seen.contains(key))
            continue;
        seen.insert(key);
        const QString text = m.displayText().isEmpty() ? "库元件" : m.displayText();
        int idx = m_matchCombo->count();
        m_matchCombo->addItem(text, key);
        m_matchCombo->setItemData(idx, m.partCode, Qt::UserRole + 1);
        m_matchCombo->setItemData(idx, m.dt, Qt::UserRole + 2);
    }

    if (m_matchCombo->count() == 0) {
        m_matchCombo->addItem("未找到匹配", QVariant());
        m_matchCombo->setEnabled(false);
    } else {
        m_matchCombo->setEnabled(true);
    }
}

void CadImportDialog::updateSummary()
{
    int selectedCount = 0;
    int matchedCount = 0;
    for (const Candidate &c : m_candidates) {
        if (c.selected)
            ++selectedCount;
        if (c.libMatch.valid())
            ++matchedCount;
    }
    int visibleCount = 0;
    for (int row = 0; row < m_table->rowCount(); ++row) {
        if (!m_table->isRowHidden(row))
            ++visibleCount;
    }
    if (m_summaryLabel) {
        m_summaryLabel->setText(QString("显示 %1 / 总计 %2 · 已选 %3 · 库匹配 %4")
                                .arg(visibleCount)
                                .arg(m_candidates.size())
                                .arg(selectedCount)
                                .arg(matchedCount));
    }
}

void CadImportDialog::applyFilter()
{
    const QString key = m_filterEdit ? m_filterEdit->text().trimmed() : QString();
    for (int row = 0; row < m_candidates.size(); ++row) {
        bool match = key.isEmpty();
        if (!match) {
            const Candidate &c = m_candidates.at(row);
            QString combined = c.designation + " " + c.partCode + " " + c.blockName + " " + c.source;
            match = combined.contains(key, Qt::CaseInsensitive);
        }
        m_table->setRowHidden(row, !match);
    }
}

CadImportDialog::LibraryMatch CadImportDialog::findBestLibraryMatch(const Candidate &candidate) const
{
    LibraryMatch match;
    if (!T_LibDatabase.isOpen())
        return match;

    QSqlQuery query(T_LibDatabase);
    const QString partCode = candidate.partCode.trimmed();
    const QString designation = candidate.designation.trimmed();

    if (!partCode.isEmpty()) {
        query.prepare("SELECT PartCode,DT,Name,Spec FROM Equipment WHERE PartCode = :pc LIMIT 1");
        query.bindValue(":pc", partCode);
        if (query.exec() && query.next()) {
            match.partCode = query.value(0).toString();
            match.dt = query.value(1).toString();
            match.name = query.value(2).toString();
            match.spec = query.value(3).toString();
            return match;
        }
    }

    if (!designation.isEmpty()) {
        query.prepare("SELECT PartCode,DT,Name,Spec FROM Equipment WHERE DT = :dt LIMIT 1");
        query.bindValue(":dt", designation);
        if (query.exec() && query.next()) {
            match.partCode = query.value(0).toString();
            match.dt = query.value(1).toString();
            match.name = query.value(2).toString();
            match.spec = query.value(3).toString();
            return match;
        }
    }

    QList<LibraryMatch> fuzzy = findFuzzyMatches(candidate);
    if (!fuzzy.isEmpty())
        match = fuzzy.first();
    return match;
}

QList<CadImportDialog::LibraryMatch> CadImportDialog::findFuzzyMatches(const Candidate &candidate) const
{
    QList<LibraryMatch> results;
    if (!T_LibDatabase.isOpen())
        return results;

    auto append = [&](QSqlQuery &query) {
        while (query.next()) {
            LibraryMatch m;
            m.partCode = query.value(0).toString();
            m.dt = query.value(1).toString();
            m.name = query.value(2).toString();
            m.spec = query.value(3).toString();
            results.append(m);
        }
    };

    const QString designation = candidate.designation.trimmed();
    const QString partCode = candidate.partCode.trimmed();
    const QString blockName = candidate.blockName.trimmed();

    QSqlQuery query(T_LibDatabase);
    if (!partCode.isEmpty()) {
        query.prepare("SELECT PartCode,DT,Name,Spec FROM Equipment WHERE PartCode LIKE :pc LIMIT 5");
        query.bindValue(":pc", "%" + partCode + "%");
        if (query.exec())
            append(query);
    }
    if (!designation.isEmpty()) {
        query.prepare("SELECT PartCode,DT,Name,Spec FROM Equipment WHERE DT LIKE :dt LIMIT 5");
        query.bindValue(":dt", "%" + designation + "%");
        if (query.exec())
            append(query);
    }
    if (!blockName.isEmpty()) {
        query.prepare("SELECT PartCode,DT,Name,Spec FROM Equipment WHERE Name LIKE :nm OR Spec LIKE :nm LIMIT 5");
        query.bindValue(":nm", "%" + blockName + "%");
        if (query.exec())
            append(query);
    }
    return results;
}

bool CadImportDialog::shouldImportAll() const
{
    return m_importAllCheck && m_importAllCheck->isChecked();
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

    QSet<QString> wantedIds;
    QSet<QString> wantedHandles;
    int selectedCount = 0;
    for (const Candidate &c : m_candidates) {
        if (!c.selected)
            continue;
        ++selectedCount;
        if (!c.dbId.isEmpty())
            wantedIds.insert(c.dbId);
        if (!c.handle.isEmpty())
            wantedHandles.insert(c.handle);
    }
    if (selectedCount == 0) {
        QMessageBox::information(this, "提示", "尚未选择需要导入的元件。");
        return false;
    }

    QMap<QString, IMxDrawBlockReference *> blkById;
    QMap<QString, IMxDrawBlockReference *> blkByHandle;
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
        QString handle = ent->dynamicCall("handle()").toString();
        if (!dbId.isEmpty() && wantedIds.contains(dbId))
            blkById.insert(dbId, (IMxDrawBlockReference *)ent);
        if (!handle.isEmpty() && wantedHandles.contains(handle))
            blkByHandle.insert(handle, (IMxDrawBlockReference *)ent);
    }

    for (const Candidate &c : m_candidates) {
        if (!c.selected)
            continue;
        IMxDrawBlockReference *blk = blkByHandle.value(c.handle, nullptr);
        if (!blk && !c.dbId.isEmpty())
            blk = blkById.value(c.dbId, nullptr);
        if (!blk)
            continue;
        if (!shouldImportAll()) {
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

void CadImportDialog::changeEvent(QEvent *event)
{
    if (event && event->type() == QEvent::WindowStateChange)
        updateMaximizeButton();
    QDialog::changeEvent(event);
}

void CadImportDialog::onRescan()
{
    scanCandidates();
}

void CadImportDialog::onSelectionChanged()
{
    QModelIndexList rows = m_table->selectionModel()->selectedRows();
    if (rows.isEmpty()) {
        m_currentRow = -1;
        return;
    }
    applySelectionRow(rows.first().row());
}

void CadImportDialog::onImportAllToggled(int state)
{
    Q_UNUSED(state);
    updateSummary();
}

void CadImportDialog::onFilterTextChanged(const QString &)
{
    applyFilter();
    updateSummary();
    if (m_currentRow >= 0 && m_currentRow < m_table->rowCount() && m_table->isRowHidden(m_currentRow)) {
        for (int row = 0; row < m_table->rowCount(); ++row) {
            if (!m_table->isRowHidden(row)) {
                m_table->selectRow(row);
                applySelectionRow(row);
                break;
            }
        }
    }
}

void CadImportDialog::onApplyDetailChanges()
{
    if (m_currentRow < 0 || m_currentRow >= m_candidates.size())
        return;
    Candidate &c = m_candidates[m_currentRow];
    c.designation = m_designationEdit->text().trimmed();
    c.partCode = m_partCodeEdit->text().trimmed();
    c.libMatch = findBestLibraryMatch(c);

    m_updatingSelection = true;
    if (QTableWidgetItem *item = m_table->item(m_currentRow, 2))
        item->setText(c.designation);
    if (QTableWidgetItem *item = m_table->item(m_currentRow, 3))
        item->setText(c.partCode);
    if (QTableWidgetItem *item = m_table->item(m_currentRow, 5))
        item->setText(c.libMatch.valid() ? c.libMatch.displayText() : QString("未匹配 · %1").arg(c.source));
    m_updatingSelection = false;
    syncDetailPanel(c);
    updateSummary();
}

void CadImportDialog::onApplyMatchSelection()
{
    if (m_currentRow < 0 || m_currentRow >= m_candidates.size())
        return;
    if (!m_matchCombo || !m_matchCombo->isEnabled())
        return;
    const QString partCode = m_matchCombo->currentData(Qt::UserRole + 1).toString();
    const QString dt = m_matchCombo->currentData(Qt::UserRole + 2).toString();
    if (!partCode.isEmpty())
        m_partCodeEdit->setText(partCode);
    if (!dt.isEmpty() && m_designationEdit->text().trimmed().isEmpty())
        m_designationEdit->setText(dt);
    onApplyDetailChanges();
}

void CadImportDialog::onSelectAll()
{
    m_updatingSelection = true;
    for (int row = 0; row < m_candidates.size(); ++row) {
        m_candidates[row].selected = true;
        if (QTableWidgetItem *item = m_table->item(row, 0))
            item->setCheckState(Qt::Checked);
    }
    m_updatingSelection = false;
    updateSummary();
}

void CadImportDialog::onSelectNone()
{
    m_updatingSelection = true;
    for (int row = 0; row < m_candidates.size(); ++row) {
        m_candidates[row].selected = false;
        if (QTableWidgetItem *item = m_table->item(row, 0))
            item->setCheckState(Qt::Unchecked);
    }
    m_updatingSelection = false;
    updateSummary();
}

void CadImportDialog::onImportModeChanged(int)
{
    updateSummary();
}

void CadImportDialog::onToggleMaximize()
{
    if (isMaximized())
        showNormal();
    else
        showMaximized();
    updateMaximizeButton();
}

void CadImportDialog::updateMaximizeButton()
{
    if (!m_maximizeButton)
        return;
    if (isMaximized()) {
        m_maximizeButton->setText("还原");
        m_maximizeButton->setToolTip("还原窗口大小");
    } else {
        m_maximizeButton->setText("最大化");
        m_maximizeButton->setToolTip("最大化窗口");
    }
}
