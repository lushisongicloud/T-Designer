#ifndef CADIMPORTDIALOG_H
#define CADIMPORTDIALOG_H

#include <QDialog>
#include <QLabel>
#include <QTableWidget>
#include <QPushButton>
#include <QAxWidget>
#include <QList>
#include <QLineEdit>
#include <QComboBox>
#include <QGroupBox>
#include <functional>
#include "common.h"
#include <QToolButton>

class QCheckBox;

class CadImportDialog : public QDialog
{
    Q_OBJECT

public:
    CadImportDialog(const QString &sourcePath,
                    std::function<bool(const QString &, QString *, int *)> pagePreparation,
                    QWidget *parent = nullptr);
    ~CadImportDialog() override;

protected:
    void accept() override;
    void changeEvent(QEvent *event) override;

private slots:
    void onRescan();
    void onSelectionChanged();
    void onImportAllToggled(int state);
    void onFilterTextChanged(const QString &text);
    void onApplyDetailChanges();
    void onApplyMatchSelection();
    void onSelectAll();
    void onSelectNone();
    void onImportModeChanged(int index);
    void onToggleMaximize();

private:
    struct LibraryMatch
    {
        QString partCode;
        QString dt;
        QString name;
        QString spec;
        bool valid() const { return !partCode.trimmed().isEmpty() || !dt.trimmed().isEmpty(); }
        QString displayText() const;
    };

    struct Candidate
    {
        QString handle;
        QString dbId;
        QString designation;
        QString blockName;
        QString partCode;
        QString source;
        bool selected = true;
        bool hasDbId = false;
        LibraryMatch libMatch;
        QString overlayHandle;
    };

    void buildUi();
    void loadDrawing();
    void clearHighlights();
    void scanCandidates();
    int ensureEquipment(const Candidate &candidate);
    bool importSymbols();
    void renderOverlays();
    QString drawHighlightBox(IMxDrawBlockReference *blk, bool selected);
    void refreshOverlayStyle(Candidate &c, bool selected);
    void pulseSelectionBox(const QString &handle);
    void applySelectionRow(int row);
    void syncDetailPanel(const Candidate &c);
    void updateSummary();
    void applyFilter();
    void updateMaximizeButton();
    LibraryMatch findBestLibraryMatch(const Candidate &candidate) const;
    QList<LibraryMatch> findFuzzyMatches(const Candidate &candidate) const;
    bool shouldImportAll() const;

    QString m_sourcePath;
    QString m_targetPath;
    int m_pageId = -1;
    QAxWidget *m_axWidget = nullptr;
    QTableWidget *m_table = nullptr;
    QLabel *m_statusLabel = nullptr;
    QLabel *m_summaryLabel = nullptr;
    QLabel *m_fileLabel = nullptr;
    QPushButton *m_rescanButton = nullptr;
    QCheckBox *m_importAllCheck = nullptr;
    QCheckBox *m_autoZoomCheck = nullptr;
    QCheckBox *m_overlayToggle = nullptr;
    QToolButton *m_maximizeButton = nullptr;
    QLineEdit *m_filterEdit = nullptr;
    QGroupBox *m_detailGroup = nullptr;
    QLineEdit *m_designationEdit = nullptr;
    QLineEdit *m_partCodeEdit = nullptr;
    QLineEdit *m_blockNameEdit = nullptr;
    QLabel *m_sourceLabel = nullptr;
    QComboBox *m_matchCombo = nullptr;
    QPushButton *m_selectAllButton = nullptr;
    QPushButton *m_clearSelectionButton = nullptr;
    std::function<bool(const QString &, QString *, int *)> m_preparePage;
    QList<Candidate> m_candidates;
    QList<QString> m_overlayHandles;
    int m_currentRow = -1;
    bool m_updatingSelection = false;
};

#endif // CADIMPORTDIALOG_H
