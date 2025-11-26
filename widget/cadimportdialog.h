#ifndef CADIMPORTDIALOG_H
#define CADIMPORTDIALOG_H

#include <QDialog>
#include <QLabel>
#include <QTableWidget>
#include <QPushButton>
#include <QAxWidget>
#include <QList>
#include <functional>
#include "common.h"

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

private slots:
    void onRescan();
    void onSelectionChanged();
    void onImportAllToggled(int state);

private:
    struct Candidate
    {
        QString handle;
        QString dbId;
        QString designation;
        QString blockName;
        QString partCode;
    };

    void buildUi();
    void loadDrawing();
    void clearHighlights();
    void scanCandidates();
    int ensureEquipment(const Candidate &candidate);
    bool importSymbols();
    void drawHighlightBox(IMxDrawBlockReference *blk);

    QString m_sourcePath;
    QString m_targetPath;
    int m_pageId = -1;
    QAxWidget *m_axWidget = nullptr;
    QTableWidget *m_table = nullptr;
    QLabel *m_statusLabel = nullptr;
    QPushButton *m_rescanButton = nullptr;
    QCheckBox *m_importAllCheck = nullptr;
    std::function<bool(const QString &, QString *, int *)> m_preparePage;
    QList<Candidate> m_candidates;
    QList<QString> m_overlayHandles;
};

#endif // CADIMPORTDIALOG_H
