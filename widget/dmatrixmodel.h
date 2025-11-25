#ifndef DMATRIXMODEL_H
#define DMATRIXMODEL_H

#include <QAbstractTableModel>

#include "testability/testability_types.h"

class DMatrixModel : public QAbstractTableModel
{
    Q_OBJECT

public:
    explicit DMatrixModel(QObject *parent = nullptr);

    void setMatrix(const testability::DMatrixBuildResult &matrix);
    const testability::DMatrixBuildResult &matrix() const { return matrix_; }
    const QVector<bool> &faultEnabledStates() const { return faultEnabled_; }
    const QVector<bool> &testEnabledStates() const { return testEnabled_; }

    void setFaultEnabledStates(const QVector<bool> &states);
    void setTestEnabledStates(const QVector<bool> &states);
    void setShowFaultNames(bool show);
    void setShowTestNames(bool show);
    bool showFaultNames() const { return showFaultNames_; }
    bool showTestNames() const { return showTestNames_; }
    void updateTests(const QVector<testability::TestDefinition> &tests);
    const testability::FaultDefinition *faultAt(int row) const;
    const testability::TestDefinition *testAt(int column) const;

    int rowCount(const QModelIndex &parent = QModelIndex()) const override;
    int columnCount(const QModelIndex &parent = QModelIndex()) const override;
    QVariant data(const QModelIndex &index, int role) const override;
    QVariant headerData(int section, Qt::Orientation orientation, int role) const override;
    Qt::ItemFlags flags(const QModelIndex &index) const override;

private:
    testability::DMatrixBuildResult matrix_;
    QVector<bool> faultEnabled_;
    QVector<bool> testEnabled_;
    bool showFaultNames_ = false;
    bool showTestNames_ = false;
};

#endif // DMATRIXMODEL_H
