#include "BO/function/systemstructureservice.h"

#include "DO/model.h"

namespace {

SystemCropResult buildResult(const SystemStructure &structure,
                             const QString &systemDescription,
                             const QString &linkText)
{
    SystemCropResult result;
    result.isConsistent = structure.isSystemConsistent();
    result.deviceLines = structure.getDeviceLineList();
    result.connectionLines = structure.getConnectionLineList();
    result.connectionPortLists = structure.getPortListInConnectionList();
    result.devicesInDefinition = structure.getDeviceSetInDefinition();
    result.componentsInConnection = structure.getComponentSetInConnection();
    result.boundaryComponents = structure.getBoundaryComponentList();

    if (result.isConsistent && !linkText.trimmed().isEmpty()) {
        result.croppedSystemDescription = structure.getCroppedSystemDescription();
    } else {
        // 当链路为空或结构不自洽时，返回原系统描述，保持上层逻辑可继续处理
        result.croppedSystemDescription = systemDescription;
    }

    return result;
}

} // namespace

SystemCropResult SystemStructureService::analyze(const QString &systemDescription,
                                                 const QString &linkText)
{
    SystemStructure structure(systemDescription, linkText);
    return buildResult(structure, systemDescription, linkText);
}

QString SystemStructureService::cropSystemDescription(const QString &systemDescription,
                                                      const QString &linkText,
                                                      bool *isConsistent)
{
    const SystemCropResult result = analyze(systemDescription, linkText);
    if (isConsistent)
        *isConsistent = result.isConsistent;
    return result.croppedSystemDescription;
}

QStringList SystemStructureService::boundaryComponents(const QString &systemDescription,
                                                       const QString &linkText,
                                                       bool *isConsistent)
{
    const SystemCropResult result = analyze(systemDescription, linkText);
    if (isConsistent)
        *isConsistent = result.isConsistent;
    return result.boundaryComponents;
}
