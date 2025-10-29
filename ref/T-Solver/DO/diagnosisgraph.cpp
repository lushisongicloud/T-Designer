#include "diagnosisgraph.h"

// Node\Edge\Dependency类已经在头文件中完全定义了,不需要额外的cpp实现。

DiagnosisGraph::DiagnosisGraph()
    : mCurrentfunctionName(""),
      mPortListInConnectionList(QList<QStringList>()) {}

void DiagnosisGraph::addNode(const QString& functionName, QSharedPointer<Node> node) {
    nodes.append(node);
    // 检查功能名是否已经存在于nameToNodeMap中
    if (!nameToNodeMap.contains(functionName))nameToNodeMap[functionName] = QMap<QString, QSharedPointer<Node>>();
    // 检查该功能名下的端口名称是否已经存在
    if (nameToNodeMap[functionName].contains(node->name)) qDebug() << "In function:" << functionName << ", Node already exists:" << node->name;
    else nameToNodeMap[functionName][node->name] = node;
}

void DiagnosisGraph::addPathway(QSharedPointer<Pathway> pathway) {
    pathways.append(pathway);
    pathway->source->connectedPathways.append(pathway);
    pathway->target->connectedPathways.append(pathway);
}
void DiagnosisGraph::addSubComponent(QSharedPointer<SubComponent> subComponent) {
    subComponents.append(subComponent);
    for(const auto& node : subComponent->nodes) {
        node->containingSubComponent = subComponent;
    }
}

void DiagnosisGraph::addEdge(QSharedPointer<Edge> edge) {
    edges.append(edge);
    edge->source->connectedEdges.append(edge);
    edge->target->connectedEdges.append(edge);
}

void DiagnosisGraph::addDependency(QSharedPointer<Dependency> dependency) {
    dependencies.append(dependency);
    dependency->source->connectedDependencies.append(dependency);
    dependency->target->connectedDependencies.append(dependency);
}

// 定义获取或创建子组件的内部函数
QSharedPointer<SubComponent> DiagnosisGraph::getOrCreateSubComponent(const QString& port, short portType, const QString& funcName) {
    QSharedPointer<SubComponent> subComponent;
    if (nameToNodeMap.contains(funcName) && nameToNodeMap[funcName].contains(port)) {
        subComponent = nameToNodeMap[funcName][port]->containingSubComponent;
    }

    // 如果子组件为空或不存在，则创建一个新的
    if (!subComponent) {
        QString componentName = port.split('.').first();
        QList<QSharedPointer<Node>> nodes = { QSharedPointer<Node>(new Node(port, portType)) };
        subComponent = QSharedPointer<SubComponent>(new SubComponent(nodes, mCompFailureProbMap[componentName]));
        addSubComponent(subComponent);
        //qDebug() << "handleEndNodes:" << funcName << " SubComponent:" << subComponent;
    }
    return subComponent;
}
void DiagnosisGraph::handleEndNodes(const QStringList& currentLink, const QString& functionName) {
    // 检查首末节点
    QString firstPort = currentLink.first();
    QString lastPort = currentLink.last();

    // 获取首、末SubComponent
    auto sourceSubComponent = getOrCreateSubComponent(firstPort, SOURCE_PORT, functionName);
    auto actuatorSubComponent = getOrCreateSubComponent(lastPort, ACTUATOR_PORT, functionName);

    // 将首、末SubComponent分别加入到funcNameToSourceSubComponentMap和funcNameToActuatorSubComponentMap中
    funcNameToSourceSubComponentMap[functionName] = sourceSubComponent;
    funcNameToActuatorSubComponentMap[functionName] = actuatorSubComponent;

    // 如果funcNameToRouteMap中的首末SubComponent尚未设置，则更新
    if (!funcNameToRouteMap[functionName].isEmpty()) {
        if (funcNameToRouteMap[functionName].first().subComponent != sourceSubComponent) {
            funcNameToRouteMap[functionName].prepend(RouteItem{sourceSubComponent}); // 插入到首位置
        }
        if (funcNameToRouteMap[functionName].last().subComponent != actuatorSubComponent) {
            funcNameToRouteMap[functionName].append(RouteItem{actuatorSubComponent}); // 插入到末位置
        }
    }
}

// 获取或创建节点的辅助函数
QSharedPointer<Node> DiagnosisGraph::getNodeOrCreate(const QString& portName, short type, const QString& funcName) {
    if (nameToNodeMap[funcName].contains(portName)) {
        return nameToNodeMap[funcName][portName];
    } else {
        auto newNode = QSharedPointer<Node>(new Node(portName, type));
        addNode(funcName, newNode);
        return newNode;
    }
}

// 该函数处理链路节点的连接问题
// TODO: 后续需完善考虑linkText中存在括号的情况"(and (or (and 1 3) (and 2 4)) 5 (or 6 7) 8)"其中(and )可省略and,可省略最外层的括号"(or (1 3) (2 4)) 5 (or 6 7) 8"
void DiagnosisGraph::handleLinkNodes(const QStringList& currentLink, const QString& currentFunctionName,int level) {
    // 如果已处理此功能，则直接返回
    if (processedFunctionLinks.contains(currentFunctionName)) return;
    processedFunctionLinks.insert(currentFunctionName);
    mFunctionDependencyChain.append(currentFunctionName);

    QList<RouteItem> route;

    for (int i = 1; i < currentLink.size(); i++) {
        // 获取前一个端口和当前端口
        QString prevPort = currentLink[i - 1];
        QString currPort = currentLink[i];

        // 用于标识两个端口是否已经连接
        bool isConnected = false;
        // 遍历所有连接，检查两个端口是否存在于同一连接中
        for (const auto& connection : mPortListInConnectionList) {
            if (connection.contains(prevPort) && connection.contains(currPort)) {
                isConnected = true;
                break;
            }
        }
        // 根据链路位置确定端口类型
        short prevType = (prevPort == currentLink.first()) ? SOURCE_PORT : GENERAL_PORT;
        short currType = (currPort == currentLink.last()) ? ACTUATOR_PORT : GENERAL_PORT;

        // 如果两个端口已连接，则建立一个Edge边连接这两个端口
        if (isConnected) {
            auto sourceNode = getNodeOrCreate(prevPort, prevType, currentFunctionName);
            auto targetNode = getNodeOrCreate(currPort, currType, currentFunctionName);
            auto edge = QSharedPointer<Edge>(new Edge(sourceNode, targetNode));
            edge->level=level;
            addEdge(edge);
            // 如果路径包含此边，记录它
            route.append(RouteItem{edge});
            //qDebug()<<"handleLinkNodes:"<<currentFunctionName<<" edge:"<<edge;
        } else {
            // 如果两个端口未连接，检查它们是否属于同一个器件
            QString prevDevice = prevPort.split('.').first();
            QString currDevice = currPort.split('.').first();
            if (prevDevice == currDevice) {
                // 如果是，创建一个Pathway边连接这两个端口
                auto sourceNode = getNodeOrCreate(prevPort, prevType, currentFunctionName);
                auto targetNode = getNodeOrCreate(currPort, currType, currentFunctionName);
                double fProb = mCompFailureProbMap[prevDevice];
                auto pathway = QSharedPointer<Pathway>(new Pathway(sourceNode, targetNode, fProb));
                addPathway(pathway);
                //qDebug()<<"handleLinkNodes:"<<currentFunctionName<<" pathway:"<<pathway;
                // 同时为这两个端口创建一个SubComponent，并设置isComponentDependency属性
                QList<QSharedPointer<Node>> subComponentNodes = {QSharedPointer<Node>(sourceNode), QSharedPointer<Node>(targetNode)};
                auto subComponent = QSharedPointer<SubComponent>(new SubComponent(subComponentNodes, mCompFailureProbMap[prevDevice]));

                // 查询其对应的器件名是否包含在functionComponentDependencyMap当前功能currentfunctionName对应的functionComponentDependency中
                QString functionComponentDependency = mFunctionInfoMap[mCurrentfunctionName].componentDependency;
                QStringList componentDependencies = functionComponentDependency.split(',');
                bool isDependency = componentDependencies.contains(prevDevice);

                // 设置isComponentDependency属性
                subComponent->isComponentDependency = isDependency;

                // 添加SubComponent到诊断图
                addSubComponent(subComponent);
                route.append(RouteItem{subComponent});
                //qDebug()<<"handleLinkNodes:"<<currentFunctionName<<" subComponent:"<<subComponent;

                // TODO: 后续需完善考虑functionComponentDependency中存在括号的情况
            }
        }
    }
    // 记录当前功能的路由
    funcNameToRouteMap[currentFunctionName] = route;

    handleEndNodes(currentLink,currentFunctionName);
}

void DiagnosisGraph::handleFunctionDependencies(const QString& depFuncString, const QString& mainFunctionName) {
    QString cleanedDepFuncString = depFuncString;
    cleanedDepFuncString.replace(QRegularExpression("\\s+"), " ");  // 将连续的空白字符替换为单个空格
    QStringList parts = cleanedDepFuncString.split(',');
    if (parts.size() < 3) {
        return;  // 如果格式不匹配，则返回
    }
    QString depFuncName = parts[1];

    // 确保给定的功能名存在于功能链路映射中
    if (!mFunctionInfoMap.contains(depFuncName) || !mFunctionInfoMap.contains(mainFunctionName)) {
        return;  // 如果不包含，则直接返回
    }
    QStringList mainFunctionLinkList = mFunctionInfoMap.value(mainFunctionName).link.split(",");

    // 获取相关的端口列表
    QStringList relatedPorts = parts[2].trimmed().split(' ');

    // 从funcNameToActuatorSubComponentMap中找到对应的执行器SubComponent
    QSharedPointer<SubComponent> sourceSubComponent = funcNameToActuatorSubComponentMap[depFuncName];

    // 创建一个set来确保不会为相同的SubComponent重复创建Dependency
    QSet<QString> processedSubComponents;

    // 遍历相关的端口
    for (const auto& port : relatedPorts) {
        // 判断该端口是否存在于mainFunctionLinkList中，并且存在于nameToNodeMap
        if (mainFunctionLinkList.contains(port) && nameToNodeMap[mainFunctionName].contains(port)) {
            QSharedPointer<Node> node = nameToNodeMap[mainFunctionName][port];

            // 使用节点的containingSubComponent属性来找到相应的subComponent
            QSharedPointer<SubComponent> targetSubComponent = node->containingSubComponent;

            if (!processedSubComponents.contains(targetSubComponent->name)) {
                // 获取两个SubComponent之一的失效概率
                QString compName = targetSubComponent->nodes.first()->name.split('.').first();
                double failureProb = mCompFailureProbMap.value(compName, 0.0);

                // 创建一个新的Dependency
                QSharedPointer<Dependency> newDependency = QSharedPointer<Dependency>(new Dependency(depFuncName, sourceSubComponent, targetSubComponent, failureProb));
                addDependency(newDependency);

                // 将该SubComponent的名称添加到已处理的set中，以确保不会重复创建
                processedSubComponents.insert(targetSubComponent->name);

                // 在funcNameToRouteMap中查找相关的RouteItem，并将isDependencyTarget标记为true
                for (RouteItem& routeItem : funcNameToRouteMap[mainFunctionName]) {
                    if (routeItem.subComponent == targetSubComponent) {
                        routeItem.isDependencyTarget = true;
                        routeItem.dependencyFunctionName = depFuncName;
                    }
                }
            }
        }
    }
}
// 该函数添加功能依赖性
void DiagnosisGraph::addFunctionDependencies(const QString& functionName, int level) {
    // 如果已处理此功能，则直接返回
    if (processedFunctions.contains(functionName))return;
    processedFunctions.insert(functionName);

    if (!mFunctionInfoMap.contains(functionName) || mFunctionInfoMap[functionName].functionDependency.isEmpty()) {
        qDebug() << "INFO: Not have FunctionDependency of Function:" << functionName;
        return;
    }

    //获取当前功能的所有依赖功能dependencies
    QStringList dependencies = mFunctionInfoMap[functionName].functionDependency.split(';');

    //遍历当前功能的每一项依赖功能
    for (const auto& depFuncString : dependencies) {
        QString depFuncName = depFuncString.split(",")[1];
        QStringList depFuncLink = mFunctionInfoMap[depFuncName].link.split(',');
        QSharedPointer<SubComponent> depFuncExecSubComp = nullptr;

        //将依赖功能的链路追加到当前的诊断图中
        handleLinkNodes(depFuncLink,depFuncName,level);

        //最后一个为依赖功能的执行器，增加Dependency边，依赖功能（depFuncName）执行器subComponent为source，当前功能（functionName）中的相关端口subComponent为target
        handleFunctionDependencies(depFuncString,functionName);

        // 递归处理当前依赖功能的依赖功能
        addFunctionDependencies(depFuncName,level+1);
    }
}

// 构建图函数
void DiagnosisGraph::buildGraph(const QString& currentfunctionName,
                                const QMap<QString, FunctionInfo>& functionInfoMap,
                                const QList<QStringList>& portListInConnectionList,
                                const QMap<QString, double>& compFailureProbMap) {
    // 更新类成员变量
    mCurrentfunctionName = currentfunctionName;
    mPortListInConnectionList = portListInConnectionList;
    mFunctionInfoMap = functionInfoMap;
    //    mFunctionLinkMap = functionLinkMap;
    //    mFunctionComponentDependencyMap = functionComponentDependencyMap;
    //    mFunctionDependencyMap = functionDependencyMap;
    mCompFailureProbMap = compFailureProbMap;

    processedFunctions.clear();
    processedFunctionLinks.clear();

    // 构建当前功能的主链路的诊断图
    QStringList currentLink = mFunctionInfoMap[currentfunctionName].link.split(',');
    handleLinkNodes(currentLink,mCurrentfunctionName,0);

    // 递归添加当前功能的所有依赖的功能
    addFunctionDependencies(currentfunctionName,1);
}

//第1步：处理currentResultEntityList
//其中有3种结果项：单器件故障、双器件故障、组合故障（1个器件故障+1个观测故障）
//对其的项进行遍历，对每一项的故障概率进行归一化处理：处理后每一项的故障概率=该项原始故障概率/所有结果项的故障概率之和

//第2步：在处理的过程中同时构建一个QMap<QString,double> failureModeProbMap中,QString用于存储故障模式的名称（是唯一的，不能重复），double用于存储故障概率。
//对于单器件故障，构建QMap时需要注意需要合并同一个器件的多种故障模式（相同器件的不同故障模式直接加和）;
//对于双器件故障，构建QMap时需要注意需要合同相同器件对的多种故障模式（相同器件对的不同故障模式直接加和）;
//对于组合故障（1个器件故障+1个观测故障），构建构建QMap时需要注意，需要对器件名称进行处理，不要包含观测故障的名称，例如故障器件对名称为"L21,obs8",故障模式为"导线断开,观测错误",则QMap的QString只需要记录L21，需要合并同一个器件的多种故障模式（相同器件的不同故障模式直接加和）
//对于组合故障的判断方法为：检查getFailureModes()中是否包含"观测错误"，如果是，则检查getComponentNames以逗号分割后是否含有与getFailureModes()相同数量的部分，将"观测错误"对应的部分去掉后作为QMap<QString,double>中的QString
QMap<QString, double> DiagnosisGraph::normalizeFaultProbabilities(QList<resultEntity>& currentResultEntityList) {
    // 第1步
    double totalProbability = 0.0;
    for (const auto& result : currentResultEntityList) {
        totalProbability += result.getProbability(); // 计算所有结果项的故障概率之和
    }

    // 第2步
    QMap<QString, double> failureModeProbMap;
    for (auto& result : currentResultEntityList) {
        double normalizedProbability = result.getProbability() / totalProbability; // 归一化故障概率
        //result.setProbability(normalizedProbability); // 更新故障概率

        QStringList componentNames = result.getComponentNames().simplified().split(",");
        QStringList failureModes = result.getFailureModes().simplified().split(",");

        // 检查failureModes与componentNames是否含有数量相同的元素
        if (failureModes.size() != componentNames.size()) {
            qDebug()<<"normalizeFaultProbabilities: failureModes.size() != componentNames.size()";
            continue; // 不匹配的情况跳过
        }
        // 组合故障的判断方法
        if (failureModes.contains("观测错误")) {
            for (int i = componentNames.size() - 1; i >= 0; --i) {
                //qDebug()<<"failureModes[i]:"<<failureModes[i];
                if (failureModes[i] == "观测错误") {
                    componentNames.removeAt(i);
                    failureModes.removeAt(i);
                }
            }
        }
        // 如果是双器件故障，则对器件名称进行排序，确保表示一致
        if (componentNames.size() >= 2) {
            std::sort(componentNames.begin(), componentNames.end());
        }

        QString componentName = componentNames.join(",");

        // 对于单器件故障、双器件故障和组合故障，合并同一个器件（对）的多种故障模式
        if (failureModeProbMap.contains(componentName)) {
            failureModeProbMap[componentName] += normalizedProbability;
        } else {
            failureModeProbMap[componentName] = normalizedProbability;
        }
    }
    return failureModeProbMap;
}

//通过DiagnosisGraph，找到不重复的所有subComponent名称，属于同一个器件的subComponent名均摊同一个器件的故障概率，得到subComponent名-故障概率Map
//subComponents容器：QList<QSharedPointer<SubComponent>> subComponents;
//subComponents中的subComponent名的格式："KM.A.1&A.2&B"，检查其是否包含"."，如果包含的话按"."进行分割，取第一部分即为器件名
//name相同的subComponent算一个subComponent，所有器件名相同的subComponent均摊该器件的故障概率
QMap<QString, double> DiagnosisGraph::calSubComponentFailureProb(QMap<QString, double>& failureModeProbMap) {
    QMap<QString, double> subCompProbMap; // 存储逻辑支路的故障概率
    QMap<QString, int> deviceSubComponentCountMap; // 存储器件内subComponent的数量
    for (const auto& subComponent : subComponents) {
        // 得到subComponent的名称
        QString subComponentName = subComponent->name;
        //qDebug()<<"subComponentName:"<<subComponentName;
        QStringList parts = subComponentName.split('.');
        QString deviceName = parts.size() > 1 ? parts[0] : QString();

        // 从failureModeProbMap找到器件的故障概率
        if(!subCompProbMap.contains(subComponentName)){
            subCompProbMap.insert(subComponentName,failureModeProbMap.value(deviceName, 0.0));
            deviceSubComponentCountMap[deviceName] += 1;
        }
    }

    // 均摊每个器件的故障概率并存储到subCompProbMap
    auto it = subCompProbMap.begin();
    while (it != subCompProbMap.end()) {
        if (it.value() > 0.0) {
            QStringList parts = it.key().split('.');
            QString deviceName = parts.size() > 1 ? parts[0] : QString();
            if(deviceSubComponentCountMap[deviceName]<1)continue;
            it.value() = it.value() / deviceSubComponentCountMap[deviceName];
            ++it; // 仅在未删除当前项时递增迭代器
        }
        else { // 检查概率是否小于等于0
            it = subCompProbMap.erase(it); // 删除该项并获取下一个迭代器
        }
    }
    return subCompProbMap;
}

double DiagnosisGraph::calcEquivalentFailureProb(const RouteItem& currentSubComp, QSet<QString>& processedSubComps, bool readOnly) {
    if (!funcNameToRouteMap.contains(currentSubComp.dependencyFunctionName)) return 0.0;

    double equivalentFailureProb = 0.0;
    const auto& route = funcNameToRouteMap[currentSubComp.dependencyFunctionName];

    for (const RouteItem& routeItem : route) {
        if (routeItem.subComponent) {
            QString subComponentName = routeItem.subComponent->name;
            if (processedSubComps.contains(subComponentName)) continue;
            if (!readOnly) processedSubComps.insert(subComponentName);
            double subComponentFailureProb = subComponentProbMap.value(subComponentName, 0.0);
            if (routeItem.isDependencyTarget && !routeItem.dependencyFunctionName.isEmpty()) {
                equivalentFailureProb +=subComponentFailureProb + calcEquivalentFailureProb(routeItem, processedSubComps, readOnly);
            } else {
                equivalentFailureProb += subComponentFailureProb;
            }
            //qDebug()<<subComponentName<<":"<<equivalentFailureProb;
        }
    }
    return equivalentFailureProb;
}

double DiagnosisGraph::calcProbability(const RouteItem& routeItem, QSet<QString>& processedSubComps, QSet<QString>& processedDepFuncs) {
    double Pij = 0.0;
    if (routeItem.subComponent) {
        const QString& subComponentName = routeItem.subComponent->name;
        if (!processedSubComps.contains(subComponentName) && subComponentProbMap[subComponentName] > 0.0) {
            Pij = subComponentProbMap[subComponentName];
            if (routeItem.isDependencyTarget && !processedDepFuncs.contains(routeItem.dependencyFunctionName)) {
                //qDebug()<<"calcEquivalentFailureProb before:"<<Pij;
                Pij += calcEquivalentFailureProb(routeItem, processedSubComps, false);
                processedDepFuncs.insert(routeItem.dependencyFunctionName);
                //qDebug()<<"calcEquivalentFailureProb after:"<<Pij;
            }
            processedSubComps.insert(subComponentName);
        }
    }
    return Pij;
}
double DiagnosisGraph::calcTestEntropy(QList<RouteItem>& route, int edgeIndex) {
    double Ppass = 0.0, Pfail = 0.0, InformDi = 0.0, InformUi = 0.0, InformBeforeTest = 0.0;
    QSet<QString> processedSubComps, processedDepFuncs;
    processedDepFuncs.insert(mCurrentfunctionName);

    for (int i = 0; i < route.size(); ++i) {
        double Pij=calcProbability(route[i], processedSubComps, processedDepFuncs);
        if(Pij<=0)continue;
        InformBeforeTest += -Pij * log(Pij);
        if (i < edgeIndex) {
            Ppass += Pij;
            InformUi += -Pij * log(Pij);
        } else if (i > edgeIndex) {
            Pfail += Pij;
            InformDi += -Pij * log(Pij);
        }
    }
    //    QString routeItemName;
    //    if (route[edgeIndex].subComponent)routeItemName=route[edgeIndex].subComponent->name;
    //    if (route[edgeIndex].edge)routeItemName=route[edgeIndex].edge->name;
    //    qDebug()<<"name:"<<routeItemName<<" Ppass:"<<(1-Ppass)<<" Pfail:"<<(1-Pfail)<<" sum:"<< (Ppass+Pfail);
    return (1 - Ppass) * InformDi + (1 - Pfail) * InformUi - InformBeforeTest;
}

QList<QSharedPointer<Edge>> DiagnosisGraph::calcRouteEntropy(QList<RouteItem>& route){
    QSet<QString> processedEdge;
    QList<QSharedPointer<Edge>> testEdgeList;
    for (int edgeIndex = 0; edgeIndex < route.size(); edgeIndex++) {
        const auto& routeItem = route[edgeIndex];
        if (routeItem.edge) {
            QString edgeName = routeItem.edge->name;
            if(processedEdge.contains(edgeName)) continue;
            processedEdge.insert(edgeName);
            double entropy = calcTestEntropy(route, edgeIndex);
            routeItem.edge->entropy = entropy;
            testEdgeList.append(routeItem.edge);
        }
    }
    return testEdgeList;
}
QList<RouteItem> DiagnosisGraph::addDepToRoute(const QString functionName, QSet<QString>& processedRouteItem, QSet<QString>& processedFunc) {
    QList<RouteItem> route = funcNameToRouteMap[functionName];
    for (int i = 0; i < route.size(); i++) {
        auto& routeItem = route[i];
        if (routeItem.edge) {
            QString edgeName = routeItem.edge->name;
            if(!edgeName.isEmpty() && !processedRouteItem.contains(edgeName))processedRouteItem.insert(edgeName);
        }
        if (!routeItem.subComponent)continue;
        processedRouteItem.insert(routeItem.subComponent->name);
        // 如果该项是依赖目标，则构造需递归处理依赖功能的链路
        if (!routeItem.isDependencyTarget)continue;
        routeItem.isDependencyTarget = false;
        QString depFuncName = routeItem.dependencyFunctionName;
        if (funcNameToRouteMap[depFuncName].isEmpty() || processedFunc.contains(depFuncName)) continue;
        processedFunc.insert(depFuncName);
        QSet<QString> processedItem;
        QList<RouteItem> dependentRoute = addDepToRoute(depFuncName, processedItem, processedFunc);
        auto it = route.begin() + i;
        bool isFirstItem = true;
        for (const auto& item : dependentRoute) {
            QString itemName = item.edge ? item.edge->name : (item.subComponent ? item.subComponent->name : QString());
            if (processedRouteItem.contains(itemName)) continue;
            if (isFirstItem && item.edge) continue;
            isFirstItem = false;
            processedRouteItem.insert(itemName);
            it = route.insert(it, item);
            ++it;
            ++i;
        }
    }
    return route;
}

QList<TestItem> DiagnosisGraph::getRecommendTestItemList(QString functionName,QList<resultEntity>& currentResultEntityList,bool isPenetrativeSolve) {

    //第1步：处理currentResultEntityList,概率归一化，同时将结果保存到failureModeProbMap中
    QMap<QString, double> failureModeProbMap = normalizeFaultProbabilities(currentResultEntityList);
        qDebug()<<"failureModeProbMap:"<<failureModeProbMap; double sumOfProbabilities = 0.0;
        for (auto it = failureModeProbMap.begin(); it != failureModeProbMap.end(); ++it) {sumOfProbabilities += it.value();qDebug()<<it.key()<<":"<<it.value();}
        qDebug() << "Sum of probabilities in failureModeProbMap: " << sumOfProbabilities;

    //第2步：通过DiagnosisGraph，找到不重复的所有subComponent名称，属于同一个器件的subComponent名均摊同一个器件的故障概率，得到subComponent名-故障概率Map
    subComponentProbMap = calSubComponentFailureProb(failureModeProbMap);
    qDebug() << "getRecommendTestItemList: subComponentProbMap:";QMapIterator<QString, double> iter1(subComponentProbMap);double prob=0.0;
    while (iter1.hasNext()) {iter1.next();prob+=iter1.value();qDebug() << iter1.key() << ":" << iter1.value();}
    qDebug()<<"prob sum:"<<prob;

    //第3步：根据主链路在DiagnosisGraph中找到从源subComponnet向执行器subComponent的路径
    //已完成，路径信息保存在QMap<QString, QList<RouteItem>> funcNameToRouteMap中，直接可使用

    //第4步：遍历路径中的所有Edge，逐项计算edge的信息熵；
    QSet<QString> processedEdge;
    QSet<QString> processedFunc;
    QList<RouteItem> route = funcNameToRouteMap[functionName];

    if(isPenetrativeSolve){
        processedFunc.insert(functionName);
        route = addDepToRoute(functionName,processedEdge,processedFunc);
        QSet<QString> nonZeroFailureSubComponents = QSet<QString>::fromList(subComponentProbMap.keys());
        qDebug()<<"nonZeroFailureSubComponents:"<<nonZeroFailureSubComponents;

        //优化对初始route的选择，从QStringList mFunctionDependencyChain;的尾部开始遍历，如果其对应的route包含所有subComponentProbMap中故障概率不为0的器件，则选其作为初始route。
        //计算步骤：遍历subComponentProbMap，将其中故障概率大于0的器件名称加入一个QSet中，从QStringList mFunctionDependencyChain;的尾部开始遍历，获取每一项功能对应的route，将其中的subComponent名加入一个QSet中
        //比较这两个QSet，如果route中器件的QSet包含故障概率大于0的QSet，则停止遍历，选当前的route作为初始route
        for (int i = mFunctionDependencyChain.count() - 1; i >= 0; --i) {
            const QString &function = mFunctionDependencyChain[i];
            QList<RouteItem> potentialRoute = funcNameToRouteMap[function];
            QSet<QString> routeSubComponents;
            for (const RouteItem &routeItem : potentialRoute) {
                if(routeItem.subComponent)routeSubComponents.insert(routeItem.subComponent->name);
            }
            if (routeSubComponents.contains(nonZeroFailureSubComponents)) {
                route = potentialRoute;
                qDebug()<<"Initial route of function is:"<<function;
                break;
            }
        }
    }
    qDebug()<<"route:"<<route;
    QList<QSharedPointer<Edge>> testEdgeList = calcRouteEntropy(route);

    //ToDo：移动到建立route的子函数中去
    QStringList levelToParentList;
    // 从后往前遍历testEdgeList
    for (int i = testEdgeList.size() - 1; i >= 0; --i) {
        const auto& edge = testEdgeList[i];
        edge->parents.clear();
        int mLevel = edge->level;
        while (levelToParentList.size() <= mLevel) {
            levelToParentList.append(QString());
        }
        // 根据 level 的变化来更新 QStringList 和 parent
        levelToParentList[mLevel] = edge->name;

        if (mLevel > 0 && !levelToParentList[mLevel - 1].isEmpty()) {
            edge->parents.append(levelToParentList[mLevel - 1]);
        }
    }

    // 根据信息熵对边进行排序
    std::sort(testEdgeList.begin(), testEdgeList.end(), [](const QSharedPointer<Edge>& a, const QSharedPointer<Edge>& b) {
        return a->entropy < b->entropy; // 升序排列
    });
    // 新建一个QList<QSharedPointer<Edge>> reorderedEdgeList
    QList<QSharedPointer<Edge>> reorderedEdgeList;

    // 使用一个哈希表来存储每个edge名称及其在reorderedEdgeList中的索引
    QHash<QString, int> edgeNameToIndex;

    int processedEdgeCount = 0;
    // 对于每个不同的level
    for (int currentLevel = 0; ; ++currentLevel) {
        // 遍历testEdgeList
        for (const auto& edge : testEdgeList) {
            if (edge->level != currentLevel) continue; // 跳过不在当前level的edge
            ++processedEdgeCount; // 增加已处理的edge的数量
            int insertPos = reorderedEdgeList.size(); // 默认插入位置是列表的末尾

            // 检查这个edge的所有parents
            for (const auto& parentName : edge->parents) {
                if (edgeNameToIndex.contains(parentName)) {
                    // 如果parent已经在reorderedEdgeList中，则更新插入位置
                    insertPos = std::min(insertPos, edgeNameToIndex[parentName]);
                }
            }
            if (!edge->parents.isEmpty() && insertPos < reorderedEdgeList.size()) {
                if (edge->entropy < reorderedEdgeList[insertPos]->entropy) edge->recommended = true;
                else edge->recommended = false;
            } else {
                if (edge->entropy < 0.0) edge->recommended = true;
                else edge->recommended = false;
            }

            // 在计算出的插入位置插入当前edge
            reorderedEdgeList.insert(insertPos, edge);

            // 更新哈希表
            for (int i = insertPos; i < reorderedEdgeList.size(); ++i) {
                edgeNameToIndex[reorderedEdgeList[i]->name] = i;
            }
        }

        if (processedEdgeCount >= testEdgeList.size()) break;
    }
    // 输出testEdgeList
    //    qDebug() << "reorderedEdgeList Edge List:";
    //    for (const auto& edge : reorderedEdgeList)qDebug() << "Edge Name:" << edge->name <<"Level:" << edge->level<< ", Parents:" << edge->parents << ", Entropy:" << edge->entropy<< ", R:" <<edge->recommended;
    return generateTestItemsFromEdges(reorderedEdgeList);
}

QList<TestItem> DiagnosisGraph::generateTestItemsFromEdges(const QList<QSharedPointer<Edge>>& testEdgeList) {
    QList<TestItem> recommendTestItemList;
    QSet<QString> testNameSet;
    auto isWire = [](const QString& name) {
        QRegExp pattern("^L(\\d+-)*\\d+(\\.\\d+)?$");
        return pattern.exactMatch(name);
    };

    for (const auto& edge : testEdgeList) {
        //qDebug()<<"generateTestItemsFromEdges:"<<edge->name<<" entropy:"<< edge->entropy;
        TestItem testItem;
        testItem.confidence = edge->entropy;
        QString testNodeName;
        QString sourceNodeName= edge->source->name;
        QString targetNodeName = edge->target->name;
        if (isWire(sourceNodeName) && !isWire(targetNodeName)) {
            testNodeName = targetNodeName;
        }
        else if (!isWire(sourceNodeName) && isWire(targetNodeName)) {
            testNodeName = sourceNodeName;
        }
        else {
            testNodeName = sourceNodeName;
        }
        //testItem.variable = QString(" ").repeated(edge->level * 4) +testNodeName + ".u";
        //液压
        testItem.variable = QString(" ").repeated(edge->level * 4) +testNodeName + ".p";
        if(edge->recommended)testItem.checkState=Qt::Checked;
        else testItem.checkState=Qt::Unchecked;
        testItem.level = edge->level;
        //if(!testNameSet.contains(testItem.variable)){
        recommendTestItemList.append(testItem);
        testNameSet.insert(testItem.variable);
        //}
    }

    return recommendTestItemList;
}

QList<QMap<QString,double>> DiagnosisGraph::getRecommendFunction(QList<resultEntity>& currentResultEntityList) {
    // TODO: 返回推荐的功能列表，每个功能与其相关的系统综合信息熵相关
    QList<QMap<QString,double>> recommendedFunctions;
    return recommendedFunctions;
}

QDebug operator<<(QDebug dbg, const Node& node) {
    dbg.nospace() << "Node(Name: " << node.name << ")";
    return dbg.maybeSpace();
}
QDebug operator<<(QDebug dbg, const Pathway& pathway) {
    dbg.nospace() << "Pathway(Source: " << pathway.source->name << ", Target: " << pathway.target->name << ", FailureProbability: " << pathway.failureProbability << ")";
    return dbg.maybeSpace();
}

QDebug operator<<(QDebug dbg, const Edge& edge) {
    dbg.nospace() << "Edge(Name:" << edge.name<<" Entropy:" << edge.entropy<<")\n";
    return dbg.maybeSpace();
}

QDebug operator<<(QDebug dbg, const Dependency& dependency) {
    dbg.nospace() << "Dependency(Source: " << dependency.source->name << ", Target: " << dependency.target->name << ", FailureProbability: " << dependency.failureProbability << ")";
    return dbg.maybeSpace();
}

QDebug operator<<(QDebug dbg, const SubComponent& subComponent) {
    dbg.nospace() << "SubComponent(Name: " << subComponent.name <<", Nodes: ";
    // 输出所有节点的名称
    QStringList nodeNames;
    for (const auto& node : subComponent.nodes)nodeNames.append(node->name);
    dbg.nospace() << nodeNames.join(", ")<<", FailureProbability: " << subComponent.failureProbability << ")";
    return dbg.maybeSpace();
}

QDebug operator<<(QDebug dbg, const DiagnosisGraph& diagnosisGraph) {
    dbg.nospace() << "DiagnosisGraph\n";
    dbg.nospace() << "Nodes:\n";
    for(const auto& node : diagnosisGraph.nodes) dbg.nospace() << *node << "\n";
    dbg.nospace() << "subComponents:\n";
    for(const auto& subComponent : diagnosisGraph.subComponents)dbg.nospace() << *subComponent << "\n";
    dbg.nospace() << "Edges:\n";
    for(const auto& edge : diagnosisGraph.edges) dbg.nospace() << *edge << "\n";
    dbg.nospace() << "Dependencies:\n";
    for(const auto& dependency : diagnosisGraph.dependencies) dbg.nospace() << *dependency << "\n";
    dbg.nospace() << "Pathways:\n";
    for(const auto& pathway : diagnosisGraph.pathways) dbg.nospace() << *pathway << "\n";
    return dbg.space();
}

QDebug operator<<(QDebug debug, const RouteItem& item) {
    QDebugStateSaver saver(debug);
    if (item.subComponent)debug.nospace() << "RouteItem(subComponent=" << item.subComponent->name;
    else debug.nospace() << "RouteItem(edge=" << item.edge->name;
    if (item.isDependencyTarget)debug.nospace() <<", TargetDepFunc=" << item.dependencyFunctionName;
    debug.nospace()<< ")\n";
    return debug;
}

