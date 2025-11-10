#include "graphadjlist.h"

GraphAdjList::GraphAdjList()
{
    /*
    .	构造函数：初始化图类型
    */
    this->type = UDG;
    this->vexNum = 0;
    this->arcNum = 0;

    MyTree = new ComboTree();
}


GraphAdjList::GraphAdjList(int type)
{
    /*
    .	构造函数：初始化图类型
    */
    this->type = type;
    this->vexNum = 0;
    this->arcNum = 0;

    MyTree = new ComboTree();
}

GraphAdjList::~GraphAdjList()
{
    /*
    .	析构函数：销毁图
    */

    for(int i=0; i<vexNum; i++)
    {
        QList<ArcNode*> arc_temp;

        ArcNode* p = vexs->first;

        while(p!=nullptr)
        {
            arc_temp.push_back(p);
            p = p->next;
        }

        for(int i=arc_temp.length()-1; i>=0; i--)
            delete arc_temp[i];
    }

    delete MyTree;
}

void GraphAdjList::Init(QVector<QString> * vexs, QVector<ArcData> * arcsList)
{
    /*
    .	初始化顶点、边数据，并构建 图|网
    .	入参：
    .		vexs: 顶点 列表
    .		arcsList: 边数据 列表
    */
    //1.创建顶点集
    _CreateVexSet(vexs);
    //2.根据图类型，创建指定的图
    switch (this->type)
    {
    case DG:
        _CreateDG(arcsList); break;
    case UDG:
        _CreateUDG(arcsList); break;
    case DN:
        _CreateDN(arcsList); break;
    case UDN:
        _CreateUDN(arcsList); break;
    default:
        break;
    }

    //3.计算每个顶点的出度和入度
    _CalculateOut();
}

void GraphAdjList::ClearGraph()
{
    for(int i=0; i<vexNum; i++)
    {
        //清空顶点名
        vexs[i].name.clear();

        //删除边
        QList<ArcNode*> arc_temp;

        ArcNode* p = vexs[i].first;
        arc_temp.push_back(p);

        while(p!=nullptr)
        {
            p = p->next;
            arc_temp.push_back(p);
        }

        for(int i=arc_temp.length()-1; i>=0; i--)
        {
            p = arc_temp[i];
            delete p;
        }


    }

    //清空MyTree
    MyTree->ClearTree();

    //初始化数据
    vexNum = 0;
    arcNum = 0;
    for(int i=0; i<_MAX_VERTEX_NUM; i++)
    {
        vexs_visited[i] = 0;
        vexs_comb_visited[i] = 0;
    }
}

void GraphAdjList::_CreateVexSet(QVector<QString> * vexs)
{
//  创建顶点集合
    QString vertex = "";
    //顶点最大数校验
    if (vexs->length() > this->_MAX_VERTEX_NUM)
    {
        return;
    }
//  遍历顶点表，无重复插入顶点，并计数顶点数
    for (int i = 0; i < vexs->length(); i++)
    {
        vertex = vexs->at(i);
        if (_Locate(vertex) == -1)
        {
            this->vexs[this->vexNum].name = vertex;
            this->vexs[this->vexNum].first = nullptr;
            this->vexs[this->vexNum].out_num = 0;
            this->vexNum++;
        }
    }
}

void GraphAdjList::_CreateDG(QVector<ArcData> * arcsList)
{

//  创建有向图
//  邻接矩阵为 非对称边

    //初始化临时 边对象
    ArcData arcData;
    //初始化 Tail Head 顶点下标索引
    int tail_node = 0, tail_port=0, head_node = 0, head_port=0;
    //遍历边数据列表
    for (int i = 0; i < arcsList->length(); i++)
    {
        //按序获取边（弧）
        arcData = arcsList->at(i);
        //定位（或设置）边的两端顶点位置
        tail_node = _Locate(arcData.Tail);
        head_node = _Locate(arcData.Head);
        //插入边
        _InsertArc(tail_node, head_node, arcData.Weight);
    }
}

void GraphAdjList::_CreateUDG(QVector<ArcData> * arcsList)
{

//    创建无向图
//    邻接矩阵为 对称边

    //初始化临时 边对象
    ArcData arcData;
    //初始化 Tail Head 顶点下标索引
    int tail_node = 0, head_node = 0;
    //遍历边数据列表
    for (int i = 0; i < arcsList->length(); i++)
    {
        //按序获取边（弧）
        arcData = arcsList->at(i);
        //定位（或设置）边的两端顶点位置
        tail_node = _Locate(arcData.Tail);
        head_node = _Locate(arcData.Head);
        //插入边
        _InsertArc(tail_node, head_node, arcData.Weight);
        _InsertArc(head_node, tail_node, arcData.Weight);
    }
}

void GraphAdjList::_CreateDN(QVector<ArcData> * arcsList)
{
//    创建有向网
//    邻接矩阵为 非对称矩阵
    //初始化临时 边对象
    ArcData  arcData;
    //初始化 Tail Head 顶点下标索引
    int tail_node = 0, head_node = 0;
    //遍历边数据列表
    for (int i = 0; i < arcsList->length(); i++)
    {
        //按序获取边（弧）
        arcData = arcsList->at(i);
        //定位（或设置）边的两端顶点位置
        tail_node = _Locate(arcData.Tail);
        head_node = _Locate(arcData.Head);
        //插入边
        _InsertArc(tail_node, head_node, arcData.Weight);
    }
}

void GraphAdjList::_CreateUDN(QVector<ArcData> * arcsList)
{

//    创建无向网
//    邻接矩阵为 对称矩阵

    //初始化临时 边对象
    ArcData arcData;
    //初始化 Tail Head 顶点下标索引
    int tail_node = 0, head_node = 0;
    //遍历边数据列表
    for (int i = 0; i < arcsList->length(); i++)
    {
        //按序获取边（弧）
        arcData = arcsList->at(i);
        //定位（或设置）边的两端顶点位置
        tail_node = _Locate(arcData.Tail);
        head_node = _Locate(arcData.Head);
        //插入边
        _InsertArc(tail_node, head_node, arcData.Weight);
        _InsertArc(head_node, tail_node, arcData.Weight);
    }
}

int GraphAdjList::_Locate(QString& vertex)
{

//    定位顶点元素位置
//    后期可改成【字典树】，顶点数超过100个后定位顶点位置可更快
    //遍历定位顶点位置
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        if (vertex == this->vexs[i].name)
        {
            return i;
        }
    }
    //cout <<  << "顶点[" << vertex << "]不存在。" << ;
    return -1;
}

void GraphAdjList::_InsertArc(int tail, int head, int weight)
{
    if(tail<0||tail>=_MAX_VERTEX_NUM||head<0||head>=_MAX_VERTEX_NUM)
        return;

//    插入边（元操作，不分有向/无向）
    //边结点指针：初始化为 弧尾 指向的第一个边
    ArcNode * p = this->vexs[tail].first;
    //初始化 前一边结点的指针
    ArcNode * q = nullptr;
    //重复边布尔值
    bool exist = false;
    //1.边的重复性校验
    while (p != nullptr)
    {
        //若已存在该边，则标记为 存在 true
        if (p->adjVex == head)
        {
            exist = true;
            break;
        }
        //若不是该边，继续下一个边校验
        q = p;
        p = p->next;
    }
    //2.1.如果边存在，则跳过，不做插入
    if (exist)
        return;
    //2.2.边不存在时，创建边
    ArcNode * newArc = new ArcNode();
    newArc->adjVex = head;
    newArc->weight = weight;
    newArc->next = nullptr;
    //3.1.插入第一条边
    if (q == nullptr)
    {
        this->vexs[tail].first = newArc;
    }
    //3.2.插入后序边
    else
    {
        q->next = newArc;
    }
    //4.边 计数
    this->arcNum++;
}

void GraphAdjList::InsertArc(ArcData * arcData)
{
    /*
    .	插入边（含有向/无向操作）
    */
    //初始化 Tail Head 顶点下标索引
    int tail_node = 0, head_node = 0;
    tail_node = _Locate(arcData->Tail);

    head_node = _Locate(arcData->Head);
    //根据图类型，插入边
    switch (this->type)
    {
    case DG:
        _InsertArc(tail_node, head_node, arcData->Weight);
        break;
    case UDG:
        _InsertArc(tail_node, head_node, arcData->Weight);
        _InsertArc(head_node, tail_node, arcData->Weight);
        break;
    case DN:
        _InsertArc(tail_node, head_node, arcData->Weight);
        break;
    case UDN:
        _InsertArc(tail_node, head_node, arcData->Weight);
        _InsertArc(head_node, tail_node, arcData->Weight);
        break;
    default:
        break;
    }
}

void GraphAdjList::_DeleteArc(int tail, int head)
{

    /*
    .	删除边（元操作，不分有向/无向）
    */
    //边结点指针：初始化为 弧尾 指向的第一个边
    ArcNode * p = this->vexs[tail].first;
    //初始化 前一边结点的指针
    ArcNode * q = NULL;
    //1.遍历查找边
    while (p != NULL)
    {
        //若存在该边，则结束循环
        if (p->adjVex == head)
        {
            break;
        }
        //若不是该边，继续下一个边
        q = p;
        p = p->next;
    }
    //2.1.边不存在
    if (p == NULL)
    {
        qDebug() << endl << "边[" << this->vexs[head].name << "->" << this->vexs[head].name << "]不存在。" << endl;
        return;
    }
    //2.2.边存在，删除边
    //2.2.1.若为第一条边
    if (q == NULL)
    {
        this->vexs[tail].first = p->next;
    }
    //2.2.2.非第一条边
    else
    {
        q->next = p->next;
    }
    //3.释放 p
    delete p;
}

void GraphAdjList::DeleteArc(ArcData * arcData)
{
    /*
    .	删除边（含有向/无向操作）
    */
    //初始化 Tail Head 顶点下标索引
    int tail_node = 0, head_node = 0;
    tail_node = _Locate(arcData->Tail);
    head_node = _Locate(arcData->Head);

    //根据图类型，删除边
    switch (this->type)
    {
    case DG:
        _DeleteArc(tail_node, head_node);
        break;
    case UDG:
        _DeleteArc(tail_node, head_node);
        _DeleteArc(head_node, tail_node);
        break;
    case DN:
        _DeleteArc(tail_node, head_node);
        break;
    case UDN:
        _DeleteArc(tail_node, head_node);
        _DeleteArc(head_node, tail_node);
        break;
    default:
        break;
    }
}

void GraphAdjList::Display()
{
    /*
    .	显示 图|网
    */
    //初始化边表结点指针
    ArcNode * p = NULL;
    qDebug()  << "邻接表：";
    //遍历顶点表
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        //空顶点（在删除顶点的操作后会出现此类情况）
        if (this->vexs[i].name == "")
        {
            continue;
        }
        //输出顶点.00.
        qDebug() << "[" << i << "]" << this->vexs[i].name << "出度" << this->vexs[i].out_num;
        //遍历输出边顶点
        p = this->vexs[i].first;
        while (p != NULL)
        {
            qDebug() << "[" << p->adjVex << "," << p->weight << "] ";
            p = p->next;
        }
    }
}

void GraphAdjList::_DFS_R(int index)
{
    /*
    .	深度优先遍历 递归
    */
    //2.初始化顶点访问数组
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        this->vexs_visited[i] = 0;
    }

    //1.访问顶点，并标记已访问
    qDebug() << this->vexs[index].name << " ";
    this->vexs_visited[index] = 1;
    //2.遍历访问其相邻顶点
    ArcNode * p = this->vexs[index].first;
    int adjVex = 0;
    while (p != NULL)
    {
        adjVex = p->adjVex;
        //当顶点未被访问过时，可访问
        if (this->vexs_visited[adjVex] != 1)
        {
            _DFS_R(adjVex);
        }
        p = p->next;
    }
}

void GraphAdjList::Display_DFS_R(QString *vertex)
{
    /*
    .	从指定顶点开始，深度优先 递归 遍历
    */
    //1.判断顶点是否存在
    int index = _Locate(*vertex);
    if (index == -1)
        return;
    //2.初始化顶点访问数组
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        this->vexs_visited[i] = 0;
    }
    //3.深度优先遍历 递归
    qDebug() << "深度优先遍历（递归）：（从顶点" << *vertex << "开始）";
    _DFS_R(index);
}

void GraphAdjList::_DFS(int index)
{

//    	深度优先遍历 非递归

    //2.初始化顶点访问数组
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        this->vexs_visited[i] = 0;
    }

    //1.访问第一个结点，并标记为 已访问
    qDebug() << this->vexs[index].name << " ";
    vexs_visited[index] = 1;
    //初始化 边结点 栈
    QList<ArcNode*> * s = new QList<ArcNode*>();
    //初始化边结点 指针
    ArcNode * p = this->vexs[index].first;
    //2.寻找下一个（未访问的）邻接结点

    int depth = 0;    //深度，判断是否搜索到底
    while (!s->isEmpty() || p != NULL)
    {
        //2.1.未访问过，则访问 （纵向遍历）
        if (vexs_visited[p->adjVex] != 1)
        {
            //访问结点，标记为访问，并将其入栈
//            qDebug() << this->vexs[p->adjVex].name << " ";
            vexs_visited[p->adjVex] = 1;
            s->push_back(p);
            //指针 p 移向 此结点的第一个邻接结点
            p = this->vexs[p->adjVex].first;

            if(p!=nullptr)
                depth = s->length();
        }
        //2.2.已访问过，移向下一个边结点 （横向遍历）
        else
        {
            p = p->next;
        }
        //3.若无邻接点，则返回上一结点层，并出栈边结点
        if (p == NULL&&!s->isEmpty())
        {
            if(depth == s->length())
            {
                QStringList out;
                for(int i=0; i<s->count();i++)
                    out << this->vexs[s->at(i)->adjVex].name;

                out << "一套连接";

                qDebug()<<out;
            }

            p = s->takeLast();
        }
    }
    //释放 栈
    delete s;
}

void GraphAdjList::Display_DFS(QString *vertex)
{

//    	从指定顶点开始，深度优先 非递归 遍历

    //1.判断顶点是否存在
    int index = _Locate(*vertex);
    if (index == -1)
        return;
    //2.初始化顶点访问数组
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        this->vexs_visited[i] = 0;
    }
    //3.深度优先遍历 递归
    qDebug() << "深度优先遍历（非递归）：（从顶点" << *vertex << "开始）";
    _DFS(index);
}

void GraphAdjList::Display_BFS(QString *vertex)
{
    /*
    .	从指定顶点开始，广度优先遍历
    */
    //1.判断顶点是否存在
    int index = _Locate(*vertex);
    if (index == -1)
        return;
    //2.初始化顶点访问数组
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        this->vexs_visited[i] = 0;
    }
    //3.广度优先遍历
    qDebug() << "广度优先遍历：（从顶点" << *vertex << "开始）";
    //3.1.初始化队列
    QQueue<int> * vexQ = new QQueue<int>();
    //3.2.访问开始顶点，并标记访问、入队
    qDebug() << this->vexs[index].name << "从这个端点开始";
    this->vexs_visited[index] = 1;
    vexQ->enqueue(index);
    //3.3.出队，并遍历邻接顶点（下一层次），访问后入队
    ArcNode * p = NULL;
    int adjVex = 0;
    while (!vexQ->isEmpty())
    {
        index = vexQ->dequeue();
        p = this->vexs[index].first;
        //遍历邻接顶点
        while (p != NULL)
        {
            adjVex = p->adjVex;
            //未访问过的邻接顶点
            if (this->vexs_visited[adjVex] != 1)
            {
                //访问顶点，并标记访问、入队
                qDebug() << this->vexs[adjVex].name << " ";
                this->vexs_visited[adjVex] = 1;
                vexQ->enqueue(adjVex);
            }
            p = p->next;
        }
    }

    //4.释放队列
    int e;
    while (!vexQ->isEmpty())
    {
        e = vexQ->dequeue();
    }
    delete vexQ;
}

QList<QStringList> GraphAdjList::CandidateConflict()
{
    QList<QStringList> my_list;

    //1.初始化顶点访问数组
    for (int i = 0; i < this->_MAX_VERTEX_NUM; i++)
    {
        this->vexs_visited[i] = 0;
        this->vexs_comb_visited[i] = 0;
    }
//    //遍历过的就不在查找
//    for(int i=0; i<vexNum; i++)
//    {
//        MyTree->ClearTree();

//        if(vexs_comb_visited[i] == 0)
//        {
//            _BFS_Candidate_Confilict(i);

//            QList<QStringList> temp1, temp2;
//            temp1 = MyTree->GetComboString();

//            for(int m=0; m<temp1.count(); m++)
//            {
//                bool ans = false;
//                for(int n=0; n<my_list.count(); n++)
//                {
//                    ans = _Compare_StringList(temp1[m], my_list[n]);
//                    if(ans)
//                        break;
//                }
//                if(!ans)
//                    temp2.append(temp1.at(m));
//            }
//            if(!temp2.isEmpty())
//                my_list.append(temp2);


//             qDebug()<<"i"<<i;

//        }

//    }

//    //出度小于3的不在查找，如果出度都为2，那么从0开始
//    QVector<int> find_num;
//    for(int i=0; i<vexNum; i++)
//    {
//        if(vexs[i].out_num>2)
//            find_num.append(vexs[i].out_num);
//    }

//    if(find_num.isEmpty())
//    {

//        MyTree->ClearTree();

//        _BFS_Candidate_Confilict(0);

//        QList<QStringList> temp1, temp2;
//        temp1 = MyTree->GetComboString();

//        for(int m=0; m<temp1.count(); m++)
//        {
//            bool ans = false;
//            for(int n=0; n<my_list.count(); n++)
//            {
//                ans = _Compare_StringList(temp1[m], my_list[n]);
//                if(ans)
//                    break;
//            }
//            if(!ans)
//                temp2.append(temp1.at(m));
//        }
//        if(!temp2.isEmpty())
//            my_list.append(temp2);
//    }
//    else
//    {
//        for(int i=0; i<find_num.count(); i++)
//        {
//            MyTree->ClearTree();

//            _BFS_Candidate_Confilict(find_num.at(i));

//            QList<QStringList> temp1, temp2;
//            temp1 = MyTree->GetComboString();

//            for(int m=0; m<temp1.count(); m++)
//            {
//                bool ans = false;
//                for(int n=0; n<my_list.count(); n++)
//                {
//                    ans = _Compare_StringList(temp1[m], my_list[n]);
//                    if(ans)
//                        break;
//                }
//                if(!ans)
//                    temp2.append(temp1.at(m));
//            }
//            if(!temp2.isEmpty())
//                my_list.append(temp2);
//        }
//    }


//    //所有点
//    for(int i=0; i<vexNum; i++)
//    {
//        MyTree->ClearTree();

//        _BFS_Candidate_Confilict(i);

//        QList<QStringList> temp1, temp2;
//        temp1 = MyTree->GetComboString();

//        for(int m=0; m<temp1.count(); m++)
//        {
//            bool ans = false;
//            for(int n=0; n<my_list.count(); n++)
//            {
//                ans = _Compare_StringList(temp1[m], my_list[n]);
//                if(ans)
//                    break;
//            }
//            if(!ans)
//                temp2.append(temp1.at(m));
//        }
//        if(!temp2.isEmpty())
//            my_list.append(temp2);

//    }

//    for(int i=0; i<my_list.count(); i++)
//        my_list[i].sort();
//    _IsComplete(my_list);

//    QTime timer;
//    timer.restart();

    //通过全排列然后删除的形式找到所有的
//    QList<QStringList>test = _DeleteTest();
//    qDebug()<<"全排序时间"<<timer.elapsed();
    my_list = _DeleteTest();
//    my_list.clear();


//    //用线排列组合
//    QList<int> one_combo;
//    QList<QList<int>> all_combo;
//    QList<QList<int>> last_length_combo;
//    QList<QList<int>> new_length_combo;

//    QVector<QVector<int>> line;

//    ArcNode* p = nullptr;

//    timer.restart();

//    for(int i=0; i<vexNum; i++)
//    {
//        p = vexs[i].first;
//        while (p!=nullptr) {
//            QVector<int> test;
//            if(i<p->adjVex)
//            {
//                test.append(i);
//                test.append(p->adjVex);
//            }
//            else if(i>p->adjVex)
//            {
//                test.append(p->adjVex);
//                test.append(i);
//            }
//            else {
//                p = p->next;
//                continue;
//            }
//            p = p->next;


//            if(line.isEmpty())
//                line.append(test);
//            else
//            {
//                int len = line.count();
//                bool isSame = false;
//                for(int j=0; j<len; j++)
//                {
//                    if(test.at(0)==line.at(j).at(0) && test.at(1)==line.at(j).at(1))
//                    {
//                        isSame = true;
//                        break;
//                    }
//                }
//                if(!isSame)
//                    line.append(test);
//            }
//        }

//        //顺便把长度为1的加进去
//        QList<int> tem;
//        tem.append(i);
//        all_combo.append(tem);
//    }

//    qDebug()<<"找到线的时间"<<timer.elapsed();

//    //先把长度为2的加进去
//    for(int i=0; i<line.count(); i++)
//    {
//        QList<int> temp;
//        temp.append(line.at(i).at(0));
//        temp.append(line.at(i).at(1));

//        all_combo.append(temp);
//        last_length_combo.append(temp);
//    }

//    timer.restart();

//    for(int len=3; len<=vexNum; len++)
//    {
//        int all_count = 1;
//        //计算每个长度最多数量
//        for(int t=0; t<len; t++)
//        {
//            all_count = all_count * (vexNum-t) / (len-t);
//        }

//        if(len == vexNum-1)
//            qDebug()<<"test";
//        int length1 = last_length_combo.length();
//        int length2 = line.count();
//        for(int i=0; i<length1; i++)
//        {
//            for(int j=0; j<length2; j++)
//            {
//                QList<int> temp = last_length_combo[i];
//                temp.append(line.at(j).at(0));
//                temp.append(line.at(j).at(1));

//                _RemoveQListIntDuplicates(temp);

//                if(temp.count() == len)
//                {
//                    if(new_length_combo.isEmpty())
//                        new_length_combo.append(temp);
//                    else
//                    {
//                        bool isAllSame = false;


//                        for(int m=0; m<new_length_combo.count(); m++)
//                        {
//                            bool isOneSame = true;
//                            for(int t=0; t<len; t++)
//                            {
//                                if(new_length_combo.at(m).at(t) != temp.at(t))
//                                {
//                                    isOneSame = false;
//                                    break;
//                                }
//                            }

//                            if(isOneSame)
//                            {
//                                isAllSame = true;
//                                break;
//                            }
//                        }

//                        if(!isAllSame)
//                            new_length_combo.append(temp);
//                    }
//                }

//                if(new_length_combo.count() == all_count)
//                    break;
//            }
//            if(new_length_combo.count() == all_count)
//                continue;
//        }

//        all_combo.append(new_length_combo);
//        last_length_combo = new_length_combo;
//        new_length_combo.clear();
//    }
//    qDebug()<<"整合时间"<<timer.elapsed();

//    for(int i=0; i<all_combo.count(); i++)
//    {
//        QStringList temp;
//        for(int j=0; j<all_combo.at(i).count(); j++)
//            temp.append(vexs[all_combo.at(i).at(j)].name);

//        my_list.append(temp);
//    }

    qDebug()<<"my_list长度"<<my_list.count();

//    qDebug()<<"my_list长度"<<my_list.count()<<"正确长度"<<test.count();
    return my_list;
}

void GraphAdjList::_RemoveQListIntDuplicates(QList<int>& list)
{
    QSet<int> set_temp;
    set_temp = list.toSet();
    list = set_temp.toList();

    std::sort(list.begin(), list.end());
}

QList<QStringList> GraphAdjList::_DFS_Candidate_Confilict(int index)
{
    QList<QStringList> my_list;

    for(int i=0; i<_MAX_VERTEX_NUM; i++)
        vexs_visited[i] = 0;

    //1.访问第一个结点，并标记为 已访问
    vexs_visited[index] = 1;
    vexs_comb_visited[index] = 0;

    //初始化 边结点 栈
    QList<ArcNode*> * s = new QList<ArcNode*>();
    //初始化边结点 指针
    ArcNode * p = this->vexs[index].first;

    //2.寻找下一个（未访问的）邻接结点

    int depth = 0;    //深度，判断是否搜索到底

//    qDebug()<<"顺序"<<index;
    while (!s->isEmpty() || p != NULL)
    {

            //2.1.未访问过，则访问 （纵向遍历）
//        if (vexs_port_visited.at(p->Tail_Vex).at(p->Tail_portNum) != 1 || vexs_port_visited.at(p->Head_Vex).at(p->Head_portNum) != 1)
        if (vexs_visited[p->adjVex] != 1)
        {
            //访问结点，标记为访问，并将其入栈
            vexs_visited[p->adjVex] = 1;
            vexs_comb_visited[p->adjVex] = 1;

//            vexs_port_visited[p->Tail_Vex][p->Tail_portNum] = 1;
//            vexs_port_visited[p->Head_Vex][p->Head_portNum] = 1;

            s->push_back(p);

            //指针 p 移向 此结点的第一个邻接结点
            p = this->vexs[p->adjVex].first;

//            qDebug()<<"从"<<vexs[s->last()->Tail_Vex].name<<"+"<<vexs[s->last()->Head_Vex].name<<"到"<<vexs[p->Tail_Vex].name<<"+"<<vexs[p->Head_Vex].name;


            depth = s->length();
        }
        //2.2.已访问过，移向下一个边结点 （横向遍历）
        //目前可能有问题，如果两个点用两根线连城循环，可能无法往下遍历
        else
        {
            p = p->next;
//            if(!s->isEmpty()&&p!=nullptr)
//                qDebug()<<"NEXT"<<"从"<<vexs[s->last()->Tail_Vex].name<<"+"<<vexs[s->last()->Head_Vex].name<<"到"<<vexs[p->Tail_Vex].name<<"+"<<vexs[p->Head_Vex].name;
        }

        //3.若无邻接点，则返回上一结点层，并出栈边结点
        if (p == NULL&&!s->isEmpty())
        {
            if(depth == s->length())    //这里表示已经探索到1条线路的底部了
            {
                QStringList out;
                out.push_back(vexs[index].name);

                for(int i=0; i<s->count();i++)
                {
                    out << this->vexs[s->at(i)->adjVex].name;
                }

                my_list.push_back(out);

                depth = 0;
            }

            p = s->takeLast();
        }

    }
    //释放 栈
    delete s;

    return my_list;
}

QList<QStringList> GraphAdjList::_BFS_Candidate_Confilict(int index)
{
    QList<QStringList> my_list;

    /*
    .	从指定顶点开始，广度优先遍历
    */
    //1.判断顶点是否存在
    if (index<0 || index>=_MAX_VERTEX_NUM)
        return my_list;

    QVector<int> start_node_num;
    QVector<int> end_node_num;

    start_node_num.append(index);

    int layer_count = 0;

    ArcNode * p = nullptr;
    bool stop_all = false;

    //处理单个的情况
    if(vexs[index].first == nullptr)
    {
        MyTree->AddNode("",vexs[index].name, layer_count);
        this->vexs_comb_visited[index] = 1;

        return my_list;
    }

    while (!stop_all) {

        if(layer_count == 0)
        {
            MyTree->AddNode("",vexs[index].name, layer_count);
            this->vexs_comb_visited[index] = 1;
            layer_count++;
        }
        else
        {
            for(int i=0; i<start_node_num.count(); i++)
            {
                p = vexs[start_node_num.at(i)].first;
                this->vexs_comb_visited[start_node_num.at(i)] = 1;

                while (p!=nullptr) {

                    end_node_num.append(p->adjVex);

                    MyTree->AddNode(vexs[start_node_num.at(i)].name, vexs[p->adjVex].name, layer_count);
                    this->vexs_comb_visited[p->adjVex] = 1;

                    p = p->next;

                }




            }

            layer_count++;
            start_node_num.clear();
            start_node_num = end_node_num;
            end_node_num.clear();



        }

//        MyTree->DisplayTree();

        stop_all = MyTree->IsFinish();
    }


    return my_list;
}

QList<QStringList> GraphAdjList::_DFS_Combination(QList<QStringList> list)
{
    QList<QStringList> my_list;

    qDebug()<<"ceshi1";
    for(int i=0; i<list.count();i++)
        qDebug()<<list.at(i);

    QList<QList<QStringList>> totle_list;   //里面每个放的是对应的list中找到的相关点
    for(int i=0; i<list.length();i++)
    {
        QList<QStringList> temp_list;

        for(int j=0; j<list.at(i).length(); j++)
        {

            {
                int ilength = list.at(i).length();

                QStringList temp;


                for(int len = 1; len<=ilength-j; len++)
                {
                    for(int m=0; m<len; m++)
                        temp<<list.at(i).at(j+m);

//                    _RemoveListSameNoSequence(temp);  //删除重复项
//                    _RemoveListSameKeepSequence(temp);



                    if(!temp_list.isEmpty())
                    {
                        //判断my_list中是否有重复
                        for(int k=0; k<temp_list.length()+1; k++)
                        {
                            if(_Compare_StringList(temp, temp_list[k]))
                                break;
                            else
                                if(k == temp_list.length()-1)
                                    temp_list.push_back(temp);
//                            if(temp == my_list.at(k))
//                                break;
//                            else
//                                if(k == my_list.length()-1)
//                                    my_list.push_back(temp);
                        }
                        temp.clear();
                    }
                    else
                    {
                        temp_list.push_back(temp);
                        temp.clear();
                    }
                }


            }

        }
        totle_list.append(temp_list);

    }

    for(int i=0; i<totle_list.count(); i++)
        for(int j=0; j<totle_list.at(i).count(); j++)
            qDebug()<<totle_list.at(i).at(j);

    qDebug()<<"totle_list"<<totle_list.count();

    return my_list;
}

QList<QStringList> GraphAdjList::_Get_Circle_Combo(const QStringList& list,QList<QList<QStringList>>& combo, QVector<int>& circle_num)
{
    QList<QStringList> my_list;

    for(int m=0; m<combo.count(); m++)   //先加入普通的
        my_list.append(combo.at(m));

    for(int i=0; i<combo.count(); i++)
    {
        for(int len=2; len<=combo.count()-i; len++)
        {
            QVector<QVector<int>> right_num;    //先拿到相关的序号
            for(int m=0; m<len; m++)
            {
                QVector<int>  temp;
                if(m==0)
                {
                    for(int k=0; k<combo.at(i+m).count(); k++)
                    {
                        QString str = list.at(circle_num.at(i+m+1)-1);
                        QStringList test = combo.at(i+m).at(k);
                        if(combo.at(i+m).at(k).contains(str))
                        {
                            temp.append(k);
                        }
                    }

                }
                else if(m == len-1)
                {
                    for(int k=0; k<combo.at(i+m).count(); k++)
                    {
                        if(combo.at(i+m).at(k).contains(list.at(circle_num.at(i+m))))
                        {
                            temp.append(k);
                        }
                    }

                }
                else
                {
                    for(int k=0; k<combo.at(i+m).count(); k++)
                    {
                        if(combo.at(i+m).at(k).contains(list.at(circle_num.at(i+m))))
                        {
                            if(combo.at(i+m).at(k).contains(list.at(circle_num.at(i+m+1)-1)))
                                temp.append(k);
                        }
                    }
                }

                right_num.append(temp);
            }

            QVector<QVector<int>> combo_num = _Get_Num_Combo(right_num);

            for(int k=0; k<combo_num.count(); k++)
            {
                QStringList temp;
                for(int mm=0; mm<combo_num.at(k).count(); mm++)
                {
                    temp<<combo.at(i+mm).at(combo_num.at(k).at(mm));
                }

                my_list.append(temp);
            }
//            qDebug()<<"test";
//            QStringList temp_list;
//            QVector<int> count, calculate;

//            int totle_length = 1;
//            for(int k=0; k<right_num.count(); k++)
//            {
//                count.append(right_num.at(k).count());
//                calculate.append(0);
//                totle_length = totle_length * right_num.at(k).count();
//            }

//            int pos = count.count()-1;

//            while (pos>=0) {


//            }

//            for(int k=0; k<totle_length; k++)
//            {
//                for(int m=0; m<right_num.count(); m++)
//                {
//                    temp_list.append(combo.at(i+m).at(right_num.at(m).at(count.at(m))));
//                }

//            }

//            int mm =5;


        }
    }

    return  my_list;
}

QVector<QVector<int>> GraphAdjList::_Get_Num_Combo(const QVector<QVector<int>>& totle_num)
{
    QVector<int> original_count, cal;
    QVector<QVector<int>> ans;
    int totle_count = 1;

    for(int i=0; i<totle_num.count(); i++)
    {
        original_count.append(totle_num.at(i).count());
        cal.append(0);
        totle_count = totle_count * totle_num.at(i).count();
    }

    for(int i=0; i<totle_count; i++)
    {
        QVector<int> temp;
        for(int m=0; m<original_count.count(); m++)
        {
            temp<<totle_num.at(m).at(cal.at(m));
        }
        ans.append(temp);

        cal.last()++;

        for(int j=cal.count()-1; j>0; j--)
        {
            if(cal.at(j) == original_count.at(j))
            {
                cal[j] = 0;
                cal[j-1]++;

            }
        }

    }

//    for(int i=0; i<ans.count(); i++)
//        qDebug()<<ans.at(i)<<"测试";

    return ans;
}

bool GraphAdjList::_Compare_StringList(QStringList& list1, QStringList& list2)
{
    bool ans = false;

    if(list1.count()!= list2.count())
        return ans;


    list1.sort();
    list2.sort();

    if(list1 == list2)
        ans = true;

    return ans;
}

void GraphAdjList::_RemoveListSameKeepSequence(QStringList& list)
{
    list.removeDuplicates();
}

void GraphAdjList::_RemoveListSameNoSequence(QStringList& list)
{

    list = list.toSet().toList();
}

bool GraphAdjList::_IsComplete(QList<QStringList> my_list)
{
    QList<QVector<int>> num_list_all;

    QVector<int> num_list_temp;

    if(vexNum<2)
        return true;

    num_list_temp.append(0);
    num_list_all.append(num_list_temp);

    for(int m=1; m<vexNum; m++)
    {
        num_list_temp.clear();
        int len = num_list_all.count();
        for(int n=0; n<len; n++)
        {
            num_list_temp.append(num_list_all.at(n));
            num_list_temp.append(m);
            num_list_all.append(num_list_temp);
            num_list_temp.clear();
        }

        num_list_temp.append(m);
        num_list_all.append(num_list_temp);
    }
    qDebug()<<"num_list_all原始长度"<<num_list_all.count();

    for(int i=0; i<num_list_all.count(); i++)
    {
        bool ans = _IsAComboConnect(num_list_all.at(i));
        if(!ans)
        {
            num_list_all.removeAt(i);
            i--;
        }

//        qDebug()<<"进度"<<i<<num_list_all.count();
    }

    QList<QStringList> list_temp;
    for(int i=0; i<num_list_all.count(); i++)
    {
        QStringList temp;
        for(int j=0; j<num_list_all.at(i).count(); j++)
        {
            temp.append(vexs[num_list_all.at(i).at(j)].name);
        }

        list_temp.append(temp);
    }

    //去掉重复的
    for(int i=0; i<list_temp.count(); i++)
        list_temp[i].sort();
    for(int i=0; i<my_list.count(); i++)
        my_list[i].sort();

    for(int i=0; i<list_temp.count(); i++)
    {
        bool isSame = false;


        for(int j=0; j<my_list.count(); j++)
        {

            isSame = _Compare_StringList(list_temp[i], my_list[j]);
            if(isSame)
            {

                my_list.removeAt(j);
                break;
            }
        }

        if(isSame)
        {
            list_temp.removeAt(i);
            i--;
        }
    }

    qDebug()<<"mylist"<<my_list.count();
    for(int i=0; i<my_list.count(); i++)
    {
        qDebug()<<my_list.at(i);
    }

    qDebug()<<"list_temp"<<list_temp.count();
    for(int i=0; i<list_temp.count(); i++)
    {
        qDebug()<<list_temp.at(i);
    }
    return false;
}

bool GraphAdjList::_IsAComboConnect(const QVector<int>& num_list)
{
    int original_count = num_list.count();
    if(original_count < 2)
        return true;

    QVector<bool> visit;

    for(int i=0; i<original_count; i++)
    {
        visit.append(false);
    }

    //3.1.初始化队列
    QQueue<int> vexQ;
    //3.2.访问开始顶点，并标记访问、入队
    vexQ.enqueue(num_list[0]);
    visit[0] = true;
    //3.3.出队，并遍历邻接顶点（下一层次），访问后入队
    ArcNode * p = nullptr;
    int adjVex = 0;
    int index = 0;
    int visit_node_count = 1;
    while (!vexQ.isEmpty())
    {
        index = vexQ.dequeue();
        p = this->vexs[index].first;
        if(p == nullptr)
            return false;

        //遍历邻接顶点
        bool isFindOne = false;
        while (p != nullptr)
        {
            adjVex = p->adjVex;
            for(int m=0; m<original_count; m++)
            {
                if(adjVex == num_list.at(m))
                {
                    isFindOne = true;
                    if(!visit.at(m))
                    {
                        visit[m] =true;
                        visit_node_count++;
                        vexQ.enqueue(adjVex);
                        break;
                    }
                }
            }

            p = p->next;

        }

        if(!isFindOne)      //如果一个都没找到，说明有个点所连接的点全都不在num_list中，直接跳出false
            return false;

//        if(visit_node_count == original_count)
//            return true;
    }


    if(visit_node_count != original_count)
        return false;


    return true;

}

void GraphAdjList::_CalculateOut()
{
    for(int i=0; i<vexNum; i++)
    {
        //计算出度
        QVector<int> out_num;
        ArcNode* p = vexs[i].first;
        while (p!=nullptr) {
            vexs[i].out_num++;
            out_num.append(p->adjVex);
            p = p->next;

        }
    }

}

QList<QStringList> GraphAdjList::_DeleteTest()
{
    QList<QVector<int>> num_list_all;

    QVector<int> num_list_temp;

    num_list_temp.append(0);
    num_list_all.append(num_list_temp);

    QTime timer;
    timer.restart();

    //全排列
    for(int m=1; m<vexNum; m++)
    {
        num_list_temp.clear();
        int len = num_list_all.count();
        for(int n=0; n<len; n++)
        {
            num_list_temp.append(num_list_all.at(n));
            num_list_temp.append(m);

            num_list_all.append(num_list_temp);

            num_list_temp.clear();
        }
        num_list_temp.append(m);
        num_list_all.append(num_list_temp);
    }
    qDebug()<<"num_list_all原始长度"<<num_list_all.count()<<"生成组合时间"<<timer.elapsed();

    timer.restart();

//    int progress_count = 0;
    CutThread* thread = new CutThread(0);
    thread->SetTotleCount(num_list_all.count());
    thread->SetNumList(&num_list_all);
    thread->SetVNodes(vexs);
    thread->SetThreadCount(4);
    thread->start();
    while (!thread->isFinished()) {

    }

//    for(int i=0; i<num_list_all.count(); i++)
//    {
//        bool ans = _IsAComboConnect(num_list_all.at(i));
//        if(!ans)
//        {
//            num_list_all.removeAt(i);
//            i--;
//        }

////        if(progress_count<10000)
////            progress_count++;
//        else
//        {
////            qDebug()<<"进度为"<<i<<num_list_all.count();
////            progress_count = 0;
//        }
//    }




    QList<QStringList> list_temp;

    qDebug()<<"去掉不连接部分的时间"<<timer.elapsed();
    timer.restart();

    for(int i=0; i<num_list_all.count(); i++)
    {
        QStringList temp;
        int length = num_list_all.at(i).count();

        for(int j=0; j<length; j++)
        {
            temp.append(vexs[num_list_all.at(i).at(j)].name);
        }

        list_temp.append(temp);
    }

    qDebug()<<"删除后的长度"<<list_temp.count();
    qDebug()<<"int转成QString时间"<<timer.elapsed();

    timer.restart();
    //去掉重复的
    for(int i=0; i<list_temp.count(); i++)
        list_temp[i].sort();

    qDebug()<<"排序时间"<<timer.elapsed();

//    qDebug()<<"list_temp"<<list_temp.count();
//    for(int i=0; i<list_temp.count(); i++)
//    {
//        qDebug()<<list_temp.at(i);
//    }


    return list_temp;
}
