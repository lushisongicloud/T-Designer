#include "combotree.h"

ComboTree::ComboTree()
{

}

void ComboTree::AddNode(const QString& father, const QString& node, int layer)
{
    if(father == node)
        return;

    if(layer > Layer.count())   //这个函数只能一层一层加，不能跳层
        return;

    if(layer == 0)
    {

        QList<TreeNode> tree_list;
        TreeNode temp;
        temp.NodeName = node;
        tree_list.append(temp);
        Layer.push_back(tree_list);
        return;
    }
    else
    {
        //先看是否需要插入一层
        if(layer == Layer.count())   //需要先插入一层
        {
            QList<TreeNode> tree_list;
            Layer.append(tree_list);
        }
        //如果这个子节点在父节点之前的层当中出现，则忽略
        int childtemp = _LocateNodeLayerNum(node);
//        if(childtemp >= 0 && childtemp <Layer.count()-1)  //注意如果子节点在父节点里有，不写
        if(childtemp >= 0 && childtemp <Layer.count()-2)  //注意如果子节点在父节点里有，那么写，但是不再往下延伸
            return;

        //如果父节点在之前的层出现过，忽略
        int fathertemp = _LocateNodeLayerNum(father);
        if(fathertemp >= 0 && fathertemp <Layer.count()-2)  //注意如果子节点在父节点里有，那么仍然写，只是不再延申
            return;

        //插入子节点
        int child_node = _LocateNodeInLayer(node,layer);
        if(child_node == -1)    //没有在这一层找到这个子节点，就加入这个子节点
        {
            TreeNode temp;
            temp.NodeName = node;
            Layer.last().append(temp);
            child_node = Layer.last().count()-1;
        }

        //在父节点上插入这个点的位置
        int father_node = _LocateNodeInLayer(father,layer-1);
        if(father_node != -1)
        {
            bool isRepeat = false;
            for(int i=0; i<Layer[layer-1][father_node].ChileNum.count(); i++)
            {
                if( Layer[layer-1][father_node].ChileNum.at(i) == child_node)
                {
                    isRepeat = true;
                    break;
                }
            }

            if(!isRepeat)
                Layer[layer-1][father_node].ChileNum.append(child_node);
        }
    }
}

void ComboTree::DisplayTree()
{
    for(int i=0; i<Layer.count(); i++)
    {

        for(int j=0; j<Layer.at(i).count(); j++)
        {
            qDebug()<<"层数"<<i<<"中，第"<<j<<"个节点";
            qDebug()<<"节点名称为"<<Layer.at(i).at(j).NodeName;

            QStringList child_num;
            for(int m=0; m<Layer.at(i).at(j).ChileNum.count(); m++)
                child_num<<QString::number(Layer.at(i).at(j).ChileNum.at(m));
            qDebug()<<"子节点为"<<child_num;

            for(int m=0; m<Layer.at(i).at(j).Combo.count(); m++)
                qDebug()<<"该节点组合有"<<Layer.at(i).at(j).Combo.at(m);
        }
    }
}

bool ComboTree::IsFinish()
{
    return Layer.last().isEmpty();

}

QList<QStringList> ComboTree::GetComboString()
{
    QList<QStringList> my_list;

    _InitNodeCombo();

//    QTime timer;

//    timer.restart();
//    QList<QStringList> loop = _ProcessLoop();       //注意处理循环之前不能排序，因为还需要他的头是在尾端这个状态来进行剪枝
//    qDebug()<<"处理循环时间"<<timer.elapsed();

//    timer.restart();
    _SortCombo();
//    qDebug()<<"排序时间"<<timer.elapsed();

    for(int i=Layer.count()-1; i>=0; i--)
    {
        for(int j=0; j<Layer.at(i).count(); j++)
        {
            if(my_list.isEmpty())
                my_list.append(Layer.at(i).at(j).Combo);
            else
            {
                for(int n=0; n<Layer.at(i).at(j).Combo.count(); n++)
                {
                    bool isSame = false;
                    for(int m = 0; m<my_list.count(); m++)
                    {
                        isSame = _Compare_StringList(my_list[m], Layer.at(i).at(j).Combo.at(n), false);
                        if(isSame)
                            break;
                    }

                    if(!isSame)
                        my_list.append(Layer.at(i).at(j).Combo.at(n));
                }
            }
        }
    }

//    timer.restart();
//    for(int i=0; i<loop.count(); i++)
//    {
//        bool isRepeat = false;
//        for(int j=0; j<my_list.count(); j++)
//        {
//            isRepeat = _Compare_StringList(my_list[j], loop[i], true);
////            isRepeat = my_list[j] == loop[i];
//            if(isRepeat)
//                break;

//        }

//        if(!isRepeat)
//            my_list.append(loop.at(i));
//    }
//    qDebug()<<"添加循环结果时间"<<timer.elapsed();

//    qDebug()<<"显示树";
//    DisplayTree();

    return my_list;

}
int ComboTree::_LocateNodeInLayer(const QString& node, int layer)
{
    if(layer<0||layer>Layer.count()-1)
        return -1;
    for(int i=0; i<Layer.at(layer).count(); i++)
    {
        if(node == Layer.at(layer).at(i).NodeName)
            return i;
    }

    return  -1;
}

int ComboTree::_LocateNodeLayerNum(const QString& node)
{
    for(int i=0; i<Layer.count(); i++)
    {
        for(int j=0; j<Layer.at(i).count(); j++)
            if(node == Layer.at(i).at(j).NodeName)
                return i;
    }

    return  -1;
}

void ComboTree::_InitNodeCombo()
{
    for(int i= Layer.count()-1; i>=0; i--)      //第i层
    {
        for(int j= Layer.at(i).count()-1; j>=0; j--)        //第i层第j个节点
        {
            TreeNode* cur_node = &Layer[i][j];

            if(cur_node->ChileNum.isEmpty())
            {
                QStringList temp;
                temp.append(cur_node->NodeName);
                cur_node->Combo.append(temp);
            }
            else
            {
                int child_count = cur_node->ChileNum.count();

                QVector<int> temp_node_combo_num;
                QVector<QVector<int>> temp_node_combo_num_all;
                temp_node_combo_num.append(cur_node->ChileNum[0]);
                temp_node_combo_num_all.append(temp_node_combo_num);


                //先把自己单独加上，注意这里virtual也会加上，用来辅助判断是否是虚拟端点
                QStringList temp_head;
                temp_head.append(cur_node->NodeName);
                cur_node->Combo.append(temp_head);

                if(child_count==1){
                    QList<QList<QStringList>> temp;
                    temp.append(Layer.at(i+1).at(cur_node->ChileNum.at(0)).Combo);
                    cur_node->Combo.append(_GetCombination(cur_node->NodeName,temp));
                    continue;
                }

                for(int m=1; m<child_count; m++)
                {
                    temp_node_combo_num.clear();
                    int len = temp_node_combo_num_all.count();
                    for(int n=0; n<len; n++)
                    {
                        temp_node_combo_num.append(temp_node_combo_num_all[n]);
                        temp_node_combo_num.append(cur_node->ChileNum.at(m));
                        temp_node_combo_num_all.append(temp_node_combo_num);
                        temp_node_combo_num.clear();
                    }
                    temp_node_combo_num.append(cur_node->ChileNum.at(m));
                    temp_node_combo_num_all.append(temp_node_combo_num);

                }

                QList<QStringList> temp;
                QList<QList<QStringList>> combo_combine;
                for(int m=0; m<temp_node_combo_num_all.count(); m++)
                {
                    combo_combine.clear();
                    //先得到combo_combine
                    for(int k=0; k<temp_node_combo_num_all.at(m).count(); k++)
                    {
                        combo_combine.append(Layer.at(i+1).at(temp_node_combo_num_all.at(m).at(k)).Combo);
                    }
                    temp = _GetCombination(cur_node->NodeName, combo_combine);

                    bool isSame = false;
                    int len = temp.count();

                    for(int n=0; n<len; n++)
                    {
                        for(int k=0; k<cur_node->Combo.count(); k++)
                        {
                            isSame = _Compare_StringList(cur_node->Combo[k], temp[n], true);
                            if(isSame)
                                break;
                        }
                        if(!isSame)
                            cur_node->Combo.append(temp[n]);
                    }
                }
            }


        }

//        //在第i层继续处理东西，判断同一层的两个是否也是直接连在一起的，如果是直接连在一起的，要给两个端点都加上对方的东西
//        if(i!=0)
//        {
//            for(int m=0; m<Layer.at(i).count()-1; m++)        //第i层第j个节点
//            {
//                if(Layer.at(i).at(m).ChileNum.isEmpty())
//                    continue;
//                for(int n=m+1; n<Layer.at(i).count(); n++)
//                {
//                    if(Layer.at(i).at(n).ChileNum.isEmpty())
//                        continue;

//                    for(int p=0; p<Layer.at(i).at(m).ChileNum.count(); p++)
//                    {
//                        for(int q=0; q<Layer.at(i).at(n).ChileNum.count(); q++)
//                        {
//                            QString node1_name = Layer.at(i).at(m).NodeName;
//                            QString node2_name = Layer.at(i).at(n).NodeName;

//                            int node_1_child_num = Layer.at(i).at(m).ChileNum[p];
//                            int node_2_child_num = Layer.at(i).at(n).ChileNum[q];
//                            QString node1_child_name = Layer.at(i+1).at(node_1_child_num).NodeName;
//                            QString node2_child_name = Layer.at(i+1).at(node_2_child_num).NodeName;


//                            if(node1_name == node2_child_name && node2_name==node1_child_name)
//                            {

//                                QList<QStringList> temp1 = Layer.at(i).at(m).Combo;
//                                QList<QStringList> temp2 = Layer.at(i).at(n).Combo;

//                                for(int k= 0; k<Layer.at(i).at(m).Combo.count(); k++)
//                                {
//                                    for(int r=0; r<Layer.at(i).at(n).Combo.count(); r++)
//                                    {
//                                        QStringList temp;
//                                        temp.append(Layer.at(i).at(m).Combo.at(k));
//                                        temp.append(Layer.at(i).at(n).Combo.at(r));
//                                        temp.removeDuplicates();


//                                        _AddStringListToQListQStringList(temp, Layer[i][m].Combo);
//                                        _AddStringListToQListQStringList(temp, Layer[i][n].Combo);
//                                    }
//                                }

//                            }
//                        }
//                    }
//                }
//            }
//        }
    }
}

QList<QStringList> ComboTree::_GetCombination(QString& head, QList<QList<QStringList>>& temp_node_combo)
{
    QList<QStringList> My_List;

    QVector<int> combo_num;         //每个节点的combo数量，用来记录计数器的最大值
    QVector<int> combo_counter;     //计数器用来计数排列组合


    if(temp_node_combo.count() == 1)
    {
        My_List = temp_node_combo[0];
        for(int i=0; i<My_List.count(); i++)
            My_List[i].append(head);

        return My_List;
    }

    //先进行剪枝处理
//    QTime timer;
//    timer.restart();
    if(temp_node_combo.count() >1)
    {
        QList<QStringList> temp0, temp1;
        for(int i=0; i<temp_node_combo.count()-1; i++)
        {
            temp0 = temp_node_combo[i];
            for(int m=1; m<temp0.count(); m++)
            {
                if(temp0.count()!=1)        //不能把头单独那一个给删掉
                    temp0[m].removeLast();
            }

            for(int n=i+1; n<temp_node_combo.count(); n++)
            {
                //注意每个temp_node_combo中他的头都是放在最后的
                temp1 = temp_node_combo[n];

                for(int j=1; j<temp1.count(); j++)
                {
                    if(temp1.count()!=1)        //不能把头单独那一个给删掉
                        temp1[j].removeLast();
                }


                for(int k=0; k<temp1.count(); k++)
                {
                    bool isSame = false;
                    int r=0;
                    for(r=0; r<temp0.count(); r++)
                    {
                        isSame = _Compare_StringList(temp0[r], temp1[k],true);
                        if(isSame)
                            break;
                    }
                    if(isSame)
                    {
                        temp1.removeAt(k);
                        temp_node_combo[n].removeAt(k);
                        k--;
                    }

                }
            }
        }

    }
    for(int n=0; n<temp_node_combo.count(); n++)        //初始化计数器
    {
        if(temp_node_combo.at(n).count() == 0)
        {
            temp_node_combo.removeAt(n);
            n--;
            continue;
        }
        combo_num.append(temp_node_combo.at(n).count());
        combo_counter.append(0);
    }

    //计数器加一
    int carry_pos = temp_node_combo.count()-1;          //进位在combo_num的位置
    QStringList combo_temp;

    while (true) {

        for(int n=0; n<temp_node_combo.count(); n++)
        {
            combo_temp.append(temp_node_combo.at(n).at(combo_counter.at(n)));
        }

        combo_temp.append(head);
        combo_temp.removeDuplicates();

        int isSame = false;
        for(int m=0; m<My_List.count(); m++)
        {
            isSame = _Compare_StringList(My_List[m], combo_temp,true);
            if(isSame)
                break;
        }
        if(!isSame)
            My_List.append(combo_temp);
        combo_temp.clear();


        for(int j=temp_node_combo.count()-1; j>=carry_pos; j--)
        {
            combo_counter[j]++;
            if(combo_counter.at(j) == combo_num.at(j))
            {
                if(j != carry_pos)
                    combo_counter[j] = 0;
                else
                {
                    combo_counter[j] = 0;
                    carry_pos--;
                    break;
                }
            }
            else
                break;
        }


        if(carry_pos <0)
            break;
    }

    return My_List;
}

QList<QStringList> ComboTree::_GetCombination(QList<QList<QStringList>>& temp_node_combo)
{
    QList<QStringList> My_List;

    QVector<int> combo_num;         //每个节点的combo数量，用来记录计数器的最大值
    QVector<int> combo_counter;     //计数器用来计数排列组合

    if(temp_node_combo.count() == 1)
    {
        My_List = temp_node_combo[0];

        return My_List;
    }

    //先进行剪枝处理
//    QTime timer;
//    timer.restart();
    if(temp_node_combo.count() >1)
    {
        QList<QStringList> temp0, temp1;
        for(int i=0; i<temp_node_combo.count()-1; i++)
        {
            temp0 = temp_node_combo[i];
            for(int m=1; m<temp0.count(); m++)
            {
                if(temp0.count()!=1)
                    temp0[m].removeLast();
            }


            for(int n=i+1; n<temp_node_combo.count(); n++)
            {
                //注意每个temp_node_combo中他的头都是放在最后的
                temp1 = temp_node_combo[n];

                for(int j=1; j<temp1.count(); j++)
                {
                    if(temp1.count()!=1)
                        temp1[j].removeLast();
                }


                for(int k=0; k<temp1.count(); k++)
                {
                    bool isSame = false;
                    int r=0;
                    for(r=0; r<temp0.count(); r++)
                    {
                        isSame = _Compare_StringList(temp0[r], temp1[k],true);
                        if(isSame)
                            break;
                    }
                    if(isSame)
                    {
                        temp1.removeAt(k);
                        temp_node_combo[n].removeAt(k);
                        k--;
                    }

                }
            }
        }

    }
    for(int n=0; n<temp_node_combo.count(); n++)        //初始化计数器
    {
        if(temp_node_combo.at(n).count() == 0)
        {
            temp_node_combo.removeAt(n);
            n--;
            continue;
        }
        combo_num.append(temp_node_combo.at(n).count());
        combo_counter.append(0);
    }

    //计数器加一
    int carry_pos = temp_node_combo.count()-1;          //进位在combo_num的位置
    QStringList combo_temp;

    while (true) {

        for(int n=0; n<temp_node_combo.count(); n++)
        {
            combo_temp.append(temp_node_combo.at(n).at(combo_counter.at(n)));
        }

        combo_temp.removeDuplicates();

        int isSame = false;
        for(int m=0; m<My_List.count(); m++)
        {
            isSame = _Compare_StringList(My_List[m], combo_temp,true);
            if(isSame)
                break;
        }
        if(!isSame)
            My_List.append(combo_temp);
        combo_temp.clear();


        for(int j=temp_node_combo.count()-1; j>=carry_pos; j--)
        {
            combo_counter[j]++;
            if(combo_counter.at(j) == combo_num.at(j))
            {
                if(j != carry_pos)
                    combo_counter[j] = 0;
                else
                {
                    combo_counter[j] = 0;
                    carry_pos--;
                    break;
                }
            }
            else
                break;
        }


        if(carry_pos <0)
            break;
    }


    return My_List;
}
bool ComboTree::_Compare_StringList(QStringList list1, QStringList list2, bool isSort)
{
    bool ans = false;

    if(list1.count()!= list2.count())
        return ans;


    if(isSort)
    {
        list1.sort();
        list2.sort();
    }

    if(list1 == list2)
        ans = true;

    return ans;
}

bool ComboTree::_IsSameGrandFather(int layer, int father1, int father2)
{

    for(int i=0; i<Layer.at(layer-1).count(); i++)
    {
        bool have1 = false;
        bool have2 = false;
        for(int j=0; j<Layer.at(layer-1).at(i).ChileNum.count(); j++)
        {
            if(father1 == Layer.at(layer-1).at(i).ChileNum.at(j))
                have1 = true;

            if(father2 == Layer.at(layer-1).at(i).ChileNum.at(j))
                have2 = true;

            if(have1&&have2)
                return true;

        }
    }

    return false;

}

QList<QStringList> ComboTree::_ProcessLoop()
{
    QList<QStringList> my_list;

    //处理循环的过程是这样的
    //在一层中，找到互为子节点的两个节点，然后把他们的combo组合起来，输出，最终要和_InitNodeCombo的结果合并起来
    if(Layer.count()<3)
        return my_list;

//    QTime timer;
//    timer.restart();
//    for(int i=1; i<Layer.count()-1; i++)
//    {
//        if(Layer.at(i).count() == 1)
//            continue;

//        for(int m=0; m<Layer.at(i).count()-1; m++)
//        {
//            for(int n=m+1; n<Layer.at(i).count(); n++)
//            {
//                for(int k=0; k<Layer.at(i).at(m).ChileNum.count(); k++)
//                {
//                    for(int r=0; r<Layer.at(i).at(n).ChileNum.count(); r++)
//                    {

//                        QString node1_name = Layer.at(i).at(m).NodeName;
//                        QString node2_name = Layer.at(i).at(n).NodeName;

//                        int node_1_child_num = Layer.at(i).at(m).ChileNum[k];
//                        int node_2_child_num = Layer.at(i).at(n).ChileNum[r];
//                        QString node1_child_name = Layer.at(i+1).at(node_1_child_num).NodeName;
//                        QString node2_child_name = Layer.at(i+1).at(node_2_child_num).NodeName;


//                        if(node1_name == node2_child_name && node2_name==node1_child_name)
//                        {

//                            QList<QStringList> temp1 = Layer.at(i).at(m).Combo;
//                            QList<QStringList> temp2 = Layer.at(i).at(n).Combo;

//                            for(int q= 0; q<Layer.at(i).at(m).Combo.count(); q++)
//                            {
//                                for(int p=0; p<Layer.at(i).at(n).Combo.count(); p++)
//                                {
//                                    QStringList temp;
//                                    temp.append(Layer.at(i).at(m).Combo.at(q));
//                                    temp.append(Layer.at(i).at(n).Combo.at(p));
//                                    temp.removeDuplicates();

//                                    my_list.append(temp);
//                                }
//                            }

//                        }
//                    }
//                }
//            }

//        }
//    }
//    qDebug()<<"第一次循环时间"<<timer.elapsed();

    //如果两个节点连接同一个子节点，那么这两个节点要互相排列组合
    QVector<int> same_node_node_num;
    for(int i=2; i<Layer.count()-1; i++)        //注意从子节点往父节点找
    {
        if(Layer.at(i-1).count() == 1)
            continue;

        for(int j=0; j<Layer.at(i).count(); j++)    //第i层第j个节点
        {
            for(int m=0; m<Layer.at(i-1).count(); m++)  //第i-1层第m个节点
            {
                for(int n=0; n<Layer.at(i-1).at(m).ChileNum.count(); n++)   //第i-1层第m个节点中的第n个childnum
                {
                    int node_1_num = j;
                    int node_2_child_num = Layer.at(i-1).at(m).ChileNum[n];

                    if(node_1_num == node_2_child_num)
                    {
                        same_node_node_num.append(m);       //same_node_node_num里面方的是同时包括这个节点的父节点的序号
                        break;
                    }
                }
            }

            TreeNode test = Layer[i][j];
            if(same_node_node_num.count()>1)
            {

                QString name1 = Layer.at(i-1).at(same_node_node_num.at(0)).NodeName;
                QString name2 = Layer.at(i-1).at(same_node_node_num.at(1)).NodeName;

                QVector<QVector<int>> same_node_node_num_combo;     //排列组合
                QVector<int> temp;

                temp.append(same_node_node_num.at(0));
                same_node_node_num_combo.append(temp);
                for(int q=1; q<same_node_node_num.count(); q++)
                {
                    temp.clear();
                    int len = same_node_node_num_combo.count();
                    for(int p=0; p<len; p++)
                    {
                        temp.append(same_node_node_num_combo.at(p));
                        temp.append(same_node_node_num.at(q));
                        same_node_node_num_combo.append(temp);
                        temp.clear();
                    }
                    temp.append(same_node_node_num.at(q));
                    same_node_node_num_combo.append(temp);
                }

                //去除其中长度为1的
                for(int q=0; q<same_node_node_num_combo.count(); q++)
                {
                    if(same_node_node_num_combo.at(q).count() == 1)
                    {
                        same_node_node_num_combo.removeAt(q);
                        q--;
                    }
                }


                //排列组合


                for(int q=0; q<same_node_node_num_combo.count(); q++)
                {
                    QList<QList<QStringList>> temp_combo;
                    for(int p=0; p<same_node_node_num_combo.at(q).count(); p++)
                    {
                        temp_combo.append(Layer.at(i-1).at(same_node_node_num_combo.at(q).at(p)).Combo);
                    }

//                    timer.restart();
                    QList<QStringList> temp_result;
                    temp_result = _GetCombination(temp_combo);
//                    qDebug()<<"第二次循环时间"<<timer.elapsed();
                    for(int g=0; g<temp_result.count(); g++)
                    {
                        temp_result[g].append(Layer.at(i).at(j).NodeName);            //把子节点也加进去
                        temp_result[g].removeDuplicates();
                        temp_result[g].sort();
                    }

                    my_list.append(temp_result);


                }





            }

            same_node_node_num.clear();
        }


    }


    return my_list;

}

void ComboTree::_SortCombo()
{
    if(Layer.count()<1)
        return;

    for(int i=0; i<Layer.count(); i++)
    {
        for(int j=0; j<Layer.at(i).count(); j++)
        {
            for(int m=0; m<Layer.at(i).at(j).Combo.count(); m++)
            {
                Layer[i][j].Combo[m].sort();
            }
        }
    }
}

void ComboTree::_AddStringListToQListQStringList(const QStringList& A, QList<QStringList>& B)
{
    bool isSame = false;
    for(int i=0; i<B.count(); i++)
    {
        isSame = _Compare_StringList(A,B[i], true);
        if(isSame)
            return;
    }

    B.append(A);
}
