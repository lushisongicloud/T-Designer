import sqlite3
import sys

def check_database(db_path, db_name):
    print(f"\n{'='*60}")
    print(f"检查数据库: {db_name}")
    print(f"路径: {db_path}")
    print(f"{'='*60}\n")
    
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        
        # 1. 检查 diagnosis_tree 表
        print("1. diagnosis_tree 表内容:")
        cursor.execute("SELECT tree_id, container_id, name, root_node_id FROM diagnosis_tree")
        trees = cursor.fetchall()
        print(f"   共有 {len(trees)} 个决策树")
        for tree in trees[:3]:  # 只显示前3个
            print(f"   - tree_id={tree[0]}, container_id={tree[1]}, name={tree[2]}, root_node_id={tree[3]}")
        if len(trees) > 3:
            print(f"   ... (还有 {len(trees)-3} 个)")
        
        # 2. 检查 diagnosis_tree_node 表
        print(f"\n2. diagnosis_tree_node 表:")
        cursor.execute("SELECT COUNT(*) FROM diagnosis_tree_node")
        node_count = cursor.fetchone()[0]
        print(f"   共有 {node_count} 个节点")
        
        # 3. 检查根节点是否有效
        print(f"\n3. 根节点有效性检查:")
        cursor.execute("""
            SELECT dt.tree_id, dt.name, dt.root_node_id, 
                   CASE WHEN dtn.node_id IS NULL THEN 'MISSING' ELSE 'OK' END as status
            FROM diagnosis_tree dt
            LEFT JOIN diagnosis_tree_node dtn ON dt.root_node_id = dtn.node_id
        """)
        root_checks = cursor.fetchall()
        invalid_count = sum(1 for r in root_checks if r[3] == 'MISSING')
        print(f"   有效根节点: {len(root_checks) - invalid_count}/{len(root_checks)}")
        if invalid_count > 0:
            print(f"   ⚠️  {invalid_count} 个决策树的根节点无效!")
            for check in root_checks:
                if check[3] == 'MISSING':
                    print(f"      - tree_id={check[0]}, root_node_id={check[2]}")
        
        # 4. 检查 container 表
        print(f"\n4. container 表:")
        cursor.execute("SELECT COUNT(*) FROM container")
        container_count = cursor.fetchone()[0]
        print(f"   共有 {container_count} 个容器")
        
        cursor.execute("""
            SELECT container_id, name, 
                   CASE 
                       WHEN analysis_json IS NULL THEN 'NULL'
                       WHEN analysis_json = '' THEN 'EMPTY'
                       ELSE 'HAS_DATA'
                   END as analysis_status
            FROM container
            WHERE analysis_json IS NOT NULL AND analysis_json != ''
        """)
        containers_with_analysis = cursor.fetchall()
        print(f"   有 analysis_json 数据的容器: {len(containers_with_analysis)}")
        
        # 5. 检查数据库表是否有索引
        print(f"\n5. diagnosis_tree 表的索引:")
        cursor.execute("""
            SELECT name FROM sqlite_master 
            WHERE type='index' AND tbl_name='diagnosis_tree'
        """)
        indexes = cursor.fetchall()
        print(f"   索引数量: {len(indexes)}")
        for idx in indexes:
            print(f"   - {idx[0]}")
        
        conn.close()
        print(f"\n✅ 数据库 {db_name} 检查完成\n")
        
    except Exception as e:
        print(f"\n❌ 错误: {e}\n")

# 检查两个数据库
db1_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"
db2_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\双电机拖曳收放装置\双电机拖曳收放装置.db"

check_database(db1_path, "集中油源动力系统")
check_database(db2_path, "双电机拖曳收放装置")

print("\n" + "="*60)
print("对比总结:")
print("="*60)
print("根据以上检查，两个数据库在结构上应该是一致的。")
print("问题可能出在:")
print("1. 数据库连接的传递方式")
print("2. TestManagementDialog 构造函数接收的数据库对象")
print("3. loadData() 调用时机")
