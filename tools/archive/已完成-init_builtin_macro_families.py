# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

import sqlite3
import json

db_path = r'd:\SynologyDrive\Project\T_DESIGNER\templete\project.db'
conn = sqlite3.connect(db_path)
cursor = conn.cursor()

# 创建连接宏族表（如果不存在）
cursor.execute("""
CREATE TABLE IF NOT EXISTS port_connect_macro_family (
    family_id INTEGER PRIMARY KEY AUTOINCREMENT,
    family_name TEXT NOT NULL UNIQUE,
    domain TEXT NOT NULL,
    description TEXT,
    is_builtin INTEGER DEFAULT 0,
    macros_json TEXT NOT NULL,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP
)
""")

# 定义内置连接宏族
builtin_families = [
    {
        'family_name': 'electric-connect',
        'domain': 'electric',
        'description': '电气端口连接宏族',
        'is_builtin': 1,
        'macros': [
            {
                'arity': 2,
                'macro_name': 'connect2e',
                'expansion': '(assert (= (+ {0}.i {1}.i) 0))\n(assert (= {0}.u {1}.u))'
            },
            {
                'arity': 3,
                'macro_name': 'connect3e',
                'expansion': '(assert (= (+ {0}.i {1}.i {2}.i) 0))\n(assert (= {0}.u {1}.u))\n(assert (= {1}.u {2}.u))'
            },
            {
                'arity': 4,
                'macro_name': 'connect4e',
                'expansion': '(assert (= (+ {0}.i {1}.i {2}.i {3}.i) 0))\n(assert (= {0}.u {1}.u))\n(assert (= {1}.u {2}.u))\n(assert (= {2}.u {3}.u))'
            }
        ]
    },
    {
        'family_name': 'hydraulic-connect',
        'domain': 'hydraulic',
        'description': '液压端口连接宏族',
        'is_builtin': 1,
        'macros': [
            {
                'arity': 2,
                'macro_name': 'connect2h',
                'expansion': '(assert (= (+ {0}.q {1}.q) 0))\n(assert (= {0}.p {1}.p))'
            },
            {
                'arity': 3,
                'macro_name': 'connect3h',
                'expansion': '(assert (= (+ {0}.q {1}.q {2}.q) 0))\n(assert (= {0}.p {1}.p))\n(assert (= {1}.p {2}.p))'
            },
            {
                'arity': 4,
                'macro_name': 'connect4h',
                'expansion': '(assert (= (+ {0}.q {1}.q {2}.q {3}.q) 0))\n(assert (= {0}.p {1}.p))\n(assert (= {1}.p {2}.p))\n(assert (= {2}.p {3}.p))'
            }
        ]
    },
    {
        'family_name': 'mechanical-connect',
        'domain': 'mechanical',
        'description': '机械端口连接宏族（位移变量）',
        'is_builtin': 1,
        'macros': [
            {
                'arity': 2,
                'macro_name': 'connect2m',
                'expansion': '(assert (= (+ {0}.F {1}.F) 0))\n(assert (= {0}.x {1}.x))'
            },
            {
                'arity': 3,
                'macro_name': 'connect3m',
                'expansion': '(assert (= (+ {0}.F {1}.F {2}.F) 0))\n(assert (= {0}.x {1}.x))\n(assert (= {1}.x {2}.x))'
            },
            {
                'arity': 4,
                'macro_name': 'connect4m',
                'expansion': '(assert (= (+ {0}.F {1}.F {2}.F {3}.F) 0))\n(assert (= {0}.x {1}.x))\n(assert (= {1}.x {2}.x))\n(assert (= {2}.x {3}.x))'
            }
        ]
    }
]

# 插入内置宏族
for family in builtin_families:
    macros_json = json.dumps(family['macros'], ensure_ascii=False)
    cursor.execute("""
        INSERT OR REPLACE INTO port_connect_macro_family 
        (family_name, domain, description, is_builtin, macros_json)
        VALUES (?, ?, ?, ?, ?)
    """, (family['family_name'], family['domain'], family['description'], 
          family['is_builtin'], macros_json))

conn.commit()

# 验证插入
cursor.execute("SELECT family_name, domain, description FROM port_connect_macro_family")
rows = cursor.fetchall()
print(f"成功插入 {len(rows)} 个内置连接宏族:")
for row in rows:
    print(f"  - {row[0]} ({row[1]}): {row[2]}")

conn.close()
print("\n内置连接宏族初始化完成！")
