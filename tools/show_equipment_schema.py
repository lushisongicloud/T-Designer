#!/usr/bin/env python3
"""查看Equipment表的结构"""
import sqlite3

def show_schema(db_path):
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # 获取Equipment表结构
    cursor.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name='Equipment'")
    result = cursor.fetchone()
    if result:
        print("Equipment表结构：")
        print(result[0])
        print()
    
    # 获取列信息
    cursor.execute("PRAGMA table_info(Equipment)")
    columns = cursor.fetchall()
    print("列信息：")
    for col in columns:
        print(f"  {col[1]:<20} {col[2]:<10} NOT NULL={col[3]} DEFAULT={col[4]}")
    
    conn.close()

if __name__ == "__main__":
    import sys
    db_path = sys.argv[1] if len(sys.argv) > 1 else "templete/project.db"
    show_schema(db_path)
