import re

file_path = r'd:\SynologyDrive\Project\T_DESIGNER\dialogUnitAttr.cpp'

with open(file_path, 'r', encoding='utf-8') as f:
    content = f.read()

# 修复第一处（on_BtnFromUnitImage_clicked 中的列号）
content = re.sub(
    r'(ui->tableWidgetUnitPic->item\(CurUnitImageIndex,0\)->data\(Qt::UserRole\)\.toString\(\);\s+if\(absoluteImagePath\.isEmpty\(\)\)return;\s+)// 更新第5列：图片路径或文件名\s+(QTableWidgetItem \*itemPic = new QTableWidgetItem\(absoluteImagePath\);\s+itemPic->setData\(Qt::UserRole, absoluteImagePath\);[^\n]+\s+ui->tableTerm->setItem\(currentRow, )5(, itemPic\);\s+)// 更新第4列：标注信息为"否"\s+(QTableWidgetItem \*itemAnnotated = new QTableWidgetItem\("否"\);\s+itemAnnotated->setData\(Qt::UserRole, ""\);[^\n]+\s+ui->tableTerm->setItem\(currentRow, )4(, itemAnnotated\);)',
    r'\1// 更新第6列：图片路径或文件名\n    \26\3// 更新第5列：标注信息为"否"\n    \45',
    content
)

# 修复第二处（on_BtnFromDisk_clicked 中的列号）  
content = re.sub(
    r'(CurImgPath=fileNames\.at\(0\);\s+int currentRow = ui->tableTerm->currentRow\(\);\s+)// 更新第5列：图片路径或文件名\s+(QTableWidgetItem \*itemPic = new QTableWidgetItem\(CurImgPath\);\s+itemPic->setData\(Qt::UserRole, CurImgPath\);[^\n]+\s+ui->tableTerm->setItem\(currentRow, )5(, itemPic\);\s+)// 更新第4列：标注信息为"否"\s+(QTableWidgetItem \*itemAnnotated = new QTableWidgetItem\("否"\);\s+itemAnnotated->setData\(Qt::UserRole, ""\);[^\n]+\s+ui->tableTerm->setItem\(currentRow, )4(, itemAnnotated\);)',
    r'\1// 更新第6列：图片路径或文件名\n    \26\3// 更新第5列：标注信息为"否"\n    \45',
    content
)

# 修复第三处（on_BtnCancelSign_clicked 中的列号）
content = re.sub(
    r'(ui->tableTerm->item\(ui->tableTerm->currentRow\(\), )4(\)->setText\("否"\);)',
    r'\15\2',
    content
)

with open(file_path, 'w', encoding='utf-8') as f:
    f.write(content)

print("修复完成")
