import csv, os
ROOT = r'C:\Users\xingg\Desktop\命运计划\Fate-world-prediction'
rows = list(csv.DictReader(open(os.path.join(ROOT, '_inventory', '引用图.csv'), encoding='utf-8-sig')))
fake = [r for r in rows if r['状态'] == '假接线']
# 按「被 import 次数」排序 —— import 多但未被调用 = 接线丢失最严重
top = sorted(fake, key=lambda x: (-int(x['被import']), -int(x['定义数'])))[:15]
print('假接线中「被 import 最多但无名字被调用」的 15 个:')
for r in top:
    print(f"  {r['模块']:<46} 被import{r['被import']:>3}  定义{r['定义数']:>3}")