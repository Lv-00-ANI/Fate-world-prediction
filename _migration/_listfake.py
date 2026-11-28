import csv, os
from collections import Counter
ROOT = r'C:\Users\xingg\Desktop\命运计划\Fate-world-prediction'
rows = list(csv.DictReader(open(os.path.join(ROOT, '_inventory', '引用图.csv'), encoding='utf-8-sig')))
fake = [r for r in rows if r['状态'] == '假接线']
print(f'假接线 {len(fake)} 个，按域:')
c = Counter(r['域'] for r in fake)
for k, v in c.most_common():
    print(f'  {k:<12} {v}')
print()
print('定义数最多的 12 个（最值得接入）:')
for r in sorted(fake, key=lambda x: int(x['定义数']), reverse=True)[:12]:
    print(f"  {r['模块']:<44} 定义{r['定义数']:>3}  被import{r['被import']}")
print()
orphan = [r for r in rows if r['状态'] == '孤立']
print(f'孤立 {len(orphan)} 个，按域:')
c2 = Counter(r['域'] for r in orphan)
for k, v in c2.most_common():
    print(f'  {k:<12} {v}')