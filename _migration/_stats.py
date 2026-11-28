import csv, os
from collections import Counter, defaultdict
ROOT = r'C:\Users\xingg\Desktop\命运计划\Fate-world-prediction'
rows = list(csv.DictReader(open(os.path.join(ROOT, '_inventory', '引用图.csv'), encoding='utf-8-sig')))
print('按域（真消费 / 假接线 / 孤立）:')
doms = defaultdict(Counter)
for r in rows:
    doms[r['域']][r['状态']] += 1
for d in sorted(doms, key=lambda x: -sum(doms[x].values())):
    c = doms[d]
    tot = sum(c.values())
    print(f'  {d:<12} 共{tot:>3}  真{c["真消费"]:>3}  假{c["假接线"]:>3}  孤{c["孤立"]:>3}')

print()
fake = [r for r in rows if r['状态'] == '假接线']
print(f'假接线 351 个中，定义数最多的 15 个:')
for r in sorted(fake, key=lambda x: int(x['定义数']), reverse=True)[:15]:
    print(f"  {r['模块']:<46} 定义{r['定义数']:>3} 被import{r['被import']:>3}")