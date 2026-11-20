import re, json, os
from collections import Counter
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
log = open(os.path.join(ROOT, '_pred_build.txt'), encoding='utf-8', errors='replace').read()
ids = set(re.findall(r'Unknown identifier .([^`.]+).', log))
unk = set(re.findall(r'unknown namespace .([^`.]+).', log))
d = json.load(open(os.path.join(ROOT, '_migration', 'name_index.json'), encoding='utf-8'))
defs = d['defs']
print(f'  Unknown identifier: {len(ids)} 种')
print(f'  unknown namespace : {len(unk)} 种 -> {sorted(unk)}')
print()
cnt = Counter()
for i in sorted(ids):
    if '.' in i:
        pfx, nm = i.split('.', 1)
        nm = nm.split('.')[0]
        if nm in defs:
            cnt[(pfx, nm, tuple(defs[nm][:2]))] += 1
for (pfx, nm, real), c in cnt.most_common(20):
    print(f'  {pfx}.{nm:<26} 实际在 {list(real)}')
