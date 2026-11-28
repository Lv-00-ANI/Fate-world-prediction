import re, os
ROOT = r'C:\Users\xingg\Desktop\命运计划\Fate-world-prediction'
p = os.path.join(ROOT, 'FateWorld', 'FateV2', 'Predict', 'PearlLawRuleBridge.lean')
lines = open(p, encoding='utf-8').read().split('\n')
out = []
n = 0
# 任意变量名 .toLawRule / .toLawRuleNoCtx（代码行内）
pat_nc = re.compile(r'\b([A-Za-z_][A-Za-z0-9_′₀-₉]*?)\.toLawRuleNoCtx\b')
pat = re.compile(r'\b([A-Za-z_][A-Za-z0-9_′₀-₉]*?)\.toLawRule\b')
for l in lines:
    s = l.lstrip()
    if s.startswith('/-') or s.startswith('--') or s.startswith('|') or s.startswith('*') or s.startswith('-'):
        out.append(l)
        continue
    orig = l
    l = pat_nc.sub(lambda m: f'toLawRuleNoCtx {m.group(1)}', l)
    l = pat.sub(lambda m: f'toLawRule {m.group(1)}', l)
    if l != orig:
        n += 1
    out.append(l)
open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(out))
print(f'  再改写 {n} 行')