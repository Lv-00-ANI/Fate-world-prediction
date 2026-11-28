import re, os
ROOT = r'C:\Users\xingg\Desktop\命运计划\Fate-world-prediction'
p = os.path.join(ROOT, 'FateWorld', 'FateV2', 'Predict', 'PearlLawRuleBridge.lean')
lines = open(p, encoding='utf-8').read().split('\n')
out = []
n = 0
for l in lines:
    s = l.lstrip()
    # 跳过注释/文档行
    if s.startswith('/-') or s.startswith('--') or s.startswith('|') or s.startswith('*') or s.startswith('-'):
        out.append(l)
        continue
    orig = l
    l = re.sub(r'\bM\.toLawRuleNoCtx\b', 'toLawRuleNoCtx M', l)
    l = re.sub(r'\bM\.toLawRule\b', 'toLawRule M', l)
    if l != orig:
        n += 1
    out.append(l)
open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(out))
print(f'  改写 {n} 行（代码行内的 M.toLawRule* → toLawRule* M）')