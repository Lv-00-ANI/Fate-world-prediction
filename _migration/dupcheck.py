#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
重名模块核查器：判断 Legacy 与 FateV2 的同名模块是「同一份代码」还是「恰好同名」。

## 为什么要查

迁移第 1 层时有个陷阱：模块 `import FateWorld.Legacy.Foo`，
而 `Foo` 在 FateV2 里也有同名文件。若直接重定向 import，
**可能指向一个完全不同的模块**。

实测反例：`Completeness`
- `Legacy/Completeness.lean` —— FCA 概念格的完备性（31 定理）
- `FateV2/Export/Completeness.lean` —— 导出层的完备性（26 定理）
两者**只是文件名相同**，内容毫无关系。

## 判据

对每一对同名模块，比较：
1. 定理名集合的 Jaccard 相似度
2. 共享定理的比例

| 相似度 | 判定 |
|---|---|
| ≥ 0.8 | **同一模块**（可作为迁移目标） |
| 0.2 ~ 0.8 | **部分重叠**（需人工判断） |
| < 0.2 | **恰好同名**（不同模块，不可重定向） |

用法：
    python _migration\\dupcheck.py
    python _migration\\dupcheck.py --csv
"""
import os, re, csv, sys, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '重名模块核查.csv')

THM_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:theorem|lemma)\s+([A-Za-z_][\w\']*)', re.M)
NS_RE = re.compile(r'^\s*namespace\s+(\S+)', re.M)


def index(base):
    """模块短名 → (相对路径, 定理名集合, 首命名空间)"""
    out = {}
    for dp, _, fs in os.walk(base):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, base).replace('\\', '.')[:-5]
            with open(p, encoding='utf-8') as fh:
                s = fh.read()
            thms = set(THM_RE.findall(s))
            ns = NS_RE.findall(s)
            out.setdefault(f[:-5], []).append((rel, thms, ns[0] if ns else ''))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--csv', action='store_true')
    a = ap.parse_args()

    leg = index(LEGACY)
    v2 = index(V2)

    rows = []
    for name in sorted(set(leg) & set(v2)):
        lrel, lt, lns = leg[name][0]
        vrel, vt, vns = v2[name][0]
        union = lt | vt
        inter = lt & vt
        jac = len(inter) / len(union) if union else 0.0
        if jac >= 0.8:
            verdict = '同一模块'
        elif jac >= 0.2:
            verdict = '部分重叠'
        else:
            verdict = '恰好同名'
        rows.append({
            '模块': name,
            'Legacy路径': lrel,
            'FateV2路径': vrel,
            'Legacy定理': len(lt),
            'FateV2定理': len(vt),
            '共享': len(inter),
            'Jaccard': round(jac, 3),
            '判定': verdict,
            'Legacy命名空间': lns,
            'FateV2命名空间': vns,
        })

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    from collections import Counter
    c = Counter(r['判定'] for r in rows)
    print(f'重名模块: {len(rows)}')
    for k in ('同一模块', '部分重叠', '恰好同名'):
        print(f'  {k}: {c.get(k, 0)}')
    print(f'\\n已写入 {OUT}')

    if a.csv:
        return
    print(f'\\n=== 恰好同名（危险：不可重定向 import） ===')
    for r in rows:
        if r['判定'] == '恰好同名':
            print(f'  {r["模块"]:<24} Legacy/{r["Legacy路径"]:<28} vs FateV2/{r["FateV2路径"]}')


if __name__ == '__main__':
    main()
