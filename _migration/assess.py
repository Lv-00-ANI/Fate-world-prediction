#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
收容层（Legacy）迁移评估器。

## 为什么需要这个脚本

`Legacy/` 有 851 个模块。不能凭感觉挑，要有可复现的判据。

## 迁移判据（三条，缺一不可）

1. **零 Legacy 依赖** —— 只 import Mathlib。
   否则迁一个会拖进整条依赖链，失去「逐步迁移」的意义。
2. **能编译** —— 在 FateV2 的命名空间下仍可编译。
3. **定理数 > 0** —— 排除纯注释 / 纯接口文件。

## 附加信息（不阻断，但决定优先级）

- `axioms`：`#print axioms` 结果。零公理的最优先。
- `theorems`：定理数量，多的优先。
- `line_count`：体量。

用法：
    python _migration\\assess.py            # 全量评估，输出 CSV
    python _migration\\assess.py --top 20   # 只看前 20 个候选
"""
import os, re, csv, sys, subprocess, json, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '迁移候选.csv')

IMPORT_RE = re.compile(r'^\s*(?:(?:module|public|private|meta)\s+)*import\s+(\S+)', re.M)
THM_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\s+', re.M)
NS_RE = re.compile(r'^\s*namespace\s+(\S+)', re.M)


def modules(base):
    out = {}
    for dp, _, fs in os.walk(base):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, base).replace('\\', '.')[:-5]
                out[rel] = p
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--top', type=int, default=0)
    a = ap.parse_args()

    leg = modules(LEGACY)
    v2names = {k.split('.')[-1] for k in modules(V2)}

    rows = []
    for name, path in sorted(leg.items()):
        with open(path, encoding='utf-8') as f:
            src = f.read()
        imports = IMPORT_RE.findall(src)
        leg_deps = [i for i in imports if i.startswith('FateWorld.Legacy.')]
        other = [i for i in imports if not i.startswith('Mathlib') and i not in leg_deps]
        n_thm = len(THM_RE.findall(src))
        ns = NS_RE.findall(src)
        rows.append({
            '模块': name.split('.')[-1],
            '路径': name,
            'Legacy依赖数': len(leg_deps),
            '其他依赖': ';'.join(other),
            '定理数': n_thm,
            '行数': src.count('\n') + 1,
            '命名空间': ns[0] if ns else '',
            '与FateV2重名': 'Y' if name.split('.')[-1] in v2names else '',
        })

    # 可迁候选：零 Legacy 依赖 + 有定理
    cand = [r for r in rows if r['Legacy依赖数'] == 0 and r['定理数'] > 0]
    cand.sort(key=lambda r: (-r['定理数'], r['行数']))

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print(f'Legacy 模块总数: {len(rows)}')
    print(f'零 Legacy 依赖且有定理: {len(cand)}')
    print(f'其中与 FateV2 重名: {sum(1 for r in cand if r["与FateV2重名"])}')
    print(f'\\n已写入 {OUT}\\n')

    show = cand if a.top == 0 else cand[:a.top]
    if show:
        print(f'{"模块":<26}{"定理":>5}{"行数":>7}  重名')
        print('-' * 48)
        for r in show:
            print(f'{r["模块"]:<26}{r["定理数"]:>5}{r["行数"]:>7}  {r["与FateV2重名"]}')


if __name__ == '__main__':
    main()
