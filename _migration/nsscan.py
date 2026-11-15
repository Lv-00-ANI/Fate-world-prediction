#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
硬编码命名空间引用排查器。

## 为什么要查这个

迁移一个模块时，除了 `namespace X` / `end X` 两行，文件正文里可能还有
**全限定名引用**，例如：

    #print axioms Fate.T43.xxx
    have h := Fate.PearlHierarchy.foo

这些引用**不会随 namespace 行一起改**，导致迁移后编译失败。
实测反例：`CfNecessity` 迁移后报 `unknown namespace PearlHierarchy` / `Fate.T43`。

## 分类

对每个 Legacy 模块，统计正文中 `Fate.<X>` 形式的引用：

| 类别 | 含义 | 迁移影响 |
|---|---|---|
| `own_ns` | 引用自己模块的命名空间 | 随 namespace 改 |
| `other_ns` | 引用**其他** Legacy 模块的命名空间 | **必须单独改写** |
| `#print` | `#print axioms` 里的全限定名 | 单独改写，且若名字不存在会失败 |

## 用法

    python _migration\\nsscan.py              # 汇总
    python _migration\\nsscan.py --module X   # 看单个模块
    python _migration\\nsscan.py --summary    # 只出统计
"""
import os, re, csv, sys, argparse
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '硬编码命名空间.csv')

NS_DEF = re.compile(r'^\s*namespace\s+(\S+)', re.M)
# 正文中的 Fate.Xxx.Yyy 引用（不在 namespace 定义行）
FATE_REF = re.compile(r'(?<![\w.])Fate\.([A-Za-z_][\w\']*(?:\.[A-Za-z_][\w\']*)*)')
PRINT_AX = re.compile(r'^\s*#print\s+axioms\s+(Fate\.\S+)', re.M)


def scan():
    rows = []
    for dp, _, fs in os.walk(LEGACY):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            name = f[:-5]
            with open(p, encoding='utf-8') as fh:
                s = fh.read()

            own = NS_DEF.findall(s)
            own_root = own[0] if own else ''
            # 自己模块的顶层命名空间（Fate 或 Fate.Sub）
            self_ns = own_root

            refs = Counter()
            for m in FATE_REF.finditer(s):
                full = 'Fate.' + m.group(1)
                refs[full] += 1

            own_hits = 0
            other_hits = 0
            other_list = Counter()
            for ref, n in refs.items():
                if ref == self_ns or ref.startswith(self_ns + '.'):
                    own_hits += n
                else:
                    other_hits += n
                    other_list[ref] += n

            prints = PRINT_AX.findall(s)

            if other_hits or prints:
                rows.append({
                    '模块': name,
                    '自命名空间': self_ns,
                    '自身引用': own_hits,
                    '外部引用': other_hits,
                    'print_axioms': len(prints),
                    '外部引用明细': ';'.join(f'{k}({v})' for k, v in other_list.most_common(6)),
                    'print明细': ';'.join(prints[:5]),
                })
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--module')
    ap.add_argument('--summary', action='store_true')
    a = ap.parse_args()

    rows = scan()
    rows.sort(key=lambda r: (-r['外部引用'], -r['print_axioms']))

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    if rows:
        with open(OUT, 'w', encoding='utf-8-sig', newline='') as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)

    if a.module:
        for r in rows:
            if r['模块'] == a.module:
                for k, v in r.items():
                    print(f'{k}: {v}')
                return
        print(f'{a.module}: 无硬编码外部引用')
        return

    total = sum(1 for _ in os.walk(LEGACY))
    n_files = sum(1 for dp, _, fs in os.walk(LEGACY) for x in fs if x.endswith('.lean'))
    with_other = sum(1 for r in rows if r['外部引用'] > 0)
    with_print = sum(1 for r in rows if r['print_axioms'] > 0)

    print(f'Legacy 模块总数: {n_files}')
    print(f'  有外部命名空间引用: {with_other}')
    print(f'  有 #print axioms:   {with_print}')
    print(f'  合计需特殊处理:     {len(rows)}')
    print(f'\\n已写入 {OUT}')

    if a.summary:
        return

    print(f'\\n=== 外部引用最多的 15 个 ===')
    for r in rows[:15]:
        print(f'  {r["模块"]:<28} 外部{r["外部引用"]:>3}  print{r["print_axioms"]:>3}  {r["外部引用明细"][:60]}')


if __name__ == '__main__':
    main()
