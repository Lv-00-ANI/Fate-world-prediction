#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复「按域限定但域写错」的引用。

## 问题

模块搬域后，引用它的地方还挂着旧域前缀：

    Unknown identifier `FateV2.Error.Stage2.ErrorBoundE2c.log_one_add_le`

`ErrorBoundE2c` 实际在 `FateV2.Predict.Stage2.ErrorBoundE2c`（Predict 域），
但引用写成 `FateV2.Error.Stage2.ErrorBoundE2c`。

## 做法

1. 收集每个 FateV2 **模块名 → 所在域**（顶层目录）
2. 扫描全限定引用 `FateV2.<域A>.<…>.<模块名>.<成员>`
3. 若 `<模块名>` 所在域 ≠ 域A ⟹ 改写为正确域

## 用法

    python _migration/fix_wrong_domain.py            # 报告
    python _migration/fix_wrong_domain.py --fix      # 执行
"""
import os, re, sys, csv, argparse
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '错域引用.csv')

# FateV2.<域>.<中间段们>.<模块名>.<成员路径>
REF = re.compile(r'FateV2\.([A-Za-z_]\w*)\.((?:[A-Za-z_]\w*\.)*)([A-Za-z_]\w*)(\.[A-Za-z_][\w.]*)')


def module_domains():
    """模块名 → 所在域集合"""
    m = defaultdict(set)
    for dom in os.listdir(V2):
        d = os.path.join(V2, dom)
        if not os.path.isdir(d):
            continue
        for f in os.listdir(d):
            if f.endswith('.lean'):
                m[f[:-5]].add(dom)
    return m


def namespace_names():
    """收集 FateV2 里声明的所有命名空间末段。

    ⚠ 必须排除这些：`FateV2.Error.Core` 里的 `Core` 是**命名空间**，
    不是 `Core` 域的那个模块。不加排除会把
    `FateV2.Error.Core.IsFitBoundary` 错改成 `FateV2.Core.Core.IsFitBoundary`。
    """
    names = set()
    for dp, _, fs in os.walk(V2):
        for fn in fs:
            if not fn.endswith('.lean'):
                continue
            with open(os.path.join(dp, fn), encoding='utf-8') as fh:
                for line in fh:
                    m = re.match(r'^\s*namespace\s+(\S+)', line)
                    if m:
                        for seg in m.group(1).split('.'):
                            names.add(seg)
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fix', action='store_true')
    a = ap.parse_args()

    mods = module_domains()
    nsnames = namespace_names()
    rows = []
    fixes = defaultdict(list)

    for dom in sorted(os.listdir(V2)):
        d = os.path.join(V2, dom)
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            if not fn.endswith('.lean'):
                continue
            p = os.path.join(d, fn)
            with open(p, encoding='utf-8') as fh:
                text = fh.read()
            code = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
            code = re.sub(r'--[^\n]*', ' ', code)

            for m in REF.finditer(code):
                dom_a, mid, modname, member = m.group(1), m.group(2), m.group(3), m.group(4)
                if modname not in mods or modname in nsnames:
                    continue
                real = mods[modname]
                if len(real) != 1:
                    continue
                real = next(iter(real))
                if real == dom_a:
                    continue
                cur = f'FateV2.{dom_a}.{mid}{modname}'
                want = f'FateV2.{real}.{mid}{modname}'
                rows.append({'模块': f'{dom}.{fn[:-5]}', '原文': cur, '应为': want})
                fixes[f'{dom}.{fn[:-5]}'].append((cur, want))

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, 'w', encoding='utf-8-sig', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=['模块', '原文', '应为'])
        w.writeheader()
        w.writerows(rows)

    print(f'错域引用: {len(rows)} 条，涉及 {len(fixes)} 个文件')
    seen = set()
    for r in rows:
        k = (r['原文'], r['应为'])
        if k in seen:
            continue
        seen.add(k)
        print(f'  {r["原文"]:<50} → {r["应为"]}')
        if len(seen) >= 20:
            break

    if not a.fix:
        print(f'\n明细写入 {OUT}；加 --fix 执行')
        return

    n = 0
    for rel, pairs in fixes.items():
        p = os.path.join(V2, rel.replace('.', os.sep) + '.lean')
        if not os.path.exists(p):
            continue
        with open(p, encoding='utf-8') as fh:
            text = fh.read()
        for cur, want in pairs:
            text = text.replace(cur, want)
        with open(p, 'w', encoding='utf-8', newline='\n') as fh:
            fh.write(text)
        n += 1
    print(f'已改写 {n} 个文件')


if __name__ == '__main__':
    main()
