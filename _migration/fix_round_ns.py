#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复「轮次编号命名空间前缀」类错误。

## 问题

Legacy 里有大量 `Fate.R238E3.xxx` / `Fate.T314.yyy` 形式的命名空间
（按轮次编号）。迁移到 FateV2 后这些名字被放进了**普通域**，
但正文里的 `R238E3.xxx` 引用没有同步。

实测：

    Unknown identifier `R238E3.ErrProfileWeak`
    Unknown identifier `FateV2.Error.HasFitBoundary`

## 做法

1. 扫描 FateV2 全部文件，建立「定义名 → 它所在的完整命名空间」
2. 对每个 `R<数字>...` / `T<数字>...` 前缀引用 `PFX.name`：
   查 `name` 的定义处，把前缀替换为那个命名空间

## 用法

    python _migration/fix_round_ns.py            # 只报告
    python _migration/fix_round_ns.py --fix      # 实际改写
"""
import os, re, sys, json, argparse
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '轮次命名空间.csv')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')  # ⚠ 无名 end 也匹配（Lean 允许用它关闭 section）
DEF_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:structure|inductive|class|def|abbrev|opaque|theorem|lemma)\s+([A-Za-z_]\w*)')

# 同名多处的名字：人工指定权威位置。
# `IsFitBoundary` 在 6 个文件里各有定义（BridgeNW / Dimensions / FitBoundary /
# FitBoundaryLowerBound / FitBoundaryN / Modeling.Sigma），引用处语义上都指
# `Error/FitBoundary.lean` 里那份（拟合边界的权威定义）。
OVERRIDE = {
    'IsFitBoundary': 'FateV2.Error.Core',
    'ErrProfileWeak': 'FateV2.Error.Core',
    'HasFitBoundary': 'FateV2.Error.Core',
}

# 轮次编号前缀：R238E3 / T314 / R44 / T1A2 ...
PFX_RE = re.compile(r'(?<![\w.])([RT]\d+[A-Za-z0-9_]*)\.([A-Za-z_]\w*)')


def scan_defs():
    """name → 定义它的完整命名空间（若同名多处则记为 None 表示歧义）"""
    idx = {}
    ambig = set()
    for dp, _, fs in os.walk(V2):
        for fn in fs:
            if not fn.endswith('.lean'):
                continue
            p = os.path.join(dp, fn)
            stack = []
            with open(p, encoding='utf-8') as fh:
                for line in fh:
                    m = NS_RE.match(line)
                    if m:
                        stack.append(m.group(1))
                        continue
                    if END_RE.match(line) and stack:  # 无名 end 同样弹出
                        stack.pop()
                        continue
                    m = DEF_RE.match(line)
                    if m:
                        nm = m.group(1)
                        full = '.'.join(stack)
                        if nm in idx and idx[nm] != full:
                            ambig.add(nm)
                        idx.setdefault(nm, full)
    return idx, ambig


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fix', action='store_true')
    a = ap.parse_args()

    idx, ambig = scan_defs()
    rows = []
    fixes = defaultdict(list)

    for dp, _, fs in os.walk(V2):
        for fn in fs:
            if not fn.endswith('.lean'):
                continue
            p = os.path.join(dp, fn)
            rel = os.path.relpath(p, V2).replace(os.sep, '.')[:-5]
            with open(p, encoding='utf-8') as fh:
                text = fh.read()
            code = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
            code = re.sub(r'--[^\n]*', ' ', code)

            for m in PFX_RE.finditer(code):
                pfx, name = m.group(1), m.group(2)
                # 歧义名字：用人工覆盖表（同名多处定义时，取与本引用语境一致的那个）
                if name in OVERRIDE:
                    target = OVERRIDE[name]
                elif name in ambig or name not in idx:
                    continue
                else:
                    target = idx[name]
                # 已经是正确前缀就不动
                if code[m.start():].startswith(target + '.'):
                    continue
                cur = f'{pfx}.{name}'
                want = f'{target}.{name}'
                rows.append({'模块': rel, '原文': cur, '应为': want})
                fixes[rel].append((cur, want))

    import csv
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, 'w', encoding='utf-8-sig', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=['模块', '原文', '应为'])
        w.writeheader()
        w.writerows(rows)

    print(f'可疑引用: {len(rows)} 条，涉及 {len(fixes)} 个文件')
    for r in rows[:15]:
        print(f'  {r["模块"]:<44} {r["原文"]} → {r["应为"]}')

    if not a.fix:
        print(f'\n明细写入 {OUT}；加 --fix 执行改写')
        return

    n = 0
    for rel, pairs in fixes.items():
        p = os.path.join(V2, rel.replace('.', os.sep) + '.lean')
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
