#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
全局命名空间索引与 open 改写器。

## 问题

Legacy 里有 823 处**裸 `open`**（无 `Fate.` 前缀），例如：

    open PearlHierarchy SCMSemantics Finset

`PearlHierarchy` 实际是 `Fate.PearlHierarchy`。迁移到 FateV2 后，
它变成 `FateV2.Modeling.PearlHierarchy`，裸 `open PearlHierarchy` 就失效。
实测反例：`CfNecessity` 迁移后报 `unknown namespace PearlHierarchy`。

## 解法

1. 扫描 Legacy 全部 namespace 定义，建索引：`Fate.Sub` → 定义它的模块
2. 扫描 FateV2 已迁模块，建反向索引：模块名 → FateV2 全路径
3. 改写裸 open：
   - Mathlib 命名空间（Finset / Set / Filter / Topology / MeasureTheory …
     ProbabilityTheory / BigOperators / Classical / ENNReal …）→ **不动**
   - `Fate.Sub` → `FateV2.<Domain>.Sub`
   - `Sub`（Fate 的子命名空间）→ `FateV2.<Domain>.Sub`
   - 其他不明 → 保留并告警

## 用法

    python _migration\\nsindex.py --stats
    python _migration\\nsindex.py --rewrite <文件>   # 试改写
"""
import os, re, json, argparse, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
CACHE = os.path.join(ROOT, '_migration', 'ns_index.json')

# Mathlib / Lean 核心命名空间，改写时不动
MATHLIB_NS = {
    'Finset', 'Set', 'Filter', 'Topology', 'MeasureTheory', 'ProbabilityTheory',
    'BigOperators', 'Classical', 'ENNReal', 'NNReal', 'Real', 'Nat', 'Int',
    'List', 'Option', 'Function', 'Relation', 'Order', 'Group', 'Ring', 'Field',
    'Algebra', 'Module', 'Matrix', 'Polynomial', 'Complex', 'Interval',
    'ContinuousLinearMap', 'InnerProductSpace', 'Measure', 'Ball', 'Metric',
    'Bornology', 'CategoryTheory', 'Equiv', 'Submodule', 'Monoid', 'Semigroup',
    'Category', 'Functor', 'MvPolynomial', 'Rat', 'Bool', 'Multiset',
}


def build():
    """扫描 Legacy，建立 namespace → 模块 的索引。"""
    idx = {}
    for dp, _, fs in os.walk(LEGACY):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            with open(p, encoding='utf-8') as fh:
                s = fh.read()
            stack = []
            for line in s.split('\n'):
                m = re.match(r'^\s*namespace\s+(\S+)', line)
                if m:
                    stack.append(m.group(1))
                    idx.setdefault('.'.join(stack), f[:-5])
                    continue
                m = re.match(r'^\s*end\s+(\S+)\s*$', line)
                if m and stack:
                    stack.pop()
    return idx


def v2_paths():
    """模块短名 → FateV2 全模块路径（不含 FateWorld. 前缀）"""
    out = {}
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, V2).replace('\\', '.')[:-5]
                out[f[:-5]] = f'FateV2.{rel}'
    return out


def load():
    if os.path.exists(CACHE):
        with open(CACHE, encoding='utf-8') as f:
            d = json.load(f)
        return d['legacy'], d['v2']
    lg, v2 = build(), v2_paths()
    with open(CACHE, 'w', encoding='utf-8') as f:
        json.dump({'legacy': lg, 'v2': v2}, f, ensure_ascii=False, indent=1)
    return lg, v2


def rewrite_opens(text, leg_idx, v2map):
    """
    改写裸 open。返回 (新文本, 告警列表)。

    只在 `open ...` 行内操作；`open X in` 这种修饰用法也覆盖。
    """
    warnings = []

    def fix_target(t):
        t = t.rstrip(',')
        if t in MATHLIB_NS:
            return t
        if t.startswith('Fate.'):
            sub = t[5:]
            mod = leg_idx.get(t) or leg_idx.get('Fate.' + sub.split('.')[0])
            if mod and mod in v2map:
                # Fate.Sub → FateV2.<域>.Sub
                base = v2map[mod]                  # 例 FateV2.Modeling.PearlHierarchy
                if '.' in sub:
                    # Fate.R259.xxx 这种：模块是 BackdoorCriterion
                    return base + '.' + sub.split('.', 1)[1] if sub.split('.')[0] == mod else base
                return base
            warnings.append(f'未解析 open Fate.*: {t}')
            return t
        # 裸名：可能是 Fate 的子命名空间
        for cand in (f'Fate.{t}',):
            mod = leg_idx.get(cand)
            if mod and mod in v2map:
                return v2map[mod]
        if t in MATHLIB_NS:
            return t
        warnings.append(f'未解析裸 open: {t}')
        return t

    out_lines = []
    for line in text.split('\n'):
        m = re.match(r'^(\s*open\s+)(.+)$', line)
        if not m:
            out_lines.append(line)
            continue
        prefix, rest = m.group(1), m.group(2)
        # 处理 `open X Y Z` 与 `open X in`
        trail = ''
        if rest.endswith(' in'):
            rest, trail = rest[:-3], ' in'
        parts = rest.split()
        new_parts = [fix_target(p) for p in parts]
        out_lines.append(prefix + ' '.join(new_parts) + trail)
    return '\n'.join(out_lines), warnings


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stats', action='store_true')
    ap.add_argument('--rewrite')
    a = ap.parse_args()

    leg, v2 = load()
    print(f'Legacy 命名空间: {len(leg)}')
    print(f'FateV2 模块:     {len(v2)}')

    if a.stats:
        # 有多少裸 open 能解析
        resolvable = unresolvable = 0
        for dp, _, fs in os.walk(LEGACY):
            for f in fs:
                if not f.endswith('.lean'):
                    continue
                with open(os.path.join(dp, f), encoding='utf-8') as fh:
                    s = fh.read()
                _, warns = rewrite_opens(s, leg, v2)
                unresolvable += len(warns)
        print(f'\\n无法解析的 open 目标: {unresolvable}')
        return

    if a.rewrite:
        with open(a.rewrite, encoding='utf-8') as fh:
            s = fh.read()
        new, warns = rewrite_opens(s, leg, v2)
        print(new[:3000])
        if warns:
            print(f'\\n告警 {len(warns)} 条：')
            for w in warns[:10]:
                print('  ' + w)


if __name__ == '__main__':
    main()
