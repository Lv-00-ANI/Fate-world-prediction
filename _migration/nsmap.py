#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Legacy 命名空间 → FateV2 命名空间 的完整映射表。

## 为什么需要这张表

Legacy 模块里大量使用**裸 open**，例如：

    open PearlHierarchy SCMSemantics Finset
    open Causalean.Graph

迁移后这些命名空间在 FateV2 里换了位置：
- `Causalean.Graph`     → `FateV2.Modeling.Graph`
- `PearlHierarchy`      → `FateV2.Modeling.PearlHierarchy`
- `Fate.T43`            → `FateV2.Predict.T43Abduction`

没有这张表，迁移后必然报 `unknown namespace`。

## 构建方法

对每个**同时存在于 Legacy 与 FateV2** 的模块：
1. 取 Legacy 版的全部 namespace 名（含嵌套，如 `Fate.PearlHierarchy`、`Causalean.Graph`）
2. 取 FateV2 版的全部 namespace 名
3. 按**顺序配对**（第一个 Legacy ns ↔ 第一个 FateV2 ns）

这是启发式，但可用：同一个模块的命名空间层级在两边的结构一致，
只是根前缀不同。

用法：
    python _migration\\nsmap.py --build     # 重建映射表
    python _migration\\nsmap.py --stats
"""
import os, re, json, argparse
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
CACHE = os.path.join(ROOT, '_migration', 'ns_map.json')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end\s+(\S+)\s*$')


def namespaces_of(path):
    """返回文件内所有**完整**命名空间路径（按出现顺序，去重）。"""
    out = []
    stack = []
    with open(path, encoding='utf-8') as f:
        for line in f:
            m = NS_RE.match(line)
            if m:
                stack.append(m.group(1))
                full = '.'.join(stack)
                if full not in out:
                    out.append(full)
                continue
            m = END_RE.match(line)
            if m and stack:
                stack.pop()
    return out


def index(base):
    out = {}
    for dp, _, fs in os.walk(base):
        for f in fs:
            if f.endswith('.lean'):
                out.setdefault(f[:-5], []).append(os.path.join(dp, f))
    return out


def build():
    leg = index(LEGACY)
    v2 = index(V2)
    mapping = {}
    details = []

    for name in sorted(set(leg) & set(v2)):
        lp, vp = leg[name][0], v2[name][0]
        lns = namespaces_of(lp)
        vns = namespaces_of(vp)
        n = min(len(lns), len(vns))
        for i in range(n):
            mapping.setdefault(lns[i], vns[i])
            details.append({'模块': name, 'Legacy ns': lns[i], 'FateV2 ns': vns[i]})

    with open(CACHE, 'w', encoding='utf-8') as f:
        json.dump({'map': mapping, 'details': details}, f,
                  ensure_ascii=False, indent=1)
    return mapping, details


def load():
    if not os.path.exists(CACHE):
        return build()
    with open(CACHE, encoding='utf-8') as f:
        d = json.load(f)
    return d['map'], d['details']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--build', action='store_true')
    ap.add_argument('--stats', action='store_true')
    ap.add_argument('--lookup')
    a = ap.parse_args()

    if a.build:
        m, d = build()
        print(f'重建完成：{len(m)} 条映射')
        return

    m, d = load()
    print(f'映射条目: {len(m)}')

    if a.lookup:
        for k in (a.lookup, 'Fate.' + a.lookup):
            if k in m:
                print(f'  {k} → {m[k]}')
                return
        print(f'  {a.lookup}: 未找到')
        return

    if a.stats:
        print('\n=== 抽样 20 条 ===')
        for i, (k, v) in enumerate(list(m.items())[:20]):
            print(f'  {k:<40} → {v}')
        return

    print('\n=== 抽样 25 条 ===')
    for k, v in list(m.items())[:25]:
        print(f'  {k:<44} → {v}')


if __name__ == '__main__':
    main()
