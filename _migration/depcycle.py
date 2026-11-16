#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
依赖环检测：在**模块级**（而非域级）判断是否存在真正的循环依赖。

## 为什么要模块级

域级别看到 `Loop → Error` 和 `Error → Loop` 会以为是环，
但这不代表真的有环——真正的环要看**具体模块**：

    Loop/Convergence      → Error/ErrorBand
    Error/ErrorBand       → Loop/Residual      ← 这两个之间不是环

只有当 A→B→...→A 走回来落到同一个模块，才是真正的循环依赖。

## 用法

    python _migration/depcycle.py            # 全库环检测
    python _migration/depcycle.py --domains  # 域级矩阵
    python _migration/depcycle.py --depth    # 最长依赖链
"""
import os, re, sys, argparse
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')

IMPORT_RE = re.compile(r'^\s*(?:(?:module|public|private|meta)\s+)*import\s+(\S+)', re.M)


def build_graph(base=V2):
    """模块全名 → 依赖模块全名集合（只含 FateWorld.FateV2.*）"""
    g = {}
    for dp, _, fs in os.walk(base):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, base).replace('\\', '.')[:-5]
            name = f'FateWorld.FateV2.{rel}'
            with open(p, encoding='utf-8') as fh:
                s = fh.read()
            deps = set()
            for m in IMPORT_RE.finditer(s):
                t = m.group(1)
                if t.startswith('FateWorld.FateV2.'):
                    deps.add(t)
            g[name] = deps
    return g


def find_cycles(g):
    """Tarjan 强连通分量：SCC 大小 > 1 即为环；自环单独处理。"""
    index = {}
    low = {}
    onstack = {}
    stack = []
    result = []
    counter = [0]

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        onstack[v] = True
        for w in g.get(v, ()):
            if w not in g:
                continue
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif onstack.get(w):
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                onstack[w] = False
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                result.append(comp)

    sys.setrecursionlimit(100000)
    for v in list(g):
        if v not in index:
            strong(v)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--domains', action='store_true')
    ap.add_argument('--depth', action='store_true')
    ap.add_argument('--loops-only', action='store_true')
    a = ap.parse_args()

    g = build_graph()
    print(f'FateV2 模块: {len(g)}')

    cycles = find_cycles(g)
    print(f'\n=== 真正的循环依赖（SCC 大小>1）: {len(cycles)} 个 ===')
    for c in sorted(cycles, key=len, reverse=True)[:10]:
        print(f'  [{len(c)} 个模块成环]')
        for m in c[:6]:
            print(f'    {m.replace("FateWorld.FateV2.", "")}')
        if len(c) > 6:
            print(f'    … 还有 {len(c)-6} 个')

    if not cycles:
        print('  ✅ 无环（依赖图是 DAG）')

    if a.domains:
        edges = defaultdict(set)
        for m, deps in g.items():
            d1 = m.split('.')[2] if len(m.split('.')) > 3 else 'root'
            for d in deps:
                d2 = d.split('.')[2] if len(d.split('.')) > 3 else 'root'
                if d1 != d2:
                    edges[d1].add(d2)
        print('\n=== 域级依赖（含传递，非环）===')
        for d1 in sorted(edges):
            print(f'  {d1:<12} → {", ".join(sorted(edges[d1]))}')

    if a.depth:
        memo = {}

        def longest(v, seen=None):
            if v in memo:
                return memo[v]
            seen = seen or set()
            if v in seen:
                return 0
            seen = seen | {v}
            best = 0
            for w in g.get(v, ()):
                if w in g:
                    best = max(best, 1 + longest(w, seen))
            memo[v] = best
            return best

        top = sorted(((longest(v), v) for v in g), reverse=True)[:8]
        print('\n=== 最长依赖链 ===')
        for n, v in top:
            print(f'  {n:>3}  {v.replace("FateWorld.FateV2.", "")}')


if __name__ == '__main__':
    main()
