#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
层位核查：判断每个模块的**实际层位**是否符合六层链路的依赖方向。

## 六层链路（来自 docs/archive/09-总设计/README.md:60-117）

    第 0 层 数学建模  Modeling
    第 1 层 模型      Model
    第 2 层 规则/IR   Rules
    第 3 层 预测      Predict
    第 4 层 导出      Export
    第 5 层 误差      Error
    第 6 层 闭环      Loop
    横切    元层      Meta
    基底    构造性核  Core / Classical / Bridge

## 依赖方向规则

**下层不得依赖上层。** 即：

    Core/Classical  → 只能依赖自己（基底）
    Modeling        → 可依赖 Core/Classical
    Model           → 可依赖 Modeling 及以下
    Rules           → 可依赖 Model 及以下
    Predict         → 可依赖 Rules 及以下
    Export          → 可依赖 Predict 及以下
    Error           → 可依赖 Export 及以下
    Loop            → 可依赖 Error 及以下

⚠ 实测事实：现有 FateV2 是 **DAG（零循环依赖）**，说明依赖本身可满足。
但存在**反向依赖**（下层 import 上层），这是层位错放，不是环。

## 用法

    python _migration/layercheck.py             # 列出全部违规
    python _migration/layercheck.py --summary   # 只出统计
"""
import os, re, sys, argparse
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
IMPORT_RE = re.compile(r'^\s*(?:(?:module|public|private|meta)\s+)*import\s+(\S+)', re.M)

# 层序（数字小 = 底层）
LAYER = {
    'Core': 0, 'Classical': 0, 'Bridge': 0,
    'Modeling': 1,
    'Model': 2,
    'Rules': 3,
    'Predict': 4,
    'Export': 5,
    'Error': 6,
    'Loop': 7,
    # Meta 是横切关注点，不参与线性层序；Demo/Data 是应用层
    'Meta': None, 'Demo': None, 'Data': None,
}


def build():
    """返回 [(模块, 所在域, [依赖的域...])]"""
    out = []
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, V2).replace('\\', '.')[:-5]
            dom = rel.split('.')[0]
            with open(p, encoding='utf-8') as fh:
                s = fh.read()
            deps = set()
            for m in IMPORT_RE.finditer(s):
                t = m.group(1)
                if t.startswith('FateWorld.FateV2.'):
                    parts = t.split('.')
                    if len(parts) >= 4:
                        d = parts[2]
                        if d != dom:
                            deps.add(d)
            out.append((rel, dom, sorted(deps), len(s.split('\n'))))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', action='store_true')
    a = ap.parse_args()

    mods = build()
    violations = []
    for rel, dom, deps, lines in mods:
        me = LAYER.get(dom)
        if me is None:
            continue
        for d in deps:
            other = LAYER.get(d)
            if other is None:
                continue
            if other > me:                 # 依赖了更高层
                violations.append((rel, dom, d, lines))

    print(f'FateV2 模块: {len(mods)}')
    print(f'反向依赖（下层 import 上层）: {len(violations)}')

    by = defaultdict(list)
    for rel, dom, d, lines in violations:
        by[(dom, d)].append((rel, lines))

    print('\n=== 按「从哪层→到哪层」分组 ===')
    for (dom, d), items in sorted(by.items(), key=lambda x: -len(x[1])):
        print(f'  {dom:<10} → {d:<10} {len(items):>2} 处')

    if a.summary:
        return

    print('\n=== 详细（前 40）===')
    for rel, dom, d, lines in violations[:40]:
        print(f'  {rel:<44} ({lines:>4} 行)  → {d}')


if __name__ == '__main__':
    main()
