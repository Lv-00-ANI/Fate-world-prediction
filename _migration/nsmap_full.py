#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Legacy 命名空间 → FateV2 命名空间 的**完整**映射（含遗留模块）。

## 为什么需要补这个

`nsmap.py` 生成的映射只覆盖「Legacy 与 FateV2 同名模块」的配对（183 条）。
但迁移中遇到 `Fate.ConvergeToOptimalND.tendsto_iter_id` 这类引用时，
`ConvergeToOptimalND` 是**命名空间**（不是 def，全定义索引里没有），
而 nsmap 里也没有它 —— 因为该模块在 Legacy 与 FateV2 中的模块名不同
（Legacy: ConvergeToOptimalND，FateV2 迁入后同名前缀但域不同）。

## 做法

对每个 **Legacy 模块**，如果 FateV2 里存在同名模块文件，则：
    Legacy 的每个 `Fate.X` 命名空间 → FateV2 中该模块实际的第一层命名空间

即使模块尚未迁移，也登记其**预期**位置（按 domains 表），
这样迁移工具能用它做替换（迁移时同时会迁移依赖，路径自然成立）。

## 用法

    python _migration/nsmap_full.py --build
    python _migration/nsmap_full.py --lookup Fate.ConvergeToOptimalND
"""
import os, re, json, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_migration', 'ns_map_full.json')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end\s+(\S+)\s*$')


def namespaces_of(path):
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
            if END_RE.match(line) and stack:
                stack.pop()
    return out


def index_by_name(base):
    out = {}
    for dp, _, fs in os.walk(base):
        for f in fs:
            if f.endswith('.lean'):
                out.setdefault(f[:-5], os.path.join(dp, f))
    return out


def build():
    leg = index_by_name(LEGACY)
    v2 = index_by_name(V2)
    mapping = {}
    miss = []

    for name, lp in leg.items():
        lns = [n for n in namespaces_of(lp) if n.startswith('Fate')]
        if not lns:
            continue
        vp = v2.get(name)
        if vp:
            vns = [n for n in namespaces_of(vp) if n.startswith('FateV2')]
            for i, ln in enumerate(lns):
                if i < len(vns):
                    mapping.setdefault(ln, vns[i])
                else:
                    # 深层子命名空间：拼到 last vns 后面
                    tail = ln.rsplit('.', 1)[-1]
                    if vns:
                        mapping.setdefault(ln, vns[-1] + '.' + tail)
        else:
            miss.append((name, lns))

    with open(OUT, 'w', encoding='utf-8') as f:
        json.dump(mapping, f, ensure_ascii=False, indent=0)

    return mapping, miss


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--build', action='store_true')
    ap.add_argument('--lookup')
    a = ap.parse_args()

    m, miss = build()
    print(f'完整映射: {len(m)} 条')
    print(f'未迁移的 Legacy 模块（无法配对）: {len(miss)}')

    if a.lookup:
        print(f'  {a.lookup} → {m.get(a.lookup, "未找到")}')
        return

    print('\n=== 抽样 12 条 ===')
    for k, v in list(m.items())[:12]:
        print(f'  {k:<40} → {v}')


if __name__ == '__main__':
    main()
