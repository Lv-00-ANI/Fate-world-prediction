#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复迁移后残留的 `Fate.<名字>` 引用。

## 问题

迁移时规则 6 只改写「能在映射表/索引里查到」的 `Fate.X`。
查不到的会原样留下，例如：

    unknown namespace `Fate.AssemblyLearnsScratch`

`AssemblyLearnsScratch` 实际是 `FateV2.Loop.AssemblyLearnsScratch`
（定义在 Loop/ScratchAssemblyLearns.lean），但映射表里没有它。

## 做法

1. 扫描 FateV2 全部文件，收集**所有命名空间全名**（含嵌套）
2. 对每个残留 `Fate.<名字>`：
   - 若 `<名字>` 是某个 FateV2 命名空间的**最后一段**，取那个全名
   - 若唯一匹配 ⟹ 替换
   - 多义 ⟹ 报告，人工处理

## 用法

    python _migration/fix_leftover_fate.py            # 只报告
    python _migration/fix_leftover_fate.py --fix      # 执行
"""
import os, re, sys, json, argparse
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '残留Fate前缀.csv')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')  # ⚠ 无名 end 也匹配（Lean 允许用它关闭 section）
# 残留引用：Fate.X（后面可能还有 .Y）
REF_RE = re.compile(r'(?<![\w.`])Fate\.([A-Za-z_]\w*)')


def collect_namespaces():
    """返回 {最后一段: {完整命名空间}}"""
    bylast = defaultdict(set)
    for dp, _, fs in os.walk(V2):
        for fn in fs:
            if not fn.endswith('.lean'):
                continue
            stack = []
            with open(os.path.join(dp, fn), encoding='utf-8') as fh:
                for line in fh:
                    m = NS_RE.match(line)
                    if m:
                        stack.append(m.group(1))
                        full = '.'.join(stack)
                        bylast[stack[-1]].add(full)
                        continue
                    if END_RE.match(line) and stack:  # 无名 end 同样弹出
                        stack.pop()
    return bylast


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fix', action='store_true')
    a = ap.parse_args()

    bylast = collect_namespaces()
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

            for m in REF_RE.finditer(code):
                name = m.group(1)
                cands = bylast.get(name, set())
                if len(cands) == 1:
                    full = next(iter(cands))
                    # 命名空间本身就叫这个名字时不要重复拼
                    want = full if full.endswith('.' + name) else full + '.' + name
                    cur = f'Fate.{name}'
                    rows.append({'模块': rel, '原文': cur, '应为': want})
                    fixes[rel].append((cur, want))
                elif len(cands) > 1:
                    rows.append({'模块': rel, '原文': f'Fate.{name}',
                                 '应为': 'AMBIGUOUS: ' + ' | '.join(sorted(cands))})

    import csv
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, 'w', encoding='utf-8-sig', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=['模块', '原文', '应为'])
        w.writeheader()
        w.writerows(rows)

    uniq = [r for r in rows if not r['应为'].startswith('AMBIGUOUS')]
    amb = [r for r in rows if r['应为'].startswith('AMBIGUOUS')]
    print(f'残留 Fate. 引用: {len(rows)} 条（唯一可修 {len(uniq)}，多义 {len(amb)}）')
    seen = set()
    for r in rows:
        k = (r['原文'], r['应为'])
        if k in seen:
            continue
        seen.add(k)
        print(f'  {r["原文"]:<38} → {r["应为"]}')
        if len(seen) >= 20:
            break

    if not a.fix:
        print(f'\n明细写入 {OUT}；加 --fix 执行')
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
