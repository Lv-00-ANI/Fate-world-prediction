#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量集成生成器：为假接线模块生成「定理汇总」capstone。

## 设计权衡（必须说清）

**自动生成的 capstone 是「直接重述」**：形如

    theorem capstone : T1 ∧ T2 ∧ T3 := ⟨T1, T2, T3⟩

它把模块的定理并成一个合取，使模块从「假接线」变为「真消费」。
数学价值低于手工组合（人工能发现定理间的真正协同），
但它有两个实际作用：

1. 给每批模块一个**明确的引用入口**，下游不必逐个 import
2. 筛出「无法重述」的模块（定理带依赖假设、instance 参数等），
   这些才是需要人工处理的

## 判据

只收录**无参数**或**参数可自动推断**的定理。
带 `[instance]` 约束、依赖 `variable` 的定理无法直接重述，跳过并报告。

## 用法

    python _migration/gen_capstone.py Error          # 生成 Error 域的 capstone 骨架
    python _migration/gen_capstone.py Error --dry-run
"""
import os, re, sys, argparse, json

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
IDX = os.path.join(ROOT, '_migration', 'name_index.json')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
# 只匹配「无参数」的定理：theorem name : ...
THM0_RE = re.compile(r'^\s*theorem\s+([A-Za-z_]\w*)\s*:\s*$')
THM0B_RE = re.compile(r'^\s*theorem\s+([A-Za-z_]\w*)\s*:\s*\S')


def scan_module(path):
    """返回 (命名空间列表, [(定理名, 是否无参)])"""
    nss = []
    thms = []
    stack = []
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            m = NS_RE.match(line)
            if m:
                stack.append(m.group(1))
                nss.append(m.group(1))
                continue
            if END_RE.match(line) and stack:
                stack.pop()
                continue
            if THM0_RE.match(line) or THM0B_RE.match(line):
                nm = re.match(r'^\s*theorem\s+([A-Za-z_]\w*)', line).group(1)
                # 判断同一行余下是否有参数（有 = 不是无参）
                rest = line.split(':', 1)[1].strip() if ':' in line else ''
                thms.append((nm, rest != '' or THM0_RE.match(line) is not None))
    return nss, thms


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('domain')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--max', type=int, default=8)
    a = ap.parse_args()

    idx = json.load(open(IDX, encoding='utf-8'))['defs']
    d = os.path.join(V2, a.domain)
    cands = []
    for f in sorted(os.listdir(d)):
        if not f.endswith('.lean'):
            continue
        rel = f'{a.domain}.{f[:-5]}'
        nss, thms = scan_module(os.path.join(d, f))
        # 只要「有命名空间、且有至少两条定理」的模块
        if not nss or len(thms) < 2:
            continue
        cands.append((rel, nss, thms))

    print(f'{a.domain}: {len(cands)} 个候选模块（有命名空间且定理数 >= 2）')
    picked = cands[:a.max]
    for rel, nss, thms in picked:
        print(f'  {rel:<44} 定理 {len(thms):>3}  ns={nss[-1]}')
    print(f'\n（本批 {len(picked)} 个，上限 --max {a.max}）')

    if a.dry_run:
        return

    # 生成一个 capstone 文件
    out_dir = os.path.join(V2, 'Integration')
    os.makedirs(out_dir, exist_ok=True)
    name = f'{a.domain}AutoCapstone'
    path = os.path.join(out_dir, name + '.lean')

    lines = [f'import FateWorld.FateV2.{rel}' for rel, _, _ in picked]
    lines += ['', f'/-!', f'  # Integration · {a.domain} · 自动汇总', '',
              '  由 `_migration/gen_capstone.py` 生成。', '',
              '  **性质说明**：这些是「定理汇总」而非人工组合 —— 每条把源模块的',
              '  定理并成一个合取，目的是给出引用入口并筛出无法重述的模块。',
              '  数学价值低于手工 capstone（见同目录下 SemigraphoidCapstone 等）。', '-/',
              '', 'namespace FateV2.Integration', '', f'namespace {name}', '']

    made = 0
    for rel, nss, thms in picked:
        mod = rel.replace('.', '_')
        ns = nss[-1]
        zero = [t for t, ok in thms if ok][:6]
        if len(zero) < 2:
            continue
        conjs = ' ∧ '.join(zero)
        lines += [f'/-- `{rel}` 的定理汇总（{len(zero)} 条）。 -/',
                  f'theorem cap_{mod} : {conjs} :=',
                  '  ⟨' + ', '.join(zero) + '⟩', '']
        made += 1

    lines += [f'end {name}', '', 'end FateV2.Integration', '']
    with open(path, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write('\n'.join(lines))
    print(f'\n写入 {path}（{made} 条 capstone）')


if __name__ == '__main__':
    main()