#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量集成生成器 v2：为假接线模块生成「定理汇总」capstone（带完整命名空间）。

## 与 v1 的差别

v1 只记裸定理名，生成后大量 Application type mismatch ——
因为定理都在各自命名空间里，裸名解析不到（autoImplicit 又把它当变量）。

v2 记录**每条定理所在的完整命名空间**，生成时用全限定名。

## 用法

    python _migration/gen_capstone2.py Error --max 6
    python _migration/gen_capstone2.py Error --dry-run
"""
import os, re, json, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
IDX = os.path.join(ROOT, '_migration', 'name_index.json')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
THM_RE = re.compile(r'^\s*(?:private\s+)?theorem\s+([A-Za-z_]\w*)\s*:\s*$')
THM_B_RE = re.compile(r'^\s*(?:private\s+)?theorem\s+([A-Za-z_]\w*)\s*:\s*\S')


def scan(path):
    """返回 [(完整命名空间, 定理名, 是否无参)]"""
    out = []
    stack = []
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            m = NS_RE.match(line)
            if m:
                stack.append(m.group(1))
                continue
            if END_RE.match(line) and stack:
                stack.pop()
                continue
            nm = None
            noarg = False
            if THM_RE.match(line):
                nm = THM_RE.match(line).group(1)
                noarg = True
            elif THM_B_RE.match(line):
                nm = THM_B_RE.match(line).group(1)
                noarg = False
            if nm:
                out.append(('.'.join(stack), nm, noarg))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('domain')
    ap.add_argument('--max', type=int, default=6)
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()

    d = os.path.join(V2, a.domain)
    cands = []
    for f in sorted(os.listdir(d)):
        if not f.endswith('.lean'):
            continue
        rel = f'{a.domain}.{f[:-5]}'
        thms = [t for t in scan(os.path.join(d, f)) if t[2]]  # 只取无参定理
        if len(thms) >= 2:
            cands.append((rel, thms))

    print(f'{a.domain}: {len(cands)} 个候选（含 >=2 条无参定理）')
    picked = cands[:a.max]
    for rel, thms in picked:
        print(f'  {rel:<44} 无参定理 {len(thms):>2}  ns={thms[0][0]}')
    if a.dry_run:
        return

    name = f'{a.domain}AutoCapstone'
    path = os.path.join(V2, 'Integration', name + '.lean')
    os.makedirs(os.path.dirname(path), exist_ok=True)

    lines = [f'import FateWorld.FateV2.{rel}' for rel, _ in picked]
    lines += ['', '/-!',
              f'  # Integration · {a.domain} · 自动汇总（全限定版）', '',
              '  由 `_migration/gen_capstone2.py` 生成。', '',
              '  **性质说明**：这些是「定理汇总」而非人工组合 —— 每条把源模块的',
              '  无参定理并成一个合取，目的是给出引用入口并筛出无法重述的模块。',
              '  数学价值低于手工 capstone。',
              '-/', '', 'namespace FateV2.Integration', '', f'namespace {name}', '']

    made = 0
    for rel, thms in picked:
        tag = rel.replace('.', '_')
        names = [f'{ns}.{nm}' if ns else nm for ns, nm, _ in thms[:6]]
        lines += [f'/-- `{rel}` 的定理汇总（{len(names)} 条）。 -/',
                  f'theorem cap_{tag} :', '    ' + ' ∧ '.join(names) + ' :=',
                  '  ⟨' + ', '.join(names) + '⟩', '']
        made += 1

    lines += [f'end {name}', '', 'end FateV2.Integration', '']
    with open(path, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write('\n'.join(lines))
    print(f'\n写入 {path}（{made} 条）')


if __name__ == '__main__':
    main()