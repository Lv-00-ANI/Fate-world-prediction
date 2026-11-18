#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复「命名空间部分未改写」与「前缀重复堆叠」的文件。

## 两类缺陷

### 1. 部分段落仍是旧命名空间

一个文件里可能有多个 `namespace Fate` 区段（文件被拼接/分段书写），
迁移只改了第一处：

    namespace FateV2.Predict   ← 已改
    ...
    namespace Fate             ← 未改（后续段落）
    namespace DAGFactorization

### 2. 前缀重复堆叠

规则被反复应用导致：

    namespace FateV2.Predict.FateV2.Predict.FateV2.Predict.......R259

实测 `Predict/WiringBackdoor` 有 8 层重复。

## 做法

- `namespace Fate` → `namespace FateV2.<域>`
- `namespace Fate.X` → `namespace FateV2.<域>.X`
- `end` 同步
- 折叠 `FateV2.<域>.` 的重复出现

## 用法

    python _migration/fix_broken_ns.py --fix
"""
import os, re, sys, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')


def fix_file(path, domain):
    with open(path, encoding='utf-8') as fh:
        text = fh.read()
    orig = text

    # 1. 折叠重复的 `FateV2.<域>.` 前缀
    pat = re.compile(rf'FateV2\.{re.escape(domain)}\.' + r'(?:' + rf'FateV2\.{re.escape(domain)}\.)+')
    text = pat.sub(f'FateV2.{domain}.', text)

    # 2. `namespace Fate` / `end Fate`
    text = re.sub(r'(?m)^namespace Fate\s*$', f'namespace FateV2.{domain}', text)
    text = re.sub(r'(?m)^end Fate\s*$', f'end FateV2.{domain}', text)

    # 3. `namespace Fate.X` / `end Fate.X`
    text = re.sub(r'(?m)^namespace Fate\.', f'namespace FateV2.{domain}.', text)
    text = re.sub(r'(?m)^end Fate\.', f'end FateV2.{domain}.', text)

    # 4. 正文里的全限定引用 Fate.X → FateV2.<域>.X（仅当不在注释）
    def repl(m):
        return f'FateV2.{domain}.' + m.group(1)
    text = re.sub(r'(?<![\w.`])Fate\.([A-Za-z_]\w*)', repl, text)

    if text == orig:
        return False
    with open(path, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(text)
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fix', action='store_true')
    a = ap.parse_args()

    targets = []
    for dp, _, fs in os.walk(V2):
        for fn in fs:
            if not fn.endswith('.lean'):
                continue
            p = os.path.join(dp, fn)
            with open(p, encoding='utf-8') as fh:
                src = fh.read()
            ns = re.findall(r'(?m)^namespace\s+(\S+)', src)
            bad = [n for n in ns if n == 'Fate' or n.startswith('Fate.')]
            dup = re.search(rf'FateV2\.[A-Za-z]+\.(?:FateV2\.[A-Za-z]+\.){{2,}}', src)
            if bad or dup:
                dom = os.path.relpath(p, V2).replace(os.sep, '.').split('.')[0]
                targets.append((p, dom, bad[:2], bool(dup)))

    print(f'待修文件: {len(targets)}')
    for p, dom, bad, dup in targets:
        print(f'  {os.path.relpath(p, V2):<44} 域={dom:<10} '
              f'旧ns={bad} {"+重复前缀" if dup else ""}')

    if not a.fix:
        print('\n加 --fix 执行')
        return

    n = 0
    for p, dom, _, _ in targets:
        if fix_file(p, dom):
            n += 1
    print(f'已修复 {n} 个文件')


if __name__ == '__main__':
    main()
