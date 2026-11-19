#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
按编译器报告移除失效的 `open`。

## 为什么必须这样做，而不是全局扫描

全局扫描「open 了未直接导入的域」是错误的判据：
大量 `open` 依赖**传递导入**（A 导入 B，B 导入 C，
在 A 里 `open C` 完全合法）。实测该判据命中 419 个文件 / 653 处，
绝大多数是误伤。

正确做法：**让编译器告诉我们**。只有编译器报
    error: unknown namespace `FateV2.X`
时，才说明该命名空间在作用域内根本不存在，此时移除对应的
`open FateV2.X` 是安全的（不可能影响传递导入，因为连命名空间都不存在）。

## 用法

    python _migration/fix_unknown_ns.py Rules               # 逐模块编译并修复
    python _migration/fix_unknown_ns.py Rules --dry-run
"""
import os, re, sys, subprocess, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OLEAN = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean', 'FateWorld', 'FateV2')

ERR_FMT = re.compile(r'error: FateWorld/FateV2/([^\s:]+)\.lean:\d+:\d+: unknown namespace `([^`]+)`')


def build(mod):
    return subprocess.run(['lake', 'build', mod], cwd=ROOT,
                          capture_output=True, text=True,
                          encoding='utf-8', errors='replace', timeout=7200)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('domain')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()

    d = os.path.join(V2, a.domain)
    todo = []
    for f in sorted(os.listdir(d)):
        if not f.endswith('.lean'):
            continue
        rel = f[:-5]
        if not os.path.exists(os.path.join(OLEAN, a.domain, rel + '.olean')):
            todo.append(rel)

    print(f'{a.domain}: {len(todo)} 个待验证', flush=True)
    fixed = 0
    for rel in todo:
        mod = f'FateWorld.FateV2.{a.domain}.{rel}'
        r = build(mod)
        if r.returncode == 0:
            continue
        out = r.stdout + r.stderr
        hits = set(ERR_FMT.findall(out))
        targets = {(p, ns) for p, ns in hits}
        if not targets:
            continue
        print(f'  {rel}: {sorted(ns for _, ns in targets)}', flush=True)
        if a.dry_run:
            continue
        p = os.path.join(d, rel + '.lean')
        with open(p, encoding='utf-8') as fh:
            text = fh.read()
        changed = False
        for _, ns in targets:
            pat = re.compile(r'(?m)^open\s+(.*\b' + re.escape(ns) + r'\b.*)$')
            def rep(m):
                toks = [t for t in m.group(1).split() if t != ns]
                return ('open ' + ' '.join(toks)) if toks else ''
            new, n = pat.subn(rep, text)
            if n:
                text = new
                changed = True
        if changed:
            with open(p, 'w', encoding='utf-8', newline='\n') as fh:
                fh.write(text)
            fixed += 1
            r2 = build(mod)
            print(f'    → {"OK" if r2.returncode == 0 else "仍有错误"}', flush=True)

    print(f'\n修复 {fixed} 个文件')


if __name__ == '__main__':
    main()
