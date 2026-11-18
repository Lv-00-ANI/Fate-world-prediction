#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
逐模块验证器：绕过 lake 的 trace 缓存，得到**真实**的编译状态。

## 为什么不能用 lake build FateWorld

`lake build FateWorld` 依据 lake 的 trace 数据库判断「已构建」，
**不检查 .olean 产物是否存在**。

实测教训：`.olean` 被清理后，`lake build FateWorld` 仍报
`[3113/3118] Replayed ...`（全部来自缓存），而实际上 622 个模块
根本没有 olean。于是「构建成功」是假的。

逐模块 `lake build FateWorld.FateV2.<域>.<模块>` 会强制检查依赖
与实际产物，才能得到真实结果。

## 输出

`_inventory/编译状态.csv`：每行 模块 / 域 / 状态 / 错误摘要

## 用法

    python _migration/verify.py                 # 验证全部未通过模块
    python _migration/verify.py --all           # 强制全部重验
    python _migration/verify.py --domain Error  # 只验一个域
    python _migration/verify.py --limit 20      # 只验前 20 个（试跑）
"""
import os, re, sys, csv, argparse, subprocess
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OLEAN = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean', 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '编译状态.csv')


def modules(domain=None):
    out = []
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            rel = os.path.relpath(os.path.join(dp, f), V2).replace(os.sep, '.')[:-5]
            dom = rel.split('.')[0]
            if domain and dom != domain:
                continue
            out.append((f'FateWorld.FateV2.{rel}', rel, dom))
    out.sort()
    return out


def has_olean(rel):
    return os.path.exists(os.path.join(OLEAN, rel.replace('.', os.sep) + '.olean'))


def build(mod):
    """返回 (ok, err_summary)。"""
    try:
        r = subprocess.run(['lake', 'build', mod], cwd=ROOT,
                           capture_output=True, text=True,
                           encoding='utf-8', errors='replace', timeout=3600)
        if r.returncode == 0:
            return True, ''
        lines = [l for l in (r.stdout + r.stderr).splitlines()
                 if l.startswith('error:') and 'Lean exited' not in l]
        return False, ' | '.join(lines[:2])[:300]
    except subprocess.TimeoutExpired:
        return False, 'TIMEOUT'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--all', action='store_true')
    ap.add_argument('--domain')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--jobs', type=int, default=1,
                    help='并发数（默认 1：lake 并发会撞 .olean 锁）')
    a = ap.parse_args()

    todo = [(m, rel, d) for m, rel, d in modules(a.domain)
            if a.all or not has_olean(rel)]
    if a.limit:
        todo = todo[:a.limit]

    print(f'待验证: {len(todo)} 个模块', flush=True)

    # 增量写盘：每验一个就落盘，进程中断也不丢进度。
    # 已记录的模块默认跳过（可用 --all 重验）。
    done = {}
    if os.path.exists(OUT):
        with open(OUT, encoding='utf-8-sig') as fh:
            for r in csv.DictReader(fh):
                done[r['模块']] = r
    todo = [t for t in todo if t[1] not in done or a.all]

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    fields = ['模块', '域', '状态', '错误']
    fresh = not os.path.exists(OUT) or a.all
    with open(OUT, 'w' if fresh else 'a', encoding='utf-8-sig', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=fields)
        if fresh:
            w.writeheader()
        ok_n = 0
        for i, (mod, rel, dom) in enumerate(todo, 1):
            ok, err = build(mod)
            if ok:
                ok_n += 1
            w.writerow({'模块': rel, '域': dom, '状态': 'OK' if ok else 'FAIL', '错误': err})
            fh.flush()
            mark = 'OK  ' if ok else 'FAIL'
            print(f'[{mark}] {i:>4}/{len(todo)} {rel}' + ('' if ok else f'  {err[:90]}'), flush=True)

    print(f'\n本轮通过 {ok_n} / {len(todo)}')
    print(f'明细写入 {OUT}')


if __name__ == '__main__':
    main()
