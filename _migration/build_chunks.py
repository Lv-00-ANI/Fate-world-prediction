#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
分块批量构建：把所有缺 .olean 的模块按块传给**一次** lake 调用。

## 为什么比逐模块快

逐模块 `lake build X` 每次都要重新分析全部依赖（约 2 分钟开销）。
`lake build X1 X2 ... X100` 只需分析一次，且 lake 内部并行调度依赖。

## 输出

逐块运行，实时打印失败模块，写入 `_inventory/批量构建失败.txt`
"""
import os, re, sys, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OLEAN = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean', 'FateWorld', 'FateV2')
LOG = os.path.join(ROOT, '_inventory', '批量构建失败.txt')
CHUNK = 20


def missing():
    out = []
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            rel = os.path.relpath(os.path.join(dp, f), V2).replace(os.sep, '.')[:-5]
            if not os.path.exists(os.path.join(OLEAN, rel.replace('.', os.sep) + '.olean')):
                out.append('FateWorld.FateV2.' + rel)
    out.sort()
    return out


def main():
    todo = missing()
    print(f'缺 olean: {len(todo)}', flush=True)
    fails = []

    for i in range(0, len(todo), CHUNK):
        chunk = todo[i:i + CHUNK]
        print(f'\n=== 块 {i // CHUNK + 1} ({i + 1}–{i + len(chunk)}) ===', flush=True)
        try:
            r = subprocess.run(['lake', 'build'] + chunk, cwd=ROOT,
                               capture_output=True, text=True,
                               encoding='utf-8', errors='replace', timeout=14400)
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            print('  TIMEOUT', flush=True)
            fails.extend(chunk)
            continue

        # 解析失败模块：`- FateWorld.FateV2.X.Y` 出现在 "logged failures" 之后
        bad = set(re.findall(r'^-\s+(FateWorld\.FateV2\.\S+)$', out, re.M))
        # 也解析 error: 行里的文件路径
        for m in re.finditer(r'error: FateWorld/FateV2/([^\s:]+)\.lean', out):
            bad.add('FateWorld.FateV2.' + m.group(1).replace('/', '.'))

        # ⚠ lake 的 "logged failures" 会包含「因依赖失败而跳过」的目标，
        # 直接采信会误报。以 **.olean 是否存在** 为准，才是真实成败。
        real_bad = []
        for m in chunk:
            rel = m[len('FateWorld.FateV2.'):].replace('.', os.sep)
            if not os.path.exists(os.path.join(OLEAN, rel + '.olean')):
                real_bad.append(m)
        ok = len(chunk) - len(real_bad)
        print(f'  成功 {ok} / {len(chunk)}', flush=True)
        if real_bad:
            for b in real_bad:
                print(f'  ❌ {b}', flush=True)
            fails.extend(real_bad)

    os.makedirs(os.path.dirname(LOG), exist_ok=True)
    with open(LOG, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(fails) + '\n')
    print(f'\n总失败 {len(fails)}，写入 {LOG}')


if __name__ == '__main__':
    main()
