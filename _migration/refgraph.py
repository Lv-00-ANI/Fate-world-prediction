#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
证明链引用图分析。

## 为什么需要

迁移完成只意味着「975 个模块能编译」，不等于「这些证明可用」。
一个模块可能：
  - 被下游 import 了，但其中定理从未在证明体里被调用（假接线）
  - 完全孤立（没有任何模块 import 它）

目标要求「把东西整合到证明链上、把这些证明实际可用」，
第一步是**量化当前的真实使用情况**。

## 判据（刻意保守）

- **真消费**：别的模块的**代码**（非注释）里出现该模块定义的定理/定义名
- **假接线**：被 import，但没有任何名字被实际引用
- **孤立**：没有任何模块 import 它

只有 import 关系是不够的 —— Lean 里 import 一个模块不会自动使用它。

## 用法

    python _migration/refgraph.py                 # 输出报告
    python _migration/refgraph.py --csv           # 同时写 _inventory/引用图.csv
"""
import os, re, csv, json, argparse
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
OUT = os.path.join(ROOT, '_inventory', '引用图.csv')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
DECL_RE = re.compile(
    r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|inductive|class|opaque)\s+([A-Za-z_]\w*)')
IMPORT_RE = re.compile(r'^\s*(?:(?:module|public|private|meta)\s+)*import\s+FateWorld\.FateV2\.(\S+)')


def strip_comments(src):
    src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
    src = re.sub(r'--[^\n]*', ' ', src)
    return src


def scan():
    """返回 modules: {rel: {'decls': set, 'imports': set, 'code': str}}"""
    modules = {}
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, V2).replace(os.sep, '.')[:-5]
            src = open(p, encoding='utf-8').read()
            imports = set(m.group(1).replace('/', '.') for m in IMPORT_RE.finditer(src))
            code = strip_comments(src)
            decls = set(DECL_RE.findall(src))
            # 代码里出现的所有标识符（剔除 import 行）
            body = re.sub(r'(?m)^\s*(?:(?:module|public|private|meta)\s+)*import\s+\S+', ' ', code)
            modules[rel] = {'decls': decls, 'imports': imports, 'body': body}
    return modules


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--csv', action='store_true')
    a = ap.parse_args()

    modules = scan()
    # 名字 → 定义它的模块
    owner = {}
    for rel, m in modules.items():
        for d in m['decls']:
            owner.setdefault(d, set()).add(rel)

    rows = []
    for rel, m in modules.items():
        # 谁 import 了我
        imported_by = {r for r, mm in modules.items() if rel in mm['imports']}
        # 谁**真消费**了我：import 了我，且其代码里出现我的某个定义名
        consumed_by = set()
        for other in imported_by:
            body = modules[other]['body']
            own = modules[other]['decls']
            for d in m['decls']:
                if d in own:
                    continue
                if re.search(r'(?<![\w.])' + re.escape(d) + r'(?![\w])', body):
                    consumed_by.add(other)
                    break

        if not imported_by:
            status = '孤立'
        elif not consumed_by:
            status = '假接线'
        else:
            status = '真消费'
        rows.append({
            '模块': rel,
            '域': rel.split('.')[0],
            '定义数': len(m['decls']),
            '被import': len(imported_by),
            '被真消费': len(consumed_by),
            '状态': status,
        })

    total = len(rows)
    cnt = defaultdict(int)
    for r in rows:
        cnt[r['状态']] += 1
    print(f'模块总数 {total}')
    for k in ('真消费', '假接线', '孤立'):
        print(f'  {k}: {cnt[k]}  ({cnt[k]*100//total}%)')
    print()
    print('按域：')
    for dom in sorted({r['域'] for r in rows}):
        sub = [r for r in rows if r['域'] == dom]
        c = defaultdict(int)
        for r in sub:
            c[r['状态']] += 1
        print(f'  {dom:<12} 共{len(sub):>3}  真消费{c["真消费"]:>3}  '
              f'假接线{c["假接线"]:>3}  孤立{c["孤立"]:>3}')

    if a.csv:
        os.makedirs(os.path.dirname(OUT), exist_ok=True)
        with open(OUT, 'w', encoding='utf-8-sig', newline='') as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f'\n写入 {OUT}')


if __name__ == '__main__':
    main()