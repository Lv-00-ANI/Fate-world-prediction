#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
类型/定义定位器：给定一个标识符，找出它在 FateV2 里定义在哪个域。

## 为什么需要

Legacy 模块大量依赖 `namespace Fate` 的**扁平可见性**：写 `StateSpace`、
`CtxSpace`，靠的是它们在同一个 `Fate` 前缀下。

迁移后这些名字散落到 `FateV2.Modeling` / `FateV2.Model` 等不同域，
**即使没有直接 import 那个模块**（间接 import 也能拿到名字），
也必须显式 open 对应域，否则报：

    Invalid field notation: Field projection operates on types of the form `C ...`

实测反例：`RuleLevel` 用 `CtxSpace`（Model 域）+ `StateSpace`（Modeling 域），
但它只 import 了同域的 `LawRule`，规则 4/5 都覆盖不到。

## 索引构建

扫描 FateV2 全部 `.lean`，记录：
    <顶层标识符> → (所在域, 定义它的模块, 它在该模块里的完整命名空间)

只索引 `structure` / `inductive` / `def` / `abbrev` / `class` 的顶层名字。

## 用法

    python _migration/typeindex.py --build
    python _migration/typeindex.py --lookup StateSpace
"""
import os, re, json, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
CACHE = os.path.join(ROOT, '_migration', 'type_index.json')

DEF_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|protected\s+)*'
    r'(?:structure|inductive|class|def|abbrev|opaque)\s+([A-Za-z_][\w\']*)', re.M)
# 只对「类型定义」建索引：structure / inductive / class。
# 理由：`def` 极易重名（实测 LawRule 在 Bridge/Core/Rules 各有一个 def），
# 而补 open 的目的是让**类型名**解析得到。混入 def 会引入大量误判。
TYPE_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:structure|inductive|class)\s+([A-Za-z_][\w\']*)', re.M)
NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end\s+(\S+)\s*$')


def scan_file(path, rel):
    """返回 [(类型名, 该名字所在的完整命名空间)]；只收 structure/inductive/class。"""
    with open(path, encoding='utf-8') as f:
        src = f.read()
    stack = []
    out = []
    for line in src.split('\n'):
        m = NS_RE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        if END_RE.match(line) and stack:
            stack.pop()
            continue
        m = TYPE_RE.match(line)
        if m:
            out.append((m.group(1), '.'.join(stack)))
    return out


def build():
    idx = {}
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, V2).replace('\\', '.')[:-5]
            dom = rel.split('.')[0]
            for name, ns in scan_file(p, rel):
                if name not in idx:
                    idx[name] = {'domain': dom, 'module': rel, 'ns': ns}
    with open(CACHE, 'w', encoding='utf-8') as f:
        json.dump(idx, f, ensure_ascii=False, indent=0)
    return idx


def load():
    if os.path.exists(CACHE):
        with open(CACHE, encoding='utf-8') as f:
            return json.load(f)
    return build()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--build', action='store_true')
    ap.add_argument('--lookup')
    a = ap.parse_args()

    if a.build:
        idx = build()
        from collections import Counter
        c = Counter(v['domain'] for v in idx.values())
        print(f'索引完成：{len(idx)} 个定义')
        for d, n in c.most_common():
            print(f'  {d:<12} {n}')
        return

    idx = load()
    if a.lookup:
        v = idx.get(a.lookup)
        print(json.dumps(v, ensure_ascii=False, indent=1) if v else f'{a.lookup}: 未找到')
        return

    print(f'已索引 {len(idx)} 个定义。用 --lookup <名字> 查询。')


if __name__ == '__main__':
    main()
