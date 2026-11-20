#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
全库「名字 → 命名空间」索引。

## 为什么需要

迁移后同一个**裸前缀**常常对应多个同名命名空间，例如：

    FateV2.Rules.AlphaMVFCA      ← rulesLocal / minClosedFinset / ...
    FateV2.Predict.AlphaMVFCA    ← minClosed / closedPartition / ...

源码里写 `AlphaMVFCA.minClosed` 时，光看前缀无法判断归属。
我在 Rules 域最后 3 个模块上为此反复试错 11 轮。

正确流程是**先建索引，再按名字修正**，而不是按前缀批量替换。

## 用法

    # 建索引（写入 _inventory/名字索引.csv）
    python _migration/name_index.py --build

    # 查单个名字
    python _migration/name_index.py --query minClosed

    # 查某个文件里所有「裸前缀」引用，报告每个名字的真实归属
    python _migration/name_index.py --file FateWorld/FateV2/Rules/MVFCAFinset.lean
"""
import os, re, sys, csv, argparse, json
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
CACHE = os.path.join(ROOT, '_migration', 'name_index.json')
CSV_OUT = os.path.join(ROOT, '_inventory', '名字索引.csv')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
DECL_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+([A-Za-z_]\w*)')


def build():
    """返回 {名字: [命名空间, ...]} 与 {名字: 定义文件}"""
    idx = defaultdict(set)
    where = {}
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, V2).replace(os.sep, '.')[:-5]
            stack = []
            with open(p, encoding='utf-8') as fh:
                for line in fh:
                    m = NS_RE.match(line)
                    if m:
                        stack.append(m.group(1))
                        continue
                    if END_RE.match(line) and stack:
                        stack.pop()
                        continue
                    m = DECL_RE.match(line)
                    if m:
                        nm = m.group(1)
                        ns = '.'.join(stack)
                        idx[nm].add(ns or '(root)')
                        where.setdefault(nm, rel)
    out = {k: sorted(v) for k, v in idx.items()}
    with open(CACHE, 'w', encoding='utf-8') as fh:
        json.dump({'defs': out, 'file': where}, fh, ensure_ascii=False)
    os.makedirs(os.path.dirname(CSV_OUT), exist_ok=True)
    with open(CSV_OUT, 'w', encoding='utf-8-sig', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['名字', '命名空间', '定义文件'])
        for k in sorted(out):
            w.writerow([k, ' | '.join(out[k]), where.get(k, '')])
    amb = {k: v for k, v in out.items() if len(v) > 1}
    print(f'索引 {len(out)} 个名字，其中 {len(amb)} 个有歧义（多处定义）')
    print(f'写入 {CSV_OUT}')
    return out, where


def load():
    if not os.path.exists(CACHE):
        return build()
    with open(CACHE, encoding='utf-8') as fh:
        d = json.load(fh)
    return d['defs'], d['file']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--build', action='store_true')
    ap.add_argument('--query')
    ap.add_argument('--file')
    a = ap.parse_args()

    defs, where = load() if not a.build else build()

    if a.query:
        print(f'{a.query}:')
        for ns in defs.get(a.query, ['(未找到)']):
            print(f'  {ns}.{a.query}     [{where.get(a.query, "?")}]')
        return

    if a.file:
        p = a.file if os.path.isabs(a.file) else os.path.join(ROOT, a.file)
        with open(p, encoding='utf-8') as fh:
            src = fh.read()
        code = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
        code = re.sub(r'--[^\n]*', ' ', code)
        # 找 `Prefix.name` 形式的引用，且 Prefix 是某个命名空间末段
        lastseg = defaultdict(set)
        for ns in {n for v in defs.values() for n in v}:
            lastseg[ns.split('.')[-1]].add(ns)
        seen = set()
        for m in re.finditer(r'(?<![\w.])([A-Za-z_]\w*)\.([A-Za-z_]\w*)', code):
            pfx, nm = m.group(1), m.group(2)
            if (pfx, nm) in seen or nm not in defs:
                continue
            seen.add((pfx, nm))
            real = defs[nm]
            flag = 'OK' if any(r.endswith('.' + pfx) or r == pfx for r in real) else 'CHECK'
            if flag == 'CHECK':
                print(f'  [{flag}] {pfx}.{nm}  →  实际在: {real}')
        return

    print(f'索引已就绪：{len(defs)} 个名字')
    print('用 --query <名字> 或 --file <文件> 查询')


if __name__ == '__main__':
    main()
