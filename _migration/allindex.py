#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
全定义索引（含 def）：用于解析正文里的 `Fate.<名字>` 全限定引用。

## 与 typeindex.py 的分工

| 索引 | 收录 | 用途 |
|---|---|---|
| `type_index.json` | 只收 structure/inductive/class（203 项） | 规则 7「补 open 用到的类型所在域」 |
| `all_index.json` | 收全部 def/abbrev/structure/inductive/class | 规则 6「改写正文全限定引用」 |

**为什么分开**：补 open 时若混入 def 会大量误判（实测 LawRule 在 Bridge/Core/Rules
各有一个 def，`Data` 在 Core.Syntax 有 def，都曾导致误 open）。
但**改写全限定引用**时正需要 def——`Fate.Rules` 里的 Rules 就是 Model/Frame 的 def。

## 用法

    python _migration/allindex.py --build
    python _migration/allindex.py --lookup Rules
"""
import os, re, json, argparse
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
CACHE = os.path.join(ROOT, '_migration', 'all_index.json')

ALL_DEF_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:structure|inductive|class|def|abbrev|opaque|instance|theorem|lemma)\s+'
    r'([A-Za-z_][\w\']*)', re.M)
NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end\s+(\S+)\s*$')


def build():
    """名字 → {domain, module, ns}。同名时优先选「定义在非 Core/Bridge」的那份？不——
    优先选第一个遇到的（os.walk 顺序），但记录全部备选，供排查。"""
    idx = {}
    dup = {}

    for dp, _, fs in os.walk(V2):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, V2).replace('\\', '.')[:-5]
            dom = rel.split('.')[0]
            with open(p, encoding='utf-8') as fh:
                src = fh.read()
            stack = []
            for line in src.split('\n'):
                m = NS_RE.match(line)
                if m:
                    stack.append(m.group(1))
                    continue
                if END_RE.match(line) and stack:
                    stack.pop()
                    continue
                m = ALL_DEF_RE.match(line)
                if m:
                    name = m.group(1)
                    rec = {'domain': dom, 'module': rel, 'ns': '.'.join(stack)}
                    if name not in idx:
                        idx[name] = rec
                    else:
                        dup.setdefault(name, [idx[name]]).append(rec)

    with open(CACHE, 'w', encoding='utf-8') as f:
        json.dump(idx, f, ensure_ascii=False, indent=0)

    # 重名报告
    if dup:
        with open(os.path.join(ROOT, '_inventory', '重名定义.csv'),
                  'w', encoding='utf-8-sig', newline='') as f:
            import csv
            w = csv.writer(f)
            w.writerow(['名字', '出现次数', '各处位置（域/模块）'])
            for name, recs in sorted(dup.items(), key=lambda x: -len(x[1])):
                w.writerow([name, len(recs),
                            '; '.join(f'{r["domain"]}/{r["module"]}' for r in recs[:6])])

    return idx, dup


def load():
    if os.path.exists(CACHE):
        with open(CACHE, encoding='utf-8') as f:
            return json.load(f)
    return build()[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--build', action='store_true')
    ap.add_argument('--lookup')
    a = ap.parse_args()

    if a.build:
        idx, dup = build()
        print(f'索引完成：{len(idx)} 个定义（含 def/theorem）')
        for d, n in Counter(v['domain'] for v in idx.values()).most_common():
            print(f'  {d:<12} {n}')
        print(f'\n重名定义: {len(dup)} 组 → _inventory/重名定义.csv')
        return

    idx = load()
    if a.lookup:
        v = idx.get(a.lookup)
        print(json.dumps(v, ensure_ascii=False, indent=1) if v else f'{a.lookup}: 未找到')
        return

    print(f'已索引 {len(idx)} 个定义。用 --lookup <名字> 查询。')


if __name__ == '__main__':
    main()
