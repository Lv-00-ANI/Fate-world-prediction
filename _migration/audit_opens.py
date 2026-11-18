#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
静态审计：找出「跨域引用但没 open 对应域」的模块。

## 为什么需要

逐模块编译验证每个要等依赖链（5–20 分钟），622 个模块不现实。
但失败原因高度集中：**Legacy 时代所有模块在同一个 `namespace Fate` 下，
分域后在 FateV2 里跨域引用必须有 `open FateV2.<域>`**。

这类问题可以**静态**发现：扫正文用到的标识符，查类型索引，
若定义在别的域而该域未被 open，就是可疑点。

## 用法

    python _migration/audit_opens.py            # 输出可疑清单
    python _migration/audit_opens.py --fix      # 自动补 open
"""
import os, re, sys, json, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
TIDX = os.path.join(ROOT, '_migration', 'type_index.json')
OUT = os.path.join(ROOT, '_inventory', '缺open审计.csv')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)')
END_RE = re.compile(r'^\s*end\s+(\S+)\s*$')
OPEN_RE = re.compile(r'^\s*open\s+(.+)$', re.M)
IMPORT_RE = re.compile(r'^\s*(?:(?:module|public|private|meta)\s+)*import\s+(FateWorld\.\S+)', re.M)

LEAN_NS = {
    'Classical', 'Data', 'Set', 'Filter', 'Finset', 'Nat', 'Int', 'Real', 'List',
    'Option', 'Function', 'Monoid', 'Group', 'Order', 'MeasureTheory', 'Topology',
    'ProbabilityTheory', 'ENNReal', 'NNReal', 'Matrix', 'Polynomial', 'Complex',
    'CategoryTheory', 'Equiv', 'Submodule', 'Bornology', 'MeasurableSpace',
    'TopologicalSpace', 'ContinuousLinearMap', 'InnerProductSpace', 'Module',
    'Algebra', 'Ring', 'Field', 'Interval', 'Metric', 'Ball', 'Rat', 'Bool',
    'Multiset', 'MvPolynomial', 'BigOperators', 'Relation', 'Ideal', 'Subgroup',
}


def self_domain(path):
    """取文件最外层 FateV2.<域>"""
    stack = []
    with open(path, encoding='utf-8') as f:
        for line in f:
            m = NS_RE.match(line)
            if m:
                stack.append(m.group(1))
                full = '.'.join(stack)
                if full.startswith('FateV2.') and full.count('.') == 1:
                    return full.split('.')[1]
                continue
            if END_RE.match(line) and stack:
                stack.pop()
    return None


def opened_domains(text):
    """本文件 open 了哪些 FateV2.<域>（含裸 open 的兄弟命名空间不算）"""
    out = set()
    for m in OPEN_RE.finditer(text):
        for tok in m.group(1).split():
            if tok.startswith('FateV2.'):
                parts = tok.split('.')
                if len(parts) >= 2:
                    out.add(parts[1])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fix', action='store_true')
    a = ap.parse_args()

    # ⚠ 不能用 type_index.json 直接判定归属：它是「先到先得」，
    # 同名标识符（如 `Model` 在 Modeling.SCM / Predict.Counterfactual /
    # Demo.ExecutableSCM 各有定义）只会保留第一个。
    # 直接按索引报警会产生大量假阳性（实测 123 条里绝大部分是 `Model`）。
    #
    # 正确做法：扫描全部定义，建立 name → {domains}；
    # **只对全局唯一定义的名字**报警。
    multi = {}
    for dp, _, fs in os.walk(V2):
        for fn in fs:
            if not fn.endswith('.lean'):
                continue
            p2 = os.path.join(dp, fn)
            rel2 = os.path.relpath(p2, V2).replace(os.sep, '.')[:-5]
            d2 = rel2.split('.')[0]
            with open(p2, encoding='utf-8') as fh2:
                src2 = fh2.read()
            for nm in re.findall(
                    r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                    r'(?:structure|inductive|class)\s+([A-Za-z_]\w*)', src2):
                multi.setdefault(nm, set()).add(d2)
    uniq = {nm: next(iter(ds)) for nm, ds in multi.items() if len(ds) == 1}
    tidx = {nm: {'domain': d} for nm, d in uniq.items()}

    rows = []
    for dp, _, fs in os.walk(V2):
        for fn in fs:
            if not fn.endswith('.lean'):
                continue
            p = os.path.join(dp, fn)
            rel = os.path.relpath(p, V2).replace(os.sep, '.')[:-5]
            dom = rel.split('.')[0]
            with open(p, encoding='utf-8') as f:
                text = f.read()

            # 剥掉注释与 import
            code = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
            code = re.sub(r'--[^\n]*', ' ', code)
            code = re.sub(r'"(?:[^"\\]|\\.)*"', ' ', code)
            code = re.sub(r'(?m)^\s*(?:(?:module|public|private|meta)\s+)*import\s+\S+', ' ', code)

            own_defs = set(re.findall(
                r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                r'(?:structure|inductive|class|def|abbrev|opaque)\s+([A-Za-z_]\w*)', text))

            used = set(re.findall(r'(?<![\w.\'])([A-Z][A-Za-z0-9_]{2,})', code))
            opened = opened_domains(text)

            need = set()
            for ident in used - own_defs - LEAN_NS:
                rec = tidx.get(ident)
                if not rec:
                    continue
                d = rec['domain']
                if d != dom and d not in opened:
                    need.add(d)

            if need:
                rows.append({'模块': rel, '域': dom, '缺open': ','.join(sorted(need))})

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    import csv
    with open(OUT, 'w', encoding='utf-8-sig', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=['模块', '域', '缺open'])
        w.writeheader()
        w.writerows(rows)

    print(f'可疑模块（跨域引用但未 open）: {len(rows)}')
    for r in rows[:20]:
        print(f'  {r["模块"]:<44} 缺 open FateV2.{r["缺open"]}')

    if not a.fix:
        print(f'\n明细写入 {OUT}')
        print('加 --fix 可自动补 open')
        return

    fixed = 0
    for r in rows:
        p = os.path.join(V2, r['模块'].replace('.', os.sep) + '.lean')
        with open(p, encoding='utf-8') as fh:
            text = fh.read()
        dom = r['域']
        adds = '\n'.join(f'open FateV2.{d}' for d in r['缺open'].split(','))
        # 插在第一个 namespace FateV2.<域> 之后
        new, n = re.subn(rf'(?m)^(namespace FateV2\.{re.escape(dom)})$',
                         lambda m: m.group(1) + '\n\n' + adds, text, count=1)
        if n:
            with open(p, 'w', encoding='utf-8', newline='\n') as fh:
                fh.write(new)
            fixed += 1
    print(f'已补 open: {fixed} 个文件')


if __name__ == '__main__':
    main()
