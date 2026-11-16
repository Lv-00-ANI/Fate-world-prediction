#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量迁移（先全写再统一验证）。

## 为什么批量

单模块迁移 + 立即验证的代价：
- 每个模块的 `lake build <单模块>` 要编它自己的依赖链（5–20 分钟）
- 每轮再跑一次全库验证（约 19 分钟）

攒一批一起验证，构建只做一次，且失败时能一次性看到所有问题模块。

## 代价

失败定位要逐个文件看。所以本脚本会：
1. 一次性写出 N 个模块（不做 per-module 编译）
2. 跑一次全库 build
3. 从输出里解析出失败模块，逐个删除并报告

## 用法

    python _migration/batch_all.py --plan 6        # 只列计划
    python _migration/batch_all.py --run 6         # 迁 6 个并验证
    python _migration/batch_all.py --run 6 --domain Predict
"""
import os, re, sys, json, argparse, subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import port_v2

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')

# 人工判定的域分配（按依赖+职责，不按文件名）
DOMAIN_HINT = {
    # —— Predict（因果推断 / d-分离 / 干预 / 可辨识性）——
    'GraphToProbView17': 'Predict', 'View17': 'Predict',
    'CausalClassificationBridge': 'Predict', 'DAGBridge': 'Predict',
    'PearlLawRuleBridge': 'Predict', 'T1DegeneracyVerify': 'Predict',
    'KK1NoiseAsymmetry': 'Predict', 'CausalPath': 'Predict',
    'CausalDescendant': 'Predict',
    # —— Loop（闭环 / 收敛 / 世界模型）——
    'DemoEndToEnd': 'Loop', 'WorldModelPipeline': 'Loop',
    'ConvergeToOptimalCounterexample': 'Loop', 'SharedThetaChain': 'Loop',
    'SharedParamGain': 'Loop',
    # —— Error（误差界 / σ）——
    'FirstLayerBound': 'Error', 'LoopBoundReal': 'Error',
    # —— Rules（规则 / 语法）——
    'RuleSyntax': 'Rules',
    # —— Modeling（建模）——
    'T43CounterfactualAbduction': 'Modeling',
}


def candidates():
    v2m = port_v2.v2_index()
    rows = []
    for dp, _, fs in os.walk(port_v2.LEGACY):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            n = f[:-5]
            if n in v2m:
                continue
            info = port_v2.analyze(n)
            if info and not info['unresolved'] and not info['blocked'] and info['theorems'] > 0:
                rows.append(info)
    rows.sort(key=lambda r: -r['theorems'])
    return rows


def guess_domain(name):
    if name in DOMAIN_HINT:
        return DOMAIN_HINT[name]
    return 'Predict'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--plan', type=int, default=0)
    ap.add_argument('--run', type=int, default=0)
    ap.add_argument('--domain')
    a = ap.parse_args()

    rows = candidates()
    n = a.run or a.plan
    if not n:
        print(f'候选 {len(rows)} 个')
        return

    picked = rows[:n]
    plan = [(r['name'], a.domain or guess_domain(r['name'])) for r in picked]

    print(f'计划迁移 {len(plan)} 个：')
    for name, dom in plan:
        thm = next(r['theorems'] for r in picked if r['name'] == name)
        print(f'  {name:<32} → {dom:<10} {thm:>3} 定理')

    if not a.run:
        return

    print('\n=== 写入 ===')
    written = []
    for name, dom in plan:
        r = port_v2.port_one(name, dom, verify=False)
        if r.get('ok'):
            written.append((name, dom, r['dst']))
            print(f'  [写] {name:<32} → {dom}')
        else:
            print(f'  [跳过] {name}: {r.get("why")}')

    if not written:
        return

    print(f'\n=== 统一验证（{len(written)} 个）===')
    proc = subprocess.run(['lake', 'build', 'FateWorld'], cwd=ROOT,
                          capture_output=True, text=True,
                          encoding='utf-8', errors='replace', timeout=7200)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0

    # 解析失败模块（形如 error: FateWorld/FateV2/<域>/<模块>.lean:行:列:）
    bad = set()
    for m in re.finditer(r'error: FateWorld/(FateV2/[^\s:]+\.lean)', out):
        bad.add(m.group(1).replace('/', os.sep))

    print(f'1) 构建结果: {"成功" if ok else "失败"}')
    if bad:
        print(f'2) 失败文件 {len(bad)} 个:')
        for b in sorted(bad):
            print(f'   {b}')
        # 回滚失败的那些
        for name, dom, dst in written:
            rel = dst[len(ROOT) + 1:]
            if rel in bad:
                os.remove(dst)
                print(f'   [回滚] {name}')
    else:
        print('2) 无失败文件')

    survivors = [w for w in written
                 if os.path.exists(w[2])]
    print(f'\n净成功 {len(survivors)} / {len(written)}')


if __name__ == '__main__':
    main()
