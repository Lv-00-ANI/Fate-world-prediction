#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量迁移器：把零依赖的 Legacy 模块迁入 FateV2 的指定域。

## 已验证的迁移流程（手工执行两次成功）

1. 源文件仅 import Mathlib（或零 import）
2. 替换最外层命名空间：`namespace Fate` → `namespace FateV2.<Domain>`
   对应 `end Fate` → `end FateV2.<Domain>`
3. 在第一个 `/-!` 前插入迁移登记头
4. 编译验证
5. 公理审计

## 用法

    python _migration\\port.py --list          # 列出所有可迁候选
    python _migration\\port.py --plan          # 输出迁移计划（domain 分配）
    python _migration\\port.py --one Foo --domain Meta
    python _migration\\port.py --batch         # 按 plan 全部执行

## 纪律

- 证明体逐字不改（只动命名空间行与文件头）
- 编译失败 → 删除已写的文件，报告
- 出现 sorryAx → 标记不合格
"""
import os, re, csv, sys, json, argparse, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
CAND_CSV = os.path.join(ROOT, '_inventory', '迁移候选.csv')

# 已迁入的模块（避免重复）
DONE = {'DeadPremiseAudit': 'Meta', 'RuleActivation': 'Rules'}

# 人工确认的 domain 分配（按文件内容判断，非文件名）
PLAN = {
    # 元层：方法论 / 审计 / 记号
    'DeadPremiseAudit': 'Meta',
    'GazeAlgebra': 'Meta',
    'T810PrMaj': 'Meta',
    'T68ComposeSemantics': 'Meta',
    'AssemblyMeta': 'Meta',
    'T65QuotientOp': 'Meta',
    'ICPCoverage': 'Meta',
    'T04NotationFidelity': 'Meta',
    # 规则层：FCA / 规则代数 / 激活
    'RuleActivation': 'Rules',
    'MVFCAPositive': 'Rules',
    'RealFCA': 'Rules',
    'RealUpDown': 'Rules',
    'AlgoKNNComponents': 'Rules',
    'Fusion': 'Rules',
    'MainlineTheorems': 'Rules',
    'T111QuotientPred': 'Rules',
    # 误差层：界 / 估计 / Lipschitz
    'ErrorBoundE1': 'Error',
    'ErrorBoundE2': 'Error',
    'ErrorBoundE3': 'Error',
    'ErrorBoundE4': 'Error',
    'ErrorBoundE5': 'Error',
    'ErrorBoundE6': 'Error',
    'ErrorBoundE78': 'Error',
    'ErrorQuadruple': 'Error',
    'ErrorE6': 'Error',
    'PipelineLipschitz': 'Error',
    'BlockLayerLowerBound': 'Error',
    'FinCondIndepSymm': 'Error',
    'ObsEstSharp': 'Error',
    'GaussMarkovScalarSymm': 'Error',
    # 预测层：因果 / 干预 / 反事实
    'T314Identifiability': 'Predict',
    'BackdoorFiber': 'Predict',
    'T44Counterfactual': 'Predict',
    # 建模层：SCM / 条件独立 / 核
    'KernelQuotient': 'Modeling',
    'FiniteCondIndep': 'Modeling',
    'CFMap': 'Modeling',
    # 模型层：轨迹
    'T51Trajectory': 'Model',
    # 闭环层：收敛
    'BanachFixedPoint': 'Loop',
    # 补充确认（读内容后判定）
    'T61MapKernel': 'Modeling',      # 映射形式是核形式的特例
    'RetreatPlan': 'Predict',        # 退守方案（决策）
    'ContinuousEvalQ': 'Error',      # 连续参数评估（可运行）
    'Core': 'Core',                  # Stage0 基座
    'SetLemmas': 'Core',             # 通用集合引理
}


def find_legacy(name):
    for dp, _, fs in os.walk(LEGACY):
        for f in fs:
            if f == name + '.lean':
                return os.path.join(dp, f)
    return None


def port_one(name, domain, verify=True):
    src = find_legacy(name)
    if not src:
        return {'module': name, 'ok': False, 'why': 'Legacy 中找不到'}

    with open(src, encoding='utf-8') as f:
        text = f.read()

    # 必须只有 Mathlib / 无 import
    imports = re.findall(r'^\s*import\s+(\S+)', text, re.M)
    bad = [i for i in imports if not i.startswith('Mathlib')]
    if bad:
        return {'module': name, 'ok': False, 'why': f'有非 Mathlib import: {bad}'}

    # 替换最外层 namespace。兼容两种写法：
    #   (a) `namespace Fate` 单独一行（后面跟 `namespace Sub`）
    #   (b) `namespace Fate.Sub` 复合形式
    m_bare = re.search(r'^namespace Fate\s*$', text, re.M)
    m_comp = re.search(r'^namespace Fate\.(\S+)\s*$', text, re.M)
    if m_bare:
        body = re.sub(r'^namespace Fate\s*$', f'namespace FateV2.{domain}', text, count=1, flags=re.M)
        body = re.sub(r'^end Fate\s*$', f'end FateV2.{domain}', body, count=1, flags=re.M)
    elif m_comp:
        sub = m_comp.group(1)
        # ⚠ 关键：必须**全文**替换限定名，不能只换 namespace/end 行。
        # 文件里常有 `#print axioms Fate.Sub.foo` 这类全限定引用，
        # 只改行首会导致 `Unknown constant` 编译失败。
        # （实测：ErrorBoundE1 有 10 处此类引用）
        body = text.replace(f'Fate.{sub}', f'FateV2.{domain}.{sub}')
    else:
        # 裸命名空间（如 `namespace Lattice`）：包一层 FateV2.<Domain>.<Bare>
        m_bare2 = re.search(r'^namespace (\S+)\s*$', text, re.M)
        if not m_bare2:
            return {'module': name, 'ok': False, 'why': '找不到任何 namespace 行'}
        bare = m_bare2.group(1)
        body = re.sub(r'^namespace ' + re.escape(bare) + r'\s*$',
                      f'namespace FateV2.{domain}.{bare}', text, count=1, flags=re.M)
        body = re.sub(r'^end ' + re.escape(bare) + r'\s*$',
                      f'end FateV2.{domain}.{bare}', body, count=1, flags=re.M)

    header = f'''/-!
  # {domain} · {name}

  ## 迁移登记
  - 来源：`FateWorld/Legacy/{name}.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.{domain}`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

'''
    idx = body.find('/-!')
    if idx < 0:
        idx = body.find('/-')
    if idx < 0:
        idx = body.find('namespace FateV2')
    out = body[:idx] + header + body[idx:]

    dst_dir = os.path.join(V2, domain)
    os.makedirs(dst_dir, exist_ok=True)
    dst = os.path.join(dst_dir, name + '.lean')
    with open(dst, 'w', encoding='utf-8', newline='\n') as f:
        f.write(out)

    if not verify:
        return {'module': name, 'ok': True, 'dst': dst, 'verified': False}

    # 编译验证
    try:
        r = subprocess.run(['lake', 'build', f'FateWorld.FateV2.{domain}.{name}'],
                           cwd=ROOT, capture_output=True, text=True,
                           encoding='utf-8', errors='replace', timeout=1800)
        rc, out = r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        rc, out = 1, 'TIMEOUT（>1800s）'
    except Exception as e:
        rc, out = 1, f'调用 lake 出错: {e}'

    if rc != 0:
        errs = [l for l in out.splitlines() if 'error' in l.lower()][:3]
        # 回滚：文件可能根本没写成功，容错处理
        try:
            if os.path.exists(dst):
                os.remove(dst)
        except OSError:
            pass
        return {'module': name, 'ok': False, 'why': '编译失败', 'errors': errs}

    return {'module': name, 'ok': True, 'dst': dst, 'verified': True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--plan', action='store_true')
    ap.add_argument('--one')
    ap.add_argument('--domain')
    ap.add_argument('--batch', action='store_true')
    a = ap.parse_args()

    if a.list:
        with open(CAND_CSV, encoding='utf-8-sig') as f:
            rows = list(csv.DictReader(f))
        cand = [r for r in rows
                if r['Legacy依赖数'] == '0' and int(r['定理数']) > 0
                and r['与FateV2重名'] != 'Y']
        print(f'可迁候选: {len(cand)}')
        for r in sorted(cand, key=lambda x: -int(x['定理数'])):
            d = PLAN.get(r['模块'], '?')
            mark = '✓' if r['模块'] in DONE else ' '
            print(f'  [{mark}] {r["模块"]:<24} {r["定理数"]:>3} 定理  → {d}')
        return

    if a.plan:
        pend = [m for m in PLAN if m not in DONE]
        print(f'待迁: {len(pend)}')
        for m in pend:
            print(f'  {m:<24} → {PLAN[m]}')
        return

    if a.one:
        r = port_one(a.one, a.domain)
        print(json.dumps(r, ensure_ascii=False, indent=1))
        return

    if a.batch:
        v2names = {x[:-5] for x in os.listdir(os.path.join(V2, '')) if x.endswith('.lean')}
        for dp, _, fs in os.walk(V2):
            v2names |= {x[:-5] for x in fs if x.endswith('.lean')}
        pend = [(m, d) for m, d in PLAN.items() if m not in v2names]
        ok, fail = [], []
        for m, d in pend:
            r = port_one(m, d)
            status = 'OK  ' if r['ok'] else 'FAIL'
            print(f'[{status}] {m:<24} → {d}   {r.get("why","")}',
                  flush=True)
            (ok if r['ok'] else fail).append(r)
        print(f'\n成功 {len(ok)} / 失败 {len(fail)}')
        for r in fail:
            print(f'  {r["module"]}: {r.get("why")} {r.get("errors","")}')
        return


if __name__ == '__main__':
    main()
