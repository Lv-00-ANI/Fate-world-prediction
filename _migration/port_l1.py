#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
第 1 层迁移器：依赖已迁模块的 Legacy 模块 → FateV2。

## 与第 0 层的区别

第 0 层模块 `import Mathlib` 或零 import，只改命名空间即可。
第 1 层模块 `import FateWorld.Legacy.X`，而 X 可能：
  (a) 已在 FateV2 → import 必须重定向
  (b) 仍在 Legacy → import 保持不变（但那样就不算「第 1 层」了）

## 重定向的安全前提

由 `dupcheck.py` 核查：170 个重名模块中 166 个是「同一模块」（定理名 Jaccard ≥ 0.8）。
**只有 3 个是「恰好同名」**——它们不能重定向：
- `Basic`: Legacy/Basic vs FateV2/Modeling.Basic
- `Completeness`: Legacy/Completeness vs FateV2/Export.Completeness
- `DetFunToStepDraft`: Legacy/DetFunToStepDraft vs FateV2/Predict.DetFunToStepDraft

若待迁模块 import 了这 3 个之一 → **跳过**，标记为「需人工处理」。

## 用法

    python _migration\\port_l1.py --list
    python _migration\\port_l1.py --one Classification --domain Rules
    python _migration\\port_l1.py --batch --max 20
"""
import os, re, csv, json, argparse, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')

# 恰好同名，不可重定向（由 dupcheck.py 实测）
COLLISIONS = {'Basic', 'Completeness', 'DetFunToStepDraft'}

IMPORT_RE = re.compile(r'^\s*(?:(?:module|public|private|meta)\s+)*import\s+(\S+)', re.M)
THM_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:theorem|lemma)\s+[A-Za-z_][\w\']*', re.M)


def v2_index():
    """模块短名 → FateV2 全模块路径"""
    out = {}
    for dp, _, fs in os.walk(V2):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, V2).replace('\\', '.')[:-5]
                out[f[:-5]] = f'FateWorld.FateV2.{rel}'
    return out


def find_legacy(name):
    for dp, _, fs in os.walk(LEGACY):
        for f in fs:
            if f == name + '.lean':
                return os.path.join(dp, f)
    return None


def analyze(name):
    """判断一个 Legacy 模块是否可迁入（第 1 层）。"""
    src = find_legacy(name)
    if not src:
        return None
    with open(src, encoding='utf-8') as f:
        text = f.read()
    imports = IMPORT_RE.findall(text)
    leg_deps = [i.split('.')[-1] for i in imports if i.startswith('FateWorld.Legacy.')]
    non_mathlib = [i for i in imports
                   if not i.startswith('Mathlib') and not i.startswith('FateWorld.Legacy.')]
    v2m = v2_index()
    unresolved = [d for d in leg_deps if d not in v2m]
    blocked = [d for d in leg_deps if d in COLLISIONS]
    return {
        'name': name,
        'src': src,
        'leg_deps': leg_deps,
        'unresolved': unresolved,
        'blocked': blocked,
        'non_mathlib': non_mathlib,
        'theorems': len(THM_RE.findall(text)),
        'migratable': not unresolved and not blocked and not non_mathlib,
    }


def port_one(name, domain, verify=True):
    info = analyze(name)
    if info is None:
        return {'module': name, 'ok': False, 'why': 'Legacy 中找不到'}
    if info['blocked']:
        return {'module': name, 'ok': False,
                'why': f'依赖恰好同名模块 {info["blocked"]}，不可重定向'}
    if info['unresolved']:
        return {'module': name, 'ok': False,
                'why': f'依赖未迁模块 {info["unresolved"]}'}

    with open(info['src'], encoding='utf-8') as f:
        text = f.read()

    v2m = v2_index()

    # 1. 重定向 Legacy import → FateV2 import
    for d in info['leg_deps']:
        text = re.sub(
            r'^(\s*(?:(?:module|public|private|meta)\s+)*import\s+)'
            + re.escape('FateWorld.Legacy.' + d) + r'\s*$',
            r'\g<1>' + v2m[d], text, flags=re.M)

    # 2. 改命名空间（三种写法）
    m_bare = re.search(r'^namespace Fate\s*$', text, re.M)
    m_comp = re.search(r'^namespace Fate\.(\S+)\s*$', text, re.M)
    if m_bare:
        body = re.sub(r'^namespace Fate\s*$', f'namespace FateV2.{domain}', text, count=1, flags=re.M)
        body = re.sub(r'^end Fate\s*$', f'end FateV2.{domain}', body, count=1, flags=re.M)
    elif m_comp:
        sub = m_comp.group(1)
        body = text.replace(f'Fate.{sub}', f'FateV2.{domain}.{sub}')
    else:
        mb = re.search(r'^namespace (\S+)\s*$', text, re.M)
        if not mb:
            return {'module': name, 'ok': False, 'why': '找不到 namespace'}
        bare = mb.group(1)
        body = re.sub(r'^namespace ' + re.escape(bare) + r'\s*$',
                      f'namespace FateV2.{domain}.{bare}', text, count=1, flags=re.M)
        body = re.sub(r'^end ' + re.escape(bare) + r'\s*$',
                      f'end FateV2.{domain}.{bare}', body, count=1, flags=re.M)

    # 3. 补 open 语句
    #    ⚠ 关键发现（实测 ResidualReduces / T43Abduction）：
    #    原文件所有内容在 `namespace Fate` 下，故 `StateSpace`、`PearlHierarchy` 等
    #    可直接引用。FateV2 把它们拆到 `FateV2.Modeling` / `FateV2.Loop` 等域，
    #    迁入后模块在 `FateV2.<Domain>` 下，引用就断了。
    #
    #    对策：扫描被重定向 import 的目标域，对每个都补 `open`。
    open_domains = set()
    for d in info['leg_deps']:
        full = v2m[d]                      # 例：FateWorld.FateV2.Modeling.PearlHierarchy
        parts = full.split('.')            # [FateWorld, FateV2, Modeling, PearlHierarchy]
        if len(parts) >= 4:
            open_domains.add(f'FateV2.{parts[2]}')
    open_lines = '\n'.join(f'open {d}' for d in sorted(open_domains))

    # 4. 组织输出：import 区 → 迁移头 → open → 正文
    header = f'''/-!
  # {domain} · {name}

  ## 迁移登记
  - 来源：`FateWorld/Legacy/{name}.lean`
  - 动作：B 适配（命名空间 + import 重定向{'+ open' if open_domains else ''}）
  - 依赖重定向：{', '.join(d + ' → FateV2' for d in info['leg_deps']) or '无'}
  - 补充 open：{', '.join(sorted(open_domains)) or '无'}
  - 改动：**仅命名空间、import 路径、open 语句**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

'''
    idx = body.find('/-!')
    if idx < 0:
        idx = body.find('/-')
    if idx < 0:
        idx = 0
    out = body[:idx] + header + body[idx:]

    if open_lines:
        out = re.sub(rf'^(namespace FateV2\.{re.escape(domain)}\S*)$',
                     lambda m: m.group(1) + '\n\n' + open_lines, out, count=1, flags=re.M)

    dst_dir = os.path.join(V2, domain)
    os.makedirs(dst_dir, exist_ok=True)
    dst = os.path.join(dst_dir, name + '.lean')
    with open(dst, 'w', encoding='utf-8', newline='\n') as f:
        f.write(out)

    if not verify:
        return {'module': name, 'ok': True, 'dst': dst, 'verified': False}

    try:
        r = subprocess.run(['lake', 'build', f'FateWorld.FateV2.{domain}.{name}'],
                           cwd=ROOT, capture_output=True, text=True,
                           encoding='utf-8', errors='replace', timeout=1800)
        rc, o = r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        rc, o = 1, 'TIMEOUT'
    except Exception as e:
        rc, o = 1, f'lake 调用失败: {e}'

    if rc != 0:
        errs = [l for l in o.splitlines() if 'error' in l.lower()][:3]
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
    ap.add_argument('--one')
    ap.add_argument('--domain')
    ap.add_argument('--batch', action='store_true')
    ap.add_argument('--max', type=int, default=0)
    ap.add_argument('--domain-filter')
    a = ap.parse_args()

    if a.list:
        v2m = v2_index()
        rows = []
        for dp, _, fs in os.walk(LEGACY):
            for f in fs:
                if not f.endswith('.lean'):
                    continue
                n = f[:-5]
                if n in v2m:
                    continue
                info = analyze(n)
                if info and info['migratable'] and info['theorems'] > 0:
                    rows.append(info)
        rows.sort(key=lambda r: (len(r['leg_deps']), -r['theorems']))
        print(f'第 1 层可迁（依赖全部已迁 + 无冲突）: {len(rows)}')
        for r in rows[:60]:
            print(f'  {r["name"]:<26} 依赖{len(r["leg_deps"])} 定理{r["theorems"]:>3}')
        return

    if a.one:
        print(json.dumps(port_one(a.one, a.domain), ensure_ascii=False, indent=1))
        return

    if a.batch:
        v2m = v2_index()
        rows = []
        for dp, _, fs in os.walk(LEGACY):
            for f in fs:
                if not f.endswith('.lean'):
                    continue
                n = f[:-5]
                if n in v2m:
                    continue
                info = analyze(n)
                if info and info['migratable'] and info['theorems'] > 0:
                    rows.append(info)
        rows.sort(key=lambda r: (len(r['leg_deps']), -r['theorems']))
        if a.max:
            rows = rows[:a.max]
        ok = fail = 0
        for r in rows:
            d = a.domain or 'Error'   # 默认域，实际由 PLAN 覆盖
            res = port_one(r['name'], PLAN.get(r['name'], d))
            if res['ok']:
                ok += 1
                print(f'[OK  ] {r["name"]:<26} → {PLAN.get(r["name"], d)}', flush=True)
            else:
                fail += 1
                print(f'[FAIL] {r["name"]:<26} {res.get("why")} {res.get("errors","")}', flush=True)
        print(f'\n成功 {ok} / 失败 {fail}')
        return


# 域分配表（人工判定，随迁移补充）
PLAN = {
    'Classification': 'Rules', 'Completeness': 'Rules', 'Implication': 'Rules',
    'LawRule': 'Rules', 'FormalContext': 'Rules', 'LawRuleLattice': 'Rules',
    'LawRuleInstances': 'Rules', 'LawRuleToTraj': 'Rules', 'InstIsDirac': 'Rules',
    'RebaseAbstract': 'Rules', 'ErrorDimUnified': 'Rules',
    'FrontdoorCounterexample': 'Predict', 'FrontdoorCriterion': 'Predict',
    'FrontdoorChainProof': 'Predict', 'BackdoorCriterion': 'Predict',
    'BackdoorGenuine': 'Predict', 'T43Abduction': 'Predict',
    'ResidualReduces': 'Loop', 'BoundWriteBack': 'Loop',
    'SCMGraph': 'Modeling', 'SCMSemantics': 'Modeling',
    'FitBoundary': 'Error', 'ErrorCriterionUnified': 'Error',
    'TrajGenDeterministic': 'Model',
}

if __name__ == '__main__':
    main()
