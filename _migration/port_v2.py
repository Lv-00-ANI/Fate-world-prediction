#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
第 1 层迁移器 v2：完整规则。

## 与 v1 的区别

v1 只做 import 重定向 + namespace 改写，失败率高。
v2 加入 **open 改写**（用 `nsmap.py` 建的映射表），这是关键。

## 三条改写规则（缺一不可）

1. **import 重定向**
   `import FateWorld.Legacy.X` → `import FateWorld.FateV2.<域>.X`

2. **命名空间改写**
   `namespace Fate` → `namespace FateV2.<域>`
   （以及复合形式 `namespace Fate.Sub` / 裸 `namespace Sub`）

3. **open 改写** ⭐ 关键
   `open PearlHierarchy` → `open FateV2.Modeling.PearlHierarchy`
   `open Causalean.Graph` → `open FateV2.Modeling.Graph`

   ⚠ 只改写**能在映射表里查到**的目标。
   Mathlib 命名空间（Finset / Set / Filter …）与 **section 名**保持不动。

## 为什么第 3 条必须有

实测 `CfNecessity`：只做 1+2 会报 `unknown namespace PearlHierarchy`。
加上第 3 条后编译通过。

## 用法

    python _migration\\port_v2.py --one X --domain Modeling
    python _migration\\port_v2.py --list
"""
import os, re, json, argparse, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')
NSMAP = os.path.join(ROOT, '_migration', 'ns_map.json')

# 恰好同名，不可重定向（dupcheck.py 实测）
COLLISIONS = {'Basic', 'Completeness', 'DetFunToStepDraft'}

IMPORT_RE = re.compile(r'^(\s*(?:(?:module|public|private|meta)\s+)*import\s+)FateWorld\.Legacy\.(\w+)\s*$', re.M)
THM_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\s+', re.M)
OPEN_RE = re.compile(r'^(\s*open\s+)(.+)$')


def load_nsmap():
    if os.path.exists(NSMAP):
        with open(NSMAP, encoding='utf-8') as f:
            return json.load(f)['map']
    return {}


def v2_index():
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
    src = find_legacy(name)
    if not src:
        return None
    with open(src, encoding='utf-8') as f:
        text = f.read()
    leg_deps = [m.group(2) for m in IMPORT_RE.finditer(text)]
    v2m = v2_index()
    unresolved = [d for d in leg_deps if d not in v2m]
    blocked = [d for d in leg_deps if d in COLLISIONS]
    return {'name': name, 'src': src, 'leg_deps': leg_deps,
            'unresolved': unresolved, 'blocked': blocked,
            'theorems': len(THM_RE.findall(text))}


def rewrite_opens(text, nsmap):
    """只改写映射表里查得到的目标；section 名与 Mathlib 名不动。"""
    out = []
    for line in text.split('\n'):
        m = OPEN_RE.match(line)
        if not m:
            out.append(line)
            continue
        pre, rest = m.group(1), m.group(2)
        trail = ''
        if rest.endswith(' in'):
            rest, trail = rest[:-3], ' in'
        parts = rest.split()
        new = []
        for p in parts:
            if p in nsmap:
                new.append(nsmap[p])
            elif f'Fate.{p}' in nsmap:
                new.append(nsmap[f'Fate.{p}'])
            else:
                new.append(p)          # 保持不动（Mathlib / section 名）
        out.append(pre + ' '.join(new) + trail)
    return '\n'.join(out)


def port_one(name, domain, verify=True):
    info = analyze(name)
    if info is None:
        return {'module': name, 'ok': False, 'why': 'Legacy 中找不到'}
    if info['blocked']:
        return {'module': name, 'ok': False, 'why': f'依赖恰好同名 {info["blocked"]}'}
    if info['unresolved']:
        return {'module': name, 'ok': False, 'why': f'依赖未迁 {info["unresolved"]}'}

    nsmap = load_nsmap()
    v2m = v2_index()

    with open(info['src'], encoding='utf-8') as f:
        text = f.read()

    # 规则 1：import 重定向
    text = IMPORT_RE.sub(lambda m: m.group(1) + v2m[m.group(2)], text)

    # 规则 2：命名空间
    #
    # ⚠ 实测陷阱：文件里可能有**多处** namespace 写法
    #     namespace Fate              (顶层)
    #     namespace Fate.WorldScenario.Tight   (后面又开一个复合的)
    # 只改第一处会留下 `namespace Fate.WorldScenario.Tight` 未改，
    # 导致引用解析不到。⟹ 必须**全文**替换 `Fate.` 前缀。
    m_bare = re.search(r'^namespace Fate\s*$', text, re.M)
    m_comp = re.search(r'^namespace Fate\.(\S+)\s*$', text, re.M)
    if m_bare:
        text = re.sub(r'^namespace Fate\s*$', f'namespace FateV2.{domain}', text, count=1, flags=re.M)
        text = re.sub(r'^end Fate\s*$', f'end FateV2.{domain}', text, count=1, flags=re.M)
        # 正文里其他 `namespace Fate.Xxx` / `end Fate.Xxx` 也要跟前缀改
        text = re.sub(r'^(namespace|end) Fate\.', rf'\1 FateV2.{domain}.', text, flags=re.M)
    elif m_comp:
        sub = m_comp.group(1)
        text = text.replace(f'Fate.{sub}', f'FateV2.{domain}.{sub}')
    else:
        mb = re.search(r'^namespace (\S+)\s*$', text, re.M)
        if not mb:
            return {'module': name, 'ok': False, 'why': '找不到 namespace'}
        bare = mb.group(1)
        text = re.sub(r'^namespace ' + re.escape(bare) + r'\s*$',
                      f'namespace FateV2.{domain}.{bare}', text, count=1, flags=re.M)
        text = re.sub(r'^end ' + re.escape(bare) + r'\s*$',
                      f'end FateV2.{domain}.{bare}', text, count=1, flags=re.M)

    # 规则 3：open 改写 ⭐
    text = rewrite_opens(text, nsmap)

    # 规则 4：补 open 依赖所在的**域** ⭐⭐
    #
    # 为什么需要：Legacy 里多个模块共享 `namespace Fate` 这一层级，例如
    #     Fate > WiringConvergence      (WiringConvergence.lean)
    #     Fate > TwoVersions            (TwoVersions.lean)
    # 因为都在 Fate 下，TwoVersions 里可以直接写 `WiringConvergence.stepMap`。
    #
    # 迁到 FateV2 后，各模块被分到不同域（FateV2.Loop / FateV2.Predict…），
    # 这种**隐含可见性**丢失，必须显式 `open` 依赖所在的域。
    #
    # 实测反例：TwoVersions（Predict 域）引用 WiringConvergence.stepMap，
    # 而 WiringConvergence 在 Loop 域 ⟹ 需 `open FateV2.Loop`。
    dep_domains = set()
    for d in info['leg_deps']:
        full = v2m[d]                       # FateWorld.FateV2.Loop.WiringConvergence
        parts = full.split('.')
        if len(parts) >= 4:
            dep_domains.add(f'FateV2.{parts[2]}')
    dep_domains.discard(f'FateV2.{domain}')  # 不 open 自己所在的域
    dep_opens = '\n'.join(f'open {d}' for d in sorted(dep_domains))

    # 规则 5：补 open **同域的兄弟命名空间** ⭐⭐⭐
    #
    # 规则 4 排除了「自己所在的域」，但同域内还有兄弟模块。例如：
    #     FateV2.Predict.InterventionTight   引用 InterventionSelection.Good
    #     FateV2.Predict.InterventionSelection
    # 两者同属 Predict 域。原文件在 `namespace Fate` 下能直接看见，
    # 迁移后必须 `open InterventionSelection`（短名，不带域前缀）。
    #
    # ⚠ 陷阱：**不能用模块名当命名空间名**。
    # 实测：`PolicyAlgorithm.lean` 里的 namespace 其实叫 `WorldScenario`，
    # 按模块名 open `PolicyAlgorithm` 会报 `unknown namespace`。
    # ⟹ 必须读文件里的真实 namespace。
    def real_ns(module_name):
        """读 FateV2 模块文件，返回它在 FateV2.<域> 下的第一层子命名空间（若无则 None）。"""
        path = v2m.get(module_name)
        if not path:
            return None
        rel = path[len('FateWorld.'):].replace('.', os.sep) + '.lean'
        fp = os.path.join(ROOT, rel)
        if not os.path.exists(fp):
            return None
        with open(fp, encoding='utf-8') as f:
            src = f.read()
        stack = []
        for line in src.split('\n'):
            m = re.match(r'^\s*namespace\s+(\S+)', line)
            if m:
                stack.append(m.group(1))
                full = '.'.join(stack)
                # 只关心 FateV2.<域>.<子> 的第一层
                prefix = f'FateV2.{domain}.'
                if full.startswith(prefix) and full.count('.') == 2:
                    return full[len(prefix):]
                continue
            if re.match(r'^\s*end\s+\S+\s*$', line) and stack:
                stack.pop()
        return None

    sibling_opens = []
    for d in info['leg_deps']:
        parts = v2m[d].split('.')
        if len(parts) >= 4 and parts[2] == domain:
            ns = real_ns(d)
            if ns:
                sibling_opens.append(ns)
    sibling_line = f'open {" ".join(sorted(set(sibling_opens)))}' if sibling_opens else ''

    header = f'''/-!
  # {domain} · {name}

  ## 迁移登记
  - 来源：`FateWorld/Legacy/{name}.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：{', '.join(info['leg_deps']) or '无'}
  - 补充 open 域：{', '.join(sorted(dep_domains)) or '无'}
  - 补充 open 兄弟：{', '.join(sorted(set(sibling_opens))) or '无'}
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

'''
    idx = text.find('/-!')
    if idx < 0:
        idx = text.find('/-')
    if idx < 0:
        idx = 0
    out = text[:idx] + header + text[idx:]

    extra = '\n'.join(x for x in (dep_opens, sibling_line) if x)
    if extra:
        out = re.sub(rf'^(namespace FateV2\.{re.escape(domain)}\S*)$',
                     lambda m: m.group(1) + '\n\n' + extra,
                     out, count=1, flags=re.M)

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
    except Exception as e:
        rc, o = 1, str(e)

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
    ap.add_argument('--one')
    ap.add_argument('--domain')
    ap.add_argument('--list', action='store_true')
    a = ap.parse_args()

    if a.one:
        print(json.dumps(port_one(a.one, a.domain), ensure_ascii=False, indent=1))
        return

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
                if info and not info['unresolved'] and not info['blocked'] and info['theorems'] > 0:
                    rows.append(info)
        rows.sort(key=lambda r: -r['theorems'])
        print(f'可迁（三重规则完整）：{len(rows)}')
        for r in rows[:40]:
            print(f'  {r["name"]:<30} {r["theorems"]:>3} 定理')


if __name__ == '__main__':
    main()
