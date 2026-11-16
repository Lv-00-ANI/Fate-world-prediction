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


def ns_exists(ns):
    """检查 ns 是否真的在 FateV2 里被声明为 namespace（防止 open 一个不存在的名字）。"""
    global _NS_CACHE
    try:
        _NS_CACHE
    except NameError:
        _NS_CACHE = None
    if _NS_CACHE is None:
        _NS_CACHE = set()
        for dp, _, fs in os.walk(V2):
            for fn in fs:
                if not fn.endswith('.lean'):
                    continue
                with open(os.path.join(dp, fn), encoding='utf-8') as fh:
                    stack = []
                    for line in fh:
                        m = re.match(r'^\s*namespace\s+(\S+)', line)
                        if m:
                            stack.append(m.group(1))
                            _NS_CACHE.add('.'.join(stack))
                            continue
                        if re.match(r'^\s*end\s+\S+\s*$', line) and stack:
                            stack.pop()
    return ns in _NS_CACHE


def _reachable_domains(text, v2m, self_domain):
    """从文件的 import 语句出发，沿 FateV2 模块依赖做 BFS，
    返回可达的所有**域**名集合。

    用途：规则 7 补 open 前的校验 —— 只能 open 已 import 到的域。"""
    seed = []
    for m in IMPORT_RE.finditer(text):
        mod = m.group(2)
        if mod in v2m:
            seed.append(mod)
    seen_mod = set(seed)
    domains = set()
    if self_domain:
        domains.add(self_domain)
    stack = list(seed)
    v2root = os.path.join(ROOT, 'FateWorld')
    while stack:
        mod = stack.pop()
        full = v2m.get(mod)
        if not full:
            continue
        rel = full[len('FateWorld.'):].replace('.', os.sep) + '.lean'
        fp = os.path.join(v2root, rel)
        parts = full.split('.')
        if len(parts) >= 4:
            domains.add(parts[2])
        if not os.path.exists(fp):
            continue
        with open(fp, encoding='utf-8') as fh:
            src = fh.read()
        for m in IMPORT_RE.finditer(src):
            nxt = m.group(2)
            if nxt in v2m and nxt not in seen_mod:
                seen_mod.add(nxt)
                stack.append(nxt)
    return domains


def load_all_index():
    """读 all_index.json（由 allindex.py 生成，含 def/theorem）。"""
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'all_index.json')
    if not os.path.exists(p):
        return {}
    with open(p, encoding='utf-8') as f:
        return json.load(f)


def load_type_index():
    """读 type_index.json（由 typeindex.py 生成）。"""
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'type_index.json')
    if not os.path.exists(p):
        return {}
    with open(p, encoding='utf-8') as f:
        return json.load(f)


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

    # 规则 6：正文里的**全限定引用**改写 ⭐⭐⭐
    #
    # 为什么需要：文件正文可能直接写全限定名，例如
    #     rw [Fate.ConvergenceOptimal.abs_one_sub_eq_c 1]
    #     have h := Fate.WiringConvergence.stepMap ...
    # 这些既不在 namespace/end 行，也不在 open 行，规则 2 与 3 都覆盖不到。
    #
    # 实测反例：ConvergeToOptimalND 迁移后 `Lean exited with code 1`
    # 但**没有任何 error 行**（错误来自项层面的未知常量，不在语法层报告）。
    #
    # 处理方式：
    #   (a) 先查 nsmap（Legacy ns → FateV2 ns，来自模块配对）
    #   (b) 查不到时查 typeindex（类型/定义名 → 所在域）
    #
    # ⚠ 实测补丁：原先只查 nsmap，且只匹配单段 `Fate.X`。
    # LearnFunction 里的 `Fate.Rules`（Rules 是 Model/Frame 里的 def）
    # 查不到，残留后报 `Unknown identifier Fate.Rules`。
    # ⟹ 加第二条通路：用 typeindex 定位任意 `Fate.<名字>` 的定义域。
    try:
        _aidx = load_all_index()
    except Exception:
        _aidx = {}

    def fix_qualified(s):
        def repl(m):
            full = m.group(0)                 # 例 Fate.ConvergenceOptimal / Fate.Rules
            if full in nsmap:
                return nsmap[full]
            name = full[5:]                   # 去掉 "Fate."
            if name in _aidx:
                d = _aidx[name]['domain']
                if ns_exists(f'FateV2.{d}'):
                    return f'FateV2.{d}.{name}'
            return full
        return re.sub(r'(?<![\w.`])Fate\.[A-Za-z_]\w*', repl, s)

    text = fix_qualified(text)

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

    # 规则 7：补 open **正文用到的类型/定义所在的域** ⭐⭐⭐⭐
    #
    # 为什么需要：Legacy 模块大量依赖 `namespace Fate` 的**扁平可见性**。
    # 写 `StateSpace` / `CtxSpace` 时，靠的是它们都在 `Fate` 前缀下
    # （即使是**间接 import** 进来的，也能拿到名字）。
    #
    # 迁移后这些名字散落到不同域，即使没有直接 import 那个模块，
    # 也必须显式 open 对应域，否则报：
    #     Invalid field notation: Field projection operates on types of
    #     the form `C ...` where C is a constant
    #
    # 实测反例：RuleLevel 只用同域的 LawRule，但它正文里的
    # CtxSpace（Model 域）+ StateSpace（Modeling 域）+ OutSpace（Model 域）
    # 都解析不到 —— 规则 4/5 都覆盖不到，因为这两个模块不在 leg_deps 里。
    #
    # 做法：扫正文出现的标识符，查 type_index 得到它所在的域，补 open。
    try:
        tindex = load_type_index()
    except Exception:
        tindex = {}

    if tindex:
        # ⚠ 只扫「正文代码区」，必须排除四类噪声：
        #   (a) import 行 —— 否则 `import Mathlib.Data.Real.Basic` 里的 Data 会被误认
        #   (b) 块注释 /- ... -/
        #   (c) 行注释 --
        #   (d) 字符串字面量
        # 实测反例：StatAlpha 因 import 行的 `Data` 命中 Core.Syntax.Data，
        # 生出 `open FateV2.Core`，而 FateV2.Core 不是命名空间 ⟹ unknown namespace。
        code = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
        code = re.sub(r'--[^\n]*', ' ', code)
        code = re.sub(r'"(?:[^"\\]|\\.)*"', ' ', code)
        code = re.sub(r'^\s*(?:(?:module|public|private|meta)\s+)*import\s+\S+',
                      ' ', code, flags=re.M)
        used_ids = set(re.findall(r'(?<![\w.\'])([A-Z][A-Za-z0-9_]{2,})', code))
        # ⚠ 排除**本文件自己定义**的名字。
        # 实测反例：StatAlpha 自己 `abbrev Data`，但索引里 Data 归到 Core.Syntax，
        # 于是误生 `open FateV2.Core` ⟹ unknown namespace（本文件并未 import Core）。
        own_defs = set(re.findall(
            r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
            r'(?:structure|inductive|class|def|abbrev|opaque)\s+([A-Z][A-Za-z0-9_\']*)',
            text))

        # ⚠ 关键校验：只 open **当前文件已经（直接或间接）import 到**的域。
        # 否则 open 一个没 import 的域会报 `unknown namespace`。
        # 实测反例：LearnFunction 只 import 了 Loop/Predict 三个模块，
        # 但正文里的 `Classical.choose` 命中索引 → 误生 open FateV2.Classical
        # → unknown namespace（本文件从未 import Classical 域）。
        #
        # 判据：用依赖闭包。直接从 import 语句出发，沿 FateV2 模块依赖 BFS，
        # 收集可达的所有域。
        reachable = _reachable_domains(text, v2m, domain)

        # 排除 Lean/Mathlib 的通用命名，它们不是 FateV2 的类型
        LEAN_NS = {'Classical', 'Data', 'Set', 'Filter', 'Finset', 'Nat', 'Int',
                   'Real', 'List', 'Option', 'Function', 'Monoid', 'Group',
                   'Order', 'MeasureTheory', 'Topology', 'ProbabilityTheory',
                   'ENNReal', 'NNReal', 'Matrix', 'Polynomial', 'Complex',
                   'CategoryTheory', 'Equiv', 'Submodule', 'Bornology'}

        for ident in used_ids - own_defs - LEAN_NS:
            rec = tindex.get(ident)
            if rec:
                d = rec['domain']
                if d != domain and d in reachable and ns_exists(f'FateV2.{d}'):
                    dep_domains.add(f'FateV2.{d}')

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
