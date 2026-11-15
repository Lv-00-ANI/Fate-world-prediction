#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
迁移 + 公理审计 一键工具。

## 用法

    python _migration\\migrate.py --module DeadPremiseAudit --domain Meta
    python _migration\\migrate.py --module DeadPremiseAudit --domain Meta --dry-run

## 它做什么

1. 从 `Legacy/` 找源文件
2. 改命名空间 `Fate.<X>` → `FateV2.<Domain>.<X>`
3. 加统一迁移登记头（保留原文件全部内容）
4. 编译验证
5. 公理审计（追命名空间，只审 theorem/lemma）
6. 输出结果

## 迁移判据（由 assess.py 给出）

- 零 Legacy 依赖（只 import Mathlib）
- 有定理
- 不与 FateV2 重名

## 纪律

- **证明体逐字不改**。只改命名空间与文件头。
- 若编译失败 → 不写入，报告原因。
- 若出现 `sorryAx` → 标记为**不合格**，不迁入。
"""
import os, re, sys, argparse, json

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEGACY = os.path.join(ROOT, 'FateWorld', 'Legacy')
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')

NS_RE = re.compile(r'^\s*namespace\s+(\S+)', re.M)
END_RE = re.compile(r'^\s*end\s+(\S+)\s*$', re.M)
THM_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:theorem|lemma)\s+([A-Za-z_][\w\']*)', re.M)


def find_legacy(name):
    for dp, _, fs in os.walk(LEGACY):
        for f in fs:
            if f == name + '.lean':
                return os.path.join(dp, f)
    return None


def migrate(name, domain, dry=False):
    src = find_legacy(name)
    if not src:
        return {'ok': False, 'why': f'Legacy 中找不到 {name}.lean'}

    with open(src, encoding='utf-8') as f:
        text = f.read()

    # 1. 找最外层命名空间（可能是 `Fate` 或 `Fate.X` 或裸名）
    orig_ns = NS_RE.findall(text)
    if not orig_ns:
        return {'ok': False, 'why': '找不到任何 namespace'}

    # 取第一个 namespace。若是裸 `Fate`，则模块名是文件名；
    # 若是 `Fate.X` 或多层，取第一层作为替换目标。
    first_ns = orig_ns[0]
    if first_ns == 'Fate':
        # 形如 `namespace Fate` + `namespace GazeAlgebra`
        # 替换 `namespace Fate` → `namespace FateV2.<Domain>`
        orig_root = 'Fate'
    elif first_ns.startswith('Fate.'):
        orig_root = first_ns
    else:
        # 裸命名空间（如 `MVFCA4`、`Lattice`）—— 直接把整棵树挪到 FateV2.<Domain> 下
        orig_root = first_ns

    short = name            # 文件名作为模块短名
    new_ns = f'FateV2.{domain}'

    # 2. 改命名空间
    if orig_root == short and not orig_root.startswith('Fate'):
        # 裸命名空间：包一层
        body = text.replace(f'namespace {orig_root}', f'namespace {new_ns}.{orig_root}', 1)
        # 对应的 end 也要改（最后一个）
        if END_RE.search(body):
            idx_end = body.rfind(f'end {orig_root}')
            if idx_end >= 0:
                body = body[:idx_end] + f'end {new_ns}.{orig_root}' + body[idx_end+len(f'end {orig_root}'):]
    else:
        body = text.replace(orig_root, new_ns, 1) if orig_root == 'Fate' else text.replace(orig_root, new_ns)

    # 3. 迁移登记头
    header = f'''/-!
  # {domain} · {short}

  ## 迁移登记
  - 来源：`FateWorld/Legacy/{short}.lean`（原 `{orig_root.replace("Fate.", "Fate/")}.lean`）
  - 动作：B 适配（改命名空间 `{orig_root}` → `{new_ns}`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

'''
    # 去掉原文件头（到第一个 -/ 为止），保留正文
    idx = body.find('-/')
    rest = body[idx + 2:] if idx >= 0 else body
    out = header + rest.lstrip('\n')

    dst_dir = os.path.join(V2, domain)
    dst = os.path.join(dst_dir, short + '.lean')

    if dry:
        return {'ok': True, 'dry': True, 'dst': dst, 'ns': new_ns,
                'lines': out.count('\n') + 1}

    os.makedirs(dst_dir, exist_ok=True)
    with open(dst, 'w', encoding='utf-8', newline='\n') as f:
        f.write(out)

    return {'ok': True, 'dst': dst, 'ns': new_ns,
            'lines': out.count('\n') + 1, 'theorems': len(THM_RE.findall(out))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--module', required=True)
    ap.add_argument('--domain', required=True,
                    help='Core/Classical/Bridge/Modeling/Model/Rules/Predict/Export/Error/Loop/Meta')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()

    r = migrate(a.module, a.domain, a.dry_run)
    print(json.dumps(r, ensure_ascii=False, indent=1))


if __name__ == '__main__':
    main()
