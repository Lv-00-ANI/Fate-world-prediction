#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""从全量盘点.csv 生成 99-应迁未迁.md"""
import csv, os, io

BASE = os.path.dirname(os.path.abspath(__file__))
CSV  = os.path.join(BASE, '全量盘点.csv')
OUT  = os.path.join(BASE, '99-应迁未迁.md')

rows = []
with open(CSV, encoding='utf-8-sig', newline='') as f:
    for r in csv.DictReader(f):
        rows.append(r)

def i(r, k):
    try: return int(r[k])
    except: return 0

pending = [r for r in rows if r['状态'].startswith('应迁未迁') and r['动作'] != 'D']
pending.sort(key=lambda r: (r['动作'], r['模块']))

L = []
w = L.append

w('# 99 个「应迁未迁」模块清单')
w('')
w('> **这是本次整理最重要的发现。**')
w('> 迁移映射表（`../命运-v2/_迁移映射.csv`）明确登记了每个模块的迁移动作，')
w('> 但**有 99 个非弃用的模块从未真正迁入 `命运-v2/FateV2/`**。')
w('')
w('**实测（2026-11-13）**：')
w('')
w('| 项 | 数字 |')
w('|---|---:|')
w(f'| 应迁未迁模块 | **{len(pending)}** |')
w(f'| 合计行数 | **{sum(i(r,"行数") for r in pending):,}** |')
w(f'| 合计定理/引理 | **{sum(i(r,"定理") for r in pending):,}** |')
w('')
w('**源文件全部存在**（在 `命运-素材-原始文件-不可更改/Fate/` 下），无缺失。')
w('')
w('---')
w('')
w('## 按迁移动作分组')
w('')
w('| 动作 | 含义 | 个数 | 行数 | 定理 | 处理难度 |')
w('|---|---|---:|---:|---:|---|')
MEAN = {'A': '原样迁入，一字不改', 'B': '需适配命名空间/import', 'C': '与裁决冲突，须重写'}
DIFF = {'A': '最低', 'B': '中', 'C': '最高'}
for act in ('A', 'B', 'C'):
    sub = [r for r in pending if r['动作'] == act]
    if not sub: continue
    w(f'| **{act}** | {MEAN[act]} | {len(sub)} | {sum(i(r,"行数") for r in sub):,} | '
      f'{sum(i(r,"定理") for r in sub):,} | {DIFF[act]} |')
w('')
w('> **A 类 36 个是白捡的**：动作定义就是「代码可直接用，只搬到新位置，**一字不改**」。')
w('> 它们从没迁，不是因为难，是因为**当时的迁移批次没走到它们**。')
w('')
w('---')
w('')
w('## 按目标层分组')
w('')
w('| 层 | 个数 | 行数 |')
w('|---|---:|---:|')
from collections import defaultdict
by = defaultdict(list)
for r in pending: by[r['层']].append(r)
for k in sorted(by, key=lambda k: -len(by[k])):
    g = by[k]
    w(f'| {k} | {len(g)} | {sum(i(r,"行数") for r in g):,} |')
w('')
w('---')
w('')
for act in ('A', 'B', 'C'):
    sub = [r for r in pending if r['动作'] == act]
    if not sub: continue
    w(f'## {act} 类（{len(sub)} 个）')
    w('')
    w('| 模块 | 层 | 行数 | 定理 |')
    w('|---|---|---:|---:|')
    for r in sub:
        w(f'| `{r["模块"]}` | {r["层"]} | {i(r,"行数")} | {i(r,"定理")} |')
    w('')

text = '\n'.join(L)
with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
    f.write(text)
print(f'已写入 {OUT}')
print(f'模块 {len(pending)} 个, 行 {sum(i(r,"行数") for r in pending):,}, 定理 {sum(i(r,"定理") for r in pending):,}')
