# Fate-world-prediction

> **《命运》世界模型 / 预测系统的正式工程仓库。**
>
> [![Lean](https://img.shields.io/badge/Lean-4.33.0--rc1-blue)](https://leanprover.github.io/)
> [![Modules](https://img.shields.io/badge/modules-1106-green)]()
> [![Build](https://img.shields.io/badge/build-passing-brightgreen)]()
>
> **建立**：2026-11-13 · **远程**：https://github.com/Lv-00-ANI/Fate-world-prediction

---

## 这是什么

一个**世界模型 / 预测系统**的形式化实现。核心命题是一条链路：

```
真实世界
   │  ① 数学建模（世界 → 数学对象的唯一接口）
   ▼
Model = ⟨V, U, F, P_U⟩        ← 模型 = 结构因果模型（SCM）
   │  ② 规则层：IR（条件定理 = 规则，带 support）
   ▼
规则集 R
   │  ③ 预测：predict / intervene / counterfactual
   ▼
预测出的 Model
   │  ④ 导出：模态 = 投影（开放注册表）
   ▼
多模态结果
   │  ⑤ 误差：σ = inf E_W（裁决 K）
   ▼
残差 ──⑥ 闭环──→ 回到模型层
```

**判据不是「误差越小越好」，而是「误差 ≈ 噪声尺度 σ」。**
σ 不是可以调的目标值——定理 3.2 证明它被误差剖面的下确界**锁死**。

---

## 三个最反直觉的设计

### ① 误差以 σ 为准绳，不是越小越好

```
E_W(γ) := b(γ) + v(γ)                                    误差剖面（偏差 + 方差）
IsFitBoundary(E, σ, γ) := (E γ = σ) ∧ (∀ γ'. σ ≤ E γ')    拟合边界
```

**满足拟合边界的 σ 必然等于剖面的下确界**（`Modeling.Sigma.sigma_is_sInf`），
且任意两个满足边界的 σ 必然相等（`sigma_locked`）。

⟹ **σ 不是自由参数。** 把误差压到低于噪声尺度，是在拟合噪声本身。

### ② 底座是纯 CIC，经典数学是「假设」

```
┌ 经典外壳（可选）──────────────────────────────┐
│ propext / Classical.choice / Quot.sound       │ ← 这三条是**假设**，不是底座
│ → 得到 ℝ、Measure、拓扑                        │
├ 构造性核（纯 CIC，无任何假设）─────────────────┤
│ Term / Formula / Data / Judgment              │
│ 在此层证出的定理：support = ∅，status = proven │
└───────────────────────────────────────────────┘
```

配套铁律 **账实相符**：`#print axioms` 必须**等于** `support.assumptions`。
用了什么就登记什么，没登记的公理不允许出现。

### ③ 模型必须按因果组织

`Model = ⟨V, U, F, P_U⟩`（内生变量 / 外生变量 / 结构方程 / 外生律），
**一体化完整系统，不按模态拆**；模态只是**导出投影**。

**代价**：「图 ⟹ 概率」的桥成为必经之路——这是全设计最脆的地方。

---

## 快速开始

```powershell
git clone https://github.com/Lv-00-ANI/Fate-world-prediction.git
cd Fate-world-prediction

# 依赖：需要本机有 Mathlib（默认路径 D:/mathlib/packages/mathlib）
# 若路径不同，改 lakefile.toml 里的 [[require]] path

# ⚠ 必须禁用多线程，否则会撞 Mathlib 的 .olean 文件锁
$env:LEAN_NUM_THREADS='1'
lake build FateWorld
```

**预期**：`Build completed successfully`。首次构建约 5 小时（含 Mathlib 依赖 8,659 jobs）。

---

## 仓库结构

```
Fate-world-prediction/
├── FateWorld.lean            总入口（自动生成，import 全部 1105 个模块）
├── FateWorld/
│   ├── FateV2/               ★ 已验证实现层（254 模块）
│   │   ├── Core/                 构造性核（纯 CIC，零公理）
│   │   ├── Classical/            经典外壳（三条公理作假设）
│   │   ├── Bridge/               核 ↔ 外壳的账本桥
│   │   ├── Modeling/             第 0 层 · 数学建模（SCM / 因果图 / σ）
│   │   ├── Model/                第 1 层 · 状态 / 时间 / 拓扑序
│   │   ├── Rules/                第 2 层 · 规则（LawRule / FCA）
│   │   ├── Predict/              第 3 层 · 预测（do-演算 / 后门 / 反事实）
│   │   ├── Export/               第 4 层 · 导出（模态投影）
│   │   ├── Error/                第 5 层 · 误差（σ / 拟合边界）
│   │   ├── Loop/                 第 6 层 · 闭环（残差 / 回写 / 收敛）
│   │   ├── Meta/                 横切元层
│   │   └── Demo/                 可执行端到端演示
│   └── Legacy/               ★ 历史代码收容层（851 模块）
│       ├── Concrete/ Stage0/ Stage2/ _root/
│       └── *.lean                原样迁入，仅改 import 前缀
├── docs/                     文档层（入口 / 裁决 / 设计导读）
├── _inventory/               清单（迁移结果 / 待修缺陷 / 空壳补全）
└── _migration/               迁移过程记录与工具
```

### 两层的关系

| 层 | 模块 | 可信度 | 用途 |
|---|---:|---|---|
| **`FateV2/`** | 254 | **已验证**（门禁 10 项通过） | 正式开发的基础 |
| **`Legacy/`** | 851 | **仅保证可编译** | 历史代码收容，供查阅与升层 |

> ⚠️ **`Legacy/` 里的代码不得在未经验证的情况下被新代码引用。**
> 它不声称任何定理正确、任何设计有效。详见 [`_migration/迁移规则.md`](_migration/迁移规则.md)。

---

## 门禁（每批改动必须通过）

```powershell
cd 命运-v2      # 门禁脚本在上游目录，尚未迁入本仓库
powershell -ExecutionPolicy Bypass -File _gate.ps1
```

| # | 判据 | 当前 |
|---|---|---|
| G1 | `lake build` 通过 | ✅ |
| G2 | `sorry` / `admit` = 0 | ✅ |
| G3 | 自定义 `axiom` = 0 | ✅ |
| G4 | 核内定理 `#print axioms` = `[]` | ✅ |
| G5 | 外壳内 `#print axioms` ≡ `support.assumptions` | ✅ |
| G6 | 核内 `Quot` 零出现 | ✅ |
| G7 | `Core/` 不 import `Classical/` | ✅ |
| G8 | 每文件有迁移登记头 | ⚠️ 19 个文件缺失（已知项） |
| G9 | 只读区未被改动 | ✅ |

---

## 当前状态

| 项 | 状态 |
|---|---|
| 模块总数 | **1106**（FateV2 256 + Legacy 850） |
| 构建 | ✅ **1106 / 1106 全通过**（9765 jobs，零 error、零 sorryAx） |
| 可执行 demo | ✅ 五层端到端能跑出数值 |
| **空壳补全** | ✅ **15 / 15 完成**（220 个新声明） |
| 公理测绘 | ⬜ 未做（开发期按需逐个去除） |
| 真实数据接入 | ❌ 无数据 |

### 已补完的空壳（全部 15 个）

| 模块 | 内容 | 关键定理 |
|---|---|---|
| `Meta/ThreeKinds` | 三类陈述判据 | **`not_support_empty_implies_proven`**：「不需要公理」≠「已证」 |
| `Meta/Ledger` | 假设账本 | `axioms_are_entries`：三条公理是**账本条目**，不是底座 |
| `Meta/Gate` | 验收闸门 | `one_condition_insufficient`：D-001 双条件缺一不可 |
| `Meta/Domain` | 入域判据 | `seven_criteria` + N 组**不是**判据（类型隔离） |
| `Modeling/Sigma` | σ 的两条腿 | **`sigma_locked`**：σ 被误差剖面下确界锁死 |
| `Modeling/Noise` | 外生律载体 | `DiracNoise.isProb_toFin`：确定性是合法的退化分布 |
| `Modeling/Dissolve` | 数据消融 | `dissolve_archive_none`：归档数据不进定理 |
| `Modeling/Observation` | A14 分支 | `mode_total` + `HasSilentGap`：**「不得默认」变成类型约束** |
| `Rules/RuleSet` | 规则集 | `empty_support_subset`：加规则不可能让系统变干净 |
| `Rules/OperatorInstance` | 四算子实例 | `runOnSet_support_mono`：**管线不会减少来源** |
| `Predict/Intervene` | do 算子 | `do_ignores_parents`：干预**切断入边** |
| `Predict/Scenario` | 场景树与择优 | `foldl_score_ge_head` + 已知退化引用 |
| `Error/Resolution` | 分辨率预算 | `satisfiability_needs_extra_constant`：界**不是**预算 |
| `Classical/Shell` | 外壳代数 | `covers_mono` / `le_trans`：G5 的链条基础 |
| `Classical/Analysis` | 经典载体入口 | `carrier_axiom_cost`：用哪个载体就要登记哪三条 |

---

## 怎么继续开发

### 1. 先读这几份

| 你想… | 读 |
|---|---|
| 五分钟看懂项目 | [`docs/00-入口.md`](docs/00-入口.md) |
| 看代码怎么组织的 | [`docs/README.md`](docs/README.md) |
| 看迁移做了什么 | [`_inventory/迁移清单.md`](_inventory/迁移清单.md) |
| 看哪些还没实现 | [`_inventory/空壳补全登记.md`](_inventory/空壳补全登记.md) |
| 看已知缺陷 | [`_inventory/待修缺陷.csv`](_inventory/待修缺陷.csv) |
| 看迁移纪律 | [`_migration/迁移规则.md`](_migration/迁移规则.md) |

### 2. 上游权威文档（在本仓库之外）

| 主题 | 位置 |
|---|---|
| **作者裁决（24 条，最高权威）** | `../理论-文档/00-裁决台账/` |
| 系统总设计 | `../理论-文档/09-总设计/README.md` |
| σ 的完整数学 | `../理论-文档/08-拟合边界/` |
| 未裁决的分歧（9 条） | `../理论-文档/03-冲突登记/` |
| IR 完整设计 | `../理论-文档/07-IR设计/README.md` |

### 3. 下一步优先级

| 优先级 | 事项 | 依据 |
|---|---|---|
| ~~P0~~ | ~~补完空壳~~ | ✅ **已完成（15/15）** |
| **P0** | 迁移门禁脚本到本仓库 | 现在还要去 `命运-v2` 跑 |
| ~~P1~~ | ~~修 `G2Backdoor`~~ | ✅ **已完成** |
| **P1** | 公理测绘（批量 `#print axioms`） | 给开发期去除公理排优先级 |
| **P2** | 从 `Legacy` 升层有价值的模块 | 需逐个读，不能靠文件名判断 |
| **P3** | 接真实数据 | 阻塞于外部（暂无数据） |

---

## 三条硬边界

| # | 边界 | 说明 |
|---|---|---|
| **1** | `../命运-素材-原始文件-不可更改/` **只读** | 一个字节不动 |
| **2** | `../理论-文档/` **只读** | 不改不删 |
| **3** | **不删除任何文件** | 被替换的移入 `_archive/` |

---

## 技术债（如实登记）

| # | 债务 | 状态 |
|---|---|---|
| 1 | ~~`G2Backdoor` 引用不存在的 `Fate.R290`~~ | ✅ **已修复**（重写 §3，见 `_inventory/待修缺陷.csv`） |
| 2 | 19 个文件缺迁移登记头（G8 未过） | 机械项 |
| 3 | `Legacy/` 851 个模块未评估价值 | 需逐个读 |
| 4 | 门禁脚本仍在 `../命运-v2/` | 待迁入 |
| 5 | 并发构建撞 Mathlib olean 锁 | 用 `LEAN_NUM_THREADS=1` 规避 |
| 6 | `Formula` 无 `DecidableEq` | 互递归定义，无法自动导出 |
| 7 | `MainLoop` 不消费 `writeBack` 输出 | 最短闭合链最后一段仍是断的 |

---

*本仓库的任务是**把散乱的历史工程收敛成可继续开发的项目**——
不是重写理论，不是新设计。所有理论判断以上游 `理论-文档/` 为准。*
