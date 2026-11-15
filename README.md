# Fate-world-prediction

> **《命运》世界模型 / 预测系统的形式化工程仓库。**
>
> [![Lean](https://img.shields.io/badge/Lean-4.33.0--rc1-blue)](https://leanprover.github.io/)
> [![Modules](https://img.shields.io/badge/modules-1148-green)]()
> [![Build](https://img.shields.io/badge/build-passing-brightgreen)]()
> [![sorry](https://img.shields.io/badge/sorry-0-brightgreen)]()
>
> **远程**：https://github.com/Lv-00-ANI/Fate-world-prediction
> **构建状态**：`Build completed successfully (9765 jobs)` — 零 error、零 sorryAx

---

## 目录

- [这是什么](#这是什么)
- [核心设计](#核心设计)
- [快速开始](#快速开始)
- [仓库结构](#仓库结构)
- [证明组织](#证明组织)
- [文档体系](#文档体系)
- [当前状态](#当前状态)
- [下一步](#下一步)
- [维护约定](#维护约定)

---

## 这是什么

一个**世界模型 / 预测系统**的形式化实现。它把真实世界建模成结构因果模型，
从数据中抽取规则，用规则预测状态、干预与反事实，并把结果导出成多模态视图。

**核心主张**：判据不是「误差越小越好」，而是**「误差 ≈ 噪声尺度 σ」**。
σ 不是可调的目标值——它被误差剖面的下确界**锁死**（`sigma_locked`）。

**技术底座**：Lean 4 + Mathlib。构造性核（纯 CIC）之上，经典数学作为
**可审计的假设**引入，而不是默认拥有。

---

## 核心设计

### 主链路

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

### 三条关键设计

**① 误差以 σ 为准绳**

```
E_W(γ) := b(γ) + v(γ)                                    误差剖面（偏差 + 方差）
IsFitBoundary(E, σ, γ) := (E γ = σ) ∧ (∀ γ'. σ ≤ E γ')    拟合边界
```

满足拟合边界的 σ 必然等于剖面的下确界（`sigma_is_sInf`），
且任意两个满足边界的 σ 必然相等（`sigma_locked`）。
**把误差压到低于噪声尺度，是在拟合噪声本身。**

**② 底座纯 CIC，经典数学是假设**

```
┌ 经典外壳（可选）──────────────────────────────┐
│ propext / Classical.choice / Quot.sound       │ ← 三条是**假设**，不是底座
│ → 得到 ℝ、Measure、拓扑                        │
├ 构造性核（纯 CIC，无任何假设）─────────────────┤
│ Term / Formula / Data / Judgment              │
│ 在此层证出的定理：support = ∅，status = proven │
└───────────────────────────────────────────────┘
```

配套铁律 **账实相符**：`#print axioms` 必须**等于** `support.assumptions`。

**③ 模型按因果组织**

`Model = ⟨V, U, F, P_U⟩`（内生变量 / 外生变量 / 结构方程 / 外生律），
一体化完整系统，不按模态拆；模态只是导出投影。

---

## 快速开始

### 环境要求

| 项 | 版本 / 路径 |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc1` |
| Mathlib | 默认 `D:/mathlib/packages/mathlib`（在 `lakefile.toml` 中配置） |

若 Mathlib 在别处，修改 `lakefile.toml` 的 `[[require]] path`。

### 构建

```powershell
git clone https://github.com/Lv-00-ANI/Fate-world-prediction.git
cd Fate-world-prediction

# ⚠ 必须禁用多线程，否则会撞 Mathlib 的 .olean 文件锁
$env:LEAN_NUM_THREADS='1'

lake build FateWorld
```

**预期输出**：

```
Build completed successfully (9765 jobs)
```

首次构建约 5 小时（含 Mathlib 依赖）。增量构建很快（缓存复用）。

### 只构建某个模块

```powershell
lake build FateWorld.FateV2.Meta.ThreeKinds
lake build FateWorld.Legacy.BackdoorWithM
```

### 检查公理依赖

```powershell
# 写一个探针文件
@"
import FateWorld.FateV2.Modeling.Sigma
#print axioms FateV2.Modeling.sigma_locked
"@ | Out-File -Encoding utf8 probe.lean
lake env lean probe.lean
```

---

## 仓库结构

```
Fate-world-prediction/
├── README.md                  ← 本文件
├── FateWorld.lean             ← 总入口（import 全部 1106 模块）
├── lakefile.toml              ← 构建配置
├── lean-toolchain             ← 工具链版本
├── FateWorld/
│   ├── FateV2/                ★ 已验证实现层（254 模块）
│   └── Legacy/                ★ 历史收容层（851 模块）
├── docs/                      ← 文档体系（见下）
├── _inventory/                ← 清单（分类表 / 缺陷登记 / 空壳补全）
└── _migration/                ← 迁移记录与规则
```

### 两层的关系

| 层 | 模块 | 可信度 | 用途 |
|---|---:|---|---|
| **`FateV2/`** | 296 | **已验证**（门禁 10 项通过） | 正式开发的基础 |
| **`Legacy/`** | 851 | **仅保证可编译** | 历史代码收容，供查阅 |

> ⚠ **`Legacy/` 里的代码不得在未经验证的情况下被新代码引用。**
> 它不声称任何定理正确、任何设计有效。

**实测事实**：722 个只在 `Legacy` 的模块**完全不引用** `FateV2` 的任何模块。
⟹ 两套代码是**平行**的，不是继承关系。

---

## 证明组织

全部 1106 个模块按**证明主题**编入索引：**[`docs/证明架构索引.md`](docs/证明架构索引.md)**

### FateV2 层（按总设计分层）

| 层 | 模块 | 职责 |
|---|---:|---|
| `Core/` | 34 | 构造性核：IR 语法、判断、四算子、声明图、缓存、反射 |
| `Classical/` | 3 | 经典外壳：三条公理作假设、载体入口 |
| `Bridge/` | 3 | 核 ↔ 外壳的账本桥 |
| `Modeling/` | 18 | 第 0 层：数学建模（SCM、因果图、σ、观测、消融） |
| `Model/` | 12 | 第 1 层：状态、时间、拓扑序 |
| `Rules/` | 13 | 第 2 层：规则（LawRule、FCA、算子实例） |
| `Predict/` | 49 | 第 3 层：预测、干预、反事实、场景树 |
| `Export/` | 5 | 第 4 层：模态投影与导出 |
| `Error/` | 65 | 第 5 层：σ、拟合边界、判据、分辨率 |
| `Loop/` | 33 | 第 6 层：残差、回写、收敛、世界模型总装 |
| `Meta/` | 5 | 横切元层：三类陈述、入域、账本、闸门 |
| `Demo/` | 11 | 可执行端到端演示 |
| `Data/` | 1 | 数据接入 |

### Legacy 层（按证明主题分类）

对 722 个只在 Legacy 的模块按**文件头内容**分类（不看文件名）：

| 主题 | 模块 | 定理 |
|---|---:|---:|
| 因果推断 | 255 | 3,436 |
| 规则与 FCA | 153 | 2,154 |
| 桥与接线 | 107 | 673 |
| 误差与拟合 | 106 | 1,039 |
| 闭环与世界模型 | 37 | 454 |
| IR 与语法 | 15 | 156 |
| 未分类 | 49 | 508 |

**完整清单**：[`_inventory/Legacy分类.csv`](_inventory/Legacy分类.csv)

---

## 文档体系

**入口**：[`docs/README.md`](docs/README.md)

| 我想… | 读 |
|---|---|
| 找一个具体证明 | [`docs/证明架构索引.md`](docs/证明架构索引.md) |
| 看作者拍板了什么 | [`docs/archive/00-裁决台账/`](docs/archive/00-裁决台账/)（24 条） |
| 看系统总设计 | [`docs/archive/09-总设计/README.md`](docs/archive/09-总设计/README.md) |
| 看 σ 的完整数学 | [`docs/archive/08-拟合边界/`](docs/archive/08-拟合边界/) |
| 看未裁决的分歧 | [`docs/archive/03-冲突登记/`](docs/archive/03-冲突登记/)（9 条） |
| 查已知缺陷 | [`_inventory/待修缺陷.csv`](_inventory/待修缺陷.csv) |

### 归档完整性

上游 `理论-文档/` 的 **254 个文件已逐字节迁入** `docs/archive/`：

| 项 | 结果 |
|---|---|
| 文件数 | 254 / 254 |
| SHA-256 一致 | **全部一致** |
| 差异 | **0** |

**文档信息零丢失。** 详见 [`docs/_归档说明.md`](docs/_归档说明.md)。

---

## 当前状态

| 项 | 状态 |
|---|---|
| 模块总数 | **1148**（FateV2 296 + Legacy 851 + 入口 1） |
| 构建 | ✅ **1148 / 1148 全通过**（9765 jobs，零 error、零 sorryAx） |
| 可执行 demo | ✅ 五层端到端能跑出数值 |
| 空壳补全 | ✅ **15 / 15 完成**（220 个新声明） |
| 文档归档 | ✅ 254 文件零差异 |
| **收容层迁移** | ✅ **42 / 42 目标模块已迁入**（见 `_inventory/收容层迁移登记.md`） |
| 证明索引 | ✅ 已建立 |
| 公理测绘 | ⬜ 未做 |
| 真实数据接入 | ❌ 无数据 |

### 已完成的新写（15 个空壳）

| 模块 | 内容 | 关键定理 |
|---|---|---|
| `Meta/ThreeKinds` | 三类陈述判据 | `not_support_empty_implies_proven`：「不需要公理」≠「已证」 |
| `Meta/Ledger` | 假设账本 | `axioms_are_entries`：三条公理是**账本条目**，不是底座 |
| `Meta/Gate` | 验收闸门 | `one_condition_insufficient`：双条件缺一不可 |
| `Meta/Domain` | 入域判据 | `seven_criteria` + N 组**不是**判据（类型隔离） |
| `Modeling/Sigma` | σ 的两条腿 | **`sigma_locked`**：σ 被误差剖面下确界锁死 |
| `Modeling/Noise` | 外生律载体 | `DiracNoise.isProb_toFin`：确定性是合法的退化分布 |
| `Modeling/Dissolve` | 数据消融 | `dissolve_archive_none`：归档数据不进定理 |
| `Modeling/Observation` | A14 分支 | `mode_total`：「不得默认」变成类型约束 |
| `Rules/RuleSet` | 规则集 | `empty_support_subset`：加规则不可能让系统变干净 |
| `Rules/OperatorInstance` | 四算子实例 | `runOnSet_support_mono`：管线不会减少来源 |
| `Predict/Intervene` | do 算子 | `do_ignores_parents`：干预**切断入边** |
| `Predict/Scenario` | 场景树与择优 | `foldl_score_ge_head` + 已知退化引用 |
| `Error/Resolution` | 分辨率预算 | `satisfiability_needs_extra_constant`：界**不是**预算 |
| `Classical/Shell` | 外壳代数 | `covers_mono` / `le_trans`：账实相符的链条基础 |
| `Classical/Analysis` | 经典载体入口 | `carrier_axiom_cost`：用哪个载体就要登记哪三条 |

---

## 下一步

| 优先级 | 事项 | 依据 |
|---|---|---|
| **P0** | 公理测绘：批量 `#print axioms`，生成可信度地图 | 给开发期去除公理排优先级 |
| **P1** | 门禁脚本迁入本仓库 | 现在还在上游目录 |
| **P1** | `Legacy` 49 个未分类模块（508 定理）逐个定性 | 需读正文，不能靠文件名 |
| **P2** | 从 `Legacy` 升层有价值的模块 | 需逐个验证 |
| **P3** | 接真实数据 | 阻塞于外部（暂无数据） |

---

## 维护约定

| 约定 | 说明 |
|---|---|
| **构建必须单线程** | `$env:LEAN_NUM_THREADS='1'`，否则撞 Mathlib olean 锁 |
| **`.lean` 文件必须无 BOM** | 否则 Lean 报 `1:0 expected token` |
| **`archive/` 只读** | 上游原文不改；要订正就在 `docs/` 顶层新建文件 |
| **数字必须带口径** | 任何「多少条/多少份」都要能复现 |
| **不引入 `sorry` / `axiom`** | 当前全库零 `sorryAx` |
| **不开源协议** | 按项目方要求，暂不添加 LICENSE 文件 |

---

## 技术债（如实登记）

| # | 债务 | 状态 |
|---|---|---|
| 1 | ~~`G2Backdoor` 引用不存在的 `Fate.R290`~~ | ✅ **已修复**（重写 §3） |
| 2 | 19 个文件缺迁移登记头 | 机械项 |
| 3 | `Legacy` 851 个模块未评估价值 | 需逐个读 |
| 4 | 门禁脚本仍在 `../命运-v2/` | 待迁入 |
| 5 | `MainLoop` 不消费 `writeBack` 输出 | 最短闭合链最后一段仍是断的 |
| 6 | `Formula` 无 `DecidableEq` | 互递归定义，无法自动导出 |

---

*本仓库的任务是**把散乱的历史工程收敛成可继续开发的项目**——
不是重写理论，不是新设计。所有理论判断以 `docs/archive/` 中的原始裁决为准。*
