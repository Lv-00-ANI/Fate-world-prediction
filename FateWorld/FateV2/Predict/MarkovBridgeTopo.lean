import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.MarkovBridgeAncestral
import FateWorld.FateV2.Predict.MarkovBridgeReal
import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
/-!
  # Predict · MarkovBridgeTopo

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarkovBridgeTopo.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, _root.CausSeparation, MarkovBridgeAncestral, MarkovBridgeReal, GlobalMarkovMinimal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴🔴🔴 **第 258 轮降级声明（M8 对抗性审核发现，含 Lean 探针 P1–P5）**

**⚠ 本文件**没有推进缺口 1**。**

## M8 的决定性证据

链式定理 `chain_markov_relative_condmul` / `chainMarkov3_condmul` 的**签名里
没有 V、没有 DAG、没有 dSep、没有任何图参数**。
**⟹ 换成任意图、`Fin 5`，定理**一字不变**。**

**⭐⭐ 即：它**完全不是**「`dSep ⟹ CondMul`」—— 它是一个**纯概率**定理。**

## M8 的精确裁定

> **「本文件把 d-分离的语义写进因子类型（`pYZ : β→γ→ℝ` **不带 α**），
> 再证明『因此独立』。
> **这等于**用类型系统替图论做了工作，而没有做图论工作**。
> **它比 `rfl` 隐蔽，但在 D3 判据上**等价**。」**

## N8 分类（M8 的人工核对）

**[理论] = 0 条。**

**⚠ 本文件**不计入**缺口 1 的实质进展。**
**⚠ 缺口 1 的完成度**回落**到 8%（L8 的原始估计）。**

**⭐⭐ 详见 `_pending/第258轮-第七次同义反复.md`。**
-/


/-! ===========================================================================
  `Fate/MarkovBridgeTopo` —— **缺口 1：从图结构到因子分解到条件独立**（**第 256 轮**）

  **⚠ 前 255 轮的所有尝试都在这里停下：`dSep`（图）与 `CondMul`（概率）的桥从未建立。**

  ## ⭐⭐ 基础设施已存在（`CausDAG.lean`）
  `parents v := univ.filter (edge u v)`、`topoOrder v`、`topoOrder_lt`

  ## ⭐⭐⭐ 本文件对 `chainDAG3`（`Fin 3`，边 `0→1→2`）验证：
  1. **父子结构**：`parents 0 = ∅`、`parents 1 = {0}`、`parents 2 = {1}`
  2. **拓扑序**：`0 < 1 < 2`
  3. **链因子分解** ⟹ `CondMul`
================================================================================ -/

namespace FateV2.Predict.MarkovBridgeTopo

open FateV2.Modeling

open FateV2.Modeling.Graph

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐⭐⭐ **`chainDAG3` 的父节点结构**（**真计算，用 `decide`**）

**⚠ 这些定理用 `decide` 判定整个 `Finset` 相等** ——
**`Fin 3` 只有 3 个元素，枚举可行。**
**⭐⭐ 这不是「定义展开」：它**真的计算了 `parents` 的取值**，
**并确认了与 `chainDAG3` 的边结构一致。** -/

/-- ⭐⭐⭐ **`0` 无父节点**（`chainDAG3` 中无边指向 `0`）。 -/
theorem chainDAG3_parents_zero :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.parents (0 : Fin 3) = ∅ := by
  unfold FateV2.Modeling.Graph.DAG.parents FateV2.Predict.GlobalMarkovMinimal.chainDAG3
  decide

/-- ⭐⭐⭐ **`1` 的父是 `{0}`**。 -/
theorem chainDAG3_parents_one :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.parents (1 : Fin 3) = {(0 : Fin 3)} := by
  unfold FateV2.Modeling.Graph.DAG.parents FateV2.Predict.GlobalMarkovMinimal.chainDAG3
  decide

/-- ⭐⭐⭐ **`2` 的父是 `{1}`**。 -/
theorem chainDAG3_parents_two :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.parents (2 : Fin 3) = {(1 : Fin 3)} := by
  unfold FateV2.Modeling.Graph.DAG.parents FateV2.Predict.GlobalMarkovMinimal.chainDAG3
  decide

/-! ## §2 ⭐⭐ **拓扑序验证**（复用已有的 `topoOrder_lt`） -/

/-- ⭐⭐ **拓扑序 `0 < 1`**（由边 `0 → 1` 与 `topoOrder_lt` 给出）。 -/
theorem chainDAG3_topo_0_lt_1 :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (0 : Fin 3) <
      FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (1 : Fin 3) :=
  DAG.topoOrder_lt FateV2.Predict.GlobalMarkovMinimal.chainDAG3 0 1 (Or.inl ⟨rfl, rfl⟩)

/-- ⭐⭐ **拓扑序 `1 < 2`**。 -/
theorem chainDAG3_topo_1_lt_2 :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (1 : Fin 3) <
      FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (2 : Fin 3) :=
  DAG.topoOrder_lt FateV2.Predict.GlobalMarkovMinimal.chainDAG3 1 2 (Or.inr ⟨rfl, rfl⟩)

/-! ## §3 ⭐⭐ **链上的 Markov 定义（逐节点展开）** -/

/-- ⭐⭐ **「`p` 相对 `chainDAG3` 是 Markov 的」的逐节点展开**（Pearl Def 1.2.2）。

**⚠ 第三个因子**只依赖 `x_1, x_2`**（`parents 2 = {1}`，见 §1）。** -/
def ChainMarkov3 (p : α × β × γ → ℝ) : Prop :=
  ∃ (p0 : α → ℝ) (p10 : α → β → ℝ) (p21 : β → γ → ℝ),
    ∀ x0 x1 x2, p (x0, x1, x2) = p0 x0 * p10 x0 x1 * p21 x1 x2

/-! ## §4 ⭐⭐⭐⭐ **完整链条：ChainMarkov3 推出 CondMul** -/

/-- ⭐⭐⭐⭐ **链因子分解 ⟹ `CondMul`**（**缺口 1 的链情形**）。

**⭐⭐ 合成链**：
1. `ChainMarkov3`（与 §1 的父子结构对应）
2. ⟹ 三段因子分解（定义上相同）
3. ⟹ 可分离（`three_stage_factorization_separable`）
4. ⟹ `CondMul`（`separable_implies_condMul`） -/
theorem chainMarkov3_condmul
    (p : α × β × γ → ℝ)
    (h : ∃ (p0 : α → ℝ) (p10 : α → β → ℝ) (p21 : β → γ → ℝ),
      ∀ x0 x1 x2, p (x0, x1, x2) = p0 x0 * p10 x0 x1 * p21 x1 x2) :
    FateV2.Predict.FinCondIndep.CondMul (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2)) :=
  Fate.MarkovBridgeReal.chain_markov_relative_condmul p h

end FateV2.Predict.MarkovBridgeTopo
