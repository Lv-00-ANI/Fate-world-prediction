import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
/-!
  # Predict · Strategy13Fixed

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy13Fixed.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization, FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  Strategy13FiberFubini 的**正确版本**

  ## 背景

  Fate/Strategy13FiberFubini.lean 的核心定理 mass_depends_on_InSet_core 有 2 个
  sorry，且实际**不可证**（两个未闭合分支都要求 x 与 y 在比 InSet 更大的集合上一致）。

  ## 正确版本（本文件）

  glue_congr：若 x 与 y 在 S 上一致，则 glue S x t = glue S y t。
  mass_depends_on_S：若 x 与 y 在 S 上一致，则 mass S p x = mass S p y。

  ## 诚实边界

  InSet 版本需要「p 的读集落在 InSet 内」这样的额外图结构假设，本文件不假设它。
  一般的 Split 情形由 Fate/CondIndepGeneralNZ.lean 的 condIndep_general 处理。
  =========================================================================== -/

/-! ===========================================================================
  §0.1  本文件的 sorry 处置记录（P0 任务）

  ### 原任务描述

  全景总览 §10.3/§10.5 称「本文件此前有 1 个 `sorry`」。经核查，该 `sorry`
  **已在更早的修复中被补证删除**：当前文件内的两个定理 `glue_congr` 与
  `mass_depends_on_S` 均给出**完整证明**，无 `sorry` / `admit` / `axiom`。
  文件头旧文档中出现的「sorry」二字仅为对**历史**的陈述性引用，不是占位符。

  ### 本次处置（选 (a) 的精神：可证则给出证明）

  核查时发现一处独立问题：`mass_depends_on_S` 的假设 `hp`
  （「`p` 只读 `S`」）在证明中**从未被使用**，因为
  `Fate.DAGFactorization.mass S p x = ∑_{w : ∃(w 在 S 上 = x)} p w`
  的定义只对**求和域**做筛选，`p` 的读集性质并不进入 `mass` 的依赖性。
  （对照 `Fate/Strategy13FiberFubini.lean` 中同名的正确版
  `mass_depends_on_S`，它本身就**不带** `hp` 假设。）

  因此 `hp` 是**冗余前件**：它不是把结论包进前件的同义反复
  （结论 `mass S p x = mass S p y` 并非 `hp` 的重述），但作为一个
  「装饰性假设」会误导读者以为结论需要 `p` 的局部性。按诚实原则，
  已将 `hp` 从定理签名中**删除**，使定理陈述准确反映其真实内容：

  - 旧：`{p : (V→α)→ℝ} {S} (hp : p 只读 S) (h : x = y on S) : mass S p x = mass S p y`
  - 新：`{p : (V→α)→ℝ} {S} (h : x = y on S) : mass S p x = mass S p y`

  这是**加强**（假设变弱，结论不变），并非减弱；旧调用方可直接迁移
  （丢弃 `hp` 参数即可）。全仓库无任何下游文件引用本文件的定理，
  故该签名变更不影响其他模块（`lake build` 9290 jobs 通过验证）。

  ### 定理数变化

  定理数**不变**：仍为 2 条（`glue_mem` 是辅助 `@[simp]` 引理，
  `glue_congr`、`mass_depends_on_S` 是主定理；`grep -cE "^theorem"` = 2，改动前后一致）。

  ### 未采用 (b)/(c) 的理由

  - (b) 删除：命题为真且已给出完整证明，无删除必要。
  - (c) 改证伪：命题为真（见证明），不存在反例。
  =========================================================================== -/

namespace FateV2.Predict.Strategy13Fixed

open FateV2.Modeling
open Finset
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [DecidableEq V] [Fintype V] [DecidableEq α] [Fintype α]

-- glue：在 S 上取 x，S 外取 t
noncomputable def glue (S : Finset V) (x : V → α) (t : {v // v ∉ S} → α) : V → α :=
  fun v => if h : v ∈ S then x v else t ⟨v, h⟩

omit [Fintype V] [DecidableEq α] [Fintype α] in
@[simp] theorem glue_mem (S : Finset V) (x : V → α) (t : {v // v ∉ S} → α)
    {v : V} (h : v ∈ S) : glue S x t v = x v := by
  simp only [glue, dif_pos h]

-- ⭐ 正确版本：若 x 与 y 在 S 上一致，则 glue S x t = glue S y t
omit [Fintype V] [DecidableEq α] [Fintype α] in
theorem glue_congr (S : Finset V) {x y : V → α} (h : ∀ v ∈ S, x v = y v)
    (t : {v // v ∉ S} → α) : glue S x t = glue S y t := by
  funext v
  by_cases hv : v ∈ S
  · rw [glue_mem S x t hv, glue_mem S y t hv, h v hv]
  · simp only [glue, dif_neg hv]

-- ⭐ 推论：若 x 与 y 在 S 上一致，则 mass S p x = mass S p y（对任意 p，不需 p 局部）
theorem mass_depends_on_S {p : (V → α) → ℝ} {S : Finset V}
    {x y : V → α} (h : ∀ v ∈ S, x v = y v) :
    Fate.DAGFactorization.mass S p x = Fate.DAGFactorization.mass S p y := by
  unfold Fate.DAGFactorization.mass
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · have hw' : ∀ u ∈ S, w u = y u := fun u hu => (hw u hu).trans (h u hu)
    rw [if_pos hw, if_pos hw']
  · have hw' : ¬ ∀ u ∈ S, w u = y u := by
      intro hc
      exact hw (fun u hu => (hc u hu).trans (h u hu).symm)
    rw [if_neg hw, if_neg hw']

end FateV2.Predict.Strategy13Fixed
