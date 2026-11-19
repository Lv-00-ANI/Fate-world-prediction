import FateWorld.FateV2.Predict.MainTheoremCFinal
import Mathlib.Tactic.Ring

/-!
  # Modeling · CondIndepEmptyZ

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CondIndepEmptyZ.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MainTheoremCFinal
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  主定理 C 的**最终组装**（`Z = ∅`）：`condIndep_emptyZ`

  ## 目标

  ```lean
  theorem condIndep_emptyZ (ψ) (p)
      (hfac   : ∀ w, p w = ∏ v, ψ v w)          -- 单点因子分解
      (hread  : ReadSet ψ R)                     -- 读集约束
      (hsplit : Split R X Y ∅)                   -- 因子图分离（无超边横跨 X/Y）
      (hXY    : Disjoint X Y)
      (hne    : ∀ v, (R v).Nonempty)             -- 读集非空
      (hcover : X ∪ Y = univ) :                  -- 无尾块
      CondIndep p X Y ∅
  ```

  ## 依赖（全部已证，零 `sorry`）

  | 构件 | 出处 |
  |---|---|
  | `Wblk`、`mem_Wblk`、`Wblk_union_univ`、`Wblk_inter_empty`、`Wblk_empty` | 本文件 §0.1 本地重建（同 `MainTheoremCFinalSplit.lean` §0.1，**因 staging 模块不可 `import`**）|
  | `mass_prod_cover`、`mass_prod_cover_all` | `Fate/MassProCover.lean` |
  | `mass_univ`、`mass` | `Fate/DAGFactorization.lean` |
  | `sum_mul_sep_final`、`toV`、`toV_mem_X`、`toV_mem_Y` | `Fate/SumMulSepFull.lean` |
  | `glue`、`glue_of_mem`、`glue_of_not_mem`、`mass_eq_sum_glue` | `Fate/View19FactorGraphSplit.lean` |
  | `mass_one_card` | `Fate/BalanceComponents.lean` |

  本文件新增（"装配件"，均在本文件内证明；另含 §0.1 的 `Wblk` 本地重建）：

  * `Wblk_disjoint_nonempty` —— `W_X` 与 `W_Y` 不交（需 `hne`）
  * `Wblk_prod_partition` —— `∏_{W_X} · ∏_{W_Y} = ∏_V · ∏_{W_∅}`
  * `mass_X_form` / `mass_Y_form` —— 从 `mass X` 中提出 `W_X` 的因子
  * `mass_X_eq_sum_Y` / `mass_Y_eq_sum_X` —— `mass` 重指标到 `toV` 形式
  * `condIndep_emptyZ` —— 最终组装

  ## ⚠ 前提的真实性（诚实边界）

  * **`hne : ∀ v, (R v).Nonempty` 必需**：`W_X ∩ W_Y = W_∅`，而 `W_∅ = {v | R v = ∅}`。
    若某 `R v = ∅`，则该因子同时计入 `W_X` 与 `W_Y`，`∏_{W_X} · ∏_{W_Y}` 会
    **重复计数**，`Wblk_prod_partition` 的配平不成立。
  * **`hcover : X ∪ Y = univ` 必需**：否则 `mass (X∪Y)` 不退化成 `p x`，
    `|α|` 的指数无法配平（`card_balance` 需要在 `Z = ∅` 时仍满足
    `|X∪Y| = |V|`）。
  * **`[Nonempty α]` 必需**（形式化基础设施的副作用，**不削弱结论**）：
    1. `toV` / `sum_mul_sep_final`（`Fate/SumMulSepFull.lean`）的变量块固定要求
       `[Nonempty α]`，且 `sum_mul_sep_final` 内部使用 `Classical.arbitrary (↥Y → α)`；
    2. `mass_one_card`（`Fate/BalanceComponents.lean`）同属要求 `[Nonempty α]` 的块。
    **为何不削弱**：`CondIndep` 的陈述是 `∀ x : V → α, …`；若 `α` 为空而 `V` 非空，
    则 `V → α` 为空集，结论**空洞为真**。故唯一被排除的退化情形中结论自动成立。
  =========================================================================== -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FateV2.Predict.GraphToProbView7

open FateV2.Predict

open Finset
open FateV2.Error
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov
open FateV2.Predict.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ===========================================================================
  §0.1  `Wblk`（本地重建）

  `Fate_agent_staging/` **不是 lake 模块根**（`lakefile.lean` 的 `lean_lib` 只含
  `Fate` 等根），故 staging 里的 `Wblk` 无法被 `import`。这里**逐字重建**同一份
  定义与引理，保证本文件只依赖 `Fate/` 且可独立编译。
  =========================================================================== -/

/-- `Wblk R S`：读集被 `S` 覆盖的全部因子。 -/
noncomputable def Wblk (R : V → Finset V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => R v ⊆ S)

theorem mem_Wblk {R : V → Finset V} {S : Finset V} {v : V} :
    v ∈ Wblk R S ↔ R v ⊆ S := by
  unfold Wblk
  simp

/-- `Split R X Y ∅` ⟹ `W_X ∪ W_Y = univ`。 -/
theorem Wblk_union_univ {R : V → Finset V} {X Y : Finset V}
    (hsplit : FateV2.Predict.View19.Split R X Y (∅ : Finset V)) :
    Wblk R X ∪ Wblk R Y = (Finset.univ : Finset V) := by
  have hcov : ∀ v, R v ⊆ X ∨ R v ⊆ Y := split_emptyZ_covers hsplit
  ext v
  simp only [Wblk, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  rcases hcov v with h | h
  · exact Or.inl h
  · by_cases h' : R v ⊆ X
    · exact Or.inl h'
    · exact Or.inr h

/-- `X`、`Y` 不交 ⟹ `W_X ∩ W_Y = W_∅`。 -/
theorem Wblk_inter_empty {R : V → Finset V} {X Y : Finset V} (hXY : Disjoint X Y) :
    Wblk R X ∩ Wblk R Y = Wblk R (∅ : Finset V) := by
  ext v
  rw [Finset.mem_inter, mem_Wblk, mem_Wblk, mem_Wblk]
  rw [← Finset.subset_inter_iff]
  rw [Finset.disjoint_iff_inter_eq_empty.mp hXY]

/-- `W_∅` 的显式形态：读集为空的因子。 -/
theorem Wblk_empty (R : V → Finset V) :
    Wblk R (∅ : Finset V) = Finset.univ.filter (fun v => R v = ∅) := by
  unfold Wblk
  congr 1
  funext v
  apply propext
  exact Finset.subset_empty

/-! ===========================================================================
  §1  `Wblk` 的两块不交（需 `hne`）
  =========================================================================== -/

/-- ⭐⭐ **`W_X` 与 `W_Y` 不交**：`X`、`Y` 不交且每个读集非空。

**证明**：若 `v ∈ W_X ∩ W_Y`，则 `R v ⊆ X ∩ Y = ∅`，与 `hne v`（有元素）矛盾。 -/
theorem Wblk_disjoint_nonempty {R : V → Finset V} {X Y : Finset V} (hXY : Disjoint X Y)
    (hne : ∀ v, (R v).Nonempty) : Disjoint (Wblk R X) (Wblk R Y) := by
  refine Finset.disjoint_left.mpr fun v hx hy => ?_
  rw [mem_Wblk] at hx hy
  obtain ⟨u, hu⟩ := hne v
  exact Finset.disjoint_left.mp hXY (hx hu) (hy hu)

/-- ⭐⭐ **`W_∅` 为空**（需 `hne`）。 -/
theorem Wblk_empty_eq_empty {R : V → Finset V} (hne : ∀ v, (R v).Nonempty) :
    Wblk R (∅ : Finset V) = ∅ := by
  rw [Wblk_empty, Finset.filter_eq_empty_iff]
  intro v _ hR
  obtain ⟨u, hu⟩ := hne v
  rw [hR] at hu
  exact absurd hu (by simp)

/-! ===========================================================================
  §2  `mass_X_form` / `mass_Y_form`

  从 `mass X ((∏ v, ψ v) * g)` 中把 `W_X` 上的因子整体提出（它们读集 `⊆ X`），
  剩余部分仍是一个 `mass X`。
  =========================================================================== -/

/-- ⭐⭐ **`mass_X_form`**：`W_X` 的因子可从 `mass X` 中提出。 -/
theorem mass_X_form (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    (X : Finset V) (g : (V → α) → ℝ) (x : V → α) :
    mass X (fun w => (∏ v, ψ v w) * g w) x
      = (∏ v ∈ Wblk R X, ψ v x)
        * mass X (fun w => (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ X)), ψ v w) * g w) x := by
  classical
  have hsplit1 : ∀ w : V → α, (∏ v, ψ v w)
      = (∏ v ∈ Wblk R X, ψ v w)
        * (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ X)), ψ v w) := by
    intro w
    rw [show Wblk R X = Finset.univ.filter (fun v => R v ⊆ X) from rfl]
    rw [Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => R v ⊆ X) (fun v => ψ v w)]
  have hfun : (fun w => (∏ v, ψ v w) * g w)
      = (fun w => (∏ v ∈ Wblk R X, ψ v w)
          * ((∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ X)), ψ v w) * g w)) := by
    funext w
    rw [hsplit1 w]
    ring
  rw [hfun]
  exact mass_prod_cover ψ hread (Wblk R X) (fun v hv => mem_Wblk.mp hv)
    (fun w => (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ X)), ψ v w) * g w) x

/-- ⭐⭐ **`mass_Y_form`**：与 `mass_X_form` 对称。 -/
theorem mass_Y_form (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    (Y : Finset V) (g : (V → α) → ℝ) (x : V → α) :
    mass Y (fun w => (∏ v, ψ v w) * g w) x
      = (∏ v ∈ Wblk R Y, ψ v x)
        * mass Y (fun w => (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) * g w) x := by
  classical
  have hsplit1 : ∀ w : V → α, (∏ v, ψ v w)
      = (∏ v ∈ Wblk R Y, ψ v w)
        * (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) := by
    intro w
    rw [show Wblk R Y = Finset.univ.filter (fun v => R v ⊆ Y) from rfl]
    rw [Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => R v ⊆ Y) (fun v => ψ v w)]
  have hfun : (fun w => (∏ v, ψ v w) * g w)
      = (fun w => (∏ v ∈ Wblk R Y, ψ v w)
          * ((∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) * g w)) := by
    funext w
    rw [hsplit1 w]
    ring
  rw [hfun]
  exact mass_prod_cover ψ hread (Wblk R Y) (fun v hv => mem_Wblk.mp hv)
    (fun w => (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) * g w) x

/-! ===========================================================================
  §3  乘积配分
  =========================================================================== -/

/-- ⭐⭐⭐ **乘积配分**：`X`、`Y` 不交且 `Split R X Y ∅` 时，
`∏_{W_X} · ∏_{W_Y} = ∏_V · ∏_{W_∅}`。

**证明**：`W_X ∪ W_Y = univ`（`Wblk_union_univ`）、`W_X ∩ W_Y = W_∅`（`Wblk_inter_empty`），
再用 `Finset.prod_union_inter`。 -/
theorem Wblk_prod_partition {R : V → Finset V} (ψ : V → (V → α) → ℝ)
    {X Y : Finset V} (hsplit : FateV2.Predict.View19.Split R X Y (∅ : Finset V))
    (hXY : Disjoint X Y) (w : V → α) :
    (∏ v ∈ Wblk R X, ψ v w) * (∏ v ∈ Wblk R Y, ψ v w)
      = (∏ v, ψ v w) * (∏ v ∈ Wblk R (∅ : Finset V), ψ v w) := by
  have hunion := Wblk_union_univ (R := R) hsplit
  have hinter := Wblk_inter_empty (R := R) hXY
  have key := Finset.prod_union_inter (s₁ := Wblk R X) (s₂ := Wblk R Y)
    (f := fun v => ψ v w)
  rw [hinter, hunion] at key
  rw [← key]

/-! ===========================================================================
  §4  `mass X` / `mass Y` 的重指标（到 `toV` 形式）

  目标：`mass X f x = Σ_{b : Y → α} f (toV X Y hY (x|_X) b)`。

  手段：`mass_eq_sum_glue`（`Fate/View19FactorGraphSplit.lean`）把 `mass` 写成
  `Sᶜ` 上的一次求和，再沿函数层双射 `{u // u ∉ X} → α ≃ (Y → α)` 换元。

  **⚠ 需要 `X ∪ Y = univ`（`hcover`）与 `Disjoint X Y`（`hXY`）** —— 缺一个
  双射就不成立。
  =========================================================================== -/

section Reindex

variable [Nonempty α]

/-- 若 `X ∪ Y = univ` 且 `X`、`Y` 不交，则 `u ∈ Y ↔ u ∉ X`。 -/
theorem mem_Y_iff_not_mem_X {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V)) (u : V) : u ∈ Y ↔ u ∉ X := by
  constructor
  · intro hu hx
    exact Finset.disjoint_left.mp hXY hx hu
  · intro hu
    have h : u ∈ X ∪ Y := by rw [hcover]; exact Finset.mem_univ u
    rcases Finset.mem_union.mp h with h' | h'
    · exact absurd h' hu
    · exact h'

/-- 若 `X ∪ Y = univ` 且 `X`、`Y` 不交，则 `u ∈ X ↔ u ∉ Y`。 -/
theorem mem_X_iff_not_mem_Y {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V)) (u : V) : u ∈ X ↔ u ∉ Y := by
  rw [Finset.union_comm] at hcover
  exact mem_Y_iff_not_mem_X hXY.symm hcover u

/-- 函数层双射：`{u // u ∉ X} → α` 与 `Y → α`。 -/
noncomputable def funEquivLeft {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V)) :
    ({ u : V // u ∉ X } → α) ≃ (↥Y → α) where
  toFun t := fun j => t ⟨j.1, (mem_Y_iff_not_mem_X hXY hcover j.1).mp j.2⟩
  invFun b := fun j => b ⟨j.1, (mem_Y_iff_not_mem_X hXY hcover j.1).mpr j.2⟩
  left_inv := by
    intro t
    funext j
    exact congrArg t (Subtype.ext rfl)
  right_inv := by
    intro b
    funext j
    exact congrArg b (Subtype.ext rfl)

/-- 函数层双射：`{u // u ∉ Y} → α` 与 `X → α`。 -/
noncomputable def funEquivRight {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V)) :
    ({ u : V // u ∉ Y } → α) ≃ (↥X → α) where
  toFun t := fun j => t ⟨j.1, (mem_X_iff_not_mem_Y hXY hcover j.1).mp j.2⟩
  invFun b := fun j => b ⟨j.1, (mem_X_iff_not_mem_Y hXY hcover j.1).mpr j.2⟩
  left_inv := by
    intro t
    funext j
    exact congrArg t (Subtype.ext rfl)
  right_inv := by
    intro b
    funext j
    exact congrArg b (Subtype.ext rfl)

/-- **`glue` 与 `toV` 的桥**（`S = X` 一侧）。 -/
theorem glue_eq_toV_left {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V))
    (hY : ∀ v, v ∈ X ∨ v ∈ Y) (x : V → α)
    (t : { u : V // u ∉ X } → α) :
    FateV2.Predict.View19.glue X x t
      = FateV2.Predict.GraphToProbView7.toV X Y hY (fun i => x i.1)
          (fun j => t ⟨j.1, (mem_Y_iff_not_mem_X hXY hcover j.1).mp j.2⟩) := by
  funext u
  by_cases hu : u ∈ X
  · rw [FateV2.Predict.View19.glue_of_mem X x t hu, toV_mem_X (hY := hY) _ _ hu]
  · rw [FateV2.Predict.View19.glue_of_not_mem X x t hu]
    have huY : u ∈ Y := (mem_Y_iff_not_mem_X hXY hcover u).mpr hu
    rw [toV_mem_Y (hY := hY) hXY _ _ huY]

/-- **`glue` 与 `toV` 的桥**（`S = Y` 一侧）。 -/
theorem glue_eq_toV_right {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V))
    (hY : ∀ v, v ∈ X ∨ v ∈ Y) (x : V → α)
    (t : { u : V // u ∉ Y } → α) :
    FateV2.Predict.View19.glue Y x t
      = FateV2.Predict.GraphToProbView7.toV X Y hY
          (fun i => t ⟨i.1, (mem_X_iff_not_mem_Y hXY hcover i.1).mp i.2⟩)
          (fun j => x j.1) := by
  funext u
  by_cases hu : u ∈ Y
  · rw [FateV2.Predict.View19.glue_of_mem Y x t hu, toV_mem_Y (hY := hY) hXY _ _ hu]
  · rw [FateV2.Predict.View19.glue_of_not_mem Y x t hu]
    have huX : u ∈ X := by
      have h : u ∈ X ∪ Y := by rw [hcover]; exact Finset.mem_univ u
      rcases Finset.mem_union.mp h with h' | h'
      · exact h'
      · exact absurd h' hu
    rw [toV_mem_X (hY := hY) _ _ huX]

/-- ⭐⭐ **`mass X f x` = 「`X` 侧钉死 `x`、`Y` 侧自由求和」**。 -/
theorem mass_X_eq_sum_Y (f : (V → α) → ℝ) {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V))
    (hf : ∀ w w', (∀ u ∈ Y, w u = w' u) → f w = f w') (x : V → α) :
    mass X f x = ∑ b : ↥Y → α, f (toV X Y
      (fun v => Finset.mem_union.mp (by rw [hcover]; exact Finset.mem_univ v))
      (fun i => x i.1) b) := by
  classical
  rw [mass_eq_sum_glue X f x]
  set hY : ∀ v : V, v ∈ X ∨ v ∈ Y :=
    fun v => Finset.mem_union.mp (by rw [hcover]; exact Finset.mem_univ v) with hYdef
  refine Eq.trans (Fintype.sum_equiv
    (funEquivLeft hXY hcover)
    (fun t : { u : V // u ∉ X } → α => f (glue X x t))
    (fun b : ↥Y → α => f (toV X Y hY (fun i => x i.1) b)) ?_) ?_
  · intro t
    refine hf _ _ ?_
    intro u hu
    rw [glue_eq_toV_left hXY hcover hY x t]
    have h1 := toV_mem_Y (α := α) (X := X) (Y := Y) (hY := hY) hXY
      (fun i : ↥X => x i.1)
      (fun j => t ⟨j.1, (mem_Y_iff_not_mem_X hXY hcover j.1).mp j.2⟩) hu
    refine Eq.trans h1 ?_
    rw [toV_mem_Y (hY := hY) hXY (fun i : ↥X => x i.1) ((funEquivLeft hXY hcover) t) hu]
    rfl
  · exact Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => rfl)

/-- ⭐⭐ **`mass Y f x`** = 「`Y` 侧钉死 `x`、`X` 侧自由求和」。 -/
theorem mass_Y_eq_sum_X (f : (V → α) → ℝ) {X Y : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y = (Finset.univ : Finset V))
    (hf : ∀ w w', (∀ u ∈ X, w u = w' u) → f w = f w') (x : V → α) :
    mass Y f x = ∑ a : ↥X → α, f (toV X Y
      (fun v => Finset.mem_union.mp (by rw [hcover]; exact Finset.mem_univ v))
      a (fun i => x i.1)) := by
  classical
  rw [mass_eq_sum_glue Y f x]
  set hY : ∀ v : V, v ∈ X ∨ v ∈ Y :=
    fun v => Finset.mem_union.mp (by rw [hcover]; exact Finset.mem_univ v) with hYdef
  refine Eq.trans (Fintype.sum_equiv
    (funEquivRight hXY hcover)
    (fun t : { u : V // u ∉ Y } → α => f (glue Y x t))
    (fun a : ↥X → α => f (toV X Y hY a (fun i => x i.1))) ?_) ?_
  · intro t
    refine hf _ _ ?_
    intro u hu
    rw [glue_eq_toV_right hXY hcover hY x t]
    have h1 := toV_mem_X (α := α) (X := X) (Y := Y) (hY := hY)
      (fun i => t ⟨i.1, (mem_X_iff_not_mem_Y hXY hcover i.1).mp i.2⟩)
      (fun j : ↥Y => x j.1) hu
    refine Eq.trans h1 ?_
    rw [toV_mem_X (hY := hY) ((funEquivRight hXY hcover) t) (fun j : ↥Y => x j.1) hu]
    rfl
  · exact Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => rfl)

end Reindex

/-! ===========================================================================
  §5  ⭐⭐⭐⭐ 主定理 C（`Z = ∅`）最终组装
  =========================================================================== -/

section FinalAssembly

variable [Nonempty α]

/-- ⭐⭐⭐⭐ **主定理 C（`Z = ∅`）：因子图 `Split` 分离 ⟹ 乘性条件独立。**

若
* `p = ∏ v, ψ v`（单点因子分解，`HyperFactorizes`），
* 每个因子 `ψ v` 只读 `R v`（`ReadSet`），
* 每条超边整块落在 `X` 或 `Y` 内（`Split R X Y ∅`），
* `X`、`Y` 不交，每个读集非空，
* `X ∪ Y = univ`（无尾块），

则 `p` 满足 `X ⊥ Y | ∅` 的乘性形式 `CondIndep p X Y ∅`。

**证明骨架**（记 `F := ∏_{W_X} ψ`、`G := ∏_{W_Y} ψ`）：

1. `p = F * G` —— `Wblk_prod_partition` + `W_∅ = ∅`（`hne`）
2. `mass X p x = F x · Σ_b G(x|_X, b)` —— `mass_X_form` + `mass_X_eq_sum_Y`
3. `mass Y p x = G x · Σ_a F(a, x|_Y)` —— `mass_Y_form` + `mass_Y_eq_sum_X`
4. `mass (X∪Y) p x = F x · G x` —— `hcover` + `mass_univ`
5. `mass ∅ p x = (Σ_a F(a,·)) · (Σ_b G(·,b))` —— `mass_empty` + `sum_mul_sep_final`
6. `ring` 收口（两边都是 `F x · G x · (Σ_a F) · (Σ_b G)`） -/
theorem condIndep_emptyZ (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hne : ∀ v, (R v).Nonempty)
    (hsplit : FateV2.Predict.View19.Split R X Y (∅ : Finset V))
    (hXY : Disjoint X Y)
    (hcover : X ∪ Y = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y ∅ := by
  classical
  intro x
  -- 记号
  set hY : ∀ v : V, v ∈ X ∨ v ∈ Y :=
    fun v => Finset.mem_union.mp (by rw [hcover]; exact Finset.mem_univ v) with hYdef
  set F : (V → α) → ℝ := fun w => ∏ v ∈ Wblk R X, ψ v w with Fdef
  set G : (V → α) → ℝ := fun w => ∏ v ∈ Wblk R Y, ψ v w with Gdef
  -- `Wblk R ∅ = ∅`（由 `∀ v, (R v).Nonempty`）
  have hWempty : Wblk R (∅ : Finset V) = ∅ := Wblk_empty_eq_empty hne
  -- `p = F * G`
  have hp : ∀ w, p w = F w * G w := by
    intro w
    rw [hfac w]
    show (∏ v, ψ v w) = (∏ v ∈ Wblk R X, ψ v w) * (∏ v ∈ Wblk R Y, ψ v w)
    have h := (Wblk_prod_partition ψ hsplit hXY w).symm
    rw [hWempty] at h
    simpa using h
  -- `F` 只读 `X`
  have hFX : ∀ w w', (∀ u ∈ X, w u = w' u) → F w = F w' := by
    intro w w' h
    refine Finset.prod_congr rfl fun v hv => ?_
    exact hread v w w' (fun u hu => h u (mem_Wblk.mp hv hu))
  -- `G` 只读 `Y`
  have hGY : ∀ w w', (∀ u ∈ Y, w u = w' u) → G w = G w' := by
    intro w w' h
    refine Finset.prod_congr rfl fun v hv => ?_
    exact hread v w w' (fun u hu => h u (mem_Wblk.mp hv hu))
  -- `mass X p`
  have hXm : mass X p x = F x * ∑ b : ↥Y → α, G (toV X Y hY (fun i => x i.1) b) := by
    have hp' : p = fun w => (∏ v ∈ Wblk R X, ψ v w) * G w := funext fun w => hp w
    rw [hp', mass_prod_cover ψ hread (Wblk R X) (fun v hv => mem_Wblk.mp hv) G x,
      mass_X_eq_sum_Y G hXY hcover hGY x]
  -- `mass Y p`
  have hYm : mass Y p x = G x * ∑ a : ↥X → α, F (toV X Y hY a (fun i => x i.1)) := by
    have hp' : p = fun w => (∏ v ∈ Wblk R Y, ψ v w) * F w := funext fun w => by
      rw [hp w]; ring
    rw [hp', mass_prod_cover ψ hread (Wblk R Y) (fun v hv => mem_Wblk.mp hv) F x,
      mass_Y_eq_sum_X F hXY hcover hFX x]
  -- `mass (X∪Y) p`
  have hXYm : mass (X ∪ Y) p x = F x * G x := by
    rw [show X ∪ Y = (Finset.univ : Finset V) from hcover, mass_univ]
    exact hp x
  -- `mass ∅ p`
  have hEmp : mass (∅ : Finset V) p x
      = (∑ a : ↥X → α, F (toV X Y hY a (Classical.arbitrary (↥Y → α))))
        * (∑ b : ↥Y → α, G (toV X Y hY (Classical.arbitrary (↥X → α)) b)) := by
    rw [mass_empty]
    have hp' : (fun w => p w) = (fun w => F w * G w) := funext hp
    rw [hp']
    exact sum_mul_sep_final hXY hY F G hFX hGY
  -- 把 `mass X p` / `mass Y p` 中的和换成 `arbitrary` 形式
  have hsumY : (∑ b : ↥Y → α, G (toV X Y hY (fun i => x i.1) b))
      = (∑ b : ↥Y → α, G (toV X Y hY (Classical.arbitrary (↥X → α)) b)) := by
    refine Finset.sum_congr rfl fun b _ => hGY _ _ ?_
    intro u hu
    rw [toV_mem_Y (hY := hY) hXY (Classical.arbitrary (↥X → α)) b hu]
    exact toV_mem_Y (hY := hY) hXY (fun i : ↥X => x i.1) b hu
  have hsumX : (∑ a : ↥X → α, F (toV X Y hY a (fun i => x i.1)))
      = (∑ a : ↥X → α, F (toV X Y hY a (Classical.arbitrary (↥Y → α)))) := by
    refine Finset.sum_congr rfl fun a _ => hFX _ _ ?_
    intro u hu
    rw [toV_mem_X (hY := hY) a (Classical.arbitrary (↥Y → α)) hu]
    exact toV_mem_X (hY := hY) a (fun i : ↥Y => x i.1) hu
  -- 收口
  show mass (X ∪ Y ∪ ∅) p x * mass ∅ p x = mass (X ∪ ∅) p x * mass (Y ∪ ∅) p x
  rw [Finset.union_empty, Finset.union_empty, Finset.union_empty]
  rw [hXYm, hEmp, hXm, hYm, hsumY, hsumX]
  ring

end FinalAssembly

end FateV2.Predict.GraphToProbView7
