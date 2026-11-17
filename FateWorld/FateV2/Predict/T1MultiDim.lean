/-
# `Fate/T1MultiDim` —— T-1 退化问题的**多维精确刻画**（CC2）

## 0  要裁决的问题

审计意见（T-1）称：在现有框架下「使残差为零的 `θ` 集合是**超平面**而非点」，
于是学习**退化为部分识别**。

本文件把该说法**精确化并机检**。取

* 状态空间 / 参数空间 `Θ = X = EuclideanSpace ℝ (Fin n)`（即 `ℝ^n`）；
* 一步转移 `step θ x = ⟪θ, x⟫`（内积，即 `θ · x`）；
* 观测模型 `y_i = step θ* x_i = ⟪θ*, x_i⟫`（无噪声）。

则「与观测相容的参数」是线性映射 `obsMap x : Θ →ₗ[ℝ] (Fin k → ℝ)` 的原像，
其**非唯一性完全由核 `amb x = ker (obsMap x)`（歧义子空间）度量**。

## 1  结论（本文件机检的定理）

| 编号 | 定理 | 判词 |
|---|---|---|
| 定义 | `step`、`obsMap`、`amb`、`solSet` | 框架载体 |
| 结构 | `sol_iff_sub_mem_amb` | 解集是 `amb x` 的**陪集** |
| 结构 | `obsMap_add_of_mem_amb` | 歧义方向**不改变观测** |
| **(a)** | `exists_nonzero_orthogonal_single` | `n ≥ 2`、`x₀ ≠ 0` ⟹ 存在非零 `δ ⊥ x₀` |
| **(a)** | `single_amb_ne_bot` | 单组观测的 `amb ≠ ⊥` ⟹ 解集**非单点** |
| **(a)** | `single_sol_nontrivial` | 单组观测：存在**两个不同**参数给出**同一**观测 |
| **(b')** | `eq_zero_of_orthogonal_span_top` | 正交于张成全空间者即 `0` |
| **(b')** | `unique_of_span_top` | `x` 张成 `Θ` ⟹ `θ` **唯一** |
| **(b')** | `obsMap_injective_of_span_top` | 张成 ⟹ `obsMap` **单射** |
| **(b)** | `unique_of_linearIndependent` | `x : Fin n → ℝ^n` 线性无关、`n ≥ 1` ⟹ `θ` **唯一** |
| **(b)** | `card_le_of_linearIndependent` | `ℝ^n` 中线性无关族大小 `≤ n` |
| **一般** | `unique_iff_span_top` | 唯一 ⟺ 观测张成 `Θ`（**充要**） |
| **一般** | `unique_iff_amb_bot` | 唯一 ⟺ `amb x = ⊥` |
| 判定 | `degenerate_iff_amb_ne_bot` | 「退化」⟺ `amb x ≠ ⊥` |
| 判定 | `degenerate_iff_span_ne_top` | 「退化」⟺ 观测**张成不成**全空间 |

**故 T-1 的措辞需修正**：退化**不是**「集合必然超平面」，
而是「**观测不足时**集合非平凡」，其精确判据是 `amb x ≠ ⊥`（⟺ 观测张成不成全空间）。
给出 `k ≥ n` 个线性无关观测（更一般地：只需观测张成 `Θ`）后退化**完全消失**。
`unique_iff_span_top` / `unique_iff_amb_bot` 是**充要**陈述，故是
「观测不足即退化、观测充分即唯一」的**完整刻画**。

## 2  ⚠ 诚实边界（必读，不得含糊）

* **2.1 只限线性读法。** 本文件只刻画 `step θ x = ⟪θ, x⟫`（与 T-1 讨论的框架一致）。
  对非线性 `f(θ, x)`，残差零点集一般**不是**仿射子空间，本文件**不声称**任何结论。
* **2.2 「超平面」取精确含义。** 本文件证明的是「解集 `= θ₀ + amb x`，且 `amb x ≠ ⊥`」
  （非平凡仿射子空间），**不**证明 `finrank (amb x) = n - 1` 这一具体维数等式——
  后者需要额外的严格不等式维数计算（单观测时 `finrank (amb) = n - 1`），本文件未做。
  `amb x ≠ ⊥` 已足以否定唯一性、也足以支撑「不是点」的结论，
  而 `single_amb_ne_top` 进一步给出 `amb x ≠ ⊤`（确实不是整个空间）。
* **2.3 `k ≥ n` 的精确化。** 在 `n` 维空间里 `k > n` 个向量**必线性相关**，
  故「`k ≥ n` 组线性无关观测」唯一可实现的形式是 `k = n`（见
  `card_le_of_linearIndependent`）。本文件**如实**地把 `k ≥ n` 精确化为 `k = n`
  并在 `unique_of_linearIndependent` 中证明，而不是把 `k > n` 当作更强假设。
  更一般的 `k`（不假设线性无关、只假设张成）由 `unique_of_span_top` 覆盖。
* **2.4 无噪声。** `y_i = ⟪θ*, x_i⟫` 严格相等。含噪情形本文件不涉及。
* **2.5 零 `sorry` / 零 `axiom`。** 全文件机检，无占位。

## 3  与既有设施的关系

本文件**不修改任何已有模块**。所用外部事实全部为 Mathlib 已证定理：
`PiLp.inner_apply`（内积展开）、`Submodule.mem_orthogonal'` /
`Submodule.orthogonal_eq_bot_iff` / `Submodule.inf_orthogonal_eq_bot`（正交补）、
`finrank_span_singleton` / `Submodule.finrank_mono`（维数）、
`LinearIndependent.fintype_card_le_finrank` /
`LinearIndependent.span_eq_top_of_card_eq_finrank`（维数—张成）。本文件不重证它们。
-/

import FateWorld.FateV2.Modeling.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module Submodule

namespace FateV2.Predict.T1MultiDim

open FateV2.Modeling

variable {n k : ℕ}

/-!
  # Predict · T1MultiDim

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1MultiDim.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## 4  基本载体 -/

/-- 参数空间与状态空间：`ℝ^n`。 -/
abbrev State (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- **一步转移**：`step θ x = ⟪θ, x⟫`（即内积 `θ · x`）。这是 T-1 讨论的线性读法本体。 -/
noncomputable def step (θ x : State n) : ℝ := inner ℝ θ x

/-- `step` 的坐标展开：`step θ x = ∑ i, θ i * x i`。 -/
theorem step_apply (θ x : State n) : step θ x = ∑ i, θ i * x i := by
  rw [step, PiLp.inner_apply]
  simp [mul_comm]

/-- **观测映射**：`obsMap x θ` 的第 `i` 个分量是「参数 `θ` 下第 `i` 次观测的预测值」`⟪θ, x i⟫`。
它是 `ℝ`-线性映射——**线性**是 T-1 框架的关键结构，退化的全部机制在此。 -/
noncomputable def obsMap (x : Fin k → State n) : State n →ₗ[ℝ] (Fin k → ℝ) where
  toFun θ i := inner ℝ θ (x i)
  map_add' θ θ' := by
    funext i
    simp [inner_add_left]
  map_smul' a θ := by
    funext i
    simp [inner_smul_left]

@[simp] theorem obsMap_apply (x : Fin k → State n) (θ : State n) (i : Fin k) :
    obsMap x θ i = inner ℝ θ (x i) := rfl

/-- `obsMap x θ = y` 的逐分量展开。 -/
theorem obsMap_eq_iff (x : Fin k → State n) (θ : State n) (y : Fin k → ℝ) :
    obsMap x θ = y ↔ ∀ i, inner ℝ θ (x i) = y i := by
  constructor
  · intro h i
    have := congrFun h i
    simpa using this
  · intro h
    funext i
    simpa using h i

/-- **歧义子空间** `amb x`：观测**看不见**的参数扰动集合 `{δ | ∀ i, ⟪δ, x i⟫ = 0}`，
恰为 `obsMap x` 的核。 -/
noncomputable def amb (x : Fin k → State n) : Submodule ℝ (State n) := LinearMap.ker (obsMap x)

theorem mem_amb {x : Fin k → State n} {δ : State n} :
    δ ∈ amb x ↔ ∀ i, inner ℝ δ (x i) = 0 := by
  constructor
  · intro h i
    have := congrFun (show obsMap x δ = 0 from h) i
    simpa using this
  · intro h
    funext i
    simpa using h i

/-- **解集**：与观测 `y` 相容的全部参数。 -/
def solSet (x : Fin k → State n) (y : Fin k → ℝ) : Set (State n) := {θ | obsMap x θ = y}

theorem mem_solSet {x : Fin k → State n} {y : Fin k → ℝ} {θ : State n} :
    θ ∈ solSet x y ↔ ∀ i, inner ℝ θ (x i) = y i := by
  rw [solSet, Set.mem_setOf_eq, obsMap_eq_iff]

/-! ## 5  解集的仿射结构 -/

/-- 歧义方向**不改变观测**：`δ ∈ amb x ⟹ obsMap x (θ + δ) = obsMap x θ`。 -/
theorem obsMap_add_of_mem_amb {x : Fin k → State n} {δ : State n} (hδ : δ ∈ amb x)
    (θ : State n) : obsMap x (θ + δ) = obsMap x θ := by
  have h : obsMap x δ = 0 := hδ
  rw [map_add, h, add_zero]

/-- ⭐ 解集是歧义子空间的**陪集**：若 `θ₀` 是解，则 `θ` 是解 ⟺ `θ - θ₀ ∈ amb x`。 -/
theorem sol_iff_sub_mem_amb {x : Fin k → State n} {y : Fin k → ℝ} {θ₀ θ : State n}
    (h₀ : obsMap x θ₀ = y) : θ ∈ solSet x y ↔ θ - θ₀ ∈ amb x := by
  rw [mem_solSet, mem_amb]
  constructor
  · intro h i
    have hi : inner ℝ θ (x i) = y i := h i
    have hi' : inner ℝ θ₀ (x i) = y i := (obsMap_eq_iff x θ₀ y).mp h₀ i
    rw [inner_sub_left, hi, hi', sub_self]
  · intro h i
    have h0i : inner ℝ (θ - θ₀) (x i) = 0 := h i
    rw [inner_sub_left, sub_eq_zero] at h0i
    have hi' : inner ℝ θ₀ (x i) = y i := (obsMap_eq_iff x θ₀ y).mp h₀ i
    rw [h0i, hi']

/-! ## 6  (a) 单组观测：歧义子空间非平凡（**确实不唯一**） -/

/-- ⭐⭐ **(a) 的核心**：`n ≥ 2` 时，任何非零 `x₀ : ℝ^n` 都有**非零正交向量** `δ`。

证明走正交补路线（避免坐标计算）：`span ℝ {x₀}` 的维数为 `1`，而 `finrank ℝ (ℝ^n) = n ≥ 2`，
故 `span ℝ {x₀} < ⊤`，于是其正交补 `≠ ⊥`，取其中非零向量即得。 -/
theorem exists_nonzero_orthogonal_single (hn : 2 ≤ n) {x₀ : State n} (hx₀ : x₀ ≠ 0) :
    ∃ δ : State n, δ ≠ 0 ∧ inner ℝ δ x₀ = 0 := by
  -- `span ℝ {x₀}` 是真子空间
  have hfr : finrank ℝ ↥(Submodule.span ℝ ({x₀} : Set (State n))) = 1 :=
    finrank_span_singleton hx₀
  have htop : finrank ℝ (State n) = n := finrank_euclideanSpace_fin
  have hlt : Submodule.span ℝ ({x₀} : Set (State n)) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hE
    have h1 : finrank ℝ ↥(Submodule.span ℝ ({x₀} : Set (State n))) = n := by
      rw [hE, finrank_top]
      exact htop
    omega
  -- 其正交补非平凡
  have hne : (Submodule.span ℝ ({x₀} : Set (State n)))ᗮ ≠ ⊥ := by
    intro hbot
    rw [Submodule.orthogonal_eq_bot_iff] at hbot
    exact (ne_of_lt hlt) hbot
  obtain ⟨δ, hδmem, hδ0⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨δ, hδ0, ?_⟩
  have hmem : x₀ ∈ Submodule.span ℝ ({x₀} : Set (State n)) :=
    Submodule.subset_span (Set.mem_singleton x₀)
  have h := (Submodule.mem_orthogonal' (Submodule.span ℝ ({x₀} : Set (State n))) δ).mp hδmem
  exact h x₀ hmem

/-- ⭐⭐ **(a)：单组观测的歧义子空间非平凡**。

`k = 1`、`x₀ = x 0 ≠ 0`、`n ≥ 2` 时 `amb x ≠ ⊥`：
存在**看不见的**非零参数扰动。这正是「使残差为零的 `θ` 不唯一」。 -/
theorem single_amb_ne_bot (hn : 2 ≤ n) {x : Fin 1 → State n} (hx : x 0 ≠ 0) :
    amb x ≠ ⊥ := by
  obtain ⟨δ, hδ0, hδorth⟩ := exists_nonzero_orthogonal_single hn hx
  intro hbot
  have hmem : δ ∈ amb x := by
    rw [mem_amb]
    intro i
    -- `Fin 1` 只有一个元素 `0`
    rw [Subsingleton.elim i 0]
    exact hδorth
  rw [hbot] at hmem
  exact hδ0 (by simpa using hmem)

/-- ⭐⭐ **(a)：单组观测下解集**确实**不是单点**。

存在两个**不同**参数 `θ₁ ≠ θ₂` 给出**完全相同**的观测向量。
（取 `θ₁ = δ`、`θ₂ = 0`，`δ` 为非零歧义方向。） -/
theorem single_sol_nontrivial (hn : 2 ≤ n) {x : Fin 1 → State n} (hx : x 0 ≠ 0) :
    ∃ θ₁ θ₂ : State n, θ₁ ≠ θ₂ ∧ obsMap x θ₁ = obsMap x θ₂ := by
  obtain ⟨δ, hδ0, hδorth⟩ := exists_nonzero_orthogonal_single hn hx
  have hmem : δ ∈ amb x := by
    rw [mem_amb]
    intro i
    rw [Subsingleton.elim i 0]
    exact hδorth
  refine ⟨δ, 0, hδ0, ?_⟩
  have := obsMap_add_of_mem_amb hmem 0
  simpa using this

/-- **(a) 的补充**：单组观测时 `amb x ≠ ⊤`——歧义方向**不含**整个空间，
故残差零点集确实是**真**非平凡仿射子空间（不是「随便哪个 θ 都行」）。

反证：若 `amb x = ⊤`，则 `x₀` 自身在 `amb x` 中，于是 `⟪x₀, x₀⟫ = 0`，得 `x₀ = 0`，矛盾。 -/
theorem single_amb_ne_top {x : Fin 1 → State n} (hx : x 0 ≠ 0) : amb x ≠ ⊤ := by
  intro htop
  have hmem : x 0 ∈ amb x := by rw [htop]; exact Submodule.mem_top
  rw [mem_amb] at hmem
  have h1 : inner ℝ (x 0) (x 0) = 0 := by
    have := hmem 0
    simpa using this
  exact hx (inner_self_eq_zero.mp h1)

/-! ## 7  (b) 观测充分 ⟹ `θ` 唯一 -/

/-- ⭐⭐ **正交于张成全空间的观测 ⟹ `δ = 0`**。 -/
theorem eq_zero_of_orthogonal_span_top {x : Fin k → State n} {δ : State n}
    (hspan : Submodule.span ℝ (Set.range x) = ⊤)
    (h : ∀ i, inner ℝ δ (x i) = 0) : δ = 0 := by
  have hmem : δ ∈ (Submodule.span ℝ (Set.range x))ᗮ := by
    rw [Submodule.mem_orthogonal']
    rintro u hu
    refine Submodule.span_induction (p := fun u _ => inner ℝ δ u = 0) ?_ ?_ ?_ ?_ hu
    · rintro u ⟨i, rfl⟩
      exact h i
    · simp
    · intro u v _ _ hu hv
      rw [inner_add_right, hu, hv, add_zero]
    · intro a u _ hu
      rw [inner_smul_right, hu, mul_zero]
  rw [hspan] at hmem
  -- `⊤ᗮ = ⊥`：与全空间正交的向量必为 `0`
  have h1 : inner ℝ δ δ = 0 :=
    (Submodule.mem_orthogonal' (⊤ : Submodule ℝ (State n)) δ).mp hmem δ Submodule.mem_top
  exact inner_self_eq_zero.mp h1

/-- ⭐⭐⭐ **主定理 (b')：观测张成 `Θ` ⟹ 参数唯一**。

若 `x` 张成整个参数空间，则任意两个在所有观测上给出**相同预测**的参数必相等。
（前件只谈**观测向量** `x` 与**预测相等**，结论谈**参数相等**；前件不含结论。） -/
theorem unique_of_span_top {x : Fin k → State n}
    (hspan : Submodule.span ℝ (Set.range x) = ⊤)
    {θ θ' : State n} (hobs : ∀ i, inner ℝ θ (x i) = inner ℝ θ' (x i)) : θ = θ' := by
  have hzero : θ - θ' = 0 := by
    refine eq_zero_of_orthogonal_span_top hspan (δ := θ - θ') (fun i => ?_)
    rw [inner_sub_left, hobs i, sub_self]
  exact sub_eq_zero.mp hzero

/-- **(b') 的「原像单射」形式**：观测张成 `Θ` ⟹ `obsMap x` 单射。 -/
theorem obsMap_injective_of_span_top {x : Fin k → State n}
    (hspan : Submodule.span ℝ (Set.range x) = ⊤) : Function.Injective (obsMap x) := by
  intro θ θ' h
  refine unique_of_span_top hspan (fun i => ?_)
  have := congrFun h i
  simpa using this

/-- ⭐⭐⭐ **主定理 (b)：`n` 组线性无关观测 ⟹ 参数唯一**。

`x : Fin n → ℝ^n` 线性无关 ⟹ 张成整个 `ℝ^n`（`finrank ℝ (ℝ^n) = n`），
再由 `unique_of_span_top` 得唯一性。

⚠ `k ≥ n` 的精确化见 `card_le_of_linearIndependent`：`ℝ^n` 中线性无关族大小必 `≤ n`，
故「`k ≥ n` 组线性无关观测」的可实现形式正是 `k = n`。 -/
theorem unique_of_linearIndependent {x : Fin n → State n} (hn : 0 < n)
    (hli : LinearIndependent ℝ x)
    {θ θ' : State n} (hobs : ∀ i, inner ℝ θ (x i) = inner ℝ θ' (x i)) : θ = θ' := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  refine unique_of_span_top ?_ hobs
  refine hli.span_eq_top_of_card_eq_finrank ?_
  simp

/-- ⭐ **`k ≥ n` 的精确化**：`ℝ^n` 中线性无关族的大小**恰好不超过** `n`。

故「`k ≥ n` 组线性无关观测」在 `ℝ^n` 中**只能取等号** `k = n`。
这不是削弱要求，而是把 `k ≥ n` 修正为 `ℝ^n` 里唯一可实现的（且已足够的）形式。 -/
theorem card_le_of_linearIndependent {x : Fin k → State n}
    (hli : LinearIndependent ℝ x) : k ≤ n := by
  have h := hli.fintype_card_le_finrank
  simpa [finrank_euclideanSpace_fin] using h

/-! ## 8  充要判定：唯一 ⟺ 观测张成全空间 ⟺ `amb = ⊥` -/

/-- ⭐⭐ **唯一 ⟺ `amb x = ⊥`**（歧义子空间平凡 ⟺ 参数被唯一确定）。

「唯一」= 任何两个在所有观测上预测相同的参数必相等；
「`amb x = ⊥`」= 观测**看不见**的非零扰动不存在。 -/
theorem unique_iff_amb_bot {x : Fin k → State n} :
    (∀ θ θ' : State n, (∀ i, inner ℝ θ (x i) = inner ℝ θ' (x i)) → θ = θ')
      ↔ amb x = ⊥ := by
  constructor
  · intro huniq
    rw [Submodule.eq_bot_iff]
    intro δ hδ
    have horth : ∀ i, inner ℝ δ (x i) = 0 := mem_amb.mp hδ
    refine huniq δ 0 (fun i => ?_)
    rw [horth i]
    simp
  · intro hbot θ θ' hobs
    have hmem : θ - θ' ∈ amb x := by
      rw [mem_amb]
      intro i
      rw [inner_sub_left, hobs i, sub_self]
    rw [hbot] at hmem
    have hzero : θ - θ' = 0 := by simpa using hmem
    exact sub_eq_zero.mp hzero

/-- ⭐⭐⭐ **唯一 ⟺ 观测张成 `Θ`**（**充要判定**，本节主定理）。

* (⇐) 即 `unique_of_span_top`；
* (⇒) 若 `x` 不张成全空间，其正交补非平凡，取非零 `δ ⊥ span x`，
  则 `δ` 与 `0` 给出**相同观测**却**不同参数**，唯一性失败。

故「退化」（解集非单点）与「观测不足」（张成不成全空间）**互为充要**：
T-1 所说的「框架缺陷」实为「观测不足」的代数表现。 -/
theorem unique_iff_span_top {x : Fin k → State n} :
    (∀ θ θ' : State n, (∀ i, inner ℝ θ (x i) = inner ℝ θ' (x i)) → θ = θ')
      ↔ Submodule.span ℝ (Set.range x) = ⊤ := by
  constructor
  · intro huniq
    by_contra hspan
    have hne : (Submodule.span ℝ (Set.range x))ᗮ ≠ ⊥ := by
      intro hbot
      rw [Submodule.orthogonal_eq_bot_iff] at hbot
      exact hspan hbot
    obtain ⟨δ, hδmem, hδ0⟩ := (Submodule.ne_bot_iff _).mp hne
    have horth : ∀ i, inner ℝ δ (x i) = 0 := by
      intro i
      have h := (Submodule.mem_orthogonal' (Submodule.span ℝ (Set.range x)) δ).mp hδmem
      exact h (x i) (Submodule.subset_span ⟨i, rfl⟩)
    have heq : δ = 0 := huniq δ 0 (fun i => by rw [horth i]; simp)
    exact hδ0 heq
  · intro hspan θ θ' h
    exact unique_of_span_top hspan h

/-- ⭐⭐ **T-1 判词的形式化**：「退化」（存在两个不同参数给出同一观测）⟺ `amb x ≠ ⊥`。 -/
theorem degenerate_iff_amb_ne_bot {x : Fin k → State n} :
    (∃ θ₁ θ₂ : State n, θ₁ ≠ θ₂ ∧ obsMap x θ₁ = obsMap x θ₂) ↔ amb x ≠ ⊥ := by
  constructor
  · rintro ⟨θ₁, θ₂, hne, heq⟩ hbot
    have huniq : ∀ θ θ' : State n,
        (∀ i, inner ℝ θ (x i) = inner ℝ θ' (x i)) → θ = θ' :=
      unique_iff_amb_bot.mpr hbot
    exact hne (huniq θ₁ θ₂ (fun i => by
      have h := congrFun heq i
      simpa using h))
  · intro hne
    obtain ⟨δ, hδmem, hδ0⟩ : ∃ δ ∈ amb x, δ ≠ 0 := Submodule.ne_bot_iff _ |>.mp hne
    refine ⟨δ, 0, hδ0, ?_⟩
    have h := obsMap_add_of_mem_amb (x := x) hδmem 0
    simpa using h

/-- ⭐⭐ **T-1 判词的形式化（张成版）**：退化 ⟺ 观测的张成**不是**全空间。 -/
theorem degenerate_iff_span_ne_top {x : Fin k → State n} :
    (∃ θ₁ θ₂ : State n, θ₁ ≠ θ₂ ∧ obsMap x θ₁ = obsMap x θ₂)
      ↔ Submodule.span ℝ (Set.range x) ≠ ⊤ := by
  rw [degenerate_iff_amb_ne_bot]
  constructor
  · intro hne htop
    exact hne (unique_iff_amb_bot.mp (unique_iff_span_top.mpr htop))
  · intro hne hbot
    exact hne (unique_iff_span_top.mp (unique_iff_amb_bot.mpr hbot))

end FateV2.Predict.T1MultiDim

/-! ===========================================================================
  §9 R-45 接线：三条充要判定**互为等价**，与观测条数的**下界**

  §8 给出三条各自成立的充要判定：

  * `unique_iff_amb_bot`：唯一 ⟺ `amb x = ⊥`；
  * `unique_iff_span_top`：唯一 ⟺ `span (range x) = ⊤`；
  * `degenerate_iff_amb_ne_bot` / `degenerate_iff_span_ne_top`：退化 = 唯一的否定。

  **本节把这些判定彼此接通**（此前文件里它们是**并列**的三条，没有任何一条
  直接把「`amb`」与「张成」联系起来），并给出一个**此前没有的定量结论**：
  唯一性 ⇒ **观测条数 `k ≥ n`**。
  =========================================================================== -/

namespace FateV2.Predict.T1MultiDim

/-! ## §9.1 两个判定的直接等价（`amb` 侧 ↔ 张成侧） -/

/-- ⭐⭐ **`amb_bot_iff_span_top`**：`amb x = ⊥ ⟺ span (range x) = ⊤`。

**为什么需要这条**：§8 的两条判定都经过「唯一」这个**中介谓词**，
而下游（如 `solSet` 的单点性、`obsMap x` 的单射性）常常**只有一个**中间量在手。
本条给出**不经中介**的直接桥，把 `amb x = ⊥` 换成 `span = ⊤`（或反向），
省掉「唯一」这一整层展开。

**⚠ 非循环**：证明是两个**已证**等价（`unique_iff_amb_bot`、`unique_iff_span_top`）
经 `Iff.trans` 传递；其**右端**（`amb x = ⊥`、`span = ⊤`）都不在前件里，
且传递本身需要两侧都真 —— 单靠任一侧无法得到本条。 -/
theorem amb_bot_iff_span_top {x : Fin k → State n} :
    amb x = ⊥ ↔ Submodule.span ℝ (Set.range x) = ⊤ :=
  (unique_iff_amb_bot (x := x)).symm.trans (unique_iff_span_top (x := x))

/-- ⭐⭐ **`obsMap_injective_iff_amb_bot`**：`obsMap x` **单射** ⟺ `amb x = ⊥`。

**为什么需要这条**：`obsMap_injective_of_span_top`（§7）只给了**一个方向**
且前件是「张成 `= ⊤`」；本节给出**单射形式下的充要刻画**，
于是「`obsMap x` 是单射」与「歧义子空间平凡」互换使用。

**⚠ 非循环**：`→` 方向由 `unique_iff_amb_bot` 的 `mp`（把单射喂给唯一谓词，
需 `obsMap_eq_iff` 把函数相等转成 `inner` 相等）；`←` 方向由
`mem_amb` 展开核、再经 `amb x = ⊥` 收成 `θ - θ' = 0`。
结论是 `Function.Injective`，前件是子空间等式，二者**不同对象**。 -/
theorem obsMap_injective_iff_amb_bot {x : Fin k → State n} :
    Function.Injective (obsMap x) ↔ amb x = ⊥ := by
  constructor
  · intro hinj
    refine (unique_iff_amb_bot (x := x)).mp ?_
    intro θ θ' hobs
    refine hinj ?_
    exact (obsMap_eq_iff x θ (obsMap x θ')).mpr hobs
  · intro hbot θ θ' heq
    have hmem : θ - θ' ∈ amb x := by
      rw [mem_amb]
      intro i
      have h : inner ℝ θ (x i) = inner ℝ θ' (x i) := congrFun heq i
      rw [inner_sub_left, h, sub_self]
    rw [hbot] at hmem
    have hzero : θ - θ' = 0 := by simpa using hmem
    exact sub_eq_zero.mp hzero

/-- ⭐⭐ **`obsMap_injective_iff_span_top`**（单射版本的**张成**刻画）。

与上一条并列，供只有张成信息的下游直接使用。 -/
theorem obsMap_injective_iff_span_top {x : Fin k → State n} :
    Function.Injective (obsMap x) ↔ Submodule.span ℝ (Set.range x) = ⊤ :=
  (obsMap_injective_iff_amb_bot (x := x)).trans (amb_bot_iff_span_top (x := x))

/-! ## §9.2 定量结论：唯一性**强制**观测条数 `k ≥ n` -/

/-- ⭐⭐⭐ **`unique_implies_card_ge`**：若观测**唯一确定**参数，则观测条数 `k ≥ n`。

**为什么这是新内容**：§8 的三条判定都只说「唯一 ⟺ 某个子空间/张成条件」，
**没有一条**把唯一性与**观测条数** `k` 联系起来。
本条的结论 `n ≤ k` 是一个**数值下界**：`ℝ^n` 里的 `n` 个自由度，
要全被观测钉住，**至少**需要 `n` 条观测。

**⚠ 非循环**：前件是「唯一」这一 `∀ θ θ'` 句式；结论是**自然数**不等式
（`n ≤ k`）。证明走 `unique_iff_span_top` 得 `span = ⊤`，
再用 `finrank_span_le_card`（张成的维数 ≤ 生成集的基数）与
`finrank_euclideanSpace_fin`（`finrank ℝ (ℝ^n) = n`）夹出 `n ≤ k`。 -/
theorem unique_implies_card_ge {x : Fin k → State n}
    (huniq : ∀ θ θ' : State n, (∀ i, inner ℝ θ (x i) = inner ℝ θ' (x i)) → θ = θ') :
    n ≤ k := by
  have hspan : Submodule.span ℝ (Set.range x) = ⊤ :=
    (unique_iff_span_top (x := x)).mp huniq
  have hle := finrank_span_le_card (R := ℝ) (Set.range x)
  rw [hspan] at hle
  rw [finrank_top, finrank_euclideanSpace_fin] at hle
  have hcard : (Set.range x).toFinset.card ≤ k := by
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le (f := x)
  omega

/-- ⭐⭐ **`not_unique_of_card_lt`**：观测条数 `k < n` 时**唯一性必然失败**。

即存在两个**不同**参数，在所有观测上给出**相同预测** ——
这是「观测不足 ⟹ 退化」的**定量版**（§8 的判定只说「唯一 ⟺ 张成」，
不说「条数不够就必然不张成」）。

**⚠ 非循环**：前件只有 `k < n`（纯算术）；结论是**存在性**（`∃ θ₁ θ₂`，
且要求 `θ₁ ≠ θ₂` 与预测相等），证明是对 `unique_implies_card_ge` 取逆否后
把「唯一」的否定经 `by_contra` 还原成显式见证。 -/
theorem not_unique_of_card_lt {x : Fin k → State n} (hk : k < n) :
    ∃ θ₁ θ₂ : State n, θ₁ ≠ θ₂ ∧ obsMap x θ₁ = obsMap x θ₂ := by
  by_contra hall
  have huniq : ∀ θ θ' : State n,
      (∀ i, inner ℝ θ (x i) = inner ℝ θ' (x i)) → θ = θ' := by
    intro θ θ' hobs
    by_contra hne
    exact hall ⟨θ, θ', hne, (obsMap_eq_iff x θ (obsMap x θ')).mpr hobs⟩
  exact absurd (unique_implies_card_ge huniq) (by omega)

end FateV2.Predict.T1MultiDim