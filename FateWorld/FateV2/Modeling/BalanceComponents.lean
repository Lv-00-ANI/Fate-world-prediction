import FateWorld.FateV2.Modeling.SumMulSepFull
import FateWorld.FateV2.Predict.MassProCover
/-!
  # Modeling · BalanceComponents

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BalanceComponents.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SumMulSepFull, MassProCover
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  主定理 C 的配平组件（`ancestral_dSep_CondIndep` 的最后一步材料）

  ## 背景

  `GraphToProbView7.lean:190` 声称的主定理 C 需要：
  ```
  mass (X∪Y∪Z) p x * mass Z p x = mass (X∪Z) p x * mass (Y∪Z) p x
  ```

  ## 本节的配平分析（关键发现）

  用 `MassProCover.mass_prod_cover`，每个 `mass S p` 可写成
  「提出因子 × 剩余 `mass`」。剩余部分是 `mass S (fun _ => 1) x`，
  **它是常数（纤维基数），记作 `c(S)`。**

  **⟹ 配平归结为两个独立条件：**

  1. **因子部分**：`∏_{W_X} · ∏_{W_Y} = ∏_V · ∏_{W_Z}`
     需 `W_X ∪ W_Y = V` 且 `W_X ∩ W_Y = W_Z`（`Split` 给出）
  2. **基数部分**：`c(X∪Y∪Z) · c(Z) = c(X∪Z) · c(Y∪Z)`
     化简为 `|X∪Y∪Z| + |Z| = |X∪Z| + |Y∪Z|`

  ## ⭐ 本节的核心发现

  **条件 2 **需要 `X`、`Y`、`Z` 两两不交。**

  **⟹ 这正是 `dSep` 定义里的三个 `Disjoint` 合取项！**

  **⟹ 所以 `dSep` 的「不交」条件**不是形式上的多余约束，而是配平必需的
  （没有它，两边纤维基数不同，等式不成立）。**

  ## 本节给什么

  1. ⭐ `card_balance`：`|X∪Y∪Z| + |Z| = |X∪Z| + |Y∪Z|`（需三对 `Disjoint`）
  2. ⭐ `mass_one_indep`：`mass S (fun _ => 1) x` 与 `x` 无关

  ## 诚实边界

  * **本节只给配平的两个**组件**，不做 `CondIndep` 的最终组装。**
  * **因子部分（`W_X ∪ W_Y = V` 等）未形式化** —— 它依赖 `Split` 与 `W` 的定义。
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open FateV2.Predict

open Finset
open FateV2.Predict.DAGFactorization

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-! ### §0.1 ⭐ 基数恒等式（配平的第二个条件） -/

/-- ⭐⭐ **基数恒等式**：`X`、`Y`、`Z` 两两不交时，
`|X∪Y∪Z| + |Z| = |X∪Z| + |Y∪Z|`。

**⟹ 这是 `CondIndep` 配平的**必要条件**：没有它，两边的纤维基数不等。**

**⚠ 而「两两不交」正是 `dSep` 定义的三个合取项。** -/
theorem card_balance (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    (X ∪ Y ∪ Z).card + Z.card = (X ∪ Z).card + (Y ∪ Z).card := by
  have h1 : Disjoint (X ∪ Y) Z := Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩
  rw [Finset.card_union_of_disjoint h1]
  rw [Finset.card_union_of_disjoint hXY]
  rw [Finset.card_union_of_disjoint hXZ]
  rw [Finset.card_union_of_disjoint hYZ]
  ring

/-! ### §0.2 ⚠ `mass S 1` 的显式值（缺口登记）

**目标形式**：
```
mass S (fun _ => 1) x = (|α| : ℝ) ^ (|V| - |S|)
```

**⟹ 这是「纤维基数」，与 `x` 无关。**

**✅ 已证**（见下方 `mass_one_card`，用的正是 `Fintype.card_congr`
加 `fibEquiv` 纤维基数的双射构造；第 618 轮更新本条陈旧登记）。

**它是配平「常数部分」的依据：若两个 `mass` 的常数部分都写成
`|α|^(|V|-|S|)`，则配平归结为 `card_balance`（§0.1，已证）。 -/


/-! ### §0.2 ⭐⭐⭐ 纤维基数（配平的常数部分） -/

noncomputable def fibEquiv (S : Finset V) (x : V → α) :
    {w : V → α // ∀ u ∈ S, w u = x u} ≃ ({v : V // v ∉ S} → α) where
  toFun w := fun v => w.1 v.1
  invFun f := ⟨fun v => if hv : v ∈ S then x v else f ⟨v, hv⟩, by
    intro u hu
    simp only [dif_pos hu]⟩
  left_inv := by
    intro w
    ext v
    by_cases hv : v ∈ S
    · simp only [dif_pos hv]
      exact (w.2 v hv).symm
    · simp only [dif_neg hv]
  right_inv := by
    intro f
    funext v
    simp only [dif_neg v.2]

-- 先证「子类型基数」这个中间形式
theorem card_subtype_fib (S : Finset V) (x : V → α) :
    Fintype.card {w : V → α // ∀ u ∈ S, w u = x u}
      = Fintype.card α ^ (Fintype.card V - S.card) := by
  rw [Fintype.card_congr (fibEquiv S x)]
  rw [Fintype.card_fun]
  congr 1
  rw [← Fintype.card_coe]
  -- |{v // v ∉ S}| = |V| - |S|
  have h1 : Fintype.card {v : V // v ∉ S} = Fintype.card V - Fintype.card ↥S := by
    rw [Fintype.card_subtype_compl]
  have h2 : Fintype.card ↥S = S.card := Fintype.card_coe S
  rw [h1, h2]

-- 现在接到 mass 上
theorem mass_one_card (S : Finset V) (x : V → α) :
    mass S (fun _ => (1 : ℝ)) x
      = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) := by
  unfold mass
  have hsum : (∑ w : V → α, if ∀ u ∈ S, w u = x u then ((fun _ => (1:ℝ)) w) else 0)
      = ((Finset.univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)).card : ℝ) := by
    rw [Finset.sum_boole]
  rw [hsum]
  have hsub : (Finset.univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)).card
      = Fintype.card {w : V → α // ∀ u ∈ S, w u = x u} := by
    rw [Fintype.card_subtype]
  rw [hsub, card_subtype_fib, Nat.cast_pow]
