import FateWorld.FateV2.Predict.BlockCIOfBlockSplit
import FateWorld.FateV2.Predict.SubFibCard
/-!
  # Predict · MassFactorOfReads

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassFactorOfReads.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BlockCIOfBlockSplit, SubFibCard
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `blockCI_of_block_split` 修正版的核心定理

  ## 结果

  ```lean
  theorem mass_factor_of_reads {A C Z : Finset V} (hAZ : A ⊆ Z) (hCA : C ⊆ A)
      (hC : Z ∩ A = C)
      (hf : f 只读 A) (ω₀ x) :
      mass C f x = |α|^(|Z|-|C|) * mass Z f x
  ```

  ## 证明（三块）

  1. `mass_self`（`Fate/BlockCIOfBlockSplit.lean`）：
     `mass Z f x = |α|^(|V|-|Z|) · f (extEnd Z ω₀ (x|_Z))`
  2. `mass_eq_card_mul_massA`：把 `mass C f x` 展成
     `|α|^(|V|-|Z|) · ∑ wZ, if (wZ|_C = x|_C) then f (extEnd Z ω₀ wZ) else 0`
  3. `sum_const_of_cond` + `f_eq_of_agree_C`：求和内每项都等于
     `f (extEnd Z ω₀ (x|_Z))`，项数为 `|α|^(|Z|-|C|)`

  ## 为什么这是「修正版」

  `BridgeStrategy5FiberBijection.lean` §4 声称的 `blockCI_of_block_split`
  原形式是 `mass C f x = mass Z f x`（**不带** `|α|^(|Z|-|C|)` 因子）。
  那个是**假的**：`mass C` 的纤维比 `mass Z` 的纤维多 `|Z|-|C|` 个自由坐标，
  每项重复 `|α|^(|Z|-|C|)` 次。

  ## 组装成 BlockCI_Gap 未做

  `BlockCI_Gap p G A B C := ∀ x, p x * mass C p x = mass A p x * mass (B ∪ C) p x`
  把它从本定理推出需要额外的步骤（关于 `mass A`、`mass (B∪C)` 的关系）。未做。
  =========================================================================== -/

namespace FateV2.Predict.C5e

open FateV2.Modeling

open Finset FateV2.Error Fate.View19 Fate.DAGFactorization

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

set_option maxHeartbeats 2000000

theorem sum_const_of_cond {Z C : Finset V} (hCZ : C ⊆ Z) (y : ↥Z → α) (c : ℝ) :
    (∑ wZ : (↥Z → α),
      if (∀ u ∈ Fate.GraphToProbView7.sub Z C hCZ, wZ u = y u) then c else 0)
      = ((Fintype.card α : ℝ) ^ (Z.card - C.card)) * c := by
  rw [← Finset.sum_filter]
  have hcard : (Finset.univ.filter (fun wZ : (↥Z → α) =>
      ∀ u ∈ Fate.GraphToProbView7.sub Z C hCZ, wZ u = y u)).card
      = Fintype.card α ^ (Z.card - C.card) := by
    rw [← Fate.C5d.card_sub_fib' hCZ y]
    exact (Fintype.card_subtype (fun wZ : (↥Z → α) =>
      ∀ u ∈ Fate.GraphToProbView7.sub Z C hCZ, wZ u = y u)).symm
  rw [Finset.sum_const, hcard]
  push_cast
  ring

-- ⭐ 组装：mass C f x = |α|^(|Z|-|C|) * mass Z f x
theorem mass_factor_of_reads {A C Z : Finset V} (hAZ : A ⊆ Z) (hCA : C ⊆ A)
    (hC : Z ∩ A = C)
    {f : (V → α) → ℝ} (hf : ∀ w w', (∀ u ∈ A, w u = w' u) → f w = f w')
    (ω₀ x : V → α) :
    mass C f x
      = ((Fintype.card α : ℝ) ^ (Z.card - C.card)) * mass Z f x := by
  have hfZ : ∀ w w', (∀ u ∈ Z, w u = w' u) → f w = f w' :=
    fun w w' h => hf w w' (fun u hu => h u (hAZ hu))
  rw [Fate.C5b.mass_self hfZ ω₀ x]
  rw [Fate.GraphToProbView7.mass_eq_card_mul_massA (A := Z) (S := C)
    (Finset.Subset.trans hCA hAZ) hfZ ω₀ x]
  -- 求和化为常数
  -- 先用 f_eq_of_agree_C 把求和内每项化为常数
  have hpt : ∀ wZ : (↥Z → α),
      (∀ u ∈ Fate.GraphToProbView7.sub Z C (Finset.Subset.trans hCA hAZ), wZ u = x u.1) →
      f (Fate.GraphToProbView7.extEnd Z ω₀ wZ)
        = f (Fate.GraphToProbView7.extEnd Z ω₀ (fun u : ↥Z => x u.1)) :=
    fun wZ hag => Fate.C5b.f_eq_of_agree_C hAZ hCA hC hf ω₀ x wZ hag
  have hsum : (∑ wZ : (↥Z → α),
      if (∀ u ∈ Fate.GraphToProbView7.sub Z C (Finset.Subset.trans hCA hAZ), wZ u = x u.1)
        then f (Fate.GraphToProbView7.extEnd Z ω₀ wZ) else 0)
      = ((Fintype.card α : ℝ) ^ (Z.card - C.card))
        * f (Fate.GraphToProbView7.extEnd Z ω₀ (fun u : ↥Z => x u.1)) := by
    rw [← sum_const_of_cond (Finset.Subset.trans hCA hAZ) (fun u : ↥Z => x u.1)
      (f (Fate.GraphToProbView7.extEnd Z ω₀ (fun u : ↥Z => x u.1)))]
    refine Finset.sum_congr rfl fun wZ _ => ?_
    by_cases hag : ∀ u ∈ Fate.GraphToProbView7.sub Z C (Finset.Subset.trans hCA hAZ),
        wZ u = x u.1
    · rw [if_pos hag, if_pos hag, hpt wZ hag]
    · rw [if_neg hag, if_neg hag]
  rw [hsum]
  ring

end FateV2.Predict.C5e
