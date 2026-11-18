import FateWorld.FateV2.Predict.MassADecompFinal
/-!
  # Predict · MassInsertCorrected

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassInsertCorrected.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassADecompFinal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  mass_insert_of_insensitive 的**正确版本**

  ## 原定理（Fate/Strategy13FactorHoist.lean，为假）

  theorem mass_insert_of_insensitive (sh : h ∉ S)
      (hins : ∀ x y, (∀ u ∈ S, x u = y u) → x h = y h → g x = g y)
      (x) : mass (insert h S) g x = mass S g x

  **这也是假的**：mass S 的纤维里 w h 可任取 |α| 种，而 hins 恰好说明
  每种取值的 g 相同，故右边是左边的 |α| 倍：

  mass S g x = |α| · mass (insert h S) g x

  ## 本文件的结果

  mass_self_insert：mass A g x = |α|^(|V|-|A|) · g(extEnd A x (x|_A))
  mass_insert_corrected：mass S g x = |α| · mass (insert h S) g x
  =========================================================================== -/

namespace FateV2.Predict.S13HoistFixed

open FateV2.Modeling
open Finset
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [DecidableEq V] [Fintype V] [DecidableEq α] [Fintype α] [Nonempty α]

theorem mass_self_insert {A : Finset V} {g : (V → α) → ℝ}
    (hg : ∀ w w', (∀ u ∈ A, w u = w' u) → g w = g w')
    (x : V → α) :
    Fate.DAGFactorization.mass A g x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card))
        * g (FateV2.Predict.GraphToProbView7.extEnd A x (fun u : ↥A => x u.1)) := by
  rw [FateV2.Predict.GraphToProbView7.mass_eq_card_mul_massA (A := A) (S := A)
    (Finset.Subset.refl _) hg x x]
  congr 1
  rw [Finset.sum_eq_single (fun u : ↥A => x u.1)]
  · simp [FateV2.Predict.GraphToProbView7.sub]
  · intro b _ hb
    simp only [FateV2.Predict.GraphToProbView7.sub, Finset.mem_filter, Finset.mem_univ, true_and]
    have : ∃ u : ↥A, b u ≠ x u.1 := by
      by_contra h; push Not at h; exact hb (funext h)
    obtain ⟨u, hu⟩ := this
    rw [if_neg]; intro hc; exact hu (hc u (by simp))
  · intro h; exact absurd (Finset.mem_univ _) h

-- ⭐ 修正版 mass_insert_of_insensitive：带 |α| 因子
theorem mass_insert_corrected {h : V} {S : Finset V} (sh : h ∉ S)
    {g : (V → α) → ℝ}
    (hins : ∀ x y : V → α, (∀ u ∈ S, x u = y u) → g x = g y)
    (x : V → α) :
    Fate.DAGFactorization.mass S g x
      = (Fintype.card α : ℝ) * Fate.DAGFactorization.mass (insert h S) g x := by
  have hgS : ∀ w w', (∀ u ∈ S, w u = w' u) → g w = g w' := hins
  have hgI : ∀ w w', (∀ u ∈ insert h S, w u = w' u) → g w = g w' := by
    intro w w' hw
    exact hins w w' (fun u hu => hw u (Finset.mem_insert_of_mem hu))
  rw [mass_self_insert hgS x, mass_self_insert hgI x]
  -- 需证：|α|^(|V|-|S|) * g(extEnd S ...) = |α| * (|α|^(|V|-|insert h S|) * g(extEnd (insert h S) ...))
  have hcard : (insert h S).card = S.card + 1 := Finset.card_insert_of_notMem sh
  have hg_eq : g (FateV2.Predict.GraphToProbView7.extEnd S x (fun u : ↥S => x u.1))
      = g (FateV2.Predict.GraphToProbView7.extEnd (insert h S) x (fun u : ↥(insert h S) => x u.1)) := by
    apply hins
    intro u hu
    have e1 : FateV2.Predict.GraphToProbView7.extEnd S x (fun u : ↥S => x u.1) u
        = (fun u : ↥S => x u.1) ⟨u, hu⟩ :=
      FateV2.Predict.GraphToProbView7.extEnd_of_mem S x (fun u : ↥S => x u.1) u hu
    have e2 : FateV2.Predict.GraphToProbView7.extEnd (insert h S) x
        (fun u : ↥(insert h S) => x u.1) u
        = (fun u : ↥(insert h S) => x u.1) ⟨u, Finset.mem_insert_of_mem hu⟩ :=
      FateV2.Predict.GraphToProbView7.extEnd_of_mem (insert h S) x
        (fun u : ↥(insert h S) => x u.1) u (Finset.mem_insert_of_mem hu)
    rw [e1, e2]
  rw [hg_eq, hcard]
  -- 现在：|α|^(|V|-|S|) * g = |α| * (|α|^(|V|-(|S|+1)) * g)
  have hV : (Fintype.card α : ℝ) ^ (Fintype.card V - S.card)
      = (Fintype.card α : ℝ) * (Fintype.card α : ℝ) ^ (Fintype.card V - (S.card + 1)) := by
    have hle : S.card + 1 ≤ Fintype.card V := by
      rw [← hcard, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    rw [← pow_succ' (Fintype.card α : ℝ) (Fintype.card V - (S.card + 1))]
    congr 1
    omega
  rw [hV]
  ring

end FateV2.Predict.S13HoistFixed
