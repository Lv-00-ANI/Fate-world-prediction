import FateWorld.Legacy.TailBlockReal
import FateWorld.Legacy.MassADecompFinal
import FateWorld.Legacy.TailBlockCondIndep
import FateWorld.Legacy.TailBlockBridge

/-! ===========================================================================
  §0  真正有尾块的主定理：`A` 上因子化 + 所有读集落在 `A` 内

  ## 前提（都不蕴含 `A = univ`，不坍缩）

  * `hfacA : p w = ∏ v ∈ A, ψ v w`（只在 `A` 上因子化，尾块已边缘化）
  * `hA : ∀ v, R v ⊆ A`（所有因子的读集落在 `A` 内）

  ## 路线

  1. `p` 只读 `A`
  2. `mass_eq_card_mul_massA`：`mass S p x = c * (∑ wA, ...)`
  3. `sum_eq_massA`：那个求和就是 `↥A` 上的 mass
  4. `condIndep_on_A`：得 `↥A` 上的 `CondIndep`
  5. 纯代数：`(c*m1)*(c*m2) = (c*m3)*(c*m4)` 由 `m1*m2 = m3*m4` 得

  为避免 Lean 的 whnf 超时，四个 mass 的等式都用 `set` 命名，最后一步只用抽象代数。
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-- 纯代数：`m1 * m2 = m3 * m4` ⟹ `(c*m1)*(c*m2) = (c*m3)*(c*m4)`。 -/
theorem alg_step (c m1 m2 m3 m4 : ℝ) (h : m1 * m2 = m3 * m4) :
    (c * m1) * (c * m2) = (c * m3) * (c * m4) := by
  linear_combination (c ^ 2) * h

/-- 辅助：`p` 只读 `A`（当 `hfacA` 与 `hA`、`hread` 成立时）。 -/
theorem hp_of_facA {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    {p : (V → α) → ℝ} (hfacA : ∀ w, p w = ∏ v ∈ A, ψ v w)
    (hread : Fate.View19.ReadSet ψ R) (hA : ∀ v, R v ⊆ A) :
    ∀ w w', (∀ u ∈ A, w u = w' u) → p w = p w' := by
  intro w w' h
  rw [hfacA w, hfacA w']
  refine Finset.prod_congr rfl fun v _ => ?_
  exact hread v w w' (fun u hu => h u (hA v hu))

/-- 辅助：`mass S p x = c * mass (sub A S) pA (x|_A)`，其中 `pA := ∏ v : ↥A, ψ v.1 ∘ extEnd`。 -/
theorem mass_eq_c_mul_massA {A S : Finset V} (hSA : S ⊆ A)
    {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    (hfacA : ∀ w, p w = ∏ v ∈ A, ψ v w) (hp : ∀ w w', (∀ u ∈ A, w u = w' u) → p w = p w')
    (x : V → α) :
    Fate.DAGFactorization.mass S p x
      = (Fintype.card α : ℝ) ^ (Fintype.card V - A.card)
        * Fate.DAGFactorization.mass (sub A S hSA)
            (fun w : ↥A → α => ∏ v : ↥A, ψ v.1 (extEnd A x w)) (fun u : ↥A => x u.1) := by
  rw [mass_eq_card_mul_massA hSA hp x x]
  congr 1
  have e : (∑ wA : (↥A → α), if (∀ u ∈ sub A S hSA, wA u = x u.1)
      then p (extEnd A x wA) else 0)
      = (∑ wA : (↥A → α), if (∀ u ∈ sub A S hSA, wA u = x u.1)
          then ∏ v ∈ A, ψ v (extEnd A x wA) else 0) := by
    refine Finset.sum_congr rfl fun wA _ => ?_
    by_cases h : ∀ u ∈ sub A S hSA, wA u = x u.1
    · rw [if_pos h, if_pos h, hfacA]
    · rw [if_neg h, if_neg h]
  rw [e, sum_eq_massA hSA (ω₀ := x) x]

/-- ⭐⭐⭐⭐ **主定理 D（真正有尾块版）**：`A` 上因子化 + 所有读集 ⊆ `A`。 -/
theorem condIndep_tail_HA {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfacA : ∀ w, p w = ∏ v ∈ X ∪ Y ∪ Z, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hA : ∀ v, R v ⊆ X ∪ Y ∪ Z)
    (hsplit : Fate.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    Fate.FactorMarkov.CondIndep p X Y Z := by
  classical
  intro x
  set A := X ∪ Y ∪ Z with hAdef
  have hp := hp_of_facA (A := A) hfacA hread hA
  -- 子集关系
  have hAA : A ⊆ A := Finset.Subset.refl A
  have hXA : X ⊆ A := fun u hu => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hu)))
  have hYA : Y ⊆ A := fun u hu => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hu)))
  have hZA : Z ⊆ A := fun u hu => Finset.mem_union.mpr (Or.inr hu)
  have hXA' : X ∪ Z ⊆ A := fun u hu => by
    rcases Finset.mem_union.mp hu with h1 | h1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1)))
    · exact Finset.mem_union.mpr (Or.inr h1)
  have hYA' : Y ∪ Z ⊆ A := fun u hu => by
    rcases Finset.mem_union.mp hu with h1 | h1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h1)))
    · exact Finset.mem_union.mpr (Or.inr h1)
  -- 四个 mass 的等式（用 set 命名避免展开）
  have e1 := mass_eq_c_mul_massA (A := A) (S := A) hAA hfacA hp x
  have e2 := mass_eq_c_mul_massA (A := A) (S := Z) hZA hfacA hp x
  have e3 := mass_eq_c_mul_massA (A := A) (S := X ∪ Z) hXA' hfacA hp x
  have e4 := mass_eq_c_mul_massA (A := A) (S := Y ∪ Z) hYA' hfacA hp x
  -- A 上的 CondIndep
  have hcover : X ∪ Y ∪ Z = A := hAdef.symm
  have hCondA := condIndep_on_A hXA hYA hZA hcover hread hA hsplit hXY hXZ hYZ x
  have hkey := hCondA (fun u : ↥A => x u.1)
  rw [sub_union_eq_sub_A hXA hYA hZA hcover] at hkey
  have hXZ' : (sub A X hXA ∪ sub A Z hZA : Finset ↥A) = sub A (X ∪ Z) hXA' := by
    ext v; simp only [mem_sub_iff, Finset.mem_union]
  have hYZ' : (sub A Y hYA ∪ sub A Z hZA : Finset ↥A) = sub A (Y ∪ Z) hYA' := by
    ext v; simp only [mem_sub_iff, Finset.mem_union]
  rw [hXZ', hYZ'] at hkey
  -- 收口：把四个 mass 各自命名，再用 alg_step
  rw [e1, e2, e3, e4]
  exact alg_step ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) _ _ _ _ hkey

end Fate.GraphToProbView7
