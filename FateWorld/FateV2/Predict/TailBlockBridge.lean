import FateWorld.FateV2.Predict.TailBlockCondIndep
/-!
  # Predict · TailBlockBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailBlockBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TailBlockCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  主定理 D 的桥接层

  ## 内容

  1. `sum_eq_massA`：`mass_dcomp_tail` 右边的求和**就是** `↥A` 上的 `mass`。
  2. `mass_eq_Pout_massA`：把 `mass S p x` 直接写成
     `Pout(x) * (mass^{↥A}(sub A S) * c)` 的形式。

  ## 语义

  `mass_dcomp_tail` 说 `mass S p x = Pout(x) * c * (A 上的求和)`。
  本文件证明那个「A 上的求和」恰好是 `↥A` 上的 `mass`（用 `unfold mass` +
  `← Finset.prod_coe_sort`）。这样就能把 V 上的 mass 与 A 上的 mass 对上，
  从而把 `condIndep_on_A` 的结论搬回 V。
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open FateV2.Modeling

open Finset FateV2.Error FateV2.Predict.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-- 桥接：mass_dcomp_tail 右边的求和就是 ↥A 上的 mass -/
theorem sum_eq_massA {A S : Finset V} (hSA : S ⊆ A) {ψ : V → (V → α) → ℝ}
    (ω₀ : V → α) (x : V → α) :
    (∑ wA : (↥A → α),
        if (∀ u ∈ sub A S hSA, wA u = x u.1)
          then ∏ v ∈ A, ψ v (extEnd A ω₀ wA) else 0)
      = Fate.DAGFactorization.mass (sub A S hSA)
          (fun w : ↥A → α => ∏ v : ↥A, ψ v.1 (extEnd A ω₀ w))
          (fun u : ↥A => x u.1) := by
  unfold Fate.DAGFactorization.mass
  refine Finset.sum_congr rfl fun wA _ => ?_
  by_cases h : ∀ u ∈ sub A S hSA, wA u = x u.1
  · rw [if_pos h, if_pos h, ← Finset.prod_coe_sort]
  · rw [if_neg h, if_neg h]

/-- mass S p x = Pout(x) * (massA * c) -/
theorem mass_eq_Pout_massA {A S Z : Finset V} (hSA : S ⊆ A) (hZS : Z ⊆ S)
    {ψ : V → (V → α) → ℝ} {R : V → Finset V} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w) (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v ⊆ Z)
    (hPA : ∀ w w', (∀ u ∈ A, w u = w' u) → (∏ v ∈ A, ψ v w) = (∏ v ∈ A, ψ v w'))
    (x : V → α) :
    Fate.DAGFactorization.mass S p x
      = (∏ v ∈ outSet A, ψ v x)
        * (Fate.DAGFactorization.mass (sub A S hSA)
            (fun w : ↥A → α => ∏ v : ↥A, ψ v.1 (extEnd A x w))
            (fun u : ↥A => x u.1)
          * ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card))) := by
  rw [mass_dcomp_tail hSA hZS hfac hread hOut hPA x]
  rw [sum_eq_massA hSA x]
  ring


/-! ### §3 四个 mass 与 condIndep_on_A 的对接 -/

variable [Nonempty α]

/-- ⭐ **`sub A A` 与三块并的关系**（`X ∪ Y ∪ Z = A` 时）。 -/
theorem sub_union_eq_sub_A {A X Y Z : Finset V} (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (hcover : X ∪ Y ∪ Z = A) :
    (sub A X hX ∪ sub A Y hY ∪ sub A Z hZ : Finset ↥A) = sub A A (Finset.Subset.refl A) := by
  ext v
  simp only [mem_sub_iff, Finset.mem_union]
  constructor
  · intro _; exact v.2
  · intro _
    have h : (v : V) ∈ X ∪ Y ∪ Z := hcover ▸ v.2
    rcases Finset.mem_union.mp h with h1 | h1
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · exact Or.inl (Or.inl h2)
      · exact Or.inl (Or.inr h2)
    · exact Or.inr h1

/-- ⭐⭐⭐⭐ **主定理 D（有尾块情形）** -/
theorem condIndep_tail_block {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hTail : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z := by
  classical
  intro x
  set A := X ∪ Y ∪ Z with hA
  have hAll : ∀ v, R v ⊆ A := hAll_of_split_tail hsplit hTail
  have hPA := hPA_of_readSet hread hAll
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
  have hZZ : Z ⊆ Z := Finset.Subset.refl Z
  have hZXZ : Z ⊆ X ∪ Z := fun u hu => Finset.mem_union.mpr (Or.inr hu)
  have hZYZ : Z ⊆ Y ∪ Z := fun u hu => Finset.mem_union.mpr (Or.inr hu)
  -- hcover : X ∪ Y ∪ Z = A（定义上）
  have hcover : X ∪ Y ∪ Z = A := hA.symm
  -- 四个 mass 的分解（先做，避免 rw 顺序问题）
  have e1 := mass_eq_Pout_massA hAA hZA hfac hread hTail hPA x
  have e2 := mass_eq_Pout_massA hZA hZZ hfac hread hTail hPA x
  have e3 := mass_eq_Pout_massA hXA' hZXZ hfac hread hTail hPA x
  have e4 := mass_eq_Pout_massA hYA' hZYZ hfac hread hTail hPA x
  -- condIndep_on_A 在 xA 处的等式
  have hCondA := condIndep_on_A hXA hYA hZA hcover hread hAll hsplit hXY hXZ hYZ x
  have hkey := hCondA (fun u : ↥A => x u.1)
  -- 把 sub A X ∪ sub A Y ∪ sub A Z 换成 sub A A
  rw [sub_union_eq_sub_A hXA hYA hZA hcover] at hkey
  -- sub A X ∪ sub A Z = sub A (X∪Z)，sub A Y ∪ sub A Z = sub A (Y∪Z)
  have hXZ : (sub A X hXA ∪ sub A Z hZA : Finset ↥A) = sub A (X ∪ Z) hXA' := by
    ext v
    simp only [mem_sub_iff, Finset.mem_union]
  have hYZ : (sub A Y hYA ∪ sub A Z hZA : Finset ↥A) = sub A (Y ∪ Z) hYA' := by
    ext v
    simp only [mem_sub_iff, Finset.mem_union]
  rw [hXZ, hYZ] at hkey
  -- 现在收口：把目标两边都用 e1..e4 重写，再用 hkey
  rw [e1, e2, e3, e4]
  -- 目标：Pout * (m1 * c) * (Pout * (m2 * c)) = Pout * (m3 * c) * (Pout * (m4 * c))
  -- hkey：m1 * m2 = m3 * m4
  -- 目标：Pout * (m1*c) * (Pout * (m2*c)) = Pout * (m3*c) * (Pout * (m4*c))
  -- hkey：m1 * m2 = m3 * m4
  linear_combination
    ((∏ v ∈ outSet A, ψ v x) ^ 2 *
      ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) ^ 2) * hkey

end FateV2.Predict.GraphToProbView7
