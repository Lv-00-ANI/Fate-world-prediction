import FateWorld.Legacy.TailBlockMassDcomp
import FateWorld.Legacy.CondIndepGeneralNZ

/-! ===========================================================================
  §0  主定理 D：有尾块情形

  ## 目标

  ```lean
  theorem condIndep_tail_block
      (hfac : p w = ∏ v, ψ v w)
      (hread : ReadSet ψ R)
      (hTail : ∀ v ∉ X ∪ Y ∪ Z, R v ⊆ Z)
      (hsplit : Split R X Y Z)
      (hXY hXZ hYZ : 两两不交) :
      CondIndep p X Y Z
  ```

  ## 路线

  记 A := X ∪ Y ∪ Z。

  1. hAll : ∀ v, R v ⊆ A（v ∈ A 用 Split，v ∉ A 用 hTail）
  2. hPA : ∏ v ∈ A, ψ v 只读 A
  3. 四个 mass 用 mass_dcomp_tail：
       mass S p x = Pout(x) * c * A_S(x)
     其中 Pout := ∏ v ∈ outSet A, ψ v，c := |α|^(|V|-|A|)，
     A_S(x) := ∑ wA, if (wA|_S = x|_S) then ∏ v ∈ A, ψ v (extEnd A x wA) else 0
  4. 在 ↥A 上调用 condIndep_general，得 A 上的 CondIndep
  5. 取 wA := x|_A，与第 3 步结合，约去 Pout(x)² c²

  ## 本文件先给第 1、2 步与「A 上的 CondIndep」的接口
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §1 `hAll`：所有读集落在 `A` 内 -/

theorem hAll_of_split_tail {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : Fate.View19.Split R X Y Z)
    (hTail : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z) :
    ∀ v, R v ⊆ X ∪ Y ∪ Z := by
  intro v u hu
  show u ∈ (X ∪ Y) ∪ Z
  by_cases hv : v ∈ X ∪ Y ∪ Z
  · rcases hsplit v with h | h
    · have h1 : u ∈ X ∪ Z := h hu
      rcases Finset.mem_union.mp h1 with h2 | h2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h2)))
      · exact Finset.mem_union.mpr (Or.inr h2)
    · have h1 : u ∈ Y ∪ Z := h hu
      rcases Finset.mem_union.mp h1 with h2 | h2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h2)))
      · exact Finset.mem_union.mpr (Or.inr h2)
  · have h1 : u ∈ Z := hTail v hv hu
    exact Finset.mem_union.mpr (Or.inr h1)

/-! ### §2 `hPA`：`∏ v ∈ A, ψ v` 只读 `A` -/

theorem hPA_of_readSet {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : Fate.View19.ReadSet ψ R) {A : Finset V}
    (hAll : ∀ v, R v ⊆ A) :
    ∀ w w', (∀ u ∈ A, w u = w' u) → (∏ v ∈ A, ψ v w) = (∏ v ∈ A, ψ v w') := by
  intro w w' h
  refine Finset.prod_congr rfl fun v _ => ?_
  exact hread v w w' (fun u hu => h u (hAll v hu))


/-! ### §3 在 `↥A` 上调用 `condIndep_general` -/

variable [Nonempty α]

theorem condIndep_on_A {ψ : V → (V → α) → ℝ} {R : V → Finset V} {X Y Z A : Finset V}
    (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A) (hcover : X ∪ Y ∪ Z = A)
    (hread : Fate.View19.ReadSet ψ R)
    (hAll : ∀ v, R v ⊆ A)
    (hsplit : Fate.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (ω₀ : V → α) :
    Fate.FactorMarkov.CondIndep
      (fun w : ↥A → α => ∏ v : ↥A, ψ v.1 (extEnd A ω₀ w))
      (sub A X hX) (sub A Y hY) (sub A Z hZ) := by
  classical
  -- 记 ψA, pA
  set ψA : ↥A → ((↥A → α) → ℝ) := fun v w => ψ v.1 (extEnd A ω₀ w) with hψA
  set pA : (↥A → α) → ℝ := fun w => ∏ v : ↥A, ψA v w with hpA
  -- RA
  set RA : ↥A → Finset ↥A := fun v => sub A (R v.1) (hAll v.1) with hRA
  -- hfacA
  have hfacA : ∀ w : ↥A → α, pA w = ∏ v, ψA v w := fun w => rfl
  -- hreadA
  have hreadA : Fate.View19.ReadSet ψA RA := by
    intro v x y hxy
    exact readSet_rebase hread A ω₀ (fun v : ↥A => hAll v.1) v x y hxy
  -- hsplitA
  have hAll' : ∀ v : V, R v ⊆ A ∨ v ∉ A := fun v => Or.inl (hAll v)
  have hsplitA : Fate.View19.Split RA (sub A X hX) (sub A Y hY) (sub A Z hZ) :=
    split_rebase hX hY hZ hAll' hsplit
  -- hdisjA
  have hdisjA_XY : Disjoint (sub A X hX) (sub A Y hY) := disjoint_attach hX hY hXY
  have hdisjA_XZ : Disjoint (sub A X hX) (sub A Z hZ) := disjoint_attach hX hZ hXZ
  have hdisjA_YZ : Disjoint (sub A Y hY) (sub A Z hZ) := disjoint_attach hY hZ hYZ
  -- 调用
  exact condIndep_general ψA pA hfacA hreadA hsplitA hdisjA_XY hdisjA_XZ hdisjA_YZ
    (attach_union_univ A X Y Z hX hY hZ hcover)


end Fate.GraphToProbView7
