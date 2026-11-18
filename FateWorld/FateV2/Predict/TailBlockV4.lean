import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.View19FactorGraphSplit
import FateWorld.FateV2.Modeling.BalanceComponents
import FateWorld.FateV2.Modeling.CondIndepGeneralNZ
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace FateV2.Predict.TailBlockV4

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization FateV2.Predict.FactorMarkov FateV2.Predict.View19 FateV2.Predict.GraphToProbView7

universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]
  [Nonempty α]



/-- `ReadsOn f A`：`f` 只读 `A` 上的坐标。 -/
def ReadsOn (f : (V → α) → ℝ) (A : Finset V) : Prop :=
  ∀ w w' : V → α, (∀ u ∈ A, w u = w' u) → f w = f w'

/-- 尾域拼接。 -/
noncomputable def extA (x : V → α) (A S : Finset V) (r : {u : V // u ∈ A ∧ u ∉ S} → α) :
    V → α :=
  fun v => if hv : v ∈ S then x v else if hvA : v ∈ A then r ⟨v, hvA, hv⟩ else x v

theorem extA_of_mem_S {x : V → α} {A S : Finset V}
    (r : {u : V // u ∈ A ∧ u ∉ S} → α) {u : V} (hu : u ∈ S) : extA x A S r u = x u := by
  unfold extA; rw [dif_pos hu]

theorem extA_of_mem_A_notS {x : V → α} {A S : Finset V}
    (r : {u : V // u ∈ A ∧ u ∉ S} → α) {u : V} (huA : u ∈ A) (huS : u ∉ S) :
    extA x A S r u = r ⟨u, huA, huS⟩ := by
  unfold extA; rw [dif_neg huS, dif_pos huA]

/-- 关键：`glue S x t` 与 `extA x A S r` 在 `A` 上一致（当 `r` 是 `t` 的限制）。 -/
theorem glue_extA_agree {x : V → α} {A S : Finset V} (hSA : S ⊆ A)
    (t : {u : V // u ∉ S} → α) :
    ∀ u ∈ A, glue S x t u
      = extA x A S (fun p => t ⟨p.1, p.2.2⟩) u := by
  intro u huA
  by_cases huS : u ∈ S
  · rw [glue_of_mem S x t huS, extA_of_mem_S _ huS]
  · rw [glue_of_not_mem S x t huS, extA_of_mem_A_notS _ huA huS]

/-- 拆解 `{u // u ∉ S}`（`S ⊆ A`）为 `(A ∧ ¬S) ⊔ (¬A)` 上的函数对。 -/
noncomputable def splitEquiv (A S : Finset V) (hSA : S ⊆ A) :
    ({u : V // u ∉ S} → α) ≃
      (({u : V // u ∈ A ∧ u ∉ S} → α) × ({u : V // u ∉ A} → α)) where
  toFun t := (fun p => t ⟨p.1, p.2.2⟩, fun p => t ⟨p.1, fun h => p.2 (hSA h)⟩)
  invFun q := fun s => by
    classical
    exact if hs : s.1 ∈ A then q.1 ⟨s.1, hs, s.2⟩ else q.2 ⟨s.1, hs⟩
  left_inv := by
    classical
    intro t
    funext s
    by_cases hs : s.1 ∈ A
    · simp only [hs, dif_pos]
    · simp only [hs, dif_neg, not_false_iff]
  right_inv := by
    classical
    intro q
    obtain ⟨a, b⟩ := q
    refine Prod.ext ?_ ?_
    · funext p
      simp only [p.2.1, dif_pos]
    · funext p
      have hpA : p.1 ∉ A := p.2
      simp only [dif_neg hpA]

theorem card_tail (A : Finset V) :
    Fintype.card ({u : V // u ∉ A} → α) = Fintype.card α ^ (Fintype.card V - A.card) := by
  rw [Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- ⭐ 尾块常数：`mass S p x = |α|^(|V|-|A|) · massA`。 -/
theorem mass_tail_const {p : (V → α) → ℝ} {A S : Finset V} (hSA : S ⊆ A)
    (hp : ReadsOn p A) (x : V → α) :
    mass S p x = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) *
      ∑ r : ({u : V // u ∈ A ∧ u ∉ S} → α), p (extA x A S r) := by
  classical
  rw [mass_eq_sum_glue]
  rw [Fintype.sum_equiv (splitEquiv A S hSA)
    (fun t => p (glue S x t))
    (fun q => p (glue S x ((splitEquiv A S hSA).symm q)))
    (fun t => by simp)]
  rw [Fintype.sum_prod_type]
  -- 对每个 `r`（`A\S` 部分），尾部求和是常数
  have key : ∀ r : ({u : V // u ∈ A ∧ u ∉ S} → α),
      (∑ s : ({u : V // u ∉ A} → α), p (glue S x ((splitEquiv A S hSA).symm (r, s))))
        = ((Fintype.card ({u : V // u ∉ A} → α) : ℕ) : ℝ) * p (extA x A S r) := by
    intro r
    have hconst : ∀ s : ({u : V // u ∉ A} → α),
        p (glue S x ((splitEquiv A S hSA).symm (r, s))) = p (extA x A S r) := by
      intro s
      have hes : (splitEquiv A S hSA) ((splitEquiv A S hSA).symm (r, s)) = (r, s) :=
        (splitEquiv A S hSA).apply_symm_apply (r, s)
      have h1 : ∀ p : {u : V // u ∈ A ∧ u ∉ S}, ((splitEquiv A S hSA).symm (r, s)) ⟨p.1, p.2.2⟩
          = r p := by
        intro p
        have := congrArg Prod.fst hes
        exact congrFun this p
      refine hp _ _ fun u huA => ?_
      have hfun : ((fun p : {u : V // u ∈ A ∧ u ∉ S} =>
          ((splitEquiv A S hSA).symm (r, s)) ⟨p.1, p.2.2⟩)) = r := by
        funext p
        have := congrArg Prod.fst hes
        exact congrFun this p
      rw [glue_extA_agree hSA _ u huA, hfun]
    calc ∑ s, p (glue S x ((splitEquiv A S hSA).symm (r, s)))
        = ∑ _s : ({u : V // u ∉ A} → α), p (extA x A S r) :=
          Finset.sum_congr rfl fun s _ => hconst s
      _ = ((Fintype.card ({u : V // u ∉ A} → α) : ℕ) : ℝ) * p (extA x A S r) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun r _ => key r, ← Finset.mul_sum, card_tail]
  push_cast
  ring


/-!
  # Predict · TailBlockV4

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailBlockV4.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization, FactorMarkov, View19FactorGraphSplit, BalanceComponents, CondIndepGeneralNZ
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## massA 层级 -/

noncomputable def massA (A S : Finset V) (p : (V → α) → ℝ) (x : V → α) : ℝ :=
  ∑ r : ({u : V // u ∈ A ∧ u ∉ S} → α), p (extA x A S r)

theorem extA_self {x : V → α} {A : Finset V} (r : {u : V // u ∈ A ∧ u ∉ A} → α) :
    extA x A A r = x := by
  funext v
  by_cases hv : v ∈ A
  · exact extA_of_mem_S _ hv
  · unfold extA; rw [dif_neg hv, dif_neg hv]

theorem card_empty_idx (A : Finset V) :
    Fintype.card ({u : V // u ∈ A ∧ u ∉ A} → α) = 1 := by
  have hempty : IsEmpty {u : V // u ∈ A ∧ u ∉ A} :=
    ⟨fun p => p.2.2 p.2.1⟩
  haveI := hempty
  rw [Fintype.card_fun]
  simp

theorem massA_self {p : (V → α) → ℝ} {A : Finset V} (x : V → α) :
    massA A A p x = p x := by
  classical
  unfold massA
  rw [Finset.sum_congr rfl (fun r _ => by rw [extA_self])]
  rw [Finset.sum_const, Finset.card_univ, card_empty_idx, nsmul_eq_mul]
  norm_num

/-- `ReadsOn g S`（`S ⊆ A`）⟹ `g (extA x A S r) = g x`。 -/
theorem reads_extA {g : (V → α) → ℝ} {A S : Finset V} (hg : ReadsOn g S)
    (x : V → α) (r : {u : V // u ∈ A ∧ u ∉ S} → α) :
    g (extA x A S r) = g x := by
  refine hg _ _ fun u hu => ?_
  exact extA_of_mem_S _ hu

theorem massA_frozen_mul (f : (V → α) → ℝ) (g : (V → α) → ℝ) {A S : Finset V}
    (hf : ReadsOn f S) (x : V → α) :
    massA A S (fun w => f w * g w) x = f x * massA A S g x := by
  classical
  unfold massA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  show f (extA x A S r) * g (extA x A S r) = f x * g (extA x A S r)
  rw [reads_extA hf x r]

theorem massA_prod_cover (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    (hread : ReadSet ψ R) {A S : Finset V} (W : Finset V)
    (hW : ∀ v ∈ W, R v ⊆ S) (g : (V → α) → ℝ) (x : V → α) :
    massA A S (fun w => (∏ v ∈ W, ψ v w) * g w) x
      = (∏ v ∈ W, ψ v x) * massA A S g x := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    show massA A S (fun w => (1 : ℝ) * g w) x = 1 * massA A S g x
    rw [massA_frozen_mul (fun _ => (1:ℝ)) g (fun _ _ _ => rfl) x]
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have hW' : ∀ v ∈ s, R v ⊆ S := fun v hv => hW v (Finset.mem_insert_of_mem hv)
    have haS : R a ⊆ S := hW a (Finset.mem_insert_self a s)
    have hfr : ReadsOn (ψ a) S := fun w w' h => hread a w w' (fun u hu => h u (haS hu))
    have ih' := ih hW'
    have hsplit : (fun w => (ψ a w * ∏ v ∈ s, ψ v w) * g w)
        = (fun w => ψ a w * ((∏ v ∈ s, ψ v w) * g w)) := by
      funext w; ring
    rw [hsplit, massA_frozen_mul _ _ hfr x, ih']
    ring


/-! ## massA 的 Z-分离 -/

section Sep

variable {X Y Z : Finset V}

/-- `A = X ∪ Y ∪ Z` 且 `u ∈ A`、`u ∉ Z`、`u ∉ X` ⟹ `u ∈ Y`。 -/
theorem mem_Y_of {A X Y Z : Finset V} (hA : A = X ∪ Y ∪ Z) {u : V}
    (huA : u ∈ A) (huZ : u ∉ Z) (huX : u ∉ X) : u ∈ Y := by
  rw [hA] at huA
  rcases Finset.mem_union.mp huA with h | h
  · rcases Finset.mem_union.mp h with h' | h'
    · exact absurd h' huX
    · exact h'
  · exact absurd h huZ

/-- `A = X ∪ Y ∪ Z` 且 `u ∈ A`、`u ∉ Z`、`u ∉ Y` ⟹ `u ∈ X`。 -/
theorem mem_X_of {A X Y Z : Finset V} (hA : A = X ∪ Y ∪ Z) {u : V}
    (huA : u ∈ A) (huZ : u ∉ Z) (huY : u ∉ Y) : u ∈ X := by
  rw [hA] at huA
  rcases Finset.mem_union.mp huA with h | h
  · rcases Finset.mem_union.mp h with h' | h'
    · exact h'
    · exact absurd h' huY
  · exact absurd h huZ

/-- 包含映射 `{u // u ∈ A ∧ u ∉ X∪Z} → {u // u ∈ A ∧ u ∉ Z}`。 -/
def i₁ {A X Z : Finset V} (p : {u : V // u ∈ A ∧ u ∉ (X ∪ Z)}) :
    {u : V // u ∈ A ∧ u ∉ Z} :=
  ⟨p.1, p.2.1, fun h => p.2.2 (Finset.mem_union.mpr (Or.inr h))⟩

/-- 包含映射 `{u // u ∈ A ∧ u ∉ Y∪Z} → {u // u ∈ A ∧ u ∉ Z}`。 -/
def i₂ {A Y Z : Finset V} (p : {u : V // u ∈ A ∧ u ∉ (Y ∪ Z)}) :
    {u : V // u ∈ A ∧ u ∉ Z} :=
  ⟨p.1, p.2.1, fun h => p.2.2 (Finset.mem_union.mpr (Or.inr h))⟩

/-- ⭐ 分解 `{u // u ∈ A ∧ u ∉ Z}` 为 X 侧与 Y 侧。 -/
noncomputable def zEquivA {A X Y Z : Finset V} (hA : A = X ∪ Y ∪ Z) (hXY : Disjoint X Y) :
    ({u : V // u ∈ A ∧ u ∉ Z} → α) ≃
      (({u : V // u ∈ A ∧ u ∉ (X ∪ Z)} → α) ×
        ({u : V // u ∈ A ∧ u ∉ (Y ∪ Z)} → α)) where
  toFun r := (fun p => r (i₁ p), fun p => r (i₂ p))
  invFun q := fun z => by
    classical
    exact if hz : z.1 ∈ X
      then q.2 ⟨z.1, z.2.1, by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun h => Finset.disjoint_left.mp hXY hz h, z.2.2⟩⟩
      else q.1 ⟨z.1, z.2.1, by
        simp only [Finset.mem_union, not_or]
        exact ⟨hz, z.2.2⟩⟩
  left_inv := by
    classical
    intro r
    funext z
    by_cases hz : z.1 ∈ X
    · simp only [dif_pos hz]
      exact congrArg r (Subtype.ext rfl)
    · simp only [dif_neg hz]
      exact congrArg r (Subtype.ext rfl)
  right_inv := by
    classical
    intro q
    obtain ⟨a, b⟩ := q
    refine Prod.ext ?_ ?_
    · funext p
      have hpX : p.1 ∉ X := fun h => p.2.2 (Finset.mem_union.mpr (Or.inl h))
      show (if h : p.1 ∈ X then _ else _) = a p
      rw [dif_neg hpX]
      exact congrArg a (Subtype.ext rfl)
    · funext p
      have hpY : p.1 ∉ Y := fun h => p.2.2 (Finset.mem_union.mpr (Or.inl h))
      have hpZ : p.1 ∉ Z := fun h => p.2.2 (Finset.mem_union.mpr (Or.inr h))
      have hpX : p.1 ∈ X := mem_X_of hA p.2.1 hpZ hpY
      show (if h : p.1 ∈ X then _ else _) = b p
      rw [dif_pos hpX]
      exact congrArg b (Subtype.ext rfl)

/-- 在 `X ∪ Z` 上：`extA x A Z r` 与 `extA x A (Y∪Z) b` 一致（`b` 是 `r` 的 Y 分量）。 -/
theorem extA_agree_XZ {A X Y Z : Finset V} (hA : A = X ∪ Y ∪ Z) (hXY : Disjoint X Y)
    (x : V → α) (r : {u : V // u ∈ A ∧ u ∉ Z} → α) :
    ∀ u ∈ X ∪ Z, extA x A Z r u = extA x A (Y ∪ Z) ((zEquivA hA hXY r).2) u := by
  intro u hu
  by_cases huz : u ∈ Z
  · rw [extA_of_mem_S _ huz, extA_of_mem_S _ (Finset.mem_union.mpr (Or.inr huz))]
  · have huX : u ∈ X := by
      rcases Finset.mem_union.mp hu with h | h
      · exact h
      · exact absurd h huz
    have huY : u ∉ Y := fun h => Finset.disjoint_left.mp hXY huX h
    have huA : u ∈ A := by rw [hA]; exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl huX)))
    have huYZ : u ∉ Y ∪ Z := by
      simp only [Finset.mem_union, not_or]; exact ⟨huY, huz⟩
    rw [extA_of_mem_A_notS _ huA huz, extA_of_mem_A_notS _ huA huYZ]
    rfl

/-- 在 `Y ∪ Z` 上：`extA x A Z r` 与 `extA x A (X∪Z) a` 一致（`a` 是 `r` 的 X 分量）。 -/
theorem extA_agree_YZ {A X Y Z : Finset V} (hA : A = X ∪ Y ∪ Z) (hXY : Disjoint X Y)
    (x : V → α) (r : {u : V // u ∈ A ∧ u ∉ Z} → α) :
    ∀ u ∈ Y ∪ Z, extA x A Z r u = extA x A (X ∪ Z) ((zEquivA hA hXY r).1) u := by
  intro u hu
  by_cases huz : u ∈ Z
  · rw [extA_of_mem_S _ huz, extA_of_mem_S _ (Finset.mem_union.mpr (Or.inr huz))]
  · have huY : u ∈ Y := by
      rcases Finset.mem_union.mp hu with h | h
      · exact h
      · exact absurd h huz
    have huX : u ∉ X := fun h => Finset.disjoint_left.mp hXY h huY
    have huA : u ∈ A := by rw [hA]; exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr huY)))
    have huXZ : u ∉ X ∪ Z := by
      simp only [Finset.mem_union, not_or]; exact ⟨huX, huz⟩
    rw [extA_of_mem_A_notS _ huA huz, extA_of_mem_A_notS _ huA huXZ]
    rfl

/-- ⭐⭐⭐ `massA Z` 的 X/Y 分离。 -/
theorem massA_sep_Z (F G : (V → α) → ℝ) {A X Y Z : Finset V}
    (hA : A = X ∪ Y ∪ Z) (hXY : Disjoint X Y)
    (hFXZ : ReadsOn F (X ∪ Z)) (hGYZ : ReadsOn G (Y ∪ Z)) (x : V → α) :
    massA A Z (fun w => F w * G w) x
      = massA A (X ∪ Z) G x * massA A (Y ∪ Z) F x := by
  classical
  unfold massA
  rw [Fintype.sum_equiv (zEquivA hA hXY)
    (fun r => F (extA x A Z r) * G (extA x A Z r))
    (fun q => F (extA x A Z ((zEquivA hA hXY).symm q))
      * G (extA x A Z ((zEquivA hA hXY).symm q))) (fun r => by simp)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hes : (zEquivA hA hXY) ((zEquivA hA hXY).symm (a, b)) = (a, b) :=
    (zEquivA hA hXY).apply_symm_apply (a, b)
  have h1 : (zEquivA hA hXY ((zEquivA hA hXY).symm (a, b))).1 = a := by rw [hes]
  have h2 : (zEquivA hA hXY ((zEquivA hA hXY).symm (a, b))).2 = b := by rw [hes]
  have e1 : ∀ u ∈ X ∪ Z, extA x A Z ((zEquivA hA hXY).symm (a, b)) u
      = extA x A (Y ∪ Z) b u := by
    intro u hu
    rw [extA_agree_XZ hA hXY x ((zEquivA hA hXY).symm (a, b)) u hu, h2]
  have e2 : ∀ u ∈ Y ∪ Z, extA x A Z ((zEquivA hA hXY).symm (a, b)) u
      = extA x A (X ∪ Z) a u := by
    intro u hu
    rw [extA_agree_YZ hA hXY x ((zEquivA hA hXY).symm (a, b)) u hu, h1]
  rw [hGYZ _ _ e2, hFXZ _ _ e1]
  ring

end Sep



theorem readsOn_prod (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    {W S : Finset V} (hW : ∀ v ∈ W, R v ⊆ S) :
    ReadsOn (fun w => ∏ v ∈ W, ψ v w) S := by
  intro w w' h
  exact Finset.prod_congr rfl fun v hv => hread v w w' (fun u hu => h u (hW v hv hu))

theorem subset_Z_A (X Y Z : Finset V) : Z ⊆ X ∪ Y ∪ Z :=
  fun u hu => Finset.mem_union.mpr (Or.inr hu)

theorem subset_XZ_A (X Y Z : Finset V) : X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases Finset.mem_union.mp hu with h | h
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
  · exact Finset.mem_union.mpr (Or.inr h)

theorem subset_YZ_A (X Y Z : Finset V) : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases Finset.mem_union.mp hu with h | h
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
  · exact Finset.mem_union.mpr (Or.inr h)

/-! ## §3 ⭐⭐⭐⭐ 主定理 D：`condIndep_tail_block` -/


/-- `hsplit` 单独给出 `∀ v, R v ⊆ A`（`A := X ∪ Y ∪ Z`）。 -/
theorem readsets_subset_union {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : Split R X Y Z) : ∀ v, R v ⊆ X ∪ Y ∪ Z := by
  intro v
  rcases hsplit v with h | h
  · exact Finset.Subset.trans h (by
      intro u hu
      rcases Finset.mem_union.mp hu with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h')))
      · exact Finset.mem_union.mpr (Or.inr h'))
  · exact Finset.Subset.trans h (by
      intro u hu
      rcases Finset.mem_union.mp hu with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h')))
      · exact Finset.mem_union.mpr (Or.inr h'))

/-- ⭐⭐⭐⭐ **主定理 D（尾块版）**。

`p = ∏ v, ψ v`，读集满足 `Split R X Y Z`（`X`、`Y`、`Z` 两两不交），
**不要求 `X ∪ Y ∪ Z = univ`** ⟹ 仍然有 `CondIndep p X Y Z`。

核心：`p` 只读 `A := X ∪ Y ∪ Z`，故每个 `mass S p x`（`S ⊆ A`）都等于
`|α|^(|V|-|A|) · massA S`，**同一个常数**。于是 `CondIndep` 的两边
`|α|^(2d)` 因子直接约掉，问题退化为 `A` 上的「无尾」情形（按三块分解计算）。 -/
theorem condIndep_tail_block (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (_hTail : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (_hXZ : Disjoint X Z) (_hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z := by
  classical
  have hAll : ∀ v, R v ⊆ X ∪ Y ∪ Z := readsets_subset_union hsplit
  have hreadsP : ReadsOn p (X ∪ Y ∪ Z) := by
    intro w w' h
    rw [hfac w, hfac w']
    exact Finset.prod_congr rfl fun v _ => hread v w w' (fun u hu => h u (hAll v hu))
  set Pz : (V → α) → ℝ := fun w => ∏ v ∈ Wblk R Z, ψ v w with hPz
  set F : (V → α) → ℝ := fun w => ∏ v ∈ WF R X Z, ψ v w with hF
  set G : (V → α) → ℝ := fun w => ∏ v ∈ WG R Y Z, ψ v w with hG
  set A : Finset V := X ∪ Y ∪ Z with hA
  have hAeq : A = X ∪ Y ∪ Z := hA
  have hpFG : ∀ w, p w = Pz w * F w * G w := by
    intro w
    rw [hfac w]
    exact prod_univ_split ψ hsplit hXY w
  -- 读集局部性
  have hPzZ : ReadsOn Pz Z :=
    readsOn_prod ψ hread (fun v hv => (mem_Wblk.mp hv))
  have hFXZ : ReadsOn F (X ∪ Z) :=
    readsOn_prod ψ hread (fun v hv => (mem_WF.mp hv).1)
  have hGYZ : ReadsOn G (Y ∪ Z) :=
    readsOn_prod ψ hread (fun v hv => (mem_WG.mp hv).1)
  intro x
  -- 四个 `mass` = `|α|^d * massA`
  have hmA : mass A p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) * massA A A p x :=
    mass_tail_const (Finset.Subset.refl A) hreadsP x
  have hmZ : mass Z p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) * massA A Z p x :=
    mass_tail_const (by rw [hA]; exact subset_Z_A X Y Z) hreadsP x
  have hmXZ : mass (X ∪ Z) p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) * massA A (X ∪ Z) p x :=
    mass_tail_const (by rw [hA]; exact subset_XZ_A X Y Z) hreadsP x
  have hmYZ : mass (Y ∪ Z) p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) * massA A (Y ∪ Z) p x :=
    mass_tail_const (by rw [hA]; exact subset_YZ_A X Y Z) hreadsP x
  -- `massA` 层的三块计算
  have hpAZ : p = fun w => (∏ v ∈ Wblk R Z, ψ v w) * (F w * G w) := funext fun w => by
    rw [hpFG w]; ring
  have hWZ_sub : ∀ v ∈ Wblk R Z, R v ⊆ Z := fun v hv => mem_Wblk.mp hv
  have hmA_A : massA A A p x = Pz x * F x * G x := by
    rw [massA_self]; exact hpFG x
  have hmA_Z : massA A Z p x = Pz x * massA A Z (fun w => F w * G w) x := by
    rw [hpAZ, massA_prod_cover ψ hread (Wblk R Z) hWZ_sub (fun w => F w * G w) x]
  have hmA_XZ : massA A (X ∪ Z) p x = Pz x * F x * massA A (X ∪ Z) G x := by
    rw [hpAZ, massA_prod_cover ψ hread (Wblk R Z)
      (fun v hv => Finset.Subset.trans (hWZ_sub v hv) Finset.subset_union_right)
      (fun w => F w * G w) x,
      massA_frozen_mul F G hFXZ x]
    show (∏ v ∈ Wblk R Z, ψ v x) * (F x * massA A (X ∪ Z) G x)
      = Pz x * F x * massA A (X ∪ Z) G x
    rw [hPz]; ring
  have hmA_YZ : massA A (Y ∪ Z) p x = Pz x * G x * massA A (Y ∪ Z) F x := by
    rw [hpAZ, massA_prod_cover ψ hread (Wblk R Z)
      (fun v hv => Finset.Subset.trans (hWZ_sub v hv) Finset.subset_union_right)
      (fun w => F w * G w) x]
    have hswap : massA A (Y ∪ Z) (fun w => F w * G w) x
        = G x * massA A (Y ∪ Z) F x := by
      rw [show (fun w => F w * G w) = (fun w => G w * F w) from funext fun w => mul_comm _ _]
      exact massA_frozen_mul G F hGYZ x
    rw [hswap]
    show (∏ v ∈ Wblk R Z, ψ v x) * (G x * massA A (Y ∪ Z) F x)
      = Pz x * G x * massA A (Y ∪ Z) F x
    rw [hPz]; ring
  have hsep : massA A Z (fun w => F w * G w) x
      = massA A (X ∪ Z) G x * massA A (Y ∪ Z) F x :=
    massA_sep_Z F G hAeq hXY hFXZ hGYZ x
  -- 收口
  show mass A p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x
  rw [hmA, hmZ, hmXZ, hmYZ, hmA_A, hmA_Z, hmA_XZ, hmA_YZ, hsep]
  ring


/-! ## §4 自检

**`hTail` 是冗余的**：`readsets_subset_union` 表明 `Split` 单独即给出
`∀ v, R v ⊆ A`，故主证明里 `hTail` 从不被使用（Lean 侧由 `_hTail` 命名佐证，
编译无 unused-variable 警告即证其未被引用）。保留形参只为与任务书签名一致。

**`hcover` 退化**：`X ∪ Y ∪ Z = univ` 时结论与 `CondIndepGeneralNZ.condIndep_general` 一致。
-/

/-- ⭐ 自检：`hTail` 与 `Split` 的关系 —— `Split` 给出的读集界更强（`A` 而非 `Z`）。 -/
theorem split_gives_subset_A {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : FateV2.Predict.View19.Split R X Y Z) : ∀ v, R v ⊆ X ∪ Y ∪ Z :=
  readsets_subset_union hsplit

/-- ⭐ 自检：`hcover` 情形下本定理可直接替代 `condIndep_general`。 -/
theorem condIndep_of_cover (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_tail_block ψ p hfac hread
    (fun v hv => by rw [hcover] at hv; exact absurd (Finset.mem_univ v) hv)
    hsplit hXY hXZ hYZ

end FateV2.Predict.TailBlockV4