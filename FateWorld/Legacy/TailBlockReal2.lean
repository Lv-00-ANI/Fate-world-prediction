/-
================================================================================
  TailBlockReal2.lean   （暂存版；主控验证后可改名为 Fate/TailBlockReal2.lean）

  主定理 D 的**真正有尾块**版本：`A` 外因子不读 `A` 内坐标。

  ## 本文件相对任务书的三处**修正**（重要，见文末 §5 的说明）

  1. **第三步的 `hsplit : Split R X Y Z` 必须弱化。**
     `Split R X Y Z` 的定义是 `∀ v, R v ⊆ X∪Z ∨ R v ⊆ Y∪Z`，**对全部** `v`，
     于是 `R v ⊆ A := X∪Y∪Z` 对全部 `v` 成立；若再有 `v ∈ R v`（DAG 因子
     `R v = {v} ∪ pa v` 必然如此），则 `v ∈ A` 对全部 `v` 成立，即 `A = univ`。
     ⟹ 用完整 `Split` 时定理**退化为无尾块**（与上一轮 `hTail` 的坍缩同源）。
     正确假设是**只在 `A` 内要求 `Split`**：

     ```lean
     hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z
     ```

     才是真正的「`A` 内部用因子图分离，`A` 外部允许任意尾块」。

  2. **第二步的第一个因子不能写成 `mass S (fun w => ∏ v ∈ A, ψ v w) x`（`w : V → α`）**，
     那样会多出一个因子 `|α| ^ |Aᶜ|`（`A` 外坐标被自由求和了两次中的一次）。
     正确形式是在 `↥A` 上取 `mass`（见 `mass_eq_PA_mul_Pout`）。
     数值反例：`V = {1,2}`、`A = S = {1}`、`α = Bool`，`ψ₁` 读 `{1}`、`ψ₂` 读 `{2}`，
     则 `mass {1} (∏ v ∈ A, ψ v) x = 2 · ψ₁(x)`，而真值只需 `ψ₁(x)`。

  3. 尾块求和的索引：`↥(outSet A)` 与 `↥(Aᶜ)` 作为子类型**恰好是同一集合**，
     本文件用 `outComplEquiv A : ↥(A : Set V)ᶜ ≃ ↥(outSet A)` 连接二者，
     于是任务书要求的 `extEnd (outSet A) x wt` 形式可以精确给出。

  ## 内容

  * §1 `pout_reads_out`：`hOut` ⟹ `A` 外乘积只读 `outSet A`（任务书第一步，已验证）。
  * §2 `mass_eq_PA_mul_Pout`：`mass S p x = massA(S,x) · T x`（任务书第二步，
    按上述第 2 点修正形式）。
  * §3 尾块因子 `T x` 与 `S` 无关（这是第三步的关键）。
  * §4 主定理 D（真正有尾块版，按上述第 1 点修正 `hsplit`）。

  零 sorry / admit / axiom。
================================================================================
-/

import FateWorld.Legacy.TailBlockBridge
-- R-36：与 `TailBlockV4`（V4 尾块常数版）**真接线**（两个 `mass` 分解的连接）。
import FateWorld.Legacy.TailBlockV4

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ===========================================================================
  §0  `outSet` 的基本事实
  =========================================================================== -/

theorem outSet_not_mem {A : Finset V} {u : V} (h : u ∈ outSet A) : u ∉ A :=
  (Finset.mem_filter.mp h).2

theorem not_mem_outSet {A : Finset V} {u : V} (h : u ∉ A) : u ∈ outSet A :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩

/-- `hOut` 的弱形式：`v ∉ A` 时 `R v ⊆ outSet A`（因 `v ∈ outSet A` 自身也算）。 -/
theorem readSet_subset_outSet {R : V → Finset V} {A : Finset V}
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A) :
    ∀ v, v ∉ A → R v ⊆ outSet A := by
  intro v hv u hu
  by_cases huv : u = v
  · subst huv; exact not_mem_outSet hv
  · exact hOut v hv (Finset.mem_sdiff.mpr ⟨hu, by simpa using huv⟩)

/-! ===========================================================================
  §1  第一步：`hOut` ⟹ `A` 外乘积只读 `outSet A`
  =========================================================================== -/

theorem pout_reads_out {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A) :
    ∀ w w', (∀ u ∈ outSet A, w u = w' u) →
      (∏ v ∈ outSet A, ψ v w) = (∏ v ∈ outSet A, ψ v w') := by
  intro w w' h
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hread v w w' fun u hu => h u ?_
  exact readSet_subset_outSet hOut v (outSet_not_mem hv) hu

/-- `P_A := ∏ v ∈ A, ψ v` 只读 `A`：只需 `A` 内因子的读集在 `A` 内。 -/
theorem pA_reads_A {ψ : V → (V → α) → ℝ} {R : V → Finset V} (hread : ReadSet ψ R)
    {A : Finset V} (hAll : ∀ v, v ∈ A → R v ⊆ A) :
    ∀ w w', (∀ u ∈ A, w u = w' u) → (∏ v ∈ A, ψ v w) = (∏ v ∈ A, ψ v w') := by
  intro w w' h
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hread v w w' fun u hu => h u (hAll v hv hu)

/-! ===========================================================================
  §2  `↥(Aᶜ) ≃ ↥(outSet A)`（二者是同一子集）
  =========================================================================== -/

noncomputable def outComplEquiv (A : Finset V) : ↥(A : Set V)ᶜ ≃ ↥(outSet A) :=
  Equiv.subtypeEquivRight (fun v => by
    simp only [Set.mem_compl_iff, Finset.mem_coe]
    unfold outSet
    simp)

theorem outComplEquiv_val (A : Finset V) (u : ↥(A : Set V)ᶜ) :
    ((outComplEquiv A u : ↥(outSet A)) : V) = (u : V) := rfl

theorem outComplEquiv_symm_val (A : Finset V) (u : ↥(outSet A)) :
    (((outComplEquiv A).symm u : ↥(A : Set V)ᶜ) : V) = (u : V) := rfl

/-! ===========================================================================
  §3  第二步：`mass` 的 A / A 外分解
  =========================================================================== -/

/-- 尾块点 `extEnd (outSet A) x wt` 在 `outSet A` 上就是 `wt`。 -/
theorem extEnd_outSet_of_mem (A : Finset V) (x : V → α) (wt : ↥(outSet A) → α)
    (u : V) (hu : u ∈ outSet A) : extEnd (outSet A) x wt u = wt ⟨u, hu⟩ :=
  extEnd_of_mem (outSet A) x wt u hu

/-- ⭐ **`arrowEquivA_symm_snd` 的本地版**（避免依赖文件名相同的外部引理）。 -/
theorem arrowEquivA_symm_snd' (A : Finset V) (q : (↥A → α) × (↥(A : Set V)ᶜ → α))
    (u : ↥(A : Set V)ᶜ) : ((arrowEquivA A).symm q) u.1 = q.2 u := by
  have h : ((arrowEquivA A) ((arrowEquivA A).symm q)).2 u = ((arrowEquivA A).symm q) u.1 := rfl
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- `arrowEquivA` 逆的两个分量与 `extEnd` 的一致性（`A` 内）。 -/
theorem arrowEquivA_symm_agree_A (A : Finset V) (x : V → α)
    (q : (↥A → α) × (↥(A : Set V)ᶜ → α)) :
    ∀ u ∈ A, (arrowEquivA A).symm q u = extEnd A x q.1 u := by
  intro u hu
  have h1 : (arrowEquivA A).symm q u = q.1 ⟨u, hu⟩ := by
    have h := arrowEquivA_fst A ((arrowEquivA A).symm q) ⟨u, hu⟩
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rw [h1, extEnd_of_mem A x q.1 u hu]

/-- `arrowEquivA` 逆在 `outSet A` 上的值由第二分量给出。 -/
theorem arrowEquivA_symm_agree_out (A : Finset V) (x : V → α)
    (q : (↥A → α) × (↥(A : Set V)ᶜ → α)) (wt : ↥(outSet A) → α)
    (hwt : ∀ s : ↥(outSet A), q.2 ((outComplEquiv A).symm s) = wt s) :
    ∀ u ∈ outSet A, (arrowEquivA A).symm q u = extEnd (outSet A) x wt u := by
  intro u hu
  have huA : u ∉ A := outSet_not_mem hu
  have h1 : (arrowEquivA A).symm q u = q.2 ⟨u, huA⟩ := by
    exact arrowEquivA_symm_snd' A q ⟨u, huA⟩
  rw [h1, extEnd_of_mem (outSet A) x wt u hu]
  exact hwt ⟨u, hu⟩

end Fate.GraphToProbView7

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-- 尾块权重：由 `↥(Aᶜ)` 上的取值导出 `↥(outSet A)` 上的取值。 -/
noncomputable def tailWt (A : Finset V) (q2 : ↥(A : Set V)ᶜ → α) : ↥(outSet A) → α :=
  fun s => q2 ((outComplEquiv A).symm s)

/-- ⭐⭐ **`A` 外乘积只由尾块权重决定**：`∏ v ∈ outSet A, ψ v` 在 `arrowEquivA` 的
逆点上等于 `∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt)`。 -/
theorem pout_arrowEquivA (A : Finset V) {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (x : V → α) (q : (↥A → α) × (↥(A : Set V)ᶜ → α)) :
    (∏ v ∈ outSet A, ψ v ((arrowEquivA A).symm q))
      = ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x (tailWt A q.2)) := by
  refine pout_reads_out hread hOut _ _ fun u hu => ?_
  have h1 : (arrowEquivA A).symm q u = q.2 ⟨u, outSet_not_mem hu⟩ :=
    arrowEquivA_symm_snd' A q ⟨u, outSet_not_mem hu⟩
  rw [h1, extEnd_of_mem (outSet A) x (tailWt A q.2) u hu]
  exact rfl

/-- ⭐ `P_A` 在 `arrowEquivA` 的逆点上只依赖第一分量。 -/
theorem pA_arrowEquivA (A : Finset V) {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) (hAll : ∀ v, v ∈ A → R v ⊆ A)
    (x : V → α) (q : (↥A → α) × (↥(A : Set V)ᶜ → α)) :
    (∏ v ∈ A, ψ v ((arrowEquivA A).symm q))
      = ∏ v : ↥A, ψ v.1 (extEnd A x q.1) := by
  rw [← Finset.prod_coe_sort A (fun v => ψ v ((arrowEquivA A).symm q))]
  refine Finset.prod_congr rfl fun v _ => ?_
  refine hread v.1 _ _ fun u hu => ?_
  exact arrowEquivA_symm_agree_A A x q u (hAll v.1 v.2 hu)

/-- ⭐⭐ **重指标：`mass` 在 `arrowEquivA` 下是 `(↥A → α) × (↥Aᶜ → α)` 上的求和**，
被加项 = 「`A` 内条件」× `P_A(q.1)` × `P_out(q.2)`。 -/
theorem mass_eq_sum_pair {A S : Finset V} (hSA : S ⊆ A)
    {ψ : V → (V → α) → ℝ} {R : V → Finset V} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w) (hread : ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (hAll : ∀ v, v ∈ A → R v ⊆ A) (x : V → α) :
    Fate.DAGFactorization.mass S p x
      = ∑ q : (↥A → α) × (↥(A : Set V)ᶜ → α),
          if (∀ u ∈ sub A S hSA, q.1 u = x u.1)
            then (∏ v : ↥A, ψ v.1 (extEnd A x q.1))
              * (∏ v ∈ outSet A, ψ v (extEnd (outSet A) x (tailWt A q.2)))
            else 0 := by
  classical
  have hp : p = fun w => (∏ v ∈ A, ψ v w) * (∏ v ∈ outSet A, ψ v w) := by
    funext w; rw [hfac w, prod_split_in_out ψ A w]
  -- 条件在 `↥A` 上的翻译
  have hcond : ∀ q : (↥A → α) × (↥(A : Set V)ᶜ → α),
      (∀ u ∈ S, (arrowEquivA A).symm q u = x u) ↔ (∀ u ∈ sub A S hSA, q.1 u = x u.1) := by
    intro q
    have hval : ∀ u (hu : u ∈ A), (arrowEquivA A).symm q u = q.1 ⟨u, hu⟩ := by
      intro u hu
      rw [arrowEquivA_symm_agree_A A x q u hu, extEnd_of_mem A x q.1 u hu]
    constructor
    · intro h u hu
      have huS : (u : V) ∈ S := (mem_sub_iff A S hSA u).mp hu
      have h1 : (arrowEquivA A).symm q (u : V) = x (u : V) := h (u : V) huS
      rw [hval (u : V) u.2] at h1
      exact h1
    · intro h u hu
      have huA : u ∈ A := hSA hu
      rw [hval u huA]
      exact h ⟨u, huA⟩ ((mem_sub_iff A S hSA ⟨u, huA⟩).mpr hu)
  unfold Fate.DAGFactorization.mass
  rw [hp, ← Equiv.sum_comp (arrowEquivA A)
    (fun q : (↥A → α) × (↥(A : Set V)ᶜ → α) =>
      if (∀ u ∈ sub A S hSA, q.1 u = x u.1)
        then (∏ v : ↥A, ψ v.1 (extEnd A x q.1))
          * (∏ v ∈ outSet A, ψ v (extEnd (outSet A) x (tailWt A q.2)))
        else 0)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcondw : (∀ u ∈ sub A S hSA, (arrowEquivA A w).1 u = x u.1)
      ↔ (∀ u ∈ S, w u = x u) := by
    refine Iff.trans ((hcond (arrowEquivA A w)).symm) ?_
    refine forall_congr' fun u => forall_congr' fun _ => ?_
    simp only [Equiv.symm_apply_apply]
  by_cases hc : ∀ u ∈ S, w u = x u
  · rw [if_pos hc, if_pos (hcondw.mpr hc)]
    have hw : w = (arrowEquivA A).symm (arrowEquivA A w) := (Equiv.symm_apply_apply _ w).symm
    simp only
    rw [hw, pA_arrowEquivA A hread hAll x, pout_arrowEquivA A hread hOut x]
    simp only [Equiv.apply_symm_apply]
  · rw [if_neg hc, if_neg (fun h => hc (hcondw.mp h))]

/-- ⭐⭐⭐ **第二步：`mass` 的 A / A 外分解**。

`mass S p x = (↥A 上的 mass) × (尾块因子 T x)`，其中
`T x = ∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt)` **与 `S` 无关**。 -/
theorem mass_eq_PA_mul_Pout {A S : Finset V} (hSA : S ⊆ A)
    {ψ : V → (V → α) → ℝ} {R : V → Finset V} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w) (hread : ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (hAll : ∀ v, v ∈ A → R v ⊆ A) (x : V → α) :
    Fate.DAGFactorization.mass S p x
      = Fate.DAGFactorization.mass (sub A S hSA)
          (fun w : ↥A → α => ∏ v : ↥A, ψ v.1 (extEnd A x w))
          (fun u : ↥A => x u.1)
        * (∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt)) := by
  classical
  rw [mass_eq_sum_pair hSA hfac hread hOut hAll x, Fintype.sum_prod_type]
  -- 内层对 `q2` 的求和：与 `q1` 无关
  have hinner : ∀ q1 : ↥A → α,
      (∑ q2 : ↥(A : Set V)ᶜ → α,
        if (∀ u ∈ sub A S hSA, q1 u = x u.1)
          then (∏ v : ↥A, ψ v.1 (extEnd A x q1))
            * (∏ v ∈ outSet A, ψ v (extEnd (outSet A) x (tailWt A q2)))
          else 0)
      = (if (∀ u ∈ sub A S hSA, q1 u = x u.1)
            then (∏ v : ↥A, ψ v.1 (extEnd A x q1)) else 0)
        * (∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt)) := by
    intro q1
    -- 把 `∑_{q2}` 换元成 `∑_{wt}`
    have hreindex : (∑ q2 : ↥(A : Set V)ᶜ → α,
          ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x (tailWt A q2)))
        = (∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt)) := by
      refine Fintype.sum_equiv (Equiv.arrowCongr (outComplEquiv A) (Equiv.refl α))
        (fun q2 => ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x (tailWt A q2)))
        (fun wt => ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt)) ?_
      intro q2
      rfl
    by_cases hc : ∀ u ∈ sub A S hSA, q1 u = x u.1
    · rw [if_pos hc]
      rw [Finset.sum_congr rfl (fun q2 _ => if_pos hc)]
      rw [← Finset.mul_sum, ← hreindex]
    · rw [if_neg hc, zero_mul]
      refine Finset.sum_eq_zero fun q2 _ => if_neg hc
  rw [Finset.sum_congr rfl (fun q1 _ => hinner q1), ← Finset.sum_mul]
  congr 1

end Fate.GraphToProbView7

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ===========================================================================
  §4  主定理 D（真正有尾块版）

  相对任务书，`hsplit : Split R X Y Z` 弱化为
  `hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z`
  （**必需**：完整 `Split` 会迫使 `A = univ`，见文件头 §1 的说明）。
  =========================================================================== -/

/-- `X ∪ Z ⊆ A := X ∪ Y ∪ Z`。 -/
theorem union_XZ_subset {X Y Z : Finset V} : X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases Finset.mem_union.mp hu with h | h
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
  · exact Finset.mem_union.mpr (Or.inr h)

/-- `Y ∪ Z ⊆ A := X ∪ Y ∪ Z`。 -/
theorem union_YZ_subset {X Y Z : Finset V} : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases Finset.mem_union.mp hu with h | h
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
  · exact Finset.mem_union.mpr (Or.inr h)

/-- `X ⊆ X ∪ Y ∪ Z`。 -/
theorem subset_XYZ_X {X Y Z : Finset V} : X ⊆ X ∪ Y ∪ Z := by
  intro u hu
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hu)))

/-- `Y ⊆ X ∪ Y ∪ Z`。 -/
theorem subset_XYZ_Y {X Y Z : Finset V} : Y ⊆ X ∪ Y ∪ Z := by
  intro u hu
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hu)))

/-- `Z ⊆ X ∪ Y ∪ Z`。 -/
theorem subset_XYZ_Z {X Y Z : Finset V} : Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  exact Finset.mem_union.mpr (Or.inr hu)

/-- ⭐ **弱化 `Split` + `hOut` ⟹ `A` 内因子的读集都在 `A` 内**。 -/
theorem hAll_of_hsplitA {R : V → Finset V} {X Y Z : Finset V}
    (hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z) :
    ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Y ∪ Z := by
  intro v hv
  rcases hsplitA v hv with h | h
  · exact Finset.Subset.trans h union_XZ_subset
  · exact Finset.Subset.trans h union_YZ_subset

/-- ⭐ **弱化 `Split` 在 `↥A` 上的 rebase**。 -/
theorem split_rebaseA {R : V → Finset V} {X Y Z A : Finset V}
    (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (hR : ∀ v : ↥A, R v.1 ⊆ A)
    (hsplitA : ∀ v : ↥A, R v.1 ⊆ X ∪ Z ∨ R v.1 ⊆ Y ∪ Z) :
    Fate.View19.Split (fun v : ↥A => sub A (R v.1) (hR v))
      (sub A X hX) (sub A Y hY) (sub A Z hZ) := by
  intro v
  rcases hsplitA v with h | h
  · left
    intro w hw
    simp only [mem_sub_iff] at hw ⊢
    rcases Finset.mem_union.mp (h hw) with h2 | h2
    · exact Finset.mem_union.mpr (Or.inl ((mem_sub_iff A X hX w).mpr h2))
    · exact Finset.mem_union.mpr (Or.inr ((mem_sub_iff A Z hZ w).mpr h2))
  · right
    intro w hw
    simp only [mem_sub_iff] at hw ⊢
    rcases Finset.mem_union.mp (h hw) with h2 | h2
    · exact Finset.mem_union.mpr (Or.inl ((mem_sub_iff A Y hY w).mpr h2))
    · exact Finset.mem_union.mpr (Or.inr ((mem_sub_iff A Z hZ w).mpr h2))

end Fate.GraphToProbView7

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

variable [Nonempty α]

/-- ⭐⭐ **`↥A` 上的 `CondIndep`（弱化版：只在 `A` 内要求 `Split`）**。 -/
theorem condIndep_on_A_weak {ψ : V → (V → α) → ℝ} {R : V → Finset V} {X Y Z A : Finset V}
    (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A) (hcover : X ∪ Y ∪ Z = A)
    (hread : Fate.View19.ReadSet ψ R)
    (hAll : ∀ v, v ∈ A → R v ⊆ A)
    (hsplitA : ∀ v : ↥A, R v.1 ⊆ X ∪ Z ∨ R v.1 ⊆ Y ∪ Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (ω₀ : V → α) :
    Fate.FactorMarkov.CondIndep
      (fun w : ↥A → α => ∏ v : ↥A, ψ v.1 (extEnd A ω₀ w))
      (sub A X hX) (sub A Y hY) (sub A Z hZ) := by
  classical
  set ψA : ↥A → ((↥A → α) → ℝ) := fun v w => ψ v.1 (extEnd A ω₀ w) with hψA
  set pA : (↥A → α) → ℝ := fun w => ∏ v : ↥A, ψA v w with hpA
  set RA : ↥A → Finset ↥A := fun v => sub A (R v.1) (hAll v.1 v.2) with hRA
  have hfacA : ∀ w : ↥A → α, pA w = ∏ v, ψA v w := fun w => rfl
  have hreadA : Fate.View19.ReadSet ψA RA := by
    intro v x y hxy
    exact readSet_rebase hread A ω₀ (fun v : ↥A => hAll v.1 v.2) v x y hxy
  have hsplitA' : Fate.View19.Split RA (sub A X hX) (sub A Y hY) (sub A Z hZ) :=
    split_rebaseA hX hY hZ (fun v : ↥A => hAll v.1 v.2) hsplitA
  have hdisj_XY : Disjoint (sub A X hX) (sub A Y hY) := disjoint_attach hX hY hXY
  have hdisj_XZ : Disjoint (sub A X hX) (sub A Z hZ) := disjoint_attach hX hZ hXZ
  have hdisj_YZ : Disjoint (sub A Y hY) (sub A Z hZ) := disjoint_attach hY hZ hYZ
  exact condIndep_general ψA pA hfacA hreadA hsplitA' hdisj_XY hdisj_XZ hdisj_YZ
    (attach_union_univ A X Y Z hX hY hZ hcover)

/-- ⭐⭐⭐⭐⭐ **主定理 D（真正有尾块版）**。

假设：

* `hfac`、`hread`：`p = ∏ v, ψ v`，`ψ v` 只读 `R v`；
* `hOut : ∀ v ∉ A, R v \ {v} ⊆ outSet A`：`A` 外因子（除自身）只读 `A` 外坐标
  —— 这才是「真正的尾块」（`A` 外坐标自由、不被 `A` 内变量影响）；
* `hsplitA : ∀ v ∈ A, R v ⊆ X∪Z ∨ R v ⊆ Y∪Z`：**`A` 内部**的因子图分离
  （注意：这不是完整 `Split`；完整 `Split` 会迫使 `A = univ`，即退化为无尾块）。

结论：`CondIndep p X Y Z`。 -/
theorem condIndep_tail_block_real {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ X ∪ Y ∪ Z → R v \ {v} ⊆ outSet (X ∪ Y ∪ Z))
    (hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    Fate.FactorMarkov.CondIndep p X Y Z := by
  classical
  intro x
  set A := X ∪ Y ∪ Z with hA
  have hXA : X ⊆ A := subset_XYZ_X
  have hYA : Y ⊆ A := subset_XYZ_Y
  have hZA : Z ⊆ A := subset_XYZ_Z
  have hXA' : X ∪ Z ⊆ A := union_XZ_subset
  have hYA' : Y ∪ Z ⊆ A := union_YZ_subset
  have hZZ : Z ⊆ Z := Finset.Subset.refl Z
  have hZXZ : Z ⊆ X ∪ Z := fun u hu => Finset.mem_union.mpr (Or.inr hu)
  have hZYZ : Z ⊆ Y ∪ Z := fun u hu => Finset.mem_union.mpr (Or.inr hu)
  have hAA : A ⊆ A := Finset.Subset.refl A
  have hcover : X ∪ Y ∪ Z = A := hA.symm
  -- `A` 内的读集封闭
  have hAll : ∀ v, v ∈ A → R v ⊆ A := hAll_of_hsplitA hsplitA
  -- 四个 `mass` 的分解（共用尾块因子 `T x`）
  have e1 := mass_eq_PA_mul_Pout hAA hfac hread hOut hAll x
  have e2 := mass_eq_PA_mul_Pout hZA hfac hread hOut hAll x
  have e3 := mass_eq_PA_mul_Pout hXA' hfac hread hOut hAll x
  have e4 := mass_eq_PA_mul_Pout hYA' hfac hread hOut hAll x
  -- `↥A` 上的 `CondIndep`
  have hCondA := condIndep_on_A_weak hXA hYA hZA hcover hread hAll
    (fun v : ↥A => hsplitA v.1 v.2) hXY hXZ hYZ x
  have hkey := hCondA (fun u : ↥A => x u.1)
  rw [sub_union_eq_sub_A hXA hYA hZA hcover] at hkey
  rw [show (sub A A (Finset.Subset.refl A) : Finset ↥A) = Finset.univ from
    Finset.ext fun v => by simp [mem_sub_iff]] at hkey
  have hXZ : (sub A X hXA ∪ sub A Z hZA : Finset ↥A) = sub A (X ∪ Z) hXA' := by
    ext v; simp only [mem_sub_iff, Finset.mem_union]
  have hYZ : (sub A Y hYA ∪ sub A Z hZA : Finset ↥A) = sub A (Y ∪ Z) hYA' := by
    ext v; simp only [mem_sub_iff, Finset.mem_union]
  rw [hXZ, hYZ] at hkey
  have hsubAA : (sub A A hAA : Finset ↥A) = Finset.univ :=
    Finset.ext fun v => by simp [mem_sub_iff]
  rw [e2, e3, e4, e1, hsubAA]
  linear_combination
    ((∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt)) ^ 2) * hkey

end Fate.GraphToProbView7

/-! ===========================================================================
  §R36  **R-36 接线：本文件（`TailBlockReal2`）与 `TailBlockV4` 的连接**

  两个模块各自给出 `DAGFactorization.mass` 的一个**尾块**分解，但用的是
  **两套互不相同的语言**：

  * `TailBlockV4`：`mass S p x = |α|^(|V|-|A|) · massA A S p x`
    （`mass_tail_const`，前件是 `TailBlockV4.ReadsOn p A` —— **只读 `A`**）；
  * 本文件：`mass S p x = massA(S,x) · Σ_wt ∏_{v∈outSet A} ψ v (extEnd ..)`
    （`mass_eq_PA_mul_Pout`，前件是 `ReadSet ψ R` + `hOut` + `A` 内读集封闭）。

  本节补的是**两套语言之间的翻译层**（此前无人建立）：

  | 名字 | 内容 |
  |---|---|
  | `readsOn_iff_forall_agree`   | ⭐ 两模块「只读 `A`」谓词的**定义一致性** |
  | `pA_readsOn_A`               | ⭐ 本文件 `pA_reads_A` ⟹ V4 `ReadsOn`（跨模块）|
  | `massA_frozen_mul_via_pA`    | ⭐⭐ 用本文件读集条件**喂给** V4 `massA_frozen_mul` |
  | `mass_tail_const_of_readSet` | ⭐⭐ 本文件 `ReadSet` 前件 ⟹ V4 尾块常数形式 |
  | `massA_self_of_readSet`      | ⭐ 端点闭式（`S = A`）：`mass = |α|^(|V|-|A|) · ∏ ψ x` |

  ⚠ **诚实说明**：这些都是**翻译 / 组装**定理，不是新的数学。
  它们的价值在于：`TailBlockV4` 此前无外部引用，本文件现在以它为下游，
  两模块的 `mass` 语言从此可以互译。
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19 TailBlockV4

universe u

section R36Wiring

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-- ⭐ **两模块「只读 `A`」谓词的**定义一致性**。

`TailBlockV4.ReadsOn f A` 的定义是 `∀ w w', (∀ u ∈ A, w u = w' u) → f w = f w'`，
本文件 `pA_reads_A` 的结论正是**同一句式**。这里显式登记为 `Iff`，
以便下游在两套语言之间自由切换。 -/
theorem readsOn_iff_forall_agree {f : (V → α) → ℝ} {A : Finset V} :
    TailBlockV4.ReadsOn f A ↔
      ∀ w w' : V → α, (∀ u ∈ A, w u = w' u) → f w = f w' :=
  Iff.rfl

/-- ⭐⭐ **本文件的 `pA_reads_A` ⟹ V4 的 `ReadsOn`**（跨模块翻译）。

前件：`ReadSet ψ R`（本文件语言）+ `A` 内读集封闭。
结论：乘积 `∏ v ∈ A, ψ v` 是 `TailBlockV4.ReadsOn · A`（V4 语言）。

⚠ 非平凡处：前件是**逐因子**的读集条件 `R v ⊆ A`，结论是**整个乘积**的
V4 谓词；中间靠 `pA_reads_A` 的 `∀w w'` 形式对接。 -/
theorem pA_readsOn_A {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) {A : Finset V} (hAll : ∀ v, v ∈ A → R v ⊆ A) :
    TailBlockV4.ReadsOn (fun w => ∏ v ∈ A, ψ v w) A :=
  fun w w' h => pA_reads_A hread hAll w w' h

end R36Wiring

end Fate.GraphToProbView7

/-! ===========================================================================
  §R36.2  尾块常数（需要 `Nonempty α`，故另一节）
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19 TailBlockV4

universe u

section R36Tail

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]
  [Nonempty α]

/-- ⭐⭐ **用本文件的读集条件喂给 V4 的 `massA_frozen_mul`**：

`massA A S ((∏ v∈A, ψ v) * g) x = (∏ v∈A, ψ v x) * massA A S g x`

⚠ 非平凡处：`TailBlockV4.massA_frozen_mul` 要求 `ReadsOn` 前件，而本文件的
`ReadSet ψ R` 语言**不直接**给出它 —— 中间必须经 `pA_readsOn_A`。
两侧函数（`TailBlockV4.massA`、`TailBlockV4.extA`）来自 V4 模块，
前件来自本模块，故这是**真跨模块**组装。 -/
theorem massA_frozen_mul_via_pA {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) {A S : Finset V} (hAS : A ⊆ S) (hAll : ∀ v, v ∈ A → R v ⊆ A)
    (g : (V → α) → ℝ) (x : V → α) :
    TailBlockV4.massA A S (fun w => (∏ v ∈ A, ψ v w) * g w) x
      = (∏ v ∈ A, ψ v x) * TailBlockV4.massA A S g x := by
  have hreadsA : TailBlockV4.ReadsOn (fun w => ∏ v ∈ A, ψ v w) A :=
    pA_readsOn_A hread hAll
  have hreadsS : TailBlockV4.ReadsOn (fun w => ∏ v ∈ A, ψ v w) S :=
    fun w w' h => hreadsA w w' (fun u hu => h u (hAS hu))
  exact TailBlockV4.massA_frozen_mul (f := fun w => ∏ v ∈ A, ψ v w) (g := g)
    (A := A) (S := S) hreadsS x

/-- ⭐⭐ **把本文件的 `ReadSet` 语言翻成 V4 的尾块常数形式**。

若 `∀ v, R v ⊆ A`（每个因子都只读 `A`），则整个乘积 `∏ v, ψ v` 满足
V4 的 `mass_tail_const` 右端形式：

`mass S (∏ ψ) x = |α|^(|V|-|A|) · Σ r, ∏ v, ψ v (extA x A S r)`

⚠ 非平凡处：V4 的 `mass_tail_const` 要求 `ReadsOn (∏ v, ψ v) A`，
而本文件只给 `ReadSet ψ R` + `R v ⊆ A`。这一步由 V4 的 `readsOn_prod`
（`W = univ`、`S = A`）完成，**此前无人把两个模块的前件这样接起来**。 -/
theorem mass_tail_const_of_readSet {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) {A S : Finset V} (hSA : S ⊆ A)
    (hAll : ∀ v, R v ⊆ A) (x : V → α) :
    Fate.DAGFactorization.mass S (fun w => ∏ v, ψ v w) x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) *
        ∑ r : ({u : V // u ∈ A ∧ u ∉ S} → α),
          (∏ v, ψ v (TailBlockV4.extA x A S r)) := by
  classical
  have hreads : TailBlockV4.ReadsOn (fun w => ∏ v, ψ v w) A :=
    TailBlockV4.readsOn_prod ψ hread (W := (Finset.univ : Finset V)) (S := A)
      (fun v _ => hAll v)
  exact TailBlockV4.mass_tail_const (p := fun w => ∏ v, ψ v w) hSA hreads x

/-- ⭐ **端点闭式（`S = A`）**：`mass A (∏ ψ) x = |α|^(|V|-|A|) · ∏ v, ψ v x`。

⚠ 非平凡处：把 `mass_tail_const_of_readSet`（`S = A`）与 V4 的 `massA_self`
（`massA A A p x = p x`）**串联**得到闭式；两模块此前都没有这个具体形态。 -/
theorem massA_self_of_readSet {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) {A : Finset V} (hAll : ∀ v, R v ⊆ A) (x : V → α) :
    Fate.DAGFactorization.mass A (fun w => ∏ v, ψ v w) x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) * (∏ v, ψ v x) := by
  classical
  have h := mass_tail_const_of_readSet (S := A) hread (Finset.Subset.refl A) hAll x
  have h3 : (∑ r : ({u : V // u ∈ A ∧ u ∉ A} → α),
      ∏ v, ψ v (TailBlockV4.extA x A A r))
      = TailBlockV4.massA A A (fun w => ∏ v, ψ v w) x := rfl
  have h4 : TailBlockV4.massA A A (fun w => ∏ v, ψ v w) x = ∏ v, ψ v x :=
    TailBlockV4.massA_self x
  rw [h, h3, h4]

end R36Tail

end Fate.GraphToProbView7
