import FateWorld.Legacy.TailOutExtract

/-! ===========================================================================
  §0  真正有尾块情形的两个关键构件

  ## 背景

  上一轮发现：主定理 D 的 `hTail : ∀ v ∉ A, R v ⊆ Z` 蕴含 `A = univ`
  （因为 `readSetOf G v = {v} ∪ pa(v)` 含 `v`，而 `v ∉ A ⊇ Z` 与 `v ∈ Z` 矛盾）。
  所以那个路线坍缩成「无尾块」。

  ## 本文件的两个构件

  1. `pout_reads_out`：若 `∀ v ∉ A, R v \ {v} ⊆ outSet A`，则 `A` 外的乘积
     `∏ v ∈ outSet A, ψ v` 只依赖 `outSet A` 上的坐标。

  2. `arrowEquivOut`：`(V → α) ≃ (↥A → α) × (↥(outSet A) → α)`。
     （用 `A ∪ outSet A = univ` 与 `A ∩ outSet A = ∅` 分解）

  ## 为什么这两个够了

  `mass S p x = ∑_{w | w|_S = x|_S} P_A(w) · P_out(w)`。由于 `P_out` 只读
  `outSet A`、不读 `A`，而 `mass S` 的纤维允许 `A` 外坐标自由，故可分解为
  `(A 内的 mass 部分) · (A 外坐标的和)`。后一个因子与 `S` 无关，
  于是对 `CondIndep` 的四个 `mass` 都相同，等式两边各两次，可约去。

  ## 诚实边界

  本文件只给这两个构件。完整的 `CondIndep` 组装未做。
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §1 `P_out` 只读 `outSet A` -/

/-- ⭐⭐ **`A` 外的乘积只读 `outSet A`**。

条件：`∀ v ∉ A, R v \ {v} ⊆ outSet A`（`A` 外因子的父节点也在 `A` 外）。 -/
theorem pout_reads_out {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : Fate.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A) :
    ∀ w w', (∀ u ∈ outSet A, w u = w' u) →
      (∏ v ∈ outSet A, ψ v w) = (∏ v ∈ outSet A, ψ v w') := by
  intro w w' h
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hread v w w' fun u hu => ?_
  have hvA : v ∉ A := by
    have : v ∈ Finset.univ.filter (fun v => v ∉ A) := hv
    exact (Finset.mem_filter.mp this).2
  have huOut : u ∈ outSet A := by
    by_cases huv : u = v
    · subst huv; exact hv
    · exact hOut v hvA (Finset.mem_sdiff.mpr ⟨hu, by simpa using huv⟩)
  exact h u huOut

/-! ### §2 `(V → α) ≃ (↥A → α) × (↥(outSet A) → α)` -/

/-- ⭐ `↥Aᶜ` 与 `↥(outSet A)` 同构（元素级等价）。 -/
noncomputable def complEquivOut (A : Finset V) : ↥(A : Set V)ᶜ ≃ ↥(outSet A) :=
  Equiv.subtypeEquivRight (fun v => by
    simp only [Set.mem_compl_iff, Finset.mem_coe]
    unfold outSet
    simp)

/-- ⭐⭐ **`(V → α) ≃ (↥A → α) × (↥(outSet A) → α)`**。

用 `A ∪ outSet A = univ` 与 `A ∩ outSet A = ∅` 把 `V` 分成两块。 -/
noncomputable def arrowEquivOut (A : Finset V) :
    (V → α) ≃ (↥A → α) × (↥(outSet A) → α) :=
  Equiv.trans
    (Equiv.arrowCongr (Equiv.Set.sumCompl (A : Set V)).symm (Equiv.refl α))
    (Equiv.trans
      (Equiv.arrowCongr (Equiv.sumCongr (Equiv.refl ↥A) (complEquivOut A)) (Equiv.refl α))
      (Equiv.sumArrowEquivProdArrow ↥A ↥(outSet A) α))


/-! ### §3 `merge`：把 `A` 内与 `A` 外的取值合并成 `V → α` -/

noncomputable def merge (A : Finset V) (wA : ↥A → α) (wt : ↥(outSet A) → α) : V → α :=
  fun v => if h : v ∈ A then wA ⟨v, h⟩ else wt ⟨v, by
    simp only [outSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h⟩

theorem merge_mem_A (A : Finset V) (wA : ↥A → α) (wt : ↥(outSet A) → α) (v : ↥A) :
    merge A wA wt v.1 = wA v := by
  unfold merge; rw [dif_pos v.2]

theorem merge_mem_out (A : Finset V) (wA : ↥A → α) (wt : ↥(outSet A) → α) (v : ↥(outSet A)) :
    merge A wA wt v.1 = wt v := by
  unfold merge
  have hvA : v.1 ∉ A := by
    have : v.1 ∈ Finset.univ.filter (fun v => v ∉ A) := v.2
    exact (Finset.mem_filter.mp this).2
  rw [dif_neg hvA]

-- 关键：p (merge A wA wt) = P_A(wA) * P_out(wt)
theorem p_merge {A : Finset V} {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w) (wA : ↥A → α) (wt : ↥(outSet A) → α) :
    p (merge A wA wt)
      = (∏ v ∈ A, ψ v (merge A wA wt)) * (∏ v ∈ outSet A, ψ v (merge A wA wt)) := by
  rw [hfac]
  exact prod_split_in_out ψ A (merge A wA wt)

/-- ⭐ `arrowEquivOut` 的第一分量是「限制到 A」。 -/
theorem arrowEquivOut_fst (A : Finset V) (w : V → α) (u : ↥A) :
    (arrowEquivOut A w).1 u = w u.1 := by
  simp only [arrowEquivOut, complEquivOut, Equiv.trans_apply, Equiv.arrowCongr,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_refl]
  rfl


/-! ### §4 若所有因子只读 `A`，则 `p` 只读 `A` -/

/-- ⭐⭐ **`p` 只读 `A`**（当所有因子只读 `A` 时）。 -/
theorem p_reads_A {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : Fate.View19.ReadSet ψ R) (hA : ∀ v, R v ⊆ A) :
    ∀ w w', (∀ u ∈ A, w u = w' u) → (∏ v, ψ v w) = (∏ v, ψ v w') := by
  intro w w' h
  refine Finset.prod_congr rfl fun v _ => ?_
  exact hread v w w' (fun u hu => h u (hA v hu))

/-- ⭐⭐ **`p(merge A wA wt)` 与 `wt` 无关**（当所有因子只读 `A` 时）。 -/
theorem p_merge_indep_of_reads_A {A : Finset V} {ψ : V → (V → α) → ℝ}
    {R : V → Finset V} (hread : Fate.View19.ReadSet ψ R)
    (hA : ∀ v, R v ⊆ A) (wA : ↥A → α) (wt wt' : ↥(outSet A) → α) :
    (∏ v, ψ v (merge A wA wt)) = (∏ v, ψ v (merge A wA wt')) := by
  refine Finset.prod_congr rfl fun v _ => ?_
  refine hread v _ _ fun u hu => ?_
  have huA : u ∈ A := hA v hu
  have h1 : merge A wA wt u = wA ⟨u, huA⟩ := merge_mem_A A wA wt ⟨u, huA⟩
  have h2 : merge A wA wt' u = wA ⟨u, huA⟩ := merge_mem_A A wA wt' ⟨u, huA⟩
  rw [h1, h2]

end Fate.GraphToProbView7
