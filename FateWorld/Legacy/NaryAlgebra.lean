import FateWorld.Legacy.CondIndepN

/-! ===========================================================================
  §GenNAlebra ⭐⭐⭐⭐⭐ **N 元的代数因子化**（**N 元桥的代数核心**，第 185 轮）

  ## 核心定理

  $$\Big(\sum_{xs \in S} p(xs, z)\Big) \cdot M^{|\iota|-1}
    = \prod_{i}\, \sum_{a \in S_i} \mathrm{marg}\,p\,i\,a\,z$$

  其中 $M = \mathrm{NMass}\ p\ z$。

  ## ⭐ 推导（本轮）

  `CondIndepN` 说 `p xs z * M^(n-1) = ∏ i, marg p i (xs i) z`。
  对 `xs` 求和（限制在 `S` 内）：
  - 左边：把 `M^(n-1)` 提出（`Finset.sum_mul`）⟹ `(∑ xs∈S, p xs z) * M^(n-1)`
  - 右边：`∑ xs∈S, ∏ i, marg i (xs i)` = `∏ i, (∑ a∈S_i, marg i a)`
    —— **这就是 `Fintype.prod_sum`**（乘积与求和的交换）

  ## ⭐⭐ 与二元版的一致性

  二元版（`BridgeKernel.condIndepFin_sum_factorize`）：
  `(∑ x∈S1, ∑ y∈S2, p) * M^1 = (∑ x∈S1, margXZ x) * (∑ y∈S2, margYZ y)`
  **⟹ 正是 `|ι| = 2` 的特例。**
  =========================================================================== -/

namespace Fate.GenC3

open MeasureTheory ProbabilityTheory

section Factorize

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable {γ : Type*}

/-- ⭐⭐⭐⭐⭐ **N 元的代数因子化**（**N 元桥的代数核心**）。

**⭐ 证明**：
1. 逐点用 `CondIndepN`：`p xs z * M^(n-1) = ∏ i, marg p i (xs i) z`
2. `Finset.sum_mul` 把 `M^(n-1)` 提进求和
3. **`Fintype.prod_sum`** 把「乘积的求和」换成「求和的乘积」 -/
theorem condIndepN_sum_factorize
    (p : NJoint (ι := ι) α γ)
    (h : CondIndepN p)
    (S : ∀ i, Set (α i)) [∀ i, DecidablePred (· ∈ S i)]
    (z : γ) :
    (∑ xs : (∀ i, α i), (if ∀ i, xs i ∈ S i then p xs z else 0))
        * (NMass p z) ^ (Fintype.card ι - 1)
      = ∏ i, ∑ a : α i, (if a ∈ S i then marg p i a z else 0) := by
  have key : ∀ xs : (∀ i, α i), p xs z * (NMass p z) ^ (Fintype.card ι - 1)
      = ∏ i, marg p i (xs i) z := fun xs => (condIndepN_iff p).mp h xs z
  rw [Finset.sum_mul]
  have hL : ∀ xs : (∀ i, α i),
      (if ∀ i, xs i ∈ S i then p xs z else 0) * (NMass p z) ^ (Fintype.card ι - 1)
      = if ∀ i, xs i ∈ S i then ∏ i, marg p i (xs i) z else 0 := by
    intro xs
    by_cases hxs : ∀ i, xs i ∈ S i
    · rw [if_pos hxs, if_pos hxs]; exact key xs
    · rw [if_neg hxs, if_neg hxs, zero_mul]
  rw [Finset.sum_congr rfl (fun xs _ => hL xs)]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  by_cases hxs : ∀ i, xs i ∈ S i
  · rw [if_pos hxs]
    exact (Finset.prod_congr rfl (fun i _ => by rw [if_pos (hxs i)])).symm
  · rw [if_neg hxs]
    push Not at hxs
    obtain ⟨j, hj⟩ := hxs
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])).symm

end Factorize

end Fate.GenC3
