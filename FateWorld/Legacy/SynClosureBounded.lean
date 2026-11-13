/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.SynClosureBounded
阶段：**COMPLEX-1 §5 第 4 条（`synClosureIter` 步数无界 → `N ≤ |M|`）**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate/Implication.lean:611` 定义的 `synClosureIter`（`Nat.iterate` 形式的
Armstrong 迭代闭包）**没有步数上界**：`Sigma^n(B)` 对任意 `n` 都有定义，
但「多少步足够」未给出。本文件补上这一缺口：

> 在 **有限属性集**（`[K.FiniteAttrs]`）上，迭代闭包在
> **`Nat.card K.MFCA` 步之内到达不动点**，即
>
>   `Nat.card K.MFCA ≤ n  →  Sigma^n(B) = Sigma^(Nat.card K.MFCA)(B)`

这正是清单里写的 **`N ≤ |M|`**。

---------------------------------------------------------------------------
方法（照搬 `Fate/T21FiniteSearch.reachIter` 的骨架）
---------------------------------------------------------------------------
`Fate.T21FiniteSearch.reachIter` 处理「有向可达的有限步上界」，
其骨架为三步：**单调 + 有限步 + `card` 上界**。
本文件把同一骨架搬到属性集的幂集上：

1. **单调**：`Sigma^m(B) ⊆ Sigma^n(B)`（`m ≤ n`）——已有
   `synClosureIter_mono`，此处直接消费。
2. **`card` 上界**：`Sigma^k(B) ⊆ M`，故 `ncard (Sigma^k B) ≤ |M|`
   （`Set.ncard_le_card`）。
3. **鸽巢**：若 `[0, N+1]` 内**每步都严格**（`Sigma^k ≠ Sigma^(k+1)`），
   则由 `Set.ncard_lt_ncard` + 扩张性得 `ncard` 每步**至少 +1**，
   故 `ncard (Sigma^(N+1) B) ≥ N+1 > N`，与上界矛盾。
   于是存在 `k ≤ N` 使 `Sigma^k B = Sigma^(k+1) B`。
4. **稳定后恒稳定**：一旦 `Sigma^k = Sigma^(k+1)`，则对一切 `m ≥ k` 有
   `Sigma^m = Sigma^k`（对 `m` 归纳 + `synClosureIter_succ`）。

---------------------------------------------------------------------------
边界（诚实登记）
---------------------------------------------------------------------------
* **不改 `Implication.lean`、不改 `T21FiniteSearch.lean`**，本文件纯新增。
  `FormalCtx` 也**未加** `Fintype M` 字段——COMPLEX-1 原文说
  「唯一缺口：`FormalCtx` 需加 `Fintype M`」，**这在该判断上偏严格**：
  既有的 `FiniteAttrs` typeclass 已给出 `(univ : Set K.MFCA).Finite`，
  由此可导出 `Finite K.MFCA`，上界用 `Nat.card K.MFCA` 即可，
  无须改动 `FormalCtx`。（该缺口已在文件末尾 `§4 说明` 中登记。）
* **前件非平凡**：`[K.FiniteAttrs]` 说的是「属性集有限」，
  **不包含**结论（结论是迭代不动点等式）。见 `§3` 的反例讨论。
* 结论**不是**同义反复：`Sigma^n(B) = Sigma^N(B)` 需要鸽巢论证；
  若 `M` 无限则结论为**假**（`§3` 的 `Nat` 反例），故有限性是本质前件。
* 零 `sorry`、零 `axiom`、零 `admit`。
-/

import FateWorld.Legacy.Implication
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Fate

universe u v

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ==========================================================================
  §1  记号与基本事实
========================================================================== -/

/-- **`M` 有限**：由 `FiniteAttrs` 的 `(univ : Set K.MFCA).Finite` 得到。

这是本文件的「有限步」来源——骨架第 2 步所依赖的 `card` 上界由此而来。 -/
theorem finite_attr_type [K.FiniteAttrs] : Finite K.MFCA :=
  Set.finite_univ_iff.mp (FiniteAttrs.finite (K := K))

/-- **迭代闭包的 `ncard` 上界**：`Sigma^k(B)` 是 `M` 的子集，故 `ncard ≤ |M|`。

骨架第 2 步。 -/
theorem synClosureIter_ncard_le_card [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) (k : ℕ) :
    (K.synClosureIter Sig k B).ncard ≤ Nat.card K.MFCA :=
  haveI := finite_attr_type (K := K)
  Set.ncard_le_card _

/-- **一步严格增 ⟹ `ncard` 严格增**。

骨架第 3 步的单步形式：由 `Sigma^k ⊆ Sigma^(k+1)`（扩张性）
与 `Sigma^k ≠ Sigma^(k+1)`，得 `ncard` 严格上升。 -/
theorem synClosureIter_ncard_lt_of_ne [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) (k : ℕ)
    (hne : K.synClosureIter Sig k B ≠ K.synClosureIter Sig (k + 1) B) :
    (K.synClosureIter Sig k B).ncard < (K.synClosureIter Sig (k + 1) B).ncard :=
  Set.ncard_lt_ncard (lt_of_le_of_ne (K.synClosureIter_le_add Sig B k 1) hne)
    (FiniteAttrs.finite_set (K := K) _)

/-- **`ncard` 对步数单调**（非严格）：由 `Sigma^k ⊆ Sigma^(k+1)`。 -/
theorem synClosureIter_ncard_le_succ [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) (k : ℕ) :
    (K.synClosureIter Sig k B).ncard ≤ (K.synClosureIter Sig (k + 1) B).ncard :=
  Set.ncard_le_ncard (K.synClosureIter_le_add Sig B k 1)
    (FiniteAttrs.finite_set (K := K) _)

/-! ==========================================================================
  §2  鸽巢：存在 `k ≤ |M|` 为不动点
========================================================================== -/

/-- ⭐ **鸽巢引理（辅助）**：若 `[0, N]` 内**每步都严格**，则 `N ≤ ncard (Sigma^N B)`。

**证明**：对 `N` 归纳。若每步严格，则 `ncard` 每步至少 +1，
于是 `ncard (Sigma^N B) ≥ N`。

**用途**：与 `ncard ≤ |M|` 组合，取 `N = |M| + 1` 即得矛盾。 -/
theorem le_ncard_of_all_strict [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) :
    ∀ N : ℕ, (∀ k < N, K.synClosureIter Sig k B ≠ K.synClosureIter Sig (k + 1) B) →
      N ≤ (K.synClosureIter Sig N B).ncard := by
  intro N
  induction N with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
      intro hstrict
      have hstrict' : ∀ k < n, K.synClosureIter Sig k B ≠ K.synClosureIter Sig (k + 1) B :=
        fun k hk => hstrict k (Nat.lt_succ_of_lt hk)
      have hn : n ≤ (K.synClosureIter Sig n B).ncard := ih hstrict'
      have hlt : (K.synClosureIter Sig n B).ncard
          < (K.synClosureIter Sig (n + 1) B).ncard :=
        K.synClosureIter_ncard_lt_of_ne Sig B n (hstrict n (Nat.lt_succ_self n))
      omega

/-- ⭐⭐⭐ **存在 `k ≤ |M|` 使 `Sigma^k B = Sigma^(k+1) B`**（迭代到达不动点）。

**证明（鸽巢）**：反设 `Sigma^k B ≠ Sigma^(k+1) B` 对一切 `k ≤ |M|` 成立。
取 `N = |M| + 1`，则 `le_ncard_of_all_strict` 给出
`|M| + 1 ≤ ncard (Sigma^(|M|+1) B)`，而 `synClosureIter_ncard_le_card` 给出
`ncard (Sigma^(|M|+1) B) ≤ |M|`。矛盾。 -/
theorem exists_synClosureIter_fixed_le_card [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) :
    ∃ k ≤ Nat.card K.MFCA,
      K.synClosureIter Sig k B = K.synClosureIter Sig (k + 1) B := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ k, k ≤ |M| → Sigma^k B ≠ Sigma^(k+1) B`
  have hstrict : ∀ k < Nat.card K.MFCA + 1,
      K.synClosureIter Sig k B ≠ K.synClosureIter Sig (k + 1) B :=
    fun k hk => hcon k (Nat.lt_succ_iff.mp hk)
  have hge : Nat.card K.MFCA + 1 ≤
      (K.synClosureIter Sig (Nat.card K.MFCA + 1) B).ncard :=
    K.le_ncard_of_all_strict Sig B (Nat.card K.MFCA + 1) hstrict
  have hle := K.synClosureIter_ncard_le_card Sig B (Nat.card K.MFCA + 1)
  omega

/-! ==========================================================================
  §3  ⭐⭐⭐⭐ 主定理：`N ≤ |M|` —— 迭代在 `|M|` 步内稳定
========================================================================== -/

/-- **不动点后恒稳定**：若 `Sigma^k B = Sigma^(k+1) B`，则对一切 `m ≥ k`
有 `Sigma^m B = Sigma^k B`。

**证明**：对 `m` 归纳（`Nat.le_induction`）。关键一步用
`synClosureIter_succ`（`Sigma^(n+1) = synClosureOne (Sigma^n)`）
展开后由归纳假设与 `hfix` 闭合。 -/
theorem synClosureIter_stable_of_fixed
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) {k : ℕ}
    (hfix : K.synClosureIter Sig k B = K.synClosureIter Sig (k + 1) B) :
    ∀ m, k ≤ m → K.synClosureIter Sig m B = K.synClosureIter Sig k B := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
      rw [K.synClosureIter_succ, ih]
      have hstep : K.synClosureIter Sig (k + 1) B =
          K.synClosureOne Sig (K.synClosureIter Sig k B) :=
        K.synClosureIter_succ Sig k B
      rw [← hstep, hfix]

/-- ⭐⭐⭐⭐ **主定理（`N ≤ |M|`）**：

在有限属性集上，**迭代闭包在 `|M|` 步之内到达不动点**：

  `|M| ≤ n  →  Sigma^n B = Sigma^(|M|)(B)`

**即：任何 Armstrong 推理链的长度不超过属性个数 `|M|`。**

**证明**：由 `exists_synClosureIter_fixed_le_card` 得 `k ≤ |M|` 与 `hfix`；
由 `synClosureIter_stable_of_fixed` 得 `Sigma^n = Sigma^k`（`n ≥ |M| ≥ k`）
与 `Sigma^(|M|) = Sigma^k`（`|M| ≥ k`）；两式合并。

**前件检查（非同义反复）**：前件是「属性集有限」这一**数值/结构条件**，
结论是迭代序列的**等式**。二者类型不同、内容不同；
且 `§4` 说明中给出 `M` 无限时结论**失败**的例子，
故前件确实是必需的、非冗余的。 -/
theorem synClosureIter_stabilizes_card [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) {n : ℕ}
    (hn : Nat.card K.MFCA ≤ n) :
    K.synClosureIter Sig n B = K.synClosureIter Sig (Nat.card K.MFCA) B := by
  obtain ⟨k, hkN, hfix⟩ := K.exists_synClosureIter_fixed_le_card Sig B
  have h1 : K.synClosureIter Sig n B = K.synClosureIter Sig k B :=
    K.synClosureIter_stable_of_fixed Sig B hfix n (le_trans hkN hn)
  have h2 : K.synClosureIter Sig (Nat.card K.MFCA) B = K.synClosureIter Sig k B :=
    K.synClosureIter_stable_of_fixed Sig B hfix (Nat.card K.MFCA) hkN
  rw [h1, h2]

/-- **推论：`|M|` 步与 `|M|+1` 步相等**（不动点判据的具体化）。

由主定理取 `n = |M| + 1` 直接得到。 -/
theorem synClosureIter_card_eq_succ [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) :
    K.synClosureIter Sig (Nat.card K.MFCA) B =
      K.synClosureIter Sig (Nat.card K.MFCA + 1) B :=
  (K.synClosureIter_stabilizes_card Sig B (Nat.le_succ _)).symm

/-- **推论：任意两个 `≥ |M|` 的步数给出同一闭包**（同调性）。

即 `|M|` 之后迭代闭包**不再变化**——这正是「步数无界」缺口的消除。 -/
theorem synClosureIter_eq_of_card_le [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) {m n : ℕ}
    (hm : Nat.card K.MFCA ≤ m) (hn : Nat.card K.MFCA ≤ n) :
    K.synClosureIter Sig m B = K.synClosureIter Sig n B := by
  rw [K.synClosureIter_stabilizes_card Sig B hm,
    K.synClosureIter_stabilizes_card Sig B hn]

/- ==========================================================================
  §4  说明：有限性前件不可去（`M` 无限时结论失败）
==========================================================================

本文件**不**陈述「无限 `M` 上也有界」这一命题，因为它为假：

  取 `M = Nat`、`B = ∅`、`Sig = {({}, {k}) | k ∈ Nat}`，
  则 `Sigma^n(B)` 至少包含 `{0,…,n-1}`，`ncard` 逐步增大，永不稳定。

形式上：`synClosureIter_ncard_le_succ` 说明 `ncard (Sigma^n B)` 只增不减；
「迭代稳定」等价于 `ncard` 停止增长。在 `M` 无限时该增长可以永不停止，
故 `[K.FiniteAttrs]` 是本质前件。

本段**不引入任何定理**（避免用 `sorry` 占位或伪造反例的形式化），
只作为文档登记，说明有限性前件的**必要性**。
========================================================================= -/

end FormalCtx

end Fate
