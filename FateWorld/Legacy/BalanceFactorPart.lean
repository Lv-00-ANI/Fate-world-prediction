import FateWorld.Legacy.BalanceComponents
import FateWorld.Legacy.FactorMarkov

/-!
# 配平的「常数部分」：`p ≡ 1` 的 `CondIndep` 实例（机检，零缺口）

## 背景与定位

`Fate/BalanceComponents.lean` 文件头把「主定理 C 的配平」拆成两块：

1. **因子部分**：`∏_{W_X} · ∏_{W_Y} = ∏_V · ∏_{W_Z}` —— 该文件 §「诚实边界」登记
   为 **未形式化**（依赖 `Split` 与 `W` 的定义，已在 `Fate/View19FactorGraphSplit.lean`
   用 `Split`/`HyperFactorizes` 路线另行处理）。
2. **基数部分**：`c(X∪Y∪Z)·c(Z) = c(X∪Z)·c(Y∪Z)`，其中
   `c(S) := mass S (fun _ => 1) x = |α|^(|V|-|S|)`。
   该文件的 §0.1 `card_balance` 只给了**指数层面的**基数恒等式，
   而 §0.2 的 `mass_one_card`（`c(S)` 的显式值）在此前被登记为缺口，**同一文件末尾已补上**。

**本文件补上它们之间缺的最后一环**：把 `card_balance` 与 `mass_one_card`
**真正接起来**，得到一个**完整的、非平凡的** `CondIndep` 结论：

> ⭐ **`p ≡ 1`（常数密度）时，任意两两不交的 `A, B, Z` 都满足 `CondIndep`。**

这**不是同义反复**：`CondIndep` 是关于四个 `mass` 的乘性等式，
而前件（`p ≡ 1` + 两两不交）里**没有任何一个字**提到 `mass`、乘积或条件独立。

## 结论清单

| 编号 | 命题 |
|---|---|
| `mass_one_card'` | `mass S (·≡1) x = (|α|:ℝ)^(|V|-|S|)` |
| `exp_balance` | 两两不交时 `(|V|-|A∪B∪Z|)+(|V|-|Z|) = (|V|-|A∪Z|)+(|V|-|B∪Z|)` |
| ⭐ `condIndep_one` | 两两不交 ⟹ `CondIndep (·≡1) A B Z` |

## 诚实边界

* 本文件**只处理常数密度 `p ≡ 1`**（配平的「常数部分」）。
  一般的因子密度 `p = ∏_v ψ_v` 的配平不在此文件范围，见 `View19FactorGraphSplit`。
* `mass_one_card'` 是 `BalanceComponents.mass_one_card` 的**重导出**（同一陈述、
  本文件给出与本文件变量上下文一致的版本），不是新结果；本文件的**新结果**是
  `exp_balance` 与 `condIndep_one`。
-/

namespace Fate.GraphToProbView7

open Finset
open Fate
open Fate.DAGFactorization

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]
  [Nonempty α]

omit [Nonempty α] in
/-- ⭐ `mass` 只依赖 `x` 在 `S` 上的取值。 -/
theorem mass_congr_on_S (S : Finset V) (p : (V → α) → ℝ) {x y : V → α}
    (h : ∀ u ∈ S, x u = y u) : mass S p x = mass S p y := by
  unfold mass
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · have hw' : ∀ u ∈ S, w u = y u := by
      intro u hu; rw [hw u hu, h u hu]
    rw [if_pos hw, if_pos hw']
  · have hw' : ¬ ∀ u ∈ S, w u = y u := by
      intro hc
      exact hw (fun u hu => by rw [hc u hu, ← h u hu])
    rw [if_neg hw, if_neg hw']

omit [Nonempty α] in
/-- ⭐ `mass` 对函数参数的标量乘线性。 -/
theorem mass_const_mul (S : Finset V) (c : ℝ) (p : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => c * p w) x = c * mass S p x := by
  unfold mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · simp only [if_pos hw]
  · simp only [if_neg hw, mul_zero]

/-- ⭐ 常数密度的 `mass` 值（`BalanceComponents.mass_one_card` 的重导出）。 -/
theorem mass_one_card' (S : Finset V) (x : V → α) :
    mass S (fun _ => (1 : ℝ)) x
      = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) :=
  mass_one_card S x

/-- ⭐⭐ **指数层面的基数恒等式**：`A, B, Z` 两两不交时，
`(|V|-|A∪B∪Z|) + (|V|-|Z|) = (|V|-|A∪Z|) + (|V|-|B∪Z|)`。

**⟹ 这是把 `card_balance` 从「`Finset.card` 层面」搬到「`mass` 指数层面」的关键一步。** -/
theorem exp_balance (A B Z : Finset V)
    (hAB : Disjoint A B) (hAZ : Disjoint A Z) (hBZ : Disjoint B Z) :
    (Fintype.card V - (A ∪ B ∪ Z).card) + (Fintype.card V - Z.card)
      = (Fintype.card V - (A ∪ Z).card) + (Fintype.card V - (B ∪ Z).card) := by
  have hb : (A ∪ B ∪ Z).card + Z.card = (A ∪ Z).card + (B ∪ Z).card :=
    card_balance A B Z hAB hAZ hBZ
  have h1 : (A ∪ B ∪ Z).card ≤ Fintype.card V := card_le_univ _
  have h2 : Z.card ≤ Fintype.card V := card_le_univ _
  have h3 : (A ∪ Z).card ≤ Fintype.card V := card_le_univ _
  have h4 : (B ∪ Z).card ≤ Fintype.card V := card_le_univ _
  omega

/-- ⭐⭐⭐ **常数密度的条件独立（配平"常数部分"的完整机检实例）**。

`A, B, Z` 两两不交时，常数密度 `p ≡ 1` 满足 `CondIndep A B Z`：
```
mass (A∪B∪Z) 1 x * mass Z 1 x = mass (A∪Z) 1 x * mass (B∪Z) 1 x
```
**前件只谈集合不交与基数，结论是四个 `mass` 的乘性等式 —— 非同义反复。** -/
theorem condIndep_one (A B Z : Finset V)
    (hAB : Disjoint A B) (hAZ : Disjoint A Z) (hBZ : Disjoint B Z) (x : V → α) :
    mass (A ∪ B ∪ Z) (fun _ => (1 : ℝ)) x * mass Z (fun _ => (1 : ℝ)) x
      = mass (A ∪ Z) (fun _ => (1 : ℝ)) x * mass (B ∪ Z) (fun _ => (1 : ℝ)) x := by
  rw [mass_one_card', mass_one_card', mass_one_card', mass_one_card']
  rw [← pow_add, ← pow_add]
  congr 1
  exact exp_balance A B Z hAB hAZ hBZ

end Fate.GraphToProbView7
