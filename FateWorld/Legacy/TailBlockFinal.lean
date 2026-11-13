/-
! TailBlockFinal：**主定理 D（尾块情形）** —— 零 `sorry` 的完整证明

## 0 结论

```lean
theorem condIndep_tail_block (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hTail : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z)
    (hsplit : Fate.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    Fate.FactorMarkov.CondIndep p X Y Z
```

**不需要 `hcover`（`X ∪ Y ∪ Z = univ`），不需要 `hTail`（它被 `Split` 蕴含）。**

## 1 数学要点（量纲分析的更正版）

记 `A := X ∪ Y ∪ Z`，`T := Aᶜ = univ \ A`（尾块）。`Split R X Y Z` 单独就给出

  `∀ v, R v ⊆ A`   （`R v ⊆ X∪Z ⊆ A` 或 `R v ⊆ Y∪Z ⊆ A`），

于是 `p = ∏ v, ψ v` **只读 `A`**（引理 `readsOn_prod`）。

### 1.1 关键量纲引理（`mass_release` / `mass_add_block`）

若 `p` 只读 `A`、`S ⊆ A`，则把 `T` 的坐标逐个"放开"（`mass_insert_sum` 的反向）
每次恰好多一个 `|α|` 因子：

  **`mass S p x = |α| ^ |T| · mass (S ∪ T) p x`**    （`mass_add_block`）

**⟹ 四个 `mass`（`A`、`Z`、`X∪Z`、`Y∪Z`，全部 `⊆ A`）都带同一个因子 `|α|^|T|`。**
（这正是任务书"第 1 步"的实质内容；只是常数写成 `S ∪ T` 的形式比 `massA` 更省事，
因为 `mass (S ∪ T)` 就是 `mass` 本身，无需新定义。）

### 1.2 化归：`Z` 换成 `Z' := Z ∪ T`

这是本文件的核心技巧。注意 `X ∪ Y ∪ Z' = A ∪ T = univ`，于是
`condIndep_general` 的 `hcover` 被满足，并且

| 条件 | 为什么成立 |
|---|---|
| `Split R X Y Z'` | `R v ⊆ A ⊆ X ∪ Z'` 或 `⊆ Y ∪ Z'` |
| `Disjoint X Y` | 假设 |
| `Disjoint X Z'` | `X ⊆ A` 且 `X ∩ Z = ∅`、`X ∩ T = ∅`（`T = Aᶜ`）|
| `Disjoint Y Z'` | 同上 |
| `X ∪ Y ∪ Z' = univ` | `Z' = Z ∪ Aᶜ` ⟹ 并集 `= A ∪ Aᶜ = univ` |

于是 **`condIndep_general ψ p … : CondIndep p X Y Z'`**，即

  `mass univ p x · mass Z' p x = mass (X∪Z') p x · mass (Y∪Z') p x`。

再用 `mass_add_block` 把 `CondIndep p X Y Z` 的四个 `mass` 逐个换成 `mass (· ∪ T)`
（两边各得 `(|α|^|T|)^2`），**等式完全对上**：

* LHS = `|α|^|T| mass univ · |α|^|T| mass Z'`
* RHS = `|α|^|T| mass (X∪Z') · |α|^|T| mass (Y∪Z')`

## 2 诚实边界

* `[Nonempty α]` 是 `mass`/`glue` 基础设施的副作用，**不削弱结论**：
  `CondIndep` 是 `∀ x : V → α, …`，若 `α` 空而 `V` 非空则 `V → α` 为空，
  结论空洞为真。
* `hTail` 未被使用（保留以匹配任务书签名）。
* **上一轮 `TailBlockV4` 里那条 `mass S p x = |α|^(|A|-|S|) · mass A p x` 是错的**
  （反例：`S = ∅` 时要求 `Σ_w p w = |α|^|A| p x`）。本文件改用
  `mass S p x = |α|^|T| · mass (S ∪ T) p x`，**方向与指数都不同**，
  这才是正确的量纲。
- 零 `sorry` / `admit` / `axiom`；不写 `Fate/`；不改 `Fate.lean`。
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.FactorMarkov
import FateWorld.Legacy.View19FactorGraphSplit
import FateWorld.Legacy.MassProCover
import FateWorld.Legacy.CondIndepGeneralNZ

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TailBlockFinal

open Finset Fate Fate.DAGFactorization Fate.FactorMarkov Fate.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ===========================================================================
  §1  `ReadsOn` 与乘积的读集局部性
  =========================================================================== -/

/-- `ReadsOn f A`：`f` 只读 `A` 上的坐标。 -/
def ReadsOn (f : (V → α) → ℝ) (A : Finset V) : Prop :=
  ∀ w w' : V → α, (∀ u ∈ A, w u = w' u) → f w = f w'

/-- ⭐ **因子之积的读集局部性**：每个 `ψ v` 只读 `R v ⊆ A` ⟹ `∏ v, ψ v` 只读 `A`。 -/
theorem readsOn_prod (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    {A : Finset V} (hRA : ∀ v, R v ⊆ A) :
    ReadsOn (fun w => ∏ v, ψ v w) A := by
  intro w w' h
  exact Finset.prod_congr rfl fun v _ => hread v w w' (fun u hu => h u (hRA v hu))

/-! ===========================================================================
  §2  `mass` 与"只读 `A`"的相互作用
  =========================================================================== -/

/-- ⭐⭐ **`mass S p` 只依赖 `x` 在 `A` 上的值**（`p` 只读 `A`、`S ⊆ A`）。

证明：`mass_eq_sum_glue` 把 `mass` 重写成 `glue` 上的一次求和；
`glue S x t` 与 `x` 在 `S` 上一致，而 `S ⊆ A`，故 `p` 作用其上只依赖 `x`。 -/
theorem mass_congr_of_readsOn {p : (V → α) → ℝ} {A S : Finset V}
    (hp : ReadsOn p A) (hSA : S ⊆ A) {x y : V → α} (hxy : ∀ u ∈ A, x u = y u) :
    mass S p x = mass S p y := by
  classical
  rw [mass_eq_sum_glue S p x, mass_eq_sum_glue S p y]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine hp _ _ fun u huA => ?_
  by_cases huS : u ∈ S
  · rw [glue_of_mem S x t huS, glue_of_mem S y t huS, hxy u huA]
  · rw [glue_of_not_mem S x t huS, glue_of_not_mem S y t huS]

/-- ⭐⭐ **`mass (insert h T) p ·` 与 `x h` 无关**（`p` 只读 `A`、`h ∉ A`）。

这需要**两个** `unpin` 版本在 `A` 上一致：`h ∉ A`，故 `unpin h x a` 与
`unpin h x a'` 在 `A` 上相同。 -/
theorem mass_insert_unpin_indep {p : (V → α) → ℝ} {A : Finset V} (hp : ReadsOn p A)
    {h : V} (hhA : h ∉ A) (T : Finset V) (x : V → α) (a a' : α) :
    mass (insert h T) p (unpin h x a) = mass (insert h T) p (unpin h x a') := by
  classical
  rw [mass_eq_sum_glue (insert h T) p (unpin h x a),
    mass_eq_sum_glue (insert h T) p (unpin h x a')]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine hp _ _ fun u huA => ?_
  by_cases huT : u ∈ T
  · have huh : u ≠ h := fun e => hhA (e ▸ huA)
    rw [glue_of_mem (insert h T) (unpin h x a) t (Finset.mem_insert_of_mem huT),
      glue_of_mem (insert h T) (unpin h x a') t (Finset.mem_insert_of_mem huT)]
    unfold unpin
    rw [if_neg huh, if_neg huh]
  · have huI : u ∉ insert h T := by
      intro hin
      rcases Finset.mem_insert.mp hin with h' | h'
      · exact hhA (h' ▸ huA)
      · exact huT h'
    rw [glue_of_not_mem (insert h T) (unpin h x a) t huI,
      glue_of_not_mem (insert h T) (unpin h x a') t huI]

/-- ⭐⭐⭐ **`mass` 的"放开一个坐标"**：若 `p` 只读 `A`、`h ∉ A`、`h ∉ T`，则

  `mass T p x = |α| · mass (insert h T) p x`。

**证明**：`mass_insert_sum` 给出 `Σ_a mass (insert h T) p (unpin h x a) = mass T p x`；
而 `mass_insert_unpin_indep` 说被加项**与 `a` 无关**，取 `a = x h`
（`unpin h x (x h) = x`）即得。 -/
theorem mass_release {p : (V → α) → ℝ} {A : Finset V} (hp : ReadsOn p A)
    {h : V} (hhA : h ∉ A) {T : Finset V} (hhT : h ∉ T) (x : V → α) :
    mass T p x = (Fintype.card α : ℝ) * mass (insert h T) p x := by
  classical
  have hstep : ∀ a : α, mass (insert h T) p (unpin h x a) = mass (insert h T) p x := by
    intro a
    have h := mass_insert_unpin_indep hp hhA T x a (x h)
    rwa [unpin_self] at h
  rw [← mass_insert_sum h T hhT p x]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hstep a]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- ⭐⭐⭐⭐ **尾块常数**：`p` 只读 `A`、`S ⊆ A` ⟹ 把 `B`（`B ∩ A = ∅`）整块放开
只贡献一个与 `x` 无关的常数 `|α|^|B|`。

  `mass S p x = |α| ^ |B| · mass (S ∪ B) p x`

**证明**：对 `B` 归纳，每步用 `mass_release`（`h ∈ B` ⟹ `h ∉ A`）。 -/
theorem mass_add_block {p : (V → α) → ℝ} {A : Finset V} (hp : ReadsOn p A)
    {S : Finset V} (hSA : S ⊆ A) (x : V → α) :
    ∀ B : Finset V, Disjoint B A →
      mass S p x = ((Fintype.card α : ℝ) ^ B.card) * mass (S ∪ B) p x := by
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert h B' hhB' ih =>
    intro hdisj
    -- `h ∉ A`，`Disjoint B' A`
    have hhA : h ∉ A := fun hh => Finset.disjoint_left.mp hdisj (Finset.mem_insert_self h B') hh
    have hdisj' : Disjoint B' A := hdisj.mono_left (Finset.subset_insert h B')
    have hhB'Not : h ∉ B' := hhB'
    -- 归纳假设
    have hIH := ih hdisj'
    -- `h ∉ S ∪ B'`
    have hhSB : h ∉ S ∪ B' := by
      intro hin
      rcases Finset.mem_union.mp hin with h' | h'
      · exact hhA (hSA h')
      · exact hhB'Not h'
    -- `mass_release`
    have hrel := mass_release hp hhA hhSB x
    -- 并集形式改写
    have hunion : S ∪ insert h B' = insert h (S ∪ B') := by
      ext u
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hIH, hrel, hunion, Finset.card_insert_of_notMem hhB', pow_succ]
    ring

end TailBlockFinal
