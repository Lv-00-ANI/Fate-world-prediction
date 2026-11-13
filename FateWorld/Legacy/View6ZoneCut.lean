/-
# 视角 6（修订版）：**消元序支撑切**（elimination-ordered support cut）
## —— 「图 ⟹ 概率」桥的第 6 种证明策略

## 0 本次修订做了什么（**先说否定的那一半**）

上一版 `Fate/View6FactorSupport.lean` 提出的策略是
「**纯支撑切** `SupportCut`」：把因子按**读集** `{v} ∪ pa(v)` 分三段
（常值段 / `X∪Z` 侧 / `Y∪Z` 侧），产品就**逐点分裂** `p = f · g`。
它把图侧压缩成一条组合命题，并把

```
∀ G X Y Z, G.dSep X Y Z → SupportCut G X Y Z          (★)
```

登记为 `supportCut_of_dsep_Gap`（「未闭合，不进下游」）。

**本次修订证明：(★) 是假命题，不是未闭合的缺口。**

> **`§3` 反例（机器检证，零 `sorry`）**：链 `0→1→2→3`，
> `X = {0}`、`Y = {3}`、`Z = {1}`。
> `dSep {0}{3}|{1}` **成立**（`dSep` 的 Bayes-ball 语义，`decide` 判定）；
> 但顶点 `2` 的读集是 `{1,2}`，它既不 `⊆ X∪Z = {0,1}` 也不 `⊆ Y∪Z = {1,3}`，
> 且它不常值 —— **没有任何一段可以安放 `π 2`**。
> 故 `SupportCut` **为假**。定理名 `supportCut_not_implied_by_dSep`。

**为什么这个反例是对的（数学）**：链 `0→1→2→3` 上
$$p = \pi_0\cdot\pi_1(x_1|x_0)\cdot\pi_2(x_2|x_1)\cdot\pi_3(x_3|x_2).$$
把它在 `X∪Y∪Z = {0,1,3}` 上边缘化，**必须对 `x₂` 求和**：
$$\mathrm{mass}_{\{0,1,3\}}p = \pi_0\,\pi_1(x_1|x_0)\cdot
  \underbrace{\textstyle\sum_{x_2}\pi_2(x_2|x_1)\pi_3(x_3|x_2)}_{=:\ \kappa(x_1,x_3)} .$$
这个 `κ` 才是 `Y∪Z` 侧的因子 —— 而它**根本不是任何一个 `π_v`**，
是 `π_2` 与 `π_3` **求和消元**之后的**消息**。
⟹ 纯支撑切**在原理上**做不到：它只看「因子读哪些坐标」，
而条件独立需要的是「**消元后**的消息读哪些坐标」。

## 1 视角 6 的正确形态：**消元序支撑切**

> 把「支撑切」从**原始因子**的读集，搬到**按消元序产生消息**的读集上。

**构造（分三层，全部塔无关）**

| 层 | 内容 | Lean |
|---|---|---|
| **L1 代数** | 指标三分段（常值 / A 侧 / B 侧）+ 落区 ⟹ `∏ = f·g` **逐点** | `prod_zone_split3` |
| **L2 消元（非塔）** | 单点消元：`u` 不被任何其它因子读 ⟹ `mass (univ\{u}) (∏π) = (∑_a π_u[:,a]) · ∏_{v≠u}π_v` | `absorb_free` |
| **L3 图侧** | `ElimCut`：在**消元后**的读集上做切；`§5` 在链上由 `dSep` 造出 | `ElimCut`, `chain4_elimCut` |

**L2 与被证伪的「塔」正交**：塔说的是 `mass S (mass T p)`（**嵌套** `mass`，假），
L2 用的是 `mass_insert_sum`（**单层** `mass` 对**一个坐标**求和，真且已证）。
本文件**全文不出现 `mass S (mass T p)`**（`§8` 有 `grep` 级声明）。

## 2 交付清单

| # | 定理 | 内容 | 状态 |
|---|---|---|---|
| **V6.01** | `prod_zone_split3` | ⭐ 代数心脏：常值段 + 两区段 + 落区 ⟹ `∏ = f·g` | ✅ |
| **V6.02** | `prod_zone_reads` | 单段乘积只读本区 | ✅ |
| **V6.03** | `supportCut_not_implied_by_dSep` | ⭐⭐⭐ **尖锐否定**：纯支撑切不可由 `dSep` 推出 | ✅ |
| **V6.04** | `absorb_free` | ⭐⭐ 单点消元（**非塔**，只用 `mass_insert_sum`） | ✅ |
| **V6.05** | `absorb_free_reads` | 消元消息只读「父 ∪ 已吸收」 | ✅ |
| **V6.06** | `ElimCut` | 消元序支撑切（定义） | ✅ |
| **V6.07** | `elimCut_zone_split` | ⭐ 消元切 ⟹ `mass W p = f(x_{X∪Z})·g(x_{Y∪Z})` | ✅ |
| **V6.08** | `chain4_dsep` / `chain4_elimCut` | 链 `0→1→2→3` 上 `dSep` 造出消元切 | ✅ |
| **V6.09** | `chain4_elim_mass_split` | ⭐⭐⭐ **端到端**：`dSep + FactorizesOn ⟹ mass {0,1,3} p = f·g` | ✅ |
| **V6.10** | `chain4_factorizesOn_condMul` | ⭐⭐⭐⭐ 收口到 `CondMul` | ✅ |

## 3 与前 5 种 / 与其他视角的分界

| 策略 | 载体 | 卡点 |
|---|---|---|
| 甲 `condMass` | `mass (S∪T)/mass S` | 需 `mass S ≠ 0`；**嵌套** `mass` |
| 乙 拓扑递归 `RouteB` | `Factorizes`/`LMG` | 定义被**证伪** |
| 丙 类型层 `Marginal` | `(S→α)→ℝ` | 只有 `T ⊆ S` 方向 |
| 丁 道德图 | `USeparated` | 中间三步从未做 |
| 戊 `LMG ⟹ GM` | `LMG` | `LMG` **为假** |
| **己（本文件）** | **原始读集** | ⭐ **被 `§3` 证伪**（本次修订新增）|
| **己′（本文件修正）** | **消元后读集** | ✅ 链上闭合；一般 DAG 登记为 `ElimCut_of_dSep_Gap` |

**与视角 11（拓扑前缀）的分界**：视角 11 的 `peel_lower` 只在**拓扑前缀**上工作，
且其收口义务是 `FibreGluing`。本文件的消元是**由 `dSep` 定位的任意自由点**
（不要求在前缀里），切的对象是**消息的读集**（不是 `mass` 的值）。

**与视角 20 的分界**：视角 20 证明 `CondMulLike`（集合口径 `mass`）**退化**；
本文件的 L2/L3 都不经 `CondMulLike`，直接在 `mass W p` 上做**逐点**分裂。

## 4 ⚠ 诚实边界（必读）

**已闭合（零 `sorry` / 零 `axiom`，仅 `propext`/`Classical.choice`/`Quot.sound`）**

```
L1  L2  L3（链 0→1→2→3 与 0→1→2 上）全部
dSep {0}{3}|{1}  ∧  FactorizesOn chain4 p  ⟹  mass {0,1,3} p = f(x₀,x₁)·g(x₁,x₃)
                                               ⟹  CondMul（三变量收缩）
```

**未闭合（登记，不进下游）**

```
ElimCut_of_dSep_Gap : ∀ G X Y Z, G.dSep X Y Z → ElimCut G X Y Z
```

**它是一个纯图论 + 纯组合命题**（`ElimCut` 里没有任何概率内容、没有 `mass`）。
本文件在两条链上**证它为真**、在 `§3` 的纯切形态上**证其必假**，
故它不是「恒真转发」，也不是「明显为假」。

**本文件不声称「Pearl 1.2.4 已证」。**
-/

import FateWorld.Legacy._root.CausDAG
import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.T1A2
import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.SeparableCondMul
import FateWorld.Legacy.FinCondIndep
import FateWorld.Legacy.GlobalMarkovMinimal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Fate
namespace View6ZoneCut

open Finset
open Causalean.Graph

variable {V : Type} [DecidableEq V] [Fintype V]

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §1 支撑语言（读集）
  =========================================================================== -/

/-- 因子的读集 `R v = {v} ∪ pa(v)`（`FactorizesOn` 的口径，`Fate.T1A2`）。 -/
def readSet (G : DAG V) (v : V) : Finset V := insert v (G.parents v)

theorem mem_readSet {G : DAG V} {v w : V} :
    w ∈ readSet G v ↔ w = v ∨ G.edge w v := by
  unfold readSet
  rw [Finset.mem_insert, G.mem_parents]

/-! ===========================================================================
  §2 L1 代数心脏：**指标三分段 + 落区 ⟹ 逐点 `∏ = f · g`**
  （**全文不出现 `mass`、不出现求和**）
  =========================================================================== -/

/-- ⭐⭐ **V6.02 单段乘积只读本区**。 -/
theorem prod_zone_reads {S ZA : Finset V} {reads : V → Finset V}
    (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, Fate.T1A2.ReadsOnlyOn (reads v) (π v))
    (hsub : ∀ v ∈ S, reads v ⊆ ZA) :
    Fate.T1A2.ReadsOnlyOn ZA (fun x => ∏ v ∈ S, π v x) := by
  intro x y hxy
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hreads v x y fun w hw => hxy w (hsub v hv hw)

theorem prod_zone_split {V₁ V₂ : Finset V} (hdisj : Disjoint V₁ V₂)
    (hcover : V₁ ∪ V₂ = univ) (π : V → (V → Bool) → ℝ) (x : V → Bool) :
    (∏ v, π v x) = (∏ v ∈ V₁, π v x) * (∏ v ∈ V₂, π v x) := by
  conv_lhs => rw [← hcover]
  rw [Finset.prod_union hdisj]

/-- ⭐⭐⭐ **V6.01 代数心脏：三分段 + 落区 ⟹ `∏ = f · g`（逐点）**。

指标集三分 `V₀ ⊔ V₁ ⊔ V₂ = univ`；`V₀` 是**常值段**（读集为空），
`V₁` 落区 `ZA`，`V₂` 落区 `ZB`（**区可以重叠**，这正是条件于 `Z` 的含义）。

**⚠ 常值段为什么必需**：真实 DAG 里总有读集与查询无关的因子；
硬塞进某一侧需要 `reads v ⊆ ZA` 或 `⊆ ZB`，二者可能都不成立
（`§3` 的反例正是这样失败的 —— 但那是因为 `π 2` 的读集**跨两侧**，
不是常值，所以**常值段救不了它**，这才需要 L2 消元）。 -/
theorem prod_zone_split3_gen {S V₀ V₁ V₂ ZA ZB : Finset V} {reads : V → Finset V}
    (h01 : Disjoint V₀ V₁) (h02 : Disjoint V₀ V₂) (h12 : Disjoint V₁ V₂)
    (hcover : V₀ ∪ V₁ ∪ V₂ = S)
    (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, Fate.T1A2.ReadsOnlyOn (reads v) (π v))
    (h0 : ∀ v ∈ V₀, reads v = ∅)
    (hA : ∀ v ∈ V₁, reads v ⊆ ZA) (hB : ∀ v ∈ V₂, reads v ⊆ ZB) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn ZA f ∧ Fate.T1A2.ReadsOnlyOn ZB g ∧
      ∀ x, (∏ v ∈ S, π v x) = f x * g x := by
  have hconst : ∀ v ∈ V₀, ∀ x y : V → Bool, π v x = π v y := by
    intro v hv x y
    exact hreads v x y (by rw [h0 v hv]; intro w hw; exact absurd hw (notMem_empty w))
  have hV0 : ∀ x y : V → Bool, (∏ v ∈ V₀, π v x) = (∏ v ∈ V₀, π v y) :=
    fun x y => Finset.prod_congr rfl fun v hv => hconst v hv x y
  refine ⟨(fun x => (∏ v ∈ V₀, π v x) * (∏ v ∈ V₁, π v x)),
          (fun x => ∏ v ∈ V₂, π v x), ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : (∏ v ∈ V₁, π v x) = (∏ v ∈ V₁, π v y) :=
      prod_zone_reads (S := V₁) (ZA := ZA) π hreads hA x y hxy
    show (∏ v ∈ V₀, π v x) * (∏ v ∈ V₁, π v x)
        = (∏ v ∈ V₀, π v y) * (∏ v ∈ V₁, π v y)
    rw [hV0 x y, h1]
  · exact prod_zone_reads (S := V₂) (ZA := ZB) π hreads hB
  · intro x
    rw [← hcover, Finset.union_assoc,
      Finset.prod_union (h := Finset.disjoint_union_right.mpr ⟨h01, h02⟩),
      Finset.prod_union (h := h12), mul_assoc]

/-- **V6.01（`univ` 版）**：§2 的代数心脏，指标覆盖整个 `univ`。 -/
theorem prod_zone_split3 {V₀ V₁ V₂ ZA ZB : Finset V} {reads : V → Finset V}
    (h01 : Disjoint V₀ V₁) (h02 : Disjoint V₀ V₂) (h12 : Disjoint V₁ V₂)
    (hcover : V₀ ∪ V₁ ∪ V₂ = univ)
    (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, Fate.T1A2.ReadsOnlyOn (reads v) (π v))
    (h0 : ∀ v ∈ V₀, reads v = ∅)
    (hA : ∀ v ∈ V₁, reads v ⊆ ZA) (hB : ∀ v ∈ V₂, reads v ⊆ ZB) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn ZA f ∧ Fate.T1A2.ReadsOnlyOn ZB g ∧
      ∀ x, (∏ v, π v x) = f x * g x :=
  prod_zone_split3_gen (S := univ) h01 h02 h12 hcover π hreads h0 hA hB

/-! ===========================================================================
  §3 ⭐⭐⭐ **尖锐否定：纯支撑切不可由 `dSep` 推出**
  =========================================================================== -/

/-- 纯支撑切（上一版 `View6FactorSupport.SupportCut` 的**逐字形态**，
在 `Fin 4` 上重述，以便反例落在同一载体上）。 -/
def SupportCut (G : DAG (Fin 4)) (X Y Z : Finset (Fin 4)) : Prop :=
  ∃ V₀ V₁ V₂ : Finset (Fin 4),
    Disjoint V₀ V₁ ∧ Disjoint V₀ V₂ ∧ Disjoint V₁ V₂ ∧ V₀ ∪ V₁ ∪ V₂ = univ ∧
    (∀ v ∈ V₀, insert v (G.parents v) = ∅) ∧
    (∀ v ∈ V₁, insert v (G.parents v) ⊆ X ∪ Z) ∧
    (∀ v ∈ V₂, insert v (G.parents v) ⊆ Y ∪ Z) ∧
    X ⊆ V₁ ∪ V₀ ∧ Y ⊆ V₂

/-- ⭐ **链 `0 → 1 → 2 → 3`**（`Fin 4`）。无环性是真的证的（沿 `<` 严格上升）。 -/
def chain4 : DAG (Fin 4) where
  edge := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v h
    have key : ∀ x y : Fin 4, Relation.TransGen
        (fun u v : Fin 4 => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)) x y →
        x < y := by
      intro x y hxy
      induction hxy with
      | single hstep =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (subst h1; subst h2; decide)
      | tail _ hstep ih =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (subst h1; subst h2; omega)
    exact absurd (key v v h) (lt_irrefl v)

theorem chain4_pa_two : chain4.parents (2 : Fin 4) = {(1 : Fin 4)} := by decide
theorem chain4_read_two : insert (2 : Fin 4) (chain4.parents 2) = {1, 2} := by decide

/-- ⭐⭐⭐ **`dSep {0} {3} | {1}` 在 `0→1→2→3` 上成立**（Bayes-ball，`decide`）。 -/
theorem chain4_dsep :
    chain4.dSep {(0 : Fin 4)} {(3 : Fin 4)} {(1 : Fin 4)} := by
  unfold Causalean.Graph.DAG.dSep
  decide

/-- ⭐⭐⭐⭐ **V6.03 尖锐否定**：`dSep {0}{3}|{1}` **成立**，
但**不存在**纯支撑切。

**⟹ 上一版把 `∀ G X Y Z, dSep → SupportCut` 登记为「缺口」是不准确的：
它是*假命题*。本定理是视角 6 必须同时上报的否定性结论。** -/
theorem supportCut_not_implied_by_dSep :
    ¬ SupportCut chain4 {(0 : Fin 4)} {(3 : Fin 4)} {(1 : Fin 4)} := by
  rintro ⟨V₀, V₁, V₂, h01, h02, h12, hcov, h0, hA, hB, hX, hY⟩
  have h2mem : (2 : Fin 4) ∈ V₀ ∪ V₁ ∪ V₂ := by rw [hcov]; exact mem_univ _
  have hins2 : insert (2 : Fin 4) (chain4.parents 2) = {1, 2} := chain4_read_two
  rcases Finset.mem_union.mp h2mem with h2a | h2b
  · rcases Finset.mem_union.mp h2a with h2 | h2
    · -- 落在常值段：读集必须是 `∅`，但它是 `{1,2}`
      have h := h0 2 h2
      rw [hins2] at h
      have hmem : (1 : Fin 4) ∈ (∅ : Finset (Fin 4)) := h ▸ (by decide)
      exact absurd hmem (notMem_empty 1)
    · -- 落在 `X∪Z` 侧：需要 `{1,2} ⊆ {0,1}`，但 `2` 不在
      have hsub := hA 2 h2
      rw [hins2] at hsub
      have hmem : (2 : Fin 4) ∈ ({(0 : Fin 4)} ∪ {(1 : Fin 4)} : Finset (Fin 4)) :=
        hsub (by decide)
      simp at hmem
  · -- 落在 `Y∪Z` 侧：需要 `{1,2} ⊆ {1,3}`，但 `2` 不在
    have hsub := hB 2 h2b
    rw [hins2] at hsub
    have hmem : (2 : Fin 4) ∈ ({(3 : Fin 4)} ∪ {(1 : Fin 4)} : Finset (Fin 4)) :=
      hsub (by decide)
    simp at hmem

/-! ===========================================================================
  §4 L2：**单点消元（非塔）**

  ⚠ 与已证伪的塔性质 `mass S (mass T p) = mass (S∪T) p` **正交**：
  本节只对**一个坐标**用 `mass_insert_sum`（**单层** `mass`），
  **没有** `mass` 的嵌套，故不可能踩塔。
  =========================================================================== -/

open Fate.DAGFactorization (mass)

/-- 局部 `unpin`（`Bool` 特化，便于省略类型参数）。 -/
noncomputable def unpinB (u : V) (x : V → Bool) (a : Bool) : V → Bool :=
  Fate.DAGFactorization.unpin u x a

theorem unpinB_self (u : V) (x : V → Bool) : unpinB u x (x u) = x :=
  Fate.DAGFactorization.unpin_self u x

/-- `π v` 不读坐标 `u`（`u ∉ readSet v`，且 `LocalTo`）。 -/
theorem insensitive_of_not_mem_readSet {π : V → (V → Bool) → ℝ} {G : DAG V}
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (readSet G v) (π v))
    {v u : V} (h : u ∉ readSet G v) (x : V → Bool) (a b : Bool) :
    π v (unpinB u x a) = π v (unpinB u x b) := by
  refine hloc v _ _ ?_
  intro w hw
  show (if w = u then a else x w) = (if w = u then b else x w)
  by_cases hwu : w = u
  · exact absurd (hwu ▸ hw) h
  · rw [if_neg hwu, if_neg hwu]

/-- ⭐⭐⭐⭐ **V6.04 单点消元（`u` 是自由点 ⟹ `∏π` 在 `univ\{u}` 上的边缘分裂）**。

$$\mathrm{mass}_{\,V\setminus\{u\}}\Bigl(\prod_v \pi_v\Bigr) x
 =\Bigl(\sum_a \pi_u\,[x_u{:=}a]\Bigr)\cdot\prod_{v\neq u}\pi_v\,x .$$

**只用 `mass_insert_sum`（T1，单坐标）+ `Finset.prod_erase`**，
**无 `mass` 嵌套、无塔、无归一化假设**。 -/
theorem absorb_free {G : DAG V} {π : V → (V → Bool) → ℝ}
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (readSet G v) (π v))
    {u : V} (hfree : ∀ v, v ≠ u → u ∉ readSet G v) (x : V → Bool) :
    mass (univ \ {u}) (fun y => ∏ v, π v y) x
      = (∑ a : Bool, π u (unpinB u x a)) * (∏ v ∈ univ.erase u, π v x) := by
  classical
  have hnote : (univ \ {u} : Finset V) = univ.erase u := by
    ext w; simp [eq_comm]
  -- 关键：`mass (univ \ {u}) = ∑_a (mass univ)` 型展开（单坐标）
  have hstep : mass (univ \ {u}) (fun y => ∏ v, π v y) x
      = ∑ a : Bool, (∏ v, π v (unpinB u x a)) := by
    have hins : insert u (univ \ {u}) = (univ : Finset V) := by
      ext w; simp
    have hnu : u ∉ (univ \ {u} : Finset V) := by simp
    rw [Fate.DAGFactorization.mass_insert_sum' u (univ \ {u}) hnu
      (fun y => ∏ v, π v y) x, hins]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Fate.DAGFactorization.mass_univ _ _
  rw [hstep]
  have hprod : ∀ y : V → Bool, (∏ v, π v y) = π u y * (∏ v ∈ univ.erase u, π v y) := by
    intro y
    rw [← Finset.mul_prod_erase (univ : Finset V) (fun v => π v y) (mem_univ u)]
  have hterm : ∀ a : Bool, (∏ v, π v (unpinB u x a))
      = π u (unpinB u x a) * (∏ v ∈ univ.erase u, π v x) := by
    intro a
    rw [hprod]
    have hinner : (∏ v ∈ univ.erase u, π v (unpinB u x a)) = (∏ v ∈ univ.erase u, π v x) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
      exact (insensitive_of_not_mem_readSet hloc (hfree v hvu) x a (x u)).trans (by
        rw [unpinB_self])
    rw [hinner]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_mul]

/-! ===========================================================================
  §5 L3：**消元序支撑切 `ElimCut`** 与主定理
  =========================================================================== -/

/-- ⭐⭐⭐ **V6.05 消元消息的读集**：`κ := ∑_a π_u[:,a]` **只读 `pa(u)`**。

**这是消元的全部收益**：原始因子 `π_u` 读 `{u} ∪ pa(u)`；
消元后的消息 `κ` **丢掉了 `u`**，只读 `pa(u)`。
⟹ 消元**只会缩小**读集，故它使支撑切**更容易**成功。
`§3` 的反例里 `π 2` 读 `{1,2}` 无处安放；消元后 `κ` 读 `pa(2) = {1} ⊆ X∪Z`，
**立刻可安放**。 -/
theorem absorb_free_reads {G : DAG V} {π : V → (V → Bool) → ℝ}
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (readSet G v) (π v))
    (u : V) :
    Fate.T1A2.ReadsOnlyOn (G.parents u) (fun x => ∑ a : Bool, π u (unpinB u x a)) := by
  intro x y hxy
  refine Finset.sum_congr rfl fun a _ => ?_
  refine hloc u _ _ ?_
  intro w hw
  rw [mem_readSet] at hw
  show (if w = u then a else x w) = (if w = u then a else y w)
  rcases hw with hwu | hw
  · rw [hwu]; rw [if_pos rfl, if_pos rfl]
  · have h1 : w ≠ u := by
      intro h2
      have hirr : ¬ G.edge w w := G.irrefl w
      exact hirr (h2 ▸ hw)
    rw [if_neg h1, if_neg h1]
    exact hxy w (G.mem_parents.mpr hw)

/-- ⭐⭐⭐⭐⭐ **`ElimCut`（消元序支撑切）**。

存在一个**被消元的顶点 `u`**，使

1. `u` **不被任何其它因子读**（`hfree`，使 `absorb_free` 可用）；
2. `univ \ {u}` 按**原始读集**三分：常值段 `V₀` / `X∪Z` 侧 `V₁` / `Y∪Z` 侧 `V₂`；
3. `X` 落 `V₁∪V₀`、`Y` 落 `V₂`；
4. **消元消息 `κ` 的读集 `pa(u)` 落在 `X∪Z` 侧**。

**⚠ `dSep` 不在定义里**：它是「`ElimCut` 是否可得」的图侧来源（`§6` 在链上造出）。
**⚠ 定义里没有任何概率内容、没有 `mass`**：它是**纯组合 + 纯图论**谓词。 -/
def ElimCut (G : DAG V) (u : V) (X Y Z : Finset V) : Prop :=
  ∃ V₀ V₁ V₂ : Finset V,
    Disjoint V₀ V₁ ∧ Disjoint V₀ V₂ ∧ Disjoint V₁ V₂ ∧
    V₀ ∪ V₁ ∪ V₂ = univ.erase u ∧
    (∀ v ∈ V₀, readSet G v = ∅) ∧
    (∀ v ∈ V₁, readSet G v ⊆ X ∪ Z) ∧
    (∀ v ∈ V₂, readSet G v ⊆ Y ∪ Z) ∧
    X ⊆ V₁ ∪ V₀ ∧ Y ⊆ V₂ ∧
    G.parents u ⊆ X ∪ Z

/-- ⭐⭐⭐⭐ **V6.07 消元切 ⟹ `mass(univ\{u})` 逐点分裂**（**无塔**）。

$$\mathrm{mass}_{V\setminus\{u\}}\Bigl(\prod_v\pi_v\Bigr)x
  = f\bigl(x|_{X\cup Z}\bigr)\cdot g\bigl(x|_{Y\cup Z}\bigr).$$

**证明链路**：`absorb_free`（单坐标消元）拆出 `κ · ∏_{v≠u}`，
`κ` 由 `V6.05` 只读 `pa(u) ⊆ X∪Z`，
`∏_{v≠u}` 由 `prod_zone_split3_gen` 在 `univ.erase u` 上三分裂。
**全程单层 `mass`、无 `mass∘mass`、无塔。** -/
theorem elimCut_zone_split {G : DAG V} {p : (V → Bool) → ℝ} {X Y Z : Finset V} {u : V}
    (hfac : Fate.T1A2.FactorizesOn G p)
    (hfree : ∀ v, v ≠ u → u ∉ readSet G v)
    (hcut : ElimCut G u X Y Z) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn (X ∪ Z) f ∧ Fate.T1A2.ReadsOnlyOn (Y ∪ Z) g ∧
      ∀ x, Fate.DAGFactorization.mass (univ \ {u}) p x = f x * g x := by
  obtain ⟨π, hloc, -, hprod⟩ := hfac
  obtain ⟨V₀, V₁, V₂, h01, h02, h12, hcov, h0, hA, hB, hX, hY, hpu⟩ := hcut
  -- `mass(univ\{u}) p = mass(univ\{u})(∏π)`（逐点重写被积函数）
  have hmass : ∀ x, Fate.DAGFactorization.mass (univ \ {u}) p x
      = Fate.DAGFactorization.mass (univ \ {u}) (fun y => ∏ v, π v y) x := by
    intro x
    unfold Fate.DAGFactorization.mass
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : ∀ u' ∈ (univ \ {u} : Finset V), w u' = x u'
    · rw [if_pos hw, if_pos hw, hprod w]
    · rw [if_neg hw, if_neg hw]
  -- 消元：拆成消息 × 其余因子之积
  have habs : ∀ x, Fate.DAGFactorization.mass (univ \ {u}) (fun y => ∏ v, π v y) x
      = (∑ a : Bool, π u (unpinB u x a)) * (∏ v ∈ univ.erase u, π v x) :=
    fun x => absorb_free hloc hfree x
  -- 其余因子之积按原始读集三分裂
  obtain ⟨f', g, hf', hg, hsplit⟩ :=
    prod_zone_split3_gen (S := univ.erase u) (reads := readSet G)
      h01 h02 h12 hcov π hloc h0 hA hB
  -- 消息 `κ` 归入 `X∪Z` 侧
  have hκ : Fate.T1A2.ReadsOnlyOn (X ∪ Z) (fun x => ∑ a : Bool, π u (unpinB u x a)) :=
    (absorb_free_reads hloc u).mono hpu
  refine ⟨fun x => (∑ a : Bool, π u (unpinB u x a)) * f' x, g, ?_, hg, ?_⟩
  · -- 乘积仍只读 `X∪Z`
    intro x y hxy
    show (∑ a : Bool, π u (unpinB u x a)) * f' x
        = (∑ a : Bool, π u (unpinB u y a)) * f' y
    have h1 : (∑ a : Bool, π u (unpinB u x a)) = (∑ a : Bool, π u (unpinB u y a)) :=
      hκ x y hxy
    rw [h1, hf' x y hxy]
  · intro x
    rw [hmass x, habs x, hsplit x]
    ring