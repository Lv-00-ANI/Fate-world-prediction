import FateWorld.FateV2.Predict.T43Abduction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! ===========================================================================
  `Fate/CfNecessity` —— **T4.3 反方向分析：`(M.sg u).2` 依赖 `u` 是不是必要的？**

  ## 0 问题

  `Fate/T43Abduction.lean` 证明了

  ```
  (∀ u, (M.sg u).2 = f)  ⟹  cfWithAbduction M x y x' y' = doLaw M x' y'
  ```

  （`abduction_eq_doLaw_of_sg_indep`）。本文件分析**反方向**：

  * 「`(M.sg u).2` 与 `u` 无关」是否**必要**？
  * `cfWithAbduction = doLaw` 的**充要条件**是什么？
  * 归一化 `Z` 究竟在何时「抹掉」`u` 的依赖？

  ## 1 结论速览（全部已在 Lean 中验证）

  | # | 结论 | 定理 |
  |---|---|---|
  | 1 | **反例存在**：`Φ = (M.sg ·).2` 依赖 `u`，但两律**逐格**相等 ⟹ 「无关」**不是**必要条件 | `M₃_cf_eq_doLaw` / `converse_fails` |
  | 2 | **充要条件**：两律相等 ⟺ `p̄` 与 `pU` 在**每个 `x'`-坐标事件**上质量相同 | `cf_eq_doLaw_iff` |
  | 3 | **最强充分条件**：`p̄` 与 `pU` 在 `Φ` 的**每个纤维**上质量相同 | `cf_eq_doLaw_of_fiber_mass` |
  | 4 | **`Z` 的真实作用**：`Z` **不**依赖 `(x',y')`，故它**不会**单独抹掉 `u`-依赖；真正抹掉它的情形是 `S = univ`（⟹ `Z = 1`、`p̄ = pU`） | `cf_eq_doLaw_of_obsSet_univ` |
  | 5 | 原文前提是 #3 的**特例**（`Φ` 常值 ⟹ 纤维平凡） | `fiber_mass_of_const` |

  ## 2 记号（贯穿全文）

  * `S := obsSet M x y`（证据截面），`Z := postZ M x y = ∑_{u∈S} pU u`；
  * `Φ u := (M.sg u).2 : X → Y`（**结构方程本身**，取值于函数空间 `X → Y`）；
  * `p̄ u := pU u · [u∈S] / Z`（**归一化后验**，`∑ p̄ = 1`）；
  * `c_u := [Φ u x' = y']`。

  则**逐字**地

  ```
  cfWithAbduction M x y x' y' = ∑ u, p̄ u · c_u     （p̄ 下的期望）
  doLaw M x' y'               = ∑ u, pU u · c_u     （pU 下的期望）
  ```

  ⟹ **「两条律相等」= 「同一个函数 `c` 在两个测度下期望相同」**。
  `c` 只通过 `Φ` 依赖 `u`。**这就是全部机制。**

  ## 3 ⚠ 一处对原文件表述的**修正**

  `T43Abduction.lean` 文件头 §2 写：

  > 「归一化的代价，就是**溯因的信息全部被 `Z` 除掉**」

  **这个诊断不准确**，本文件给出更精确的替代（§3 节）。真正的机制是
  **`c_u` 与 `u` 无关**（即 `Φ u x'` 不随 `u` 变），**不是** `Z` 做了除法。
  `/ Z` 起的唯一作用是**把 `pU·[u∈S]` 归一化成概率**，从而让两个期望可比。
=========================================================================== -/

namespace FateV2.Error

namespace CfNecessity

open FateV2.Modeling.PearlHierarchy FateV2.Modeling.SCMSemantics Finset

-- ⚠ `obsSet` / `postZ` / `cfWithAbduction` 定义在 `T43` 命名空间内。
open FateV2.Predict.T43

/-! ## §1 两个**测度**的显式形式

把两条律统一写成「对某个 `u`-权重求期望」。这一步是纯定义展开，
但它把 §2–§4 的全部论证变成**测度比较**。 -/

section Measures

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- 证据指示函数 `[u ∈ S]`（作为 `0/1` 实数）。 -/
noncomputable def evInd (M : SCM X Y) (x : X) (y : Y) (u : M.U) : ℝ :=
  if u ∈ obsSet M x y then 1 else 0

/-- ⭐⭐ **归一化后验** `p̄ u = pU u · [u∈S] / Z`。 -/
noncomputable def post (M : SCM X Y) (x : X) (y : Y) (u : M.U) : ℝ :=
  M.pU u * evInd M x y u / postZ M x y

/-- ⭐⭐⭐ **`cfWithAbduction` = `p̄` 下对 `c_u = [Φ u x' = y']` 的期望**。 -/
theorem cfWithAbduction_eq_sum_post (M : SCM X Y) (x : X) (y : Y) (x' : X) (y' : Y) :
    cfWithAbduction M x y x' y'
      = ∑ u : M.U, post M x y u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0) := by
  rw [cfWithAbduction_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  by_cases h : u ∈ obsSet M x y
  · rw [post, evInd, if_pos h]
    have hmem := (mem_obsSet M x y u).1 h
    rw [if_pos hmem]
  · rw [post, evInd, if_neg h]
    have hmem : ¬ ((M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y) :=
      fun hh => h ((mem_obsSet M x y u).2 hh)
    rw [if_neg hmem]

/-- ⭐ **`doLaw` = `pU` 下对同一 `c_u` 的期望**（定义即此）。 -/
theorem doLaw_eq_sum_pU (M : SCM X Y) (x' : X) (y' : Y) :
    doLaw M x' y' = ∑ u : M.U, M.pU u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0) := rfl

/-- ⭐⭐ **后验总质量 = 1**（`p̄` 确实是概率测度）。 -/
theorem post_total (M : SCM X Y) (x : X) (y : Y)
    (hZ : postZ M x y = ∑ u ∈ obsSet M x y, M.pU u)
    (hne : (obsSet M x y).Nonempty) (hpos : ∀ u, 0 < M.pU u) :
    (∑ u : M.U, post M x y u) = 1 := by
  have hZpos : 0 < ∑ u ∈ obsSet M x y, M.pU u := by
    rw [← hZ]; exact postZ_pos M x y hpos hne
  have hZne : postZ M x y ≠ 0 := by rw [hZ]; exact ne_of_gt hZpos
  have hpt : ∀ u : M.U, post M x y u
      = if u ∈ obsSet M x y then M.pU u / postZ M x y else 0 := by
    intro u
    by_cases h : u ∈ obsSet M x y
    · rw [post, evInd, if_pos h, if_pos h, mul_one]
    · rw [post, evInd, if_neg h, if_neg h, mul_zero, zero_div]
  calc ∑ u : M.U, post M x y u
      = ∑ u : M.U, (if u ∈ obsSet M x y then M.pU u / postZ M x y else 0) :=
        Finset.sum_congr rfl (fun u _ => hpt u)
    _ = ∑ u ∈ obsSet M x y, M.pU u / postZ M x y := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = (∑ u ∈ obsSet M x y, M.pU u) / postZ M x y := (Finset.sum_div ..).symm
    _ = 1 := by rw [← hZ]; exact div_self hZne

end Measures

/-! ## §2 ⭐⭐⭐⭐⭐ 反例：`Φ` 依赖 `u`，但两律仍逐格相等

**构造**（`X = Y = U = Bool`，`pU ≡ 1/2`，`X := false` 恒定）：

| `u` | `Φ u = (M.sg u).2` | `Φ u false` | `Φ u true` |
|---|---|---|---|
| `false` | `id` | `false` | **`true`** |
| `true`  | `const false` | `false` | **`false`** |

**关键的两点**：

1. **`Φ` 确实依赖 `u`** —— `Φ false ≠ Φ true`（`M₃_phi_depends_on_u`）；
   故原文定理的**前提不成立**。
2. 但 `Φ u false = false` **对一切 `u`**，故证据 `(X,Y) = (false,false)`
   与**所有** `u` 相容 ⟹ `S = univ` ⟹ `Z = 1` ⟹ `p̄ = pU`。

⟹ 于是两律**逐格**相等，**且不依赖 `Φ` 的任何性质**。 -/

section ConcreteCounterexample

/-- ⭐⭐⭐⭐ **反例 SCM `M₃`**：`X := false`（与 `u` 无关），
`Y := if u = false then id else const false`（**与 `u` 有关**）。 -/
noncomputable def M₃ : SCM Bool Bool where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1 / 2
  sg := fun u => (false, if u = false then id else fun _ => false)

theorem M₃_sg_fst (u : Bool) : (M₃.sg u).1 = false := rfl

theorem M₃_sg_snd_false : (M₃.sg false).2 = (id : Bool → Bool) := rfl

theorem M₃_sg_snd_true : (M₃.sg true).2 = (fun _ => false) := rfl

/-- 两者在 `false` 处相同（`S = univ` 的根源）。 -/
theorem M₃_apply_false (u : Bool) : (M₃.sg u).2 false = false := by
  cases u <;> rfl

theorem M₃_pU (u : Bool) : M₃.pU u = 1 / 2 := rfl

/-- ⭐⭐⭐⭐ **`Φ` 真的依赖 `u`**：不存在共同的 `f` 使 `∀ u, Φ u = f`。

**⟹ 原文 `abduction_eq_doLaw_of_sg_indep` 的前提在 `M₃` 上失败。** -/
theorem M₃_phi_depends_on_u : ¬ ∃ f : Bool → Bool, ∀ u : M₃.U, (M₃.sg u).2 = f := by
  rintro ⟨f, hf⟩
  have h1 : (id : Bool → Bool) = f := by rw [← M₃_sg_snd_false]; exact hf false
  have h2 : (fun _ => false) = f := by rw [← M₃_sg_snd_true]; exact hf true
  have hid : (id : Bool → Bool) = (fun _ => false) := by rw [h1, h2]
  have := congrFun hid true
  simp at this

/-- ⭐⭐⭐ **`S = univ`**：证据 `(false, false)` 过滤不掉**任何** `u`。 -/
theorem M₃_obsSet_univ : obsSet M₃ false false = (univ : Finset M₃.U) := by
  ext u
  rw [mem_obsSet]
  simp only [Finset.mem_univ, iff_true]
  exact ⟨M₃_sg_fst u, (M₃_sg_fst u) ▸ M₃_apply_false u⟩

theorem M₃_pU_sum : (∑ u : M₃.U, M₃.pU u) = 1 := by
  rw [show (∑ u : M₃.U, M₃.pU u) = (∑ u : Bool, (1:ℝ)/2) from by
    refine Finset.sum_congr rfl ?_; intro u _; exact M₃_pU u]
  rw [Fintype.sum_bool]; norm_num

/-- ⭐ **`Z = 1`**（后验 = 先验）。 -/
theorem M₃_postZ : postZ M₃ false false = 1 := by
  rw [postZ, obsEventMass_eq_sum_obsSet, M₃_obsSet_univ, M₃_pU_sum]

/-- ⭐⭐⭐⭐⭐ **反例主定理**：`Φ` 依赖 `u`，但 `cfWithAbduction = doLaw` **逐格**。 -/
theorem M₃_cf_eq_doLaw (x' y' : Bool) :
    cfWithAbduction M₃ false false x' y' = doLaw M₃ x' y' := by
  have hZ : postZ M₃ false false = 1 := M₃_postZ
  rw [cfWithAbduction_eq_sum, doLaw]
  refine Finset.sum_congr rfl ?_
  intro u _
  have hmem : ((M₃.sg u).1 = false ∧ (M₃.sg u).2 (M₃.sg u).1 = false) := by
    have : u ∈ obsSet M₃ false false := by rw [M₃_obsSet_univ]; exact Finset.mem_univ u
    exact (mem_obsSet M₃ false false u).1 this
  rw [hZ, if_pos hmem, mul_one, div_one]

/-- ⭐⭐⭐⭐⭐ **「依赖 `u` 不是必要条件」的完整陈述**：

**存在**一个 SCM，使

* 「`Φ` 与 `u` 无关」**不成立**（左边），**且**
* `cfWithAbduction = doLaw` 对**一切** `x' y'` 成立（右边）。 -/
theorem converse_fails :
    (¬ ∃ f : Bool → Bool, ∀ u : M₃.U, (M₃.sg u).2 = f) ∧
    (∀ (x' y' : Bool), cfWithAbduction M₃ false false x' y' = doLaw M₃ x' y') :=
  ⟨M₃_phi_depends_on_u, M₃_cf_eq_doLaw⟩

/-- 推论：在 `M₃` 上**没有**任何一格能区分两条律。 -/
theorem M₃_no_diff : ¬ ∃ (x' y' : Bool),
    cfWithAbduction M₃ false false x' y' ≠ cfNoAbduction M₃ x' y' := by
  rintro ⟨x', y', hne⟩
  exact hne (M₃_cf_eq_doLaw x' y')

end ConcreteCounterexample

/-! ## §3 ⭐⭐⭐ `Z` 究竟做了什么（对原文件措辞的修正）

### 3.1 `Z` **不**依赖 `(x', y')`

`postZ M x y` 只依赖**证据** `(x, y)`。所以 `/ Z` 对 `(x', y')` 是**同一个常数因子**。

⟹ `/ Z` **不可能**「把某个 `x'` 相关的量变成 `x'` 无关」。
它唯一的作用是：**把 `pU · [u∈S]` 的总质量从 `Z` 归一化成 `1`。**

### 3.2 真正的「抹掉 `u`-依赖」只有四种情形

| # | 情形 | 机制 | 定理 |
|---|---|---|---|
| (a) | `S = univ` | `Z = 1` 且 `p̄ = pU` **逐点** ⟹ 两律**恒等**，**与 `Φ` 无关** | `cf_eq_doLaw_of_obsSet_univ` |
| (b) | `S = ∅` | `Z = 0`（Lean 中 `cfWithAbduction` 的语义已不适用）⟹ 这是**退化**而非「抹掉」 | — |
| (c) | `p̄` 与 `pU` 在 `Φ` 的每个纤维上质量相同 | 见 §4 的充分条件 | `cf_eq_doLaw_of_fiber_mass` |
| (d) | `Φ` 常值（原文前提） | `Φ` 只有一个非空纤维 = `univ`，质量为 `1 = 1` | `fiber_mass_of_const` |

**⟹ 关键判读**：

* (a) 是**最常见**的「反例来源」：**证据弱到与一切 `u` 相容**时，
  溯因**什么也没更新**，两条律必然相同 —— **哪怕 `Φ` 依赖 `u`**。
* (d) 是原文条件，比 (a) **更强**（(d) ⟹ (a) 只在 `S` 覆盖全空间时等价）。
  原文证明用的是 (d)，而 (a) 与 (c) 都**严格更弱**、仍然充分。 -/

section ZAnalysis

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- ⭐⭐⭐⭐ **情形 (a) — 一般定理**：`S = univ` ⟹ 两律逐格相等，
**对 `Φ = (M.sg ·).2` 不作任何假设**。

⟹ 这正是 §2 的 `M₃` 的抽象化，也证明「`Φ` 与 `u` 无关」**不是**必要条件。 -/
theorem cf_eq_doLaw_of_obsSet_univ (M : SCM X Y) (x : X) (y : Y)
    (hS : obsSet M x y = (univ : Finset M.U))
    (hpU : ∑ u : M.U, M.pU u = 1) :
    ∀ x' y', cfWithAbduction M x y x' y' = doLaw M x' y' := by
  intro x' y'
  have hZ : postZ M x y = 1 := by
    rw [postZ, obsEventMass_eq_sum_obsSet, hS, hpU]
  rw [cfWithAbduction_eq_sum, doLaw]
  refine Finset.sum_congr rfl ?_
  intro u _
  have hmem : ((M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y) := by
    have : u ∈ obsSet M x y := by rw [hS]; exact Finset.mem_univ u
    exact (mem_obsSet M x y u).1 this
  rw [hZ, if_pos hmem, mul_one, div_one]

end ZAnalysis

/-! ## §4 ⭐⭐⭐⭐⭐ 充要条件与最强充分条件

### 4.1 充要条件（字面重述，但把 `u`-依赖定位到 `Φ` 的坐标边缘）

两律逐格相等 ⟺ 对每个 `(x', y')`，`p̄` 与 `pU` 在同一事件上给同一质量：
`∑_u p̄ u·[Φ u x' = y'] = ∑_u pU u·[Φ u x' = y']`。

即：**对每个 `x'`，`(u ↦ Φ u x')` 在 `p̄` 与 `pU` 下的推前律相同。**

### 4.2 最强充分条件（本文件主结果）

若 `p̄` 与 `pU` 在 `Φ : U → (X → Y)` 的**每个纤维**上质量相同，则两律**恒等**。

**证明机制**：`c_u = [Φ u x' = y']` 在每个纤维上**是常数**，
于是「纤维质量相等」⟹「加权和相等」。**`Φ` 的取值可以任意依赖 `u`**，
只要**纤维内的总质量**与先验一致。 -/

section Characterisation

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- ⭐⭐⭐⭐⭐ **`cf_eq_doLaw_of_fiber_mass`（最强充分条件）**：

若 `p̄` 与 `pU` 在 `Φ = (M.sg ·).2` 的**每个纤维**上质量相等，则两律逐格相等。

**⚠⚠ 注意它**不要求** `Φ` 与 `u` 无关**：
`Φ` 可以取 `|X→Y|` 个不同值，本定理照样成立。 -/
theorem cf_eq_doLaw_of_fiber_mass (M : SCM X Y) (x : X) (y : Y)
    (hfib : ∀ g : X → Y, (∑ u ∈ univ.filter (fun u => (M.sg u).2 = g), post M x y u)
                        = (∑ u ∈ univ.filter (fun u => (M.sg u).2 = g), M.pU u)) :
    ∀ x' y', cfWithAbduction M x y x' y' = doLaw M x' y' := by
  intro x' y'
  rw [cfWithAbduction_eq_sum_post, doLaw_eq_sum_pU]
  rw [← Finset.sum_fiberwise (s := (univ : Finset M.U)) (g := fun u => (M.sg u).2)
        (f := fun u => post M x y u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0))]
  rw [← Finset.sum_fiberwise (s := (univ : Finset M.U)) (g := fun u => (M.sg u).2)
        (f := fun u => M.pU u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0))]
  refine Finset.sum_congr rfl ?_
  intro g _
  have h1 : ∀ u ∈ univ.filter (fun u : M.U => (M.sg u).2 = g),
      post M x y u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0)
      = post M x y u * (if g x' = y' then (1:ℝ) else 0) := by
    intro u hu; rw [(Finset.mem_filter.1 hu).2]
  have h2 : ∀ u ∈ univ.filter (fun u : M.U => (M.sg u).2 = g),
      M.pU u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0)
      = M.pU u * (if g x' = y' then (1:ℝ) else 0) := by
    intro u hu; rw [(Finset.mem_filter.1 hu).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  have e1 : (∑ u ∈ univ.filter (fun u : M.U => (M.sg u).2 = g),
      post M x y u * (if g x' = y' then (1:ℝ) else 0))
      = (∑ u ∈ univ.filter (fun u : M.U => (M.sg u).2 = g), post M x y u)
        * (if g x' = y' then (1:ℝ) else 0) := (Finset.sum_mul ..).symm
  have e2 : (∑ u ∈ univ.filter (fun u : M.U => (M.sg u).2 = g),
      M.pU u * (if g x' = y' then (1:ℝ) else 0))
      = (∑ u ∈ univ.filter (fun u : M.U => (M.sg u).2 = g), M.pU u)
        * (if g x' = y' then (1:ℝ) else 0) := (Finset.sum_mul ..).symm
  rw [e1, e2, hfib g]

/-- ⭐⭐⭐⭐ **充要条件（`iff` 形式）**：两律逐格相等 ⟺ 逐事件质量相等。

**⚠ 这是字面上的重述**（§1 的两个定义直接给出），但它把「何时退化」
精确地变成**两个测度在同一族事件上的比较**，是 §4.2 的出发点。 -/
theorem cf_eq_doLaw_iff (M : SCM X Y) (x : X) (y : Y) :
    (∀ x' y', cfWithAbduction M x y x' y' = doLaw M x' y')
      ↔ ∀ x' y', (∑ u : M.U, post M x y u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0))
                = (∑ u : M.U, M.pU u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0)) := by
  constructor
  · intro h x' y'
    rw [← cfWithAbduction_eq_sum_post, ← doLaw_eq_sum_pU]
    exact h x' y'
  · intro h x' y'
    rw [cfWithAbduction_eq_sum_post, doLaw_eq_sum_pU]
    exact h x' y'

/-- ⭐⭐⭐ **原文前提 ⟹ §4.2 的纤维质量条件**：
`Φ` 常值 `= f` 时纤维平凡（`f` 的纤维 = `univ`，其余为空），
质量为 `1 = 1`（需 `∑pU = 1` 与 `∑p̄ = 1`）。

**⟹ 原文 `abduction_eq_doLaw_of_sg_indep` 是 `cf_eq_doLaw_of_fiber_mass` 的特例，
而不是它的等价刻画。** -/
theorem fiber_mass_of_const (M : SCM X Y) (x : X) (y : Y) (f : X → Y)
    (hsg : ∀ u, (M.sg u).2 = f)
    (hZ : postZ M x y = ∑ u ∈ obsSet M x y, M.pU u)
    (hne : (obsSet M x y).Nonempty) (hpos : ∀ u, 0 < M.pU u)
    (hpU : ∑ u : M.U, M.pU u = 1) :
    ∀ g : X → Y, (∑ u ∈ univ.filter (fun u => (M.sg u).2 = g), post M x y u)
                = (∑ u ∈ univ.filter (fun u => (M.sg u).2 = g), M.pU u) := by
  intro g
  have hpow : ∀ u : M.U, ((M.sg u).2 = g) ↔ (g = f) := by
    intro u; rw [hsg u]; exact ⟨fun h => h.symm, fun h => h.symm⟩
  by_cases hg : g = f
  · have hfil : univ.filter (fun u : M.U => (M.sg u).2 = g) = (univ : Finset M.U) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact (hpow u).2 hg
    rw [hfil, post_total M x y hZ hne hpos, hpU]
  · have hfil : univ.filter (fun u : M.U => (M.sg u).2 = g) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro u _ h
      exact hg ((hpow u).1 h)
    rw [hfil]; simp

/-! ## §5 ⭐⭐⭐⭐ **真正的 `≠` 反例**：`X := u` 且 `Φ` 依赖 `u`

`T43Abduction.lean` 文件头 §2 声称「归一化口径下**不可能**构造 `≠` 反例」。
**本节的 `M₄` 直接否证这一断言。**

**构造**（`X = Y = U = Bool`，`pU ≡ 1/2`）：

| `u` | `(M.sg u).1` | `Φ u = (M.sg u).2` | `Φ u true` |
|---|---|---|---|
| `false` | `false` | `id` | `true` |
| `true`  | `true`  | `const false` | `false` |

证据 `(X,Y) = (false,false)` ⟹ `S = {false}`（**`X := u` 使证据筛选 `u`**），
`Z = 1/2`，故 `p̄ = δ_{false}`。

* `cfWithAbduction M₄ (0,0) (1,1) = [Φ false 1 = 1] = 1`
* `doLaw M₄ (1,1) = (1/2)·1 + (1/2)·0 = 1/2`

⟹ **两律不同。** -/

section DistinctCounterexample

/-- ⭐⭐⭐⭐ **`M₄`**：`X := u`（证据筛选 `u`），`Φ` 依赖 `u`。 -/
noncomputable def M₄ : SCM Bool Bool where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1 / 2
  sg := fun u => (u, if u = false then id else fun _ => false)

theorem M₄_sg (u : Bool) : M₄.sg u = (u, if u = false then id else fun _ => false) := rfl

theorem M₄_fst (u : Bool) : (M₄.sg u).1 = u := by rw [M₄_sg]

theorem M₄_snd (u : Bool) :
    (M₄.sg u).2 = (if u = false then (id : Bool → Bool) else fun _ => false) := by rw [M₄_sg]

theorem M₄_pU (u : Bool) : M₄.pU u = 1 / 2 := rfl

theorem M₄_phi_dep : ¬ ∃ f : Bool → Bool, ∀ u : M₄.U, (M₄.sg u).2 = f := by
  rintro ⟨f, hf⟩
  have h1 : (id : Bool → Bool) = f := by
    have := hf false; rwa [M₄_snd, if_pos rfl] at this
  have h2 : (fun _ => false) = f := by
    have := hf true; rwa [M₄_snd, if_neg (by decide : ¬ (true = false))] at this
  have hid : (id : Bool → Bool) = (fun _ => false) := by rw [h1, h2]
  have := congrFun hid true
  simp at this

/-- ⭐ **`S = {false}`**：证据 `(0,0)` 唯一确定 `u = false`。 -/
theorem M₄_obsSet : obsSet M₄ false false = {false} := by
  ext u
  rw [mem_obsSet]
  constructor
  · intro hh
    have h1 : u = false := by rw [← M₄_fst u]; exact hh.1
    rw [h1]; exact Finset.mem_singleton_self false
  · intro hh
    have h1 : u = false := Finset.mem_singleton.1 hh
    subst h1
    exact ⟨M₄_fst false, by rw [M₄_fst, M₄_snd, if_pos rfl]; rfl⟩

theorem M₄_sum_single (f : M₄.U → ℝ) :
    (∑ u ∈ ({false} : Finset M₄.U), f u) = f false :=
  @Finset.sum_singleton M₄.U ℝ _ f (false : M₄.U)

/-- **`Z = 1/2`**。 -/
theorem M₄_postZ : postZ M₄ false false = 1 / 2 := by
  rw [postZ, obsEventMass_eq_sum_obsSet, M₄_obsSet, M₄_sum_single, M₄_pU]

/-- ⭐ **`doLaw M₄ true true = 1/2`**（`X` 与 `Φ` 独立地依赖 `u`）。 -/
theorem M₄_doLaw_true_true : doLaw M₄ true true = 1 / 2 := by
  rw [doLaw]
  rw [show (∑ u : M₄.U, M₄.pU u * (if (M₄.sg u).2 true = true then (1:ℝ) else 0))
        = (∑ u : Bool, (1/2:ℝ) * (if (M₄.sg u).2 true = true then (1:ℝ) else 0)) from by
    refine Finset.sum_congr rfl ?_; intro u _; rfl]
  rw [Fintype.sum_bool, M₄_snd, M₄_snd,
      if_pos rfl, if_neg (by decide : ¬ (true = false))]
  norm_num

/-- ⭐ **`cfWithAbduction M₄ (0,0) (1,1) = 1`**（后验是点质量于 `u = false`）。 -/
theorem M₄_cf_true_true : cfWithAbduction M₄ false false true true = 1 := by
  rw [cfWithAbduction_eq_obsSet, M₄_obsSet, M₄_sum_single, M₄_postZ, M₄_pU, M₄_snd,
      if_pos rfl]
  norm_num

/-- ⭐⭐⭐⭐⭐ **`cfWithAbduction ≠ doLaw`**（`1 ≠ 1/2`）。 -/
theorem M₄_diff : cfWithAbduction M₄ false false true true ≠ doLaw M₄ true true := by
  rw [M₄_cf_true_true, M₄_doLaw_true_true]; norm_num

/-- ⭐⭐⭐⭐⭐ **否定 `T43Abduction.lean` 文件头「不可能构造 `≠`」的断言**。 -/
theorem M₄_diff_exists : ∃ (x' y' : Bool),
    cfWithAbduction M₄ false false x' y' ≠ cfNoAbduction M₄ x' y' :=
  ⟨true, true, M₄_diff⟩

end DistinctCounterexample

end Characterisation

/-! ## §5 ⚠ 诚实边界

1. **§4.1 的 `iff` 是字面重述**（`D4` 型），**不**冒充定理：它的价值在于
   把退化问题**翻译**成测度比较，从而给出 §4.2、§3.2 这些**严格更弱**的充分条件。

2. **§4.2 是充要条件吗？不是。** 它是一个**充分条件**，
   而且**比原文条件严格更弱**（原文条件 ⟹ 纤维平凡 ⟹ §4.2 成立；反向不成立，
   例如 §2 的 `M₃`：纤维为两单点，`p̄ = pU` 使条件成立）。
   **真正的充要条件**是 §4.1 的逐事件质量相等 —— 那已经是
   「两条律相等」的另一种写法，**没有更"结构化"的充要刻画**：
   因为等号成立依赖于 `pU` 的**数值巧合**（见注 3）。

3. **为什么没有更结构化的充要条件**：取 `X = Y = Bool`，`pU` 为任意分布，
   `Φ` 的纤维为 `{u₀}` 与 `U∖{u₀}`。只要 `pU u₀ = p̄ u₀`（一个**实数等式**），
   两律就相等；否则不等。**这是关于 `pU` 数值的条件，不是关于 `SCM` 结构的条件。**
   ⟹ 「`cfWithAbduction = doLaw`」在 `SCM` 空间里**不是**结构性质。

4. **本文件没有做**：`S = ∅`（`Z = 0`）时的语义讨论。
   在 `Lean` 的 `ℝ` 除法下 `x / 0 = 0`，故 `cfWithAbduction` 退化为 `0`，
   这不是「概率」，需要另设口径。本文件将其登记为 §3.2 情形 (b)，**不展开**。
-/

end CfNecessity

end FateV2.Error
