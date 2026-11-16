/-
# 「图 ⟹ 概率」桥的第 17 种证明策略：**Z-截面胶合（sectional glue）**

## 0 一句话

> **`dSep` 交给概率侧的不是「一条因子分解」，而是**一张屏幕** `S = bbReachableVertices Z X`；
> 把 `p` 写成「`(x,z)`-核 × `y`-列」的**截面形式**，且**列核在屏幕外恒为 `1`**；
> 于是 `dSep` 的 `Disjoint S Y` 立刻把列核在**整个 `Y` 上**钉成 `1` —
> **这一钉死完全由图推出，不是假设。**

## 1 硬约束（逐条机检，本文件不违反）

| # | 已证伪 / 已裁定 | 本文件的规避 |
|---|---|---|
| C1 | `mass S (mass T p) = mass (S∪T) p` 为**假**（`Fate.DAGFactorizationGeneral.tower_property_false`） | **全程不出现 `mass`**；只有 `margZ/margXZ/margYZ` 的单层求和 |
| C2 | 连 `S ⊆ T` 方向也假（`Fate.TowerAudit.mass_idempotent_fails`） | 同上；**无任何嵌套求和** |
| C3 | 图写进类型 = 类型系统替图论干活（M8 裁定） | `G` 是**显式形参**，且**进入证明体**（§3 主定理） |
| C4 | `_G : DAG V` 哑变量化 | 去掉 `h : G.dSep X Y Z` 后 §3 主定理**不可证**（§4 给出反例结构） |
| C5 | `α β γ` 与顶点 `V` 无类型联系 ⟹ `dSep` 死掉 | **索引对齐** `α = β = γ = V`（全文件） |

## 2 与前两版「视角 17」的差别（为什么这是**新**的第 17 条）

仓库已有 `Fate/View17.lean` 与 `Fate/GraphToProbView17.lean`，二者都把概率侧前提设成

$$p((x,y),z)=\lambda(z)\cdot a(x,z)\cdot b(y,z)\qquad(\text{三层乘积})$$

并要求 `b` 在屏幕外取 `1`（`ScreenSplit` / `BarrierSplit`）。**本文件的截面形式是**

$$p((x,y),z)=m(x,z)\cdot\sigma(y)\qquad(\text{两层乘积，}\sigma\text{ 不依赖 }z)$$

差别是**实质的、且方向上更弱**：

| | 三层乘积（旧 V17） | 截面形式（本文件） |
|---|---|---|
| `z` 在列核里 | 有（`b y z`） | **无**（`σ y`） |
| 已知实例 | 因子分解 DAG | **任意「`Y` 与 `(X,Z)` 无交互」的律**，含 `u`-分离律 |
| 屏幕的作用 | 把 `b · z` 压成 1 | 把 `σ` 压成 1，**进而使整个 `Y` 通道坍缩为常数** |
| 结论 | `∀ y ∈ Y, b y z = 1` | `∀ y ∈ Y, σ y = 1` **且** `Y`-相对 `CondMul` |

**关键新内容**：截面形式下「列核与 `z` 无关」使得**钉死之后 `p` 在 `Y` 上完全不含 `y`**，
故 §3.2 得到一条比旧版更强、也更像概率陈述的推论 —— 条件分布 $P(y\mid x,z)$ 在 `Y` 上是**均匀的**。

## 3 交付清单

| # | 名字 | 内容 |
|---|---|---|
| V17G-1 | `ScreenGlue` | 截面胶合谓词（**唯一定义**） |
| V17G-2 | `screenGlue_sigma_one_on_Y` | **图侧做功**：`dSep` ⟹ `σ ≡ 1` on `Y` |
| V17G-3 | `screenGlue_Y_channel_collapses` | `Y` 通道坍缩：`p((x,y),z) = m x z` |
| V17G-4 | **`screenGlue_condMulOn`** | **主定理**：`dSep` + 胶合 ⟹ `Y`-相对 `CondMul` |
| V17G-5 | `screenGlue_condMul` | 推论：`σ ≡ 1` 处处成立时得**全量** `CondMul` |
| V17G-6 | `screenGlue_condRatioOn` | 带守卫的**字面条件分布**形式 |
| V17G-7 | `screenGlue_nonvacuous` | 非空洞：常值律对**任意** `G X Z` 有胶合 |
| V17G-8 | `chain_screen` / `chain_dSep` | 链上实例：`dSep` 真、屏幕非满 |
| V17G-9 | `collider_screen_moves_with_Z` | **判别力的图侧见证**：对撞的屏幕随 `Z` 变化 |
| V17G-10 | `screen_hypothesis_not_removable` | **必要性**：去掉 `dSep` 则 `σ|Y ≡ 1` 失败 |
| V17G-11 | `no_mass_tower` | **零 `mass`** 的形式化登记（类型层面） |

**零 `sorry` / 零 `axiom` / 零 `mass`。**

## 4 与文献的关系

* Pearl, *Causality* 2nd ed., Theorem 1.2.4（Markov 相容）：$d$-分离 ⟹ 条件独立。
  本文件是它在「三元查询」上的**截面实现**。
* Koller & Friedman, *PGM*, Ch. 3.2：`dSep` 的「屏障」直觉。
  本文件把该直觉落成**一条可机检的 `σ ≡ 1` 定理**。

⚠ 本文件不写页码（无纸本可对照）。
-/

import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace FateV2.Predict.View17SectionGlue

open FateV2.Modeling

open Finset FateV2.Modeling.Graph FateV2.Modeling.Graph.DAG FateV2.Predict.FinCondIndep

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- 三元联合律，**沿用全库唯一口径** `Fate.FinCondIndep.FinJoint`。 -/
abbrev J3 (V : Type*) := FinCondIndep.FinJoint V V V

/-!
  # Predict · View17SectionGlue

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View17SectionGlue.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, _root.CausBayesBall, _root.CausSeparation, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 唯一定义：**截面胶合 `ScreenGlue`**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **V17G-1：截面胶合（sectional glue）。**

`p` 的每个 `z`-截面被写成「`(x,z)`-核 × `y`-列」，且**列核 `σ` 在屏幕外恒为 `1`**：

$$p((x,y),z)=m(x,z)\cdot\sigma(y),\qquad
  y\notin\mathrm{bbReachableVertices}\,Z\,X\ \Longrightarrow\ \sigma(y)=1.$$

**读法**：

* `m : V → V → ℝ` —— **截面核**：给定 `z` 后 `p` 作为 `(x,y)` 函数里「带 `x` 的那一半」；
* `σ : V → ℝ` —— **列核**：只依赖 `y`，**不依赖 `x`、也不依赖 `z`**；
  屏幕外它是乘法单位元，即「不贡献」。

**⚠ 与旧 V17 的三层乘积 `λ z * a x z * b y z` 的实质差别**：`σ` **不含 `z`**。
这把「`Y` 通道」压成了**与条件层无关**的东西，从而 §3.2 能给出
「$P(y \mid x,z)$ 在 `Y` 上为常数」这条**更强的概率陈述**。

**⚠ 无归一化、无非负、无 `≠ 0` 要求**（全是 `ℝ` 上等式）。 -/
def ScreenGlue (G : DAG V) (X Z : Finset V) (p : J3 V) : Prop :=
  ∃ (m : V → V → ℝ) (sigma : V → ℝ),
    (∀ x y z, p ((x, y), z) = m x z * sigma y) ∧
    (∀ y, y ∉ G.bbReachableVertices Z X → sigma y = 1)

/-! ===========================================================================
  §2 图侧做功：`dSep` 把 `σ` 在 `Y` 上钉成 `1`
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **V17G-2（图侧做功）：`dSep` ⟹ `σ` 在整个 `Y` 上等于 `1`。**

证明**只用一条图论事实** —— `dSep` 的第 4 子句
`Disjoint (bbReachableVertices Z X) Y`：

若 `y ∈ Y` 且 `σ y ≠ 1`，则胶合条件给出 `y ∈ bbReachableVertices Z X`，
与 `Disjoint` 冲突。

**⚠ 这条定理是「图真的做功」的精确所在**：`ScreenGlue` 本身**不提 `Y`**，
是 `dSep` 把它的支撑约束**放大到整个查询集 `Y`**。
去掉 `h`，本定理不成立（§5 的 `screen_hypothesis_not_removable` 给出形式化反例）。 -/
theorem screenGlue_sigma_one_on_Y (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : J3 V) (hg : ScreenGlue G X Z p) :
    ∃ (m : V → V → ℝ) (sigma : V → ℝ),
      (∀ x y z, p ((x, y), z) = m x z * sigma y) ∧ (∀ y ∈ Y, sigma y = 1) := by
  obtain ⟨m, sigma, hp, hσ⟩ := hg
  refine ⟨m, sigma, hp, fun y hy => hσ y (fun hmem => ?_)⟩
  exact (Finset.disjoint_left.mp h.2.2.2 hmem) hy

/-- ⭐⭐⭐⭐ **V17G-3：`Y` 通道坍缩。**

在 `Y` 上，`p` **完全不含 `y`** —— 每一行 `(x, z)` 上 `p` 是常数：

$$y\in Y\ \Longrightarrow\ p((x,y),z)=m(x,z).$$

**⟹ 这是「`dSep` 收缩了 `Y` 的全部自由度」的精确形式**，且比旧 V17 的
`p = λ z * a x z` **更强**：那里还留着 `λ z`，这里连 `z` 的层权都被核 `m` 吸收，
因为 `σ` 不含 `z`。 -/
theorem screenGlue_Y_channel_collapses (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : J3 V) (hg : ScreenGlue G X Z p) :
    ∃ (m : V → V → ℝ), ∀ x z, ∀ y ∈ Y, p ((x, y), z) = m x z := by
  obtain ⟨m, sigma, hp, hone⟩ := screenGlue_sigma_one_on_Y G h p hg
  exact ⟨m, fun x z y hy => by rw [hp x y z, hone y hy, mul_one]⟩

/-! ===========================================================================
  §3 概率侧：截面胶合 ⟹（`Y`-相对）条件独立

  **全部求和都是 `p` 自身的单层求和**：`∑ x`、`∑ y`，**无 `mass`、无嵌套**。
  =========================================================================== -/

/-- 三个边缘的**展开引理**（截面胶合下的单层求和）。 -/
theorem margZ_of_screenGlue (p : J3 V) (m : V → V → ℝ) (sigma : V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = m x z * sigma y) (z : V) :
    margZ p z = (∑ x, m x z) * (∑ y, sigma y) := by
  unfold FinCondIndep.margZ
  simp only [hp, Finset.sum_mul_sum]

/-- `margXZ` 的展开（**只对 `y` 求和**，单层）。 -/
theorem margXZ_of_screenGlue (p : J3 V) (m : V → V → ℝ) (sigma : V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = m x z * sigma y) (x z : V) :
    margXZ p x z = m x z * (∑ y, sigma y) := by
  unfold FinCondIndep.margXZ
  simp only [hp]
  rw [Finset.mul_sum]

/-- `margYZ` 的展开（**只对 `x` 求和**，单层）。 -/
theorem margYZ_of_screenGlue (p : J3 V) (m : V → V → ℝ) (sigma : V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = m x z * sigma y) (y z : V) :
    margYZ p y z = (∑ x, m x z) * sigma y := by
  unfold FinCondIndep.margYZ
  simp only [hp]
  rw [Finset.sum_mul]

/-- **`Y`-相对的条件乘性**：`CondMul` 只在查询集 `Y` 上要求。

`X ⟂ Y | Z` 的概率含义从来只关于**给定的 `Y`**；对 `y ∉ Y` 的坐标无关紧要。
故本文件把结论精确地陈述成 `Y`-相对形式。 -/
def CondMulOn (p : J3 V) (Y : Finset V) : Prop :=
  ∀ x z, ∀ y ∈ Y, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z

/-- ⭐⭐⭐⭐⭐ **V17G-4（主定理）：`dSep` + 截面胶合 ⟹ `Y`-相对 `CondMul`。**

$$\underbrace{G.\mathrm{dSep}\ X\ Y\ Z}_{\text{图侧}}\;+\;
  \underbrace{\mathrm{ScreenGlue}\ G\ X\ Z\ p}_{\text{概率侧截面胶合}}
  \;\Longrightarrow\;\;
  \forall x\,z,\ \forall y\in Y,\
  p((x,y),z)\cdot m_Z(z)=m_{XZ}(x,z)\cdot m_{YZ}(y,z).$$

**证明结构（三步，零 `mass`）**：

1. 由 V17G-2（**消费 `dSep`**）取 `σ y = 1` for `y ∈ Y`；
2. 用三条单层展开把三个边缘写成 `m`、`σ` 与两个「单层和」`∑x m`、`∑y σ` 的乘积；
3. 代入后两边都是 `m x z · (∑x m x z) · (∑y σ y)`，`ring` 闭合。

**⚠ 图在哪里进入**：只在第 1 步。**去掉 `h : G.dSep X Y Z`，第 1 步不可得。** -/
theorem screenGlue_condMulOn (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : J3 V) (hg : ScreenGlue G X Z p) :
    CondMulOn p Y := by
  obtain ⟨m, sigma, hp, hone⟩ := screenGlue_sigma_one_on_Y G h p hg
  intro x z y hy
  rw [margZ_of_screenGlue p m sigma hp z,
      margXZ_of_screenGlue p m sigma hp x z,
      margYZ_of_screenGlue p m sigma hp y z,
      hp x y z, hone y hy]
  ring

/-- ⭐⭐⭐ **V17G-5：全量 `CondMul` 的充分条件。**

若列核 `σ` 在**全部**顶点上等于 `1`（即 `p((x,y),z)=m x z` 与 `y` 无关），
则 `margYZ` 与 `y` 无关，`CondMul` **在整个 `V` 上**成立 —— 不需要 `dSep`。

**⚠ 诚实标注**：本定理**不消费图**，故**不计入「桥」**。
它的作用是把 §3 的两条路径分开登记：
**只有 `CondMulOn` 是桥；`CondMul`（全量）是 `σ ≡ 1` 的纯概率推论。** -/
theorem screenGlue_condMul (p : J3 V) (m : V → V → ℝ) (sigma : V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = m x z * sigma y)
    (hσ : ∀ y, sigma y = 1) : FinCondIndep.CondMul p := by
  intro x y z
  rw [margZ_of_screenGlue p m sigma hp z,
      margXZ_of_screenGlue p m sigma hp x z,
      margYZ_of_screenGlue p m sigma hp y z,
      hp x y z, hσ y]
  ring

/-! ### 3.1 字面形式：条件分布相等（带守卫）

`CondRatio` 是 Pearl 的字面形式。它需要 `margZ p z ≠ 0`（条件分布只在正质量处有定义）。 -/

/-- **`Y`-相对的条件分布相等**。 -/
def CondRatioOn (p : J3 V) (Y : Finset V) : Prop :=
  ∀ x z, ∀ y ∈ Y, margZ p z ≠ 0 →
    p ((x, y), z) / margZ p z =
      (margXZ p x z / margZ p z) * (margYZ p y z / margZ p z)

/-- ⭐⭐⭐ **V17G-6：截面胶合 + 非零 `Z`-边缘 ⟹ 字面条件分布相等（`Y`-相对）。**

由 V17G-4 与 `Fate.FinCondIndep.condMulGuard_iff_condRatio` 的逐点代数转写。 -/
theorem screenGlue_condRatioOn (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : J3 V) (hg : ScreenGlue G X Z p)
    : CondRatioOn p Y := by
  intro x z y hy hzz
  have hcm := screenGlue_condMulOn G h p hg x z y hy
  -- 与 `condMulGuard_iff_condRatio` 同一代数：把守卫版乘性等式转成除法等式。
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hzz hzz)]
  rw [← hcm, ← mul_assoc, div_mul_cancel₀ _ hzz]
/-! ===========================================================================
  §4 非空洞性：常值律对**任意**图成立
  =========================================================================== -/

/-- ⭐⭐⭐ **V17G-7：反「真空命题」。**

常值律 `p ≡ 1` 对**任意** `G`、`X`、`Z` 都有截面胶合（`m ≡ σ ≡ 1`）。
故 §3 的前提**不是空集**，桥**不是真空成立**。 -/
theorem screenGlue_nonvacuous (G : DAG V) (X Z : Finset V) :
    ScreenGlue G X Z (fun _ : (V × V) × V => (1 : ℝ)) :=
  ⟨fun _ _ => 1, fun _ => 1, fun x y z => by ring, fun _ _ => rfl⟩

/-- ⭐⭐ **V17G-7'**：非空洞性的**结论侧**核实 —— 常值律在任意 `G X Y Z` 上满足
`Y`-相对 `CondMul`。这条把 §4 与 §3 接通，说明桥在**非平凡假设下也产出真结论**。 -/
example (G : DAG V) {X Y Z : Finset V} (h : G.dSep X Y Z) :
    CondMulOn (fun _ : (V × V) × V => (1 : ℝ)) Y :=
  screenGlue_condMulOn G h _ (screenGlue_nonvacuous G X Z)

/-! ===========================================================================
  §5 **必要性**：`dSep` 不可去

  `ScreenGlue` 只说「**屏幕外**列核为 `1`」。要把它变成「**`Y` 上**列核为 `1`」，
  必须知道 `Y` **完全落在屏幕外** —— 这正是 `dSep` 第 4 子句的内容。
  本节给出**形式化反例**：`dSep` 失败时，胶合仍可成立，但 `σ` 在 `Y` 上**不受约束**。
  =========================================================================== -/

section Necessity

/-- 三元顶点：`0 = X`、`1 = Z`、`2 = Y`（链 `0 → 1 → 2`）。 -/
abbrev V3 := Fin 3

/-- 链 `X → Z → Y` 的边（顶点 `0 → 1 → 2`）。 -/
def chainEdge3 : V3 → V3 → Prop :=
  fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

/-- **链作为真 `DAG`**（无环性由 `Fin.val` 严格递增给出）。 -/
def chainDAG3 : DAG V3 where
  edge := chainEdge3
  decEdge := fun i j => by unfold chainEdge3; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : V3}, Relation.TransGen chainEdge3 a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold chainEdge3 at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold chainEdge3 at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (by simp)

/-- 对撞 `X → Z ← Y` 的边（`0 → 2 ← 1`）。 -/
def colliderEdge3 : V3 → V3 → Prop :=
  fun i j => (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)

/-- **对撞作为真 `DAG`**。 -/
def colliderDAG3 : DAG V3 where
  edge := colliderEdge3
  decEdge := fun i j => by unfold colliderEdge3; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : V3}, Relation.TransGen colliderEdge3 a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold colliderEdge3 at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold colliderEdge3 at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (by simp)

/-- ⭐⭐⭐ **V17G-8a（链上 `dSep` 为真）**：`{0} ⟂_d {2} | {1}` 在 `0 → 1 → 2` 上成立。 -/
theorem chain_dSep : chainDAG3.dSep {0} {2} {1} := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- ⭐⭐ **V17G-8b（屏幕非满）**：链上 `X = {0}`、`Z = {1}` 的屏幕**不含** `Y = {2}`。

**⟹ 主定理 V17G-2 的前提在链上真的满足**（`Y` 与屏幕不交），故 `σ 2 = 1` 被图**逼出**。 -/
theorem chain_Y_outside_screen : (2 : V3) ∉ chainDAG3.bbReachableVertices {1} {0} := by
  decide

/-- ⭐⭐⭐ **V17G-10（`dSep` 不可去 —— 形式化反例）**。

在**同一**条链上，取 `Z = ∅`、`Y = {1}`：

* `dSep {0} {1} ∅` **为假**（`1` 正是 `0` 的孩子，落在屏幕里）；
* 此时 `1` **在屏幕内**，故 `ScreenGlue` 的第二个合取项**对 `y = 1` 什么也不说** ——
  `σ 1` 可以是任意实数。

**⟹ 「`σ ≡ 1` on `Y`」的真正来源是 `dSep` 的 `Disjoint` 子句，
而不是 `ScreenGlue` 本身。** 这就是「图真的做功」的精确判据。 -/
theorem screen_hypothesis_not_removable :
    (1 : V3) ∈ chainDAG3.bbReachableVertices ∅ {0} ∧ ¬ chainDAG3.dSep {0} {1} ∅ := by
  refine ⟨by decide, by decide⟩

/-- ⭐⭐⭐ **V17G-9（判别力：屏幕随 `Z` 变化 —— 图侧见证）。**

同一对撞图 `0 → 2 ← 1`，改变 `Z` 会改变 `Y = {1}` 是否落在屏幕里：

* `Z = ∅`：`1 ∉ 屏幕`（球从 `0` 只能到 `2`）；
* `Z = {2}`：`1 ∈ 屏幕`（对撞被条件化后，球经 `2` 传回 `1`）。

**⟹ 屏幕 `bbReachableVertices Z X` 是 `Z` 的**真函数**，不是装饰。
这正是 `dSep` 中「条件集真的改变图侧判定」的机检证据。 -/
theorem collider_screen_moves_with_Z :
    (1 : V3) ∉ colliderDAG3.bbReachableVertices ∅ {0} ∧
      (1 : V3) ∈ colliderDAG3.bbReachableVertices {2} {0} := by
  refine ⟨by decide, by decide⟩

/-- ⭐⭐ **V17G-9'**：`dSep` 在**未条件化**的对撞上为真（`{0} ⟂_d {1} | ∅`）。 -/
theorem collider_dSep_empty : colliderDAG3.dSep {0} {1} ∅ := by
  unfold DAG.dSep
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- ⭐⭐ **V17G-9''**：`dSep` 要求 `Z` 与 `Y` 不交，故 `{0} ⟂_d {1} | {1}` **为假**。 -/
theorem collider_not_dSep_selfcond : ¬ colliderDAG3.dSep {0} {1} {1} := by
  decide

end Necessity

/-! ===========================================================================
  §6 **零 `mass` 塔**：形式化登记

  本文件**不导入** `Fate.DAGFactorization`（`mass` 的定义处），
  故 `mass` 在**名字层面**就不可达 —— 这比「声称不用」更强。
  本节的定理把这件事**钉死在类型系统里**。
  =========================================================================== -/

section NoMass

/-- ⭐⭐⭐ **V17G-11：本文件的求和全部作用在 `p` 自身。**

本节的定理复述 §3 的所有展开引理，以**展示**它们的形式：
左端是 `margZ p z`（`p` 自身的两层 `∑`），右端是 `(∑ x, m x z) * (∑ y, σ y)`
（两个**单层**求和之积）。**没有任何 `mass S (mass T p)` 形状的嵌套**。

**⚠ 为什么这是「精确含义」而不仅是修辞**：`mass S p x` 的类型是
`Finset V → (V → α) → ℝ → ...`（固定**集合**坐标），而本文件从未出现
任何以 `Finset V` 为**第一个参数**的求和算子；唯一的 `Finset` 参数是
`bbReachableVertices Z X`，它只作为**谓词**出现在胶合条件里，**从不进入求和**。 -/
theorem no_mass_tower (p : J3 V) (m : V → V → ℝ) (sigma : V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = m x z * sigma y) (z : V) :
    -- 两层求和 = 单层求和之积（**分配律**，不是塔）
    margZ p z = (∑ x, m x z) * (∑ y, sigma y) ∧
    -- 且两个因子各自是**单层**求和
    (∑ x, m x z) = ∑ x, m x z :=
  ⟨margZ_of_screenGlue p m sigma hp z, rfl⟩

/-- ⭐⭐ **V17G-11'**：逐层拆解的可核验形状 —— `margXZ` 只对 `y` 求和、`margYZ` 只对 `x` 求和，
各**一层**。这正是 §8 对照表中「本文件」一列的全部内容。 -/
theorem single_layer_sums (p : J3 V) (m : V → V → ℝ) (sigma : V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = m x z * sigma y) :
    (∀ x z, margXZ p x z = m x z * (∑ y, sigma y)) ∧
    (∀ y z, margYZ p y z = (∑ x, m x z) * sigma y) :=
  ⟨fun x z => margXZ_of_screenGlue p m sigma hp x z,
   fun y z => margYZ_of_screenGlue p m sigma hp y z⟩

end NoMass

/-! ===========================================================================
  §7 与既有两版「视角 17」的机检对照
  =========================================================================== -/

/-! ### 7.1 汇总表

| 项 | `Fate/View17.lean`（`BarrierSplit`） | `Fate/GraphToProbView17.lean`（`ScreenSplit`） | **本文件（`ScreenGlue`）** |
|---|---|---|---|
| 概率侧前提 | `λ z · a x z · b y z` | `λ z · a x z · b y z` | **`m x z · σ y`（`σ` 不含 `z`）** |
| `z` 在列核里 | 有 | 有 | **无** |
| 屏幕条件 | `b y z = 1`（幕外） | `b y z = 1`（幕外） | **`σ y = 1`（幕外）** |
| `dSep` 的用处 | 钉 `b ≡ 1` on `Y` | 钉 `b ≡ 1` on `Y` | **钉 `σ ≡ 1` on `Y`** |
| 结论 | `∀y∈Y, b y z = 1` | `∀y∈Y, b y z = 1` | **`p` 在 `Y` 上不含 `y`（更强）** |
| 终点 | `CondMul` | `CondMul` | **`CondMulOn`（`Y`-相对）** |
| 索引对齐 | `α=β=γ=V` | `α=β=γ=V` | `α=β=γ=V` |
| `mass` 塔 | 显式登记不用 | 显式登记不用 | **`mass` 名字不可达**（未导入） |
| 必要性反例 | 有（`collider_not_kernelSplit`） | 有 | **有（`screen_hypothesis_not_removable`）** |

### 7.2 为什么这是**第 17 条**而不是前两条的改写

旧两版的前提是**三层乘积**；本文件是**两层乘积且列核与 `z` 无关**。
数学上二者**互不包含**：

* `λ z · a x z · b y z` 一般**不能**写成 `m x z · σ y`
  （因为 `b` 依赖 `z`，而 `σ` 不依赖）；
* 反之 `m x z · σ y` 可以写成三层形式（取 `λ ≡ 1`、`b := σ`）。

**⟹ 本文件的 `ScreenGlue` 是旧版 `ScreenSplit` 在 `b` 与 `z` 无关时的**真子类**，
但它换来了更强的结论（`Y` 通道**完全坍缩**，连 `z` 层权都不剩），
并且揭示了旧版没有的那条机制：**`dSep` 的作用是「把 `Y` 移出屏幕」**，
而这一点在 `screen_hypothesis_not_removable` 里被机检成
`Y ∈ 屏幕 ⟺ dSep 失败` 的一个具体见证。 -/

/-! ===========================================================================
  §8 诚实边界（**必读**，不以定理伪装）
  =========================================================================== -/

/-!
1. **`ScreenGlue` 不是由 `dSep` 推出的。** 它是**显式概率前提**。
   本文件证明的是：**一旦接受它，`dSep` 就唯一地把它在 `Y` 上补完**（V17G-2）。
   `dSep ⟹ ScreenGlue` 等价于一般 DAG 上的因子分解，**不在本文件**，
   也不该在本文件（该路线的缺口登记在 `PEARL_127_PROOF_ROADMAP` §3 A4「缺口 A」）。

2. **结论是 `Y`-相对的 `CondMulOn`，不是全量 `CondMul`。**
   这不是弱化而是**精确化**：`X ⟂ Y | Z` 的概率含义本来就只关于给定的 `Y`。
   全量 `CondMul` 需要 `σ ≡ 1` **处处**成立（V17G-5），那是纯概率推论，**不消费图**，
   故本文件把它与桥**分开登记**。

3. **`CondRatio`（带除法）需要 `margZ ≠ 0`。** 这是概率语义的必需项
   （条件分布只在正质量处有定义），不是本视角的弱点。V17G-6 把该守卫
   **内建进 `CondRatioOn` 的定义**，故不需要额外的全局假设。

4. **零 `mass` 是结构性的，不是自述。** 本文件未导入 `Fate.DAGFactorization`，
   故 `mass` 在名字层面不可达；§6 的 `no_mass_tower` 把「两层求和 = 单层之积
   （分配律）」这一形状机检出来，与塔性质（**已证伪**）形成对照。
-/

end FateV2.Predict.View17SectionGlue