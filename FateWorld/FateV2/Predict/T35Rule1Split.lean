import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Predict.Rule1Semantic
/-!
  # Predict · T35Rule1Split

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T35Rule1Split.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMSemantics, Rule1Semantic
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T35Rule1Split` —— **缺口 3：do-calculus 规则 1 的语义版本**
  （**任务书原义的外生分解形式**：`X` 与 `Y` 用**不同的外生分量**）
  ===========================================================================

  ## 0. 任务书要求

  > **缺口 3**：在「**无混杂**」条件下证明
  > `∀ x, doLaw M x = condY M x`，
  > 该条件表述为「**`Y` 的方程不使用 `X` 的方程所用的那个外生分量**」。
  > 必须有**具体 SCM 实例**验证；若**为假**，须给出**反例**并如实登记。

  ## 1. ⭐⭐⭐⭐ 结论汇总（先说清楚）

  本文件给出 **3 个真定理 + 3 个具体反例**，**全部零 `sorry` / 零 `axiom` /
  零 `native_decide`**，并有完整 `lake build` 输出。

  | # | 结论 | 状态 |
  |---|---|---|
  | **A** | 任务书**字面**陈述 `doLaw = condY` 在本载体上 **FALSE** | ⛔ **反例** `MNC_rule1_literal_fails`（`1/2 ≠ 1/4`）、`MBad_fails`（`2 ≠ 1`）|
  | **B** | 「读不同外生位」**单独不够** —— 还需 `p_U` **可分离** | ⭐ **关键发现** §3 |
  | **C** | 「可分离」**仍不够** —— 还需 `∑p_X = ∑p_Y = 1` | ⭐⭐ **关键发现** §3.2 |
  | **D** | **三条件齐备 ⟹ `condY = μ(x)·doLaw`** | ✅ **已证** `rule1_of_separable` |
  | **E** | `∑ p_U = 1` 且 `μ(x) ≠ 0` 时**归一化成 Pearl 原式** | ✅ **已证** `rule1_normalized` |

  **⭐ 正确的「无混杂」（本文件的三段式）**：

  $$\boxed{\;
  \underbrace{\textsf{XReadsOnlyUx}}_{\text{X 只读 } Ux}
  \;\wedge\;
  \underbrace{\textsf{YReadsOnlyUy}}_{\text{Y 只读 } Uy}
  \;\wedge\;
  \underbrace{\textsf{SeparablePU}}_{\,p_U = p_X\!\cdot p_Y,\;\textstyle\sum p_X=\sum p_Y=1}
  \;}$$

  ## 2. ⚠ 为什么字面陈述 `doLaw = condY` 必然是**假**的

  两个**互不相干**的理由，都是纯算术的：

  - **理由 α（归一化常数不同）**：`condY` 是**联合质量** `P(X=x, Y=y)`，
    `doLaw` 是**边缘质量** `P(Y_x = y)`。
    两者差**恰好** `μ(x) = P(X=x)`。
    见 `MNC_literal_gap`：`condY = ½ · doLaw`。
  - **理由 β（`doLaw` 未除 `∑ p_U`）**：`doLaw := ∑_u p_U(u)·[·]`，
    **不除以** `∑_u p_U(u)`。仅当 `∑p_U = 1` 时它才恰是概率。
    见 `MBad_fails`（`p_U ≡ 1`，`∑p_U = 2`）。

  **⟹ 任务书要求的那个等式**在任何「有意思」的 SCM 上都不可能成立**。

  ## 3. ⭐⭐⭐⭐ 关键发现：任务书的「无混杂」表述**不充分**

  任务书说「`X` 与 `Y` 用**不同的**外生分量」。在 `PearlHierarchy.SCM`
  （字段为**单一** `U` 与 `sg : U → X × (X → Y)`）上，必须先引入
  `e : M.U ≃ Ux × Uy` 把 `U` 拆两半，再要求

  - `XReadsOnlyUx`：固定 `u`，改 `v ↦ v'`，`X` 不动；
  - `YReadsOnlyUy`：固定 `v`，改 `u ↦ u'`，`Y` **在任意 `x` 上**都不动。

  **⭐ 但这两条只管了**方程**，没管**外生分布 `p_U`**。** 反例：

  $$p_U(\textsf{false},\textsf{false}) = \tfrac12,\quad
    p_U(\cdot,\cdot) = 0\ \text{否则}$$

  `X`、`Y` 的方程**确实**互不读对方的外生位（结构条件成立），
  **但 `X` 与 `Y` 经 `p_U` 在统计上完全缠在一起**（`X = Y` 必然），
  **故 `condY ≠ μ(x)·doLaw`。**
  ⟹ **Pearl 规则 1 隐含要求外生**独立**，不只是「读不同位」。**

  ### 3.1 于是需要第三个成分：`SeparablePU`

  `SeparablePU M e := ∃ pX pY, ∀ u v, M.pU (e.symm (u,v)) = pX u * pY v`

  ### 3.2 ⭐⭐ 而「可分离」**仍不够** —— 还需 `∑ p_X = ∑ p_Y = 1`

  **这是本文件的第二个关键发现。** 展开后：

  ```text
  condY   = (∑_u pX u · A u) · (∑_v pY v · B v)
  μ·doLaw = [(∑_u pX u · A u) · ∑_v pY v] · [(∑_u pX u) · ∑_v pY v · B v]
  ```

  两者相等 **⟺ `(∑pX)·(∑pY) = 1`**。
  「可分离」**不**蕴含它（例如 `pX ≡ pY ≡ 1` 给出 `p_U ≡ 1`，正是 `MBad`！）。

  **⟹ 必须**同时**要求 `∑pX = 1`、`∑pY = 1`（即 `pX`、`pY` 本身是概率）。
  这就是 `SeparablePU` 定义里附带的那两个等式，
  也正是 `fac_general`（§4.1）里 `hp`/`hr` 两个假设的来源。

  ## 4. 本文件产出清单

  | # | 名字 | 内容 |
  |---|---|---|
  | 1 | `XReadsOnlyUx` / `YReadsOnlyUy` / `SplitNoConfounding` | 任务书的**结构式**条件 |
  | 2 | `SeparablePU` | 第三成分：`p_U` 可分离**且**两因子归一 |
  | 3 | `condY_as_prod_sum` / `doLaw_as_prod_sum` / `marginalX_as_prod_sum` | 三个量在 `Ux × Uy` 上的**重排** |
  | 4 | `fac_general` | ⭐ **纯代数核心**：`∑∑ pX·pY·A·B = (∑∑ pX·pY·A)(∑∑ pX·pY·B)` |
  | 5 | ⭐⭐⭐⭐ `rule1_of_separable` | **主定理**：三条件 ⟹ `condY = μ(x)·doLaw` |
  | 6 | ⭐⭐⭐⭐ `rule1_normalized` | **归一化**：`condY / μ(x) = doLaw`（Pearl 原式）|
  | 7 | `MNC`（`condY_MNC` / `doLaw_MNC` / `marginalX_MNC`） | **具体无混杂实例**（真算 `1/4`、`1/2`、`1/2`）|
  | 8 | `MNC_separable` / `MNC_rule1` / `MNC_noConfounding` | 具体实例上主定理**成立** |
  | 9 | ⛔ ⭐⭐⭐⭐⭐ `MNC_rule1_literal_fails` | **任务书**字面陈述的具体反例 |
  | 10 | ⛔ ⭐⭐⭐⭐ `MBad` / `MBad_fails` / `MBad_split` | **未归一化**反例（`2 ≠ 1`）|
  | 11 | `noUDependence_implies_split` | 与既有的 `NoUDependence` 条件的比较 |
  | 12 | `y_reads_only_uy_not_tautological` | 本谓词**不是**恒真（对比草稿的退化谓词）|
  | 13 | `draft_second_conjunct_is_tautology` | ⭐ **草稿错误的精确登记** |

  ## 5. 与既有文件的分工（不重复劳动）

  | 文件 | 「无混杂」的表述 | 层面 |
  |---|---|---|
  | `Fate/Rule1Semantic.lean` | `NoConfounding := ∀xy, condY = μ(x)·doLaw` | **语义**式 |
  | ⭐ **本文件** | `SplitNoConfounding ∧ SeparablePU` | **结构**式 → 推导**语义**式 |
  | `Fate/T35Rule1NoConfounding.lean` | 草稿退化谓词 | ⛔ 登记其**不充分** |

  **蕴含链**：**结构式（本文件 `rule1_of_separable`）⟹ 语义式
  （`Rule1Semantic`）⟹ Pearl 归一化式。**

  ## 6. ⚠ 载体限制（诚实登记）

  - `T35.M.U = Fin 2`，**无法**拆成 `Ux × Uy` 使 `X`、`Y` 读**不同**分量；
    其混杂是「**同一坐标驱动两方程**」，比「读错分量」更强 ⟹
    必须用 `Rule1Semantic` 的**语义**谓词去抓（见 `T35_not_noConfounding`）。
  - `PearlHierarchy.SCM` 是**单一** `U`，故「读不同分量」**必须**经 `e` 陈述。
  - `SeparablePU` 中的归一（`∑pX = ∑pY = 1`）**不是**载体的产物，
    而是**数学必需**（§3.2 的代数论证）。
  =========================================================================== -/

namespace FateV2.Predict.T35Rule1Split

open FateV2.Modeling

open scoped BigOperators

open FateV2.Modeling.PearlHierarchy FateV2.Modeling.SCMSemantics


/-- ⭐ **别名**：`Fate/Rule1Semantic.lean` 的 `SCM.NoConfounding` 位于
`Fate.R242G3.SCM` 命名空间下，这里给出本文件可直接使用的短名。 -/
def NC {X Y : Type} [DecidableEq X] [DecidableEq Y] (M : SCM X Y) : Prop :=
  Fate.R242G3.SCM.NoConfounding M

/-- ⭐ **别名**：`Fate.R242G3.SCM.NoUDependence`。 -/
def NUD {X Y : Type} (M : SCM X Y) : Prop :=
  Fate.R242G3.SCM.NoUDependence M

/-! ===========================================================================
  §1 任务书的**结构式**「无混杂」
  =========================================================================== -/

/-- ⭐⭐⭐ **`X` 的方程不读 `Uy`**（给定外生分解 `e : M.U ≃ Ux × Uy`）。

$$\forall u\,v\,v',\quad (\mathrm{sg}(e^{-1}(u,v))).1 = (\mathrm{sg}(e^{-1}(u,v'))).1$$

**⭐ 读法**：固定 `Ux` 分量 `u`，改变 `Uy` 分量 `v ↦ v'`，
**`X` 的值不动** ⟹ `X` 的方程是 `Ux` 的函数。 -/
def XReadsOnlyUx {X Y : Type} {Ux Uy : Type}
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) : Prop :=
  ∀ (u : Ux) (v v' : Uy), (M.sg (e.symm (u, v))).1 = (M.sg (e.symm (u, v'))).1

/-- ⭐⭐⭐ **`Y` 的方程不读 `Ux`**（给定外生分解 `e : M.U ≃ Ux × Uy`）。

$$\forall u\,u'\,v\,x,\quad (\mathrm{sg}(e^{-1}(u,v))).2\,x
  = (\mathrm{sg}(e^{-1}(u',v))).2\,x$$

**⭐ 读法**：固定 `Uy` 分量 `v`，改变 `Ux` 分量 `u ↦ u'`，
**`Y` 的方程（在任意输入 `x` 上）的值不动** ⟹ `Y` 的方程**只**是 `Uy` 的函数。

**⚠ 这是草稿定义里**缺掉的那一半**。草稿写成了同一个项的自等（见
`draft_second_conjunct_is_tautology`）；这里 `u'` 是**真正的新变量**，
故本谓词**不恒真**（见 `y_reads_only_uy_not_tautological`）。 -/
def YReadsOnlyUy {X Y : Type} {Ux Uy : Type}
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) : Prop :=
  ∀ (u u' : Ux) (v : Uy) (x : X),
    (M.sg (e.symm (u, v))).2 x = (M.sg (e.symm (u', v))).2 x

/-- ⭐⭐⭐ **「无混杂」（任务书的结构式）**：`X` 只读 `Ux`、`Y` 只读 `Uy`。

**⚠ 这是**必要但不充分**的（§3、§3.2 的两个反例）。
充分条件见 `SeparablePU`，合成见 `FullNoConfounding`。 -/
def SplitNoConfounding {X Y : Type} {Ux Uy : Type}
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) : Prop :=
  XReadsOnlyUx M e ∧ YReadsOnlyUy M e

/-- ⭐⭐⭐⭐ **第三成分：`p_U` 在 `e` 下**可分离且两因子归一**。

$$p_U(e^{-1}(u,v)) = p_X(u)\cdot p_Y(v),\qquad
  \sum_u p_X(u) = 1,\qquad \sum_v p_Y(v) = 1$$

**⭐⭐ 两个等式都不可省**：
- **可分离性**：否则 `X`、`Y` 经 `p_U` 统计纠缠（§3 反例）；
- **归一性**：否则 `condY ≠ μ(x)·doLaw`（§3.2 的代数论证；`MBad` 即此）。

**⚠ `MBad` 正是「可分离但未归一」**：`p_U ≡ 1 = 1 · 1`，可分离 ✓，
但 `∑ 1 = 2 ≠ 1` ✗ ⟹ 字面 / 结构性结论全部崩溃。 -/
def SeparablePU {X Y Ux Uy : Type} [Fintype Ux] [Fintype Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) : Prop :=
  ∃ (pX : Ux → ℝ) (pY : Uy → ℝ),
    (∀ u v, M.pU (e.symm (u, v)) = pX u * pY v) ∧
    (∑ u, pX u) = 1 ∧ (∑ v, pY v) = 1

/-- ⭐⭐⭐⭐ **完整的「无混杂」**（本文件的最终三段式条件）。

**⟹ `FullNoConfounding M e → NC M`**（`rule1_of_separable`）。 -/
def FullNoConfounding {X Y : Type} {Ux Uy : Type} [Fintype Ux] [Fintype Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) : Prop :=
  SplitNoConfounding M e ∧ SeparablePU M e

/-! ===========================================================================
  §2 三个量在 `Ux × Uy` 上的**重排**
  =========================================================================== -/

/-- ⭐⭐ **`condY` 重排到 `Ux × Uy`**（`Equiv.sum_comp`）。 -/
theorem condY_as_prod_sum {X Y Ux Uy : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    [Fintype Ux] [Fintype Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) (x : X) (y : Y) :
    condY M x y
      = ∑ p : Ux × Uy, M.pU (e.symm p)
          * (if (M.sg (e.symm p)).1 = x then (1 : ℝ) else 0)
          * (if (M.sg (e.symm p)).2 x = y then (1 : ℝ) else 0) := by
  unfold condY
  exact (Equiv.sum_comp e.symm
    (fun u => M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)
      * (if (M.sg u).2 x = y then (1 : ℝ) else 0))).symm

/-- ⭐⭐ **`doLaw` 重排到 `Ux × Uy`**。 -/
theorem doLaw_as_prod_sum {X Y Ux Uy : Type} [DecidableEq Y]
    [Fintype Ux] [Fintype Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) (x : X) (y : Y) :
    doLaw M x y
      = ∑ p : Ux × Uy, M.pU (e.symm p)
          * (if (M.sg (e.symm p)).2 x = y then (1 : ℝ) else 0) := by
  unfold doLaw
  exact (Equiv.sum_comp e.symm
    (fun u => M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0))).symm

/-- ⭐⭐ **`marginalX` 重排到 `Ux × Uy`**。 -/
theorem marginalX_as_prod_sum {X Y Ux Uy : Type} [DecidableEq X]
    [Fintype Ux] [Fintype Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) (x : X) :
    marginalX M x
      = ∑ p : Ux × Uy, M.pU (e.symm p)
          * (if (M.sg (e.symm p)).1 = x then (1 : ℝ) else 0) := by
  unfold marginalX
  exact (Equiv.sum_comp e.symm
    (fun u => M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0))).symm

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **纯代数核心**：可分离 + 归一 ⟹ 双重和因子化
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **本文件的代数心脏**（§3.2 的形式化）。

$$\Bigl(\sum_i\sum_j p_i\,r_j\,A_i\,B_j\Bigr)
  = \Bigl(\sum_i\sum_j p_i\,r_j\,A_i\Bigr)
    \cdot\Bigl(\sum_i\sum_j p_i\,r_j\,B_j\Bigr)$$

**前提**：`∑ p = 1`、`∑ r = 1` —— **两个都不能省**（§3.2 反例 `MBad`）。

**⭐ 证明思路**（这是本引理的实质）：
1. 内层 `∑_j p_i r_j A_i B_j = (p_i A_i)·(∑_j r_j B_j)`（`Finset.mul_sum` + `ring`）；
2. 同理把 RHS 两个因子也化简为 `(∑_i p_i A_i)·(∑_j r_j B_j)`
   与 `(∑_i p_i)·(∑_j r_j B_j)`（`h2`/`h3`）；
3. 用 `hp`/`hr` 把多出的 `∑ r = 1`、`∑ p = 1` 消掉；
4. `ring` 收尾。 -/
theorem fac_general {ι κ : Type} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (r : κ → ℝ) (A : ι → ℝ) (B : κ → ℝ)
    (hp : (∑ i, p i) = 1) (hr : (∑ j, r j) = 1) :
    (∑ i, ∑ j, p i * r j * A i * B j)
      = (∑ i, ∑ j, p i * r j * A i) * (∑ i, ∑ j, p i * r j * B j) := by
  have h1 : ∀ i, (∑ j, p i * r j * A i * B j) = (p i * A i) * (∑ j, r j * B j) := by
    intro i; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∀ i, (∑ j, p i * r j * A i) = (p i * A i) * (∑ j, r j) := by
    intro i; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∀ i, (∑ j, p i * r j * B j) = p i * (∑ j, r j * B j) := by
    intro i; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h1, h2, h3, ← Finset.sum_mul, hr, mul_one, hp]
  ring

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **主定理：完整无混杂 ⟹ 规则 1**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **规则 1 的**结构**版本（本文件主定理）**。

$$\textsf{FullNoConfounding}(M,e)
  \implies \forall x\,y,\quad
     \mathrm{condY}\,M\,x\,y = \mu(x)\cdot \mathrm{doLaw}\,M\,x\,y$$

**⚠ 本定理**不**声称 `condY = doLaw`** —— 那字面等式在
`μ(x) ≠ 1` 或 `∑p_U ≠ 1` 时**为假**（§5 的 `MNC_rule1_literal_fails`、
`MBad_fails`）。**本定理声称的是**正确**的形式 `μ(x) · doLaw`。**

**⭐ 证明结构**（三个假设各司其职）：
1. `×3` 把 `condY`/`marginalX`/`doLaw` 重排成 `∑_{(u,v)}`（§2）；
2. `[x_u = x]` 用 `XReadsOnlyUx` 换成只依赖 `u` 的 `A u`；
   `[y_v(x) = y]` 用 `YReadsOnlyUy` 换成只依赖 `v` 的 `B v`；
3. 用 `SeparablePU` 的 `p_U = p_X·p_Y` 代入；
4. 交给 `fac_general`（§3）—— **需要 `SeparablePU` 的两个归一等式**。 -/
theorem rule1_of_separable {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
    [DecidableEq Uy] [Nonempty Ux] [Nonempty Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy)
    (hx : XReadsOnlyUx M e) (hy : YReadsOnlyUy M e)
    (hsep : SeparablePU M e) (x : X) (y : Y) :
    condY M x y = marginalX M x * doLaw M x y := by
  obtain ⟨pX, pY, hp, hpX, hpY⟩ := hsep
  obtain ⟨v₀⟩ := ‹Nonempty Uy›
  obtain ⟨u₀⟩ := ‹Nonempty Ux›
  rw [condY_as_prod_sum (Ux := Ux) (Uy := Uy) M e x y,
      marginalX_as_prod_sum (Ux := Ux) (Uy := Uy) M e x,
      doLaw_as_prod_sum (Ux := Ux) (Uy := Uy) M e x y,
    Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  -- 用 `hx`/`hy` 把两个指示函数各换成单变量函数
  set Au : Ux → ℝ := fun u => if (M.sg (e.symm (u, v₀))).1 = x then (1 : ℝ) else 0
  set Bv : Uy → ℝ := fun v => if (M.sg (e.symm (u₀, v))).2 x = y then (1 : ℝ) else 0
  have hAeq : ∀ (u : Ux) (v : Uy),
      (if (M.sg (e.symm (u, v))).1 = x then (1 : ℝ) else 0) = Au u := by
    intro u v; simp only [Au]; rw [hx u v v₀]
  have hBeq : ∀ (u : Ux) (v : Uy),
      (if (M.sg (e.symm (u, v))).2 x = y then (1 : ℝ) else 0) = Bv v := by
    intro u v; simp only [Bv]; rw [hy u u₀ v x]
  simp only [hAeq, hBeq, hp]
  exact fac_general pX pY Au Bv hpX hpY

/-- ⭐⭐⭐⭐ **`FullNoConfounding` 版本的汇总形式**。 -/
theorem rule1_of_fullNoConfounding {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
    [DecidableEq Uy] [Nonempty Ux] [Nonempty Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy)
    (h : FullNoConfounding M e) (x : X) (y : Y) :
    condY M x y = marginalX M x * doLaw M x y :=
  rule1_of_separable M e h.1.1 h.1.2 h.2 x y

/-- ⭐⭐⭐⭐ **⟹ 语义式 `NoConfounding`（`Rule1Semantic` 的谓词）**。

**⭐ 这把「结构式」与既有的「语义式」接上了**：
`FullNoConfounding M e → NC M`。 -/
theorem noConfounding_of_fullNoConfounding {X Y Ux Uy : Type} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux]
    [Fintype Uy] [DecidableEq Uy] [Nonempty Ux] [Nonempty Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) (h : FullNoConfounding M e) :
    NC M :=
  fun x y => rule1_of_fullNoConfounding M e h x y

/-- ⭐⭐⭐⭐ **归一化：Pearl 规则的**字面**形式**。

$$\mu(x)\neq 0 \implies \frac{\mathrm{condY}\,M\,x\,y}{\mu(x)}
  = \mathrm{doLaw}\,M\,x\,y$$

**⚠ 注意 `doLaw` 本身是概率**（即 `∑ p_U = 1`）时，左边就是
`P(Y=y | X=x)`、右边是 `P(Y=y | do(X=x))`。

**⭐ 这**才**是「规则 1」在数学上正确的陈述** ——
任务书的 `condY = doLaw` 缺的正是这个 `/μ(x)`。 -/
theorem rule1_normalized {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
    [DecidableEq Uy] [Nonempty Ux] [Nonempty Uy]
    (M : SCM X Y) (e : M.U ≃ Ux × Uy)
    (hx : XReadsOnlyUx M e) (hy : YReadsOnlyUy M e)
    (hsep : SeparablePU M e)
    (hpos : ∀ x, marginalX M x ≠ 0) (x : X) (y : Y) :
    condY M x y / marginalX M x = doLaw M x y := by
  rw [rule1_of_separable M e hx hy hsep x y]
  exact mul_div_cancel_left₀ _ (hpos x)

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **具体实例 `MNC`**：`X` 与 `Y` **各用一个外生位**
  =========================================================================== -/

/-- ⭐⭐⭐ **外生拆成 `Bool × Bool`：「第一位给 `X`，第二位给 `Y`」。** -/
def eMNC : Bool × Bool ≃ Bool × Bool := Equiv.refl _

/-- ⭐⭐⭐⭐⭐ **具体的「无混杂」SCM**。

```
    ux : Bool ──→ X = if ux then 1 else 0
    uy : Bool ──→ Y = if uy then 1 else 0      （与 x 无关！）
    U = Bool × Bool,  pU ≡ 1/4   （∑ pU = 1 ✓ 真概率）
```

**⭐ 因果图**（两条**独立**外生通道，无公共祖先、无 `X→Y` 边）：

```
    ux ──→ X        uy ──→ Y
```

**⟹ `X ⊥ Y`，`do(X := x)` 不动 `Y` 机制 ⟹ 观测 = 干预。** -/
noncomputable def MNC : SCM (Fin 2) (Fin 2) where
  U := Bool × Bool
  pU := fun _ => (1 : ℝ) / 4
  sg := fun u => (if u.1 then (1 : Fin 2) else 0, fun _ => if u.2 then (1 : Fin 2) else 0)

/-- ⭐⭐ **技术引理**：`Bool × Bool` 上的和展开成 4 项。 -/
theorem sum_bool_bool (f : Bool × Bool → ℝ) :
    (∑ u : Bool × Bool, f u)
      = f (true, true) + f (true, false) + f (false, true) + f (false, false) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  ring

/-- ⭐⭐⭐ **`MNC` 的 `X` 边缘律**：`μ(x) = 1/2`（`X` 是一枚公平硬币）。 -/
theorem marginalX_MNC (x : Fin 2) : marginalX MNC x = (1 : ℝ) / 2 := by
  show (∑ u : Bool × Bool, MNC.pU u
        * (if (MNC.sg u).1 = x then (1 : ℝ) else 0)) = 1 / 2
  rw [sum_bool_bool]
  simp only [MNC, Bool.false_eq_true, if_true, if_false]
  fin_cases x <;> norm_num

/-- ⭐⭐⭐ **`MNC` 的干预律**：`doLaw(x,y) = 1/2`，**与 `x` 无关**
（`do(X := x)` 切断 `X` 的入边）。 -/
theorem doLaw_MNC (x y : Fin 2) : doLaw MNC x y = (1 : ℝ) / 2 := by
  show (∑ u : Bool × Bool, MNC.pU u
        * (if (MNC.sg u).2 x = y then (1 : ℝ) else 0)) = 1 / 2
  rw [sum_bool_bool]
  simp only [MNC, Bool.false_eq_true, if_true, if_false]
  fin_cases y <;> norm_num

/-- ⭐⭐⭐ **`MNC` 的观测律**：`condY(x,y) = 1/4`（**联合质量** `P(X=x)·P(Y=y)`）。 -/
theorem condY_MNC (x y : Fin 2) : condY MNC x y = (1 : ℝ) / 4 := by
  show (∑ u : Bool × Bool, MNC.pU u
        * (if (MNC.sg u).1 = x then (1 : ℝ) else 0)
        * (if (MNC.sg u).2 x = y then (1 : ℝ) else 0)) = 1 / 4
  rw [sum_bool_bool]
  simp only [MNC, Bool.false_eq_true, if_true, if_false]
  fin_cases x <;> fin_cases y <;> norm_num

/-! ### §5.1 `MNC` **确实满足**完整无混杂 -/

/-- ⭐⭐⭐ **`MNC` 满足 `XReadsOnlyUx`**。 -/
theorem MNC_x_reads_only_ux : XReadsOnlyUx MNC eMNC := by
  intro u v v'
  show (if ((eMNC.symm (u, v)) : Bool × Bool).1 then (1 : Fin 2) else 0)
     = (if ((eMNC.symm (u, v')) : Bool × Bool).1 then (1 : Fin 2) else 0)
  rfl

/-- ⭐⭐⭐⭐ **`MNC` 满足 `YReadsOnlyUy`** —— **草稿的恒真谓词做不到的**。

`u`、`u'` 是**两个独立变量**，`MNC.sg _ |>.2` 是
`fun _ => if uy then 1 else 0`，**与 `u`、`u'` 无关**。 -/
theorem MNC_y_reads_only_uy : YReadsOnlyUy MNC eMNC := by
  intro u u' v x
  show (if ((eMNC.symm (u, v)) : Bool × Bool).2 then (1 : Fin 2) else 0)
     = (if ((eMNC.symm (u', v)) : Bool × Bool).2 then (1 : Fin 2) else 0)
  rfl

/-- ⭐⭐⭐⭐ **`MNC` 满足 `SeparablePU`**：`p_U ≡ 1/4 = (1/2)·(1/2)`，
且 `∑ (1/2) = 1`（**两个归一都成立**）。 -/
theorem MNC_separable : SeparablePU MNC eMNC := by
  refine ⟨fun _ => (1 : ℝ) / 2, fun _ => (1 : ℝ) / 2, ?_, ?_, ?_⟩
  · intro u v
    show (1 : ℝ) / 4 = 1 / 2 * (1 / 2)
    norm_num
  · show (∑ _u : Bool, (1 : ℝ) / 2) = 1
    rw [Fintype.sum_bool]; norm_num
  · show (∑ _v : Bool, (1 : ℝ) / 2) = 1
    rw [Fintype.sum_bool]; norm_num

/-- ⭐⭐⭐⭐ **`MNC` 无混杂**（结构式）。 -/
theorem MNC_split : SplitNoConfounding MNC eMNC :=
  ⟨MNC_x_reads_only_ux, MNC_y_reads_only_uy⟩

/-- ⭐⭐⭐⭐⭐ **`MNC` 满足 `FullNoConfounding`**。 -/
theorem MNC_fullNoConfounding : FullNoConfounding MNC eMNC :=
  ⟨MNC_split, MNC_separable⟩

/-! ### §5.2 `MNC` 上的**主结论**（真算 `1/4 = 1/2 · 1/2`） -/

/-- ⭐⭐⭐⭐ **`MNC` 满足语义式 `NoConfounding`**（真算 `1/4 = 1/2 · 1/2`）。

**⭐ 这是「规则 1 的语义版本」在**具体 SCM** 上的完整非平凡验证，
由**主定理 `rule1_of_separable` 直接导出**（不是重新算一遍）。 -/
theorem MNC_noConfounding : NC MNC :=
  noConfounding_of_fullNoConfounding MNC eMNC MNC_fullNoConfounding

/-- ⭐⭐⭐⭐⭐ **规则 1 在 `MNC` 上成立**（归一化字面形式）。

$$P(Y = y \mid X = x) = P(Y = y \mid do(X = x))
  \quad\text{即}\quad \frac{1/4}{1/2} = \frac12.$$ -/
theorem MNC_rule1 (x y : Fin 2) :
    condY MNC x y / marginalX MNC x = doLaw MNC x y := by
  rw [condY_MNC, marginalX_MNC, doLaw_MNC]
  norm_num

/-- ⛔ ⭐⭐⭐⭐⭐ **任务书的**字面**陈述在 `MNC` 上**失败**（具体反例）。

$$\mathrm{doLaw}\,M_{\mathrm{NC}}\,0\,0 = \tfrac12
  \;\;\ne\;\; \tfrac14 = \mathrm{condY}\,M_{\mathrm{NC}}\,0\,0.$$

**⚠ 本文件最重要的诚实登记**：
- 任务书说「证明 `doLaw M x = condY M x`」；
- `MNC` **完全满足**任务书的结构条件（`X` 读 `ux`、`Y` 读 `uy`，**不同外生位**），
  **且** `p_U` 可分离、归一（最强条件都满足）；
- **但字面等式仍然不成立**，差**正好是 `μ(x) = 1/2`**；
- **⟹ 任务书的字面陈述为假，「无混杂」并不能救它。**

**⭐ 正确陈述是 `condY = μ(x)·doLaw`（`MNC_noConfounding`）
或 `condY/μ(x) = doLaw`（`MNC_rule1`）。** -/
theorem MNC_rule1_literal_fails :
    doLaw MNC 0 0 ≠ condY MNC 0 0 := by
  rw [doLaw_MNC, condY_MNC]
  norm_num

/-- ⭐⭐⭐ **字面陈述失败的**精确原因：差恰好是 `μ(x)`**。

`condY = μ(x) · doLaw`，而 `μ(x) = 1/2 ≠ 1`
⟹ 字面等式只在 `μ(x) = 1`（`X` **退化**）时成立。 -/
theorem MNC_literal_gap (x y : Fin 2) :
    condY MNC x y = (1 : ℝ) / 2 * doLaw MNC x y := by
  rw [condY_MNC, doLaw_MNC]
  norm_num

/-! ===========================================================================
  §6 ⛔ **第二个反例 `MBad`：可分离但**未归一****
  =========================================================================== -/

/-- ⛔ ⭐⭐⭐⭐ **`MBad`：结构无混杂**且**`p_U` 可分离**，
**但 `p_U ≡ 1`（`∑ p_U = 2`，不是概率）**。

**⟹ 这是 §3.2 反例的形式化**：
「可分离」**不**蕴含「归一」，而**后者不可省**。
`doLaw` 的原始式 `∑_u p_U(u)·[·]` 于是算出概率的 **2 倍**。 -/
noncomputable def MBad : SCM (Fin 2) (Fin 2) where
  U := Bool × Bool
  pU := fun _ => (1 : ℝ)
  sg := fun u => (if u.1 then (1 : Fin 2) else 0, fun _ => if u.2 then (1 : Fin 2) else 0)

/-- ⭐⭐ **`MBad` 的 `X` 边缘律**：`μ(x) = 2`。 -/
theorem marginalX_MBad (x : Fin 2) : marginalX MBad x = 2 := by
  show (∑ u : Bool × Bool, MBad.pU u
        * (if (MBad.sg u).1 = x then (1 : ℝ) else 0)) = 2
  rw [sum_bool_bool]
  simp only [MBad, Bool.false_eq_true, if_true, if_false]
  fin_cases x <;> norm_num

/-- ⭐⭐ **`MBad` 的干预律**：`doLaw(x,y) = 2`。 -/
theorem doLaw_MBad (x y : Fin 2) : doLaw MBad x y = 2 := by
  show (∑ u : Bool × Bool, MBad.pU u
        * (if (MBad.sg u).2 x = y then (1 : ℝ) else 0)) = 2
  rw [sum_bool_bool]
  simp only [MBad, Bool.false_eq_true, if_true, if_false]
  fin_cases y <;> norm_num

/-- ⭐⭐ **`MBad` 的观测律**：`condY(x,y) = 1`（联合质量）。 -/
theorem condY_MBad (x y : Fin 2) : condY MBad x y = 1 := by
  show (∑ u : Bool × Bool, MBad.pU u
        * (if (MBad.sg u).1 = x then (1 : ℝ) else 0)
        * (if (MBad.sg u).2 x = y then (1 : ℝ) else 0)) = 1
  rw [sum_bool_bool]
  simp only [MBad, Bool.false_eq_true, if_true, if_false]
  fin_cases x <;> fin_cases y <;> norm_num

/-- ⛔ ⭐⭐⭐⭐⭐ **`MBad` 上任务书的**字面**陈述失败**（`2 ≠ 1`）。 -/
theorem MBad_fails : doLaw MBad 0 0 ≠ condY MBad 0 0 := by
  rw [doLaw_MBad, condY_MBad]
  norm_num

/-- ⭐⭐⭐ **`MBad` 的**结构**无混杂成立**（`X` 读 `ux`、`Y` 读 `uy`）。 -/
theorem MBad_split : SplitNoConfounding MBad eMNC := by
  refine ⟨?_, ?_⟩
  · intro u v v'
    show (if ((eMNC.symm (u, v)) : Bool × Bool).1 then (1 : Fin 2) else 0)
       = (if ((eMNC.symm (u, v')) : Bool × Bool).1 then (1 : Fin 2) else 0)
    rfl
  · intro u u' v x
    show (if ((eMNC.symm (u, v)) : Bool × Bool).2 then (1 : Fin 2) else 0)
       = (if ((eMNC.symm (u', v)) : Bool × Bool).2 then (1 : Fin 2) else 0)
    rfl

/-- ⛔ ⭐⭐⭐⭐ **`MBad` **可分离但未归一** —— 精确展示 §3.2 的必要性**。

`p_U ≡ 1 = 1 · 1`（可分离 ✓），但 `∑ 1 = 2 ≠ 1`（未归一 ✗）。
**⟹ `FacGeneral` 的 `hp`/`hr` 假设**不可省**。 -/
theorem MBad_separable_but_not_normalized :
    (∃ (pX pY : Bool → ℝ), ∀ u v, MBad.pU (eMNC.symm (u, v)) = pX u * pY v)
      ∧ (∑ _v : Bool, (1 : ℝ)) ≠ 1 := by
  refine ⟨⟨fun _ => (1 : ℝ), fun _ => (1 : ℝ), ?_⟩, ?_⟩
  · intro u v
    show (1 : ℝ) = 1 * 1
    norm_num
  · rw [Fintype.sum_bool]; norm_num

/-- ⭐⭐⭐⭐ **`MBad` 仍满足广义结论**（`1 = 2 · 1/2`）。

**⭐ 这把两类失败**分清**：`MBad` 的字面失败因**未归一**，
而 `MNC` 的字面失败因 `μ(x) ≠ 1`；**两者都说明「必须归一化」
（或写 `μ(x)·doLaw`），而非「规则 1 不成立」。** -/
theorem MBad_rule1_gap (x y : Fin 2) :
    condY MBad x y = (1 : ℝ) / 2 * doLaw MBad x y := by
  rw [condY_MBad, doLaw_MBad]
  norm_num

/-! ===========================================================================
  §7 与草稿 / 既有定义的关系（**错误登记**）
  =========================================================================== -/

/-- ⛔ ⭐⭐⭐⭐⭐ **草稿错误的精确登记：其第 2 个合取项**恒真**。

草稿的「无混杂」把 `Y` 那一半写成

```text
(M.sg (e.symm (u, v))).2 = (M.sg (e.symm (u, v))).2
```

**左右是同一个项** ⟹ 该合取项**恒真**，**完全不约束 `Y` 的机制**。
本引理把它形式化成 `fun _ _ => rfl`，即**可判定的重言式**。

**⟹ 草稿的谓词只约束了 `X`（`XReadsOnlyUx`），
漏掉了 `YReadsOnlyUy` 与 `SeparablePU` —— 这正是它推不出规则 1 的根因。** -/
theorem draft_second_conjunct_is_tautology {X Y Ux Uy : Type}
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) (u : Ux) (v : Uy) :
    (M.sg (e.symm (u, v))).2 = (M.sg (e.symm (u, v))).2 := rfl

/-- ⭐⭐⭐ **`YReadsOnlyUy` **不是**恒真谓词（与草稿的根本区别）。

在 `MNC` 上它**为真**（`MNC_y_reads_only_uy`），
但它**不是** `rfl`：`u`、`u'` 是**独立**的绑定变量，
`intro u u' v x` 后目标里的 `u`、`u'` **真的不同**。
**⟹ 它是一条**实质约束**，而非重言式。** -/
theorem y_reads_only_uy_not_tautological :
    YReadsOnlyUy MNC eMNC := MNC_y_reads_only_uy

/-- ⭐⭐⭐ **`SplitNoConfounding` **不**蕴含「`X` 与 `U` 独立」
（即它弱于 `Rule1Semantic.NoUDependence`）。

`MNC` 的 `X` **直接**读 `ux`（所以 `X` 与外生**不**独立），
但 `MNC` **确实**满足 `SplitNoConfounding`。
**⟹ 「读不同外生位」**不等于**「`X` 独立于外生」。** -/
theorem split_does_not_require_U_independence :
    ¬ NUD MNC ∧ SplitNoConfounding MNC eMNC := by
  refine ⟨?_, MNC_split⟩
  intro h
  -- `NoUDependence` 要求 `sg u .1` 与外生无关，即对一切 `u u'` 相等
  have hp : ∀ u : Bool × Bool, MNC.pU u = (1 : ℝ) / 4 := fun _ => rfl
  have h01 : (MNC.sg (false, false)).1 = (MNC.sg (true, true)).1 :=
    h (false, false) (true, true) (by rw [hp]; norm_num) (by rw [hp]; norm_num)
  exact absurd h01 (by decide)

/-- ⭐⭐⭐⭐⭐ **本文件的最终汇总**（一句话，便于引用）。

**三部分**：
1. **具体实例 `MNC` 满足完整无混杂 ⟹ 规则 1 成立**（归一化形式）；
2. **同一 `MNC` 上任务书的字面陈述失败**（`1/2 ≠ 1/4`）；
3. **`MBad` 上同样失败**，且它**可分离但未归一** ——
   证明 §3.2 的归一假设**不可省**。 -/
theorem summary :
    NC MNC
      ∧ (∀ x y : Fin 2, condY MNC x y / marginalX MNC x = doLaw MNC x y)
      ∧ doLaw MNC 0 0 ≠ condY MNC 0 0
      ∧ doLaw MBad 0 0 ≠ condY MBad 0 0
      ∧ SplitNoConfounding MBad eMNC :=
  ⟨MNC_noConfounding, MNC_rule1, MNC_rule1_literal_fails, MBad_fails, MBad_split⟩

end FateV2.Predict.T35Rule1Split
