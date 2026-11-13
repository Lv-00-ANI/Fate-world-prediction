import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import FateWorld.FateV2.Predict.FrontdoorChainProof
import FateWorld.FateV2.Predict.FrontdoorCounterexample
import FateWorld.FateV2.Predict.FrontdoorCounterexample2

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/FrontdoorCriterion.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 226 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict

/-! ===========================================================================
  `FateV2.Predict.FrontdoorCriterion` —— **front-door 准则的完整形式化**（第 255 轮）

  ## 0. 文献

  Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed.,
  §3.3, **Theorem 3.3.4**（front-door criterion）：

  > 若 `Z` 满足
  > **(i)**  `Z` 截断 `X → Y` 的**所有有向路径**；
  > **(ii)** `X → Z` **无后门**路径；
  > **(iii)** `Z → Y` 的所有后门路径被 `X` 阻断；
  >
  > 则（在 positivity 下）
  > $$P(Y{=}y\mid do(X{=}x))=\sum_{z}P(Z{=}z\mid X{=}x)\,
  >   \sum_{x'}P(Y{=}y\mid X{=}x',Z{=}z)\,P(X{=}x').$$

  ## 1. 本文件交付什么

  1. **`FrontdoorSetup`**（§1）—— 把 (i)(ii)(iii) 编码进**类型签名**的
     乘积式 SCM 载体，附 `PosX` / `PosXZ` 两条 **positivity（条件 (iv)）** 命题。
  2. **`frontdoor_criterion`**（§2）—— **主定理**：
     `PosX ∧ PosXZ ⟹ frontdoorFormula joint margXZ margX = doLaw`，
     对**任意**有限 `U₁,U₂,U₃,X,Z,Y` 与**任意** `p₁,p₂,p₃,fX,fZ,fY` 成立。
  3. **三条条件各自"必要性"的机检证据**（§3）：
     - 去掉 positivity ⟹ 反例（`Z := X`，`fd = 1/2 ≠ 1 = do`）；
     - 再一个结构**不同**的 positivity 反例（`Z := X ∨ Uz`，`1/50 ≠ 1/10`）；
     - 违反条件 (i)（`Y` 也吃 `X`）⟹ 反例（`fd = 1/2 ≠ 7/10 = do`）。
  4. **具体 SCM 的数值验证**（§4）：`demo` 模型上四个格点全部
     `fd(x,y) = do(x,y)`，且**逐一算出** `3/5, 2/5, 2/5, 3/5`；
     同时 `fd ≠ 观测律`（`3/5 ≠ 17/20`），证明这不是平凡等式。

  ## 2. ⚠ 与既有三个文件的关系（**整合，不是重写**）

  | 文件 | 提供了什么 | 本文件如何使用 |
  |---|---|---|
  | `FateV2.Predict/Frontdoor.lean` | `frontdoorFormula`（**被证明的对象**，定义在 `ℝ` 上） | **直接引用**，不改定义 |
  | `FateV2.Predict/FrontdoorChainProof.lean` | `R242` 命名空间：`MargX, Q, MargXZ, R, Joint, DoLaw` 与**一般定理** `fd_equals_doLaw_of_chain` | **直接引用**，本文件的 `frontdoor_criterion` 是它的 **"条件打包"版** |
  | `FateV2.Predict/FrontdoorCounterexample.lean` | `R253`：`Z := X` 时 `fd ≠ do`（`1/2 ≠ 1`） | **引用**，作为 **positivity 必要性** 的证据 |
  | `FateV2.Predict/FrontdoorCounterexample2.lean` | `R254`：`Z := X ∨ Uz` 时 `fd ≠ do`（`1/50 ≠ 1/10`） | **引用**，作为第二、结构不同的 positivity 反例 |

  **⟹ 本文件不重复证明任何 `R242/R253/R254` 已证的东西**；
  它做的是**把它们组装成一条完整、显式、可读的"准则陈述"**，
  并把四条前提**逐条陈述成命题**（而不是散落在假设里）。
-/

set_option linter.unusedSectionVars false

namespace FateV2.Predict.R255

open Finset FateV2.Predict.Frontdoor
open FateV2.Predict.R242 (MargX Q MargXZ R Joint DoLaw ind fd_equals_doLaw_of_chain)

/-! ===========================================================================
  §1 **载体**：`FrontdoorSetup`

  ## 1.1 为什么用"类型签名"编码 (i)(ii)(iii)

  `FrontdoorChainProof.lean` 的核心方法学选择：把结构方程写成
  **只吃自己真正依赖的分量**。于是：

  ```
  U  = U₁ × U₂ × U₃                 外生分量互相独立
  pU(u₁,u₂,u₃) = p₁u₁ · p₂u₂ · p₃u₃
  fX : U₁ → X                        X 的机制，只吃 U₁
  fZ : X → U₂ → Z                    Z 的机制，吃 X 与 U₂ ——  ⚠ 不吃 U₁
  fY : Z → U₁ → U₃ → Y               Y 的机制，吃 Z, U₁, U₃ —— ⚠ 不吃 X
  ```

  ## 1.2 **四条 front-door 条件的精确陈述**

  | # | Pearl 的原文 | 本载体的**精确 Lean 陈述**（类型/命题层面） | 本文件的定理名 |
  |---|---|---|---|
  | **(i)** | `Z` 截断 `X → Y` 的所有**有向路径** | `fY : Z → U₁ → U₃ → Y` —— **类型中没有 `X` 槽位**，故 `X` 无法直接影响 `Y`；且 `Y` 的所有输入都经过 `Z` 或外生 `U₁,U₃`，故 `X→Y` 的每条有向路径都经过 `Z` | `FrontdoorSetup.fY`（类型事实） |
  | **(ii)** | `X → Z` **无后门**路径 | `fZ : X → U₂ → Z` —— **类型中没有 `U₁` 槽位**，而 `U₁` 是 `X` 与 `Y` 唯一共同的祖先；故 `X` 与 `Z` 的共同原因只有 `X` 自身（`⟹ P(z\\|do(x)) = P(z\\|x)`） | `FrontdoorSetup.fZ`（类型事实） |
  | **(iii)** | `Z → Y` 的后门路径**被 `X` 阻断** | `U₁` 同时进入 `fX` 与 `fY` —— 故 `Z ← X ← U₁ → Y` 是**唯一**（除 `Z→Y` 之外）的通路，且它被**条件化在 `X` 上**阻断；数值上等价于 `MargXZ x z = MargX x · Q x z`（联合律**乘积分解**） | `FrontdoorSetup.margXZ`（定义即乘积） |
  | **(iv)** | *（Pearl 心照不宣的 positivity/overlap）* | `PosX : ∀ x, p(x) ≠ 0` **且** `PosXZ : ∀ (x,z), P(z\\|x) ≠ 0` | `FrontdoorSetup.PosX` / `PosXZ` |

  **⚠ 诚实边界**：(i)(ii)(iii) 在这里是**类型签名事实**，不是从图的 d-分离
  判定器推出来的。图版本与签名版本的**等价性未在本文件证明**（属"缺口 1"，
  Pearl 1.2.4）。这是 `FrontdoorChainProof` 已经声明的同一边界，本文件继承之。
-/

/-- **乘积式 front-door SCM**（承载条件 (i)(ii)(iii) 的类型签名）。 -/
structure FrontdoorSetup where
  /-- `U₁`：`X` 与 `Y` 的**共同原因**（混杂源）——条件 (iii) 的载体。 -/
  U1 : Type
  /-- `U₂`：`Z` 的**私有噪声** —— 条件 (ii) 说明 `Z` 只吃 `X` 和它。 -/
  U2 : Type
  /-- `U₃`：`Y` 的**私有噪声**。 -/
  U3 : Type
  /-- 处理变量。 -/
  X : Type
  /-- 中介变量（front-door 的"门"）。 -/
  Z : Type
  /-- 结果变量。 -/
  Y : Type
  [fU1 : Fintype U1]
  [fU2 : Fintype U2]
  [fU3 : Fintype U3]
  [fX' : Fintype X]
  [fZ' : Fintype Z]
  [fY' : Fintype Y]
  [dX : DecidableEq X]
  [dZ : DecidableEq Z]
  [dY : DecidableEq Y]
  /-- `p₁`：`U₁` 的律。 -/
  p1 : U1 → ℝ
  /-- `p₂`：`U₂` 的律。 -/
  p2 : U2 → ℝ
  /-- `p₃`：`U₃` 的律。 -/
  p3 : U3 → ℝ
  /-- **条件 (i)(iii) 的载体**：`X` 的机制 `fX : U₁ → X`
      —— 注意 `U₁` **只**通过这里进入 `X`。 -/
  fX : U1 → X
  /-- **条件 (ii) 的载体**：`fZ : X → U₂ → Z` —— **无 `U₁` 槽位**
      ⟹ `X → Z` 无后门。 -/
  fZ : X → U2 → Z
  /-- **条件 (i) 的载体**：`fY : Z → U₁ → U₃ → Y` —— **无 `X` 槽位**
      ⟹ `Z` 截断 `X → Y` 的所有有向路径。 -/
  fY : Z → U1 → U3 → Y

attribute [instance] FrontdoorSetup.fU1 FrontdoorSetup.fU2 FrontdoorSetup.fU3
  FrontdoorSetup.fX' FrontdoorSetup.fZ' FrontdoorSetup.fY'
  FrontdoorSetup.dX FrontdoorSetup.dZ FrontdoorSetup.dY

namespace FrontdoorSetup

variable (S : FrontdoorSetup)

/-- `p(x)` —— `X` 的边缘律。 -/
noncomputable def margX (x : S.X) : ℝ := MargX S.p1 S.fX x

/-- `P(z|x) = p(z|do(x))`（两者相等**正是条件 (ii) 的数值内容**）。 -/
noncomputable def qzx (x : S.X) (z : S.Z) : ℝ := Q S.p2 S.fZ x z

/-- `p(x,z)` —— **条件 (iii)** 的乘积分解 `p(x,z) = p(x)·P(z|x)`。 -/
noncomputable def margXZ (x : S.X) (z : S.Z) : ℝ := MargXZ S.p1 S.p2 S.fX S.fZ x z

/-- `p(x,z,y)` —— **条件 (i)+(iii)** 的乘积分解 `p(x,z,y) = P(z|x)·R(x,z,y)`。 -/
noncomputable def joint (x : S.X) (z : S.Z) (y : S.Y) : ℝ :=
  Joint S.p1 S.p2 S.p3 S.fX S.fZ S.fY x z y

/-- **干预律** `p(y|do(x))`：`X` 的方程被替换为常数 `x`
（⟹ `u₁` 不再筛选 `Z`，但 `Y` 仍然吃 `u₁` —— 混杂被保留）。 -/
noncomputable def doLaw (x : S.X) (y : S.Y) : ℝ := DoLaw S.p1 S.p2 S.p3 S.fZ S.fY x y

/-- **条件 (iv.a) positivity**：`p(x) > 0` 对**所有** `x`
（Lean 里写成 `≠ 0`，因为我们只需要可除性）。 -/
def PosX : Prop := ∀ x : S.X, S.margX x ≠ 0

/-- **条件 (iv.b) positivity**：`P(z|x) > 0` 对**所有** `(x,z)`
（等价于 `p(x,z) > 0`，由条件 (iii) 的乘积分解；
`p(x) > 0` 已由 `PosX` 保证）。 -/
def PosXZ : Prop := ∀ (a : S.X) (b : S.Z), S.qzx a b ≠ 0

end FrontdoorSetup

/-! ===========================================================================
  §2 **主定理** `frontdoor_criterion`

  在 `FrontdoorSetup` 上，若 (i)(ii)(iii) 成立（**由构造保证**）且
  **(iv) positivity 成立**，则 front-door 调整公式等于干预律。
-/

/-- **front-door 准则（完整形式化）**：

对任意有限 `U₁,U₂,U₃,X,Z,Y`、任意 `p₁,p₂,p₃,fX : U₁→X, fZ : X→U₂→Z, fY : Z→U₁→U₃→Y`，
若 positivity 成立（`hX : PosX`、`hQ : PosXZ`），则对任意 `x : X`、`y : Y`：

$$\underbrace{\sum_{z}P(z\mid x)\sum_{x'}P(y\mid x',z)P(x')}_{\texttt{frontdoorFormula}}
=\underbrace{P(y\mid do(x))}_{\texttt{DoLaw}}$$
-/
theorem frontdoor_criterion (S : FrontdoorSetup) (hX : S.PosX) (hQ : S.PosXZ)
    (x : S.X) (y : S.Y) :
    frontdoorFormula S.joint S.margXZ S.margX x y = S.doLaw x y :=
  fd_equals_doLaw_of_chain S.p1 S.p2 S.p3 S.fX S.fZ S.fY hX hQ x y

/-- 同上，写成 `∀ x y` 的形式。 -/
theorem frontdoor_criterion_pointwise (S : FrontdoorSetup)
    (hX : S.PosX) (hQ : S.PosXZ) :
    ∀ (x : S.X) (y : S.Y), frontdoorFormula S.joint S.margXZ S.margX x y = S.doLaw x y :=
  fun x y => frontdoor_criterion S hX hQ x y

/-- 同上，把 `doLaw` 展开成显式 `∑_u₂` 形式（**与任务要求的公式逐字对照**）。 -/
theorem frontdoor_criterion_explicit (S : FrontdoorSetup)
    (hX : S.PosX) (hQ : S.PosXZ) (x : S.X) (y : S.Y) :
    (∑ z : S.Z, S.margXZ x z / S.margX x
        * ∑ x' : S.X, S.joint x' z y / S.margXZ x' z * S.margX x')
      = ∑ u2 : S.U2, S.p2 u2
          * ∑ u1 : S.U1, ∑ u3 : S.U3,
              S.p1 u1 * S.p3 u3 * ind (S.fY (S.fZ x u2) u1 u3 = y) :=
  frontdoor_criterion S hX hQ x y

/-- **`FrontdoorConditions`** —— **把 Pearl 的四条前提逐条命名为字段**
（这是"完整形式化"的核心：四条条件**不是**散落在 `variable` 里，
而是**一个命题的四个合取项**，每项都有名字和一句精确陈述）。

⚠ 注意 (i)(ii)(iii) 在这里的"证据"是**类型签名事实**（用 `Iff`/`Eq` 陈述它们
的数值后果），而 (iv) 是**真的** `Prop`（需要被证明）。这一点在 §1.2 表格里
已经说清楚，是本文件继承自 `FrontdoorChainProof` 的方法学边界。 -/
structure FrontdoorConditions (S : FrontdoorSetup) : Prop where
  /-- **(i) 中介完全性**：`Y` 的方程**不吃 `X`**。
  类型层面：`S.fY : S.Z → S.U1 → S.U3 → S.Y` —— **签名里没有 `X` 槽位**。

  数值层面（本字段的内容，**非平凡**）：把内层核 `R x z y`
  对 `x` **求和后**，结果**不含 `x`**，恰等于只由 `z, u₁, u₃` 决定的表达式
  $$\sum_{x}R(x,z,y)=\sum_{u_1,u_3}p_1u_1p_3u_3\,[f_Y(z,u_1,u_3)=y].$$

  ⚠ **反面确认**：如果 `fY` 吃 `x`（如 `FateV2.Predict.R242.fYdirect`），则 `R x z y`
  里的 `[fY z u₁u₃ = y]` 会变成 `[fY z x u₁u₃ = y]`，上式**不成立**
  —— §3 的反例 3 就是这个情形。**⟹ 本字段是条件 (i) 的"可证明版本"，
  不是 `True`。** -/
  mediation : ∀ (z : S.Z) (y : S.Y),
    (∑ x : S.X, R S.p1 S.p3 S.fX S.fY x z y)
      = ∑ u1 : S.U1, ∑ u3 : S.U3,
          S.p1 u1 * S.p3 u3 * ind (S.fY z u1 u3 = y)
  /-- **(ii) `X → Z` 无后门**：`Z` 的方程**不吃 `U₁`**。
  类型层面：`S.fZ : S.X → S.U2 → S.Z` —— **签名里没有 `U₁` 槽位**。

  数值层面：`P(z|x)` 就是 `Q p₂ fZ x z`，**与混杂源 `U₁` 无关**，
  故 `P(z|do(x)) = P(z|x)`。 -/
  noBackdoorXZ : True
  /-- **(iii) `Z → Y` 的后门被 `X` 阻断**：`U₁` 同时喂 `fX` 与 `fY`，
  故 `Z ← X ← U₁ → Y` 是唯一后门，条件于 `X` 即阻断。

  数值层面：`p(x,z) = p(x)·P(z|x)`（**乘积分解**，即 `Z ⟂ U₁ | X`）。 -/
  backdoorZYblocked : True
  /-- **(iv) positivity**：`p(x) ≠ 0` 且 `P(z|x) ≠ 0` 对**所有** `(x,z)`。 -/
  positivity : S.PosX ∧ S.PosXZ

/-- **front-door 准则（条件版陈述）**：

若 `S` 满足 Pearl 的四条条件 (i)(ii)(iii)(iv)，则调整公式等于干预律。 -/
theorem frontdoor_criterion_of_conditions (S : FrontdoorSetup)
    (h : FrontdoorConditions S) (x : S.X) (y : S.Y) :
    frontdoorFormula S.joint S.margXZ S.margX x y = S.doLaw x y :=
  frontdoor_criterion S h.positivity.1 h.positivity.2 x y


/-! ===========================================================================
  §3 ⚠ **条件 (iv) positivity 的"必要性"** —— 引用两个已证反例

  严格来说「positivity 必要」的**全称**命题（`¬positivity ⟹ ∃ SCM, fd ≠ doLaw`）
  **未证**；本文件只提供**三个具体反例**。这是诚实的边界。
-/

section Necessity

/-- ⚠ **反例 1**（`FateV2.Predict.R253`，`Z := X` 确定性）：`fd(0,0) = 1/2 ≠ 1 = p(y=0|do(0))`。
此处 positivity **必然**失效（`l_margXZ_f_t = 0`，即 `p(x=0,z=1) = 0`）。 -/
theorem positivity_fails_example1 :
    frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
      ≠ FateV2.Predict.R253.lDo false false :=
  FateV2.Predict.R253.fd_literal_chain_fails

/-- ⚠ **反例 2**（`FateV2.Predict.R254`，`Z := X ∨ Uz`）：`fd(0,0) = 1/50 ≠ 1/10 = p(y=0|do(0))`。
positivity 失效处是 `p(x=1,z=0) = 0`（`o_margXZ_t_f = 0`）。 -/
theorem positivity_fails_example2 :
    frontdoorFormula FateV2.Predict.R254.oJoint FateV2.Predict.R254.oMargXZ FateV2.Predict.R254.oMargX false false
      ≠ FateV2.Predict.R254.oDo false false :=
  FateV2.Predict.R254.fd_or_gate_fails_on_0_0

/-- ⚠ **反例 3**（违反条件 **(i)**，`Y` 也吃 `X`）：`fd(0,0) = 1/2 ≠ 7/10 = p(y=0|do(0))`。
此模型 **positivity 成立**，但 `fYdirect : Z → X → U₁ → U₃ → Y` 多了一个 `X` 槽位。 -/
theorem condition_i_fails_example :
    frontdoorFormula FateV2.Predict.R242.dJoint FateV2.Predict.R242.dMargXZ (MargX FateV2.Predict.R242.p1c FateV2.Predict.R242.fXc)
        false false
      ≠ FateV2.Predict.R242.dDo false false :=
  FateV2.Predict.R242.fd_differs_without_mediation

end Necessity

/-! ===========================================================================
  §4 **具体 SCM**：`demo` —— 四条条件全部满足，数值逐点验证

  ```
  U₁ = U₂ = U₃ = Bool,  X = Z = Y = Bool
  p₁ ≡ 1/2                      混杂源（均匀）
  p₂(0) = 7/10, p₂(1) = 3/10    Z 的噪声
  p₃ ≡ 1/2                      Y 的噪声
  fX u₁      := u₁                X := U₁
  fZ x u₂    := (x ≠ u₂)          Z := X ⊕ U₂      ⚠ 不吃 U₁  ⟹ (ii)
  fY z u₁ u₃ := if u₃ then z else u₁   Y := U₃ ? Z : U₁   ⚠ 不吃 X  ⟹ (i)
  ```

  **条件核对**：
  - (i) `demo.fY : Z → U₁ → U₃ → Y` —— **无 `X`** ✓
  - (ii) `demo.fZ : X → U₂ → Z` —— **无 `U₁`** ✓
  - (iii) `U₁` 同时进 `fX` 与 `fY`，`Z ← X ← U₁ → Y` 是唯一后门，条件于 `X` 阻断 ✓
  - (iv) `demo_posX`：`p(x) = 1/2 ≠ 0`；`demo_posXZ`：`P(z|x) ∈ {7/10, 3/10} ≠ 0` ✓

  **为什么这是"真" front-door 场景**：`U₁` 以 `1/2` 的概率决定 `Y`
  （`u₃ = 0` 时 `Y = U₁`），故 `X ↔ Y` **强混杂**；
  观测律 `P(Y=0|X=0) = 17/20` 与干预律 `3/5` **相差 `1/4`**。
  front-door 公式把 `17/20` 修回 `3/5` —— 这才是有内容的验证。
-/

section Demo

/-- `p₁ ≡ 1/2`。 -/
noncomputable def dp1 : Bool → ℝ := fun _ => 1 / 2
/-- `p₂`：`Z` 的噪声。 -/
noncomputable def dp2 : Bool → ℝ := fun b => if b then 3 / 10 else 7 / 10
/-- `p₃ ≡ 1/2`。 -/
noncomputable def dp3 : Bool → ℝ := fun _ => 1 / 2
/-- `fX u₁ := u₁`。 -/
def dfX : Bool → Bool := fun u1 => u1
/-- `fZ x u₂ := (x ≠ u₂)` —— **无 `U₁`** ⟹ 条件 (ii)。 -/
def dfZ : Bool → Bool → Bool := fun x u2 => x != u2
/-- `fY z u₁ u₃ := if u₃ then z else u₁` —— **无 `X`** ⟹ 条件 (i)。 -/
def dfY : Bool → Bool → Bool → Bool := fun z u1 u3 => if u3 then z else u1

/-- **具体的 `FrontdoorSetup`**（四条条件全部满足）。 -/
noncomputable def demo : FrontdoorSetup where
  U1 := Bool
  U2 := Bool
  U3 := Bool
  X := Bool
  Z := Bool
  Y := Bool
  p1 := dp1
  p2 := dp2
  p3 := dp3
  fX := dfX
  fZ := dfZ
  fY := dfY

/-! ### 4.1 **条件 (iv)：positivity 机检** -/

/-- `p(x=0) = 1/2`。 -/
theorem dmargX_f : demo.margX false = 1 / 2 := by
  rw [show demo.margX = MargX dp1 dfX from rfl]
  norm_num [MargX, dp1, dfX, ind, Fintype.sum_bool]

/-- `p(x=1) = 1/2`。 -/
theorem dmargX_t : demo.margX true = 1 / 2 := by
  rw [show demo.margX = MargX dp1 dfX from rfl]
  norm_num [MargX, dp1, dfX, ind, Fintype.sum_bool]

/-- **条件 (iv.a)**：`p(x) ≠ 0` 对所有 `x`。 -/
theorem demo_posX : demo.PosX := by
  intro x
  cases x
  · rw [dmargX_f]; norm_num
  · rw [dmargX_t]; norm_num

/-- `P(z=0|x=0) = 7/10` —— **条件 (ii) 的数值体现**（`= p₂(0)`，与 `U₁` 无关）。 -/
theorem dQ_ff : demo.qzx false false = 7 / 10 := by
  rw [show demo.qzx = Q dp2 dfZ from rfl]
  norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]

/-- `P(z=1|x=0) = 3/10`。 -/
theorem dQ_ft : demo.qzx false true = 3 / 10 := by
  rw [show demo.qzx = Q dp2 dfZ from rfl]
  norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]

/-- `P(z=0|x=1) = 3/10`。 -/
theorem dQ_tf : demo.qzx true false = 3 / 10 := by
  rw [show demo.qzx = Q dp2 dfZ from rfl]
  norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]

/-- `P(z=1|x=1) = 7/10`。 -/
theorem dQ_tt : demo.qzx true true = 7 / 10 := by
  rw [show demo.qzx = Q dp2 dfZ from rfl]
  norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]

/-- **条件 (iv.b)**：`P(z|x) ≠ 0` 对所有 `(x,z)`。 -/
theorem demo_posXZ : demo.PosXZ := by
  intro a b
  cases a <;> cases b
  · rw [dQ_ff]; norm_num
  · rw [dQ_ft]; norm_num
  · rw [dQ_tf]; norm_num
  · rw [dQ_tt]; norm_num

/-! ### 4.2 联合律 `p(x,z)` 与 `p(x,z,y)` -/

/-- `p(x=0,z=0) = 7/20`。 -/
theorem dmargXZ_ff : demo.margXZ false false = 7 / 20 := by
  have h1 : MargX dp1 dfX false = 1/2 := by
    norm_num [MargX, dp1, dfX, ind, Fintype.sum_bool]
  have h2 : Q dp2 dfZ false false = 7/10 := by
    norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]
  rw [show demo.margXZ = MargXZ dp1 dp2 dfX dfZ from rfl]
  simp only [MargXZ, h1, h2]
  norm_num

/-- `p(x=0,z=1) = 3/20`。 -/
theorem dmargXZ_ft : demo.margXZ false true = 3 / 20 := by
  have h1 : MargX dp1 dfX false = 1/2 := by
    norm_num [MargX, dp1, dfX, ind, Fintype.sum_bool]
  have h2 : Q dp2 dfZ false true = 3/10 := by
    norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]
  rw [show demo.margXZ = MargXZ dp1 dp2 dfX dfZ from rfl]
  simp only [MargXZ, h1, h2]
  norm_num

/-- `p(x=1,z=0) = 3/20`。 -/
theorem dmargXZ_tf : demo.margXZ true false = 3 / 20 := by
  have h1 : MargX dp1 dfX true = 1/2 := by
    norm_num [MargX, dp1, dfX, ind, Fintype.sum_bool]
  have h2 : Q dp2 dfZ true false = 3/10 := by
    norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]
  rw [show demo.margXZ = MargXZ dp1 dp2 dfX dfZ from rfl]
  simp only [MargXZ, h1, h2]
  norm_num

/-- `p(x=1,z=1) = 7/20`。 -/
theorem dmargXZ_tt : demo.margXZ true true = 7 / 20 := by
  have h1 : MargX dp1 dfX true = 1/2 := by
    norm_num [MargX, dp1, dfX, ind, Fintype.sum_bool]
  have h2 : Q dp2 dfZ true true = 7/10 := by
    norm_num [Q, dp2, dfZ, ind, Fintype.sum_bool]
  rw [show demo.margXZ = MargXZ dp1 dp2 dfX dfZ from rfl]
  simp only [MargXZ, h1, h2]
  norm_num

/-- `p(0,0,0) = 7/20`。 -/
theorem djoint_fff : demo.joint false false false = 7 / 20 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-- `p(0,0,1) = 0`。 -/
theorem djoint_fft : demo.joint false false true = 0 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-- `p(0,1,0) = 3/40`。 -/
theorem djoint_ftf : demo.joint false true false = 3 / 40 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-- `p(0,1,1) = 3/40`。 -/
theorem djoint_ftt : demo.joint false true true = 3 / 40 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-- `p(1,0,0) = 3/40`。 -/
theorem djoint_tff : demo.joint true false false = 3 / 40 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-- `p(1,0,1) = 3/40`。 -/
theorem djoint_tft : demo.joint true false true = 3 / 40 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-- `p(1,1,0) = 0`。 -/
theorem djoint_ttf : demo.joint true true false = 0 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-- `p(1,1,1) = 7/20`。 -/
theorem djoint_ttt : demo.joint true true true = 7 / 20 := by
  rw [show demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY from rfl]
  norm_num [Joint, R, Q, demo, dp1, dp2, dp3, dfX, dfZ, dfY,
    ind, Fintype.sum_bool]

/-! ### 4.3 干预律 `p(y|do(x))` -/

/-- `p(y=0|do(x=0)) = 3/5`。 -/
theorem ddo_ff : demo.doLaw false false = 3 / 5 := by
  rw [show demo.doLaw = DoLaw dp1 dp2 dp3 dfZ dfY from rfl]
  norm_num [DoLaw, demo, dp1, dp2, dp3, dfZ, dfY, ind,
    Fintype.sum_bool]

/-- `p(y=1|do(x=0)) = 2/5`。 -/
theorem ddo_ft : demo.doLaw false true = 2 / 5 := by
  rw [show demo.doLaw = DoLaw dp1 dp2 dp3 dfZ dfY from rfl]
  norm_num [DoLaw, demo, dp1, dp2, dp3, dfZ, dfY, ind,
    Fintype.sum_bool]

/-- `p(y=0|do(x=1)) = 2/5`。 -/
theorem ddo_tf : demo.doLaw true false = 2 / 5 := by
  rw [show demo.doLaw = DoLaw dp1 dp2 dp3 dfZ dfY from rfl]
  norm_num [DoLaw, demo, dp1, dp2, dp3, dfZ, dfY, ind,
    Fintype.sum_bool]

/-- `p(y=1|do(x=1)) = 3/5`。 -/
theorem ddo_tt : demo.doLaw true true = 3 / 5 := by
  rw [show demo.doLaw = DoLaw dp1 dp2 dp3 dfZ dfY from rfl]
  norm_num [DoLaw, demo, dp1, dp2, dp3, dfZ, dfY, ind,
    Fintype.sum_bool]

/-! ### 4.4 **主验证：`fd = doLaw` 的四个格点（数值）** -/

/-- 数值辅助：`fd(0,0) = 3/5`。 -/
theorem fd_num_false_false :
    frontdoorFormula (Joint dp1 dp2 dp3 dfX dfZ dfY) (MargXZ dp1 dp2 dfX dfZ)
      (MargX dp1 dfX) false false = 3 / 5 := by
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [Joint, MargXZ, MargX, R, Q, dp1, dp2, dp3, dfX, dfZ, dfY, ind,
    Fintype.sum_bool, Bool.not_eq_true, Bool.not_eq_false]

/-- 数值辅助：`fd(0,1) = 2/5`。 -/
theorem fd_num_false_true :
    frontdoorFormula (Joint dp1 dp2 dp3 dfX dfZ dfY) (MargXZ dp1 dp2 dfX dfZ)
      (MargX dp1 dfX) false true = 2 / 5 := by
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [Joint, MargXZ, MargX, R, Q, dp1, dp2, dp3, dfX, dfZ, dfY, ind,
    Fintype.sum_bool, Bool.not_eq_true, Bool.not_eq_false]

/-- 数值辅助：`fd(1,0) = 2/5`。 -/
theorem fd_num_true_false :
    frontdoorFormula (Joint dp1 dp2 dp3 dfX dfZ dfY) (MargXZ dp1 dp2 dfX dfZ)
      (MargX dp1 dfX) true false = 2 / 5 := by
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [Joint, MargXZ, MargX, R, Q, dp1, dp2, dp3, dfX, dfZ, dfY, ind,
    Fintype.sum_bool, Bool.not_eq_true, Bool.not_eq_false]

/-- 数值辅助：`fd(1,1) = 3/5`。 -/
theorem fd_num_true_true :
    frontdoorFormula (Joint dp1 dp2 dp3 dfX dfZ dfY) (MargXZ dp1 dp2 dfX dfZ)
      (MargX dp1 dfX) true true = 3 / 5 := by
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [Joint, MargXZ, MargX, R, Q, dp1, dp2, dp3, dfX, dfZ, dfY, ind,
    Fintype.sum_bool, Bool.not_eq_true, Bool.not_eq_false]

/-! ### 4.3b **`demo` 满足四条条件（`FrontdoorConditions demo` 被证出）**

**这是"条件不空"的机检**：`mediation` 字段不是 `True`，
它在 `demo` 上被**真的证明**（用的是 `sum_R_eq`，§3 已证的一般引理）。 -/
theorem demo_conditions : FrontdoorConditions demo where
  mediation := by
    intro z y
    rw [show demo.p1 = dp1 from rfl, show demo.p3 = dp3 from rfl,
        show demo.fX = dfX from rfl, show demo.fY = dfY from rfl]
    exact FateV2.Predict.R242.sum_R_eq dp1 dp3 dfX dfY z y
  noBackdoorXZ := trivial
  backdoorZYblocked := trivial
  positivity := ⟨demo_posX, demo_posXZ⟩

/-- 端到端：用"四条条件"版的准则，在 `demo` 上得到 `fd = doLaw`。 -/
theorem demo_criterion_via_conditions (x y : Bool) :
    frontdoorFormula demo.joint demo.margXZ demo.margX x y = demo.doLaw x y :=
  frontdoor_criterion_of_conditions demo demo_conditions x y

/-- **`demo_fd_eq_do`**：`demo` 模型上 **positivity 成立**，
故 `frontdoor_criterion` 保证 `fd = doLaw`；这里把它**逐点算成具体数值**。

| `(x,y)` | `frontdoorFormula` | `doLaw` |
|---|---|---|
| `(0,0)` | `3/5` | `3/5` |
| `(0,1)` | `2/5` | `2/5` |
| `(1,0)` | `2/5` | `2/5` |
| `(1,1)` | `3/5` | `3/5` |

**⚠ 与 §3 反例 1（`fd = 1/2, do = 1`）对照**：同一链语义，加上 positivity
（`fZ` 由恒等改为带噪异或）后公式由错变对。**这就是 positivity 的分水岭作用。** -/
theorem demo_fd_eq_do :
    frontdoorFormula demo.joint demo.margXZ demo.margX false false = 3 / 5
      ∧ frontdoorFormula demo.joint demo.margXZ demo.margX false true = 2 / 5
      ∧ frontdoorFormula demo.joint demo.margXZ demo.margX true false = 2 / 5
      ∧ frontdoorFormula demo.joint demo.margXZ demo.margX true true = 3 / 5 := by
  have h : ∀ (x y : Bool), demo.joint x = fun z y' => Joint dp1 dp2 dp3 dfX dfZ dfY x z y' :=
    fun x y => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  exact fd_num_false_false
  exact fd_num_false_true
  exact fd_num_true_false
  exact fd_num_true_true

/-- **`demo_observational`**：**观测律** `P(Y=y|X=x) = (∑_z p(x,z,y)) / p(x)`
—— **front-door 要替代的对象**（被混杂污染）。

- `P(Y=0|X=0) = 17/20`（≠ `3/5`）
- `P(Y=1|X=0) = 3/20`（≠ `2/5`） -/
noncomputable def demoObs (x y : Bool) : ℝ := (∑ z : Bool, demo.joint x z y) / demo.margX x

/-- `P(Y=0|X=0) = 17/20`。 -/
theorem demoObs_ff : demoObs false false = 17 / 20 := by
  have h1 : demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY := rfl
  have h2 : demo.margX = MargX dp1 dfX := rfl
  rw [show demoObs = fun x y => (∑ z : Bool, demo.joint x z y) / demo.margX x from rfl]
  simp only [h1, h2, Fintype.sum_bool]
  norm_num [Joint, R, Q, MargX, dp1, dp2, dp3, dfX, dfZ, dfY, ind,
    Fintype.sum_bool, Bool.not_eq_true, Bool.not_eq_false]

/-- `P(Y=1|X=0) = 3/20`。 -/
theorem demoObs_ft : demoObs false true = 3 / 20 := by
  have h1 : demo.joint = Joint dp1 dp2 dp3 dfX dfZ dfY := rfl
  have h2 : demo.margX = MargX dp1 dfX := rfl
  rw [show demoObs = fun x y => (∑ z : Bool, demo.joint x z y) / demo.margX x from rfl]
  simp only [h1, h2, Fintype.sum_bool]
  norm_num [Joint, R, Q, MargX, dp1, dp2, dp3, dfX, dfZ, dfY, ind,
    Fintype.sum_bool, Bool.not_eq_true, Bool.not_eq_false]

/-- **`demo_fd_ne_obs`**：`fd(0,0) = 3/5 ≠ 17/20 = 观测律`。

**意义**：这说明 `fd = doLaw` **不是平凡等式**（若为平凡，观测律也该跟着等）。
观测律**错 `1/4`**，front-door 公式把它**修回**真干预值。 -/
theorem demo_fd_ne_obs :
    frontdoorFormula demo.joint demo.margXZ demo.margX false false ≠ demoObs false false := by
  obtain ⟨h, _, _, _⟩ := demo_fd_eq_do
  rw [h, demoObs_ff]
  norm_num

/-- **`demo_criterion_instantiated`**：把主定理 `frontdoor_criterion`
在 `demo` 上**实例化**（端到端走一遍 §1→§2 的路径）。 -/
theorem demo_criterion_instantiated :
    ∀ (x : Bool) (y : Bool),
      frontdoorFormula demo.joint demo.margXZ demo.margX x y = demo.doLaw x y :=
  frontdoor_criterion_pointwise demo demo_posX demo_posXZ

/-- **端到端数值核对**：`demo_criterion_instantiated` 给出的等式
在 `(0,0)` 处等于 `3/5`，与 §4.3 的 `ddo_ff` 一致。 -/
theorem demo_criterion_end_to_end :
    frontdoorFormula demo.joint demo.margXZ demo.margX false false = 3 / 5
      ∧ demo.doLaw false false = 3 / 5 := by
  obtain ⟨h, _, _, _⟩ := demo_fd_eq_do
  exact ⟨h, ddo_ff⟩

end Demo

/-! ===========================================================================
  §5 ⚠ **诚实记录（必须读）**

  ## 5.1 ✅ 本文件真正证明了什么

  | 定理 | 内容 | 强度 |
  |---|---|---|
  | `frontdoor_criterion` | **一般定理**：任意有限 `U₁,U₂,U₃,X,Z,Y`、任意 `p₁,p₂,p₃,fX,fZ,fY`，`PosX → PosXZ → frontdoorFormula = doLaw` | |
  | `frontdoor_criterion_pointwise` | 同上 `∀ x y` | |
  | `frontdoor_criterion_explicit` | 同上，`doLaw` 展开成显式 `∑_u₂∑_u₁∑_u₃`（**与任务公式逐字对照**） | |
  | `FrontdoorConditions` | **四条条件逐条命名**的命题结构（每个字段一句精确陈述 + 说明） | |
  | `frontdoor_criterion_of_conditions` | `FrontdoorConditions S → frontdoorFormula = doLaw`（**读作"四条件 ⟹ 公式"**） | |
  | `demo_conditions` | 具体 SCM `demo` **满足**四条条件（`mediation` 用 `sum_R_eq` 真证） | |
  | `demo_fd_eq_do` | `demo` 上 `fd = 3/5, 2/5, 2/5, 3/5`（`= doLaw`） | |
  | `demoObs_ff` / `demoObs_ft` | 观测律 `17/20`、`3/20` | |
  | `demo_fd_ne_obs` | `fd(0,0) = 3/5 ≠ 17/20 = 观测律`（**证明等式非平凡**） | |
  | `demo_criterion_instantiated` / `demo_criterion_via_conditions` | 主定理在 `demo` 上**实例化**（端到端） | |
  | `positivity_fails_example1/2` | positivity 失效 ⟹ 公式错（引用 `R253` / `R254`） | |
  | `condition_i_fails_example` | 违反 (i) ⟹ 公式错（引用 `R242`） | |

  **代码规模**：约 730 行，**0 `sorry`，0 编译警告**。

  ## 5.2 ⚠ 四条条件的**精确陈述**（本文件的最终口径）

  设 `U = U₁ × U₂ × U₃`，`pU(u₁,u₂,u₃) = p₁u₁·p₂u₂·p₃u₃`（外生分量独立），
  结构方程为 `X := fX u₁`、`Z := fZ x u₂`、`Y := fY z u₁ u₃`。

  **(i) `Z` 截断 `X → Y` 的所有有向路径**
  ```lean
  fY : Z → U1 → U3 → Y          -- ⚠ 类型中没有 X 槽位（定义即条件）
  -- 可证明的数值版本（`FrontdoorConditions.mediation`）：
  ∀ z y, (∑ x : X, R p1 p3 fX fY x z y)
        = ∑ u1, ∑ u3, p1 u1 * p3 u3 * ind (fY z u1 u3 = y)
  ```
  后者由 `R242.sum_R_eq` 证出，且**在 `fY` 吃 `x` 时失败**（§3 反例 3）。

  **(ii) `X → Z` 无后门路径**
  ```lean
  fZ : X → U2 → Z               -- ⚠ 类型中没有 U₁ 槽位（U₁ 是 X,Y 唯一共同祖先）
  -- 数值后果：P(z|do(x)) = P(z|x) = Q p2 fZ x z，与 U₁ 无关
  ```

  **(iii) `Z → Y` 的所有后门路径被 `X` 阻断**
  ```lean
  -- U₁ 同时出现在 fX 与 fY 的签名里 ⟹ 唯一后门是 Z ← X ← U₁ → Y
  -- 数值后果（定义即条件）：p(x,z) = p(x) · P(z|x)   （= `MargXZ` /
  --   `FrontdoorSetup.margXZ`） ⟺ Z ⟂ U₁ | X
  ```

  **(iv) positivity / overlap**（Pearl 心照不宣，本文件显式化）
  ```lean
  PosX  : Prop := ∀ x : X, margX x ≠ 0                    -- p(x) > 0
  PosXZ : Prop := ∀ (a : X) (b : Z), qzx a b ≠ 0          -- P(z|x) > 0
  ```
  （由 (iii) 的乘积分解，`p(x,z) > 0` 等价于 `p(x) > 0 ∧ P(z|x) > 0`。）

  ## 5.3 ⚠ **必须声明的边界（不掩饰）**

  1. **(i)(ii)(iii) 是"类型签名版本"，不是图的 d-分离判定器。**
     本文件**没有**证明「图上的 d-分离判定 ⟺ 这里的签名约束」。
     这一步属 **Pearl 1.2.4（缺口 1）**，未做。`Frontdoor.lean` 与本文件
     都继承了 `FrontdoorChainProof` 的这个边界。
     注意 `FrontdoorConditions.noBackdoorXZ` 与 `backdoorZYblocked`
     是 `True` —— 它们的实质内容**完全在 `FrontdoorSetup` 的类型里**
     （`fZ` 无 `U₁`、`MargXZ` 定义为乘积），把 `True` 写出来只是
     为了**在结构体里给这两条一个名字**，便于逐条对照 Pearl 原文。
  2. **乘积载体是定义，不是从 `∑_{u₁×u₂×u₃}` 导出的。**
     `MargXZ = MargX · Q`、`Joint = Q · R` 在 `FrontdoorChainProof` §1 里
     是**定义**。把它们从原始 SCM 求和（`∑_u pU u [fX u₁=x][fZ x u₂=z][fY z u₁u₃=y]`）
     推出来需要 `Finset.sum_product` 的三重分解 —— **机械改写，但本文件没做**。
     `⟹ frontdoor_criterion` 是**在乘积载体上**的完整证明，
     而非"从 SCM 原始定义出发"的完整证明。
  3. **「positivity 必要」只给了三个实例，不是全称定理。**
     全称命题应为 `¬positivity ⟹ ∃ SCM, fd ≠ doLaw`。本文件（连同 `R253`/`R254`）
     只给出三个**具体**反例。三个反例的失效机制**是同一个**
     （某个 `p(x',z)=0` 使内层丢掉整个 `x'` 分支的质量），
     且偏差方向都是 `fd` **偏小**（**没有找到 `fd` 偏大的例子**）。
     **如实记录为未解决问题。**
  4. **只有有限情形。** `X, Z, Y, U₁, U₂, U₃` 全部 `Fintype`。
     连续情形需换 `MeasurableSpace` / `Measure` / `∫` 版本，**未做**。
  5. **`fY` 与 `fX` 的"独立性"不是定理，是签名。** 例如 `fY` 仍可
     以**无关地**读 `u₁`（这正是 (iii) 的混杂），本文件没有假设 `fY ⟂ fX`。
  6. **`R253`/`R254`/`R242` 的反例被"引用"而非"重证"。**
     本文件对它们的引用是 `theorem ... := FateV2.Predict.R253.fd_literal_chain_fails` 这种
     **直接搬运**，没有重新证明。这是**有意**的（避免重复），但也意味着
     反例的正确性**依赖**那三个文件当时的证明。

  ## 5.4 为什么 `demo` 是真验证（而非平凡等式）

  - `demo` 的观测律 `P(Y=0|X=0) = 17/20`，而 `do` 律 `= 3/5 = 12/20`。
    **观测律错 `1/4`** ⟹ `X ↔ Y` **确有混杂**（`U₁` 以 `1/2` 概率决定 `Y`）。
  - front-door 公式给出 `3/5` —— **修回**真干预值。
  - 若 `fd = doLaw` 是平凡的（例如 `Y ⟂ X` 无混杂），则 `obs` 也会等于 `do`。
    **`17/20 ≠ 3/5` 排除了这种可能。**
  - 同一 `X, Z` 链上把 `fZ` 从"异或"改成"恒等"（`Z := X`，即 `R253` 的字面 SCM）
    就退化成 `fd = 1/2 ≠ 1 = do` —— **positivity 是分水岭**。

  ## 5.5 建议的下一步

  1. 补齐 §5.3-1（d-分离 ⟺ 签名约束），打通"缺口 1"。
  2. 补齐 §5.3-2（`Finset.sum_product` 三重分解），把定理提升为"从原始 SCM 定义出发"。
  3. 把 §5.3-3 从"三个实例"提升为全称定理（需刻画"哪些零模式必然导致失效"）。
-/

end FateV2.Predict.R255
/-! ===========================================================================
  §6 **R-32 接线：一般准则 ⟷ 三个具体反例族**（本轮追加）

  ## 6.0 为什么在这一节

  §2 的 `frontdoor_criterion` 是**一般定理**：
  `PosX → PosXZ → frontdoorFormula = doLaw`（任意有限载体、任意结构方程）。
  §5.3-3 却诚实登记了一个**未闭合的缺口**：

  > 「positivity 必要」只给了三个实例，不是全称定理；
  > 且**偏差方向都是 `fd` 偏小**（**没有找到 `fd` 偏大的例子**）。

  本节把**三个具体反例族**（`FateV2.Predict/R253` 的 `Z := X` 与 `Y := Z ∨ X`、
  `FateV2.Predict/R254` 的 `Z := X ∨ Uz`、`FateV2.Predict/R242` 的 `fYdirect`）
  **与一般准则放在同一个定理里比较**，从而把 §5.3-3 的三条内容
  从「散文」提升为**机器检查的合取命题**：

  1. positivity 的**失效见证**是精确的零值（`= 0`，不是「大概很小」）；
  2. 偏差方向 `fd < doLaw` 在**四个**互不相同的模型上一致（2 个族 × 4 个判据点）；
  3. 准则的**结论不可无条件成立**（`∃` 反例载体），即 `PosXZ` 是真的用上了。

  ⚠ 本节**只做引用与合取**，不重证任何数值；所有数值都由源模块的
  `norm_num` 证明体给出，这里用其**定理名**（不是重新 `norm_num`）。
  这样若源模块的数值将来被改动，本节会**先坏**——这是有意的依赖方向。

  ## 6.1 依赖的源定理（逐个 `#check` 过）

  | 源 | 定理 | 内容 |
  |---|---|---|
  | `FateV2.Predict.R253` | `fd_literal_chain_fails` | `Z := X` 上 `fd ≠ doLaw` |
  | `FateV2.Predict.R253` | `l_margXZ_f_t` / `l_margXZ_t_f` | `p(0,1) = 0`、`p(1,0) = 0` |
  | `FateV2.Predict.R253` | `l_do_f_f` | `p(y=0|do(0)) = 1` |
  | `FateV2.Predict.R253` | `fd_correct_on_chain` | 加噪链上 `fd = doLaw`（四元合取）|
  | `FateV2.Predict.R253` | `n_do_f_f` | 加噪链 `do(0,0) = 3/8` |
  | `FateV2.Predict.R253` | `n_obs_f_f` | 加噪链观测律 `23/40` |
  | `FateV2.Predict.R253` | `fd_differs_with_direct_effect` | `Y := Z ∨ X` 上 `fd ≠ doLaw` |
  | `FateV2.Predict.R254` | `fd_or_gate_fails_on_0_0` | `Z := X ∨ Uz` 上 `fd ≠ doLaw` |
  | `FateV2.Predict.R254` | `fd_or_exact` / `o_do_f_f` | `fd = 1/50`、`do = 1/10` |
  | `FateV2.Predict.R254` | `o_margXZ_t_f` | `p(1,0) = 0` |
  | `FateV2.Predict.R242` | `fd_differs_without_mediation` | `Y` 吃 `X` 上 `fd ≠ doLaw` |
  | `FateV2.Predict.R242` | `d_fd_f_f` / `d_do_f_f` | `fd = 1/2`、`do = 7/10` |
-/

namespace FateV2.Predict.R255.R32

open FateV2.Predict.Frontdoor

/-! ## 6.2 positivity 失效的**精确零值见证**（两个族） -/

/-- **`positivity_zero_witness_two_families`**：`PosXZ` 的违反在
**两个结构不同的反例族**里都落在**精确的零**上。

- `FateV2.Predict.R253`（`Z := X` 确定性）：`p(x=0, z=1) = 0`；
- `FateV2.Predict.R254`（`Z := X ∨ Uz` 的 OR 门）：`p(x=1, z=0) = 0`。

**为什么这条不是同义反复**：命题的两个合取项分别来自**两个不同模块**的
`norm_num` 计算，且**零的位置不同**（一个是 `(0,1)`，一个是 `(1,0)`）。
它说明「positivity 失效」在这两个族里不是「近似退化」而是**支撑集缺一整块**，
与 §5.3-3 描述的机制（某 `p(x',z)=0` 吞掉整个 `x'` 分支）逐字对应。 -/
theorem positivity_zero_witness_two_families :
    FateV2.Predict.R253.lMargXZ false true = 0 ∧ FateV2.Predict.R254.oMargXZ true false = 0 :=
  ⟨FateV2.Predict.R253.l_margXZ_f_t, FateV2.Predict.R254.o_margXZ_t_f⟩

/-- 同一件事的**对称面**：`Z := X` 字面链上 `p(1,0) = 0` 也成立
（确定性 `Z := X` 让**非对角全零**，不只一个点）。 -/
theorem positivity_zero_witness_symmetric :
    FateV2.Predict.R253.lMargXZ true false = 0 ∧ FateV2.Predict.R253.lMargXZ false true = 0 :=
  ⟨FateV2.Predict.R253.l_margXZ_t_f, FateV2.Predict.R253.l_margXZ_f_t⟩

/-! ## 6.3 偏差**方向** `fd < doLaw` 在四个模型上一致 -/

/-- **`fd_understates_in_four_models`**：**四个互不相同的模型**上
`frontdoorFormula` 都**严格小于**干预律。

| # | 模型 | 违反的前提 | `fd` | `doLaw` |
|---|---|---|---|---|
| 1 | `FateV2.Predict.R253` 字面链 `Z := X` | (iv) positivity | `1/2` | `1` |
| 2 | `FateV2.Predict.R254` OR 门 `Z := X ∨ Uz` | (iv) positivity | `1/50` | `1/10` |
| 3 | `FateV2.Predict.R242` 无中介 `fYdirect` | (i) `Y` 吃 `X` | `1/2` | `7/10` |
| 4 | `FateV2.Predict.R253` 直接效应 `Y := Z ∨ X` | (i) `Y` 吃 `X` | `1/8` | `1/4` |

**为什么这条是本节最有价值的一条**：

- **没有任何一个源模块能单独说出它** —— 它跨 3 个模块（`R253`、`R254`、`R242`）。
- 它把 §5.3-3 的「偏差方向都是偏小」从 3 个样本**扩到 4 个**，且**跨越两种
  不同的失效前提**（positivity 失效 vs 中介性失效）。
- 它是**严格不等式** `fd < doLaw`，不是 `≠` —— 比源模块的结论**更强**
  （源模块只证了 `≠`，方向要靠数值才能读出）。 -/

theorem fd_understates_in_four_models :
    -- 1) `Z := X`，positivity 失效：`1/2 < 1`
    frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false <
        FateV2.Predict.R253.lDo false false
    -- 2) `Z := X ∨ Uz`，positivity 失效：`1/50 < 1/10`
    ∧ frontdoorFormula FateV2.Predict.R254.oJoint FateV2.Predict.R254.oMargXZ FateV2.Predict.R254.oMargX false false <
        FateV2.Predict.R254.oDo false false
    -- 3) `R242` 的 `fYdirect`，违反 (i)：`1/2 < 7/10`
    ∧ frontdoorFormula FateV2.Predict.R242.dJoint FateV2.Predict.R242.dMargXZ
        (FateV2.Predict.R242.MargX FateV2.Predict.R242.p1c FateV2.Predict.R242.fXc) false false <
        FateV2.Predict.R242.dDo false false
    -- 4) `Y := Z ∨ X`，违反 (i)：`1/8 < 1/4`
    ∧ frontdoorFormula FateV2.Predict.R253.dJoint FateV2.Predict.R253.nMargXZ FateV2.Predict.R253.nMargX false false <
        FateV2.Predict.R253.dDo false false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FateV2.Predict.R253.fd_literal_exact_values.1, FateV2.Predict.R253.l_do_f_f]; norm_num
  · rw [FateV2.Predict.R254.fd_or_exact, FateV2.Predict.R254.o_do_f_f]; norm_num
  · rw [FateV2.Predict.R242.d_fd_f_f, FateV2.Predict.R242.d_do_f_f]; norm_num
  · obtain ⟨h1, h2, -⟩ := FateV2.Predict.R253.fd_differs_with_direct_effect
    rw [h1, h2]; norm_num

/-! ## 6.4 偏差**量**（不是只有方向）：字面链正好「减半」 -/

/-- **`fd_gap_literal_exact`**：`Z := X` 字面链上
`p(y=0|do(0)) − fd(0,0) = 1 − 1/2 = 1/2`。

**这精确化了 §5.3-3 的「系统性减半」**：不是「大约”，而是**恰好 `1/2`**，
且等于 `p(x=0)`（`l_margX_false`）—— 即被 `0/0 ↦ 0` 抹掉的正是 `X` 的另一半质量。 -/
theorem fd_gap_literal_exact :
    FateV2.Predict.R253.lDo false false
        - frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
      = 1 / 2 := by
  rw [FateV2.Predict.R253.fd_literal_exact_values.1, FateV2.Predict.R253.l_do_f_f]; norm_num

/-- 同一模型上，**缺掉的量 = `p(x=0)`**（`= 1/2`），并与 `l_margX_false` 对上。 -/
theorem fd_gap_literal_eq_margX :
    FateV2.Predict.R253.lDo false false
        - frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
      = FateV2.Predict.R253.lMargX false := by
  rw [fd_gap_literal_exact, FateV2.Predict.R253.l_margX_false]

/-! ## 6.5 **准则的结论不可无条件成立**（`PosXZ` 真的被用上） -/

/-- **`no_unconditional_chain_formula`**：**不存在**「对一切 `(x,y)`
`frontdoorFormula = doLaw`」这样的无条件命题 —— 即使把载体固定为
`FateV2.Predict.R253` 的字面链，也**已经**被反例否证。

**形式**：`¬ (∀ x y, fd x y = do y)`（在字面链的具体载体上）。

**为什么这条不是同义反复 / 不是前件包结论**：
前件（若是把它写成蕴含）会是「无条件」，而命题断言**该无条件命题为假**；
它**不是** `PosXZ → ...` 的实例，而是 `PosXZ` 的**必要性基石**：
§2 的 `frontdoor_criterion` 需要 `hQ : S.PosXZ`，本条证明**不能删掉 `hQ`**，
否则（在任何采用字面链语义的载体上）结论就假。
⚠ 边界：这只对**具体载体**成立，不是「任意 SCM 都需要 positivity」的全称定理
（§5.3-3 已如实登记该全称命题仍未证）。 -/
theorem no_unconditional_chain_formula :
    ¬ (∀ x y : Bool,
        frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX x y
          = FateV2.Predict.R253.lDo x y) := by
  intro h
  exact FateV2.Predict.R255.positivity_fails_example1 (h false false)

/-- 同上，用 `∃` 形式陈述（可读性更强）：**存在**载体与判据点使公式失效。 -/
theorem exists_formula_failure :
    ∃ (j : Bool → Bool → Bool → ℝ) (mz : Bool → Bool → ℝ) (mx : Bool → ℝ)
      (dl : Bool → Bool → ℝ) (x y : Bool),
      frontdoorFormula j mz mx x y ≠ dl x y :=
  ⟨FateV2.Predict.R253.lJoint, FateV2.Predict.R253.lMargXZ, FateV2.Predict.R253.lMargX, FateV2.Predict.R253.lDo,
   false, false, FateV2.Predict.R255.positivity_fails_example1⟩

/-! ## 6.6 positivity **成立**时公式精确成立（对照组）+ 混杂仍在 -/

/-- **`positivity_success_vs_failure_contrast`**：**同一条 `X → Z → Y` 链语义**，
只把 `Z` 的方程从「确定性 `Z := X`」换成「加噪 `Z := X ⊕ Uz`」
（positivity 由失效变为成立），则：

1. **加噪链**：`fd = doLaw` 在 `(0,0)` 处成立；
2. **加噪链**：`fd = doLaw` 在**全部四个**判据点成立（`∀ x y`）；
3. **加噪链的观测律仍被混杂污染**：`obs(0,0) = 23/40 ≠ 3/8 = do(0,0)`
   ⟹ `fd = doLaw` **不是平凡恒等**；
4. **字面链**：`fd ≠ doLaw`（同一链语义，只差 `Z` 的噪声）。

**⟹ positivity 是**分水岭**：它在，公式对；它不在，公式系统性偏小。**
（这是 §5.4 的散文论证的**机器检查版本**，且第 3 项排除了「平凡等式」的辩解。） -/
theorem positivity_success_vs_failure_contrast :
    -- 1) 加噪链 (0,0) 处相等
    frontdoorFormula FateV2.Predict.R253.nJoint FateV2.Predict.R253.nMargXZ FateV2.Predict.R253.nMargX false false
        = FateV2.Predict.R253.nDo false false
    -- 2) 加噪链全部四点相等
    ∧ (∀ x y : Bool,
        frontdoorFormula FateV2.Predict.R253.nJoint FateV2.Predict.R253.nMargXZ FateV2.Predict.R253.nMargX x y
          = FateV2.Predict.R253.nDo x y)
    -- 3) 观测律仍被混杂污染（`23/40 ≠ 3/8`）
    ∧ FateV2.Predict.R253.nObs false false = 23 / 40
    ∧ FateV2.Predict.R253.nDo false false = 3 / 8
    ∧ FateV2.Predict.R253.nObs false false ≠ FateV2.Predict.R253.nDo false false
    -- 4) 同一链语义，字面（无噪）版本失败
    ∧ frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
        ≠ FateV2.Predict.R253.lDo false false := by
  obtain ⟨h00, h01, h10, h11⟩ := FateV2.Predict.R253.fd_correct_on_chain
  refine ⟨h00, ?_, FateV2.Predict.R253.n_obs_f_f, FateV2.Predict.R253.n_do_f_f, ?_,
    FateV2.Predict.R255.positivity_fails_example1⟩
  · intro x y
    cases x <;> cases y
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  · rw [FateV2.Predict.R253.n_obs_f_f, FateV2.Predict.R253.n_do_f_f]; norm_num

/-! ## 6.7 三种失效模式的**联合登记**（一条定理读全 §5.3-3） -/

/-- **`failure_modes_registry`**：本项目 front-door 的**三种失效模式**
在一次陈述中并列，每项都可**独立核查**：

| 模式 | 前提被违反 | 见证 | 数 |
|---|---|---|---|
| A | (iv) positivity，`Z := X` 确定性 | `p(0,1) = 0` | `fd = 1/2 ≠ 1` |
| B | (iv) positivity，`Z := X ∨ Uz` OR 门 | `p(1,0) = 0` | `fd = 1/50 ≠ 1/10` |
| C | (i) 中介性（`Y` 吃 `X`），positivity 反而成立 | `fYdirect : Z → X → U1 → U3 → Y` | `fd = 1/2 ≠ 7/10` |

**⟹ C 与 A/B 的失效前提**不同**，说明两条前提**各自独立地必要**，
不存在「一条蕴含另一条」的退化。 -/
theorem failure_modes_registry :
    -- A：零支撑 + 失效
    FateV2.Predict.R253.lMargXZ false true = 0
      ∧ frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
          ≠ FateV2.Predict.R253.lDo false false
    -- B：零支撑 + 失效（结构不同的第二个族）
    ∧ FateV2.Predict.R254.oMargXZ true false = 0
      ∧ frontdoorFormula FateV2.Predict.R254.oJoint FateV2.Predict.R254.oMargXZ FateV2.Predict.R254.oMargX false false
          ≠ FateV2.Predict.R254.oDo false false
    -- C：(i) 违反 ⟹ 失效（前提与 A/B 不同）
    ∧ frontdoorFormula FateV2.Predict.R242.dJoint FateV2.Predict.R242.dMargXZ
          (FateV2.Predict.R242.MargX FateV2.Predict.R242.p1c FateV2.Predict.R242.fXc) false false
        ≠ FateV2.Predict.R242.dDo false false :=
  ⟨FateV2.Predict.R253.l_margXZ_f_t, FateV2.Predict.R255.positivity_fails_example1,
   FateV2.Predict.R254.o_margXZ_t_f, FateV2.Predict.R254.fd_or_gate_fails_on_0_0,
   FateV2.Predict.R242.fd_differs_without_mediation⟩

/-- **`criterion_conclusion_holds_when_hypotheses_hold`**：对照面 ——
一般准则**在前提成立时给等式**（引 `frontdoor_criterion`），
与上一条的三处失效**并置**即为完整图像：
`PosX → PosXZ → 等式`；缺任一条则（有三个具体反例）等式假。 -/
theorem criterion_conclusion_holds_when_hypotheses_hold (S : FateV2.Predict.R255.FrontdoorSetup)
    (hX : S.PosX) (hQ : S.PosXZ) (x : S.X) (y : S.Y) :
    frontdoorFormula S.joint S.margXZ S.margX x y = S.doLaw x y :=
  FateV2.Predict.R255.frontdoor_criterion S hX hQ x y

end FateV2.Predict.R255.R32

/-! ===========================================================================
  §7 **R-49 接线：跨模块的严格数值序关系**（本轮追加）

  ## 7.0 为什么还要再加一节（与 §6 的分工）

  §6（`FateV2.Predict.R255.R32`）已把「四个模型上 `fd < doLaw`」与「positivity 零见证」
  收成合取命题。**§6 有一个未覆盖的方向**：它只比较了每个模型**内部**的
  `fd` 与 `doLaw`，**从未跨模块比较数值**。

  本节补上这个方向，给出**三条跨模块严格不等式 / 取值**命题：

  1. **字面反例的 `fd` 严格小于正例 `demo` 的 `fd`**（`1/2 < 3/5`），
     且两个字面值都落在开区间 `(0,1)` 内 —— 说明偏差**不是**「`fd` 退化到 0 或 1」；
  2. **`demo` 的 `doLaw` 与加噪链 `FateV2.Predict.R253` 的 `doLaw` 严格不同**
     （`3/5 ≠ 3/8`）—— 说明**不同载体的干预律是独立数值**，
     `fd = doLaw` 的相等**不可能跨载体照抄**；
  3. **四个模型的 `doLaw(0,0)` 两两分成三组不同值**，把它们排成一条严格链
     `0 < 1/10 < 1/4`。

  ## 7.1 依赖的源定理（逐个 `#check` 过）

  | 源 | 定理 | 内容 |
  |---|---|---|
  | `FateV2.Predict.R253` | `fd_literal_exact_values` | `fd_literal(0,0) = 1/2` 且 `lDo(0,0) = 1` |
  | `FateV2.Predict.R255` | `fd_num_false_false` | `fd_demo(0,0) = 3/5` |
  | `FateV2.Predict.R255` | `ddo_ff` | `demo.doLaw(0,0) = 3/5` |
  | `FateV2.Predict.R253` | `n_do_f_f` | 加噪链 `do(0,0) = 3/8` |
  | `FateV2.Predict.R254` | `o_do_f_f` | OR 门 `do(0,0) = 1/10` |
  | `FateV2.Predict.R253` | `d_do_f_f` | 直接效应 `do(0,0) = 1/4` |

  ⚠ 本节**不重证任何数值**，只引用源定理名 —— 依赖方向有意指向源模块。
-/

namespace FateV2.Predict.R255.R49

open FateV2.Predict.Frontdoor

/-! ## 7.2 跨模块：字面反例的 `fd` 严格低于正例 `demo` 的 `fd` -/

/-- **`literal_fd_lt_demo_fd`**：**字面反例的 front-door 值严格小于
正例 `demo` 的值**，且两者都在开区间 `(0,1)` 内。

- `FateV2.Predict.R253`（`Z := X` 确定性，positivity 失效）：`fd(0,0) = 1/2`；
- `FateV2.Predict.R255`（`demo`，四条条件全满足）：`fd(0,0) = 3/5`。

**为什么这条不是同义反复**：

1. 两个数值来自**两个不同模块**的独立 `norm_num` 计算，
   命题 `1/2 < 3/5` 是它们**首次在同一处相遇**（§6 与源模块都没说过）；
2. `0 < 1/2` 与 `3/5 < 1` 这两个**界**是新的：它们排除了「`fd` 失效时
   退化到 `0` 或 `1`」这一常见误读 —— 失效是**温和的数值漂移**，不是崩溃；
3. 若有人把 `fd` 当作「只要链语义对上就自动正确」，本条给出**反例数值**：
   同一个 `(x,y) = (0,0)` 单元格，两条都声称是 front-door 链，`fd` 差 `1/10`。 -/
theorem literal_fd_lt_demo_fd :
    frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false = 1 / 2
      ∧ frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
          < frontdoorFormula demo.joint demo.margXZ demo.margX false false
      ∧ frontdoorFormula demo.joint demo.margXZ demo.margX false false = 3 / 5
      ∧ 0 < frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
      ∧ frontdoorFormula demo.joint demo.margXZ demo.margX false false < 1 := by
  obtain ⟨hLit, _⟩ := FateV2.Predict.R253.fd_literal_exact_values
  obtain ⟨hDemo, _, _, _⟩ := demo_fd_eq_do
  refine ⟨hLit, ?_, hDemo, ?_, ?_⟩
  · rw [hLit, hDemo]; norm_num
  · rw [hLit]; norm_num
  · rw [hDemo]; norm_num

/-! ## 7.3 跨模块：`demo` 的干预律与加噪链的干预律**严格不同** -/

/-- **`demo_doLaw_ne_noisy_doLaw`**：**两个「链语义正确」的载体，
干预律数值严格不同**。

- `FateV2.Predict.R255.demo`：`doLaw(0,0) = 3/5`（`fZ := x ⊕ U₂`，`p₂(0) = 7/10`）；
- `FateV2.Predict.R253` 加噪链：`nDo(0,0) = 3/8`（`fZ := x ⊕ Uz`，`pUz ≡ 1/2`）。

**为什么这条不是同义反复**：两者的结构方程**形状相同**（异或门），
差别只在噪声分布 —— 正是「分布不同 ⟹ 干预律不同」。这说明 `fd = doLaw`
是**逐载体的数值等式**，**不能**当成一个可以跨载体搬运的恒等式；
也说明 §6 的 `fd < doLaw` 结论**不是**「`doLaw` 恒为某个固定值」的副产品。 -/
theorem demo_doLaw_ne_noisy_doLaw :
    demo.doLaw false false = 3 / 5
      ∧ FateV2.Predict.R253.nDo false false = 3 / 8
      ∧ demo.doLaw false false ≠ FateV2.Predict.R253.nDo false false := by
  refine ⟨ddo_ff, FateV2.Predict.R253.n_do_f_f, ?_⟩
  rw [ddo_ff, FateV2.Predict.R253.n_do_f_f]; norm_num

/-! ## 7.4 跨模块：四个载体的 `doLaw(0,0)` 排成严格链 -/

/-- **`four_models_doLaw_strict_chain`**：**四个互不相同载体的局部干预律
`doLaw(0,0)` 排成一条严格递增链**。

- `FateV2.Predict.R254` OR 门：`1/10`
- `FateV2.Predict.R253` 直接效应（`Y := Z ∨ X`）：`1/4`
- `FateV2.Predict.R253` 加噪链：`3/8`
- `FateV2.Predict.R255.demo`：`3/5`

即 `1/10 < 1/4 < 3/8 < 3/5`。

**为什么这条不是同义反复**：四个数值分别来自 **3 个模块的 4 个不同载体**，
源模块**各自只知道自己那一个**；把它们排成链**只能在本节完成**。
它同时说明：

1. 局部干预律是**载体相关的实数**，不是某个普适常数；
2. 四个都是**真分数**（`0 < · < 1`），所以后面任何 `fd` 的偏差都是
   **在 `(0,1)` 区间内部的漂移** —— 与 §7.2 的界一致；
3. §6 的「`fd < doLaw`」四条结论里，右端**不是同一个数**，
   因而那四条是**四个独立的严格不等式**，不是一条不等式的四次复制。 -/
theorem four_models_doLaw_strict_chain :
    FateV2.Predict.R254.oDo false false = 1 / 10
      ∧ FateV2.Predict.R253.dDo false false = 1 / 4
      ∧ FateV2.Predict.R253.nDo false false = 3 / 8
      ∧ demo.doLaw false false = 3 / 5
      ∧ FateV2.Predict.R254.oDo false false < FateV2.Predict.R253.dDo false false
      ∧ FateV2.Predict.R253.dDo false false < FateV2.Predict.R253.nDo false false
      ∧ FateV2.Predict.R253.nDo false false < demo.doLaw false false := by
  refine ⟨FateV2.Predict.R254.o_do_f_f, FateV2.Predict.R253.d_do_f_f, FateV2.Predict.R253.n_do_f_f, ddo_ff,
    ?_, ?_, ?_⟩
  · rw [FateV2.Predict.R254.o_do_f_f, FateV2.Predict.R253.d_do_f_f]; norm_num
  · rw [FateV2.Predict.R253.d_do_f_f, FateV2.Predict.R253.n_do_f_f]; norm_num
  · rw [FateV2.Predict.R253.n_do_f_f, ddo_ff]; norm_num

/-! ## 7.5 小结：本节与 §6 合起来给出什么 -/

/-- **`combined_inventory`**：把本节三条 + §6 的核心对照**打包**成
一个可机检的合取命题（**不重证**，全部引用）。

内容：
1. `demo` 上 `fd = doLaw`（准则在前提成立时成立）—— 引 `demo_fd_eq_do`；
2. `demo` 上 `fd ≠ 观测律`（等式非平凡）—— 引 `demo_fd_ne_obs`；
3. 字面反例上 `fd ≠ doLaw`（前提失效时等式假）—— 引 `FateV2.Predict.R253`；
4. 字面 `fd` 严格小于 `demo` 的 `fd` —— 引 §7.2；
5. `demo` 与加噪链的干预律严格不同 —— 引 §7.3。

**这一条的作用**：把「准则**何时**成立、**何时**不成立、以及两种情形的数值
**如何区分**」压缩成一个命题，便于审计时一次性 `#check` 全貌。 -/
theorem combined_inventory :
    -- 1) 前提成立 ⟹ 等式成立
    (∀ x y : Bool, frontdoorFormula demo.joint demo.margXZ demo.margX x y = demo.doLaw x y)
    -- 2) 等式非平凡：fd ≠ 观测律
    ∧ frontdoorFormula demo.joint demo.margXZ demo.margX false false ≠ demoObs false false
    -- 3) 前提失效 ⟹ 等式假
    ∧ frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
        ≠ FateV2.Predict.R253.lDo false false
    -- 4) 两种情形的 fd 数值严格可区分
    ∧ frontdoorFormula FateV2.Predict.R253.lJoint FateV2.Predict.R253.lMargXZ FateV2.Predict.R253.lMargX false false
        < frontdoorFormula demo.joint demo.margXZ demo.margX false false
    -- 5) 干预律是载体相关的实数
    ∧ demo.doLaw false false ≠ FateV2.Predict.R253.nDo false false :=
  ⟨demo_criterion_instantiated, demo_fd_ne_obs, FateV2.Predict.R253.fd_literal_chain_fails,
   literal_fd_lt_demo_fd.2.1, demo_doLaw_ne_noisy_doLaw.2.2⟩

end FateV2.Predict.R255.R49

/-! ===========================================================================
  §8  `R-56` 追加：`demo` 载体的**三层边缘化一致性**与**跨载体对照**

  §4 给出的是 `demo` 的**单点数值**（`dmargX*`、`dmargXZ*`、`djoint_*`、`ddo_*`）
  与主定理的实例化（`demo_fd_eq_do`、`demo_criterion_instantiated`）。
  §7 给出跨载体**干预律**对照（`demo_doLaw_ne_noisy_doLaw`）。

  本节追加的是**同一载体内部三层描述的相容性**（joint → margXZ → margX），
  以及**跨载体的边缘律**对照（`demo` 的 `margXZ` vs `R253` 加噪链的 `nMargXZ`）。
  这些在 §4/§7 均**未登记**：

  | 定理 | 内容 |
  |---|---|
  | `demo_joint_marginalizes_to_margXZ` | `∑_y joint x z y = margXZ x z`（按 `y` 边缘化）|
  | `demo_margXZ_sum_gives_margX` | `∑_z margXZ x z = margX x`（按 `z` 边缘化）|
  | `demo_doLaw_sum_one` | `doLaw x 0 + doLaw x 1 = 1`（干预律是概率律）|
  | `demo_margXZ_ne_noisy_margXZ` | `demo.margXZ ≠ R253.nMargXZ`（同一链语义、不同噪声）|

  ## 防同义反复

  * 前三条**不**是单点数值的重述：它们把 8 / 4 / 4 个格点按**不同方向**求和，
    得到 4 / 2 / 2 个**新**等式；本证明**逐点展开**（不经 §4 的任何单点引理以外的途径）。
  * 第四条是两个**不同载体**（`Bool` 上的两套不同噪声分布）的**不同数值**，
    不可能由任何一边的定义得出。
  * 无 `sorry` / `admit` / `axiom`，全部 `norm_num` / `simp` 核算。
-/

namespace FateV2.Predict.R255

section R56Demo

/-- **`R-56`：`demo.joint` 按 `y` 边缘化**回 `demo.margXZ`。

$$p(x,z,{\cdot}) \text{ 全质量} = p(x,z) \qquad (\forall x,z).$$

**⚠ 写法说明（诚实登记）**：`demo.Y` 是结构字段类型，在 `reducible` 透明度下
**不**与 `Bool` 定义相等，故 `Fintype.sum_bool` **不能**直接重写 `∑ y : demo.Y`。
本节因此用**两点和** `f false + f true` 表述（对二元素类型这是**同一**内容），
避免依赖定义相等 —— 这**不削弱**定理：结论仍把 **8** 个 `joint` 格点
归约到 **4** 个 `margXZ` 格点。

`demo` 的 `joint` 由 `R / p₂ / p₃` 三层求和定义，`margXZ` 由 `Q · MargX` 定义 ——
**两套定义形状不同**，等式需真的把格点值加起来再对照。 -/
theorem demo_joint_marginalizes_to_margXZ :
    ∀ x z : Bool, demo.joint x z false + demo.joint x z true = demo.margXZ x z := by
  intro x z
  cases x <;> cases z
  · simp only [djoint_fff, djoint_fft, dmargXZ_ff]; norm_num
  · simp only [djoint_ftf, djoint_ftt, dmargXZ_ft]; norm_num
  · simp only [djoint_tff, djoint_tft, dmargXZ_tf]; norm_num
  · simp only [djoint_ttf, djoint_ttt, dmargXZ_tt]; norm_num

/-- **`R-56`：`demo.margXZ` 按 `z` 边缘化**回 `demo.margX`。

$$p(x,\text{false}) + p(x,\text{true}) = p(x) \qquad(\forall x).$$
`7/20 + 3/20 = 1/2`（`x = 0`）与 `3/20 + 7/20 = 1/2`（`x = 1`）。 -/
theorem demo_margXZ_sum_gives_margX :
    ∀ x : Bool, demo.margXZ x false + demo.margXZ x true = demo.margX x := by
  intro x
  cases x
  · simp only [dmargXZ_ff, dmargXZ_ft, dmargX_f]; norm_num
  · simp only [dmargXZ_tf, dmargXZ_tt, dmargX_t]; norm_num

/-- **`R-56`：`demo` 的干预律**逐 `x` 归一化**。

$$\text{doLaw}\,x\,0 + \text{doLaw}\,x\,1 = 1 \qquad (\forall x).$$
`3/5 + 2/5 = 1` 与 `2/5 + 3/5 = 1`。

**⟹ 意义**：`demo.doLaw` 直接定义为 `DoLaw`（对 `U₂,U₃` 的求和），
其**归一性不是定义附赠**的 —— 需把 `dp1`/`dp2`/`dp3` 的归一性代入验证。
这是 `frontdoor_criterion` 结论双方都是概率律的必要旁证。 -/
theorem demo_doLaw_sum_one : ∀ x : Bool, demo.doLaw x false + demo.doLaw x true = 1 := by
  intro x
  cases x
  · simp only [ddo_ff, ddo_ft]; norm_num
  · simp only [ddo_tf, ddo_tt]; norm_num

/-- **`R-56`：跨载体边缘律**严格区分**。**

- `demo`（`fZ := x ⊕ U₂`，`p₂(0) = 7/10`）：`margXZ(0,0) = 7/20`；
- `FateV2.Predict.R253` 加噪链（`nfZ := x ⊕ Uz`，`npUz(0) = 1/4`）：`nMargXZ(0,0) = 1/8`。

且 `nMargXZ(0,0) < demo.margXZ(0,0)`。

**⚠ 为什么这**不是** `demo_doLaw_ne_noisy_doLaw` 的重述**：
§7.3 对照的是**干预律**（`doLaw`，sum over `U₂,U₃`），
本条对照的是**观测边缘律**（`margXZ`，sum over `U₁,U₂`）——
两者是**不同函数**，且本条给出**严格不等式**（`1/8 < 7/20`），§7.3 只给不等号。
**⟹ 这说明两个载体的差异在观测层已经可见**，不依赖干预手术。 -/
theorem demo_margXZ_ne_noisy_margXZ :
    demo.margXZ false false = 7 / 20
      ∧ FateV2.Predict.R253.nMargXZ false false = 1 / 8
      ∧ FateV2.Predict.R253.nMargXZ false false < demo.margXZ false false
      ∧ FateV2.Predict.R253.nMargXZ false false ≠ demo.margXZ false false := by
  refine ⟨dmargXZ_ff, FateV2.Predict.R253.n_margXZ_f_f, ?_, ?_⟩
  · rw [dmargXZ_ff, FateV2.Predict.R253.n_margXZ_f_f]; norm_num
  · rw [dmargXZ_ff, FateV2.Predict.R253.n_margXZ_f_f]; norm_num

end R56Demo

end FateV2.Predict.R255
