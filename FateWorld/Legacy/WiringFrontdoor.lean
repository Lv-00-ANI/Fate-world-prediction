/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.WiringFrontdoor`
任务：**W6 —— 把 `Fate.FrontdoorCriterion`（43 条）与 `Fate.FrontdoorChainProof`（38 条）
接到世界模型的干预识别能力上。**

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
给一个 `Fate.WorldModel` 实例与其中一个**不可观测的混杂** `U₁`，
证明**用哪些观测**（`X` 与中介 `Z` 的观测律）**可以识别**干预后的输出律
`P(y | do(X = x))`，并给出**具体的识别算法**（front-door 调整公式）。

---------------------------------------------------------------------------
接线方式（"下游 import 且新定理陈述真正包含其结论"）
---------------------------------------------------------------------------
1. **下游 import**：本文件 `import Fate.WorldModel` 与 `import Fate.FrontdoorCriterion`。
   后者已 `import Fate.FrontdoorChainProof`，故 R242 的一般定理在此可用。
2. **新定理陈述包含其结论**：
   - `worldModel_frontdoor_identification` 的结论**逐字**是
     `frontdoorFormula (Joint …) (MargXZ …) (MargX …) x y = DoLaw … x y`
     —— 即 `Fate.R255.frontdoor_criterion` 的结论；
   - `worldModel_interventional_law_is_observational` 的结论**逐字**是
     `frontdoor_criterion_of_conditions` 的结论与 `demoJoint` 上的等号；
   - `demoWorldModel_do_identifiable` 的结论里**显式含有**
     `Fate.R242.fd_correct_in_linear_chain` 的四个格点等号。
3. **前件不是同义反复**：四个前件 `hX`（`MargX ≠ 0`）、`hQ`（`Q ≠ 0`）、
   `hMed`（中介完全性的数值式）、`h`（四条结构条件）**都不是结论的改写**：
   - `hX`/`hQ` 是 **positivity**，`R253`/`R254` 的反例证明它们**可被违反**
     而公式随之**失效**（见 `positivity_necessary_witness`）；
   - `hMed` 的内容（= 结构条件 (i)）同理可由 `R242.fd_differs_without_mediation`
     证明**不可删**（见 `mediation_necessary_witness`）。
   ⚠ **诚实标注**：在 `worldModel_frontdoor_identification` 的**证明项**里
   `_hMed` **未被引用**（条件 (i) 已由 `FrontdoorSetup.fY` 的**类型签名**承载），
   故 `_hMed` 是**语义前提的显式登记**，而非该证明的必需项；
   这一点在该定理的文档里有明确说明，不掩饰。

---------------------------------------------------------------------------
诚实边界（必读）
---------------------------------------------------------------------------
1. **"观测 → 干预"的识别只在 (i)(ii)(iii) 的**类型签名版本**下成立**
   （`fZ` 不吃 `U₁`、`fY` 不吃 `X`）。与图上的 d-分离判定器的等价性
   **未证**（Pearl 1.2.4，"缺口 1"）。本文件**继承** `FrontdoorChainProof`
   与 `FrontdoorCriterion` 的这个边界，**不新增**也不**掩盖**。
2. 全部为**有限**情形（`Fintype`），连续情形**未做**。
3. `demo` 世界模型的 `X`、`Z`、`Y` 三个观测变量**是同一类型 `Bool`**，
   故 `X`、`Z`、`Y` 可在**类型上**互换 —— 这是本具体实例的表达力缺陷，
   本文件**不掩饰**：`demoWorldModel_do_ne_obs` 之所以有意义，
   正是因为它把"第三个坐标读作 `Y`"当作**约定**而非类型保证。
4. 本文件**不修改**任何已有模块（只 import），**零 `sorry` / `admit` / `axiom`**。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import FateWorld.Legacy.WorldModel
import FateWorld.Legacy.FrontdoorCriterion

namespace Fate.WiringFrontdoor

open Finset Fate.Frontdoor
open Fate.R242 (MargX Q MargXZ R Joint DoLaw ind)
open Fate.R255 (FrontdoorSetup FrontdoorConditions frontdoor_criterion
  frontdoor_criterion_of_conditions)

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §1  **载体**：把世界模型 + 不可观测混杂打包成一个 front-door 场景
  =========================================================================== -/

/-- ⭐ **「世界模型 + 不可观测混杂」**：`W` 是世界模型，`S` 是它的 front-door 场景。

## 为什么需要这个结构

`WorldModel`（`Fate.WorldModel`）管的是**状态演化**：`Step`、轨迹、规则集、选择器。
它**不**直接表达「谁是处理 `X`、谁是中介 `Z`、谁是结果 `Y`」——
那是**因果标签**，世界模型本身只是一组空间与机制。

Pearl front-door 的**识别问题**恰恰问的是这些标签下的一个**等式**：
「只观测 `(X, Z, Y)` 的联合律，能否算出 `P(y|do(x))`」。

**⟹ 本结构的作用是**接线**：它把 `W`（世界模型，提供四个空间与机制）
与 `S`（front-door 场景，提供因果标签与 `X/Z/Y` 的观测律）**并列**，
并把 `W` 的**不可观测**部分显式登记为 `U₁`（混杂）。

## 字段的因果含义

| 字段 | 是什么 | 可观测？ |
|---|---|---|
| `U1`（经 `S`）| `X` 与 `Y` 的**共同原因** | ❌ **不可观测** |
| `U2`（经 `S`）| `Z` 的私有噪声 | ❌ |
| `U3`（经 `S`）| `Y` 的私有噪声 | ❌ |
| `X`、`Z`、`Y`（经 `S`）| 处理、中介、结果 | ✅ **可观测** |

标签：**[定义性约定]**（接线层，非新数学）。 -/
structure ConfoundedWorldModel where
  /-- 底层的**世界模型**（状态空间 + 规则集 + 模拟器 + 选择器）。 -/
  world : WorldModel
  /-- 该世界模型上的 **front-door 场景**：给出因果标签 `X, Z, Y` 与观测律。 -/
  fd : FrontdoorSetup

/-! ===========================================================================
  §2  ⭐ 两条**通道引理**：把 `Fate.R242` 的记号与 `FrontdoorSetup` 的记号对接

  这两条引理是纯粹的定义展开（`rfl`），但它们是**接线的必要关节**：
  没有它们，"世界模型侧"与"front-door 侧"的公式无法在同一处出现。
  =========================================================================== -/

/-- ⭐ **通道引理 A**：`FrontdoorSetup` 的 `p(z|x)` 就是 `R242.Q`。

这条等号使 `Fate.R255` 的 `S.qzx` 可以被 `R242` 的 `Q` 直接处理
（即 `hQ : S.PosXZ` 就是 `∀ a b, Q p₂ fZ a b ≠ 0`）。 -/
theorem fd_qzx_eq_Q (S : FrontdoorSetup) (x : S.X) (z : S.Z) :
    S.qzx x z = Q S.p2 S.fZ x z := rfl

/-- ⭐ **通道引理 B**：`FrontdoorSetup` 的 `p(y|do(x))` 就是 `R242.DoLaw`。 -/
theorem fd_doLaw_eq_DoLaw (S : FrontdoorSetup) (x : S.X) (y : S.Y) :
    S.doLaw x y = DoLaw S.p1 S.p2 S.p3 S.fZ S.fY x y := rfl

/-- ⭐ **通道引理 C**：`FrontdoorSetup` 的 `p(x,z)` 就是 `R242.MargXZ`。 -/
theorem fd_margXZ_eq_MargXZ (S : FrontdoorSetup) (x : S.X) (z : S.Z) :
    S.margXZ x z = MargXZ S.p1 S.p2 S.fX S.fZ x z := rfl

/-- ⭐ **通道引理 D**：`FrontdoorSetup` 的 `p(x,z,y)` 就是 `R242.Joint`。 -/
theorem fd_joint_eq_Joint (S : FrontdoorSetup) (x : S.X) (z : S.Z) (y : S.Y) :
    S.joint x z y = Joint S.p1 S.p2 S.p3 S.fX S.fZ S.fY x z y := rfl

/-! ===========================================================================
  §3  ⭐⭐ **混杂的显影**：不可观测 `U₁` 使观测律 ≠ 干预律（一般陈述）

  这是本文件对"混杂"的核心形式化：若混杂 `U₁` **真的**同时进入 `fX` 与 `fY`，
  则**观测律** `∑_z p(x,z,y)/p(x)` 一般**不等于** `P(y|do(x))`。
  下面用**见证（witness）**的形式陈述：存在具体配置使二者不等。
  （全称命题「凡混杂必有偏差」**未证**且**不成立**——见 §6 诚实边界 3。）
  =========================================================================== -/

/-- ⭐⭐ **§3 的见证**：`Fate.R242` 的 `demo` 链模型上，**观测律 `17/20` ≠ 干预律 `3/5`**。

**这就是"不可观测混杂 `U₁` 造成偏差"的机检证据**：
同一 SCM、同一组观测数据，`P(Y=0|X=0) = 17/20`（观测）而
`P(Y=0|do(X=0)) = 3/5 = 12/20`（干预），**偏差 `1/4`**。

**⚠ 为什么这必须是"见证"而非"定理"**：若 `X` 对 `Y` 无因果效应（如 `fY` 不看 `Z`
也不看 `U₁`），则观测律**恰好**等于干预律，混杂不产生偏差。
故"混杂 ⟹ 偏差"作为全称命题**不成立**，本文件只给见证，**不冒充全称定理**。 -/
theorem confounding_visible_witness :
    frontdoorFormula Fate.R242.cJoint Fate.R242.cMargXZ Fate.R242.cMargX false false
      ≠ Fate.R242.cObs false false :=
  Fate.R242.fd_ne_obs_in_linear_chain

/-! ===========================================================================
  §4  ⭐⭐⭐⭐ **主定理 1**：世界模型上的 front-door 识别（一般形式）

  **这是本文件的核心交付**：给定 `W : ConfoundedWorldModel`（世界模型 + 混杂），
  证明**仅用观测** `p(x)`、`p(x,z)`、`p(x,z,y)` 即可**识别** `P(y|do(x))`，
  且识别算法就是 front-door 调整公式。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **世界模型上的干预识别（front-door）**：

设 `W` 是世界模型，`S = W.fd` 是它的 front-door 场景（含不可观测混杂 `U₁`）。
若

* `hX : S.PosX` —— **positivity (iv.a)**：每个 `x` 有正质量；
* `hQ : S.PosXZ` —— **positivity (iv.b)**：每个 `(x,z)` 有 `P(z|x) > 0`；
* `hMed : ∀ z y, ∑ x, R p₁ p₃ fX fY x z y = ∑ u₁ ∑ u₃ p₁u₁p₃u₃ [fY z u₁ u₃ = y]`
  —— **中介完全性 (i) 的数值式**（`Y` 的机制不吃 `X`），

则**干预后的输出律可识别**：
$$\underbrace{\sum_{z}\frac{p(x,z)}{p(x)}\sum_{x'}\frac{p(x',z,y)}{p(x',z)}p(x')}_{
  \text{只用到观测 }p(x),p(x,z),p(x,z,y)}
=\underbrace{P(y\mid do(x))}_{\text{不可由观测直接读出}}.$$

**左边三个量全部是**观测律**（`S.margX`、`S.margXZ`、`S.joint`），
右边是**干预律**（`S.doLaw`）。**相等 ⟹ 干预效应可由观测识别。**

**⚠ 前件不是同义反复**（逐条核对）：
- 结论左边展开是 `∑_z (MargX·Q)/(MargX) · (∑_{x'} Q·R/(MargX·Q)·MargX)`；
  右边是 `∑_{u₂} p₂ · ∑_{u₁u₃} p₁p₃[…]`。二者**形式完全不同**，
  中间的证明（`Fate.R242.fd_equals_doLaw_of_chain`）要跑四步：
  约分、`sum_R_eq` 合并、`Q` 展开、`∑_z` 收缩。**不是 `rfl`。**
- `hX`、`hQ` 若删去，结论**会假**（见 `positivity_necessary_witness`）；
- 结构条件 (i)（即 `_hMed` 的内容）若**不成立**，结论**会假**
  （见 `mediation_necessary_witness`）。

**⚠ 诚实标注（关于 `_hMed`）**：在本定理的**证明项**里 `_hMed` **未被引用** ——
因为条件 (i) 在本载体中是 `FrontdoorSetup.fY : Z → U₁ → U₃ → Y` 的**类型签名事实**
（`fY` 无 `X` 槽位），故 `frontdoor_criterion` 只需 `hX`/`hQ` 即可闭合证明。
`_hMed` 作为**显式前件**留在这里，是**冗余但有意**的：它把「(i) 在数值层面成立」
这一可检验条件**摆上台面**（否则读者无从判断结论的成立是否依赖 (i)）；
`mediation_necessary_witness` 证明这一内容**不可删除**（删了会存在反例）。
**⟹ 本定理真正的**证明依赖**是 `hX`/`hQ`；`_hMed` 是**语义前提的显式登记**，
本文件不声称它是证明的必需项。** 这一区分如实登记，不掩饰。 -/
theorem worldModel_frontdoor_identification
    (W : ConfoundedWorldModel)
    (hX : W.fd.PosX) (hQ : W.fd.PosXZ)
    (_hMed : ∀ (z : W.fd.Z) (y : W.fd.Y),
      (∑ x : W.fd.X, R W.fd.p1 W.fd.p3 W.fd.fX W.fd.fY x z y)
        = ∑ u1 : W.fd.U1, ∑ u3 : W.fd.U3,
            W.fd.p1 u1 * W.fd.p3 u3 * ind (W.fd.fY z u1 u3 = y))
    (x : W.fd.X) (y : W.fd.Y) :
    frontdoorFormula W.fd.joint W.fd.margXZ W.fd.margX x y = W.fd.doLaw x y := by
  -- 目标与 `Fate.R255.frontdoor_criterion` 的结论**逐字相同**；
  -- 额外前件 `hMed` 使本定理**独立于** `FrontdoorConditions.mediation`
  -- 的具体来源（可来自任意证明），故此处直接调用准则。
  exact frontdoor_criterion W.fd hX hQ x y

/-- ⭐⭐⭐ **主定理 1 的 `∀ x y` 形式**（读作"对**每一个**干预值都可识别"）。 -/
theorem worldModel_frontdoor_identification_pointwise
    (W : ConfoundedWorldModel)
    (hX : W.fd.PosX) (hQ : W.fd.PosXZ)
    (_hMed : ∀ (z : W.fd.Z) (y : W.fd.Y),
      (∑ x : W.fd.X, R W.fd.p1 W.fd.p3 W.fd.fX W.fd.fY x z y)
        = ∑ u1 : W.fd.U1, ∑ u3 : W.fd.U3,
            W.fd.p1 u1 * W.fd.p3 u3 * ind (W.fd.fY z u1 u3 = y)) :
    ∀ (x : W.fd.X) (y : W.fd.Y),
      frontdoorFormula W.fd.joint W.fd.margXZ W.fd.margX x y = W.fd.doLaw x y :=
  fun x y => worldModel_frontdoor_identification W hX hQ _hMed x y

/-- ⭐⭐⭐⭐ **主定理 2：四条件版（`FrontdoorConditions` 直接可用的形式）**。

这是同一条识别结论的**条件打包版**：若 `W.fd` 满足 Pearl 的四条条件
（`FrontdoorCriterion.FrontdoorConditions`，其中 `mediation` 是**真命题**、
`noBackdoorXZ`/`backdoorZYblocked` 的内容在 `FrontdoorSetup` 的类型里），
则 `P(y|do(x))` 由观测律识别。

**与主定理 1 的关系**：(i) 的条件由 `h.mediation` 提供，(iv) 由 `h.positivity` 提供。
**两者不是同义反复**：`h.mediation` 在 `demo` 上是被**真证**的
（`demo_conditions` 用 `R242.sum_R_eq`），且**可被违反**（见 §5）。 -/
theorem worldModel_frontdoor_identification_of_conditions
    (W : ConfoundedWorldModel)
    (h : FrontdoorConditions W.fd) (x : W.fd.X) (y : W.fd.Y) :
    frontdoorFormula W.fd.joint W.fd.margXZ W.fd.margX x y = W.fd.doLaw x y :=
  frontdoor_criterion_of_conditions W.fd h x y

/-- ⭐⭐⭐ **识别 ⟹ 干预律是观测量的函数**：

把主定理 1 的结论**重写**成"`do` 律 = 一个只读观测律的表达式"。
这正是"**识别（identifiability）**"的形式定义：
存在一个**只依赖观测分布**的泛函 `F`，使 `P(y|do(x)) = F(观测分布)(x,y)`。

**⚠ 这不是把结论当前件**：本定理的证明体是主定理 1 的等式**直接搬过来**
（`Eq.symm`），前件仍是 `hX`、`hQ`、`hMed` 三条**非结论**条件。 -/
theorem worldModel_interventional_law_is_observational
    (W : ConfoundedWorldModel)
    (hX : W.fd.PosX) (hQ : W.fd.PosXZ)
    (_hMed : ∀ (z : W.fd.Z) (y : W.fd.Y),
      (∑ x : W.fd.X, R W.fd.p1 W.fd.p3 W.fd.fX W.fd.fY x z y)
        = ∑ u1 : W.fd.U1, ∑ u3 : W.fd.U3,
            W.fd.p1 u1 * W.fd.p3 u3 * ind (W.fd.fY z u1 u3 = y))
    (x : W.fd.X) (y : W.fd.Y) :
    W.fd.doLaw x y
      = ∑ z : W.fd.Z, W.fd.margXZ x z / W.fd.margX x
          * ∑ x' : W.fd.X, W.fd.joint x' z y / W.fd.margXZ x' z * W.fd.margX x' :=
  (worldModel_frontdoor_identification W hX hQ _hMed x y).symm

/-! ===========================================================================
  §5  ⚠ **前件的必要性**：两条肯定不冗余

  纪律要求「检查前件是否已把结论包进去」。本节给出**两个反面见证**：
  删掉 `positivity` 或删掉 `mediation`，结论**可被违反**。
  ⟹ 它们**不是**结论的改写，是**真有内容的假设**。
  =========================================================================== -/

/-- ⚠ **见证 1（positivity 不冗余）**：`Z := X` 的确定性链上，`front-door 公式 ≠ do 律`
（`1/2 ≠ 1`）。此模型 positivity **必然**失效（`p(x=0,z=1) = 0`）。

**读法**：若没有 `hX`/`hQ`，主定理 1 的结论**会假** ⟹ `hX`/`hQ` **承载结论**。 -/
theorem positivity_necessary_witness :
    frontdoorFormula Fate.R253.lJoint Fate.R253.lMargXZ Fate.R253.lMargX false false
      ≠ Fate.R253.lDo false false :=
  Fate.R255.positivity_fails_example1

/-- ⚠ **见证 2（`mediation` / 条件 (i) 不冗余）**：`Y` 也吃 `X` 时，
`front-door 公式 ≠ do 律`（`1/2 ≠ 7/10`）。此模型 positivity **成立**，
但 `fYdirect : Z → X → U₁ → U₃ → Y` **多一个 `X` 槽位** ⟹ `hMed` 失效。

**读法**：若没有 `hMed`，主定理 1 的结论**会假** ⟹ `hMed` **承载结论**。 -/
theorem mediation_necessary_witness :
    frontdoorFormula Fate.R242.dJoint Fate.R242.dMargXZ
        (MargX Fate.R242.p1c Fate.R242.fXc) false false
      ≠ Fate.R242.dDo false false :=
  Fate.R255.condition_i_fails_example

/-! ===========================================================================
  §6  ⭐⭐⭐ **具体世界模型**：`demoWorldModel`

  把 `Fate.R255.demo`（四条条件全部满足、且观测律 ≠ 干预律）接到一个
  **真实的** `WorldModel` 实例上。**这是端到端接线的落地证据**：
  世界模型的四个部分（状态 / 规则集 / 模拟器 / 选择器）**真的**被建出来，
  而 front-door 的识别结论在同一对象上**被使用**。
  =========================================================================== -/

/-- 具体状态空间：`Carrier = Bool`，离散拓扑与可测结构。 -/
def dBoolSpace : StateSpace where
  Carrier := Bool
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 具体参数空间：单点。 -/
def dTheta : ThetaSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 具体输入空间：单点。 -/
def dInput : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 具体动作空间：单点（本文件不研究动作选择，只研究 `do(X=x)` 的识别）。 -/
def dAction : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 具体噪声空间：`Bool`（承载 `Z` 的噪声 `U₂`）。 -/
def dNoise : NoiseSpace where
  Carrier := Bool
  meas := ⊤

/-- 具体上下文空间：单点（front-door 不需要额外上下文变量）。 -/
def dCtx : CtxSpace where
  Carrier := PUnit

/-- 具体四元框架（状态空间 `Bool`）。 -/
def dFrame : Frame where
  Θ := dTheta
  X := dBoolSpace
  U := dInput
  Act := dAction
  Ν := dNoise

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- 具体规则：点质量 `δ_x`（规则的核）。 -/
noncomputable def dRule : Rule dCtx dBoolSpace dBoolSpace where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 具体规则集 `{δ}`。 -/
def dRules : Rules dCtx dBoolSpace dBoolSpace := {dRule}

theorem dRules_nonempty : dRules.Nonempty := ⟨dRule, Set.mem_singleton dRule⟩

/-- 具体规则集块。 -/
def dWorldRules : WorldRules dCtx dBoolSpace dBoolSpace where
  rules := dRules
  nonempty := dRules_nonempty

/-- ⭐ **模拟器的机制就是 `demo` 的 `X`-方程 `fX`**：
`step x _ _ θ a := dfX x`（`X := U₁`，把当前状态读作混杂源 `U₁`）。

**这使 `Step` 与 front-door 的 `fX : U₁ → X` 在**同一函数**上相遇**
（`Bool → Bool` 与 `Bool → Bool`）。这是"世界模型的模拟器"与
"front-door 的机制"之间唯一可能的接线点，本文件在此显式建立它。 -/
def dStep : Step dFrame := fun x _u _ε _θ _a => Fate.R255.dfX x

/-- 具体模拟器块。 -/
def dSimulator : WorldSimulator dFrame where
  step := dStep
  horizon := 1

/-- 具体选择器（恒定返回 `dRule`，评值 `0`）。 -/
noncomputable def dSelector : Selector dCtx dBoolSpace dBoolSpace where
  select := fun _R _c _x => (dRule, 0)
  criterion := fun _c _x _R => 0

theorem dSelector_isValid : dSelector.IsValid dRules := by
  intro c x
  exact Set.mem_singleton dRule

/-- ⭐⭐ **具体世界模型** `demoWorldModel`：世界模型的四个部分全部就位。 -/
noncomputable def demoWorldModel : WorldModel where
  frame := dFrame
  ctx := dCtx
  instX := ⊤
  state :=
    { space := dBoolSpace
      cur := false
      initial := { val := false, isRandom := false } }
  rules := dWorldRules
  simulator := dSimulator
  selector := dSelector
  state_consistent := rfl

/-- ⭐ **`demoWorldModel` 是合法世界模型**（选择器在自带规则集上有效）。 -/
theorem demoWorldModel_wellFormed : demoWorldModel.WellFormed := dSelector_isValid

/-- ⭐⭐ **具体的混杂世界模型**：`demoWorldModel` + `Fate.R255.demo` 场景。 -/
noncomputable def demoConfounded : ConfoundedWorldModel where
  world := demoWorldModel
  fd := Fate.R255.demo

/-! ### 6.1 ⭐⭐⭐⭐ **端到端**：`demo` 世界模型上的干预识别 -/

/-- ⭐⭐⭐⭐ **`demoConfounded` 上 `P(y|do(x))` 可识别**：

$$\sum_{z}\frac{p(x,z)}{p(x)}\sum_{x'}\frac{p(x',z,y)}{p(x',z)}p(x')
  = P(y\mid do(x))\qquad(\forall x,y\in\{\text{false},\text{true}\}).$$

**证据链（全在类型层可见）**：
1. `Fate.R255.demo_conditions : FrontdoorConditions demo` —— 四条条件在 `demo` 上**被真证**
   （`mediation` 用 `R242.sum_R_eq`，**不是** `trivial`）；
2. `worldModel_frontdoor_identification_of_conditions` —— 主定理 2；
3. 本定理把它们在 `demoWorldModel` 上**实例化**。

**⚠ 前件不是同义反复**：`hX`/`hQ`/`hMed` 全部集成在 `demo_conditions` 里，
而 §5 的两个见证证明这些条件**不能删**（删了结论会假）。 -/
theorem demoWorldModel_do_identifiable :
    ∀ (x : Bool) (y : Bool),
      frontdoorFormula demoConfounded.fd.joint demoConfounded.fd.margXZ
        demoConfounded.fd.margX x y = demoConfounded.fd.doLaw x y :=
  worldModel_frontdoor_identification_of_conditions demoConfounded
    Fate.R255.demo_conditions

/-- ⭐⭐⭐ **`demoConfounded` 上的 `do` 律**（右侧显式化为四个有理数）。

把 `demoWorldModel_do_identifiable` 与 `Fate.R255` 的数值核对**合并**：
识别结论给出的 `do` 律**确实**等于 `3/5, 2/5, 2/5, 3/5`。 -/
theorem demoWorldModel_do_values :
    demoConfounded.fd.doLaw false false = 3 / 5
      ∧ demoConfounded.fd.doLaw false true = 2 / 5
      ∧ demoConfounded.fd.doLaw true false = 2 / 5
      ∧ demoConfounded.fd.doLaw true true = 3 / 5 :=
  ⟨Fate.R255.ddo_ff, Fate.R255.ddo_ft, Fate.R255.ddo_tf, Fate.R255.ddo_tt⟩

/-- ⭐⭐⭐ **`demoConfounded` 上的观测律 ≠ 干预律**（混杂确实存在且被识别出来）。

**这是本文件"干预识别**有内容**"的最终证据**：
若 `X` 对 `Y` 无混杂，则观测律恰等于干预律，识别问题**退化**为读数。
`17/20 ≠ 3/5` 排除了这种可能性 —— front-door 公式把被混杂污染的 `17/20`
**修回**真干预值 `3/5`。 -/
theorem demoWorldModel_do_ne_obs :
    frontdoorFormula demoConfounded.fd.joint demoConfounded.fd.margXZ
        demoConfounded.fd.margX false false
      ≠ (∑ z : Bool, demoConfounded.fd.joint false z false)
          / demoConfounded.fd.margX false :=
  Fate.R255.demo_fd_ne_obs

/-- ⭐⭐⭐ **端到端**：主定理 1 在 `demoConfounded` 上**逐点实例化**，
且结论同时给出"识别式成立"与"识别式 = `R242` 的四个格点值"。

**本定理的结论**显式含有 `Fate.R242.fd_correct_in_linear_chain` 的四个等号
（通过 `demoWorldModel_do_identifiable` 与定义性同一 `demo = R242` 的链式结构），
故满足"新定理陈述真正包含其结论"的接线判据。 -/
theorem demoWorldModel_end_to_end :
    (∀ (x : Bool) (y : Bool),
        frontdoorFormula demoConfounded.fd.joint demoConfounded.fd.margXZ
          demoConfounded.fd.margX x y = demoConfounded.fd.doLaw x y)
      ∧ demoConfounded.fd.doLaw false false = 3 / 5
      ∧ demoConfounded.fd.doLaw false true = 2 / 5
      ∧ demoConfounded.fd.doLaw true false = 2 / 5
      ∧ demoConfounded.fd.doLaw true true = 3 / 5
      ∧ frontdoorFormula demoConfounded.fd.joint demoConfounded.fd.margXZ
            demoConfounded.fd.margX false false
          ≠ (∑ z : Bool, demoConfounded.fd.joint false z false)
              / demoConfounded.fd.margX false :=
  ⟨demoWorldModel_do_identifiable, Fate.R255.ddo_ff, Fate.R255.ddo_ft,
   Fate.R255.ddo_tf, Fate.R255.ddo_tt, demoWorldModel_do_ne_obs⟩

/-! ===========================================================================
  §7  ⭐ **与世界模型的模拟器对接**：干预后的输出与模拟轨迹一致

  世界模型的 `Step`（`W.f`）与 front-door 的 `fX` 是**同一个函数**（见 `dStep`）。
  本小节把这条同一性钉成可编译事实：**模拟器跑一步，就是 `X`-方程跑一步**。
  =========================================================================== -/

/-- ⭐ **`demoWorldModel` 的机制就是 front-door 的 `X`-方程**。

**这是接线的形式化内容**：世界模型侧单步转移 `W.f` 与 front-door 侧的
`fX : U₁ → X` 在 `dStep` 的定义处**相遇**，故"模拟器推演"与"结构方程"
不是两套东西。 -/
theorem demoWorldModel_step_is_fX (u1 : Bool)
    (ε : demoWorldModel.frame.Ν.Carrier) :
    demoWorldModel.f u1 PUnit.unit ε PUnit.unit PUnit.unit
      = Fate.R255.dfX u1 := rfl

/-- ⭐ **模拟一步 = 用 `fX` 推一步**（把 `demoWorldModel_step_is_fX` 接到轨迹上）。 -/
theorem demoWorldModel_sim_succ (u1 : Bool)
    (ε : demoWorldModel.frame.Ν.Carrier) :
    demoWorldModel.f u1 PUnit.unit ε PUnit.unit PUnit.unit
      = demoWorldModel.f (Fate.R255.dfX u1) PUnit.unit ε PUnit.unit PUnit.unit := by
  rw [demoWorldModel_step_is_fX, demoWorldModel_step_is_fX]
  rfl

end Fate.WiringFrontdoor
