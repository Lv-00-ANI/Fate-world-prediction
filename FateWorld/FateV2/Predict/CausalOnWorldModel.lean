/-
===============================================================================
  `CausalOnWorldModel` —— **因果 × 世界模型的接线层**

  ⚠⚠ **本文件是 P0 修复后的版本。原文件 8 个编译错误，且原头部声明与代码严重不符。
  修复内容与删除的定理在下面「⚠ 修复日志」逐条登记，不掩饰。**

-------------------------------------------------------------------------------
  ⭐ 本文件**实际交付**的内容（与代码逐条对应，无一项虚报）
-------------------------------------------------------------------------------
  | # | 名称 | 内容 |
  |---|---|---|
  | §1 | `doLaw` | `SCMSemantics.doLaw` 的别名（`CausalRouteDo` 语义）|
  | §1 | `doLaw_eq` | 定义展开（`rfl`）|
  | §2 | `DoLawOn` | 「后门载体的可观测侧与 SCM 一致」的精确定义（5 场）|
  | §2 | `bd_joint_obs` | `hZ.joint` 的读出（逐 `(x,z₁,z₂,y)`）|
  | §3 | `bd_sum_joint` | ⭐ **把 `joint` 对 `z₂` 求和**：`Σ pXZ·pYcond = condY · Σ pZ` |
  | §3 | `zb_pZ_sum` | `zb` 的 `pZ` 关于 `z₂` 归一（`7/20 + 13/20 = 1`）|
  | §4 | `badd` / `badd_pZ_sum` | ⚠ 一个 `pz₁` 不归一的 setup（`pz₁ ≡ 3`，故 `Σ pZ = 3`）|
  | §4 | `DoLawOn_fails_on_badd` | ⚠⚠ **`DoLawOn` 可失败**（前件非空转的机检见证）|

-------------------------------------------------------------------------------
  ⚠⚠ 修复日志（P0，必读；逐条对应原文件的 8 个错误）
-------------------------------------------------------------------------------

  **【错误 1｜146:7 `dependsOnNoncomputable`】—— 纯语法，已修**
  `abbrev doLaw` 依赖 `SCMSemantics.doLaw`（`noncomputable`），故须加
  `noncomputable`。**不改任何陈述，纯装饰性修复。**

  **【错误 2｜186:44 `HMul ℝ (T.Z₂t → ℝ)`】—— 实质性类型错误，已修**
  `DoLawOn.margX_of` 字段原写作

  ```
  ∑ z₂ : T.Z₂t, FateV2.Predict.R277.pXZ T x z₁ z₂ = SCMSemantics.marginalX M x * FateV2.Predict.R277.pZ T z₁
  ```

  但 `FateV2.Predict.R277.pZ : Z₁ → Z₂t → ℝ`（**柯里化二元**，实测
  `Fate/BackdoorGenuine.lean:739`）。故 `pZ T z₁ : Z₂t → ℝ` 是一个**函数**，
  与 `ℝ` 相乘不存在实例 ⟹ 该结构体**根本无法声明**。
  修复：改为 `marginalX M x * T.pz₁ z₁`（`pz₁ : Z₁ → ℝ`，正是该字段原本注释
  「`∑_{z₂} pXZ = p(x)·pz₁`」所写的内容）。**这是把一行打错的类型改对，
  不是改陈述** —— 原陈述因类型错误并不存在。

  **【错误 3-6｜216/233/267/293 `Unknown identifier DoLawOn`】—— 级联，已随错误 2 消失**
  因结构体 `DoLawOn` 声明失败，Lean 未登记该名字，故全部使用处报「未知标识符」。
  这是错误的**下游回声**，不是 4 个独立缺陷。

  **【错误 7｜293:62 `unsolved goals hZ : sorry ⊢ False`】—— 实质性，已删定理**
  原文件 `bd_adjustLaw_eq` 的证明调用了**两个本仓库不存在**的引理：
  `bd_marg_univ`、`bd_condY_eq_doLaw`（`grep` 全库零命中）。
  其目标退化为 `hZ : sorry ⊢ False`。
  **⟹ 该定理的证明从未完成。** 见下文「删除清单」第 (1) 条。

  **【错误 8｜307 `Invalid name after end: Expected CausalOnWorldModel, but found Generic`】
  —— 纯笔误，已删**
  文件在 `namespace CausalOnWorldModel` 内，却写了 `end Generic`。

-------------------------------------------------------------------------------
  ⚠⚠⚠ 删除清单（证不出 / 陈述为假 ⟹ 按纪律 6 删除，**绝不 `sorry` 占位**）
-------------------------------------------------------------------------------

  **(1) `bd_adjustLaw_eq`** —— 陈述
  `adjustLaw zb x y = doLaw M x y`（由 `hZ` + `hM : Σ pU = 1`）。
  **为什么删**：该命题**不可由前件推出**。
  * `hZ.margX` 只给 `marginalX M x = Σ_{z₁,z₂} pXZ`。配合 `hM`（`Σ pU = 1`）
    得 `Σ_x Σ_{z₁,z₂} pXZ = 1`，但**不能**逐点得 `marginalX M x = 1`
    （原证明想要的 `hmarg_one` 依赖**逐点**归一，这是错的）。
  * 即使补上 `marginalX ≡ 1`，「`condY = doLaw`」**仍需 `pU` 非负**：
    取 `U = {0,1,2}`、`pU = (1,-1,1)`（和为 1）、`sg 0 .1 = x`、
    `sg 1 .1 = sg 2 .1 ≠ x`、`sg 0 .2 x = sg 1 .2 x = true`、`sg 2 .2 x = false`，
    则 `marginalX x = 1`，而 `condY x true = 1`、`doLaw x true = 0`。**反例成立。**
  * 再加上 `zb_adjustLaw_eq`（`Fate/BackdoorGenuine.lean:923`）已证
    `adjustLaw zb = doLaw2 zb`（即 `pYdo` 版），而 `doLaw2 ≠ condY`
    （`zb` 上 `obs ≠ do`）⟹ 原陈述在 `zb` 上本身也站不住。

  **(2) `bd_adjustLaw_sum_eq_condY`** —— 陈述
  `adjustLaw zb x y = condY M x y * (S/S)`，其中 `S = Σ_{z₂} pZ zb () z₂`。
  **为什么删**：`S/S = 1`，故它等价于 **`adjustLaw zb = condY M`**，该式**为假**。
  **代数错误的根源**：`adjustLaw = Σ_{z₂} pYcond·pZ`，而 `hZ.joint` 控制的是
  `pXZ·pYcond`。二者仅在 `pXZ = pZ` 时相同，而 `zb` 里 **`pXZ ≠ pZ`**
  （`pXZ` 带 `fX` 指示函数）。由 `hZ.joint` 求和**只能**得到

  ```
  Σ_{z₂} pXZ·pYcond = condY · Σ_{z₂} pZ      （= 本文件的 `bd_sum_joint`）
  ```

  这是**观测**律 `P(x,y)` 的分解，**不是** `adjustLaw`。
  数值验证：`adjustLaw zb true false = 13/20`（`zb_adjustLaw_eq` + `zb_doLaw2`），
  而 `Σ pXZ·pYcond` 在 `(true,false)` 处 `= pXZ(true,true) = 3/5`（`Y = x⊕z₂`
  确定）。**`13/20 ≠ 3/5` ⟹ 原陈述假。**
  **⟹ 这是原文件里唯一的「实质性命题问题」，已如实删除。**

  **(3) `DoLawOn_fails_on_zb_T35`** —— 陈述
  `¬ DoLawOn zb (fun _ _ => 0) FateV2.Predict.T35.M`。
  **为什么删**：**类型不符，无法陈述**。`DoLawOn T d M` 要求
  `M : SCM T.Xt T.Yt`，而 `FateV2.Predict.T35.M : SCM (Fin 2) (Fin 2)`
  （`Fate/T35Confounding.lean:49`），`zb` 的 `Xt = Yt = Bool`。
  `Fin 2 ≠ Bool` ⟹ 该类型归属失败（这正是错误 7 里目标退化为 `⊢ False` 的原因）。
  **替代**：本文件用**同型但类型正确**的见证 `DoLawOn_fails_on_badd`（§4），
  它证明 `DoLawOn` 的 `pZ_sum` 字段**可失败** ⟹ 结构体非恒真、前件真承载内容。

-------------------------------------------------------------------------------
  ⚠ 诚实边界（必读）
-------------------------------------------------------------------------------
  1. **本文件不做「前门/后门公式对给定 SCM 正确」的证明**，那是
     `WiringFrontdoor` / `WiringBackdoorFixed` 各自在自己载体上的工作。
  2. **`FrontdoorSetup` / `ZBlockedSetup` 与 `SCM` 之间不存在类型层等同**。
     本仓库**没有**「图-核对应引理」，故 `DoLawOn` 的全部字段都是**假设**。
  3. **本文件不声称任何「前门 = 后门 = `doLaw`」的等式链。**
     原头部大段宣称的 §4/§5/§6（`frontdoor_eval_on_worldModel`、
     主定理 `frontdoor_eq_backdoor_on_worldModel`、§5.5/§5.6 反例、§6 实例）
     **在代码中一条都不存在**（全库 `grep` 零命中）。
     **故本文件不宣称它，本文件头也不再宣称它。** 该空位仍然空着。
  4. 全部**有限**离散（`Fintype`，`ℝ` 值），无测度论。
  5. **不修改任何已有模块**，只 `import`。
  6. **零 `sorry` / 零 `admit` / 零 `axiom`**（可 `grep` 验证）。
=============================================================================== -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import FateWorld.FateV2.Predict.WiringFrontdoor
import FateWorld.FateV2.Predict.WiringBackdoorFixed
import FateWorld.FateV2.Predict.AdjustmentUnified
import FateWorld.FateV2.Predict.CausalRouteDo
import FateWorld.FateV2.Loop.DoLawWorldModel
import FateWorld.FateV2.Predict.T34DoPushforward
import FateWorld.FateV2.Predict.Rule1Semantic
import FateWorld.FateV2.Predict.BackdoorGenuine
set_option autoImplicit false

namespace FateV2.Predict

open FateV2.Loop
namespace CausalOnWorldModel

open Finset

/-!
  # Predict · CausalOnWorldModel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausalOnWorldModel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WiringFrontdoor, WiringBackdoorFixed, AdjustmentUnified, CausalRouteDo, DoLawWorldModel, T34DoPushforward, Rule1Semantic, BackdoorGenuine
  - 补充 open 域：FateV2.Loop
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  **载体与记号**
  =========================================================================== -/

/-- **世界模型侧的 `doLaw`**：`CausalRouteDo` / `SCMSemantics` 的 `doLaw`。

⭐ 显式取带命名空间的全名，使读者一眼看到本文件用的是 `SCMSemantics.doLaw`
（干预律），而**不是** `FrontdoorSetup.doLaw`。

**⚠ 修复 1**：加 `noncomputable`（`SCMSemantics.doLaw` 是 `noncomputable`）。 -/
noncomputable abbrev doLaw {X Y : Type} [DecidableEq Y] (M : PearlHierarchy.SCM X Y) : X → Y → ℝ :=
  FateV2.Modeling.SCMSemantics.doLaw M

/-- ⭐ **定义展开**（`rfl`）：本文件的 `doLaw` 逐字就是显式求和式。 -/
theorem doLaw_eq {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : PearlHierarchy.SCM X Y) (x : X) (y : Y) :
    doLaw M x y = ∑ u, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0) := rfl

/-! ===========================================================================
  §2  ⭐⭐ **`DoLawOn`：「后门载体的可观测侧与 SCM 一致」**

  **⚠ 注意（诚实边界）**：`joint` 字段把 `pXZ·pYcond` 接到 `condY·pZ`。它给出的是
  **观测**律的分解（`bd_sum_joint`），**不是** `adjustLaw` 的分解
  （`adjustLaw` 用 `pYcond·pZ`，而 `pZ ≠ pXZ`）。原文件把两者混为一谈，
  导致了被删除的 (1)(2) 两个假命题。见头部「删除清单」。
  =========================================================================== -/

/-- ⭐⭐ **后门载体的可观测侧与 SCM 一致**（四条逐点等式 + 一条登记）。

**⚠ 修复 2**：`margX_of` 原写作 `= marginalX M x * pZ T z₁`，但
`pZ : Z₁ → Z₂t → ℝ` 是柯里化二元的，`pZ T z₁ : Z₂t → ℝ` 是函数，
与 `ℝ` 相乘无实例 ⟹ 结构体无法声明。
改为 `* T.pz₁ z₁`（`pz₁ : Z₁ → ℝ`，即原注释所写的 `pz₁` 归一）。 -/
structure DoLawOn (T : FateV2.Predict.R277.ZBlockedSetup) (d : T.Xt → T.Yt → ℝ)
    (M : PearlHierarchy.SCM T.Xt T.Yt) : Prop where
  /-- ⭐ **`p(x)`**：`∑_{z₁ z₂} pXZ T x z₁ z₂ = M.marginalX x`。 -/
  margX : ∀ x : T.Xt,
    ∑ z₁ : T.Z₁, ∑ z₂ : T.Z₂t, FateV2.Predict.R277.pXZ T x z₁ z₂ = SCMSemantics.marginalX M x
  /-- ⭐ **单点 `z₁` 的 `p(x)`**：`∑_{z₂} pXZ = marginalX x · pz₁ z₁`。 -/
  margX_of : ∀ (z₁ : T.Z₁) (x : T.Xt),
    ∑ z₂ : T.Z₂t, FateV2.Predict.R277.pXZ T x z₁ z₂ = SCMSemantics.marginalX M x * T.pz₁ z₁
  /-- ⭐ **`pZ` 关于 `z₂` 归一**（`∑_{z₂} pZ(z₁,z₂) = 1`）。 -/
  pZ_sum : ∀ z₁ : T.Z₁, ∑ z₂ : T.Z₂t, FateV2.Predict.R277.pZ T z₁ z₂ = (1 : ℝ)
  /-- ⭐ **联合质量**：`pXZ(x,z₁,z₂)·P(y|x,z₁,z₂) = M.condY x y · pZ(z₁,z₂)`。 -/
  joint : ∀ (x : T.Xt) (z₁ : T.Z₁) (z₂ : T.Z₂t) (y : T.Yt),
    FateV2.Predict.R277.pXZ T x z₁ z₂ * FateV2.Predict.R277.pYcond T x z₁ z₂ y
      = SCMSemantics.condY M x y * FateV2.Predict.R277.pZ T z₁ z₂
  /-- ⭐ **登记**：参数 `d` 就是 `M` 的干预律（`d` 为参数，此处只作登记）。 -/
  interventional : ∀ (x : T.Xt) (y : T.Yt), d x y = FateV2.Modeling.SCMSemantics.doLaw M x y

variable {T : FateV2.Predict.R277.ZBlockedSetup}

/-- ⭐ **`joint` 的直接读出**（逐 `(x,z₁,z₂,y)`），另起一名使 §3 可读。 -/
theorem bd_joint_obs (M : PearlHierarchy.SCM T.Xt T.Yt) {d : T.Xt → T.Yt → ℝ}
    (hZ : DoLawOn T d M) (x : T.Xt) (z₁ : T.Z₁) (z₂ : T.Z₂t) (y : T.Yt) :
    FateV2.Predict.R277.pXZ T x z₁ z₂ * FateV2.Predict.R277.pYcond T x z₁ z₂ y
      = SCMSemantics.condY M x y * FateV2.Predict.R277.pZ T z₁ z₂ :=
  hZ.joint x z₁ z₂ y

/-! ===========================================================================
  §3  ⭐⭐ **`joint` 的求和形式**（这是 `hZ` **真正**给出的东西）

  **⚠ 为什么不是 `adjustLaw`**：见头部「删除清单 (2)」。
  `adjustLaw` 的权重是 `pZ`，`joint` 控制的是 `pXZ`，而 `zb` 上 `pXZ ≠ pZ`。
  =========================================================================== -/

/-- ⭐⭐ **把 `joint` 对 `z₂` 求和**：

$$\sum_{z_2} p(x,z_2)\cdot P(y\mid x,z_2) \;=\; P(X{=}x,Y{=}y)\cdot \sum_{z_2}p(z_2)$$

**⚠ 读法**：左边是**观测**律的分子（`pXZ` 加权），右边是 `condY` 乘 `pZ` 总质量。
**它不是** `adjustLaw`（后者用 `pZ` 加权）。 -/
theorem bd_sum_joint (M : PearlHierarchy.SCM Bool Bool) {d : Bool → Bool → ℝ}
    (hZ : DoLawOn FateV2.Predict.R277.zb d M) (x y : Bool) :
    ∑ z₂ : Bool, FateV2.Predict.R277.pXZ FateV2.Predict.R277.zb x () z₂
        * FateV2.Predict.R277.pYcond FateV2.Predict.R277.zb x () z₂ y
      = SCMSemantics.condY M x y * (∑ z₂ : Bool, FateV2.Predict.R277.pZ FateV2.Predict.R277.zb () z₂) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z₂ _ => hZ.joint x () z₂ y)

/-- ⭐ `zb` 的 `pZ` 关于 `z₂` **归一**（`7/20 + 13/20 = 1`）——
即 `DoLawOn.pZ_sum` 在 `zb` 上**成立**。 -/
theorem zb_pZ_sum : ∀ z₁ : Unit, ∑ z₂ : Bool, FateV2.Predict.R277.pZ FateV2.Predict.R277.zb z₁ z₂ = (1 : ℝ) := by
  intro z₁
  rw [Fintype.sum_bool, FateV2.Predict.R277.zb_pZ, FateV2.Predict.R277.zb_pZ]
  norm_num

/-! ===========================================================================
  §4  ⚠⚠ **`DoLawOn` 可失败**（前件非空转的机检见证）

  原文件的 `DoLawOn_fails_on_zb_T35` 是它想说的话，但**类型不对**
  （`T35.M : SCM (Fin 2) (Fin 2)` 而 `DoLawOn zb` 要求 `SCM Bool Bool`），
  故无法陈述。这里用**类型正确**的见证替代：构造一个 `pz₁` 不归一的 setup
  `badd`，则 `pZ_sum` 失败 ⟹ `DoLawOn` 对它**不成立**。
  =========================================================================== -/

/-- ⚠ 一个 `pz₁ ≡ 3`（**不归一**）的 `ZBlockedSetup`，其余同 `zb`。 -/
noncomputable def badd : FateV2.Predict.R277.ZBlockedSetup where
  Z₁ := Unit
  Z₂t := Bool
  Ux := Bool
  Uz₂ := Bool
  Uy := Unit
  Xt := Bool
  Yt := Bool
  pz₁ := fun _ => 3
  pu := fun ux => if ux then 3 / 4 else 1 / 4
  puz₂ := fun uz => if uz then 1 / 5 else 4 / 5
  py := fun _ => 1
  fX := FateV2.Predict.R277.zbFx
  fZ := FateV2.Predict.R277.zbFz
  fY := FateV2.Predict.R277.zbFy

/-- `badd` 的 `pZ` 总和是 `3`（而非 `1`）：`3 · (7/20 + 13/20) = 3`。 -/
theorem badd_pZ_sum : ∑ z₂ : Bool, FateV2.Predict.R277.pZ badd () z₂ = (3 : ℝ) := by
  unfold FateV2.Predict.R277.pZ badd
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_true, if_false,
    FateV2.Predict.R277.zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]
  norm_num

/-- ⚠⚠ **`DoLawOn` 对 `badd` 不成立**（`pZ_sum` 字段失败）。

**⟹ 这证明 `DoLawOn` 不是恒真式，其字段真的承载内容**——
即它作为前件不是空转的。 -/
theorem DoLawOn_fails_on_badd (M : PearlHierarchy.SCM Bool Bool) (d : Bool → Bool → ℝ) :
    ¬ DoLawOn badd d M := by
  intro hZ
  have h : ∑ z₂ : Bool, FateV2.Predict.R277.pZ badd () z₂ = 1 := hZ.pZ_sum ()
  rw [badd_pZ_sum] at h
  norm_num at h

end CausalOnWorldModel

end FateV2.Predict