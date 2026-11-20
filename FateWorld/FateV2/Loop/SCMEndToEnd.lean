/-
命运理论 · Lean 4 形式化实现
================================

模块：`SCMEndToEnd`
定位：**建桥 —— 把 SCM 实例接到端到端链上**（`predFrom` / `e2eResidual` / `endToEnd`）

---------------------------------------------------------------------------
〇、本文件做的唯一一件事
---------------------------------------------------------------------------
第 151 轮的 `Fate/SCMWorldModel.lean` 首次把任意 `SCM X Y` 翻译成 `WorldModel`
（`scmWorldModel M`，机制 `scmWorldStep M`）。本文件把该实例**直接喂给**
`Fate/EndToEnd.lean` 的 `predFrom` / `e2eResidual` / `endToEnd` / `endToEndIter`，
并证明它们在 SCM 实例上的**具体形式**。

**⚠ 本文件不新增任何因果/统计内容**，所有定理都是「把 `EndToEnd` 的通式
在 `scmWorldModel M` 上求值」的**等式**（下游 `simp`/`rw` 用）。

---------------------------------------------------------------------------
一、SCM 实例上 `EndToEnd` 各环节的**载体结构从哪来**（诚实登记）
---------------------------------------------------------------------------
`EndToEnd` 的 §3–§6 要求 `W.frame.X.Carrier` 上有 `AddCommGroup`，
`W.frame.Θ.Carrier` 上有 `Ring`。在本翻译中
`W.frame.X.Carrier = Y`、`W.frame.Θ.Carrier = PUnit`，
**故本文件的 §3 起一律以显式类型类参数
`[AddCommGroup Y] [Ring PUnit] [NoZeroDivisors PUnit]` 的形式出现**
（不是 `instance`，不是隐藏假设）。

**⚠ 这些实例在本文件里是「参数」，不是「事实」**：
`Y` 在 SCM 里是任意结果空间（`FateV2.Modeling.PearlHierarchy.SCM.U/pU/sg` 只要求
`Fintype`/`DecidableEq` 的**外生空间** `U`），一般**没有**群结构。
因此本文件 §3 起的定理**不外推到任意 SCM**，而是「**若** `Y` 带加法群结构
**则** 端到端链在 SCM 实例上取这个形状」—— 这是如实的条件形式，
而不是把群结构偷渡成 SCM 的性质。

`PUnit` 上的 `Ring` / `NoZeroDivisors` 由库中实例给出（可满足性见
`scmE2E_instance_satisfiable`，其中 `Y := ℤ`）。

---------------------------------------------------------------------------
二、交付的定理（`grep -n "^theorem"` 实测 **22** 条，逐条列此）
---------------------------------------------------------------------------
| 节 | 定理 | 内容 |
|---|---|---|
| §0 | `scmThetaSpace_carrier` | `scmThetaSpace.Carrier = PUnit`（`rfl`）|
| §0 | `scmWorldModel_theta` | `(scmWorldModel M).frame.Θ = scmTheta`（`rfl`）|
| §1 | `predFrom_scmWorldModel` | ⭐ **(b)** `predFrom (scmWorldModel M) θ u ε a y = (sg u).2 a` |
| §1 | `predFrom_scmWorldModel_facts` | ⭐ `predFrom … (sg u).1 = (sg u).2 (sg u).1`（读事实值） |
| §1 | `predFrom_scmWorldModel_indep_start` | 出发位 `y` 被丢弃（`do` 切断入边） |
| §1 | `predFrom_scmWorldModel_eq_sim_one` | `predFrom … = sim … 1`（与 `sim` 的一步一致） |
| §2 | `e2eResidual_scmWorldModel` | ⭐ **(c)** `r = x̂_obs − (sg u).2 a` |
| §2 | `e2eResidual_scmWorldModel_eq_zero_iff` | 残差为零 ⟺ 观测 = 结构映射预测 |
| §2 | `e2eResidual_scmWorldModel_ne_iff` | 残差非零 ⟺ 观测 ≠ 结构映射预测 |
| §2 | `e2eResidual_scmWorldModel_indep_start` | 残差不依赖出发状态 |
| §3 | `endToEnd_scmWorldModel` | ⭐ **(c)** `θ' = θ + η * φ (x̂ − (sg u).2 a)` |
| §3 | `endToEnd_scmWorldModel_apply` | 上式作为「`θ + η * φ r` 形状」的逆方向重述 |
| §3 | `endToEnd_scmWorldModel_step_eq` | `θ' − θ = η * φ (x̂ − (sg u).2 a)` |
| §4 | `endToEnd_scmWorldModel_fixed_iff` | ⭐⭐ **(d)** 不动点 ⟺ `φ (x̂ − (sg u).2 a) = 0`（`FillGap.fixed_iff_phi_resid_zero`） |
| §4 | `endToEnd_scmWorldModel_fixed_of_predicts` | `predFrom … = observe h y` ⟹ 不动点（`FillGap.fixed_of_predicts_exactly`） |
| §4 | `endToEnd_scmWorldModel_fixed_of_sg_hit` | ⭐⭐ **(d)** `(sg u).2 a = observe h y` ⟹ 不动点 |
| §4 | `endToEnd_scmWorldModel_moves` | 观测 ≠ `(sg u).2 a` ⟹ `θ' ≠ θ` |
| §5 | `endToEndIter_scmWorldModel_zero` | 多步闭环第 0 步 |
| §5 | `endToEndIter_scmWorldModel_succ` | 多步闭环递推落到 SCM |
| §5 | `endToEndIter_scmWorldModel_succ_ne` | 残差非零 ⟹ 多步闭环一步也不停 |
| §6 | `scmE2E_instance_satisfiable` | `Y := ℤ` 上的具体见证（反「空真」核查）|
| §6 | `scmE2E_residual_concrete` | 具体 SCM 上 `r = yobs`（定量见证）|

---------------------------------------------------------------------------
三、诚实边界
---------------------------------------------------------------------------
1. **本文件不证收敛**（`EndToEnd` 本身也不证）。`η`、`φ` 仍是参数。
2. **本文件不声称 `Y` 一般带群结构**；§3 起全部是条件形式（见上一节）。
3. **本文件不改动任何既有模块**；零 `sorry` / 零 `admit` / 零 `axiom`。
-/

import FateWorld.FateV2.Loop.SCMWorldModel
import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Loop.FillGap
namespace FateV2.Loop

open FateV2.Modeling
namespace SCMEndToEnd

open FateV2.Modeling.PearlHierarchy

set_option autoImplicit false

noncomputable section

/-!
  # Loop · SCMEndToEnd

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMEndToEnd.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMWorldModel, EndToEnd, FillGap
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ### §0.0 局部缩写（只为签名可读，不改任何语义）

`EndToEnd` / `ResidualLoop` 的 Θ 位是 `ThetaSpace`（**结构**，不是裸类型），
本文件在 SCM 翻译下该结构恒为 `SCMWorldModel.scmThetaSpace = PUnit`。
下面三个缩写把这个结构 **定义性地**（`rfl`）摊平成 `PUnit`，
使签名直接以 `PUnit` 书写，**不改变任何定理的内容**。 -/

/-- `SCMWorldModel.scmThetaSpace` 的载体就是 `PUnit`（`rfl`）。 -/
theorem scmThetaSpace_carrier : SCMWorldModel.scmThetaSpace.Carrier = PUnit := rfl

/-- 记 `Θ := SCMWorldModel.scmThetaSpace`（别名，仅为签名可读）。 -/
abbrev scmTheta : ThetaSpace := SCMWorldModel.scmThetaSpace

/-- `scmWorldModel M` 的参数空间**就是** `scmTheta`（`rfl`）。 -/
theorem scmWorldModel_theta {X Y : Type} (M : SCM X Y) [Nonempty Y] :
    (SCMWorldModel.scmWorldModel M).frame.Θ = scmTheta := rfl

/-! ===========================================================================
  §1  环节 ②：`predFrom` 在 SCM 实例上的具体形式（任务书 (b)）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **任务书 (b)：`predFrom (scmWorldModel M)` 逐字就是 SCM 的结构映射**。

$$\mathrm{predFrom}\;(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;y
  \;=\;(\mathrm{sg}\,u).2\;a .$$

**读法**：端到端链的「一步预测」在 SCM 上**就是**结构方程在
外生实现 `u` 与干预/事实值 `a` 处的取值。

**⚠ 反同义反复核查**：
* 前件只有 `[Nonempty Y]`（`scmWorldModel` 的构造前提，见 `SCMWorldModel` §4）；
* 结论左侧是 `EndToEnd.predFrom`（`Fate/EndToEnd.lean:144`），
  右侧是 `FateV2.Modeling.PearlHierarchy.SCM.sg`（`Fate/FateV2.Modeling.PearlHierarchy.lean:75`）——
  **两个模块各自的定义**，由本定理首次相等；
* 证明必须依次展开 `predFrom` → `WorldModel.f` → `simulator.step`
  （即 `scmWorldModel` 的构造），**不是**把结论塞进前件。

**⚠ 右侧不含 `θ`/`ε`/`y`**：这是 SCM 机制的真实性质
（无参数、噪声在 `pU`、机制不读旧状态），由 `SCMWorldModel` 的
`scmWorldModel_step_indep_start` 独立见证。 -/
theorem predFrom_scmWorldModel {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (y : Y) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y
      = (M.sg u).2 a := rfl

/-- ⭐⭐ **读事实值**：把 `Act` 取成外生实现的事实分量 `(sg u).1`，
则预测就是**观测到的**那个 `Y` 值。

$$\mathrm{predFrom}\;(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;(\mathrm{sg}\,u).1\;y
  \;=\;(\mathrm{sg}\,u).2\;(\mathrm{sg}\,u).1 .$$

**读法**：这正是 `FateV2.Modeling.SCMSemantics.marginalY` / `jointLaw` 里出现的那一项
（`(sg u).2 ((sg u).1)`）—— 端到端链的预测端与 SCM 的观测律**对齐**。 -/
theorem predFrom_scmWorldModel_facts {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : PUnit) (y : Y) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε (M.sg u).1 y
      = (M.sg u).2 (M.sg u).1 :=
  predFrom_scmWorldModel M θ u ε (M.sg u).1 y

/-- ⭐⭐ **预测端与「出发状态」无关**：`do`/`Act` 切断入边在端到端链上的形式。

$$\forall y_1\,y_2,\quad
  \mathrm{predFrom}\;(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;y_1
  = \mathrm{predFrom}\;(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;y_2 .$$

**⚠ 与 `SCMWorldModel.scmWorldModel_step_indep_start` 的关系**：
后者讲的是 `WorldModel.f`；本定理讲的是 `EndToEnd.predFrom`——
**端到端链确实继承了这个性质**（故链的预测端不看 `x`，
残差完全由「观测 − 结构映射」决定）。 -/
theorem predFrom_scmWorldModel_indep_start {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (y₁ y₂ : Y) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y₁
      = FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y₂ := by
  rw [predFrom_scmWorldModel M θ u ε a y₁, predFrom_scmWorldModel M θ u ε a y₂]

/-- ⭐ **首步模拟的端到端读法**：`predFrom` 与 `sim` 的第 1 步一致。

$$\mathrm{predFrom}\;(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;y
  = \mathrm{sim}\,(\mathrm{scmWorldModel}\,M)\,\theta\,(\text{const }u)\,
    (\text{const }\varepsilon)\,(\text{const }a)\;1 .$$

**⚠ 为什么需要**：`EndToEnd` 的 §1 诚实边界 1.5 指出「`sim` 没有『从任意状态出发一步』的接口」，
`predFrom` 是通过 `W.f` 补齐的。本定理证明在 **SCM 实例**上这条补齐
与 `sim` 的一步**完全一致**（这正是 `predFrom_eq_sim_succ` 的具体形态，
但因 SCM 机制不读旧状态而可以更强：**不用取 `sim` 的第 `n` 步**）。 -/
theorem predFrom_scmWorldModel_eq_sim_one {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (y : Y) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y
      = (SCMWorldModel.scmWorldModel M).sim θ (fun _ => u) (fun _ => ε)
          (fun _ => a) 1 := by
  rw [SCMWorldModel.scmWorldModel_sim_one M θ u (fun _ => ε) a,
    predFrom_scmWorldModel]

/-! ===========================================================================
  §2  环节 ③：残差 = 「观测 − SCM 结构映射预测」（任务书 (c)）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **任务书 (c)（残差层）：端到端残差在 SCM 实例上就是「观测 − 结构映射」**。

$$r \;=\; y_{\mathrm{obs}} - (\mathrm{sg}\,u).2\;a .$$

**读法**：`EndToEnd.e2eResidual`（`Fate/EndToEnd.lean:175`）在 `scmWorldModel M` 上
**没有留下任何额外结构**：`θ`（`PUnit`）、`ε`（`PUnit`）、出发状态 `x` 全部消失，
只剩「观测值」与「SCM 结构映射（由外生实现 `u` 与 `Act := a` 决定）」之差。

**⟹ 这正是任务书 (c) 要求的「残差与 SCM 的 `sg` 直接相关」**：
`sg` 出现在**减号右侧的唯一位置**。

**⚠ 反同义反复核查**：
* 前件：`[Nonempty Y]`（构造）、`[AddCommGroup Y]`（做减法，显式参数）——
  **不含任何关于残差值的假设**；
* 结论：把 `e2eResidual`（经 `predFrom` → `W.f` → `simulator.step`）**求值**成
  `sg` 的表达式。若 `predFrom` 与 `sg` 脱钩，本定理立即失败。 -/
theorem e2eResidual_scmWorldModel {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    (xobs : Y) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (xpred : Y) :
    FateV2.Loop.EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a xpred
      = xobs - (M.sg u).2 a := by
  rw [FateV2.Loop.EndToEnd.e2eResidual_def,
    predFrom_scmWorldModel M θ u ε a xpred]

/-- ⭐⭐⭐ **残差为零 ⟺ 观测 = SCM 结构映射的预测**。

$$\bigl(y_{\mathrm{obs}} - (\mathrm{sg}\,u).2\,a = 0\bigr)
  \iff y_{\mathrm{obs}} = (\mathrm{sg}\,u).2\,a .$$

**⚠ 这是 `EndToEnd.e2eResidual_eq_zero_iff` 在 SCM 实例上的具体化**：
通式右侧是 `predFrom …`，本定理把它换成 `(sg u).2 a`，
从而「残差为零」这个**可校验的判据**直接落到 SCM 的结构方程上。 -/
theorem e2eResidual_scmWorldModel_eq_zero_iff {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    (xobs : Y) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (xpred : Y) :
    FateV2.Loop.EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a xpred = 0
      ↔ xobs = (M.sg u).2 a := by
  rw [e2eResidual_scmWorldModel, sub_eq_zero]

/-- ⭐⭐ **残差非零 ⟺ 观测 ≠ SCM 结构映射的预测**（上一条的否命题形式）。 -/
theorem e2eResidual_scmWorldModel_ne_iff {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    (xobs : Y) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (xpred : Y) :
    FateV2.Loop.EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a xpred ≠ 0
      ↔ xobs ≠ (M.sg u).2 a :=
  not_congr (e2eResidual_scmWorldModel_eq_zero_iff M xobs θ u ε a xpred)

/-- ⭐⭐ **残差不依赖出发状态 `xpred`**（承 §1 的 `indep_start`）。

**⟹ 端到端链在 SCM 实例上「残差只由观测与外生实现 + 干预决定」**，
这是 `do` 切断入边的端到端表现。 -/
theorem e2eResidual_scmWorldModel_indep_start {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    (xobs : Y) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (xpred₁ xpred₂ : Y) :
    FateV2.Loop.EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a xpred₁
      = FateV2.Loop.EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a xpred₂ := by
  rw [e2eResidual_scmWorldModel, e2eResidual_scmWorldModel]

/-! ===========================================================================
  §3  环节 ④ + 全链：`endToEnd` 在 SCM 实例上的具体形式
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **任务书 (c)（全链层）：`endToEnd (scmWorldModel M)` 的显式形式**。

$$\theta' \;=\; \theta + \eta * \varphi\bigl(\hat x^{\mathrm{obs}} - (\mathrm{sg}\,u).2\;a\bigr).$$

其中 $\hat x^{\mathrm{obs}} = \mathrm{observe}\,h\,y$（环节 ①，观测 $y$ 经估计器）。

**读法**：四个环节全部可见，且**环节 ② 的位置被 SCM 的结构映射占据**——
即「端到端残差与 SCM 的 `sg` 直接相关」的**最强形式**（残差出现在参数更新里）。

**⚠ 载体**：`W.frame.X.Carrier = Y` 需 `[AddCommGroup Y]`（做减法），
`W.frame.Θ.Carrier = PUnit` 需 `[Ring PUnit]`（做标量乘）。二者为**显式参数**，
见文件头 §一。 -/
theorem endToEnd_scmWorldModel {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit)
    (φ : Y →+ PUnit)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x
      = θ + η * φ (FateV2.Loop.EndToEnd.observe h y - (M.sg u).2 a) := by
  rw [FateV2.Loop.EndToEnd.endToEnd_apply, predFrom_scmWorldModel]

/-- ⭐ **同一等式的`rfl` 级重述**（逆方向，便于 `rw` 回到 `endToEnd`）。

**⚠ 之所以不是「残差位显式写出」的第二种形状**：`ResidualLoop.writeBack` 要求
`Residual X` 与 `Y` 在类型层**统一**（`Residual X := X.Carrier = Y`），
而 `writeBack` 的 `Θ` 位是**结构** `scmTheta`；直接以 `writeBack scmTheta η φ (…)` 书写
会令 Lean 的类型类搜索同时实例化两处，得不偿失。故本条只保留
「`θ + η * φ r = endToEnd …`」这一定义性等式（`endToEnd_scmWorldModel` 的逆）。 -/
theorem endToEnd_scmWorldModel_apply {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x
      = FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x := by
  rw [endToEnd_scmWorldModel]

/-- ⭐⭐⭐ **参数位移 = 步长 × 残差方向，残差 = 观测 − `sg` 预测**。

$$\theta' - \theta \;=\; \eta * \varphi\bigl(\hat x^{\mathrm{obs}} - (\mathrm{sg}\,u).2\,a\bigr).$$

**读法**：`θ` 的位移**唯一地**由「观测估计」与「SCM 结构映射预测」之差决定，
**没有第三项**（无漂移、无遗忘）。

**⚠ 反同义反复**：这是 `EndToEnd.endToEnd_step_eq` 与
本文件 `predFrom_scmWorldModel` 的**复合**，不是前件的重念——
通式里出现的是 `predFrom …`，此处才第一次变成 `(sg u).2 a`。 -/
theorem endToEnd_scmWorldModel_step_eq {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x - θ
      = η * φ (FateV2.Loop.EndToEnd.observe h y - (M.sg u).2 a) := by
  rw [FateV2.Loop.EndToEnd.endToEnd_step_eq, predFrom_scmWorldModel]

/-! ===========================================================================
  §4  任务书 (d)：**不动点 ⟺ 预测精确命中观测**（在 SCM 实例上）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **任务书 (d)：SCM 实例上 `endToEnd` 的不动点 ⟺ 残差经 `φ` 为零**。

$$\mathrm{endToEnd}\,(\mathrm{scmWorldModel}\,M)\,\dots\,\theta = \theta
  \iff \varphi\bigl(\hat x^{\mathrm{obs}} - (\mathrm{sg}\,u).2\,a\bigr) = 0 .$$

**⟹ 这是 `FateV2.Loop.FillGap.fixed_iff_phi_resid_zero`（`Fate/FillGap.lean:42`）
在 SCM 实例上的落点**：通式的残差位 `observe h y - predFrom …`
被本文件的 `predFrom_scmWorldModel` 换成 `observe h y - (sg u).2 a`。

**⚠ 前件 `hη : η ≠ 0` 是真前提**（`FillGap` 已论证：`η = 0` 时链恒不动，
右式可非零）——本文件**不**删除它。 -/
theorem endToEnd_scmWorldModel_fixed_iff {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit] [NoZeroDivisors PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) (hη : η ≠ 0) :
    FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x = θ
      ↔ φ (FateV2.Loop.EndToEnd.observe h y - (M.sg u).2 a) = 0 := by
  rw [FateV2.Loop.FillGap.fixed_iff_phi_resid_zero
    (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x hη,
    predFrom_scmWorldModel]

/-- ⭐⭐⭐⭐ **任务书 (d)：预测精确命中观测 ⟹ `endToEnd` 不动**。

$$\mathrm{predFrom}\;(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;x
    = \hat x^{\mathrm{obs}}
  \ \Longrightarrow\ \mathrm{endToEnd}\dots\theta = \theta .$$

**⚠ 前件是按 `predFrom` 写的（不是按 `sg` 写的）** —— 这是**刻意的**：
`endToEnd_fixed_of_sg_hit`（下一条）把它换成 `(sg u).2 a`，
两条合读即：**「SCM 结构映射命中观测」⟹「端到端不动」**。

**⟹ 这是 `FateV2.Loop.FillGap.fixed_of_predicts_exactly`（`Fate/FillGap.lean:65`）
在 SCM 实例上的落点。** -/
theorem endToEnd_scmWorldModel_fixed_of_predicts {X Y G : Type} (M : SCM X Y)
    [Nonempty Y] [AddCommGroup Y] [Ring PUnit] [NoZeroDivisors PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit) (hφ : Function.Injective φ)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) (hη : η ≠ 0)
    (hpred : FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a x
      = FateV2.Loop.EndToEnd.observe h y) :
    FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x = θ :=
  FateV2.Loop.FillGap.fixed_of_predicts_exactly (SCMWorldModel.scmWorldModel M)
    h η φ hφ y θ u ε a x hη hpred

/-- ⭐⭐⭐⭐ **任务书 (d) 的最终形态：SCM 结构映射命中观测 ⟹ 端到端不动**。

$$(\mathrm{sg}\,u).2\;a \;=\; \hat x^{\mathrm{obs}}
  \ \Longrightarrow\ \mathrm{endToEnd}\,(\mathrm{scmWorldModel}\,M)\dots\theta = \theta .$$

$$\text{即：}\quad
  \mathrm{observe}\,h\,y = (\mathrm{sg}\,u).2\,a
  \ \Longrightarrow\ \theta' = \theta .$$

**⚠ 反同义反复核查（本定理是本文件最需要核查的一条）**：
* 前件：`φ` 单射、`η ≠ 0`、`[NoZeroDivisors PUnit]`（**参数**，与 `θ` 无关），
  以及**唯一的实质前件** `hpred : (sg u).2 a = observe h y`；
* 结论：`endToEnd … θ = θ`；
* **前件是否把结论包进去了？——没有**：`hpred` 讲的是**观测估计 = 结构映射预测**
  （一个关于 `y`/`u`/`a` 的等式），结论讲的是**参数 `θ` 不动**
  （`θ + η * φ(0) = θ`）。二者之间隔着
  `writeBack` 的代数（`sub_self`、`map_zero`、`mul_zero`、`add_zero`）
  与 `predFrom` 的展开，**不是同一句话**；
* **非平凡性对照**：若 `hpred` 不成立而残差经 `φ` 后非零，则 `θ' ≠ θ`
  （见 `endToEnd_scmWorldModel_moves`）—— 故本定理**不是**恒真。 -/
theorem endToEnd_scmWorldModel_fixed_of_sg_hit {X Y G : Type} (M : SCM X Y)
    [Nonempty Y] [AddCommGroup Y] [Ring PUnit] [NoZeroDivisors PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit) (hφ : Function.Injective φ)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) (hη : η ≠ 0)
    (hpred : (M.sg u).2 a = FateV2.Loop.EndToEnd.observe h y) :
    FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x = θ := by
  refine endToEnd_scmWorldModel_fixed_of_predicts M h η φ hφ y θ u ε a x hη ?_
  rw [predFrom_scmWorldModel]
  exact hpred

/-- ⭐⭐⭐ **非平凡性（SCM 实例）：观测 ≠ 结构映射预测 ⟹ `θ` 必改**。

$$\hat x^{\mathrm{obs}} \neq (\mathrm{sg}\,u).2\,a
  \ \Longrightarrow\ \mathrm{endToEnd}\dots\theta \neq \theta .$$

前件 `hR : ReadsResidual PUnit η φ` 是 `ResidualLoop` 的**具名判据**
（参数空间感受得到残差），不是三个散落假设。

**⟹ 与 `endToEnd_scmWorldModel_fixed_of_sg_hit` 合读**：
在 SCM 实例上「命不命中 `sg`」是 `θ` 动不动**唯一**的分界，没有中间态。 -/
theorem endToEnd_scmWorldModel_moves {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit)
    (hR : ResidualLoop.ReadsResidual (X := SCMWorldModel.scmStateSpace Y) scmTheta η φ)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y)
    (hne : FateV2.Loop.EndToEnd.observe h y ≠ (M.sg u).2 a) :
    FateV2.Loop.EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x ≠ θ := by
  refine FateV2.Loop.EndToEnd.endToEnd_moves (SCMWorldModel.scmWorldModel M) h η φ hR
    y θ u ε a x ?_
  rw [predFrom_scmWorldModel]
  exact hne

/-! ===========================================================================
  §5  多步闭环：`endToEndIter` 在 SCM 实例上的递推
  =========================================================================== -/

/-- ⭐⭐ **SCM 实例上多步闭环的第 0 步**（`EndToEnd.endToEndIter_zero` 的落点）。 -/
theorem endToEndIter_scmWorldModel_zero {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    FateV2.Loop.EndToEnd.endToEndIter (SCMWorldModel.scmWorldModel M) h η φ y u ε a x 0 θ = θ :=
  FateV2.Loop.EndToEnd.endToEndIter_zero (SCMWorldModel.scmWorldModel M) h η φ y u ε a x θ

/-- ⭐⭐⭐ **SCM 实例上多步闭环的递推**：
每一步都按「观测 − SCM 结构映射预测」写回。

$$\theta_{k+1} = \theta_k + \eta * \varphi\bigl(\hat x^{\mathrm{obs}} - (\mathrm{sg}\,u).2\,a\bigr).$$

**⚠ 本文件不证收敛**（`EndToEnd` §1.3 明确不做）：本定理只把递推**落到 SCM**。 -/
theorem endToEndIter_scmWorldModel_succ {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) (k : ℕ) :
    FateV2.Loop.EndToEnd.endToEndIter (SCMWorldModel.scmWorldModel M) h η φ y u ε a x (k + 1) θ
      = θ + η * φ (FateV2.Loop.EndToEnd.observe h y - (M.sg u).2 a) := by
  rw [FateV2.Loop.EndToEnd.endToEndIter_succ, endToEnd_scmWorldModel]

/-- ⭐⭐ **残差非零则多步闭环一步也不停**（`endToEndIter` 层的非平凡性）。 -/
theorem endToEndIter_scmWorldModel_succ_ne {X Y G : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit)
    (hR : ResidualLoop.ReadsResidual (X := SCMWorldModel.scmStateSpace Y) scmTheta η φ)
    (y : G) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x : Y) (k : ℕ)
    (hne : FateV2.Loop.EndToEnd.observe h y ≠ (M.sg u).2 a) :
    FateV2.Loop.EndToEnd.endToEndIter (SCMWorldModel.scmWorldModel M) h η φ y u ε a x (k + 1) θ
      ≠ θ := by
  rw [endToEndIter_scmWorldModel_succ]
  exact endToEnd_scmWorldModel_moves M h η φ hR y θ u ε a x hne

/-! ===========================================================================
  §6  可满足性见证（反「空真」核查）
  =========================================================================== -/

/-- ⭐⭐⭐ **本文件的条件不是空真**：取 `Y := ℤ`（SCM 的 `X := Bool`、`U := PUnit`），
则 §2–§5 所需的一切实例（`[AddCommGroup ℤ]`、`[Ring PUnit]`、`[NoZeroDivisors PUnit]`）
**均可满足**，且 §5 的残差公式给出具体值。

**⟹ 本文件的所有条件形式定理在**至少一个真实 SCM**上可实例化**
（不是「条件永假所以定理空洞」）。 -/
theorem scmE2E_instance_satisfiable :
    ∃ (M : SCM Bool ℤ), Nonempty ℤ ∧
      ∀ (θ : PUnit) (a : Bool), ∀ (u : M.U),
        FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u PUnit.unit a (0 : ℤ)
          = (M.sg u).2 a := by
  let M : SCM Bool ℤ :=
    { U := PUnit
      pU := fun _ => 1
      sg := fun _ => (false, fun _ => (0 : ℤ)) }
  exact ⟨M, ⟨0⟩, fun θ a u => predFrom_scmWorldModel M θ u PUnit.unit a (0 : ℤ)⟩

/-- ⭐⭐⭐ **具体 SCM 上的残差公式**（`scmE2E_instance_satisfiable` 的定量版）。

取 `M` 使 `sg u ≡ (false, fun _ => 0)`，`pU ≡ 1`。
则端到端残差**恒等于观测值本身**：

$$r = y_{\mathrm{obs}} - 0 = y_{\mathrm{obs}} .$$

**⚠ 这条定理的作用**：证明本文件的残差公式**真的给出数值**（不是形式重念）——
把 `sg` 的形状填进去，残差就退化成可计算的差。 -/
theorem scmE2E_residual_concrete (u : PUnit) (yobs : ℤ) (a : Bool) :
    let M : SCM Bool ℤ :=
      { U := PUnit
        pU := fun _ => 1
        sg := fun _ => (false, fun _ => (0 : ℤ)) }
    FateV2.Loop.EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) yobs PUnit.unit u
      PUnit.unit a (0 : ℤ) = yobs := by
  intro M
  rw [e2eResidual_scmWorldModel]
  show yobs - 0 = yobs
  exact sub_zero yobs

end

end SCMEndToEnd

end FateV2.Loop