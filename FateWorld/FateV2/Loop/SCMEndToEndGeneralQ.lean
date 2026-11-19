/-
命运理论 · Lean 4 形式化实现
================================

模块：`SCMEndToEndGeneralQ`
定位：**任务 D / G6 的主链接入宿主** —— 在 `Y = ℚ` 上给
`SCMEndToEndGeneral` 的**三个需要 `[AddCommGroup Y]` 的定理**
提供**具体的 SCM 实例**，从而让它们从「无条件可用但无人调用」
变成「被主链模块真的调用」。

===========================================================================
〇、为什么需要本文件（诊断，不是猜测）
===========================================================================

`SCMEndToEndGeneral` 交付 4 条定理：

| 定理 | 要求 `[AddCommGroup Y]`？ |
|---|---|
| `scmEndToEnd_general_predFrom` | ❌ 只要求 `[Nonempty Y]` |
| `scmEndToEnd_general_e2eResidual` | ✅ 需要 |
| `scmEndToEnd_general_apply` | ✅ 需要 |
| `scmEndToEnd_general_apply_eq_star` | ✅ 需要 |

而**全库所有具体 `SCM` 实例都是 `SCM Bool Bool`**（本轮用
`grep -rnE "SCM (Bool|ℚ|ℝ|ℤ|Fin)" Fate/*.lean` 实测确认，
排除 `Fate/Assembly.lean` 的同名异义 `SCM`）：
`scmDemo`（`SCMWorldModelEval`）、`modelC`（`PearlHierarchy`）、
`M₃`/`M₄`（`CfNecessity`）、`M0`/`M1`（`CfPartialIdent`）…

`Bool` 上**没有** `AddCommGroup Bool` 实例（且**不应该**有：`Bool` 是二元素集，
不存在特征 0 的加法群结构）。⟹ 那三条要求 `[AddCommGroup Y]` 的定理
在**现有**所有 SCM 实例上**根本无法调用**（不是「证明失败」，
而是 `e2eResidual (scmWorldModel M) …` 这个表达式在 `Y := Bool` 时
`failed to synthesize AddCommGroup Bool`，**连类型都打不出来**）。

**⟹ 本文件的处置**：`Bool` 上做不到，就**新造一个 `Y = ℚ` 的 SCM 实例**
（`scmQ`），在它上面把三条定理**真的调用一次**。这是唯一不需要
修改任何既有模块、又能给出真实消费证据的路线。

===========================================================================
一、本文件交付的定理
===========================================================================

| 定理 | 内容 | 真实消费的 `SCMEndToEndGeneral` 定理 |
|---|---|---|
| `scmQ_theta` | `Θ = PUnit` | （定义性）|
| `scmQ_predFrom` | `predFrom = (sg u).2 a` | `scmEndToEnd_general_predFrom` |
| `scmQ_e2eResidual` | `e2eResidual = xobs − (sg u).2 a` | `scmEndToEnd_general_e2eResidual` |
| `scmQ_apply` | `endToEnd = θ + η * φ (observe h y − (sg u).2 a)` | `scmEndToEnd_general_apply` |
| `scmQ_apply_eq_star` | `endToEnd = star` | `scmEndToEnd_general_apply_eq_star` |
| ⭐ `scmQ_e2eResidual_concrete` | **可计算数值**：`e2eResidual … = xobs − a − (if u then 1 else 0)` | `scmQ_e2eResidual`（自链）|
| ⭐ `scmQ_e2eResidual_zero_iff` | 残差为零 ⟺ 观测 = 结构方程预测 | `scmQ_e2eResidual` |

**⚠ 反同义反复核查（本项目最高频问题）**：
- `scmQ_e2eResidual` / `scmQ_apply` / `scmQ_apply_eq_star` 的**前件**
  只有 `M := scmQ` 的构造前提（`[Nonempty ℚ]`、`[AddCommGroup ℚ]`、`[Ring PUnit]`）
  与自由变量（`xobs`、`h`、`η`、`φ`、`y`、`θ`、`u`、`a`、`x`），
  **不含任何等式假设**；结论是展开式。非循环。
- ⭐ `scmQ_e2eResidual_concrete` 是**唯一带数值右端**的一条：
  它的右端 `xobs - a - (if u then 1 else 0)` 来自 `scmQ.sg` 的**定义**
  （`fun x => x + (if u then 1 else 0)`），**不是**把结论写进前件。
- ⭐ `scmQ_e2eResidual_zero_iff` 是**真正有内容的**：它把「残差 `= 0`」
  等价于「观测精确等于结构方程预测」，前件**不含**该等价。

===========================================================================
二、诚实边界
===========================================================================

1. **本文件不声称「去 `AddCommGroup` 已实现」**。恰恰相反：
   它**证实**了「`Y = Bool` 时那三条定理不可陈述」这一诊断——
   因为本文件必须**另造 `Y = ℚ`** 才能调用它们。
2. **本文件只新建，不修改任何既有模块**：只 `import`，无 `set_option` 外溢。
3. **零 `sorry` / `admit` / `axiom`**。
4. `scmQ` 是**为接线而造**的玩具实例（`U = Bool`、`X = Y = ℚ`、
   `sg u = (0, fun x => x + if u then 1 else 0)`）。它**不是**对任何
   真实世界模型的建模声明；其作用只是「让一个带 `AddCommGroup` 的
   SCM 存在」。
-/

import FateWorld.FateV2.Loop.SCMEndToEndGeneral
namespace FateV2.Loop

open FateV2.Modeling
namespace SCMEndToEndGeneralQ

open FateV2.Modeling.PearlHierarchy

set_option autoImplicit false

noncomputable section

/-!
  # Loop · SCMEndToEndGeneralQ

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMEndToEndGeneralQ.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMEndToEndGeneral
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  具体 SCM：`Y = ℚ`（**关键**：`ℚ` 上 `AddCommGroup` 可用，`Bool` 上不可用）
    =========================================================================== -/

/-- ⭐ **`ℚ` 上的具体 SCM**（`U = Bool`，均匀外生律）。

$$\mathrm{sg}\,u \;=\; \bigl(0,\; x \mapsto x + [\![u]\!]\bigr),$$

其中 $[\![\mathrm{true}]\!] = 1$、$[\![\mathrm{false}]\!] = 0$。

**读法**：`u` 是「加性偏移」，`false` 时结构方程是恒等（观测可精确预测），
`true` 时整体平移 `1`（残差非零）。这让 §3 的数值定理有真内容。

**⚠ 为什么必须是 `ℚ`（或 `ℝ`）而不能是 `Bool`**：见文件头 §〇。
`Bool` 上不存在 `AddCommGroup` 实例，故 `EndToEnd.e2eResidual`
在 `Y := Bool` 时**无法通过类型检查**。 -/
def scmQ : SCM ℚ ℚ where
  U := Bool
  pU := fun _ => (1 / 2 : ℝ)
  sg := fun u => (0, fun x => x + (if u then (1 : ℚ) else 0))

instance : Nonempty ℚ := ⟨0⟩

/-- `scmQ` 的外生空间是 `Bool`（定义性）。 -/
theorem scmQ_U : scmQ.U = Bool := rfl

/-! ===========================================================================
    §2  环节 ②：**`predFrom` 段**（只为自足；此段本不需要 `AddCommGroup`）
    =========================================================================== -/

/-- `scmQ` 上的 `predFrom = (sg u).2 a`。

**真实消费**：`SCMEndToEndGeneral.scmEndToEnd_general_predFrom`。 -/
theorem scmQ_predFrom (θ : PUnit) (u : Bool) (ε : PUnit) (a : ℚ) (y : ℚ) :
    EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmQ) θ u ε a y
      = (scmQ.sg u).2 a :=
  SCMEndToEndGeneral.scmEndToEnd_general_predFrom scmQ θ u ε a y

/-! ===========================================================================
    §3  ⭐ 残差 / 写回段：**三条需要 `[AddCommGroup ℚ]` 的定理的真正调用点**
    =========================================================================== -/

/-- ⭐⭐⭐ **`scmQ` 上的端到端残差**。

$$\mathrm{e2eResidual}\;(\mathrm{scmWorldModel}\,\mathrm{scmQ})\;x^{\mathrm{obs}}\;\theta\;u\;\varepsilon\;a\;x^{\mathrm{pred}}
  \;=\;x^{\mathrm{obs}} - (\mathrm{sg}\,u).2\,a .$$

**真实消费**：`SCMEndToEndGeneral.scmEndToEnd_general_e2eResidual`
（该定理要求 `[AddCommGroup Y]`，故**只能**在 `ℚ`/`ℝ` 型 SCM 上调用 —— 见文件头 §〇）。 -/
theorem scmQ_e2eResidual (xobs : ℚ) (θ : PUnit) (u : Bool) (ε : PUnit)
    (a : ℚ) (xpred : ℚ) :
    EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel scmQ) xobs θ u ε a xpred
      = xobs - (scmQ.sg u).2 a :=
  SCMEndToEndGeneral.scmEndToEnd_general_e2eResidual scmQ xobs θ u ε a xpred

/-- ⭐⭐⭐⭐ **残差的显式数值形式**（把 `(sg u).2 a` 算出来）。

$$\mathrm{e2eResidual}\;(\mathrm{scmWorldModel}\,\mathrm{scmQ})\;x^{\mathrm{obs}}\;\theta\;u\;\varepsilon\;a\;x^{\mathrm{pred}}
  \;=\;x^{\mathrm{obs}} - a - [\![u]\!] .$$

**读法**：残差 = 观测 − 干预值 − 外生偏移。`u = false` 时残差 = 观测 − 干预值；
`u = true` 时还多减 `1`。**这就是「外生实现真的进入残差」的最简证据**。

**⚠ 反同义反复**：前件只有自由变量，**不**含任何关于残差的假设；
右端的 `if u then 1 else 0` 来自 `scmQ.sg` 的**定义**，非前件。 -/
theorem scmQ_e2eResidual_concrete (xobs : ℚ) (θ : PUnit) (u : Bool) (ε : PUnit)
    (a : ℚ) (xpred : ℚ) :
    EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel scmQ) xobs θ u ε a xpred
      = xobs - a - (if u then (1 : ℚ) else 0) := by
  rw [scmQ_e2eResidual]
  simp only [scmQ]
  ring

/-- ⭐⭐⭐ **残差为零 ⟺ 观测精确等于结构方程预测**（真内容，不是重念）。

$$\mathrm{e2eResidual}\;(\mathrm{scmWorldModel}\,\mathrm{scmQ})\;x^{\mathrm{obs}}\;\dots = 0
  \;\Longleftrightarrow\;
  x^{\mathrm{obs}} = a + [\![u]\!] .$$

**读法**：端到端链的「残差归零」在 SCM 上**就是**「观测与结构方程在
外生实现 `u` 处的取值一致」。这把端到端收敛判据翻译成了 SCM 的可检验条件。

**⚠ 反同义反复**：前件**不含**任何等式（只有 `xobs`、`u`、`a`、`xpred` 自由）；
结论是一个 `↔`，左右两侧分别经由 `e2eResidual`（端到端链）与
`scmQ.sg`（SCM 结构方程）**两条不同定义路径**得到，非循环。 -/
theorem scmQ_e2eResidual_zero_iff (xobs : ℚ) (θ : PUnit) (u : Bool) (ε : PUnit)
    (a : ℚ) (xpred : ℚ) :
    EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel scmQ) xobs θ u ε a xpred = 0
      ↔ xobs = a + (if u then (1 : ℚ) else 0) := by
  rw [scmQ_e2eResidual_concrete]
  constructor
  · intro h
    linarith
  · intro h
    subst h
    ring

/-- ⭐⭐⭐ **`endToEnd` 在 `scmQ` 上的更新律**。

$$\mathrm{endToEnd}\;(\mathrm{scmWorldModel}\,\mathrm{scmQ})\;h\;\eta\;\varphi\;y\;\theta\;u\;\varepsilon\;a\;x
  \;=\;\theta + \eta * \varphi\bigl(\mathrm{observe}\,h\,y - (\mathrm{sg}\,u).2\,a\bigr).$$

**真实消费**：`SCMEndToEndGeneral.scmEndToEnd_general_apply`。 -/
theorem scmQ_apply {G : Type} (h : ℚ → G) (η : PUnit) (φ : ℚ →+ PUnit) (y : G)
    (θ : PUnit) (u : Bool) (ε : PUnit) (a : ℚ) (x : ℚ) :
    EndToEnd.endToEnd (SCMWorldModel.scmWorldModel scmQ) h η φ y θ u ε a x
      = θ + η * φ (EndToEnd.observe h y - (scmQ.sg u).2 a) :=
  SCMEndToEndGeneral.scmEndToEnd_general_apply scmQ h η φ y θ u ε a x

/-- ⭐⭐⭐ **`endToEnd` 在 `scmQ` 上恒为 `star`**（`Θ = PUnit` 单点）。

**真实消费**：`SCMEndToEndGeneral.scmEndToEnd_general_apply_eq_star`。

**读法（结构诊断）**：`PUnit` 只有一个元素，故「参数更新」在本实例上
**不含信息**——`endToEnd` 的全部内容都落在残差位。这不是缺陷登记，
而是本文件 §3 把重点放在残差上的**理由**。 -/
theorem scmQ_apply_eq_star {G : Type} (h : ℚ → G) (η : PUnit) (φ : ℚ →+ PUnit)
    (y : G) (θ : PUnit) (u : Bool) (ε : PUnit) (a : ℚ) (x : ℚ) :
    EndToEnd.endToEnd (SCMWorldModel.scmWorldModel scmQ) h η φ y θ u ε a x
      = PUnit.unit :=
  SCMEndToEndGeneral.scmEndToEnd_general_apply_eq_star scmQ h η φ y θ u ε a x

end

end SCMEndToEndGeneralQ

end FateV2.Loop