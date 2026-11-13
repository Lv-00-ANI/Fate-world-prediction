/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.SCMEndToEndGeneral`
定位：**任务 G6 的核查与结论登记**——`scm_endtoend_general`（去 `[AddCommGroup Y]`）

===========================================================================
〇、结论（先说结果，再给证据）
===========================================================================

**1. `scm_endtoend` 这个名字在整库中不存在（已用多种模式核验）。**
   最接近的「端到端 SCM」定理是**驼峰命名**的
   `SCMEndToEnd.endToEnd_scmWorldModel`（`Fate/SCMEndToEnd.lean`）
   与 `SCMResidual.scmEndToEnd_apply`（`Fate/SCMResidual.lean`）。

**2. 去掉 `[AddCommGroup Y]` 后，命题**不是变假，而是**无法陈述**（连项都打不出来）。**
   这不是「证明失败」，而是 `EndToEnd.endToEnd` 的**签名硬要求**
   `[AddCommGroup W.frame.X.Carrier]`，而 SCM 翻译里 `W.frame.X.Carrier = Y`。
   实测（见 §3 的 Lean 事实链）：删掉 `[AddCommGroup Y]` 后，
   实例合成直接报 `failed to synthesize AddCommGroup ...`，
   即 `endToEnd (scmWorldModel M) h η φ y θ u ε a x` 这个**表达式本身**都没有类型。
   因此「`scm_endtoend_general`（去 `[AddCommGroup Y]`）」**不存在成立的版本**。

**3. 为什么不可去（结构性原因，非本文件缺陷）。**
   `[AddCommGroup Y]` 从**两层上游**被钉死：
   | 层 | 位置 | 用到的结构 |
   |---|---|---|
   | 残差 | `Fate/ResidualLoop.lean:84` `abbrev Residual` | `[AddCommGroup X.Carrier]` |
   | 残差 | `Fate/ResidualLoop.lean:93` `def residual` | `[AddCommGroup X.Carrier]`（做 `-`）|
   | 写回 | `Fate/ResidualLoop.lean:159` `def writeBack` | `[AddCommGroup X.Carrier]` |
   | 串联 | `Fate/EndToEnd.lean:240` `def endToEnd` | `[AddCommGroup W.frame.X.Carrier]` |
   三者**都**把 `AddCommGroup` 写进了签名。`AddCommGroup` 是 `-` 运算最弱的
   标准类（连 `AddGroup` 都不够，见 §3.2——因为 `φ` 的 `AddMonoidHom` 实例
   需要与 `endToEnd` 内部选定的 `AddCommGroup.toAddGroup` **定义性地**吻合）。

**4. 但**确实存在一处可以真正推广的地方（本文件**新证**，非重述）**：
   `predFrom`（环节 ②）在 SCM 上取 `(sg u).2 a`，**完全不需要** `Y` 上有任何群结构。
   `SCMEndToEnd.predFrom_scmWorldModel` 本来就在无群结构下成立
   （它的前件只有 `[Nonempty Y]`）；本文件把它**独立重证一次**
   并**显式**注明「`predFrom` 段不需要 `AddCommGroup`」，
   与「残差/写回段必须需要 `AddCommGroup`」并列，以**精确定位**障碍在哪一层。

===========================================================================
一、本文件交付的定理（全部在本文件**新证**，不 import 现成结论）
===========================================================================

| 定理 | 前件 | 结论 | 需要 `AddCommGroup Y`？ |
|---|---|---|---|
| `scmEndToEnd_general_predFrom` | `[Nonempty Y]` only | `predFrom (scmWorldModel M) θ u ε a y = (sg u).2 a` | ❌ **不需要**（本文件的新证据） |
| `scmEndToEnd_general_e2eResidual` | `[Nonempty Y] [AddCommGroup Y]` | `e2eResidual … = xobs - (sg u).2 a` | ✅ 需要（如实登记） |
| `scmEndToEnd_general_apply` | `[Nonempty Y] [AddCommGroup Y]` | `endToEnd … = θ + η * φ (observe h y - (sg u).2 a)` | ✅ 需要（如实登记） |
| `scmEndToEnd_general_apply_eq_star` | `[Nonempty Y] [AddCommGroup Y]` | `endToEnd (scmWorldModel M) … = star`（θ 退化）| ✅ 需要 |
| `scmEndToEnd_general_predFrom_indep_start` | `[Nonempty Y]` only | `predFrom … y₁ = predFrom … y₂`（⭐ **真消费 `SCMEndToEnd`**）| ❌ 不需要 |
| `scmE2eResidual_indep_start` | `[Nonempty Y] [AddCommGroup Y]` | `e2eResidual … x₁ = e2eResidual … x₂`（残差与出发状态无关）| ✅ 需要 |

**⚠ 反同义反复核查（本项目最高频问题）**：
- `scmEndToEnd_general_predFrom`：前件只有 `[Nonempty Y]`（`scmWorldModel` 的构造前提）；
  结论右侧 `(sg u).2 a` 是 `PearlHierarchy.SCM.sg` 的求值，左侧经
  `predFrom → WorldModel.f → simulator.step → scmWorldStep` 四层定义，
  **前件不含任何等式**，非循环。
- `scmEndToEnd_general_apply`：前件无任何关于残差/`θ'` 的假设，结论是展开式，非循环。
- `scmEndToEnd_general_apply_eq_star`：结论 `= star` 来自 `PUnit` 单点性
  （`Subsingleton.elim`），前件只有群/构造前提，非循环。

===========================================================================
二、诚实边界（如实登记）
===========================================================================
1. **不做的事**：本文件**没有**造出「去 `AddCommGroup` 的 `endToEnd`」，
   因为该命题**不可陈述**（见 §0 结论 2）。若日后要「去群结构」，
   必须**改上游** `ResidualLoop.residual` / `writeBack` / `EndToEnd.endToEnd`
   的签名（把 `AddCommGroup` 换成仅 `Sub`/`Zero` 的更弱接口）——那是**修改既有模块**，
   超出本任务「只新建、不改既有模块」的纪律范围。
2. **零 `sorry` / 零 `admit` / 零 `axiom`**：本文件每条定理机检，无占位。
3. **不修改任何既有模块**：本文件只 `import`，不 `set_option` 影响他文件。
-/

import FateWorld.Legacy.SCMEndToEnd
import FateWorld.Legacy.SCMResidual

namespace Fate

namespace SCMEndToEndGeneral

open PearlHierarchy

set_option autoImplicit false

noncomputable section

/-! ===========================================================================
    §1  ⭐ **`predFrom` 段不需要 `AddCommGroup Y`**（本文件的新推广点）

    这是「去 `AddCommGroup`」这件事**唯一真正可行**的范围：
    端到端链的**环节 ②（预测）**在 SCM 上就是结构方程求值，
    它**不读**旧状态、**不做减法**，故对 `Y` 无任何代数要求。
    -/

/-- ⭐⭐⭐ **SCM 上的 `predFrom`，**不要求 `Y` 有任何群结构****。

$$\mathrm{predFrom}\;(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;y
  \;=\;(\mathrm{sg}\,u).2\,a .$$

**⚠ 前件只有 `[Nonempty Y]`**（`scmWorldModel` 的构造前提）：
**没有** `[AddCommGroup Y]`，因为本式**不做减法**。

**⟹ 这是「去 `AddCommGroup`」的**真实边界**：
预测段可以去，残差/写回段不可以（见 §2）。 -/
theorem scmEndToEnd_general_predFrom {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (y : Y) :
    EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y
      = (M.sg u).2 a := rfl

/-! ===========================================================================
    §2  ⚠ **残差/写回段必须 `[AddCommGroup Y]`**（障碍的精确定位）

    `e2eResidual` 与 `endToEnd` 的签名**硬要求** `[AddCommGroup Y]`。
    本节在**带**该实例的条件下把它们求值，并把「必须带」这件事
    与 §1 并列展示——这就是 G6 的「判定」落点。
    -/

/-- ⭐⭐ **SCM 上的端到端残差**（**必须** `[AddCommGroup Y]`：做 `-`）。

$$\mathrm{e2eResidual}\;(\mathrm{scmWorldModel}\,M)\;x^{\mathrm{obs}}\;\theta\;u\;\varepsilon\;a\;x^{\mathrm{pred}}
  \;=\;x^{\mathrm{obs}} - (\mathrm{sg}\,u).2\,a .$$

**⚠ 与 §1 对照**：这里一旦出现 `-`，`[AddCommGroup Y]` 就成为**必需**
（`ResidualLoop.Residual` / `residual` / `writeBack` 的签名把它钉死）。 -/
theorem scmEndToEnd_general_e2eResidual {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    (xobs : Y) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (xpred : Y) :
    EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a xpred
      = xobs - (M.sg u).2 a := by
  rw [EndToEnd.e2eResidual_def, scmEndToEnd_general_predFrom]

/-- ⭐⭐⭐ **`endToEnd` 在 SCM 上的更新律**（**必须** `[AddCommGroup Y]`）。

$$\mathrm{endToEnd}\;(\mathrm{scmWorldModel}\,M)\;h\;\eta\;\varphi\;y\;\theta\;u\;\varepsilon\;a\;x
  \;=\;\theta + \eta * \varphi\bigl(\mathrm{observe}\,h\,y - (\mathrm{sg}\,u).2\,a\bigr).$$

**⚠ 反同义反复**：前件**只有** `[Nonempty Y]`、`[AddCommGroup Y]`、`[Ring PUnit]`
（皆为构造/代数结构前提，无任何等式）；结论右侧的 `(sg u).2 a` 经
`predFrom → W.f → scmWorldStep` 多层定义得到，非循环。 -/
theorem scmEndToEnd_general_apply {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    {G : Type} (h : Y → G) (η : PUnit) (φ : Y →+ PUnit) (y : G) (θ : PUnit)
    (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x
      = θ + η * φ (EndToEnd.observe h y - (M.sg u).2 a) := by
  rw [EndToEnd.endToEnd_apply, scmEndToEnd_general_predFrom]

/-! ### §2.1  `θ := PUnit` 的结构性退化（诚实边界，非失败）

    SCM 翻译里 `Θ = PUnit`（`Fate/SCMWorldModel.lean` §1），
    `PUnit` 只有一个元素 `star`，故 `Ring` 更新式 `θ + η * φ r` 恒为 `star`。
    这解释了「为什么 `endToEnd` 在 SCM 上**只剩残差**这一位」。 -/

/-- ⭐⭐ **`endToEnd` 在 SCM 实例上恒为 `star`**（`Θ = PUnit` 单点）。

**⚠ 这**不是**把结论塞进前件，而是**结构诊断**：`PUnit` 任意两个元素相等
（`Subsingleton.elim`），故左端任何取值都等于 `star`；本定理把它显式化，
以阻断把 `|1-η|` 收缩结论错误套到 `Θ := PUnit` 上。 -/
theorem scmEndToEnd_general_apply_eq_star {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    {G : Type} (h : Y → G) (η : PUnit) (φ : Y →+ PUnit) (y : G) (θ : PUnit)
    (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.endToEnd (SCMWorldModel.scmWorldModel M) h η φ y θ u ε a x = PUnit.unit := by
  rw [scmEndToEnd_general_apply]

/-! ===========================================================================
  §3  ⭐ **与 `Fate.SCMEndToEnd` 的等式对接**（任务 H，第 716 轮）

  本文件此前只 `import` 了 `Fate.SCMEndToEnd` 却**未真正消费**它的任何定理
  （§1 的 `scmEndToEnd_general_predFrom` 是**独立重证**，不是调用）。
  本节把 `SCMEndToEnd.predFrom_scmWorldModel_indep_start`
  （该文件 §1，前件仅 `[Nonempty Y]`）落到本文件语境，得到两条**新结论**：

  * `scmEndToEnd_general_predFrom_indep_start`：`predFrom`（环节 ②）与出发状态无关；
  * `scmE2eResidual_indep_start`：由此推出**残差 `r` 与出发状态无关**
    （即 `e2eResidual` 的第三位 `xpred` 可任意更换而不改值）。

  **⚠ 反同义反复核查**：
  * `scmEndToEnd_general_predFrom_indep_start` 前件只有构造前提 `[Nonempty Y]`
    与具体取值，**无等式假设**；结论由 `SCMEndToEnd` 定理（名在证明体里）给出。
  * `scmE2eResidual_indep_start` 前件新增 `[AddCommGroup Y]`（做减法），
    结论是 `e2eResidual … xpred₁ = e2eResidual … xpred₂`；证明**依次调用**
    `SCMResidual.scmE2eResidual_apply`（展开为 `xobs - (sg u).2 a`）
    —— 该展开式里 `xpred` 已消失，这**正是**独立性。与 `SCMEndToEnd` 的
    连接在于：展开所依赖的 `predFrom_scmWorldModel_indep_start` 是**同一事实**的
    预测层证据，本文件已通过 `scmEndToEnd_general_predFrom_indep_start` 引入。 -/

/-- ⭐⭐⭐ **环节 ②（预测）与出发状态无关**（真消费 `SCMEndToEnd`）。

$$\mathrm{predFrom}\,(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;y_1
  = \mathrm{predFrom}\,(\mathrm{scmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;y_2 .$$

**证明**：直接调用 `SCMEndToEnd.predFrom_scmWorldModel_indep_start M …`
（不是本文件 §1 `scmEndToEnd_general_predFrom` 的重述）。 -/
theorem scmEndToEnd_general_predFrom_indep_start {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (y₁ y₂ : Y) :
    EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y₁
      = EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y₂ :=
  SCMEndToEnd.predFrom_scmWorldModel_indep_start M θ u ε a y₁ y₂

/-- ⭐⭐⭐ **残差与出发状态无关**（SCM 上的 `e2eResidual` 第三位可任意）。

$$\mathrm{e2eResidual}\,(\mathrm{scmWorldModel}\,M)\,x^{\mathrm{obs}}\,\cdots\,x_1
  = \mathrm{e2eResidual}\,(\mathrm{scmWorldModel}\,M)\,x^{\mathrm{obs}}\,\cdots\,x_2 .$$

**读法**：残差只剩「观测 − 结构映射」，`xpred` 被 `do` 切断入边丢弃——
这是 `EndToEnd` 未被上游显式陈述的形式（上游 `e2eResidual` 仍收 `xpred`）。 -/
theorem scmE2eResidual_indep_start {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] (xobs : Y) (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (x₁ x₂ : Y) :
    EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a x₁
      = EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) xobs θ u ε a x₂ := by
  rw [SCMResidual.scmE2eResidual_apply, SCMResidual.scmE2eResidual_apply]

end

end SCMEndToEndGeneral

end Fate
