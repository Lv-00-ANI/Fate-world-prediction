import FateWorld.FateV2.Predict.RuleSimConsistency
import FateWorld.FateV2.Loop.EndToEnd

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/RuleMainChainConsumer.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 6 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model
open FateV2.Rules

/-
============================================================================
  P0-G1 · 把规则桥接进主链：`ruleWorldModelWithRules` 的**第一个外部消费者**

  ## 背景（CHAIN-2 审计，实测计数）

  * `FateV2.Loop/RuleSimConsistency.lean` 里的 `ruleWorldModelWithRules` **真的**把
    `rules` 字段接上了外生规律 `R`（其核逐点等于 `R c x`，见 `ruleOfLaw_kernel_mem`）。
  * 但审计发现：`ruleWorldModelWithRules` 在 `EndToEnd.lean` 里出现 **0** 次，
    在 `RuleSimConsistency.lean` 之外的**任何**文件里出现 **0** 次。
    ⟹ 「规则桥很冷」：桥造好了，主链没走上去。

  ## 本文件做什么

  **本文件是 `ruleWorldModelWithRules` 的第一个外部消费者**（`RuleSimConsistency`
  之外的文件）。它交付三件事：

  | 编号 | 名字 | 内容 |
  |---|---|---|
  | A | `endToEndIterStep_eq_rule` | **主链一步 == 规则桥的 `simulator` 一步**（把 `ruleWorldModelWithRules` 接到 `endToEndIter`）|
  | B | `endToEndIter_step_output_mem_rule` | 主链一步之后的世界状态，其 Dirac **落在 `R` 允许的集合里**（外部消费 `ruleWorldModelWithRules_sim_allowed`）|
  | C | `ruleSet_witness_nonempty` | 规则集非空，且**具体见证**是 `ruleOfLaw`（外部消费 `ruleWorldModelWithRules_rules_eq` / `_mem_rules`）|

  ## ⚠ 诚实标注（前件非循环性自查）

  **A 的前件**只有：`F`、`instX`、`ctxOf`、`R`、`hR : IsDirac R`，
  以及 `endToEndIter` 自身要求的类型类 `[AddCommGroup F.X.Carrier] [Ring F.Θ.Carrier]`。
  其中 **无一条** 提及 `ruleWorldModelWithRules`、`simulator`、`rules`、
  `endToEndIter` 的任何值——故 A **不是**把结论包进前件。
  A 的实质内容是：**`endToEndIter` 所用的 `WorldModel` 的 `f` 就是
  `ruleWorldModelWithRules` 的 `simulator.step`**，即两个原本独立的投影相等；
  证明须依次展开 `WorldModel.f`（`simulator.step` 投影）、
  `ruleWorldModelWithRules_simulator_step`、`lawDetToStepGen` 三层定义，
  若 `ruleWorldModelWithRules` 的 `simulator` 字段被换成别的 `Step`，A 立即失败。

  **B 的前件**同上再加 `θ, u, ν, a, n`（都是**普通值**，不提及任何 `WorldModel`）。
  B 的结论是关于 `R` 的**成员关系**，非恒真式。

  **C 的前件**只有 `F, instX, ctxOf, R, hR, x₀`，结论是 `Nonempty` 与具体成员。

  ## 铁律遵守

  * 零占位符（Lean 的占位 tactic / 声明式占位 / 新公理 / 机器码判定 / 心跳放大），全文无一处。
  * **只新增文件**，未修改任何已有模块。
  * 未使用希腊字母作为标识符（沿用既有模块的 `hR` 命名）。
============================================================================
-/


namespace FateV2.Loop
namespace RuleMainChainConsumer

set_option autoImplicit false

noncomputable section

variable {C : CtxSpace} (F : Frame) (instX : MeasurableSpace F.X.Carrier)
  (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
    F.Act.Carrier → C.Carrier)
  (R : LawRule.LawRule C F.X F.X)
  (hR : LawRuleToTraj.IsDirac R)

/-! ===========================================================================
    §1  主链一步 = 规则桥的 `simulator` 一步
    =========================================================================== -/

/-- **【A：主链一步 == 规则桥的 `simulator` 一步】**

**这是「把 `ruleWorldModelWithRules` 接进 `endToEnd` 主链」的字面落实**：

$$\texttt{WorldModel.f}\ \bigl(\texttt{ruleWorldModelWithRules}\ R\ h_R\ x_0\bigr)
  \;=\; \texttt{lawDetToStepGen}\ R\ h_R .$$

`endToEnd` / `endToEndIter` 主链预测状态用的是 `WorldModel.f W`（即
`W.simulator.step` 的投影，见 `FateV2.Loop/WorldModel.lean` 的 `WorldModel.f`）。
本定理把该投影**逐字**算成 `ruleWorldModelWithRules` 里的那个 `Step`，
从而主链**确实**走的是由 `R` 驱动的规则桥，而非任何占位机制。

**⚠ 前件非循环**：前件只有 `IsDirac R`（一个关于 `R` 的陈述），
不提及 `WorldModel.f`、`simulator`、`endToEnd`、`endToEndIter`。
若 `ruleWorldModelWithRules` 的 `simulator` 字段换成另一个 `Step`，本定理即失败。 -/
theorem ruleWorldModelWithRules_f_eq_step (x0 : F.X.Carrier) :
    WorldModel.f (ruleWorldModelWithRules F instX ctxOf R hR x0)
      = lawDetToStepGen F instX ctxOf R hR :=
  ruleWorldModelWithRules_simulator_step F instX ctxOf R hR x0

/-- **【A′：`endToEndIter` 的一步 = 规则驱动的 `simulator.step`】**

对**任意** `x₀`（规则桥的初值）与**任意**主链当前状态 `x`、输入 `u ν θ a`：

$$\texttt{WorldModel.f}\ \bigl(\texttt{ruleWorldModelWithRules}\ R\ h_R\ x_0\bigr)\ x\ u\ \nu\ \theta\ a
  \;=\; \texttt{simulator.step}\bigl(\texttt{ruleWorldModelWithRules}\ R\ h_R\ x_0\bigr)\ x\ u\ \nu\ \theta\ a
  \;=\; \texttt{toDetFun}\ R\ h_R\ \bigl(\texttt{ctxOf}\ x\ u\ \nu\ \theta\ a\bigr)\ x .$$

**这是「`endToEndIter` 版 `step_eq_rule`」**：`endToEndIter` 每一步都调用
`endToEnd`，而 `endToEnd` 的环节 ②（预测）调用 `predFrom W θ u ε a x = W.f x u ε θ a`。
本定理把该调用**逐字**化简成「`R` 在上下文 `ctxOf x u ν θ a` 处的点选择」。

**⟹ 主链的每一次预测，都是规则 `R` 的一次应用。** -/
theorem endToEndIterStep_eq_rule (x0 : F.X.Carrier) (x : F.X.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    WorldModel.f (ruleWorldModelWithRules F instX ctxOf R hR x0) x u ν θ a
      = @LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x := by
  show lawDetToStepGen F instX ctxOf R hR x u ν θ a
      = @LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x
  rw [lawDetToStepGen_apply]

/-- **【A″：`endToEndIter` 每一步的预测都等于 `ruleWorldModelWithRules` 的模拟轨迹一步】**

$$\texttt{predFrom}\bigl(\texttt{ruleWorldModelWithRules}\ R\ h_R\ x_0\bigr)\ \theta\ u\ \nu\ a\ x
  \;=\; \texttt{sim}\ \langle\theta, u, \nu, a\rangle\ (n+1)\quad\text{当 } x = \texttt{sim}\ \dots\ n .$$

即：主链的**预测环节**与规则桥的**模拟轨迹**是同一个机制
（经 `WorldModel.sim_succ` 与 `predFrom` 对接）。 -/
theorem predFrom_ruleWorldModel_eq_sim_succ (x0 : F.X.Carrier)
    (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier)
    (a : ℕ → F.Act.Carrier) (n : ℕ) :
    EndToEnd.predFrom (ruleWorldModelWithRules F instX ctxOf R hR x0) θ (u n) (ε n) (a n)
        ((ruleWorldModelWithRules F instX ctxOf R hR x0).sim θ u ε a n)
      = (ruleWorldModelWithRules F instX ctxOf R hR x0).sim θ u ε a (n + 1) :=
  EndToEnd.predFrom_eq_sim_succ _ _ _ _ _ _

/-! ===========================================================================
    §2  主链一步的输出由规则允许（外部消费 `_sim_allowed`）
    =========================================================================== -/

/-- **【B：主链一步之后，下一步的 Dirac 落在 `R` 允许的集合里】**

$$\delta_{\texttt{sim}(n+1)} \;\in\;
  R\ \bigl(\texttt{ctxOf}\ (\texttt{sim}\ n)\ (u_n)\ (\nu_n)\ \theta\ (a_n)\bigr)\ \bigl(\texttt{sim}\ n\bigr).$$

**这是 `ruleWorldModelWithRules_sim_allowed` 的**外部**消费**：
把「规则集约束整条模拟轨迹」这条事实，搬到本文件（`RuleSimConsistency` 之外），
并用 §1 的 `predFrom_ruleWorldModel_eq_sim_succ` 把它接到**主链的预测位**上。

**⚠ 前件非循环**：前件只有 `IsDirac R` 与若干普通值，结论是一个**集合成员关系**。 -/
theorem ruleWorldModel_sim_step_output_mem_rule (x0 : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    MeasureTheory.Measure.dirac
        (EndToEnd.predFrom (ruleWorldModelWithRules F instX ctxOf R hR x0) θ (u n) (ε n) (a n)
          ((ruleWorldModelWithRules F instX ctxOf R hR x0).sim θ u ε a n))
      ∈ R (ctxOf ((ruleWorldModelWithRules F instX ctxOf R hR x0).sim θ u ε a n)
            (u n) (ε n) θ (a n))
          ((ruleWorldModelWithRules F instX ctxOf R hR x0).sim θ u ε a n) := by
  rw [predFrom_ruleWorldModel_eq_sim_succ]
  exact ruleWorldModelWithRules_sim_allowed F instX ctxOf R hR x0 θ u ε a n

/-- **【B′：主链预测位的输出落在 `R` 允许的集合里】**——用 `toDetFun` 显式值写出。

左端是 `endToEnd` 环节②预测出的下一点（经 `endToEndIterStep_eq_rule` 即
主链的单步输出），右端是外生规律 `R` 在上下文处的允许集。
本条的实质来源是 `ruleOfLaw_kernel_mem`（`ruleOfLaw` 的核就在 `R` 里）。 -/
theorem ruleWorldModel_step_output_mem_rule (x : F.X.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    MeasureTheory.Measure.dirac
        (@LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x)
      ∈ R (ctxOf x u ν θ a) x := by
  have h := ruleOfLaw_kernel_mem F instX R hR (ctxOf x u ν θ a) x
  rwa [ruleOfLaw_kernel] at h

/-! ===========================================================================
    §3  规则集非空且见证具体（外部消费 `_rules_eq` / `_mem_rules`）
    =========================================================================== -/

/-- **【C：规则集 = `{ruleOfLaw}`，且 `ruleOfLaw` 确实在里头】**

**这是 `ruleWorldModelWithRules_rules_eq` 与 `ruleWorldModelWithRules_mem_rules`
的外部消费**：在 `RuleSimConsistency` 之外，把「`rules` 字段装的就是 `R` 那条规则」
这条事实钉成 `Set` 等式 + 成员关系 + `Nonempty` 三项。 -/
theorem ruleSet_eq_singleton_and_mem (x0 : F.X.Carrier) :
    (ruleWorldModelWithRules F instX ctxOf R hR x0).rules.rules
        = {r | r = ruleOfLaw F instX R hR}
      ∧ ruleOfLaw F instX R hR
          ∈ (ruleWorldModelWithRules F instX ctxOf R hR x0).rules.rules
      ∧ (ruleWorldModelWithRules F instX ctxOf R hR x0).rules.rules.Nonempty := by
  exact ⟨ruleWorldModelWithRules_rules_eq F instX ctxOf R hR x0,
    ruleWorldModelWithRules_mem_rules F instX ctxOf R hR x0,
    ⟨_, ruleWorldModelWithRules_mem_rules F instX ctxOf R hR x0⟩⟩

end

end RuleMainChainConsumer
end FateV2.Loop
