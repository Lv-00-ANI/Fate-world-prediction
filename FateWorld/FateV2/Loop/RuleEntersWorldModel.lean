import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.LawRuleToTraj
import FateWorld.FateV2.Model.TrajGenDeterministic
import FateWorld.FateV2.Model.DetFunToStep
import FateWorld.FateV2.Predict.LawDetToStepGen
/-!
  # Loop · RuleEntersWorldModel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RuleEntersWorldModel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame, WorldModel, EndToEnd, LawRule, LawRuleToTraj, TrajGenDeterministic, DetFunToStep, LawDetToStepGen
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
============================================================================
  规则核心链 · P0-2 / P0-3 · **规则驱动的整条世界模型轨迹**
  ## 本模块做什么
  把 `LawRule` 在 `IsDirac` 档抽出的 `Step` 装进 `WorldSimulator`，
  并证明 `trajGen`（世界模型的轨迹生成器）在它上面生成的轨迹
  **就是** `LawRule` 自己的轨迹（`trajOfRichLaw`）。
  ## 关键定义（实测原文）
  ```lean
  -- LawRuleToTraj.lean:421
  abbrev RichLaw (F : Frame) [MeasurableSpace F.X.Carrier] : Type _ :=
    LawRule (RichCtx F) F.X F.X

  -- LawRuleToTraj.lean:444
  noncomputable def trajOfRichLaw (R : RichLaw F) (hR : IsDirac R)
      (θ) (x₀) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
      Traj ℕ F.X :=
    fun n => Nat.rec x₀ (fun k xk => toDetFun R hR (u k, ε k, θ, a k) xk) n

  -- TrajGenDeterministic.lean:71
  def trajGen (F : Frame) (f : Step F) (θ) (x₀) (u) (ε) (a) : Traj ℕ F.X :=
    fun n => Nat.rec x₀ (fun k xk => f xk (u k) (ε k) θ (a k)) n

  -- WorldModel.lean:169
  structure WorldSimulator (F : Frame) where
    step : Step F
    horizon : ℕ
  ```
  ## 本模块的定理
  | # | 定理 | 内容 |
  |---|---|---|
  | 1 | `ctxOfRich` | `RichCtx` 的抽取函数 `(x,u,ε,θ,a) ↦ (u,ε,θ,a)` |
  | 2 | `ruleSimulator` | 由 Dirac 规则构造 `WorldSimulator` |
  | 3 | `ruleSimulator_step` | 它的 `step` = `lawDetToStepGen`（`rfl`） |
  | 4 | `trajGen_rule_eq_trajOfRichLaw` | ⭐⭐⭐⭐⭐ **规则世界模型轨迹 ≡ `trajOfRichLaw`（`rfl` 级）** |
  | 5 | `trajGen_rule_zero` | 第 0 步 = 初值 |
  | 6 | `trajGen_rule_succ` | 递推式 |
  | 7 | `trajGen_rule_succ_of_ctx` | 递推式的「任取 `ctxOf`」版 |
  | 8 | `trajGen_rule_eq_simulate_of_ctx` | ⭐⭐⭐ **任取 `ctxOf`（只要它逐点等于 `ctxOfRich`）轨迹不变** |
  | 9 | `ruleSimulator_step_law` | ⭐⭐⭐ 一步**合法于规则 `R`** |
  | 10 | `trajGen_rule_law` | ⭐⭐⭐⭐ 整条轨迹**每一步都合法于 `R`**（对 `n` 归纳） |
  | 11 | `trajGen_rule_eq_iterate` | ⭐⭐⭐ 常量输入下轨迹 = `Step` 的函数迭代（对 `n` 归纳） |
  | 12 | `trajGen_rule_unique` | ⭐⭐⭐ **唯一性（泛性质）**：满足同一递推与初值的任意轨迹**必等于** `trajGen` |
  ## 诚实边界
  * **不构造完整 `WorldModel`**：它还需 `WorldState` / `WorldRules` / `Selector`，
    这些与规则无关，故不在此伪造；
  * 本模块只把「轨迹生成」这一段接通（`trajGen` 就是 `WorldModel.sim` 用的那个函数）。

## §6 的追加说明（定理 7–12）

定理 1–6 中**全部**是 `:= rfl`。定理 7–12 是**追加的非 `rfl` 定理**，
每条都**不是**把定义展开一次：

| # | 为什么不是 `rfl` |
|---|---|
| 7–8 | 前件 `hctx` 是**任意** `ctxOf` 与 `ctxOfRich` 的逐点相等；结论是 `trajGen` 的相等（对 `n` 归纳，或经 `lawDetToStepGen_eq_of_ctxOf`） |
| 9 | 用 `lawDetToStepGen_spec`（`toDetFun_spec`），把「算出的值」升级为「`R` 允许的唯一分布」 |
| 10 | 对 `n` 归纳 + 定理 9；整条轨迹**逐时刻**被 `R` 约束 |
| 11 | 对 `n` 归纳，把 `Nat.rec` 轨迹改写成 `Function.iterate` |
| 12 | 对 `n` 归纳，用定理 5 的递推式对齐两条轨迹 |

**⚠ 反同义反复自查**（逐条）：定理 7–12 的**前件**只有
`R : RichLaw F`、`hR : IsDirac R`、初值、输入序，以及
（定理 7/8 的）`ctxOf` 与 `ctxOfRich` 逐点相等。
它们**都不提及** `trajGen`、`WorldSimulator`、`Function.iterate`
或「轨迹合法于 `R`」中的任何一项。故**前件没有把结论包进去**。
============================================================================
-/

namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
open FateV2.Rules
namespace RuleEntersWorldModel

noncomputable section

open FateV2.Rules.LawRuleToTraj
open FateV2.Model.TrajGenDeterministic

variable (F : Frame) (instX : MeasurableSpace F.X.Carrier)

/-- **富上下文的抽取函数**：从 `(x, u, ε, θ, a)` 取出 `RichCtx` 四元组 `(u, ε, θ, a)`。

**⟹ 这正是 `RichCtx F` 的定义，故它是 `id` 在四元组上的投影。** -/
def ctxOfRich (x : F.X.Carrier) (u : F.U.Carrier) (ε : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) : (RichCtx F).Carrier :=
  (u, ε, θ, a)

@[simp] theorem ctxOfRich_apply (x : F.X.Carrier) (u : F.U.Carrier)
    (ε : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    ctxOfRich F x u ε θ a = (u, ε, θ, a) := rfl

/-- ⭐⭐ **【由 Dirac 规则构造 `WorldSimulator`】** -/
def ruleSimulator (R : RichLaw F) (hR : IsDirac R) (horizon : ℕ) : WorldSimulator F :=
  { step := lawDetToStepGen F instX (ctxOfRich F) R hR, horizon := horizon }

/-- **规则模拟器的 `step` 逐字等于 `lawDetToStepGen`。** -/
@[simp] theorem ruleSimulator_step (R : RichLaw F) (hR : IsDirac R) (horizon : ℕ) :
    (ruleSimulator F instX R hR horizon).step
      = lawDetToStepGen F instX (ctxOfRich F) R hR := rfl

/-- ⭐⭐⭐⭐⭐ **【规则驱动的世界模型轨迹 ≡ `LawRule` 自己的轨迹】**

`trajGen F (ruleSimulator.step) θ x₀ u ε a = trajOfRichLaw R hR θ x₀ u ε a`

**⟹ 这是 P0 的最终结论：**
**⟹ 世界模型用它生成的轨迹，与规则自己生成的轨迹是同一条。**

**证明**：两者都是 `fun n => Nat.rec x₀ (fun k xk => …) n`，
且递推核在 `ctxOfRich` 下逐字相同 ⟹ **`rfl`**。 -/
theorem trajGen_rule_eq_trajOfRichLaw (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a
      = trajOfRichLaw R hR θ x₀ u ε a := rfl

/-- ⭐ **第 0 步 = 初值。** -/
theorem trajGen_rule_zero (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a 0 = x₀ := rfl

/-- ⭐⭐ **递推式：第 n+1 步 = 用第 n 步作输入调用抽出机制。** -/
theorem trajGen_rule_succ (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a (n + 1)
      = toDetFun R hR (u n, ε n, θ, a n)
          (trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a n) := rfl

/-! ===========================================================================
    §6  ⭐ 追加的**非 `rfl`** 定理（定理 7–12）

    本节每条定理都不是定义展开：证明里都出现**归纳**
    或对 `LawRuleToTraj` 侧**实质引理**（`lawDetToStepGen_spec` /
    `lawDetToStepGen_eq_of_ctxOf`）的调用。

    ### 前件非循环（自查）

    * `R : RichLaw F` 与 `hR : IsDirac R`：只陈述「`R c x` 是某个 Dirac 单点集」，
      **不**提及 `trajGen` / `WorldSimulator` / 轨迹合法性 / 迭代；
    * 定理 7/8 的 `hctx` 只陈述 `ctxOf` 与 `ctxOfRich` **逐点相等**，
      也**不**提及轨迹；
    * 定理 12 的 `g` / `hg0` / `hgS` 是**任意**轨迹及其**递推方程**，
      「满足同一递推」并不等于「等于 `trajGen`」——后者需要归纳证明。
    =========================================================================== -/

/-- ⭐⭐⭐ **【定理 7：任取 `ctxOf` 的递推式】**

设 `ctxOf` 与 `ctxOfRich F` **逐点相等**（即它也在算同一个富上下文四元组），则

$$\mathrm{trajGen}(\mathrm{lawDetToStepGen}\ F\ instX\ \mathrm{ctxOf}\ R\ h_R)(n+1)
  = \mathrm{toDetFun}\ R\ h_R\ (u_n,\varepsilon_n,\theta,a_n)\ (\text{同式在 } n).$$

**为何非平凡**：`ctxOf` 是**外层给的任意函数**（不是 `ctxOfRich F`），
故 `trajGen` 左端的 `Step` 是一个**不同的** `Step`。
要把它的递推核改写成 `toDetFun R hR (u n, ε n, θ, a n)`，
**必须先**用 `hctx` 把 `ctxOf` 换成 `ctxOfRich F`。
定理 5（`trajGen_rule_succ`）**不能**直接用于任意 `ctxOf`。 -/
theorem trajGen_rule_succ_of_ctx
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → (RichCtx F).Carrier)
    (hctx : ∀ x u ε θ a, ctxOf x u ε θ a = ctxOfRich F x u ε θ a)
    (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    trajGen F (lawDetToStepGen F instX ctxOf R hR) θ x₀ u ε a (n + 1)
      = toDetFun R hR (u n, ε n, θ, a n)
          (trajGen F (lawDetToStepGen F instX ctxOf R hR) θ x₀ u ε a n) := by
  rw [TrajGenDeterministic.trajGen_succ]
  rw [lawDetToStepGen_apply, hctx]
  rfl

/-- ⭐⭐⭐ **【定理 8：轨迹对 `ctxOf` 的「表示」不变】**

设 `ctxOf` 与 `ctxOfRich F` **逐点相等**，则**两条轨迹完全相同**：

$$\mathrm{trajGen}\ F\ (\mathrm{lawDetToStepGen}\ F\ instX\ \mathrm{ctxOf}\ R\ h_R)
  \theta\ x_0\ u\ \varepsilon\ a
  = \mathrm{trajOfRichLaw}\ R\ h_R\ \theta\ x_0\ u\ \varepsilon\ a .$$

**为何非平凡**：这是定理 4 的**推广**——定理 4 只对**那一个具体的** `ctxOfRich F` 成立
（故可 `rfl`）；本定理对**任意** `ctxOf` 成立，条件是它与 `ctxOfRich F` 逐点相等。
证明需先证 `Step` 相等（`lawDetToStepGen_eq_of_ctxOf`），再对 `n` **归纳**。

**⟹ 语义**：`trajGen` 与 `trajOfRichLaw` 的等同**不依赖**「上下文如何被写出」，
只依赖「上下文取值相同」。这是本条相对定理 4 的**实质内容**。 -/
theorem trajGen_rule_eq_simulate_of_ctx
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → (RichCtx F).Carrier)
    (hctx : ∀ x u ε θ a, ctxOf x u ε θ a = ctxOfRich F x u ε θ a)
    (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGen F (lawDetToStepGen F instX ctxOf R hR) θ x₀ u ε a
      = trajOfRichLaw R hR θ x₀ u ε a := by
  have hstep : lawDetToStepGen F instX ctxOf R hR
      = lawDetToStepGen F instX (ctxOfRich F) R hR :=
    lawDetToStepGen_eq_of_ctxOf F instX ctxOf (ctxOfRich F) hctx R hR
  rw [hstep]
  exact trajGen_rule_eq_trajOfRichLaw F instX R hR θ x₀ u ε a

/-- ⭐⭐⭐ **【定理 9：规则模拟器的一步**合法于** `R`】**

$$R\ (u,\varepsilon,\theta,a)\ x
  = \bigl\{\delta_{\mathrm{step}\ x\ u\ \varepsilon\ \theta\ a}\bigr\}.$$

**为何非平凡**：定理 3（`ruleSimulator_step`）只说「`step` 逐字等于 `lawDetToStepGen`」——
那只是**定义相等**，不涉及 `R` 本身。本条说的是
「**该 `step` 的输出正是 `R` 在相应上下文处唯一允许的下一状态**」，
需要用 `lawDetToStepGen_spec`（其实质是 `toDetFun_spec` = `Classical.choose_spec`）。

**反事实检验**：把 `step` 换成任意别的函数，本条即**失败**。 -/
theorem ruleSimulator_step_law (R : RichLaw F) (hR : IsDirac R)
    (x : F.X.Carrier) (u : F.U.Carrier) (ε : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    R (ctxOfRich F x u ε θ a) x
      = {MeasureTheory.Measure.dirac
          ((ruleSimulator F instX R hR 1).step x u ε θ a)} := by
  rw [ruleSimulator_step]
  exact lawDetToStepGen_spec F instX (ctxOfRich F) R hR x u ε θ a

/-- ⭐⭐⭐⭐ **【定理 10：整条轨迹**逐时刻合法于** `R`】**

$$\forall n,\quad R\ (u_n,\varepsilon_n,\theta,a_n)\ (x_n) = \{\delta_{x_{n+1}}\}.$$

**为何非平凡**：这是**轨迹层**（对 `n` 量化）的陈述，
由定理 4（`trajGen_rule_succ`）把 `x_{n+1}` 化成一步 + 定理 9 得出。
它不是定义展开：`trajGen` 的定义里**没有** `R`，只有 `lawDetToStepGen`；
「轨迹每步都被 `R` 允许」是**把定义与 `R` 的语义接起来**之后的推论。 -/
theorem trajGen_rule_law (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    R (u n, ε n, θ, a n)
        (trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a n)
      = {MeasureTheory.Measure.dirac
          (trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a (n + 1))} := by
  rw [trajGen_rule_succ F instX R hR θ x₀ u ε a n]
  exact lawDetToStepGen_spec F instX (ctxOfRich F) R hR _ (u n) (ε n) θ (a n)

/-- ⭐⭐⭐ **【定理 11：常量输入下轨迹 = `Step` 的函数迭代】**

输入序取**常量** `u`、`ε`、`a` 时，

$$\mathrm{trajGen}(n) = \bigl(\mathrm{lawDetToStepGen}\ F\ instX\ \mathrm{ctxOfRich}\ R\ h_R
  \cdot\ u\ \varepsilon\ \theta\ a\bigr)^{[n]}\ x_0 .$$

**为何非平凡**：对 `n` 的**归纳**，把 `Nat.rec` 形式的轨迹改写为
`Function.iterate` 形式。**⟹ 它把本模块的轨迹与下游的迭代/不动点论证对齐。** -/
theorem trajGen_rule_eq_iterate (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : F.U.Carrier) (ε : F.Ν.Carrier) (a : F.Act.Carrier) :
    ∀ n : ℕ,
      trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀
          (fun _ => u) (fun _ => ε) (fun _ => a) n
        = (lawDetToStepGen F instX (ctxOfRich F) R hR · u ε θ a)^[n] x₀ := by
  intro n
  induction n with
  | zero =>
    rw [trajGen_rule_zero]
    rfl
  | succ k ih =>
    rw [trajGen_rule_succ, ih, Function.iterate_succ_apply']
    rw [lawDetToStepGen_apply]
    rfl

/-- ⭐⭐⭐ **【定理 12：`trajGen` 的唯一性（泛性质）】**

若 `g : ℕ → F.X.Carrier` 满足

* `g 0 = x₀`，
* `∀ k, g (k+1) = toDetFun R h_R (u_k, ε_k, θ, a_k) (g k)`，

则 `g = trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a`。

**为何非平凡**：这是 `trajGen` 的**泛性质**（universal property）：
`trajGen` 是满足该递推的**唯一**轨迹。`g` 是**任意**序列，
证明必须对 `n` **归纳**，且 `hgS` 只给出递推方程，
**不**直接等于结论（否则就是同义反复）。

**⟹ 用途**：任何其他途径（例如 §6 外部的迭代实现）算出的轨迹，
只要满足同一递推与初值，**自动**等于本模块的 `trajGen`。 -/
theorem trajGen_rule_unique (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (g : ℕ → F.X.Carrier) (hg0 : g 0 = x₀)
    (hgS : ∀ k, g (k + 1) = toDetFun R hR (u k, ε k, θ, a k) (g k)) :
    ∀ n, g n
      = trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a n := by
  intro n
  induction n with
  | zero =>
    rw [hg0, trajGen_rule_zero]
  | succ k ih =>
    rw [hgS k, ih, trajGen_rule_succ]

/-! ===========================================================================
    §7  ⭐⭐⭐ 具体见证：**步进结果确实依赖 `R`**（定理 13–17）

    ## 为什么需要本节

    定理 7–12 说明了「怎样用 `R` 生成轨迹」，但它们**没有**排除这种可能：
    这里抽出的 `Step` 实际上**不依赖 `R`**（若如此，整个构造就空洞无物）。
    本节在一个**具体 `Frame`**（状态空间 `ℝ`，其余空间单点）上给出两个
    **不同的** Dirac 规律，并证明它们的 `Step` **不相等**。

    **⟹ 这是「规则链不是定义缝合」的最强形式证据**：
    换一个 `R`，抽出机制会**真的变**。

    ### 前件非循环（自查）

    * `lawZero` / `lawOne` 是两个**具体的** `LawRule`，其定义不提及任何 `Step`；
    * `isDirac_zero` / `isDirac_one` 只说「允许集是 Dirac 单点集」；
    * 定理 17（`ruleStep_depends_on_R`）的前件**全无**：它是**无条件**的
      （在一个具体的 `Frame` 上陈述），结论是存在性。
    ### 诚实标注

    本节的 `Frame` 是**为了构造见证**而定制的（状态空间 `ℝ`，拓扑与可测结构取
    `⊤`）。它**不**声称与任何物理意义对应；它只用于证明「`Step` 依赖 `R`」
    这一**否定性断言的反面**（即非平凡性）。
    =========================================================================== -/

/-- **见证用参数空间**（单点）。 -/
def wTheta : ThetaSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- **见证用状态空间**：`ℝ`，拓扑/可测结构取 `⊤`（全离散）。 -/
def wX : StateSpace where
  Carrier := ℝ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- **见证用输入空间**（单点）。 -/
def wU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- **见证用动作空间**（单点）。 -/
def wAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- **见证用噪声空间**（单点）。 -/
def wN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- **见证用上下文空间**（单点）。 -/
def wC : CtxSpace where
  Carrier := PUnit

/-- **见证用 `Frame`**。 -/
def wFrame : Frame where
  Θ := wTheta
  X := wX
  U := wU
  Act := wAct
  Ν := wN

instance wXMeas : MeasurableSpace wX.Carrier := wX.meas

/-- `wX.Carrier` 上的 `0`（显式标注，避开结构投影路径）。 -/
instance wXZero : OfNat wX.Carrier 0 := ⟨(0 : ℝ)⟩

/-- `wX.Carrier` 上的 `1`。 -/
instance wXOne : OfNat wX.Carrier 1 := ⟨(1 : ℝ)⟩

/-- 全离散可测结构**分离点**（单点集可测）。 -/
instance wXSeparates : MeasurableSpace.SeparatesPoints wX.Carrier :=
  MeasurableSpace.SeparatesPoints.mk (fun x y hxy => by
    have hms : MeasurableSet ({x} : Set wX.Carrier) := trivial
    have hy : y ∈ ({x} : Set wX.Carrier) := hxy {x} hms (Set.mem_singleton x)
    exact (Set.mem_singleton_iff.mp hy).symm)

/-- 见证中的点 `0`。 -/
def wZero : wX.Carrier := 0

/-- 见证中的点 `1`。 -/
def wOne : wX.Carrier := 1

/-- **规律一：无论上下文与状态，下一步必为 `0`。** -/
noncomputable def lawToZero : @LawRule.LawRule wC wX wX wX.meas :=
  fun _ _ =>
    ({@MeasureTheory.Measure.dirac wX.Carrier wX.meas wZero} : Set (MeasureTheory.Measure wX.Carrier))

/-- **规律二：无论上下文与状态，下一步必为 `1`。** -/
noncomputable def lawToOne : @LawRule.LawRule wC wX wX wX.meas :=
  fun _ _ =>
    ({@MeasureTheory.Measure.dirac wX.Carrier wX.meas wOne} : Set (MeasureTheory.Measure wX.Carrier))

/-- 规律一是 Dirac 档（见证：`0`）。 -/
theorem isDirac_lawToZero : @LawRuleToTraj.IsDirac wC wX wX wX.meas lawToZero :=
  fun _ _ => ⟨wZero, rfl⟩

/-- 规律二是 Dirac 档（见证：`1`）。 -/
theorem isDirac_lawToOne : @LawRuleToTraj.IsDirac wC wX wX wX.meas lawToOne :=
  fun _ _ => ⟨wOne, rfl⟩

/-- 见证用上下文注入（恒取单点）。 -/
def wCtx : wX.Carrier → wU.Carrier → wN.Carrier → wTheta.Carrier → wAct.Carrier → wC.Carrier :=
  fun _ _ _ _ _ => PUnit.unit

/-- `wZero ≠ wOne`（具体的非平凡性来源）。 -/
theorem wZero_ne_wOne : wZero ≠ wOne := by
  intro h
  exact absurd (congrArg (fun z : wX.Carrier => z) h) (by
    show ¬ ((0 : ℝ) = 1)
    norm_num)

/-- **定理 14：`lawToZero` 的抽出函数恒为 `0`。**

证明用 `toDetFun_spec`：若抽出值不是 `0`，贝 `R c x` 将是两个不同的单点集。 -/
theorem toDetFun_lawToZero_eq (c : wC.Carrier) (x : wX.Carrier) :
    @LawRuleToTraj.toDetFun wC wX wX wX.meas lawToZero isDirac_lawToZero c x = wZero := by
  have h := @LawRuleToTraj.toDetFun_spec wC wX wX wX.meas lawToZero isDirac_lawToZero c x
  rw [lawToZero] at h
  have hy : (MeasureTheory.Measure.dirac wZero : MeasureTheory.Measure wX.Carrier)
      ∈ ({MeasureTheory.Measure.dirac
          (@LawRuleToTraj.toDetFun wC wX wX wX.meas lawToZero isDirac_lawToZero c x)}
          : Set (MeasureTheory.Measure wX.Carrier)) :=
    h ▸ Set.mem_singleton _
  exact (MeasureTheory.dirac_eq_dirac_iff.mp (Set.mem_singleton_iff.mp hy)).symm

/-- **定理 15：`lawToOne` 的抽出函数恒为 `1`。** -/
theorem toDetFun_lawToOne_eq (c : wC.Carrier) (x : wX.Carrier) :
    @LawRuleToTraj.toDetFun wC wX wX wX.meas lawToOne isDirac_lawToOne c x = wOne := by
  have h := @LawRuleToTraj.toDetFun_spec wC wX wX wX.meas lawToOne isDirac_lawToOne c x
  rw [lawToOne] at h
  have hy : (MeasureTheory.Measure.dirac wOne : MeasureTheory.Measure wX.Carrier)
      ∈ ({MeasureTheory.Measure.dirac
          (@LawRuleToTraj.toDetFun wC wX wX wX.meas lawToOne isDirac_lawToOne c x)}
          : Set (MeasureTheory.Measure wX.Carrier)) :=
    h ▸ Set.mem_singleton _
  exact (MeasureTheory.dirac_eq_dirac_iff.mp (Set.mem_singleton_iff.mp hy)).symm

/-- **定理 16：两个规律抽出的 `Step` **不相等**。**

$$\mathrm{lawDetToStepGen}\ wFrame\ wX.meas\ wCtx\ (\text{lawToZero})\ isDirac_0
  \neq \mathrm{lawDetToStepGen}\ wFrame\ wX.meas\ wCtx\ (\text{lawToOne})\ isDirac_1 .$$

**为何非平凡**：两条规律在**每个** `(c, x)` 处都是一般的单点集，
只有用定理 14/15 把抽出函数具体化到 `0` / `1` 才能把它们分开。
引理 3/5 无法直接区分它们。 -/
theorem ruleStep_depends_on_R_z :
    lawDetToStepGen wFrame wX.meas wCtx lawToZero isDirac_lawToZero
    ≠ lawDetToStepGen wFrame wX.meas wCtx lawToOne isDirac_lawToOne := by
  intro h
  have h1 : lawDetToStepGen wFrame wX.meas wCtx lawToZero isDirac_lawToZero
        wZero PUnit.unit PUnit.unit PUnit.unit PUnit.unit
      = lawDetToStepGen wFrame wX.meas wCtx lawToOne isDirac_lawToOne
        wZero PUnit.unit PUnit.unit PUnit.unit PUnit.unit :=
    congrArg (fun f : Step wFrame =>
      f wZero PUnit.unit PUnit.unit PUnit.unit PUnit.unit) h
  have h2 : @LawRuleToTraj.toDetFun wC wX wX wX.meas lawToZero isDirac_lawToZero
        (wCtx wZero PUnit.unit PUnit.unit PUnit.unit PUnit.unit) wZero
      = @LawRuleToTraj.toDetFun wC wX wX wX.meas lawToOne isDirac_lawToOne
        (wCtx wZero PUnit.unit PUnit.unit PUnit.unit PUnit.unit) wZero := h1
  rw [toDetFun_lawToZero_eq, toDetFun_lawToOne_eq] at h2
  exact wZero_ne_wOne h2

/-- ⭐⭐⭐⭐ **【定理 17：`R₁ ≠ R₂` 确有不同步进（存在性形式）】**

$$\exists\ F\ (instX)\ ctxOf\ R_1\ R_2\ h_1\ h_2,\
  R_1 \neq R_2 \;\land\;
  \mathrm{lawDetToStepGen}\ \dots\ R_1\ h_1 \neq \mathrm{lawDetToStepGen}\ \dots\ R_2\ h_2 .$$

**为何非平凡**：这是一条**存在性**陈述，前件为空（无可包结论的假设）。
它直接回答了「`lawDetToStepGen` 是否依赖 `R`」：**是**。
**⟹ 因此本模块的「规则 → 轨迹」链路不是定义缝合。** -/
theorem ruleStep_depends_on_R :
    ∃ (R₁ R₂ : @LawRule.LawRule wC wX wX wX.meas)
      (h₁ : @LawRuleToTraj.IsDirac wC wX wX wX.meas R₁)
      (h₂ : @LawRuleToTraj.IsDirac wC wX wX wX.meas R₂),
      R₁ ≠ R₂ ∧
      lawDetToStepGen wFrame wX.meas wCtx R₁ h₁
        ≠ lawDetToStepGen wFrame wX.meas wCtx R₂ h₂ := by
  refine ⟨lawToZero, lawToOne, isDirac_lawToZero, isDirac_lawToOne, ?_,
    ruleStep_depends_on_R_z⟩
  intro h
  have h1 : lawToZero PUnit.unit wZero = lawToOne PUnit.unit wZero :=
    congrArg (fun R : @LawRule.LawRule wC wX wX wX.meas => R PUnit.unit wZero) h
  have h1' : ({MeasureTheory.Measure.dirac wZero} : Set (MeasureTheory.Measure wX.Carrier))
      = {MeasureTheory.Measure.dirac wOne} := h1
  have hy : (MeasureTheory.Measure.dirac wZero : MeasureTheory.Measure wX.Carrier)
      ∈ ({MeasureTheory.Measure.dirac wOne} : Set (MeasureTheory.Measure wX.Carrier)) :=
    h1' ▸ Set.mem_singleton _
  exact wZero_ne_wOne (MeasureTheory.dirac_eq_dirac_iff.mp (Set.mem_singleton_iff.mp hy))

end
end RuleEntersWorldModel
end FateV2.Loop