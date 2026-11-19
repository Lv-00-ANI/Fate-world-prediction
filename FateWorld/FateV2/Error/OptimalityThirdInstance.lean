/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.OptimalityThirdInstance`
任务：**把 `OptimalityPattern`（19 条定理）应用到第三个真实例上**，
检验「界 + 可达 + 唯一」模式的普适性。

===========================================================================
本文件**实际声明**的定理/定义（与下文逐一对应，无宣传溢出）
===========================================================================

§1  ⭐ **第三实例（正面）：`Fate.FitBoundary` 的 `profExp` @ `σ = 2`**
    fitExpPattern                       ⭐⭐ `profExp.err` 在 `ℝ` 上以 `2` 为界紧唯一最小值
    fitExp_opt_unique                   达到 `2` 的 `γ` **必等于** `0`
    fitExp_opt_value_eq                 达到 `2` 的 `γ` 与最优点同值
    fitExp_gap_zero_iff                 间隙 `err γ - 2 = 0 ↔ γ = 0`
    fitExp_star_zero                    `p_star = 0`
    fitExp_lb_two                       `lb = 2`
    fitExp_opt_le                       `2 ≤ err γ`（经 `opt_le`）

§2  ⚠⚠ **负面结果一：`Fate.InterventionTight` 不满足模式（点层）**
    no_point_unique_of_two_eq           水平集有两点 ⟹ **不存在**带 `unique` 字段的模式

§2.1 干预选择上的显式反例（承接 §2）
    scenTop_ne_scenBot                  `scenTop ≠ scenBot`（不同 `plan`）
    T2 / T2_nonempty / constPolicy      两点树 + 常得分策略（显式构造）
    intervention_no_point_unique        ⭐ `↑T2` 上**不存在**点层 `OptimalityPattern`
    intervention_only_value_layer       干预选择只满足「值层」最优性，不满足「点层」

§3  ⚠ **负面结果二：`Fate.FitBoundary` 的 `profW` @ `σ = 0` 不满足模式**
    fitW_no_pattern_profW               `profW` 有两边界点 ⟹ `unique` 为假
    fitW_two_boundary_points            两点反例的显式形态
    fitW_two_star_candidates            两个 `p_star` 候选都满足 `bound ∧ attained`

§4  **三实例并置**
    three_instances_share_pattern       Gauss–Markov / OptimalEta / `profExp`

===========================================================================
⚠ **结论 (d)：`OptimalityPattern` 是否覆盖干预选择的最优性？**
===========================================================================

**答：只在「值层」覆盖，不在「点层」覆盖。** 详见 §5.3。

* `InterventionTight` 的 `bestScore_isGreatest` = `bound ∧ attained`；
  `bestScore_no_better` = `bound` 的推论；`bestScore_isLUB` = `bound` 的
  `⟺` 形态。**三条全部符合模式的前两字段。**
* **但 `unique` 字段在点层为假** —— `InterventionTight` 自己的诚实边界 4
  已声明「`chooseOptimal` 的 tie-breaking 仍未承诺」。本文件 §2
  **把这件事证成定理**（`intervention_no_point_unique`），
  给出**显式反例树** `T2 = {scenTop, scenBot}` 与常得分策略，
  两点得分相同但 `scenTop ≠ scenBot`。
* **⟹ 结论**：`OptimalityPattern` 覆盖干预选择的**最优值**唯一性，
  **不覆盖**干预选择的**最优干预**唯一性。这是模式的**真实边界**，
  不是模式缺陷：`unique` 需要点层可判别性（`DecidableEq` / 严格凸性 /
  Cauchy–Schwarz 等号结构），而干预场景层**三者皆无**。

**⟹ 真正的第三实例因此不是干预选择，而是 `FitBoundary` 的 `profExp`**
（严格凸 ⟹ 唯一，见 §1）。这一「换实例」本身是本轮任务的实质结论：
模式普适，但**每个实例都必须各自提供 `unique` 的几何来源**。

===========================================================================
⚠ 前件自查（最高频问题：结论是否已被前件包进去）
===========================================================================

逐条见 §5.1 表格。三点特别说明：

1. `fitExpPattern` 的三个字段分别来自 `IsFitBoundary` 的**第二分量**
   （`∀γ', 2 ≤ err γ'`）、`profExp_err` 在 `γ = 0` 的求值、
   `eq_of_isFitBoundary_of_strictConvexOn`。**没有**任何字段把
   「`p_star = 0`」或「唯一」放进前件。
2. `fitExp_star_zero` / `fitExp_lb_two` 是 `rfl`（定义展开），
   **如实登记为弱**，不当作独立数学内容。
3. `no_point_unique_of_two_eq` 的前件是「存在两点同值且不同」，
   结论是「不存在 `p_star`」。**前件不含 `p_star`**，故非同义反复。

===========================================================================
⚠ 诚实边界
===========================================================================

1. **§2 的负面结果只针对「点层」**。值层唯一性
   （`OptimalityPattern.value_unique` 形态）**在干预选择上仍成立**，
   只是它不需要 `OptimalityPattern` 的 `unique` 字段，只需 `attained`。
   本文件**不**主张「干预选择完全不满足模式」。
2. **§2 的反例用的是常得分 `score ≡ 0`** —— 这是**合法的** `Policy`
   （`Policy.score` 无任何额外约束），但**不是**一个「有意义的」判准。
   本文件**不**主张真实判准一定退化；只主张「**存在**退化实例」，
   而模式的 `unique` 字段是**全称**要求（对一切实例），故一条反例即否定。
3. **§3 只证 `profW` 这一个剖面不满足模式**，
   **不**声称「所有误差剖面都不满足」（那是假的：§1 的 `profExp` 就满足）。
4. **本文件不重新证明任何不等式**：§1 只调用 `profExp_err /
   profExp_strictConvex / existsUnique_isFitBoundary_of_strictConvexOn`；
   §3 只调用 `boundary_not_unique`。
5. **§1 的 `fitExpPattern` 是 `def` 不是 `theorem`**：其真伪完全由
   `FitBoundary` 承担（与 `OptimalityPattern` 文件 §6.2 同一登记口径）。
6. **零 `sorry` / 零 `admit` / 零 `axiom`**。本文件**无删除项**。

===========================================================================
纪律：只新增本文件，不修改任何已有模块（只 `import`）。
===========================================================================
-/

import FateWorld.FateV2.Error.OptimalityPattern
import FateWorld.FateV2.Predict.InterventionTight
import FateWorld.FateV2.Error.FitBoundary
namespace FateV2.Error

open FateV2.Modeling
open FateV2.Predict
/-!
  # Error · OptimalityThirdInstance

  ## 迁移登记
  - 来源：`FateWorld/Legacy/OptimalityThirdInstance.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：OptimalityPattern, InterventionTight, FitBoundary
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  ⭐⭐⭐ **第三实例（正面）：`profExp` 的误差以 `2` 为界紧唯一最小值**
    =========================================================================== -/

namespace FitExpThirdInstance

open FateV2.Error.Core

/-- ⭐⭐⭐⭐⭐ **【实例 C：`profExp` 满足 `OptimalityPattern`】**

`Fate.FitBoundary.profExp` 的误差为 $E(\gamma)=e^{\gamma}+e^{-\gamma}$。
令

* 参数空间 `ℝ`（分辨率粒度）；
* `f γ := profExp.err γ`；
* `lb := 2`；
* `p_star := 0`。

三个字段的**来源**（**全部**来自 `Fate.FitBoundary`）：
* `bound`    ← `IsFitBoundary` 的第二分量（`profExp.err 0 = 2` 提供边界点，
  于是 `∀ γ, 2 ≤ err γ`）；
* `attained` ← `profExp_err 0` + `Real.exp_zero`（`exp 0 + exp 0 = 2`）；
* `unique`   ← `eq_of_isFitBoundary_of_strictConvexOn`（严格凸 ⟹ 最小点唯一），
  其严格凸前提由 `profExp_strictConvex` 提供。

**⚠ 本定义不重新证明任何凸性或 AM–GM 不等式**，只做「填字段」。 -/
noncomputable def fitExpPattern : OptimalityPattern ℝ where
  f := fun γ => profExp.toErrProfileWeak.err γ
  lb := 2
  p_star := 0
  bound := by
    have h := profExp_unique_boundary_two
    obtain ⟨γ₀, hγ₀, _⟩ := h
    exact fun γ => hγ₀.2 γ
  attained := by
    show profExp.toErrProfileWeak.err 0 = 2
    rw [profExp_err]
    norm_num [Real.exp_zero]
  unique := by
    intro γ hγ
    have hb : IsFitBoundary profExp.toErrProfileWeak 2 γ :=
      ⟨hγ, (by
        obtain ⟨γ₀, hγ₀, _⟩ := profExp_unique_boundary_two
        exact hγ₀.2)⟩
    have hb0 : IsFitBoundary profExp.toErrProfileWeak 2 0 :=
      ⟨by
        show profExp.toErrProfileWeak.err 0 = 2
        rw [profExp_err]; norm_num [Real.exp_zero],
       (by
        obtain ⟨γ₀, hγ₀, _⟩ := profExp_unique_boundary_two
        exact hγ₀.2)⟩
    exact eq_of_isFitBoundary_of_strictConvexOn profExp_strictConvex hb hb0

/-- ⭐⭐⭐ **【实例 C 的模式定理展开：最优点唯一】**

任何使误差达到下界 `2` 的 `γ` 都**等于** `0`。

**⭐ 推导链**：`err γ = 2`（`γ` 取到下界）⟹ `γ = p_star`（模式 `unique_opt`）
⟹ `γ = 0`（`p_star` 的定义）。
结论 `γ = 0` **不**在前件中出现。 -/
theorem fitExp_opt_unique (γ : ℝ) (h : fitExpPattern.f γ = fitExpPattern.lb) :
    γ = 0 := by
  have h' := OptimalityPattern.unique_opt fitExpPattern γ h
  simpa [fitExpPattern] using h'

/-- ⭐⭐ **【实例 C 的最优值唯一】** 达到 `2` 的点与最优点同值。 -/
theorem fitExp_opt_value_eq (γ : ℝ) (h : fitExpPattern.f γ = fitExpPattern.lb) :
    fitExpPattern.f γ = fitExpPattern.f fitExpPattern.p_star :=
  OptimalityPattern.value_unique _ γ h

/-- ⭐⭐ **【实例 C 的间隙刻画】** `err γ - 2 = 0 ↔ γ = 0`。 -/
theorem fitExp_gap_zero_iff (γ : ℝ) :
    fitExpPattern.f γ - fitExpPattern.lb = 0 ↔ γ = 0 := by
  rw [OptimalityPattern.gap_zero_iff]
  simp [fitExpPattern]

/-- ⭐ **【实例 C 的最优点识别】** `p_star = 0`（`rfl`，登记为弱）。 -/
theorem fitExp_star_zero : fitExpPattern.p_star = (0 : ℝ) := rfl

/-- ⭐ **【实例 C 的下界识别】** `lb = 2`（`rfl`，登记为弱）。 -/
theorem fitExp_lb_two : fitExpPattern.lb = 2 := rfl

/-- ⭐⭐ **【实例 C 的最优性】** `2 ≤ err γ` 对一切 `γ`（经模式 `opt_le`）。

**⚠ 这不是 AM–GM 的重证**：它经 `opt_le`（`attained` + `bound` 组合）
从上面已填的 `fitExpPattern` 得到。 -/
theorem fitExp_opt_le (γ : ℝ) : fitExpPattern.f fitExpPattern.p_star ≤ fitExpPattern.f γ :=
  OptimalityPattern.opt_le fitExpPattern γ

end FitExpThirdInstance

/-! ===========================================================================
    §2  ⚠⚠ **负面结果一：`Fate.InterventionTight` 不满足点层模式**
    =========================================================================== -/

/-!
### 为什么必须给这条负面结果

`Fate.InterventionTight` 提供了

* `bestScore_isGreatest` —— 「取等 + 上界」，即模式的 `attained ∧ bound`；
* `bestScore_no_better`  —— 「不存在更好的干预」，`bound` 的推论；
* `bestScore_isLUB`      —— `bound` 的 `⟺` 形态。

**前两字段全部符合。** 但模式的第三个字段 `unique : ∀ p, f p = lb → p = p_star`
**在场景层为假**：`InterventionTight` 的诚实边界 4 明确说
「`chooseOptimal` 的 tie-breaking 仍未承诺」。下面把这件事**证成定理**。
-/

namespace InterventionNegative

open FateV2.Predict.WorldScenario FateV2.Predict.WorldScenario.Tight

universe u

/-- ⭐⭐⭐⭐ **【负面结果的一般形态】**

若 `f` 在**两个不同点** `s ≠ t` 上**同时**取到下界 `lb`（`f s = lb` 且
`f t = lb`），则**不存在**任何 `p_star` 使 `unique` 型条件
`∀ p, f p = lb → p = p_star` 成立。

**⟹** 模式的 `unique` 字段**要求 `f` 在水平集 `{p | f p = lb}` 上至多一点**。
凡该水平集有 `≥ 2` 点（「最优不唯一」），点层模式**不可能**存在。

**⚠ 前件自查**：前件是关于 `f, lb, s, t` 的；结论是「**不存在** `p_star`」。
前件**不含** `p_star`，中间必须做「`s = p_star = t`」的**矛盾推理**。 -/
theorem no_point_unique_of_two_eq {S : Type u} (f : S → ℝ) (lb : ℝ) (s t : S)
    (hst : s ≠ t) (hs : f s = lb) (ht : f t = lb) :
    ¬ ∃ p_star : S, ((f p_star = lb) ∧ ∀ p : S, f p = lb → p = p_star) := by
  rintro ⟨ps, _, huniq⟩
  have h1 : s = ps := huniq s hs
  have h2 : t = ps := huniq t ht
  exact hst (by rw [h1, h2])

/-! ### §2.1 干预选择上的显式反例 -/

attribute [local instance] Classical.decEq

/-- 顶端场景 `plan ≡ true` 与底端场景 `plan ≡ false` **不同**
（它们在时刻 `0` 的动作为 `true` / `false`）。 -/
theorem scenTop_ne_scenBot : scenTop ≠ scenBot := by
  intro h
  have h2 : scenTop.plan 0 = scenBot.plan 0 := by rw [h]
  have h3 : scenTop.plan 0 = true := rfl
  have h4 : scenBot.plan 0 = false := rfl
  rw [h3, h4] at h2
  exact Bool.noConfusion h2

/-- ⭐ **两点场景树** `{scenTop, scenBot}`（**得分相同**的两条不同干预）。 -/
noncomputable def T2 : Finset (Scenario Bool Unit) := {scenTop, scenBot}

theorem T2_nonempty : T2.Nonempty := ⟨scenTop, by simp [T2]⟩

/-- ⭐ **常得分策略**：`score ≡ 0`（合法 `Policy`，用于构造反例）。

`choose` 复用 `Tight.baseChoose`（满足 `choose_mem`）。 -/
noncomputable def constPolicy : Policy Bool Unit where
  score := fun _ => 0
  choose := baseChoose
  choose_mem := fun hne => baseChoose_mem hne

/-- ⭐⭐⭐⭐⭐ **【负面结果一：`InterventionTight` 不满足点层模式】**

在两点树 `T2 = {scenTop, scenBot}` 上、常得分策略 `constPolicy` 下，
**不存在**任何 `p_star` 使得「得分等于 `p_star` 的得分 ⟹ 场景相等」成立。

**⟹ 结论**：以 `↑T2` 为参数空间、以 `P.score` 为 `f` 的
`OptimalityPattern` 实例**不存在**（`unique` 字段**必然为假**）。

**⚠ 前件自查**：前件只有 `T2` 与 `constPolicy` 的**构造**；
结论是模式实例的**不存在性**。要得到它必须用
`scenTop_ne_scenBot`（`plan` 在时刻 `0` 取值不同）与 `score ≡ 0`
（两点同值），**两者都不作为假设出现在前件里**，是**证出来的**。 -/
theorem intervention_no_point_unique :
    ¬ ∃ ps : ↑T2,
        ((fun x : ↑T2 => constPolicy.score (x : Scenario Bool Unit)) ps
            = (0 : ℝ)
          ∧ ∀ p : ↑T2,
              (fun x : ↑T2 => constPolicy.score (x : Scenario Bool Unit)) p
                = (0 : ℝ) → p = ps) := by
  have hst : (⟨scenTop, by simp [T2]⟩ : ↑T2) ≠ ⟨scenBot, by simp [T2]⟩ := by
    intro h
    exact scenTop_ne_scenBot (congrArg Subtype.val h)
  exact no_point_unique_of_two_eq
    (fun x : ↑T2 => constPolicy.score (x : Scenario Bool Unit)) 0
    ⟨scenTop, by simp [T2]⟩ ⟨scenBot, by simp [T2]⟩ hst rfl rfl

/-- ⭐⭐ **【负面结果的读法：只到值层】**

即便点层不唯一，**最优值**仍被达到且唯一。
形式：`T2` 上确有场景得分**等于** `bestScore`，且**不存在**严格更高者。

**⟹ 这正是模式「值层」部分的完整内容**（`attained ∧ bound`），
而 `unique` 只剩**得分相等**这一弱形态（`value_unique` 形态）。 -/
theorem intervention_only_value_layer :
    (∃ t ∈ T2, constPolicy.score t = bestScore constPolicy T2 T2_nonempty)
      ∧ (¬ ∃ t ∈ T2, constPolicy.score t > bestScore constPolicy T2 T2_nonempty) :=
  ⟨bestScore_attained_exactly constPolicy T2 T2_nonempty,
   by
     rintro ⟨t, ht, hgt⟩
     exact bestScore_no_better constPolicy T2 T2_nonempty ht hgt⟩

end InterventionNegative

/-! ===========================================================================
    §3  ⚠ **负面结果二：`profW` @ `σ = 0` 不满足模式**
    =========================================================================== -/

namespace FitWNegative

open FateV2.Error.Core

/-- ⭐⭐⭐⭐ **【负面结果二：`profW` 不满足 `OptimalityPattern`】**

对 `profW`（`err γ = (γ² - 1)²`）与 `σ = 0`：

* `bound`    成立（`0 ≤ err γ`，因 `err γ` 是平方）；
* `attained` 成立（`err 1 = 0`）；
* **`unique` 为假**（`err (-1) = 0` 但 `-1 ≠ 1`）。

**⟹** 以 `f := profW.err`、`lb := 0`、`p_star := 1` 为数据的
`OptimalityPattern ℝ` 实例**不存在**。

**⚠ 前件自查**：前件无（只有 `profW` 与 `σ = 0` 的**字面构造**）；
结论的证明**必须**用 `profW_err` 展开成 `(γ²-1)²` 并在 `γ = ±1` 两点求值 ——
**不是**定义展开能得到的。 -/
theorem fitW_no_pattern_profW :
    profW.err 1 = 0 ∧ (∀ γ : ℝ, (0 : ℝ) ≤ profW.err γ)
      ∧ ¬ (∀ γ : ℝ, profW.err γ = 0 → γ = 1) := by
  refine ⟨boundary_not_unique.1.1, boundary_not_unique.1.2, ?_⟩
  intro hall
  have hneg : profW.err (-1) = 0 := boundary_not_unique.2.1.1
  have h := hall (-1) hneg
  norm_num at h

/-- ⭐⭐ **【反例的显式形态】** `profW` 在 `σ = 0` 处有**两个**边界点 `±1`。 -/
theorem fitW_two_boundary_points :
    IsFitBoundary profW 0 1 ∧ IsFitBoundary profW 0 (-1) :=
  ⟨boundary_not_unique.1, boundary_not_unique.2.1⟩

/-- ⭐⭐ **【为什么不满足模式，精确陈述】**

`profW` 在 `σ = 0` 处的两个边界点 `1` 与 `-1` 给出两个**不同**的
`p_star` 候选，它们在 `f := fun γ => profW.err γ`、`lb := 0` 下都满足前两字段。
**⟹ 任何** `OptimalityPattern ℝ` 的 `unique` 字段**都不可能**同时容纳两者。 -/
theorem fitW_two_star_candidates :
    (profW.err 1 = 0 ∧ ∀ γ : ℝ, (0 : ℝ) ≤ profW.err γ)
      ∧ (profW.err (-1) = 0 ∧ ∀ γ : ℝ, (0 : ℝ) ≤ profW.err γ)
      ∧ (1 : ℝ) ≠ -1 :=
  ⟨⟨boundary_not_unique.1.1, boundary_not_unique.1.2⟩,
   ⟨boundary_not_unique.2.1.1, boundary_not_unique.2.1.2⟩,
   boundary_not_unique.2.2⟩

end FitWNegative

/-! ===========================================================================
    §4  ⭐⭐⭐ **三个实例的并置**
    =========================================================================== -/

section ThreeInstances

open MeasureTheory FateV2.Error.GaussMarkovScalar FateV2.Loop.OptimalEta FateV2.Error.Core

variable {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]

/-- ⭐⭐⭐ **【三实例同构：唯一的共同结构】**

三个**具体构造出**的 `OptimalityPattern` 实例：
1. `GaussMarkovInstance.gaussMarkovPattern`（最优权重 `a ≡ 1/n`）；
2. `OptimalEtaInstance.optimalEtaPattern`（最优步长 `η = 1`）；
3. `FitExpThirdInstance.fitExpPattern`（最优粒度 `γ = 0`，下界 `2`）。

三者都**享有** `OptimalityPattern` 的全部 19 条模式定理
（`unique_opt / value_unique / gap_zero_iff / opt_le / lb_unique / star_unique / …`）。
本定理把三者的**下界与最优点识别**并列陈述，以证明「同一组公理确实被三次填满」。

**⚠ 诚实说明**：本定理只主张三者**满足同一结构**，
**不**主张它们之间有保序映射（`OptimalityPattern` 文件 §6.2 登记 1 已说明
`variance` 与 `|1-η|` 之间不存在这样的对应；指数误差与之更无对应）。 -/
theorem three_instances_share_pattern (n : ℕ) (hn : 0 < n)
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    (hv : 0 < varOf P) :
    (FateV2.Error.GaussMarkovInstance.gaussMarkovPattern n hn hP hv).lb = varOf P / (n : ℝ)
      ∧ FateV2.Error.OptimalEtaInstance.optimalEtaPattern.lb = 0
      ∧ FateV2.Error.OptimalEtaInstance.optimalEtaPattern.p_star = (1 : ℝ)
      ∧ FateV2.Error.FitExpThirdInstance.fitExpPattern.lb = 2
      ∧ FateV2.Error.FitExpThirdInstance.fitExpPattern.p_star = (0 : ℝ)
      ∧ (∀ η : ℝ, FateV2.Error.OptimalEtaInstance.optimalEtaPattern.f η
            = FateV2.Error.OptimalEtaInstance.optimalEtaPattern.lb → η = 1)
      ∧ (∀ γ : ℝ, FateV2.Error.FitExpThirdInstance.fitExpPattern.f γ
            = FateV2.Error.FitExpThirdInstance.fitExpPattern.lb → γ = 0)
      ∧ (∀ a : {a : Fin n → ℝ // ∑ i, a i = 1},
          (FateV2.Error.GaussMarkovInstance.gaussMarkovPattern n hn hP hv).f a
            = (FateV2.Error.GaussMarkovInstance.gaussMarkovPattern n hn hP hv).lb →
          a = (FateV2.Error.GaussMarkovInstance.gaussMarkovPattern n hn hP hv).p_star) :=
  ⟨rfl,
   FateV2.Error.OptimalEtaInstance.optimalEta_lb_zero,
   FateV2.Error.OptimalEtaInstance.optimalEta_star_one,
   FateV2.Error.FitExpThirdInstance.fitExp_lb_two,
   FateV2.Error.FitExpThirdInstance.fitExp_star_zero,
   fun η hη => FateV2.Error.OptimalEtaInstance.optimalEta_opt_unique η hη,
   fun γ hγ => FateV2.Error.FitExpThirdInstance.fitExp_opt_unique γ hγ,
   fun a ha => OptimalityPattern.unique_opt _ a ha⟩

end ThreeInstances

/-! ===========================================================================
    §5  ⚠ **前件自查表 + 结论 (d)**
    =========================================================================== -/

/-!
### §5.1 前件自查（逐条确认无同义反复）

| 定理 | 前件 | 结论 | 结论是否被前件包含？ |
|---|---|---|---|
| `fitExp_opt_unique` | `f γ = lb`（`err γ = 2`）| `γ = 0` | ❌ 否（全局等式 ⟹ 点识别，需 `unique` 字段 + 严格凸）|
| `fitExp_opt_value_eq` | `f γ = lb` | `f γ = f p_star` | ❌ 否（需 `attained` 代换）|
| `fitExp_gap_zero_iff` | 无 | `f γ - lb = 0 ↔ γ = 0` | ❌ 否（需 `unique` + `attained`）|
| `fitExp_opt_le` | 无 | `f p_star ≤ f γ` | ❌ 否（经 `opt_le` = `attained` + `bound`）|
| `fitExp_star_zero` | 无 | `p_star = 0` | ⚠ **是 `rfl`，登记为弱** |
| `fitExp_lb_two` | 无 | `lb = 2` | ⚠ **是 `rfl`，登记为弱** |
| `no_point_unique_of_two_eq` | `s ≠ t`、`f s = f t` | `¬∃ p_star, …` | ❌ 否（前件不含 `p_star`）|
| `scenTop_ne_scenBot` | 无 | `scenTop ≠ scenBot` | ❌ 否（需 `plan` 在时刻 `0` 求值）|
| `intervention_no_point_unique` | 无（`T2`、`constPolicy` 是构造）| 点层模式不存在 | ❌ 否（需两条子定理）|
| `intervention_only_value_layer` | 无 | 值层达到 ∧ 无更好 | ❌ 否（调用 `bestScore_attained_exactly` / `bestScore_no_better`）|
| `fitW_no_pattern_profW` | 无 | `unique` 为假 | ❌ 否（需 `profW_err` 展开 + `γ = ±1`）|
| `fitW_two_boundary_points` | 无 | 两边界点 | ❌ 否（调用 `boundary_not_unique`）|
| `fitW_two_star_candidates` | 无 | 两组 `(attained, bound)` + `1 ≠ -1` | ❌ 否（同上）|
| `three_instances_share_pattern` | `hv`、`hP`、`n ≥ 1` | 八个并列事实 | ❌ 否（合取包装，各分量均另证）|

**⚠ 登记为弱的三条**（不含数学内容，列出仅为「识别 `lb` / `p_star`」，
与 `OptimalityPattern` 文件 §4 的 `optimalEta_lb_zero` / `optimalEta_star_one`
同一口径）：
`fitExp_star_zero`、`fitExp_lb_two`（均 `rfl`），
以及 `three_instances_share_pattern` 中的 `rfl` 分量。

### §5.2 关键：`fitExpPattern` 的 `unique` 字段**没有**放入结论

`unique` 字段的类型是 `∀ γ, f γ = lb → γ = p_star`。
填入的证明是：

```
intro γ hγ
-- hγ : err γ = 2
-- 目标 : γ = 0
exact eq_of_isFitBoundary_of_strictConvexOn profExp_strictConvex
        ⟨hγ, 下界⟩ ⟨err 0 = 2, 下界⟩
```

即：**从 `err γ = 2` 出发，经「严格凸 ⟹ 最小点唯一」得到 `γ = 0`**。
`γ = 0` **不**在前件 `hγ` 中出现，`eq_of_isFitBoundary_of_strictConvexOn`
是 `FitBoundary` 的独立定理（它内部调用 Mathlib 的
`StrictConvexOn.eq_of_isMinOn`）。**故无同义反复。**

### §5.3 结论 (d)：`OptimalityPattern` 是否覆盖干预选择的最优性？

**答：只在「值层」覆盖，不在「点层」覆盖。分四点。**

1. **值层 —— 覆盖。**`InterventionTight.bestScore_isGreatest`
   字面上就是 `bound ∧ attained`（`IsGreatest` = 在集合里 + 是上界）；
   `bestScore_no_better` 是 `bound` 的推论；
   `bestScore_isLUB` 是 `bound` 的 `⟺` 形态。
   `intervention_only_value_layer`（§2）把「值层仍成立」显式证出。

2. **点层 —— 不覆盖，且不可能覆盖。**
   模式的 `unique` 要求 `p = p_star`（点相等）。
   `InterventionTight` 的诚实边界 4 声明 `chooseOptimal` 的
   tie-breaking 未承诺。§2 的 `intervention_no_point_unique`
   **把这件事证成定理**：在 `T2 = {scenTop, scenBot}` 与常得分策略下，
   `scenTop` 与 `scenBot` 得分相同但不同，故无 `p_star` 可满足 `unique`。
   `no_point_unique_of_two_eq` 给出**一般判据**：
   **`f` 非单射 ⟹ 点层模式不存在。**

3. **因此「第三个实例」不能是干预选择，只能是 `profExp`。**
   §1 的 `fitExpPattern` 用 `FitBoundary` 的严格凸性提供 `unique` 的
   **几何来源**，这是模式第三个**真正的**实例。
   **这一「换实例」本身是本轮任务的实质结论**：
   模式普适（三处填满），但**每个实例都必须各自提供 `unique` 的来源** ——
   Gauss–Markov 用 Cauchy–Schwarz 等号结构，`OptimalEta` 用 `|·|` 零点，
   `profExp` 用严格凸最小点唯一；干预选择层**三种来源皆无**。

4. **`FitBoundary` 的一般剖面也不总满足模式。**
   §3 的 `fitW_no_pattern_profW` 是**已验证的负面结果**：
   `profW`（`err = (γ²-1)²`）在 `σ = 0` 有边界点 `±1`，
   `unique` 为假。**⟹** 模式对误差剖面边界的覆盖是**有条件的**
   （恰好严格凸 / 单谷的那些剖面），不是无条件的。
   该文件自己的 `existsUnique_isFitBoundary_of_strictConvexOn`
   说明**必须**加严格凸前件才能唯一 —— 与本节结论一致。

**综合（给任务 (d) 的最终答复）**：
`OptimalityPattern` 的 19 条定理对干预选择**可用但仅到值层**；
它对「**选哪个干预**」这一**点层**问题**不可用**，且
§2 证明这**不是**模式缺陷（`unique` 需要点层可判别性，
`Scenario` 无 `DecidableEq`、无凸结构、无等号结构）。
模式普适性的**真实边界**正是：**`unique` 的几何来源必须逐实例提供。**

### §5.4 未做项（明确登记，**非**删除项）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | `Scenario A X` 的 `DecidableEq` 实例 | `Scenario` 含 `ℕ → A`、`ℕ → X` 函数，一般不可判别；**不可做** |
| 2 | 点层干预模式（若给 `Policy` 加 tie-breaking 标签） | 需**修改** `WorldScenario.Policy` —— **违反纪律 2（不改已有模块）**；且 `InterventionTight` 已诚实声明不作承诺 |
| 3 | `FitBoundary` 在**所有**剖面上不满足模式 | **为假**：§1 的 `profExp` 满足；本文件只登记 `profW` 反面 |
| 4 | 三实例之间的**函子**（保序映射）| `variance`、`\|1-η\|`、`e^γ+e^{-γ}` 三者的载体不同，之间**不存在**自然保序双射；强行构造会得到假陈述 |
| 5 | 模式的 `lb_unique / star_unique` 在干预实例上的跨模式应用 | 需第二个「同一 `f`、同一 `p_star`」的模式实例；本环境无第二个 `Policy` 的自然来源，**不做**而不虚构 |

**⚠ 无 `sorry` / `admit` / `axiom`。**
**⚠ 本文件无删除项：§1–§4 全部陈述均已证出。**
-/

end FateV2.Error