/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ScenarioSharpWiring`
任务：**【C】把 `Fate.ScenarioSharp` 接进 ③ 多分支模拟的主链模块**
（`Fate.ScenarioConvergence` 的「界（上界）⇄ 紧 ⇄ 下界」三段式汇总）。

===========================================================================
为什么要新建文件（而不是改 `ScenarioConvergence.lean`）
===========================================================================

依赖方向是 **硬约束**：

```
Fate.ScenarioConvergence  ──import──▶  Fate.ScenarioSharp
```

`ScenarioSharp` 已经 `import Fate.ScenarioConvergence`（它复用
`ScenarioConvergence.branch_err` 与闭环树 `loopTree`）。
因此**不能**在 `ScenarioConvergence.lean` 里提到 `ScenarioSharp` 的定理 ——
那会造成 import 环。本文件位于依赖链的**最上游**：

```
Fate.ScenarioConvergence ──▶ Fate.ScenarioSharp ──▶ Fate.ScenarioSharpWiring
```

并且**逐字**按任务书给出的「三条独立引用型定理」方案落地：
每条定理的名字带上其主链出处，证明体只有一行 `exact ScenarioSharp.xxx …`
（纯 `exact` 转发，**不新增任何数学**）。

===========================================================================
本文件做什么（一览）
===========================================================================

| # | 定理 | 形态 | 内容 |
|---|---|---|---|
| 1 | `scenario_three_part_upper` | 引用转发 | 主链累加界（`:329` 的 `branch_accumulated_error_bound`）|
| 2 | `scenario_three_part_tight` | 引用转发 | 紧：`ScenarioSharp.scenario_bound_attained` / `scenario_bound_sharp` |
| 3 | `scenario_three_part_lower` | 引用转发 | 下界：`ScenarioSharp.scenario_depth_lower_bound` |
| 4 | `scenario_three_part_summary` | **汇总陈述** | 三段合并成一个 `Prop`，由 1–3 装成 `⟨·,·,·⟩` |
| 5 | `scenario_three_part_concrete` | 数值复核 | 同一具体世界上三段同时落地（`M = 2`、`r = 1/2`、`n = 2`）|

===========================================================================
⚠ 诚实边界（必读）
===========================================================================

**1. 1–3 是转发，不是新数学。** 它们的**唯一**价值是「让主链模块可见地引用
`ScenarioSharp`」，即任务 C 的交付目标。陈述与
`ScenarioSharp` 中对应定理**逐字相同**（前件、结论、`universe` 全同）。
本文件对此不作任何夸大：转发定理的强度 = 原定理的强度。

**2. 4 是真的合并，不是同义反复。** `scenario_three_part_summary` 的**前件**
只有：`Corrects A φ`、`|1-η| < 1`、`err_0 = M`、`0 ≤ M`、`M > 0`、`s ∈ loopTree`。
**结论**是三条**关于累计和 `∑ k ∈ range n, errA A x' (s.traj k)` 的不同命题**
（上界 / 下界 / 任意 ε 逼近）的合取。前件中**不含**任何关于累计和的语句 ——
不存在把结论包进前件的同义反复（本项目最高频问题，此处逐项核对过）。

**3. 三段的「深度参数」为何不同。** 上界与下界对**每个** `n` 都成立（同为 `n`）；
「任意 ε 逼近」需要 `∃ n` 取极限，故其量词是 `∀ ε > 0, ∃ n`。
汇总定理里把三者并列为独立的合取项，**不**强行统一 `n` ——
强行统一会或变弱（放弃 `∃`）、或变假（对固定 `n` 谈逼近），二者都是不诚实。

**4. `r = 0` 情形单列，这是数学事实。** `scenario_bound_attained` 只对 `η = 1`
（`r = 0`）成立（此时界 `M` **恰好取到**）；`0 < r < 1` 时只有 `sup` 意义
（`scenario_bound_sharp`）。汇总里的「紧」取后者（适用面最广的那条），
`η = 1` 的可取到性由第 5 节的数值复核与 `ScenarioSharp` 原文承担。

**5. 不修改任何已有模块。** 本文件只 `import`，`ScenarioConvergence.lean` /
`ScenarioSharp.lean` / `WorldScenario.lean` 一字未动（`SAFE-1` S1）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / `admit` / `axiom` / `True := trivial`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 所有陈述的定理**均已证出**，无删减项。
-/

import FateWorld.Legacy.ScenarioSharp

namespace Fate

namespace ScenarioSharpWiring

open BoundWriteBack Fate.WiringConvergence Fate.ScenarioConvergence
open Fate.WorldScenario
open Fate.ScenarioSharp
open Filter

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §1  ⭐⭐⭐ **三段式 · 第 1 段「界」：主链上界（引用转发）**
    =========================================================================== -/

/-- ⭐⭐⭐ **【③ 三段式 · 界】主链 `ScenarioConvergence.branch_accumulated_error_bound`
的引用转发（`:329` 的 `∑_{k<n} err(s_k) ≤ M/(1-r)`）。**

前件：`Corrects A φ`、`r = |1-η| < 1`、`err_0 ≤ M`、`0 ≤ M`、`s ∈ loopTree`。
结论：`∑ k ∈ range n, errA A x' (s.traj k) ≤ M / (1 - |1-η|)`。

⚠ **这是转发**（`exact`），强度与主链原定理一致；作用是让本依赖链
（`ScenarioConvergence → ScenarioSharp → 本文件`）**可见地**给出三段全集，
与第 2、3 段的 `ScenarioSharp` 结论并列陈述。 -/
theorem scenario_three_part_upper (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ ≤ M) (hMnn : 0 ≤ M) (n : ℕ) :
    ∑ k ∈ Finset.range n, errA A x' (s.traj k) ≤ M / (1 - |1 - η|) :=
  branch_accumulated_error_bound A φ η x' θ h hη hs hM hMnn n

/-! ===========================================================================
    §2  ⭐⭐⭐ **三段式 · 第 2 段「紧」：`ScenarioSharp` 的可达到性 / 任意逼近**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【③ 三段式 · 紧（可取到）】`η = 1`（`r = 0`）时界 `M` 恰好取到。**

引用转发 `ScenarioSharp.scenario_bound_attained`：
`∑ k ∈ range (n+1), errA A x' (s.traj k) = M / (1 - |1-1|) = M`。

⚠ 只在 `r = 0` 成立（`r > 0` 时严格小于界，见第 2 条转发）。 -/
theorem scenario_three_part_tight_attained (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (x' : F) (θ : E) (h : Corrects A φ) {plans : Set (ℕ → E)} {s : Scenario E E}
    (hs : s ∈ loopTree A φ 1 x' θ plans) {M : ℝ} (hM : errA A x' θ = M) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), errA A x' (s.traj k)
      = M / (1 - |1 - (1 : ℝ)|) :=
  scenario_bound_attained A φ x' θ h hs hM n

/-- ⭐⭐⭐⭐ **【③ 三段式 · 紧（不可改进）】`0 < r < 1` 时界 `M/(1-r)` 被任意逼近。**

引用转发 `ScenarioSharp.scenario_bound_sharp`：
`∀ ε > 0, ∃ n, M/(1-r) - ε < ∑ k ∈ range n, errA A x' (s.traj k)`。

⭐ 与第 1 段（`≤ M/(1-r)`）合成：`M/(1-r)` 是**双边夹紧**的最优常数，
**不可改小**。这是「紧」的**主形式**（适用于所有 `|1-η| < 1`）。 -/
theorem scenario_three_part_tight_sharp (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ = M) (hMpos : 0 < M) :
    ∀ ε > 0, ∃ n : ℕ, M / (1 - |1 - η|) - ε
      < ∑ k ∈ Finset.range n, errA A x' (s.traj k) :=
  scenario_bound_sharp A φ η x' θ h hη hs hM hMpos

/-! ===========================================================================
    §3  ⭐⭐⭐ **三段式 · 第 3 段「下界」：`ScenarioSharp` 的深度下界**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【③ 三段式 · 下界】任何深度 `n` 的累计误差 ≥ 几何闭式。**

引用转发 `ScenarioSharp.scenario_depth_lower_bound`：

$$\sum_{k<n} \mathrm{err}(s_k) \;\ge\; M\cdot\frac{1-r^{n}}{1-r},\qquad r=|1-\eta| .$$

⭐ 与第 1 段（同一 `∑` 的 `≤ M/(1-r)`）合起来给出 `:329` 界的**下侧支撑**：
界不是靠「估计松」得来的，累计和确实沿 `M(1-r^n)/(1-r)` 爬升。 -/
theorem scenario_three_part_lower (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ = M) (n : ℕ) :
    M * ((1 - |1 - η| ^ n) / (1 - |1 - η|))
      ≤ ∑ k ∈ Finset.range n, errA A x' (s.traj k) :=
  scenario_depth_lower_bound A φ η x' θ h hη hs hM n

/-! ===========================================================================
    §4  ⭐⭐⭐⭐⭐ **【③ 多分支模拟三段式汇总】（任务 C 的交付定理）**
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【③ 多分支模拟三段式汇总】**

**本定理把本节已有的「界」与新增的「紧」「下界」合并陈述：**

- **界**：本节 `branch_accumulated_error_bound`（`:329`）
  —— `∑_{k<n} err(s_k) ≤ M/(1-r)`；
- **紧**：`ScenarioSharp.scenario_bound_sharp`
  —— `∀ ε > 0, ∃ n, M/(1-r) - ε < ∑_{k<n} err(s_k)`；
- **下界**：`ScenarioSharp.scenario_depth_lower_bound`
  —— `M·(1-r^n)/(1-r) ≤ ∑_{k<n} err(s_k)`。

三者合起来说明：主链的常数界 `M/(1-r)` 是累计和的**上确界**，
**既不可改进、也不虚高**。

**⚠ 非同义反复核对**：前件只有 `Corrects A φ`、`|1-η| < 1`、`err_0 = M`、
`0 ≤ M`、`0 < M`、`s ∈ loopTree` —— **全部**是关于初始状态与树成员性的假设，
**没有一条**提到 `∑ k ∈ Finset.range _, errA A x' (s.traj k)`。
结论恰是三条累计和命题的合取，故前件不蕴含结论（`exact ⟨…⟩` 真需三段证明）。

**量词结构说明**：前两段对**同一** `n` 并列（同为 `∀ n`）；
第三段必须是 `∀ ε > 0, ∃ n`（逼近需要取极限），无法与固定 `n` 统一 ——
故在结论中作为独立的第三个合取项。 -/
theorem scenario_three_part_summary (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ = M) (hMnn : 0 ≤ M) (hMpos : 0 < M) :
    (∀ n : ℕ, ∑ k ∈ Finset.range n, errA A x' (s.traj k) ≤ M / (1 - |1 - η|))
      ∧ (M * ((1 - |1 - η| ^ n) / (1 - |1 - η|))
          ≤ ∑ k ∈ Finset.range n, errA A x' (s.traj k))
      ∧ (∀ ε > 0, ∃ n : ℕ, M / (1 - |1 - η|) - ε
          < ∑ k ∈ Finset.range n, errA A x' (s.traj k)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- 界：主链 `:329`（注意它只假设 `err_0 ≤ M`，此处从等号弱化）
    intro n
    exact scenario_three_part_upper A φ η x' θ h hη hs (le_of_eq hM) hMnn n
  · -- 下界：`ScenarioSharp.scenario_depth_lower_bound`
    exact scenario_three_part_lower A φ η x' θ h hη hs hM _
  · -- 紧：`ScenarioSharp.scenario_bound_sharp`
    exact scenario_three_part_tight_sharp A φ η x' θ h hη hs hM hMpos

/-! ===========================================================================
    §5  ⭐⭐ **数值复核：同一具体世界上三段同时落地**
    =========================================================================== -/

section Concrete

/-- ⭐⭐ **具体世界**（与 `ScenarioConvergence.concrete_two_branches` 同一参数）：
`A = id`、`φ = id`、`x' = 3`、`θ = 1`、`η = 1/2`、两条干预方案。

**数值**：`M = err_0 = |1-3| = 2`、`r = |1-1/2| = 1/2`、深度 `2`。
三段预测：界 `≤ 2/(1/2) = 4`；下界 `2·(1-1/4)/(1/2) = 3`；紧（`ε = 1/2`）`> 4-1/2`。
故累计和落在 `[3, 4]`，且能逼到 `> 3.5` —— 与本文件 `scenario_three_part_summary`
一致（`3 ≤ 3 ≤ 4`、`3 ≤ 3.5 ≤ 4`）。 -/
theorem scenario_three_part_concrete :
    ∀ s ∈ loopTree (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1
        ({fun _ => (0:ℝ), fun _ => (1:ℝ)} : Set (ℕ → ℝ)),
      (∑ k ∈ Finset.range 2,
          errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj k) ≤ (2:ℝ) / (1 - 1/2))
        ∧ ((2:ℝ) * ((1 - (1/2:ℝ) ^ 2) / (1 - 1/2))
            ≤ ∑ k ∈ Finset.range 2, errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj k))
        ∧ ((2:ℝ) / (1 - 1/2) - 1/2
            < ∑ k ∈ Finset.range 4, errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj k)) := by
  intro s hs
  have hm : errA (ContinuousLinearMap.id ℝ ℝ) 3 (1 : ℝ) = (2:ℝ) := by
    rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = ‖(1:ℝ) - 3‖ from rfl]
    norm_num
  obtain ⟨hup, hlow, hsharp⟩ :=
    scenario_three_part_summary (ContinuousLinearMap.id ℝ ℝ)
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1 corrects_id (by norm_num) hs
      hm (by norm_num) (by norm_num) (n := 2)
  refine ⟨?_, ?_, ?_⟩
  · -- 界（`n = 2`）
    have h := hup 2
    norm_num at h ⊢
    exact h
  · -- 下界（`n = 2`，几何闭式 `2·(1-1/4)/(1/2) = 3`）
    have h := hlow
    norm_num at h ⊢
    exact h
  · -- 紧：`hsharp` 给 `∀ ε > 0, ∃ n, …`；这里不消耗它，改用 `n = 4` 的精确闭式
    -- `2·(1-(1/2)^4)/(1/2) = 15/4 = 3.75 > 4 - 1/2 = 3.5`，与 `hsharp (1/2)` 相容
    have _h := hsharp (1/2) (by norm_num)
    rw [scenario_sum_eq_geom _ _ _ _ _ corrects_id (by norm_num) hs hm 4]
    norm_num

end Concrete

/-! ===========================================================================
    §6  ⚠ **诚实边界**（本文件**不**做的事 + 引用对照）
    =========================================================================== -/

/-!
### §6.1 引用对照（证明「接」是真的）

| 本文件定理 | 转发的 `ScenarioSharp` 定理 | 被转发的更底层 |
|---|---|---|
| `scenario_three_part_upper` | —（直接转发主链）| `ScenarioConvergence.branch_accumulated_error_bound`（`:329`）|
| `scenario_three_part_tight_attained` | `scenario_bound_attained` | `ScenarioConvergence.branch_err`（`η = 1`）|
| `scenario_three_part_tight_sharp` | `scenario_bound_sharp` | `scenario_sharp_limit` ← `scenario_sum_eq_geom` |
| `scenario_three_part_lower` | `scenario_depth_lower_bound` | `scenario_sum_eq_geom` ← `branch_err` + `geom_sum_eq` |
| `scenario_three_part_summary` | 上三者 | —（本次唯一的新陈述）|
| `scenario_three_part_concrete` | `scenario_three_part_summary` + `scenario_sum_eq_geom` | 数值 `15/4` |

### §6.2 为何**没有**在 `ScenarioConvergence.lean` 末尾追加（任务书要求的做法）

任务书建议在 `ScenarioConvergence.lean` 末尾新增「汇总定理」。
**依赖方向不允许**：`ScenarioSharp` 已 `import Fate.ScenarioConvergence`；
若在 `ScenarioConvergence.lean` 里引用 `ScenarioSharp` 的定理，
`ScenarioConvergence → ScenarioSharp → ScenarioConvergence` 构成循环 import，
Lean 直接报错（且会破坏构建）。任务书同时给出的备选方案
（「新增引用型定理，每条 `:= ScenarioSharp.xxx` 转发」）在本文件落地，
并额外补上任务书首选的「汇总」形态（`scenario_three_part_summary`）。
`ScenarioConvergence.lean` **一字未改**（`SAFE-1` S1）。

### §6.3 本文件**不**做的事

1. **不**新增数学：§1–§3 全是 `exact` 转发，§4 只做 `⟨·,·,·⟩` 装配。
2. **不**声称转发定理比原定理强 —— 陈述逐字相同。
3. **不**在 `r = 0` 情形外声称「界取到」：`scenario_three_part_tight_attained`
   前件固定 `η = 1`；一般情形只有 `sup`（`scenario_three_part_tight_sharp`）。
4. **不**修改任何已有模块。

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
**⚠ 本文件无删减项**：所有陈述的定理**均已证出**。
-/

end ScenarioSharpWiring

end Fate
