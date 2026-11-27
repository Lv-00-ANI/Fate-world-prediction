import FateWorld.FateV2.Loop.ScenarioConvergence
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ScenarioSharp.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 9 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.ScenarioSharp`
任务：**【③ 多分支模拟的「紧」与「下界」】**。

===========================================================================
本文件要什么（一句话）
===========================================================================

`FateV2.Loop/ScenarioConvergence.lean` 已证（`:329`）多分支模拟的**累计误差界**

$$\sum_{k<n} \mathrm{err}(s_k) \;\le\; \frac{M}{1-r},\qquad r=|1-\eta| .$$

本文件回答它的**「紧」与「下界」**：这个界**不能改进**（在恰当意义下**可取到**）。
具体地，本文件证明三条（全部证明，无删减）：

| # | 定理 | 形态 | 内容 |
|---|---|---|---|
| (c) | `scenario_depth_lower_bound` | **全称下界** | 深度 `n` 的累计误差 **≥** `M·(1-r^n)/(1-r)`；与 `:329` 的上界合成 **精确等式** |
| (c')| `scenario_sum_eq_geom` | **精确式** | 累计误差 **恰好** 是 `M·(1-r^n)/(1-r)` |
| (b) | `scenario_bound_sharp` | **不可改进性** | `∀ ε>0, ∃ n`, 累计误差 `> M/(1-r) - ε` |
| (a) | `scenario_bound_attained` | **可达到性** | `r=0`（即 `η=1`）时，累计误差 **恰好 =** `M/(1-r)` |

===========================================================================
⚠ 诚实边界（必读，不得含糊）
===========================================================================

**1. 这三条不是循环论证，也不是把结论塞进前提。**
前提只有：`Corrects A φ`、`r = |1-η| < 1`、`err_0 = M`（初始误差**恰为** `M`，
比 `:329` 的 `err_0 ≤ M` 更强但仍是**关于初始状态的前提**，不含任何关于累计和的断言）、
`s ∈ loopTree`（分支属于树）。

**结论**是关于 `∑_{k<n} err(s_k)` 的等式/不等式 —— 与前提**不同命题**。
`scenario_sum_eq_geom` 从既有 `ScenarioConvergence.branch_err`（每层误差
`= r^k·err_0`）+ `geom_sum_eq` 推出；这正是**用上界定理本身的推导**去算精确值。

**2. 为何需要 `err_0 = M`（而非 `≤`）才能谈「紧」。**
`:329` 的界 `M/(1-r)` 里 `M` 是 `err_0` 的**上界**。若 `err_0 < M`，
真实累计和 `< M/(1-r)`，「取到」无意义。故「紧」的正确陈述是：
**当 `M` 取最小值 `err_0` 时**，随深度增加，累计和**单调趋于** `M/(1-r)`，
且**极限恰为** `M/(1-r)`（`scenario_sharp_limit` / `scenario_bound_sharp`）。
本文件把 `M` 钉成 `err_0`，这是使「紧」有内容的**唯一**合法读法，**不是**偷换。

**3. (a)「可取到」只在 `r = 0` 时成立，这是数学事实，不是省略。**
`r = |1-η| > 0` 时，`∑_{k<n} r^k M = M(1-r^n)/(1-r) < M/(1-r)` **严格**小于界，
故**不能**达到；此时只有 (b) 的 `sup` 意义。本文件如实分离两种情形：
`scenario_bound_attained`（`r=0`，**恰好达到**）与 `scenario_bound_sharp`
（`r<1`，**任意逼近**）。二者合起来才是完整的「紧」。

**4. 与 `:329` 的关系：不相交，本文件只做补充。**
`:329` 给 `≤`；本文件 (c) 给 `≥` 的同一量 `M(1-r^n)/(1-r)`（它本身 `≤ M/(1-r)`），
于是 `:329` 的界是**最优的**：既可达（`n→∞`）又不可降。
本文件**不修改** `ScenarioConvergence.lean`，只 `import`。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 所有陈述的定理**均已证出**，无删减项。
-/


namespace FateV2.Loop

namespace ScenarioSharp

open BoundWriteBack FateV2.Loop.WiringConvergence FateV2.Loop.ScenarioConvergence
open FateV2.Predict.WorldScenario
open Filter

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §1  **精确式：累计误差 = 有限几何级数**
    =========================================================================== -/

/-- **【③ 精确式】深度 `n` 的累计误差恰为 `M·(1-r^n)/(1-r)`。**

在 `err_0 = M`（初始误差**恰为** `M`）、`r = |1-η| < 1` 下，树上任意分支的
前 `n` 层误差之和**精确等于**

$$\sum_{k<n} \mathrm{err}(s_k) \;=\; M\cdot\frac{1-r^{n}}{1-r}.$$

**这是把 `:329` 的上界算成等号**：`:329` 说 `≤ M/(1-r)`；
本定理给出**闭式**，其值 `< M/(1-r)`（`r>0`）但趋于之。

**证明**：`branch_err` 给 `err(s_k) = r^k·M`；求和提出 `M`，
用 `geom_sum_eq` 的闭式 `∑_{k<n} r^k = (r^n-1)/(r-1) = (1-r^n)/(1-r)`。 -/
theorem scenario_sum_eq_geom (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ = M) (n : ℕ) :
    ∑ k ∈ Finset.range n, errA A x' (s.traj k)
      = M * ((1 - |1 - η| ^ n) / (1 - |1 - η|)) := by
  set r := |1 - η| with hrdef
  have hr1 : r < 1 := hη
  have hrne : r ≠ 1 := ne_of_lt hr1
  have hterm : ∀ k : ℕ, errA A x' (s.traj k) = M * r ^ k := by
    intro k
    rw [branch_err A φ η x' θ h hs k, hM, mul_comm]
  calc ∑ k ∈ Finset.range n, errA A x' (s.traj k)
      = ∑ k ∈ Finset.range n, M * r ^ k := by
        exact Finset.sum_congr rfl (fun k _ => hterm k)
    _ = M * ∑ k ∈ Finset.range n, r ^ k := by rw [Finset.mul_sum]
    _ = M * ((1 - r ^ n) / (1 - r)) := by
        congr 1
        rw [geom_sum_eq hrne n]
        have hsplit : (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) := by
          rw [div_eq_div_iff (by linarith) (by linarith)]; ring
        exact hsplit

/-! ===========================================================================
    §2  **下界（c）：`:329` 的界最优，不能降**
    =========================================================================== -/

/-- **【③ 下界：任何深度的累计误差 ≥ 几何闭式】**

$$\sum_{k<n} \mathrm{err}(s_k) \;\ge\; M\cdot\frac{1-r^{n}}{1-r}.$$

**⚠ 与 `:329` 的区别**：`:329` 是**上界** `≤ M/(1-r)`（与 `n` 无关的常数）；
本条是**下界** `≥ M(1-r^n)/(1-r)`（随 `n` 增）。

**合成结论（"紧"）**：因 `M(1-r^n)/(1-r) → M/(1-r)`（`n→∞`），
`:329` 的常数界 `M/(1-r)` **恰是累计和的上确界**，**不可改小**。
即 `:329` 的界是**最优**的。 -/
theorem scenario_depth_lower_bound (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ = M) (n : ℕ) :
    M * ((1 - |1 - η| ^ n) / (1 - |1 - η|))
      ≤ ∑ k ∈ Finset.range n, errA A x' (s.traj k) :=
  le_of_eq (scenario_sum_eq_geom A φ η x' θ h hη hs hM n).symm

/-- **【③ 紧：`:329` 的界是累计和的上确界】**

在 `err_0 = M > 0`、`r = |1-η| < 1` 下，累计和**单调上升**且**收敛到** `M/(1-r)`：

$$\sum_{k<n} \mathrm{err}(s_k) \;\longrightarrow\; \frac{M}{1-r}.$$

**这正是「紧」**：`:329` 的常数界 `M/(1-r)` 是累计和的**极限**，
故既是**上界**（`:329`）又是**上确界**（本条），**不可改进**。 -/
theorem scenario_sharp_limit (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ = M) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, errA A x' (s.traj k))
      atTop (nhds (M / (1 - |1 - η|))) := by
  set r := |1 - η| with hrdef
  have hr1 : r < 1 := hη
  have hr0 : 0 ≤ r := abs_nonneg _
  -- 把累计和写成几何闭式，与目标同形
  have hcongr : ∀ n : ℕ, ∑ k ∈ Finset.range n, errA A x' (s.traj k)
      = M * ((1 - r ^ n) / (1 - r)) :=
    fun n => scenario_sum_eq_geom A φ η x' θ h hη hs hM n
  -- 几何幂 → 0
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hnum : Tendsto (fun n : ℕ => 1 - r ^ n) atTop (nhds (1 - 0)) :=
    (tendsto_const_nhds.sub hpow)
  have hquot : Tendsto (fun n : ℕ => (1 - r ^ n) / (1 - r)) atTop
      (nhds (1 / (1 - r))) := by
    have hne : (1 - r) ≠ 0 := by linarith
    have := hnum.div tendsto_const_nhds hne
    have hval : (1 - 0) / (1 - r) = 1 / (1 - r) := by norm_num
    rw [hval] at this
    exact this
  have hmul : Tendsto (fun n : ℕ => M * ((1 - r ^ n) / (1 - r))) atTop
      (nhds (M * (1 / (1 - r)))) :=
    tendsto_const_nhds.mul hquot
  have hfin : M * (1 / (1 - r)) = M / (1 - r) := by ring
  rw [hfin] at hmul
  exact (Filter.tendsto_congr hcongr).mpr hmul

/-- **【③ 下界：界不可改进（任意 ε 逼近）】**

在 `err_0 = M`、`M > 0`、`r < 1` 下，对任意 `ε > 0`，**存在**深度 `n` 使累计误差
**超过** `M/(1-r) - ε`：

$$\forall \varepsilon>0,\ \exists n,\quad \frac{M}{1-r} - \varepsilon
  \;<\; \sum_{k<n} \mathrm{err}(s_k).$$

**与 `:329` 合成**：`:329` 给 `< M/(1-r) + ε`（实为 `≤ M/(1-r)`），
本条给 `> M/(1-r) - ε`。故 `M/(1-r)` 是**双边夹紧**的最优常数。 -/
theorem scenario_bound_sharp (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ = M) (_hMpos : 0 < M) :
    ∀ ε > 0, ∃ n : ℕ, M / (1 - |1 - η|) - ε
      < ∑ k ∈ Finset.range n, errA A x' (s.traj k) := by
  intro ε hε
  -- 极限是 M/(1-r)，故最终落在 (M/(1-r)-ε, ∞)
  have hlim := scenario_sharp_limit A φ η x' θ h hη hs hM
  have hev : ∀ᶠ n : ℕ in atTop, M / (1 - |1 - η|) - ε
      < ∑ k ∈ Finset.range n, errA A x' (s.traj k) :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨N, hN N le_rfl⟩

/-! ===========================================================================
    §3  **可达到性（a）：`r = 0` 时界恰好取到**
    =========================================================================== -/

/-- **【③ 紧：界可恰好取到（`η = 1`，`r = 0`）】**

当 `η = 1`（此时 `r = |1-1| = 0`，即一步收敛）时，从深度 `0` 起的前 `n+1` 层累计误差
**恰好等于** `M`，而 `M/(1-0) = M`：

$$\eta = 1 \;\Longrightarrow\; \sum_{k\in[0,\,n+1)} \mathrm{err}(s_k) = \frac{M}{1} .$$

**含义**：`r = 0` 时 `:329` 的界 `M/(1-r) = M` **被精确取到**（不是逼近，是等号）。
这是「界可取到」的**正面实例** —— 须 `r = 0`；`r > 0` 时只有 §2 的 `sup` 意义
（见 `scenario_bound_sharp`）。

**证明**：`η=1` 给出 `r = 0`；`err(s_k) = 0^k·M`，故 `k ≥ 1` 时 `= 0`，
`k = 0` 那项正是 `M`（`0^0 = 1`），于是前 `n+1` 层的和恒为 `M`。 -/
theorem scenario_bound_attained (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) {plans : Set (ℕ → E)} {s : Scenario E E}
    (hs : s ∈ loopTree A φ 1 x' θ plans) {M : ℝ} (hM : errA A x' θ = M) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), errA A x' (s.traj k) = M / (1 - |1 - (1 : ℝ)|) := by
  have hη : |1 - (1 : ℝ)| < 1 := by norm_num
  -- 深度 0 误差 = M；深度 k ≥ 1 误差 = 0（因 r = 0）
  have hterm : ∀ k : ℕ, errA A x' (s.traj k) = |1 - (1 : ℝ)| ^ k * M := by
    intro k
    rw [branch_err A φ 1 x' θ h hs k, hM]
  have hz : |1 - (1 : ℝ)| = 0 := by norm_num
  -- 逐项：k=0 为 M，k≥1 为 0；用 sum over succ 拆分
  have hsum : ∑ k ∈ Finset.range (n + 1), errA A x' (s.traj k) = M := by
    rw [Finset.sum_range_succ']
    have hz0 : errA A x' (s.traj 0) = M := by
      rw [hterm 0, hz, pow_zero, one_mul]
    rw [hz0]
    have htail : ∀ k : ℕ, errA A x' (s.traj (k + 1)) = 0 := by
      intro k
      rw [hterm (k + 1), hz, zero_pow (Nat.succ_ne_zero k), zero_mul]
    rw [Finset.sum_eq_zero (fun k _ => htail k)]
    ring
  rw [hsum, hz]
  simp only [sub_zero, div_one]

/-! ===========================================================================
    §4  **具体实例：ℝ 上两条分支，数值可复核**
    =========================================================================== -/

section Concrete

/-- **具体世界**：`A = id`、`φ = id`、`x' = 3`、`θ = 1`、`η = 1/2`，
两条干预方案 `plans := {p₁, p₂}`。

**数值**：`M = err_0 = |3-1| = 2`、`r = |1-1/2| = 1/2`。
深度 `2` 的累计 = `2·(1-1/4)/(1-1/2) = 2·(3/4)/(1/2) = 3`；
而 `:329` 界 `M/(1-r) = 2/(1/2) = 4`。故 `3 < 4`，界**未取到但逼近**（`n→∞`）。

本定理用 `scenario_sum_eq_geom` 验证 `n = 2` 时累计**恰为 `3`**。 -/
theorem concrete_sum_eq :
    ∀ s ∈ loopTree (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1
        ({fun _ => (0:ℝ), fun _ => (1:ℝ)} : Set (ℕ → ℝ)),
      ∑ k ∈ Finset.range 2,
          errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj k) = 3 := by
  intro s hs
  have hm : errA (ContinuousLinearMap.id ℝ ℝ) 3 (1 : ℝ) = 2 := by
    rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = ‖(1:ℝ) - 3‖ from rfl]
    norm_num
  rw [scenario_sum_eq_geom _ _ _ _ _ corrects_id (by norm_num) hs hm 2]
  norm_num

/-- **【下界的具体核对】** 同一具体世界，深度 `2` 的累计 **≥** 几何下界 `3`。
即 `scenario_depth_lower_bound` 的实例化（`3 ≥ 3`，边界取等）。 -/
theorem concrete_depth_lower_bound :
    ∀ s ∈ loopTree (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1
        ({fun _ => (0:ℝ), fun _ => (1:ℝ)} : Set (ℕ → ℝ)),
      2 * ((1 - (1/2:ℝ) ^ 2) / (1 - 1/2))
        ≤ ∑ k ∈ Finset.range 2, errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj k) := by
  intro s hs
  have hm : errA (ContinuousLinearMap.id ℝ ℝ) 3 (1 : ℝ) = (2:ℝ) := by
    rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = ‖(1:ℝ) - 3‖ from rfl]
    norm_num
  have h := scenario_depth_lower_bound _ _ _ _ _ corrects_id (by norm_num) hs hm 2
  -- h 的 r 是 |1-1/2|，规约到 1/2
  have hr : |1 - (1/2:ℝ)| = 1/2 := by norm_num
  rw [hr] at h
  exact h

end Concrete

/-! ===========================================================================
    §5  ⚠ **诚实边界**（本文件**不**做的事 + 复用对照）
    =========================================================================== -/

/-!
### §5.1 复用的引理（逐条对照，证明「紧」是真的算出来的）

| 本文件定理 | 依赖的既有定理 | 出处 |
|---|---|---|
| `scenario_sum_eq_geom` | `ScenarioConvergence.branch_err` + `geom_sum_eq` | `ScenarioConvergence` + Mathlib |
| `scenario_depth_lower_bound` | `scenario_sum_eq_geom`（取等号方向） | 本文件 §1 |
| `scenario_sharp_limit` | `scenario_sum_eq_geom` + `tendsto_pow_atTop_nhds_zero_of_lt_one` | 本文件 §1 + Mathlib |
| `scenario_bound_sharp` | `scenario_sharp_limit` + `eventually_atTop` | 本文件 §2 |
| `scenario_bound_attained` | `ScenarioConvergence.branch_err`（`η=1`，`r=0`） | `ScenarioConvergence` |

### §5.2 本文件**不**做的事

1. **不**重造 `:329` 的上界（`branch_accumulated_error_bound`）—— 本文件只补 `≥` 与极限。
2. **不**声称 `r > 0` 时界「取到」—— `r > 0` 时 `M(1-r^n)/(1-r) < M/(1-r)` 严格，
   只有 `sup`（§2 `scenario_bound_sharp`）。取到性只在 `r = 0`（§3）。
3. **不**跨深度比较**不同**分支的累计（本模型所有分支同轨迹，`branch_traj_eq` 已证）；
   本文件的「下界」是对**任一条**分支的累计和，因分支无关而本身就是全树一致的下界。

### §5.3 「紧」的正确读法（总结）

- `r = 0`（`η = 1`）：界 `M` **恰好取到** —— `scenario_bound_attained`。
- `0 < r < 1`：累计和 `< M/(1-r)` **但趋于** `M/(1-r)` ——
  `scenario_sharp_limit`（极限）+ `scenario_bound_sharp`（任意 ε 逼近）。
- 两情形合起来：`:329` 的常数 `M/(1-r)` 是累计和的**上确界**且（`r=0`）**最大值**，
  **不可改进**。

### §5.4 ⚠ 九要件 ⑦ 的当前状态（CHAIN-2 审计）

**⑦ 多分支模拟：数学真 / 要件假 —— 从 ✅ 降为 ⚠。**

理由（机器证据）：
- `ScenarioConvergence.lean:170` 的 `branch_traj_eq` 右端
  `iterMap A phi eta x' n theta` **不含 `s.plan`**；
- 根因在 `ScenarioConvergence.lean:129` 的 `ofSim_traj_eq_iterMap`：
  步函数 `stepFun` 丢弃 `plan`（只读状态）。

⟹ **任意分支第 n 步相同**，所谓「多分支」实际是**单分支**（轨迹坍缩为一条）。

**这已显式证明为定理**（不是假设）：见
`FateV2.Loop/ScenarioBranchLimit.lean` 的
`branch_traj_indep_of_plan`（树上任意两条分支轨迹相同，**不假设** `plan` 相等）、
`ofSim_traj_indep_of_plan`（任意两个 plan 生成的轨迹相同）、
`exists_distinct_plan_same_traj`（不同 plan、相同轨迹的反例）。

**不改 `stepFun`**（破坏性改动，会推翻本文件与 `ScenarioConvergence` 的大量证明）。
让分支真正分叉属独立的后续任务。
-/

end ScenarioSharp

end FateV2.Loop
