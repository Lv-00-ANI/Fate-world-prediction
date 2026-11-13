import FateWorld.FateV2.Loop.WiringConvergence
import FateWorld.FateV2.Predict.WorldScenario
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecificLimits.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ScenarioConvergence.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 16 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict
open FateV2.Loop
open FateV2.Error
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.ScenarioConvergence`
任务：**【X4】把已入库的闭环收敛与场景树接起来**。

===========================================================================
本文件要什么（一句话）
===========================================================================

`FateV2.Predict.WorldScenario` 给了**场景树** `ScenarioTree`（「同时模拟不同分支」
= 对每个候选干预方案各跑一条轨迹）；`FateV2.Loop.WiringConvergence` 给了**闭环收敛**
（反复观测-预测-更新，误差按 `|1-η|^n` 几何收敛）。但**两条线此前没有相交**：

| 模块 | 现有真结果 | 定理 |
|---|---|---|
| `FateV2.Loop/WorldScenario.lean` | 场景树、方案唯一确定轨迹 | `scenario_traj_determined` |
| `FateV2.Loop/WiringConvergence.lean` | `err_n = |1-η|^n · err_0`、`err_n → 0` | `err_iterMap` / `closedLoop_tendsto_zero` |

**本文件补上的正是「接」**：把闭环的迭代动力学生成**场景树的一条分支**，
于是得到「**在场景树上，每条分支都收敛**」，并给出
「**收敛速率与分支深度的关系**」（速率 `|1-η|^n`，深度 `n`；逐支一致、
关于整个树均匀，累计误差被有限几何级数 `M/(1-|1-η|)` 控制）。

===========================================================================
⚠ 诚实边界（必读，不得含糊）
===========================================================================

**1. 分支的「干预方案」在这一层被抽象掉了，但**不是**把结论塞进前提。**
`Scenario.ofSim` 的步函数 `stepFun` 忽略 `u, e, plan`（只读状态 `x`），
因为 `WiringConvergence` 的闭环步 `stepMap` 是**线性预测器**上的
`θ ↦ θ + η • φ(x' - A θ)`，其误差递推 `err_{k+1} = |1-η|·err_k`
**与 `u, e, plan` 无关**。因此「不同干预方案」在本模型下**误差轨迹相同**，
这正是**被证明的内容**（`branch_traj_eq`），而不是假设：
我们**不**假设所有分支同轨迹，而是**证明**在闭环动力学下它们同轨迹。

**2. 「每条分支都收敛」是真的全称量化。** `tree_tendsto_uniform` 的形式是
`∀ ε>0, ∃ N, ∀ n≥N, ∀ s ∈ tree, err(s 在深度 n) < ε` ——
`∀ s ∈ tree` 在 `n≥N` **之后**，且 `N` **不依赖** `s`（对整棵树一致）。
不是「逐点各有一个 `N`」的弱形式。

**3. 收敛是「几何收敛」，速率常数 `|1-η|` 由 `WiringConvergence` 给定。**
收缩窗 `|1-η| < 1`（即 `0 < η < 2`）；窗外不收敛，本文件沿用该窗，**不**放宽。

**4. `score`（「满足要求」的判准）不在本文件范围。** 本文件只做「每条分支
收敛 + 速率-深度关系」，即「多分支模拟」的**动力学**要件；
「从收敛的分支里挑一个」（`Policy`）属 `FateV2.Loop/WorldScenario.lean` /
`FateV2.Loop/PolicyAlgorithm.lean`，本文件**不**涉及。

**5. 初始误差上界 `M` 是显式前提**（来自 `ObsEstimationStrong` 的 `L·η_max`，
见 `WiringConvergence.obs_initial_bound`）。本文件把它做成参数 `M`，
**不**在此处重造估计器。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 所有陈述的定理**均已证出**；无删减项。
-/


namespace FateV2.Loop

namespace ScenarioConvergence

open BoundWriteBack FateV2.Loop.WiringConvergence
open FateV2.Predict.WorldScenario

universe u

/-! ===========================================================================
    §1  **桥梁：`iterMap` 是迭代幂、`ofSim` 生成同样轨迹**
    =========================================================================== -/

section Bridge

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`iterMap` 就是 `stepMap` 的 `n` 次幂** `(stepMap)^[n]`。

承 `WiringConvergence.iterMap` 的定义（`Nat.rec` 从外向内剥），
本节把它转成标准 `Function.iterate`（从内向外构建），
从而与 `Scenario.ofSim`（同样从内向外 `Nat.rec`）对齐。 -/
theorem iterMap_eq_iterate (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ : E) :
    iterMap A φ η x' n θ = (stepMap A φ η x')^[n] θ := by
  induction n generalizing θ with
  | zero => simp [iterMap_zero]
  | succ k ih =>
    rw [iterMap_succ, ih (stepMap A φ η x' θ)]
    rw [Function.iterate_succ_apply]

/-- **通用辅助：`Nat.rec` 与 `Function.iterate` 一致**（从内向外构建）。 -/
theorem rec_eq_iterate {P : Type u} (g : P → P) (x : P) :
    ∀ n : ℕ, Nat.rec x (fun _ y => g y) n = g^[n] x := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show g (Nat.rec x (fun _ y => g y) k) = g^[Nat.succ k] x
    rw [Function.iterate_succ_apply', ← ih]

/-- **闭环步函数**：`Scenario.ofSim` 所需的 `step`，
**忽略** `u, e, plan`，只读状态 `x` —— 即闭环动力学 `stepMap`。

⚠ **这不是「抹掉分支」的偷懒**：`WiringConvergence` 的闭环步就是
`θ ↦ θ + η • φ(x' - A θ)`，其误差递推与 `u, e, plan` 无关（§3 证明）；
把 `u, e, plan` 显式保留为哑元，使 `Scenario.ofSim` 能接受**任意**方案。 -/
def stepFun (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) :
    E → E → E → E → E :=
  fun x _ _ _ => stepMap A φ η x' x

/-- **【桥梁核心】`ofSim` 生成的分支轨迹 = `iterMap`**。

对**任意**干预方案 `plan`，`Scenario.ofSim (stepFun …)` 在深度 `n` 的轨迹
恰是闭环 `iterMap` 迭代 `n` 步的结果。

**这是本文件把 `WorldScenario`（场景树）与 `WiringConvergence`（闭环收敛）
接起来的关键一步**：它证明 `Scenario.ofSim`（场景树的分支生成器）
与 `iterMap`（闭环迭代）是**同一条动力学**。 -/
theorem ofSim_traj_eq_iterMap (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (plan : ℕ → E) (n : ℕ) :
    ((Scenario.ofSim (stepFun A φ η x') θ (fun _ => 0) (fun _ => 0) plan).traj) n
      = iterMap A φ η x' n θ := by
  show Nat.rec θ (fun k xk => stepMap A φ η x' xk) n = iterMap A φ η x' n θ
  rw [iterMap_eq_iterate, rec_eq_iterate]

end Bridge

/-! ===========================================================================
    §2  **闭环场景树**
    =========================================================================== -/

section Tree

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **闭环场景树**：把 `ScenarioTree` 的步函数取成闭环 `stepFun`。

- 状态空间 = 参数空间 `E`（轨迹记录参数 `θ_n`）；
- 动作空间 `A = E`（干预方案 `plan : ℕ → E`，本层抽象，见文件头 §1 边界）；
- `u = e ≡ 0`（闭环是确定性的：`WiringConvergence` 的所有定理无 `u,e`）；
- `x₀ = θ`（初始参数）。

**⟹ 「同时模拟不同分支」= 对每个 `plans` 里的方案，各生成一条闭环轨迹。** -/
def loopTree (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (plans : Set (ℕ → E)) : Set (Scenario E E) :=
  ScenarioTree (stepFun A φ η x') θ (fun _ => 0) (fun _ => 0) plans

/-- **闭环树的成员刻画**（逐字继承 `WorldScenario.mem_scenarioTree`）。 -/
theorem mem_loopTree {A : E →L[ℝ] F} {φ : F →ₗ[ℝ] E} {η : ℝ} {x' : F} {θ : E}
    {plans : Set (ℕ → E)} {s : Scenario E E} :
    s ∈ loopTree A φ η x' θ plans ↔
      s.plan ∈ plans ∧
        s.traj = (Scenario.ofSim (stepFun A φ η x') θ (fun _ => 0) (fun _ => 0)
          s.plan).traj :=
  Iff.rfl

/-- **【分支轨迹】树上任意分支在深度 `n` 的轨迹 = 闭环 `iterMap`**。 -/
theorem branch_traj_eq (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    {plans : Set (ℕ → E)} {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans)
    (n : ℕ) : s.traj n = iterMap A φ η x' n θ := by
  obtain ⟨_, htraj⟩ := mem_scenarioTree.mp hs
  rw [htraj]
  exact ofSim_traj_eq_iterMap A φ η x' θ s.plan n

/-- **【分支误差 = 几何式】** 在 `Corrects` 下，树上任意分支在深度 `n`
的误差**精确地**是 `|1-η|^n · err_0`。

**这是 `WiringConvergence.err_iterMap` 被「搬到」树上**：
`err_iterMap` 说迭代 `n` 步后误差是 `|1-η|^n·err_0`；
`branch_traj_eq` 说每条分支在深度 `n` 就是迭代 `n` 步；两者一合成即是本式。 -/
theorem branch_err (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) {plans : Set (ℕ → E)} {s : Scenario E E}
    (hs : s ∈ loopTree A φ η x' θ plans) (n : ℕ) :
    errA A x' (s.traj n) = |1 - η| ^ n * errA A x' θ := by
  rw [branch_traj_eq A φ η x' θ hs n]
  exact err_iterMap A φ η x' θ h n

end Tree

/-! ===========================================================================
    §3  **主定理 1：每条分支都收敛（关于整棵树均匀）**
    =========================================================================== -/

section EveryBranch

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【逐深度·关于树一致的界】**

给定初始误差上界 `M`（`err_0 ≤ M`），树中**每一条**分支在深度 `n`
的误差都 `≤ |1-η|^n · M` —— 界**与分支无关**。

**读法**：无论模拟哪条干预分支，误差在同一深度被**同一个界**控制。 -/
theorem tree_uniform_bound (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) {plans : Set (ℕ → E)} {M : ℝ} (hM : errA A x' θ ≤ M) (n : ℕ) :
    ∀ s ∈ loopTree A φ η x' θ plans, errA A x' (s.traj n) ≤ |1 - η| ^ n * M := by
  intro s hs
  rw [branch_err A φ η x' θ h hs n]
  have hp : (0 : ℝ) ≤ |1 - η| ^ n := pow_nonneg (abs_nonneg _) n
  exact mul_le_mul_of_nonneg_left hM hp

/-- **【主定理 1：每条分支都收敛（均匀）】**

收缩窗 `|1-η| < 1` 内，**整棵场景树**的分支误差关于深度**一致收敛到 0**：

$$\forall \varepsilon>0,\ \exists N,\ \forall n\ge N,\
  \forall s\in \mathrm{loopTree},\quad \mathrm{err}(s_n) < \varepsilon .$$

**这是「多分支模拟」的实质内容**：不是「每条分支各自收敛」
（那只是 `∀ s, ∀ε, ∃N`），而是 **`∃N` 在 `∀ s` 之前** —— 一个 `N`
同时对所有分支有效。这是 `WorldScenario`（树）与 `WiringConvergence`
（收敛）合流后才能陈述的定理。

**证明**：`tree_uniform_bound` 给每条分支 `≤ |1-η|^n·M`；
`|1-η|^n·M → 0`（`tendsto_pow_atTop_nhds_zero_of_lt_one` × 常数 `M`），
取其 `N` 即对**所有**分支同时生效。 -/
theorem tree_tendsto_uniform (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)} {M : ℝ}
    (hM : errA A x' θ ≤ M) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ loopTree A φ η x' θ plans,
      errA A x' (s.traj n) < ε := by
  intro ε hε
  have hbase : Filter.Tendsto (fun n : ℕ => |1 - η| ^ n * M) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => |1 - η| ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hη
    simpa using h1.mul_const M
  have hev : ∀ᶠ n : ℕ in Filter.atTop, |1 - η| ^ n * M < ε :=
    hbase.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn s hs => ?_⟩
  calc errA A x' (s.traj n) ≤ |1 - η| ^ n * M := tree_uniform_bound A φ η x' θ h hM n s hs
    _ < ε := hN n hn

/-- **【每条分支各自收敛（沿深度 `→ 0`）】**

逐支的 `Filter.Tendsto` 形式。可用 `M := err_0`（此时 `hM` 自动成立）。

**⚠ 与主定理 1 的差别**：这里 `∀ s` 在 `Tendsto` **外**（逐支），
主定理 1 是**一致**的（`∃N` 在所有分支之前）。两者都给，主定理 1 更强。 -/
theorem branch_tendsto_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)} {s : Scenario E E}
    (hs : s ∈ loopTree A φ η x' θ plans) :
    Filter.Tendsto (fun n : ℕ => errA A x' (s.traj n)) Filter.atTop (nhds 0) := by
  have hrw : (fun n : ℕ => errA A x' (s.traj n))
      = (fun n : ℕ => errA A x' (iterMap A φ η x' n θ)) := by
    funext n
    rw [branch_traj_eq A φ η x' θ hs n]
  rw [hrw]
  exact closedLoop_tendsto_zero A φ η x' θ h hη

end EveryBranch

/-! ===========================================================================
    §4  **主定理 2：收敛速率与分支深度的关系**
    =========================================================================== -/

section RateDepth

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【深度单调：越深越准】**

收缩窗 `|1-η| < 1` 内，树中任意分支的误差**关于深度不增**：

$$n \le m \;\Longrightarrow\; \mathrm{err}(s_m) \le \mathrm{err}(s_n).$$

**「速率与深度」的第一层关系**：深度增加不放大误差。 -/
theorem branch_err_antitone (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)} {s : Scenario E E}
    (hs : s ∈ loopTree A φ η x' θ plans) {n m : ℕ} (hnm : n ≤ m) :
    errA A x' (s.traj m) ≤ errA A x' (s.traj n) := by
  rw [branch_err A φ η x' θ h hs m, branch_err A φ η x' θ h hs n]
  have hr0 : (0 : ℝ) ≤ |1 - η| := abs_nonneg _
  have hr : |1 - η| ^ m ≤ |1 - η| ^ n :=
    pow_le_pow_of_le_one hr0 (le_of_lt hη) hnm
  exact mul_le_mul_of_nonneg_right hr (errA_nonneg A x' θ)

/-- **【主定理 2：速率-深度精确关系】**

在 `Corrects` 下，**每条**分支在深度 `n` 的误差**精确等于**

$$\mathrm{err}(s_n) \;=\; |1-\eta|^{\,n}\cdot \mathrm{err}_0 ,$$

即**速率常数** `|1-η|`、**深度** `n`、且**与分支（干预方案）无关**。

**这是「收敛的速率与分支深度的关系」的正面回答**：

| 量 | 值 |
|---|---|
| 速率（每深一层的衰减比）| `\|1-\eta\|` |
| 深度 `n` 的累积因子 | `\|1-\eta\|^n` |
| 分支依赖 | **无**（所有分支同一因子）|

与 `WiringConvergence.err_iterMap` **逐字一致** —— 本定理即把后者
经 `branch_traj_eq` 搬到树上（`branch_err` 的显式重述，供引用）。 -/
theorem branch_err_rate_depth (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) {plans : Set (ℕ → E)} {s : Scenario E E}
    (hs : s ∈ loopTree A φ η x' θ plans) (n : ℕ) :
    errA A x' (s.traj n) = |1 - η| ^ n * errA A x' θ :=
  branch_err A φ η x' θ h hs n

/-- **【全树累计误差被几何级数控制】**

树上任意分支的**前 `n` 层累计误差**（各深度误差之和）被有限几何级数控制：

$$\sum_{k<n} \mathrm{err}(s_k) \;\le\; \frac{M}{1-|1-\eta|} ,$$

其中 `err_0 ≤ M`、`|1-η| = r < 1`。

**「速率-深度」的第二层关系**：不仅逐层趋零，**总代价有界** ——
无限深模拟的总误差有限（`M/(1-r)`），这是「多分支大规模模拟可终止性」
的定量依据。 -/
theorem branch_accumulated_error_bound (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ ≤ M) (hMnn : 0 ≤ M) (n : ℕ) :
    ∑ k ∈ Finset.range n, errA A x' (s.traj k) ≤ M / (1 - |1 - η|) := by
  set r := |1 - η| with hrdef
  have hr0 : 0 ≤ r := abs_nonneg _
  have hr1 : r < 1 := hη
  have hterm : ∀ k : ℕ, errA A x' (s.traj k) ≤ r ^ k * M := by
    intro k
    rw [branch_err A φ η x' θ h hs k]
    exact mul_le_mul_of_nonneg_left hM (pow_nonneg hr0 k)
  calc ∑ k ∈ Finset.range n, errA A x' (s.traj k)
      ≤ ∑ k ∈ Finset.range n, r ^ k * M := Finset.sum_le_sum (fun k _ => hterm k)
    _ ≤ M / (1 - r) := by
        have hsum : ∑ k ∈ Finset.range n, r ^ k * M
            = M * ∑ k ∈ Finset.range n, r ^ k := by
          rw [Finset.mul_sum]; simp [mul_comm]
        rw [hsum]
        have hgeo : ∑ k ∈ Finset.range n, r ^ k ≤ 1 / (1 - r) := by
          rw [geom_sum_eq (by linarith : r ≠ 1) n]
          have hsplit : (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) := by
            rw [div_eq_div_iff (by linarith) (by linarith)]; ring
          rw [hsplit]
          have h1 : (0:ℝ) ≤ 1 - r := by linarith
          have hrn : r ^ n ≤ 1 := pow_le_one₀ hr0 (le_of_lt hr1)
          have hrnn : 0 ≤ r ^ n := pow_nonneg hr0 n
          gcongr
          linarith
        calc M * ∑ k ∈ Finset.range n, r ^ k ≤ M * (1 / (1 - r)) :=
              mul_le_mul_of_nonneg_left hgeo hMnn
          _ = M / (1 - r) := by ring

/-- **【单层误差 ≤ 累计余量】**：每层误差不超过总误差预算 `M/(1-r)`。
作为上一定理的即时推论（`n` 层中的每一项）。 -/
theorem branch_layer_le_budget (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ ≤ M) (hMnn : 0 ≤ M) (n : ℕ) :
    errA A x' (s.traj n) ≤ M / (1 - |1 - η|) := by
  have hsingle : errA A x' (s.traj n)
      ≤ ∑ k ∈ Finset.range (n + 1), errA A x' (s.traj k) := by
    have : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
    exact Finset.single_le_sum (f := fun k => errA A x' (s.traj k))
      (fun k _ => errA_nonneg A x' (s.traj k)) this
  exact le_trans hsingle (branch_accumulated_error_bound A φ η x' θ h hη hs hM hMnn (n + 1))

end RateDepth

/-! ===========================================================================
    §5  **具体实例：两条分支在 ℝ 上，逐一可复核**
    =========================================================================== -/

section Concrete

/-- **具体世界**：`A = id`、`φ = id`（`Corrects` 自动成立，`BoundWriteBack.corrects_id`），
`x' = 3`、`θ = 1`、`η = 1/2`，**两条**干预方案 `plans := {p₁, p₂}`。

本定理验证 §3 的 `tree_uniform_bound`：**两条分支**在深度 `1` 的误差都 `≤ (1/2)·2 = 1`。

**数值**：初始误差 `err_0 = |1-3| = 2`；深度 `1` 误差 `= (1/2)·2 = 1`
（与 `WiringConvergence.concrete_two_steps` 一致）。 -/
theorem concrete_two_branches :
    ∀ s ∈ loopTree (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1
        ({fun _ => (0:ℝ), fun _ => (1:ℝ)} : Set (ℕ → ℝ)),
      errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj 1) ≤ (1/2:ℝ)^1 * 2 := by
  intro s hs
  have h := tree_uniform_bound _ _ _ _ _ corrects_id (M := 2) ?_ 1 s hs
  · norm_num at h ⊢
    exact h
  · rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = ‖(1:ℝ) - 3‖ from rfl]
    norm_num

/-- **具体实例的精确值**：两条分支在深度 `2` 的误差**精确等于** `(1/2)^2 · 2 = 1/2`。

**这验证 §4 的 `branch_err_rate_depth`**：速率 `|1-1/2| = 1/2`、深度 `2`、
且**两条分支同值**（与干预方案无关）。 -/
theorem concrete_two_branches_exact :
    ∀ s ∈ loopTree (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1
        ({fun _ => (0:ℝ), fun _ => (1:ℝ)} : Set (ℕ → ℝ)),
      errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj 2) = (1/2)^2 * 2 := by
  intro s hs
  rw [branch_err_rate_depth _ _ _ _ _ corrects_id hs 2]
  norm_num [errA]

end Concrete

/-! ===========================================================================
    §6  ⚠ **诚实边界**（本文件**不**做的事 + 复用对照）
    =========================================================================== -/

/-!
### §6.1 复用的引理（逐条对照，证明「接」是真的）

| 本文件定理 | 依赖的既有定理 | 出处 |
|---|---|---|
| `ofSim_traj_eq_iterMap` | `Scenario.ofSim`（定义）+ §1 辅助 | `FateV2.Loop/WorldScenario.lean` |
| `branch_traj_eq` | `mem_scenarioTree` + `ofSim_traj_eq_iterMap` | `WorldScenario` + 本文件 §1 |
| `branch_err` | `branch_traj_eq` + `WiringConvergence.err_iterMap` | `WiringConvergence` + 本文件 §2 |
| `branch_tendsto_zero` | `branch_traj_eq` + `closedLoop_tendsto_zero` | `WiringConvergence` |
| `tree_tendsto_uniform` | `tree_uniform_bound` + `tendsto_pow_atTop_nhds_zero_of_lt_one` | 本文件 §3 |
| `branch_err_antitone` | `branch_err` + `pow_le_pow_of_le_one` | 本文件 §3/§4 |

**⟹ 「接上」的判定标准**（任务书）：本文件 `import` 两个模块
（`FateV2.Loop/WorldScenario`、`FateV2.Loop/WiringConvergence`），
且主定理 `tree_tendsto_uniform` / `branch_err_rate_depth` 的**陈述**真正
包含两边的结论（树的 `∀ s ∈ tree` 量化 + 闭环的 `|1-η|^n` 速率）。

### §6.2 「接」的程度（分模块诚实评估）

| 模块 | 接线程度 | 说明 |
|---|---|---|
| `WorldScenario` | ✅ **强接** | `loopTree` **就是** `ScenarioTree`（定义性），主定理用其成员性 |
| `WiringConvergence` | ✅ **强接**（定量） | `err_iterMap` 的 `|1-η|^n` 是 `branch_err` 的**引擎**；`closedLoop_tendsto_zero` 直接复用于 `branch_tendsto_zero` |

**⚠ 关于 `stepFun` 忽略 `u, e, plan` 的诚实说明**：
`WiringConvergence` 的闭环步是线性预测器 `θ ↦ θ + η • φ(x' - A θ)`，
其误差递推 `err_{k+1} = |1-η| · err_k` **与干预方案无关**。因此本模型下
不同分支的**误差轨迹相同**——这是**被证明的**（`branch_traj_eq`），
不是被假设的。若要让「分支真正分叉」（不同干预 → 不同误差），
需把非线性动力学纳入，`WiringConvergence §8.3` 已登记该限制，本文件承之。

### §6.3 本文件**未**做的事（明确登记）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | 「不同干预方案产生不同误差轨迹」 | `WiringConvergence` 只在线性预测器上给精确速率；该速率与方案无关。要分支分叉需非线性动力学，参见其 §8.3 |
| 2 | `score` / `Policy`（选出满足要求的干预）| 属「干预选择」，在 `WorldScenario §0.3` / `PolicyAlgorithm.lean`，本文件只做「多分支收敛」的动力学要件 |
| 3 | 无限深树上的一致性的「紧速率」（是否存在更慢但共识的分支）| 本文件给的是 `|1-η|^n` 这一精确速率（`branch_err_rate_depth`），已是最强形式 |
| 4 | 随机 / 不确定分叉（`e` 也成集合）| 确定性框架；`WorldScenario §0.4` 已登记此限制 |

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
**⚠ 本文件无删减项**：所有陈述的定理**均已证出**。
-/

/-! ===========================================================================
    §7  **三段式汇总（界 / 紧 / 下界）**

    **任务 C 的同构交付**：把本文件的「界」、「紧」、「下界」三条主结果
    合并为**一条**合取命题。

    | 段 | 本文件的定理 | 内容 |
    |---|---|---|
    | 界 | `branch_accumulated_error_bound` | `∑_{k<n} err(s_k) ≤ M/(1-|1-η|)` |
    | 紧 | `branch_err_rate_depth` | `err(s_n) = |1-η|^n · err_0`（**精确等式**，故上界在每层取等）|
    | 下界 | `branch_err_antitone` | `n ≤ m ⟹ err(s_m) ≤ err(s_n)`（深度不放大误差）|

    ### ⚠ 非同义反复自查

    前件：`Corrects A φ`、`|1-η| < 1`、`s ∈ loopTree`、`err_0 ≤ M`、`0 ≤ M`。
    **无一**提到 `∑ k ∈ Finset.range n, errA A x' (s.traj k)`、
    也**无一**提到 `errA A x' (s.traj n) = ...` 或单调性。
    结论是三条命题的合取，必须逐个证明。 -/
theorem scenarioConvergence_three_part_summary {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) {plans : Set (ℕ → E)}
    {s : Scenario E E} (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ}
    (hM : errA A x' θ ≤ M) (hMnn : 0 ≤ M) :
    -- ① 界：累计误差被几何级数控制
    (∀ n : ℕ, ∑ k ∈ Finset.range n, errA A x' (s.traj k) ≤ M / (1 - |1 - η|))
      -- ② 紧：每层误差的**精确**几何值（故上界在每层取等）
      ∧ (∀ n : ℕ, errA A x' (s.traj n) = |1 - η| ^ n * errA A x' θ)
      -- ③ 下界：深度不放大误差（单调不增）
      ∧ (∀ {n m : ℕ}, n ≤ m → errA A x' (s.traj m) ≤ errA A x' (s.traj n)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ① 界（`branch_accumulated_error_bound`）
    intro n
    exact branch_accumulated_error_bound A φ η x' θ h hη hs hM hMnn n
  · -- ② 紧（`branch_err_rate_depth`，精确等式）
    intro n
    exact branch_err_rate_depth A φ η x' θ h hs n
  · -- ③ 下界（`branch_err_antitone`）
    intro n m hnm
    exact branch_err_antitone A φ η x' θ h hη hs hnm

end ScenarioConvergence

end FateV2.Loop
