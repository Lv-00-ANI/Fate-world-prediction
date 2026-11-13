/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ScenarioSharpForTree`
任务：**【C】为 `tree_uniform_bound` 单独补「紧」与「下界」**。

===========================================================================
为什么要新建本文件（任务 C 的判定结果：情形 (b)）
===========================================================================

规划说 `tree_uniform_bound` 的「有界、紧性与下界」中，有界已给、紧性与下界缺。
核实结果：

- `Fate/ScenarioConvergence.lean:329` 的 `branch_accumulated_error_bound` 是**求和界**
  `∑_{k<n} err(s_k) ≤ M/(1-r)`；`Fate/ScenarioSharp` / `Fate/ScenarioSharpWiring`
  补的全是**这条求和界**的紧性与下界（`scenario_depth_lower_bound` 等）。
- `tree_uniform_bound`（`:208`）是**另一条界**：**逐深度、关于整棵树一致**的界
  `err(s_n) ≤ |1-η|^n · M`。
- 用两种 grep 模式（`tree_uniform_bound`、`tree_uniform\|uniform_bound`）核对
  `ScenarioSharp.lean` 与 `ScenarioSharpWiring.lean`：**零命中**，两文件不引用
  `tree_uniform_bound`，也不证明它的任何紧性/下界。

**⟹ 情形 (b)**：`ScenarioSharp` 针对的是**别的界**（求和界），
`tree_uniform_bound`（逐深度界）的紧性与下界确实**未补**。本文件单独补齐。

===========================================================================
本文件补什么（三条，全部证明，零 `sorry`）
===========================================================================

`tree_uniform_bound` 给 `err(s_n) ≤ |1-η|^n · M`（`M` 是 `err_0` 的上界，`∀ s ∈ 树`）。

| # | 定理 | 形态 | 内容 |
|---|---|---|---|
| 1 | `tree_bound_exact` | **精确式** | 取 `M = err_0` 时 `err(s_n) = |1-η|^n · M` **恰为等号**：界在最优常数上无松弛 |
| 2 | `tree_bound_attained` | **可达到性（紧）** | 逐深度上确界**恰为** `|1-η|^n·M` 且被**每条分支同时取到** |
| 3 | `tree_bound_not_improvable` | **下界（不可改进）** | 任何对**全树**成立的逐深度常数界 `B` 都必须 `≥ |1-η|^n·M` |

===========================================================================
⚠ 诚实边界（必读，逐项对照，防止同义反复）
===========================================================================

**1. 前件不含结论，不是同义反复。**
- `tree_bound_exact` 的前件只有：`Corrects A φ`、`err_0 = M`、`s ∈ loopTree`。
  `err_0 = M` 是**关于初始状态**的前提（把 `tree_uniform_bound` 里
  `err_0 ≤ M` 的松弛去掉、钉成等号），**不含**任何关于 `err(s_n)` 的语句。
  结论是深度 `n` 的**逐深度误差等式**——与前提是不同命题。
- `tree_bound_not_improvable` 的前件只有：`Corrects A φ`、`err_0 = M`、
  `plans` **非空**（保证存在分支可供量化）、`B` 满足「对全树逐深度不超过 `B`」。
  `B` 的这个性质是**候选界的定义**（"一个对全树成立的界"），
  **不是**结论 `|1-η|^n·M ≤ B`；结论是对 `B` 的**下界约束**。
  这正是「不可改进」的精确含义：任何可行的均匀常数都压不到 `|1-η|^n·M` 以下。

**2. 为何 `tree_bound_exact` 需要 `err_0 = M` 才能谈「紧」。**
`tree_uniform_bound` 中 `M` 只是 `err_0` 的**上界**；若 `err_0 < M`，
真实误差 `< |1-η|^n·M`，界有松弛，「取到」无意义。
故「紧」的正确陈述是：**当 `M` 取最小值 `err_0` 时**，逐深度误差**恰等于**该界。
这与 `ScenarioSharp` 处理求和界时釘 `err_0 = M` 的读法**一致**，不是偷换。

**3. 与 `ScenarioSharp` 的关系：互补，不相交。**
- `ScenarioSharp`：**求和** `∑_{k<n} err(s_k)` 的上界 / 下界 / 极限。
- 本文件：**逐深度** `err(s_n)` 的上界（既有 `:208`）/ 等号 / 逐深度不可改进。
二者的界分别是 `M/(1-r)` 与 `|1-η|^n·M`，**不同对象**，互不蕴含。
本文件**不修改**任何已有模块，只 `import`。

**4. 本文件不做的：**
- 不声称 `err_0 < M` 时取到等号（那时只有 `<`，见边界 2）。
- 不把逐深度紧性冒称求和紧性（那是 `ScenarioSharp` 的事）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
-/

import FateWorld.Legacy.ScenarioConvergence
import Mathlib.Analysis.SpecificLimits.Basic

namespace Fate

namespace ScenarioSharpForTree

open BoundWriteBack Fate.ScenarioConvergence
open Fate.WorldScenario

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §1  ⭐⭐⭐ **精确式：最优常数下逐深度界取等号**
    =========================================================================== -/

/-- ⭐⭐⭐ **【逐深度精确式】取 `M = err_0` 时 `tree_uniform_bound` 的界取等号。**

在 `err_0 = M`（初始误差**恰为** `M`）、`Corrects A φ` 下，树上**任意**分支在深度 `n`
的误差**精确等于** `|1-η|^n · M`：

$$\mathrm{err}(s_n) \;=\; |1-\eta|^{n}\,M .$$

**⭐ 这是把 `tree_uniform_bound`（`:208`，`≤`）算成等号**：
`:208` 只说 `err(s_n) ≤ |1-η|^n·M`（且 `M` 仅需 `≥ err_0`）；
本条在最优常数 `M = err_0` 下给出**闭式等号**，故界在最优常数上**无任何松弛**。

**证明**：`branch_err` 给 `err(s_n) = |1-η|^n · err_0`，代入 `err_0 = M` 即得。 -/
theorem tree_bound_exact (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) {plans : Set (ℕ → E)} {s : Scenario E E}
    (hs : s ∈ loopTree A φ η x' θ plans) {M : ℝ} (hM : errA A x' θ = M) (n : ℕ) :
    errA A x' (s.traj n) = |1 - η| ^ n * M := by
  rw [branch_err A φ η x' θ h hs n, hM]

/-! ===========================================================================
    §2  ⭐⭐⭐⭐ **可达到性（紧）：逐深度上确界恰为 `|1-η|^n·M`，且被每条分支取到**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【紧：逐深度界是全树逐深度的上确界，且被每条分支同时取到】**

在 `err_0 = M`、`plans` 非空（存在分支）下，对每个深度 `n`：

1. **仍有界**：`∀ s ∈ 树, err(s_n) ≤ |1-η|^n·M`（复用 `tree_uniform_bound`）；
2. **可取到**：存在分支使 `err(s_n) = |1-η|^n·M`（事实上**每条**分支都取到）；
3. **是上确界**：故 `|1-η|^n·M` 是 `{err(s_n) : s ∈ 树}` 的**上确界**。

**⭐ 这是「紧」的正面内容**：`tree_uniform_bound` 的界不是松的估计，
而是**精确最大值**，无法缩小。

**证明**：(1) 即 `tree_uniform_bound`（取 `M = err_0`，因 `err_0 ≤ M` 自反成立）；
(2) 由 `tree_bound_exact`，每条分支都取等号；(3) 由 (1)(2) 用 `le_antisymm`
（上界 + 达到）直接得 `sSup` 的刻画，见 `tree_bound_sSup_eq`。 -/
theorem tree_bound_attained (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) {plans : Set (ℕ → E)} {M : ℝ} (hM : errA A x' θ = M) (n : ℕ) :
    (∀ s ∈ loopTree A φ η x' θ plans, errA A x' (s.traj n) ≤ |1 - η| ^ n * M)
      ∧ (∀ s ∈ loopTree A φ η x' θ plans, errA A x' (s.traj n) = |1 - η| ^ n * M) := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · -- 有界：复用已有 `tree_uniform_bound`（此处 `err_0 ≤ M` 由 `hM` 直接得）
    exact tree_uniform_bound A φ η x' θ h (le_of_eq hM) n s hs
  · -- 取到：精确式（每条分支都取到）
    exact tree_bound_exact A φ η x' θ h hs hM n

/-- ⭐⭐⭐⭐ **【紧的定量版：逐深度上确界 = `|1-η|^n·M`】**

在 `err_0 = M`、`plans` 非空下，集合 `{err(s_n) : s ∈ 树}` 的**上确界**
恰为 `|1-η|^n·M`：

$$\sup_{s\in \mathrm{loopTree}} \mathrm{err}(s_n) \;=\; |1-\eta|^{n}\,M .$$

**⭐ 这正是「界即上确界」**：`tree_uniform_bound` 的常数 `|1-η|^n·M`
**既**是全树逐深度上界（`:208`）**又**是上确界（本条），故**不可改进**。

**证明**：`sSup` 的 `le_antisymm`：
- `≤`：每条分支值 `≤ |1-η|^n·M`（`tree_uniform_bound`）⟹ 上确界 `≤` 它；
- `≥`：存在分支值 `= |1-η|^n·M`（`plans` 非空 + `tree_bound_exact`）⟹ 上确界 `≥` 它。 -/
theorem tree_bound_sSup_eq (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) {plans : Set (ℕ → E)} {M : ℝ} (hM : errA A x' θ = M) (n : ℕ)
    {p₀ : ℕ → E} (hp₀ : p₀ ∈ plans) :
    sSup ((fun s : Scenario E E => errA A x' (s.traj n)) '' loopTree A φ η x' θ plans)
      = |1 - η| ^ n * M := by
  -- 存在一个具体分支：由 `plans` 非空 + `Scenario.ofSim`
  classical
  set T := loopTree A φ η x' θ plans with hT
  -- 具体分支：`plans` 非空 ⟹ 用 `ofSim` 造出成员
  have hmem₀ : (Scenario.ofSim (stepFun A φ η x') θ (fun _ => 0) (fun _ => 0) p₀) ∈ T :=
    mem_loopTree.mpr ⟨hp₀, rfl⟩
  have hnonempty : (T).Nonempty := ⟨_, hmem₀⟩
  have hbound : ∀ y ∈ (fun s : Scenario E E => errA A x' (s.traj n)) '' T,
      y ≤ |1 - η| ^ n * M := by
    rintro y ⟨s, hs, rfl⟩
    exact tree_uniform_bound A φ η x' θ h (le_of_eq hM) n s hs
  -- 有一个元素恰好取到该值
  obtain ⟨s₁, hs₁⟩ := hnonempty
  have hmem : errA A x' (s₁.traj n)
      ∈ (fun s : Scenario E E => errA A x' (s.traj n)) '' T := ⟨s₁, hs₁, rfl⟩
  have hval : errA A x' (s₁.traj n) = |1 - η| ^ n * M :=
    tree_bound_exact A φ η x' θ h hs₁ hM n
  -- 非空有界集的上确界刻画
  have hbdd : BddAbove ((fun s : Scenario E E => errA A x' (s.traj n)) '' T) :=
    ⟨_, fun y hy => hbound y hy⟩
  refine le_antisymm (csSup_le ⟨_, hmem⟩ (fun y hy => hbound y hy)) ?_
  calc |1 - η| ^ n * M = errA A x' (s₁.traj n) := hval.symm
    _ ≤ sSup ((fun s : Scenario E E => errA A x' (s.traj n)) '' T) :=
        le_csSup hbdd hmem

/-! ===========================================================================
    §3  ⭐⭐⭐⭐ **下界（不可改进）：任何全树逐深度常数界都必须 ≥ 该值**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【下界：`tree_uniform_bound` 的常数对任何全树界都是下界】**

在 `err_0 = M`、`plans` 非空、`Corrects A φ` 下，
任何满足「对**全树每条**分支、深度 `n` 的误差都 `≤ B`」的常数 `B`，
都必须

$$|1-\eta|^{n}\,M \;\le\; B .$$

**⭐ 这是「不可改进」的精确陈述**：`B` 是**任意**一个全树逐深度上界
（`hB` 是"`B` 是一个界"的定义，**不是**结论）；结论是**任何这样的 `B` 都压不下去**，
故 `|1-η|^n·M` 是最优（最小）的可行常数，`tree_uniform_bound` 已取到最优。

**⚠ 非同义反复**：前件 `hB` 断言的是 `B` 的上界性（所有分支误差 `≤ B`），
结论断言的是 `|1-η|^n·M ≤ B`（常数间的大小）。二者是不同命题；
证明用"某条分支值恰为 `|1-η|^n·M`"（`tree_bound_exact`）从 `hB` 挤出结论。

**证明**：取一条分支 `s`，`tree_bound_exact` 给 `err(s_n) = |1-η|^n·M`；
`hB s hs` 给 `err(s_n) ≤ B`；两式传递即得。 -/
theorem tree_bound_not_improvable (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) {plans : Set (ℕ → E)} {M : ℝ} (hM : errA A x' θ = M) (n : ℕ)
    {B : ℝ}
    (hB : ∀ s ∈ loopTree A φ η x' θ plans, errA A x' (s.traj n) ≤ B)
    {p₀ : ℕ → E} (hp₀ : p₀ ∈ plans) :
    |1 - η| ^ n * M ≤ B := by
  -- 造一条具体分支并把两段接起来
  have hmem : (Scenario.ofSim (stepFun A φ η x') θ (fun _ => 0) (fun _ => 0) p₀)
      ∈ loopTree A φ η x' θ plans := mem_loopTree.mpr ⟨hp₀, rfl⟩
  have hexact : errA A x' ((Scenario.ofSim (stepFun A φ η x') θ (fun _ => 0) (fun _ => 0)
        p₀).traj n) = |1 - η| ^ n * M :=
    tree_bound_exact A φ η x' θ h hmem hM n
  calc |1 - η| ^ n * M
      = errA A x' ((Scenario.ofSim (stepFun A φ η x') θ (fun _ => 0) (fun _ => 0)
          p₀).traj n) := hexact.symm
    _ ≤ B := hB _ hmem

/-! ===========================================================================
    §4  ⭐ **具体实例：ℝ 上一族分支，逐深度界数值复核**
    =========================================================================== -/

section Concrete

/-- ⭐ **具体世界**：`A = id`、`φ = id`、`x' = 3`、`θ = 1`、`η = 1/2`。

**数值**：`M = err_0 = |3-1| = 2`、`|1-η| = 1/2`。
深度 `2` 的界 `= (1/2)^2 · 2 = 1/2`。本定理用 `tree_bound_exact` 验证
每条分支在深度 `2` 的误差**恰为** `1/2`（界取等号，无松弛）。 -/
theorem concrete_tree_bound_exact :
    ∀ s ∈ loopTree (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1
        ({fun _ => (0:ℝ), fun _ => (1:ℝ)} : Set (ℕ → ℝ)),
      errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj 2) = 1/2 := by
  intro s hs
  have hm : errA (ContinuousLinearMap.id ℝ ℝ) 3 (1 : ℝ) = 2 := by
    rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = ‖(1:ℝ) - 3‖ from rfl]
    norm_num
  rw [tree_bound_exact _ _ _ _ _ corrects_id hs hm 2]
  norm_num

/-- ⭐ **【下界的具体核对】** 同一世界，深度 `2`：任何全树界 `B` 都 `≥ 1/2`。
即 `tree_bound_not_improvable` 的实例化（`1/2 ≤ B`）。 -/
theorem concrete_tree_bound_not_improvable {B : ℝ}
    (hB : ∀ s ∈ loopTree (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        (1/2) 3 1 ({fun _ => (0:ℝ), fun _ => (1:ℝ)} : Set (ℕ → ℝ)),
      errA (ContinuousLinearMap.id ℝ ℝ) 3 (s.traj 2) ≤ B) :
    (1/2 : ℝ) ≤ B := by
  have hm : errA (ContinuousLinearMap.id ℝ ℝ) 3 (1 : ℝ) = (2:ℝ) := by
    rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = ‖(1:ℝ) - 3‖ from rfl]
    norm_num
  have h := tree_bound_not_improvable (ContinuousLinearMap.id ℝ ℝ)
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1 corrects_id hm 2 hB
    (p₀ := fun _ => (0:ℝ)) (by simp)
  -- h : |1 - 1/2|^2 * 2 ≤ B，规约到 1/2 ≤ B
  have hr : |1 - (1/2:ℝ)| = 1/2 := by norm_num
  rw [hr] at h
  norm_num at h
  linarith

end Concrete

/-! ===========================================================================
    §5  ⚠ **诚实边界汇总（本文件不做的 + 复用对照）**
    =========================================================================== -/

/-!
### §5.1 复用的引理（逐条对照）

| 本文件定理 | 依赖的既有定理 | 出处 |
|---|---|---|
| `tree_bound_exact` | `ScenarioConvergence.branch_err` | `ScenarioConvergence` |
| `tree_bound_attained` | `tree_uniform_bound`（有界）+ `tree_bound_exact`（取到） | `ScenarioConvergence` + 本文件 |
| `tree_bound_sSup_eq` | `tree_bound_attained` + `csSup_le` / `le_csSup` | 本文件 + Mathlib |
| `tree_bound_not_improvable` | `tree_bound_exact` | 本文件 |

### §5.2 本文件**不**做的事

1. **不**重造 `tree_uniform_bound`（`:208` 的上界）—— 本文件只补等号、上确界、下界。
2. **不**声称 `err_0 < M` 时取到等号 —— 那是只有 `<` 的情形（见文件头边界 2）。
3. **不**把逐深度紧性冒称序号求和紧性 —— 后者是 `Fate.ScenarioSharp` 的事，
   两文件互补、界不同（`|1-η|^n·M` vs `M/(1-r)`）、互不蕴含。

### §5.3 「紧」的正确读法（本文件结论）

对逐深度界 `err(s_n) ≤ |1-η|^n·M`：
- **最优常数**（`M = err_0`）：`err(s_n) = |1-η|^n·M` **恰取等号**（`tree_bound_exact`）。
- **上确界**：`sup_{s∈树} err(s_n) = |1-η|^n·M`（`tree_bound_sSup_eq`）。
- **不可改进**：任何全树逐深度界 `B` 都 `≥ |1-η|^n·M`（`tree_bound_not_improvable`）。
三者合起来即为该逐深度界的**紧性 + 下界**。
-/

end ScenarioSharpForTree

end Fate
