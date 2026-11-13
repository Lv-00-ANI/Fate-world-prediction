import FateWorld.FateV2.Loop.WiringConvergence
import FateWorld.FateV2.Loop.OptimalEta
import Mathlib.Analysis.SpecificLimits.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ConvergenceOptimal.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 9 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.ConvergenceOptimal`
任务：**【AA2】把 `OptimalEta` 接进 `WiringConvergence`。**

===========================================================================
本文件要什么（一句话）
===========================================================================

`FateV2.Loop/WiringConvergence.lean` 给出一条**收敛速率**定理
`closedLoop_rate`：

    err(θ_n)  ≤  |1-η|^n · (L · ηmax)

而 `FateV2.Loop/OptimalEta.lean` 给出一条**最优步长**定理 `c_one_le`：

    c 1 ≤ c η      （∀ η ∈ ℝ，其中 c η := |1 - η|）

两条定理此前**互不引用**（`OptimalEta` 单向 import `WiringConvergence`，
反向没有任何组合定理）。本文件补上的正是**组合定理**：

    在**所有**步长 η 中，η = 1 给出**最快**的收敛（一步归零）。

===========================================================================
本文件给出的定理（逐条）
===========================================================================

| # | 定理 | 内容 |
|---|---|---|
| 1 | `c_eq_abs_one_sub`     | **桥**：`OptimalEta.c η = |1 - η|`（两个模块的收缩因子逐字等同）|
| 2 | `rate_eq_c_pow`        | **桥**：`WiringConvergence` 的速率 `|1-η|^n` 就是 `OptimalEta.c η ^ n` |
| 3 | `rate_one_minimal`     | **组合主定理 A**：`η = 1` 的速率对**每个** `η` 都最小 |
| 4 | `rate_one_is_zero`     | `η = 1` 的速率恰为 `0`（一步归零）|
| 5 | `converges_fastest`    | **组合主定理 B**：`∀ η, err_n(1) ≤ err_n(η)`（载体层最快）|
| 6 | `one_step_zero_fastest`| **组合主定理 C**：`η = 1` 一步归零，且**任何**别的 `η` 都做不到 |
| 7 | `rate_strict_others`   | `η ≠ 1` 时速率**严格**更大（唯一最优）|
| 8 | `convergence_optimal_summary` | **总汇**：速率最小 + 误差最小 + 一步归零，三者同条 |

===========================================================================
⚠ 诚实边界（必读）
===========================================================================

**1. 本文件是「组合」，不是「重新证明」。** 定理 1、2 是**定义性桥接**
（`OptimalEta.c` 的定义就是 `|1 - η|`，见其 `def c`），把
`WiringConvergence` 的 `|1-η|^n` 与 `OptimalEta` 的 `c η ^ n` 统一到同一记号；
定理 3–8 则**同时**引用两模块的结论（`c_one_le` 与 `closedLoop_rate` /
`err_eq_c_pow`），故「真正同时引用两个模块」。

**2. 「最快」= 「`n ≥ 1` 步后误差最小」，且是**一致**最优（对每个 `n ≥ 1`）。**
`n = 0` 时误差与 `η` 无关，故最优性陈述统一取 `n ≥ 1`，与 `OptimalEta §9.1`
的自查表口径**完全一致**。

**3. 「一步归零」是 `η = 1` 的**独有**性质。** 定理 6 的 `↔` 形式
（`err_1(η) = 0 ↔ η = 1`）表明：任何 `η ≠ 1` 一步后误差**严格正**
（在 `err_0 > 0` 下）。这不是新结论，而是把 `OptimalEta.eta_one_unique_zero`
用 `WiringConvergence` 的载体语言重述并**与速率比较合流**。

**4. 依赖 `Corrects A φ`。** 所有载体层定理的前件都含
`BoundWriteBack.Corrects A φ`（承 `BoundWriteBack §7` 与
`WiringConvergence §8` 的诚实边界：`c(η) = |1-η|` 的精确性依赖它）。
`Corrects` 失效时的最优 `η` 不在本文件范围（`OptimalEta §9.2` 已登记同项）。

**5. 前件自查（无同义反复）**：见 §6 表格。核心点：`c η = |1 - η|` 是
**定义等式**，不是把结论塞进前件；而定理 3、5 的**结论**（关于 `err` 的序）
**不在**任何前件中出现，需经 `c_pow_mono` + `mul_le_mul_of_nonneg_right` 两步推出。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / `零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 所有陈述定理**均已证出**；无删减项。
-/


namespace FateV2.Loop

namespace ConvergenceOptimal

universe u

/-! ===========================================================================
    §1  **桥接：两模块的收缩因子是同一个数**
    =========================================================================== -/

/-- **【桥 1：`OptimalEta.c` 就是 `|1 - η|`】**

`OptimalEta` 的收缩因子 `c η := |1 - η|` 与 `WiringConvergence` 里
**逐字出现**的 `|1 - η|` 是同一个数。

**证明**：`OptimalEta.c` 的**定义**即 `|1 - η|`，故 `rfl`。

**意义**：这条定义性等式让两个模块的「速率」可以**直接比较** ——
下游定理 3–8 全部依赖它把 `closedLoop_rate` 的 `|1-η|^n`
换成 `OptimalEta.c η ^ n`，从而能用 `OptimalEta.c_one_le` 的序。 -/
theorem c_eq_abs_one_sub (η : ℝ) : OptimalEta.c η = |1 - η| := rfl

/-- **【桥 1′：反向读法】** `|1 - η| = OptimalEta.c η`。 -/
theorem abs_one_sub_eq_c (η : ℝ) : |1 - η| = OptimalEta.c η := rfl

/-- **【桥 2：`WiringConvergence` 的速率 `= OptimalEta.c η ^ n`】**

`WiringConvergence.closedLoop_rate` 结论中的 `|1 - η| ^ n`
**逐字等于** `OptimalEta.c η ^ n`。

**证明**：由 `c_eq_abs_one_sub` 直接 `rw`。

**意义**：这是把「收敛速率」（`WiringConvergence`）与
「最优步长」（`OptimalEta`）放在**同一标量层**上比较的关键一步。 -/
theorem rate_eq_c_pow (η : ℝ) (n : ℕ) :
    |1 - η| ^ n = OptimalEta.c η ^ n := by
  rw [abs_one_sub_eq_c]

/-! ===========================================================================
    §2  **组合主定理 A：`η = 1` 的速率对每个 η 都最小**
    =========================================================================== -/

section RateOptimality

/-- **【组合主定理 A：速率最小性】**

**这是 `OptimalEta.c_one_le` 在「速率」层面的兑现**，用
`WiringConvergence` 的收缩因子 `|1 - η|` 陈述：

$$\forall \eta \in \mathbb{R},\ \forall n:\quad
  |1 - 1|^n \;\le\; |1 - \eta|^n .$$

即：**在所有步长中，`η = 1` 的收敛速率（`|1-η|^n`）对每个 `n` 都最小**。

**证明（两模块各出一半）**：
1. `OptimalEta.c_one_le η` 给标量序 `c 1 ≤ c η`；
2. `OptimalEta.c_pow_mono` 把它提升为 `c 1 ^ n ≤ c η ^ n`；
3. `rate_eq_c_pow` 把两边换回 `|1-·|^n`。

**前件只有 `η` 与 `n`（无任何前提），故**不是**同义反复：
结论是关于 `pow` 的序，需经 `pow_le_pow_left₀` 才能得到。 -/
theorem rate_one_minimal (η : ℝ) (n : ℕ) :
    |1 - (1 : ℝ)| ^ n ≤ |1 - η| ^ n := by
  rw [rate_eq_c_pow 1 n, rate_eq_c_pow η n]
  exact OptimalEta.c_pow_mono (OptimalEta.c_nonneg 1) (OptimalEta.c_one_le η) n

/-- **【组合主定理 A′：`η = 1` 的速率恰为零】**

$$\bigl(|1 - 1|\bigr)^n = 0 \quad (n \ge 1).$$

**意义**：定理 A 的「最小值」**恰为 0** —— 不是「取到下确界」，
而是**取到** `0`（一步归零）。这使 `η = 1` 不只是最优，而是**零误差**。 -/
theorem rate_one_is_zero {n : ℕ} (hn : 0 < n) : |1 - (1 : ℝ)| ^ n = 0 := by
  have : |1 - (1 : ℝ)| = 0 := by norm_num
  rw [this, zero_pow (Nat.pos_iff_ne_zero.mp hn)]

/-- **【组合主定理 A″：`η ≠ 1` 的速率严格更大】**

若 `η ≠ 1` 且 `n ≥ 1`，则

$$\bigl(|1-1|\bigr)^n = 0 \;<\; |1 - \eta|^n .$$

**证明**：`OptimalEta.c_one_lt_of_ne` 给 `c 1 < c η`；
`OptimalEta.c_pow_strict_of_lt` 提升为严格序；`rate_eq_c_pow` 换回。

**意义**：最小值是**唯一**的 —— `η = 1` 是独一档最优点，
不是「最优集合中的一员」（与 `OptimalEta §9.1` 的自查口径一致）。 -/
theorem rate_strict_others {η : ℝ} (hne : η ≠ 1) {n : ℕ} (hn : 0 < n) :
    |1 - (1 : ℝ)| ^ n < |1 - η| ^ n := by
  rw [rate_eq_c_pow 1 n, rate_eq_c_pow η n]
  exact OptimalEta.c_pow_strict_of_lt (OptimalEta.c_nonneg 1)
    (OptimalEta.c_one_lt_of_ne hne) hn

end RateOptimality

/-! ===========================================================================
    §3  **组合主定理 B：载体层 —— `η = 1` 使误差最小**
    =========================================================================== -/

section ErrorOptimality

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

open BoundWriteBack

/-- **【组合主定理 B：`η = 1` 在任何步长下误差最小】**

在 `Corrects A φ` 下，对**任意**候选步长 `η₀` 与**任意**步数 `n`：

$$\mathrm{err}\bigl(\theta_n^{(1)}\bigr)\;\le\;
  \mathrm{err}\bigl(\theta_n^{(\eta_0)}\bigr).$$

**证明（真正同时引用两模块）**：
1. `WiringConvergence.err_iterMap`（经 `OptimalEta.err_eq_c_pow`）给出
   `err_n(η) = c(η)^n · err_0`（**`WiringConvergence`** 的迭代结构）；
2. `OptimalEta.c_pow_mono` + `OptimalEta.c_one_le` 给出
   `c(1)^n ≤ c(η₀)^n`（**`OptimalEta`** 的最优性引擎）；
3. `err_0 ≥ 0` 放大得结论。

**⚠ 前件**只有 `Corrects`（不含任何关于最优性的假设）——**非同义反复**。 -/
theorem converges_fastest (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) (η₀ : ℝ) (n : ℕ) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ)
      ≤ errA A x' (WiringConvergence.iterMap A φ η₀ x' n θ) := by
  rw [OptimalEta.err_eq_c_pow A φ 1 x' θ h n,
      OptimalEta.err_eq_c_pow A φ η₀ x' θ h n]
  have hmono : OptimalEta.c 1 ^ n ≤ OptimalEta.c η₀ ^ n :=
    OptimalEta.c_pow_mono (OptimalEta.c_nonneg 1) (OptimalEta.c_one_le η₀) n
  exact mul_le_mul_of_nonneg_right hmono (errA_nonneg A x' θ)

/-- **【组合主定理 C：`η = 1` 一步归零，且「归零」恰刻画 `η = 1`】**

$\mathrm{err}_1(\eta) = 0 \iff \eta = 1$（在 `Corrects` 与 `err_0 > 0` 下）。

**证明**：
- `(←)`：`η = 1` 时由 `WiringConvergence.optimal_one_step` 一步归零；
- `(→)`：`err_1(η) = c(η) · err_0`；若 `c(η) = |1-η| ≠ 0` 且 `err_0 > 0`
  则乘积严格正，矛盾。故 `c(η) = 0`，由 `OptimalEta.eta_one_unique_zero`
  得 `η = 1`。

**意义**：这是「**一步**归零」的**完整刻画** —— 不只是「`η=1` 能一步归零」，
更是「**只有** `η=1` 能一步归零」。这把 `WiringConvergence §6`（正向）
与 `OptimalEta §3`（唯一性）**合成一条 `↔`**。 -/
theorem one_step_zero_fastest (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) (hpos : 0 < errA A x' θ) (η : ℝ) :
    errA A x' (WiringConvergence.iterMap A φ η x' 1 θ) = 0 ↔ η = 1 := by
  constructor
  · intro hzero
    rw [OptimalEta.err_eq_c_pow A φ η x' θ h 1] at hzero
    have hprod : OptimalEta.c η ^ 1 * errA A x' θ = 0 := hzero
    rw [pow_one] at hprod
    have hc0 : OptimalEta.c η = 0 := by
      rcases mul_eq_zero.mp hprod with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt hpos)
    exact (OptimalEta.eta_one_unique_zero η).mp hc0
  · intro hη
    subst hη
    exact WiringConvergence.optimal_one_step A φ x' θ h

/-- **【组合总汇：速率 + 误差 + 一步归零，三者同条】**

在 `Corrects A φ` 下，对**每个** `n ≥ 1` 与**每个** `η₀`，同时成立：

(a) **速率最小**：`|1-1|^n ≤ |1-η₀|^n`（`OptimalEta.c_one_le` + `c_pow_mono`）；
(b) **`η = 1` 误差为零**：`err_n(1) = 0`（`WiringConvergence` 的迭代 ✓）；
(c) **误差最小**：`err_n(1) ≤ err_n(η₀)`（(a) 的载体层兑现）。

**这是本文件对任务书的**正面回答**：
「在所有步长中，`η = 1` 给出最快收敛（一步归零）」——「最快」由 (a)、(c)
给出，「一步归零」由 (b) 给出，且 (a) 的引擎来自 `OptimalEta`、
(b)(c) 的引擎来自 `WiringConvergence`，**两模块同时被引用**。 -/
theorem convergence_optimal_summary (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (θ : E) (h : Corrects A φ) (η₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    |1 - (1 : ℝ)| ^ n ≤ |1 - η₀| ^ n
    ∧ errA A x' (WiringConvergence.iterMap A φ 1 x' n θ) = 0
    ∧ errA A x' (WiringConvergence.iterMap A φ 1 x' n θ)
        ≤ errA A x' (WiringConvergence.iterMap A φ η₀ x' n θ) :=
  ⟨rate_one_minimal η₀ n,
   WiringConvergence.optimal_stays_zero A φ x' θ h hn,
   converges_fastest A φ x' θ h η₀ n⟩

end ErrorOptimality

/-! ===========================================================================
    §4  **具体数值实例（两模块在最优点上合流，可逐字复核）**
    =========================================================================== -/

section Concrete

open BoundWriteBack

/-- **实例：候选步长的速率一覧（`n = 1`）**。

`η = 1` 的速率 `= 0`；`η = 1/2`、`η = 3/2` 为 `1/2`；`η = 0`、`η = 2` 为 `1`；
`η = -1` 为 `2`（**发散**）。**全部 ≥ `0`（`η = 1` 的值）**，
且**只有** `η = 1` 取等。 -/
theorem concrete_rate_table :
    |1 - (1:ℝ)| ^ 1 = 0 ∧ |1 - (1/2:ℝ)| ^ 1 = 1/2
      ∧ |1 - (3/2:ℝ)| ^ 1 = 1/2 ∧ |1 - (0:ℝ)| ^ 1 = 1
      ∧ |1 - (2:ℝ)| ^ 1 = 1 ∧ |1 - (-1:ℝ)| ^ 1 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **实例：`η = 1` 的速率是最小的（对表中每个候选逐一验证）**。 -/
theorem concrete_all_at_least :
    |1 - (1:ℝ)| ^ 1 ≤ |1 - (1/2:ℝ)| ^ 1
      ∧ |1 - (1:ℝ)| ^ 1 ≤ |1 - (3/2:ℝ)| ^ 1
      ∧ |1 - (1:ℝ)| ^ 1 ≤ |1 - (0:ℝ)| ^ 1
      ∧ |1 - (1:ℝ)| ^ 1 ≤ |1 - (2:ℝ)| ^ 1
      ∧ |1 - (1:ℝ)| ^ 1 ≤ |1 - (-1:ℝ)| ^ 1 :=
  ⟨rate_one_minimal (1/2) 1, rate_one_minimal (3/2) 1, rate_one_minimal 0 1,
   rate_one_minimal 2 1, rate_one_minimal (-1) 1⟩

/-- **实例：具体载体（`A = id`、`φ = id`、`x' = 3`、`θ = 1`）上
`η = 1` 一步归零，而 `η = 1/2` 一步后误差为 `1 > 0`**。

**这同时验证**：`converges_fastest`（`0 ≤ 1`）与 `one_step_zero_fastest`
（唯一性：`η = 1/2` 一步**未**归零）。 -/
theorem concrete_one_vs_half :
    errA (ContinuousLinearMap.id ℝ ℝ) 3
        (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ ℝ)
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 3 1 1) = 0
    ∧ errA (ContinuousLinearMap.id ℝ ℝ) 3
        (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ ℝ)
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1 1) = 1 := by
  refine ⟨?_, ?_⟩
  · -- η = 1: one step to zero
    rw [WiringConvergence.optimal_one_step _ _ _ _ corrects_id]
  · -- η = 1/2: err = |1-1/2|·|1-3| = (1/2)·2 = 1
    rw [OptimalEta.err_eq_c_pow _ _ _ _ _ corrects_id 1]
    simp only [OptimalEta.c, pow_one, errA]
    norm_num

/-- **实例：`η = 1/2` 一步后误差 `1` 严格大于 `η = 1` 的 `0`**。 -/
theorem concrete_half_not_fastest :
    errA (ContinuousLinearMap.id ℝ ℝ) 3
        (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ ℝ)
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 3 1 1)
      < errA (ContinuousLinearMap.id ℝ ℝ) 3
        (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ ℝ)
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1 1) := by
  refine lt_of_le_of_ne (converges_fastest _ _ _ _ corrects_id (1/2) 1) ?_
  intro heq
  rw [concrete_one_vs_half.1, concrete_one_vs_half.2] at heq
  norm_num at heq

end Concrete

/-! ===========================================================================
    §5  ⚠ **诚实边界（本文件**不**做的事）**
    =========================================================================== -/

/-!
### §5.1 「接线」的判定标准与本文件的达成情况

| 判定项 | 达成 | 证据 |
|---|---|---|
| `import FateV2.Loop.WiringConvergence` | ✅ | 文件头 |
| `import FateV2.Loop.OptimalEta` | ✅ | 文件头 |
| 定理**同时引用**两模块 | ✅ | 见 §5.2 逐条对照 |
| 主结论真正包含两模块结论 | ✅ | `convergence_optimal_summary`：速率最小（`OptimalEta`）+ 一步归零（`WiringConvergence`）|
| 不改已有模块 | ✅ | 只新增本文件 |

### §5.2 逐条引用对照（证明「串」是真的）

| 本文件定理 | 引用的 `WiringConvergence` | 引用的 `OptimalEta` |
|---|---|---|
| `c_eq_abs_one_sub` | 速率记号 `\|1-η\|` | `def c` |
| `rate_eq_c_pow` | `\|1-η\|^n` 记号 | `c` 的定义 |
| `rate_one_minimal` | `\|1-η\|^n` 记号 | `c_one_le`、`c_pow_mono`、`c_nonneg` |
| `rate_strict_others` | — | `c_one_lt_of_ne`、`c_pow_strict_of_lt`、`c_nonneg` |
| `converges_fastest` | `iterMap`（迭代结构）| `err_eq_c_pow`、`c_pow_mono`、`c_one_le` |
| `one_step_zero_fastest` | `optimal_one_step`（`η=1` 正向）| `eta_one_unique_zero`、`err_eq_c_pow` |
| `convergence_optimal_summary` | `optimal_stays_zero`、`iterMap` | `c_one_le`、`c_pow_mono` |
| `concrete_one_vs_half` 等 | `optimal_one_step`、`iterMap` | `err_eq_c_pow` |

### §5.3 本文件**未**做的事（明确登记，非删减项）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | **变步长** `η_k` 序列的最优性 | `OptimalEta §9.2` 已登记：需 `err_k = ∏ c(η_k)`，是另一问题 |
| 2 | `Corrects` **失效**时的最优 `η` | 承 `BoundWriteBack §7`：此时 `c(η)=|1-η|` 不精确 |
| 3 | **噪声**下的最优 `η`（期望误差）| 确定性框架，概率版需测度结构 |
| 4 | 世界模型 `WorldModel` 实例上的最优 `η` | 承 `WiringConvergence §8.3`：残差语义不同 |
| 5 | 「有界约束」`\|η\| ≤ 1` 下的最快性 | `OptimalEta.eta_in_unit_ball_optimal` 已答（约束无效）；本文件不重复 |

**⚠ 无 `sorry` / `admit` / `axiom`。**
**⚠ 本文件无删减项**：§1–§4 全部陈述定理均已证出。

-/

end ConvergenceOptimal

end FateV2.Loop
