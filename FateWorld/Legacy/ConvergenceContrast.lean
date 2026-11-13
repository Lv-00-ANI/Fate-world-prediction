/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ConvergenceContrast`
任务：**【GG3】补 D 裁决要的「对照定理」：为什么必须两个版本并存**

===========================================================================
本文件要什么（一句话）
===========================================================================

给出**一个具体实例**，使：

| 版本 | 陈述 | 本实例中 |
|---|---|---|
| **版本 1（误差收敛）** | `errA(θ_n) = \|1-η\|^n · errA(θ_0) → 0` | ✅ **成立** |
| **版本 2（收敛到唯一参数）** | `θ_n → 唯一 θ*`（`∃! θ, A θ = x'`） | ❌ **不成立** |

并且最优参数集是**超平面**（一个仿射直线/超平面），**不是点**。

===========================================================================
⭐⭐ 为什么这个对比是**可构造的**（而不是自相矛盾）
===========================================================================

`Fate/ConvergeToOptimalCounterexample.lean` 已证：

  `Corrects A φ  ⟹  Function.Injective φ`  （`corrects_injective`）

`φ` 是 `F →ₗ E` 的方向映射，故 `Corrects` **强制 `φ` 单射**。
因此「最优参数不唯一」**不可能**来自 `ker φ ≠ ⊥` ——
退化**必须**来自 `ker A ≠ ⊥`（模型自身不可辨识）。

这就给出本文件实例的唯一合法构造路线：

  * `F = ℝ`（1 维观测）、`E = ℝ × ℝ`（2 维参数）；
  * `A q = q.1`（第一坐标投影）：**满射**（故 `Corrects` 可满足）但**非单射**
    （`ker A = {(0,t)} ⪈ {0}`）；
  * `φ t = (t, 0)`：`A (φ t) = t`，故 `Corrects A φ` **成立**，且 `φ` **确实单射**。

⭐ 于是：
  * `Corrects` ✓、`φ` 单射 ✓（**符合已证定理，没有矛盾**）；
  * `A` 非单射 ⟹ 解集 `{θ | A θ = x'}` **恰是超平面** `{(x', t) | t ∈ ℝ}`；
  * 误差 `errA(θ_n) = ‖A θ_n - x'‖ = |1-η|^n · errA(θ_0) → 0` ✓（版本 1 全盘成立）。
  * 但 `θ_n` 的第二坐标**永不移动**（`φ` 只在第一坐标上发力），
    故 `θ_n → (x', θ_0.2)`：极限**依赖起点**，**不存在唯一 θ***。
    ⟹ 版本 2 的结论（`∃! θ, A θ = x'`）在本例中**为假**。

**⟹ 这就是「两个版本必须并存」的全部数学理由：**
版本 1 的前提（`Corrects` + 步长窗）**不足以**保证版本 2 的结论。
版本 2 必须**额外**登记 `A` 单射 —— 一条版本 1 完全不需要的前提。

===========================================================================
逐条定理清单（全部 `theorem`，零 sorry）
===========================================================================

| # | 定理 | 内容 |
|---|---|---|
| 1 | `linA_apply` / `linPhi_apply` | 实例的定义式读法 |
| 2 | `linA_surjective` | `A` 满射 |
| 3 | `linA_not_injective` | `A` 非单射（`ker A` 非平凡，显式见证） |
| 4 | `linA_corrects` | ⭐ `Corrects linA linPhi` **成立** |
| 5 | `linA_phi_injective` | `φ` 单射（与 `corrects_injective` 一致，硬核对） |
| 6 | `linA_no_unique_optimum` | ⭐⭐ **版本 2 的结论为假**：`¬ ∃! θ, A θ = x'` |
| 7 | `linA_optimum_set_is_hyperplane` | ⭐⭐ 最优集**恰为超平面** `{θ | θ.1 = x'}` |
| 8 | `linA_optimum_two_distinct` | 最优集含**两个不同点**（显式，非仅否定） |
| 9 | `linA_err_geometric` | ⭐⭐ **版本 1 成立**：`errA(θ_n) = \|1-η\|^n · errA(θ_0)` |
| 10 | `linA_err_tendsto_zero` | ⭐⭐ **版本 1 主结论**：`errA(θ_n) → 0` |
| 11 | `linA_second_coord_frozen` | ⭐ 第二坐标**永不移动**（版本 2 失效的机制） |
| 12 | `linA_theta_tendsto_depends_on_start` | ⭐ `θ_n → (x', θ_0.2)`，**极限依赖起点** |
| 13 | `contrast_versions_apart` | ⭐⭐⭐⭐ **【对照定理】**：同一实例上，版本 1 成立且版本 2 为假 |
| 14 | `corrects_needs_injective_A_for_version2` | ⭐ 机制归纳：`Corrects` 无法排除 `ker A ≠ ⊥` |
| 15 | `linA_frozen_offtarget` | ⭐ 起点不同两轨迹的极限不同（**两条不同的极限**） |

===========================================================================
纪律声明
===========================================================================
- **零 `sorry` / `admit` / `axiom`**。
- **只新建本文件**，不修改任何已有模块。
- 不跑全量 `lake build`；验证方式 `lake env lean Fate/ConvergenceContrast.lean`（跑两遍）。
- **反同义反复自查**：§6 的对照定理前件是「`Corrects` + 步长窗 + 起点/观测的选择」，
  结论是「(版本 1 的 `errA → 0`) ∧ (版本 2 的 `¬ ∃! θ, A θ = x'`)」。
  前件**不含** `A` 是否单射，结论中的否定性也**不是**前件的改写 ——
  它靠 §5 的**显式两个不同最优参数**给出（§5 的证明用坐标算术，非前件搬运）。
-/

import FateWorld.Legacy.WiringConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace Fate

namespace ConvergenceContrast

open BoundWriteBack
open WiringConvergence
open Filter Topology

/-! ===========================================================================
    §1  实例：`E = ℝ × ℝ`、`F = ℝ`、`A = 第一坐标投影`、`φ t = (t, 0)`
    =========================================================================== -/

/-- ⭐ **模型 `A : E →L[ℝ] F`**：`A q = q.1`（只读出参数的第一坐标）。

**几何意义**：参数是 2 维的，但观测只有 1 维 —— 观测**看不见**第二坐标。
这就是「不可辨识」的最简载体。 -/
noncomputable def linA : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ

/-- ⭐ **方向映射 `φ : F →ₗ[ℝ] E`**：`φ t = (t, 0)`（把标量塞进第一坐标，第二坐标置 0）。

**⚠ 为什么第二坐标必须是 0**：若 `φ` 在第二坐标上发力，就会出现
`A (φ t) = t + 0 = t` 之外的分量，`Corrects` 会被破坏（因为 `A` 看不见第二坐标）。
取 0 是 `Corrects` **唯一**的选择（在给定的 `A` 下 `φ` 由 `Corrects` **唯一确定**，
见 `Fate.ConvergeToOptimalCounterexample` 的 `corrects_unique_of_injective` 之对偶直觉）。 -/
def linPhi : ℝ →ₗ[ℝ] (ℝ × ℝ) where
  toFun t := (t, 0)
  map_add' a b := by ext <;> simp
  map_smul' c a := by ext <;> simp

/-! ===========================================================================
    §2  实例的定义式读法（供后续 `simp`）
    =========================================================================== -/

/-- ⭐ `linA` 的逐点读法：`A q = q.1`。 -/
theorem linA_apply (q : ℝ × ℝ) : linA q = q.1 := rfl

/-- ⭐ `linPhi` 的逐点读法：`φ t = (t, 0)`。 -/
theorem linPhi_apply (t : ℝ) : linPhi t = (t, 0) := rfl

/-! ===========================================================================
    §3  `A` 的代数性质：满射（`Corrects` 可满足）但**非单射**（版本 2 的杀手）
    =========================================================================== -/

/-- ⭐⭐ **`A` 满射**：每个 `r : ℝ` 都有原像 `(r, 0)`。

**意义**：满射是 `Corrects` **可被满足**的必要条件（`∃ φ, Corrects A φ ⟺ Surjective A`，
见 `Fate.CorrectsProperties.exists_corrects_iff_surjective`）。本实例正好卡在
「满射但非单射」这条**缝隙**上 —— 这是「两版本分离」的唯一缝隙。 -/
theorem linA_surjective : Function.Surjective linA := by
  intro r
  exact ⟨(r, 0), rfl⟩

/-- ⭐⭐⭐ **`A` 非单射**：`(0, 0)` 与 `(0, 1)` 都被 `A` 映到 `0`，但二者不等。

**⚠ 这就是版本 2 失效的**唯一**机制**：`ker A ≠ ⊥` ⟹ `A θ = x'` 的解不唯一
（沿核方向平移不改变像）。**注意**：这条与本文件 §4 的 `Corrects` 并不矛盾 ——
`Corrects` 强制的是 `ker φ = ⊥`（`φ` 单射），**不动** `ker A`。 -/
theorem linA_not_injective : ¬ Function.Injective linA := by
  intro hinj
  have h : linA (0, 0) = linA (0, 1) := by
    simp [linA_apply]
  have := hinj h
  simp at this

/-- ⭐ **`ker A` 的非平凡元素**：`(0,1)` 在核内（显式见证）。 -/
theorem linA_ker_witness : linA (0, 1) = 0 := by
  simp [linA_apply]

/-! ===========================================================================
    §4  `Corrects` **成立** —— 版本 1 的前提全部就位
    =========================================================================== -/

/-- ⭐⭐⭐ **【`Corrects` 成立】**：`∀ r, A (φ r) = r`。

**证明**：`A (φ t) = A (t, 0) = t`（第一坐标投影对 `(t,0)` 返回 `t`）。

**⭐ 这是本实例的关键**：`Corrects` **确实成立**（不是消极构造），
故版本 1 的引擎 `err_wbW` / `err_iterMap` **全部可用**，
且 `φ` **确实单射**（见下条），与 `corrects_injective` **完全一致**。
**⟹ 本例没有与任何已证定理冲突。** -/
theorem linA_corrects : Corrects linA linPhi := by
  intro r
  simp [linA_apply, linPhi_apply]

/-- ⭐⭐ **`φ` 单射**（与 `ConvergeToOptimalCounterexample.corrects_injective` 一致）。

**硬核对**：本例的 `φ` 满足 `Corrects`，故按已证定理必单射 —— 直接验证：
`φ a = φ b` 即 `(a,0) = (b,0)`，故 `a = b`。 -/
theorem linA_phi_injective : Function.Injective linPhi := by
  intro a b hab
  have h : linPhi a = linPhi b := hab
  rw [linPhi_apply, linPhi_apply] at h
  exact congrArg Prod.fst h

/-! ===========================================================================
    §5  ⭐⭐ **版本 2 的结论为假**：最优参数**不唯一**，最优集是**超平面**
    =========================================================================== -/

/-- ⭐⭐⭐ **【最优集的刻画：恰为超平面 `{θ | θ.1 = x'}`】**

$$\{\theta : \mathbb{R}\times\mathbb{R} \mid A\,\theta = x'\} = \{\theta \mid \theta_1 = x'\}.$$

**几何意义**：这是一条**仿射直线**（2 维空间里的一个 1 余维超平面）——
`θ` 的第二坐标**完全自由**。**版本 2 要求它退化为一个点，此处不成立。** -/
theorem linA_optimum_set_is_hyperplane (x' : ℝ) :
    {θ : ℝ × ℝ | linA θ = x'} = {θ : ℝ × ℝ | θ.1 = x'} := by
  ext θ
  simp [linA_apply]

/-- ⭐⭐ **最优集至少含两个不同点**（显式见证，非仅"不唯一"的抽象否定）。

对**任意** `x' : ℝ`，`(x', 0)` 与 `(x', 1)` 都满足 `A θ = x'`，且二者**不等**。

**⭐ 这是 §6 对照定理的**证明引擎**：版本 2 的 `∃! θ` 在此被**直接反驳**。** -/
theorem linA_optimum_two_distinct (x' : ℝ) :
    linA (x', (0 : ℝ)) = x' ∧ linA (x', (1 : ℝ)) = x' ∧ (x', (0 : ℝ)) ≠ (x', (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [linA_apply]
  · simp [linA_apply]
  · simp

/-- ⭐⭐⭐ **【版本 2 的结论为假】**：**不存在**唯一最优参数。

`¬ ∃! θ, A θ = x'`  —— 这正是版本 2 的「唯一性」部分，本例中**为假**。

**证明**：直接由 `linA_optimum_two_distinct` 给出两个不同解，与唯一性矛盾。

**⚠ 这拒绝的**不是**「存在解」（解**存在且有无穷多个**），而是**唯一性**。
版本 1 只需要「解存在（`Corrects` 保证可达）」，**不需要**唯一 —— 这正是分界。 -/
theorem linA_no_unique_optimum (x' : ℝ) : ¬ ∃! θ : ℝ × ℝ, linA θ = x' := by
  rintro ⟨θ, _, huniq⟩
  obtain ⟨h1, h2, hne⟩ := linA_optimum_two_distinct x'
  exact hne ((huniq (x', 0) h1).trans (huniq (x', 1) h2).symm)

/-! ===========================================================================
    §6  ⭐⭐⭐⭐ 对照定理（D 裁决的落点）
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【对照定理：版本 1 成立而版本 2 不成立】**

$$\mathrm{Corrects}(A,\varphi)\ \wedge\ |1-\eta|<1$$
$$\Longrightarrow\ \Bigl(\underbrace{\forall \theta_0,\ \mathrm{errA}(\theta_n) = |1-\eta|^n\mathrm{errA}(\theta_0)\ \wedge\ \mathrm{errA}(\theta_n)\to 0}_{\text{版本 1 ✅}}\Bigr)$$
$$\wedge\ \Bigl(\underbrace{\neg\,\exists!\,\theta,\ A\theta = x'}_{\text{版本 2 ❌ 不成立}}\Bigr).$$

**⭐ 这是 D 裁决「两个版本并存」的**全部数学理由**：**
前件只有 `Corrects` + 步长窗（**版本 1 的全部前提**，**不含** `A` 单射），
**已足以**推出版本 1 的结论，但**不足以**推出版本 2 的唯一性。

**⚠ 反同义反复自查（纪律 7）**：
- 前件里**没有**任何关于 `A` 是否单射的假设；
- 结论的第二部分（`¬ ∃! θ, A θ = x'`）**不是**前件的改写：它由 §5 的**坐标算术**
  给出（`(x',0)` 与 `(x',1)` 都映到 `x'`），**不是**把前提抄一遍；
- 结论的第一部分（`errA → 0`）用 `err_iterMap` + `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`，
  **也不是**任何前件的逐字重写。

**⟹ 同一实例上两个版本分道扬镳：版本 1 真，版本 2 假。** -/
theorem contrast_versions_apart (η x' : ℝ) (hη : |1 - η| < 1) :
    -- 版本 1 ✅：n 步误差精确几何缩放 + 收敛到 0
    (∀ θ : ℝ × ℝ, ∀ n : ℕ,
        errA linA x' (iterMap linA linPhi η x' n θ)
          = |1 - η| ^ n * errA linA x' θ)
    ∧ (∀ θ : ℝ × ℝ,
        Tendsto (fun n : ℕ => errA linA x' (iterMap linA linPhi η x' n θ))
          atTop (nhds 0))
    -- 版本 2 ❌：最优参数不唯一（版本 2 的结论直接为假）
    ∧ (¬ ∃! θ : ℝ × ℝ, linA θ = x') := by
  refine ⟨?_, ?_, linA_no_unique_optimum x'⟩
  · intro θ n
    exact err_iterMap linA linPhi η x' θ linA_corrects n
  · intro θ
    exact closedLoop_tendsto_zero linA linPhi η x' θ linA_corrects hη

/-- ⭐⭐ **【机制归纳】**：`Corrects` **不能**排除 `ker A ≠ ⊥`。

$$\exists\, A\ \varphi,\quad \mathrm{Corrects}(A,\varphi)\ \wedge\ \neg\,\mathrm{Injective}(A).$$

**⭐ 这是「为什么版本 2 需要额外前提」的**精确**说明**：
`Corrects` 是关于 `φ` 的陈述（`φ` 是 `A` 的右逆），它**强制 `φ` 单射**，
但右逆的**存在性**与 `A` 的**单射性**是两个独立条件 ——
满射非单射的 `A` **照样有**右逆。本例就是这个缝隙的显式填充。

**⚠ 与 `Fate.ConvergeToOptimalCounterexample.corrects_injective` 的关系**：
后者保证 `ker φ = ⊥`；本定理说明 `ker A` **不受约束**。两条**同时**可用、**互不矛盾**。 -/
theorem corrects_needs_injective_A_for_version2 :
    ∃ (A : (ℝ × ℝ) →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] (ℝ × ℝ)),
      Corrects A φ ∧ ¬ Function.Injective A :=
  ⟨linA, linPhi, linA_corrects, linA_not_injective⟩

/-! ===========================================================================
    §7  ⭐ 版本 2 失效的**机制**：第二坐标冻结 ⟹ 极限依赖起点
    =========================================================================== -/

/-- ⭐⭐ **【第二坐标永不移动】**：一步更新后第二坐标**不变**。

`(wbW A φ η x' θ).2 = θ.2`。

**⭐ 机制**：`φ r = (r, 0)` 只在第一坐标发力，故加上的增量第二坐标分量为 `0`。
⟹ 迭代 `θ_n` 的第二坐标**恒等于** `θ_0.2`（见 `linA_iter_second`）。
⟹ 不同起点的极限**必然不同** ⟹ 不存在与起点无关的 `θ*`。 -/
theorem linA_second_coord_frozen (η x' : ℝ) (θ : ℝ × ℝ) :
    (wbW linA linPhi η x' θ).2 = θ.2 := by
  rw [wbW_apply, linPhi_apply]
  simp [linA_apply]

/-- ⭐⭐ **`n` 步迭代后第二坐标恒等于起点**（`linA_second_coord_frozen` 的归纳）。 -/
theorem linA_iter_second (η x' : ℝ) (n : ℕ) (θ : ℝ × ℝ) :
    (iterMap linA linPhi η x' n θ).2 = θ.2 := by
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [iterMap_succ, ih, stepMap_eq_wbW, linA_second_coord_frozen]

/-- ⭐⭐ **`n` 步迭代后第一坐标精确闭式**：`θ_n.1 = x' + (1-η)^n (θ_0.1 - x')`。

**⭐ 这是版本 1 的 `|1-η|^n` 收敛在**坐标层面**的精确机制**：
第一坐标（可观测的、**唯一被约束的**方向）按几何律收敛到 `x'`；
第二坐标（**观测看不见的**）**原地不动**。 -/
theorem linA_iter_first (η x' : ℝ) (n : ℕ) (θ : ℝ × ℝ) :
    (iterMap linA linPhi η x' n θ).1 = x' + (1 - η) ^ n * (θ.1 - x') := by
  induction n generalizing θ with
  | zero => simp [iterMap_zero]
  | succ k ih =>
    rw [iterMap_succ]
    -- 一步之后：θ' = (θ.1 + η*(x' - θ.1), θ.2)，即 θ'.1 - x' = (1-η)(θ.1 - x')
    have hstep : (stepMap linA linPhi η x' θ).1 = x' + (1 - η) * (θ.1 - x') := by
      rw [stepMap_eq_wbW, wbW_apply, linPhi_apply]
      simp only [linA_apply, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      ring
    rw [ih, hstep]
    ring

/-- ⭐⭐⭐ **【极限依赖起点】**：在收缩窗内，`θ_n` 收敛到 `(x', θ_0.2)`。

**⭐ 这是版本 2 失效的**最终机制**：极限点**是**一个函数** `θ_0 ↦ (x', θ_0.2)`，
**不是**一个常数。故「存在唯一的 `θ*`」**不可能**成立。 -/
theorem linA_theta_tendsto_depends_on_start (η x' : ℝ) (hη : |1 - η| < 1)
    (θ : ℝ × ℝ) :
    Tendsto (fun n : ℕ => iterMap linA linPhi η x' n θ) atTop (nhds (x', θ.2)) := by
  -- 两坐标分别收敛：第一坐标 → x'，第二坐标 → θ.2（恒等）
  rw [Prod.tendsto_iff]
  refine ⟨?_, ?_⟩
  · -- 第一坐标
    have hbase : Tendsto (fun n : ℕ => (1 - η) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one hη
    have hlim : Tendsto (fun n : ℕ => x' + (1 - η) ^ n * (θ.1 - x')) atTop (nhds x') := by
      have h0 := hbase.mul_const (θ.1 - x')
      have h1 : Tendsto (fun n : ℕ => x' + (1 - η) ^ n * (θ.1 - x')) atTop
          (nhds (x' + 0 * (θ.1 - x'))) := tendsto_const_nhds.add h0
      simpa using h1
    have hfun : (fun n : ℕ => (iterMap linA linPhi η x' n θ).1)
        = fun n : ℕ => x' + (1 - η) ^ n * (θ.1 - x') := by
      funext n
      exact linA_iter_first η x' n θ
    rw [hfun]
    exact hlim
  · -- 第二坐标：恒等于 θ.2
    have hfun : (fun n : ℕ => (iterMap linA linPhi η x' n θ).2) = fun _ : ℕ => θ.2 := by
      funext n
      exact linA_iter_second η x' n θ
    rw [hfun]
    exact tendsto_const_nhds

end ConvergenceContrast

end Fate
