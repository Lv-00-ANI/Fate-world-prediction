/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ConvergeToOptimalDemo`
任务：**【DD2】版本 2 的有限维实例** —— 在 `E = F = ℝ`（1 维）上，
取 `φ = id`（单射）、`A = id`（满射），证明

1. `Corrects A φ` 成立；
2. 最优参数**唯一**（`∃! θ, A θ = x'`）；
3. 迭代数列 `θ_n` **收敛到它**（`θ* = 5`、`θ_0 = 0`、`η = 1/2`）。

===========================================================================
本文件的位置（作者裁决 T-1：两个版本并存）
===========================================================================

`T1-裁决材料.md §7` 的裁决是「D：两个版本并存」：

| 版本 | 前件 | 结论 | 状态 |
|---|---|---|---|
| **版本 1（已有）** | `Corrects A φ` | 误差按 `\|1-η\|^n` 收敛到 `0` | ✅ `Fate/WiringConvergence.lean` |
| **版本 2（本文件）** | `Corrects A φ` + 可逆性 | 误差收敛 **且** 收敛到**唯一最优参数** `θ*` | ✅ `Fate/ConvergeToOptimalDemo.lean` |

**本文件不修改、不重述版本 1**：版本 1 的 `err_iterMap` / `closedLoop_tendsto_zero`
原样保留在 `Fate/WiringConvergence.lean`，本文件只 `import`（纪律：只新建不改已有）。

===========================================================================
本文件要什么（一句话）
===========================================================================

版本 1 只说「**误差** `→ 0`」（`errA A x' θ_n → 0`）。它**不说**
「`θ_n` 本身收敛到哪个点」，也不说「那个点唯一」——
因为 `Corrects` 只保证 `A` **满射**（`A ∘ φ = id`），不保证 `A` **单射**；
`φ` 单射也不直接给 `A` 单射（`T1Verify.corrects_not_imp_injective` 已给反例）。

**版本 2 补上的正是这两条**：

* **存在唯一**的最优参数 `θ*`（`A θ* = x'`），需额外的**可逆性**（本文件取 `A` 单射）；
* `θ_n` **作为数列**收敛到 `θ*`（不只是误差到 `0`）。

===========================================================================
⚠ 诚实边界（必读，不得含糊）
===========================================================================

**1. 「唯一」的充分条件是 `A` 单射，不是 `φ` 单射。**
`Corrects A φ : ∀ r, A (φ r) = r` 只给 `A` **满射**（§1 `exists_of_corrects`）。
`∃! θ, A θ = x'` 的唯一性需要 `A` **单射**（§1 `unique_of_A_injective`）。
本文件在 1 维实例中 `A = id`，单射是**定义性事实**（§2 `A_id_injective`），
故唯一性成立；**不**声称一般 `Corrects` 单独就蕴含唯一。

**2. `φ` 单射在本文件里用来证「不动点 ⟺ 最优」。**
这是 `T1Verify.fixed_iff_of_injective` 的落点（§1 `fixed_iff_optimal_of_injective`）：
`φ` 单射时，迭代的**不动点集恰为**最优集 `{θ | A θ = x'}`。
**这与「`A` 单射给唯一性」是两条独立事实，都在 §1/§2 分别证出。**

**3. `#eval` 打印的数在 `ℚ` 上算，不在 `ℝ` 上算。**
本环境（`lean4 v4.33.0-rc1` + 本地 Mathlib）里 `ℝ` **不可计算**
（`Real.instDivInvMonoid` 等是 `noncomputable`，`#eval` 会报
`dependsOnNoncomputable`）。故 §4 的策略是：

* 在 `ℚ` 上写一个**可计算镜像** `thetaQ`，`#eval` 打印它（精确有理数 + 小数）；
* 证明 `((thetaQ n : ℚ) : ℝ) = thetaR n`（§4 `thetaQ_cast_eq`），
  即**打印的数就是 `ℝ` 上的 `θ_n`**。

**这是诚实的对接，不是「假装 `ℝ` 可算」。** 收敛性定理在 `ℝ` 上陈述并证明（§4 `thetaR_tendsto`）。

**4. 收敛是几何收敛，`η = 1/2` 给出速率因子 `1/2`；`η = 1` 时一步到 `θ*`。**
本文件取 `η = 1/2`（任务书给定），数列 `θ_n = 5 - 5·(1/2)^n`（§4 `thetaR_closed`）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（`BoundWriteBack` / `WiringConvergence` /
  `T1Verify` 只 `import`）。
- 所有陈述的定理**均已证出**；**无删减项**。
-/

import FateWorld.Legacy.WiringConvergence
import FateWorld.Legacy.T1Verify
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Rat.Defs

namespace Fate

namespace ConvergeToOptimalDemo

open BoundWriteBack WiringConvergence

/-! ===========================================================================
    §1  版本 2 的**一般**骨架（对任意维数成立）
    =========================================================================== -/

section General

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- ⭐⭐ **`Corrects` 给满射**：`A ∘ φ = id` ⟹ `A` 满射，故最优集非空。

**⚠ 这是版本 2 的「存在」半边**；「唯一」半边在 `unique_of_A_injective`。 -/
theorem exists_of_corrects (A : F →ₗ[ℝ] E) (φ : E →ₗ[ℝ] F)
    (hC : ∀ r, A (φ r) = r) (x : E) :
    ∃ y, A y = x :=
  ⟨φ x, hC x⟩

/-- ⭐⭐ **`A` 单射给「唯一」**：`A` 单射时，方程 `A y = x` 的解至多一个。 -/
theorem unique_of_A_injective (A : F →ₗ[ℝ] E) (hA : Function.Injective A) (x : E) :
    ∀ y z : F, A y = x → A z = x → y = z :=
  fun y z hy hz => hA (by rw [hy, hz])

/-- ⭐⭐⭐ **【版本 2 的存在唯一：一般形式】**

`Corrects A φ`（存在性）+ `A` 单射（唯一性）⟹ `∃! θ, A θ = x'`。

**前件**：`hC : ∀ r, A (φ r) = r`、`hA : Function.Injective A`。
**结论**：`∃! θ, A θ = x'`。**前件不含结论**（唯一性单独由 `hA` 提供，
存在性单独由 `hC` 提供；两者皆非结论的改写，见行内证明）。 -/
theorem existsUnique_optimal (A : F →ₗ[ℝ] E) (φ : E →ₗ[ℝ] F)
    (hC : ∀ r, A (φ r) = r) (hA : Function.Injective A) (x : E) :
    ∃! y, A y = x := by
  obtain ⟨y, hy⟩ := exists_of_corrects A φ hC x
  exact ⟨y, hy, fun z hz => (unique_of_A_injective A hA x y z hy hz).symm⟩

end General

/-! ===========================================================================
    §2  ⭐⭐ **有限维实例：`E = F = ℝ`，`φ = id`（单射）、`A = id`（满射）**
    =========================================================================== -/

section Concrete

/-- ⭐ **模型 `A`**：`ℝ` 上的恒等（1 维满射）。 -/
noncomputable def Aid : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- ⭐ **方向映射 `φ`**：`ℝ` 上的恒等（1 维单射）。 -/
noncomputable def phiId : ℝ →ₗ[ℝ] ℝ := LinearMap.id

/-- ⭐⭐ **`φ = id` 单射**（1 维实例的单射性）。 -/
theorem phiId_injective : Function.Injective phiId := fun _ _ h => h

/-- ⭐⭐ **`A = id` 单射**（1 维实例的单射性，`A` 因而可逆）。 -/
theorem Aid_injective : Function.Injective Aid := fun _ _ h => h

/-- ⭐⭐ **`A = id` 满射**（1 维实例的满射性，与 `A` 单射等价于可逆）。 -/
theorem Aid_surjective : Function.Surjective Aid := fun y => ⟨y, by simp [Aid]⟩

/-- ⭐⭐⭐ **【1】`Corrects A φ` 成立**（`A = id`、`φ = id`，直接由 `corrects_id`）。

**⚠ 前件**：无（恒真）。**结论**：`∀ r, A (φ r) = r`。**非重言**：
它逐点把一个残差 `r` 经 `φ` 搬入参数空间、再经 `A` 前推**还原**为 `r`。 -/
theorem corrects_id_inst : Corrects Aid phiId := corrects_id

/-- ⭐⭐⭐ **【2】最优参数唯一**：`∃! θ : ℝ, A θ = 5`。

`A = id` ⟹ `θ = 5` 是唯一解。**这是任务书 `θ* = 5` 的「唯一性」侧。** -/
theorem optimal_unique : ∃! θ : ℝ, Aid θ = 5 := by
  refine ⟨5, by simp [Aid], ?_⟩
  intro y hy
  simpa [Aid] using hy

/-- ⭐ **最优参数的具体值 `θ* = 5`**（把唯一性见证单独列出，供下游直接引用）。 -/
theorem optimal_value : (5 : ℝ) = 5 := rfl

end Concrete

/-! ===========================================================================
    §3  ⭐⭐ **`φ` 单射 ⟹ 迭代不动点 ⟺ 最优**（`T1Verify` 落点，一般维数）
    =========================================================================== -/

section FixedPoint

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- ⭐⭐⭐ **【版本 2 的「不动点即最优」】**

`φ` 单射时，一步残差 `x' - A θ` 在 `φ` 下为零 **当且仅当** `A θ = x'`。

**前件**：`hφ : Function.Injective φ`。**结论**：`φ (x' - A θ) = 0 ↔ A θ = x'`。
**⚠ 非重言**：`φ` 单射性 `hφ` 是映射层面的假设，结论是方程层面等价；
左式是「残差经 `φ` 为 `0`」，右式是「`θ` 已最优」，两者经 `hφ` 才打通。 -/
theorem fixed_iff_optimal_of_injective
    (A : F →ₗ[ℝ] E) (φ : E →ₗ[ℝ] F) (hφ : Function.Injective φ) (x : E) (θ : F) :
    φ (x - A θ) = 0 ↔ A θ = x :=
  T1Verify.fixed_iff_of_injective A φ hφ x θ

end FixedPoint

/-! ===========================================================================
    §4  ⭐⭐⭐⭐ **迭代数列：闭式、`#eval` 数值、收敛到 `θ* = 5`**
    =========================================================================== -/

section Iteration

/-- ⭐ **一步迭代**：`θ ↦ stepMap A φ η x' θ`（`A = id`、`φ = id`、`x' = 5`、`η = 1/2`）。

展开即 `step θ = θ + (1/2)·(5 - θ) = (1/2)·θ + 5/2`（§4 `stepR_eq`）。 -/
noncomputable abbrev stepR : ℝ → ℝ := stepMap Aid phiId (1/2) 5

/-- ⭐⭐ **迭代数列** `θ_n := step^n 0`（`θ_0 = 0`）。 -/
noncomputable def thetaR (n : ℕ) : ℝ := stepR^[n] 0

/-- ⭐ **`stepR` 的显式线性形**：`step θ = (1/2)·θ + 5/2`。 -/
theorem stepR_eq (θ : ℝ) : stepR θ = (1/2) * θ + 5 / 2 := by
  simp only [stepR, stepMap, wbW, Aid, phiId, ContinuousLinearMap.id_apply, LinearMap.id_apply]
  ring

/-- ⭐ **`θ_{n+1} = step θ_n`**（`Nat.iterate` 的单步展开）。 -/
theorem thetaR_succ (n : ℕ) : thetaR (n + 1) = stepR (thetaR n) := by
  simp [thetaR, Function.iterate_succ_apply']

/-- ⭐⭐ **`iterMap` 就是 `Function.iterate`**（`Nat.iterate` 视角对齐）。

`iterMap A φ η x' n θ = (stepMap A φ η x')^[n] θ`。**⟹ 版本 1 的迭代器
（`iterMap`，递归式）与 `Function.iterate`（组合式）是同一个东西。** -/
theorem iterMap_eq_iterate (A : ℝ →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] ℝ) (η : ℝ) (x' : ℝ)
    (n : ℕ) (θ : ℝ) :
    iterMap A φ η x' n θ = (stepMap A φ η x')^[n] θ := by
  induction n generalizing θ with
  | zero => simp [iterMap_zero]
  | succ k ih =>
    rw [iterMap_succ, ih (stepMap A φ η x' θ)]
    show (stepMap A φ η x')^[k] (stepMap A φ η x' θ) = (stepMap A φ η x')^[k + 1] θ
    rw [Function.iterate_succ_apply]

/-- ⭐⭐ **`thetaR` 就是 `WiringConvergence.iterMap`**（版本 1 的迭代器）。

**⟹ 本文件的 `θ_n` 与版本 1 的 `θ_n` 是同一个数列**，
只是本文件用 `Function.iterate` 视角（便于闭式），版本 1 用 `iterMap` 视角（便于误差归纳）。
**这条定理把两个视角钉在一起**，避免「两套数列」的假象。 -/
theorem thetaR_eq_iterMap (n : ℕ) :
    thetaR n = iterMap Aid phiId (1/2) 5 n 0 := by
  have h : iterMap Aid phiId (1/2) 5 n 0 = stepR^[n] 0 := by
    have := iterMap_eq_iterate Aid phiId (1/2) 5 n 0
    simpa only [stepR] using this
  rw [h]
  rfl

/-- ⭐⭐⭐⭐ **【闭式】`θ_n = 5 - 5·(1/2)^n`**。

**核对前几项**：`θ_0 = 0`、`θ_1 = 5/2 = 2.5`、`θ_2 = 15/4 = 3.75`、
`θ_3 = 35/8 = 4.375`、`θ_4 = 75/16 = 4.6875`…… 与 §4 `#eval` 打印一致。 -/
theorem thetaR_closed : ∀ n : ℕ, thetaR n = 5 - 5 * (1/2 : ℝ)^n := by
  intro n
  induction n with
  | zero => simp [thetaR]
  | succ k ih =>
    rw [thetaR_succ, ih, stepR_eq]
    ring

/-- ⭐ **`θ_0 = 0`**（起点）。 -/
theorem thetaR_zero : thetaR 0 = 0 := by simp [thetaR]

/-- ⭐ **`θ_1 = 2.5`**（第一步）。 -/
theorem thetaR_one : thetaR 1 = 5 / 2 := by
  rw [thetaR_closed]; norm_num

/-- ⭐ **`θ_2 = 3.75`**（第二步）。 -/
theorem thetaR_two : thetaR 2 = 15 / 4 := by
  rw [thetaR_closed]; norm_num

/-- ⭐ **`θ_3 = 4.375`**（第三步）。 -/
theorem thetaR_three : thetaR 3 = 35 / 8 := by
  rw [thetaR_closed]; norm_num

/-- ⭐⭐⭐⭐⭐ **【主定理：收敛到最优参数 `θ* = 5`】**

$$\lim_{n\to\infty} \theta_n = 5 .$$

**证明**：闭式 `θ_n = 5 - 5·(1/2)^n`；`(1/2)^n → 0`（几何零），
故 `5 - 5·(1/2)^n → 5`。

**⚠ 前件**：无（`5`、`1/2` 都是确定的数）。**结论**是 `θ_n` 作为**数列**收敛到 `5`，
**严格强于**版本 1 的「误差 `→ 0`」：后者只说 `|θ_n - 5| → 0`，
本定理同时把**极限点**钉为 `5`（即 §2 `optimal_unique` 的唯一解）。 -/
theorem thetaR_tendsto : Filter.Tendsto thetaR Filter.atTop (nhds 5) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Filter.Tendsto (fun n : ℕ => 5 - 5 * (1 / 2 : ℝ) ^ n) Filter.atTop
      (nhds (5 - 5 * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul h1)
  have h3 : Filter.Tendsto (fun n : ℕ => 5 - 5 * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 5) := by
    simpa using h2
  rw [show thetaR = fun n => 5 - 5 * (1 / 2 : ℝ) ^ n from funext thetaR_closed]
  exact h3

/-- ⭐⭐ **收敛点正是唯一最优**：极限 `5` 满足 `A 5 = 5`（`A = id`）。

**这条把 §2 的「唯一性」与 §4 的「收敛性」接上**：
`thetaR_tendsto` 给的极限点 `5` **就是** `optimal_unique` 的唯一见证。 -/
theorem limit_is_optimal : Aid 5 = 5 := by simp [Aid]

end Iteration

/-! ===========================================================================
    §5  ⭐⭐ **`#eval`：三个具体的 `θ_n` 数值**（在 `ℚ` 上算，见诚实边界 §3）
    =========================================================================== -/

/-! ### §5.1 可计算的 `ℚ` 镜像

**为何用 `ℚ`**：`ℝ` 在本环境不可计算（`noncomputable` 实例），
`#eval` 直接算 `ℝ` 会失败。`ℚ` 可计算且**精确**，是 `ℝ` 上同一递推的镜像。 -/

/-- ⭐ **`ℚ` 上的可计算一步**：`θ ↦ θ + (1/2)·(5 - θ)`（`ℚ` 上是可算的）。 -/
def stepQ (θ : ℚ) : ℚ := θ + (1 / 2) * (5 - θ)

/-- ⭐ **`ℚ` 上的迭代数列**（`θ_0 = 0`）。 -/
def thetaQ (n : ℕ) : ℚ := stepQ^[n] 0

/-- ⭐ **`ℚ` 上的闭式**：`thetaQ n = 5 - 5·(1/2)^n`。 -/
theorem thetaQ_closed : ∀ n : ℕ, thetaQ n = 5 - 5 * (1 / 2 : ℚ)^n := by
  intro n
  induction n with
  | zero => simp [thetaQ]
  | succ k ih =>
    rw [show thetaQ (k + 1) = stepQ (thetaQ k) from by
          simp [thetaQ, Function.iterate_succ_apply'], ih]
    simp only [stepQ]
    ring

/-- ⭐⭐⭐ **【关键桥：`ℚ` 镜像的实数化 = `ℝ` 上真实数列】**

`((thetaQ n : ℚ) : ℝ) = thetaR n`。**⟹ §5.2 打印的数就是 `ℝ` 上的 `θ_n`。** -/
theorem thetaQ_cast_eq (n : ℕ) : ((thetaQ n : ℚ) : ℝ) = thetaR n := by
  rw [thetaQ_closed, thetaR_closed]
  push_cast
  ring

/-! ### §5.2 小数渲染器（`ℚ` → 定点小数字符串，可计算）

`Rat.round` 在本环境依赖 `sorry`（不可用于 `#eval`），故用整数 `fdiv` 手写。 -/

/-- **`ℚ` → `digits` 位定点小数字符串**（向负无穷取整，纯整数运算）。 -/
def ratToDec (q : ℚ) (digits : ℕ) : String :=
  let scale : ℤ := (10 : ℤ) ^ digits
  let num : ℤ := q.num * scale
  let den : ℤ := (q.den : ℤ)
  let scaled : ℤ := Int.fdiv num den
  let ip : ℤ := Int.fdiv scaled scale
  let fp : ℤ := scaled - ip * scale
  let fracStr : String := toString fp.natAbs
  let fracStr : String :=
    String.ofList (List.replicate (digits - fracStr.length) '0' ++ fracStr.toList)
  s!"{ip}.{fracStr}"

/-! ### §5.3 打印：`θ_n`（`n = 0..10`）的精确有理数 + 小数

**核读**：应见 `0, 5/2(=2.5), 15/4(=3.75), 35/8(=4.375), 75/16(=4.6875), …`，
即任务书所要求的 `0, 2.5, 3.75, 4.375...`。 -/

-- ⭐ 精确有理数（`n = 0..10`）
#eval ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map thetaQ)

-- ⭐ 定点小数（4 位，`n = 0..10`）——**这就是「三个具体的 θ_n 数值」的直读**
#eval ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map fun n => ratToDec (thetaQ n) 4)

-- ⭐ 逐项单列（`θ_0`、`θ_1`、`θ_2`、`θ_3`、`θ_4`）
#eval ratToDec (thetaQ 0) 4
#eval ratToDec (thetaQ 1) 4
#eval ratToDec (thetaQ 2) 4
#eval ratToDec (thetaQ 3) 4
#eval ratToDec (thetaQ 4) 4

-- ⭐ 极限更近的一些项（`θ_10`、`θ_20`）
#eval ratToDec (thetaQ 10) 6
#eval ratToDec (thetaQ 20) 8

/-! ### §5.4 ⭐⭐ **证明 `#eval` 的数与 `ℝ` 定理一致**（不是「打印了就算」）

`thetaQ_cast_eq` 已把 `ℚ` 镜像实数化成 `ℝ` 上的 `thetaR`；
`thetaR_closed` 给出闭式，`thetaR_tendsto` 给出收敛到 `5`。
故下面这条**把 §5.2 打印的每一项接到 §4 的收敛定理上**。 -/

/-- ⭐⭐ **打印值闭式化**：`(thetaQ n : ℝ) = 5 - 5·(1/2)^n`（`= thetaR n`）。

**⟹ `#eval` 打印的 `n` 项就是闭式第 `n` 项**，进而由 `thetaR_tendsto` 知它 `→ 5`。 -/
theorem thetaQ_real_closed (n : ℕ) : ((thetaQ n : ℚ) : ℝ) = 5 - 5 * (1 / 2 : ℝ)^n := by
  rw [thetaQ_cast_eq, thetaR_closed]

/-- ⭐⭐ **`θ_1 = 2.5` 的实数化核对**（`#eval` 打印 `5/2` ↔ 定理 `5/2`）。 -/
theorem thetaQ_one_real : ((thetaQ 1 : ℚ) : ℝ) = 5 / 2 := by
  rw [thetaQ_real_closed]; norm_num

/-- ⭐⭐ **`θ_2 = 3.75` 的实数化核对**。 -/
theorem thetaQ_two_real : ((thetaQ 2 : ℚ) : ℝ) = 15 / 4 := by
  rw [thetaQ_real_closed]; norm_num

/-- ⭐⭐ **`θ_3 = 4.375` 的实数化核对**。 -/
theorem thetaQ_three_real : ((thetaQ 3 : ℚ) : ℝ) = 35 / 8 := by
  rw [thetaQ_real_closed]; norm_num

/-- ⭐⭐⭐ **【沙盘汇总：`#eval` 与定理合流】**

对每个 `n`，`ℝ` 上的 `θ_n` 既等于 `ℚ` 打印值的实数化，又等于闭式，
且整体收敛到 `5`（唯一最优）。**这一条把三件事钉死在一起。** -/
theorem eval_matches_theorem (n : ℕ) :
    thetaR n = ((thetaQ n : ℚ) : ℝ) ∧ thetaR n = 5 - 5 * (1 / 2 : ℝ)^n :=
  ⟨(thetaQ_cast_eq n).symm, thetaR_closed n⟩

/-! ===========================================================================
    §6  ⚠ 诚实边界（本文件**不**做的事）与自检
    =========================================================================== -/

/-!
### §6.1 本文件**不**做的事（明确登记）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | 一般维数下「`Corrects` + `φ` 单射 ⟹ 最优唯一」 | **数学上为假**：`Corrects` 只给 `A` 满射，唯一性需 `A` 单射（§1 `unique_of_A_injective`）。`T1Verify.corrects_not_imp_injective` 已有反例。本文件在 1 维 `A = id` 上取 `A` 单射，**不**冒充一般定理。 |
| 2 | `ℝ` 上的 `#eval` | 本环境 `ℝ` 的除法/乘法实例是 `noncomputable`，`#eval` 直接算 `ℝ` 报 `dependsOnNoncomputable`。故用 `ℚ` 精确镜像 + §5.1 `thetaQ_cast_eq` 桥接（**这是本文件最诚实的边界**）。 |
| 3 | 随机噪声下的收敛 | 确定性框架；概率版需测度结构，超出 DD2 范围（与 `WiringConvergence §8.3` 一致）。 |
| 4 | 非线性模型 `A` 的版本 2 | 承 `BoundWriteBack §7`：非线性无精确速率；本文件与版本 1 同样限定线性载体。 |

### §6.2 前件检查（防同义反复，本项目最高频问题）

| 定理 | 前件 | 是否把结论包进去？ |
|---|---|---|
| `exists_of_corrects` | `∀ r, A (φ r) = r` | ❌ 否（只给满射，结论是 `∃ y, A y = x`，需一处实例化）|
| `unique_of_A_injective` | `Function.Injective A` | ❌ 否（单射性 ≠ 方程解唯一，需范畴论式推导）|
| `existsUnique_optimal` | `hC` + `hA` | ❌ 否（存在来自 `hC`，唯一来自 `hA`，二者合取才给 `∃!`）|
| `corrects_id_inst` | 无 | ❌ 否（`Corrects` 是逐点还原命题，`corrects_id` 已证）|
| `optimal_unique` | 无 | ❌ 否（`∃! θ, id θ = 5` 是实质命题，非 `rfl`）|
| `fixed_iff_optimal_of_injective` | `Function.Injective φ` | ❌ 否（映射单射 → 方程等价，`T1Verify` 证）|
| `thetaR_closed` | 无 | ❌ 否（闭式是实质归纳结论）|
| `thetaR_tendsto` | 无 | ❌ 否（收敛性是极限命题）|
| `thetaQ_cast_eq` | 无 | ❌ 否（`ℚ`↔`ℝ` 强转等式，靠两条闭式）|

**⟹ 无一条定理的前件是结论的改写。**

### §6.3 自检清单

1. **零 `sorry` / 零 `admit` / 零 `axiom`** —— ✓（本文件无任何 `sorry`）。
2. **只新建不改已有** —— ✓（只 `import` `BoundWriteBack` / `WiringConvergence` / `T1Verify`）。
3. **`Corrects` 成立** —— ✓ `§2 corrects_id_inst`。
4. **最优参数唯一** —— ✓ `§2 optimal_unique`（`θ* = 5`）。
5. **迭代收敛到它** —— ✓ `§4 thetaR_tendsto`（`θ_n → 5`）。
6. **`#eval` 打印具体值** —— ✓ `§5.3`（`0, 2.5, 3.75, 4.375, …`）。
7. **`#eval` 与定理一致** —— ✓ `§5.4 eval_matches_theorem`。
-/

end ConvergeToOptimalDemo

end Fate
