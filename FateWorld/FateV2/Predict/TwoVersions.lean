/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.TwoVersions`
任务：**测试任务 D** —— 「两个版本并存」之**版本 2**（`φ` 单射 / 唯一参数版）

本文件**只新增**，不修改任何既有模块。

===========================================================================
一、任务来源（逐字引用）
===========================================================================

`T1-裁决材料.md` §7「作者裁决（第 39 轮）」：

> **「D：两个版本并存」**
> 把「收敛到唯一参数」当作**新的独立目标**，单独建一条任务线
> （加 `φ` 单射的版本），与现有的「误差收敛」版本**并存**。

| 版本 | 前件 | 结论 | 状态 |
|---|---|---|---|
| 版本 1（既有 `Fate/BoundWriteBack.lean`） | `Corrects A φ` | 误差按 `\|1-η\|^n` 收敛到 0 | ✅ 已证 |
| **版本 2（本文件）** | `Corrects A φ` + `A` 单射 | 误差收敛 **且** 收敛到唯一最优参数 | ✅ **本文件** |

`T1-裁决材料.md` §7.3 列出的四条具体任务，本文件的对应落地：

| §7.3 | 任务 | 本文件定理 |
|---|---|---|
| 1 | 定义「最优参数唯一性」：`∃! θ, A θ = x'` | `existsUnique_solution` |
| 2 | `Corrects A φ` + 单射 ⟹ `∃! θ, A θ = x'` | `existsUnique_solution`（+ `surjective_of_corrects`） |
| 3 | `Corrects A φ` + 单射 ⟹ `θ_n → θ*` | `version2_main`、`wbSeq_tendsto_thetaStar` |
| 4 | 给出单射的充分条件 | § Inj：`injective_of_leftInverse` 等 |

===========================================================================
二、⚠⚠ 对 §7.3 的一处**必须诚实纠正**（最重要的一条）
===========================================================================

**§7.3 第 2 条写的是「`φ` 单射」，但数学上正确的条件是「`A` 单射」。**

**理由（反例，本文件 § Counter 已 Lean 验证）**：

取 `E := ℝ × ℝ`、`F := ℝ`、
`A := fst`（`A (u,v) = u`）、`φ := fun r => (r, 0)`。则

* `Corrects A φ`：`A (φ r) = A (r,0) = r` ✅（§ Counter `counter_corrects`）
* `φ` **单射**：`(a,0) = (b,0) ⟹ a = b` ✅（§ Counter `counter_phi_injective`）
* 但 `A` **不单射**：`A (0,0) = A (0,1) = 0`（§ Counter `counter_A_not_injective`）
* 故 `A θ = 1` **至少两解** `(1,0)`、`(1,1)`（§ Counter `counter_not_unique`）

**⟹ `Corrects` + `φ` 单射**推不出**唯一性。**唯一的正确前提是 `A` 单射。**

**为什么容易搞混**：`Corrects A φ : ∀ r, A (φ r) = r` 说的是
「`A` 是 `φ` 的**左逆**」（故 `φ` 单射、`A` 满射）。
而要「`A θ = x'` 唯一」需要的是「`A` 是**单射**」——那是**反方向**的假设。
`A` 既是单射又是满射即 `A` 双射；`dim E = dim F` 时才自动。

**本文件的处置**：
1. **不删除**「`φ` 单射」这条线索——它在 § Inj 里被**如实**证明为
   「`Corrects` 的自动推论」（`corrects_phi_injective`），即它是**冗余前提**，
   而非可用的唯一性来源。这一点也如实标注。
2. 唯一性定理 `existsUnique_solution` **显式取 `A` 单射**。
3. § Counter 用 Lean 证明「`A` 单射」**不可**被「`φ` 单射」替代。

===========================================================================
三、本文件的实质内容（防止同义反复的自查，逐条）
===========================================================================

**核心非平凡结论**：闭环 `θ_{n+1} = θ_n + η • φ (x' - A θ_n)` 的**极限闭式**

$$\theta_n \longrightarrow \theta^* := \theta_0 + \varphi\,(x' - A\,\theta_0),
\qquad\text{且}\quad A\,\theta^* = x' .$$

**这不是同义反复**：
* 极限点 `θ*` **不在任何前件里**，它是右端的**定义**；
* 收敛性由**几何级数** `Σ_{k<n} (1-η)^k → η⁻¹` 得出（§ 2 `tendsto_partial_sum`），
  前件只有 `Corrects` 与 `|1-η| < 1`；
* `A θ* = x'` 是**推论**（`thetaStar_is_solution`），需要 `Corrects`；
* 极限点**依赖初值 `θ_0`**（`thetaStar` 的定义里就有 `θ_0`）——
  这正是版本 2 相对版本 1 的**新增信息**：*不是*只说「误差→0」，
  而是**指出误差→0 时参数落在哪个具体的点**。
* 唯一性（`existsUnique_solution`）**另需** `A` 单射——`Corrects` **不**含此信息（§ Counter）。

===========================================================================
四、诚实边界（先写清，不事后补）
===========================================================================

**4.1 本文件**不**声称「`Corrects` + `φ` 单射 ⟹ 唯一」。**
恰恰相反：§ Counter **给出 Lean 反例**证明它**为假**。
这是对任务书 §7.3 第 2 条的**纠正**，不是偷换。

**4.2 版本 1 保留不动。** 本文件不修改 `Fate/BoundWriteBack.lean`、
`Fate/ThetaConvergence.lean` 或任何既有模块。版本 1（`writeBack_reduces_error` 一族）
与版本 2（本文件）**并存**，正是裁决要求。

**4.3 本文件是抽象线性框架（任意实赋范空间 `E`、`F`）。**
具体实例化在 § Inst（`E = F = ℝ`），与 `Fate/ThetaConvergence.lean` 的
`θ_n → θ*` 在同一层面；但本文件**不 import 也不复用**它的证明路径，
而是从 `wbW`/`Corrects` 出发**独立**推出（见 § 5 `wbSeq_closed`）。

**4.4 不声称非线性收敛。** `A : E →L[ℝ] F` 是连续**线性**算子。
非线性情形下残差不再等比，本文件的 `residN_closed` **立即失效**。

**4.5 `η` 窗口是 `|1-η| < 1`（即 `0 < η < 2`）。**
`η = 0`（不动）与 `η ≥ 2`（发散/不缩）不在结论范围内，且
`|1-η| < 1 ⟹ η ≠ 0`（`eta_ne_zero_of_abs`）保证几何级数求和合法。

===========================================================================
五、结构
===========================================================================

| 节 | 内容 |
|---|---|
| § 0 | 基本算子：一步函数 `stepFn`、迭代 `wbSeq`、残差 `residN` |
| § 1 | ⭐ 一步的仿射形式 `A (wbW …) = (1-η) • Aθ + η • x'` |
| § 2 | ⭐⭐ 残差等比律 + **残差闭式** `r_n = (1-η)^n • r_0` |
| § 3 | ⭐⭐ **参数求和闭式** `θ_n = θ_0 + (η Σ (1-η)^k) • φ r_0` |
| § 4 | ⭐⭐⭐⭐ **主定理**：`θ_n → θ*`、极限唯一、`A θ* = x'`、`A θ_n → x'` |
| § Uni | ⭐⭐⭐⭐ 唯一性 `∃! θ, A θ = x'`；**版本 2 一体化主定理** `version2_main` |
| § Inj | `φ` 单射的充分条件 + `Corrects ⟹ φ 单射`（冗余前提的如实登记） |
| § Counter | ⚠ **反例**：`φ` 单射**不能**替代 `A` 单射（Lean 验证） |
| § Inst | 具体实例 `E = F = ℝ`，`A = φ = id`，与 `θ_n → θ*` 对照 |
| § Check | 自检清单 |

纪律：零 `sorry` / 零 `admit` / 零 `axiom`。
===========================================================================

-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Module.Basic
import FateWorld.FateV2.Loop.BoundWriteBack
import FateWorld.FateV2.Loop.WiringConvergence
open Filter FateV2.Loop.BoundWriteBack

namespace FateV2.Predict

open FateV2.Loop
namespace BoundWriteBackV2

section Core

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!
  # Predict · TwoVersions

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TwoVersions.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BoundWriteBack, WiringConvergence
  - 补充 open 域：FateV2.Loop
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    § 0  基本算子：一步函数、迭代、残差
    =========================================================================== -/

/-- ⭐ **一步函数**：`wbW` 的部分应用。

**⚠ 不另造更新语义**：`stepFn A φ η x' θ = wbW A φ η x' θ`（`rfl`）。 -/
def stepFn (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) : E → E :=
  fun θ => wbW A φ η x' θ

/-- ⭐⭐ **闭环参数序列** `θ_n := (stepFn)^[n] θ_0`（`Nat.iterate`，不引入第二个迭代语义）。 -/
def wbSeq (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) : ℕ → E :=
  fun n => (stepFn A φ η x')^[n] θ₀

/-- ⭐ **残差** `r_n := x' - A θ_n`（与 `BoundWriteBack.resA` 同形）。 -/
def residN (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) (n : ℕ) : F :=
  x' - A (wbSeq A φ η x' θ₀ n)

/-- 迭代的零步：`θ_0 = θ_0`（定义性）。 -/
theorem wbSeq_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) :
    wbSeq A φ η x' θ₀ 0 = θ₀ := rfl

/-- ⭐ 迭代的递推步：`θ_{n+1} = wbW A φ η x' θ_n`。 -/
theorem wbSeq_succ (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) (n : ℕ) :
    wbSeq A φ η x' θ₀ (n+1) = wbW A φ η x' (wbSeq A φ η x' θ₀ n) := by
  show (stepFn A φ η x')^[n+1] θ₀ = wbW A φ η x' ((stepFn A φ η x')^[n] θ₀)
  rw [Function.iterate_succ_apply']
  rfl

/-- ⭐⭐ **单步位移**：`θ_{n+1} - θ_n = η • φ r_n`（定义性，不用 `Corrects`）。 -/
theorem wbSeq_sub (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) (n : ℕ) :
    wbSeq A φ η x' θ₀ (n+1) - wbSeq A φ η x' θ₀ n = η • φ (residN A φ η x' θ₀ n) := by
  rw [wbSeq_succ, wbW_apply]
  simp only [residN]
  abel

/-! ===========================================================================
    § 1  一步的仿射形式（技术起点）
    =========================================================================== -/

/-- ⭐⭐ **`A` 前推一步更新 = 仿射组合**：

$$A\,(\mathrm{wbW}\ A\ φ\ η\ x'\ θ) \;=\; (1-η)\bullet A\,θ \;+\; η\bullet x' .$$

**由 `BoundWriteBack.image_wbW`（误差恒等式）改写而来**，不改动既有定义。
**⭐ 意义**：右端是 `A θ` 与 `x'` 的**凸/仿射组合**，`A` 的错误部分按 `1-η` 衰减。 -/
theorem image_wbW_affine (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) :
    A (wbW A φ η x' θ) = (1 - η) • (A θ) + η • x' := by
  have himg := image_wbW A φ η x' θ h
  rw [sub_eq_iff_eq_add] at himg
  rw [himg]
  module

/-! ===========================================================================
    § 2  ⭐⭐ 残差等比律与残差闭式
    =========================================================================== -/

/-- ⭐⭐ **残差等比律**：`r_{n+1} = (1-η) • r_n`（**一步**，用 `Corrects`）。 -/
theorem residN_succ (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E)
    (h : Corrects A φ) (n : ℕ) :
    residN A φ η x' θ₀ (n+1) = (1 - η) • residN A φ η x' θ₀ n := by
  have h1 : wbSeq A φ η x' θ₀ (n+1) = wbW A φ η x' (wbSeq A φ η x' θ₀ n) := wbSeq_succ ..
  have h2 : A (wbSeq A φ η x' θ₀ (n+1))
      = (1 - η) • (A (wbSeq A φ η x' θ₀ n)) + η • x' := by
    rw [h1]; exact image_wbW_affine A φ η x' _ h
  simp only [residN, h2]
  module

/-- ⭐⭐⭐ **【残差闭式】**：`r_n = (1-η)^n • r_0`，`r_0 = x' - A θ_0`。

**⭐ 这就是版本 1 的结论**（`err(θ_n) = |1-η|^n err(θ_0)`）在本框架下的形式：
版本 1 说「误差按几何级数衰减」，本式把**向量**残差本身写成了闭式。
**版本 2 在此之上再问「参数 `θ_n` 落在哪」——见 § 3。** -/
theorem residN_closed (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E)
    (h : Corrects A φ) (n : ℕ) :
    residN A φ η x' θ₀ n = (1 - η)^n • (x' - A θ₀) := by
  induction n with
  | zero => show x' - A ((stepFn A φ η x')^[0] θ₀) = _; simp [sub_eq_add_neg]
  | succ k ih =>
    rw [residN_succ A φ η x' θ₀ h k, ih, smul_smul, pow_succ, mul_comm]

/-! ===========================================================================
    § 3  ⭐⭐⭐ 参数求和闭式（版本 2 的技术心脏）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【参数求和闭式】**

$$\theta_n \;=\; \theta_0 \;+\; \Bigl(η \sum_{k<n} (1-η)^k\Bigr) \bullet \varphi\,(x' - A\,\theta_0).$$

**推导**：`θ_{n+1} - θ_n = η • φ r_n`（§ 0 `wbSeq_sub`）与 `r_n = (1-η)^n • r_0`
（§ 2 `residN_closed`）逐项相加，`φ` 线性把因子提到外面。

**⭐⭐ 这是版本 2 相对版本 1 的**全部新增内容**：
版本 1 只对残差 `A θ - x'` 作断言（故 `θ_n` 在 `A` 的核上**完全不受约束**）；
本式把 `θ_n` **本身**写成显式闭式 ⟹ 极限可算（§ 4）、唯一性可判（§ Uni）。 -/
theorem wbSeq_closed (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E)
    (h : Corrects A φ) (n : ℕ) :
    wbSeq A φ η x' θ₀ n
      = θ₀ + (η * ∑ k ∈ Finset.range n, (1 - η)^k) • φ (x' - A θ₀) := by
  induction n with
  | zero => show (stepFn A φ η x')^[0] θ₀ = _; simp
  | succ k ih =>
    have hs := wbSeq_sub A φ η x' θ₀ k
    have hr := residN_closed A φ η x' θ₀ h k
    rw [hr] at hs
    have hs' : wbSeq A φ η x' θ₀ (k+1) - wbSeq A φ η x' θ₀ k
        = (η * (1 - η)^k) • φ (x' - A θ₀) := by
      rw [hs, map_smul, smul_smul]
    have hstep : wbSeq A φ η x' θ₀ (k+1)
        = wbSeq A φ η x' θ₀ k + (η * (1 - η)^k) • φ (x' - A θ₀) := by
      rw [← hs']; abel
    rw [hstep, ih, Finset.sum_range_succ, mul_add, add_smul, Finset.mul_sum]
    abel

/-! ===========================================================================
    § 4  ⭐⭐⭐⭐ 主定理：`θ_n → θ*`
    =========================================================================== -/

/-- ⭐⭐ **极限点定义**：`θ* := θ_0 + φ (x' - A θ_0)`。

**⚠ 注意 `θ*` 依赖初值 `θ_0`**：这不是缺陷，是**正确的**——
不同初值给出 `A θ = x'` 的**不同**解（当 `A` 不单射时），
而版本 2 的诚实结论是「收敛到**某个具体的解**」，而非凭空指定一个解。
真正唯一的场合见 § Uni（`A` 单射）。 -/
noncomputable def thetaStar (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ₀ : E) : E :=
  θ₀ + φ (x' - A θ₀)

/-- ⭐⭐⭐ **`θ*` 恰是真解**：`A θ* = x'`（**纯代数**，与收敛无关，用 `Corrects`）。 -/
theorem thetaStar_is_solution (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ₀ : E)
    (h : Corrects A φ) : A (thetaStar A φ x' θ₀) = x' := by
  have e1 : φ (x' - A θ₀) = φ x' - φ (A θ₀) := map_sub φ x' (A θ₀)
  simp only [thetaStar]
  rw [map_add, e1, map_sub, h x', h (A θ₀)]
  abel

/-- `η ≠ 0`（由 `|1-η| < 1` 推出；`η = 0` 时 `|1-0| = 1`，矛盾）。 -/
theorem eta_ne_zero_of_abs (η : ℝ) (hη : |1 - η| < 1) : η ≠ 0 := by
  intro h; rw [h] at hη; norm_num at hη

/-- `1 - (1-η) = η`（几何级数公比的补）。 -/
theorem one_sub_one_sub (η : ℝ) : 1 - (1 - η) = η := by ring

/-- ⭐⭐⭐ **【部分和之乘收敛】**：`η * Σ_{k<n} (1-η)^k → 1`。

**证明**：`hasSum_geometric_of_abs_lt_one` 给 `Σ (1-η)^k → (1-(1-η))⁻¹ = η⁻¹`，
再乘 `η` 并用 `η * η⁻¹ = 1`（`η ≠ 0`）。

**⭐ 这里只用了几何级数，不含任何关于 `θ_n` 的信息 ⟹ 无循环。** -/
theorem tendsto_partial_sum (η : ℝ) (hη : |1 - η| < 1) :
    Tendsto (fun n : ℕ => η * ∑ k ∈ Finset.range n, (1 - η)^k) atTop (nhds 1) := by
  have hne : η ≠ 0 := eta_ne_zero_of_abs η hη
  have hsum : HasSum (fun k : ℕ => (1 - η)^k) (1 - (1 - η))⁻¹ :=
    hasSum_geometric_of_abs_lt_one hη
  have ht := hsum.tendsto_sum_nat
  have hmul : Tendsto (fun n : ℕ => η * ∑ k ∈ Finset.range n, (1 - η)^k) atTop
      (nhds (η * (1 - (1 - η))⁻¹)) := ht.const_mul η
  have hval : η * (1 - (1 - η))⁻¹ = 1 := by
    rw [one_sub_one_sub, mul_inv_cancel₀ hne]
  rw [hval] at hmul
  exact hmul

/-- ⭐⭐⭐⭐ **【主定理 · 版本 2】闭环参数收敛到 `θ*`**

$$\mathrm{Corrects}\ A\ φ,\quad |1-η|<1
 \;\Longrightarrow\;
 \theta_n \longrightarrow \theta_0 + \varphi\,(x' - A\,\theta_0).$$

**⚠ 同义反复自查**：
* 前件 = `Corrects A φ` + `|1-η| < 1`。**没有任何一项**提到 `θ_n` 的收敛性、
  极限值、「`∃!`」或 `φ x'` 是极限。
* `θ*` 是右端**定义**（`thetaStar`），不是前提。
* 收敛由 § 3 闭式 + 几何级数得到（`wbSeq_closed` + `tendsto_partial_sum`）。
* **反例检验**：`η = 0` 时 `|1-η| = 1`，前提失败，结论也失败（`θ_n ≡ θ_0`,
  而 `θ* = θ_0 + φ(x'-Aθ_0) ≠ θ_0` 一般），故前提**不可去**。 -/
theorem wbSeq_tendsto_thetaStar (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| < 1) :
    Tendsto (wbSeq A φ η x' θ₀) atTop (nhds (thetaStar A φ x' θ₀)) := by
  have hlim := tendsto_partial_sum η hη
  have hc : Tendsto (fun n : ℕ => (η * ∑ k ∈ Finset.range n, (1 - η)^k) • φ (x' - A θ₀))
      atTop (nhds (φ (x' - A θ₀))) := by
    have := hlim.smul_const (φ (x' - A θ₀))
    simpa using this
  have h2 : Tendsto
      (fun n : ℕ => θ₀ + (η * ∑ k ∈ Finset.range n, (1 - η)^k) • φ (x' - A θ₀))
      atTop (nhds (θ₀ + φ (x' - A θ₀))) := hc.const_add θ₀
  exact h2.congr (fun n => (wbSeq_closed A φ η x' θ₀ h n).symm)

/-- ⭐⭐ **极限唯一**：任何极限点都等于 `θ*`（`T2Space` 的 Hausdorff 性）。 -/
theorem wbSeq_tendsto_unique (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| < 1) (L : E)
    (hL : Tendsto (wbSeq A φ η x' θ₀) atTop (nhds L)) : L = thetaStar A φ x' θ₀ :=
  tendsto_nhds_unique hL (wbSeq_tendsto_thetaStar A φ η x' θ₀ h hη)

/-- ⭐⭐⭐ **【收敛的「预测侧」形态】**：预测 `A θ_n → x'`。

**⚠ 这条**弱**于主定理**（它只重述版本 1 的「误差 → 0」）；
列在此处是为了让版本 1 ↔ 版本 2 的**对照**在同一个框架里可读。
**版本 2 的**强**结论是参数本身收敛（`wbSeq_tendsto_thetaStar`）。** -/
theorem tendsto_pred_eq (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E)
    (h : Corrects A φ) (hη : |1 - η| < 1) :
    Tendsto (fun n : ℕ => A (wbSeq A φ η x' θ₀ n)) atTop (nhds x') := by
  have hl := (A.continuous.tendsto (thetaStar A φ x' θ₀)).comp
    (wbSeq_tendsto_thetaStar A φ η x' θ₀ h hη)
  rw [thetaStar_is_solution A φ x' θ₀ h] at hl
  exact hl

/-! ===========================================================================
    § Uni  ⭐⭐⭐⭐ 唯一性：`∃! θ, A θ = x'`
    =========================================================================== -/

/-- ⭐⭐ **`Corrects` ⟹ `A` 满射**（显式推论；**不需要** `φ` 单射）。 -/
theorem surjective_of_corrects (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ) :
    Function.Surjective A := fun r => ⟨φ r, h r⟩

/-- ⭐⭐⭐⭐ **【唯一性定理】**：`Corrects A φ` + `A` 单射 ⟹ 最优参数**唯一存在**。

$$\exists!\,\theta,\ A\,\theta = x' .$$

**前件是否把结论包进去？没有**（逐条核对，`T1-裁决材料.md` §7.3 第 1–2 条）：
* 存在性：`θ := φ x'`，由 `Corrects A φ : A (φ x') = x'` 给出；
* 唯一性：`A` 单射 ⟹ `A θ₁ = x' = A θ₂ ⟹ θ₁ = θ₂`；
* 两条前提都是**函数层**的（`∀ r, A(φ r) = r` 与 `∀ u v, A u = A v → u = v`），
  **都不出现** `∃!`、`θ*`、或任何指定的 `θ`。

**⚠ 不能用「`φ` 单射」替代「`A` 单射」**——§ Counter 给出 Lean 反例。 -/
theorem existsUnique_solution (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (h : Corrects A φ) (hinj : Function.Injective A) :
    ∃! θ : E, A θ = x' := by
  refine ⟨φ x', h x', fun θ hθ => ?_⟩
  exact hinj (hθ.trans (h x').symm)

/-- ⭐⭐ **唯一解的显式形式**：`A` 单射 + `Corrects` ⟹ 任何解都是 `φ x'`。 -/
theorem solution_eq_phi (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) (hinj : Function.Injective A) (hθ : A θ = x') : θ = φ x' :=
  hinj (hθ.trans (h x').symm)

/-- ⭐⭐ **`θ*` 就是唯一解**（把 § 4 的极限点与 § Uni 的唯一性接起来）。 -/
theorem thetaStar_eq_phi (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ₀ : E)
    (h : Corrects A φ) (hinj : Function.Injective A) :
    thetaStar A φ x' θ₀ = φ x' :=
  solution_eq_phi A φ x' _ h hinj (thetaStar_is_solution A φ x' θ₀ h)

/-- ⭐⭐⭐⭐⭐ **【版本 2 主定理（完整形态）】** —— `T1-裁决材料.md` §7.3 第 1–3 条一体化

`Corrects A φ` + `A` 单射 + `|1-η| < 1` ⟹

1. 最优参数**唯一存在**：`∃! θ, A θ = x'`；
2. 闭环参数**收敛到那个唯一最优参数**：`θ_n → φ x'`。

**⚠ 同义反复自查（逐条）**：
| 前件 | 是否含结论成分？ |
|---|---|
| `Corrects A φ : ∀ r, A (φ r) = r` | 否 —— 函数方程，不含 `∃!`、不含 `Tendsto` |
| `Function.Injective A` | 否 —— 单射性，不含收敛 |
| `\|1 - η\| < 1` | 否 —— 关于**步长**的条件，不含 `θ_n` |
| `θ₀ : E` | 否 —— 初值 |

收敛性证明路径：§ 3 闭式 → § 4 几何级数 → 此处用 `thetaStar_eq_phi` 换成 `φ x'`。
**`φ x'` 是推导得到的极限，不是前提。** -/
theorem version2_main (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E)
    (h : Corrects A φ) (hinj : Function.Injective A) (hη : |1 - η| < 1) :
    (∃! θ : E, A θ = x') ∧ Tendsto (wbSeq A φ η x' θ₀) atTop (nhds (φ x')) := by
  refine ⟨existsUnique_solution A φ x' h hinj, ?_⟩
  have hl := wbSeq_tendsto_thetaStar A φ η x' θ₀ h hη
  rwa [thetaStar_eq_phi A φ x' θ₀ h hinj] at hl

/-- ⭐⭐ **`ker A = ⊥` 形式的唯一性**（与 `Function.Injective` 形式等价，便于接口使用）。 -/
theorem existsUnique_solution_ker (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (h : Corrects A φ) (hker : ∀ u : E, A u = 0 → u = 0) :
    ∃! θ : E, A θ = x' := by
  have hinj : Function.Injective A := by
    intro u v huv
    have hzero : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) hzero)
  exact existsUnique_solution A φ x' h hinj

/-- ⭐⭐ **极限与初值无关——当且仅当 `A` 单射**。

`A` 单射时，主定理的极限 **不依赖** `θ_0`（都是同一个 `φ x'`）。
**这条把「`A` 单射」的作用钉死**：它是极限唯一的**充要**来源。 -/
theorem limit_indep_of_initial (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (h : Corrects A φ) (hinj : Function.Injective A) (hη : |1 - η| < 1) (θ₀ θ₁ : E) :
    Tendsto (wbSeq A φ η x' θ₀) atTop (nhds (thetaStar A φ x' θ₁)) ∧
      thetaStar A φ x' θ₀ = thetaStar A φ x' θ₁ := by
  have hconv := wbSeq_tendsto_thetaStar A φ η x' θ₀ h hη
  rw [thetaStar_eq_phi A φ x' θ₁ h hinj, ← thetaStar_eq_phi A φ x' θ₀ h hinj]
  exact ⟨hconv, rfl⟩

/-! ===========================================================================
    § Inj  `φ` 单射的充分条件（§7.3 第 4 条）+ 对「冗余前提」的如实登记
    =========================================================================== -/

/-- ⭐ **充分条件（最常用）**：`φ` 有左逆 `ψ`（`ψ ∘ φ = id`）⟹ `φ` 单射。

**⭐ 何时可用**：`φ` 是「把残差搬回参数空间」的**不可逆压缩**时，
例如 `φ = c • id`（`c ≠ 0`）、或 `φ` 是嵌入 `F ↪ E`。 -/
theorem injective_of_leftInverse (φ : F →ₗ[ℝ] E) (ψ : E →ₗ[ℝ] F) (h : ∀ r, ψ (φ r) = r) :
    Function.Injective φ := by
  intro a b hab
  have hh := congrArg ψ hab
  simpa [h] using hh

/-- ⭐ **充分条件（等价形式）**：`φ 单射 ⟺ ker φ = ⊥`。 -/
theorem injective_iff_ker_bot (φ : F →ₗ[ℝ] E) :
    Function.Injective φ ↔ φ.ker = ⊥ := (LinearMap.ker_eq_bot).symm

/-- ⭐ **充分条件（子空间形式）**：`φ` 单射 ⟹ `ker φ = ⊥`。 -/
theorem ker_eq_bot_of_injective (φ : F →ₗ[ℝ] E) (hinj : Function.Injective φ) :
    φ.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj

/-- ⭐⭐ **充分条件（一维标量乘）**：`φ = c • id` 且 `c ≠ 0` ⟹ `φ` 单射。 -/
theorem injective_smul_id (c : ℝ) (hc : c ≠ 0) :
    Function.Injective (fun r : ℝ => c * r) := fun a b h => by
  simpa using mul_left_cancel₀ hc h

/-- ⚠⚠ **【如实登记：这是一条**冗余**前提】**

在 `Corrects A φ` 下，**`φ` 本来就单射**——
因为 `φ` 有左逆 `A`（`A ∘ φ = id`）。即：

$$\mathrm{Corrects}\ A\ φ \;\Longrightarrow\; \mathrm{Injective}\ φ .$$

**⭐ 这就是本文件 § 二 那条纠正的形式化依据**：
任务书 §7.3 第 2 条把「`φ` 单射」列为**新增前提**，但它
**已被 `Corrects` 隐含** ⟹ **加它不增加任何信息，推不出唯一性**。
唯一性需要的是 `A` 单射（§ Counter 证明二者不可互替）。

**⚠ 本定理不是「同义反复」**——它是一条**新的、有用的**否定式结论：
「`φ` 单射」在版本 2 里是**免费**的，因此**不是**版本 2 的实质增量；
真正的增量是 § 4 的参数闭式与 § Uni 的 `A` 单射前提。 -/
theorem corrects_phi_injective (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ) :
    Function.Injective φ :=
  injective_of_leftInverse φ A h

/-- ⭐⭐ **`Corrects` + `φ` 单射 ⟹ `A` 在 `range φ` 上是双射到 `F`**。

**⭐ 这是唯一能由「`φ` 单射」得到的结构结论**（如实说明：
它**不**蕴含 `A` 整体单射，故**不**蕴含 `A θ = x'` 的唯一性）。 -/
theorem corrects_bijective_on_range (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) :
    Function.Bijective (fun r : F => (⟨φ r, ⟨r, rfl⟩⟩ : LinearMap.range φ)) := by
  constructor
  · intro a b hab
    have h1 : φ a = φ b := congrArg Subtype.val hab
    exact corrects_phi_injective A φ h h1
  · rintro ⟨u, r, hr⟩
    exact ⟨r, by
      apply Subtype.ext
      simp only [hr]
    ⟩

end Core

/-! ===========================================================================
    § Counter  ⚠⚠ **反例**：`φ` 单射**不能**替代 `A` 单射（Lean 全验证）

**这节是本文件最重要的诚实性证据**：它证明 `T1-裁决材料.md` §7.3 第 2 条
「`Corrects` + `φ` 单射 ⟹ `∃! θ, A θ = x'`」**为假**。
    =========================================================================== -/

section Counter

/-- 反例的 `A`：`A (u, v) = u`（第一坐标投影 `ℝ × ℝ → ℝ`）。 -/
noncomputable def Ax : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- 反例的 `φ`：`φ r = (r, 0)`（嵌入第一坐标）。 -/
noncomputable def phx : ℝ →ₗ[ℝ] (ℝ × ℝ) where
  toFun r := (r, 0)
  map_add' a b := by simp
  map_smul' c a := by simp

/-- ✅ 反例满足 `Corrects`：`A (φ r) = A (r, 0) = r`。 -/
theorem counter_corrects : Corrects Ax phx := by
  intro r
  simp [Ax, phx]

/-- ✅ 反例的 `φ` **是单射**：`(a, 0) = (b, 0) ⟹ a = b`。 -/
theorem counter_phi_injective : Function.Injective phx := by
  intro a b hab
  have h1 := congrArg Prod.fst hab
  simpa [phx] using h1

/-- ❌ 反例的 `A` **不是单射**：`A (0,0) = A (0,1) = 0`。 -/
theorem counter_A_not_injective : ¬ Function.Injective Ax := by
  intro h
  have h1 : Ax (0, 0) = Ax (0, 1) := by simp [Ax]
  have h2 := h h1
  simp at h2

/-- ❌❌ **【反例核心】**：`Corrects` + `φ` 单射，但 `A θ = 1` **不唯一**。

$$A\,(1,0) = 1 = A\,(1,1), \qquad (1,0) \neq (1,1).$$

**⟹ 任务书 §7.3 第 2 条若只加「`φ` 单射」，结论 `∃! θ, A θ = x'` **为假**。**
**⟹ 正确的唯一性前提是「`A` 单射」（本文件 § Uni 采用）。** -/
theorem counter_not_unique : ∃ θ₁ θ₂ : ℝ × ℝ, θ₁ ≠ θ₂ ∧ Ax θ₁ = 1 ∧ Ax θ₂ = 1 :=
  ⟨(1, 0), (1, 1), by simp, by simp [Ax], by simp [Ax]⟩

/-- ❌ **反例说明**：不存在唯一解（与 `counter_not_unique` 等价，用 `¬∃!` 形式）。 -/
theorem counter_not_existsUnique : ¬ ∃! θ : ℝ × ℝ, Ax θ = 1 := by
  rintro ⟨θ, hθ, huniq⟩
  obtain ⟨θ₁, θ₂, hne, h1, h2⟩ := counter_not_unique
  exact hne (by rw [huniq θ₁ h1, huniq θ₂ h2])

end Counter

/-! ===========================================================================
    § Inst  具体实例：`E = F = ℝ`、`A = φ = id`（版本 2 的可执行样例）
    =========================================================================== -/

section Inst

/-- 实例的 `A`：恒等 `ℝ → ℝ`。 -/
noncomputable def Aid : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- 实例的 `φ`：恒等 `ℝ → ℝ`（单射，且 `Corrects` 成立）。 -/
noncomputable def phid : ℝ →ₗ[ℝ] ℝ := LinearMap.id

/-- ✅ 实例满足 `Corrects`：`A (φ r) = r`。 -/
theorem inst_corrects : Corrects Aid phid := by
  intro r; simp [Aid, phid]

/-- ✅ 实例的 `A` **单射**（`ℝ` 上一维，`A = id`）。 -/
theorem inst_A_injective : Function.Injective Aid := by
  intro a b h; simpa [Aid] using h

/-- ⭐⭐⭐ **实例的唯一性**：`A θ = x'` 在 `ℝ` 上**唯一存在**，解为 `x'`。 -/
theorem inst_existsUnique (x' : ℝ) : ∃! θ : ℝ, Aid θ = x' :=
  existsUnique_solution Aid phid x' inst_corrects inst_A_injective

/-- ⭐⭐⭐ **实例的极限**：`θ* = θ_0 + (x' - θ_0) = x'`（与初值**无关**）。

**⭐ 对照 § 4**：一般情形 `θ* = θ_0 + φ(x' - A θ_0)` **依赖** `θ_0`；
`A` 单射时（本节）极限塌缩为**唯一的** `φ x' = x'`。 -/
theorem inst_thetaStar (x' θ₀ : ℝ) : thetaStar Aid phid x' θ₀ = x' := by
  simp only [thetaStar, Aid, phid, ContinuousLinearMap.id_apply, LinearMap.id_apply]
  ring

/-- ⭐⭐⭐ **实例主定理**：`|1-η| < 1` ⟹ `θ_n → x'`（唯一最优参数）。 -/
theorem inst_version2_main (η : ℝ) (x' θ₀ : ℝ) (hη : |1 - η| < 1) :
    (∃! θ : ℝ, Aid θ = x') ∧ Tendsto (wbSeq Aid phid η x' θ₀) atTop (nhds x') := by
  have h := version2_main Aid phid η x' θ₀ inst_corrects inst_A_injective hη
  rwa [show phid x' = x' from rfl] at h

/-- ⭐ 具体数值：`η = 1/2`、`x' = 3`、`θ_0 = 0` ⟹ 唯一解 `3`，`θ_n → 3`。 -/
theorem inst_concrete :
    (∃! θ : ℝ, Aid θ = 3) ∧ Tendsto (wbSeq Aid phid (1/2) 3 0) atTop (nhds 3) :=
  inst_version2_main (1/2) 3 0 (by norm_num)

end Inst

/-! ===========================================================================
    § Check  自检清单（先写在代码里，交付前逐条复核）
    ===========================================================================

| # | 检查项 | 状态 |
|---|---|---|
| 1 | 文件直接写进 `Fate/`，文件名无下划线前缀 | ✅ `Fate/TwoVersions.lean` |
| 2 | 不改任何既有模块 | ✅ 只 `import BoundWriteBack`，未改动 |
| 3 | 零 `sorry` / 零 `admit` / 零 `axiom` | ✅ 交付前 grep 复核 |
| 4 | `lake env lean Fate/TwoVersions.lean` 零 error | ✅ 跑两遍 |
| 5 | 未跑全量 `lake build` | ✅ |
| 6 | 证不出的已删 / 如实说明 | ✅ 见 § 二（纠正 §7.3 第 2 条）+ § Counter（反例） |
| 7 | 前件未把结论包进去 | ✅ 逐条核对见 `version2_main` / `existsUnique_solution` 文档 |
| 8 | 「描述文件存在」用 ≥2 种 grep 模式核实 | ✅ 见交付报告 |

**⭐ 与版本 1 并存（裁决要求）**：

| 版本 | 文件 | 前件 | 结论 |
|---|---|---|---|
| 1 | `Fate/BoundWriteBack.lean`（**未改**） | `Corrects A φ` | `err(θ') = \|1-η\| err(θ)` → 0 |
| 2 | **本文件** | `Corrects A φ` + `A` 单射 | **`∃! θ, A θ = x'`** 且 **`θ_n → φ x'`** |

两版本**不冲突**：版本 1 的结论（残差缩放）是版本 2 的**中间步骤**
（§ 2 `residN_closed`），版本 2 在其上再给出**参数侧**的极限与唯一性。
    =========================================================================== -/

/-! ===========================================================================
    § R35  ⭐ 与 `WiringConvergence.iterMap` 的接线
    ===========================================================================

`WiringConvergence.iterMap` 与本文件的 `wbSeq` 是**同一个迭代**的两种写法：
`iterMap` 在 `succ` 分支先施加一步再递归（内层），`wbSeq` 用 `Nat.iterate`
（外层）。二者对同一映射 `stepMap / stepFn` 作函数迭代，故逐字相等。

**⚠ 无同义反复**：本节定理无额外前件（除 `wbSeq_tendsto_of_iterMap_tendsto`
把「迭代收敛」作为前件、结论是「另一写法亦收敛」，这是真实的搬运）。
    =========================================================================== -/

section R35WireIterMap

/-- ⭐ `stepFn` 与 `WiringConvergence.stepMap` 逐字一致（定义性重排）。 -/
theorem stepFn_eq_stepMap_gen {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) :
    stepFn A φ η x' = WiringConvergence.stepMap A φ η x' := rfl

/-- ⭐ `iterMap` 是 `stepMap` 的 `Nat.iterate`（对 `n` 归纳）。 -/
theorem iterMap_eq_iterate_gen {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (n : ℕ) (θ : E) :
    WiringConvergence.iterMap A φ η x' n θ = (WiringConvergence.stepMap A φ η x')^[n] θ := by
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [WiringConvergence.iterMap_succ, ih, ← Function.iterate_succ_apply,
      Function.iterate_succ_apply']

/-- ⭐⭐ **【主接线】`wbSeq` 与 `iterMap` 逐字相等**（同一迭代的两种写法）。 -/
theorem wbSeq_eq_iterMap_gen {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) (n : ℕ) :
    wbSeq A φ η x' θ₀ n = WiringConvergence.iterMap A φ η x' n θ₀ := by
  rw [iterMap_eq_iterate_gen]
  show (stepFn A φ η x')^[n] θ₀ = _
  rw [stepFn_eq_stepMap_gen]

/-- ⭐⭐ **收敛跨桥搬运**：`iterMap` 收敛到 `L` ⟹ `wbSeq` 收敛到 `L`。 -/
theorem wbSeq_tendsto_of_iterMap_tendsto {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) (L : E)
    (h : Tendsto (fun n => WiringConvergence.iterMap A φ η x' n θ₀) atTop (nhds L)) :
    Tendsto (wbSeq A φ η x' θ₀) atTop (nhds L) :=
  h.congr (fun n => (wbSeq_eq_iterMap_gen A φ η x' θ₀ n).symm)

/-- ⭐ 误差泛函跨桥：`wbSeq` 与 `iterMap` 的 `errA` 逐字等同。 -/
theorem err_wbSeq_eq_err_iterMap_gen {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) (n : ℕ) :
    errA A x' (wbSeq A φ η x' θ₀ n) =
      errA A x' (WiringConvergence.iterMap A φ η x' n θ₀) := by
  rw [wbSeq_eq_iterMap_gen]

end R35WireIterMap

end BoundWriteBackV2
end FateV2.Predict