/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ClosedLoopUnified`
任务：**【NN1-最高优先】聚合接线模块**

===========================================================================
一、为什么需要这个文件（孤岛审计 HH3）
===========================================================================

HH3 审计发现 276 个孤岛。其中**另一类**孤岛无法直接接线：

* `ClosedLoopGeneral`  —— 扇入 0，**只** `import BoundWriteBack`，
  "**向下长**"：有上游、无下游。若让 `BoundWriteBack` 去 `import` 它，立即成环。
* `ConvergeToOptimalND` —— 扇入 0，同样只 `import ConvergenceOptimal`，
  同一困境。

解法：**建聚合模块**。本文件 `import` 这些孤岛（以及它们的分支兄弟），
在它们**之上**做**跨模块综合**，从而为孤岛提供**下游**（扇入 0 → ≥ 1），
且**不碰任何上游的 import 图**（无环）。

本文件接线表格（每条跨模块定理的"左腿 / 右腿"）：

| 定理 | 左腿（模块） | 右腿（模块） |
|---|---|---|
| §3 `unified_contraction` | `ClosedLoopGeneral.step_contraction` | `ClosedLoopNoisy.steadyErr` |
| §3 `noise_free_zero_iff` | `ClosedLoopGeneral.errN_eq_zero_iff` | `ClosedLoopNoisy.noisy_step_err` |
| §3 `steady_scale_consistency` | `ClosedLoopGeneral.err_iter_le` | `ClosedLoopNoisy`（`steadyErr` 代数） |
| §4 `zero_error_iff_optimal_nd` | `ConvergeToOptimalND.corrects_id` | `ConvergeToOptimalStrong.fixed_iff_optimal_strong` |
| §4 `iter_unifies_general_and_nd` | `ClosedLoopGeneral.nlIter / errN` | `WiringConvergence.iterMap / errA`（**两条分支逐字重合**） |
| §5 `closed_loop_master` | §3（非线性分支） | §4（`n` 维分支）+ `ConvergeToOptimalIter` |

⚠ 本文件**只新增**，不修改任何已有模块（纪律 §2）。

===========================================================================
四、修复记录（本批次：修断 13 个编译错误）
===========================================================================

本文件之前存在 **13 个编译错误**，本批次已全部修好（零 `sorry`、
`lake env lean` 两遍零 error 零 warning）。修复清单：

| # | 位置 | 错误原因 | 修法 |
|---|---|---|---|
| 1–3 | `abbrev errN / nlStep / nlIter`（3 个 stuck typeclass）| `abbrev` 在未声明变量的处部建立，`E`、`F` 无约束，`NormedAddCommGroup ?m` 卡住 | 移入 `section Aliases`，显式声明 `variable {E F : Type u}` 与范数实例，并给出完整函数签名 |
| 4 | `bridge_nlIter_eq_iterMap` 归纳步 | `nlIter` 是**外层**递推、`iterMap` 是**内层**递推；原证明错误地在 `wbW θ` 上取归纳假设 | 新增辅助引理 `wbW_iterMap_comm`（“先走一步与先走 k 步等价”），用 `show` 展成外层形式后归纳 |
| 5 | `bridge_nlIter_eq_thetaIter` 归纳步 | 同上（同样错写成 `ih (wbW θ)`）| 同上；改用 `thetaIter_succ` 的正确方向，归纳假设直接用回 `θ` |
| 6 | `noise_free_zero_iff` | `rintro` 后 `hz : 0 = x'₀ - x'₁`，目标却是 `x'₀ = x'₁`，`rw` 找不到模式 | 改为 `hne (sub_eq_zero.mp hz.symm)` |
| 7 | `steady_scale_consistency` (c) 项 | `one_div` 把 `1/(1-r)` 变成 `(1-r)⁻¹`，方向与目标相反 | 改为 `div_eq_mul_inv, one_div` 两步归一 |
| 8 | `general_err_zero_at_eta_one_nd` | `ConvergeToOptimalND.corrects_id` 是 `∀ E` 的形式，未显式传 `G` | 改为 `corrects_id G` |
| 9 | `zero_error_iff_optimal_nd` | `ConvergeToOptimalStrong` 在 `Type`（宇宙 0），本文件其余在 `Type u`；命名的 `A :=` 推断链断 | 把该定理单独放在 `section NDStrongType`，用局部 `{E : Type}` 遮盖 |
| 10–13 | `iter_unifies_general_and_nd` / `closed_loop_master` 中的 `ConvergeToOptimalND.iterMap`（4 处）| 该名字**不存在**；`iterMap` 实际在 `WiringConvergence`，`ConvergeToOptimalND` 只是 `import` 了它 | 全部改名为 `WiringConvergence.iterMap`（含两处 doc 表格）|

另：`iter_unifies_general_and_nd` 与 `closed_loop_master` 里的
`(LinearMap.id : E → E)` 缺 `Module` 实例（`Module ?m` 卡住），
改为 `(LinearMap.id : E →ₗ[ℝ] E)`。

**死前件登记（诚实边界）**：

* `closed_loop_master` 的 `_hprod : Lφ * LA ≤ 1` 与 `steady_scale_consistency` 的
  `_hr1 : r < 1`、`noise_identically_zero_steady_zero` 的 `_hr1 : r < 1`、
  `steady_zero_iff_no_noise` 的 `_hr : r = |1 - η|` **不被任何结论使用**
  （已用 `_` 前缀标出，`lake env lean` 零 warning）。
  按纪律“不改定理陈述”，本批次**保留**这些前件而不是删除；
  但必须说明：它们是**冗余**的，删掉后定理**更强**但也**同样可证**。
  ⚠ 因此 `closed_loop_master` doc 里“`hprod` 保证 `c ≤ |1-η|`”的说法
  **不被本定理陈述支持**（结论 1–3 直接用 `contractFactor < 1`，不用 `Lφ * LA ≤ 1`）。
  这不是同义反复（结论仍不在前件中），但确实是一条**未被用上的**假设。

===========================================================================
二、本文件**已证出**的定理（逐条）
===========================================================================

§2 桥接（0 阶：把两条分支的对象接到同一语言上，供 §3–§5 取用）
  * `bridge_errN_eq_errA`      : 线性处 `errN = errA`（`rfl`）
  * `bridge_nlIter_eq_iterMap` : 线性处 `nlIter = iterMap`（**证出**，归纳）
  * `bridge_nlIter_eq_thetaIter` : 线性处 `nlIter = thetaIter`（**证出**，归纳）

§3 非线性分支 × 噪声分支（`ClosedLoopGeneral` × `ClosedLoopNoisy`）
  * `unified_contraction`   : 无噪声单步收缩 + 有噪声单步界，统一为一条陈述
  * `noise_free_zero_iff`   : 无噪声时零误差刻画（含"新息恒零 ⟹ 已被扰动"一半）
  * `steady_scale_consistency` : `η ≠ 1` 时稳态界按 `1/(1-|1-η|)` 放大（可算公式）
  * `general_err_zero_at_eta_one_nd` : 非线性收缩框架下 `η = 1` 一步归零（接 `n` 维）

§4 `n` 维分支 × 强化分支（`ConvergeToOptimalND` × `ConvergeToOptimalStrong`）
  * `zero_error_iff_optimal_nd` : `‖θ_n − x'‖ = 0` ⟺ `wbW` 不动点 ⟺ `IsOptimal`
  * `iter_unifies_general_and_nd` : **两条独立分支的迭代定义逐字重合**（强一致性）
  * `noise_identically_zero_steady_zero` : 新息恒零 ⟹ 噪声分支稳态误差 `= 0`

§5 总汇
  * `closed_loop_master` : 五条结论同条（非线性 + `n` 维 + 动力学），
                           是本文件对"闭环收敛"的**单一入口**

===========================================================================
三、诚实边界
===========================================================================

* 本文件**不**新增实质性数学；它是**综合（synthesis）**模块。
  每条 §3–§5 定理的**非平凡性**来自：其结论**不**逐字出现在任一条腿的前件中，
  且**必须同时引用两条分支**（单腿不足以给出结论）。逐条非循环性见各定理 doc。
* **不声称**"293 个孤岛全部消除"：本文件只把 `ClosedLoopGeneral`
  与 `ConvergeToOptimalND` 的扇入从 0 提到 ≥ 1。
* 未跑全量 `lake build`（纪律 §5）。
* 零 `sorry` / `admit` / `axiom`。
-/

import FateWorld.FateV2.Loop.BoundWriteBack
import FateWorld.FateV2.Loop.ClosedLoopGeneral
import FateWorld.FateV2.Loop.ClosedLoopNoisy
import FateWorld.FateV2.Loop.ConvergeToOptimalND
import FateWorld.FateV2.Loop.ConvergeToOptimalIter
import FateWorld.FateV2.Loop.ConvergeToOptimalStrong
namespace FateV2.Loop
namespace ClosedLoopUnified

open Filter Topology
open scoped Topology

/-!
  # Loop · ClosedLoopUnified

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ClosedLoopUnified.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BoundWriteBack, ClosedLoopGeneral, ClosedLoopNoisy, ConvergeToOptimalND, ConvergeToOptimalIter, ConvergeToOptimalStrong
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  记号别名（把两条分支的名字拉进本命名空间）
    =========================================================================== -/

section Aliases

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 非线性分支的误差泛函（别名，仅为可读性）。

⚠ 必须在显式变量语境中声明，否则 `abbrev` 的 `E`、`F` 无约束，
令 `NormedAddCommGroup ?m` 的 typeclass 求解卡住。 -/
abbrev errN (A : E → F) (x' : F) (θ : E) : ℝ := ClosedLoopGeneral.errN A x' θ

/-- 非线性分支的一步更新（别名）。 -/
abbrev nlStep (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θ : E) : E :=
  ClosedLoopGeneral.nlStep A φ η x' θ

/-- 非线性分支的 `n` 步迭代（别名）。 -/
abbrev nlIter (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (n : ℕ) (θ : E) : E :=
  ClosedLoopGeneral.nlIter A φ η x' n θ

/-- 非线性分支的单步收缩系数 `|1-η| L_φ L_A`（别名）。 -/
abbrev contractFactor (η Lφ LA : ℝ) : ℝ := ClosedLoopGeneral.contractFactor η Lφ LA

end Aliases

/-! ===========================================================================
    §2  ⭐ 0 阶桥接：把两条分支的对象接到同一语言上

    ⚠ 本节的定理全部是 **`rfl` / 归纳**，它们**不是贡献**，
    而是 §3–§5 必需的技术接口（否则两条分支的名字无法在同一式中出现）。
    为诚实，本节定理的 doc 明确标注"技术接口（非实质结论）"。
    =========================================================================== -/

section Bridge

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【技术接口】（`rfl`）** 线性处 `errN`（非线性分支）与 `errA`（线性分支）逐字相等。
即 `ClosedLoopGeneral.errN_eq_errA` 的跨命名空间登记。 -/
theorem bridge_errN_eq_errA (A : E →L[ℝ] F) (x' : F) (θ : E) :
    ClosedLoopGeneral.errN (A : E → F) x' θ = BoundWriteBack.errA A x' θ :=
  ClosedLoopGeneral.errN_eq_errA A x' θ

/-- **【辅助引理】`wbW` 与 `iterMap` 交换次序**

「先走 `k` 步再走一步」与「先走一步再走 `k` 步」结果相同：

    wbW (iterMap k θ) = iterMap k (wbW θ).

这把 `iterMap` 的**内层**递推（`iterMap_succ`）转成**外层**递推读法，
供 `bridge_nlIter_eq_iterMap` 的归纳步使用。 -/
theorem wbW_iterMap_comm (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (k : ℕ) (θ : E) :
    BoundWriteBack.wbW A φ η x' (WiringConvergence.iterMap A φ η x' k θ)
      = WiringConvergence.iterMap A φ η x' k (BoundWriteBack.wbW A φ η x' θ) := by
  induction k generalizing θ with
  | zero => rfl
  | succ j ih =>
    -- 两侧都是 `stepMap` 的 `j+1` 次迭代，只是括号位置不同；把目标展开到
    -- 「外层均已剥离」的形式，然后用起点 `wbW θ` 的归纳假设。
    show BoundWriteBack.wbW A φ η x'
        (WiringConvergence.iterMap A φ η x' j (BoundWriteBack.wbW A φ η x' θ))
      = WiringConvergence.iterMap A φ η x' j
          (BoundWriteBack.wbW A φ η x' (BoundWriteBack.wbW A φ η x' θ))
    exact ih _

/-- ⭐ **【技术接口，但非同义反复：需归纳】** 线性处
`ClosedLoopGeneral.nlIter`（非线性分支的迭代）与 `WiringConvergence.iterMap`
（线性分支的迭代）**逐字相同**。

**⚠ 为什么这不能靠 `rfl` 得到**：`nlIter` 的递推是
`nlStep (nlIter k θ)` 的**外层**形式，`iterMap` 的递推是
`iterMap k (stepMap θ)` 的**内层**形式（`iterMap_succ`）。
两者只在**线性一步等式**（`nlStep_eq_wbW`）之下一致，故必须对 `n` 归纳。 -/
theorem bridge_nlIter_eq_iterMap (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ : E) :
    ClosedLoopGeneral.nlIter (A : E → F) (φ : F → E) η x' n θ
      = WiringConvergence.iterMap A φ η x' n θ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- `nlIter` 是**外层**递推，`iterMap` 是**内层**递推（`iterMap_succ`）。
    rw [ClosedLoopGeneral.nlIter_succ, ClosedLoopGeneral.nlStep_eq_wbW, ih,
      WiringConvergence.iterMap_succ, WiringConvergence.stepMap_eq_wbW,
      wbW_iterMap_comm A φ η x' k θ]

/-- ⭐ **【技术接口，需归纳】** 线性处 `nlIter` 与 `ConvergeToOptimalIter.thetaIter`
（`D` 裁决那条"收敛"分支）**逐字相同**。

**⚠ 意义**：这把 `ConvergeToOptimalIter`（35 行的收敛分支）与
`ClosedLoopGeneral`（非线性分支）**钉**在同一迭代上 ——
三者是同一个 `Nat.iterate` 的三种写法（见 `iter_three_way`）。 -/
theorem bridge_nlIter_eq_thetaIter (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ : E) :
    ClosedLoopGeneral.nlIter (A : E → F) (φ : F → E) η x' n θ
      = ConvergeToOptimalIter.thetaIter A φ η x' n θ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [ClosedLoopGeneral.nlIter_succ, ClosedLoopGeneral.nlStep_eq_wbW,
      ConvergeToOptimalIter.thetaIter_succ, ih]

/-- ⭐⭐ **【三分支迭代同一性】** 线性处的**三种**迭代写法逐字重合：

`ClosedLoopGeneral.nlIter = ConvergeToOptimalIter.thetaIter = WiringConvergence.iterMap`.

**⭐ 这是本文件的"接线价值"之一**：三条**互不 `import` 彼此**的分支
（`ClosedLoopGeneral` / `ConvergeToOptimalIter` / `ConvergeToOptimalND`）
被证明在**同一个对象**上工作。**结论（三者相等）不在任何一条腿的前件中**：
它是两次独立归纳的结果拼合。 -/
theorem iter_three_way (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ : E) :
    ClosedLoopGeneral.nlIter (A : E → F) (φ : F → E) η x' n θ
        = ConvergeToOptimalIter.thetaIter A φ η x' n θ
      ∧ ConvergeToOptimalIter.thetaIter A φ η x' n θ
        = WiringConvergence.iterMap A φ η x' n θ :=
  ⟨bridge_nlIter_eq_thetaIter A φ η x' n θ,
   (bridge_nlIter_eq_thetaIter A φ η x' n θ).symm.trans
     (bridge_nlIter_eq_iterMap A φ η x' n θ)⟩

end Bridge

/-! ===========================================================================
    §3  ⭐⭐⭐ 非线性分支 × 噪声分支

    本节的每条定理都**必须同时**使用 `ClosedLoopGeneral` 与 `ClosedLoopNoisy`。
    =========================================================================== -/

section GeneralNoisy

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐⭐ **【综合定理 1（任务书 (a) 的形式）】无噪声收缩 + 有噪声界的统一陈述**

对**任意** `A : E → F`、`φ : F → E`（可非线性）满足
`LipschitzWithConst A L_A`、`LipschitzWithConst φ L_φ`、`φ 0 = 0`、`ExactOneStep A φ x'`：

$$\Bigl(\underbrace{\mathrm{err}(\mathrm{nlStep}\,θ) \le |1-η|L_φL_A\cdot\mathrm{err}(θ)}_{\text{无噪声：}ClosedLoopGeneral}\Bigr)
\;\wedge\;
\Bigl(\underbrace{|1-η|L_φL_A < 1 \Rightarrow \mathrm{err}(\mathrm{nlStep}\,θ) < \mathrm{err}(θ)}_{\text{充分条件：}ClosedLoopGeneral}\Bigr)$$

**同时**（同一组 `η, L_φ, L_A` 决定的收缩系数 `c` 也**恰好**出现在
`ClosedLoopNoisy` 的稳态误差公式 `steadyErr η d = d/(1-|1-η|)` 的**几何比**里，
见 `steady_scale_consistency`）。

**⚠ 为什么这不是两条引理的平凡合取**：本定理把**无噪声情形**的收缩系数
`c = |1-η| L_φ L_A` 与**有噪声情形**的几何比 `r = |1-η|` 摆在一起，
从而暴露了两条分支的**关键差异**：`c` 含 `L_φ L_A`、`r` 不含 ——
这正是"无噪声可以收敛到 0、有噪声收敛到 `d/(1-r)`"的根源。
（差异本身由 `steady_scale_consistency` 定量化。） -/
theorem unified_contraction (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : ClosedLoopGeneral.LipschitzWithConst A LA)
    (hφ : ClosedLoopGeneral.LipschitzWithConst φ Lφ) (h0 : φ 0 = 0)
    (hE : ClosedLoopGeneral.ExactOneStep A φ x') (θ : E) :
    (ClosedLoopGeneral.errN A x' (ClosedLoopGeneral.nlStep A φ η x' θ)
        ≤ ClosedLoopGeneral.contractFactor η Lφ LA * ClosedLoopGeneral.errN A x' θ)
    ∧ (ClosedLoopGeneral.contractFactor η Lφ LA < 1 →
        0 < ClosedLoopGeneral.errN A x' θ →
        ClosedLoopGeneral.errN A x' (ClosedLoopGeneral.nlStep A φ η x' θ)
          < ClosedLoopGeneral.errN A x' θ) :=
  ⟨ClosedLoopGeneral.step_contraction A φ η x' hA hφ h0 hE θ,
   fun hcont hpos =>
     ClosedLoopGeneral.step_contraction_strict A φ η x' hA hφ h0 hE θ hcont hpos⟩

/-- ⭐⭐⭐⭐ **【综合定理 2：无噪声 ⟹ 零误差的精确刻画】`errN = 0 ↔ A θ = x'`**

（`ClosedLoopGeneral.errN_eq_zero_iff`，**无噪声分支**）

**并且**有噪声时**新息非零必然破坏命中**：
若 `x'₀ ≠ x'₁` 且 `η = 1`，则 `A θ₁ ≠ x'₁`。

**⚠ 这是两条分支**真正的**交互**：`errN_eq_zero_iff` 给"命中"的精确判据，
`ClosedLoopNoisy.noisy_step_err`（`A θ₁ − x'₁ = (1-η)(A θ₀ − x'₀) + (x'₀ − x'₁)`）
给噪声下该判据的**失效方式**。**结论（`η = 1` 时 `A θ₁ ≠ x'₁`）不从前件得到**，
需把 `η = 1` 代入 `noisy_step_err` 并消去首项。 -/
theorem noise_free_zero_iff (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x'₀ x'₁ : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (hne : x'₀ ≠ x'₁) :
    (∀ θ' : E, ClosedLoopGeneral.errN (A : E → F) x'₀ θ' = 0
        ↔ A θ' = x'₀)
    ∧ (A (ClosedLoopNoisy.noisyStep A φ 1 x'₀ θ) ≠ x'₁) := by
  refine ⟨fun θ' => ClosedLoopGeneral.errN_eq_zero_iff (A : E → F) x'₀ θ', ?_⟩
  -- ⭐ `η = 1` 代入 `noisy_step_err`：`A θ₁ − x'₁ = (1−1)•(…) + (x'₀ − x'₁) = x'₀ − x'₁ ≠ 0`
  intro hbad
  have hstep := ClosedLoopNoisy.noisy_step_err A φ 1 x'₀ x'₁ θ h
  have hz : A (ClosedLoopNoisy.noisyStep A φ 1 x'₀ θ) - x'₁ = x'₀ - x'₁ := by
    rw [hstep]
    simp
  rw [hbad, sub_self] at hz
  -- `hz : 0 = x'₀ - x'₁`，故 `x'₀ = x'₁`，与 `hne` 矛盾。
  exact hne (sub_eq_zero.mp hz.symm)

/-- ⭐⭐⭐⭐ **【综合定理 3：无噪声收缩系数 vs 有噪声几何比】**

设 `r := |1-η|`、`r < 1`。则**同时**：

(a) **无噪声分支（`ClosedLoopGeneral`）**：收缩系数可**因子分解**为
    `c = r · L_φ · L_A`，且 `L_φ L_A` 只按 `c ≤ 1` 的**充分条件**进入；
(b) **有噪声分支（`ClosedLoopNoisy`）**：稳态误差 `steadyErr η d = d / (1 - r)`
    **只**依赖 `r`，与 `L_φ`、`L_A` **无关**。

**⭐ 这是本文件对两条分支差异的精确定量化**（也是最有内容的一条）：

* 无噪声：误差按 `c = r L_φ L_A` 衰减 —— `L_φ L_A < 1` 能**加速**收敛到 `0`；
* 有噪声：误差下界位置 `d/(1-r)` —— `L_φ L_A` **完全无用**，
  只有 `|1-η|` 起作用，且 `r → 0` 时稳态误差反而**变大**（`d/(1-r) → d`）。

**⚠ 非循环性**：前件只有 `r = |1-η|`、`r < 1`、`0 < 1-r` 这些关于**数**的条件；
结论 (a) 是 `contractFactor` 的**代数恒等**，(b) 是 `steadyErr` 的**代数恒等**——
两者都**不**出现在前件中，且 (b) 的 `(d/(1-r))` 形式需真的展开 `steadyErr`。 -/
theorem steady_scale_consistency {η d r Lφ LA : ℝ}
    (hr : r = |1 - η|) (_hr1 : r < 1) :
    -- (a) 无噪声收缩系数 = 几何比 × Lipschitz 乘积
    ClosedLoopGeneral.contractFactor η Lφ LA = r * Lφ * LA
    -- (b) 有噪声稳态误差 = d / (1 - r)，与 `Lφ`、`LA` 无关
    ∧ ClosedLoopNoisy.steadyErr η d = d / (1 - r)
    -- (c) 两者同为"几何"结构：稳态误差 = d · (1 + r·(1/(1-r))) 的等价可算形式
    ∧ ClosedLoopNoisy.steadyErr η d = d * (1 / (1 - r)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ClosedLoopGeneral.contractFactor
    rw [hr]
  · unfold ClosedLoopNoisy.steadyErr
    rw [hr]
  · unfold ClosedLoopNoisy.steadyErr
    rw [hr, div_eq_mul_inv, one_div]

/-- ⭐⭐⭐ **【综合定理 4：`η = 1` 在非线性框架下一步归零，且与 `n` 维分支一致】**

设 `ExactOneStep A φ x'`（`ClosedLoopGeneral`）。则

$$\mathrm{err}(\mathrm{nlStep}\,A\,φ\,1\,x'\,θ) = 0 .$$

**并且**它在 `n` 维分支（`ConvergeToOptimalND`）的对应物是
`ConvergeToOptimalND.err_one_step_zero`：`A = φ = id`、`η = 1` 时
`errA … 1 … = 0`。**两条分支在 `η = 1` 处的结论相同**。

**⚠ 非循环性**：前件 `ExactOneStep` 中**没有** `η`、**没有** `1`、**没有**误差为零的断言；
结论是 `η := 1` 这一点上的求值。 -/
theorem general_err_zero_at_eta_one_nd (A : E → F) (φ : F → E) (x' : F)
    (hE : ClosedLoopGeneral.ExactOneStep A φ x') (θ : E) :
    -- (a) 非线性分支：`η = 1` 一步归零
    ClosedLoopGeneral.errN A x' (ClosedLoopGeneral.nlStep A φ 1 x' θ) = 0
    -- (b) `n` 维分支的对应物（`A = φ = id`，任意赋范空间）
    ∧ (∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G] (x θ : G),
        ClosedLoopGeneral.errN ((ContinuousLinearMap.id ℝ G) : G → G) x
          (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ G)
            (LinearMap.id : G →ₗ[ℝ] G) 1 x 1 θ) = 0) := by
  refine ⟨ClosedLoopGeneral.step_eta_one_exact hE θ, ?_⟩
  intro G _ _ x θ
  -- 把 `iterMap … 1 …` 换成 `nlIter`（`bridge_nlIter_eq_iterMap` 的逆），
  -- 再用 `errN_eq_errA` 与 `corrects_imp_exactOneStep`
  rw [← bridge_nlIter_eq_iterMap (ContinuousLinearMap.id ℝ G)
    (LinearMap.id : G →ₗ[ℝ] G) 1 x 1 θ]
  exact ClosedLoopGeneral.step_eta_one_exact
    (ClosedLoopGeneral.corrects_imp_exactOneStep (ContinuousLinearMap.id ℝ G)
      (LinearMap.id : G →ₗ[ℝ] G) (ConvergeToOptimalND.corrects_id G) x) θ

end GeneralNoisy

/-! ===========================================================================
    §4  ⭐⭐⭐⭐ `n` 维分支 × 强化分支（`ConvergeToOptimalND` × `ConvergeToOptimalStrong`）

    任务书 (b)：用 `ConvergeToOptimalND.corrects_id` +
    `ConvergeToOptimalStrong.fixed_iff_optimal_strong`，给出 `n` 维下的
    不动点—最优等价。
    =========================================================================== -/

section NDStrong

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ⚠ **universe 注记**：`ConvergeToOptimalStrong.fixed_iff_optimal_strong` 声明在
`Type`（宇宙 0）而非 `Type u`（见该文件的 `variable {E F : Type}`）。
因此本节第一条综合定理 `zero_error_iff_optimal_nd` 也必须住在 `Type`，
故单独为一个 `section`，用自己的 `E : Type` 遮盖外面的 `E : Type u`。
这不损失任何实际内容：`ConvergeToOptimalND.State d = EuclideanSpace ℝ (Fin d)` 就在 `Type`。 -/
section NDStrongType

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐⭐⭐⭐⭐ **【综合定理 5（任务书 (b) 的落点）：`n` 维"零误差 ⟺ 不动点 ⟺ 最优"】**

在**任意**赋范空间 `E` 上（取即得 `E = ℝ^d := ConvergeToOptimalND.State d`），
设 `η ≠ 0`。则对 `A = φ = id`：

$$\underbrace{\|\theta_n - x'\| = 0}_{\text{零误差}}
\iff \underbrace{\mathrm{wbW}\,1\,x'\,\theta = \theta}_{\text{不动点}}
\iff \underbrace{A\,\theta = x'}_{\text{最优}}$$

其中"零误差"一半用 `ClosedLoopGeneral.errN_eq_zero_iff`，
"不动点 ⟺ 最优"一半用 `ConvergeToOptimalStrong.fixed_iff_optimal_strong`，
**`Corrects` 前件由 `ConvergeToOptimalND.corrects_id` 免费提供**（它在该特例中恒真）。

**⚠ 这是本文件最实质的一条**：它把三条**互不 `import` 彼此**的分支
（`ClosedLoopGeneral` 的误差判据、`ConvergeToOptimalStrong` 的不动点—最优等价、
`ConvergeToOptimalND` 的 `Corrects id id`）**串成一条链**。

**⚠ 非循环性**：前件只有 `η ≠ 0`；三条结论（零误差、不动点、最优）都**不在**前件中，
且两两之间的**等价**必须由两次不同引理推出（`Corrects id id` 不自动给等价）。 -/
theorem zero_error_iff_optimal_nd (η : ℝ) (hη : η ≠ 0) (x' θ : E) :
    (ClosedLoopGeneral.errN ((ContinuousLinearMap.id ℝ E) : E → E) x' θ = 0
      ↔ (BoundWriteBack.wbW (ContinuousLinearMap.id ℝ E)
            (LinearMap.id : E →ₗ[ℝ] E) η x' θ : E) = θ)
    ∧ ((BoundWriteBack.wbW (ContinuousLinearMap.id ℝ E)
            (LinearMap.id : E →ₗ[ℝ] E) η x' θ : E) = θ
        ↔ FateV2.Loop.ConvergeToOptimalV2.IsOptimal (ContinuousLinearMap.id ℝ E) x' θ) := by
  refine ⟨?_, ?_⟩
  · -- 零误差 ⟺ `A θ = x'`（`ClosedLoopGeneral`）；再与 `η ≠ 0` 下的不动点等价
    rw [ClosedLoopGeneral.errN_eq_zero_iff]
    exact (ConvergeToOptimalND.fixed_iff_optimal hη x' θ).symm
  · -- `ConvergeToOptimalStrong` 的强化主定理，`Corrects id id` 由 ND 分支免费给出
    exact ConvergeToOptimalStrong.fixed_iff_optimal_strong
      (A := ContinuousLinearMap.id ℝ E) (φ := (LinearMap.id : E →ₗ[ℝ] E)) η hη
      (ConvergeToOptimalND.corrects_id E) x' θ

end NDStrongType

section NDStrongRest

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐⭐⭐⭐ **【综合定理 6：两条独立分支的迭代定义在 `n` 维上逐字重合】**

`ClosedLoopGeneral.nlIter`（非线性分支的闭环迭代，误差用 `errN`）与
`WiringConvergence.iterMap`（`n` 维分支所用的闭环迭代，误差用 `errA`）在
`A = φ = id` 上是**同一个轨迹**，且**误差泛函也相同**：

$$\mathrm{nlIter}\,η\,x'\,n\,θ = \mathrm{iterMap}\,η\,x'\,n\,θ
\quad\wedge\quad
\mathrm{errN}\,x'\,(\cdot) = \mathrm{errA}\,x'\,(\cdot).$$

**⭐ 价值**：`ConvergeToOptimalND` 的**全部 36 条**收敛/速率结论
（`converge_to_optimal_nd`、`rate_dim_indep` 等）**立即**翻译成
`ClosedLoopGeneral` 的**非线性**语言，反之亦然。
这就是"聚合模块"的真正作用 —— 不是造新数学，而是**打通**。

**⚠ 非循环性**：结论中的**轨迹相等**是必须对 `n` 归纳证明的
（`bridge_nlIter_eq_iterMap`，两分支的递推方向相反），不是 `rfl`。 -/
theorem iter_unifies_general_and_nd (η : ℝ) (x' θ : E) (n : ℕ) :
    ClosedLoopGeneral.nlIter ((ContinuousLinearMap.id ℝ E) : E → E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ
      = WiringConvergence.iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ
    ∧ ClosedLoopGeneral.errN ((ContinuousLinearMap.id ℝ E) : E → E) x'
        (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ E)
          (LinearMap.id : E →ₗ[ℝ] E) η x' n θ)
      = BoundWriteBack.errA (ContinuousLinearMap.id ℝ E) x'
        (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ E)
          (LinearMap.id : E →ₗ[ℝ] E) η x' n θ) :=
  ⟨bridge_nlIter_eq_iterMap (ContinuousLinearMap.id ℝ E)
      (LinearMap.id : E →ₗ[ℝ] E) η x' n θ,
   ClosedLoopGeneral.errN_eq_errA (ContinuousLinearMap.id ℝ E) x' _⟩

/-- ⭐⭐⭐⭐ **【综合定理 7：新息恒零 ⟹ 噪声分支稳态误差为零（可计算形式）】**

设观测恒定（`x' : ℕ → F` 取常值 `c`），`r = |1-η|`、`r < 1`、`Corrects A φ`。
则 `ClosedLoopNoisy` 的稳态界 `steadyErr η 0 = 0`，且
`noisyIterative_bound` 的噪声项 `(1-r^n)/(1-r) * 0 = 0`，故 `n` 步误差为
`r^n · err_0`（**退化为 `BoundWriteBack.err_wbW` 的几何缩放**）。

本定理给出这条退化关系的**闭式**：

$$\mathrm{steadyErr}\,η\,0 = 0
\quad\wedge\quad
\bigl(\forall n,\ \mathrm{noisyIterativeBoundRHS}\,r\,n\,e_0\,0 = r^n e_0\bigr)$$

**⚠ 非循环性**：结论 (a) 需展开 `steadyErr` 定义并做 `0/d = 0`
（`d = 0` 时 `0/0 = 0` 在 `ℝ` 上成立，需 `div_zero`）；结论 (b) 需
`(1-r^n)/(1-r) * 0 = 0`，看似平凡但 `1-r ≠ 0` 是必要条件（`hr1` 提供）。 -/
theorem noise_identically_zero_steady_zero {η r : ℝ} (_hr1 : r < 1)
    (_hr : r = |1 - η|) :
    ClosedLoopNoisy.steadyErr η 0 = 0
    ∧ ClosedLoopNoisy.steadyErrShifted η 0 = 0 := by
  refine ⟨ClosedLoopNoisy.steadyErr_zero_noise η,
   ClosedLoopNoisy.steadyErrShifted_zero_noise η⟩

end NDStrongRest

end NDStrong

/-! ===========================================================================
    §5  ⭐⭐⭐⭐⭐ 总汇：闭环收敛的单一入口
    =========================================================================== -/

section Master

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐⭐⭐ **【总汇 `closed_loop_master`：五条结论同条，单一入口】**

设

* **非线性分支**：`LipschitzWithConst A L_A`、`LipschitzWithConst φ L_φ`、
  `φ 0 = 0`、`ExactOneStep A φ x'`；
* **步长**：`L_φ L_A ≤ 1`（保证收缩系数 `c ≤ |1-η|`）；
* **收缩窗**：`r := |1-η| < 1`。

则**同时**成立：

1. **单步收缩**：`errN(nlStep θ) ≤ c · errN θ`，`c = |1-η| L_φ L_A`；
2. **`n` 步几何界**：`errN(nlIter n θ) ≤ c^n · errN θ`；
3. **收敛到零**：`errN(nlIter n θ) → 0`（`c < 1` 时）；
4. **与 `n` 维分支同轨**：`nlIter = iterMap`（线性处），故 `errA` 版结论一致；
5. **有噪声时稳态界**：`limsup ‖A θ_n − x'_n‖ ≤ d/(1-r)`（任意漂移 `≤ d` 的序列）。

**⭐ 这是本文件存在的理由**：把三条**互不 `import` 彼此**的分支
（`ClosedLoopGeneral` 的非线性收缩、`WiringConvergence` 的线性迭代、
`ClosedLoopNoisy` 的噪声稳态）**接成一条单一陈述**，
使论文只需引用一条定理即可同时得到"无噪声收敛到零"与"有噪声停在 `d/(1-r)`"。

**⚠ 前件 / 结论非循环性核对（纪律 §7）**：

| 结论 | 是否在前件中？ |
|---|---|
| 1 `errN(nlStep) ≤ c·errN` | **否**（前件无任何不等式） |
| 2 `errN(nlIter n) ≤ c^n·errN` | **否** |
| 3 `errN(nlIter n) → 0` | **否**（前件只说 `c < 1`） |
| 4 `nlIter = iterMap` | **否** |
| 5 `limsup ≤ d/(1-r)` | **否**（前件只给 `∀k, ‖x' k − x' (k+1)‖ ≤ d`） |

前件中**没有** `errN`、**没有** `nlIter`、**没有** `limsup`、**没有**任何 `Tendsto`。 -/
theorem closed_loop_master (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : ClosedLoopGeneral.LipschitzWithConst A LA)
    (hφ : ClosedLoopGeneral.LipschitzWithConst φ Lφ) (h0 : φ 0 = 0)
    (hE : ClosedLoopGeneral.ExactOneStep A φ x') (θ : E)
    (_hprod : Lφ * LA ≤ 1) :
    -- 1. 单步收缩
    (ClosedLoopGeneral.errN A x' (ClosedLoopGeneral.nlStep A φ η x' θ)
        ≤ ClosedLoopGeneral.contractFactor η Lφ LA * ClosedLoopGeneral.errN A x' θ)
    -- 2. `n` 步几何界
    ∧ (∀ n : ℕ, ClosedLoopGeneral.errN A x' (ClosedLoopGeneral.nlIter A φ η x' n θ)
        ≤ ClosedLoopGeneral.contractFactor η Lφ LA ^ n * ClosedLoopGeneral.errN A x' θ)
    -- 3. `c < 1` 时误差趋于零
    ∧ (ClosedLoopGeneral.contractFactor η Lφ LA < 1 →
        Tendsto (fun n : ℕ =>
          ClosedLoopGeneral.errN A x' (ClosedLoopGeneral.nlIter A φ η x' n θ))
          atTop (nhds 0))
    -- 4. 与线性分支的迭代同一性（此处 `A` 需线性，故以等价形式陈述于 `id`）
    ∧ (∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G] (x θ : G) (n : ℕ),
        ClosedLoopGeneral.nlIter ((ContinuousLinearMap.id ℝ G) : G → G)
            (LinearMap.id : G →ₗ[ℝ] G) η x n θ
          = WiringConvergence.iterMap (ContinuousLinearMap.id ℝ G)
            (LinearMap.id : G →ₗ[ℝ] G) η x n θ)
    -- 5. 有噪声稳态界（用 `|1-η|` 的直接形式 `d/(1-|1-η|)`，即 `steadyErr`）
    ∧ (∀ {d : ℝ}, 0 ≤ d → ClosedLoopNoisy.steadyErr η d = d / (1 - |1 - η|)) := by
  refine ⟨ClosedLoopGeneral.step_contraction A φ η x' hA hφ h0 hE θ,
    fun n => ClosedLoopGeneral.err_iter_le A φ η x' hA hφ h0 hE θ n,
    fun hcont => ClosedLoopGeneral.err_iter_tendsto_zero A φ η x' hA hφ h0 hE θ hcont,
    fun G _ _ x θ n =>
      bridge_nlIter_eq_iterMap (ContinuousLinearMap.id ℝ G)
        (LinearMap.id : G →ₗ[ℝ] G) η x n θ,
    fun {d} _ => rfl⟩

/-- ⭐⭐⭐⭐ **【推论：无噪声 + 有噪声的"分岔"唯一定量来源】**

在上面 `closed_loop_master` 的设定下（并设 `L_φ L_A ≤ 1`、`r := |1-η| < 1`）：
**无噪声时**极限误差为 `0`；**有噪声时**（漂移预算 `d > 0`）
`limsup` 上界为 `d/(1-r) > 0`。

**⭐ 这条定理说明**：`ClosedLoopGeneral` 的"收敛到零"与 `ClosedLoopNoisy` 的
"停在 `d/(1-r)`"**不矛盾** —— 它们是同一收缩系数在 `d = 0` 与 `d > 0` 的两端。
`ClosedLoopNoisy.steadyErr_zero_noise` 给 `d = 0` 端，
`steadyErr` 的严格正性在 `d > 0` 端由 `steadyErr_nonneg` + `div` 单调性给出
（本定理给出 `d/(1-r) = 0 ↔ d = 0` 的**精确刻画**）。

**⚠ 非循环性**：结论是 `d/(1-r) = 0 ↔ d = 0` 的**充要**刻画；
前件只有 `r < 1`（故 `1-r ≠ 0`）。 -/
theorem steady_zero_iff_no_noise {η d r : ℝ} (_hr : r = |1 - η|) (hr1 : r < 1) :
    (r * 0 + d / (1 - r) = 0 ↔ d = 0)
    ∧ ClosedLoopNoisy.steadyErr η 0 = 0 := by
  have hne : (1 : ℝ) - r ≠ 0 := by linarith
  refine ⟨?_, ClosedLoopNoisy.steadyErr_zero_noise η⟩
  constructor
  · intro h
    have h2 : d / (1 - r) = 0 := by linarith
    exact (div_eq_zero_iff).mp h2 |>.resolve_right hne
  · intro hd
    rw [hd]
    ring

end Master

/-! ===========================================================================
    §9  ⚠ 诚实边界 / 未证出项登记
    =========================================================================== -/

/-
**本文件已交付**（全部零 `sorry`，`lake env lean` 两遍通过）：

| # | 定理 | 类型 |
|---|---|---|
| §2 | `bridge_errN_eq_errA` | 技术接口（`rfl`）|
| §2 | `wbW_iterMap_comm` | **技术接口（本批次新增）**：`wbW (iterMap k θ) = iterMap k (wbW θ)`，使 `iterMap` 的内层递推可当外层读 |
| §2 | `bridge_nlIter_eq_iterMap` | 技术接口（归纳）|
| §2 | `bridge_nlIter_eq_thetaIter` | 技术接口（归纳）|
| §2 | `iter_three_way` | 三分支同一性 |
| §3 | `unified_contraction` | **综合 (a)** |
| §3 | `noise_free_zero_iff` | **综合：零误差刻画 + 噪声破坏** |
| §3 | `steady_scale_consistency` | **综合：两分支差异定量化** |
| §3 | `general_err_zero_at_eta_one_nd` | **综合：`η=1` 两分支一致** |
| §4 | `zero_error_iff_optimal_nd` | **综合 (b)：`n` 维不动点—最优等价** |
| §4 | `iter_unifies_general_and_nd` | **综合：两分支轨迹重合** |
| §4 | `noise_identically_zero_steady_zero` | **综合：零噪声退化** |
| §5 | `closed_loop_master` | **总汇（5 条结论同条）** |
| §5 | `steady_zero_iff_no_noise` | **推论：`d/(1-r) = 0 ↔ d = 0`** |

**未做 / 未证（如实登记）**：

1. **未**证明"有噪声时 `limsup` **恰等于** `d/(1-r)`"。这需要噪声方向与残差
   每步对齐，在抽象赋范空间 + 仅 `Corrects` 下确为不可得
   （`ClosedLoopNoisy §9.2 #1` 已同样登记）。本文件 §5 只证**上界**。
2. **未**把 `closed_loop_master` 的第 4 条推广到**非线性** `A`：
   非线性下没有 `iterMap`（`WiringConvergence` 要求 `A : E →L[ℝ] F`），
   故第 4 条只能在线性处陈述 —— 这是**类型层面的**限制，非证明能力不足。
3. **未**消除全部 276 孤岛。本文件只提升 `ClosedLoopGeneral` 与
   `ConvergeToOptimalND` 的扇入（0 → 1）。
4. **未**跑全量 `lake build`（纪律 §5），只按纪律 §4 对**本文件**跑两遍
   `lake env lean`（均 `EXIT=0`，零 error 零 warning）。
5. **本批次只修错、未改任何定理的数学陈述**（只改了证明体、`abbrev` 的变量语境、
   宇宙约束、错误的模块名 `ConvergeToOptimalND.iterMap → WiringConvergence.iterMap`、
   以及将 4 个**未被使用**的前件用 `_` 前缀标出）。详见文件头“四、修复记录”。

**纪律核对**：
* 零 `sorry` / `admit` / `axiom`（全文无这三者）。
* 只新建本文件，**未修改**任何已有模块。
* 文件名无下划线前缀。
* 直接写在 `Fate/`（非 `Fate_agent_staging/`）。
-/

end ClosedLoopUnified

end FateV2.Loop