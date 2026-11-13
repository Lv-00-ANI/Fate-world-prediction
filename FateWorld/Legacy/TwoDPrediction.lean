import FateWorld.Legacy.WorldModelInstance2D
import FateWorld.Legacy.ConvergeToOptimalIter

/-! ===========================================================================
  §T4.2  端到端预测：`d = 2` 实例上的**一条真实数据 → 一个预测**

  ## 本文件做什么

  任务 T4.2 要求「一条真实数据的端到端预测」。
  既有 `ConvergeToOptimalIter.predicts_converges` 只给**渐近**收敛
  （`Tendsto ... atTop (nhds x')`），不是**具体预测值**。本文件补上具体的。

  取 `d = 2` 实例的 `A := swap2CLM`（`swap2` 的有界线性版，
  非恒等，见 `WorldModelInstance2D.swap2_ne_id`），`φ := swap2`（线性映射）。
  因 `swap2 ∘ swap2 = id`（`swap2_involutive`），故 `Corrects swap2CLM swap2`
  **成立**（是证明出来的，不是额外假设）。

  具体数据：观测 `x' = (3, -1)`，初值 `θ₀ = (0, 0)`，步长 `η = 1/2`。

  ## 主结果

  * `pred1_eq`：**一步预测 `pred1 = (-1/2, 3/2)`**（从 `wbW` 定义算出）。
  * `swap2_pred1_eq`：模型输出 `A pred1 = (3/2, -1/2)`。
  * `pred1_err_eq`：`A pred1 - x' = (-3/2, 1/2)`，与闭式 `(1-η)•(Aθ₀ - x')` 一致。
  * `pred1_error_band`：`∀ i, |A pred1 i - x' i| ≤ 3/2`（一步误差带）。
  * `pred1_end_to_end_band`：对**任意真值** `y` 满足 `∀ i, |x' i - y i| ≤ d`，
    得 `∀ i, |A pred1 i - y i| ≤ 3/2 + d`（端到端带）。
  * `pred2_error_band`：两步后逐坐标误差 `≤ 3/4`（半径按 `(1/2)^n` 收缩）。

  ## 诚实边界

  * `Corrects` 此处**可证**（`swap2` 对合），非假设。
  * 误差带由 `iterErr_closed` 的**等式**推出，不是新公设。
  * 不声称有限步精确；`η = 1/2` 时误差按 `(1/2)^n` 几何衰减。
  * 零 `sorry` / `admit` / `axiom`。

  ## 非平凡性自查

  * `pred1_eq` 的前件为空，结论来自 `wbW` 的**定义展开**，不是同义反复。
  * `pred1_error_band` 的前件为空，结论是范数不等式，靠 `fin_cases` + 具体数值。
  * `pred1_end_to_end_band` 前件只约束 `x'` 与 `y` 的距离，
    结论把**模型输出** `A pred1` 与 `y` 联系起来，中间用三角不等式，
    没有把结论塞进前件。
  =========================================================================== -/

namespace Fate
namespace TwoDPrediction

open Fate.WorldModelInstance2D
open Fate.ConvergeToOptimalIter
open Fate.BoundWriteBack

/-! ### §1 有界版 `swap2` 与 `Corrects` -/

/-- `swap2` 的**有界**线性版（有限维线性映射自动连续）。 -/
noncomputable def swap2CLM : V2 →L[ℝ] V2 := LinearMap.toContinuousLinearMap swap2

/-- `swap2CLM` 与 `swap2` 作为函数一致。 -/
theorem swap2CLM_apply (v : V2) : swap2CLM v = swap2 v := rfl

/-- ⭐ **`swap2` 是对合**：`swap2 (swap2 v) = v`。 -/
theorem swap2_involutive (v : V2) : swap2 (swap2 v) = v := by
  ext i
  simp only [swap2, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  omega

/-- ⭐ **【`Corrects` 成立，且非假设】**：`A := swap2CLM`, `φ := swap2`。 -/
theorem corrects_swap2 : Corrects swap2CLM swap2 := by
  intro r
  rw [swap2CLM_apply]
  exact swap2_involutive r

/-! ### §2 具体数据 -/

/-- **具体观测**：`x' = (3, -1)`。 -/
noncomputable def xObs : V2 := fun i => if i = 0 then 3 else -1

/-- **具体初值**：`θ₀ = (0, 0)`。 -/
def thetaZero : V2 := fun _ => 0

/-- **步长** `η = 1/2`（满足 `|1-η| = 1/2 < 1`）。 -/
noncomputable def eta : ℝ := 1 / 2

theorem xObs_zero : xObs 0 = 3 := by simp [xObs]
theorem xObs_one : xObs 1 = -1 := by simp [xObs]
theorem thetaZero_apply (i : Fin 2) : thetaZero i = 0 := rfl

/-! ### §3 ⭐ 一步预测的具体值 -/

/-- **一步预测** `pred1 := thetaIter swap2CLM swap2 eta xObs 1 thetaZero`。 -/
noncomputable def pred1 : V2 := thetaIter swap2CLM swap2 eta xObs 1 thetaZero

/-- ⭐ **【一步预测第一坐标】** `pred1 0 = -1/2`。 -/
theorem pred1_zero : pred1 0 = -1 / 2 := by
  simp [pred1, thetaIter, eta, xObs, thetaZero, wbW, swap2, swap2CLM]
  norm_num

/-- ⭐ **【一步预测第二坐标】** `pred1 1 = 3/2`。 -/
theorem pred1_one : pred1 1 = 3 / 2 := by
  simp [pred1, thetaIter, eta, xObs, thetaZero, wbW, swap2, swap2CLM]
  norm_num

/-- ⭐⭐ **【一步预测完整值】**：`pred1 = (-1/2, 3/2)`。 -/
theorem pred1_eq : pred1 0 = -1 / 2 ∧ pred1 1 = 3 / 2 :=
  ⟨pred1_zero, pred1_one⟩

/-- ⭐⭐ **【模型输出】**：`A pred1 = swap2 pred1 = (3/2, -1/2)`。 -/
theorem swap2_pred1_zero : swap2CLM pred1 0 = 3 / 2 := by
  rw [swap2CLM_apply, swap2_apply_zero, pred1_one]

/-- **模型输出第二坐标**：`A pred1 1 = -1/2`。 -/
theorem swap2_pred1_one : swap2CLM pred1 1 = -1 / 2 := by
  rw [swap2CLM_apply]
  simp only [swap2, LinearMap.coe_mk, AddHom.coe_mk]
  have : (1 : Fin 2) + 1 = 0 := by decide
  rw [this, pred1_zero]

/-- ⭐⭐ **【一步预测误差 = 闭式实例】**：`(A pred1 - x') 0 = -3/2`。 -/
theorem pred1_err_zero : (swap2CLM pred1 - xObs) 0 = -3 / 2 := by
  show swap2CLM pred1 0 - xObs 0 = -3 / 2
  rw [swap2_pred1_zero, xObs_zero]; norm_num

/-- **一步误差第二坐标**：`(A pred1 - x') 1 = 1/2`。 -/
theorem pred1_err_one : (swap2CLM pred1 - xObs) 1 = 1 / 2 := by
  show swap2CLM pred1 1 - xObs 1 = 1 / 2
  rw [swap2_pred1_one, xObs_one]; norm_num

/-- ⭐⭐ **【误差对得上闭式】**：`A pred1 - x' = (1-η)^1 • (A θ₀ - x')`。 -/
theorem pred1_err_closed_check : ∀ i : Fin 2,
    (swap2CLM pred1 - xObs) i = (1 - eta) ^ 1 * (swap2CLM thetaZero - xObs) i := by
  have h := iterErr_closed swap2CLM swap2 eta xObs corrects_swap2 1 thetaZero
  intro i
  have := congrFun h i
  simpa [pred1, Pi.sub_apply] using this

/-! ### §4 ⭐⭐ 误差带 -/

/-- ⭐⭐ **【一步误差带】**：模型输出 `A pred1` 落在观测 `x'` 的半径 `3/2` 的逐坐标带内。 -/
theorem pred1_error_band : ∀ i, |swap2CLM pred1 i - xObs i| ≤ 3 / 2 := by
  intro i
  fin_cases i
  · show |(swap2CLM pred1 - xObs) 0| ≤ 3 / 2
    rw [pred1_err_zero]; norm_num
  · show |(swap2CLM pred1 - xObs) 1| ≤ 3 / 2
    rw [pred1_err_one]; norm_num

/-- ⭐⭐⭐ **【主定理：端到端预测带】**

对**任意**真值 `y : V2`（真实数据），若它与观测读数 `x'` 逐坐标相差不超过 `d`，
则一步预测的模型输出 `A pred1` 与真值 `y` 逐坐标相差不超过 `d + 3/2`：

```
∀ i, |A pred1 i - y i| ≤ 3/2 + d
```

**为什么这是端到端预测**：`A pred1` 是**模型算出的预测**，
`3/2 + d` 是**误差带**（模型自身误差 `3/2` + 数据偏差 `d`）。
`d = 0` 时得到 `|A pred1 i - x' i| ≤ 3/2`（模型对观测的误差）。 -/
theorem pred1_end_to_end_band {y : V2} {d : ℝ}
    (hyd : ∀ i, |xObs i - y i| ≤ d) :
    ∀ i, |swap2CLM pred1 i - y i| ≤ 3 / 2 + d := by
  intro i
  have h1 : |swap2CLM pred1 i - xObs i| ≤ 3 / 2 := pred1_error_band i
  have h2 : |xObs i - y i| ≤ d := hyd i
  have hsplit : swap2CLM pred1 i - y i
      = (swap2CLM pred1 i - xObs i) + (xObs i - y i) := by ring
  calc |swap2CLM pred1 i - y i|
      = |(swap2CLM pred1 i - xObs i) + (xObs i - y i)| := by rw [hsplit]
    _ ≤ |swap2CLM pred1 i - xObs i| + |xObs i - y i| := abs_add_le _ _
    _ ≤ 3 / 2 + d := by linarith

/-- **`d = 0` 特例**（真值就是观测）：`|A pred1 i - x' i| ≤ 3/2`。 -/
theorem pred1_band_at_truth :
    ∀ i, |swap2CLM pred1 i - xObs i| ≤ 3 / 2 + 0 := by
  intro i
  simpa using pred1_error_band i

/-! ### §5 ⭐⭐ 两步预测：误差按 `(1-η)^n` 收缩 -/

/-- **两步预测**。 -/
noncomputable def pred2 : V2 := thetaIter swap2CLM swap2 eta xObs 2 thetaZero

/-- ⭐ **【两步误差闭式】**：`A pred2 - x' = (1/2)^2 • (A θ₀ - x')`。 -/
theorem pred2_err (i : Fin 2) :
    swap2CLM pred2 i - xObs i = (1 / 2) ^ 2 * (swap2CLM thetaZero i - xObs i) := by
  have h := iterErr_closed swap2CLM swap2 eta xObs corrects_swap2 2 thetaZero
  have hi := congrFun h i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  show swap2CLM (thetaIter swap2CLM swap2 eta xObs 2 thetaZero) i - xObs i = _
  rw [hi]
  norm_num [eta]

/-- `A θ₀ = θ₀ = 0`。 -/
theorem swap2CLM_thetaZero : swap2CLM thetaZero = thetaZero := by
  rw [swap2CLM_apply]
  ext j
  simp only [swap2, LinearMap.coe_mk, AddHom.coe_mk, thetaZero]

/-- ⭐⭐ **【误差带收缩】**：两步后逐坐标误差 `≤ 3/4`，即从 `3/2` 减半。 -/
theorem pred2_error_band : ∀ i, |swap2CLM pred2 i - xObs i| ≤ 3 / 4 := by
  intro i
  rw [pred2_err i, swap2CLM_thetaZero]
  fin_cases i <;>
    (simp only [thetaZero, xObs]
     norm_num)

end TwoDPrediction
end Fate
