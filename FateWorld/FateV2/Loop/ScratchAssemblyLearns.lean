import FateWorld.FateV2.Loop.WorldModelAssembly
import FateWorld.FateV2.Loop.ThetaConvergence
namespace FateV2.Loop

open FateV2.Predict
namespace AssemblyLearnsScratch

open FateV2.Loop.EndToEnd
open FateV2.Loop.ThetaConvergence

/-!
  # Loop · ScratchAssemblyLearns

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ScratchAssemblyLearns.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModelAssembly, ThetaConvergence
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-- `A : ℝ →L[ℝ] ℝ` 取 `x • id`，即 `A θ = x * θ`。 -/
noncomputable def mulCLM (x : ℝ) : ℝ →L[ℝ] ℝ :=
  x • ContinuousLinearMap.id ℝ ℝ

theorem mulCLM_apply (x θ : ℝ) : mulCLM x θ = x * θ := by
  simp [mulCLM]

/-- `φ : ℝ →ₗ[ℝ] ℝ` 取 `(1/x) • id`。 -/
noncomputable def invLM (x : ℝ) : ℝ →ₗ[ℝ] ℝ :=
  (1 / x) • LinearMap.id

theorem invLM_apply (x r : ℝ) : invLM x r = (1 / x) * r := by
  simp [invLM, LinearMap.smul_apply]

theorem corrects_mulCLM_invLM (x : ℝ) (hx : x ≠ 0) :
    BoundWriteBack.Corrects (mulCLM x) (invLM x) := by
  intro r
  rw [mulCLM_apply, invLM_apply]
  field_simp

/-- `endToEndIter` 的 `Nat.iterate` 形式。 -/
theorem endToEndIter_eq_iterate (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] {Y : Type v} [Nonempty W.frame.X.Carrier]
    (h : W.frame.X.Carrier → Y) (η : W.frame.Θ.Carrier)
    (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier) (y : Y)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (n : ℕ) (θ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x n θ
      = (fun t => endToEnd W h η φ y t u ε a x)^[n] θ := by
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [endToEndIter_succ, ih, Function.iterate_succ_apply]

/-- ⭐ **桥：`linWorld` 上的 `endToEnd` 就是 `wbW (x • id) ((1/x) • id)`**。 -/
theorem linWorld_endToEnd_eq_wbW (η y θ x : ℝ) :
    endToEnd linWorld (id : ℝ → ℝ) η ((invLM x).toAddMonoidHom)
        y θ PUnit.unit PUnit.unit PUnit.unit x
      = BoundWriteBack.wbW (mulCLM x) (invLM x) η y θ := by
  rw [endToEnd_apply, BoundWriteBack.wbW_apply, observe_id, linWorld_predFrom]
  simp only [LinearMap.toAddMonoidHom_coe, invLM_apply, mulCLM_apply]
  ring_nf

open Filter Topology
open scoped Topology

theorem id_lipschitz (L : ℝ) (hL : 0 < L) (hL1 : 1 ≤ L) :
    RA14Strong.LipschitzInvertibleOn (id : ℝ → ℝ) L := by
  intro a b
  simp only [id, Real.dist_eq]
  rw [ge_iff_le, div_le_iff₀ hL]
  have h := abs_nonneg (a - b)
  nlinarith

/-- `fstep η (y/x)` 就是装配的一步 `wbW (mulCLM x) (invLM x) η y`（标量恒等式）。 -/
theorem fstep_eq_wbW (η y x : ℝ) (hx : x ≠ 0) (θ : ℝ) :
    fstep η (y / x) θ
      = BoundWriteBack.wbW (mulCLM x) (invLM x) η y θ := by
  rw [BoundWriteBack.wbW_apply, invLM_apply, mulCLM_apply, smul_eq_mul]
  unfold fstep
  field_simp
  ring

/-- ⭐⭐ **桥【真正同时引用两模块】：`linWorld` 的端到端迭代 = 装配的带噪迭代（常数观测）**。

`ThetaConvergence.thetaN` 是 `EndToEnd.endToEndIter linWorld`（观测固定为 `y`）；
`ClosedLoopNoisy.noisyIter` 是 `WorldModelAssembly` 用的装配迭代。
本定理证明**在 `linWorld` 上、常数观测下两者是同一个迭代**。 -/
theorem endToEndIter_linWorld_eq_noisyIter (η y x θ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    thetaN η (y / x) x θ n
      = ClosedLoopNoisy.noisyIter (mulCLM x) (invLM x) η (fun _ => y) n θ := by
  rw [thetaN_eq_iterate η (y / x) x θ hx n]
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ClosedLoopNoisy.noisyIter_succ, ih]
    rw [fstep_eq_wbW η y x hx]
    rfl

/-- 核对：`linWorld` 的一步 = `noisyStep`（常数观测）。 -/
theorem linWorld_step_eq_noisyStep (η y θ x : ℝ) :
    BoundWriteBack.wbW (mulCLM x) (invLM x) η y θ
      = ClosedLoopNoisy.noisyStep (mulCLM x) (invLM x) η y θ := rfl
