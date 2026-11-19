import FateWorld.FateV2.Predict.NotLMGColliderP
import FateWorld.FateV2.Predict.ThreeNodeFactorizes
/-!
  # Predict · ColliderDAGValues

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ColliderDAGValues.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NotLMGColliderP, ThreeNodeFactorizes
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `colliderDAG` 上 `colliderP` 的 mass 值

  ## 背景

  `Fate/BridgeA4.lean` 的 `factorizes_not_implies_LMG` 用 `factorizes_colliderP 0`
  在 `chainDAG` 上证明 `LMG` 失败。**但 `ThreeNodeFactorizes.lean` 的
  `chain_not_factorizes_colliderP` 证明 `colliderP` 在 `chainDAG` 上**不**满足
  `Factorizes`**（因 `pa_chain(1) = {0} ⊉ {0,2}`）。

  ⟹ `BridgeA4` 的那个证明**是假证**。

  ## 正确的见证：`colliderDAG`

  `colliderDAG` 的 `pa(1) = {0, 2}`，故 `colliderP` 在其上**满足** `Factorizes`
  （`ThreeNodeFactorizes.colliderP_factorizes`）。

  在 `v = 0` 处：`pa(0) = ∅`、`nd(0) = {2}`，故 `nd ∪ pa = {2}`、`insert 0 {2} = {0,2}`。

  取 `x := fun v => if v = 0 then false else if v = 2 then true else false`
  （`x 0 = false ≠ true = x 2`，故 `p x = 0`）：
  * `mass {2} p x = 2`
  * `mass {0,2} p x = ?`

  ## 本文件

  `mass_two_colliderP`：`mass {2} colliderP x = 2`。
  =========================================================================== -/

namespace FateV2.Predict.BridgeA4Fixed4

open FateV2.Modeling

theorem mass_two_colliderP :
    FateV2.Predict.DAGFactorization.mass ({2} : Finset (Fin 3))
      (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool))
      (fun v : Fin 3 => if v = 0 then false else if v = 2 then true else false) = 2 := by
  have h1 : ∀ w : Fin 3 → Bool, FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool) w
      = if w 0 = w 2 then (1 : ℝ) else 0 := fun w => rfl
  simp only [FateV2.Predict.DAGFactorization.mass, h1, Finset.mem_singleton, forall_eq]
  -- 用 conv 把那个 if 化简
  conv_lhs =>
    arg 2
    ext w
    rw [show (if (2:Fin 3) = 0 then false else (if True then true else false)) = true from by
      rw [if_neg (by decide : ¬ (2:Fin 3) = 0), if_pos trivial]]
  rw [show (∑ w : Fin 3 → Bool, (if w 2 = true then (if w 0 = w 2 then (1:ℝ) else 0) else 0))
      = ∑ w : Fin 3 → Bool, if (w 2 = true ∧ w 0 = w 2) then (1:ℝ) else 0 from by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hh1 : w 2 = true <;> by_cases hh2 : w 0 = w 2 <;> simp [hh1, hh2]]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 2 = true ∧ w 0 = w 2)).card = 2 := by
    decide
  rw [hc]
  norm_num

end FateV2.Predict.BridgeA4Fixed4
