import FateWorld.FateV2.Predict.ColliderDAGValues
import FateWorld.FateV2.Predict.ThreeNodeFactorizes
import FateWorld.FateV2.Predict.FactorRecursionRouteB
/-!
  # Predict · FactorizesNotImpliesLMG

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FactorizesNotImpliesLMG.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ColliderDAGValues, ThreeNodeFactorizes, FactorRecursionRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `factorizes_not_implies_LMG` 的**正确证明**

  ## 背景：BridgeA4 的原证明是假证

  `Fate/BridgeA4.lean` 用 `factorizes_colliderP 0` 在 `chainDAG` 上证明，
  **但 `ThreeNodeFactorizes.chain_not_factorizes_colliderP` 证明
  `colliderP` 在 `chainDAG` 上不满足 `Factorizes`**（因 `pa_chain(1) = {0} ⊉ {0,2}`）。

  所以那个证明是假证。

  ## 正确的见证：`colliderDAG`（`pa(1) = {0,2}`）

  1. `colliderP_factorizes`：`Factorizes colliderP colliderDAG` ✓（`ThreeNodeFactorizes` 已有）
  2. `not_lmg_colliderP_colliderDAG`：`¬ LMG colliderP colliderDAG`（本文件）

  在 `v = 0` 处：`pa(0) = ∅`、`nd(0) = {2}`，取 `x = fun _ => false`：
    `p x = 1`、`mass {2} x = 2`、`mass {0,2} x = 2`
    LMG 断言 `1 · 2 = 2 · 2`，即 `2 = 4`，**假**。

  ## 本文件

  `factorizes_not_implies_LMG`：`Factorizes ⟹ LMG` 是假命题。
  =========================================================================== -/

namespace FateV2.Predict.Witness

open FateV2.Modeling

-- 取 x 满足 x0 = x2（全 false）
-- 验证三个值
theorem p_x_one :
    FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)
      (fun _ : Fin 3 => false) = 1 := by
  unfold FateV2.Predict.ThreeNodeFactorizes.colliderP; rfl

theorem mass_two_all_false :
    Fate.DAGFactorization.mass ({2} : Finset (Fin 3))
      (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool))
      (fun _ : Fin 3 => false) = 2 := by
  have h1 : ∀ w : Fin 3 → Bool, FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool) w
      = if w 0 = w 2 then (1 : ℝ) else 0 := fun w => rfl
  simp only [Fate.DAGFactorization.mass, h1, Finset.mem_singleton, forall_eq]
  -- 目标已是 if x 2 = false then ..., 无需化简
  rw [show (∑ w : Fin 3 → Bool, if w 2 = false then (if w 0 = w 2 then (1:ℝ) else 0) else 0)
      = ∑ w : Fin 3 → Bool, if (w 2 = false ∧ w 0 = w 2) then (1:ℝ) else 0 from by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hh1 : w 2 = false <;> by_cases hh2 : w 0 = w 2 <;> simp [hh1, hh2]]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 2 = false ∧ w 0 = w 2)).card = 2 := by
    decide
  rw [hc]; norm_num

theorem mass_pair_all_false :
    Fate.DAGFactorization.mass ({0, 2} : Finset (Fin 3))
      (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool))
      (fun _ : Fin 3 => false) = 2 := by
  have h1 : ∀ w : Fin 3 → Bool, FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool) w
      = if w 0 = w 2 then (1 : ℝ) else 0 := fun w => rfl
  simp only [Fate.DAGFactorization.mass, h1]
  have key : ∀ w : Fin 3 → Bool,
      (if (∀ u ∈ ({0, 2} : Finset (Fin 3)), w u = (fun _ : Fin 3 => false) u)
        then (if w 0 = w 2 then (1:ℝ) else 0) else 0)
      = if (w 0 = false ∧ w 2 = false ∧ w 0 = w 2) then (1:ℝ) else 0 := by
    intro w
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Fin.isValue, if_true]
    by_cases ha : w 0 = false <;> by_cases hb : w 2 = false <;> by_cases hc : w 0 = w 2 <;>
      simp [ha, hb, hc]
  rw [Finset.sum_congr rfl (fun w _ => key w), Finset.sum_boole]
  have hc2 : (Finset.univ.filter (fun w : Fin 3 → Bool => w 0 = false ∧ w 2 = false ∧ w 0 = w 2)).card = 2 := by
    decide
  rw [hc2]; norm_num


-- ⭐ colliderDAG 上 LMG 失败（见证：x = fun _ => false）
-- 在 v = 0 处：pa(0) = ∅、nd(0) = {2}，LMG 断言 p x * mass {2} = mass {0,2} * mass {2}
-- 代入 1 * 2 = 2 * 2 ⟹ 2 = 4 ⟹ 假
theorem not_lmg_colliderP_colliderDAG :
    ¬ FateV2.Predict.FactorRecursionRouteB.LMG (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool))
        FateV2.Predict.ThreeNodeFactorizes.colliderDAG := by
  intro h
  have hnd : FateV2.Predict.ThreeNodeFactorizes.colliderDAG.nonDescendants (0 : Fin 3)
      = ({2} : Finset (Fin 3)) := by decide
  have hpa : Fate.DAGFactorization.pa FateV2.Predict.ThreeNodeFactorizes.colliderDAG (0 : Fin 3) = ∅ := by
    decide
  have key := h (0 : Fin 3) (fun _ : Fin 3 => false)
  simp only [hnd, hpa, Finset.union_empty] at key
  rw [p_x_one,
    mass_two_all_false,
    show Fate.DAGFactorization.mass (insert (0 : Fin 3) ({2} : Finset (Fin 3)))
        (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false)
        = 2 from by
      rw [show (insert (0 : Fin 3) ({2} : Finset (Fin 3))) = ({0, 2} : Finset (Fin 3)) from by decide]
      exact mass_pair_all_false] at key
  norm_num at key


-- ⭐⭐⭐ A4.0e 的正确证明：Factorizes ⟹ LMG 是假命题
-- 见证：colliderP 在 colliderDAG 上满足 Factorizes（ThreeNodeFactorizes.colliderP_factorizes）
--       却不满足 LMG（上一条）
theorem factorizes_not_implies_LMG :
    ¬ (∀ {G : FateV2.Modeling.Graph.DAG (Fin 3)},
        FateV2.Predict.FactorRecursionRouteB.Factorizes
          (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) G →
        FateV2.Predict.FactorRecursionRouteB.LMG
          (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) G) := by
  intro h
  exact not_lmg_colliderP_colliderDAG
    (h (G := FateV2.Predict.ThreeNodeFactorizes.colliderDAG)
       (FateV2.Predict.ThreeNodeFactorizes.colliderP_factorizes Bool))

end FateV2.Predict.Witness
