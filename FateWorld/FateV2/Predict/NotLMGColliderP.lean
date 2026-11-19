import FateWorld.FateV2.Predict.ColliderPValues
import FateWorld.FateV2.Predict.ThreeNodeFactorizes
import FateWorld.FateV2.Predict.FactorRecursionRouteB
/-!
  # Predict · NotLMGColliderP

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NotLMGColliderP.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ColliderPValues, ThreeNodeFactorizes, FactorRecursionRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `not_lmg_colliderP_chain` 的完整证明

  ## 背景

  `Fate/BridgeA4.lean` 的这条定理有两个问题：
  1. `mass {0} colliderP x = 2 := by decide` —— `decide` 对 `ℝ` 不可计算
  2. 注释说 `mass ∅ = 1` —— 实际是 4

  **但定理的结论是对的**：LMG 在 `v = 0` 处断言
    `p x · mass ∅ = mass {0} · mass ∅`
  取 `x := fun v => if v = 0 then false else if v = 2 then true else false`，
  代入 `p x = 0`、`mass ∅ = 4`、`mass {0} = 2` 得 `0 · 4 = 2 · 4`，即 `0 = 8`，**假**。

  ## 本文件的证明

  用 `Fate/ColliderPValues.lean` 的三个数值引理，避免 `decide`。
  `chainDAG` 在 `v = 0` 处 `nd = ∅`、`pa = ∅`，故 `nd ∪ pa = ∅`、`insert 0 ∅ = {0}`。
  =========================================================================== -/

namespace FateV2.Predict.BridgeA4Fixed3

open FateV2.Modeling

-- ⭐ not_lmg_colliderP_chain 的正确证明
-- LMG 在 v = 0 处断言：p x * mass ∅ = mass {0} * mass ∅
-- 代入：0 * 4 = 2 * 4 ⟹ 0 = 8 ⟹ 假
theorem not_lmg_colliderP_chain :
    ¬ FateV2.Predict.FactorRecursionRouteB.LMG (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool))
        FateV2.Predict.ThreeNodeFactorizes.chainDAG := by
  intro h
  -- nd(0) 与 pa(0)
  have hnd : FateV2.Modeling.Graph.DAG.nonDescendants FateV2.Predict.ThreeNodeFactorizes.chainDAG
      (0 : Fin 3) = ∅ := by decide
  have hpa : FateV2.Predict.DAGFactorization.pa FateV2.Predict.ThreeNodeFactorizes.chainDAG (0 : Fin 3) = ∅ := by
    decide
  set x : Fin 3 → Bool := fun v => if v = 0 then false else if v = 2 then true else false with hx
  have key := h (0 : Fin 3) x
  simp only [hnd, hpa, Finset.union_empty] at key
  rw [Finset.insert_empty] at key
  -- key : p x * mass ∅ = mass {0} * mass ∅
  rw [show FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool) x = 0 from
      Fate.BridgeA4Fixed2.colliderP_x_zero,
    show FateV2.Predict.DAGFactorization.mass (∅ : Finset (Fin 3))
        (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) x = 4 from
      Fate.BridgeA4Fixed2.mass_empty_colliderP,
    show FateV2.Predict.DAGFactorization.mass ({(0 : Fin 3)} : Finset (Fin 3))
        (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) x = 2 from
      Fate.BridgeA4Fixed2.mass_single_zero_colliderP] at key
  norm_num at key

end FateV2.Predict.BridgeA4Fixed3
