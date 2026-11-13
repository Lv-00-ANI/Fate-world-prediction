import FateWorld.Legacy.BridgeA4Fixed
import FateWorld.Legacy.ThreeNodeFactorizes
import FateWorld.Legacy.FactorRecursionRouteB

/-! ===========================================================================
  §0  `mass` 在 `colliderP` 上的具体数值（为 `not_lmg_colliderP_chain` 做准备）

  ## 背景

  `Fate/BridgeA4.lean` 的 `not_lmg_colliderP_chain` 用 `decide` 证明
  `mass {0} colliderP x = 2`，但 `decide` 失败——**不是因为命题为假**，
  而是因为 `mass` 返回 `ℝ`，而 `ℝ` 的 `DecidableEq` 来自 `Classical`，不可计算。

  ## 本文件的结果

  * `mass_single_zero_colliderP`：`mass {0} colliderP x = 2`
  * `mass_empty_colliderP`：`mass ∅ colliderP x = 4`（⚠ 原注释说 1，是错的）
  * `colliderP_x_zero`：`colliderP x = 0`（因 `x 0 = false ≠ true = x 2`）

  取 `x := fun v => if v = 0 then false else if v = 2 then true else false`。

  ## 意义

  有了这三个数值，`LMG` 在该点的断言
  `p x · mass ∅ p x = mass {0} p x · mass ∅ p x`
  化为 `0 · 4 = 2 · 4`，即 `0 = 8`，**假**。
  =========================================================================== -/

namespace Fate.BridgeA4Fixed2

theorem mass_single_zero_colliderP :
    Fate.DAGFactorization.mass ({(0 : Fin 3)} : Finset (Fin 3))
      (Fate.ThreeNodeFactorizes.colliderP (α := Bool))
      (fun v : Fin 3 => if v = 0 then false else if v = 2 then true else false) = 2 := by
  unfold Fate.DAGFactorization.mass Fate.ThreeNodeFactorizes.colliderP
  simp only [Finset.mem_singleton, forall_eq, Fin.isValue, if_true]
  rw [show (∑ w : Fin 3 → Bool, if w 0 = false then (if w 0 = w 2 then (1:ℝ) else 0) else 0)
      = ∑ w : Fin 3 → Bool, if (w 0 = false ∧ w 0 = w 2) then (1:ℝ) else 0 from by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : w 0 = false <;> by_cases h2 : w 0 = w 2 <;> simp [h1, h2]]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 0 = false ∧ w 0 = w 2)).card = 2 := by
    decide
  rw [hc]; norm_num

-- mass ∅：直接枚举 8 项
theorem mass_empty_colliderP :
    Fate.DAGFactorization.mass (∅ : Finset (Fin 3))
      (Fate.ThreeNodeFactorizes.colliderP (α := Bool))
      (fun v : Fin 3 => if v = 0 then false else if v = 2 then true else false) = 4 := by
  unfold Fate.DAGFactorization.mass Fate.ThreeNodeFactorizes.colliderP
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true]
  -- 现在是 ∑ w : Bool³, (if w 0 = w 2 then 1 else 0) = 2
  have : (∑ w : Fin 3 → Bool, (if w 0 = w 2 then (1:ℝ) else 0)) = 4 := by
    rw [Finset.sum_boole]
    have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 0 = w 2)).card = 4 := by decide
    rw [hc]; norm_num
  exact this


-- colliderP x = 0（因为 x 0 ≠ x 2）
theorem colliderP_x_zero :
    Fate.ThreeNodeFactorizes.colliderP (α := Bool)
      (fun v : Fin 3 => if v = 0 then false else if v = 2 then true else false) = 0 := by
  unfold Fate.ThreeNodeFactorizes.colliderP
  -- 化简所有 if
  simp only [Fin.isValue, if_true, show (2 : Fin 3) = 0 ↔ False from by decide,
    if_false, if_true]
  norm_num

end Fate.BridgeA4Fixed2
