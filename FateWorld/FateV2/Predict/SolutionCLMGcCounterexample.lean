import FateWorld.FateV2.Predict.RouteBGapNote
import FateWorld.FateV2.Predict.ThreeNodeFactorizes
/-!
  # Predict · SolutionCLMGcCounterexample

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SolutionCLMGcCounterexample.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RouteBGapNote, ThreeNodeFactorizes
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⭐ `FactorizesC ⟹ LMGc` 的**机检反例**

  ## 反例设置

  `G = colliderDAG`（`0 → 2 ← 1`），`p = colliderP`（`p w = [w_0 = w_2]`），
  `α = Bool`，`x ≡ false`。

  ## 四个 mass 值（全部机检）

  | 量 | 值 |
  |---|---|
  | `mass {0} p x` | **2** |
  | `mass {2} p x` | **2** |
  | `mass ∅ p x` | **4** |
  | `mass {0,2} p x` | **2** |

  ## 化简后的 `LMGc` 在 `v = 0` 处断言

  `pa(0) = ∅`、`nd(0) = {2}` ⟹ `LMGc` 断言
    `mass {0} * mass {2} = mass ∅ * mass {0,2}`
  代入：`2 · 2 = 4 · 2`，即 **`4 = 8`，假**。

  ## ⚠ 而 `colliderP` 满足 `FactorizesC colliderDAG`

  `ThreeNodeFactorizes.colliderP_factorizes` 已证 `Factorizes colliderP colliderDAG`，
  且 `colliderPhi v x = if v = 1 then [x 0 = x 2] else 1` 只读 `{v} ∪ pa v`，
  故 `FactorizesC` 的读集封闭条件满足。

  ## ⟹ 结论

  **`FactorizesC ⟹ LMGc` 是假的。**

  这与 `AncestralInheritanceRouteB.lean:309` 把
  `FactorizesC_implies_LMGc_Gap` 只登记为 `Prop`（从不证）是一致的。

  ## 意义

  这是本会话发现的**第 13 处真实数学错误**，也是最严重的一个：
  它意味着 `AncestralInheritanceRouteB` 的核心路线
  （`FactorizesC ⟹ LMGc`）在撞子图上**不成立**。
  =========================================================================== -/

namespace FateV2.Predict.GapCE

open FateV2.Modeling
open Finset FateV2.Error FateV2.Predict.DAGFactorization
open FateV2.Modeling.Graph

theorem cP_rfl : ∀ w : Fin 3 → Bool, FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool) w
    = if w 0 = w 2 then (1 : ℝ) else 0 := fun _ => rfl

-- 统一形式：x ≡ false 时，mass S = #{w | w|_S = false 且 w0 = w2}
-- 对 S = {0}: 需 w0 = false，且 w0 = w2 ⟹ w2 = false，w1 自由 ⟹ 2
theorem m0 : FateV2.Predict.DAGFactorization.mass ({(0 : Fin 3)} : Finset (Fin 3))
    (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) = 2 := by
  simp only [FateV2.Predict.DAGFactorization.mass, cP_rfl, Finset.mem_singleton, forall_eq]
  rw [show (∑ w : Fin 3 → Bool, if w 0 = (fun _ : Fin 3 => false) 0 then (if w 0 = w 2 then (1:ℝ) else 0) else 0)
      = ∑ w : Fin 3 → Bool, if (w 0 = false ∧ w 0 = w 2) then (1:ℝ) else 0 from by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : w 0 = false <;> by_cases h2 : w 0 = w 2 <;> simp [h1, h2]]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 0 = false ∧ w 0 = w 2)).card = 2 := by decide
  rw [hc]; norm_num

-- S = {2}: 需 w2 = false，且 w0 = w2 ⟹ w0 = false，w1 自由 ⟹ 2
theorem m2 : FateV2.Predict.DAGFactorization.mass ({2} : Finset (Fin 3))
    (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) = 2 := by
  simp only [FateV2.Predict.DAGFactorization.mass, cP_rfl, Finset.mem_singleton, forall_eq]
  rw [show (∑ w : Fin 3 → Bool, if w 2 = (fun _ : Fin 3 => false) 2 then (if w 0 = w 2 then (1:ℝ) else 0) else 0)
      = ∑ w : Fin 3 → Bool, if (w 2 = false ∧ w 0 = w 2) then (1:ℝ) else 0 from by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : w 2 = false <;> by_cases h2 : w 0 = w 2 <;> simp [h1, h2]]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 2 = false ∧ w 0 = w 2)).card = 2 := by decide
  rw [hc]; norm_num

-- S = ∅: ∑ w, (if w0 = w2 then 1 else 0) = #{w | w0 = w2} = 4
theorem mempty : FateV2.Predict.DAGFactorization.mass (∅ : Finset (Fin 3))
    (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) = 4 := by
  unfold FateV2.Predict.DAGFactorization.mass
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true, cP_rfl]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 0 = w 2)).card = 4 := by decide
  rw [hc]; norm_num

-- S = {0,2}: 需 w0 = false 且 w2 = false，且 w0 = w2 ✓，w1 自由 ⟹ 2
theorem m02 : FateV2.Predict.DAGFactorization.mass ({0, 2} : Finset (Fin 3))
    (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) = 2 := by
  simp only [FateV2.Predict.DAGFactorization.mass, cP_rfl]
  have key : ∀ w : Fin 3 → Bool,
      (if (∀ u ∈ ({0, 2} : Finset (Fin 3)), w u = (fun _ : Fin 3 => false) u)
        then (if w 0 = w 2 then (1:ℝ) else 0) else 0)
      = if (w 0 = false ∧ w 2 = false ∧ w 0 = w 2) then (1:ℝ) else 0 := by
    intro w
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, Fin.isValue]
    by_cases h1 : w 0 = false <;> by_cases h2 : w 2 = false <;> by_cases h3 : w 0 = w 2 <;>
      simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun w _ => key w), Finset.sum_boole]
  have hc : (Finset.univ.filter (fun w : Fin 3 → Bool => w 0 = false ∧ w 2 = false ∧ w 0 = w 2)).card = 2 := by
    decide
  rw [hc]; norm_num


-- ⭐ 结论：LMGc 在 v = 0 处失败
theorem lmgc_fails_at_0 :
    FateV2.Predict.DAGFactorization.mass ({(0 : Fin 3)} : Finset (Fin 3))
      (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) *
    FateV2.Predict.DAGFactorization.mass ({2} : Finset (Fin 3))
      (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) ≠
    FateV2.Predict.DAGFactorization.mass (∅ : Finset (Fin 3))
      (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) *
    FateV2.Predict.DAGFactorization.mass ({0, 2} : Finset (Fin 3))
      (FateV2.Predict.ThreeNodeFactorizes.colliderP (α := Bool)) (fun _ : Fin 3 => false) := by
  rw [m0, m2, mempty, m02]
  norm_num

end FateV2.Predict.GapCE
