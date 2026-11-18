import FateWorld.FateV2.Predict.LMGcDirectRoute
import FateWorld.FateV2.Predict.MassInsertCorrected
import FateWorld.FateV2.Predict.FactorMarkov
/-!
  # Predict · MassOfReadsCover

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassOfReadsCover.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LMGcDirectRoute, MassInsertCorrected, FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⭐ `mass S p x = |α|^(|V| - |S|) * p x`（当所有因子只读 `S` 时）

  ## 背景

  `Fate/LMGcDirectRoute.lean` 指出：`zEquiv` 路线不通，
  应当用 `mass` 的「因子分解 + 读集」**直接计算**。

  ## 本文件（核心引理）

  ```lean
  theorem mass_eq_of_reads_cover (hfac : p = ∏ v, ψ v)
      (hread : ∀ v, ψ v 只读 S) (x) :
      mass S p x = |α|^(|V| - |S|) * p x
  ```

  ## 证明

  1. `p = ∏ ψ`（`hfac`）
  2. `∏ ψ` 只读 `S`（由每个 `ψ v` 只读 `S`）
  3. `mass_self_insert` ⟹ `mass S (∏ ψ) x = |α|^(|V|-|S|) · (∏ ψ)(extEnd S x ...)`
  4. `extEnd S x ...` 与 `x` 在 `S` 上一致 ⟹ `∏ ψ` 在该点取值 = `p x`

  ## 用途

  这是 `LMGc` 直接计算路线的基础：
  `LMGc` 的四个 `mass` 都形如 `mass S p x`，其中 `S ∈ {{v}, pa v, {v}∪pa v, nd v, {v}∪nd v}`。
  只要各因子在这些 `S` 上「读集覆盖」，就能把 `mass` 化成 `|α|` 幂乘以 `p x`，
  再用 `card_balance` 配平指数。
  =========================================================================== -/

namespace FateV2.Predict.Direct

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization FateV2.Predict.View19
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- 思路：
-- p = ∏ φ v（Factorizes）
-- 对 S ⊆ V，mass S p x = ?
-- 若所有 φ v（v ∉ S 的）都只读 S，则 mass S p x = ∏_{v ∉ S} φ v x * mass S (∏_{v ∈ S} φ v) x
-- 而 ∏_{v ∈ S} φ v 只读 S ⟹ mass S (...) x = |α|^(|V|-|S|) * ∏_{v ∈ S} φ v x

-- 所以 KEY：若 ∀ v, readSet v ⊆ S，则 mass S p x = |α|^(|V|-|S|) * p x
theorem mass_eq_of_reads_cover {S : Finset V} {ψ : V → (V → α) → ℝ}
    {p : (V → α) → ℝ} (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : ∀ v, ∀ w w', (∀ u ∈ S, w u = w' u) → ψ v w = ψ v w')
    (x : V → α) :
    mass S p x = ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card)) * p x := by
  have hg : ∀ w w', (∀ u ∈ S, w u = w' u) → (∏ v, ψ v w) = (∏ v, ψ v w') := by
    intro w w' h
    exact Finset.prod_congr rfl fun v _ => hread v w w' h
  -- 把 mass S p x 换成 mass S (∏ ψ) x
  have hpeq : p = fun w => ∏ v, ψ v w := funext hfac
  rw [hpeq, Fate.S13HoistFixed.mass_self_insert hg x]
  congr 1
  -- extEnd S x (x|_S) 与 x 在 S 上一致，故 ∏ ψ 相等
  refine Finset.prod_congr rfl fun v _ => ?_
  exact hread v _ _ (fun u hu => by
    rw [FateV2.Predict.GraphToProbView7.extEnd_of_mem S x _ u hu])

end FateV2.Predict.Direct
