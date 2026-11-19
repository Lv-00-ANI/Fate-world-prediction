import FateWorld.FateV2.Predict.BarCorrected
import FateWorld.FateV2.Modeling.MultSUnify
import FateWorld.FateV2.Predict.FactorMarkov
/-!
  # Predict · MassMultSBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassMultSBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BarCorrected, MultSUnify, FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `mass S g x = multS S x * g x`（当 `g` 只读 `S`）

  ## 背景：`sink_peel` 可能的问题

  `Fate/Strategy9SinkPeelNorm.lean` 的 `sink_peel` 声称：
    `bar T f x = bar (T \ {s}) f (unpin s x a₀) * f s x`

  当 `T = {s}` 时：
  * 左 = `mass {s} (∏_{v≠s} f v) x` —— 纤维大小 `|α|^(|V|-1)`
  * 右 = `(∑ w, ∏ v, f v w) · f s x` —— 全空间求和
  两者相差 `multS` 因子。**故原陈述可疑。**

  ## 本文件的关键引理

  `mass_eq_multS_of_reads`：若 `g` 只读 `S`，则
    `mass S g x = multS S x * g x`

  这是「`mass` ⟷ `multS`」的正式桥梁，是分析 `sink_peel` 的基础。

  ## 诚实边界

  本文件不声称 `sink_peel` 为假——需要进一步分析 `T` 一般时的情形。
  本文件只给出分析所需的工具。
  =========================================================================== -/

namespace FateV2.Predict.C8

open FateV2.Modeling
open Finset FateV2.Error FateV2.Predict.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

open FateV2.Predict.S9Fixed

-- ⭐ 正确版本：若 g 只读 S，则 mass S g x = multS S x * g x
-- 注意：g 只读 S 时，在 S-纤维上 g 是常数，所以每项都是 g x
-- 而纤维大小 = multS S x
theorem mass_eq_multS_of_reads {S : Finset V} {g : (V → α) → ℝ}
    (hg : ∀ w w', (∀ u ∈ S, w u = w' u) → g w = g w') (x : V → α) :
    mass S g x = FateV2.Predict.TowerExactLaw.multS S x * g x := by
  classical
  unfold FateV2.Predict.DAGFactorization.mass FateV2.Predict.TowerExactLaw.multS
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · rw [if_pos hw, if_pos hw, one_mul]
    rw [hg w x hw]
  · rw [if_neg hw, if_neg hw, zero_mul]

end FateV2.Predict.C8
