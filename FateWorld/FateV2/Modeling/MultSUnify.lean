import FateWorld.FateV2.Predict.MassAEqCorrected
import FateWorld.FateV2.Predict.TowerExactLaw
/-!
  # Modeling · MultSUnify

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MultSUnify.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassAEqCorrected, TowerExactLaw
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `multS` = `|α|^(|V|-|S|)` —— 统一「mass 纤维大小」的两个表述

  ## 背景

  本会话发现 10 处真实数学错误，其中 4 处属于**同一系统性盲点**：
  把 `mass S`（`S ⊊ univ`）当作「单点求和」，漏掉 `|α|^(|V|-|S|)` 因子。

  `Fate/TowerExactLaw.lean` 已经用 `multS S x` 正确刻画了这个因子：
  ```lean
  noncomputable def multS (S) (x) : ℝ := ∑ w, if (∀ u ∈ S, w u = x u) then 1 else 0
  theorem mass_self_eq : mass S (mass S p) x = multS S x * mass S p x
  theorem multS_univ : multS univ x = 1
  theorem mass_self_fails (hm : multS S x ≠ 1) (hp : mass S p x ≠ 0) :
      mass S (mass S p) x ≠ mass S p x
  ```

  本会话的 `Fate/SubFibCard.lean` 用另一种表述算同一个量：
  `card_sub_fib' : #{w : ↥Z → α // w|_S = y} = |α|^(|Z|-|S|)`。

  ## 本文件

  `multS_eq_card_pow`：`multS S x = |α|^(|V|-|S|)`。

  **⟹ 这条把两个框架正式连接起来**，任何用到 `multS` 的地方都可以换成
  `|α|` 幂形式，反之亦然。
  =========================================================================== -/

namespace FateV2.Modeling.C6c

open FateV2.Predict
open Finset FateV2.Error FateV2.Predict.View19 FateV2.Predict.DAGFactorization
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- ⭐ 统一：multS 就是 |α|^(|V|-|S|)
theorem multS_eq_card_pow (S : Finset V) (x : V → α) :
    FateV2.Predict.TowerExactLaw.multS S x = ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card)) := by
  unfold FateV2.Predict.TowerExactLaw.multS
  rw [Finset.sum_boole]
  have h1 : (Finset.univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)).card
      = Fintype.card α ^ (Fintype.card V - S.card) := by
    rw [← FateV2.Predict.GraphToProbView7.card_subtype_fib S x]
    exact (Fintype.card_subtype (fun w : V → α => ∀ u ∈ S, w u = x u)).symm
  rw [h1]
  push_cast
  ring

end FateV2.Modeling.C6c
