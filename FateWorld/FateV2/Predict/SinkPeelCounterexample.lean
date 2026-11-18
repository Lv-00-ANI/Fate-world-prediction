import FateWorld.FateV2.Predict.MassMultSBridge
import FateWorld.FateV2.Predict.BarCorrected
/-!
  # Predict · SinkPeelCounterexample

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SinkPeelCounterexample.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassMultSBridge, BarCorrected
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `sink_peel` 的**机检反例**（`T = {s}` 时不成立）

  ## 原定理（Fate/Strategy9SinkPeelNorm.lean，在 `T = {s}` 时失败）

  ```lean
  theorem sink_peel (hsT : s ∈ T) (hsink : ∀ w, ¬ G.edge s w) (x) (a₀) :
      bar T f x = bar (T \ {s}) f (unpin s x a₀) * f s x
  ```

  ## 反例（`V = Fin 1`、`α = Bool`、`f ≡ 1`、`T = {0}`、`s = 0`）

  * **左**：`bar {0} f x`
    - `tail f {0} = ∏ v ∈ univ \ {0}, 1 = ∏ v ∈ ∅ = 1`
    - `bar {0} f x = mass {0} 1 x`
    - `{0} = univ`（`V = Fin 1`），故 `= mass univ 1 x = 1`
  * **右**：`bar ∅ f (unpin 0 x a) * f 0 x`
    - `tail f ∅ = ∏ v ∈ univ, 1`
    - `bar ∅ f y = mass ∅ (∏ v, 1) y = ∑ w, 1 = 2`（`α = Bool`，2 个取值）
    - `* f 0 x = 1`
    - 故 `= 2`

  **1 ≠ 2 ⟹ sink_peel 在 `T = {s}` 时不成立。**

  ## 诊断

  左边是 **单个乘积** 乘以纤维大小（这里 `{0} = univ` 故为 1）；
  右边是**全体求和**（`mass ∅`）。

  **⟹ `sink_peel` 缺一个 `multS` 类因子**（或需要 `f s` 在某种意义下的常值性）。

  ## 诚实边界

  本文件只给 `T = {s}` 的反例。一般的 `T` 是否需要类似修正，**未验证**。
  =========================================================================== -/

namespace FateV2.Predict.C9

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization
open FateV2.Modeling.Graph

abbrev U := Fin 1
def f1 : U → (U → Bool) → ℝ := fun _ _ => 1

-- 左边 = 1
theorem lhs_eq (x : U → Bool) : Fate.S9Fixed.bar ({0} : Finset U) f1 x = 1 := by
  unfold Fate.S9Fixed.bar Fate.S9Fixed.tail
  -- 目标：mass {0} (fun w => ∏ v ∈ univ \ {0}, f1 v w) x = 1
  have h : (univ \ ({0} : Finset U)) = ∅ := by
    ext u; simp [Fin.eq_zero]
  rw [h]
  simp only [Finset.prod_empty]
  -- {0} = univ 在 U = Fin 1 上
  have h2 : ({0} : Finset U) = univ := by
    ext u; simp [Fin.eq_zero]
  rw [h2, Fate.DAGFactorization.mass_univ]

-- 右边 = 2
theorem rhs_eq (x : U → Bool) (a : Bool) :
    Fate.S9Fixed.bar (∅ : Finset U) f1 (Fate.DAGFactorization.unpin 0 x a) * f1 0 x = 2 := by
  unfold Fate.S9Fixed.bar Fate.S9Fixed.tail
  have h : (univ \ (∅ : Finset U)) = univ := Finset.sdiff_empty
  rw [h]
  rw [Fate.DAGFactorization.mass_empty]
  simp [f1, Fintype.card_fin, U]

end FateV2.Predict.C9
