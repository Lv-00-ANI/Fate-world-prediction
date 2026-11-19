import FateWorld.FateV2.Predict.BarSdiffIndep
/-!
  # Predict · SinkPeelGeneralRefutation

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SinkPeelGeneralRefutation.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BarSdiffIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `sink_peel` 的**一般反证**（不是特例，是结构性证伪）

  ## 结果

  ```lean
  theorem sink_peel_general_refutation (hsT : s ∈ T)
      (hfs : f s 只读 s) (hft : tail f T 只依赖 univ \ T)
      (hfsxy : f s x = f s y) (hne : bar T f x ≠ bar T f y) :
      ¬ (∀ z, bar T f z = bar (T \ {s}) f (unpin s z (z s)) * f s z)
  ```

  ## 意义

  **⟹ 只要左边 `bar T f` 依赖 `x`，而 `f s` 在 x、y 处相同，`sink_peel` 的等式就不成立。**

  这不是某个特定图的偶然失败，而是**结构性的**：

  * `bar (T\{s}) f` 与 `x` 无关（`Fate/BarSdiffIndep.lean`）
  * 故 `sink_peel` 右边 = 常数 × `f s z`
  * 而左边 `bar T f z` 一般不是 `f s z` 的常数倍

  ⟹ **`sink_peel` 需要额外的结构假设（如 `bar T f` 恰是 `f s` 的常数倍），
     而非单纯的「补因子」或「加局部性前提」。**

  ## 与特例反证的关系

  `Fate/SinkPeelCounterexample.lean` 给的是具体数值反例；
  本文件给的是**参数化**的反证条件。
  =========================================================================== -/

namespace FateV2.Predict.C19

open FateV2.Modeling
open Finset FateV2.Error FateV2.Predict.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

open FateV2.Predict.S9Fixed

-- ⭐ sink_peel 的一般反证：
-- 若 bar T f 依赖 x，而 f s 不依赖 x（在 x y 上相等），则 sink_peel 不成立
theorem sink_peel_general_refutation {T : Finset V} {s : V} (hsT : s ∈ T)
    {f : V → (V → α) → ℝ}
    (hfs : ∀ w w' : V → α, w s = w' s → f s w = f s w')
    (hft : ∀ w w' : V → α, (∀ u ∈ univ \ T, w u = w' u) → tail f T w = tail f T w')
    {x y : V → α} (hfsxy : f s x = f s y)
    (hne : bar T f x ≠ bar T f y) :
    ¬ (∀ z : V → α, bar T f z = bar (T \ {s}) f (FateV2.Predict.DAGFactorization.unpin s z (z s)) * f s z) := by
  intro h
  have hx := h x
  have hy := h y
  have hind := FateV2.Predict.C18.bar_sdiff_indep hsT hfs hft
    (FateV2.Predict.DAGFactorization.unpin s x (x s)) (FateV2.Predict.DAGFactorization.unpin s y (y s))
  -- bar T f x = A * f s x, bar T f y = A * f s y, 且 f s x = f s y
  apply hne
  calc bar T f x
      = bar (T \ {s}) f (FateV2.Predict.DAGFactorization.unpin s x (x s)) * f s x := hx
    _ = bar (T \ {s}) f (FateV2.Predict.DAGFactorization.unpin s y (y s)) * f s x := by rw [hind]
    _ = bar (T \ {s}) f (FateV2.Predict.DAGFactorization.unpin s y (y s)) * f s y := by rw [hfsxy]
    _ = bar T f y := hy.symm

end FateV2.Predict.C19
