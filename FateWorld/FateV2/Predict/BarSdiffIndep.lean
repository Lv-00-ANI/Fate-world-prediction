import FateWorld.FateV2.Predict.MassIndepOfCompl
import FateWorld.FateV2.Predict.BarSdiffEq
/-!
  # Predict · BarSdiffIndep

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BarSdiffIndep.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassIndepOfCompl, BarSdiffEq
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `sink_peel` 的**根本原因**：左边与 `x` 无关

  ## 结果

  ```lean
  theorem bar_sdiff_indep (hfs : f s 只读 s)
      (hft : tail f T 只依赖 univ \ T) (x y) :
      bar (T \ {s}) f x = bar (T \ {s}) f y
  ```

  **⟹ `bar (T\{s}) f` 完全不依赖 `x`。**

  ## 为什么这解释了 sink_peel 的反例

  `sink_peel` 声称：
    `bar T f x = bar (T\{s}) f (unpin s x a₀) * f s x`

  右边含 `bar (T\{s}) f (unpin s x a₀)`（与 `x` 无关，因上式）
  以及 `f s x`（依赖 `x`）。
  而左边 `bar T f x` 依赖 `x`。

  ⟹ 等式要求 `bar T f x / f s x` 是常数——这在一般情况下不成立。

  反例（`V = Fin 1`、`α = Bool`、`f ≡ 1`、`T = {0}`）：左 = 1，右 = 2。

  ## 证明

  `bar (T\{s}) f x = mass (T\{s}) (f_s · tail_T f) x`（`BarSdiffEq`）
  `f_s · tail_T f` 只依赖 `{s} ∪ (univ\T) = univ\(T\{s})`
  ⟹ 用 `mass_indep_of_reads_compl`（取 `T := T\{s}`）得与 `x` 无关。
  =========================================================================== -/

namespace FateV2.Predict.C18

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

open Fate.S9Fixed

-- ⭐ sink_peel 的正确结论：bar (T\{s}) f x 与 x 无关（当 f s 只读 s）
theorem bar_sdiff_indep {T : Finset V} {s : V} (hsT : s ∈ T)
    {f : V → (V → α) → ℝ}
    (hfs : ∀ w w' : V → α, w s = w' s → f s w = f s w')
    (hft : ∀ w w' : V → α, (∀ u ∈ univ \ T, w u = w' u) → tail f T w = tail f T w')
    (x y : V → α) : bar (T \ {s}) f x = bar (T \ {s}) f y := by
  rw [Fate.C15.bar_sdiff_eq hsT f x, Fate.C15.bar_sdiff_eq hsT f y]
  -- 用 mass_indep_of_reads_compl，取 T := T\{s}
  apply Fate.C17.mass_indep_of_reads_compl
  -- 需：g := fun w => f s w * tail f T w 只依赖 univ \ (T\{s})
  intro w w' h
  -- univ \ (T\{s}) = {s} ∪ (univ\T)
  have hset : (univ \ (T \ {s}) : Finset V) = insert s (univ \ T) := by
    rw [Finset.sdiff_singleton_eq_erase]
    exact Fate.C14.sdiff_erase_eq hsT
  -- w 与 w' 在 {s} ∪ (univ\T) 上一致
  have hws : w s = w' s := h s (by rw [hset]; exact Finset.mem_insert_self _ _)
  have hwt : ∀ u ∈ univ \ T, w u = w' u := fun u hu => h u (by rw [hset]; exact Finset.mem_insert_of_mem hu)
  rw [hfs w w' hws, hft w w' hwt]

end FateV2.Predict.C18
