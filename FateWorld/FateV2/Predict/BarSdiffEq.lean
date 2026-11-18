import FateWorld.FateV2.Predict.SdiffEraseEq
import FateWorld.FateV2.Predict.MassSdiffConst
/-!
  # Predict · BarSdiffEq

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BarSdiffEq.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SdiffEraseEq, MassSdiffConst
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `bar (T \ {s})` 的被积函数分解

  ## 结果

  ```lean
  theorem bar_sdiff_eq (hsT : s ∈ T) (f) (x) :
      bar (T \ {s}) f x = mass (T \ {s}) (fun w => f s w * tail f T w) x
  ```

  ## 意义

  `bar (T\{s})` 的被积函数 `∏_{v ∉ T\{s}} f v` 可以分解为 `f_s · ∏_{v ∉ T} f v`，
  利用补集恒等式 `univ\{T\{s}} = {s} ∪ (univ\T)`。

  这是 `sink_peel` 修正的第一个结构步骤。

  ## 诚实边界

  要把 `f_s` 从这个 `mass` 中提出来，需要额外条件。
  **本会话的分析表明**：`mass_sdiff_of_reads` 的假设（`g` 只依赖 `T\{s}`）
  与这里的 `f_s · tail f T`（只依赖补集 `univ\(T\{s})`）**方向相反**，
  故不能直接套用。完整的 `sink_peel` 修正仍需额外工作。
  =========================================================================== -/

namespace FateV2.Predict.C15

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

open Fate.S9Fixed

theorem bar_sdiff_eq {T : Finset V} {s : V} (hsT : s ∈ T)
    (f : V → (V → α) → ℝ) (x : V → α) :
    bar (T \ {s}) f x = mass (T \ {s}) (fun w => f s w * tail f T w) x := by
  unfold bar tail
  congr 1
  funext w
  have hset : (univ \ (T \ {s}) : Finset V) = insert s (univ \ T) := by
    rw [Finset.sdiff_singleton_eq_erase]
    exact Fate.C14.sdiff_erase_eq hsT
  rw [hset]
  rw [Finset.prod_insert]
  intro h
  exact absurd hsT (Finset.mem_sdiff.mp h).2

-- ⭐ 关键分析：tail f T 只读 univ\T，而 f s 只读 s
-- 所以 f s * tail f T 只读 {s} ∪ (univ\T) = univ \ (T\{s})
-- ⟹ 这正是 mass_sdiff_of_reads 所需的「只读 T\{s}」条件！

-- 但要证「只读 T\{s}」，需要 univ \ (T\{s}) 上的坐标决定其值
-- 而 univ \ (T\{s}) = {s} ∪ (univ\T) ✓ 正是所需

end FateV2.Predict.C15
