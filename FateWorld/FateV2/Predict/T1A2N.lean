import FateWorld.FateV2.Predict.T1A2
import FateWorld.FateV2.Predict.T1A2CI
import FateWorld.FateV2.Modeling.CausDAG
import Mathlib.Tactic

/-!
  # Predict · T1A2N

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2N.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2, T1A2CI, _root.CausDAG
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/T1A2N` —— `T1A.2` 的抽象推广

## 内容

把 `T1A.2` 从**具体叉图**推广到**任意 DAG**。
-/

namespace FateV2.Predict.T1A2N

open FateV2.Modeling

open Finset
open Fate.T1A2

/-- ⭐⭐⭐⭐ **`T1A.2` 的**完全抽象版**（对任意 DAG、任意 `S`）：

若 `p` 在 `G` 上因子分解，则对**任意** `S : Finset V`，`p` 可分离。

**⚠ 这实际上就是 `factorizesOn_separable` 的显式命名，**
**但它是**推广**的锚点：从「叉图的 `{0,2}` vs `{1}`」推广到「任意 `S` vs `Sᶜ`」。** -/
theorem t1a2_abstract
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) (x : V → Bool) :
    ∃ π : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      ∀ S : Finset V, p x = (∏ v ∈ S, π v x) * (∏ v ∈ Sᶜ, π v x) :=
  Fate.T1A2CI.factorizesOn_separable h x

/-- ⭐⭐⭐ **任意 `S` 的真子集情形也成立**（对 `S = ∅` 与 `S = univ` 的退化检查）。 -/
theorem t1a2_abstract_degenerate
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) (x : V → Bool) :
    ∃ π : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      p x = (∏ v ∈ (∅ : Finset V), π v x) * (∏ v ∈ (∅ : Finset V)ᶜ, π v x) ∧
      p x = (∏ v ∈ (univ : Finset V), π v x) * (∏ v ∈ (univ : Finset V)ᶜ, π v x) := by
  obtain ⟨π, hreads, hpos, hsep⟩ := Fate.T1A2CI.factorizesOn_separable h x
  exact ⟨π, hreads, hpos, hsep ∅, hsep univ⟩

-- ⭐ **公理审计**
#print axioms t1a2_abstract
#print axioms t1a2_abstract_degenerate

end FateV2.Predict.T1A2N
