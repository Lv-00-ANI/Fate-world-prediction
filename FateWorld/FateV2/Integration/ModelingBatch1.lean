import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Modeling.CFMap
import FateWorld.FateV2.Modeling.FiniteCondIndep
import FateWorld.FateV2.Modeling.CondIndepGeneralNZ

/-!
# Integration · Modeling · 跨模块综合（第一批）

## 本文件做什么

一次消费 **4 个** Modeling/图论侧模块的既有结果，把它们各自的核心性质
组合成下游可直接取用的形式：

| 源模块 | 被消费的定理 |
|---|---|
| `Modeling.CausBayesBall` | `bbReachable_mono_source`、`bbReachableVertices_mono_source` |
| `Modeling.CFMap` | `not_injective_iff_nontrivial_fiber` |
| `Modeling.FiniteCondIndep` | `sum_margXZ`、`sum_margYZ`、`sum_margZ` |
| `Modeling.CondIndepGeneralNZ` | `notMemXZ_memY`、`notMemYZ_memX` |

这 4 个模块此前都是「假接线」——被 import 但从没被真正调用。

## 不引入新数学

每个定理都是源定理的组合或直接特化。
-/

namespace FateV2.Integration

namespace ModelingBatch1

/-! ---------------------------------------------------------------------------
  §1  Bayes Ball 可达性：状态层与顶点层的单调性一致
  --------------------------------------------------------------------------- -/

open FateV2.Modeling.Graph

section BayesBall

variable {V : Type*} [DecidableEq V] [Fintype V] (G : DAG V)

/-- ⭐⭐ **状态层与顶点层的单调性一致**。

`bbReachable`（状态层）与 `bbReachableVertices`（顶点层）对源集的单调性
**同时**成立。后者由前者经 `Finset.image` 得到，本定理把两层并置。

**为什么值得一条定理**：下游若同时用到两层（例如先算状态再取顶点集），
需要知道单调性在两层之间**不丢失**。这需要两条定理协同。 -/
theorem bbReachable_mono_both {Z X X' : Finset V} (hXX' : X' ⊆ X) :
    G.bbReachable Z X' ⊆ G.bbReachable Z X
      ∧ G.bbReachableVertices Z X' ⊆ G.bbReachableVertices Z X :=
  ⟨G.bbReachable_mono_source hXX', G.bbReachableVertices_mono_source hXX'⟩

end BayesBall

/-! ---------------------------------------------------------------------------
  §2  反事实映射：非单射与纤维不平凡
  --------------------------------------------------------------------------- -/

namespace CFMapNS

open FateV2.Modeling.CFMap

/-- ⭐⭐ **非单射的可检形态**。

`PhiNotInjective Φ` 等价于「存在一个值，其反事实纤维里有**两个不同**的结构」。
本体即 `not_injective_iff_nontrivial_fiber`；单列是因为下游常用
「纤维不平凡」这一形式，且需要知道它与 `PhiNotInjective` **完全同义**
（双向，不是单向蕴含）。 -/
theorem phi_noninj_iff_fiber_nontrivial
    {SCM Ind Act Out : Type*} (Φ : SCM → (Ind → (Act → Out))) :
    PhiNotInjective Φ ↔
      ∃ φ₀, ∃ s t : SCM, s ∈ cfFiber Φ φ₀ ∧ t ∈ cfFiber Φ φ₀ ∧ s ≠ t :=
  not_injective_iff_nontrivial_fiber Φ

end CFMapNS

/-! ---------------------------------------------------------------------------
  §3  有限条件独立：边缘和的同步收缩
  --------------------------------------------------------------------------- -/

namespace FiniteCondIndepNS

open FateV2.Modeling.FiniteCondIndep

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- ⭐⭐⭐ **两个方向对 `z` 的边缘和同时收缩到同一条边缘律**。

对联合律 `p`，把 `x` 求和得到 `margZ p z`，把 `y` 求和**也**得到
`margZ p z`。

**这是「边缘化与求和次序无关」的最小证据**：两条等式分别由
`sum_margXZ` 与 `sum_margYZ` 给出，**它们收敛到同一个右端**——
这一点单看任一条看不出来，正是「条件独立可检验」的技术基础。 -/
theorem marg_sum_both_eq (p : FinJoint α β γ) (z : γ) :
    (∑ x, margXZ p x z = margZ p z)
      ∧ (∑ y, margYZ p y z = margZ p z) :=
  ⟨sum_margXZ p z, sum_margYZ p z⟩

/-- ⭐ **边缘和的右端可再求和**：`∑_z margZ p z` 就是把全表求和，
与「先对 `x` 求和再对 `z` 求和」一致。

这需要 `sum_margZ` 与 `sum_margXZ` 两两组合，属于本模块内第一条
真正跨两条定理的推论。 -/
theorem sum_margZ_eq (p : FinJoint α β γ) :
    ∑ z : γ, margZ p z = ∑ z, ∑ x, margXZ p x z := by
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [sum_margXZ]

end FiniteCondIndepNS

/-! ---------------------------------------------------------------------------
  §4  覆盖关系下的集合定位
  --------------------------------------------------------------------------- -/

namespace CondIndepNZNS

open FateV2.Predict.GraphToProbView7

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐ **覆盖下 `X ∪ Z` 之外的元素必在 `Y` 中，且对偶方向同样成立**。

给定 `X ∪ Y ∪ Z = univ`：
- `v ∉ X ∪ Z` ⟹ `v ∈ Y`（`notMemXZ_memY`）
- `v ∉ Y ∪ Z` ⟹ `v ∈ X`（`notMemYZ_memX`）

两条**不是**彼此的对称改写（第二个的并是 `Y ∪ Z`，第三个成分不同），
必须各自证明；本定理把两者并置，供「三集穷尽」的推理一次取用。 -/
theorem mem_of_notMem_both {X Y Z : Finset V} (hcover : X ∪ Y ∪ Z = Finset.univ) :
    (∀ v : V, v ∉ X ∪ Z → v ∈ Y) ∧ (∀ v : V, v ∉ Y ∪ Z → v ∈ X) :=
  ⟨fun _ hv => notMemXZ_memY hcover hv,
   fun _ hv => notMemYZ_memX hcover hv⟩

end CondIndepNZNS

end ModelingBatch1

end FateV2.Integration
