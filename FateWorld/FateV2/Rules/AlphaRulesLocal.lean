import FateWorld.FateV2.Predict.AlphaMVFCA
/-!
  # Rules · AlphaRulesLocal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaRulesLocal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：AlphaMVFCA
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `RulesLocal`：从局部域构造规则（`α` 的另一半）

  ## 背景

  `InstanceChain.RulesLocal p rs` 要求：
  ```lean
  ∀ r ∈ rs, ∀ c x y, y ∈ p x → r c x = r c y
  ```
  即「同局部域内，规则输出相同」。

  **这是「局部域」概念唯一有内容的约束。**

  ## 本节的关键构造

  **让规则只看局部域，而不是看原始状态。**

  给定：
  * `K : PatStruct G L`（提供 `minClosed`）
  * `target : Set G → Set (Measure Y)`（**按局部域给出允许分布**）

  定义：
  ```lean
  localRuleAsLaw K c₀ target := fun c x => target (minClosed K x)
  ```

  **⟹ 由定义即得**：`minClosed K x = minClosed K y ⟹ localRule x = localRule y`。

  **这正是 `RulesLocal` 的要求。**

  ## ⚠ 桥接假设（显式给出）

  **`G := X.Carrier`** —— 即「MVFCA 的对象集」就是「状态空间的载体」。

  这**不是自动的**，故作为**类型参数固定**：本节所有定理都在 `G = X.Carrier` 下陈述。
  这样避免了 `ident : X.Carrier → G` 这个额外映射，也就避免了「`ident` 需与划分相容」这个前提。

  ## 为什么这个构造不是「把结论写进前件」

  **`RulesLocal` 的内容是**：「规则只通过局部域看状态」。

  **本节的做法是**：**显式地构造**一个只通过局部域看状态的规则
  （`target` 的参数就是 `Set G`，即局部域本身）。**这不是假设，是构造。**

  ## 诚实边界

  * **这个构造是平凡的**（忘掉细粒度）。价值在于「证明可共存」，不是「给出算法」。
  * **`target` 从哪来**未解决（`α` 的算法问题，仍是 H-C）。
  * **`RulesInhabited` 需 `target` 非空** —— 真实前提，不是技巧。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
open FateV2.Predict.AlphaMVFCA
namespace AlphaMVFCA

open FateV2.Rules.MVFCA4
open MeasureTheory

universe u v

variable {L : Type v} [CompleteLattice L]
variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ### §0.1 ⭐ 局部域规则（`G := X.Carrier`） -/

/-- ⭐ **按局部域构造的规则**：`x ↦ target (minClosed K x)`。

**关键**：`target` 的定义域是 `Set X.Carrier`（局部域），**不是**单个状态。
故规则**只通过局部域看状态**。

⚠ **这个构造是平凡的**（忘掉细粒度），其价值是证明可共存。 -/
def localRuleAsLaw (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (target : Set X.Carrier → Set (Measure Y.Carrier)) : FateV2.Rules.LawRule.LawRule C X Y :=
  fun _ x => target (minClosed K x)

/-! ### §0.2 ⭐⭐ 主定理：`RulesLocal` 成立 -/

/-- ⭐⭐ **同局部域内的状态给出相同输出**。

**证明**：`y ∈ closedPartition K x` 即 `minClosed K y = minClosed K x`，
故 `target (minClosed K y) = target (minClosed K x)`。

**⚠ 无需任何额外假设** —— 这是划分定义的直接推论。 -/
theorem localRuleAsLaw_eq_of_same_class (K : PatStruct X.Carrier L)
    (target : Set X.Carrier → Set (Measure Y.Carrier))
    {x y : X.Carrier} (hxy : y ∈ closedPartition K x)
    (c : C.Carrier) :
    localRuleAsLaw K c₀ target c x =
    localRuleAsLaw K c₀ target c y := by
  unfold localRuleAsLaw
  have h : minClosed K y = minClosed K x := hxy
  rw [h]

/-! ### §0.3 ⭐ 规则集形式的 `RulesLocal` -/

/-- ⭐⭐⭐ **`RulesLocal` 成立**（对由 `target` 构造的单规则集）。

**这是 `α` 的另一半：局部域划分与规则相容。** -/
theorem rulesLocal (K : PatStruct X.Carrier L)
    (target : Set X.Carrier → Set (Measure Y.Carrier)) :
    InstanceChain.RulesLocal (closedPartition K)
      {localRuleAsLaw K c₀ target} := by
  intro r hr c x y hxy
  rw [Set.mem_singleton_iff] at hr
  subst hr
  exact localRuleAsLaw_eq_of_same_class K target hxy c

/-! ### §0.4 ⭐ `RulesInhabited` 的条件 -/

/-- **`RulesInhabited` 的充分条件**：若 `target` 处处非空，则规则处处允许至少一个分布。

**⚠ `target` 非空是真实前提**（不是自动的）。 -/
theorem rulesInhabited (K : PatStruct X.Carrier L)
    (target : Set X.Carrier → Set (Measure Y.Carrier))
    (ht : ∀ A : Set X.Carrier, (target A).Nonempty) :
    InstanceChain.RulesInhabited (C := C) (X := X) (Y := Y)
      {localRuleAsLaw K c₀ target} := by
  intro r hr c x
  rw [Set.mem_singleton_iff] at hr
  subst hr
  exact ht (minClosed K x)

/-! ### §0.5 ⭐⭐ `α` 的两半合起来 -/

/-- ⭐⭐⭐ **`α` 的两半合起来**：给定的 `target` 与划分 `closedPartition K` 一起
满足 `RulesLocal`，且（在 `target` 处处非空时）满足 `RulesInhabited`。

**⟹ 这是 `α` 的第一个「结构上完整」的候选**：
划分合法（`closedPartition_spec`）+ 规则局部一致（本节）+ 规则非退化（前件）。

**⚠ 但 `target` 的内容仍是自由的** —— 本节只定结构，不定算法。 -/
theorem alphaStructure (K : PatStruct X.Carrier L)
    (target : Set X.Carrier → Set (Measure Y.Carrier))
    (ht : ∀ A : Set X.Carrier, (target A).Nonempty) :
    InstanceChain.PartitionCovers (closedPartition K) ∧
    InstanceChain.PartitionSymm (closedPartition K) ∧
    InstanceChain.PartitionTrans (closedPartition K) ∧
    InstanceChain.RulesLocal (closedPartition K)
      {localRuleAsLaw K c₀ target} ∧
    InstanceChain.RulesInhabited (C := C) (X := X) (Y := Y)
      {localRuleAsLaw K c₀ target} :=
  ⟨closedPartition_covers K, closedPartition_symm K, closedPartition_trans K,
   rulesLocal K target, rulesInhabited K target ht⟩

end AlphaMVFCA

end FateV2.Rules