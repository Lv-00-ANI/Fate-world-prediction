import FateWorld.FateV2.Rules.AlphaRulesLocal
/-!
  # Rules · AlphaOf

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaOf.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：AlphaRulesLocal
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `α` 的具体实现：由 `target` 构造的完整 `AlphaSpec` 实例

  ## 背景

  `InstanceChain.AlphaSpec` 有五条要求（S1–S5）。前一轮 `alphaStructure` 已证其合取。

  **本节把它们打包成一个具体的 `α : Alpha D C X Y`，并证明 `AlphaSpec α`。**

  ## 这个实现是什么

  ```lean
  def alphaOf (K : PatStruct X.Carrier L) (target : ...) : Alpha D C X Y :=
    fun _ => { partition := closedPartition K, rules := {localRuleAsLaw K c₀ target} }
  ```

  **⟹ 即**：
  * **忽略数据集 `d`**（划分与规则不依赖数据）
  * **划分** = `closedPartition K`（由 MVFCA 闭集诱导）
  * **规则** = 单条 `localRuleAsLaw`（只看局部域）

  ## ⚠ 诚实边界（必须写清）

  **这个实现忽略数据集 `d`** —— 即它不是「从数据学习」，而是「给定结构」。

  **⟹ 所以它满足 `AlphaSpec`，但**不是**「从数据学出规则」的算法。**

  **真正的 `α` 算法需要**：
  * `K` 从数据构造（`PatStruct` 的 `desc` 从数据估计）
  * `target` 从数据估计（条件分布 / 允许集）

  **⟹ 本节给出的是**「给定 `K` 与 `target` 时的完整 `AlphaSpec` 实例」**，
  **这是 `α` 的**结构闭合**，不是算法的实现。**

  **这符合作者裁决「降级 = 未证项记录」**：把「算法未给出」如实登记为缺口，
  而不是假装已实现。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Predict.AlphaMVFCA
open FateV2.Modeling
namespace AlphaMVFCA

open FateV2.Rules.MVFCA4
open MeasureTheory

universe u v

variable {L : Type v} [CompleteLattice L]
variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ### §0.1 ⭐ 由 `K` 与 `target` 构造的 `α` -/

/-- ⭐ **具体的 `α`**：给定模式结构 `K` 与允许集 `target`，构造 `Alpha`。

**⚠ 忽略数据集 `d`** —— 见文件头诚实边界。 -/
def alphaOf (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (target : Set X.Carrier → Set (Measure Y.Carrier)) : InstanceChain.Alpha (Type u) C X Y :=
  fun _ =>
    { partition := closedPartition K
      rules := {localRuleAsLaw K c₀ target} }

/-! ### §0.2 ⭐⭐ 主定理：满足 `AlphaSpec` -/

/-- ⭐⭐ **`alphaOf` 满足 `AlphaSpec`**（S1–S5 全部）。

**⚠ 需 `target` 处处非空**（对应 S5）。其余四条无需假设。 -/
theorem alphaOf_spec (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (target : Set X.Carrier → Set (Measure Y.Carrier))
    (ht : ∀ A : Set X.Carrier, (target A).Nonempty) :
    InstanceChain.AlphaSpec (alphaOf (C := C) (X := X) (Y := Y) K c₀ target) where
  covers := fun _ => closedPartition_covers K
  part_symm := fun _ => closedPartition_symm K
  part_trans := fun _ => closedPartition_trans K
  localize := fun _ => rulesLocal K target
  inhabited := fun _ => rulesInhabited K target ht

/-! ### §0.3 ⭐ 推论：直接用 `AlphaSpec` 的导出性质 -/

/-- ⭐ **`alphaOf` 的局部域覆盖全空间**（S1 的直接用法）。 -/
theorem alphaOf_covers (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (target : Set X.Carrier → Set (Measure Y.Carrier))
    (ht : ∀ A : Set X.Carrier, (target A).Nonempty) (d : Type u) (x : X.Carrier) :
    x ∈ (alphaOf (C := C) (X := X) (Y := Y) K c₀ target d).partition x :=
  (alphaOf_spec K c₀ target ht).class_refl d x

/-- ⭐ **同局部域内的状态，规则给出相同输出**（S4 的直接用法）。 -/
theorem alphaOf_local (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (target : Set X.Carrier → Set (Measure Y.Carrier))
    (ht : ∀ A : Set X.Carrier, (target A).Nonempty) (d : Type u)
    {x y : X.Carrier}
    (hxy : y ∈ (alphaOf (C := C) (X := X) (Y := Y) K c₀ target d).partition x)
    (r : FateV2.Rules.LawRule.LawRule C X Y)
    (hr : r ∈ (alphaOf (C := C) (X := X) (Y := Y) K c₀ target d).rules)
    (c : C.Carrier) :
    r c x = r c y :=
  (alphaOf_spec K c₀ target ht).local_rules_apply d (r := r) hr c hxy

/-! ### §0.4 ⚠ 缺口登记：算法未给出 -/

/-- **⚠ 缺口：`K` 从数据构造**（`PatStruct.desc` 的估计），未实现。 -/
def LearnKGap (D : Type u) : Prop :=
  ∃ (learn : D → PatStruct X.Carrier L), True

/-- **⚠ 缺口：`target` 从数据估计**，未实现。 -/
def LearnTargetGap (D : Type u) : Prop :=
  ∃ (learn : D → (Set X.Carrier → Set (Measure Y.Carrier))), True

end AlphaMVFCA

end FateV2.Rules
