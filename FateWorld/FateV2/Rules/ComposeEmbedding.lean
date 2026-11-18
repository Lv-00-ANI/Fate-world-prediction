/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ComposeEmbedding`
阶段：**裁决 1 要件 3「A 是 B（推广后）的特例」—— 读法三（嵌入）的判定**

---------------------------------------------------------------------------
(a) 作者裁决 1 的原话（第 465 轮，逐字）
---------------------------------------------------------------------------
> 「裁决1 b和a到底什么讲清楚 然后为什么不能构造一个融合的 以b为主导
>   **a是b（推广后）的一种特例**」
> 「那就可以」

---------------------------------------------------------------------------
(b) 三种读法
---------------------------------------------------------------------------
| 读法 | 含义 | 状态 |
|---|---|---|
| 一 | 顶层抽象 + B 族（`CommutativeComposite`）+ A 族（`DirectedComposite`），**并列** | `Fate/ComposeUnified.lean` 已实施 |
| 二 | **A 直接是 `CommutativeComposite` 的实例** | ❌ 数学上做不到（`A` 不可交换，`comp_comm` 会失败）|
| 三（本文件） | **存在编码 `enc : MeasurableRule → Set K3.MFCA`**，使 `enc (a.comp b) = combClosure (enc a) (enc b)`（A **嵌入** B） | **本文件判定** |

---------------------------------------------------------------------------
(c) 本文件证明了什么（只列**实际存在**的声明）
---------------------------------------------------------------------------
* `no_faithful_embedding` —— ⭐⭐⭐
  **不存在**单射（忠实）的 `enc : MeasurableRule CX SS2 SS2 → Set K3.MFCA`
  满足同态性 `enc (a.comp b) = combClosure (enc a) (enc b)`。

  即：**「读法三（忠实版）」不可能**。A 不是 B 的（忠实的）特例。

* `trivial_embedding_exists` —— ⭐⭐（**退化正面命题**）
  常函数 `enc := fun _ => ∅` 是**保持复合**的编码（需 `K3.closureOp ∅ = ∅`，
  取自 `AlphaConcreteInstance.takeConcept_eq_empty` + `takeConcept = closureOp`）。
  它**非单射**（把一切映到同一点），故与 `no_faithful_embedding` **不矛盾**。

* `hom_encoding_not_injective` —— §3，`no_faithful_embedding` 的等价重述。

**证明是纯代数的「交换性反向搬运」**：
1. `combClosure` 可交换（`ComposeSemantics.combClosure_commutable`）；
2. 由同态性得 `enc (a.comp b) = enc (b.comp a)`；
3. 由单射得 `a.comp b = b.comp a`（对**所有** `a b`）；
4. 与 `CompNotCommutative.comp_not_commutative`（不可交换）矛盾。

---------------------------------------------------------------------------
(d) 诚实边界（**必读**）
---------------------------------------------------------------------------
1. **本文件证明了「否命题」与一个「退化正面命题」**：
   * 忠实的嵌入**不存在**（`no_faithful_embedding`）；
   * **非忠实**（常函数）的嵌入**存在**（`trivial_embedding_exists`），
     但它把 A 的**全部信息压成一个点**（`∅`），故它是「特例」的**最弱可能形式**。
2. **强的正面「A 是 B 的特例」（即忠实的、无损的）【已证明为假】**
   （`no_faithful_embedding`）。故「a 是 b（推广后）的一种特例」这句原话，
   **只在「允许丢失全部信息」的意义下成立**，在「要求无损」的意义下**不成立**。
   **本文件不声称**该原话已在强意义下成立。
3. **本文件不声称「裁决 1 要件 3 已完全解决」**。
   它判定：读法三的**忠实版本不可能**、**退化的非忠实版本存在**；
   因此「是否把退化版本算作『特例』」需作者裁决。
4. **载体限制**：反例只对 `CX := CompNotCommutative.CX`（`Unit`）、
   `SS2 := CompNotCommutative.SS2`（`Fin 2`）成立，因为
   `comp_not_commutative` 就在这两个具体载体上。定理的陈述因此
   **只用这两个具体载体**，不冒充「对任意 `C X`」。
   这不削弱结论：**对具体一对载体就不存在**，则「对任意载体存在」为假。
5. **零 `sorry` / `admit` / `axiom`**。

---------------------------------------------------------------------------
(e) 同义反复自检
---------------------------------------------------------------------------
| 定理 | 前件 | 结论 | 判定 |
|---|---|---|---|
| `no_faithful_embedding` | 存在单射 `enc` 且保持复合 | 矛盾（假） | **真内容**：前件是**被反驳的对象**，不是把结论偷放进前件；证明用到一个**具体数值反例** |
| `trivial_embedding_exists` | 无（`K3`、`CX`、`SS2` 均为具体值） | `∃ enc, ∀ a b, enc (a.comp b) = combClosure (enc a) (enc b)` | **真内容**：显式构造 `fun _ => ∅`，并需 `closureOp ∅ = ∅`（引用已入链事实）；**结论不在前件** |
| `hom_encoding_not_injective` | `enc` 保持复合 | `¬ Injective enc` | **真内容**：**前件只是同态性**（不含量词于单射性），结论是「必不单射」——把 `no_faithful_embedding` 拆成**无蕴含式**的形态 |
-/

import FateWorld.FateV2.Rules.ComposeUnified
import FateWorld.FateV2.Rules.CompNotCommutative
namespace FateV2.Rules

open FateV2.Modeling
namespace ComposeEmbedding

open Fate.ComposeOperator

/-!
  # Rules · ComposeEmbedding

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ComposeEmbedding.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ComposeUnified, CompNotCommutative
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  ⭐⭐⭐ 主定理：忠实的嵌入不存在
    =========================================================================== -/

/- ⚠ 下文用具体载体 `CX`、`SS2`（来自 `Fate.CompNotCommutative`），
   因为「不可交换」这一事实就在这两个载体上被证实。 -/

/-- ⭐⭐⭐ **【裁决 1 要件 3 的判定：读法三（忠实嵌入）不可能】**

不存在一个**单射**编码 `enc : MeasurableRule CX SS2 SS2 → Set K3.MFCA`
使得 `enc` 把 `MeasurableRule.comp` **忠实映成** `combClosure`。

即：**A（概率核复合）不是 B（属性集合并+闭包）的（忠实的）特例。**

**证明**（纯代数，把交换性从 B 搬回 A）：
* 由 `hhom` 与 `combClosure` 的交换性得 `enc (a.comp b) = enc (b.comp a)`；
* 由 `hinj` 得 `a.comp b = b.comp a`，对**所有** `a b`；
* 与 `comp_not_commutative`（存在 `a b` 使 `b.comp a ≠ a.comp b`）矛盾。

**⚠ 边界**：本定理只否证**单射**编码；**非单射**（丢失信息）的编码**未被**排除
——事实上它存在，见 §2 的 `trivial_embedding_exists`（常函数 `fun _ => ∅`）。
两者 **不矛盾**：本定理说的就是「非单射的编码必然丢失全部或部分信息」。见文件头 (d)。 -/
theorem no_faithful_embedding :
    ¬ ∃ (enc : MeasurableRule Fate.CompNotCommutative.CX
        Fate.CompNotCommutative.SS2 Fate.CompNotCommutative.SS2
        → Set FateV2.Rules.AlphaInstance.K3.MFCA),
        Function.Injective enc
        ∧ (∀ (a b : MeasurableRule Fate.CompNotCommutative.CX
              Fate.CompNotCommutative.SS2 Fate.CompNotCommutative.SS2),
            enc (a.comp b)
              = FateV2.Rules.AlphaInstance.WiringFixed.combClosure (enc a) (enc b)) := by
  rintro ⟨enc, hinj, hhom⟩
  -- 反证：若有这样的 `enc`，则核复合必可交换
  apply Fate.CompNotCommutative.comp_not_commutative
  intro R₁ R₂
  -- 目标：`R₂.comp R₁ = R₁.comp R₂`
  apply hinj
  -- 归约为 `enc (R₂.comp R₁) = enc (R₁.comp R₂)`
  calc enc (R₂.comp R₁)
      = FateV2.Rules.AlphaInstance.WiringFixed.combClosure (enc R₂) (enc R₁) := hhom R₂ R₁
    _ = FateV2.Rules.AlphaInstance.WiringFixed.combClosure (enc R₁) (enc R₂) :=
          FateV2.Rules.ComposeSemantics.combClosure_commutable (enc R₂) (enc R₁)
    _ = enc (R₁.comp R₂) := (hhom R₁ R₂).symm

/-! ===========================================================================
    §2  正面（退化）结论：非忠实的编码存在
    =========================================================================== -/

/-- ⭐ **`K3` 上空集的闭包是空集**（`combClosure ∅ ∅ = ∅` 的技术基础）。

**来源**：`K3.takeConcept ∅ = ∅`（`AlphaConcreteInstance.takeConcept_eq_empty`，实测 `:209`）
而 `FormalCtx.takeConcept K = K.closureOp`（`Fate/Alpha.lean:302` 的定义展开）。 -/
theorem K3_closureOp_empty : FateV2.Rules.AlphaInstance.K3.closureOp
    (∅ : Set FateV2.Rules.AlphaInstance.K3.MFCA) = ∅ := by
  show FateV2.Rules.AlphaInstance.K3.takeConcept (∅ : Set FateV2.Rules.AlphaInstance.K3.MFCA) = ∅
  exact FateV2.Rules.AlphaInstance.takeConcept_eq_empty

/-- ⭐ **`combClosure ∅ ∅ = ∅`**（上面引理的 `combClosure` 形式）。 -/
theorem combClosure_empty_empty :
    FateV2.Rules.AlphaInstance.WiringFixed.combClosure
      (∅ : Set FateV2.Rules.AlphaInstance.K3.MFCA)
      (∅ : Set FateV2.Rules.AlphaInstance.K3.MFCA) = ∅ := by
  unfold FateV2.Rules.AlphaInstance.WiringFixed.combClosure
  rw [Set.union_empty]
  exact K3_closureOp_empty

/-- ⭐⭐ **【正面结论：读法三的退化版本成立】**

**存在**一个编码 `enc : MeasurableRule CX SS2 SS2 → Set K3.MFCA`
使得 `enc (a.comp b) = combClosure (enc a) (enc b)`——取常函数 `enc := fun _ => ∅`。

**⟹ 「A 是 B 的特例」在【不要求忠实】的意义下【成立】**。

**⚠ 这是「特例」的最弱形式**：`enc` **非单射**（把 A 的全部信息压到 `∅`），
故它与 `no_faithful_embedding` **不矛盾**。**本定理不声称 A 的信息被保存**。

**证明**：两边都归约为 `∅ = combClosure ∅ ∅`，由 `combClosure_empty_empty` 得证。 -/
theorem trivial_embedding_exists :
    ∃ (enc : MeasurableRule Fate.CompNotCommutative.CX
        Fate.CompNotCommutative.SS2 Fate.CompNotCommutative.SS2
        → Set FateV2.Rules.AlphaInstance.K3.MFCA),
        ∀ (a b : MeasurableRule Fate.CompNotCommutative.CX
              Fate.CompNotCommutative.SS2 Fate.CompNotCommutative.SS2),
            enc (a.comp b)
              = FateV2.Rules.AlphaInstance.WiringFixed.combClosure (enc a) (enc b) := by
  refine ⟨fun _ => ∅, ?_⟩
  intro a b
  exact (combClosure_empty_empty).symm

/-! ===========================================================================
    §3  推论：同态编码必不单射
    =========================================================================== -/

/-- ⭐ **等价表述**：任何**保持复合**（同态）的编码，只要它存在，就**必不单射**
（必然丢失信息）。

这是 `no_faithful_embedding` 的直接重写，便于下游引用。 -/
theorem hom_encoding_not_injective
    (enc : MeasurableRule Fate.CompNotCommutative.CX
        Fate.CompNotCommutative.SS2 Fate.CompNotCommutative.SS2
        → Set FateV2.Rules.AlphaInstance.K3.MFCA)
    (hhom : ∀ (a b : MeasurableRule Fate.CompNotCommutative.CX
              Fate.CompNotCommutative.SS2 Fate.CompNotCommutative.SS2),
            enc (a.comp b)
              = FateV2.Rules.AlphaInstance.WiringFixed.combClosure (enc a) (enc b)) :
    ¬ Function.Injective enc := by
  intro hinj
  exact no_faithful_embedding ⟨enc, hinj, hhom⟩

end ComposeEmbedding
end FateV2.Rules