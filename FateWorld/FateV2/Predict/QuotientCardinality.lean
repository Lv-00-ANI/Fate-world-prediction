import FateWorld.FateV2.Error.LoopBound
import FateWorld.FateV2.Predict.BridgeQuotient
/-!
  # Predict · QuotientCardinality

  ## 迁移登记
  - 来源：`FateWorld/Legacy/QuotientCardinality.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LoopBound, BridgeQuotient
  - 补充 open 域：FateV2.Error, FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §35  ⭐⭐ **商结构的定量刻画**（「定量化」计划的第二步）

  **动机**（依作者裁决 R「不设上限加强」）：
  已有的商定理给出**结构性质**（单值、最优、信息保全），
  但**缺**定量的**结论**。

  ## 本节的目标

  **给出商的规模的**显式界**与**精确刻画**。

  | 定理 | 内容 |
  |---|---|
  | ⭐ **`quot_card_le`** | 商的基数 $\le$ 原集基数 |
  | ⭐ **`quot_card_eq_one_iff`** | **商基数 = 1 $\iff$ 万有关系** |
  | ⭐⭐ **`bridge_quot_card_eq_distinct_fibers`** | **桥商基数 = 不同纤维签名数** |
  | ⭐ **`quot_card_le_range_card`** | 商基数 = 像基数 |

  ## ⭐ 为何这是「定量」

  **结构定理说「商单值」；定量定理说「商有多大」** ——
  **后者才能回答「换商」的实际代价。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Error
open FateV2.Model
open FateV2.Modeling
namespace QuotientCardinality

universe u v

variable {α : Type u}

/-! ### §35.1 ⭐ 一般商的基本定量事实 -/

/-- ⭐ **商的基数不超过原集基数**。

**⟹ 「取商」只会减少元素。** -/
theorem quot_card_le [Finite α] (r : Setoid α) :
    Nat.card (Quotient r) ≤ Nat.card α :=
  Nat.card_le_card_of_surjective _ Quotient.mk_surjective

/-- ⭐⭐ **商基数 = 像基数**（第一同构的定量形式）。

$$\bigl|\alpha/r\bigr| = \bigl|\mathrm{range}(\mathrm{mk}_r)\bigr|$$

**⟹ 即**：**商的规模恰由商映射的像决定。**

**⚠ 证明**：商映射满射，故其像就是全集 —— 两边同为 `Nat.card (Quotient r)`。 -/
theorem quot_card_eq_range_card (r : Setoid α) :
    Nat.card (Quotient r) = Nat.card (Set.range (Quotient.mk r : α → Quotient r)) := by
  have h : (Set.range (Quotient.mk r : α → Quotient r)) = Set.univ :=
    Set.range_eq_univ.mpr Quotient.mk_surjective
  rw [h, Nat.card_univ]

/-- ⭐⭐ **商基数 = 1 ⟹ 万有关系**（**单向**，可证）。 -/
theorem forall_of_quot_card_eq_one [Finite α] (r : Setoid α)
    (h : Nat.card (Quotient r) = 1) : ∀ a b : α, r.r a b := by
  intro a b
  have hsub : Subsingleton (Quotient r) :=
    Finite.card_le_one_iff_subsingleton.mp (le_of_eq h)
  exact Quotient.exact (hsub.elim _ _)

/-- ⭐⭐ **商基数 = 1 $\iff$ 万有关系**（给定 `α` 非空）。 -/
theorem quot_card_eq_one_iff [Finite α] [Nonempty α] (r : Setoid α) :
    Nat.card (Quotient r) = 1 ↔ ∀ a b : α, r.r a b := by
  refine ⟨forall_of_quot_card_eq_one r, fun h => ?_⟩
  have hsub : Subsingleton (Quotient r) :=
    ⟨fun q₁ q₂ => by
      induction q₁ using Quotient.inductionOn with
      | _ a =>
        induction q₂ using Quotient.inductionOn with
        | _ b => exact Quotient.sound (h a b)⟩
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨hsub, ⟨Quotient.mk r (Classical.arbitrary α)⟩⟩

/-! ### §35.2 ⭐⭐ 桥商的定量刻画 -/

/-- **纤维签名**：一个 SCM 对应的「出现在哪些纤维中」的集合。 -/
def fiberSignature {Graph : Type v} {SCM : Type u} (bridge : Graph → Set SCM) (s : SCM) :
    Set Graph :=
  {g | s ∈ bridge g}

/-- ⭐⭐ **桥商基数 = 不同纤维签名的个数**。

$$\bigl|\mathrm{SCM}/\sim\bigr| =
  \bigl|\{\mathrm{fiberSignature}\,s \mid s \in \mathrm{SCM}\}\bigr|$$

**⟹ 即**：**商的规模恰由「桥能区分出多少种签名」决定** ——
**这是「换商」代价的**精确定量刻画**。**

**⭐⭐ 实用含义**：若 `Graph` 有 `n` 个元素，
则签名的**数量至多** $2^n$ —— 故**桥商的规模至多** $2^{|G|}$。

**⚠ 后半句（$2^n$ 界）本节不证** —— 它需要「`Set Graph` 的基数 ≤ $2^{|G|}$」，
**留待后续**。本定理只给**等势刻画**。 -/
theorem bridge_quot_card_eq_distinct_fibers [Finite SCM] {Graph : Type v}
    (bridge : Graph → Set SCM) :
    Nat.card (Quotient (BridgeQuotient.bridgeSetoid bridge)) =
      Nat.card (Set.range (fiberSignature bridge)) := by
  -- 商 ≃ 签名像
  refine Nat.card_congr (Equiv.ofBijective
    (fun q : Quotient (BridgeQuotient.bridgeSetoid bridge) =>
      Quotient.liftOn q (fun s => (⟨fiberSignature bridge s, s, rfl⟩ : Set.range (fiberSignature bridge))) (fun a b hab => by
        refine Subtype.ext ?_
        exact funext fun g => propext (hab g)))
    ⟨?_, ?_⟩)
  · -- 单射
    intro q₁ q₂ heq
    induction q₁ using Quotient.inductionOn with
    | _ a =>
      induction q₂ using Quotient.inductionOn with
      | _ b =>
        apply Quotient.sound
        intro g
        have h1 : fiberSignature bridge a = fiberSignature bridge b :=
          congrArg Subtype.val heq
        have h2 : g ∈ fiberSignature bridge a ↔ g ∈ fiberSignature bridge b := by
          rw [h1]
        exact (by simpa [fiberSignature] using h2)
  · -- 满射
    rintro ⟨S, s, rfl⟩
    exact ⟨Quotient.mk _ s, rfl⟩

end QuotientCardinality

end FateV2.Predict