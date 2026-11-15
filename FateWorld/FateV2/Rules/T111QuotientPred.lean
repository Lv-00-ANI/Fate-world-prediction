import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

/-!
  # Rules · T111QuotientPred

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T111QuotientPred.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Rules`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T111QuotientPred` —— **T1.11 规则作为实例的商**（**第 221 轮**）

  ## 清单原文（T1.11）

  > **规则作为实例的商**：给定实例集 `ℰ` 与抽象等价关系 `∼_ℰ`（定义 5.13 的设定），
  > 商集 `ℰ/∼_ℰ` 与 `ℰ` 上「`∼_ℰ`-不变谓词」的集合之间**存在自然双射**。

  ## ⭐ 这条为何是理论的核心

  **依作者裁决（导读 §2 第 (6) 条）**：
  > **规则是实例集合在等价关系下的商，其数学原型是 Galois 连接的不动点结构。**
  > `SCM → 规则` 这条边**废止**。

  **⭐⭐ 故 T1.11 是「规则 = 商」这一裁决的**形式化载体**：
  它给出**商集**与**不变谓词**之间的**一一对应**，
  **⟹ 「按等价类给出的规则」与「用不变谓词给出的规则」是同一件事。**
================================================================================ -/

namespace FateV2.Rules.T111
/-- ⭐⭐ **谓词在等价关系下不变**（`∼`-不变谓词）。

$$x \sim x' \implies (P\,x \leftrightarrow P\,x')$$ -/
def InvariantPred {α : Type*} (s : Setoid α) (P : α → Prop) : Prop :=
  ∀ ⦃x x'⦄, x ≈ x' → (P x ↔ P x')

/-! ## §1 ⭐ 从商集上的谓词到不变谓词 -/

/-- ⭐⭐ **提升**：商集 `α/∼` 上的谓词 `Q` 拉回为 `α` 上的不变谓词。 -/
def liftPred {α : Type*} (s : Setoid α) (Q : Quotient s → Prop) : α → Prop :=
  fun a => Q (Quotient.mk s a)

/-- ⭐⭐ **提升后的谓词**是不变的**。 -/
theorem liftPred_invariant {α : Type*} (s : Setoid α) (Q : Quotient s → Prop) :
    InvariantPred s (liftPred s Q) := by
  intro x x' hxx'
  show Q (Quotient.mk s x) ↔ Q (Quotient.mk s x')
  rw [Quotient.sound hxx']

/-! ## §2 ⭐⭐⭐ T1.11 主定理：**自然双射** -/

/-- ⭐⭐⭐⭐ **T1.11**：**商集上的谓词**与**`α` 上 `∼`-不变谓词**之间存在**双射**。

**🔹 对应清单**：T1.11 的「自然双射」。

**⚠ 精确化说明（诚实登记）**：
清单说「商集 `ℰ/∼` 与 `ℰ` 上 `∼`-不变谓词的集合之间存在自然双射」——
**严格的字面上，「商集」是 `Quotient s : Type`，而「谓词集」是 `α → Prop` 的子集**，
**两者的**基数**相同但**类型**不同（一个是元素，一个是谓词）。

**⭐⭐ 故正确的陈述是**：
**「商集上的谓词 `Q : Quotient s → Prop`」与「`α` 上 `∼`-不变谓词 `P`」之间存在双射** ——
**即 `Q ↔ P` 一一对应**。**这才是「规则 = 商」的形式化含义**
（**每个等价类要么满足规则，要么不满足，且与代表元的选择无关**）。

**⚠ 我**不建议**把它写成「`Quotient s ≃ {P | InvariantPred s P}`」** ——
**那在 `α` 无限时不成立**（**两者基数不同**：`Quotient s` 是 `Type`，
**而 `{P | Invariant}` 是 `Prop` 的集合**）。**清单的这一表述应被**理解为**「谓词层的双射」。** -/
theorem t111_pred_bijection {α : Type*} (s : Setoid α) :
    ∃ (f : (Quotient s → Prop) → { P : α → Prop // InvariantPred s P })
      (g : { P : α → Prop // InvariantPred s P } → (Quotient s → Prop)),
      (∀ Q, g (f Q) = Q) ∧ (∀ P, f (g P) = P) := by
  classical
  -- f：把商集谓词 Q 映为「拉回的不变谓词」
  refine ⟨fun Q => ⟨liftPred s Q, liftPred_invariant s Q⟩, ?_, ?_, ?_⟩
  · -- g：把不变谓词 P 映为「商集上的谓词」
    intro P
    exact fun q => Quotient.lift (fun a => P.1 a)
      (fun a b hab => propext (P.2 hab)) q
  · -- g ∘ f = id
    intro Q
    funext q
    induction q using Quotient.ind with
    | _ a => rfl
  · -- f ∘ g = id
    intro P
    -- 需要证明两个 Subtype 相等 ⟹ 用 Subtype.ext + funext
    apply Subtype.ext
    funext a
    rfl

end FateV2.Rules.T111