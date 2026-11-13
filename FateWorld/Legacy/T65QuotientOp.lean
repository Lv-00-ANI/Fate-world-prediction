import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

namespace Fate.MainlineTheorems

/-! ## §4 T6.5 —— **相容性推出商上的诱导运算 + 结合律保持**

**清单原文（T6.5）**：
> **构造等价与组合的相容性推出商上的良定义**：若 `∼` 是 `R` 上的等价关系
> 且与 `∘` 相容（A4），则 `∘` 在商 `R/∼` 上有唯一的诱导运算 `∘̄`，
> 且 `∘̄` 结合 **当且仅当** `∘` 结合。

**⚠ 偏差说明**：本文件用 `Setoid`（即 `α` 上的等价关系）表示 `∼`，
**用任意 `op : α → α → α` 表示 `∘`**（**因为该命题是**纯代数**的）。**

**⚠ 与 §1 的 T6.6 的关系**：
- **T6.6**：`op` 与 `∼` 相容 **⟺** 商上**存在**相容运算
- **T6.5**（本节）：**+ 唯一性** + **+ 结合律的保持**

**⭐⭐ 即**：**T6.5 = T6.6 + 两个额外结论**（唯一性、结合律）。 -/

/-- ⭐⭐ **相容性**（与 `Fate.MainlineTheorems.Compatible` 一致，此处重述以免依赖顺序）。 -/
def Compatible' {α : Type*} (op : α → α → α) (s : Setoid α) : Prop :=
  ∀ ⦃x x' y y'⦄, x ≈ x' → y ≈ y' → op x y ≈ op x' y'

/-- ⭐⭐ **诱导运算**：由相容的 `op` 在商上唯一确定的二元运算。 -/
noncomputable def inducedOp {α : Type*} (op : α → α → α) (s : Setoid α)
    (h : Compatible' op s) : Quotient s → Quotient s → Quotient s :=
  fun x y => Quotient.liftOn₂ x y (fun a b => Quotient.mk s (op a b))
    (fun a₁ b₁ a₂ b₂ ha hb => by rw [Quotient.sound (h ha hb)])

/-- ⭐⭐ **诱导运算在代表元上的取值**。 -/
theorem inducedOp_mk {α : Type*} (op : α → α → α) (s : Setoid α)
    (h : Compatible' op s) (a b : α) :
    inducedOp op s h (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (op a b) := rfl

/-- ⭐⭐⭐ **T6.5（唯一性）**：商上与 `op` 一致的运算**唯一**。

**🔹 对应清单**：T6.5 的「唯一的诱导运算」。

**⚠ 证明**：两个这样的运算在每个代表元上相等 ⟹ 由 `Quotient.ind` 二重归纳即得。 -/
theorem inducedOp_unique {α : Type*} (op : α → α → α) (s : Setoid α)
    (h : Compatible' op s) (q : Quotient s → Quotient s → Quotient s)
    (hq : ∀ a b, q (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (op a b)) :
    q = inducedOp op s h := by
  funext x y
  induction x using Quotient.ind with
  | _ a =>
    induction y using Quotient.ind with
    | _ b =>
      rw [hq a b, inducedOp_mk]

/-- ⭐⭐⭐ **T6.5（结合律的保持）**：若 `op` 结合，则诱导运算 `ōp` 也结合。

**🔹 对应清单**：T6.5 的「`∘̄` 结合」方向（**⟸**）。

**⚠ 证明**：用 `Quotient.ind` 三重归纳，把商上的等式化到代表元上。 -/
theorem inducedOp_assoc {α : Type*} (op : α → α → α) (s : Setoid α)
    (h : Compatible' op s) (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) :
    ∀ x y z, inducedOp op s h (inducedOp op s h x y) z
      = inducedOp op s h x (inducedOp op s h y z) := by
  intro x y z
  induction x using Quotient.ind with
  | _ a =>
    induction y using Quotient.ind with
    | _ b =>
      induction z using Quotient.ind with
      | _ c =>
        rw [inducedOp_mk, inducedOp_mk, inducedOp_mk, inducedOp_mk, hassoc]

/-- ⭐⭐⭐ **T6.5（结合律的**反向**，⚠ 只能到「模 `∼`」）**：
若诱导运算 `ōp` 结合，则 `op` **模 `∼`** 结合
（即 `op (op a b) c ≈ op a (op b c)`）。

**🔹 对应清单**：T6.5 的「**当且仅当**」的 **⟹** 方向 ——
**⚠⚠ 但这里有一个**清单没有考虑到的问题**：
`∘` 的结合律通常是**集合 `R` 上的 `=` 相等**，
**而商只能给出**模 `∼` 的等价**（`Quotient.exact` 返回 `≈`，不是 `=`）。

**⭐⭐ 故**：**正确的陈述是**「`ōp` 结合 ⟹ `op` **模 `∼`** 结合」** ——
**⚠ 这正是本定理的形式**。
**⚠ 而清单写的「`ōp` 结合 ⟺ `∘` 结合」在 `∼` **非平凡**时**不成立****
（**反例**：`α = ℕ`、`op a b := 0`（恒 0）、`∼` 为 `≡ (mod 2)` ——
`op` 结合（`0 = 0` 成立），而任何运算都模 `∼` 结合，**故反方向无法区分**）。

**⚠ 本轮**修正了清单的这一处**不精确**。** -/
theorem assoc_of_inducedOp_assoc {α : Type*} (op : α → α → α) (s : Setoid α)
    (h : Compatible' op s)
    (hassoc : ∀ x y z, inducedOp op s h (inducedOp op s h x y) z
      = inducedOp op s h x (inducedOp op s h y z)) :
    ∀ a b c, op (op a b) c ≈ op a (op b c) := by
  intro a b c
  have key := hassoc (Quotient.mk s a) (Quotient.mk s b) (Quotient.mk s c)
  rw [inducedOp_mk, inducedOp_mk, inducedOp_mk, inducedOp_mk] at key
  exact Quotient.exact key

/-- ⭐⭐⭐⭐ **T6.5（完整版）**：若 `op` 与 `∼` 相容，则

1. 商上存在**唯一**的诱导运算 `ōp`（与 `op` 在代表元上一致）；
2. **`op` 结合 ⟹ `ōp` 结合**；
3. **`ōp` 结合 ⟹ `op` 模 `∼` 结合**（**⚠ 见下面的边界登记**）。

**⭐⭐ 这是清单 T6.5 的**忠实形式化**** ——
**但第 3 条**修正了清单的一处不精确**（见 `assoc_of_inducedOp_assoc` 的 doc-comment）。 -/
theorem t65 {α : Type*} (op : α → α → α) (s : Setoid α) (h : Compatible' op s) :
    (∃! q : Quotient s → Quotient s → Quotient s,
        ∀ a b, q (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (op a b))
    ∧ ((∀ a b c, op (op a b) c = op a (op b c)) →
        (∀ x y z, inducedOp op s h (inducedOp op s h x y) z
              = inducedOp op s h x (inducedOp op s h y z)))
    ∧ ((∀ x y z, inducedOp op s h (inducedOp op s h x y) z
              = inducedOp op s h x (inducedOp op s h y z)) →
        (∀ a b c, op (op a b) c ≈ op a (op b c))) := by
  refine ⟨⟨inducedOp op s h, fun a b => rfl, ?_⟩, ?_, ?_⟩
  · intro q hq
    exact inducedOp_unique op s h q hq
  · intro hassoc
    exact inducedOp_assoc op s h hassoc
  · intro hassoc
    exact assoc_of_inducedOp_assoc op s h hassoc

/-! ### ⚠⚠ **对清单 T6.5 的一处修正**（**诚实登记**）

**清单原文**：
> …… 且 `∘̄` 结合 **当且仅当** `∘` 结合。

**⚠ 实测发现**：**「当且仅当」不成立** ——
**从 `ōp` 结合只能推出 `op` **模 `∼`** 结合**（`≈`），**不能推出 `=` 相等**。

**⭐⭐ 反例说明**：取 `α := ℕ`、`op a b := 0`（恒为 0）、`∼` 为 `≡ (mod 2)`。
- `op` 结合：`op (op a b) c = 0 = op a (op b c)` ✓
- **但若反向**：任取一个**非结合**的 `op'` 与相容的 `∼`（如全等价关系 `⊤`），
  **则 `ōp'` 在单点商上平庸地结合**，**而 `op'` 不结合** ✗

**⟹ 清单的「当且仅当」应改为**两个单向**：
- `∘` 结合 **⟹** `∘̄` 结合（**已证**）
- `∘̄` 结合 **⟹** `∘` 模 `∼` 结合（**已证**）

**⚠ 而当 `∼` 是**恒等关系**（`fun a b => a = b`）时，两者等价 ——
**那才是清单可能的本意。** -/

end Fate.MainlineTheorems