import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

namespace Fate.MainlineTheorems

/-! ## §1 T6.6 —— **商上的运算良定义性判别**

**清单原文（T6.6）**：
> **商上的运算良定义性判别**：给定的 `∘` 与 `∼` 相容，**当且仅当** `∘̄` 良定义。

**⚠ 偏差说明（诚实登记）**：清单用 `∘` 表示规则组合（`R₁ ∘ R₂`），
**而本文件用**抽象的二元运算** `op : α → α → α`** ——
**这是**更一般的**陈述（对任意 `op` 成立 ⟹ 对 `∘` 也成立）。**

**⚠ 技术依赖的说明**：
**本文件用 `Setoid` 的商（`Quotient`）而非裸 `Quot`** ——
**因为裸 `Quot` **没有 `exact`**（无法从商相等反推出等价关系），
**而 `Setoid.quot` 有 `Quotient.exact`**（**实测确认**）。**

**⭐ 这不是技术妥协，而是**正确的选择**：
「商上的运算良定义」这一命题**本质性地**需要「商相等 ⟹ 等价」，
**而那正是 `Setoid` 提供的。** -/

/-- ⭐⭐ **相容性**：`op` 与 `Setoid` 相容（**即商上的 `op` 良定义**）。

$$x \approx x' \implies y \approx y' \implies \mathrm{op}\,x\,y \approx \mathrm{op}\,x'\,y'$$ -/
def Compatible {α : Type*} (op : α → α → α) (s : Setoid α) : Prop :=
  ∀ ⦃x x' y y'⦄, x ≈ x' → y ≈ y' → op x y ≈ op x' y'

/-- ⭐⭐⭐ **T6.6（正向）**：若 `op` 与 `s` 相容，则商上存在运算与 `op` 一致。

**🔹 证明**：用 `Quotient.liftOn₂`。 -/
theorem exists_quot_op_of_compatible {α : Type*} (op : α → α → α)
    (s : Setoid α) (h : Compatible op s) :
    ∃ qop : Quotient s → Quotient s → Quotient s,
      ∀ a b, qop (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (op a b) :=
  ⟨fun x y => Quotient.liftOn₂ x y (fun a b => Quotient.mk s (op a b))
      (fun a₁ b₁ a₂ b₂ ha hb => by
        rw [Quotient.sound (h ha hb)]),
   fun a b => rfl⟩

/-- ⭐⭐⭐ **T6.6（反方向）**：若商上存在与 `op` 相容的运算，则 `op` 与 `s` 相容。

**🔹 证明**：用 `Quotient.exact` 把商相等转回等价关系。 -/
theorem compatible_of_quot_op {α : Type*} (op : α → α → α) (s : Setoid α)
    (h : ∃ qop : Quotient s → Quotient s → Quotient s,
      ∀ a b, qop (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (op a b)) :
    Compatible op s := by
  obtain ⟨qop, hq⟩ := h
  intro x x' y y' hxx' hyy'
  have key : (Quotient.mk s (op x y) : Quotient s) = Quotient.mk s (op x' y') := by
    rw [← hq x y, ← hq x' y', Quotient.sound hxx', Quotient.sound hyy']
  exact Quotient.exact key

/-- ⭐⭐⭐⭐ **T6.6（完整版）**：`op` 与 `s` 相容 **⟺** 商上存在与 `op` 一致的运算。

**⭐ 这是清单 T6.6 的**逐字形式化**（推广到任意 `op`）。** -/
theorem t66_iff {α : Type*} (op : α → α → α) (s : Setoid α) :
    Compatible op s ↔
      ∃ qop : Quotient s → Quotient s → Quotient s,
        ∀ a b, qop (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (op a b) :=
  ⟨exists_quot_op_of_compatible op s, compatible_of_quot_op op s⟩

/-! ## §2 T6.4 —— **组合的封闭性与结合律**

**清单原文（T6.4）**：
> **组合的封闭性与结合律**（A3 的展开）：若 `R` 对 `∘` 封闭，则 `n` 元组合
> `R₁∘⋯∘Rₙ ∈ R`；**若进一步假设 `∘` 结合**，则括号方式不影响结果。

**⚠ 偏差说明**：**本文件把 `∘` 抽象为**任意二元运算 `op`**
（**因为「封闭性」与「结合律」都是**纯代数**性质**）。 -/

/-- ⭐⭐ **T6.4（封闭性）**：若 `S` 对 `op` 封闭，则 `op` 折叠后的结果仍在 `S` 中。

**🔹 对应清单**：T6.4 的前半「`n` 元组合 `∈ R`」。

**⭐ 实质内容**：「封闭」一个假设就足以推出**所有长度**的组合都在 `S` 中。 -/
theorem closed_foldr {α : Type*} (op : α → α → α) (S : Set α)
    (hclosed : ∀ a ∈ S, ∀ b ∈ S, op a b ∈ S) :
    ∀ (l : List α) (a : α), a ∈ S → (∀ x ∈ l, x ∈ S) → l.foldr op a ∈ S := by
  intro l
  induction l with
  | nil => intro a ha _; simpa using ha
  | cons x xs ih =>
    intro a ha hx
    rw [List.foldr_cons]
    have hxS : x ∈ S := hx x List.mem_cons_self
    have hxsS : ∀ y ∈ xs, y ∈ S := fun y hy => hx y (List.mem_cons_of_mem x hy)
    exact hclosed x hxS (xs.foldr op a) (ih a ha hxsS)
/-! ### ⚠ **T6.4 后半（结合律）的**边界登记****

**⚠ 我原本想证**：「`op` 结合 ⟹ `foldr` = `foldl`」。
**⚠ 实测发现**：**这**不成立** —— **结合律不够，还需要交换律**。**
（`foldr op a [x,y] = op x (op y a)`，而 `foldl op a [x,y] = op (op a x) y` ——
**二者在**非交换**的 `op` 下不同**。）

**⭐⭐ 故 T6.4 的**正确形式**应是**：**「若 `op` 结合，则**任意两种括号方式**给出相同结果」** ——
**而这**不需要**交换律（**因为所有括号方式都保持元素的**相对顺序**）。

**⚠ 本轮**未形式化**这一点**（**需要 `List.rec` 的深层归纳**）——
**⟹ 登记为**未还债务**，下一轮补。**

**✅ 本轮**已证**：**T6.4 的封闭性部分（`closed_foldr`）**。** -/

end Fate.MainlineTheorems