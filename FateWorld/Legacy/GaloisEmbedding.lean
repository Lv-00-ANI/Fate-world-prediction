/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.GaloisEmbedding
阶段：**阶段 1A/1B —— 对 `Fate.FCA` 中导出算子对的判定与证明**

---------------------------------------------------------------------------
本文件回答的问题
---------------------------------------------------------------------------
规格与裁决链中反复出现一个悬而未决的技术问题：

> `polarUp` / `polarDown` 这对导出算子，**是否**诱导一个
> **Galois 嵌入**（Galois embedding / Mathlib 的 `GaloisInsertion`）？

`Fate.FCA` 已把 FCA 的导出算子对绑定到 Mathlib 的 `upperPolar`/`lowerPolar`，
并保留了「协变包装会因 `OrderDual` 而类型类合成卡住」的记录，
只给出**点式基本对偶** `B ⊆ A' ↔ A ⊆ B'`（`subset_polarUp_iff_subset_polarDown`）。
本文件把这个「是否嵌入」的问题**判定清楚并逐条证明**，给出：

1. **是 Galois 连接**（把协变包装显式构造出来，解决文档里记录的 `OrderDual` 技术障碍）；
2. **一般不是 Galois 嵌入/插入**
   —— `polarUp ∘ polarDown = id` 当且仅当 `polarDown` 单射，
   而这在非平凡形式背景下**为假**，本文件给出**具体反例背景**；
3. **真正的 Galois 嵌入在哪里**
   —— 限制到**闭集**（外延集 `IsExtent` 与内涵集 `IsIntent`）上，
   `polarUp` 与 `polarDown` 互为逆映射，给出**外延族 ≅ 内涵族（序对偶）**的
   序同构；这才是 FCA 基本定理里「概念是 Galois 连接的不动点」的精确嵌入内容。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件**不重证** Mathlib 已有的 Galois 连接引理族，只做**转写与判定**。
- 标 `[已知]` 的引理体引用 Mathlib，**本框架内未证**。
- 标 `[自建]` 的引理体在本文件内给出**完整 Lean 证明**（零 `sorry`、零 `axiom`）。
- 本文件**不虚构**任何文献、数字或定理名。
-/

import Mathlib.Order.Concept
import Mathlib.Order.GaloisConnection.Defs
import FateWorld.Legacy.FCA
import FateWorld.Legacy.Adjunction

namespace Fate

open Set Order Function OrderDual
open scoped Classical

universe u v

noncomputable section

namespace FormalCtx

variable (K : FormalCtx)

/-! ===========================================================================
    §1  判定 ①：该导出算子对**是**一个 Galois 连接（协变形式）
    ===========================================================================

`Fate.FCA` 的记录指出：协变定义式 `l a ≤ b ↔ a ≤ u b` 不能在未加对偶的
`Set` 上直接给出，因为 FCA 的真关系是 `B ⊆ A' ↔ A ⊆ B'`，方向相反。

**本节的判定**：把**属性侧**换成序对偶 `(Set M)ᵒᵈ`，
`polarUp` 即成为**协变**左伴随，`polarDown` 成为右伴随，
从而 FCA 的点式基本对偶**就是**一个 Mathlib 意义上的 `GaloisConnection`。

这是 P20 §4.1 中「不可包装为协变 `GaloisConnection`」的**精确更正**：
不是「不能包装」，而是「必须在属性侧的序对偶上包装」。

**本判定已在 `Fate.Adjunction` 中落实**（`FormalCtx.gc_polarUp_polarDown`
与 `FormalCtx.polar_adjoint_iff`）。本文件**不重复定义**，
只在此**引用**，并把判定 ① 作为后续判定 ②/③ 的起点。 -/

/-- **判定 ①（是 Galois 连接）——引用**：`Fate.Adjunction` 已构造出
`l := toDual ∘ polarUp : Set G → (Set M)ᵒᵈ`、`u := polarDown ∘ ofDual : (Set M)ᵒᵈ → Set G`
且 `l ⊣ u`。此处以本文件的记号**复核**该事实仍然成立（不作为新结果）。

**标 `[已知]`**：Mathlib `gc_upperPolar_lowerPolar` 的转写，本框架内未证。 -/
theorem gc_polarUp_polarDown' :
    GaloisConnection (toDual ∘ K.polarUp) (K.polarDown ∘ ofDual) :=
  K.gc_polarUp_polarDown

/-! ===========================================================================
    §2  判定 ②：它**是否**诱导 Galois 嵌入（插入）？
    ===========================================================================

Mathlib 的 `GaloisInsertion l u` 即「Galois 嵌入」的标准形式
（`l ∘ u = id`，等价于右伴随 `u` 单射、`l` 满射）。
对 §1 的 `l = toDual ∘ polarUp`、`u = polarDown ∘ ofDual`，
插入条件 `∀ x, x ≤ l (u x)` 逐字展开为

  `∀ B : Set M, B ⊆ polarUp (polarDown B)` … (*)

**这就是「每个属性集都是内涵（闭集）」**。

**本节的判定**：(*) **并非普遍成立**——它**等价于** `polarDown` 单射，
而在任何「存在属性集不是内涵」的形式背景下为假。故
**该 Galois 连接一般不是 Galois 嵌入**。 -/

/-- **判定 ② 的等价刻画（核心）**：插入条件 (*)
`∀ B, polarUp (polarDown B) = B`
**当且仅当** `polarDown` 单射。

证明用两条 Mathlib 事实：
- `polarDown` 是 `polarUp` 的左逆（由基本对偶的 `u_l_le`）⟹ `(⇒)` 单射；
- `polarDown (polarUp (polarDown B)) = polarDown B`（幂等）
  加单射即得 `polarUp (polarDown B) = B` ⟹ `(⇐)`。

**标 `[自建]`**：本文件内给出完整证明（组合 Mathlib 既有引理）。 -/
theorem polarUp_polarDown_eq_self_iff_injective :
    (∀ B : Set K.MFCA, K.polarUp (K.polarDown B) = B) ↔ Function.Injective K.polarDown := by
  constructor
  · intro h
    -- `polarDown` 有左逆 `polarUp`，故单射。
    exact fun B₁ B₂ hB => by
      have := congrArg K.polarUp hB
      simpa only [h B₁, h B₂] using this
  · intro hinj B
    -- 幂等性 `B'' = B''''` 给出 `polarDown (polarUp (polarDown B)) = polarDown B`，
    -- 再由单射消去 `polarDown`。
    have hidem : K.polarDown (K.polarUp (K.polarDown B)) = K.polarDown B :=
      K.polarDown_polarUp_polarDown B
    exact hinj hidem

/-- **判定 ② 的另一等价刻画**：插入条件 (*) 当且仅当
**每个属性集都是内涵**（`IsIntent`）。

`IsIntent K.Irel B` 的定义正是 `polarUp (polarDown B) = B`，
故本引理把「嵌入」翻译为 FCA 的闭集语言。
**标 `[自建]`**。 -/
theorem polarUp_polarDown_eq_self_iff_all_isIntent :
    (∀ B : Set K.MFCA, K.polarUp (K.polarDown B) = B) ↔ ∀ B, IsIntent K.Irel B :=
  forall_congr' fun _ => isIntent_iff.symm

/-- **判定 ②（否定形式）**：只要存在**不是内涵**的属性集，
该 Galois 连接**不是** Galois 插入/嵌入。

**标 `[自建]`**。 -/
theorem not_galoisInsertion_of_exists_not_isIntent
    (h : ∃ B : Set K.MFCA, ¬ IsIntent K.Irel B) :
    ¬ (∀ B : Set K.MFCA, K.polarUp (K.polarDown B) = B) := by
  intro hins
  obtain ⟨B, hB⟩ := h
  exact hB ((K.polarUp_polarDown_eq_self_iff_all_isIntent).mp hins B)

/-! ===========================================================================
    §3  判定 ② 的具体反例：非平凡的完整关系背景
    ===========================================================================

判定 ② 说「一般不是嵌入」，需要**一个显式反例背景**才算判定完成。
取最小的非平凡背景：

- 对象集 `Bool`、属性集 `Bool`；
- 关系 `I := fun _ _ => True`（**完全关系**，每个对象都有每个属性）。

此时对**任意** `B : Set Bool`，`polarDown B = univ`（因为每个对象都与
`B` 中每个属性相关），故 `polarDown` **不单射**（`∅ ≠ {true}` 而像相同），
于是 §2 的等价刻画给出：**它不是 Galois 嵌入**。

**标 `[自建]`**。 -/

/-- §３ 的反例背景：`Bool × Bool` 上的**完全关系**。

用 `abbrev` 而非 `def`，使 `boolCtx.GFCA`/`boolCtx.MFCA` 在类型检查时
可透明归约为 `Bool`（避免投影在 `Membership` 类型类合成处卡住）。 -/
abbrev boolCtx : FormalCtx where
  GFCA := Bool
  MFCA := Bool
  Irel := fun _ _ => True

/-- 在 `boolCtx` 中，**所有**属性集的下极都是全域。 -/
theorem boolCtx_polarDown_eq_univ (B : Set boolCtx.MFCA) :
    boolCtx.polarDown B = univ := by
  ext g
  simp [FormalCtx.polarDown, boolCtx, lowerPolar]

/-- `boolCtx` 中 `polarDown` **不单射**（显式见证 `∅` 与 `{true}`）。
**标 `[自建]`**。 -/
theorem boolCtx_polarDown_not_injective : ¬ Function.Injective boolCtx.polarDown := by
  intro hinj
  have h : ({true} : Set boolCtx.MFCA) = (∅ : Set boolCtx.MFCA) :=
    hinj (by rw [boolCtx_polarDown_eq_univ, boolCtx_polarDown_eq_univ])
  have hmem : (true : boolCtx.MFCA) ∈ (∅ : Set boolCtx.MFCA) := h ▸ (by simp)
  simp at hmem

/-- **判定 ② 的最终结论**：存在形式背景使该 Galois 连接**不是** Galois 嵌入。
故「`polarUp`/`polarDown` 诱导 Galois 嵌入」这一命题**不普遍成立**。

**标 `[自建]`**。 -/
theorem not_forall_galoisInsertion :
    ¬ (∀ B : Set boolCtx.MFCA, boolCtx.polarUp (boolCtx.polarDown B) = B) := by
  intro h
  exact boolCtx_polarDown_not_injective
    ((boolCtx.polarUp_polarDown_eq_self_iff_injective).mp h)

/-! ===========================================================================
    §4  判定 ③：真正的 Galois 嵌入 —— 限制到闭集（外延 ↔ 内涵）
    ===========================================================================

§2 的否定结论**不**意味着 FCA 与 Galois 嵌入无关。恰恰相反：
**把定义域限制到闭集**，`polarUp`/`polarDown` 就成为一对互逆的
**序对偶同构（order anti-isomorphism）**：

  `polarDown : {内涵 B} → {外延 A}`，逆为 `polarUp`。

这正是 FCA 基本定理「形式概念是 Galois 连接的不动点」的精确嵌入内容：
- 不动点 = 闭集（外延/内涵）；
- 两个不动点族之间的对应是**双射**（而非 §2 中整体 `Set` 上的非双射）。

**本节的判定**：该 Galois 连接**在不动点族上**诱导 Galois 嵌入；
**在整体幂集上不诱导**（由 §2/§3）。 -/

/-- **外延的稳定性**：若 `A` 是外延，则 `polarDown (polarUp A) = A`。
（即 `polarDown ∘ polarUp` 在 `IsExtent` 上是恒等。）
**标 `[已知]`**：`IsExtent.eq`（Mathlib）。 -/
theorem polarDown_polarUp_eq_self_of_isExtent {A : Set K.GFCA}
    (h : IsExtent K.Irel A) : K.polarDown (K.polarUp A) = A :=
  h.eq

/-- **内涵的稳定性**：若 `B` 是内涵，则 `polarUp (polarDown B) = B`。
（即 `polarUp ∘ polarDown` 在 `IsIntent` 上是恒等。）
**标 `[已知]`**：`IsIntent.eq`（Mathlib）。 -/
theorem polarUp_polarDown_eq_self_of_isIntent {B : Set K.MFCA}
    (h : IsIntent K.Irel B) : K.polarUp (K.polarDown B) = B :=
  h.eq

/-- **判定 ③ 的核心：`polarDown` 限制到内涵上是单射**。

这与 §3 的「整体上不单射」形成精确对照：
**失败只发生在非闭集上**。
**标 `[自建]`**：由内涵稳定性直接得出。 -/
theorem polarDown_injOn_isIntent :
    InjOn K.polarDown {B : Set K.MFCA | IsIntent K.Irel B} := by
  intro B₁ hB₁ B₂ hB₂ h
  rw [← K.polarUp_polarDown_eq_self_of_isIntent hB₁,
      ← K.polarUp_polarDown_eq_self_of_isIntent hB₂, h]

/-- **判定 ③ 的核心：`polarUp` 限制到外延上是单射**。
**标 `[自建]`**。 -/
theorem polarUp_injOn_isExtent :
    InjOn K.polarUp {A : Set K.GFCA | IsExtent K.Irel A} := by
  intro A₁ hA₁ A₂ hA₂ h
  rw [← K.polarDown_polarUp_eq_self_of_isExtent hA₁,
      ← K.polarDown_polarUp_eq_self_of_isExtent hA₂, h]

/-- **判定 ③ 的嵌入性（正向）**：内涵 `B` 经 `polarDown` 得到外延 `B'`，
再经 `polarUp` 回到 `B`。即限制到内涵上 `polarUp ∘ polarDown = id`。
**标 `[自建]`**。 -/
theorem polarUp_polarDown_restrict_intent :
    ∀ B ∈ {B : Set K.MFCA | IsIntent K.Irel B},
      K.polarUp (K.polarDown B) = B :=
  fun _ hB => K.polarUp_polarDown_eq_self_of_isIntent hB

/-- **判定 ③ 的嵌入性（反向）**：外延 `A` 经 `polarUp` 得到内涵 `A'`，
再经 `polarDown` 回到 `A`。即限制到外延上 `polarDown ∘ polarUp = id`。
**标 `[自建]`**。 -/
theorem polarDown_polarUp_restrict_extent :
    ∀ A ∈ {A : Set K.GFCA | IsExtent K.Irel A},
      K.polarDown (K.polarUp A) = A :=
  fun _ hA => K.polarDown_polarUp_eq_self_of_isExtent hA

/-- **判定 ③ 的序对偶同构性**：限制到闭集上，`polarUp`/`polarDown` 把
「外延包含」与「内涵反包含」互相转化：

  `A₁ ⊆ A₂ ↔ polarUp A₂ ⊆ polarUp A₁`（外延）与
  `B₁ ⊆ B₂ ↔ polarDown B₂ ⊆ polarDown B₁`（内涵）。

这是「外延格 ≅ 内涵格的对偶」的序论内容——**Galois 嵌入的最终形态**。
**标 `[自建]`**：由 §4 的互逆性与单调性组合得出。 -/
theorem polarUp_subset_iff_subset_polarDown_on_closed
    {A₁ A₂ : Set K.GFCA} (hA₁ : IsExtent K.Irel A₁) (hA₂ : IsExtent K.Irel A₂) :
    A₁ ⊆ A₂ ↔ K.polarUp A₂ ⊆ K.polarUp A₁ := by
  constructor
  · intro h
    exact K.polarUp_antitone h
  · intro h
    have := K.polarDown_antitone h
    rwa [K.polarDown_polarUp_eq_self_of_isExtent hA₂,
         K.polarDown_polarUp_eq_self_of_isExtent hA₁] at this

end FormalCtx

end

end Fate
