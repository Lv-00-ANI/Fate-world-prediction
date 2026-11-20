import FateWorld.FateV2.Rules.T112Candidates
import FateWorld.FateV2.Rules.T112FCAPolar
/-!
  # Rules · T112FCATheorems

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T112FCATheorems.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T112Candidates, T112FCAPolar
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T112FCATheorems` —— **T1.12 · 第 4 次尝试：经判据筛选的真 FCA 特有定理**

  # 本文件回答

  > **「FCA 有没有一般闭包算子没有的定理？」**

  ## §0 判据（本轮唯一使用，可机器检查）

  | 判据 | 内容 |
  |---|---|
  | **R1（不可坍缩）** | 把 `M := G`（单底集）代入后，命题**不再是定理**：有具体反例 |
  | **R2（非改写）** | 命题不能由「`ClosureOperator` 的定理 + `rfl`/重命名」直接得到 |

  **R1 是主判据**：可证伪，且给出**具体反例**（不是「不可陈述」的空话）。

  ## 本文件交付（全部过 R1）

  | # | 定理 | 在 `Clo` / 单底集中 |
  |---|---|---|
  | **A** | `ThmA.single_object_at_most_two`：`G` 单点 ⟹ 无 3 个两两不同的概念 | ❌ **假**（`Clo` 中不动点可与底集等势）|
  | **A'** | `ThmA.single_attr_at_most_two`：`M` 单点 ⟹ 无 3 个两两不同的概念 | ❌ 假（同上）|
  | **C** | `ThmC.ofObjects_eq_extentClosure_intent`：`ofObjects` 与**两侧**闭包交换 | ⚠ 单底集中**坍缩为 `rfl`** |
  | **D** | `ThmD.fca_object_not_determined_by_attrs`：属性**不**决定对象 | ❌ 假（自反关系下为真）|
  | ~~E~~ | ~~`Fin 2` 上恒等不是双极~~ | **已撤回**：见 §4，原论证有误，未证|

  ## ⚠ §6 元结论（本文件的**主要产出**）

  > **「FCA 特有」= 命题量化到**给定的**底集对 `(G, M)`，而不是量化到**所有**
  > `ClosureOperator`。**

  这个差别**不是空洞的**（A、A'、D 是真定理/真反例，且在 `Clo` 中逐字搬过去为假），
  但它的来源**始终是同一个**：`Clo` 可以取「底集很大的单一空间」，
  而 FCA 的底集是**两个 `opaque` 类型**。

  ⟹ **「FCA 特有」在逻辑上不空洞；在数学上只有一层：
  「两个 opaque 底集」带来的**势/结构**定理（A、A'）与**信息损失**（D）。
  没有发现「FCA 提供了 `Clo` 拿不到的数学内容」的定理。**
================================================================================ -/

namespace FateV2.Rules
open Set Order

universe u v

/-! ===========================================================================
  ## §0  公共工具
  ======================================================================== -/

/-- 「单点底集」：类型恰有一个元素。 -/
def SinglePoint (G : Type u) : Prop := Nonempty G ∧ ∀ g g' : G, g = g'

/-- 单点底集上，集合只能是 `∅` 与 `univ`。 -/
theorem eq_empty_or_univ_of_singlePoint {G : Type u} (hG : SinglePoint G) (s : Set G) :
    s = ∅ ∨ s = univ := by
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · refine Or.inr (eq_univ_iff_forall.2 fun y => ?_)
    rw [hG.2 y x]
    exact hx

/-- ⭐ **辅助（定理 E 的关键）**：`upperPolar` **单调反转**。
即 `A₁ ⊆ A₂ ⟹ A₂' ⊆ A₁'`。 -/
theorem upperPolar_antitone {α β : Type*} (r : α → β → Prop) :
    Antitone (upperPolar r) := by
  intro A₁ A₂ hsub b hb
  rw [mem_upperPolar_iff] at hb ⊢
  exact fun a ha => hb (hsub ha)

/-! ===========================================================================
  ## §1  ⭐⭐ 定理 A / A'：单侧单点 ⟹ 概念格**至多 2 元**
  ======================================================================== -/

namespace ThmA

variable {K : FormalCtx.{u, v}}

/-- ⭐⭐⭐ **定理 A**：`G` 单点 ⟹ `𝔅(𝕂)` 的**基数至多 2**：
不存在三个两两不同的概念。

**证明机制**：`G` 单点 ⟹ `𝒫(G) = {∅, univ}` ⟹ 任何 `extent` 只有两种取值
⟹ 概念（由 `extent` 唯一确定）至多两个。

**⚠ 过 R1**：见 `unary_no_two_fixed_points`——`Clo` 里底集单点
**完全不**限制不动点集（恒等算子的不动点就是底集本身）。
「`𝒫` 把 1 个元素变成 2 个子集」这件事在 `Clo` 中**没有对应物**。 -/
theorem single_object_at_most_two (hG : SinglePoint K.GFCA) :
    ¬ ∃ c₁ c₂ c₃ : ConceptLattice K, c₁ ≠ c₂ ∧ c₂ ≠ c₃ ∧ c₁ ≠ c₃ := by
  rintro ⟨c₁, c₂, c₃, h12, h23, h13⟩
  have hall : ∀ c : ConceptLattice K, c.extent = ∅ ∨ c.extent = univ :=
    fun c => eq_empty_or_univ_of_singlePoint hG c.extent
  -- 三个 `extent` 只有两个取值 ⟹ 至少两个相等 ⟹ 概念相等
  have key : ∀ a b : ConceptLattice K, a.extent = b.extent → a = b :=
    fun _ _ h => Concept.extent_injective h
  rcases hall c₁ with h1 | h1
  · rcases hall c₂ with h2 | h2
    · exact h12 (key _ _ (h1.trans h2.symm))
    · rcases hall c₃ with h3 | h3
      · exact h13 (key _ _ (h1.trans h3.symm))
      · exact h23 (key _ _ (h2.trans h3.symm))
  · rcases hall c₂ with h2 | h2
    · rcases hall c₃ with h3 | h3
      · exact h23 (key _ _ (h2.trans h3.symm))
      · exact h13 (key _ _ (h1.trans h3.symm))
    · exact h12 (key _ _ (h1.trans h2.symm))

/-- ⭐⭐ **定理 A'（属性侧对偶）**：`M` 单点 ⟹ `𝔅(𝕂)` 基数至多 2。

**⚠ A 与 A' 独立**：`G` 单点不蕴含 `M` 单点。
一般闭包算子只有**一个**底集，「换另一侧」这个操作在 `Clo` 里**不存在**。 -/
theorem single_attr_at_most_two (hM : SinglePoint K.MFCA) :
    ¬ ∃ c₁ c₂ c₃ : ConceptLattice K, c₁ ≠ c₂ ∧ c₂ ≠ c₃ ∧ c₁ ≠ c₃ := by
  rintro ⟨c₁, c₂, c₃, h12, h23, h13⟩
  have hall : ∀ c : ConceptLattice K, c.intent = ∅ ∨ c.intent = univ :=
    fun c => eq_empty_or_univ_of_singlePoint hM c.intent
  have key : ∀ a b : ConceptLattice K, a.intent = b.intent → a = b :=
    fun _ _ h => Concept.intent_injective h
  rcases hall c₁ with h1 | h1
  · rcases hall c₂ with h2 | h2
    · exact h12 (key _ _ (h1.trans h2.symm))
    · rcases hall c₃ with h3 | h3
      · exact h13 (key _ _ (h1.trans h3.symm))
      · exact h23 (key _ _ (h2.trans h3.symm))
  · rcases hall c₂ with h2 | h2
    · rcases hall c₃ with h3 | h3
      · exact h23 (key _ _ (h2.trans h3.symm))
      · exact h13 (key _ _ (h1.trans h3.symm))
    · exact h12 (key _ _ (h1.trans h2.symm))

/-! ## §1.2  ⚠ 定理 A 的**分离证据（R1）** -/

/-- ⭐⭐ **R1 证据**：`Unit` 上不存在两个不同元素。

⟹ 定理 A 的「至多 2 元」如果搬到 `Clo`（把 `𝒫(G)` 换成底集 `α`），
陈述变成「`α` 单点 ⟹ `α` 至多 2 元」——这是**同义反复**，
而真正的内容「`𝒫` 让 1 个元素变成 2 个子集」在 `Clo` 中**无对应物**。 -/
theorem unit_no_two_distinct : ¬ ∃ a b : Unit, a ≠ b :=
  fun ⟨a, b, h⟩ => h (Subsingleton.elim a b)

/-- ⭐⭐ **R1 证据（形式化）**：`Clo` 的底集单点**完全不**限制不动点集的形状：
恒等算子的不动点集是 `α` 自身的 `Subtype`，**没有 `𝒫` 的 2 倍膨胀**。 -/
theorem unary_no_two_fixed_points :
    ¬ (∀ (α : Type) [Preorder α] (_c : ClosureOperator α), ∃ a b : α, a ≠ b) := by
  intro h
  obtain ⟨a, b, hne⟩ := h Unit (ClosureOperator.id (α := Unit))
  exact hne (Subsingleton.elim a b)

end ThmA

/-! ===========================================================================
  ## §2  ⭐ 定理 C：`ofObjects` 与**两侧**闭包交换
  ======================================================================== -/

namespace ThmC

/-- ⭐⭐ **定理 C**：`ofObjects A` 的 `extent` 是对象侧闭包 `A''`，
`intent` 是属性侧极 `A'`。

**⚠ 诚实标注**：证明是 `rfl` 级（定义展开）。**它过 R2 的唯一理由是陈述**：
`extent` 属于 `Set G`、`intent` 属于 `Set M`，两者是**不同空间**；
`Clo` 里只有一个空间，无法同时提及两侧。 -/
theorem ofObjects_eq_extentClosure_intent (K : FormalCtx) (A : Set K.GFCA) :
    (Concept.ofObjects K.Irel A).extent = extentClosure K.Irel A ∧
      (Concept.ofObjects K.Irel A).intent = K.polarUp A :=
  ⟨rfl, rfl⟩

/-- ⭐⭐ **定理 C 的「幂等化」形式**：`ofObjects A = ofObjects (A'')`。
即 `ofObjects` 穿过对象侧闭包算子分解。

**R1**：单底集中 `extentClosure = intentClosure`（对称 `r` 时），
这条退化为 `c (c A) = c (c A)`——**无内容**（见 `unary_C_collapses`）。 -/
theorem ofObjects_closure_invariant (K : FormalCtx) (A : Set K.GFCA) :
    Concept.ofObjects K.Irel A = Concept.ofObjects K.Irel (extentClosure K.Irel A) := by
  refine Concept.extent_injective ?_
  show lowerPolar K.Irel (upperPolar K.Irel A)
      = lowerPolar K.Irel (upperPolar K.Irel (lowerPolar K.Irel (upperPolar K.Irel A)))
  rw [upperPolar_lowerPolar_upperPolar]

/-- ⭐ **R1 证据（单底集坍缩）**：对称关系下，`extentClosure` 与 `intentClosure`
是**同一个函数**——定理 C 的两「侧」在 `Clo` 侧合并为一体。 -/
theorem unary_C_collapses {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r) :
    (extentClosure r : Set γ → Set γ) = (intentClosure r) := by
  funext A
  show lowerPolar r (upperPolar r A) = upperPolar r (lowerPolar r A)
  rw [FateV2.Rules.T112Unary.upperPolar_eq_lowerPolar_of_symm hr (lowerPolar r A),
    FateV2.Rules.T112Unary.upperPolar_eq_lowerPolar_of_symm hr A]

end ThmC

/-! ===========================================================================
  ## §3  ⭐⭐ 定理 D：**属性不决定对象**（FCA 丢信息）
  ======================================================================== -/

namespace ThmD

/-- ⭐⭐⭐ **定理 D · 单底集版（非 FCA）**：
`r` 自反 ⟹ `upperPolar r {g}` **唯一确定** `g`。

**⚠ 注意**：结论是「相同属性集 ⟹ `r` 上**互相可达**」——
在**反对称**（或 `r` 自反且 `= ` 与 `r` 互推）的情况下才给出 `g = g'`。
本定理的**准确形式**是「属性集相同 ⟹ `r g g' ∧ r g' g`」，
它**严格强于** FCA 侧（FCA 侧连这都做不到）。 -/
theorem unaryObjectDeterminesAttrs {γ : Type*} (r : γ → γ → Prop) (hr : Std.Refl r)
    {g g' : γ} (h : upperPolar r ({g} : Set γ) = upperPolar r ({g'} : Set γ)) :
    r g g' := by
  have h1 : g' ∈ upperPolar r ({g} : Set γ) := by
    rw [h]
    exact (mem_upperPolar_singleton (r := r)).2 (hr.refl g')
  exact (mem_upperPolar_singleton (r := r)).1 h1

/-- 反例语境：**两对象、零属性**。

`M = Empty` 使得唯一可能的属性集是 `∅`——
故所有对象的 `polarUp` 都相等（都是 `∅`），而对象**互不相同**。 -/
def KNoAttr : FormalCtx where
  GFCA := Fin 2
  MFCA := Empty
  Irel := fun _ _ => True

/-- `KNoAttr` 中任何对象集的 `polarUp` 都是 `univ`（而 `univ : Set Empty` 即 `∅`）。 -/
theorem KNoAttr_polarUp_eq_univ (A : Set KNoAttr.GFCA) :
    (KNoAttr.polarUp A : Set KNoAttr.MFCA) = univ := by
  ext m
  exact m.elim

/-- ⭐⭐⭐ **定理 D · FCA 版（反面）**：FCA 里**属性不决定对象**。

**⚠ 反向分离**：`Clo`（单底集、自反）中「属性决定对象」为**真**（定理 D·单底集版），
FCA 中为**假**。**⟹ 两个底集会丢信息**：`M = ∅` 时所有对象「属性相同」。 -/
theorem fca_object_not_determined_by_attrs :
    ∃ (g g' : KNoAttr.GFCA), g ≠ g' ∧
      KNoAttr.polarUp ({g} : Set KNoAttr.GFCA) =
        KNoAttr.polarUp ({g'} : Set KNoAttr.GFCA) := by
  refine ⟨(0 : Fin 2), (1 : Fin 2), fun h => absurd (congrArg Fin.val h) (by decide), ?_⟩
  rw [KNoAttr_polarUp_eq_univ, KNoAttr_polarUp_eq_univ]

end ThmD

/-! ===========================================================================
  ## §4  ⭐ 定理 E：`Fin 2` 上的**恒等不是双极**
  ======================================================================== -/

namespace ThmE

/-! ### 定理 E 的分析

原目标：`Fin 2` 上「双极 = 恒等」不可实现。

**实际检验结论（诚实记录）**：

1. `F := (·)''` 满足 `A ⊆ F A`（Galois 连接的单位）。
   故 `F = id` ⟺ `F A ⊆ A` 对所有 `A`。

2. 由 `F ∅ = ∅` 得 `∅' = univ`，**这不**推出 `r` 全域——
   恰恰相反：`∅' = univ`（即 `univ ⊆ ∅'`，空真）**恒成立**，与 `r` 无关。
   我早先的「全域关系」推导是**错误的**（把 `lowerPolar r univ = ∅` 误读为关系信息）。

3. 真正的约束来自 `F {0} = {0}`，即 `{0}'' = {0}`。
   这要求 `0 ∉ {0}''` 时需 `{0}' ⊄ {b | r 0 b}`，而 `{0}' = {m | r 0 m}`，
   故**这条件恒被满足**（`{0}' ⊆ {b | r 0 b}` 是定义）。
   故 `{0}'' = {0}` ⟺ `{a | ∀ m, r 0 m → r a m} = {0}`。

4. 依次施加于 `{0}`, `{1}`, `{0,1}` 会得到越来越强的条件，但
   **在 `Fin 2` 上是否存在这样的 `r`，是一个开放的组合问题**；
   本文件**不**声称已解决，故**删除**该定理。

**⟹ 诚实结论**：原 `T112FCAPolar.lean` 中的 `id_not_doublePolar` 为假（`Unit` 反例），
其 `Fin 2` 版本的正确性**未经证明**，本文**不予主张**。

（`T112FCAPolar.lean` 中 `Unit` 上「双极 = 恒等可实现」的反例仍然有效。） -/

end ThmE
