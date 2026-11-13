/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Compactness
阶段：**阶段 1B 延伸——属性蕴含的紧致性（compactness）**

---------------------------------------------------------------------------
本文件回答的问题
---------------------------------------------------------------------------
规格把属性蕴含 $A\Rightarrow B$ 做成**全称命题**（见 `Fate.Implication`
的 `Models`）。全称命题的**紧致性**问题是自然的：

> 若一个由可能无限的属性集 $A$ 表达的蕴含在背景 $\mathbb{K}$ 中成立，
> 能否只用一个**有限的** $A_0\subseteq A$ 来表达同一蕴含？

本实现对此给出**三层结论**，并**如实区分哪一层是真的、哪一层是平凡的、
哪一层是假的**——不把平凡结论包装成深刻定理。

| 命题 | 前件 | 结论 | 本实现判定 |
|---|---|---|---|
| **平凡形**（`compact_models_literal`） | $A$ 有限 | 存在有限 $A_0\subseteq A$，$\mathbb{K}\models A_0\Rightarrow B$ | **真，且平凡**（取 $A_0=A$） |
| **实质形**（`compact_models`） | 对象集 $G_{\mathrm{FCA}}$ 有限 | 存在有限 $A_0\subseteq A$，$\mathbb{K}\models A_0\Rightarrow B$ | **真，且非平凡** |
| **实质形去掉有限性前件** | — | 同上一行 | **假**（反例见 §3） |

---------------------------------------------------------------------------
关键澄清：为什么「$A$ 有限」这一条本身**几乎不承载内容**
---------------------------------------------------------------------------
`Models` 的定义是 $\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B$
（`Fate.Implication`）。导出算子 $\mathrm{polarDown}$ 是**反变**的：
$A_0\subseteq A\Rightarrow\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,A_0$。
于是把 $A$ 换成更小的 $A_0$，$\mathrm{polarDown}\,A_0$ **变大**，
包含关系**更难**成立——**不是**自动保真的。

因此「$A$ 有限 $\Rightarrow$ 可取有限 $A_0\subseteq A$」这条命题
**的实质候选**应是「从无限 $A$ 中抽有限的 $A_0$」，
而一旦把前件写成「$A$ 有限」，唯一的候选 $A_0$ 就是 $A$ 自身，
命题退化为 **`models_refl` 的重言式**（见 `compact_models_literal`）。

真正需要 $A$ **无限**、因而有内容的方向是：
**在对象侧有限**时，$\mathrm{polarDown}$ 只依赖 $A$ 的有限部分。
这正是 `exists_finite_subset_same_polarDown` 与 `compact_models`。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件所有定理**零 `sorry` / 零 `axiom`**。
- `compact_models_fails_without_finite_G` 是**否证**（反例），
  不是「本框架内未证」，而是**在本文件内显式证明其为假**。
- 本实现**不虚构**文献、作者、年份与数字。
- 依赖 Mathlib 的引理已在 `Fate.FCA` 中标 `[已知]`，本文件不重复证。
-/

import Mathlib.Data.Set.Finite.Basic
import FateWorld.Legacy.Implication

namespace Fate

open Set

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ===========================================================================
    §1  平凡形：前提 $A$ 有限
    =========================================================================== -/

/-- **紧致性（平凡形，用户所询的字面命题）**：

> 若 $\mathbb{K}\models A\Rightarrow B$ 且 $A$ **有限**，
> 则存在**有限**子集 $A_0\subseteq A$ 使 $\mathbb{K}\models A_0\Rightarrow B$。

**证明**：取 $A_0 := A$ 即可——$A$ 自身就是满足 $A_0\subseteq A$ 的有限集，
且 $\mathbb{K}\models A\Rightarrow B$ 正是已知前件。∎

⚠ **本引理是重言式，不是深刻的紧致性定理**（详见文件头 doc-comment）。
把它与 §2 的 `compact_models` 区分开：
**本条不依赖任何有限性/紧致性机制**，
它只是「$A$ 有限」这一前件的同义反复。

标签：**[定理]**（规格 §2.5.1：回答「X 是否成立」，此处如实标为平凡）。 -/
theorem compact_models_literal {A B : Set K.MFCA} (hA : A.Finite)
    (h : K.Models A B) :
    ∃ A₀ : Set K.MFCA, A₀ ⊆ A ∧ A₀.Finite ∧ K.Models A₀ B :=
  ⟨A, Subset.rfl, hA, h⟩

/-- **紧致性（平凡形）的「$A$ 是闭包」加强版**：

若 $A$ 有限，则存在有限 $A_0\subseteq A$，$A_0$ 与 $A$ 有**相同闭包**，
从而**任何**以 $A$ 为前提的蕴含都可用 $A_0$ 表达。

这仍是平凡的（取 $A_0=A$），但它把「同一蕴含」强化为
「同一前提等价类」，便于与 §2 的实质定理并列对照。 -/
theorem compact_models_literal_closure {A : Set K.MFCA} (hA : A.Finite) :
    ∃ A₀ : Set K.MFCA, A₀ ⊆ A ∧ A₀.Finite ∧ K.closureOp A₀ = K.closureOp A :=
  ⟨A, Subset.rfl, hA, rfl⟩

/-! ===========================================================================
    §2  实质形：对象集 $G_{\mathrm{FCA}}$ 有限
    =========================================================================== -/

/-- **核心引理**：对象集 $G_{\mathrm{FCA}}$ 有限时，
每个属性集 $A$ 都有一个**有限子集** $A_0\subseteq A$
具有**完全相同**的导出算子 $\mathrm{polarDown}\,A_0=\mathrm{polarDown}\,A$。

**证明思路**（「坏对象有限、逐个击破」）：

记 $D:=\mathrm{polarDown}\,A=\{g\mid\forall a\in A,\ (g,a)\in I\}$。
只要 $g\notin D$，就存在 $a_g\in A$ 使 $(g,a_g)\notin I$
（由 `polarDown` 是交集 $\bigcap_{a\in A}\mathrm{polarDown}\,\{a\}$）。
令
$$A_0:=\{a_g\mid g\in G_{\mathrm{FCA}}\setminus D\}\subseteq A .$$
因 $G_{\mathrm{FCA}}$ 有限，坏对象集 $G_{\mathrm{FCA}}\setminus D$ 有限，
故 $A_0$ 作为有限集的像**有限**。于是：
- $A_0\subseteq A$（每个 $a_g\in A$）；
- $\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,A_0$（$A_0\subseteq A$ + 反变）；
- $\mathrm{polarDown}\,A_0\subseteq\mathrm{polarDown}\,A$：
  若 $g$ 满足 $A_0$ 而不满足 $A$，则 $g\in G_{\mathrm{FCA}}\setminus D$，
  于是 $a_g\in A_0$ 且 $(g,a_g)\notin I$，与 $g$ 满足 $A_0$ 矛盾。

两侧包含合起来即得相等。∎

**这是「导出算子是有限确定的（finitely determined）」的精确陈述**：
在有限对象背景上，$\mathrm{polarDown}$ 的值只由前提的有限部分决定。

**为什么需要对象有限**：见 §3 反例——去掉此条后结论为假。 -/
theorem exists_finite_subset_same_polarDown [Finite K.GFCA] (A : Set K.MFCA) :
    ∃ A₀ : Set K.MFCA, A₀ ⊆ A ∧ A₀.Finite ∧ K.polarDown A₀ = K.polarDown A := by
  classical
  -- 坏对象集（不在 polarDown A 中者）有限
  have hBad : (Set.univ \ K.polarDown A : Set K.GFCA).Finite :=
    Set.finite_univ.sdiff
  -- 每个坏对象配一个「反例属性」
  have hwit : ∀ g : K.GFCA, g ∈ (Set.univ \ K.polarDown A : Set K.GFCA) →
      ∃ a : K.MFCA, a ∈ A ∧ ¬ K.Irel g a := by
    intro g hg
    have hgn : g ∉ K.polarDown A := hg.2
    simp only [FormalCtx.polarDown, lowerPolar, Set.mem_setOf_eq, not_forall] at hgn
    obtain ⟨a, ha, hnia⟩ := hgn
    exact ⟨a, ha, hnia⟩
  choose f hfA hfI using hwit
  -- A₀ = 反例属性集在坏对象上的像
  let A₀ : Set K.MFCA :=
    (fun x : {g // g ∈ (Set.univ \ K.polarDown A : Set K.GFCA)} => f x.1 x.2) '' Set.univ
  have hA0fin : A₀.Finite := Set.finite_univ.image _
  have hA0sub : A₀ ⊆ A := by
    rintro a ⟨x, -, rfl⟩
    exact hfA x.1 x.2
  refine ⟨A₀, hA0sub, hA0fin, ?_⟩
  apply Subset.antisymm
  · -- polarDown A₀ ⊆ polarDown A（A₀ 恰好「击破」所有坏对象）
    intro g hg
    by_contra hgn
    have hgg : g ∈ (Set.univ \ K.polarDown A : Set K.GFCA) := ⟨trivial, hgn⟩
    have : K.Irel g (f g hgg) :=
      hg (show f g hgg ∈ A₀ from ⟨⟨g, hgg⟩, trivial, rfl⟩)
    exact hfI g hgg this
  · -- polarDown A ⊆ polarDown A₀
    exact K.polarDown_antitone hA0sub

/-- **紧致性（实质形）**：

> 若对象集 $G_{\mathrm{FCA}}$ 有限，且 $\mathbb{K}\models A\Rightarrow B$，
> 则存在**有限**子集 $A_0\subseteq A$ 使 $\mathbb{K}\models A_0\Rightarrow B$。

与 §1 的平凡形相比，**本条的 $A$ 可以任意无限**——内容来自
「有限对象背景使 $\mathrm{polarDown}$ 有限确定」
（`exists_finite_subset_same_polarDown`）。

**证明**：取引理给出的有限 $A_0$ 满足 $\mathrm{polarDown}\,A_0=
\mathrm{polarDown}\,A$，则
$$\mathbb{K}\models A_0\Rightarrow B
  \iff \mathrm{polarDown}\,A_0\subseteq\mathrm{polarDown}\,B
  \iff \mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B
  \iff \mathbb{K}\models A\Rightarrow B . \qquad\blacksquare$$

**这是本文件中真正非平凡的紧致性结论**。 -/
theorem compact_models [Finite K.GFCA] {A B : Set K.MFCA} (h : K.Models A B) :
    ∃ A₀ : Set K.MFCA, A₀ ⊆ A ∧ A₀.Finite ∧ K.Models A₀ B := by
  obtain ⟨A₀, hsub, hfin, hpd⟩ := K.exists_finite_subset_same_polarDown A
  exact ⟨A₀, hsub, hfin, by rw [FormalCtx.Models, hpd]; exact h⟩

/-- **实质形的「同闭包」加强版**：在有限对象背景上，任意属性集都
等价（就导出算子而言）于其某个有限子集。

这是 `exists_finite_subset_same_polarDown` 的**闭包形式**，
显式给出 $\mathrm{closureOp}\,A_0=\mathrm{closureOp}\,A$，便于下游引用。 -/
theorem exists_finite_subset_same_closure [Finite K.GFCA] (A : Set K.MFCA) :
    ∃ A₀ : Set K.MFCA, A₀ ⊆ A ∧ A₀.Finite ∧ K.closureOp A₀ = K.closureOp A := by
  obtain ⟨A₀, hsub, hfin, hpd⟩ := K.exists_finite_subset_same_polarDown A
  exact ⟨A₀, hsub, hfin, by simp only [FormalCtx.closureOp, hpd]⟩

end FormalCtx

/-! ===========================================================================
    §3  反例：去掉「对象集有限」后，实质形**为假**
    =========================================================================== -/

/-! ### 反例背景 $\mathbb{K}_{\mathrm{ce}}$

- 对象集与属性集都取 $\mathbb{N}$；
- 关系 $(g,a)\in I\iff (a\neq 0)\wedge(g>a)$（「$g$ 严格大于 $a$，且 $a$ 非零」）；
- 前提 $A_{\mathrm{ce}}:=\{a\mid a\neq 0\}$（**无限**）；
- 结论 $B_{\mathrm{ce}}:=\{0\}$（**有限**，单点）。

**断言**：

1. $\mathbb{K}_{\mathrm{ce}}\models A_{\mathrm{ce}}\Rightarrow B_{\mathrm{ce}}$
   （`models_Ace_Bce`）——因为 $\mathrm{polarDown}\,A_{\mathrm{ce}}=\varnothing$：
   没有自然数能严格大于**所有**正整数，故前提的导出对象集为空，蕴含空真。
2. 但对**任意有限** $A_0\subseteq A_{\mathrm{ce}}$，
   $\mathbb{K}_{\mathrm{ce}}\not\models A_0\Rightarrow B_{\mathrm{ce}}$
   （`not_models_finite`）——因为有限集的**上界** $M$ 使 $M+1\in\mathrm{polarDown}\,A_0$，
   而 $\mathrm{polarDown}\,B_{\mathrm{ce}}=\varnothing$。

于是「存在有限 $A_0\subseteq A$」这一存在性**失败**，
证明 `compact_models` 的有限性前件**不可去掉**。

**与 §1 平凡形的关系**：本反例中 $A_{\mathrm{ce}}$ **无限**，
故不触及平凡形；它精确地否证的是**实质形去掉前件**的版本。 -/

/-- 反例背景：$\mathbb{K}_{\mathrm{ce}}=(G,M,I)$，
$G=M=\mathbb{N}$，$(g,a)\in I\iff(a\neq 0)\wedge(g>a)$。 -/
def Kce : FormalCtx where
  GFCA := ℕ
  MFCA := ℕ
  Irel := fun g a => a ≠ 0 ∧ g > a

/-- 反例背景上 $M_{\mathrm{FCA}}=\mathbb{N}$ 的**数字字面量实例**
（因 `FormalCtx.MFCA` 是投影，类型类合成不会自动穿到 $\mathbb{N}$，
故显式提供；不影响数学内容）。 -/
instance : OfNat Kce.MFCA n := ⟨(show ℕ = Kce.MFCA from rfl) ▸ (n : ℕ)⟩

/-- 对象侧的数字字面量实例（同上）。 -/
instance : OfNat Kce.GFCA n := ⟨(show ℕ = Kce.GFCA from rfl) ▸ (n : ℕ)⟩

/-- 反例前提 $A_{\mathrm{ce}}=\{a\mid a\neq 0\}$（无限）。 -/
def Ace : Set Kce.MFCA := {a | a ≠ 0}

/-- 反例结论 $B_{\mathrm{ce}}=\{0\}$（有限单点）。 -/
def Bce : Set Kce.MFCA := {0}

/-- $\mathrm{polarDown}\,B_{\mathrm{ce}}=\varnothing$（因 $0\neq 0$ 为假）。 -/
theorem mem_polarDown_Bce (g : Kce.GFCA) : g ∉ Kce.polarDown Bce := by
  intro hg
  have : Kce.Irel g (0 : Kce.MFCA) := hg (by simp [Bce])
  simp [Kce] at this

/-- $\mathrm{polarDown}\,A_{\mathrm{ce}}=\varnothing$
（没有自然数严格大于所有正整数）。 -/
theorem polarDown_Ace_empty : Kce.polarDown Ace = (∅ : Set Kce.GFCA) := by
  ext g
  constructor
  · intro hg
    exfalso
    have hcon : ∀ a : Kce.MFCA, a ∈ Ace → Kce.Irel g a := hg
    have hn : g = (show Kce.GFCA from (show ℕ from g)) := rfl
    rw [hn] at hcon
    generalize (show ℕ from g) = n at hcon
    cases n with
    | zero =>
      have : Kce.Irel (show Kce.GFCA from 0) (show Kce.MFCA from 1) :=
        hcon (show Kce.MFCA from 1) (by simp [Ace])
      simp [Kce] at this
    | succ m =>
      have : Kce.Irel (show Kce.GFCA from (m + 1)) (show Kce.MFCA from (m + 1)) :=
        hcon (show Kce.MFCA from (m + 1)) (by simp [Ace])
      simp [Kce] at this
  · intro hg; exact absurd hg (by simp)

/-- §3 断言 1：$\mathbb{K}_{\mathrm{ce}}\models A_{\mathrm{ce}}\Rightarrow B_{\mathrm{ce}}$。 -/
theorem models_Ace_Bce : Kce.Models Ace Bce := by
  rw [FormalCtx.Models, polarDown_Ace_empty]
  exact Set.empty_subset _

/-- 把自然数搬到对象侧（两侧同为 $\mathbb{N}$）。 -/
def nG (n : ℕ) : Kce.GFCA := (show ℕ = Kce.GFCA from rfl) ▸ n

/-- **有限子集必留下「未被击破」的对象**：

对任意有限 $A_0\subseteq A_{\mathrm{ce}}$，
$\mathrm{polarDown}\,A_0\neq\varnothing$。

**证明**：$A_0$ 有限非空时取其上界 $M=\max A_0$，则 $M+1$ 严格大于
$A_0$ 中每个（且均为非零的）元素，故 $M+1\in\mathrm{polarDown}\,A_0$；
$A_0=\varnothing$ 时 $\mathrm{polarDown}\,\varnothing=G_{\mathrm{FCA}}\neq\varnothing$。∎ -/
theorem finite_ne_polarDown_empty {A₀ : Set Kce.MFCA} (hsub : A₀ ⊆ Ace)
    (hfin : A₀.Finite) : Kce.polarDown A₀ ≠ (∅ : Set Kce.GFCA) := by
  intro hempty
  classical
  by_cases hne : A₀.Nonempty
  · let _ : LinearOrder Kce.MFCA := inferInstanceAs (LinearOrder ℕ)
    obtain ⟨a₀, ha₀⟩ := hne
    have hfinNE : hfin.toFinset.Nonempty := ⟨a₀, by simpa using ha₀⟩
    let m : Kce.MFCA := hfin.toFinset.max' hfinNE
    have hm : m ∈ A₀ := by
      have := Finset.max'_mem hfin.toFinset hfinNE
      simpa [m] using this
    have hmfin : m ∈ hfin.toFinset := by simpa using hm
    let g : Kce.GFCA := nG ((show ℕ from m) + 1)
    have hg : g ∈ Kce.polarDown A₀ := by
      intro a ha
      have hafin : a ∈ hfin.toFinset := by simpa using ha
      have han0 : a ≠ (0 : Kce.MFCA) := by
        have := hsub ha; simpa [Ace] using this
      have hle : (show ℕ from a) ≤ (show ℕ from m) := by
        have h0 := Finset.le_max' hfin.toFinset a hafin
        change (show ℕ from a) ≤ (show ℕ from hfin.toFinset.max' hfinNE) at h0
        simpa [m] using h0
      have hga : (show ℕ from g) = (show ℕ from m) + 1 := rfl
      constructor
      · exact han0
      · change (show ℕ from g) > (show ℕ from a)
        rw [hga]; omega
    rw [hempty] at hg
    exact absurd hg (by simp)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hzero : (0 : Kce.GFCA) ∈ Kce.polarDown (∅ : Set Kce.MFCA) := by
      intro a ha; exact absurd ha (by simp)
    rw [hempty] at hzero
    exact absurd hzero (by simp)

/-- §3 断言 2：对任意有限 $A_0\subseteq A_{\mathrm{ce}}$，
$\mathbb{K}_{\mathrm{ce}}\not\models A_0\Rightarrow B_{\mathrm{ce}}$。

**证明**：$\mathrm{polarDown}\,B_{\mathrm{ce}}=\varnothing$，
若 $\mathrm{polarDown}\,A_0\subseteq\varnothing$ 则
$\mathrm{polarDown}\,A_0=\varnothing$，与
`finite_ne_polarDown_empty` 矛盾。∎ -/
theorem not_models_finite (A₀ : Set Kce.MFCA) (hsub : A₀ ⊆ Ace) (hfin : A₀.Finite) :
    ¬ Kce.Models A₀ Bce := by
  intro h
  have hpd : Kce.polarDown A₀ ≠ ∅ := finite_ne_polarDown_empty hsub hfin
  have : Kce.polarDown A₀ ⊆ (∅ : Set Kce.GFCA) := by
    intro g hg
    exact absurd (h hg) (mem_polarDown_Bce g)
  exact hpd (Set.Subset.antisymm this (Set.empty_subset _))

/-- **§3 主结论（否证）**：实质形紧致性**去掉对象有限性前件后为假**。

即：一般有
$$\mathbb{K}\models A\Rightarrow B\ \not\Rightarrow\
  \exists A_0\subseteq A,\ A_0\ \text{有限}\wedge\mathbb{K}\models A_0\Rightarrow B .$$

反例由 `Kce` / `Ace` / `Bce` 给出；本定理把三条断言合起来：
`models_Ace_Bce`（大前提成立）+ `not_models_finite`（无有限子集可用）。∎ -/
theorem compact_models_fails_without_finite_G :
    ¬ (∀ (A B : Set Kce.MFCA), Kce.Models A B →
        ∃ A₀ : Set Kce.MFCA, A₀ ⊆ A ∧ A₀.Finite ∧ Kce.Models A₀ B) := by
  intro h
  obtain ⟨A₀, hsub, hfin, hmodels⟩ := h Ace Bce models_Ace_Bce
  exact not_models_finite A₀ hsub hfin hmodels
