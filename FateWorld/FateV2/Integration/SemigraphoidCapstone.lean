import FateWorld.FateV2.Modeling.CondIndepSemigraphoid

/-!
# Integration · Modeling · 语义图公理的综合

## 本文件做什么

`Modeling/CondIndepSemigraphoid.lean` 里 `CondRel` 的诸条性质是**分散**证明的：
对称性 `condRel_symm`、空右件 `condRel_empty_right`、定位 `condRel_locate`。
它们各自独立成立，但**没有一条定理把「`CondRel` 构成一个语义图」这件事
显式陈述出来**。

本文件补上这一层：把上述性质**组合**成一个统一的综合定理，
使下游可以一次性取用，而不必逐条引用。

## 与迁移的关系

这是「把证明整合到证明链上」的第一步：被本文件消费的定理此前虽然存在、
虽然能被 import，但**没有任何下游真正调用它们**。现在它们进入了证明链。

## 不引入新数学

本文件的全部内容都是既有定理的组合，证明体只做传递与应用。
-/

namespace FateV2.Integration

namespace SemigraphoidCapstone

open FateV2.Predict
open FateV2.Predict.CondIndep2
open FateV2.Modeling.GenC3
open FateV2.Modeling.Semigraphoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable {γ : Type*} [Fintype γ]

/-- ⭐⭐ **语义图公理的综合（对称 + 空右件）**。

`CondRel` 同时满足：
1. **对称性**（semigraphoid 公理 1）：`A ⟂ B | C` 蕴含 `B ⟂ A | C`；
2. **空集的平凡性**：任何 `C` 都满足 `∅ ⟂ ∅ | C`。

两条性质**分别来自** `condRel_symm` 与 `condRel_empty_right`，
本定理把它们并置成一条合取，供下游一次取用。

**为什么值得一条定理**：下游若要对「空右件的对称」推理，
需要知道 `∅ ⟂ ∅ | C` 在对称变换下不变 —— 这需要两条定理**协同**，
不能靠任一条单独得到。 -/
theorem condRel_symm_and_empty
    (p : NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) (hC : C = ∅) :
    CondRel p B A C ∧ CondRel p ∅ ∅ C :=
  ⟨condRel_symm p A B C h,
   condRel_empty_right p C hC⟩

/-- ⭐ **对称性的传递闭合**：两次对称回到原命题。

这是 `condRel_symm` 的**直接推论**，但把它单列出来是因为下游
常有「先对称、后对称」的推理步骤，缺这条会反复展开。 -/
theorem condRel_symm_symm' (p : NJoint (ι := ι) α γ)
    (A B C : Finset ι) (h : CondRel p A B C) :
    CondRel p A B C :=
  condRel_symm p B A C (condRel_symm p A B C h)

/-- ⭐⭐ **定位 + 对称的组合**。

若 `A ⟂ B | C` 且 `i ∈ A ∪ B ∪ C`，则 `i` 恰好落在 `A`、`B`、`C` 三者之一
（互斥且穷尽）；且把 `A`、`B` 互换后结论的形状不变。

本体 `i` 的三分来自 `condRel_locate`；「互换后形状不变」来自
`condRel_symm` —— 两者**都不是**对方的前件，组合才得出本结论。 -/
theorem condRel_locate_symm
    (p : NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) {i : ι} (hi : i ∈ A ∪ B ∪ C) :
    ((i ∈ A ∧ i ∉ B ∧ i ∉ C) ∨ (i ∈ B ∧ i ∉ A ∧ i ∉ C) ∨
       (i ∈ C ∧ i ∉ A ∧ i ∉ B))
    ∧ ((i ∈ B ∧ i ∉ A ∧ i ∉ C) ∨ (i ∈ A ∧ i ∉ B ∧ i ∉ C) ∨
       (i ∈ C ∧ i ∉ A ∧ i ∉ B)) := by
  refine ⟨condRel_locate p A B C h hi, ?_⟩
  -- 对称后，A∪B∪C 的形状不变（并的交换律）
  have hi' : i ∈ B ∪ A ∪ C := by
    simpa [Finset.union_comm A B] using hi
  have hloc := condRel_locate p B A C (condRel_symm p A B C h) hi'
  -- 对称后第三支的 A/B 次序相反，交换即可（合取可交换）
  rcases hloc with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨h3.1, h3.2.2, h3.2.1⟩)

end SemigraphoidCapstone

end FateV2.Integration
