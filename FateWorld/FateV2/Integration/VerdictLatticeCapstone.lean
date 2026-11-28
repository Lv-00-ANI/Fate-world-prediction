import FateWorld.FateV2.Core.VerdictAlgebra

/-!
# Integration · Core · 判定标准的格结构综合

## 本文件做什么

`Core/VerdictAlgebra.lean` 把「判定标准」`Criterion ι` 组织成一个格：
`And` 是下确界、`Or` 是上确界、`Stronger` 是序，并证明幂等、吸收、分配、
顶/底等性质。但这些性质**各自独立陈述**，下游要建一个「判定标准构成
分配格」的印象，需要自己把十几条并起来。

本文件把这一层补上：给出**打包**的综合定理，使下游一次取到完整结构。

## 与迁移的关系

`Core.VerdictAlgebra` 此前是「假接线」（被 import 但无名字被调用）。
本文件使它的格论定理进入证明链。

## 不引入新数学

每条都是既有定理的组合。
-/

namespace FateV2.Integration

namespace VerdictLatticeCapstone

open FateV2.Core

variable {ι : Type}

/-- ⭐⭐⭐ **`And` 是下确界、`Or` 是上确界（完整形式）**。

同时给出：
1. `And` 的两个上界（即「弱于两个分量」）；
2. `And` 的最大性（任何同时弱于两者的 `R` 也弱于 `And P Q`）；
3. `Or` 的两个下界；
4. `Or` 的最小性。

**为什么值得一条定理**：下游若要建立「`Criterion` 是格」，
需要 glb 与 lub 的**四条**性质同时成立。分成两次引用
（`and_is_glb`、`or_is_lub`）会丢掉「它们是同一个格的上下确界」
这一整体信息。 -/
theorem criterion_glb_lub (P Q R S : Criterion ι) :
    (Stronger (And P Q) P ∧ Stronger (And P Q) Q
        ∧ (Stronger R P → Stronger R Q → Stronger R (And P Q)))
      ∧ (Stronger P (Or P Q) ∧ Stronger Q (Or P Q)
        ∧ (Stronger P S → Stronger Q S → Stronger (Or P Q) S)) :=
  ⟨and_is_glb P Q R, or_is_lub P Q S⟩

/-- ⭐⭐ **幂等 + 吸收：格的两条压缩律**。

`P ⊓ P = P`（双向）与 `P ⊓ (P ⊔ Q) = P`（双向）同时成立。

这两条是「格」与「仅有序」的分界 —— 单靠 `stronger_preorder`
得不到它们。本定理把它们并置，供下游一次取用。 -/
theorem criterion_idem_absorb (P Q : Criterion ι) :
    (Stronger (And P P) P ∧ Stronger P (And P P))
      ∧ (Stronger (And P (Or P Q)) P ∧ Stronger P (And P (Or P Q))) :=
  ⟨and_idem P, absorb_and_or P Q⟩

/-- ⭐⭐ **分配律（双向）**。

`P ⊓ (Q ⊔ R) = (P ⊓ Q) ⊔ (P ⊓ R)`，两个方向都给出。

分配律是区分「格」与「分配格」的关键；下游若要用「判定标准的分情形论证」
（把合取分配到析取上），必须有这一条。 -/
theorem criterion_distrib (P Q R : Criterion ι) :
    Stronger (And P (Or Q R)) (Or (And P Q) (And P R))
      ∧ Stronger (Or (And P Q) (And P R)) (And P (Or Q R)) :=
  and_distrib_or P Q R

/-- ⭐⭐⭐ **判定标准的格公理汇总**。

把上述四组性质并成一条大合取：
序是预序、`And`/`Or` 分别是 glb/lub、幂等、吸收、分配，
且 `TrueC` 是顶、`FalseC` 是底。

**这条是本模块存在的理由**：它把「`Criterion ι` 构成分配格」
这一**整体断言**变成一条可引用的定理，而源文件里只有它的**零件**。 -/
theorem criterion_is_distributive_lattice (P Q R S : Criterion ι) :
    -- 序是预序
    (Stronger P P
      ∧ (Stronger P Q → Stronger Q R → Stronger P R))
    -- glb / lub
    ∧ (Stronger (And P Q) P ∧ Stronger (And P Q) Q
        ∧ (Stronger S P → Stronger S Q → Stronger S (And P Q)))
    ∧ (Stronger P (Or P Q) ∧ Stronger Q (Or P Q)
        ∧ (Stronger P R → Stronger Q R → Stronger (Or P Q) R))
    -- 幂等 + 吸收
    ∧ (Stronger (And P P) P ∧ Stronger P (And P P))
    ∧ (Stronger (And P (Or P Q)) P ∧ Stronger P (And P (Or P Q)))
    -- 分配
    ∧ (Stronger (And P (Or Q R)) (Or (And P Q) (And P R))
        ∧ Stronger (Or (And P Q) (And P R)) (And P (Or Q R)))
    -- 顶 / 底
    ∧ (Stronger P TrueC ∧ Stronger FalseC P) := by
  refine ⟨⟨stronger_refl P, fun h₁ h₂ => stronger_trans P Q R h₁ h₂⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact and_is_glb P Q S
  · exact or_is_lub P Q R
  · exact and_idem P
  · exact absorb_and_or P Q
  · exact and_distrib_or P Q R
  · exact ⟨stronger_true ι P, false_stronger ι P⟩

end VerdictLatticeCapstone

end FateV2.Integration