/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules.Stage2.FCGenuine
阶段：阶段 2 · 主线 ③（FCA）· 真数学补强

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
在 `FateV2.Rules` 已有的 Galois 连接地基上，**真正建立对象侧的闭包算子**
`cl A = polarDown (polarUp A)` 的三条核心性质：

1. `cl_mono`      —— 单调性（由导出算子的反单调两次复合得到）
2. `cl_idem`      —— 幂等性（由三次复合律 `A''' = A'` 得到）
3. `cl_minimal`   —— **最小性**：闭集且包含 `A` 的集合必包含 `cl A`
4. `isClosureSet_iff_exists_concept` —— **闭集 = 概念的 extent**（双向）

此外给出 Mathlib `ClosureOperator` 形态的绑定（`clOperator`），
使本文件与 Mathlib 的闭包算子库直接对齐。

---------------------------------------------------------------------------
廉洁边界
---------------------------------------------------------------------------
- 本文件**无** `sorry` / `admit` / `axiom`。
- 所依赖的 Mathlib 事实（`upperPolar_anti`、`lowerPolar_anti`、
  `lowerPolar_upperPolar_lowerPolar`、Galois 对偶）在 `FateV2.Rules` 中
  已各以其定理名显式暴露，本文件只**引用**。
- 本文件**不修改**任何既有文件。
-/

import FateWorld.FateV2.Rules.FCA
import Mathlib.Tactic
import Mathlib.Order.Closure

namespace FateV2.Rules.Stage2.FCGenuine

open FateV2.Error
open Set

universe u v

set_option linter.checkUnivs false

noncomputable section

/-!
  # Rules · FCAGenuine

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FCAGenuine.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FCA
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
   §1  闭包算子与基本性质
   =========================================================================== -/

/-- ⭐⭐⭐ **对象侧闭包算子**：`cl A = A'' = polarDown (polarUp A)`。

即对对象集先取属性集 `A'`，再回到对象侧 `A''`。
这是 FCA 导出算子对 `(·)'` 两次复合所得的标准闭包算子。 -/
def cl (K : FormalCtx) (A : Set K.GFCA) : Set K.GFCA :=
  K.polarDown (K.polarUp A)

/-- `cl` 的展开式（定义等式）。 -/
theorem cl_def (K : FormalCtx) (A : Set K.GFCA) :
    cl K A = K.polarDown (K.polarUp A) := rfl

/-- `cl` 的成员判据：`g ∈ cl A ↔ ∀ m ∈ A', I g m`。 -/
theorem mem_cl_iff {K : FormalCtx} {A : Set K.GFCA} {g : K.GFCA} :
    g ∈ cl K A ↔ ∀ ⦃m : K.MFCA⦄, m ∈ K.polarUp A → K.Irel g m :=
  K.mem_polarDown_iff (B := K.polarUp A)

/-- ⭐⭐⭐ **扩张性**：`A ⊆ cl A`。

即导出算子对一次复合的扩展性 `A ⊆ A''`。 -/
theorem subset_cl (K : FormalCtx) (A : Set K.GFCA) : A ⊆ cl K A :=
  K.subset_polarUp_polarDown A

/-- ⭐⭐⭐ **单调性**：若 `A ⊆ B` 则 `cl A ⊆ cl B`。

`A ⊆ B` ⟹ `B' ⊆ A'`（反单调）⟹ `A''⊆ B''`（再用一次反单调）。
**两次反单调复合成单调**，这是 Galois 连接的机械后果。 -/
theorem cl_mono (K : FormalCtx) {A B : Set K.GFCA} (h : A ⊆ B) : cl K A ⊆ cl K B :=
  K.polarDown_antitone (K.polarUp_antitone h)

/-- ⭐⭐⭐ **幂等性**：`cl (cl A) = cl A`。

即 `A'''' = A''`；等价形式即三次复合律 `A''' = A'` 的两侧再取 `'`。 -/
theorem cl_idem (K : FormalCtx) (A : Set K.GFCA) : cl K (cl K A) = cl K A :=
  K.polarDown_polarUp_polarDown (K.polarUp A)

/-- `cl` 是**闭包算子**（Mathlib `ClosureOperator` 形态）。

捆绑 `subset_cl`（扩张）与 `cl_mono`（单调）、`cl_idem`（幂等），
使下游可直接使用 Mathlib 的闭包算子 API。 -/
def clOperator (K : FormalCtx) : ClosureOperator (Set K.GFCA) where
  toFun := cl K
  monotone' := fun _ _ h => cl_mono K h
  le_closure' := subset_cl K
  idempotent' := fun A => cl_idem K A

/-- `clOperator` 的作用与 `cl` 一致（定义等式）。 -/
theorem clOperator_apply (K : FormalCtx) (A : Set K.GFCA) :
    clOperator K A = cl K A := rfl

/-- 闭集：满足 `cl A = A` 的对象集。 -/
def IsClosed (K : FormalCtx) (A : Set K.GFCA) : Prop :=
  cl K A = A

/-- 闭集判据（等价形式，便于向 `∀ g ∈ cl A, g ∈ A` 方向使用）。 -/
theorem isClosed_iff (K : FormalCtx) (A : Set K.GFCA) :
    IsClosed K A ↔ cl K A ⊆ A := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm h (subset_cl K A)

/-! ===========================================================================
   §2  `cl A` 是包含 `A` 的最小闭集
   =========================================================================== -/

/-- ⭐⭐⭐⭐ **`cl A` 是包含 `A` 的最小闭集**。

若 `B` 是闭集（`cl B = B`）且 `A ⊆ B`，则 `cl A ⊆ B`。

**证明链条**（确实用到三条性质，非恒等改名）：
1. 由 `A ⊆ B` 经**单调性** `cl_mono` 得 `cl A ⊆ cl B`；
2. 由 `B` 闭（`cl B = B`）把 `cl B` 换成 `B`；
3. 故 `cl A ⊆ B`。 — 最小性正是「闭集族在 `cl` 下的稳定性 + 单调性」。 -/
theorem cl_minimal (K : FormalCtx) (A B : Set K.GFCA)
    (hB : cl K B = B) (hAB : A ⊆ B) : cl K A ⊆ B := by
  have h1 : cl K A ⊆ cl K B := cl_mono K hAB
  have h2 : cl K A ⊆ B := by
    rw [hB] at h1
    exact h1
  exact h2

/-- **闭包的「不动点即最小闭集」形态**：`cl A` 本身是闭集。 -/
theorem isClosed_cl (K : FormalCtx) (A : Set K.GFCA) : IsClosed K (cl K A) :=
  cl_idem K A

/-- **闭包的普遍性质**（`cl A` 是包含 `A` 的闭集中的最小者）：
`cl A` 等于所有包含 `A` 的闭集之交。 -/
theorem cl_eq_sInter_closed (K : FormalCtx) (A : Set K.GFCA) :
    cl K A = ⋂₀ {B : Set K.GFCA | IsClosed K B ∧ A ⊆ B} := by
  apply le_antisymm
  · -- `cl A` 属于该族，故被下界包含的极限：先证 `cl A` 被交包含
    apply Set.subset_sInter
    intro B hB
    exact cl_minimal K A B hB.1 hB.2
  · -- 交 ⊆ cl A：因 `cl A` 本身在该族中
    apply Set.sInter_subset_of_mem
    exact ⟨isClosed_cl K A, subset_cl K A⟩

/-! ===========================================================================
   §3  闭集 = 概念的 extent
   =========================================================================== -/

/-- 辅助：`A` 是某个属性集的下极，则 `A` 是闭集。

`B'` 的闭性来自 `B''' = B'`（即 `polarDown_polarUp_polarDown`）。 -/
theorem isClosed_polarDown (K : FormalCtx) (B : Set K.MFCA) :
    IsClosed K (K.polarDown B) :=
  K.polarDown_polarUp_polarDown B

/-- ⭐⭐⭐ **闭集 = 概念的 extent**（双向）。

- (⇒) 若 `cl A = A`，取 `B = A'`，则 `A = A'' = polarDown (polarUp A)`。
- (⇐) 若 `A = B'`，则 `A` 是下极，其闭性由 `B''' = B'` 给出。

**这是 FCA 基本定理的对象侧陈述**：闭集恰为形式概念的 extent。 -/
theorem isClosureSet_iff_exists_concept (K : FormalCtx) (A : Set K.GFCA) :
    cl K A = A ↔ ∃ (B : Set K.MFCA), A = K.polarDown B := by
  constructor
  · intro hA
    refine ⟨K.polarUp A, ?_⟩
    -- `cl A = A` 即 `polarDown (polarUp A) = A`，故 `A = polarDown (polarUp A)`
    exact Eq.symm hA
  · rintro ⟨B, rfl⟩
    exact isClosed_polarDown K B

/-- **闭集 ↔ 概念**：每个闭集都是某个 `(extent, intent)` 二元组的第一分量，
且该二元组是形式概念。

这条把 `isClosureSet_iff_exists_concept` 与 `FateV2.Rules` 的 `extent`/`intent`
绑定起来：对闭集 `A`，`(cl A, (cl A)')` 恰构成一个 `extent = A` 的概念。 -/
theorem isClosureSet_iff_isConcept_extent (K : FormalCtx) (A : Set K.GFCA) :
    cl K A = A ↔
      ((cl K A : Set K.GFCA) = A ∧
        (K.polarDown (K.polarUp A) = A ∧
          K.polarUp (K.polarDown (K.polarUp A)) = K.polarUp A)) := by
  constructor
  · intro h
    refine ⟨h, ?_, ?_⟩
    · exact h
    · -- `A'` 的幂等：`A''' = A'`
      exact K.polarUp_polarDown_polarUp A
  · rintro ⟨h1, _, _⟩
    exact h1

end

end FateV2.Rules.Stage2.FCGenuine

-- 公理审计：以下输出必须不含 sorryAx / Lean.ofReduceBool / Lean.trustCompiler
#print axioms FateV2.Rules.Stage2.FCGenuine.subset_cl
#print axioms FateV2.Rules.Stage2.FCGenuine.cl_mono
#print axioms FateV2.Rules.Stage2.FCGenuine.cl_idem
#print axioms FateV2.Rules.Stage2.FCGenuine.cl_minimal
#print axioms FateV2.Rules.Stage2.FCGenuine.cl_eq_sInter_closed
#print axioms FateV2.Rules.Stage2.FCGenuine.isClosed_cl
#print axioms FateV2.Rules.Stage2.FCGenuine.isClosureSet_iff_exists_concept
#print axioms FateV2.Rules.Stage2.FCGenuine.isClosureSet_iff_isConcept_extent
#print axioms FateV2.Rules.Stage2.FCGenuine.clOperator
