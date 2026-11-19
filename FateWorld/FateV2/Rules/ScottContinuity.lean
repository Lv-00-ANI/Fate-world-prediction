/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules
阶段：**专项审计 —— FCA 闭包算子的 Scott 连续性**

---------------------------------------------------------------------------
本文件回答的问题
---------------------------------------------------------------------------
规格任务：

> `closureOp` 的 Scott 连续性——查文献中「FCA 闭包算子是否 Scott 连续」的结果；
> 若连续，写出 Lean 陈述；若不连续，说明反例。

**结论（先说答案）**：

> **FCA 的属性闭包算子 $B\mapsto B''$ 在一般情况下*不是* Scott 连续的。**
> 它连续 **当且仅当** 相应的闭包系统（内涵集族 $\mathrm{Int}(\mathbb{K})$）
> 对**有向上并**封闭；这等价于闭包算子是 **finitary / algebraic（有限生成）** 的。
> **有限形式背景**（$M_{\mathrm{FCA}}$ 有限）是保证连续的充分条件；
> 无限背景存在反例（见本文件 §3，机器可验证）。

---------------------------------------------------------------------------
文献定位（诚实标注，不虚构作者/年份/数字）
---------------------------------------------------------------------------
「Scott 连续」是 **Dana Scott** 创立的 domain theory 术语，
Mathlib 的 `Mathlib.Order.ScottContinuity`（作者 Christopher Hoskin）以其命名，
参考 [Abramsky–Jung, *Domain Theory*]、[Gierz et al., *A Compendium of
Continuous Lattices*]。

与本任务相关的**标准事实**（可对任意格论/domain theory 教材复核）：

1. **闭包算子一般不必 Scott 连续。**
   闭包算子保**任意交**（因此闭集族是闭包系统），但**不保**有向上并。
   闭包算子 Scott 连续 $\iff$ 闭包系统对**有向上并**封闭
   $\iff$ 闭包算子**有限生成 / 代数（algebraic / finitary）**。

2. **FCA 的内涵集族 = 一个闭包系统的闭集。**
   $B$ 闭 $\iff B=B''$。它**对任意交封闭**，
   但**对有向上并一般*不*封闭**（反例见 §3）。

3. **有限形式背景**：此时 $M_{\mathrm{FCA}}$ 有限，
   `Set M_FCA` 的有向上族必在有限步内触顶，
   故闭包算子**必 Scott 连续**（§4）。

**本文件不虚构文献条目**；上述仅为标准结论的陈述，
其**形式化证明由本文件自己给出**（§3、§4），不依赖任何未在 Lean 中验证的引文。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- `[已知]`：所引 Mathlib 的定义/引理（Scott 连续性、Galois 连接、Concept）。
- `[自证]`：本文件内的定理，均**机器可验证**，无 `sorry`/`axiom`。
- 本文件**不**声称「文献中某篇论文首次证明」——只给出结论与可复核的形式化。
-/

import Mathlib.Order.ScottContinuity
import Mathlib.Order.Concept
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Preorder.Finite
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
namespace FateV2.Rules
open Set

universe u v

noncomputable section

-- 反例背景 `Kbad` 的 `GFCA`/`MFCA` 是 `ℕ`/`Option ℕ`。
-- Mathlib 默认对结构投影使用半可约透明度，导致 `ℕ` 与 `Kbad.GFCA`
-- 在 `Membership` 类型类合成时不被视为 defeq。此处放宽等定义性透明度。
set_option backward.isDefEq.respectTransparency false

namespace FormalCtx

variable (K : FormalCtx)

/-!
  # Rules · ScottContinuity

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ScottContinuity.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FCA, Implication
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  Scott 连续性的陈述（Mathlib 绑定）
    =========================================================================== -/

/-- **属性闭包算子的 Scott 连续性**（规格任务的陈述落点）。

依 Mathlib `Mathlib.Order.ScottContinuity`：

> `f` Scott 连续 $\iff$ 对每个**非空有向上**集 $D$，
> $f(\bigsqcup D)=\bigsqcup f(D)$。

在 `Set K.MFCA` 上，`⊔ = ∪`、`⨆ = ⋃`，
故此处即为：对每个非空有向上族 $D$（关于 $\subseteq$ 有向上），

$$\mathrm{closureOp}\Bigl(\bigcup_{B\in D}B\Bigr)=\bigcup_{B\in D}\mathrm{closureOp}(B).$$

**此定义是对 Mathlib `ScottContinuous` 的记法绑定**，不是新概念。
标 `[已知]`（Mathlib 定义）。 -/
abbrev IsScottContinuous (f : Set K.MFCA → Set K.MFCA) : Prop := ScottContinuous f

/-- $B\mapsto B''$ 的 Scott 连续性的**逐条展开**（便于下游按规格写法使用）。

`[已知]`：与 `ScottContinuous` 定义等价（`Iff.rfl`）。 -/
theorem isScottContinuous_iff (f : Set K.MFCA → Set K.MFCA) :
    IsScottContinuous K f ↔
      ∀ ⦃D : Set (Set K.MFCA)⦄, D.Nonempty → DirectedOn (· ⊆ ·) D →
        ∀ ⦃a⦄, IsLUB D a → IsLUB (f '' D) (f a) :=
  Iff.rfl

/-! ===========================================================================
    §2  内涵集族：交封闭（总是），有向上并封闭（一般不）
    =========================================================================== -/

/-- **内涵集族对任意交封闭**（闭包系统）。

$B''=B$ 的内涵族在**任意交**下封闭：
若每个 $B\in S$ 是内涵，则 $\bigcap S$ 也是内涵。

**这是 FCA 基本定理的伴随（Galois 连接）侧的直接推论**：
`closureOp` 是 `upperPolar ∘ lowerPolar`，
`upperPolar` 作为右伴随保**任意交**。标 `[自证]`。 -/
theorem isClosedAttr_sInter {S : Set (Set K.MFCA)} (h : ∀ B ∈ S, K.IsClosedAttr B) :
    K.IsClosedAttr (⋂₀ S) := by
  -- 两向包含：`⋂S ⊆ (⋂S)''` 为扩张性；反向由单调性 + 每个 B 闭。
  have hle : K.closureOp (⋂₀ S) ⊆ ⋂₀ S := by
    intro m hm B hB
    -- m ∈ closureOp (⋂S) ⊆ closureOp B = B
    have hmono : K.closureOp (⋂₀ S) ⊆ K.closureOp B :=
      K.closureOp_mono (sInter_subset_of_mem hB)
    rw [show K.closureOp B = B from h B hB] at hmono
    exact hmono hm
  have hge : ⋂₀ S ⊆ K.closureOp (⋂₀ S) := K.subset_closureOp _
  rw [IsClosedAttr]
  exact Set.Subset.antisymm hle hge

/-- **闭集判定：$B$ 闭 $\iff$ $B''\subseteq B$**（供 §3 用的等价形式）。`[自证]` -/
theorem isClosedAttr_iff_closureOp_subset (B : Set K.MFCA) :
    K.IsClosedAttr B ↔ K.closureOp B ⊆ B := by
  rw [IsClosedAttr]
  exact ⟨fun h => h.le, fun h => Set.Subset.antisymm h (K.subset_closureOp B)⟩

end FormalCtx

/-! ===========================================================================
    §3  ⭐ 反例：FCA 闭包算子一般**不** Scott 连续
    =========================================================================== -/

/-- **反例形式背景** $\mathbb{K}_{\text{bad}}$。

- 对象集 $G_{\mathrm{FCA}}=\mathbb{N}$；
- 属性集 $M_{\mathrm{FCA}}=\{\,a_k\mid k\in\mathbb{N}\,\}\cup\{z\}$
  （Lean 中 `Option ℕ`：`some k` 记 $a_k$，`none` 记 $z$）；
- $I$：$g\,I\,a_k\iff k\le g$，且 $g\,I\,z$ **恒假**。

**直观**：对象 $g$ 只与「前 $g+1$ 个」属性 $a_0,\dots,a_g$ 关联。 -/
def Kbad : FormalCtx where
  GFCA := ℕ
  MFCA := Option ℕ
  Irel := fun g m => match m with | some k => k ≤ g | none => False

namespace Kbad

open FateV2.Rules.FormalCtx

/-- 反例中 $\mathrm{Irel}$ 的展开规则（`some k` 时）。 -/
@[simp] theorem Irel_some (g k : ℕ) : Kbad.Irel g (some k) = (k ≤ g) := rfl
/-- 反例中 $\mathrm{Irel}$ 的展开规则（`none` 时）。 -/
@[simp] theorem Irel_none (g : ℕ) : Kbad.Irel g none = False := rfl

/-- 属性集 $t_n=\{a_0,\dots,a_n\}$。 -/
def tn (n : ℕ) : Set Kbad.MFCA := {m | ∃ k, k ≤ n ∧ m = some k}

/-- 「全部 $a_k$」集 $\bigcup_n t_n=\{a_k\mid k\in\mathbb{N}\}$。 -/
def allA : Set Kbad.MFCA := {m | ∃ k, m = some k}

theorem mem_tn {n : ℕ} {m : Kbad.MFCA} : m ∈ tn n ↔ ∃ k, k ≤ n ∧ m = some k :=
  Iff.rfl

theorem mem_allA {m : Kbad.MFCA} : m ∈ allA ↔ ∃ k, m = some k := Iff.rfl

/-- **每个 $t_n$ 都是内涵**（闭集）：$t_n''=t_n$。

**证明直观**：与 $t_n$ 全部属性关联的对象恰为 $\{g_m\mid m\ge n\}$
（因 $g_m\,I\,a_k\iff k\le m$），而与这些对象全部关联的属性恰为 $a_0,\dots,a_n$。 -/
theorem isClosedAttr_tn (n : ℕ) : Kbad.IsClosedAttr (tn n) := by
  rw [FormalCtx.isClosedAttr_iff_closureOp_subset]
  intro m hm
  -- hm : m ∈ closureOp (tn n)
  rw [FormalCtx.closureOp, FormalCtx.polarUp, FormalCtx.polarDown] at hm
  rw [mem_upperPolar_iff] at hm
  have hn : (n : Kbad.GFCA) ∈ lowerPolar Kbad.Irel (tn n) := by
    rw [mem_lowerPolar_iff]
    intro b hb
    rw [mem_tn] at hb
    obtain ⟨k, hk, hbk⟩ := hb
    rw [hbk, Irel_some]; exact hk
  have hm' := hm hn
  rcases m with _ | k
  · rw [Irel_none] at hm'; exact hm'.elim
  · rw [mem_tn]
    rw [Irel_some] at hm'
    exact ⟨k, hm', rfl⟩

/-- **$\bigcup_n t_n$ 的闭包是整个属性集**：$(\bigcup_n t_n)''=M_{\mathrm{FCA}}$。

**关键**：没有任何对象与*所有* $a_k$ 关联
（$g$ 与 $a_{g+1}$ 不关联），故 $(\bigcup_n t_n)'=\varnothing$，
从而其闭包为 $\varnothing'=M_{\mathrm{FCA}}$。 -/
theorem closureOp_iUnion_tn : Kbad.closureOp (⋃ n, tn n) = univ := by
  ext m; constructor
  · intro _; trivial
  · intro _
    rw [FormalCtx.closureOp, FormalCtx.polarUp, mem_upperPolar_iff]
    intro g hg
    rw [FormalCtx.polarDown, mem_lowerPolar_iff] at hg
    -- hg 要求 g 与所有 a_k 关联，但 g 与 a_{g+1} 不关联 → 矛盾
    let g' : ℕ := g
    exact absurd (hg (b := some (g' + 1)) (by
      rw [mem_iUnion]
      exact ⟨(g' + 1 : Kbad.GFCA), ⟨g' + 1, le_refl _, rfl⟩⟩))
      (by rw [Irel_some]; omega)

/-- `none`（即 $z$）不属于 $\bigcup_n t_n$。 -/
theorem none_not_mem_iUnion_tn : (none : Kbad.MFCA) ∉ (⋃ n, tn n) := by
  rw [mem_iUnion]
  rintro ⟨n, hn⟩
  rw [mem_tn] at hn
  obtain ⟨k, _, hk⟩ := hn
  exact nomatch hk

/-- **⭐ 主反例：$\mathbb{K}_{\text{bad}}$ 的 `closureOp` 不 Scott 连续。**

取 $D=\{t_n\mid n\in\mathbb{N}\}$。它是一个**非空有向上**族
（$t_i\cup t_j=t_{\max(i,j)}$），其上确界为 $\bigcup_n t_n$。
于是 Scott 连续性会要求

$$\mathrm{closureOp}\Bigl(\bigcup_n t_n\Bigr)=\bigcup_n \mathrm{closureOp}(t_n),$$

即 $M_{\mathrm{FCA}}=\bigcup_n t_n$（左端由 `closureOp_iUnion_tn`，右端用各 $t_n$ 闭）。
但 $z\notin\bigcup_n t_n$，矛盾。 -/
theorem not_scottContinuous : ¬ FormalCtx.IsScottContinuous Kbad Kbad.closureOp := by
  rw [FormalCtx.isScottContinuous_iff]
  intro hsc
  -- D = range tn，非空、有向上
  have hne : (Set.range tn).Nonempty := ⟨tn 0, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range tn) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine ⟨tn (max i j), ⟨max i j, rfl⟩, ?_, ?_⟩
    · intro m hm; rw [mem_tn] at hm ⊢
      obtain ⟨k, hk, rfl⟩ := hm; exact ⟨k, hk.trans (le_max_left _ _), rfl⟩
    · intro m hm; rw [mem_tn] at hm ⊢
      obtain ⟨k, hk, rfl⟩ := hm; exact ⟨k, hk.trans (le_max_right _ _), rfl⟩
  -- 上确界为 allA = ⋃ n, tn n
  have hallA : (⋃ n, tn n) = allA := by
    ext m; constructor
    · intro hm
      rw [mem_iUnion] at hm
      obtain ⟨n, hn⟩ := hm
      rw [mem_tn] at hn
      obtain ⟨k, _, rfl⟩ := hn
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      rw [mem_iUnion]
      exact ⟨k, ⟨k, le_refl k, rfl⟩⟩
  have hlub : IsLUB (Set.range tn) (⋃ n, tn n) := by
    constructor
    · rintro _ ⟨n, rfl⟩ m hm
      exact mem_iUnion.mpr ⟨n, hm⟩
    · intro ub hub m hm
      rw [mem_iUnion] at hm
      obtain ⟨n, hn⟩ := hm
      exact hub ⟨n, rfl⟩ hn
  have him := hsc hne hdir hlub
  -- allA 是 closureOp '' range tn 的上界（因每个 closureOp(tn)=tn⊆allA）
  have hub : ∀ a ∈ (Kbad.closureOp '' Set.range tn), a ⊆ allA := by
    rintro a ⟨y, ⟨n, rfl⟩, rfl⟩ m hm
    have hcl : Kbad.closureOp (tn n) = tn n :=
      isClosedAttr_tn n
    rw [hcl, mem_tn] at hm
    obtain ⟨k, _, rfl⟩ := hm
    exact ⟨k, rfl⟩
  -- 由 IsLUB 的最小上界性：closureOp (⋃ tn) ⊆ allA
  have hsub : Kbad.closureOp (⋃ n, tn n) ⊆ allA := him.2 hub
  -- 但 closureOp (⋃ tn) = univ ⊇ {none}，而 none ∉ allA
  rw [closureOp_iUnion_tn] at hsub
  exact none_not_mem_iUnion_tn (by
    rw [hallA]; exact hsub (mem_univ none))

end Kbad

/-! ===========================================================================
    §4  正向结果：有限背景 ⟹ Scott 连续
    =========================================================================== -/

/-- **有限有向集必有最大元**（有限 + 有向上 $\Rightarrow$ 触顶）。

标 `[自证]`（纯序论事实，用 `Set.Finite.exists_maximal`）。 -/
theorem finite_directed_has_max {α : Type*} [PartialOrder α] [Fintype α] (D : Set α)
    (hD : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) :
    ∃ d ∈ D, ∀ x ∈ D, x ≤ d := by
  classical
  obtain ⟨m, hmD, hmax⟩ := (Set.toFinite D).exists_maximal hD
  refine ⟨m, hmD, ?_⟩
  intro x hxD
  obtain ⟨z, hzD, hmz, hxz⟩ := hdir m hmD x hxD
  exact hxz.trans (hmax hzD hmz)

/-- **有限格上的单调函数 Scott 连续**。

有限完备格中，任何非空有向上集都有最大元，故上确界被取到；
单调函数于是把上确界映到上确界。标 `[自证]`。 -/
theorem monotone_scottContinuous_of_finite {α β : Type*} [CompleteLattice α] [Fintype α]
    [Preorder β] {f : α → β} (hf : Monotone f) : ScottContinuous f := by
  intro d hdne hdir a ha
  obtain ⟨m, hmd, hmax⟩ := finite_directed_has_max d hdne hdir
  have hsup : IsLUB d m := ⟨fun x hx => hmax x hx, fun _ hub => hub hmd⟩
  have heq : a = m := ha.unique hsup
  rw [heq]
  -- f m 是 f '' d 的最大元，即其上确界
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hf (hmax x hx)
  · intro ub hub
    exact hub ⟨m, hmd, rfl⟩

/-- **⭐ 有限形式背景的闭包算子 Scott 连续。**

当 $M_{\mathrm{FCA}}$ 有限（`Fintype K.MFCA`）时，
`Set K.MFCA` 的有向上族必在有限步内触顶，故 `closureOp`
（作为单调函数）Scott 连续。

**证明**：`closureOp_mono` 给出单调性，再由
`monotone_scottContinuous_of_finite`。标 `[自证]`。 -/
theorem closureOp_scottContinuous_of_finite [Fintype K.MFCA] :
    FormalCtx.IsScottContinuous K K.closureOp :=
  monotone_scottContinuous_of_finite (fun _ _ h => K.closureOp_mono h)

/-! ===========================================================================
    §5  小结合论
    =========================================================================== -/

/-!
**本文件确立的结论**：

| 命题 | 结论 | Lean |
|---|---|---|
| 闭包算子保任意交（闭包系统） | 成立 | `isClosedAttr_sInter` |
| 闭包算子在**一般**背景下 Scott 连续 | **否** | `Kbad.not_scottContinuous` |
| 闭包算子在**有限**背景下 Scott 连续 | 成立 | `closureOp_scottContinuous_of_finite` |

**为什么不连续（本质）**：
Scott 连续性 $B\mapsto B''$ 等价于「内涵集族对*有向上并*封闭」。
FCA 的内涵集族**只保证对任意交封闭**，不保证对有向上并封闭。
§3 的反例正构造了一个**有向上**的内涵族 $\{t_n\}$，
其并 $\bigcup_n t_n$ 恰因「缺少一个对象见证」而不再是内涵，
补闭包后多出 $z$。

**何时连续**：当且仅当闭包算子 **finitary（有限生成 / algebraic）**——
即每个内涵由某个有限子集生成。有限背景是充分条件（§4）。

**诚实边界**：
- 本文件不主张「§3 反例在文献中首次出现」；它是标准「闭包系统非代数」的实例。
- 本文件不引入任何 `axiom`/`sorry`；所有定理机器可验证。
- `not_scottContinuous` 只否定 `ScottContinuous`（全定义域）；
  未在本文档中断言「没有任何背景使其连续」——恰恰相反，§4 给出充分条件。
-/

end

end FateV2.Rules