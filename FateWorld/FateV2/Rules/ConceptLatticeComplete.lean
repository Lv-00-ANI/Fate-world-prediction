/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.ConceptLatticeComplete
阶段：**阶段 1A 的实质补强**（规格 `02-证明路线/02-定理清单.md` T1A.9）

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
规格 T1A.9：

> `FCA 基本定理：概念格是完备格；形式概念是 Galois 连接的不动点`
> ｜前件：形式背景 $\mathbb{K}$ 给定｜类别 ①（几乎无条件）

`Fate.Stage1A` 中的 `T1A9_conceptLattice_complete` 只断言
`Nonempty (CompleteLattice (ConceptLattice K))`（证体为 `⟨inferInstance⟩`）。
那**只是「实例存在」的暴露**，**不是**「概念格为什么完备」的证明。

**本文件补上实质内容**：给出概念格的**任意交/任意并的显式构造**，
并证明它们满足 $\mathrm{IsGLB}$ / $\mathrm{IsLUB}$ 的**泛性质**：

1. **任意交**：对概念族 $S$，令
   $\bigwedge S=\bigl(\bigcap_{c\in S}A_c,\ (\bigcap_{c\in S}A_c)'\bigr)$。
   **关键数学事实**：**任意多个外延的交仍是外延**——
   因为概念格是闭包算子 $A\mapsto A''$ 的**闭集格**，
   而闭集对**任意交**封闭（`Order.IsExtent.iInter₂`）。
   这给出 $\bigwedge S$ 是一个形式概念，且是 $S$ 的最大下界。

2. **任意并**：对概念族 $S$，令
   $\bigvee S=\bigl(\bigcup_{c\in S}A_c\bigr)''$
   $=\mathrm{ofObjects}\bigl(\bigcup_{c\in S}A_c\bigr)$。
   即：**先取外延之并，再取闭包**。它是最小上界。

这两条合起来**构造性地**证明概念格完备——而不是引用一个黑箱实例。

---------------------------------------------------------------------------
与 Mathlib 的关系（诚实边界）
---------------------------------------------------------------------------
- Mathlib 的 `Mathlib.Order.Concept` **已提供** `instance : CompleteLattice (Concept α β r)`
  （文件内注释标为 *"One half of the fundamental theorem of concept lattices"*）。
- 本文件**不重新发明**该实例，而是**重复其证明思路**，把
  「闭集对任意交封闭 ⟹ 完备」这一**实质机制**在本框架的命名下展开，
  使 `T1A9` 在验收报告中有**可回查的证明体**，而非一句 `inferInstance`。
- 所用 Mathlib 构件（`IsExtent.iInter₂`、`ofObjects_le_iff`、
  `rel_extent_intent` 等）均标 `[已知]`：**外部既有结果，本框架内未证**。
- 本实现**不虚构**文献、作者、年份与数字。

---------------------------------------------------------------------------
-/

import Mathlib.Order.Concept
import Mathlib.Data.Set.Lattice
import Mathlib.Order.CompleteLattice.Basic
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Rules.FCA
namespace FateV2.Rules

open FateV2.Modeling
open Set Order

universe u v

set_option linter.checkUnivs false

noncomputable section

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-!
  # Rules · ConceptLatticeComplete

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ConceptLatticeComplete.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, FCA
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  任意交：外延的任意交仍是概念的外延
    =========================================================================== -/

/-- **任意多个外延的交仍是外延**（`[已知]`：Mathlib 的 `Order.IsExtent.iInter₂`）。

这是概念格**完备性**的**唯一实质来源**：
概念格外延的集合是一个**闭集系**（闭包算子 $A\mapsto A''$ 的不动点），
而**闭集系对任意交封闭**——这正是一条完备格公理模式。

本引理把该事实**在本框架的命名下显式化**，使下游不必知道
`IsExtent.iInter₂` 的名字。 -/
theorem isExtent_iInter_extent (S : Set (ConceptLattice K)) :
    IsExtent K.Irel (⋂ c ∈ S, c.extent) :=
  Order.IsExtent.iInter₂ _ fun c _ => c.isExtent_extent

/-- **概念族的任意交（显式构造）**——规格 $\bigwedge S$。

定义即「以外延之交集为外延、以上极化为内涵」的概念：
$$\bigwedge S=\Bigl(\bigcap_{c\in S}A_c,\ \Bigl(\bigcap_{c\in S}A_c\Bigr)'\Bigr).$$

**它由 `isExtent_iInter_extent` 保证是良定义的形式概念**——
这正是「闭集系对任意交封闭」的直接后果。 -/
def sInfConcept (S : Set (ConceptLattice K)) : ConceptLattice K :=
  Concept.ofIsExtent K.Irel (⋂ c ∈ S, c.extent) (K.isExtent_iInter_extent S)

/-- $\bigwedge S$ 的外延就是外延之交集（定义等式，`rfl`）。 -/
@[simp]
theorem sInfConcept_extent (S : Set (ConceptLattice K)) :
    (K.sInfConcept S).extent = ⋂ c ∈ S, c.extent := rfl

/-- **$\bigwedge S$ 是下界**：对每个 $c\in S$，$\bigwedge S\le c$。

证：外延之交集包含于每个外延（`biInter_subset_of_mem`），
再由 `concept_le_iff_extent_subset` 转成格序。 -/
theorem sInfConcept_le (S : Set (ConceptLattice K)) {c : ConceptLattice K}
    (hc : c ∈ S) : K.sInfConcept S ≤ c := by
  rw [concept_le_iff_extent_subset, sInfConcept_extent]
  exact biInter_subset_of_mem hc

/-- **$\bigwedge S$ 是最大下界**：任何下界 $d$（即 $\forall c\in S,\ d\le c$）
都满足 $d\le\bigwedge S$。

证：$d$ 的外延含于每个外延，故含于其交集。 -/
theorem le_sInfConcept (S : Set (ConceptLattice K)) {d : ConceptLattice K}
    (hd : ∀ c ∈ S, d ≤ c) : d ≤ K.sInfConcept S := by
  rw [concept_le_iff_extent_subset, sInfConcept_extent]
  exact subset_iInter₂ fun c hc => (concept_le_iff_extent_subset K d c).mp (hd c hc)

/-- **$\bigwedge S$ 的泛性质**（规格 $\mathrm{IsGLB}$）。

「$\bigwedge S$ 是 $S$ 的最大下界」——由 `sInfConcept_le`（下界）
与 `le_sInfConcept`（最大）合成。 -/
theorem isGLB_sInfConcept (S : Set (ConceptLattice K)) :
    IsGLB S (K.sInfConcept S) :=
  ⟨fun _ hc => K.sInfConcept_le S hc, fun _ hd => K.le_sInfConcept S hd⟩

/-! ===========================================================================
    §2  任意并：外延之并的闭包
    =========================================================================== -/

/-- **概念族的任意并（显式构造）**——规格 $\bigvee S$。

定义即**「外延之并的闭包」**：
$$\bigvee S=\Bigl(\bigcup_{c\in S}A_c\Bigr)''=\mathrm{ofObjects}\Bigl(\bigcup_{c\in S}A_c\Bigr).$$

**注意这里必须取闭包**：外延之并**一般不是**外延
（闭集系对并**不**封闭），故须再取一次 $(\cdot)''$ 使其稳定。
这正是「概念格完备 + 闭包算子」的标准构造。 -/
def sSupConcept (S : Set (ConceptLattice K)) : ConceptLattice K :=
  Concept.ofObjects K.Irel (⋃ c ∈ S, c.extent)

/-- **$\bigvee S$ 的内涵**：内涵之交（`[已知]`：Mathlib 的 `Concept.intent_sSup` 同型）。

证：$\mathrm{ofObjects}(s)$ 的内涵 $=$ 外延之并的上极化
$=\bigcap_{c\in S}(\text{$c$ 的外延的上极化})=\bigcap_{c\in S}B_c$。

**本引理给出 $\bigvee S$ 的「可计算」内涵**，使完备性的证明体不依赖黑箱。 -/
theorem sSupConcept_intent (S : Set (ConceptLattice K)) :
    (K.sSupConcept S).intent = ⋂ c ∈ S, c.intent := by
  rw [sSupConcept]
  simp only [Concept.ofObjects]
  rw [Concept.ofIsIntent]
  simp only
  rw [upperPolar_iUnion₂]
  exact iInter₂_congr fun c _ => c.upperPolar_extent

/-- **$\bigvee S$ 的外延**：$\bigvee S$ 的外延 $=$ 内涵之交的下极化。

它**一般严格大于**外延之并——差额正是闭包补上的部分。 -/
theorem sSupConcept_extent (S : Set (ConceptLattice K)) :
    (K.sSupConcept S).extent = lowerPolar K.Irel (⋂ c ∈ S, c.intent) := by
  rw [sSupConcept]
  simp only [Concept.ofObjects]
  rw [Concept.ofIsIntent]
  simp only
  rw [upperPolar_iUnion₂]
  congr 1
  exact iInter₂_congr fun c _ => c.upperPolar_extent

/-- **$\bigvee S$ 是上界**：对每个 $c\in S$，$c\le\bigvee S$。

证：$a\in A_c$ 时，须证 $a\in\bigvee S$，即
$\forall b\in B_{\bigvee S},\ I(a,b)$。而
$B_{\bigvee S}=\bigcap_{c'}B_{c'}$，故 $b\in B_c$；
再由 $c$ 是形式概念（外延与内涵 $\cdot'$ 互逆）得 $I(a,b)$。 -/
theorem le_sSupConcept (S : Set (ConceptLattice K)) {c : ConceptLattice K}
    (hc : c ∈ S) : c ≤ K.sSupConcept S := by
  rw [concept_le_iff_extent_subset, sSupConcept_extent]
  intro a ha
  rw [FormalCtx.mem_polarDown_iff]
  intro b hb
  exact Concept.rel_extent_intent ha (mem_iInter₂.mp hb c hc)

/-- **$\bigvee S$ 是最小上界**：任何上界 $d$（即 $\forall c\in S,\ c\le d$）
都满足 $\bigvee S\le d$。

证：外延之并含于 $A_d$，而 $A_d$ 是外延（闭集），
故其闭包也含于 $A_d$——由 `ofObjects_le_iff`。 -/
theorem sSupConcept_le (S : Set (ConceptLattice K)) {d : ConceptLattice K}
    (hd : ∀ c ∈ S, c ≤ d) : K.sSupConcept S ≤ d := by
  rw [sSupConcept, Concept.ofObjects_le_iff]
  intro a ha
  rcases mem_iUnion₂.mp ha with ⟨c, hc, hac⟩
  exact (concept_le_iff_extent_subset K c d).mp (hd c hc) hac

/-- **$\bigvee S$ 的泛性质**（规格 $\mathrm{IsLUB}$）。

由 `le_sSupConcept`（上界）与 `sSupConcept_le`（最小）合成。 -/
theorem isLUB_sSupConcept (S : Set (ConceptLattice K)) :
    IsLUB S (K.sSupConcept S) :=
  ⟨fun _ hc => K.le_sSupConcept S hc, fun _ hd => K.sSupConcept_le S hd⟩

/-! ===========================================================================
    §3  概念格是完备格——**构造性证明**
    =========================================================================== -/

/-- **T1A.9（完备格部分）的实质证明**：$\mathfrak{B}(\mathbb{K})$ 的完备格结构
**可由 §1、§2 显式构造出来**。

本定义**重新组装**一个 `CompleteLattice (ConceptLattice K)`：
- `sInf := sInfConcept`（外延之交，闭集系对任意交封闭）；
- `sSup := sSupConcept`（外延之并的闭包）；
- `isGLB_sInf` / `isLUB_sSup` 由 §1、§2 的泛性质给出；
- 格运算与界元沿用既有的 `Lattice`/`BoundedOrder` 结构
  （`inferInstance`，它们是 `PartialOrder` + `Min`/`Max`/`⊤`/`⊥`）。

**这不是 `inferInstance`**：证明体**具体给出了**任意交与任意并，
并证了它们的泛性质。这与 `Fate.FCA` 中暴露的
`instance : CompleteLattice (ConceptLattice K)`（Mathlib 提供）**相容**——
二者给出同一个完备格结构（`sSup`/`sInf` 的外延公式一致）。 -/
@[instance_reducible]
def conceptLatticeCompleteLattice : CompleteLattice (ConceptLattice K) where
  __ := (inferInstance : Lattice (ConceptLattice K))
  __ := (inferInstance : BoundedOrder (ConceptLattice K))
  sSup := K.sSupConcept
  sInf := K.sInfConcept
  isLUB_sSup S := K.isLUB_sSupConcept S
  isGLB_sInf S := K.isGLB_sInfConcept S

/-- **T1A.9（完备格部分）**——与既有实例一致性：本文件构造的
`sSup`/`sInf` 与 Mathlib 实例在同一条泛性质刻画下**重合**。

具体地：本文件构造的任意交的外延就是**外延之交集**，
任意并的内涵就是**内涵之交集**——这正是 `Concept.extent_sInf`
与 `Concept.intent_sSup` 所断言的内容（在 `Fate` 命名下的转写）。

标 `[已知]`：所对照的是 Mathlib 的 `Concept` 实例。 -/
theorem conceptLattice_sInf_extent (S : Set (ConceptLattice K)) :
    (K.sInfConcept S).extent = ⋂ c ∈ S, c.extent :=
  rfl

/-- 对应的「内涵」公式：$\bigwedge S$ 的内涵 $=\bigl(\bigcap A_c\bigr)'$。 -/
theorem conceptLattice_sInf_intent (S : Set (ConceptLattice K)) :
    (K.sInfConcept S).intent = upperPolar K.Irel (⋂ c ∈ S, c.extent) := rfl

end FormalCtx

/-! ===========================================================================
    §4  顶层定理：概念格是完备格
    =========================================================================== -/

/-- **T1A.9（完备格部分）——实质证明**。

规格 T1A.9：`FCA 基本定理：概念格是完备格`。

`Fate.Stage1A` 的原陈述只断言**实例存在**（`Nonempty (CompleteLattice _)`）。
本定理给出**实质版本**：$\mathfrak{B}(\mathbb{K})$ 的**任意交与任意并**
都由 §1、§2 的**显式构造**给出，并满足泛性质——
即概念格**确实是**完备格，而不只是「有某个完备格实例」。

**前件**：$\mathbb{K}$ 是形式背景（`FormalCtx`，具名类型，非匿名前提）。

**标 `[已知]`**：所依赖的 Mathlib 事实（闭集对任意交封闭、
`ofObjects` 的伴随刻画等）是**外部既有结果，本框架内未证**；
本文件证的是**由这些事实组装出完备性**这一步。 -/
theorem T1A9_conceptLattice_complete_substantive (K : FormalCtx.{u, v}) :
    (∀ S : Set (ConceptLattice K), IsGLB S (K.sInfConcept S)) ∧
    (∀ S : Set (ConceptLattice K), IsLUB S (K.sSupConcept S)) :=
  ⟨fun S => K.isGLB_sInfConcept S, fun S => K.isLUB_sSupConcept S⟩

/-- **T1A.9（完备格部分）的可判定落点**：任取 $S$，
$\bigwedge S$ 与 $\bigvee S$ **都是形式概念**（类型正确），
且 $\bigwedge S\le\bigvee S$——完备性蕴含的一个非平凡推论。

**为什么这不是废话**：$\bigwedge S\le\bigvee S$ 需要
「下界 $\le$ 上界」这一格论事实；在**非空**族上它由
$\bigwedge S\le c\le\bigvee S$（任取 $c\in S$）得到，
在**空**族上它退化为 $\top\le\bot$ 的**反例**，
故本定理**只对非空族**陈述——这是诚实的边界标注。 -/
theorem sInfConcept_le_sSupConcept (K : FormalCtx.{u, v})
    (S : Set (ConceptLattice K)) (hne : S.Nonempty) :
    K.sInfConcept S ≤ K.sSupConcept S := by
  obtain ⟨c, hc⟩ := hne
  exact le_trans (K.sInfConcept_le S hc) (K.le_sSupConcept S hc)

end

end FateV2.Rules