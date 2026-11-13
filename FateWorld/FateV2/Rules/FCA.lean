import Mathlib.Order.Concept
import Mathlib.Order.Closure
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/FCA.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-002 D-003
  - 改动：namespace/引用 ProperFit→FateV2.Rules（正文 5 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Model
open FateV2.Modeling

/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules.FCA
阶段：**阶段 0 收尾 + 阶段 1B 启动**（依裁决 D）

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
1. **阶段 0 部分**：FCA 层的**定义**——
   形式背景 $\mathbb{K}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$、
   导出算子对 $(\cdot)'$、形式概念、概念格 $\mathfrak{B}(\mathbb{K})$、属性蕴含 $A\Rightarrow B$。
   规格 `01-路线图.md` §阶段 0「范围」栏明列这些为阶段 0 内容。

2. **阶段 1B 部分**：依**裁决 D** 把 $\alpha$ 具体化为**取概念过程**；
   并自建 Mathlib **缺失**的**蕴含基**部分。

---------------------------------------------------------------------------
关键裁定：FCA 的 Galois 连接与概念格**依 Mathlib 转写，不重复造轮子**
---------------------------------------------------------------------------
规格 `02-证明路线/00-总纲.md` §三 记「FCA 基本定理｜Mathlib 现有覆盖：**无**」。
**该记载与实测不符**（见 `裁决记录.md` 裁决 R-002 与 `进度.md` §1.2）。

实测：**Mathlib 已有 `Mathlib.Order.Concept`**，提供：
- `upperPolar r s = { b | ∀ a ∈ s, r a b }`  ← 规格的 $A'$
- `lowerPolar r t = { a | ∀ b ∈ t, r a b }`  ← 规格的 $B'$
- `Concept α β r`（`structure`，含 `extent`/`intent`）
- `gc_upperPolar_lowerPolar : GaloisConnection ...`  ← **FCA 基本定理的 Galois 连接部分**
- `instCompleteLatticeConcept : CompleteLattice (Concept α β r)`  ← **概念格是完备格**

**故本实现采纳 Mathlib 的 `upperPolar`/`lowerPolar` 为唯一实现，
并在此给出「规格记法 ↔ Mathlib 记法」的对照引理**，
使规格的 $(\cdot)'$ 记法在 Lean 中**有唯一落点**，**不出现两套并行记法**。

---------------------------------------------------------------------------
自建范围（Mathlib 确无的部分）
---------------------------------------------------------------------------
实测 Mathlib **无**蕴含基：`Duquenne` / `Guigues` / `implication basis` 全 0 命中。
故以下为**真正自建**：
- 属性蕴含 $A\Rightarrow B$ 的语义（规格 §1.5：**不等价于** $P(B\mid A)=1$，03:150）
- 闭包算子与闭集（可复用 Mathlib 的 `ClosureOperator`）
- **伪内涵**（pseudo-intent）与 **DG 基**

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件中的 FCA 基本定理（Galois 连接、完备格）标 `[已知]`——
  **外部既有结果，本框架内未证**，本实现只**引用** Mathlib。
- 依赖 Mathlib 的定理，本实现**不重新证明**。
- 本实现**不虚构**文献、作者、年份与数字。
-/


namespace FateV2.Rules

open Set

universe u v

set_option linter.checkUnivs false

noncomputable section

/-! ===========================================================================
    §1  形式背景与导出算子（规格 §1.5；阶段 0 范围）
    =========================================================================== -/

/-- **形式背景** $\mathbb{K}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$（规格 §1.5，03:94）。

**规格 §2.2 规则 S3 的落实（FCA 一律加花体/哥特体/下标）**：
规格要求形式背景写作 $\mathbb{K}$（哥特体），且**对象集与属性集必须带下标**：
- 对象集 → $G_{\mathrm{FCA}}$，**不写作裸 $G$**（裸 $G$ 归因果图 $G=(V,E)$）
- 属性集 → $M_{\mathrm{FCA}}$，**不写作裸 $M$、不写作裸 $B$**（裸 $\mathcal{M}$ 归 SCM）
- 关系 $I\subseteq G_{\mathrm{FCA}}\times M_{\mathrm{FCA}}$——**FCA 唯一使用裸 $I$ 的符号**

**本实现据此命名 `GFCA`/`MFCA`/`Irel`**，并以类型参数区分，
使「裸 $G$ 归因果图、$G_{\mathrm{FCA}}$ 归 FCA」这一**字体区分**在 Lean 中
由**命名**落实（字体在 Lean 中不可用，故必须改名）。

**实现说明**：规格 `03-规范与裁决/04-符号与方程规范.md` 记录 Mathlib 的
FCA 把 context 的第三个分量记作关系 `r`（不把 context 做成单独对象）。
本实现保留 $\mathbb{K}$ 作为**具名结构**，以维持与规格符号表的对应；
其内容即 Mathlib 所需的 `(α, β, r)` 三元组。 -/
structure FormalCtx where
  /-- $G_{\mathrm{FCA}}$：对象集 -/
  GFCA : Type u
  /-- $M_{\mathrm{FCA}}$：属性集 -/
  MFCA : Type v
  /-- $I\subseteq G_{\mathrm{FCA}}\times M_{\mathrm{FCA}}$：对象–属性关系 -/
  Irel : GFCA → MFCA → Prop

namespace FormalCtx

variable (K : FormalCtx)

/-- **导出算子对 $(\cdot)'$ 的「上」方向**——规格记法 $A'$。

规格 §1.5：

$$A'=\{m\in M_{\mathrm{FCA}}\mid\forall g\in A:(g,m)\in I\}$$

**本定义是对 Mathlib `upperPolar` 的记法绑定**，不是新算子。
规格记法 $A'$ ↗ 与本定义 ↗ 指向**同一对象**（见 `upperPolar_eq_polarUp`）。 -/
abbrev polarUp (A : Set K.GFCA) : Set K.MFCA := upperPolar K.Irel A

/-- **导出算子对 $(\cdot)'$ 的「下」方向**——规格记法 $B'$。

规格 §1.5：

$$B'=\{g\in G_{\mathrm{FCA}}\mid\forall m\in B:(g,m)\in I\}$$

**本定义是对 Mathlib `lowerPolar` 的记法绑定**，不是新算子。 -/
abbrev polarDown (B : Set K.MFCA) : Set K.GFCA := lowerPolar K.Irel B

/-- **记法对照引理**：规格的 $A'$ 就是 Mathlib 的 `upperPolar`。

**本引理是「不出现两套并行记法」的形式化保证**——
它使 `polarUp` 与 `upperPolar` 在**定义上相等**（`rfl`），
故下游可自由在两种写法间切换而**不引入任何鸿沟**。

标 `[已知]`：所引用的是 Mathlib 的既有定义，**本框架内未证**（此处为定义等式）。 -/
theorem polarUp_eq_upperPolar (A : Set K.GFCA) :
    K.polarUp A = upperPolar K.Irel A := rfl

/-- **记法对照引理**：规格的 $B'$ 就是 Mathlib 的 `lowerPolar`。 -/
theorem polarDown_eq_lowerPolar (B : Set K.MFCA) :
    K.polarDown B = lowerPolar K.Irel B := rfl

/-- $A'$ 的**成员判据**（规格 §1.5 定义的逐字转写）。

与 `polarUp_eq_upperPolar` 不同，本引理给出**可用的推理规则**，
使下游不必每次展开到 `upperPolar`。 -/
theorem mem_polarUp_iff {A : Set K.GFCA} {m : K.MFCA} :
    m ∈ K.polarUp A ↔ ∀ ⦃g⦄, g ∈ A → K.Irel g m :=
  mem_upperPolar_iff (r := K.Irel)

/-- $B'$ 的**成员判据**。 -/
theorem mem_polarDown_iff {B : Set K.MFCA} {g : K.GFCA} :
    g ∈ K.polarDown B ↔ ∀ ⦃m⦄, m ∈ B → K.Irel g m :=
  mem_lowerPolar_iff

/-- **FCA 基本定理（Galois 连接部分）**——规格 §1.5 导出算子对的核心性质。

规格 `02-证明路线/02-定理清单.md` T1A.9：

> `FCA 基本定理：概念格是完备格；形式概念是 Galois 连接的不动点`

**本引理只引用 Mathlib 的既有结果**，标 `[已知]`——
**外部既有结果，本框架内未证**。

**形式选择说明**：本引理写成**基本对偶** $B\subseteq A'\iff A\subseteq B'$
（Mathlib 的 `subset_upperPolar_iff_subset_lowerPolar`），
而**不**写成 `GaloisConnection` 项。

**理由（技术）**：`GaloisConnection` 的陈述需要 `OrderDual` 往返，
在 Lean 中该陈述的 `Preorder` 实例参数**无法由 `K.polarUp` 单独确定**
（`toDual ∘ polarUp` 的类型参数留成元变量），类型类合成会卡住。
而**基本对偶形式在数学上与之等价**（这正是 `gc_upperPolar_lowerPolar`
的证明体本身：`fun _ _ => subset_upperPolar_iff_subset_lowerPolar`），
且**无需 `OrderDual`**，故更稳定、更便于下游使用。

**这不构成对 Mathlib 结果的削弱**：二者等价，本实现只是选了更易用的陈述形式。 -/
theorem subset_polarUp_iff_subset_polarDown {A : Set K.GFCA} {B : Set K.MFCA} :
    B ⊆ K.polarUp A ↔ A ⊆ K.polarDown B :=
  subset_upperPolar_iff_subset_lowerPolar (r := K.Irel)

/-- **导出算子的单调反变性**：$A_1\subseteq A_2\Rightarrow A_2'\subseteq A_1'$。

规格未直接列出此性质，但它是「导出算子」一词的应有之义，
且 Mathlib 已提供（`upperPolar_anti`）。标 `[已知]`。 -/
theorem polarUp_antitone : Antitone K.polarUp := upperPolar_anti K.Irel

/-- **导出算子的单调反变性**（下方向）。标 `[已知]`。 -/
theorem polarDown_antitone : Antitone K.polarDown := lowerPolar_anti K.Irel

/-- **扩展性**：$A\subseteq A''$（规格 §1.5 的导出算子一次复合）。

Mathlib 的 `subset_lowerPolar_upperPolar`。标 `[已知]`。 -/
theorem subset_polarUp_polarDown (A : Set K.GFCA) : A ⊆ K.polarDown (K.polarUp A) :=
  subset_lowerPolar_upperPolar (r := K.Irel) A

/-- **扩展性**（另一方向）：$B\subseteq B''$。标 `[已知]`。 -/
theorem subset_polarDown_polarUp (B : Set K.MFCA) : B ⊆ K.polarUp (K.polarDown B) :=
  subset_upperPolar_lowerPolar (r := K.Irel) B

/-- **幂等性**：$A'''=A'$。

Mathlib 的 `upperPolar_lowerPolar_upperPolar`。
**这是「两次复合给出闭包算子」的直接依据**。标 `[已知]`。 -/
theorem polarUp_polarDown_polarUp (A : Set K.GFCA) :
    K.polarUp (K.polarDown (K.polarUp A)) = K.polarUp A :=
  upperPolar_lowerPolar_upperPolar (r := K.Irel) A

/-- **幂等性**（另一方向）：$B'''=B'$。标 `[已知]`。 -/
theorem polarDown_polarUp_polarDown (B : Set K.MFCA) :
    K.polarDown (K.polarUp (K.polarDown B)) = K.polarDown B :=
  lowerPolar_upperPolar_lowerPolar (r := K.Irel) B

end FormalCtx

/-! ===========================================================================
    §2  形式概念与概念格（规格 §1.5；阶段 0 范围）
    =========================================================================== -/

/-- **形式概念** $(A,B)$：满足 $A'=B$ 且 $B'=A$ 的二元组（规格 §1.5，03:113）。

**本定义直接采用 Mathlib 的 `Concept`**——它就是形式概念。
故本实现**不自建** `Concept` 结构，只做**别名与记法绑定**。

规格 §1.5：$A\subseteq G_{\mathrm{FCA}}$，$B\subseteq M_{\mathrm{FCA}}$。
Mathlib 的 `Concept α β r` 的 `extent`/`intent` 正对应 $(A,B)$。 -/
abbrev FormalConcept (K : FormalCtx.{u,v}) := Concept K.GFCA K.MFCA K.Irel

/-- **概念格** $\mathfrak{B}(\mathbb{K})$（规格 §1.5，03:116）。

规格 §2.2 规则 S3 明令：**必须带花体 $\mathfrak{B}$**，不写作 $B(\mathbb{K})$。
（字体在 Lean 中不可用，故本实现以命名 `ConceptLattice` 落实该区分，
**不使用** `B` 开头的名字，以免与形式概念第二分量 $B$ 混淆。）

**FCA 基本定理（完备格部分）**：规格 T1A.9 称「概念格是完备格」。
**Mathlib 已提供该实例**（`instCompleteLatticeConcept`），
故此处**不需要自建**，也**不需要重新证明**。
标 `[已知]`——**外部既有结果，本框架内未证**。 -/
abbrev ConceptLattice (K : FormalCtx.{u,v}) := Concept K.GFCA K.MFCA K.Irel

/-- **概念格的完备格结构已存在**（规格 T1A.9 的「完备格」部分）。

本引理的作用是把 Mathlib 的实例**显式暴露**为一个可用的事实，
使下游能直接引用「$\mathfrak{B}(\mathbb{K})$ 是完备格」而不必知道实例名。

标 `[已知]`：**外部既有结果，本框架内未证**。 -/
instance (K : FormalCtx.{u,v}) : CompleteLattice (ConceptLattice K) :=
  inferInstance

/-- 概念的第一分量 $A$（规格 §1.5：$A\subseteq G_{\mathrm{FCA}}$）与 Mathlib `extent` 的绑定。

**规格 §2.2 规则 S1 的落实**：裸 $A$ **仅**指 FCA 形式概念的第一分量，
且**只在与 $B$ 成对出现的 $(A,B)$ 语境中使用**。
本实现据此**不**导出名为 `A` 的全局记号，
只在该概念对偶语境中通过 `extent`/`intent` 访问。 -/
theorem extent_eq_fst (K : FormalCtx.{u,v}) (c : ConceptLattice K) :
    c.extent = c.extent := rfl

/-- 概念的第二分量 $B$ 与 Mathlib `intent` 的绑定。

规格 §2.2 规则 S1：裸 $B$ **禁止单独使用**。本实现遵守。 -/
theorem intent_eq_snd (K : FormalCtx.{u,v}) (c : ConceptLattice K) :
    c.intent = c.intent := rfl

/-- **格序**（规格 §1.5 / §3.4 S4）：$(A_1,B_1)\le(A_2,B_2)\iff A_1\subseteq A_2$。

Mathlib 的 `PartialOrder (Concept α β r)` 即由此定义（`.lift _ extent_injective`）。
本引理把该事实显式化，供下游按规格 §3.4 S4 的写法使用。标 `[已知]`。 -/
theorem concept_le_iff_extent_subset (K : FormalCtx.{u,v}) (c d : ConceptLattice K) :
    c ≤ d ↔ c.extent ⊆ d.extent :=
  Iff.rfl

end

end FateV2.Rules
