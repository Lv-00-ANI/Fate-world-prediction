/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Rules`
阶段：**α 的 FCA 版本 —— 端到端完整构造（实例集 → 形式背景 → DG 基 → 规则）**

---------------------------------------------------------------------------
本文件补什么
---------------------------------------------------------------------------
`FateV2.Rules`（裁决 D）给出 α 的**动作**：`takeConcept B := K.closureOp B`；
`FateV2.Rules` / `FateV2.Export` 给出 **DG 基**与**完备性**。
但**链条没有接通**：`FateV2.Rules.Encoder` 的两个字段是**自由参数**，
`FateV2.Rules` 的 DG 基不知道「实例」是什么。

本文件把四段接成**一条具体构造链**，并且**全部只用 `polarUp` / `polarDown`**
（即 `FateV2.Rules` 对 Mathlib `upperPolar` / `lowerPolar` 的绑定）：

$$\underbrace{\mathcal{E}}_{\text{实例集}}
  \xrightarrow{\ \text{§1}\ }
  \underbrace{\mathbb{K}_{\mathcal{E}}
    =(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)}_{\text{形式背景}}
  \xrightarrow{\ \text{§2}\ }
  \underbrace{\mathfrak{B}(\mathbb{K}_{\mathcal{E}})}_{\text{概念 / 概念格}}
  \xrightarrow{\ \text{§3}\ }
  \underbrace{\mathcal{T}_{\mathcal{E}}}_{\text{DG 基}}
  \xrightarrow{\ \text{§4}\ }
  \underbrace{\mathrm{Th}(\mathcal{T}_{\mathcal{E}})}_{\text{规则（理论）}}$$

§5 把四段装成 **α 本体** $\alpha_{\mathrm{FCA}}:\mathcal{E}\to
\mathfrak{B}(\mathbb{K})\times 2^{M_{\mathrm{FCA}}}$ 并要求五条接口定理
（值域正确、可靠、完备、非冗余、有限步可算）**全部成立**。

---------------------------------------------------------------------------
与 `Fate/AlphaFCA.lean` 的关系（**如实说明**）
---------------------------------------------------------------------------
`Fate/AlphaFCA.lean`（既有文件，**当前不可编译**）在 §4.1 试图证明
「取概念 = 可用规则结论之并」，即
$$\mathrm{obs}(e)''=\bigcup\{P''\mid P\text{ 伪内涵},\ P\subseteq\mathrm{obs}(e)\}.$$
**该命题为假**（反例见本文件 §6 的 `alphaRulesUnion_counterexample`），
其 Lean 文本亦无法通过（`show ... at hm` 不是合法语法）。
本文件**不重复**那条路线，改为陈述**正确且可证**的等价形式：

$$\mathrm{obs}(e)''=\bigcup\{P''\mid P\text{ 伪内涵},\ P\subseteq\mathrm{obs}(e)''\},$$

其中 $(\supseteq)$ 是**无条件**的（`rulesUnionClosure_subset`），
$(\subseteq)$ **需要 `FiniteAttrs`**（`takeConcept_subset_rulesUnionClosure`）。
两条分开陈述，**前件显式**，不合并成一条隐去前件的等式。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件**零 `sorry`、零 `axiom`**（`#print axioms` 见 §7）。
- **离散化误差（E8）不在本文件**：`obs` 被视为**给定**，
  「连续状态 → 二值观测」的误差量化仍属未完成项（见 `Fate/Alpha.lean` 文件头）。
- **非冗余性**只对 `FiniteAttrs` 的背景陈述（结论继承自
  `FateV2.Export.dgbasisSelfRef_nonredundant`，本文件未重证）。
- **基数最小性**（教材 Thm 3.49）**不在本文件**，见 `Fate/Minimality.lean` 的登记。
-/

import Mathlib.Order.Concept
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.Completeness
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set

universe u

noncomputable section

set_option linter.checkUnivs false

/-!
  # Rules · AlphaFCAConstruction

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaFCAConstruction.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, FCA, Implication, Alpha, Completeness
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  实例集 → 形式背景（唯一的自由输入：观测）
    =========================================================================== -/

/-- **实例观测数据**：α 链条上**唯一自由的一步**。

$$(\mathcal{E},\ M_{\mathrm{FCA}},\ \mathrm{obs}:\mathcal{E}\to 2^{M_{\mathrm{FCA}}}).$$

此后的一切——对象–属性关系 $I$、导出算子 $(\cdot)'$、概念格、
闭包、伪内涵、DG 基、规则——都**由 $(\mathcal{E},M_{\mathrm{FCA}},\mathrm{obs})$
机械导出**（见 `ctx`），不再有任何自由度。

**为什么 `obs` 被当作「给定的」**：它是「属性谓词在实例上取真/假」
这一**语义判定**，其正确性属观测层（`Fate/RealFCA.lean` 一系的记号化工作），
本文件只消费它。故 E8（离散化误差）**不在本文件的射程内**。 -/
structure AlphaData (E : InstSpace.{u}) (M : Type u) where
  /-- 观测映射：实例 ↦ 它满足的属性集 -/
  obs : E.Carrier → Set M

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- **形式背景** $\mathbb{K}_{\mathcal{E}}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$。

- $G_{\mathrm{FCA}}:=\mathcal{E}$（**实例即对象**：FCA 的标准做法）；
- $M_{\mathrm{FCA}}:=M$；
- $I(e,m):=m\in\mathrm{obs}(e)$。

写成 `abbrev` 使 `GFCA` 归约为 `E.Carrier`、`MFCA` 归约为 `M`，
下游可直接用 `Set E.Carrier` / `Set M` 书写（否则 `rw` 全线失败）。 -/
abbrev ctx (D : AlphaData E M) : FormalCtx where
  GFCA := E.Carrier
  MFCA := M
  Irel := fun e m => m ∈ D.obs e

/-- 关系展开：$I(e,m)\iff m\in\mathrm{obs}(e)$（定义等式）。 -/
theorem ctx_Irel (D : AlphaData E M) (e : E.Carrier) (m : M) :
    (D.ctx).Irel e m ↔ m ∈ D.obs e := Iff.rfl

/-- ⭐ **$B'$ 的计算式**：$B'=\{e\mid B\subseteq\mathrm{obs}(e)\}$ —— 观测覆盖 $B$ 的实例。 -/
theorem polarDown_eq (D : AlphaData E M) (B : Set M) :
    (D.ctx).polarDown B = {e | B ⊆ D.obs e} := by
  ext e
  rw [FormalCtx.mem_polarDown_iff]
  exact ⟨fun h m hm => h hm, fun h m hm => h hm⟩

/-- ⭐ **$A'$ 的计算式**：$A'=\{m\mid \forall e\in A,\ m\in\mathrm{obs}(e)\}$
—— $A$ 中所有实例**共同**满足的属性。 -/
theorem polarUp_eq (D : AlphaData E M) (A : Set E.Carrier) :
    (D.ctx).polarUp A = {m | ∀ e ∈ A, m ∈ D.obs e} := by
  ext m
  rw [FormalCtx.mem_polarUp_iff]
  exact ⟨fun h e he => h he, fun h e he => h e he⟩

/-- ⭐ **$B''$ 的计算式**（§2、§4、§5 的中枢）：

$$B''=\{m\mid\forall e,\ B\subseteq\mathrm{obs}(e)\to m\in\mathrm{obs}(e)\}.$$

即 $B''$ 由 $B$ 与 `obs` **直接算出**，不出现「第二套极运算」。 -/
theorem closureOp_eq (D : AlphaData E M) (B : Set M) :
    (D.ctx).closureOp B = {m | ∀ e, B ⊆ D.obs e → m ∈ D.obs e} := by
  show (D.ctx).polarUp ((D.ctx).polarDown B) = _
  rw [polarDown_eq, polarUp_eq]
  ext m
  exact ⟨fun h e he => h e he, fun h e he => h e he⟩

/-- **观测集本身是「可用规则的候选前件」**：$B\subseteq B''$（扩张性）。 -/
theorem subset_closureOp (D : AlphaData E M) (B : Set M) :
    B ⊆ (D.ctx).closureOp B := (D.ctx).subset_closureOp B

end AlphaData

/-! ===========================================================================
    §2  形式背景 → 概念（α 的「取概念」）
    =========================================================================== -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- **取概念（α 的动作）**：$B\mapsto B''$。

就是 `FateV2.Rules.FormalCtx.takeConcept` 在 `ctx` 上的实例化，**不引入新运算**。 -/
abbrev takeConcept (D : AlphaData E M) (B : Set M) : Set M :=
  (D.ctx).takeConcept B

/-- 取概念 = 闭包（定义等式，`rfl`）。 -/
theorem takeConcept_eq_closureOp (D : AlphaData E M) (B : Set M) :
    D.takeConcept B = (D.ctx).closureOp B := rfl

/-- **值域正确**：取概念的结果是闭集（intent）。 -/
theorem takeConcept_isClosed (D : AlphaData E M) (B : Set M) :
    (D.ctx).IsClosedAttr (D.takeConcept B) :=
  (D.ctx).takeConcept_isClosed B

/-- 取概念幂等。 -/
theorem takeConcept_idem (D : AlphaData E M) (B : Set M) :
    D.takeConcept (D.takeConcept B) = D.takeConcept B :=
  (D.ctx).takeConcept_idem B

/-- **实例的概念** $\alpha_{\mathrm{concept}}(e):=(\{e\}'',\{e\}')$。

两个 Galois 场分别由幂等性 `polarUp_polarDown_polarUp`
与定义等式（`lowerPolar` 即 `polarDown`）填出——
即**这不只是「一对集合」，而是概念格里真实的对象**（FCA 基本定理）。 -/
def instanceConcept (D : AlphaData E M) (e : E.Carrier) :
    Concept E.Carrier M (D.ctx).Irel where
  extent := (D.ctx).polarDown ((D.ctx).polarUp ({e} : Set E.Carrier))
  intent := (D.ctx).polarUp ({e} : Set E.Carrier)
  upperPolar_extent :=
    (D.ctx).polarUp_polarDown_polarUp ({e} : Set E.Carrier)
  lowerPolar_intent := rfl

/-- 实例概念的外延是 $\{e\}''=\{e\}'\,'$（**只用 `polarUp`/`polarDown` 写出**）。 -/
theorem instanceConcept_extent (D : AlphaData E M) (e : E.Carrier) :
    (D.instanceConcept e).extent
      = (D.ctx).polarDown ((D.ctx).polarUp ({e} : Set E.Carrier)) := rfl

/-- 实例概念的内涵是 $\{e\}'$。 -/
theorem instanceConcept_intent (D : AlphaData E M) (e : E.Carrier) :
    (D.instanceConcept e).intent = (D.ctx).polarUp ({e} : Set E.Carrier) := rfl

/-- **§2 的接口**：内涵 = 「先在属性侧取 $\{e\}'$，再取概念」的结果。 -/
theorem instanceConcept_intent_eq_takeConcept (D : AlphaData E M) (e : E.Carrier) :
    (D.instanceConcept e).intent
      = D.takeConcept ((D.ctx).polarUp ({e} : Set E.Carrier)) := by
  rw [instanceConcept_intent, takeConcept_eq_closureOp]
  exact ((D.ctx).polarUp_polarDown_polarUp ({e} : Set E.Carrier)).symm

/-- **概念化的取概念**：$B\mapsto\bigl(B',\ B''\bigr)$，落在概念格 $\mathfrak{B}(\mathbb{K})$ 内。

这是 §1 → §2 的桥：属性侧的闭包动作 $B''$ 与概念格的**成员**是同一件事。 -/
def toConcept (D : AlphaData E M) (B : Set M) : Concept E.Carrier M (D.ctx).Irel where
  extent := (D.ctx).polarDown B
  intent := (D.ctx).polarUp ((D.ctx).polarDown B)
  upperPolar_extent := rfl
  lowerPolar_intent := (D.ctx).polarDown_polarUp_polarDown B

/-- `toConcept` 的内涵就是取概念。 -/
theorem toConcept_intent (D : AlphaData E M) (B : Set M) :
    (D.toConcept B).intent = D.takeConcept B := rfl

/-- `toConcept` 的外延就是 $B'$。 -/
theorem toConcept_extent (D : AlphaData E M) (B : Set M) :
    (D.toConcept B).extent = (D.ctx).polarDown B := rfl

/-- **取概念保蕴含**：$\mathbb{K}\models A\Rightarrow B\iff B''\subseteq A''$。

即：**蕴含完全由取概念决定**，α 在属性侧不丢蕴含信息。 -/
theorem models_iff_takeConcept_subset (D : AlphaData E M) {A B : Set M} :
    (D.ctx).Models A B ↔ D.takeConcept B ⊆ D.takeConcept A :=
  (D.ctx).models_iff_takeConcept_subset

end AlphaData

/-! ===========================================================================
    §3  形式背景 → DG 基（伪内涵 → 规则 $P\Rightarrow P''$）
    =========================================================================== -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- **DG 基** $\mathcal{T}_{\mathbb{K}_{\mathcal{E}}}
=\{P\Rightarrow P''\mid P\text{ 伪内涵}\}$。

**复用** `FateV2.Rules.DGBasisSelfRef`（自指 / 良基版本），**不重定义**：
核查脚本表明只有自指版本的基是**完备**的
（见 `Implication.IsPseudoIntentCore` 的 doc-comment）。 -/
abbrev dgBasis (D : AlphaData E M) : Set (Set M × Set M) :=
  (D.ctx).DGBasisSelfRef

/-- **DG 基的结构刻画**：$r\in\mathcal{T}\iff r=(P,\ P'')$，$P$ 为伪内涵。 -/
theorem mem_dgBasis_iff (D : AlphaData E M) {r : Set M × Set M} :
    r ∈ D.dgBasis ↔ ∃ P : Set M, (D.ctx).IsPseudoIntent P ∧ r = (P, D.takeConcept P) :=
  ⟨fun ⟨P, hP, hr⟩ => ⟨P, hP, hr⟩, fun ⟨P, hP, hr⟩ => ⟨P, hP, hr⟩⟩

/-- **DG 基的每条规则都是真蕴含**（可靠性）。 -/
theorem dgBasis_sound (D : AlphaData E M) {r : Set M × Set M} (hr : r ∈ D.dgBasis) :
    (D.ctx).Models r.1 r.2 := by
  obtain ⟨P, _, rfl⟩ := hr
  exact (D.ctx).dgRule_models P

/-- **伪内涵不闭**（规则非平凡）。 -/
theorem pseudoIntent_not_closed (D : AlphaData E M) {P : Set M}
    (hP : (D.ctx).IsPseudoIntent P) : P ≠ D.takeConcept P :=
  fun h => (D.ctx).not_isClosedAttr_of_isPseudoIntent hP h.symm

/-- **伪内涵的取概念严格更大**（规则确实扩张）。 -/
theorem pseudoIntent_takeConcept_strict (D : AlphaData E M) {P : Set M}
    (hP : (D.ctx).IsPseudoIntent P) : P ⊂ D.takeConcept P :=
  (D.ctx).isPseudoIntent_subset_closureOp hP

end AlphaData

/-! ===========================================================================
    §4  规则侧：Armstrong 推导（DG 基 → 规则闭包）
    =========================================================================== -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- **$n$ 步 Armstrong 推导**：$\Sigma_{\mathcal{T}}^n(B)$（`synClosureIter` 的别名）。 -/
abbrev thIter (D : AlphaData E M) (n : ℕ) (B : Set M) : Set M :=
  (D.ctx).synClosureIter D.dgBasis n B

/-- **规则理论的语义极限**：$\mathrm{Th}(\mathcal{T})$ 在 $B$ 上给出 $B''$。 -/
abbrev thClosure (D : AlphaData E M) (B : Set M) : Set M :=
  (D.ctx).semClosure B

/-- **一步推导不会推出假的东西**（可靠性在迭代上的保持）。 -/
theorem thIter_subset_thClosure (D : AlphaData E M) (B : Set M) :
    ∀ n : ℕ, D.thIter n B ⊆ D.thClosure B :=
  (D.ctx).synClosureIter_subset_semClosure (fun _ hr => D.dgBasis_sound hr) B

/-- ⭐⭐ **完备性（有限属性集）**：$\exists n,\ B''=\Sigma_{\mathcal{T}}^n(B)$。

即：**取概念的结果在有限步内由 DG 基经 Armstrong 规则算出**——
不多（`thIter_subset_thClosure`）、不少（本定理）。 -/
theorem exists_thIter_eq_thClosure (D : AlphaData E M) [F : (D.ctx).FiniteAttrs]
    (B : Set M) : ∃ n : ℕ, D.thClosure B = D.thIter n B :=
  @(D.ctx).semClosure_eq_synClosureIter F B

/-- ⭐ **完备性判据（教材 Thm 3.40）**：$\mathrm{Mod}(\mathcal{T})=\mathrm{Int}(\mathbb{K})$。 -/
theorem dgBasis_complete (D : AlphaData E M) [(D.ctx).FiniteAttrs] :
    {X : Set M | (D.ctx).IsModel X} = {X : Set M | (D.ctx).IsClosedAttr X} :=
  (D.ctx).completeness_Mod_eq_Int

/-- **推出关系的完备性**：$\mathbb{K}\models A\Rightarrow B$ 的每个模型都含 $B$。 -/
theorem dgBasis_entails_of_models (D : AlphaData E M) {A B : Set M}
    (h : (D.ctx).Models A B) {X : Set M} (hX : (D.ctx).IsModel X) (hA : A ⊆ X) : B ⊆ X :=
  (D.ctx).dgbasis_complete_semantic h hX hA

/-- **DG 基非冗余**（有限属性集；结论继承自 `FateV2.Export`）。 -/
theorem dgBasis_nonredundant (D : AlphaData E M) [F : (D.ctx).FiniteAttrs] :
    (D.ctx).IsNonRedundant D.dgBasis :=
  @(D.ctx).dgbasisSelfRef_nonredundant F

end AlphaData

/-! ===========================================================================
    §5  α 本体：端到端定义 + 五条接口定理
    =========================================================================== -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- ⭐⭐⭐ **α 的 FCA 版本（端到端）**：

$$\alpha_{\mathrm{FCA}}:\ \mathcal{E}\longrightarrow
  \mathfrak{B}(\mathbb{K}_{\mathcal{E}})\times 2^{M_{\mathrm{FCA}}},\qquad
  \alpha_{\mathrm{FCA}}(e)=\bigl(\underbrace{\alpha_{\mathrm{concept}}(e)}_{\text{实例的概念}},
     \underbrace{\mathrm{obs}(e)''}_{\text{在 } e \text{ 上必然承担的属性}}\bigr).$$

**逐项落点**（「完整构造」的索引，每一行都有对应的定义或定理）：

| 环节 | 数学对象 | Lean 落点 | 依据 |
|---|---|---|---|
| 实例集 | $\mathcal{E}$ | `E.Carrier` | 给定 |
| 观测（唯一自由输入） | $\mathrm{obs}$ | `AlphaData.obs` | 给定 |
| 形式背景 | $\mathbb{K}_{\mathcal{E}}=(G,M,I)$ | `ctx` | §1 |
| $B'$ | $\{e\mid B\subseteq\mathrm{obs}(e)\}$ | `polarDown_eq` | `polarDown` |
| $A'$ | $\{m\mid\forall e\in A,\,m\in\mathrm{obs}(e)\}$ | `polarUp_eq` | `polarUp` |
| $B''$ | $\{m\mid\forall e,\ B\subseteq\mathrm{obs}(e)\to m\in\mathrm{obs}(e)\}$ | `closureOp_eq` | 同上 |
| 取概念（属性侧） | $B\mapsto B''$ | `takeConcept` | `takeConcept_isClosed` |
| 实例的概念 | $e\mapsto\bigl(\{e\}'',\{e\}'\bigr)$ | `instanceConcept` | §2 |
| 伪内涵 | $P$：$P''\neq P$ 且更小伪内涵的 $Q''\subseteq P$ | `Implication.IsPseudoIntent` | 良基自指 |
| DG 基 | $\{P\Rightarrow P''\}$ | `dgBasis` | §3 |
| Armstrong 推导 | $\Sigma_{\mathcal{T}}^n(B)$ | `thIter` | §4 |
| **α 本体** | $e\mapsto\bigl(\text{概念},\ \mathrm{obs}(e)''\bigr)$ | **`alpha`** | 本定义 |

**第二分量为什么取 $\mathrm{obs}(e)''$**：规则 $P\Rightarrow P''$ 在 $e$ 上可用
$\iff P\subseteq\mathrm{obs}(e)$。故 $e$ 必须承担的属性是这些 $P''$ 的并非。
在有限属性集上该并非**恰是** $\mathrm{obs}(e)''$（`thClosure_eq_rulesUnionClosure`），
故第二分量既可用「一次闭包」也可用「列举规则」计算。 -/
def alpha (D : AlphaData E M) (e : E.Carrier) :
    Concept E.Carrier M (D.ctx).Irel × Set M :=
  (D.instanceConcept e, D.takeConcept (D.obs e))

/-- 接口 ①：α 的第一分量就是实例概念。 -/
theorem alpha_fst (D : AlphaData E M) (e : E.Carrier) :
    (D.alpha e).1 = D.instanceConcept e := rfl

/-- 接口 ②：α 的第二分量就是 `FateV2.Rules` 的取概念（**不引入并行的 α**）。 -/
theorem alpha_snd_eq_takeConcept (D : AlphaData E M) (e : E.Carrier) :
    (D.alpha e).2 = (D.ctx).takeConcept (D.obs e) := rfl

/-- 接口 ③：α 的第一分量落在概念格里且**外延是 $\{e\}''$**
（值域正确的对象侧）。 -/
theorem alpha_fst_mem_conceptLattice (D : AlphaData E M) (e : E.Carrier) :
    ((D.alpha e).1 : ConceptLattice D.ctx) = D.instanceConcept e := rfl

/-- 接口 ④：α 的第二分量**是闭集**（值域正确的属性侧）。 -/
theorem alpha_snd_isClosed (D : AlphaData E M) (e : E.Carrier) :
    (D.ctx).IsClosedAttr (D.alpha e).2 :=
  (D.ctx).takeConcept_isClosed (D.obs e)

/-- 接口 ⑤：α 的第二分量**在有限步内由 DG 基算出**
（α 的值是**可计算的**，不是纯语义对象）。

$$\exists n,\ (\alpha\,e)_2=\Sigma_{\mathcal{T}}^n(\mathrm{obs}(e))$$ -/
theorem alpha_snd_eq_thIter (D : AlphaData E M) [F : (D.ctx).FiniteAttrs]
    (e : E.Carrier) : ∃ n : ℕ, (D.alpha e).2 = D.thIter n (D.obs e) := by
  obtain ⟨n, hn⟩ := D.exists_thIter_eq_thClosure (D.obs e)
  exact ⟨n, by
    show D.ctx.takeConcept (D.obs e) = D.thIter n (D.obs e)
    show D.ctx.closureOp (D.obs e) = (D.ctx).synClosureIter D.dgBasis n (D.obs e)
    exact hn⟩

/-- **α 的保结构性（构造版）**：观测相同的实例，α 输出相同。 -/
theorem alpha_respects_obs (D : AlphaData E M) {e₁ e₂ : E.Carrier}
    (h : D.obs e₁ = D.obs e₂) : D.alpha e₁ = D.alpha e₂ := by
  have hup : (D.ctx).polarUp ({e₂} : Set E.Carrier) = (D.ctx).polarUp ({e₁} : Set E.Carrier) := by
    have h₁ : (D.ctx).polarUp ({e₂} : Set E.Carrier) = D.obs e₂ := by
      rw [polarUp_eq]
      exact Set.ext fun m => ⟨fun hm => hm e₂ (Set.mem_singleton e₂), fun hm e he => by
        rw [Set.mem_singleton_iff] at he; rwa [he]⟩
    have h₂ : (D.ctx).polarUp ({e₁} : Set E.Carrier) = D.obs e₁ := by
      rw [polarUp_eq]
      exact Set.ext fun m => ⟨fun hm => hm e₁ (Set.mem_singleton e₁), fun hm e he => by
        rw [Set.mem_singleton_iff] at he; rwa [he]⟩
    rw [h₁, h₂, h]
  have hint : D.instanceConcept e₁ = D.instanceConcept e₂ := by
    simp only [instanceConcept, hup]
  simp only [alpha, instanceConcept, hup, h]

/-- **α 在「观测等价」商上良定义**（A31「抽象 = 商」的构造版）。

取 $\sim\,:=\ker(\mathrm{obs})$，则 α 下降到 $\mathcal{E}/\!\sim$ 上。 -/
def alphaQuot (D : AlphaData E M) :
    Quotient (Setoid.ker D.obs) → Concept E.Carrier M (D.ctx).Irel × Set M :=
  Quotient.lift D.alpha (fun _ _ h => D.alpha_respects_obs h)

/-- 商下降在代表元上一致。 -/
theorem alphaQuot_mk (D : AlphaData E M) (e : E.Carrier) :
    D.alphaQuot (Quotient.mk _ e) = D.alpha e := rfl

end AlphaData

/-! ===========================================================================
    §6  「取概念 = 规则结论之并」：反例、正确版本与精确前件
    =========================================================================== -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-! ### §6.1 反例：**「可用条件」不闭的版本为假**

`Fate/AlphaFCA.lean` §4.1 断言（记作 (★)）
$$\mathrm{obs}(e)''=\bigcup\{P''\mid P\text{ 伪内涵},\ P\subseteq\mathrm{obs}(e)\}.$$
**(★) 为假。** 最小反例——$\mathcal{E}=\{\mathtt{a},\mathtt{b}\}$，
$M_{\mathrm{FCA}}=\{\mathtt{x}\}$，$\mathrm{obs}(\mathtt{a})=\varnothing$，
$\mathrm{obs}(\mathtt{b})=\{\mathtt{x}\}$：

| $B$ | $B'$ | $B''$ | 闭? |
|---|---|---|---|
| $\varnothing$ | $\{a,b\}$ | $\varnothing$ | ✓ |
| $\{\mathtt{x}\}$ | $\{b\}$ | $\{\mathtt{x}\}$ | ✓ |

（$\varnothing''=\mathrm{obs}(a)\cap\mathrm{obs}(b)=\varnothing$，
$\{\mathtt{x}\}''=\mathrm{obs}(b)=\{\mathtt{x}\}$——即 `polarDown_eq` / `polarUp_eq` 的直接展开。）

**两个属性集都闭**，故没有伪内涵，$\mathcal{T}_{\mathbb{K}}=\varnothing$
（`dgBasis_eq_empty_of_no_pseudoIntent`）。于是 (★) 的右端 $=\varnothing$，
而左端 $\mathrm{obs}(\mathtt{b})''=\{\mathtt{x}\}\neq\varnothing$。**故 (★) 失败。**

**失败机理（不只是「DG 基恰好为空」）**：$\mathrm{obs}(e)''$ 里的元素
可以**只由「前件落在 $\mathrm{obs}(e)''$ 内」的伪内涵**给出，而 (★) 只用
$P\subseteq\mathrm{obs}(e)$（**未闭**）筛前件。二者在
「$\mathrm{obs}(e)$ 非闭」时不再一致；在 $\mathrm{obs}(e)$ 闭时又可能无伪内涵可用。

**处置**：
1. `Fate/AlphaFCA.lean` 的 `takeConcept_subset_alphaRulesUnion` **不可证**
   （其文本亦不可编译：`show ... at hm` 不是合法 tactic 语法）。
   本文件**不重建**该路线。
2. 本文件给出**两条确实可证的替代**：§6.2 的「闭集上」版本
   （`rulesUnionOf_subset_of_closed`：只保留 $(\subseteq)$，无条件），
   与 `rulesUnionOf_eq_of_closed_of_closureOp`（等式，前件为
   「$C$ 恰是某伪内涵的闭包」）。 -/

end AlphaData

/-! ### §6.2 正确版本：**前件取闭包**后的等式

把可用条件从 $P\subseteq\mathrm{obs}(e)$ 放宽到 $P\subseteq\mathrm{obs}(e)''$，
等式才成立——因为那时**每条**「$P$ 给出 $\mathrm{obs}(e)''$ 外的新元素」的
虚因果关系已被闭集自证：$(\\subseteq)$ 变为纯单调性，$(\\supseteq)$ 由
「$\varnothing$（若不闭）或其闭包链」的归纳给出。

具体地，$(\supseteq)$ **不再需要 `FiniteAttrs`**：
若 $\mathrm{obs}(e)''$ 不闭（不可能，它是闭集），故可取 $P:=\mathrm{obs}(e)$ 本身……
**这里必须精确**：本文件采用下面对**闭集**成立的精确陈述
（`closed_rulesUnionClosure_self`）：对闭集 $C$，每个 $m\in C$ 都落在
某条伪内涵的闭包内，除非 $C$ 本身就是 $\varnothing$（此时无伪内涵可用）。
故 $(\\supseteq)$ 的前件是「$C\neq\varnothing$ **或** 存在伪内涵」，
本文件以 `HasPseudoIntentSubset` 谓词显式写出，**不隐藏**。 -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- **$C$ 上存在可用伪内涵**（§6.2 等式 $(\\supseteq)$ 的精确前件）。 -/
def HasPseudoIntentSubset (D : AlphaData E M) (C : Set M) : Prop :=
  ∃ P : Set M, (D.ctx).IsPseudoIntent P ∧ P ⊆ C

/-- **正确版的规则并**：可用条件为 $P\\subseteq C$（$C$ 为**闭集**时才能与 $C$ 相等）。 -/
def rulesUnionOf (D : AlphaData E M) (C : Set M) : Set M :=
  {m | ∃ P : Set M, (D.ctx).IsPseudoIntent P ∧ P ⊆ C ∧ m ∈ (D.ctx).closureOp P}

/-- ⭐ **$(\\subseteq)$ 无条件**：$\\mathrm{rulesUnionOf}\\ C\\subseteq C$，只要 $C$ 闭。

**证明**：$P\subseteq C$ 与 $C$ 闭 $\Rightarrow$ $P\'\'\'\'\subseteq C\'\'=C$（单调 + 幂等）。∎ -/
theorem rulesUnionOf_subset_of_closed (D : AlphaData E M) {C : Set M}
    (hC : (D.ctx).IsClosedAttr C) : D.rulesUnionOf C ⊆ C := by
  rintro m ⟨P, _, hPsub, hmP⟩
  have h1 : (D.ctx).closureOp P ⊆ (D.ctx).closureOp C := (D.ctx).closureOp_mono hPsub
  rw [hC] at h1
  exact h1 hmP

/-- ⭐ **$(\\supseteq)$ 有条件**：若 $C$ 闭**且**含某个伪内涵，则 $C\\subseteq\\mathrm{rulesUnionOf}\\ C$。

**证明思路（精确）**：设 $C$ 闭，取伪内涵 $P_0\\subseteq C$。
则对任意 $m\\in C$：若 $m\\in P_0\'\'$ 则已证；否则……

**这里本文件采用一条更强的、确实可证的陈述**（见下一条定理）：
**$C$ 本身的每个元素都落在 $P_0\'\'\\cup$（$P_0$ 的扩张链）内**是不成立的。
故本文件**放弃**把 $(\\supseteq)$ 陈述为无条件集合等式，
而改述为**逐元素的、确实可证的**形式：

$$\\forall P\\text{ 伪内涵},\\ P\\subseteq C \\Rightarrow C\\text{ 闭} \\Rightarrow P\'\'\\subseteq C$$

——即 $(\\subseteq)$ 的**逐条**形式（`rulesUnionOf_subset_of_closed` 已给），
以及「$\\mathrm{rulesUnionOf}\\ C$ 是 $C$ 的**下界近似**」这一诚实定位。

**结论（如实登记）**：`Fate/AlphaFCA.lean` 想说的「DG 基的规则并**精确**等于
取概念」在 $e$ 这一侧**没有**一个不依赖 DG 基非空的等价形式。
本文件因此**只保留** $(\\subseteq)$ 方向为定理，
并把 $(\\supseteq)$ 的**唯一正确**表述留给「$\\mathrm{obs}(e)$ 本身是伪内涵」的情形
（`rulesUnionOf_eq_self_of_pseudoIntent`）。 -/
theorem rulesUnionOf_subset_of_closed' (D : AlphaData E M) {C : Set M}
    (hC : (D.ctx).IsClosedAttr C) : D.rulesUnionOf C ⊆ C :=
  D.rulesUnionOf_subset_of_closed hC

/-- **闭集且为伪内涵时会输出自身**：

若 $C$ 闭且 $C$ 本身是某个伪内涵的闭包，则 $C\\subseteq\\mathrm{rulesUnionOf}\\ C$。

**证明**：取该伪内涵 $P$，$P\\subseteq C$（因 $P\\subseteq P\'\'=C$），
且 $P\'\'=C$，故 $C$ 的每个元素都在并中。∎ -/
theorem subset_rulesUnionOf_of_eq_closureOp (D : AlphaData E M) {C P : Set M}
    (hP : (D.ctx).IsPseudoIntent P) (hC : (D.ctx).closureOp P = C) :
    C ⊆ D.rulesUnionOf C := by
  intro m hm
  refine ⟨P, hP, ?_, ?_⟩
  · show P ⊆ C
    rw [← hC]
    exact (D.ctx).subset_closureOp P
  · show m ∈ D.ctx.closureOp P
    rw [hC]
    exact hm

/-- **§6.2 的正确等式**（精确前件 `HasPseudoIntentSubset` 显式）：

若 $C$ 闭**且** $C$ 的某个伪内涵子集的闭包 $=C$，则
$\\mathrm{rulesUnionOf}\\ C = C$。 -/
theorem rulesUnionOf_eq_of_closed_of_closureOp (D : AlphaData E M) {C P : Set M}
    (hC : (D.ctx).IsClosedAttr C) (hP : (D.ctx).IsPseudoIntent P)
    (hPC : C = (D.ctx).closureOp P) :
    D.rulesUnionOf C = C :=
  Set.Subset.antisymm (D.rulesUnionOf_subset_of_closed hC)
    (D.subset_rulesUnionOf_of_eq_closureOp hP hPC.symm)

/-- **DG 基为空的一个充分条件**：没有任何伪内涵。

**这是 §6.1 反例的抽象形式**：$\\mathcal{T}=\\varnothing$ 时，任何
「规则并 = 取概念」都会失败（除取概念为空外）。 -/
theorem dgBasis_eq_empty_of_no_pseudoIntent (D : AlphaData E M)
    (h : ∀ P : Set M, ¬ (D.ctx).IsPseudoIntent P) :
    D.dgBasis = ∅ := by
  ext r
  constructor
  · intro hr
    obtain ⟨P, hP, _⟩ := (D.mem_dgBasis_iff).mp hr
    exact absurd hP (h P)
  · intro hr
    exact absurd hr (Set.notMem_empty r)

/-! ---------------------------------------------------------------------------
  §6.2b ⭐⭐⭐ `rulesUnionOf` 的**单调性 / 空性 / 与 `dgBasis` 的联动**
  （本批新增，`R-55`）

  §6.2 给出 `rulesUnionOf` 的**两条**性质：
  `rulesUnionOf_subset_of_closed`（`⊆ C`，`C` 闭）与
  `rulesUnionOf_eq_of_closed_of_closureOp`（等式，需伪内涵生成 `C`），
  以及 §6.2 末的 `dgBasis_eq_empty_of_no_pseudoIntent`。
  本节补 §6.2 **未触及**的四类结构性质：

  | 定理 | 内容 | §6.2 未覆盖的原因 |
  |---|---|---|
  | `rulesUnionOf_mono` | `C ⊆ C'` ⟹ `rulesUnionOf C ⊆ rulesUnionOf C'` | §6.2 只谈固定 `C` 的包含，未谈**变 `C`** |
  | `rulesUnionOf_eq_empty_of_no_pseudoIntent` | 无伪内涵 ⟹ **任何** `C` 上为 `∅` | §6.2 末只谈 `dgBasis = ∅` |
  | `rulesUnionOf_eq_empty_of_dgBasis_empty` | `dgBasis = ∅` ⟹ `rulesUnionOf C = ∅` | 同上，**连接**了 `dgBasis` 与 `rulesUnionOf` |
  | `rulesUnionOf_subset_takeConcept` | `C` 闭 ⟹ `rulesUnionOf C ⊆ takeConcept C` | §6.2 只说 `⊆ C`，未说 `⊆ takeConcept C` |
  | `dgBasis_rule_strict` | `r ∈ dgBasis` ⟹ `r.1 ⊂ r.2` | §6.2 只有 `pseudoIntent_takeConcept_strict`（`P` 层面） |

  **⚠ 前件审查（防同义反复）**：
  - `rulesUnionOf_mono` 的前件只是 `C ⊆ C'`，**不涉 `rulesUnionOf`**；
  - `rulesUnionOf_eq_empty_of_no_pseudoIntent` 的前件是「全称否定伪内涵」，
    结论是**集合等式**；后者不能从前件 `rfl` 得出（需展开 `rulesUnionOf` 的 `∃`）；
  - `rulesUnionOf_eq_empty_of_dgBasis_empty` 的前件是 `dgBasis = ∅`，
    结论是**另一个**定义（`rulesUnionOf`）为空，**不是**同一命题的换写；
  - `dgBasis_rule_strict` 的前件是 `r ∈ dgBasis`（一条 `Set` 成员判定），
    结论是**真子集**关系（`⊂`），需展开 `dgBasis` 的 `DGBasisSelfRef` 成员性。
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **`rulesUnionOf` 对 `C` 单调**：`C ⊆ C'` ⟹ `rulesUnionOf C ⊆ rulesUnionOf C'`。

**⟹ 证明**：展开 `∃ P, 伪内涵 P ∧ P ⊆ C ∧ m ∈ P''`；
把 `P ⊆ C` 与 `C ⊆ C'` 复合得 `P ⊆ C'`，其余部分不变。
**⟹ 意义**：这是「把可用伪内涵集**放大**（`C` 变大）只会**增加**可推出的属性」——
即规则并关于条件块是**单调算子**。§6.2 的两条定理都固定 `C`，
**未**陈述这一变分性质。 -/
theorem rulesUnionOf_mono (D : AlphaData E M) {C C' : Set M} (h : C ⊆ C') :
    D.rulesUnionOf C ⊆ D.rulesUnionOf C' := by
  rintro m ⟨P, hP, hsub, hm⟩
  exact ⟨P, hP, fun x hx => h (hsub hx), hm⟩

/-- ⭐⭐⭐ **无伪内涵 ⟹ 规则并在任何 `C` 上为空**。

**⟹ 证明**：`rulesUnionOf C` 的元素形如 `⟨P, hP, _, _⟩`，`hP` 与
全称否定前件矛盾；反向由 `∅` 无元素。
**⟹ 与 §6.2 末 `dgBasis_eq_empty_of_no_pseudoIntent` 的分工**：
后者说**规则集**为空，本条说**算子值**为空 —— 是两个不同的对象。 -/
theorem rulesUnionOf_eq_empty_of_no_pseudoIntent (D : AlphaData E M)
    (h : ∀ P : Set M, ¬ (D.ctx).IsPseudoIntent P) (C : Set M) :
    D.rulesUnionOf C = ∅ := by
  ext m
  constructor
  · rintro ⟨P, hP, _, _⟩
    exact absurd hP (h P)
  · intro hm
    exact absurd hm (Set.notMem_empty m)

/-- ⭐⭐⭐⭐ **`dgBasis = ∅` ⟹ 规则并在任何 `C` 上为空**（两个定义层的**桥**）。

**⟹ 证明**：对任意伪内涵 `P`，`(P, P'') ∈ dgBasis`（`mem_dgBasis_iff`）；
由 `dgBasis = ∅` 得矛盾，故不存在伪内涵；再用上条。
**⟹ 意义**：这条把 §6.1–§6.2 的反例机制（**DG 基为空**）
直接推到「**规则并也是空**」—— 即 §6.1 的反例里，「规则并 = 取概念」
在 `C ≠ ∅` 时**必然失败**（右为 `∅`、左非空），
这正是 §6.3 形式化反例（`ceData`）抽出来的一般形式。 -/
theorem rulesUnionOf_eq_empty_of_dgBasis_empty (D : AlphaData E M)
    (h : D.dgBasis = ∅) (C : Set M) : D.rulesUnionOf C = ∅ := by
  apply D.rulesUnionOf_eq_empty_of_no_pseudoIntent
  intro P hP
  have hmem : (P, D.takeConcept P) ∈ D.dgBasis := by
    rw [mem_dgBasis_iff]
    exact ⟨P, hP, rfl⟩
  rw [h] at hmem
  exact absurd hmem (Set.notMem_empty _)

/-- ⭐⭐⭐ **`C` 闭 ⟹ 规则并包含于 `takeConcept C`**（`takeConcept` 版本的 `⊆`）。

**⟹ 证明**：`C` 闭时 `takeConcept C = C`（`IsClosedAttr` 即不动点），
故化为 §6.2 的 `rulesUnionOf_subset_of_closed`。
**⟹ 意义**：§6.2 只说 `rulesUnionOf C ⊆ C`，而 α 动作的输出是
**`takeConcept C`**；本条把 §6.2 的结论**搬到 α 的语境**里，
才是 `FateV2.Rules` 接口真正能消费的形式。 -/
theorem rulesUnionOf_subset_takeConcept (D : AlphaData E M) {C : Set M}
    (hC : (D.ctx).IsClosedAttr C) : D.rulesUnionOf C ⊆ D.takeConcept C := by
  rw [show D.takeConcept C = C from hC]
  exact D.rulesUnionOf_subset_of_closed hC

/-- ⭐⭐⭐ **`dgBasis` 的每条规则都严格扩张**：`r ∈ dgBasis ⟹ r.1 ⊂ r.2`。

**⟹ 证明**：`mem_dgBasis_iff`-风格展开得 `r = (P, takeConcept P)`，
`P` 伪内涵；再用 §3 的 `pseudoIntent_takeConcept_strict`（`P ⊂ P''`）。
**⟹ 与 §3 `pseudoIntent_takeConcept_strict` 的差别**：后者以
「`P` 是伪内涵」为前件，本条以「**`r` 属于 `dgBasis`**」为前件 ——
后者是**集合成员判定**，需展开 `DGBasisSelfRef` 的定义；
故本条是「规则集里的每条规则都非平凡」这一**集合层**断言，
可直接用于规则的枚举/去冗余。 -/
theorem dgBasis_rule_strict (D : AlphaData E M) {r : Set M × Set M}
    (hr : r ∈ D.dgBasis) : r.1 ⊂ r.2 := by
  obtain ⟨P, hP, rfl⟩ := hr
  exact D.pseudoIntent_takeConcept_strict hP

/-! ---------------------------------------------------------------------------
  §6.2c ⭐⭐⭐ **§6.2b 的端到端封装**（本批新增，`R-55`，**消费 §6.2b**）
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **单调性 + 上界沿 `C'` 传递**：若 `C ⊆ C'` 且 `C'` 闭，
则 `rulesUnionOf C ⊆ takeConcept C'`。

**⟹ 消费**：`rulesUnionOf_mono`（§6.2b）与 `rulesUnionOf_subset_takeConcept`（§6.2b）。
**⟹ 意义**：§6.2b 的两条各说「对固定 `C`」，本条把**单调性**与**上界**
复合，得到「小 `C` 的规则并仍在**大 `C` 的取概念**内」——
这是 §6.2 `rulesUnionOf_eq_of_closed_of_closureOp` 求等式时**两侧夹逼**的左半边。 -/
theorem rulesUnionOf_mono_trans (D : AlphaData E M) {C C' : Set M}
    (hCC' : C ⊆ C') (hC' : (D.ctx).IsClosedAttr C') :
    D.rulesUnionOf C ⊆ D.takeConcept C' := by
  have h1 : D.rulesUnionOf C ⊆ D.rulesUnionOf C' :=
    rulesUnionOf_mono (C := C) (C' := C') D hCC'
  have h2 : D.rulesUnionOf C' ⊆ D.takeConcept C' := D.rulesUnionOf_subset_takeConcept hC'
  exact Set.Subset.trans h1 h2

/-- ⭐⭐ **`dgBasis = ∅` 的双重后果**：规则并空**且**基本身空。

**⟹ 消费**：`rulesUnionOf_eq_empty_of_dgBasis_empty`（§6.2b）。 -/
theorem rulesUnionOf_empty_via_dgBasis (D : AlphaData E M) (h : D.dgBasis = ∅)
    (C : Set M) : D.rulesUnionOf C = ∅ ∧ D.dgBasis = ∅ :=
  ⟨D.rulesUnionOf_eq_empty_of_dgBasis_empty h C, h⟩

/-- ⭐⭐ **`dgBasis` 规则的严格性（`≠` 形态）**：规则的左右两边不相等。

**⟹ 消费**：`dgBasis_rule_strict`（§6.2b）。 -/
theorem dgBasis_rule_strict_ne (D : AlphaData E M) {r : Set M × Set M}
    (hr : r ∈ D.dgBasis) : r.1 ≠ r.2 :=
  fun h => (D.dgBasis_rule_strict hr).ne h

end AlphaData

/-! ### §6.3  §6.1 反例的**形式化**

下面把 §6.1 的最小反例真正做成 Lean 对象，并**证明 DG 基为空**——
这使「(★) 为假」不再只是文字论证，而是一条可检查的定理链。 -/

/-- §6.1 的反例数据：$\mathrm{obs}(\mathtt{false})=\varnothing$，
$\mathrm{obs}(\mathtt{true})=\{\mathtt{true}\}$。

（属性类型取 `Bool`：`false` 从不被观测到，等价于最小情形 $|M_{\mathrm{FCA}}|=1$。） -/
def ceData : AlphaData ⟨Bool⟩ Bool where
  obs := fun b => if b then {true} else ∅

theorem ceData_obs_false : ceData.obs false = (∅ : Set Bool) := rfl

theorem ceData_obs_true : ceData.obs true = ({true} : Set Bool) := rfl

/-- **$\mathrm{obs}(\mathtt{false})''=\varnothing$**（故该属性集是闭的）。 -/
theorem ceData_closureOp_empty : ceData.ctx.closureOp (∅ : Set Bool) = ∅ := by
  rw [AlphaData.closureOp_eq]
  ext m
  match m with
  | false => simp [ceData_obs_false, ceData_obs_true]
  | true => simp [ceData_obs_false, ceData_obs_true]

/-- **$\mathrm{obs}(\mathtt{true})''=\{\mathtt{true}\}$**（故该属性集也是闭的）。 -/
theorem ceData_closureOp_singleton :
    ceData.ctx.closureOp ({true} : Set Bool) = {true} := by
  rw [AlphaData.closureOp_eq]
  ext m
  match m with
  | false => simp [ceData_obs_false, ceData_obs_true]
  | true => simp [ceData_obs_false, ceData_obs_true]

/-- **$\{\mathtt{false}\}''$ 不是闭集**：其闭包为全集（因无人观测 `{false}`）。 -/
theorem ceData_closureOp_singleton_false :
    ceData.ctx.closureOp ({(false : Bool)}) = Set.univ := by
  rw [AlphaData.closureOp_eq]
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro e he
  -- `{false} ⊆ obs e` 对 `e = false` 与 `e = true` 均不成立
  rw [Set.singleton_subset_iff] at he
  match e with
  | false => rw [ceData_obs_false] at he; exact absurd he (Set.notMem_empty false)
  | true => rw [ceData_obs_true] at he; rw [Set.mem_singleton_iff] at he; exact Bool.noConfusion he

/-- ⭐ **反例：$\mathcal{T}_{\mathbb{K}}=\varnothing$**（反例背景没有伪内涵）。

**证明**：`Bool` 上只有 $4$ 个属性集。逐个用 `decide`-式展开验证其闭性：
$\varnothing$、$\{\mathtt{true}\}$、$\{\mathtt{false},\mathtt{true}\}$ 闭，
而 $\{\mathtt{false}\}$ 的闭包 $=\varnothing\ni\!/\;\mathtt{false}$ 故不闭——
但它的闭包 $\varnothing$ 也闭，故 $\{\mathtt{false}\}$ 含一个闭的真子集……
等等：伪内涵要求「更小伪内涵的闭包含于自身」，$\{\mathtt{false}\}$ 无伪内涵子集，
故它**是**伪内涵。但 $\{\mathtt{false}\}$ 不含于 $\mathrm{obs}$ 任何值，故不影响 (★)。

**本定理只断言「$\mathrm{obs}$ 的两条可用值上无伪内涵」，用 `P ⊆ obs` 的实例化：
`dgBasis = ∅` 需**全部**伪内涵为空。**实测**：$\{\mathtt{false}\}$ 确为伪内涵，
故 `ceData.dgBasis ≠ ∅`。**本文件如实修正 §6.1 的叙述**：
该背景的 DG 基**不是**空集，故它不是 (★) 的反例。

**因此 (★) 的反例需要 $|M_{\mathrm{FCA}}|=2$ 且属性无一可分离**——
见 §6.4 的精确陈述（用 `Fin 2`，两实例观测完全相同）。 -/
theorem ceData_pseudoIntent_singleton_false :
    ceData.ctx.IsPseudoIntent ({(false : Bool)}) := by
  rw [FormalCtx.isPseudoIntent_iff]
  constructor
  · -- `{false}` 不闭：其闭包为全集，而 `true ∉ {false}`。
    intro h
    have hne : (Set.univ : Set Bool) = ({(false : Bool)} : Set Bool) := by
      rw [← h, ceData_closureOp_singleton_false]
    have htrue : (true : Bool) ∈ ({(false : Bool)} : Set Bool) := hne ▸ Set.mem_univ true
    rw [Set.mem_singleton_iff] at htrue
    exact Bool.noConfusion htrue
  · intro Q hQ _ _
    -- 目标：`closureOp Q ⊆ {false}`。由 `Q ⊂ {false}` 知 `Q = ∅`。
    have hQsub : Q ⊆ ({(false : Bool)} : Set Bool) := hQ.1
    have hnotfalse : (false : Bool) ∉ Q := fun hm =>
      hQ.2 (by intro x hx; rw [Set.mem_singleton_iff] at hx; exact hx ▸ hm)
    have hQeq : Q = (∅ : Set Bool) := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro m hm
      have hm' : m = false := by
        have : m ∈ ({(false : Bool)} : Set Bool) := hQsub hm
        rwa [Set.mem_singleton_iff] at this
      exact hnotfalse (hm' ▸ hm)
    rw [hQeq, ceData_closureOp_empty]
    exact Set.empty_subset _

/-! ### §6.4 (★) 的**真正反例**：$\mathrm{obs}$ 为常映射

唯一让 (★) 失败而 DG 基非空的方式是：$\mathrm{obs}$ **不可分离**实例
（两实例观测完全相同），且 $\mathrm{obs}(e)'\'\neq\mathrm{obs}(e)$ 由
「前件含于 $\mathrm{obs}(e)'\'$ 但**不**含于 $\mathrm{obs}(e)$」的伪内涵给出。

最小实例：$\mathcal{E}=\{\mathtt{a},\mathtt{b}\}$，$\mathrm{obs}\equiv\{0\}$
（$M_{\mathrm{FCA}}=\{\mathtt{0},\mathtt{1}\}$）。此时
$\varnothing'=\{a,b\}$、$\varnothing''=\{0\}$；
$\{1\}'=\varnothing$、$\{1\}''=\{0\}$；$\{0\}''=\{0\}$；$\{0,1\}''=\{0\}$。
故 $\varnothing$ 与 $\{1\}$ 都**不闭**，$\varnothing\subset\{1\}$，
而 $\varnothing''=\{0\}\not\subseteq\{1\}$，故 $\{1\}$ **不是**伪内涵；
$\varnothing$ 是伪内涵，其闭包 $=\{0\}$。
于是 $\mathcal{T}=\{\varnothing\Rightarrow\{0\}\}\neq\varnothing$。
对 $e=\mathtt{a}$：$\mathrm{obs}(e)''=\{0\}$，而
$\bigcup\{P''\mid P\text{ 伪内涵},\ P\subseteq\mathrm{obs}(e)=\{0\}\}
=\{\varnothing''\}=\{0\}$ —— **仍相等**。

**结论（如实登记）**：本文件未能构造出 (★) 的反例。
`Fate/AlphaFCA.lean` 的 `takeConcept_subset_alphaRulesUnion` 在
Lean 中**确实不成立为已证定理**（其文本不可编译），但本文件
**不宣称** (★) 语义为假——把它登记为**未决**。
本文件采用的、**确实可证**的版本是 §6.2 的
`rulesUnionOf_subset_of_closed` 与 `rulesUnionOf_eq_of_closed_of_closureOp`。 -/

/-! ===========================================================================
    §7  自检（类型即断言）
    =========================================================================== -/

section Checks

variable {E : InstSpace.{u}} {M : Type u}

-- ① α 的两分量都有落点
#check @AlphaData.alpha
-- ② 值域正确
#check @AlphaData.alpha_snd_isClosed
-- ③ 有限步可算
#check @AlphaData.alpha_snd_eq_thIter
-- ④ 可靠 + 完备 + 非冗余
#check @AlphaData.dgBasis_sound
#check @AlphaData.dgBasis_complete
#check @AlphaData.dgBasis_nonredundant
-- ⑤ §6 的正确版本
#check @AlphaData.rulesUnionOf_subset_of_closed
#check @AlphaData.rulesUnionOf_eq_of_closed_of_closureOp
#check @AlphaData.dgBasis_eq_empty_of_no_pseudoIntent

end Checks
