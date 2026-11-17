/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Model.Alpha
阶段：**阶段 1B —— 依作者裁决 D 把 α 具体化为「取概念过程」**

---------------------------------------------------------------------------
裁决依据（**最高优先级**）
---------------------------------------------------------------------------
`_规格/03-规范与裁决/01-作者裁决C-最彻底.md` **裁决 D**：

> ### 裁决 D：α 具体化为 FCA 的取概念过程
> **采纳。** 理由：FCA 是理论中"抽象"环节唯一获得真实功能位置的模块（主文档第 5 章）。
> - α **定义为**形式背景 `𝕂=(G_FCA, M_FCA, I)` 上的**取概念（导出算子不动点）过程**
> - 由此 **α 的存在性由 FCA 基本定理保证**，不再作为独立待证命题悬置
> - 代价：必须先解决**编码算子**（连续状态 → 二值形式背景），及**离散化误差**的量化
> - 该桥当前未建立（主文档开放问题 5.5），**本裁决要求把它建起来**

规格 `02-证明路线/01-路线图.md` 阶段 1B 的 **T1B.2**：

> **（依裁决 D 重新陈述）**
> `α 定义为形式背景 𝕂 上的取概念（导出算子不动点）过程 ⟹ α:ℰ→ℛ 存在`

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
1. **编码算子** $\mathrm{enc}:\mathcal{X}\to 2^{G_{\mathrm{FCA}}}\times 2^{M_{\mathrm{FCA}}}$
   的**类型与结构**（A32 / T1B.2a 的**定义层**）
2. **取概念过程** $\alpha$ 的**定义**（依裁决 D，T1B.2）
3. **保结构性**（T1B.2b / 主文档 T6.13）：
   $\alpha$ 保持抽象等价关系 $\sim_{\mathcal{E}}$

---------------------------------------------------------------------------
诚实边界（**必须与结果同时阅读**）
---------------------------------------------------------------------------
**本文件完成的是「定义层」与「结构性陈述」，不是「存在性证明」。**

具体地：
1. $\alpha$ 的**存在性**在本文件中是**构造性地给出**的
   （即：`takeConcept` 是一个**具体函数**），
   故**不需要**引用 FCA 基本定理来「保证存在」——
   这正是裁决 D 的意图：把存在性从「待证命题」变为「构造」。
2. **但**「该构造是否满足主文档第 5 章对 $\alpha$ 的全部语义要求」
   **本文件不主张**。那是一组**额外条件**，须逐条陈述与验证。
3. **离散化误差的量化（E8）未做**——它是**大项目**
   （需自建连续状态 → 二值形式背景的误差理论，无 Mathlib 构件可借）。
   本文件**据实登记**该未完成项，**不掩盖**。
4. **A31（$\sim_{\mathcal{E}}$ 的判据）仍是待作者裁决项 Q-3。**
   本实现把 $\sim_{\mathcal{E}}$ **参数化**（作为一个外部给定的等价关系），
   **不擅自选定判据**。故 T1B.2b 在本文件中是
   「**若** $\sim_{\mathcal{E}}$ 给定，**则** $\alpha$ 保持它」这一**条件形式**，
   而不是无条件断言。
-/

import Mathlib.Order.Concept
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Equiv.Basic
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set

universe u v

noncomputable section

set_option linter.checkUnivs false

/-!
  # Rules · Alpha

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Alpha.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Implication
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  编码算子 enc（A32 / T1B.2a）
    =========================================================================== -/

/-- **编码算子** $\mathrm{enc}:\mathcal{X}\to 2^{G_{\mathrm{FCA}}}\times 2^{M_{\mathrm{FCA}}}$
（A32 / T1B.2a）。

规格 A32 原文：

> **A32**｜FCA 编码算子 $x_t\mapsto(A_t,B_t)$ 存在且其**离散化误差有界**｜待证命题

规格 `01-路线图.md` T1B.2a：

> **编码算子定义**（依裁决 D 新增）：存在映射
> $\mathrm{enc}:\mathcal{X}\to 2^{G_{\mathrm{FCA}}}\times 2^{M_{\mathrm{FCA}}}$，
> 把连续状态 $x_t$ 映到二值形式背景的对象集／属性集。

**本实现的结构选择（及其理由）**：

把编码算子**拆成两个可分别检验的部分**：

1. `toObjects : X → Set GFCA` —— 状态 ↦ **对象集**
   （「该状态属于哪些 FCA 对象」）；
2. `toAttrs : X → Set MFCA` —— 状态 ↦ **属性集**
   （「该状态满足哪些属性」）。

**为什么拆**：规格 §3.4 的 S2 步骤要求
$I(e_t,m_j):=[m_j(x_t)=\text{真}]$——
即**对象–属性关系由属性谓词在状态上的取值决定**。
故 `toAttrs` 是**本质的**（它承载属性谓词），
而 `toObjects` 是**索引方式**（选择哪些对象参与背景）。

拆分使**两者可独立替换与检验**，且使下面的一致性条件
（`coherent`）成为一个**可陈述、可验证**的谓词。

**本定义即 A32 的「存在」一半在定义层的落点。**
「误差有界」一半**未做**（见文件头诚实边界 3）。 -/
structure Encoder (F : Frame) (K : FormalCtx.{u,v}) where
  /-- 状态 ↦ 该状态在 $\mathbb{K}$ 中对应的**对象集** $A_t\subseteq G_{\mathrm{FCA}}$ -/
  toObjects : F.X.Carrier → Set K.GFCA
  /-- 状态 ↦ 该状态满足的**属性集** $B_t\subseteq M_{\mathrm{FCA}}$ -/
  toAttrs : F.X.Carrier → Set K.MFCA

/-- **编码算子的自洽性条件**（**本实现新增，非规格原文**）。

$(\mathrm{enc})$ **自洽** $\iff$ 对每个状态 $x$：

$$\mathrm{toObjects}(x)' = \mathrm{toAttrs}(x)$$

即「由对象的属性闭包」与「直接读出的属性集」一致。

**为什么必须显式写出这一条**：若不要求，则 `toObjects` 与 `toAttrs`
可以**互相矛盾**（如某状态既「属于对象 $g$」又「不满足 $g$ 的所有属性」），
此时形式背景 $I$ 与状态到概念的映照**不自洽**，
下游的「取概念过程」就不再是状态的忠实抽象。

**本实现不把该条件塞进 `Encoder` 结构**——理由：
塞进去等于把一条**有真假的断言**伪装成**定义的一部分**，
违反规格 §2.5.3「不得用同一编号承载定义与由该定义导出的性质」。
故它是**独立的谓词**，可由使用者在需要时要求。 -/
def Encoder.Coherent {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K) : Prop :=
  ∀ x : F.X.Carrier, K.polarDown (enc.toAttrs x) = enc.toObjects x

/-- 自洽性的**展开形式**：逐状态写出 `Coherent` 的等式。 -/
theorem Encoder.coherent_iff {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K) :
    enc.Coherent ↔ ∀ x, K.polarDown (enc.toAttrs x) = enc.toObjects x :=
  Iff.rfl

/-! ### §1.1 自洽性的**等价条件**

`Encoder.Coherent` 的定义 `toObjects x = polarDown (toAttrs x)` 是**等式形式**。
下面给出它的三个**等价条件**，分别把「自洽」这件事翻译成
**逐元素判据**、**闭包/不动点判据**、**概念格判据**。

这三个条件是**真正的充要条件**（不是「由定义导出的弱性质」）：
每一条都**反向**蕴含 `Coherent`。

**一个必须说清的边界**：`Coherent` 是**不对称**的——它只约束「对象侧」，
即要求 `toObjects x` 恰是 `toAttrs x` 的下极。
它**不**要求 `toAttrs x` 是闭集（见 `coherent_not_symmetric`）。
故下面三个等价条件都**显式地**只把闭性加在对象侧，
**不**错误地要求 `toAttrs x = polarUp (toObjects x)`。 -/

/-- **等价条件 A（逐元素判据）**：

$$\mathrm{Coherent}\iff
  \forall x\,g,\quad g\in\mathrm{toObjects}(x)\iff
  \bigl(\forall m\in\mathrm{toAttrs}(x),\ (g,m)\in I\bigr)$$

即：**一个对象 $g$ 属于状态 $x$ 的对象集，当且仅当 $g$ 满足 $x$ 列出的全部属性**。
这是「`toObjects` 与 `toAttrs` 自洽」的**最直白读法**：
两边的成员关系互相推出，没有「属于对象却不满足其属性」的缝隙。

**证明**：把集合等式用 `Set.ext` 化为成员等价，
再用 `mem_polarDown_iff`（$B'$ 的成员判据）即得。∎ -/
theorem Encoder.coherent_iff_pointwise {F : Frame} {K : FormalCtx.{u,v}}
    (enc : Encoder F K) :
    enc.Coherent ↔ ∀ x g, g ∈ enc.toObjects x ↔ ∀ m ∈ enc.toAttrs x, K.Irel g m := by
  constructor
  · intro h x g
    rw [← h x, K.mem_polarDown_iff]
  · intro h x
    refine Set.ext fun g => ?_
    rw [K.mem_polarDown_iff]
    exact (h x g).symm

/-- **等价条件 B（闭包/不动点判据）**：

$$\mathrm{Coherent}\iff \forall x,
  \underbrace{\mathrm{polarDown}\,(\mathrm{polarUp}\,(\mathrm{toObjects}\,x))
    = \mathrm{toObjects}\,x}_{\text{对象侧闭（是 extent）}}
  \ \wedge\
  \underbrace{\mathrm{closureOp}\,(\mathrm{toAttrs}\,x) = \mathrm{polarUp}\,(\mathrm{toObjects}\,x)}_{\text{属性侧闭包被对象侧回收}}$$

即：**对象集是闭的（一个 extent），且对属性集取闭包恰好回收为对象集的上极**。

**为什么这仍是充要的（而「只要求 toObjects 闭」不够）**：
只要求 $\mathrm{toObjects}\,x$ 闭、并附带 $\mathrm{toAttrs}\,x\subseteq\mathrm{polarUp}(\mathrm{toObjects}\,x)$
是**严格更弱**的（反例：取 $\mathrm{toAttrs}\,x=\varnothing$，则 $\mathrm{polarDown}\,\varnothing$ 是全集）。
本条件用「闭包**相等**」把这条缝补上，故反向也成立。

**证明**：正向用 $\mathrm{polarDown\_polarUp\_polarDown}$ 与定义等式；
反向把 $\mathrm{polarDown}\,(\mathrm{toAttrs}\,x)$ 用
$\mathrm{polarDown}(\mathrm{closureOp}\,B)=\mathrm{polarDown}\,B$ 接到对象侧。∎ -/
theorem Encoder.coherent_iff_closed_and_closure {F : Frame} {K : FormalCtx.{u,v}}
    (enc : Encoder F K) :
    enc.Coherent ↔ ∀ x,
      K.polarDown (K.polarUp (enc.toObjects x)) = enc.toObjects x ∧
      K.closureOp (enc.toAttrs x) = K.polarUp (enc.toObjects x) := by
  constructor
  · intro h x
    refine ⟨?_, ?_⟩
    · rw [← h x, K.polarDown_polarUp_polarDown]
    · rw [← h x]
  · intro h x
    have hcl : K.polarDown (K.closureOp (enc.toAttrs x)) = K.polarDown (enc.toAttrs x) :=
      K.polarDown_polarUp_polarDown (enc.toAttrs x)
    calc K.polarDown (enc.toAttrs x)
        = K.polarDown (K.closureOp (enc.toAttrs x)) := hcl.symm
      _ = K.polarDown (K.polarUp (enc.toObjects x)) := by rw [(h x).2]
      _ = enc.toObjects x := (h x).1

/-- **等价条件 C（概念格判据）**：

$$\mathrm{Coherent}\iff \forall x,\ \exists c\in\mathfrak{B}(\mathbb{K}),\quad
  c.\mathrm{extent}=\mathrm{toObjects}\,x\ \wedge\
  c.\mathrm{intent}=\mathrm{closureOp}\,(\mathrm{toAttrs}\,x)$$

即：**每个状态的 $(\mathrm{toObjects}\,x,\ \mathrm{closureOp}(\mathrm{toAttrs}\,x))$
确是一个形式概念**（其外延是对象集，内涵是属性集的闭包）。

这是把自洽性**接回 FCA 基本定理**的说法：
「取概念」过程 $\alpha$ 的输入输出对**落在概念格里**，
而不只是两个互不相干的集合。

**证明**：正向直接构造该概念（两个 Galois 场由 `Coherent` 与幂等性填出）；
反向用概念的 `lowerPolar_intent` 场
（$\mathrm{polarDown}(\mathrm{intent})=\mathrm{extent}$）还原 $\mathrm{Coherent}$。∎ -/
theorem Encoder.coherent_iff_exists_concept {F : Frame} {K : FormalCtx.{u,v}}
    (enc : Encoder F K) :
    enc.Coherent ↔ ∀ x, ∃ c : Concept K.GFCA K.MFCA K.Irel,
      c.extent = enc.toObjects x ∧ c.intent = K.closureOp (enc.toAttrs x) := by
  constructor
  · intro h x
    refine ⟨⟨enc.toObjects x, K.closureOp (enc.toAttrs x), ?_, ?_⟩, rfl, rfl⟩
    · -- upperPolar (toObjects x) = closureOp (toAttrs x)
      show K.polarUp (enc.toObjects x) = K.polarUp (K.polarDown (enc.toAttrs x))
      rw [h x]
    · -- lowerPolar (closureOp (toAttrs x)) = toObjects x
      show K.polarDown (K.polarUp (K.polarDown (enc.toAttrs x))) = enc.toObjects x
      rw [K.polarDown_polarUp_polarDown]
      exact h x
  · intro h x
    obtain ⟨c, hc, hci⟩ := h x
    have hlower : K.polarDown (c.intent) = c.extent := c.lowerPolar_intent
    calc K.polarDown (enc.toAttrs x)
        = K.polarDown (K.polarUp (K.polarDown (enc.toAttrs x))) :=
          (K.polarDown_polarUp_polarDown (enc.toAttrs x)).symm
      _ = K.polarDown (c.intent) := by rw [hci]
      _ = c.extent := hlower
      _ = enc.toObjects x := hc

/-- **`Coherent` 的对称版本是严格的**（**诚实边界**）。

`Coherent` **不**蕴含「属性侧自洽」$\mathrm{toAttrs}\,x=\mathrm{polarUp}(\mathrm{toObjects}\,x)$。

**反例构造**：取 $\mathrm{toAttrs}\,x=B$ 使 $B$ **不**闭（$B''\neq B$），
并取 $\mathrm{toObjects}\,x=B'$。则 $\mathrm{polarDown}(\mathrm{toAttrs}\,x)=B''^{\!\!\prime}=B'=\mathrm{toObjects}\,x$，
故 `Coherent` 成立；但 $\mathrm{polarUp}(\mathrm{toObjects}\,x)=B''\neq B=\mathrm{toAttrs}\,x$。

**本引理的作用**：**阻止**把 `Coherent` 误述为「概念对 $(A,B)$」
（后者要求 $B$ 也闭）。`Coherent` 只钉住对象侧。
规格纪律要求把这条**不对称性显式登记**，而不是含糊带过。

**形式陈述**（**条件形式**）：若某个状态的 `toAttrs` 非闭且 `toObjects` 取为其下极，
则 `Coherent` 与对称等式**不可兼得**。 -/
theorem Encoder.coherent_not_symmetric {F : Frame} {K : FormalCtx.{u,v}}
    (enc : Encoder F K) {x : F.X.Carrier}
    (hnc : K.closureOp (enc.toAttrs x) ≠ enc.toAttrs x)
    (ho : enc.toObjects x = K.polarDown (enc.toAttrs x)) :
    enc.toAttrs x ≠ K.polarUp (enc.toObjects x) := by
  intro hsym
  apply hnc
  rw [hsym, ho, K.closureOp_idem]

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ===========================================================================
    §2  取概念过程 α（依裁决 D；T1B.2）
    =========================================================================== -/

/-- **取概念过程**：把一个属性集**取到其闭包**（导出算子的不动点上）。

裁决 D 原文：

> α **定义为**形式背景 $\mathbb{K}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$ 上的
> **取概念（导出算子不动点）过程**

**本实现的具体构造**：给定属性集 $B$，取 $B''$。
由 `Fate.FCA` 的幂等性（Mathlib 的 `upperPolar_lowerPolar_upperPolar`），
$B''$ **确是一个不动点**（即闭集）——
故「取概念」这一动作**有具体函数实现**，其**值域落在闭集内**。

**这就是裁决 D 所说的「存在性由 FCA 基本定理保证」的落地方式**：
我们没有「假设存在一个 α」，而是**写出了一个 α**，
并证明**它的输出确在概念侧**（见 `takeConcept_isClosed`）。 -/
def takeConcept (B : Set K.MFCA) : Set K.MFCA := K.closureOp B

/-- **取概念过程的输出是不动点**（**这是 α 值域正确的证明**）：

$$(\mathrm{takeConcept}\,B)'' = \mathrm{takeConcept}\,B$$

即：取概念的结果**确是一个闭集**（FCA 意义上的 intent / 概念的第二分量）。

**证明**：闭包算子的幂等性。∎

**本定理是 T1B.2 的核心**——它使「$\alpha$ 的值域落在规则/概念侧」
从**假设**变为**已证**。 -/
theorem takeConcept_isClosed (B : Set K.MFCA) : K.IsClosedAttr (K.takeConcept B) :=
  K.closureOp_idem B

/-- **取概念过程是幂等的**：再取一次不变。 -/
theorem takeConcept_idem (B : Set K.MFCA) :
    K.takeConcept (K.takeConcept B) = K.takeConcept B :=
  K.closureOp_idem B

/-- **取概念过程是单调的**。 -/
theorem takeConcept_mono {B₁ B₂ : Set K.MFCA} (h : B₁ ⊆ B₂) :
    K.takeConcept B₁ ⊆ K.takeConcept B₂ :=
  K.closureOp_mono h

/-- **取概念过程是扩张的**：$B\subseteq B''$。 -/
theorem subset_takeConcept (B : Set K.MFCA) : B ⊆ K.takeConcept B :=
  K.subset_closureOp B

/-- **取概念过程保蕴含**（**与蕴含语义的相容性**）：

$$\mathbb{K}\models A\Rightarrow B \iff B''\subseteq A''$$

即：蕴含**完全由闭包决定**——
$A\Rightarrow B$ 成立当且仅当「$B$ 的取概念结果」被「$A$ 的取概念结果」包含。

**这是把「蕴含」与「取概念」两个概念接起来的关键引理**，
也是 `takeConcept` 作为 α 的语义依据：
它说明**取概念过程不丢失蕴含信息**。

**证明**：由 `models_iff_subset_semClosure`
（$\mathbb{K}\models A\Rightarrow B\iff B\subseteq A''$）
与 $A''$ 是闭集（$A''''=A''$）：
$B\subseteq A''\iff B''\subseteq A''$（需用闭包的最小性）。
详细地：($\Leftarrow$) $B\subseteq B''\subseteq A''$；
($\Rightarrow$) 若 $B\subseteq A''$，对两边取闭包得 $B''\subseteq (A'')''=A''$。∎ -/
theorem models_iff_takeConcept_subset {A B : Set K.MFCA} :
    K.Models A B ↔ K.takeConcept B ⊆ K.takeConcept A := by
  rw [models_iff_subset_semClosure]
  constructor
  · -- B ⊆ A''  ⟹  B'' ⊆ A''
    intro h
    have h2 : K.closureOp B ⊆ K.closureOp (K.closureOp A) := K.closureOp_mono h
    rwa [K.closureOp_idem A] at h2
  · -- B'' ⊆ A''  ⟹  B ⊆ A''
    intro h m hm
    exact h (K.subset_closureOp B hm)

end FormalCtx

/-! ===========================================================================
    §3  保结构性：α 保持抽象等价关系（T1B.2b / 主文档 T6.13）
    =========================================================================== -/

/-- **抽象等价关系 $\sim_{\mathcal{E}}$ 的参数化载体**。

**规格依据与待裁决状态**：

规格 A31：

> **A31**｜「抽象」与「压缩」在本框架中的数学含义已给定
> （抽象＝实例集在**等价关系下的代表元／商**，而非率失真有损映射）｜定义性约定

规格 `01-路线图.md` 阶段 0 风险 **R0.3（中）**：

> A31 已裁定「抽象＝实例集在等价关系下的商」，但**判据未给**（主文档开放问题 5.3）。
> 若 $\sim_{\mathcal{E}}$ 无判据，$\alpha$ 在 Lean 中只能是**未解释的常量**，
> 阶段 1B 会因此无法启动。

**本实现的处置（依 `裁决记录.md` Q-3）**：
把 $\sim_{\mathcal{E}}$ **做成参数**（一个 `Setoid`），
**不擅自选定判据**——因为判据属**作者裁决**。

**这样做的好处**：$\alpha$ 的**定义**不再依赖判据（它不是未解释常量，
而是 `takeConcept` 这一具体函数），
而**保结构性定理**（T1B.2b）成为一个**条件定理**：
「**若** $\sim_{\mathcal{E}}$ 给定且满足 [条件]，**则** $\alpha$ 保持它」。

**这符合规格 `00-总纲.md` 第二节的三分类**：
T1B.2b 是**类别 ②（条件定理）**，
其前件（$\sim_{\mathcal{E}}$ 的判据）交给实验/作者裁决。 -/
abbrev AbstractEquiv (E : InstSpace) := Setoid E.Carrier

/-- **实例集的抽象等价关系是的：A31 的「商」结构**。

规格 A31 明写：抽象＝实例集在等价关系下的**代表元／商**。
本定义给出商类型，使 A31 的内容成为**类型层的事实**。 -/
abbrev AbstractQuotient {E : InstSpace} (eqv : AbstractEquiv E) := Quotient eqv

/-- **保结构性的条件（本实现显式化的前件）**。

$(\mathrm{enc},\sim_{\mathcal{E}})$ **相容** $\iff$
等价的实例被编码到**相同的属性集**：

$$e_1\sim_{\mathcal{E}} e_2 \Longrightarrow \mathrm{toAttrs}(e_1)=\mathrm{toAttrs}(e_2)$$

**为什么需要这一条**：$\sim_{\mathcal{E}}$ 是「实例何时算同一个抽象对象」的关系；
若两个「相同」的实例被编码到**不同**的属性集，
则「取概念」后它们给出**不同的概念**，
即 $\alpha$ **不**保持抽象等价——这正是 T1B.2b 要说的事。

**本实现把该前件显式写出，而不是假定它自动成立**——
依规格阶段 1B 验收标准 2：
「每条条件定理的前件必须是**一个可以写成 Lean 类型的东西**」。 -/
def Encoder.RespectsEquiv {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K)
    {E : InstSpace} (embed : E.Carrier → F.X.Carrier) (eqv : AbstractEquiv E) : Prop :=
  ∀ e₁ e₂ : E.Carrier, e₁ ≈ e₂ → enc.toAttrs (embed e₁) = enc.toAttrs (embed e₂)

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-- **T1B.2b（主文档 T6.13）：α 保持抽象等价关系**。

**这是本文件的中心定理。**

**陈述**：若编码算子与 $\sim_{\mathcal{E}}$ 相容（`RespectsEquiv`），
则**取概念过程后的结果也相等**——
即 $\alpha$ 把等价的实例映到**同一个概念**。

形式地：$e_1\sim_{\mathcal{E}}e_2\Longrightarrow
\mathrm{takeConcept}(\mathrm{toAttrs}(e_1))=\mathrm{takeConcept}(\mathrm{toAttrs}(e_2))$。

**类别**：**② 条件定理**（规格 `00-总纲.md` 第二节）。
前件 ＝ `Encoder.RespectsEquiv`（+ 编码算子给定 + $\sim_{\mathcal{E}}$ 给定）。
**前件的成立性交给实验/作者裁决**，本实现只证蕴含式。

**证明**：由 `RespectsEquiv` 得 $\mathrm{toAttrs}(e_1)=\mathrm{toAttrs}(e_2)$，
两边同取 `takeConcept` 即得（等式替换）。∎

**这证明是「平凡」的吗？** —— 就 $\mathbb{K}$ 内部而言是。
但它的价值在于**把「α 保持抽象」这件事的**真正负担**定位清楚了**：
负担**不在**「取概念」这一步（它自动保持相等），
而**在编码算子**这一侧（是否把等价实例映到同一属性集）。
**这个定位本身就是 T1B.2b 的实质内容**——
规格 `01-路线图.md` R1B.2 说「风险转化为编码算子与离散化误差」，
本定理正是这一转化的**形式化体现**。 -/
theorem alpha_respects_equiv {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K)
    {E : InstSpace} (embed : E.Carrier → F.X.Carrier) (eqv : AbstractEquiv E)
    (hresp : enc.RespectsEquiv embed eqv) :
    ∀ e₁ e₂ : E.Carrier, e₁ ≈ e₂ →
      K.takeConcept (enc.toAttrs (embed e₁)) = K.takeConcept (enc.toAttrs (embed e₂)) :=
  fun e₁ e₂ he => by rw [hresp e₁ e₂ he]

/-- **推论：α 在商上良定义**。

由 `alpha_respects_equiv`，$\alpha\circ\mathrm{enc}$ 可**下降**到商
$\mathcal{E}/\!\sim_{\mathcal{E}}$ 上，给出一个良定义的映射。

**这是 A31「抽象＝商」与裁决 D「α＝取概念」两条的结合点**：
它说明「先在实例集上取商、再抽象」与「先抽象、再取商」
在**编码算子相容**的前提下给出**同一结果**。

**实现说明**：本定理用 `Quotient.lift` 的**可计算性条件**
（`RespectsEquiv` 正是所需的 `∀ a b, a ≈ b → f a = f b`），
故它是一个**具体的商下降**，不是抽象存在性断言。

**待裁决提示**：$\sim_{\mathcal{E}}$ 的**判据**仍是 Q-3（作者裁决）。 -/
def alphaOnQuotient {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K)
    {E : InstSpace} (embed : E.Carrier → F.X.Carrier) (eqv : AbstractEquiv E)
    (hresp : enc.RespectsEquiv embed eqv) :
    Quotient eqv → Set K.MFCA :=
  Quotient.lift (fun e => K.takeConcept (enc.toAttrs (embed e)))
    (fun a b hab => alpha_respects_equiv enc embed eqv hresp a b hab)

end FormalCtx

/-! ===========================================================================
    §4  E8：编码算子的**离散化误差界**（A32 / T1B.2a 的「误差有界」一半）
        **依作者裁决 I：先查文献**
    =========================================================================== -/

/-! ### §4.1 文献核查（**依裁决 I**，动手前先查）

**查到**（arXiv API，见 `_refs/引用登记.md`）：

| 主题 | 文献中的标准处理 |
|---|---|
| 量化误差的度量 | **Wasserstein 距离**是标准度量 |
| 最优 $N$ 点量化的速率 | **Zador 定理**：误差 $\sim N^{-1/d}$（$d$ 为维数） |
| 网格/分箱离散化 | 误差上界与**网格直径**成正比 |

**⚠ 文献与本理论的关系（必须分清）**：

| 部分 | 来源 |
|---|---|
| 「离散化误差用 Wasserstein 度量」「与网格直径成正比」 | **标准**（可引 `[已知]`） |
| $\mathrm{enc}:\mathcal{X}\to 2^{G}\times 2^{M}$ 这一**特定的 FCA 二值化形式** | **本理论特有**，文献无 |
| 原型实测的「**胞腔直径不由 $\gamma$ 单独控制**」 | **本实现的原型实测**（非文献） |

**故 E8 的「界的形式」不能照抄文献**——
文献给的是**通用**的量化误差界，
而本理论需要的是**该特定编码**的界。 -/

/-- **编码的胞腔**：被 $\mathrm{enc}$ 映到同一 $(A,B)$ 的状态集合。

$$\mathrm{fiber}(\mathrm{enc}, A, B) := \{x\mid \mathrm{toObjects}(x)=A\wedge\mathrm{toAttrs}(x)=B\}$$

**这是 E8 中「离散化误差」的**载体**：
同一胞腔内的状态**不可区分**，故误差只能以**胞腔的直径**度量。 -/
def Encoder.Fiber {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K)
    (A : Set K.GFCA) (B : Set K.MFCA) : Set F.X.Carrier :=
  {x | enc.toObjects x = A ∧ enc.toAttrs x = B}

/-- **E8 的误差量**：胞腔直径的上确界（**由调用者提供的度量**）。

**为什么把度量做成参数**：$\mathcal{X}$ 上**未给定度量**
（`StateSpace` 只要求拓扑 + 可测，见 `Fate.Basic`）。
**强行指定一个度量就是往定义里塞额外假设**——
违反「定义与断言分离」（规格 §2.5.3）。

故本实现把 $\mathrm{diam}$ 做成**显式参数**，
并要求调用者声明所用度量。 -/
abbrev CellDiameter (F : Frame) :=
  (F.X.Carrier → F.X.Carrier → ℝ) → Set F.X.Carrier → ℝ

/-- **E8 界的形式（本实现采用的，**依原型实测**）**。

**原型实测的关键发现**（`prototype/fca-alpha/results/report.md` §V1）：

> 本运行中有 **158/200** 个状态的胞腔在某一坐标上**横跨至盒下界**
> （即不受任何下界谓词约束），
> 故其直径**由盒端点而非阈值间隔决定**。

**故本实现登记 E8 的界为三参数形式**：

$$\mathrm{diam}\ \le\ g(\gamma,\ \text{盒端点},\ \lvert M_{\mathrm{FCA}}\rvert)$$

**而不是**单参数 $g(\gamma)$——**后者经原型实测不足以控制胞腔直径**。

**⚠ 本实现的处置（诚实标注）**：
本实现**只登记该界的形式（参数表）**，
**不填充 $g$ 的具体表达式**——
理由：填具体表达式需要**具体的编码方案**（阈值规则、盒的定义），
而规格尚未固定编码方案（A32 只说「存在」）。
**填数即为虚构**（规格纪律）。 -/
structure E8BoundForm where
  /-- 参数一：阈值间隔 $\gamma$。 -/
  gamma : ℝ
  /-- 参数二：盒端点（**原型实测要求此项**）。 -/
  boxLo : ℝ
  boxHi : ℝ
  /-- 参数三：属性个数 $\lvert M_{\mathrm{FCA}}\rvert$（**原型实测建议**）。 -/
  attrCount : ℕ
  /-- 盒端点的合法性前件（**不假定，显式要求**）。 -/
  hbox : boxLo ≤ boxHi

/-- **E8 的界谓词**（**条件形式**）。

$$\forall x\in C,\ \forall y\in C,\ \mathrm{diam}(x,y)\ \le\ g(\text{参数})$$

即：**胞腔 $C$ 内任意两点的距离都被界 $g$ 控制**。

**本实现只给出谓词的形状**：
把「界函数 $g$」与「度量 $\mathrm{diam}$」都做成**参数**，
因为二者都属**编码方案的选择**，规格未固定。

---------------------------------------------------------------------------
⚠ **本定义的第一版是错的 —— 如实记录（依主控诊断）**
---------------------------------------------------------------------------
**第一版**曾写作：

```lean
def E8Holds ... (_g) (_diam) (_C) (diamC : ℝ) : Prop := diamC ≤ _g form
```

**其缺陷**：`_diam` 与 `_C` **从未出现在右端**（本实现当时用 `_` 前缀
标注了「未使用」，但**没有意识到后果**）。
于是该谓词**只说「某个数 ≤ 某个数」，与集合 $C$ 无关**——
它**无法表达「这个集合的直径有界」**。

**主控诊断（精确）**：这不是「内容弱」，而是**结构上缺了一环**：
`diamC` 没有通过 `diam` 与 `C` 联系起来。

**后果**：`E8Holds F form g diam C (g form)` 对**任意** `diam`、`C`
都由 `le_refl` 成立——**该形式实际上没有断言任何东西**。

**这与 R-022 的错误同类**：一个**看起来在说某事、实际没说某事**的形式。
区别是 R-022 是「**声明为假**」，本条是「**形式太松**」。

**本版修正**：把 `diam` 与 `C` **真正用进右端**（见上方的 `∀ x ∈ C, ∀ y ∈ C, …`）。
**修正后**：
- `diam` 与 `C` 真正被使用；
- 谓词表达「$C$ 内任意两点的距离 $\le$ 界」——**正是 E8 想要的**；
- **仍然不填 $g$ 的具体表达式**（那是 OQ-4 的事）；
- **`le_refl` 那类平凡构造不再可行**
  （要证的是 `∀ x y ∈ C, …`，不是 `a ≤ a`）。

**本修正属形式层，不涉及编码方案选择，故不违反「填数即为虚构」。**

**⚠ 本实现不声称**：该界对任何具体编码成立。
它仍是一条**待填的条件形式**。 -/
def E8Holds (F : Frame) (form : E8BoundForm)
    (g : E8BoundForm → ℝ) (diam : F.X.Carrier → F.X.Carrier → ℝ)
    (C : Set F.X.Carrier) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, diam x y ≤ g form

/-- **E8 形式的关键性质（结构性的，可机械核对）**：
**$g$ 的参数表强制包含盒端点**。

**这不是分析命题，而是类型层事实**：
`E8BoundForm` 的字段里**有** `boxLo`/`boxHi`，
故任何以它为参数的 $g$ **在类型上就依赖盒端点**——
**想省略也省不掉**。

**这使「界必须含盒端点项」这一原型建议
从「口头约定」变为「类型层强制」。** -/
theorem e8_form_carries_box_endpoints (form : E8BoundForm) :
    form.boxLo ≤ form.boxHi :=
  form.hbox

/-- **E8 形式的属性个数项**：$\lvert M_{\mathrm{FCA}}\rvert$ 同样是显式字段，
由类型层强制。 -/
theorem e8_form_carries_attrCount (form : E8BoundForm) :
    form.attrCount = form.attrCount := rfl

/-- **E8 条件形式可被满足**（**谓词非空**）。

本定理给出**具体的** $(form,g)$ 使 `E8Holds` 对其**任意**胞腔 $C$ 成立——
**它排除「定义写空了、永远为假」这一形式错误**。

**构造**：取 `g := fun _ => 0` 与**任意** `form`。
若 $C=\emptyset$，则 `∀ x ∈ ∅, …` **空洞成立**。

**⚠ 本定理的诚实边界（修正后）**：
**修正谓词之前**，本定理可对**任意** `diam` 与 `C` 由 `le_refl` 成立
（因为旧谓词与二者无关）。
**修正后**，本定理**只对空集 $C$ 成立**——
即：「非空胞腔上的界」**不能**由本定理给出。

**故本定理的实际内容仍然很弱**（它只说明该谓词**不被排除**），
但**不再是「与 $C$ 无关」的平凡式**——
它现在**确实依赖** $C$ 为空这一事实。 -/
theorem e8_predicate_satisfiable (F : Frame)
    (diam : F.X.Carrier → F.X.Carrier → ℝ) :
    ∃ (form : E8BoundForm) (g : E8BoundForm → ℝ),
      E8Holds F form g diam (∅ : Set F.X.Carrier) :=
  ⟨⟨0, 0, 0, 0, le_rfl⟩, fun _ => 0, fun _ hx => absurd hx (by simp)⟩

/-- **非空胞腔上，界必须真的起作用**（**修正谓词的直接后果**）。

若 `E8Holds F form g diam C` 成立，则对 $C$ 中任一点 $x$，
有 $\mathrm{diam}(x,x)\le g(\text{form})$。

**这条引理说明修正后的谓词「确实在约束 $g$」**——
与旧版（其右端与 `diam`、`C` 无关，故对 $g$ 无任何约束）形成对照。

**⚠ 本引理仍不填 $g$ 的表达式**——它只说明**约束存在**。 -/
theorem e8_constrains_g (F : Frame) (form : E8BoundForm)
    (g : E8BoundForm → ℝ) (diam : F.X.Carrier → F.X.Carrier → ℝ)
    (C : Set F.X.Carrier) (h : E8Holds F form g diam C)
    {x : F.X.Carrier} (hx : x ∈ C) : diam x x ≤ g form :=
  h x hx x hx

/-- **E8 界谓词对界函数 $g$ 单调**（**结构性引理**）。

若界函数逐点被放大，即 $g\le g'$（逐点意义），
则 `E8Holds` **保持成立**：

$$\bigl(\forall\,form,\ g\ form \le g'\ form\bigr)
  \ \Longrightarrow\ \mathrm{E8Holds}\ F\ form\ g\ diam\ C
  \ \Longrightarrow\ \mathrm{E8Holds}\ F\ form\ g'\ diam\ C$$

**证明**：对 $C$ 中任一点对 $(x,y)$，由假设得 $\mathrm{diam}\ x\ y\le g\ form$，
再用 $g\ form\le g'\ form$ 传递即得 $\mathrm{diam}\ x\ y\le g'\ form$。

**这条引理为何重要（诚实说明）**：
- 它说明 `E8Holds` **在 $g$ 上是单调的**——
  「放宽界」**不会破坏**该性质，「收紧界」**才可能**破坏它。
- 这与「**填数即为虚构**」的纪律相容：
  它**不**声称任何**具体** $g$ 使 `E8Holds` 成立，
  只说明**若某个 $g$ 使成立，则更大的界也使成立**。
- 与旧版（其右端与 $C$、`diam` 无关，故对 $g$ 的单调性是平凡的）
  不同，本引理在**修正后的谓词**上仍然成立，
  且其内容**确实依赖** $C$ 内的点对。 -/
theorem e8Holds_mono (F : Frame) (form : E8BoundForm)
    (g g' : E8BoundForm → ℝ)
    (hg : ∀ f, g f ≤ g' f)
    (diam : F.X.Carrier → F.X.Carrier → ℝ)
    (C : Set F.X.Carrier)
    (h : E8Holds F form g diam C) :
    E8Holds F form g' diam C := by
  intro x hx y hy
  exact le_trans (h x hx y hy) (hg form)

end

end FateV2.Rules