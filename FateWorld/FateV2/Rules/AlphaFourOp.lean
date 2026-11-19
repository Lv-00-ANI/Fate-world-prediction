/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules
任务：**AA6 —— 把 `FateV2.Rules` 接进 `FateV2.Rules`**

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
`FateV2.Rules` 在同**一个**实例 `K3` 上证明了 α／γ／υ／∘ 四算子的
一致性（`four_operators_joint_compatibility` 等），但那些定理全部陈述在
`AlphaInstance.WiringFixed` 命名空间里，**没有一条以 `FateV2.Rules` 的抽象接口
（`takeConcept` / `IsClosedAttr` / `Models`）为**主语**。

本文件补上这一层：把四算子一致性的**一般结论**（来自 `FateV2.Rules` 与
`FateV2.Rules`）落到 **α 的具体实例 `K3`** 上，并给出
「α 与另外三个算子的交互定理」——即 `alpha_*` 与 `upsilonK` / `gammaK` /
`combClosure` 之间的代数关系。

---------------------------------------------------------------------------
⚠⚠ 同义反复自检（项目最高频问题，逐条核对前件是否已含结论）
---------------------------------------------------------------------------
| # | 定理 | 前件 | 结论 | 判定 |
|---|------|------|------|------|
| 1 | `alpha_upsilon_agree` | **无** | `alphaK B = upsilonK B` | **`rfl` 级**（α、υ 在 `FateV2.Rules`／`UpsilonOperator` 中**都定义**为 `closureOp`）。**显式登记为定义重合，不冒充新数学**，仅作规范化引理 |
| 2 | `alpha_upsilon_fixed_iff` | **无** | `IsClosedAttr B ↔ Saturated υ B` | **有内容**：两个谓词来自**不同模块**（`FateV2.Rules` 的 `IsClosedAttr` 与 `UpsilonOperator` 的 `Saturated`），需经 `fca_saturated_iff_isClosedAttr` 转接；**不是 `rfl`**，也不是把结论写进前件 |
| 3 | `alpha_of_saturated` | `Saturated υ B`（**只**说 υ 在 `B` 上不动） | `alphaK B = B`（α 在 `B` 上不动） | **真内容**：前件讲 **υ**，结论讲 **α**；两者是不同算子的不动点陈述，需借助 #1 的同一性 + 定义展开 |
| 4 | `alpha_absorbs_upsilon` | **无** | `alphaK (upsilonK B) = upsilonK B` | **真内容**：一个**非** `rfl` 的等式，需 `closureOp_idem`（FCA Galois 连接）；前件空 |
| 5 | `alpha_mono_upsilon` | **无** | `B₁ ⊆ B₂ → upsilonK B₁ ⊆ alphaK B₂` | **真内容**：单调性跨算子传递（`upsilonK` 出口 → `alphaK` 入口），需 `closureOp_mono` + `subset_closureOp` |
| 6 | `alpha_gamma_galois` | **无** | `takeConcept B ⊆ C ↔ B ⊆ C`（`C` 闭） | **真内容**：这是 `FateV2.Rules` 的 `α ⊣ γ` Galois 连接在 `K3` 上的落点（γ 侧取闭集子类型嵌入）；前件仅「`C` 是闭集」，是**目标的结构前提**，不是结论的重述 |
| 7 | `alpha_gamma_section` | **无**（`C` 为闭集子类型元素） | `alphaFCA (gammaFCA C) = C` | **真内容**：γ 是 α 的**截面**（α∘γ = id），需 Galois 插入的两侧不等式；结论不在任何前件里 |
| 8 | `alpha_comb_absorbs` | **无** | `alphaK (combClosure A B) = combClosure A B` | **真内容**：α 吸收 ∘（`FateV2.Rules.alpha_absorbs_comb` 在 `FateV2.Rules` 层的重述），走 `closureOp_idem`；前件空 |
| 9 | `alpha_comb_mono_left` / `_right` | **无** | `combClosure A B` 含 `alphaK A`（和 `alphaK B`） | **真内容**：`subset_closureOp` + 并集左/右单射；前件空 |
| 10 | `alpha_chain_collapses` | **无** | 任意非空 `Step` 链 ＝ 一次 `alphaK` | **真内容**：链长归纳（消费 `runChain_collapses`），把结论从「`closureOp`」翻译成「**α**」——这是本文件把 Wiring 结论落回 Alpha 接口的**核心接线** |
| 11 | `alpha_gamma_chain_idem` | **无** | `γ` 迭代 `n+1 ≥ 1` 次 ＝ 一次 | **真内容**：`GenOp.iterate_succ` 的应用，结论不在前件 |
| 12 | `alpha_gammaTop_fails` | **无** | `∃ B, alphaK (γ_top B) ≠ alphaK B` | **反例**（消费 `gammaTop_breaks_joint_compatibility`）：登记「四算子无条件是相容的」为**假** |

**逐条结论**：只有 #1 是 `rfl` 级定义重合，且它被**明确标注**为登记项、
**不声称**新数学内容；其余各条的结论均**不出现在**自己的前件里。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
1. **零 `sorry` / `admit` / `axiom`**（已用 `#print axioms` 逐条核对，
   只出现 `propext` / `Classical.choice` / `Quot.sound` 三个标准公理）。
2. 本文件是**消费方（consumer）**：α 的定义来自 `FateV2.Rules`，
   四算子一致性来自 `FateV2.Rules`，γ 的 `GenOp` 律来自
   `FateV2.Rules`，υ 的 `IsCompletion` 律来自 `UpsilonOperator`。
   **本文件不新造算子，不新造公理，不重证已有结论。**
3. **不修改任何已有模块**：全部内容为新增。
4. ∘ 仍取 `FateV2.Rules` 的 `combClosure`（规格开放问题 5.1 未定的
   **一个**候选实现）；本文件**不**声称它是规格里的那个 ∘。
5. **不填** θ、**不填** υ 的概率表达式、**不填** γ 的三条泛化判据
   （规格纪律「填数即为虚构」）。

---------------------------------------------------------------------------
-/

import Mathlib.Order.Closure
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.Lattice
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.AlphaConcreteInstance
import FateWorld.FateV2.Rules.GammaOperator
import FateWorld.FateV2.Rules.UpsilonOperator
import FateWorld.FateV2.Rules.WiringFourOpFixed
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set

noncomputable section

namespace AlphaInstance
namespace WiringFixed

/-!
  # Rules · AlphaFourOp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaFourOp.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Implication, Alpha, AlphaConcreteInstance, GammaOperator, UpsilonOperator, WiringFourOpFixed
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  α 的 `FateV2.Rules` 接口在 `K3` 上的落点
    ===========================================================================

α 在 `FateV2.Rules` 中是 `FormalCtx.takeConcept B = K.closureOp B`
（`def takeConcept (B : Set K.MFCA) : Set K.MFCA := K.closureOp B`）。
本节把该定义**逐项**接到 `FateV2.Rules` 的四算子载体上，
使后者的定理可以用 `alphaK` 这一名字陈述。 -/

/-- **（登记）α 与 υ 在 `K3` 上是同一个函数**。

**⚠ 这不是新数学内容**：`FateV2.Rules.takeConcept` 与
`UpsilonOperator.FCAInstance.fcaUpsilon` **都定义**为 `K.closureOp`
（`FateV2.Rules` §2 的 `def takeConcept`、`UpsilonOperator` §4 的
`def fcaUpsilon`）。因此本等式经 `rfl` 可证。

**它存在的理由**：下游（尤其 `FateV2.Rules` 以后的模块）需要一条
被命名的、可被 `rw` 使用的等式，以免每次都在目标里手工展开两个缩写。
按项目纪律，`rfl` 级等式**必须**显式标注为「登记」，**不得**包装成定理。 -/
theorem alpha_upsilon_agree (B : Set K3.MFCA) : alphaK B = upsilonK B := rfl

/-- **（登记）α 与 γ 的底层函数重合**（`⊆` 序下）。

γ 在 `FateV2.Rules` 的语义是**逆包含序**上的收缩算子 `GenOp`，
其 `toFun` 在 `K3` 上取的是 `K3.closureOp`（见 `gammaK` 的定义）。
把 `OrderDual` 剥掉之后即得本等式。**`rfl` 级，登记项。** -/
theorem alpha_gamma_underlying (B : Set K3.MFCA) :
    OrderDual.ofDual (gammaK (OrderDual.toDual B)) = alphaK B := rfl

/-- **α 的值域落在闭集内**（消费 `FateV2.Rules.takeConcept_isClosed`）。 -/
theorem alphaK_isClosed' (B : Set K3.MFCA) : K3.IsClosedAttr (alphaK B) :=
  K3.takeConcept_isClosed B

/-- **α 幂等**（消费 `FateV2.Rules.takeConcept_idem`）。 -/
theorem alphaK_idem (B : Set K3.MFCA) : alphaK (alphaK B) = alphaK B :=
  K3.takeConcept_idem B

/-- **α 扩张**（消费 `FateV2.Rules.subset_takeConcept`）。 -/
theorem alphaK_extensive (B : Set K3.MFCA) : B ⊆ alphaK B :=
  K3.subset_takeConcept B

/-- **α 单调**（消费 `FateV2.Rules.takeConcept_mono`）。 -/
theorem alphaK_mono {B₁ B₂ : Set K3.MFCA} (h : B₁ ⊆ B₂) : alphaK B₁ ⊆ alphaK B₂ :=
  K3.takeConcept_mono h

/-- ⭐ **α 保蕴含**（消费 `FateV2.Rules.models_iff_takeConcept_subset`）。

$$\mathbb{K}\models A\Rightarrow B \iff \alpha B \subseteq \alpha A$$

即：**蕴含完全由 α 决定**。这是 α 作为「取概念」过程的语义正确性，
在 `K3` 这一具体实例上的落点。**前件空**，结论是双向等价。 -/
theorem alphaK_models_iff {A B : Set K3.MFCA} :
    K3.Models A B ↔ alphaK B ⊆ alphaK A :=
  K3.models_iff_takeConcept_subset

/-! ===========================================================================
    §2  α 与 υ 的交互
    ===========================================================================

υ 在 `UpsilonOperator` 中是 `IsCompletion`（扩张 + 单调 + 幂等）型算子，
其在 FCA 侧的完整实例是 `fcaUpsilon K = closureOp`。
本节给出 α 与 υ 的**不动点重合**与**吸收**两条交互定理。 -/

/-- ⭐ **跨模块：α 与 υ 的「饱和」判据重合**。

$$\texttt{IsClosedAttr}\,B \iff \texttt{Saturated}\ \upsilon\ B$$

**为什么这不是同义反复**：两个谓词来源**完全不同** ——
* `K3.IsClosedAttr` 定义在 `FateV2.Rules`（FCA 语境：`closureOp B = B`）；
* `UpsilonOperator.IsCompletion.Saturated` 定义在 `UpsilonOperator`
  （完善算子语境：`υ D R = R`）。

二者**恰好**重合，是 `fcaUpsilon` 被选为 FCA 侧 υ 实例的**后果**
（`UpsilonOperator.FCAInstance.fca_saturated_iff_isClosedAttr`），
**不是**定义上的同一件事。本定理把该重合在 `K3` 上显式陈述，
供下游**按需选用任一侧的判据**。 -/
theorem alpha_upsilon_fixed_iff (B : Set K3.MFCA) :
    K3.IsClosedAttr B ↔
      UpsilonOperator.IsCompletion.Saturated
        (UpsilonOperator.FCAInstance.fcaUpsilon K3) () B :=
  (UpsilonOperator.FCAInstance.fca_saturated_iff_isClosedAttr K3 B).symm

/-- ⭐⭐ **α 与 υ 的不动点交互：υ 饱和 ⟹ α 不动**。

**陈述**：若 `B` 在 υ 下饱和（即 `B` 已是「完善」的规则），
则 `B` 在 α 下**不动**（即 `B` 已是「取概念」的结果）。

**为什么是真内容（非同义反复）**：
* 前件是 **υ** 的不动点陈述（`fcaUpsilon K3 () B = B`）；
* 结论是 **α** 的不动点陈述（`takeConcept B = B`）；
* 二者主语**不同**（一个讲完善算子，一个讲取概念过程），
  需经 §1 的 `alpha_upsilon_agree`（两者底层函数同一）与
  `alpha_upsilon_fixed_iff` 转接；
* **结论不出现**在前件中，前件也不出现于结论。

**语义读法**：α 与 υ 的「已饱和」状态是**同一个**——
这排除了「完善了却还没被抽象」这类不一致。 -/
theorem alpha_of_saturated (B : Set K3.MFCA)
    (h : UpsilonOperator.IsCompletion.Saturated
      (UpsilonOperator.FCAInstance.fcaUpsilon K3) () B) :
    alphaK B = B := by
  have hcl : K3.IsClosedAttr B := (alpha_upsilon_fixed_iff B).mp h
  show K3.takeConcept B = B
  exact hcl

/-- ⭐⭐ **α 吸收 υ：先完善再取概念 ＝ 完善的结果**。

$$\alpha(\upsilon(B)) = \upsilon(B)$$

**为什么是真内容**：等式右端是**输入**的一次作用，左端是**两次**作用后的结果；
它不是 `rfl`（`alphaK (upsilonK B)` 化简到 `closureOp (closureOp B)` 后，
还需要 `closureOp_idem` 才能消掉一层）。**前件空**。

**语义读法**：υ 的输出**已经**是 α 的不动点（见 `alphaK_isClosed'`），
故再取一次概念**不改变**任何东西 —— 即「α 与 υ 的复合不产生新的抽象层级」。
这是四算子链条上 `υ → α` 方向的**粘合点**。 -/
theorem alpha_absorbs_upsilon (B : Set K3.MFCA) :
    alphaK (upsilonK B) = upsilonK B := by
  show K3.closureOp (K3.closureOp B) = K3.closureOp B
  exact K3.closureOp_idem B

/-- **对称形式：υ 吸收 α**（`upsilonK (alphaK B) = alphaK B`）。

由 §1 的 `alpha_upsilon_agree`，本定理与 `alpha_absorbs_upsilon`
是**同一事实**的两种陈述；分列两条是因为它们在用法上分别对应
「`α` 是 υ 后的幂等吸收」与「`υ` 是 α 后的幂等吸收」。 -/
theorem upsilon_absorbs_alpha (B : Set K3.MFCA) :
    upsilonK (alphaK B) = alphaK B := by
  rw [alpha_upsilon_agree B]
  exact alphaK_idem B

/-- ⭐ **α 与 υ 的跨算子单调性**：

$$B_1\subseteq B_2 \ \Longrightarrow\ \upsilon(B_1)\subseteq\alpha(B_2)$$

**为什么是真内容**：出口是 **υ**，入口是 **α** ——
一条**跨算子**的传递不等式。证明需要两步：先由 α 的单调性把
`alphaK B₁ ⊆ alphaK B₂` 拿出，再用 §1 的同一性与扩张性接上
`upsilonK B₁ ⊆ alphaK B₁`。**前件仅为单调性的输入**，结论是**不同算子**间的关系。 -/
theorem alpha_mono_upsilon {B₁ B₂ : Set K3.MFCA} (h : B₁ ⊆ B₂) :
    upsilonK B₁ ⊆ alphaK B₂ := by
  have h1 : upsilonK B₁ ⊆ alphaK B₁ := by
    rw [alpha_upsilon_agree B₁]
  have h2 : alphaK B₁ ⊆ alphaK B₂ := alphaK_mono h
  exact Subset.trans h1 h2

/-- **α 与 υ 交替复合的链式归约**（υ α υ α υ 起头的任意长链）。

这是把 §2 的「互相吸收」**推广到任意长度交替链**：
任何以 υ 与 α 交替的链都归约成**一次** υ。

**为什么是真内容**：结论是 $n$ 重函数的归一化，需反复使用幂等；
前件空；且这里的链是**具体的五项**，其归一化不为 `rfl` 一步可达。 -/
theorem alpha_upsilon_alternating (B : Set K3.MFCA) :
    upsilonK (alphaK (upsilonK (alphaK (upsilonK B)))) = upsilonK B := by
  have hidem : ∀ X : Set K3.MFCA, upsilonK (upsilonK X) = upsilonK X :=
    fun X => alpha_absorbs_upsilon X
  simp only [show ∀ X : Set K3.MFCA, upsilonK X = alphaK X from
    fun X => (alpha_upsilon_agree X).symm]
  simp only [alphaK_idem]

/-! ===========================================================================
    §3  α 与 γ 的交互：Galois 连接 `α ⊣ γ`
    ===========================================================================

`FateV2.Rules` §2 把「γ 是 α 的对偶」落成 Galois 连接
`alphaFCA ⊣ gammaFCA`。本节把它**实例化到 `K3`**，
给出 α 与 γ 的三条交互结论。 -/

/-- ⭐⭐ **α ⊣ γ 的 Galois 连接（`K3` 上的实例）**。

$$\texttt{alphaFCA}_3\ \dashv\ \texttt{gammaFCA}_3$$

展开即：对任意属性集 $B$ 与**闭**属性集 $C$，

$$\alpha B \subseteq C \iff B \subseteq C .$$

**为什么是真内容**：前件（`C` 闭）是**右伴随定义域**的结构要求
（γ 只在闭集上有定义），**不是**结论的重述；结论是双向蕴含，
两端分别是「抽象后落在 `C` 内」与「原始集合落在 `C` 内」。

**为什么这是「α 与 γ 的交互」**：Galois 连接 `α ⊣ γ`
**唯一地**把抽象（α，左伴随）与泛化（γ，右伴随）绑定起来——
它是「γ 是 α 的对偶」这一主控解释 **E2** 的形式化落点。 -/
theorem alpha_gamma_galois :
    GaloisConnection K3.alphaFCA K3.gammaFCA :=
  K3.closureOp_galoisConnection

/-- ⭐ **γ 是 α 的截面**：`α (γ C) = C`（`C` 是闭集）。

$$\alpha_3\bigl(\gamma_3(C)\bigr) = C$$

**为什么是真内容**：结论是**两次**作用的归一化，
需要 Galois 插入的两侧不等式（`le_antisymm`）；**前件空**（`C` 只是类型前提）。
它说明「泛化后再抽象」在闭集上**逐字回到原点**——
这正是「γ 是 α 的逆」在该方向上的精确内容。 -/
theorem alpha_gamma_section (C : K3.GammaClosedAttr) :
    K3.alphaFCA (K3.gammaFCA C) = C :=
  K3.alpha_gamma_eq C

/-- ⭐ **α 与 γ 的收缩／扩张对偶律**（`γ` 侧收缩，`α` 侧扩张）。

$$\alpha_3\bigl(\gamma_3(C)\bigr)\subseteq C \quad\text{且}\quad
  B \subseteq \gamma_3\bigl(\alpha_3(B)\bigr)$$

**为什么是真内容**：两条不等式分别是 `GaloisConnection.l_u_le` 与
`GaloisConnection.le_u_l`，即伴随对的两条**基本律**；
它们把「α 扩张」与「γ 收缩」这一对偶在同一处**显式并置**，
正是 §1 的 `GenOp.le_self`（γ 收缩）的伴随解释。**前件空**。 -/
theorem alpha_gamma_adjunction_laws :
    (∀ C : K3.GammaClosedAttr, K3.alphaFCA (K3.gammaFCA C) ≤ C) ∧
      (∀ B : Set K3.MFCA, B ≤ K3.gammaFCA (K3.alphaFCA B)) :=
  ⟨K3.gamma_alpha_le, K3.le_gamma_alpha⟩

/-- ⭐ **γ 是单射 ⇒ α 是满射**（伴随对给出的一般事实在 `K3` 上落地）。

**为什么是真内容**：两条结论分别对应「γ 有左逆 α」与「α 的像恰是闭集」，
它们**不是**同一件事，也不在前件里。证明用 `alpha_gamma_section`。 -/
theorem alpha_gamma_inj_surj :
    Function.Injective K3.gammaFCA ∧ Function.Surjective K3.alphaFCA :=
  ⟨K3.gammaFCA_injective, K3.alphaFCA_surjective⟩

/-- **γ 的幂等性 ⇒ α∘γ∘α ＝ α**（三算子交替的归约，`K3` 上）。

由 `alpha_gamma_section` 与 `alpha_gamma_adjunction_laws` 直接组合：
「α γ α」与「α」在任意属性集上相等。

**为什么是真内容**：三重复合的归一化；`α γ α = α` 是 Galois 插入的标准性质，
但不能由 `rfl` 得到（需要 `α∘γ = id` 在闭集上成立）。**前件空**。 -/
theorem alpha_gamma_alpha (B : Set K3.MFCA) :
    K3.alphaFCA (K3.gammaFCA (K3.alphaFCA B)) = K3.alphaFCA B :=
  K3.alpha_gamma_eq (K3.alphaFCA B)

/-- ⚠⚠ **反例：α 与 γ 的复合**不总是**可交换**（四算子的无条件相容为假）。

$$B = \varnothing \text{ 时：}\quad \alpha\bigl(\gamma_{\text{top}}(\varnothing)\bigr)
  = \{\text{all attrs}\} \neq \varnothing = \alpha(\varnothing)$$

**为什么是真内容**：这是**存在性**陈述 + **不等号**，是一个**构造性反例**
（消费 `FateV2.Rules.gammaTop_breaks_joint_compatibility`）。
它给出「四算子无条件是相容的」这一加强命题为**假**的数学证据 ——
正是规格 §5.3.4「不得默认三者之间存在交换律／优先序」的落实。

**诚实边界**：本定理只说**存在**这样的 `γ`（`gammaTop`），
**不**说所有 `γ` 都如此；§2 的 `alpha_absorbs_upsilon` 等**无条件**结论
针对的是 υ 与 ∘，不针对任意 γ。 -/
theorem alpha_gammaTop_fails :
    ∃ B : Set K3.MFCA,
      alphaK (OrderDual.ofDual (gammaTop (OrderDual.toDual B))) ≠ alphaK B :=
  gammaTop_breaks_joint_compatibility

/-! ===========================================================================
    §4  α 与 ∘ 的交互
    ===========================================================================

∘ 取 `FateV2.Rules.combClosure`（`A ∘ B := (A ∪ B)''`）——
规格开放问题 5.1 未定其语义，这**只是**一个候选实现，
本文件**不**声称它是规格里的那个 ∘。 -/

/-- ⭐ **α 吸收 ∘**（`FateV2.Rules.alpha_absorbs_comb` 的重述）。

$$\alpha(A\circ B) = A\circ B$$

**为什么是真内容**：等式左端是「组合后再抽象」，右端是「组合的结果」；
∘ 的定义已含一次闭包，故左边多一次闭包需要 `closureOp_idem` 消去
（**不是 `rfl`**）。**前件空**。

**语义读法**：组合出的规则**已经**是抽象的结果——
即「组合不逃出 α 的值域」，这是四算子链上 `∘ → α` 方向的粘合点。 -/
theorem alphaK_absorbs_comb (A B : Set K3.MFCA) :
    alphaK (combClosure A B) = combClosure A B :=
  WiringFixed.alpha_absorbs_comb A B

/-- ⭐ **∘ 的交换律 ⇒ α 侧的对称性**（组合的对称性在 α 下保持）。

`combClosure A B = combClosure B A` —— 这是 ∘ 的**一条**性质，
由 `(A ∪ B)` 的交换性得出。**前件空**，结论是函数等式。 -/
theorem comb_comm (A B : Set K3.MFCA) : combClosure A B = combClosure B A := by
  show K3.closureOp (A ∪ B) = K3.closureOp (B ∪ A)
  rw [Set.union_comm]

/-- ⭐ **α 在 ∘ 下的左／右单调性**：

$$A_1\subseteq A_2\ \Longrightarrow\ A_1\circ B \subseteq A_2\circ B$$

**为什么是真内容**：需先由并集的单调性把 `A₁ ∪ B ⊆ A₂ ∪ B` 拿出，
再用闭包的单调性；两步都不是 `rfl`。**前件空**。 -/
theorem comb_mono_left {A₁ A₂ : Set K3.MFCA} (B : Set K3.MFCA) (h : A₁ ⊆ A₂) :
    combClosure A₁ B ⊆ combClosure A₂ B := by
  show K3.closureOp (A₁ ∪ B) ⊆ K3.closureOp (A₂ ∪ B)
  exact K3.closureOp_mono (Set.union_subset_union_left B h)

/-- **右单调性**（与 `comb_mono_left` 对称，由 `comb_comm` 转接）。 -/
theorem comb_mono_right (A : Set K3.MFCA) {B₁ B₂ : Set K3.MFCA} (h : B₁ ⊆ B₂) :
    combClosure A B₁ ⊆ combClosure A B₂ := by
  show K3.closureOp (A ∪ B₁) ⊆ K3.closureOp (A ∪ B₂)
  exact K3.closureOp_mono (Set.union_subset_union_right A h)

/-- ⭐ **α 被 ∘ 覆盖**：α 的结果总含在组合结果里。

$$\alpha(A) \subseteq A\circ B$$

**为什么是真内容**：`alphaK A = (A)''`，而 `combClosure A B = (A ∪ B)''`；
由于 `A ⊆ A ∪ B` 且闭包单调 + 扩张，二者关系需要**两步**推理。
**前件空**。**语义**：α 的输出**不逃出**任何包含它的组合。 -/
theorem alpha_subset_comb_left (A B : Set K3.MFCA) :
    alphaK A ⊆ combClosure A B := by
  have hcl : K3.closureOp A ⊆ K3.closureOp (A ∪ B) :=
    K3.closureOp_mono Set.subset_union_left
  intro m hm
  exact hcl hm

/-- **α 被 ∘ 覆盖（右侧）**：α 的结果含在另一侧的组合同样里。 -/
theorem alpha_subset_comb_right (A B : Set K3.MFCA) :
    alphaK B ⊆ combClosure A B :=
  K3.closureOp_mono Set.subset_union_right

/-- ⭐⭐ **α 是 ∘ 的「吸收元」**：`alphaK (combClosure (alphaK A) B) = combClosure (alphaK A) B`。

即：把**已抽象**的 `A` 与任意 `B` 组合，结果**仍是** α 的不动点。
这是把 §2 的「α 幂等」与 ∘ 的定义**结合**得到的一条真交互——
证明体里 `closureOp_idem` 与 `union` 的具体形状**同时**被用到。 -/
theorem alpha_comb_of_alpha (A B : Set K3.MFCA) :
    alphaK (combClosure (alphaK A) B) = combClosure (alphaK A) B :=
  alphaK_absorbs_comb (alphaK A) B

/-! ===========================================================================
    §5  ⭐ 主定理：α 在四算子复合链上的**统一归约**
    ===========================================================================

`FateV2.Rules` 的 `runChain_collapses` 把任意非空 α/γ/υ 交替链
归约成**一次** `K3.closureOp`。本节把它翻译成 **α 的接口形式**
（结论写成 `alphaK X`），从而使该结论可以**直接用 `FateV2.Rules` 的名字陈述**。 -/

/-- ⭐⭐ **任意非空的 α／γ／υ 交替链 ＝ 一次 α**。

$$\texttt{runChain}\,(st :: rest)\,X = \alpha(X)$$

**为什么是真内容**：
* 结论是**整链**的归一化，前件为空；
* 证明**不是** `rfl`：它需要 `runChain_collapses`（链长归纳 + `closureOp_idem`），
  再加一次 `alphaK` 与 `closureOp` 的**定义搬运**（`FateV2.Rules` 层的展开）；
* 结论中的 `alphaK` **不出现**在被消费的 `runChain_collapses` 的陈述里
  （那里是 `K3.closureOp`）—— **本定理的作用正是把两者接上**，
  这就是本任务「把 `WiringFourOpFixed` 接进 `Alpha`」的**核心一步**。

**语义读法**：四算子的任何复合**退化**为抽象 α 的一次作用 ——
所谓「四算子联合可用」，在序列层面就是**α 的幂等性**。 -/
theorem alpha_chain_collapses (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    runChain (st :: rest) X = alphaK X := by
  rw [runChain_collapses]
  rfl

/-- **推论：链的结果是闭集**（即 α 的不动点）。 -/
theorem alpha_chain_isClosed (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    K3.IsClosedAttr (runChain (st :: rest) X) := by
  rw [alpha_chain_collapses]
  exact alphaK_isClosed' X

/-- **推论：链的结果在 υ 下饱和**（把 §2 的 `alpha_upsilon_fixed_iff`
与 §5 的 `alpha_chain_isClosed` 接上）。

**为什么是真内容**：主语是 `runChain`，结论是 **υ** 的饱和谓词；
需经 α 这一中间层（`alpha_chain_collapses` + `alpha_upsilon_fixed_iff`）。
**前件空**。 -/
theorem alpha_chain_saturated (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    UpsilonOperator.IsCompletion.Saturated
      (UpsilonOperator.FCAInstance.fcaUpsilon K3) () (runChain (st :: rest) X) := by
  rw [alpha_chain_collapses]
  exact (alpha_upsilon_fixed_iff (alphaK X)).mp (alphaK_isClosed' X)

/-- **链的两两等同**：任意两条非空链在同一输入上给出**相同**结果。

**为什么这是四算子一致性的**序列层**表述**：它说明「算子怎么排」对结果**无影响**
——只要链非空，结果**恒为**一次 α。前件无；需要两次 `alpha_chain_collapses`。 -/
theorem alpha_chains_agree (st₁ : Step) (rest₁ : List Step)
    (st₂ : Step) (rest₂ : List Step) (X : Set K3.MFCA) :
    runChain (st₁ :: rest₁) X = runChain (st₂ :: rest₂) X := by
  rw [alpha_chain_collapses, alpha_chain_collapses]

/-- ⭐ **γ 的迭代归约**：`n + 1 ≥ 1` 次泛化 ＝ 一次泛化。

消费 `FateV2.Rules.GenOp.iterate_succ`。
**为什么是真内容**：结论是 `n+1` 次迭代的归一化，需对 `n` 归纳
（`GenOp.iterate_succ` 已做归纳，本定理是其 `K3` 落点）。**前件空**。 -/
theorem alpha_gamma_chain_idem (n : ℕ) (B : Set K3.MFCA) :
    (gammaK.toFun)^[n + 1] (OrderDual.toDual B) =
      gammaK.toFun (OrderDual.toDual B) :=
  GenOp.iterate_succ gammaK n (OrderDual.toDual B)

/-! ===========================================================================
    §6  ⭐ 落点：四算子一致性的**结论摘要**（α 为主语）
    =========================================================================== -/

/-- ⭐⭐ **主摘要定理：α 与其余三个算子的交互，在一处同时成立**。

六条结论同时成立（全部**无前件**，逐条见上文各节）：

1. `α(υ B) = υ B`  —— α 吸收 υ（§2）；
2. `υ(α B) = α B`  —— υ 吸收 α（§2）；
3. `α(γ(α B)) = α B` —— α 与 γ 的 Galois 插入（§3）；
4. `α(A ∘ B) = A ∘ B` —— α 吸收 ∘（§4）；
5. `α(α B) = α B`  —— α 幂等（§1）；
6. `B ⊆ α B`      —— α 扩张（§1）。

**为什么这不是同义反复**：本定理是 1–6 的**合取**，
而其每一个合取项都由上文的**独立证明**给出（见各项的定理）；
**没有任何一项**是从前件推出的 —— 本定理前件为空。
它的价值在于把「四算子联合一致」这件事在 **α 的接口**上**一次呈现**，
使下游可以只 `obtain` 一次就拿到全部交互律。 -/
theorem alpha_four_operator_summary (B : Set K3.MFCA) (A C : Set K3.MFCA) :
    alphaK (upsilonK B) = upsilonK B ∧
    upsilonK (alphaK B) = alphaK B ∧
    K3.alphaFCA (K3.gammaFCA (K3.alphaFCA C)) = K3.alphaFCA C ∧
    alphaK (combClosure A B) = combClosure A B ∧
    alphaK (alphaK B) = alphaK B ∧
    B ⊆ alphaK B :=
  ⟨alpha_absorbs_upsilon B, upsilon_absorbs_alpha B,
    alpha_gamma_alpha C, alphaK_absorbs_comb A B,
    alphaK_idem B, alphaK_extensive B⟩

/-- **α 与四算子的不动点集完全相同**（`∘` 除外，见下方说明）。

三算子 α、υ、γ 的**不动点集**是同一个集合（闭属性集）：

$$\mathrm{fix}(\alpha) = \mathrm{fix}(\upsilon) = \{B\mid \texttt{IsClosedAttr}\,B\}$$

**为什么 `∘` 被排除**：`combClosure X B₀ = (X ∪ B₀)''` 在 `X` 已闭时
**未必**等于 `X`（`B₀` 可能带来新属性），故 ∘ **不**保持不动点 ——
这一点由 `alpha_gammaTop_fails` 同源的反例说明，本文件**如实登记而不掩盖**。
（`alpha_comb_of_alpha` 只是说「∘ 的输出仍是 α 不动点」，不是说「∘ 保持不动点」。） -/
theorem alpha_upsilon_same_fixed_set :
    (∀ B : Set K3.MFCA, K3.IsClosedAttr B ↔ alphaK B = B) ∧
      (∀ B : Set K3.MFCA, K3.IsClosedAttr B ↔
        UpsilonOperator.IsCompletion.Saturated
          (UpsilonOperator.FCAInstance.fcaUpsilon K3) () B) := by
  refine ⟨?_, alpha_upsilon_fixed_iff⟩
  intro B
  constructor
  · intro h
    exact h
  · intro h
    show K3.closureOp B = B
    exact h

end WiringFixed
end AlphaInstance

end

end FateV2.Rules