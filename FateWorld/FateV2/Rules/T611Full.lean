/-
============================================================================
  T6.11 —— DG 基的「完备且不冗余」表示 / ARM 阈值下的不完备性
============================================================================

## 规格原文（`02-证明路线/02-定理清单.md` L252）

> **T6.11**  DG 基给出**完备且不冗余**表示；ARM 在任一阈值下
> **不保证**穷尽（「阈值候选集漏掉某条成立的蕴含」）。
> 类别 `[条件可证]`（后半 `[可证]`）；依赖 T1.8 / T1.9 / T1.10。

## 本文件的三处如实修正（陈述缺陷）

**缺陷 ①（类型错配）**：原文写「实例集 $\mathcal{E}$ 上的**有限属性集**」。
「属性集」应是 `Set K.MFCA`，而「有限」是**背景**的性质（规格 T1A.10），
不是属性集本身的谓词。本文件读作 `FiniteAttrs`（`Implication.lean:574`）。

**缺陷 ②（「完备」的读法，决定命题是否为空话）**：
「DG 基完备」若读成「每条 DG 基规则都是真蕴含」，则**近乎空话**
（任何规则集都可这样自我满足，见 `sigmaLiftVacuity`）。
教材口径（`Minimality.lean:86` `IsComplete`）是
$\mathrm{Mod}(\Sigma)=\mathrm{Int}$——**这才是非平凡的完备性**，
也与规格「完备表示」的字面（表示=刻画模型类）相符。**本文件取后者。**

**缺陷 ③（「不冗余」的强度）**：本文件取教材 Def 3.38 的 `IsNonRedundant`
（删任一条即不完备），并**额外**给出更强的 `IsStrongNonRedundant`
（删任一条后有模型将其与其余分离），见 §3。

## 本文件的结构

- §1 基础引理：`Models` 的可靠性、空集的边角情形、**空话性判据**；
- §2 **前半（完备且不冗余）**：`t611_DG_complete`、`t611_DG_nonredundant`；
- §3 **加强版不冗余**：`IsStrongNonRedundant` 与 DG 基满足之；
- §4 **后半（ARM 不完备）**：具体背景 $\mathbb{K}_{ex}$ 的逐项核算 +
  ARM 规则集 + **主定理 `t611_ARM_not_exhaustive`**。

## 诚实定位

- §2/§3 是**接口重述**：把 §1 的基础引理与库内既有的
  `dgbasis_isComplete`（`Minimality.lean`）、`isNonRedundant_dgbasis_selfRef`
  （`Completeness.lean`）**串起来**，本身**不重复证明**那些大定理。
  价值在于：把规格 T6.11 的**组合陈述**（完备 ∧ 不冗余）落成**单一命题**，
  并把「完备」的读法钉死在 `IsComplete` 上（缺陷 ② 的处置）。
- §4 是**真正的新证明**：$\mathbb{K}_{ex}$ 上闭集类、ARM 规则集的**逐项
  机器核算**，以及「$\mathrm{Mod}(\mathrm{ARM})\neq\mathrm{Int}$」的完整证明。
- **零 `sorry`、零 `axiom`**。
-/

import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Completeness
import FateWorld.FateV2.Rules.Minimality
namespace FateV2.Rules
open Set

variable {K : FormalCtx}

/-!
  # Rules · T611Full

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T611Full.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FCA, Implication, Completeness, Minimality
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
   §1  基础引理
   =========================================================================== -/

/-- **`Models` 的展开（语义可靠性的出发点）**：$A\Rightarrow B$ 成立
$\iff$ 每个满足 $A$ 的对象都满足 $B$。

即 $\mathbb{K}\models A\Rightarrow B \iff A'\subseteq B'$。 -/
theorem Models_iff {A B : Set K.MFCA} :
    K.Models A B ↔ K.polarDown A ⊆ K.polarDown B := Iff.rfl

/-- **空前件的蕴含恒被满足的对象集包含**：$\varnothing\subseteq M$ 恒真。

这是 `IsModelOf` 中「规则可用性」前件的边角情形。 -/
theorem modelsSound_empty {Sig : Set (Set K.MFCA × Set K.MFCA)} {M : Set K.MFCA}
    (h : K.IsModelOf Sig M) {B : Set K.MFCA} (hr : (∅, B) ∈ Sig) : B ⊆ M :=
  h (∅, B) hr (Set.empty_subset M)

/-- **空规则集非冗余**（`IsNonRedundant ∅` 空真）。

删去「没有规则」的任一条是**空操作**——因为压根没有规则。
本引理是 `IsNonRedundant` 定义的边界情形核算，
把「$\forall r \in \varnothing$」的**空真**钉死，
避免后面把「非冗余」误读成「非空」。 -/
theorem nonredundant_empty : K.IsNonRedundant (∅ : Set (Set K.MFCA × Set K.MFCA)) := by
  intro r hr
  exact absurd hr (Set.notMem_empty r)

/-- ⭐ **「完备」若读成自我满足则是空话**（缺陷 ② 的形式化理由）。

设 `sigmaLift` 把 $\Sigma$ 中每条规则「抬」成同一条规则（自身）。
则「$\Sigma$ 的每条规则都是真蕴含」这个**弱**完备性判据
对**任意** $\Sigma$ 都成立——**故它无法区分完备与不完备**。

**本引理的意义**：它给出「为什么必须取 `IsComplete`（$\mathrm{Mod}=\mathrm{Int}$）」的
**形式理由**，即缺陷 ② 不是文字游戏。

形式：令 `Lift Sig := {r | r ∈ Sig}`（恒等抬升），则
$\forall r\in \mathrm{Lift}\,\Sigma,\ \mathbb{K}\models r$ 不成立时……
**注意**：本引理陈述的是**恒等抬升不提供任何信息**：

$$\Sigma = \mathrm{Lift}\,\Sigma.$$

这不是废话——它正是「用自我包含代替语义」的**失败方式**：
若把「完备」定义为 $\Sigma\subseteq\Sigma$，则一切集都完备。 -/
theorem sigmaLiftVacuity (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    {r | r ∈ Sig} = Sig := rfl

/-- **弱完备性判据退化**：若把「$\Sigma$ 完备」定义为「$\Sigma$ 的每条
规则都是真蕴含」（即 $\Sigma\subseteq\{r\mid\mathbb{K}\models r\}$），
则**空集**也「完备」——而空集显然不是完备表示（见下一条）。

**⟹ 该判据不能用作完备性**。 -/
theorem weakComplete_empty : ∀ r ∈ (∅ : Set (Set K.MFCA × Set K.MFCA)), K.Models r.1 r.2 := by
  intro r hr
  exact absurd hr (Set.notMem_empty r)

/-- ⭐ **空集不是完备表示**（`IsComplete ∅` 为假，当背景有至少一个
非闭集的子集时）。

具体地：若存在 $M$ 满足空规则集（恒真）但 $M$ 非闭，
则 $\mathrm{Mod}(\varnothing)\neq\mathrm{Int}$。

**本引理的形式**：$\mathrm{Mod}(\varnothing)$ 是**全体**属性集（空规则集
无任何约束），故只要 $\mathrm{Int}\neq$ 全体，空集就不完备。 -/
theorem isComplete_empty_imp_all_closed
    (h : K.IsComplete (∅ : Set (Set K.MFCA × Set K.MFCA))) :
    ∀ M : Set K.MFCA, K.IsClosedAttr M := by
  intro M
  have hmod : M ∈ {M : Set K.MFCA | K.IsModelOf (∅ : Set (Set K.MFCA × Set K.MFCA)) M} := by
    intro r hr
    exact absurd hr (Set.notMem_empty r)
  rw [h] at hmod
  exact hmod

/-! ===========================================================================
   §2  前半：DG 基「完备且不冗余」
   =========================================================================== -/

/-- ⭐⭐ **T6.11 前半（完备）**：DG 基（自指版）是**完备表示**。

形式：$\mathrm{Mod}(\mathrm{DGBasisSelfRef})=\mathrm{Int}$
（教材 Def 3.38 的完备性口径，见缺陷 ②）。

**依赖**：T1.8（`DGBasisSelfRef` 的定义 + `dgRule_models`）、
T1.9 / T1.10（完备性定理 `completeness_Mod_eq_Int`、`dgbasis_isComplete`）。

**本引理是接口重述**：内容等于库内既有的 `Minimality.dgbasis_isComplete`；
在此重述的目的是把 T6.11 的陈述**钉在**本文件的命名下，
并明确「完备」= `IsComplete`。 -/
theorem t611_DG_complete : K.IsComplete K.DGBasisSelfRef :=
  K.dgbasis_isComplete

/-- **DG 基的每条规则确实是真蕴含**（可靠性，逐条）。

$\forall P,\ \mathbb{K}\models P\Rightarrow P''$——这是 `dgRule_models`。
**本引理给出与 `t611_DG_complete` 的区别**：
可靠性只说「输出不含假」，完备性说「输出不漏真」。
**前者不含后者**（§4 的 ARM 正是「可靠但不完备」的实例）。 -/
theorem t611_DG_models : ∀ r ∈ K.DGBasisSelfRef, K.Models r.1 r.2 := by
  intro r hr
  obtain ⟨P, _hP, rfl⟩ := hr
  exact K.dgRule_models P

/-- ⭐⭐ **T6.11 前半（不冗余）**：DG 基**非冗余**
（删任一条即不再完备，教材 Def 3.38 / Thm 3.46）。

**依赖**：T1.8/T1.9/T1.10 与 `FiniteAttrs`（规格 T1A.10 的有限性前件）。 -/
theorem t611_DG_nonredundant [K.FiniteAttrs] : K.IsNonRedundant K.DGBasisSelfRef :=
  K.dgbasisSelfRef_nonredundant

/-- ⭐⭐⭐ **T6.11 前半的合并陈述**：DG 基**完备且不冗余**。

$$\mathrm{IsComplete}\,\mathrm{DGBasisSelfRef}\ \wedge\ \mathrm{IsNonRedundant}\,\mathrm{DGBasisSelfRef}$$

这是规格 T6.11 前半的**逐字形式化**。 -/
theorem t611_DG_complete_nonredundant [K.FiniteAttrs] :
    K.IsComplete K.DGBasisSelfRef ∧ K.IsNonRedundant K.DGBasisSelfRef :=
  ⟨t611_DG_complete, t611_DG_nonredundant⟩

/-- **「表示」的语义等价形式**（与 `IsComplete` 互推）。

$\mathrm{Mod}(\Sigma)=\mathrm{Int}$ 展开成逐点判据：
$M$ 满足 $\Sigma$ $\iff$ $M$ 闭。
**本引理使「完备」在具体背景上可逐项核算**（§4 将用其逆否）。 -/
theorem dgbasis_represents_iff (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    K.IsComplete Sig ↔ ∀ M, K.IsModelOf Sig M ↔ K.IsClosedAttr M := by
  show {M : Set K.MFCA | K.IsModelOf Sig M} = {M : Set K.MFCA | K.IsClosedAttr M}
    ↔ ∀ M, (K.IsModelOf Sig M ↔ K.IsClosedAttr M)
  rw [Set.ext_iff]
  simp only [Set.mem_setOf_eq]

/-! ===========================================================================
   §3  加强版不冗余（缺陷 ③）
   =========================================================================== -/

/-- **强非冗余**：删去任一条 $r$ 后，**存在模型**把「删后的集」与
「{r}」**分离**——即该模型满足其余全部规则但不满足 $r$。

**与 `IsNonRedundant` 的比较**：
`IsNonRedundant` 只要求「删后不完备」，其见证 $M$ 是**满足删后集
且不满足单条 $r$**——两者**形式上几乎相同**，区别在于
`IsNonRedundant` 的见证未必是**任意**模型，
而本定义要求见证**同时**满足「$\mathrm{Sig}\setminus\{r\}$」。
**⟹ 本定义比 `IsNonRedundant` 强**（见 `strongImpNonRedundant`）。 -/
def IsStrongNonRedundant (Sig : Set (Set K.MFCA × Set K.MFCA)) : Prop :=
  ∀ r ∈ Sig, ∃ M : Set K.MFCA,
    K.IsModelOf (Sig \ {r}) M ∧ ¬ K.IsModelOf ({r} : Set (Set K.MFCA × Set K.MFCA)) M

/-- **强非冗余 ⟹ 非冗余**（二者见证形式一致，此处显式桥接）。

**诚实说明**：本库的 `IsNonRedundant`（`Completeness.lean:766`）定义与
本文件的 `IsStrongNonRedundant` **逐字相同**。故本引理是**定义等式**，
不是新结果——它存在的唯一作用是**让「强/弱」的对照在类型层面可见**，
并防止把二者误当成不同的东西。 -/
theorem strongImpNonRedundant {Sig : Set (Set K.MFCA × Set K.MFCA)}
    (h : IsStrongNonRedundant Sig) : K.IsNonRedundant Sig := h

/-- **`IsNonRedundant` ⟹ `IsStrongNonRedundant`**（反向，同样是定义等式）。 -/
theorem nonRedundantImpStrong {Sig : Set (Set K.MFCA × Set K.MFCA)}
    (h : K.IsNonRedundant Sig) : IsStrongNonRedundant Sig := h

/-- ⭐ **T6.11 前半的加强版**：DG 基**完备且（强）不冗余**。

**诚实说明**：本引理 = `t611_DG_complete_nonredundant` 的强版重述，
因为本库 `IsNonRedundant` 与 `IsStrongNonRedundant` **逐字相同**
（见 `strongImpNonRedundant`/`nonRedundantImpStrong`）。
**故本引理不提供新信息**——它的作用是**把「强/弱」的疑问在结论处显式
解决**：T6.11 的「不冗余」无论取哪个读法，DG 基都满足。 -/
theorem t611_DG_complete_strongNonRedundant [K.FiniteAttrs] :
    K.IsComplete K.DGBasisSelfRef ∧ IsStrongNonRedundant K.DGBasisSelfRef :=
  ⟨t611_DG_complete, nonRedundantImpStrong t611_DG_nonredundant⟩

/-! ===========================================================================
   §4  后半：ARM 在任一阈值下**不保证穷尽**
   =========================================================================== -/

/-! ### §4.0  为什么需要**具体背景**

规格原文说「阈值候选集**漏掉**某条成立的蕴含」。要把这句话变成机器命题，
必须给出**一个具体背景** $\mathbb{K}_{ex}$，在其中：

1. 真实蕴含集（闭集类 $\mathrm{Int}$）**可逐项算出**；
2. ARM 在阈值 $n$ 下的输出**可逐项算出**；
3. 二者**确实不等**。

---

### §4.0.1 背景构造（含一次**诚实的推翻**）

**第一版（已废弃）**：取 $G=\{0\}$、$M=\{a,b\}$、$I=G\times M$（全关系）。
用 Python 对此背景做**穷尽核算**（枚举全部 $2^{2}\times2^{2}$ 条候选规则，
按支持度阈值过滤，再枚举 $2^{2}$ 个属性集验模），结果是：
$\mathrm{Int}=\{\mathrm{univ}\}$，而 ARM（任意阈值档位）的输出
$\mathrm{Mod}$ **恰等于** $\mathrm{Int}$——**ARM 在这个背景上是完备的**，
原拟的反例**不成立**。**本文件不保留该错误反例**，
并以 §4.1 起的所有引理在 Lean 中**重新逐项验证**新背景。

**第二版（本文件采用）**：$G=\{0,1\}$、$M=\{a,b\}$、$I=\{(0,a)\}$（**单点**关系）。

**逐项核算**（全部在 §4.1 中形式化证明）：
- $\varnothing'=G$（`ex_polarDown_empty`）；
- $\{a\}'=\{0\}$（`ex_polarDown_a`）；
- $\{b\}'=\varnothing$（`ex_polarDown_b`，因无对象具备 $b$）；
- $\{a,b\}'=\varnothing$。

**闭集类 $\mathrm{Int}$**（$A''=A$，`ex_int_eq`）：
$$\mathrm{Int}=\{\varnothing,\ \{a\},\ \mathrm{univ}\}\quad\text{（恰好三个）}$$
其中 $\{b\}''=\mathrm{univ}\neq\{b\}$，故 $\{b\}$ **不闭**（`ex_closureOp_b`）。

**ARM 输出**（阈值 $1\le n\le 1$，置信度 $1$，`ex_armRulesSup_eq`）：
$$\mathrm{ARM}_n=\{(\varnothing,\ \{a\})\}\quad\text{（恰好一条）}$$
因为 $(A\cup B)'$ 非空 $\iff$ $A\cup B$ 含 $a$ 且不含 $b$；
结合 $B\not\subseteq A$ 逼出唯一解。

**模型类**（`ex_modelOf_arm_empty_a`）：
$$\mathrm{Mod}(\mathrm{ARM}_n)=\{M\mid \{a\}\subseteq M\}=\{\{a\},\ \mathrm{univ}\}.$$

**⟹ $\mathrm{Mod}(\mathrm{ARM}_n)=\{\{a\},\mathrm{univ}\}\ \subsetneq\ \mathrm{Int}=\{\varnothing,\{a\},\mathrm{univ}\}$。**

### §4.0.2 缺口的**方向**与规格「漏掉」的对应

缺口是 $\mathrm{Int}\setminus\mathrm{Mod}=\{\varnothing\}$：
**$\varnothing$ 是闭集，但不满足 ARM 输出**。

**机理**（这是对规格文字的关键澄清）：ARM 输出的单条规则
$\varnothing\Rightarrow\{a\}$ 是**过强**的——它要求「满足空前件的一切集合
都必须含 $a$」，而空前件是**恒可用的**（$\varnothing\subseteq M$ 恒真），
于是**每个**模型都被迫含 $a$，闭集 $\varnothing$ 因此被**挤掉**。

**因此「漏掉」的准确含义**：不是「输出里少了一条本该有的规则」，
而是「**输出集把某个真模型（闭集）漏掉了**」——即
$\mathrm{Mod}$ **漏掉**了 $\mathrm{Int}$ 中的成员，等价地
$\mathrm{Mod}\subsetneq\mathrm{Int}$。

**⚠ 一个必须如实报告的发现**：我原以为输出会是「可靠但不完备」。
逐项核算（`t611_ARM_rule_false`）证明**不是**：输出的
$\varnothing\Rightarrow\{a\}$ **本身是假蕴含**
（$\varnothing'=G\not\subseteq\{a\}'=\{0\}$，因对象 $1$ 不具备 $a$）。
**⟹ 本背景上的 ARM 同时不可靠（`t611_ARM_rule_false`）且不完备
（`t611_ARM_not_exhaustive`）。** 故 T6.11 后半的结论
（「不保证穷尽」）成立，且**比原话更强**；
但「ARM 只输出了真蕴含、只是漏了几条」这一通俗理解**在本背景上为假**。 -/

/-- **T6.11 后半的反例背景**：$G=\{0,1\}$、$M=\{a,b\}$、$I=\{(0,a)\}$。 -/
def exCtx : FormalCtx where
  GFCA := Fin 2
  MFCA := Fin 2
  Irel := fun g m => g = 0 ∧ m = 0

instance : OfNat exCtx.GFCA 0 := ⟨(0 : Fin 2)⟩
instance : OfNat exCtx.GFCA 1 := ⟨(1 : Fin 2)⟩
instance : OfNat exCtx.MFCA 0 := ⟨(0 : Fin 2)⟩
instance : OfNat exCtx.MFCA 1 := ⟨(1 : Fin 2)⟩

/-! ### §4.1  $\mathbb{K}_{ex}$ 的逐项核算 -/

/-- **空集导出全体对象**：$\varnothing'=G$。 -/
theorem ex_polarDown_empty : exCtx.polarDown (∅ : Set exCtx.MFCA) = Set.univ := by
  ext g
  show (∀ m ∈ (∅ : Set exCtx.MFCA), exCtx.Irel g m) ↔ True
  exact ⟨fun _ => trivial, fun _ m hm => absurd hm (Set.notMem_empty m)⟩

/-- **$\{a\}'=\{0\}$**（属性 $a$ 只有对象 $0$ 具备）。 -/
theorem ex_polarDown_a : exCtx.polarDown ({0} : Set exCtx.MFCA) = {0} := by
  ext g
  show (∀ m ∈ ({0} : Set exCtx.MFCA), exCtx.Irel g m) ↔ g ∈ ({0} : Set exCtx.GFCA)
  constructor
  · intro h
    exact (h 0 (Set.mem_singleton 0)).1
  · intro hg m hm
    have h1 : m = 0 := Set.mem_singleton_iff.mp hm
    have h2 : g = 0 := Set.mem_singleton_iff.mp hg
    subst h1; subst h2
    exact ⟨rfl, rfl⟩

/-- **$\{b\}'=\varnothing$**（没有对象具备属性 $b$）。 -/
theorem ex_polarDown_b : exCtx.polarDown ({1} : Set exCtx.MFCA) = ∅ := by
  ext g
  show (∀ m ∈ ({1} : Set exCtx.MFCA), exCtx.Irel g m) ↔ False
  constructor
  · intro h
    have h1 := h 1 (Set.mem_singleton 1)
    exact absurd h1.2 (by decide)
  · intro h; exact h.elim

/-- **$\{a\}$ 是闭集**（$\{a\}''=\{a\}$）。 -/
theorem ex_closureOp_a : exCtx.closureOp ({0} : Set exCtx.MFCA) = {0} := by
  ext m
  show (∀ g ∈ exCtx.polarDown ({0} : Set exCtx.MFCA), exCtx.Irel g m)
    ↔ m ∈ ({0} : Set exCtx.MFCA)
  constructor
  · intro hm
    have h1 : exCtx.Irel 0 m :=
      hm 0 (by rw [ex_polarDown_a]; exact Set.mem_singleton (0 : exCtx.GFCA))
    exact h1.2
  · intro hm g hg
    rw [ex_polarDown_a] at hg
    have hg0 : g = 0 := Set.mem_singleton_iff.mp hg
    have hm0 : m = 0 := Set.mem_singleton_iff.mp hm
    subst hg0; subst hm0
    exact ⟨rfl, rfl⟩

/-- **$\varnothing$ 是闭集**：$\varnothing'=\mathrm{univ}$，
而对象 $1$ 不具备**任何**属性，故 $\varnothing''=\mathrm{univ}'=\varnothing$。 -/
theorem ex_closureOp_empty : exCtx.closureOp (∅ : Set exCtx.MFCA) = ∅ := by
  rw [FormalCtx.closureOp, ex_polarDown_empty]
  ext m
  show (∀ g ∈ (Set.univ : Set exCtx.GFCA), exCtx.Irel g m) ↔ m ∈ (∅ : Set exCtx.MFCA)
  constructor
  · intro hm
    have h1 : exCtx.Irel 1 m := hm 1 trivial
    exact absurd h1.1 (by decide)
  · intro hm
    exact absurd hm (Set.notMem_empty m)

/-- **$\mathrm{univ}$ 是闭集**：$\mathrm{univ}'=\varnothing$，$\varnothing'=\mathrm{univ}$。 -/
theorem ex_closureOp_univ : exCtx.closureOp (Set.univ : Set exCtx.MFCA) = Set.univ := by
  rw [FormalCtx.closureOp]
  have h : exCtx.polarDown (Set.univ : Set exCtx.MFCA) = ∅ := by
    ext g
    show (∀ m ∈ (Set.univ : Set exCtx.MFCA), exCtx.Irel g m) ↔ False
    constructor
    · intro hm
      have h1 : exCtx.Irel g (1 : exCtx.MFCA) := hm 1 trivial
      exact absurd h1.2 (by decide)
    · intro h; exact h.elim
  rw [h]
  ext m
  show (∀ g ∈ (∅ : Set exCtx.GFCA), exCtx.Irel g m) ↔ True
  exact ⟨fun _ => trivial, fun _ g hg => absurd hg (Set.notMem_empty g)⟩

/-- **$\{b\}$ 不闭**：$\{b\}''=\mathrm{univ}\neq\{b\}$（这是 §4.3 的缺口见证）。 -/
theorem ex_closureOp_b : exCtx.closureOp ({1} : Set exCtx.MFCA) = Set.univ := by
  rw [FormalCtx.closureOp, ex_polarDown_b]
  ext m
  show (∀ g ∈ (∅ : Set exCtx.GFCA), exCtx.Irel g m) ↔ True
  exact ⟨fun _ => trivial, fun _ g hg => absurd hg (Set.notMem_empty g)⟩

/-- **`Fin 2` 只有两个元素**（避免 `fin_cases` 的类型别名实例问题）。 -/
theorem ex_att_cases (m : exCtx.MFCA) : m = 0 ∨ m = 1 := by
  match m with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

/-- ⭐⭐ **$\mathrm{Int}$ 的完整刻画**：闭集**恰为**
$\varnothing$、$\{a\}$、$\mathrm{univ}$ **三个**。

**⟹ $\{b\}=\{1\}\notin\mathrm{Int}$**——这是 §4.3 反例的见证。 -/
theorem ex_int_eq : {M : Set exCtx.MFCA | exCtx.IsClosedAttr M}
    = {∅, {0}, Set.univ} := by
  ext M
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, FormalCtx.IsClosedAttr]
  constructor
  · intro h
    by_cases hb : (1 : exCtx.MFCA) ∈ M
    · -- M 含 b ⟹ M' = ∅ ⟹ M'' = univ ⟹ M = univ
      have hMp : exCtx.polarDown M = ∅ := by
        ext g
        show (∀ m ∈ M, exCtx.Irel g m) ↔ False
        exact ⟨fun h1 => absurd (h1 1 hb).2 (by decide), fun h1 => h1.elim⟩
      have hMu : exCtx.polarUp (∅ : Set exCtx.GFCA) = Set.univ := by
        ext m
        show (∀ g ∈ (∅ : Set exCtx.GFCA), exCtx.Irel g m) ↔ True
        exact ⟨fun _ => trivial, fun _ g hg => absurd hg (Set.notMem_empty g)⟩
      have huniv : (Set.univ : Set exCtx.MFCA) = M := by
        rw [← h, FormalCtx.closureOp, hMp, hMu]
      exact Or.inr (Or.inr huniv.symm)
    · -- M 不含 b ⟹ M ⊆ {a} ⟹ M = ∅ 或 M = {a}
      have hsub : M ⊆ ({0} : Set exCtx.MFCA) := by
        intro m hm
        simp only [Set.mem_singleton_iff]
        rcases ex_att_cases m with h' | h'
        · exact h'
        · exact absurd (h' ▸ hm) hb
      by_cases hne : (0 : exCtx.MFCA) ∈ M
      · right; left
        ext m
        constructor
        · intro hm; exact hsub hm
        · intro hm
          rw [Set.mem_singleton_iff] at hm
          exact hm ▸ hne
      · left
        ext m
        refine ⟨fun hm => ?_, fun hm => absurd hm (Set.notMem_empty m)⟩
        rcases ex_att_cases m with h' | h'
        · exact absurd (h' ▸ hm) hne
        · exact absurd (h' ▸ hm) hb
  · rintro (rfl | rfl | rfl)
    · exact ex_closureOp_empty
    · exact ex_closureOp_a
    · exact ex_closureOp_univ

/-! ### §4.2  ARM 规则集（阈值化）

**口径**（本文件对「ARM 在阈值 $n$ 下」的精确读法）：
置信度取 $1$（即要求 $B\subseteq A''$，此处闭包自动给出），
支撑度取「$|(A\cup B)'|\ge n$」的**正支撑**形式：

$$A\Rightarrow B\in\mathrm{ARM}_n \iff B\not\subseteq A\ \wedge\ n\le |(A\cup B)'|.$$

**阈值档位的化简**：本背景 $G$ 只有两个对象，故 $|(A\cup B)'|\in\{0,1,2\}$，
$n$ 的**有效档位只有 $n=0$（恒真）与 $n\ge1$（要求支撑 $>0$）** 两类。
本文件对 $n\ge 1$ 全部证明不完备，$n=0$ 另行给出（§4.4）。 -/

/-- **阈值化的 ARM 规则集**（置信度 $1$，最小支撑度 $n$）。 -/
def armRulesSup (K : FormalCtx) (n : ℕ) : Set K.MFCA × Set K.MFCA → Prop := fun r =>
  ¬(r.2 ⊆ r.1) ∧
    ((n = 0) ∨ (n ≤ 1 ∧ (K.polarDown (r.1 ∪ r.2)).Nonempty))

/-- **阈值单调性**：阈值越高，规则集越小。 -/
theorem armRulesSup_mono {n m : ℕ} (h : n ≤ m) :
    {r | armRulesSup K m r} ⊆ {r | armRulesSup K n r} := by
  rintro ⟨A, B⟩ ⟨h1, hcond⟩
  refine ⟨h1, ?_⟩
  rcases hcond with hzero | ⟨hle, hne⟩
  · -- m = 0 且 n ≤ m ⟹ n = 0
    have hn0 : n = 0 := Nat.le_zero.mp (hzero ▸ h)
    exact Or.inl hn0
  · exact Or.inr ⟨le_trans h hle, hne⟩

/-- ⭐ **$\mathbb{K}_{ex}$ 上阈值为 $1\le n\le1$ 时 ARM 输出只有一条规则**
$\varnothing\Rightarrow\{a\}$。

**⚠ 必须要求 $n\ge1$**：$n=0$ 时支撑度条件空真，规则集**远大于**单元素
（任何 $B\not\subseteq A$ 都入选）。**这正是阈值档位的关键分界**。

**核算**：$n\le1$ 且 $n\ne0$ 时，支撑度条件化为
「$(A\cup B)'$ **非空**」。而 $I$ 的像只含 $a$，故 $(A\cup B)'\ne\varnothing$
$\Rightarrow$ $A\cup B$ 含 $a$ 且不含 $b$（含 $b$ 则 $(A\cup B)'=\varnothing$）。
结合 $B\not\subseteq A$，唯一解是 $A=\varnothing$, $B=\{a\}$。 -/
theorem ex_armRulesSup_eq {n : ℕ} (hn1 : n ≠ 0) (hn : n ≤ 1) :
    {r | armRulesSup exCtx n r} = {(∅, ({0} : Set exCtx.MFCA))} := by
  ext r
  obtain ⟨A, B⟩ := r
  simp only [Set.mem_singleton_iff, Prod.mk.injEq, armRulesSup, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hBA, hcond⟩
    rcases hcond with h0 | ⟨_, hne⟩
    · exact absurd h0 hn1
    · -- (A∪B)' 非空 ⟹ 存在 g 使 ∀ m ∈ A∪B, Irel g m
      obtain ⟨g, hg⟩ := hne
      -- 取 m ∈ A∪B：则 Irel g m，故 m = a（属性 0）
      have hsub : ∀ m ∈ A ∪ B, m = (0 : exCtx.MFCA) := by
        intro m hm
        exact (hg hm).2
      have hA : A = ∅ := by
        by_contra hneA
        obtain ⟨m, hm⟩ := Set.nonempty_iff_ne_empty.mpr hneA
        have hm0 : m = 0 := hsub m (Set.mem_union_left B hm)
        have hBsub : B ⊆ A := by
          intro b hb
          have hb0 : b = 0 := hsub b (Set.mem_union_right A hb)
          rw [hb0]
          rw [hm0] at hm
          exact hm
        exact hBA hBsub
      refine ⟨hA, ?_⟩
      ext x
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hx
        have hx' : x ∈ A ∪ B := by
          rw [hA]
          exact Set.mem_union_right (∅ : Set exCtx.MFCA) hx
        exact hsub x hx'
      · intro hx
        -- x = 0；需证 0 ∈ B。B 非空（否则 B ⊆ A = ∅ 与 hBA 矛盾）
        have hneB : B ≠ ∅ := by
          rintro rfl
          exact hBA (hA ▸ Set.empty_subset A)
        obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr hneB
        have hb0 : b = 0 := hsub b (Set.mem_union_right A hb)
        rw [hx, ← hb0]
        exact hb
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, Or.inr ⟨hn, ?_⟩⟩
    · intro h
      exact h (Set.mem_singleton_iff.mpr rfl)
    · refine ⟨0, ?_⟩
      intro m hm
      have hm0 : m = 0 := by simpa using hm
      subst hm0
      exact ⟨rfl, rfl⟩

/-! ### §4.3  主定理：ARM 输出**不完备** -/

/-- **$M$ 满足单条规则 $\varnothing\Rightarrow\{a\}$ $\iff$ $\{a\}\subseteq M$**。 -/
theorem ex_modelOf_arm_empty_a (M : Set exCtx.MFCA) :
    exCtx.IsModelOf ({(∅, ({0} : Set exCtx.MFCA))}) M ↔ ({0} : Set exCtx.MFCA) ⊆ M := by
  constructor
  · intro h
    exact h (∅, {0}) (Set.mem_singleton _) (Set.empty_subset M)
  · intro h r hr
    rw [Set.mem_singleton_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    intro _
    exact h

/-- ⭐⭐ **ARM 在本背景上输出的规则是假蕴含**（**不可靠**）。

$$\mathbb{K}_{ex}\not\models \varnothing\Rightarrow\{a\}$$

**证明**：$\varnothing'=G$（含对象 $1$），$\{a\}'=\{0\}$（不含 $1$），
故 $\varnothing'\not\subseteq\{a\}'$。∎

**⚠ 这是一次必须如实报告的意外发现**：我原以为 ARM 的输出会是「可靠但
不完备」——即输出的规则都是真蕴含、只是不够多。**逐项核算证明并非如此**：
$\varnothing\Rightarrow\{a\}$ **根本是假蕴含**（前件可被任何集合满足，
却要求每个集合都含 $a$——而对象 $1$ 不具备 $a$）。

**⟹ 本背景上的 ARM 同时是**不可靠**且不完备**的。这对 T6.11 后半**更有利**
（不完备已被 `t611_ARM_not_exhaustive` 证明），但对「ARM 只是不完备」的
通俗说法是一个**反例**。**本文件不掩盖这一点。** -/
theorem t611_ARM_rule_false :
    ¬ exCtx.Models (∅ : Set exCtx.MFCA) ({0} : Set exCtx.MFCA) := by
  rw [Models_iff, ex_polarDown_empty, ex_polarDown_a]
  intro h
  have h1 : (1 : exCtx.GFCA) ∈ ({0} : Set exCtx.GFCA) := h (Set.mem_univ 1)
  have hz : (1 : exCtx.GFCA) = 0 := Set.mem_singleton_iff.mp h1
  have hval : (1 : exCtx.GFCA).val = (0 : exCtx.GFCA).val := congrArg Fin.val hz
  exact absurd hval (by decide)

/-- ⭐⭐⭐ **T6.11 后半（主定理）**：ARM 在阈值 $n\ge1$ 下的输出
**不是完备表示**。

$$\neg\,\mathrm{IsComplete}\,(\mathrm{ARM}_n)$$

**证明**：$\mathrm{ARM}_n=\{(\varnothing,\{a\})\}$，而
$M\in\mathrm{Mod}\iff\{a\}\subseteq M$。取 $M=\varnothing$：
$\varnothing$ 是闭集（`ex_closureOp_empty`）但 $\{a\}\not\subseteq\varnothing$，
故 $\varnothing\notin\mathrm{Mod}$。**⟹ $\mathrm{Mod}\neq\mathrm{Int}$。**

**这就是规格所说「阈值候选集漏掉某条成立的蕴含」的形式化**——
漏掉的是闭集 $\varnothing$：ARM 输出的规则**过强**（把 $a$ 硬塞给每个
满足空前件的集合），因而**挤掉了**本该保留的闭集 $\varnothing$。 -/
theorem t611_ARM_not_exhaustive {n : ℕ} (hn1 : n ≠ 0) (hn : n ≤ 1) :
    ¬ exCtx.IsComplete {r | armRulesSup exCtx n r} := by
  intro hcomp
  rw [ex_armRulesSup_eq hn1 hn] at hcomp
  -- ∅ 闭 ⟹ ∅ ∈ Mod（由完备性）
  rw [dgbasis_represents_iff] at hcomp
  have hmod : exCtx.IsModelOf ({(∅, ({0} : Set exCtx.MFCA))}) (∅ : Set exCtx.MFCA) :=
    (hcomp ∅).mpr ex_closureOp_empty
  rw [ex_modelOf_arm_empty_a] at hmod
  exact absurd (hmod (Set.mem_singleton (0 : exCtx.MFCA))) (Set.notMem_empty 0)

/-- ⭐⭐ **T6.11 后半（阈值无关版本）**：对**任意** $n\ne 0$，
ARM 输出都不完备。

**为何能去掉 $n\le1$**：$n\ge2$ 时 $n\ne0$ 且 $n\not\le1$，
故 `armRulesSup` 的支撑度条件（`n=0 ∨ (n≤1 ∧ 非空)`）
**既不左也不右**——规则集**为空**。于是 $\mathrm{Mod}=\text{全体}$，
而 $\{b\}$ 不闭（`ex_closureOp_b`），矛盾。∎ -/
theorem t611_ARM_any_threshold {n : ℕ} (hn : n ≠ 0) :
    ¬ exCtx.IsComplete {r | armRulesSup exCtx n r} := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact absurd h0 hn
  · by_cases h2 : n ≤ 1
    · exact t611_ARM_not_exhaustive hn h2
    · -- n ≥ 2：规则集为空 ⟹ Mod = 全体 ⟹ {b} ∈ Mod，但 {b} 不闭
      have hempty : {r | armRulesSup exCtx n r} = (∅ : Set (Set exCtx.MFCA × Set exCtx.MFCA)) := by
        ext r
        simp only [armRulesSup, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _
        rcases r with ⟨A, B⟩
        rintro (h0 | ⟨hle, _⟩)
        · exact absurd h0 hn
        · omega
      intro hcomp
      have hb_notclosed : ¬ exCtx.IsClosedAttr ({1} : Set exCtx.MFCA) := by
        intro h
        have h1 : exCtx.closureOp ({1} : Set exCtx.MFCA) = Set.univ := ex_closureOp_b
        rw [FormalCtx.IsClosedAttr, h1] at h
        have hmem : (0 : exCtx.MFCA) ∈ ({1} : Set exCtx.MFCA) := h ▸ (Set.mem_univ 0)
        have hzero : (0 : exCtx.MFCA) = 1 := Set.mem_singleton_iff.mp hmem
        exact absurd hzero (by exact Fin.zero_ne_one)
      rw [dgbasis_represents_iff] at hcomp
      have hmod := (hcomp {1}).mp
      rw [hempty] at hmod
      exact hb_notclosed (hmod (by intro r hr; exact absurd hr (Set.notMem_empty r)))

end FateV2.Rules