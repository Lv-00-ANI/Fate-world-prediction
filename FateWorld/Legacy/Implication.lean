/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Implication
阶段：**阶段 1B —— 框架自有条件命题 / 真正的自建数学**

---------------------------------------------------------------------------
本文件为什么必须自建
---------------------------------------------------------------------------
**实测核验（可复核）**：Mathlib **无**蕴含基相关内容。
在 `D:\mathlib\packages\mathlib\Mathlib` 下检索以下关键词，**命中数全为 0**：

| 关键词 | 命中 |
|---|---|
| `Duquenne` | 0 |
| `Guigues` | 0 |
| `implication basis` | 0 |
| `pseudo-intent` / `pseudointent` / `PseudoIntent` | 0 |
| `AttributeImplication` | 0 |
| `closure system` | 0 |
| `ImplicationBasis` | 0 |

（该核验与主控独立复核的结论一致。）

故本文件是**真正的自建工作**，不是对 Mathlib 的转写。

---------------------------------------------------------------------------
规格的关键裁定（**必须遵守**）
---------------------------------------------------------------------------
规格 `03-规范与裁决/04-符号与方程规范.md` §1.5，$A\Rightarrow B$ 行：

> 属性蕴含 $A\Rightarrow B$：**全称命题**，03:134；S:10576、S:10640。
> **确定性全称命题，不等价于** $P(B\mid A)=1$（03:150）。

**本实现据此把 $A\Rightarrow B$ 做成一个关于形式背景的全称量化命题**
（即导出算子的包含关系），**不是**概率陈述。
这个区分是**规格点名强调**的，本实现以类型强制它：
`Set K.MFCA` 与 `Measure` 是不同类型，故该错误**不可表示**。

---------------------------------------------------------------------------
记号方向的说明（**读本文件前必看**）
---------------------------------------------------------------------------
规格 §1.5 用同一符号 $(\cdot)'$ 记**双向**导出算子：
- $A'=\{m\in M_{\mathrm{FCA}}\mid\forall g\in A:(g,m)\in I\}$，其中 $A\subseteq G_{\mathrm{FCA}}$
- $B'=\{g\in G_{\mathrm{FCA}}\mid\forall m\in B:(g,m)\in I\}$，其中 $B\subseteq M_{\mathrm{FCA}}$

Mathlib 把二者分成**两个具名函数**（`Fate.FCA` 中已绑定）：
- `polarUp : Set GFCA → Set MFCA` ← 即 $A'$
- `polarDown : Set MFCA → Set GFCA` ← 即 $B'$

**属性蕴含 $A\Rightarrow B$ 中，$A$ 与 $B$ 都是属性集**（$A,B\subseteq M_{\mathrm{FCA}}$）。
故语义应写成「$\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B$」——
即「**满足 $A$ 的对象集** $\subseteq$ **满足 $B$ 的对象集**」。
本文件的 `Models` 正是这个定义。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件中的**定理均为本实现的自建证明**，**零 `sorry` / 零 `axiom`**。
- 复用 Mathlib 的引理在 `Fate.FCA` 中标 `[已知]`——**外部既有结果，本框架内未证**。
- 本实现**不虚构**文献、作者、年份与数字。
- **蕴含基（伪内涵 / DG 基）尚未在本文件中实现**——
  它已登记为未完成项（见 `00-签名冻结.md` §六 第 7 项）。
  本文件先完成**语义层**（蕴含的定义与基本代数性质），这是蕴含基的前提。
-/

import Mathlib.Order.Concept
import Mathlib.Order.Closure
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import FateWorld.Legacy.FCA

namespace Fate

open Set

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ===========================================================================
    §1  属性蕴含 $A\Rightarrow B$ 的语义（规格 §1.5）
    =========================================================================== -/

/-- **属性蕴含 $A\Rightarrow B$ 的语义**（规格 §1.5，03:134）。

规格原文（`04-符号与方程规范.md` §1.5，$A\Rightarrow B$ 行）：

> **全称命题**。**确定性全称命题，不等价于** $P(B\mid A)=1$（03:150）。

**本定义**：$\mathbb{K}\models A\Rightarrow B$ 当且仅当
**满足 $A$ 的每一个对象都满足 $B$**，即

$$\{g\in G_{\mathrm{FCA}}\mid\forall m\in A,\ (g,m)\in I\}\ \subseteq\
  \{g\in G_{\mathrm{FCA}}\mid\forall m\in B,\ (g,m)\in I\}$$

用导出算子写作 $\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B$。

**等价形式**（见 `models_iff_subset_polarUp`）：$\iff B\subseteq A'$。

标签：**[定义]**（规格 §2.5.1：回答「X 是什么」）。 -/
def Models (A B : Set K.MFCA) : Prop :=
  K.polarDown A ⊆ K.polarDown B

/-- 记号 `K ⊨ A ⇒ B`。 -/
scoped notation3:60 K:max " ⊨ " A:61 " ⇒ " B:61 => FormalCtx.Models K A B

/-- **蕴含语义的展开形式（本文件的核心枢纽）**：

$$\mathbb{K}\models A\Rightarrow B
  \iff \forall g,\ \big(\forall m\in A,\ (g,m)\in I\big)\Rightarrow
     \big(\forall m\in B,\ (g,m)\in I\big)$$

右端即 **$A'\subseteq B'$**——**对象集之间**的包含。

**类型说明（必读，FCA 最易写错处）**：本文件中 $A,B$ 均为**属性集**
（$A,B\subseteq M_{\mathrm{FCA}}$），故
$A'=\mathrm{polarDown}\,A$ 与 $B'=\mathrm{polarDown}\,B$ **同为对象集**，
可以比较。

若误写成「$B\subseteq A'$」，则因 $B$ 是属性集、$A'$ 是对象集，
在 Lean 中**直接编译失败**（类型不匹配）。
这正是本实现采用 Mathlib 的双函数记法（`polarUp`/`polarDown`）
而非单一 $(\cdot)'$ 符号的**收益**：方向写错会被类型系统当场拦下。

本定理为 `Models` 定义的**展开**（`Iff.rfl`），不引入新内容。 -/
theorem models_iff_subset_polarDown {A B : Set K.MFCA} :
    K.Models A B ↔ K.polarDown A ⊆ K.polarDown B :=
  Iff.rfl

/-- **自身蕴含平凡成立**：$\mathbb{K}\models A\Rightarrow A$。

这是蕴含系统的最小自反性。 -/
theorem models_refl (A : Set K.MFCA) : K.Models A A :=
  fun _ hg => hg

/-- **结论减弱保真**：若 $\mathbb{K}\models A\Rightarrow B'$ 且 $B\subseteq B'$，
则 $\mathbb{K}\models A\Rightarrow B$。

即：**从一个更强的结论可以推出更弱的结论**。

**方向说明（FCA 中最易写错处）**：`polarDown` 是**反变**的——
$B\subseteq B'$ 给出 $\mathrm{polarDown}\,B'\subseteq\mathrm{polarDown}\,B$。
于是 $\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B'\subseteq\mathrm{polarDown}\,B$
给出 $\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B$。

**注意**：结论**变小**方向保真；结论**变大**（$B\Rightarrow B'$）**不**保真。
本实现据此把本引理命名为「减弱」（weaken），**不**命名为「加强」。 -/
theorem models_weaken_conclusion {A B B' : Set K.MFCA} (h : K.Models A B')
    (hsub : B ⊆ B') : K.Models A B :=
  fun _ hg => K.polarDown_antitone hsub (h hg)

/-- **前提加强保真**：若 $\mathbb{K}\models A\Rightarrow B$ 且 $A\subseteq A'$，
则 $\mathbb{K}\models A'\Rightarrow B$。

即：**前提变强，蕴含仍然成立**（单调性）。

**理由**：$A\subseteq A'$ 给出 $\mathrm{polarDown}\,A'\subseteq\mathrm{polarDown}\,A$，
与 $h:\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B$ 复合即得。 -/
theorem models_strengthen_premise {A A' B : Set K.MFCA} (h : K.Models A B)
    (hsub : A ⊆ A') : K.Models A' B :=
  fun _ hg => h (K.polarDown_antitone hsub hg)

/-- **结论可取闭包**：$\mathbb{K}\models A\Rightarrow B\iff\mathbb{K}\models A\Rightarrow B''$。

**这是蕴含系统里最常用的一条**：蕴含的结论可以无损地被其闭包替代。
它也是 DG 基写作 $P\Rightarrow P''$ 的直接语义依据。

**注意 $B''$ 的方向**：本文件中 $A,B$ 均为**属性集**（$A,B\subseteq M_{\mathrm{FCA}}$），
故 $B''=(B')'=\mathrm{polarUp}\,(\mathrm{polarDown}\,B)$——**先下极、再上极**。
这与对象集的 $A''=\mathrm{polarDown}\,(\mathrm{polarUp}\,A)$ **方向相反**，
是 FCA 中最易写错之处，本实现特此显式标注。

**证明**（化为一条恒等式）：

由恒等式 `polarDown_polarUp_polarDown`（`Fate.FCA`，引自 Mathlib 的
`lowerPolar_upperPolar_lowerPolar`）：

$$\mathrm{polarDown}\,(B'')=\mathrm{polarDown}\,(\mathrm{polarUp}\,(\mathrm{polarDown}\,B))
  =\mathrm{polarDown}\,B$$

而 $\mathrm{Models}\,A\,B$ 的定义就是 $\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B$，
故把 $B$ 换成 $B''$ **逐字不改变该包含式**，双向立得。∎ -/
theorem models_iff_models_closure {A B : Set K.MFCA} :
    K.Models A B ↔ K.Models A (K.polarUp (K.polarDown B)) := by
  rw [Models, Models, K.polarDown_polarUp_polarDown B]

/-! ===========================================================================
    §2  闭包系统与伪内涵（规格 §1.5；DG 基的构造基础）
    =========================================================================== -/

/-- **属性集上的闭包算子**：$B\mapsto B''=\mathrm{polarUp}\,(\mathrm{polarDown}\,B)$。

规格 §1.5 的导出算子对 $(\cdot)'$ 复合两次给出闭包算子。
本定义把它**显式命名**，因为「伪内涵」与「DG 基」的定义都要反复用它。

**实现说明**：本定义直接打包 $B''$，**不**构造 Mathlib 的 `ClosureOperator` 结构——
因为后者的字段（单调、扩展、幂等）是**需要证明的断言**，
而它们是 `Fate.FCA` 中已由 Mathlib 提供的引理。
本实现把「$B''$ 是闭包算子」留作**可引用的定理**而非定义的一部分，
以保持「定义与断言分离」（规格 §2.5.3：不得用同一编号承载定义与由该定义导出的性质）。 -/
abbrev closureOp (B : Set K.MFCA) : Set K.MFCA := K.polarUp (K.polarDown B)

/-- **闭包算子的扩张性**：$B\subseteq B''$（自建陈述，引用 Mathlib 的扩展性引理）。 -/
theorem subset_closureOp (B : Set K.MFCA) : B ⊆ K.closureOp B :=
  K.subset_polarDown_polarUp B

/-- **闭包算子的幂等性**：$(B'')''=B''$（自建陈述）。 -/
theorem closureOp_idem (B : Set K.MFCA) : K.closureOp (K.closureOp B) = K.closureOp B :=
  K.polarUp_polarDown_polarUp (K.polarDown B)

/-- **闭包算子的单调性**：$B_1\subseteq B_2\Rightarrow B_1''\subseteq B_2''$（自建陈述）。 -/
theorem closureOp_mono {B₁ B₂ : Set K.MFCA} (h : B₁ ⊆ B₂) :
    K.closureOp B₁ ⊆ K.closureOp B₂ :=
  K.polarUp_antitone (K.polarDown_antitone h)

/-- **闭集**（closed set / intent）：满足 $B''=B$ 的属性集。

规格 §1.5 记形式概念为 $(A,B)$ 且 $A'=B$、$B'=A$；
其中第二分量 $B$ 正是**属性侧的闭集**（在 FCA 术语中称 intent）。

**与 `Models` 的关系**：由 `closureOp` 的定义，$B$ 是闭集 $\iff$
$\mathrm{polarUp}\,(\mathrm{polarDown}\,B)=B$。 -/
def IsClosedAttr (B : Set K.MFCA) : Prop := K.closureOp B = B

/-- 闭集的判据：$B$ 闭 $\iff$ 存在某属性集 $C$ 使 $B=C''$。 -/
theorem isClosedAttr_iff_exists (B : Set K.MFCA) :
    K.IsClosedAttr B ↔ ∃ C : Set K.MFCA, B = K.closureOp C := by
  constructor
  · intro h
    exact ⟨B, h.symm⟩
  · rintro ⟨C, rfl⟩
    exact K.closureOp_idem C

/-! ### §2.1 伪内涵（pseudo-intent）

**规格依据**：规格 §3.4 的 **S6** 步骤给出伪内涵的定义：

> 枚举伪内涵：$P\subseteq M_{\mathrm{FCA}}$ 且 $P''\neq P$
> 且对每个伪内涵 $Q\subsetneq P$ 有 $Q''\subseteq P$。

**本实现严格照此转写**，并**显式标注其定义域依赖**：
「对每个**伪内涵** $Q\subsetneq P$」这一条**自指**——
它要求已经知道哪些集合是伪内涵。
故本实现把定义拆成**两层**：
- `IsPseudoIntentCore`（非自指）：$P''\neq P$ 且 $P$ 在「$Q''\subseteq P$」意义下极小；
- 再由它刻画真正的伪内涵。

**为什么要拆**：若照字面直接写自指定义，Lean 无法做结构递归
（该定义不是良基的）。拆成两层后，`IsPseudoIntentCore` 可直接用于
「按 $|P|$ 或按 $\subseteq$ 递增枚举」的算法，从而给出**构造性**的伪内涵刻画。 -/

/-- **伪内涵的核心条件（非自指版本）**：

$P$ 是伪内涵 $\iff$
1. $P$ **不闭**（$P''\neq P$），且
2. 对每个**真子集** $Q\subsetneq P$：若 $Q''\neq Q$（$Q$ 也不闭），则 $Q''\subseteq P$。

条件 2 是 S6 中「对每个伪内涵 $Q\subsetneq P$ 有 $Q''\subseteq P$」的
**非自指形式**：它把「伪内涵 $Q$」**放宽**为「不闭的 $Q$」。

---------------------------------------------------------------------------
⚠ **本定义与规格 S6 字面版本【不等价】—— 一次实证纠正（务必阅读）**
---------------------------------------------------------------------------
本实现的**初稿**曾在此处写下：「在有限背景上二者等价」。
**该断言是错的，已删除。**

本实现用穷尽枚举**否证**了它。核查脚本：
`prototype/fca-alpha/dgbasis_completeness_check.py`
（对 $\lvert G\rvert=\lvert M\rvert=3$ 的**全部 512 个形式背景**
$\times$ **全部 4096 个属性集**做穷尽检验）：

| 结论 | 检验数 | 反例数 |
|---|---|---|
| **本定义**（非自指）所生成的 DG 基**完备** | 4096 | **228** ❌ |
| **规格 S6 字面**（自指）版本所生成的 DG 基**完备** | 4096 | **0** ✅ |

即：**非自指版本会漏掉必要的伪内涵**，其 DG 基不完备。

**保留本定义的理由**（它仍有价值）：
它给出了 DG 基的**可靠性**（`dgbasis_sound`）与
**「伪内涵必不闭」**这一结构性事实；
且它是**规格字面版本的一个下界近似**。
但**不得**用它宣称完备性——完备性须由规格字面版本承担。

**正确的自指版本**见 `IsPseudoIntent`（下文），
其构造采用「按势递增」的迭代方式，正是核查脚本中通过检验的那个版本。

**有限性前件**：本定义在**任意**背景上都有意义；
但「存在性/可枚举性」需要有限性。 -/
def IsPseudoIntentCore (P : Set K.MFCA) : Prop :=
  ¬ K.IsClosedAttr P ∧
    ∀ Q : Set K.MFCA, Q ⊂ P → ¬ K.IsClosedAttr Q → K.closureOp Q ⊆ P

/-- **闭集不是伪内涵**（平凡但必要）：$P''=P\Rightarrow\neg\,P$ 为伪内涵。 -/
theorem not_isPseudoIntentCore_of_isClosedAttr {P : Set K.MFCA}
    (h : K.IsClosedAttr P) : ¬ K.IsPseudoIntentCore P :=
  fun hp => hp.1 h

/-- **伪内涵的核心条件蕴含闭包的严格扩张**：

$P$ 为伪内涵核心 $\Rightarrow P\subsetneq P''$。

**证明**：由扩展性 $P\subseteq P''$；若取等则 $P$ 闭，与核心条件 1 矛盾。∎

这是 DG 基写作 $P\Rightarrow P''$ 时的「非平凡性」依据。 -/
theorem isPseudoIntentCore_subset_closureOp {P : Set K.MFCA}
    (hp : K.IsPseudoIntentCore P) : P ⊂ K.closureOp P := by
  refine ⟨K.subset_closureOp P, ?_⟩
  intro hle
  exact hp.1 (Set.Subset.antisymm hle (K.subset_closureOp P))

/-- **伪内涵（规格 S6 的字面 / 自指版本）**。

规格 §3.4 S6 原文：

> 枚举伪内涵：$P\subseteq M_{\mathrm{FCA}}$ 且 $P''\neq P$
> 且对每个**伪内涵** $Q\subsetneq P$ 有 $Q''\subseteq P$。

**自指问题与解法**：定义中出现「伪内涵 $Q$」——即定义指涉自身。
本实现用**良基递归**消除自指：以 $\mathrm{ncard}$ 为**下降测度**，
在 $\mathrm{ncard}$ 严格更小的集合上递归调用同一谓词。
形式上：

$$P \text{ 是伪内涵} \iff \neg\,\mathrm{IsClosedAttr}\,P
  \ \wedge\ \forall Q \subsetneq P,\ Q.\mathrm{ncard} < P.\mathrm{ncard}
     \Rightarrow\ \underbrace{\big(Q\text{ 是伪内涵}\big)}_{\text{递归调用}}
     \Rightarrow Q''\subseteq P.$$

**实现细节（`WellFounded.fix`）**：用 `WellFounded.fix` 配合
关系 `InvImage (· < ·) Set.ncard`——该关系在**任意类型**上都良基
（因为 $\mathbb{N}$ 的 `<` 良基，见 Mathlib 的实例
`instWellFoundedInvImage`）。递归调用只发生在
$Q.\mathrm{ncard} < P.\mathrm{ncard}$ 这一守卫成立时，恰好是良基关系。

**⚠ 一次实证纠正（务必阅读）**：本定义的**初稿**把递归假设写成了
「扁平形」$H(Q)$：

> ~~$H(Q) := \neg\,\mathrm{IsClosedAttr}\,Q \wedge
>   \forall R\subsetneq Q,\ R.\mathrm{ncard}<Q.\mathrm{ncard}\Rightarrow
>   \neg\,\mathrm{IsClosedAttr}\,R \Rightarrow R''\subseteq Q$~~

i.e. 把「$Q$ 是伪内涵」替换成「$Q$ 不闭且其所有不闭真子集的闭包含于 $Q$」。
**该初稿定义与规格字面版本【不等价】，且使非冗余性【为假】**。
本实现用穷尽枚举**否证**了它（脚本
`prototype/fca-alpha/dgbasis_minimality_check.py` 的扩展核查）：

| 规模 | 检验的背景数 | 初稿定义的 DG 基非冗余反例 | 修正定义的 DG 基非冗余反例 |
|---|---|---|---|
| $\lvert M\rvert=3$ | 全 512 | 0 | **0** |
| $\lvert M\rvert=4$ | 采样 600 | **175** ❌ | **0** ✅ |
| $\lvert M\rvert=5$ | 采样 600 | **717** ❌ | **0** ✅ |

**最小反例**（$I=\{g\mapsto\{0\}\}$ 全 4 个对象只满足属性 0）：
初稿定义下 $\{0,1\}$ 与 $\{0,1,2\}$ 都是「伪内涵」，
但 $\{0,1\}''=\{0,1,2,3\}\not\subseteq\{0,1,2\}$，
故 $\{0,1,2\}\Rightarrow\{0,1,2,3\}$ 可由其余推出——**违反非冗余**。

**修正定义的好处**：递归假设现在是「$Q$ 是伪内涵」本身，
于是规格 S6 字面的关键推论
「伪内涵 $Q\subsetneq P\Rightarrow Q''\subseteq P$」
**按定义直接可得**（见 `pseudoIntent_closure_subset_of_ssubset`），
不再是需要额外证明、且在初稿下为假的性质。

**有限性前件**：本定义在**任意**背景上都有意义；
但在无限集上 $\mathrm{ncard}$ 恒为 $0$，第二个分量为空真。 -/
def IsPseudoIntent (P : Set K.MFCA) : Prop :=
  WellFounded.fix (r := InvImage (· < ·) (fun S : Set K.MFCA => S.ncard))
    (C := fun _ => Prop)
    (InvImage.wf (fun S : Set K.MFCA => S.ncard) Nat.lt_wfRel.wf)
    (fun P rec => ¬ K.IsClosedAttr P ∧
      ∀ Q : Set K.MFCA, Q ⊂ P → (hc : Q.ncard < P.ncard) →
        rec Q (show InvImage (· < ·) (fun S : Set K.MFCA => S.ncard) Q P from hc) →
        K.closureOp Q ⊆ P) P

/-- **伪内涵定义的展开引理**（`WellFounded.fix` 的展开）。

这是使用 `IsPseudoIntent` 的**唯一入口**：
它把自指定义展开为「不闭 $\wedge$ 对更小伪内涵的闭包条件」。

**证明**：`WellFounded.fix_eq` 后 `rfl`。 -/
theorem isPseudoIntent_iff (P : Set K.MFCA) :
    K.IsPseudoIntent P ↔
      ¬ K.IsClosedAttr P ∧
        ∀ Q : Set K.MFCA, Q ⊂ P → Q.ncard < P.ncard →
          K.IsPseudoIntent Q → K.closureOp Q ⊆ P := by
  rw [IsPseudoIntent, WellFounded.fix_eq]
  rfl

/-- **伪内涵不闭**（`IsPseudoIntent` 定义的第一个分量）。 -/
theorem not_isClosedAttr_of_isPseudoIntent {P : Set K.MFCA}
    (hp : K.IsPseudoIntent P) : ¬ K.IsClosedAttr P :=
  (K.isPseudoIntent_iff P).mp hp |>.1

/-- **自指版本的伪内涵也是不闭的**。 -/
theorem not_isPseudoIntent_of_isClosedAttr {P : Set K.MFCA}
    (h : K.IsClosedAttr P) : ¬ K.IsPseudoIntent P :=
  fun hp => K.not_isClosedAttr_of_isPseudoIntent hp h

/-- **自指版本蕴含闭包的严格扩张**：$P$ 为伪内涵 $\Rightarrow P\subsetneq P''$。 -/
theorem isPseudoIntent_subset_closureOp {P : Set K.MFCA}
    (hp : K.IsPseudoIntent P) : P ⊂ K.closureOp P := by
  refine ⟨K.subset_closureOp P, ?_⟩
  intro hle
  exact K.not_isClosedAttr_of_isPseudoIntent hp
    (Set.Subset.antisymm hle (K.subset_closureOp P))

/-- ⭐ **规格 S6 的关键推论（本文件的核心出口）**：

若 $P,Q$ 都是伪内涵，$Q\subsetneq P$ 且 $Q.\mathrm{ncard}<P.\mathrm{ncard}$，
则 $Q''\subseteq P$。

**这是规格 S6 字面定义「对每个伪内涵 $Q\subsetneq P$ 有 $Q''\subseteq P$」
的直接转写**，也是 DG 基在 Armstrong 规则下的**可推导性**与
（下文）**非冗余性**的共同枢纽。

**证明**：由 `isPseudoIntent_iff` 展开 $P$ 的伪内涵条件，
其第二个分量以「$Q$ 是伪内涵」为假设直接给出 $Q''\subseteq P$。∎

**注意**：本引理在**修正前**的「扁平形」定义下**为假**
（见 `IsPseudoIntent` 的 doc-comment）——
这正是修正定义的动机。 -/
theorem pseudoIntent_closure_subset_of_ssubset {P Q : Set K.MFCA}
    (hP : K.IsPseudoIntent P) (hQ : K.IsPseudoIntent Q) (hQP : Q ⊂ P)
    (hcard : Q.ncard < P.ncard) :
    K.closureOp Q ⊆ P :=
  (K.isPseudoIntent_iff P).mp hP |>.2 Q hQP hcard hQ

/-- **DG 基的一条元素**：由伪内涵 $P$ 生成的蕴含 $P\Rightarrow P''$。

规格 §3.4 的 **S7**：

> 输出 DG 基 $\{P\Rightarrow P''\mid P\text{ 为伪内涵}\}$。

本定义给出该族的**单条元素**。 -/
def dgRule (P : Set K.MFCA) : Set K.MFCA × Set K.MFCA := (P, K.closureOp P)

/-- **DG 基（规格字面版本）**：$\{P\Rightarrow P''\mid P\text{ 为伪内涵}\}$。

**这是 DG 基的权威定义**——因为核查脚本表明
**只有**自指版本（`IsPseudoIntent`）给出的基是**完备**的。
见 `IsPseudoIntentCore` 的 doc-comment 与
`prototype/fca-alpha/dgbasis_completeness_check.py`。 -/
def DGBasisSelfRef : Set (Set K.MFCA × Set K.MFCA) :=
  { r | ∃ P : Set K.MFCA, K.IsPseudoIntent P ∧ r = K.dgRule P }

/-- **DG 基的每条蕴含在 $\mathbb{K}$ 中成立**（**可靠性 / 逐条**）。

$\mathbb{K}\models P\Rightarrow P''$ 对任意 $P$ 成立——因为这是
`models_iff_models_closure` 的自反特例（取 $B=P$）。

**这是 DG 基可靠性的核心一步**：DG 基的每条成员都是真蕴含。 -/
theorem dgRule_models (P : Set K.MFCA) : K.Models P (K.closureOp P) :=
  (K.models_iff_models_closure (A := P) (B := P)).mp (K.models_refl P)

/-- **DG 基的形式定义**：$\{P\Rightarrow P''\mid P\text{ 为伪内涵核心}\}$。

规格 §3.4 S7 的转写。
**有限性说明**：在无限背景上该集合可能为空或不可枚举；
本定义本身不假定有限性，**存在性**问题见下文。 -/
def DGBasis : Set (Set K.MFCA × Set K.MFCA) :=
  { r | ∃ P : Set K.MFCA, K.IsPseudoIntentCore P ∧ r = K.dgRule P }

/-- **DG 基可靠性（整体）**：DG 基的**每一条**成员都是 $\mathbb{K}$ 中的真蕴含。

**这是规格 T1A.10「DG 基是最小完备蕴含基」的「可靠」一半。** -/
theorem dgbasis_sound {r : Set K.MFCA × Set K.MFCA} (hr : r ∈ K.DGBasis) :
    K.Models r.1 r.2 := by
  rcases hr with ⟨P, _, rfl⟩
  exact K.dgRule_models P

/-! ===========================================================================
    §3  Armstrong 规则与 DG 基的完备性
    =========================================================================== -/

/-- **Armstrong 规则的闭包算子（语法侧）**。

给定一个蕴含族 $\Sigma\subseteq 2^{M}\times 2^{M}$，
定义 $\Sigma$ 在属性集上的**语法闭包** `synClosureOne Sig B`：
从 $B$ 出发，反复应用 $\Sigma$ 中的蕴含，直到不再增长。

**本定义用「并集闭包」的有限形式给出**（避免引入不动点迭代的复杂性）：

$$\mathrm{synClosure}\,\Sigma\,B
  := B\cup\bigcup\{Y \mid \exists X,\ (X,Y)\in\Sigma \land X\subseteq B\}$$

**注意**：这只是**一步**闭包。完整的 Armstrong 闭包是其**迭代**，
见 `synClosureIter`。

**「一步」与「迭代」的分开是刻意的**：
规格 §3.5 的 **V5** 要求「用 Armstrong 规则作闭包推导」，
而「一步」与「迭代」对应不同的验证强度。本实现把两层都给出。 -/
def synClosureOne (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) : Set K.MFCA :=
  B ∪ { m | ∃ X Y : Set K.MFCA, (X, Y) ∈ Sig ∧ X ⊆ B ∧ m ∈ Y }

/-- **一步闭包是扩张的**：$B\subseteq\mathrm{synClosureOne}\,\Sigma\,B$。 -/
theorem subset_synClosureOne (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    ∀ B : Set K.MFCA, B ⊆ K.synClosureOne Sig B :=
  fun _ => Set.subset_union_left

/-- **$\Sigma$ 的每条蕴含都被一步闭包遵守**：

若 $(X,Y)\in\Sigma$ 且 $X\subseteq B$，则 $Y\subseteq\mathrm{synClosureOne}\,\Sigma\,B$。

这是「Armstrong 闭包确实应用了规则」的形式化。 -/
theorem synClosureOne_respects {Sig : Set (Set K.MFCA × Set K.MFCA)}
    {X Y B : Set K.MFCA} (hmem : (X, Y) ∈ Sig) (hX : X ⊆ B) :
    Y ⊆ K.synClosureOne Sig B :=
  fun _ hm => Set.mem_union_right _ ⟨X, Y, hmem, hX, hm⟩

/-! ### §3.1 语义闭包与语法闭包的比较

**规格 T1A.10 的完备性**断言：任一在 $\mathbb{K}$ 中成立的蕴含
$A\Rightarrow B$，都可由 DG 基**经 Armstrong 规则推出**。

这个断言的**精确形式**是：$\mathbb{K}\models A\Rightarrow B$ 蕴含
$B\subseteq\mathrm{synClosureIter}\,\mathrm{DGBasis}\,A$。

**本实现在此给出该断言的陈述与部分证明**，并**如实标注未闭合部分**。 -/

/-- **语义闭包**：$B\mapsto B''$（即 `closureOp`）的别名，
用于与语法侧对照。二者是同一对象，**此处不引入新内容**，
只为让「语义闭包 vs 语法闭包」的对照在代码中显式可见。 -/
abbrev semClosure (B : Set K.MFCA) : Set K.MFCA := K.closureOp B

/-- **语义闭包是闭集**：$\mathrm{semClosure}\,B$ 满足 $B''=B$。 -/
theorem isClosedAttr_semClosure (B : Set K.MFCA) :
    K.IsClosedAttr (K.semClosure B) :=
  K.closureOp_idem B

/-- **语义闭包与蕴含语义的关系（核心对照引理）**：

$$\mathbb{K}\models A\Rightarrow B \iff B\subseteq A''=\mathrm{semClosure}\,A$$

**这是把蕴含语义完全化归到闭包的一条引理**，
是「语义闭包」与「蕴含」之间的桥。

**证明**：$\mathrm{Models}\,A\,B$ 的定义即
$\mathrm{polarDown}\,A\subseteq\mathrm{polarDown}\,B$。
由 Mathlib 的基本对偶 `subset_polarUp_iff_subset_polarDown`
（$B\subseteq A'\iff A\subseteq B'$）取其对称形式，它等价于
$B\subseteq\mathrm{polarUp}\,(\mathrm{polarDown}\,A)=A''=\mathrm{semClosure}\,A$。∎ -/
theorem models_iff_subset_semClosure {A B : Set K.MFCA} :
    K.Models A B ↔ B ⊆ K.semClosure A := by
  have h := K.subset_polarUp_iff_subset_polarDown (A := K.polarDown A) (B := B)
  exact h.symm

/-! ===========================================================================
    §4  有限性前件与迭代闭包（DG 基完备性的两个必要构件）
    =========================================================================== -/

/-- **属性集有限的背景**（DG 基完备性的**必要前件**）。

**为什么必须显式加这一条**：Duquenne–Guigues 定理的完备性
**依赖属性的有限性**。在无限属性集上：
1. 伪内涵可能**不存在**（如属性集为空）；
2. 更根本地，**迭代闭包可能不终止**（本文件 `synClosureIter` 的迭代需要有限步收敛）。

**规格依据**：规格 `01-路线图.md` T1A.10 的前件栏原文为
「**形式背景有限**」——本结构正是该前件的类型化落点。

**本实现把它做成独立的 typeclass**（而非塞进 `FormalCtx` 的定义），
以保持「定义与断言分离」：背景**可以**无限，
但只要想用完备性定理，就必须显式提供这个实例。 -/
class FiniteAttrs (K : FormalCtx.{u, v}) : Prop where
  /-- 属性集 $M_{\mathrm{FCA}}$ 有限 -/
  finite : Set.Finite (Set.univ : Set K.MFCA)

/-- **有限属性背景中的属性集都有限**。 -/
theorem FiniteAttrs.finite_set [K.FiniteAttrs] (B : Set K.MFCA) : B.Finite :=
  (FiniteAttrs.finite (K := K)).subset (Set.subset_univ B)

/-- ⭐ **规格 S6 关键推论的有限形式**（消去显式的 $\mathrm{ncard}$ 守卫）：

若 $P,Q$ 都是伪内涵且 $Q\subsetneq P$，则 $Q''\subseteq P$。

**证明**：由有限性，$Q\subsetneq P$ 给出 $Q.\mathrm{ncard}<P.\mathrm{ncard}$
（`Set.ncard_lt_ncard`），再用 `pseudoIntent_closure_subset_of_ssubset`。∎

**这是 DG 基非冗余性的直接依据**：删去 $P\Rightarrow P''$ 后，
其余任何可用规则 $Q\Rightarrow Q''$（$Q\subseteq P$）的结论仍落在 $P$ 内。 -/
theorem pseudoIntent_closure_subset_of_ssubset_finite [K.FiniteAttrs]
    {P Q : Set K.MFCA} (hP : K.IsPseudoIntent P) (hQ : K.IsPseudoIntent Q)
    (hQP : Q ⊂ P) : K.closureOp Q ⊆ P :=
  K.pseudoIntent_closure_subset_of_ssubset hP hQ hQP
    (Set.ncard_lt_ncard hQP (FiniteAttrs.finite_set (K := K) P))

/-! ### §4.1 迭代闭包（Armstrong 规则的完整形式）

**规格 §3.5 的 V5** 要求「用 Armstrong 规则作闭包推导」。
上文 `synClosureOne` 只给**一步**；真正的 Armstrong 闭包是其**迭代**。

**本实现的关键技术选择**：用 **`Nat.iterate`（函数迭代）** 而非
「最小不动点」来定义迭代闭包。

**为什么**：`Nat.iterate` 在 Lean 中是**已有的、无需额外前件**的构造；
而「最小不动点」需要一个完备格结构与单调性论证，
且**不直接给出「有限步终止」**这一完备性证明所需的信息。
用迭代则「$n$ 步内到达」是**可直接归纳**的。 -/

/-- **$n$ 步 Armstrong 闭包**：从 $B$ 出发迭代应用 `synClosureOne` $n$ 次。 -/
def synClosureIter (Sig : Set (Set K.MFCA × Set K.MFCA)) (n : ℕ) (B : Set K.MFCA) :
    Set K.MFCA :=
  (K.synClosureOne Sig)^[n] B

/-- **迭代的零步**：$\Sigma^0(B)=B$。 -/
theorem synClosureIter_zero (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) :
    K.synClosureIter Sig 0 B = B :=
  rfl

/-- **迭代的步进**：$\Sigma^{n+1}(B)=\mathrm{synClosureOne}\,\Sigma\,(\Sigma^n(B))$。

**实现说明**：本引理不是 `rfl`——`Nat.iterate` 在 Lean 中对 `n+1`
走的是 `Function.iterate_succ_apply'`，需要显式 `rw`。 -/
theorem synClosureIter_succ (Sig : Set (Set K.MFCA × Set K.MFCA)) (n : ℕ) (B : Set K.MFCA) :
    K.synClosureIter Sig (n + 1) B = K.synClosureOne Sig (K.synClosureIter Sig n B) := by
  rw [synClosureIter, Function.iterate_succ_apply']
  rfl

/-- **$n$ 步闭包是扩张的**：$B\subseteq\Sigma^n(B)$。 -/
theorem subset_synClosureIter (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) :
    ∀ n : ℕ, B ⊆ K.synClosureIter Sig n B := by
  intro n
  induction n with
  | zero => exact subset_rfl
  | succ k ih =>
      rw [K.synClosureIter_succ]
      exact ih.trans (K.subset_synClosureOne Sig _)

/-- **迭代闭包关于步数单调**：$m\le n\Rightarrow\Sigma^m(B)\subseteq\Sigma^n(B)$。

**证明策略**：先证「固定起点、增加步数」的单向版本 `synClosureIter_le_add`，
再由 $n=m+k$ 转换。这样避免归纳假设中残留不等式前件。 -/
theorem synClosureIter_le_add (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA)
    (m : ℕ) : ∀ k : ℕ,
      K.synClosureIter Sig m B ⊆ K.synClosureIter Sig (m + k) B := by
  intro k
  induction k with
  | zero => exact subset_rfl
  | succ j ih =>
      refine ih.trans ?_
      rw [Nat.add_succ, K.synClosureIter_succ]
      exact K.subset_synClosureOne Sig _

/-- **迭代闭包关于步数单调**：$m\le n\Rightarrow\Sigma^m(B)\subseteq\Sigma^n(B)$。 -/
theorem synClosureIter_mono (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA)
    {m n : ℕ} (h : m ≤ n) : K.synClosureIter Sig m B ⊆ K.synClosureIter Sig n B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact K.synClosureIter_le_add Sig B m k
/-- **迭代闭包遵守 $\Sigma$ 的每条规则**。

若 $(X,Y)\in\Sigma$ 且 $X\subseteq\Sigma^n(B)$，则
$Y\subseteq\Sigma^{n+1}(B)$。

这是「Armstrong 规则在迭代中确实生效」的形式化——
**完备性证明的核心引理**：它说明「一步应用规则」总能被迭代吸收。 -/
theorem synClosureIter_step {Sig : Set (Set K.MFCA × Set K.MFCA)}
    {X Y : Set K.MFCA} (hmem : (X, Y) ∈ Sig) (n : ℕ) {B : Set K.MFCA}
    (hX : X ⊆ K.synClosureIter Sig n B) :
    Y ⊆ K.synClosureIter Sig (n + 1) B := by
  rw [K.synClosureIter_succ]
  exact K.synClosureOne_respects hmem hX

/-! ### §4.2 有界迭代（有限属性集上的收敛）

**技术核心**：在有限属性集上，**属性集的包含链必然稳定**。
故存在一个 $n$，使 $\Sigma^n(B)=\Sigma^{n+1}(B)$，即迭代**收敛**。

**本实现用一个「链长」常数 `chainBound`** 给出该 $n$ 的存在性，
其取值为 $|\mathcal{P}(M_{\mathrm{FCA}})|$——
即属性集的**幂集基数**（有限性前件下为 $\mathbb{N}$ 中的某数）。

**为什么用幂集基数**：属性侧闭包是 $\mathcal{P}(M)\to\mathcal{P}(M)$ 的映射，
其**严格递增链的最长长度不超过幂集的基数**（每步至少增加一个元素）。
这是**鸽巢原理式的论证**，不依赖任何额外结构。 -/

/-- **有限属性集的幂集基数**：迭代收敛的步数上界。

**说明**：本定义在**无限**属性集上取 $0$——
但这不影响完备性定理，因为该定理**要求** `FiniteAttrs` 实例，
此时 `Fintype.card` 有意义。

**实现细节**：为在无限情形也保持定义的非空性，
本实现用 `Fintype.card` 配合 `Fintype` 实例；无实例时取 $0$。 -/
noncomputable def chainBound [Fintype K.MFCA] : ℕ := 2 ^ Fintype.card K.MFCA

/-- **有界迭代的收敛性（抽象形式）**：

若 $\Sigma$ 的**每条规则都是 $\mathbb{K}$ 中的真蕴含**（即 $\Sigma$ 可靠），
则 $\Sigma^n(B)$ 的任何元素都可由 $B\cup\mathrm{semClosure}$ 给出。

**本实现的处置（诚实说明）**：
下面这条定理给出的是**可靠性方向在迭代上的保持**——
即迭代闭包**不会推出 $\mathbb{K}$ 中不成立的属性**。
这是完备性证明的**必要组成部分**（否则「语法闭包」会推出错的东西）。

**反向（语法闭包 ⊆ 语义闭包）**由本定理给出；
**正向（语义闭包 ⊆ 语法闭包）**即完备性，需要伪内涵的覆盖论证，
见 §5。 -/
theorem synClosureIter_subset_semClosure
    {Sig : Set (Set K.MFCA × Set K.MFCA)}
    (hsound : ∀ r ∈ Sig, K.Models r.1 r.2) (B : Set K.MFCA) :
    ∀ n : ℕ, K.synClosureIter Sig n B ⊆ K.semClosure B := by
  intro n
  induction n with
  | zero =>
      -- Σ⁰(B) = B ⊆ B''
      exact fun _ hm => K.subset_closureOp B hm
  | succ k ih =>
      intro m hm
      rw [K.synClosureIter_succ] at hm
      rcases hm with hm | ⟨X, Y, hXY, hX, hmY⟩
      · exact ih hm
      · -- 由可靠性 K ⊨ X ⇒ Y，得 Y ⊆ X''（语义闭包化归）
        have hY : Y ⊆ K.semClosure X :=
          (K.models_iff_subset_semClosure (A := X) (B := Y)).mp (hsound (X, Y) hXY)
        -- 又 X ⊆ Σ^k(B) ⊆ B''，而 B'' 是闭集（幂等），故 X'' ⊆ B''
        have hXB : X ⊆ K.semClosure B := fun a ha => ih (hX ha)
        have hXX : K.semClosure X ⊆ K.semClosure B := by
          have h1 : K.closureOp X ⊆ K.closureOp (K.closureOp B) := K.closureOp_mono hXB
          rwa [K.closureOp_idem B] at h1
        exact hXX (hY hmY)

/-- **DG 基是可靠的**（作为 `synClosureIter_subset_semClosure` 的输入）。 -/
theorem dgbasis_sound' : ∀ r ∈ K.DGBasis, K.Models r.1 r.2 := fun _ hr =>
  K.dgbasis_sound hr

/-- **由 DG 基迭代出的属性都在语义闭包内**（**可靠性在迭代上的完全形式**）：

$$\mathrm{synClosureIter}\,\mathrm{DGBasis}\,n\,B \subseteq B''$$

**这是完备性证明的「不推错」一半**，已完整证明。 -/
theorem dgbasisIter_subset_semClosure (B : Set K.MFCA) :
    ∀ n : ℕ, K.synClosureIter K.DGBasis n B ⊆ K.semClosure B :=
  K.synClosureIter_subset_semClosure K.dgbasis_sound' B

/-! ===========================================================================
    §5  DG 基的完备性（规格 T1A.10 的「完备」一半）
    =========================================================================== -/

/-- **极小不闭超集的存在性**（有限性前件下的良基论证）。

若 $B$ 不闭，则存在**极小**的包含 $B$ 的不闭集合 $P$：
- $B\subseteq P$；
- $P$ 不闭；
- 对任意 $C$：若 $B\subseteq C\subsetneq P$，则 $C$ **闭**。

**证明**：在有限属性集上，集合的**势**（`Set.ncard`）在严格包含下严格减小
（Mathlib 的 `Set.ncard_lt_ncard`）。故「包含 $B$ 且不闭」这一族
（非空，$B$ 自身在其中）按势取极小者即为所求。

**⚠ 边界**：本引理**要求** `FiniteAttrs`。
无限属性集上该族可能没有极小元（下降链不终止）。 -/
theorem exists_minimal_nonclosed [K.FiniteAttrs] {B : Set K.MFCA}
    (hB : ¬ K.IsClosedAttr B) :
    ∃ P : Set K.MFCA, B ⊆ P ∧ ¬ K.IsClosedAttr P ∧
      ∀ C : Set K.MFCA, B ⊆ C → C ⊂ P → K.IsClosedAttr C := by
  classical
  -- 势良基：在「包含 B 的不闭集」族中取 ncard 最小者
  obtain ⟨n0, hn0, hn0min⟩ := exists_minimal_of_wellFoundedLT (α := ℕ)
      (fun n => ∃ C : Set K.MFCA, B ⊆ C ∧ ¬ K.IsClosedAttr C ∧ C.ncard = n)
      ⟨B.ncard, B, subset_rfl, hB, rfl⟩
  obtain ⟨C0, hC0B, hC0nc, hC0card⟩ := hn0
  refine ⟨C0, hC0B, hC0nc, ?_⟩
  intro C hCB hClt
  by_contra hCnc
  -- C 也满足族条件，且 ncard C < ncard C0，与极小性矛盾
  have hlt : C.ncard < n0 := by
    rw [← hC0card]
    exact Set.ncard_lt_ncard hClt (FiniteAttrs.finite_set (K := K) C0)
  have hnew : ∃ D : Set K.MFCA, B ⊆ D ∧ ¬ K.IsClosedAttr D ∧ D.ncard = C.ncard :=
    ⟨C, hCB, hCnc, rfl⟩
  exact absurd (hn0min hnew hlt.le) (not_le.mpr hlt)


