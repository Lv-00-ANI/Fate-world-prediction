import Mathlib.Order.Concept
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/Completeness.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-002 D-003
  - 改动：namespace/引用 ProperFit→FateV2.Rules（正文 9 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Rules
open FateV2.Model
open FateV2.Modeling

/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules.Completeness
阶段：**阶段 1B —— DG 基完备性**（规格 T1A.10 的「完备」一半）

---------------------------------------------------------------------------
本文件证明什么
---------------------------------------------------------------------------
规格 `02-证明路线/01-路线图.md` **T1A.10**：

> `DG 基是最小完备蕴含基`｜前件：**形式背景有限**｜类别 ①

本文件证明其中的**完备性**：

> 任一在 $\mathbb{K}$ 中成立的蕴含 $A\Rightarrow B$，
> 都可由 DG 基**经 Armstrong 规则迭代推出**。

形式地：

$$\mathbb{K}\models A\Rightarrow B
  \Longrightarrow \exists n,\ B\subseteq\mathrm{synClosureIter}\,\mathrm{DGBasisSelfRef}\,n\,A$$

**「最小」一半本文件不证**（见文末「未完成项」）。

---------------------------------------------------------------------------
证明策略：**迭代推进**（**本文件的核心，含一次实证纠正**）
---------------------------------------------------------------------------
**先记一次被否证的尝试。** 本实现最初想用

> ~~$A$ 不闭 $\Rightarrow$ 存在伪内涵 $P$ 使 $A\subseteq P$~~

作为枢纽引理。**该形式经穷尽枚举是假的**：
对 $\lvert G\rvert=\lvert M\rvert=3$ 的全部 512 个形式背景、
全部 2119 个不闭 $A$，有 **1053 个反例**。

**真正的枢纽引理方向相反**（本实现经实证找到并验证）：

> **对不闭的 $A$，存在伪内涵 $P\subseteq A$，使 $P''\not\subseteq A$。**
> （即：有一条**可用的**规则，且它**确实推进了**。）

**验证**（脚本 `prototype/fca-alpha/dgbasis_driving_lemma_check.py`）：

| 规模 | 检验数 | 反例数 |
|---|---|---|
| $\lvert M\rvert=3$ | 2119 | **0** |
| $\lvert M\rvert=4$ | 8094 | **0** |
| $\lvert M\rvert=5$ | 18607 | **0** |

**为什么这条是对的（直觉）**：$A$ 不闭意味着「$A$ 遗漏了某些它应满足的属性」。
Duquenne–Guigues 基的性质保证：**遗漏总能被某个由 $A$ 内部触发的伪内涵捕捉到**。

**归纳结构**：对 $\mathrm{ncard}(A''\setminus A)$ 做良基归纳——
每步用上述引理严格减小该差集（因 $P''\not\subseteq A$ 且 $P''\subseteq A''$）。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件中的定理均为**本实现的自建证明**，**零 `sorry` / 零 `axiom`**。
- 依赖 Mathlib 的引理在 `FateV2.Rules.FCA` 中标 `[已知]`。
- **非冗余性已证**（`dgbasisSelfRef_nonredundant`）；但**基数最小性**
  （Theorem 3.49）**未证**——见文末。二者是不同的性质，不得混同。
- **本实现不虚构**文献、作者、年份与数字。
-/


namespace FateV2.Rules

open Set

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ===========================================================================
    §1  完备性的可靠性方向（已在 `FateV2.Rules.Implication` 证过，此处只重述接口）
    =========================================================================== -/

/-- **迭代 DG 基推出的属性都在语义闭包内**（完备性的「不推错」一半）。

$$\mathrm{synClosureIter}\,\mathrm{DGBasisSelfRef}\,n\,A\subseteq A''$$

**本引理已在 `FateV2.Rules.Implication` 中证明**（`synClosureIter_subset_semClosure`）；
此处重述为 **`DGBasisSelfRef` 版本**，供 §3 的完备性定理配套引用。

**证明**：`DGBasisSelfRef` 的每条成员都是真蕴含
（由 `DGBasisSelfRef` 的定义与 `dgRule_models`），
故可用 `synClosureIter_subset_semClosure`。∎ -/
theorem dgbasisSelfRefIter_subset_semClosure (A : Set K.MFCA) :
    ∀ n : ℕ, K.synClosureIter K.DGBasisSelfRef n A ⊆ K.semClosure A := by
  refine K.synClosureIter_subset_semClosure ?_ A
  -- DGBasisSelfRef 的每条成员都是 P ⇒ P''，故是真蕴含
  rintro ⟨X, Y⟩ ⟨P, hP, heq⟩
  rw [heq]
  exact K.dgRule_models P

/-! ===========================================================================
    §2  伪内涵与闭包的交互引理
    =========================================================================== -/

/-- **伪内涵的闭包仍是闭集**：$(P'')''=P''$。 -/
theorem pseudoIntent_closure_closed {P : Set K.MFCA} (_hP : K.IsPseudoIntent P) :
    K.IsClosedAttr (K.closureOp P) :=
  K.closureOp_idem P

/-- **伪内涵的闭包严格更大**：$P\subsetneq P''$（对伪内涵成立）。

由 `FateV2.Rules.Implication` 的 `isPseudoIntent_subset_closureOp` 直接给出。 -/
theorem pseudoIntent_closure_strict {P : Set K.MFCA} (hP : K.IsPseudoIntent P) :
    P ⊂ K.closureOp P :=
  K.isPseudoIntent_subset_closureOp hP

/-- **DG 基中的规则可由迭代应用**（**单步推进引理**）。

若 $P$ 是伪内涵且 $P\subseteq A$，则

$$P''\subseteq\mathrm{synClosureIter}\,\mathrm{DGBasisSelfRef}\,1\,A.$$

**证明**：$P\subseteq A=\Sigma^0(A)$，故由 `synClosureIter_step`
得 $P''\subseteq\Sigma^1(A)$。∎

**这是「规则确实被迭代吸收」的形式化**——
完备性证明的每一步都靠它。 -/
theorem pseudoIntent_closure_subset_iter_one {P A : Set K.MFCA}
    (hP : K.IsPseudoIntent P) (hPA : P ⊆ A) :
    K.closureOp P ⊆ K.synClosureIter K.DGBasisSelfRef 1 A := by
  have hmem : (P, K.closureOp P) ∈ K.DGBasisSelfRef := ⟨P, hP, rfl⟩
  -- 先用 zero_add 把 1 写成 0 + 1
  show K.closureOp P ⊆ K.synClosureIter K.DGBasisSelfRef (0 + 1) A
  refine K.synClosureIter_step hmem 0 (B := A) ?_
  rw [K.synClosureIter_zero]
  exact hPA

/-! ===========================================================================
    §3  完备性：主定理
    =========================================================================== -/

/-! ### §3.1 ⚠ **本路线已被 §4 的语义路线取代**（**保留作历史与对照**）

**本节（`DrivingLemma` / `iterReachesClosure` / `dgbasis_complete`）
所要证的「语法迭代」形式，经裁决 I（先查文献）核实后——
不是教材采用的路线，也不是完备性的必需形式。**

**教材（Ganter–Wille Thm 3.46）的完备性判据是**（逐字）：

> **Complete**: It suffices to show that `Mod(T) ⊆ Int(X,Y,I)`.

即**语义形式**：DG 基的**模型类 $=$ 闭集类**。
该形式**已在 §4 证毕**（`model_iff_closed`、`completeness_Mod_eq_Int`、
`dgbasis_complete_semantic`），**无需任何迭代**。

**两种形式的等价性已实证**（`prototype/fca-alpha/dgbasis_semantic_vs_syntactic.py`）：

| 规模 | 检验的背景数 | 「$\mathrm{Mod}(T)=\mathrm{Int}$」成立 | 「迭代完备」成立 | **不一致** |
|---|---|---|---|---|
| $\lvert M\rvert=3$ | 512 | 512 | 512 | **0** |
| $\lvert M\rvert=4$ | 400 | 400 | 400 | **0** |
| $\lvert M\rvert=5$ | 400 | 400 | 400 | **0** |

**故本节的两个「缺口」实为冗余**：
- `DrivingLemma`——语法版所需，**语义版不需要**；
- `iterReachesClosure`——同上。

**⚠ 重要更新（§4.1 完成后）**：
上述「缺口」如今**已全部闭合**——`iterReachesClosure` 已在 §4.1
**无条件证明**（`semClosure_subset_synClosureIter` / `iterReachesClosure_proved`）。
闭合方式**不是**补上「找 witness」的构造，而是**发现语法形式根本不需要它**：
只需调用 §4 的 `model_iff_closed`（模型 ⟺ 闭集）。
`DrivingLemma` 因此**从未被真正需要**——它只是「找 witness」这条
错误路线的产物。

**本实现保留本节的理由**：
1. **历史记录**——它记录了一次四轮失败的构造探索（负面知识）；
2. **对照价值**——说明「换路线」（语义 vs 语法）如何消除缺口；
3. **可能的后续用途**——若日后需要**构造性/算法性**的完备性陈述
   （如为代码提取提供 `Σ^n` 的具体步数），语法形式**仍有独立价值**。

**但本节的所有命题均标为「非必需」，不得作为完备性的依据。** -/

/-- **完备性的核心归纳步**：只要 $A$ 不闭，迭代就能把闭包差缩小。

**本引理的内容**：存在 $n$，使 $\Sigma^n(A)$ 严格包含 $A$
（即迭代**至少推进了一步**）。

**前件**：`FiniteAttrs`（良基性的来源）+ $A$ **不闭**。

**证明策略（本实现采用的）**：
取**包含于 $A$ 且其闭包不包含于 $A$ 的伪内涵** $P$——
其存在性即 §0 所述的**枢纽引理**（实证验证见文件头表格）。
由 `pseudoIntent_closure_subset_iter_one`，
$P''\subseteq\Sigma^1(A)$，且 $P''\not\subseteq A$，
故 $\Sigma^1(A)\not\subseteq A$，即推进了一步。∎

**⚠ 关于枢纽引理的形式化状态**：
该引理（「存在 $P\subseteq A$ 且 $P''\not\subseteq A$」）的**实证验证已完成**
（28k+ 检验、0 反例），但其 **Lean 形式化证明尚未完成**。
故本引理**以该引理为显式前件**陈述——
这符合规格对**条件定理**的要求：
**前件必须写成 Lean 类型，且不得匿名**。

**本实现不掩盖这一点**：本引理是一个**条件定理**，
其前件 `DrivingLemma` 是**具名的、可陈述的**。 -/
def DrivingLemma (A : Set K.MFCA) : Prop :=
  ∃ P : Set K.MFCA, K.IsPseudoIntent P ∧ P ⊆ A ∧ ¬ K.closureOp P ⊆ A

/-- **由枢纽引理得「迭代至少推进一步」**。

若 $A$ 不闭且枢纽引理对 $A$ 成立，则
$\Sigma^1(A)\not\subseteq A$（迭代确实推进）。 -/
theorem iter_one_advances {A : Set K.MFCA} (h : K.DrivingLemma A) :
    ¬ K.synClosureIter K.DGBasisSelfRef 1 A ⊆ A := by
  obtain ⟨P, hP, hPA, hPnot⟩ := h
  intro hsub
  exact hPnot ((K.pseudoIntent_closure_subset_iter_one hP hPA).trans hsub)

/-! ### ⚠ 已删除：`dgbasis_complete`（同义反复）

**删除依据**：`审计-定理实质度.md` §2.4.2 与根因 6。

**原陈述**：
```lean
theorem dgbasis_complete
    (hreach : ∀ A, ∃ n, K.semClosure A ⊆ K.synClosureIter K.DGBasisSelfRef n A)
    {A B} (h : K.Models A B) :
    ∃ n, B ⊆ K.synClosureIter K.DGBasisSelfRef n A
```

**问题**：前件 `hreach` **就是完备性本身**（且更强：要求**语法**迭代达到）。
故该定理是**同义反复** —— 结论由前件直接推出，无独立数学内容。

**而真正的完备性已在本文件 §4 无条件证毕**（`completeness_Mod_eq_Int` /
`model_iff_closed` / `dgbasis_complete_semantic`）。

**为何删除而非保留**：保留会让人误以为「完备性还有缺口」——
**误导性大于其登记价值**。删除后，完备性的唯一权威陈述是 §4 的无条件版本。

**⚠ 历史保留**：原文已备份为 `Completeness.lean.bak-p6`；
`裁决记录.md` 中关于本定理四轮尝试的记录**不动**（那是历史，有价值）。
-/


/-- **`iterReachesClosure`（= `semClosure_subset_synClosureIter` 的逐点形式）**。

**⚠ 状态更新（本节初版撰写后补记）**：
本引理曾被登记为「未完成的形式化策略」。
**现已在 §4.1 无条件证明**（仅需 `FiniteAttrs`）——见
`semClosure_subset_synClosureIter`，其陈述与本定义**逐字相同**。

**此前四轮失败的原因已诊断清楚**（见 §4.1 的说明）：
失败的是「构造伪内涵 witness」这条**不必要的**路线；
正确的路线是调用 §4 已证的 `model_iff_closed`（模型 ⟺ 闭集）。 -/
def iterReachesClosure (A : Set K.MFCA) : Prop :=
  ∃ n : ℕ, K.semClosure A ⊆ K.synClosureIter K.DGBasisSelfRef n A

/-- **不闭子集的存在性引理（构造性的极小元）**。

若 $A$ 不闭，则存在**极小**的不闭子集 $P_0\subseteq A$：
$P_0$ 不闭，且 $P_0$ 的**每个真子集都闭**。

**证明**：对「$A$ 的不闭子集」这一族取 $\mathrm{ncard}$ 极小元。
非空（$A$ 自身在其中）。∎

**本引理已完整证明**（无前件）。 -/
theorem exists_minimal_nonclosed_subset [K.FiniteAttrs] {A : Set K.MFCA}
    (hA : ¬ K.IsClosedAttr A) :
    ∃ P₀ : Set K.MFCA, P₀ ⊆ A ∧ ¬ K.IsClosedAttr P₀ ∧
      ∀ Q : Set K.MFCA, Q ⊂ P₀ → K.IsClosedAttr Q := by
  classical
  obtain ⟨n₀, hn₀, hn₀min⟩ := exists_minimal_of_wellFoundedLT (α := ℕ)
      (fun n => ∃ C : Set K.MFCA, C ⊆ A ∧ ¬ K.IsClosedAttr C ∧ C.ncard = n)
      ⟨A.ncard, A, subset_rfl, hA, rfl⟩
  obtain ⟨P₀, hP₀A, hP₀nc, hP₀card⟩ := hn₀
  refine ⟨P₀, hP₀A, hP₀nc, ?_⟩
  intro Q hQ
  by_contra hQnc
  have hlt : Q.ncard < n₀ := by
    rw [← hP₀card]
    exact Set.ncard_lt_ncard hQ (FiniteAttrs.finite_set (K := K) P₀)
  exact absurd (hn₀min ⟨Q, hQ.1.trans hP₀A, hQnc, rfl⟩ hlt.le) (not_le.mpr hlt)

/-- **极小不闭子集必是伪内涵**（**已完整证明**）。

设 $P_0$ 是 $A$ 的极小不闭子集，则 $P_0$ 满足 `IsPseudoIntent`。

**证明**：伪内涵定义的第二条要求
「对 $Q\subsetneq P_0$，若 $Q$ 满足该性质则 $Q''\subseteq P_0$」。
但由 $P_0$ 的**极小性**，$P_0$ 的每个真子集都**闭**；
而该性质的第一分量要求 $Q$ **不闭**——
**前提恒为假，条件空洞成立**。∎

**这是「空洞成立」（`ex falso` 式论证）的一次实质运用。** -/
theorem minimal_nonclosed_subset_isPseudoIntent {P₀ : Set K.MFCA}
    (hmin : ∀ Q : Set K.MFCA, Q ⊂ P₀ → K.IsClosedAttr Q)
    (hnc : ¬ K.IsClosedAttr P₀) : K.IsPseudoIntent P₀ := by
  rw [K.isPseudoIntent_iff]
  refine ⟨hnc, ?_⟩
  intro Q hQP _ hQcond
  exact absurd (hmin Q hQP) (K.not_isClosedAttr_of_isPseudoIntent hQcond)

/-! ### §2.1 **四个被实证排除的构造**（**记录在此，防止重走弯路**）

本实现的**目标是构造性地找出**枢纽引理
「存在伪内涵 $P\subseteq A$ 使 $P''\not\subseteq A$」的**证明**。

**已尝试四条候选构造，均被实证排除**：

| # | 候选构造 | $\lvert M\rvert=3$ | $\lvert M\rvert=4$ | $\lvert M\rvert=5$ |
|---|---|---|---|---|
| 1 | **极小不闭子集** $P_0$ 满足 $P_0''\not\subseteq A$ | **114 反例** ❌ | — | — |
| 2 | **极大伪内涵** $P\subseteq A$ 满足 $P''\not\subseteq A$ | 0 反例 ✅ | **159 反例** ❌ | **860 反例** ❌ |
| 3 | $A''$ 被 $\{P''\mid P\text{ 伪内涵},P\subseteq A\}$ 的并覆盖 | **684 反例** ❌ | — | — |
| 4 | **情形分析**：$P_0''\not\subseteq A$ 用 $P_0$；否则用 $A$ 自身 | 0 反例 ✅ | **372 反例** ❌ | **1736 反例** ❌ |

**构造 2 与构造 4 是两个「小规模通过」的实例**：
二者在 $\lvert M\rvert=3$ 上**完全通过**（2119 检验零反例），
在 $\lvert M\rvert=4$ 上即失败——
**这正是本实现反复强调的「小规模通过 ≠ 正确」**
（参见 `裁决记录.md` R-009、R-011、R-012）。

**构造 4 尤其具有误导性**：它建立在一条**已证**引理
（`minimal_nonclosed_subset_isPseudoIntent`）与一个**在小规模上完美成立**的
情形分析之上。**若本实现只测最小规模，它会是一个看起来完全可靠的证明骨架。**

核查脚本：
- `prototype/fca-alpha/dgbasis_maxwitness_check.py`（候选 2）
- `prototype/fca-alpha/dgbasis_case_analysis_check.py`（候选 4）

**结论**：枢纽引理**为真**（`dgbasis_driving_lemma_check.py`：
$\lvert M\rvert\le5$ 共 28,820 检验零反例），
但**「找 witness」这条路线四轮尝试均失败**。

**故第五轮（依作者裁决「最后试一次」）换了路线**——见 §2.2。 -/

/-! ### §2.2 **第五轮：改用「模型特征」路线**（**成功**）

**思路转变**：前四轮都在**找一个具体的伪内涵 $P$**（「找 witness」路线）。
本轮改用**标准证明的特征引理**（Ganter–Wille 教材 Thm 3.46 的证明结构）。

**关键定义**：属性集 $M$ 是 DG 基的**模型** $\iff$

$$\forall P,\ \big(P\text{ 为伪内涵} \wedge P\subseteq M\big)\Longrightarrow P''\subseteq M.$$

**关键引理（本轮的核心）**：

$$M\text{ 是 DG 基的模型} \iff M\text{ 是闭集（}M''=M\text{）}$$

**跨规模实证验证**（`prototype/fca-alpha/dgbasis_keylemma_check.py`）：

| 规模 | 检验数 | 反例数 |
|---|---|---|
| $\lvert M\rvert=3$ | 4096 | **0** |
| $\lvert M\rvert=4$ | 6400 | **0** |
| $\lvert M\rvert=5$ | 12800 | **0** |

**为什么这条路线比「找 witness」好**：

1. **两个方向的可证性不对称**：
   - $(\Leftarrow)$ $M$ 闭 $\Rightarrow$ $M$ 是模型：**平凡**——
     $P\subseteq M$ 与 $M''=M$ 由 `closureOp_mono` 给出 $P''\subseteq M''=M$；
   - $(\Rightarrow)$ $M$ 是模型 $\Rightarrow$ $M$ 闭：**这才是实质**，
     也是完备性的真正核心。
2. **不需要构造 witness**——前四轮失败的正是「构造」这一步。

**⚠ 本轮的诚实状态**：
$(\Leftarrow)$ 方向**已证**（见 `model_of_closed`）；
$(\Rightarrow)$ 方向**仍未证**，但**已被化为一条清晰的引理**
（`ClosedOfModel`），其陈述比原枢纽引理更接近标准证明的结构。

**本实现不声称完备性已完全形式化。** -/

/-- **$M$ 是 DG 基的模型**（Ganter–Wille 特征引理的左端）。

$M$ 是模型 $\iff$ 对每个伪内涵 $P\subseteq M$，有 $P''\subseteq M$。

**这与「$M$ 在 Armstrong 迭代下不变」等价**——
因为 DG 基的每条规则是 $P\Rightarrow P''$，
而「$M$ 被所有可用规则封闭」正是上式。 -/
def IsModel (M : Set K.MFCA) : Prop :=
  ∀ P : Set K.MFCA, K.IsPseudoIntent P → P ⊆ M → K.closureOp P ⊆ M

/-- **特征引理的 $(\Leftarrow)$ 方向（已证）**：

$M$ 闭 $\Longrightarrow$ $M$ 是 DG 基的模型。

**证明**：设 $P$ 是伪内涵且 $P\subseteq M$。
由 `closureOp_mono` 得 $P''\subseteq M''$；
而 $M$ 闭即 $M''=M$，故 $P''\subseteq M$。∎

**这是一个真正的证明**（不是条件形式）。 -/
theorem model_of_closed {M : Set K.MFCA} (hM : K.IsClosedAttr M) : K.IsModel M :=
  fun _ _ hPM => by
    have h := K.closureOp_mono hPM
    rwa [hM] at h

/-- **$M$ 是伪内涵**（在 $M$ 不闭时，由「$M$ 是模型」推出）。

**这是 Ganter–Wille Thm 3.46 完备性证明的第一步**（原文：

> 「Assume $C\neq C^{\downarrow\uparrow}$. **Then $C$ is a pseudo-intent**
> (indeed, if $P\subsetneq C$ is a pseudo-intent then since
> $\|P\Rightarrow P^{\downarrow\uparrow}\|_C=1$, we get $P^{\downarrow\uparrow}\subseteq C$).」
> ）

**证明**：伪内涵定义条件 1 即 $M\neq M''$（本假设）；
条件 2 要求「对 $Q\subsetneq M$ 且 $Q$ 满足同样性质，有 $Q''\subseteq M$」——
由 $M$ 是模型与 $Q\subseteq M$ 直接给出。∎

**注意**：本证明**只用到了 $M$ 是模型这一假设**，
**不需要** $M$ 的其它结构性质——这正是标准证明简洁的原因。 -/
theorem isPseudoIntent_of_isModel_of_not_closed {M : Set K.MFCA}
    (hM : K.IsModel M) (hne : ¬ K.IsClosedAttr M) : K.IsPseudoIntent M := by
  rw [K.isPseudoIntent_iff]
  refine ⟨hne, ?_⟩
  intro Q hQM _hcard hQcond
  -- Q ⊂ M 给出 Q ⊆ M；Q 是伪内涵，故由 M 是模型得 Q'' ⊆ M
  exact hM Q hQcond hQM.1

/-- **特征引理的 $(\Rightarrow)$ 方向（**已证**）**：

$M$ 是 DG 基的模型 $\Longrightarrow$ $M$ 闭。

**这是完备性的真正核心**，也是 Ganter–Wille Thm 3.46 完备性证明的实质一步。

**本实现的证明严格沿用教材骨架**（见 `裁决记录.md` R-017 的逐字摘录）：

1. 设 $M$ 是模型且 $M\neq M''$（反证假设）；
2. 由 `isPseudoIntent_of_isModel_of_not_closed` 得 **$M$ 是伪内涵**；
3. 于是 $M\Rightarrow M''$ **属于 DG 基**；
4. $M$ 是模型且 $M\subseteq M$，故 $M''\subseteq M$；
5. 结合扩展性 $M\subseteq M''$ 得 $M''=M$——**与步骤 1 矛盾**；
6. 故 $M''=M$，即 $M$ 闭。∎

**这一条此前是具名前件（`def ClosedOfModel`），
现依作者裁决 I（先查文献）从「找不到证明的缺口」
变为「有标准证明、已转写」。** -/
theorem closed_of_model {M : Set K.MFCA} (hM : K.IsModel M) : K.IsClosedAttr M := by
  by_contra hne
  -- 步骤 2：M 是伪内涵
  have hpseudo : K.IsPseudoIntent M := K.isPseudoIntent_of_isModel_of_not_closed hM hne
  -- 步骤 3-4：M ⇒ M'' 属于 DG 基，且 M 是模型、M ⊆ M，故 M'' ⊆ M
  have hsub : K.closureOp M ⊆ M := hM M hpseudo subset_rfl
  -- 步骤 5：结合扩展性得 M'' = M，与 hne 矛盾
  exact hne (Set.Subset.antisymm hsub (K.subset_closureOp M))

/-- **完备性的最终形式：模型 $\iff$ 闭集**（**两个方向均已证**）。

$$M\text{ 是 DG 基的模型}\iff M\text{ 是闭集}$$

**这是 Ganter–Wille Thm 3.46 完备性证明的完整转写**：

- $(\Leftarrow)$ `model_of_closed`；
- $(\Rightarrow)$ `closed_of_model`。

**教材对「完备」的判据（逐字，`_refs/ganter-wille.txt` L2338）**：

> **Complete**: It suffices to show that `Mod(T) ⊆ Int(X,Y,I)`.

而 $\mathrm{Mod}(T)\supseteq\mathrm{Int}$ 是**平凡**的
（闭集满足每条 $P\Rightarrow P''$）——即 `model_of_closed`。

**故本定理 $=$ 教材所要的「$T$ 完备」**。 -/
theorem model_iff_closed (M : Set K.MFCA) : K.IsModel M ↔ K.IsClosedAttr M :=
  ⟨K.closed_of_model, K.model_of_closed⟩

/-- **教材意义下的完备性**：$\mathrm{Mod}(T)=\mathrm{Int}(\mathbb{K})$。

**教材 `Mod(T)` 的定义**（逐字，`_refs/ganter-wille.txt` L1919）：

> `Mod(T) = {M ⊆ Y | ||A ⇒ B||_M = 1 for every A ⇒ B ∈ T}`

本实现的 `IsModel` 正是该定义（以「$P$ 伪内涵 $\wedge P\subseteq M
\Rightarrow P''\subseteq M$」表述，与逐条满足 $T$ 等价）。

**本定理即教材「$T$ 完备」的形式化**，由 `model_iff_closed` 直接给出。 -/
theorem completeness_Mod_eq_Int :
    {M : Set K.MFCA | K.IsModel M} = {M : Set K.MFCA | K.IsClosedAttr M} := by
  ext M
  exact K.model_iff_closed M

/-- **回归原始陈述：DG 基在「推出关系」意义下完备**。

**规格 `02-定理清单.md` T1A.10 的完备性原话**：

> 任一在 $\mathbb{K}$ 中成立的蕴含 $A\Rightarrow B$，
> 都可由 DG 基**经 Armstrong 规则推出**。

**本实现在此给出其精确形式**：
若 $A\Rightarrow B$ 在 $\mathbb{K}$ 中成立（即 `Models A B`），
则**任何** DG 基的模型若满足 $A$ 必满足 $B$。

**证明**：设 $M$ 是模型且 $A\subseteq M$。
由 `closed_of_model` 得 $M''=M$；
由 $\mathbb{K}\models A\Rightarrow B$ 与 `models_iff_subset_semClosure`
得 $B\subseteq A''$；
再由 `closureOp_mono` 得 $B\subseteq A''\subseteq M''=M$。∎

**这就是「推出」的语义刻画**：DG 基的模型类**恰好**刻画了
$\mathbb{K}$ 中一切成立的蕴含——
因为模型类 $=$ 闭集类，而闭集类正是 $\mathrm{Mod}(\text{全部真蕴含})$。

**⚠ 与先前路线的对比（重要）**：
本实现此前试图证明「$B\subseteq\Sigma^n(A)$」这一**语法迭代**形式
（`iterReachesClosure`），四轮构造失败。
**教材的路线绕开了语法迭代**：直接证 $\mathrm{Mod}(T)=\mathrm{Int}$，
而**集合相等已蕴含两条推出关系等价**。
**故 `iterReachesClosure` 不再是必需的**——见下。 -/
theorem dgbasis_complete_semantic {A B : Set K.MFCA} (h : K.Models A B)
    {M : Set K.MFCA} (hM : K.IsModel M) (hA : A ⊆ M) : B ⊆ M := by
  have hMcl : K.IsClosedAttr M := K.closed_of_model hM
  have hB : B ⊆ K.semClosure A := (K.models_iff_subset_semClosure).mp h
  have h1 : K.closureOp A ⊆ K.closureOp M := K.closureOp_mono hA
  rw [show K.closureOp M = M from hMcl] at h1
  exact hB.trans h1

/-! ===========================================================================
    §4.1  **语法完备性**（`iterReachesClosure`）——**此前四轮失败的反向包含**
    ===========================================================================

**本节目的**：证明此前被登记为「四轮构造失败」的反向包含，即

$$\mathrm{semClosure}\,A\subseteq\mathrm{synClosureIter}\,\mathrm{DGBasisSelfRef}\,n\,A$$

**此前失败的原因（诊断）**：前四轮（见 §3.1 与 §2.1 的表格）都在
「**找一个具体的伪内涵 witness** $P\subseteq A$ 使 $P''\not\subseteq A$」这条
「构造 witness」路线上。而这条路线**是不必要的**：
完备性的枢纽不是某个具体的 $P$，而是
**§4 已证的 `model_iff_closed`（模型 ⟺ 闭集）**。

**本节的证明结构（不构造任何 witness）**：

1. **链单调**：$\Sigma^0(A)\subseteq\Sigma^1(A)\subseteq\cdots$
   （由 `subset_synClosureOne` 逐步给出）；
2. **有限稳定**：属性集有限 $\Rightarrow$ 存在 $n$ 使
   $\Sigma^n(A)=\Sigma^{n+1}(A)$（`exists_synClosureIter_stabilize`，鸽巢式）；
3. **稳定点即模型**：$\mathrm{synClosureOne}\,\Sigma\,C\subseteq C$
   $\Rightarrow$ $C$ 是 `IsModel`（逐条应用规则即得）；
4. **模型即闭集**：由 **§4 的 `closed_of_model`**（已证）得
   $\Sigma^n(A)$ 闭；
5. **闭包最小**：$A\subseteq\Sigma^n(A)$ 且后者闭 $\Rightarrow$
   $A''\subseteq(\Sigma^n(A))''=\Sigma^n(A)$。∎

**关键点**：第 4 步调用的正是 §4 的 `closed_of_model`——
它与本节的反向包含**是同一个数学事实**的两个朝向。
**故「四轮失败」的缺口不是靠新构造补上的，而是靠换掉枢纽引理**。 -/

/-- **有限链的稳定**：在有限属性集上，`synClosureIter` 的迭代链必在有限步稳定。

$$\exists n,\ \Sigma^n(B)=\Sigma^{n+1}(B).$$

**证明**（鸽巢）：若永不相等，则由链单调性每步都**严格**扩张，
故 `ncard` 每步严格递增。于是 $k\le\mathrm{ncard}\,(\Sigma^k(B))\le|M|$
对所有 $k$ 成立——取 $k=|M|+1$ 即矛盾。∎

**与 §3.1 的 `iterReachesClosure` 的关系**：
本引理是后者的**存在性来源**。此前 `iterReachesClosure` 被登记为
「未完成的形式化」；**本节直接证出它**（见 `semClosure_subset_synClosureIter`）。 -/
theorem exists_synClosureIter_stabilize [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (B : Set K.MFCA) :
    ∃ n : ℕ, K.synClosureIter Sig n B = K.synClosureIter Sig (n + 1) B := by
  by_contra hnot
  push Not at hnot
  -- 每步严格扩张
  have hstep : ∀ k : ℕ,
      K.synClosureIter Sig k B ⊆ K.synClosureIter Sig (k + 1) B := by
    intro k
    rw [K.synClosureIter_succ]
    exact K.subset_synClosureOne Sig _
  have hss : ∀ k : ℕ,
      K.synClosureIter Sig k B ⊂ K.synClosureIter Sig (k + 1) B :=
    fun k => (Set.ssubset_iff_subset_ne).2 ⟨hstep k, hnot k⟩
  -- ncard 每步严格递增
  have hcard : ∀ k : ℕ, (K.synClosureIter Sig k B).ncard <
      (K.synClosureIter Sig (k + 1) B).ncard :=
    fun k => Set.ncard_lt_ncard (hss k) (FiniteAttrs.finite_set (K := K) _)
  -- 故 k ≤ ncard(Σ^k B)
  have hbound : ∀ k : ℕ, k ≤ (K.synClosureIter Sig k B).ncard := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hcard k))
  -- 但 ncard ≤ |M|
  have hle_univ : ∀ k : ℕ,
      (K.synClosureIter Sig k B).ncard ≤ (Set.univ : Set K.MFCA).ncard :=
    fun k => Set.ncard_le_ncard (Set.subset_univ _) (FiniteAttrs.finite (K := K))
  have hfin : (Set.univ : Set K.MFCA).ncard = Nat.card K.MFCA := Set.ncard_univ _
  have hbig := hbound (Nat.card K.MFCA + 1)
  have hsmall := hle_univ (Nat.card K.MFCA + 1)
  rw [hfin] at hsmall
  omega

/-- **一步闭包被遵守 $\Rightarrow$ 模型**：
若 $\mathrm{synClosureOne}\,\mathrm{DGBasisSelfRef}\,C\subseteq C$，
则 $C$ 是 DG 基的模型（`IsModel C`）。

**证明**：设 $P$ 是伪内涵且 $P\subseteq C$。则 $(P,P'')\in\mathrm{DGBasisSelfRef}$，
故 $P''\subseteq\mathrm{synClosureOne}\,\cdots\,C\subseteq C$。∎

**这是「稳定点即模型」的精确形式**——它说明迭代稳定后
**再也没有任何规则可用**，故 $C$ 满足所有可用蕴含。 -/
theorem isModel_of_synClosureOne_subset {C : Set K.MFCA}
    (h : K.synClosureOne K.DGBasisSelfRef C ⊆ C) : K.IsModel C := by
  intro P hP hPC
  have hmem : (P, K.closureOp P) ∈ K.DGBasisSelfRef := ⟨P, hP, rfl⟩
  exact (K.synClosureOne_respects hmem hPC).trans h

/-- **语法完备性（反向包含）**：在有限属性集上，语义闭包必被
**有限步**的 DG 基 Armstrong 迭代所包含。

$$\exists n,\ \mathrm{semClosure}\,A\subseteq
  \mathrm{synClosureIter}\,\mathrm{DGBasisSelfRef}\,n\,A$$

**这正是 `iterReachesClosure A` 的定义**——
本定理**无条件证明了它**（仅需 `FiniteAttrs`）。

**证明**：取稳定步数 $n$（`exists_synClosureIter_stabilize`），
令 $C=\Sigma^n(A)$。由 `synClosureIter_succ`，
$\mathrm{synClosureOne}\,\mathrm{DGBasisSelfRef}\,C=C$。
故 $C$ 是模型（`isModel_of_synClosureOne_subset`），
从而是闭集（§4 的 `closed_of_model`）。
又 $A\subseteq C$，故 $A''\subseteq C''=C$，即 $\mathrm{semClosure}\,A\subseteq C$。∎

**与 `synClosureIter_subset_semClosure` 合起来**：
$$\bigcup_n \mathrm{synClosureIter}\,\mathrm{DGBasisSelfRef}\,n\,A
  =\mathrm{semClosure}\,A$$
即语法闭包与语义闭包**在有限属性集上一致**——这正是规格 T1A.10
「任一成立的蕴含都可由 DG 基经 Armstrong 规则推出」的**字面形式**。 -/
theorem semClosure_subset_synClosureIter [K.FiniteAttrs] (A : Set K.MFCA) :
    ∃ n : ℕ, K.semClosure A ⊆ K.synClosureIter K.DGBasisSelfRef n A := by
  obtain ⟨n, hn⟩ := K.exists_synClosureIter_stabilize K.DGBasisSelfRef A
  refine ⟨n, ?_⟩
  set C := K.synClosureIter K.DGBasisSelfRef n A with hC
  -- 稳定点：synClosureOne C = C
  have hstab : K.synClosureOne K.DGBasisSelfRef C = C := by
    have h := hn
    rw [K.synClosureIter_succ] at h
    exact h.symm
  -- 稳定点即模型，模型即闭集
  have hclosed : K.IsClosedAttr C :=
    K.closed_of_model (K.isModel_of_synClosureOne_subset (le_of_eq hstab))
  -- A ⊆ C，闭包最小
  have hAC : A ⊆ C := K.subset_synClosureIter K.DGBasisSelfRef A n
  have h := K.closureOp_mono hAC
  rwa [hclosed] at h

/-- **语法与语义闭包的双向包含（合并陈述）**：

$$\exists n,\ \mathrm{semClosure}\,A=\mathrm{synClosureIter}\,
  \mathrm{DGBasisSelfRef}\,n\,A.$$

即：**在有限属性集上，语义闭包恰是某一有限步的语法闭包**。

**证明**：取 `semClosure_subset_synClosureIter` 给出的 $n$，
另一方向由 `dgbasisSelfRefIter_subset_semClosure` 给出，双向 `antisymm`。∎ -/
theorem semClosure_eq_synClosureIter [K.FiniteAttrs] (A : Set K.MFCA) :
    ∃ n : ℕ, K.semClosure A = K.synClosureIter K.DGBasisSelfRef n A := by
  obtain ⟨n, hn⟩ := K.semClosure_subset_synClosureIter A
  exact ⟨n, Set.Subset.antisymm hn (K.dgbasisSelfRefIter_subset_semClosure A n)⟩

/-- **`iterReachesClosure` 已被无条件证明**（此前登记为「未完成形式的策略」）。

本定理即 §4.1 主定理的直接重述，故立得。 -/
theorem iterReachesClosure_proved [K.FiniteAttrs] (A : Set K.MFCA) :
    K.iterReachesClosure A :=
  K.semClosure_subset_synClosureIter A

/-! ===========================================================================
    §5  「最小性」（T1A.10 的「最小」一半）——**依作者裁决 I 先查文献**
    =========================================================================== -/

/- **教材对「最小性」的处理**（逐字，`_refs/ganter-wille.txt`）。

> **Definition 3.38**（non-redundant set of AIs）. A set $T$ of attribute
> implications is called **non-redundant** if for any $A\Rightarrow B\in T$
> we have $T-\{A\Rightarrow B\}\not\models A\Rightarrow B$.
>
> **Theorem 3.40**（criterion for $T$ being complete）.
> $T$ is complete in $\langle X,Y,I\rangle$
> **iff** $\mathrm{Mod}(T)=\mathrm{Int}(X,Y,I)$.
>
> **Lemma 3.48**. If $T$ is complete, then for each pseudo-intent $P$,
> $T$ contains $A\Rightarrow B$ with $A^{\downarrow\uparrow}=P^{\downarrow\uparrow}$.
>
> **Theorem 3.49**（Guigues-Duquenne basis is the **smallest** one）.
> If $T$ is the Guigues-Duquenne base and $T'$ is complete then $|T|\le|T'|$.
> Proof. **Direct corollary of the above Lemma.**

**⚠ 本实现的形式化范围（诚实标注）**：

| 项 | 教材 | 本实现 |
|---|---|---|
| **Theorem 3.40**（完备性判据） | 已证（教材证明略） | ✅ **已证**（`completeness_Mod_eq_Int`，§4） |
| **Definition 3.38**（非冗余） | 定义 | ✅ **已形式化**（`IsNonRedundant`，只是**谓词定义**） |
| **非冗余性**（DG 基满足 3.38） | Thm 3.46 的 Non-redundant 部分 | ✅ **已证**（`dgbasisSelfRef_nonredundant`，无前件除 `FiniteAttrs`） |
| **Theorem 3.49**（**基数最小**） | 「Lemma 3.48 的直接推论」 | ❌ **未做** |

**⚠ 上表第 3 行的历史（**如实记录，依 `裁决记录.md` R-021/R-022**）**：
本文件**曾**在此行写入「✅ **已证**（`dgbasis_nonredundant`）」——
但**该定理从未存在**（一次虚假完工声明，见 R-022）。
修正为「🟡 实证已验，形式化未完成」后，**本轮又真正证明了它**：
定理名为 `dgbasisSelfRef_nonredundant`，其证明**依赖 `IsPseudoIntent` 的良基递归定义**
（见 `Implication.lean`）——旧定义（扁平形）下该定理**为假**。
故本次「✅ 已证」**有真实定理支撑**，与 R-022 的虚假声明**性质不同**。

**教训（本实现记录在案）**：
**注释里的假声明比代码错误更危险**——代码错了编译不过，
注释错了会**静默污染所有依赖它的后续论证**。
故 `SigCheck` 新增 **Check 6** 以机械检出此类声明。

**关于 Theorem 3.49 未做的原因（技术性，必须说明）**：
其证明依赖 **Lemma 3.48**，而 Lemma 3.48 的证明使用了
「$\mathrm{Mod}(T)$ 是闭包系统」「$A^{\downarrow\uparrow}\cap P$ 不是 intent」
等**教材前文的若干结果**（原文以「(Thm. on basic connections…)」「()」
**引用先前编号**）。**完整转写须先形式化那些前文结果**，属**独立工作量**。
**本实现如实登记为未做。** -/

/-- **「$M$ 是 $\Sigma$ 的模型」**（相对**任意**蕴含集 $\Sigma$，不只 DG 基）。

教材 `Mod(T)` 的定义（逐字，L1919）：

> `Mod(T) = {M ⊆ Y | ||A ⇒ B||_M = 1 for every A ⇒ B ∈ T}`

**本定义即逐字转写**：$M$ 满足 $\Sigma$ 中每条**可用**（前件被 $M$ 包含）的蕴含。

**与 §4 的 `IsModel` 的关系**：`IsModel` 是
$\Sigma=\mathrm{DGBasisSelfRef}$ 的特例（见 `isModel_iff_isModelOf_dgbasis`）。 -/
def IsModelOf (Sig : Set (Set K.MFCA × Set K.MFCA)) (M : Set K.MFCA) : Prop :=
  ∀ r ∈ Sig, r.1 ⊆ M → r.2 ⊆ M

/-- **特例化**：$M$ 是 DG 基的模型 $\iff$ $M$ 是 `DGBasisSelfRef` 的模型。

**证明**：`DGBasisSelfRef` 的成员恰为 $(P,P'')$（$P$ 伪内涵），
故「逐条满足 $T$」即「$P$ 伪内涵 $\wedge P\subseteq M\Rightarrow P''\subseteq M$」
——正是 `IsModel` 的定义。∎ -/
theorem isModel_iff_isModelOf_dgbasis (M : Set K.MFCA) :
    K.IsModel M ↔ K.IsModelOf K.DGBasisSelfRef M := by
  constructor
  · intro h r hr hsub
    obtain ⟨P, hP, rfl⟩ := hr
    exact h P hP hsub
  · intro h P hP hsub
    exact h (P, K.closureOp P) ⟨P, hP, rfl⟩ hsub

/-- **非冗余**（教材 Definition 3.38 的转写）。

$T$ **非冗余** $\iff$ 删去任一条后**不再完备**
（即存在一个集合，它满足其余蕴含但不满足被删的那条）。

**与教材定义的关系**：教材原文为「$T$ 去掉某条后不再推出该条」。
本实现采用**等价形式**：由教材 **Thm 3.40**，
「完备 $\iff$ $\mathrm{Mod}(T)=\mathrm{Int}$」，
故「删一条后不完备 $\iff$ 模型类变大」——
**二者在同一语言内等价**，不需要另建语法推出关系。 -/
def IsNonRedundant (Sig : Set (Set K.MFCA × Set K.MFCA)) : Prop :=
  ∀ r ∈ Sig, ∃ M : Set K.MFCA,
    K.IsModelOf (Sig \ {r}) M ∧ ¬ K.IsModelOf ({r} : Set (Set K.MFCA × Set K.MFCA)) M

/-- **DG 基的自指版本非冗余**（规格 T1A.10「最小」一半的核心，教材 Thm 3.46 的 Non-redundant 部分）。

$$\mathrm{IsNonRedundant}\,\mathrm{DGBasisSelfRef}$$

即：**删去 DG 基中的任意一条 $P\Rightarrow P''$ 后，
剩下的蕴含不再能推出它**。

**这是任务「DG 基自指版中，任一条不能由其余推出」的精确形式化。**

**前件 `FiniteAttrs`**：非冗余的论证需要「$Q\subsetneq P\Rightarrow
Q.\mathrm{ncard}<P.\mathrm{ncard}$」，该不等式依赖有限性。

---
**证明结构（严格遵循教材的 witness 构造）**

对 $r=P\Rightarrow P''\in\mathrm{DGBasisSelfRef}$，取**见证** $M:=P$：

1. **$\neg\,\mathrm{IsModelOf}\,\{r\}\,P$**：
   $r$ 的前件 $P\subseteq P$ 成立，但结论 $P''\subseteq P$ 不成立
   ——因为 $P$ 是伪内涵，$P\subsetneq P''$（`isPseudoIntent_subset_closureOp`）。
   故 $P$ **不满足** $r$。

2. **$\mathrm{IsModelOf}\,(\mathrm{DGBasisSelfRef}\setminus\{r\})\,P$**：
   对任一条其余规则 $Q\Rightarrow Q''$（$Q$ 伪内涵，$Q\Rightarrow Q''\neq r$），
   若其前件可用（$Q\subseteq P$），则因 $Q\Rightarrow Q''\neq r$ 且 $Q\subseteq P$
   必有 $Q\subsetneq P$，由 `pseudoIntent_closure_subset_of_ssubset_finite`
   得 $Q''\subseteq P$——即结论成立。

两者合起来即表明删去 $r$ 后 $P$ 成为新模型，**删 $r$ 破坏完备性**，
故 $r$ 不可由其余推出。∎

**⚠ 定义修正记录（必须阅读，这也是本定理成立的关键）**：
本定理在 `IsPseudoIntent` 的**初稿（扁平形）定义下【为假】**——
$\lvert M\rvert=4$ 即有 **175/1958** 条规则冗余，$\lvert M\rvert=5$ 有 **717/3371**。
最小反例：所有对象只满足属性 $0$ 时，$\{0,1\}\Rightarrow\{0,1,2,3\}$ 可由
$\{0,1,2\}\Rightarrow\{0,1,2,3\}$ 推出。
**故本实现先修正 `IsPseudoIntent`（见其 doc-comment 与 `pseudoIntent_closure_subset_of_ssubset`），
再证本定理。** -/
theorem dgbasisSelfRef_nonredundant [K.FiniteAttrs] :
    K.IsNonRedundant K.DGBasisSelfRef := by
  rintro r hr
  obtain ⟨P, hP, rfl⟩ := hr
  refine ⟨P, ?_, ?_⟩
  · -- 其余规则在 M = P 下都成立
    rintro r' hr' hX
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hr'
    obtain ⟨⟨Q, hQ, heq⟩, hne⟩ := hr'
    -- heq : r' = (Q, Q'')；由 hX : r'.1 ⊆ P 得 Q ⊆ P
    have hQP : r'.1 = Q := congrArg Prod.fst heq
    have hY : r'.2 = K.closureOp Q := congrArg Prod.snd heq
    have hQPs : Q ⊆ P := by rw [hQP] at hX; exact hX
    rw [hY]
    rcases eq_or_ne Q P with hQPeq | hQPne
    · -- Q = P 时 r' = (P,P'') = r，与 hr' 中 r' ≠ r 矛盾
      exfalso
      subst hQPeq
      exact hne heq
    · -- Q ⊊ P，用核心引理
      exact K.pseudoIntent_closure_subset_of_ssubset_finite hP hQ
        (Set.ssubset_iff_subset_ne.mpr ⟨hQPs, hQPne⟩)
  · -- (P, P'') 在 M = P 下不成立
    intro h
    have hsub : K.closureOp P ⊆ P := h (K.dgRule P) (by simp [FormalCtx.dgRule]) subset_rfl
    exact K.not_isClosedAttr_of_isPseudoIntent hP
      (Set.Subset.antisymm hsub (K.subset_closureOp P))


/-! ### §5.1 ⚠ **非冗余性的形式化（已证）与其间的一次定义修正**（）

**教材对非冗余性的证明**（逐字，L2345）：

> **Non-redundant**: Take any $P\Rightarrow P^{\downarrow\uparrow}$.
> We show that $T-\{P\Rightarrow P^{\downarrow\uparrow}\}\not\models
> P\Rightarrow P^{\downarrow\uparrow}$. Since $\|P\Rightarrow P^{\downarrow\uparrow}\|_P=0$
> (obvious, check), it suffices to show that
> $\|T-\{P\Rightarrow P^{\downarrow\uparrow}\}\|_P=1$.
> That is, we need to show that for each $Q\Rightarrow Q^{\downarrow\uparrow}\in
> T-\{P\Rightarrow P^{\downarrow\uparrow}\}$ we have
> $\|Q\Rightarrow Q^{\downarrow\uparrow}\|_P=1$, i.e. that
> **if $Q\subseteq P$ then $Q^{\downarrow\uparrow}\subseteq P$.
> But this follows from the definition of a pseudo-intent (apply to $P$).**

**本实现已完成该证明**——即 §5 上方的
`dgbasisSelfRef_nonredundant : IsNonRedundant DGBasisSelfRef`。
其关键在于把教材所说的「apply to $P$」形式化为
`pseudoIntent_closure_subset_of_ssubset`：

> $P,Q$ 都是伪内涵，$Q\subsetneq P$ $\Longrightarrow$ $Q''\subseteq P$。

在**修正后**的自指定义下，这是定义的第二个分量**直接给出**的
（递归假设就是「$Q$ 是伪内涵」，与 $P$ 条件 2 所需的假设**逐字一致**）。

---------------------------------------------------------------------------
⚠ **一次定义缺陷的实证发现（必须记录，防止重蹈）**
---------------------------------------------------------------------------
**为什么需要修正定义**：本实现最初的 `IsPseudoIntent` 把递归假设写成了
「扁平形」$H(Q)$（$Q$ 不闭，且 $Q$ 的**所有**不闭真子集闭包含于 $Q$），
而非「$Q$ 是伪内涵」。

**本次任务在证 `dgbasisSelfRef_nonredundant` 时，穷尽枚举检出了**
**该初稿定义使定理【为假】**（不止是「难证」）：

| 规模 | 检验的背景数 | 初稿定义的 DG 基非冗余反例 | 修正定义的 DG 基非冗余反例 |
|---|---|---|---|
| $\lvert M\rvert=3$ | 全 512 | 0 | **0** |
| $\lvert M\rvert=4$ | 采样 600 | **175/1958** ❌ | **0** ✅ |
| $\lvert M\rvert=5$ | 采样 600 | **717/3371** ❌ | **0** ✅ |

**最小反例**（$I=\{g\mapsto\{0\}\}$，全 4 个对象只满足属性 $0$）：
初稿定义下 $\{0,1\}$ 与 $\{0,1,2\}$ 均为「伪内涵」，
但 $\{0,1\}''=\{0,1,2,3\}\not\subseteq\{0,1,2\}$，
故 $\{0,1,2\}\Rightarrow\{0,1,2,3\}$ **可由 $\{0,1\}\Rightarrow\{0,1,2,3\}$ 推出**——
违反非冗余。

**先前记录的「配对形不蕴含扁平形（114/952）」是同一定义缺陷的另一面**：
初稿把「$Q$ 是伪内涵」错误地加强为扁平形，
使定义**多收**了本不该是伪内涵的集合。
**本次修正把递归假设改回「$Q$ 是伪内涵」本身，
两个症状同时消除**（既恢复了完备性所需的枚举一致性，
也使非冗余性成立并可证）。

**验证脚本**：`prototype/fca-alpha/dgbasis_minimality_check.py`
（原脚本）与本次的三方枚举核查
（`PI_enum` / `PI_lean-初稿` / `PI_rec-修正`，$\lvert M\rvert\le5$）。

**⚠ 与完备性的关系（重要，防止误读）**：
本文件的**完备性**（§4）在**初稿定义下也成立**
（`closed_of_model` 的证明只用 `IsModel` 与伪内涵定义条件 1
及条件 2 的存在性，与递归假设的形状无关）。
本次修正**不改变**完备性结论，只使**非冗余性**从「假」变「真」。
**故不存在「修正定义后完备性作废」的问题——但确实重新构建了
`Implication.lean` 与 `Completeness.lean`（均零 `sorry` / 零 `axiom`）。** -/

/-! ===========================================================================
   §5  抽象–解构循环（作者裁决 O 的形式化）

   **来源**：作者裁决 O —— 循环的内容是「抽象与解构」，
   分类 ↔ 因果互修，不结束，信息不足则临时停止。

   **哲学依据**：时态性层级体系（`操作闭合主义/原始文件/`）的两种目光 ——
   **向上目光**追问「它归于何类」（抽象），
   **向下目光**追问「它由何构成」（解构）。

   **⚠ 映射声明**：本节的「抽象 ↔ `polarUp`」「解构 ↔ `polarDown`」
   是**分析者的解读**，非原文明述。其正确性由本节**定理的可证性**验证，
   **不由原文权威保证**。

   **本节不引入任何常数**（依作者裁决 Q-1「禁止一切硬编码」）：
   收敛上界由 `Nat.card K.MFCA` 推出，非硬编码。
   =========================================================================== -/



/-! ### §5.1 「抽象」与「解构」= FCA 的两个导出算子 -/

/-- **向上抽象**：对象集 ↦ 它们共享的属性集（上位归类）。

对应时态性体系的「向上目光」：追问「它归于何类」。 -/
def abstractStep (O' : Set K.GFCA) : Set K.MFCA := K.polarUp O'

/-- **向下解构**：属性集 ↦ 满足它的对象集（内部构成）。

对应时态性体系的「向下目光」：追问「它由何构成」。 -/
def deconstructStep (B : Set K.MFCA) : Set K.GFCA := K.polarDown B

/-- **一轮循环 = 先解构、后抽象**（向下目光 → 向上目光）。

即 `B ↦ (B')'`，正是 FCA 的**闭包算子**。

**⚠ 这是本节的核心观察**：时态性体系的「一轮抽象–解构」，
在 FCA 中**恰好就是闭包算子** —— 故本库已有其全部构件。 -/
def oneRound (B : Set K.MFCA) : Set K.MFCA := K.polarUp (K.polarDown B)

/-- **等式：`oneRound` 即 `closureOp`**。

两者按定义都是 `B ↦ B''`（先解构后抽象），故为**定义等式**。

**证明是 `rfl`** —— 如实标注：`oneRound K B` 与 `K.closureOp B`
展开后同为 `K.polarUp (K.polarDown B)`，无需任何引理。 -/
theorem oneRound_eq_closureOp (B : Set K.MFCA) :
    oneRound K B = K.closureOp B :=
  rfl

/-! ### §5.2 单调性：信息只增不减 -/

/-- **循环单调**：一轮之后属性集只增不减。

**数学内容**：这就是闭包算子的**外延性**（`B ⊆ B''`）。
**它排除了「循环把已有信息丢掉」这一可能**。 -/
theorem loop_monotone (B : Set K.MFCA) : B ⊆ oneRound K B :=
  K.subset_closureOp B

/-! ### §5.3 不动点 ⟺ 概念（「临时停止」的判据） -/

/-- **循环的不动点恰好是概念（闭属性集）**。

**这给出了「何时可停」的判据**：循环稳定 ⟺ 已到达概念。

**⚠ 本证明是 `Iff.rfl`（定义展开）** —— 如实标注，不夸大难度。
**其价值在于「陈述」**：它把「抽象–解构循环的稳定点」与
「形式概念」**等同起来**，从而使裁决 O 的循环有了精确落点。 -/
theorem loop_fixpoint_iff_concept (B : Set K.MFCA) :
    oneRound K B = B ↔ K.IsClosedAttr B :=
  Iff.rfl

/-! ### §5.4 循环收敛定理 -/

/-- 迭代单调：第 `n` 轮 ⊆ 第 `n+1` 轮。 -/
theorem oneRound_iterate_mono (B : Set K.MFCA) :
    ∀ n : ℕ, (oneRound K)^[n] B ⊆ (oneRound K)^[n + 1] B := by
  intro n
  induction n with
  | zero => exact loop_monotone K B
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact K.closureOp_mono ih

/-- **循环收敛定理**：有限属性集上，`oneRound` 迭代必在**有限步**稳定。

**这是本节唯一的实质定理。**

**证明思路**：反证。若永不稳定，则第 `k` 轮严格包含第 `k+1` 轮之和的真扩，
故 `ncard` 严格递增；但 `ncard ≤ |M|`，矛盾（鸽巢论证）。

**⚠ 无硬编码**（依作者裁决 Q-1）：上界 `Nat.card K.MFCA` 由
`[K.FiniteAttrs]` **推出**，不是选定的常数。

**与裁决 O 的关系**：作者说循环「不结束，信息不足则临时停」。
本定理给出「**信息充足时必停**」这一半 —— 即有限属性集上收敛有保证。
「信息不足」那一半须由误差判据（裁决 K）给出，不在本节范围。 -/
theorem loop_stabilizes [K.FiniteAttrs] (B : Set K.MFCA) :
    ∃ N : ℕ, (oneRound K)^[N] B = (oneRound K)^[N + 1] B := by
  by_contra hnot
  push Not at hnot
  have hne : ∀ k : ℕ, (oneRound K)^[k] B ≠ (oneRound K)^[k + 1] B := hnot
  have hss : ∀ k : ℕ, (oneRound K)^[k] B ⊂ (oneRound K)^[k + 1] B :=
    fun k => (Set.ssubset_iff_subset_ne).2 ⟨oneRound_iterate_mono K B k, hne k⟩
  have hcard : ∀ k : ℕ, ((oneRound K)^[k] B).ncard < ((oneRound K)^[k + 1] B).ncard :=
    fun k => Set.ncard_lt_ncard (hss k) (FiniteAttrs.finite_set (K := K) _)
  have hbound : ∀ k : ℕ, k ≤ ((oneRound K)^[k] B).ncard := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hcard k))
  have hle_univ : ∀ k : ℕ, ((oneRound K)^[k] B).ncard ≤ (Set.univ : Set K.MFCA).ncard :=
    fun k => Set.ncard_le_ncard (Set.subset_univ _) (FiniteAttrs.finite (K := K))
  have hfin : (Set.univ : Set K.MFCA).ncard = Nat.card K.MFCA := Set.ncard_univ _
  have hbig := hbound (Nat.card K.MFCA + 1)
  have hsmall := hle_univ (Nat.card K.MFCA + 1)
  rw [hfin] at hsmall
  omega

/-! ### §5.4.1 精确界：稳定所需步数 ≤ `|M|`

上一节的 `loop_stabilizes` **只断言存在** `N`，其证明是鸽巢论证，
故其「上界」是 `Nat.card K.MFCA`（置 `k = |M| + 1` 反证）。
本小节给出**精确界**：显式取 `N = |M|` 时等式成立。

**关键观察（使界远小于 `|M|`）**：`oneRound` **不是**任意单调算子，
而是 FCA 的**闭包算子** `B ↦ B''`，它**幂等**（`closureOp_idem`）。
幂等性使迭代**从第 1 步起恒定**，故真正的**最优界是 `1`**（空属性集时 `0`）。

因此「步数 ≤ `|M|`」不仅成立，而且**远非紧**：
鸽巢论证给出的 `|M|` 是一个**有效但非最优**的界。
本节同时给出两个定理：

- `loop_stabilizes_within_card`：`|M|` 步内稳定（任务所求的**精确界**陈述）；
- `loop_stabilizes_within_one`：**1** 步内稳定（真正的**最优界**）。 -/

/-- **`oneRound` 的幂等性**：`oneRound (oneRound B) = oneRound B`。

这是「`oneRound` = 闭包算子」的直接后果（`closureOp_idem`），
也是精确界远小于 `|M|` 的**根本原因**。 -/
theorem oneRound_idem (B : Set K.MFCA) :
    oneRound K (oneRound K B) = oneRound K B :=
  K.closureOp_idem B

/-- **迭代从第 1 步起恒定**：`oneRound^[n+1] B = oneRound B`。

由幂等性归纳而得。 -/
theorem oneRound_iterate_succ (B : Set K.MFCA) :
    ∀ n : ℕ, (oneRound K)^[n + 1] B = oneRound K B := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega,
          Function.iterate_succ_apply']
      rw [ih]
      exact oneRound_idem K B

/-- **精确界（`|M|`）**：`N = |M|` 时迭代已稳定，即
`oneRound^[|M|] B = oneRound^[|M|+1] B`。

这比 `loop_stabilizes` 的「存在 `N`」**强**：它给出具体的 `N = |M|`。

**证明**：`oneRound` 幂等，故迭代从第 1 步起恒定。
当 `|M| ≥ 1`，两边都等于 `oneRound B`；
当 `|M| = 0`，`M_{\mathrm{FCA}}` 为空（`Finite` + `Nat.card = 0`），
任何属性集都是 `∅` 且 `oneRound ∅ = ∅`，故取 `N = 0` 即稳定。

**⚠ 关于最优性**：本界**不是最优的**——真正的界是 `1`
（见 `loop_stabilizes_within_one`）。保留 `|M|` 形式是为**回应任务**
「步数 ≤ `|M|`」的陈述；其数学内容由幂等性承载，而非鸽巢。 -/
theorem loop_stabilizes_within_card [K.FiniteAttrs] (B : Set K.MFCA) :
    (oneRound K)^[Nat.card K.MFCA] B =
      (oneRound K)^[Nat.card K.MFCA + 1] B := by
  have hfin : Finite K.MFCA := Finite.of_finite_univ (FiniteAttrs.finite (K := K))
  rcases Nat.eq_zero_or_pos (Nat.card K.MFCA) with h | h
  · -- |M| = 0：MFCA 为空，任何属性集都是 ∅，而 oneRound ∅ = ∅
    have hempty : IsEmpty K.MFCA := by
      rcases Nat.card_eq_zero.mp h with h0 | hinf
      · exact h0
      · exact absurd hinf hfin.not_infinite
    have hB : B = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x _ => hempty.elim x
    subst hB
    rw [h]
    show (oneRound K)^[0] (∅ : Set K.MFCA) = (oneRound K)^[0 + 1] ∅
    rw [oneRound_iterate_succ K (∅ : Set K.MFCA) 0]
    exact (Set.eq_empty_iff_forall_notMem.mpr fun x _ => hempty.elim x).symm
  · have hstep : ∀ n : ℕ, (oneRound K)^[n + 1] B = (oneRound K)^[n + 1 + 1] B :=
      fun n => by rw [oneRound_iterate_succ K B n, oneRound_iterate_succ K B (n + 1)]
    have e1 : Nat.card K.MFCA = (Nat.card K.MFCA - 1) + 1 := by omega
    rw [e1]
    exact hstep (Nat.card K.MFCA - 1)

/-- **最优界（`1`）**：`oneRound` 迭代**一步**即稳定：
`oneRound (oneRound B) = oneRound B`。

这是 `loop_stabilizes_within_card` 的加强，也是**真正的精确界**：
`oneRound` 是**幂等闭包算子**，故从第 1 步起恒定，
不可能需要更多步。空属性集时甚至 `0` 步即稳定（见上文分支）。

**与鸽巢界的关系**：`|M|` 是**有效但非紧**的界；
`loop_stabilizes` 的鸽巢论证之所以只能给出 `|M|`，
是因为它只用了「单调 + 有限」，**未用幂等性**。 -/
theorem loop_stabilizes_within_one (B : Set K.MFCA) :
    (oneRound K)^[1] B = (oneRound K)^[2] B := by
  rw [Function.iterate_one, Function.iterate_succ_apply', Function.iterate_one]
  exact (oneRound_idem K B).symm

/-! ### §5.5 抽象与解构的伴随性 -/

/-- **抽象与解构构成伴随对**（Galois 连接）。

`O' ⊆ deconstruct(B) ↔ B ⊆ abstract(O')` ——
即**「解构的右伴随是抽象」**。

**这给出了两种目光的精确代数关系**：
它们不是两个独立操作，而是**一对伴随**。
时态性体系说「投向即构成」，伴随性正是这一说法的代数化。 -/
theorem abstract_deconstruct_adjoint (O' : Set K.GFCA) (B : Set K.MFCA) :
    O' ⊆ deconstructStep K B ↔ B ⊆ abstractStep K O' :=
  (K.subset_polarUp_iff_subset_polarDown (A := O') (B := B)).symm

end FormalCtx

end

end FateV2.Rules
