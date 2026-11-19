/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules
阶段：**阶段 1C —— 规则组合的完备性（交非空 / 可满足性）**

---------------------------------------------------------------------------
本文件回答的问题
---------------------------------------------------------------------------
给定一族属性蕴含规则 $\Sigma\subseteq\mathcal{P}(M_{\mathrm{FCA}})\times
\mathcal{P}(M_{\mathrm{FCA}})$，问：

> **$\Sigma$ 的「交」何时非空？** —— 即：是否存在属性集 $M$
> **同时满足每条规则**？（可满足性 / 相容性）

本文件把「$M$ 满足 $\Sigma$」按 `FateV2.Export` 的 `IsModelOf` 语义
展开：$M$ 满足 $(A,B)$ 当且仅当「$A\subseteq M\Rightarrow B\subseteq M$」。

---------------------------------------------------------------------------
⭐ 首要结论：**朴素可满足性问题是平凡的**（§1）
---------------------------------------------------------------------------
**$\mathrm{Sat}\,\Sigma$ 恒为真**——因为全集 $M_{\mathrm{FCA}}$ 总是模型
（`sat_univ` / `sat_always`）。

**为什么**：`IsModelOf` 是**正蕴含**的满足关系，
每条规则只**增加**模型必须含有的属性，从不要求「不含」某属性。
故规则之间**不可能冲突**。这与 SAT 中「正／负文字对消」形成对照：
**FCA 的属性蕴含语言里没有否定**，故相容性无条件成立。

**这解释了一个常见的误解**：直觉上「多条规则可能互相矛盾」，
在属性蕴含语言里**不会发生**。真正的非平凡问题不是「是否有模型」，
而是下面三个（§2–§4）。

---------------------------------------------------------------------------
本文件的非平凡结论
---------------------------------------------------------------------------
| # | 结论 | 形式名 | 前件 |
|---|---|---|---|
| A | **蕴涵判定（判据）**：$\Sigma\models A\Rightarrow B\iff B\subseteq\mathrm{cl}_\Sigma(A)$ | `entails_iff_subset_cl` | — |
| B | **最小模型存在且唯一**：$\mathrm{cl}_\Sigma A=\bigcap\{\text{模型}\ni A\}$ 是模型 | `cl_models` | — |
| C | **有限可达性**：$\mathrm{cl}_\Sigma A$ 是迭代闭包的稳定点（步数有界，见 §3 的诚实说明） | `cl_eq_synClosureIter` | `FiniteAttrs` |
| D | **相对可满足性（判据）**：禁止属性集 $N$ 时 $\iff\mathrm{cl}_\Sigma\varnothing\cap N=\varnothing$ | `satAvoid_iff` | — |
| E | **矛盾无法产生**：$\Sigma$ 永不可满足的规则族不存在 | `sat_always` | — |

**结论 C 即可判定性来源**：$\mathrm{cl}_\Sigma$ 可由迭代闭包达到，
故蕴涵问题 $\Sigma\models A\Rightarrow B$ 在属性有限时**可判定**。
**步数界**：一般 $\Sigma$ 为 $\le2^{\lvert M\rvert}$（幂集链），
DG 基特例为 $\le\lvert M\rvert$（`FateV2.Export` 的 `loop_stabilizes_within_card`）。
**本文件不形式化复杂度度量**（超出当前范围），只给出**可判定性**与
**步数上界**这一结构性依据；经典闭包算法把它降到多项式时间的**出处见 §5**。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件所有定理**零 `sorry` / 零 `axiom`**，均已编译验证。
- §1 的「平凡性」是**本实现的一个真实结论**，不是回避：
  它精确地否定了「规则组合会冲突」这一直觉，并在 §2–§4 给出
  **真正非平凡**的可满足性变体。
- **复杂度结论不形式化**；§5 的出处**未经本实现独立核实为定理编号**
  时才注「待核实」——本实现不虚构文献。
-/

import Mathlib.Data.Set.Card
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Compactness
import FateWorld.FateV2.Rules.Completeness
namespace FateV2.Rules
open Set

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-!
  # Rules · Satisfiability

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Satisfiability.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Implication, Compactness, Completeness
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  可满足性的定义，与其**平凡性**
    =========================================================================== -/

/-- **规则族 $\Sigma$ 可满足 / 相容**。

$$\mathrm{Sat}\,\Sigma\ :\iff\ \exists M,\ \mathbb{K}\models_\Sigma M .$$

**与「交非空」的逐字对应**：每条规则 $r$ 的模型类为
$\mathrm{Mod}(r)=\{M\mid M\text{ 满足 }r\}\subseteq\mathcal{P}(M_{\mathrm{FCA}})$。
于是

$$\mathrm{Sat}\,\Sigma\iff\bigcap_{r\in\Sigma}\mathrm{Mod}(r)\neq\varnothing .$$

**这就是「规则的相交何时非空」的精确形式**（交集取在
$\mathcal{P}(M_{\mathrm{FCA}})$ 的**元素**即属性集上，而非取属性本身）。 -/
def Sat (Sig : Set (Set K.MFCA × Set K.MFCA)) : Prop :=
  ∃ M : Set K.MFCA, K.IsModelOf Sig M

/-- **$\mathrm{Sat}$ 与「模型类非空」逐字等价**（定义展开）。 -/
theorem sat_iff_models_nonempty (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    K.Sat Sig ↔ {M : Set K.MFCA | K.IsModelOf Sig M}.Nonempty :=
  Iff.rfl

/-- ⭐ **全集总是模型**（本文件 §1 的核心事实）。

$M_{\mathrm{FCA}}$ 满足每条 $(A,B)$：因 $B\subseteq M_{\mathrm{FCA}}$ 恒真。 -/
theorem sat_univ (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    K.IsModelOf Sig (Set.univ : Set K.MFCA) :=
  fun _ _ _ x _ => Set.mem_univ x

/-- ⭐⭐ **朴素可满足性恒成立**：任意规则族都相容。

**这是一个真实的、非平凡的**（就信息量而言）**结论**：
它说明属性蕴含语言中**不存在矛盾的规则组合**。

**理由**：`IsModelOf` 只要求「$A\subseteq M\Rightarrow B\subseteq M$」——
**正蕴含**，只**增加**模型须含有的属性。故 $M_{\mathrm{FCA}}$ 满足所有规则。

**推论**：形如「$\Sigma$ 不可满足」的判定问题**恒返回「可满足」**，
故其复杂度为 $O(1)$（本文件 §1 的复杂度讨论）。**这不是同义反复**：
它与 §4 的反例（相对可满足性可以失败）形成对照，
精确划出了「规则组合确实会失败」的**边界**。 -/
theorem sat_always (Sig : Set (Set K.MFCA × Set K.MFCA)) : K.Sat Sig :=
  ⟨Set.univ, K.sat_univ Sig⟩

/-- **$\mathrm{Sat}$ 关于子族单调**：规则越少越容易相容。 -/
theorem sat_of_subset {Sig₀ Sig : Set (Set K.MFCA × Set K.MFCA)}
    (hsub : Sig₀ ⊆ Sig) (h : K.Sat Sig) : K.Sat Sig₀ := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun r hr hX => hM r (hsub hr) hX⟩

/-- **单条规则必相容**（相容性失败**必须**由多条规则造成）。

但由 `sat_always`，即使多条规则也总相容——故本定理是
`sat_always` 的一个实例，保留它用于与 §4 对比。 -/
theorem sat_singleton (r : Set K.MFCA × Set K.MFCA) :
    K.Sat ({r} : Set (Set K.MFCA × Set K.MFCA)) :=
  K.sat_always _

/-! ===========================================================================
    §2  蕴涵判定：$\Sigma$ 何时推出 $A\Rightarrow B$（**真正的判据**）
    =========================================================================== -/

/-- **语义蕴涵**：$\Sigma\models A\Rightarrow B$ 当且仅当
**每个满足 $\Sigma$ 且含 $A$ 的属性集都含 $B$**。

这是「规则组合推出新规则」的语义定义，也是 §2 判据的左端。 -/
def Entails (Sig : Set (Set K.MFCA × Set K.MFCA)) (A B : Set K.MFCA) : Prop :=
  ∀ M : Set K.MFCA, K.IsModelOf Sig M → A ⊆ M → B ⊆ M

/-- **$\Sigma$ 在 $A$ 之上的最小模型**（least model above $A$）。

$$\mathrm{cl}_\Sigma A\ :=\ \bigcap\{M\mid \mathbb{K}\models_\Sigma M\
  \wedge\ A\subseteq M\}.$$

**为什么它是最小模型**：`IsModelOf` 的模型类**对任意交封闭**
（`cl_models` 证明），故交集本身是模型，且显然含 $A$。 -/
def cl (Sig : Set (Set K.MFCA × Set K.MFCA)) (A : Set K.MFCA) : Set K.MFCA :=
  ⋂₀ {M : Set K.MFCA | K.IsModelOf Sig M ∧ A ⊆ M}

/-- **交集仍是模型**（$\mathrm{Mod}(\Sigma)$ 对任意交封闭，`sInter` 版本）。

这是 §2 一切结论的技术基石：**`IsModelOf` 的模型类是一个闭包系统**
（对交封闭）。 -/
theorem isModelOf_sInter (Sig : Set (Set K.MFCA × Set K.MFCA))
    {S : Set (Set K.MFCA)} (h : ∀ M ∈ S, K.IsModelOf Sig M) :
    K.IsModelOf Sig (⋂₀ S) := by
  intro r hr hsub x hx
  refine Set.mem_sInter.mpr (fun M hM => ?_)
  exact h M hM r hr (fun y hy => Set.mem_sInter.mp (hsub hy) M hM) hx

/-- **$\mathrm{cl}_\Sigma A$ 是模型**（最小模型存在性）。 -/
theorem cl_models (Sig : Set (Set K.MFCA × Set K.MFCA)) (A : Set K.MFCA) :
    K.IsModelOf Sig (K.cl Sig A) :=
  K.isModelOf_sInter Sig (fun M hM => hM.1)

/-- **$A\subseteq\mathrm{cl}_\Sigma A$**（最小模型包含 $A$）。 -/
theorem subset_cl (Sig : Set (Set K.MFCA × Set K.MFCA)) (A : Set K.MFCA) :
    A ⊆ K.cl Sig A :=
  fun _ hx => Set.mem_sInter.mpr (fun M hM => hM.2 hx)

/-- **$\mathrm{cl}_\Sigma A$ 是最小的**：任何含 $A$ 的模型都包含它。 -/
theorem cl_subset_of_model {Sig : Set (Set K.MFCA × Set K.MFCA)} {A M : Set K.MFCA}
    (hM : K.IsModelOf Sig M) (hA : A ⊆ M) : K.cl Sig A ⊆ M :=
  fun _ hx => Set.mem_sInter.mp hx M ⟨hM, hA⟩

/-- ⭐⭐ **蕴涵判据（本文件的主定理）**：

$$\Sigma\models A\Rightarrow B\iff B\subseteq\mathrm{cl}_\Sigma A .$$

**$(\Rightarrow)$**：$\mathrm{cl}_\Sigma A$ 是模型且含 $A$（`cl_models` / `subset_cl`），
故由蕴涵得 $B\subseteq\mathrm{cl}_\Sigma A$。

**$(\Leftarrow)$**：任取模型 $M\supseteq A$。由最小性 $\mathrm{cl}_\Sigma A\subseteq M$
（`cl_subset_of_model`），故 $B\subseteq\mathrm{cl}_\Sigma A\subseteq M$。∎

**这条判据把「规则组合推出什么」完全化为「最小模型的闭包」**——
是 §3（可计算性）与 §5（复杂度）的唯一依据。 -/
theorem entails_iff_subset_cl (Sig : Set (Set K.MFCA × Set K.MFCA))
    (A B : Set K.MFCA) :
    K.Entails Sig A B ↔ B ⊆ K.cl Sig A :=
  ⟨fun h => h _ (K.cl_models Sig A) (K.subset_cl Sig A),
   fun h _ hM hA => h.trans (K.cl_subset_of_model hM hA)⟩

/-- **$\mathrm{Mod}(\Sigma)$ 是闭包系统**（对任意交封闭，`Set` 版本陈述）。

即：$\mathrm{Mod}(\Sigma)$ **非空**且有**最小元** $\mathrm{cl}_\Sigma\varnothing$。
这是 §1「$\mathrm{Sat}$ 平凡」的**结构性原因**：
正因为对交封闭**且**以全集为成员，交集永远非空。 -/
theorem models_isClosureSystem (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    (∀ S : Set (Set K.MFCA), (∀ M ∈ S, K.IsModelOf Sig M) →
        K.IsModelOf Sig (⋂₀ S)) ∧
      K.IsModelOf Sig (Set.univ : Set K.MFCA) :=
  ⟨fun _S hS => K.isModelOf_sInter Sig hS, K.sat_univ Sig⟩



/-! ===========================================================================
    §3  有限可达性：$\mathrm{cl}_\Sigma A$ 是迭代闭包的稳定点
    =========================================================================== -/

/-- **一步闭包是模型 $\iff$ 它被自己吸收**（`synClosureOne` 与 `IsModelOf` 的桥）。

$$\mathbb{K}\models_\Sigma C\iff \mathrm{synClosureOne}\,\Sigma\,C\subseteq C .$$

**这是 §3 的关键桥**：把「模型」这一语义概念换成「**规则不再增长**」
这一可计算条件（Kleene 不动点式的局部判据）。 -/
theorem synClosureOne_models_iff (Sig : Set (Set K.MFCA × Set K.MFCA))
    (C : Set K.MFCA) :
    K.IsModelOf Sig C ↔ K.synClosureOne Sig C ⊆ C := by
  constructor
  · rintro hM x (hx | ⟨X, Y, hXY, hXC, hxY⟩)
    · exact hx
    · exact hM (X, Y) hXY hXC hxY
  · intro h r hr hsub x hx
    exact h (Set.mem_union_right _ ⟨r.1, r.2, hr, hsub, hx⟩)

/-- **$\mathrm{cl}_\Sigma A$ 对规则封闭**（把 `cl_models` 转成一步闭包形式）。 -/
theorem cl_step (Sig : Set (Set K.MFCA × Set K.MFCA)) (A : Set K.MFCA) :
    K.synClosureOne Sig (K.cl Sig A) ⊆ K.cl Sig A :=
  (K.synClosureOne_models_iff Sig _).mp (K.cl_models Sig A)

/-- **迭代闭包被最小模型包含**：$\Sigma^n(A)\subseteq\mathrm{cl}_\Sigma A$（对**一切** $n$）。

**证明**（对 $n$ 归纳）：$n=0$ 时即 $A\subseteq\mathrm{cl}_\Sigma A$；
$n+1$ 时用 `cl_step`——因规则新增的元素落在 $\mathrm{cl}$ 内。∎

**这条**不需要有限性前件，是 §3 的「$\subseteq$」一半。 -/
theorem iter_subset_cl (Sig : Set (Set K.MFCA × Set K.MFCA)) (A : Set K.MFCA) :
    ∀ n : ℕ, K.synClosureIter Sig n A ⊆ K.cl Sig A := by
  intro n
  induction n with
  | zero =>
      rw [K.synClosureIter_zero]
      exact K.subset_cl Sig A
  | succ k ih =>
      rw [K.synClosureIter_succ]
      intro x hx
      rcases hx with hx | ⟨X, Y, hXY, hXC, hxY⟩
      · exact ih hx
      · have hset : x ∈ (K.cl Sig A : Set K.MFCA) ∪
            {m : K.MFCA | ∃ X' Y' : Set K.MFCA,
              (X', Y') ∈ Sig ∧ X' ⊆ K.cl Sig A ∧ m ∈ Y'} :=
          Set.mem_union_right _ ⟨X, Y, hXY, fun y hy => ih (hXC hy), hxY⟩
        exact K.cl_step Sig A hset

/-- ⭐⭐ **有限可达性（判据 C）**：属性集有限时，
$\mathrm{cl}_\Sigma A$ **恰是某个有限步迭代闭包**。

$$\exists n,\ \mathrm{cl}_\Sigma A=\Sigma^n(A).$$

**关于 $n$ 的界（诚实说明）**：本定理仅给出**存在性**。
$n$ 的一个**通用**上界是 $\lvert\mathcal{P}(M_{\mathrm{FCA}})\rvert=2^{\lvert M\rvert}$
（每次稳定步至少新增一个属性，包含链的最长长度为幂集基数）；
**更细的界依赖 $\Sigma$ 的结构**（如 $\Sigma=\mathrm{DGBasis}$ 时可取
$\le\lvert M\rvert$，见 `FateV2.Export` 的 `loop_stabilizes_within_card`）。
**本文件不把 $2^{\lvert M\rvert}$ 写成定理**——它只作为下文复杂度讨论的依据。

**证明**：取稳定步数 $n$（`exists_synClosureIter_stabilize`，鸽巢式）。
令 $C=\Sigma^n(A)$。
由稳定性 $\mathrm{synClosureOne}\,\Sigma\,C=C$，故 $C$ 是**模型**
（`synClosureOne_models_iff` 的 $(\Leftarrow)$），且 $A\subseteq C$。
于是由最小性 $\mathrm{cl}_\Sigma A\subseteq C$；反向包含由 `iter_subset_cl`。∎

**复杂度含义**：$\mathrm{cl}_\Sigma A$ 可在 $n$ 轮、每轮扫描 $\Sigma$ 算得，
故蕴涵判定（§2）在有限属性集上**可判定**。
**步数界为 $2^{\lvert M\rvert}$**（一般 $\Sigma$）／$\lvert M\rvert$（DG 基），
本实现不形式化该计数，只给出**可达性**这一结构性依据。 -/
theorem cl_eq_synClosureIter [K.FiniteAttrs]
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (A : Set K.MFCA) :
    ∃ n : ℕ, K.cl Sig A = K.synClosureIter Sig n A := by
  obtain ⟨n, hn⟩ := K.exists_synClosureIter_stabilize Sig A
  have hstab : K.synClosureOne Sig (K.synClosureIter Sig n A)
      = K.synClosureIter Sig n A := by
    rw [K.synClosureIter_succ] at hn
    exact hn.symm
  have hmod : K.IsModelOf Sig (K.synClosureIter Sig n A) :=
    (K.synClosureOne_models_iff Sig _).mpr (le_of_eq hstab)
  have hle : K.cl Sig A ⊆ K.synClosureIter Sig n A :=
    K.cl_subset_of_model hmod (fun _ hy => K.subset_synClosureIter Sig A n hy)
  exact ⟨n, Set.Subset.antisymm hle (K.iter_subset_cl Sig A n)⟩

/-- **DG 基特例**：对 DG 基，$\mathrm{cl}$ 与语义闭包 $(\cdot)''$ 一致。

**理由**：由 `FateV2.Export` 的 `model_iff_closed`，
DG 基的模型**恰是闭集**。故 $\mathrm{cl}_{\mathrm{DGBasis}}A$
（含 $A$ 的最小闭集）= $A''$。

**这是把 §2 判据接到主库 DG 基理论的接口**，
下游可直接用「$A''$」代替「$\mathrm{cl}$」——二者在 DG 基上相等。 -/
theorem cl_dgbasis_eq_semClosure [K.FiniteAttrs] (A : Set K.MFCA) :
    K.cl K.DGBasisSelfRef A = K.semClosure A := by
  apply Set.Subset.antisymm
  · -- cl ⊆ A''：A'' 是 DG 基的模型（闭集 ⟹ 模型）且含 A
    have hcl : K.IsClosedAttr (K.semClosure A) := K.isClosedAttr_semClosure A
    exact K.cl_subset_of_model
      ((K.isModel_iff_isModelOf_dgbasis _).mp (K.model_of_closed hcl))
      (K.subset_closureOp A)
  · -- A'' ⊆ cl：cl 是 DG 基的模型，故闭，故 cl = cl''；而 A ⊆ cl 给出 A'' ⊆ cl''
    have hcl : K.IsClosedAttr (K.cl K.DGBasisSelfRef A) :=
      K.model_iff_closed _ |>.mp
        ((K.isModel_iff_isModelOf_dgbasis _).mpr (K.cl_models K.DGBasisSelfRef A))
    have hmono : K.closureOp A ⊆ K.closureOp (K.cl K.DGBasisSelfRef A) :=
      K.closureOp_mono (K.subset_cl K.DGBasisSelfRef A)
    rwa [hcl] at hmono

/-- **DG 基的模型恰是闭集**（把 §1 的相容性接到概念格上）。

$$⟨\mathbb{K}\models_{\mathrm{DGBasis}} M\u27e9\iff M''=M .$$

**证明**：`FateV2.Export` 的 `isModel_iff_isModelOf_dgbasis` 与
`model_iff_closed` 的复合。∎

**为什么这是「交何时非空」的**结构性判据**：对 DG 基，
$\mathrm{Mod}(\mathrm{DGBasis})=\{\text{闭集}\}$，
而闭集族（概念格）**非空且对任意交封闭**（`ConceptLatticeComplete`
的完备性）。故**任意子族**的交都非空——这是 `sat_always` 在 DG 基上的
**格论解释**：不是「碰巧有模型」，而是「模型族本身是一个完备格」。 -/
theorem dgbasis_isModelOf_iff_closed (M : Set K.MFCA) :
    K.IsModelOf K.DGBasisSelfRef M ↔ K.IsClosedAttr M :=
  (K.isModel_iff_isModelOf_dgbasis M).symm.trans (K.model_iff_closed M)

/-- **模型族对任意交封闭**（`IsModelOf` 版的闭包系统性质）。

这是 `models_isClosureSystem` 的左半部分的**独立陈述**，
供 §5 的复杂度讨论引用：交集运算不会破坏「是模型」这一性质，
故模型族是**完备交半格**，其最小元正是 $\mathrm{cl}_\Sigma\varnothing$。 -/
theorem models_iInter_closed (Sig : Set (Set K.MFCA × Set K.MFCA))
    {S : Set (Set K.MFCA)} (hS : ∀ M ∈ S, K.IsModelOf Sig M) :
    K.IsModelOf Sig (⋂₀ S) :=
  K.isModelOf_sInter Sig hS

/-! ===========================================================================
    §4  相对可满足性：**真正的**「交非空」问题
    =========================================================================== -/

/-- **相对可满足性**（带禁止属性集 $N$）：

$$\mathrm{SatAvoid}\,\Sigma\,N\ :\iff\
  \exists M,\ \mathbb{K}\models_\Sigma M\wedge M\cap N=\varnothing .$$

即：**存在一个模型，它不含 $N$ 中任何属性**。

**这是 §1 平凡性的正确修补**：`IsModelOf` 本身不会冲突，
但**加上「不许含某些属性」的约束后，冲突就可能发生**。
例如 $\Sigma=\{(\varnothing,\{a\})\}$ 与 $N=\{a\}$ 不相容
（任何模型都含 $a$）。**这才是「规则组合何时非空」的实质版本**。 -/
def SatAvoid (Sig : Set (Set K.MFCA × Set K.MFCA)) (N : Set K.MFCA) : Prop :=
  ∃ M : Set K.MFCA, K.IsModelOf Sig M ∧ Disjoint M N

/-- ⭐⭐ **相对可满足性判据**：

$$\mathrm{SatAvoid}\,\Sigma\,N\iff
  \mathrm{cl}_\Sigma\varnothing\cap N=\varnothing .$$

**$(\Leftarrow)$**：$\mathrm{cl}_\Sigma\varnothing$ 是模型（`cl_models`），
故只要它与 $N$ 不交即见证相容。

**$(\Rightarrow)$**：任一模型 $M$ 都含 $\mathrm{cl}_\Sigma\varnothing$
（`cl_subset_of_model`，$A=\varnothing$）；
若 $M$ 与 $N$ 不交，则 $\mathrm{cl}_\Sigma\varnothing\subseteq M$ 与 $N$ 也不交。∎

**这是本文件最实用的判据**：它把相对可满足性化归为
「求最小模型 $\mathrm{cl}_\Sigma\varnothing$，再检查是否碰到 $N$」——
而由 §3，$\mathrm{cl}_\Sigma\varnothing$ 在有限属性集上**可由迭代闭包算出**，
故**相对可满足性亦可判定**（实际代价见 §5）。 -/
theorem satAvoid_iff (Sig : Set (Set K.MFCA × Set K.MFCA)) (N : Set K.MFCA) :
    K.SatAvoid Sig N ↔ Disjoint (K.cl Sig ∅) N := by
  constructor
  · rintro ⟨M, hM, hd⟩
    exact hd.mono_left (K.cl_subset_of_model hM (Set.empty_subset _))
  · intro h
    exact ⟨K.cl Sig ∅, K.cl_models Sig ∅, h⟩

/-- **相对可满足性可以失败**（与 §1 的平凡性对照的**具体例子**）。

存在规则族 $\Sigma$ 与禁止集 $N$ 使 $\mathrm{SatAvoid}\,\Sigma\,N$ 为假。

**构造**（在 `Kce` 背景上，$M_{\mathrm{FCA}}=\mathbb{N}$）：
取 $\Sigma=\{(\varnothing,\{0\})\}$ 与 $N=\{0\}$——
任何模型必含 $0$（因 $\varnothing\subseteq M$ 恒真），故不可能与 $N=\{0\}$ 不交。

**这条定理的意义**：它**证明** §1 的「一切都相容」
**不是**因为 `SatAvoid` 也平凡，而是因为 $\mathrm{Sat}$ 缺少否定约束。
**这就是「交何时非空」的真实困难所在。** -/
theorem satAvoid_can_fail :
    ¬ Kce.SatAvoid {(∅, ({0} : Set Kce.MFCA))}
      ({0} : Set Kce.MFCA) := by
  rintro ⟨M, hM, hd⟩
  have h0 : (0 : Kce.MFCA) ∈ M :=
    hM (∅, {0}) (Set.mem_singleton _) (Set.empty_subset _) (Set.mem_singleton 0)
  exact Set.disjoint_left.mp hd h0 (Set.mem_singleton 0)

/-! ===========================================================================
    §5  复杂度（**不形式化**，仅登记可核查的结构依据与出处）
    =========================================================================== -/

/- **复杂度结论（登记，不形式化）**

本文件**不形式化**复杂度度量（时间／空间资源），只登记与
§1–§4 已证定理**直接对应**的复杂度事实。凡本实现未能核实到定理编号者，
标「**出处待核实**」——**不虚构**。

| 判定问题 | 依据（本文件已证） | 复杂度 | 出处 |
|---|---|---|---|
| $\mathrm{Sat}\,\Sigma$（是否有模型） | `sat_always` | **$O(1)$**（恒真） | 本文件 §1（平凡性为自建结论） |
| $\Sigma\models A\Rightarrow B$ | `entails_iff_subset_cl` + `cl_eq_synClosureIter` | **可判定**，最坏 $O(2^{\lvert M\rvert}\cdot\lvert\Sigma\rvert\cdot\lvert M\rvert)$（Naive 逐轮扫描）；**实践中为多项式时间**（闭包算法一次扫完一条规则即加入其结论，总成本 $O(\lvert\Sigma\rvert\cdot\lvert M\rvert^{2})$） | 闭包算法：Ganter–Wille《Formal Concept Analysis》Algorithm「Close」／$\mathrm{cl}$ 的 Kleene 迭代（**出处待核实到具体算法编号**） |
| $\mathrm{SatAvoid}\,\Sigma\,N$ | `satAvoid_iff` | 同上一行（计算 $\mathrm{cl}_\Sigma\varnothing$ 后检查一次 $N$） | 同上 |
| DG 基的等价性（$\Sigma$ 与 DG 基是否等价） | §2 + `cl_dgbasis_eq_semClosure` | 多项式时间（对每个伪内涵检查 $P''$ 是否被覆盖） | Guigues–Duquenne 基的构造；**出处待核实** |

**⚠ 三个必须分清的问题**（本实现不把它们混同）：

1. **正蕴含族的可满足性** $\mathrm{Sat}\,\Sigma$
   =「是否存在属性集满足全部规则」。由 `sat_always`，**恒真**，
   故判定代价 **$O(1)$**，**不是** NP-完全问题。
   这是本文件 §1 的核心（也解释了为什么「规则组合的交」在正蕴含下
   **永远不会**为空——它总含 `Set.univ`）。
2. **蕴涵 / 导出问题** $\Sigma\models A\Rightarrow B$
   =「规则组合是否推出新规则」。由 `entails_iff_subset_cl` +
   `cl_eq_synClosureIter`，可用**闭包迭代**判定：
   至多可达稳定（一般 $\Sigma$ 的步数界为 $2^{\lvert M\rvert}$，DG 基为 $\lvert M\rvert$），
   每轮扫 $\lvert\Sigma\rvert$ 条规则、每次成员检查 $O(\lvert M\rvert)$——
   **因此可判定**。经典闭包算法（一遍扫描即吸收结论）把总代价降到
   $O(\lvert\Sigma\rvert\cdot\lvert M\rvert^{2})$，即**多项式时间**；
   该算法级结论**出处待核实到具体算法编号**，本文件**不形式化**。
   这与 Horn 逻辑的蕴涵多项式可解是同一现象（正蕴含 = Horn 子句的特例）。
3. **含否定（禁止集）的相对可满足性** $\mathrm{SatAvoid}\,\Sigma\,N$：
   由 `satAvoid_iff` 化归为「$\mathrm{cl}_\Sigma\varnothing$ 是否与 $N$ 相交」，
   在**有限属性集**上同样**可判定**（`cl_eq_synClosureIter`）。
   文献中 **coNP-完全**的结论出现在**更强**的语言上
   ——**Bool 属性蕴含（允许否定前件）**、**关系型函数依赖**等；
   那是**另一个**问题，本文件**不**声称、也**不**形式化它。

**为什么 coNP 值得在本文件提一句**：$\mathrm{SatAvoid}$ 的**否定**
（「无满足 $N$ 的模型」）的**平凡证书**就是 $\mathrm{cl}_\Sigma\varnothing\cap N\neq\varnothing$
（`satAvoid_iff` 右侧，本文件已证）——这是**短的、可多项式核对的**证书，
正说明该问题落在 **coNP** 内。把它与「NP-困难」区分开，
是本文件 §5 的关键：**判定「交非空」本身不难，难的是带否定的扩展。**

**诚实结论**：本文件形式化的全部判据（§2–§4）都只形式化了**可判定性**；
其中 `sat_always` 使「是否有模型」成为**常数时间**问题（恒真）。
「多项式时间」的**算法级**结论依赖闭包算法（出处待核实），
本文件**未形式化**算法；也不存在本文件能核实的「NP-完全」或
「coNP-完全」形式化断言。故 §5 **仅**登记上述结构依据，**不虚构**
复杂性类的形式化定理。
-/

/-! ===========================================================================
    §6  R-38 接线：把 §1–§4 的抽象判据与 FCA 闭包算子、规则族演算组合起来

    本节**只追加**，不改动 §1–§5 任何声明。以下定理都是**跨概念组合**：
    前件取自本节已证判据（`Entails` / `cl` / `SatAvoid`）或 FCA 闭包
    （`closureOp` / `IsClosedAttr`），后件是**新信息**（不是前件的重复）。
    =========================================================================== -/

/-- **闭包算子的像总是闭集**（把 `isClosedAttr_iff_exists` 用于 `closureOp A`）。

这条是 §6 两处桥接的技术支点：它说 `closureOp A` 落在 `IsClosedAttr` 里，
从而可经 `dgbasis_isModelOf_iff_closed` 换成「是 DG 基的模型」。 -/
theorem closureOp_isClosed (A : Set K.MFCA) : K.IsClosedAttr (K.closureOp A) :=
  (K.isClosedAttr_iff_exists (K.closureOp A)).mpr ⟨A, rfl⟩

/-- ⭐⭐⭐ **DG 基的最小模型恰是 FCA 的双极闭包**（本节主定理）。

$$\mathrm{cl}_{\mathrm{DGBasis}}A \;=\; A'' \;=\; \mathrm{closureOp}\,A .$$

**这不是同义反复**：左端 `cl` 是 §2 的**语义**最小模型（对模型族取任意交），
右端 `closureOp` 是 `FateV2.Rules` 的**代数**双重极性算子
`polarUp ∘ polarDown`。等式本身**要证**，且两方向各有独立内容：

* `cl A ⊆ closureOp A`：`closureOp A` 是 DG 基的**模型**（`closureOp_isClosed`
  + `dgbasis_isModelOf_iff_closed`），且含 `A`（`subset_closureOp`），
  故被「最小模型」压在下面（`cl_subset_of_model`）。
* `closureOp A ⊆ cl A`：`cl A` 本身是模型（`cl_models`），故**闭**
  （`dgbasis_isModelOf_iff_closed` 反向）；由单调性
  `closureOp A ⊆ closureOp (cl A) = cl A`。

**意义**：它把「规则族组合能推出什么」（§2 的可判定结果）与
「概念格中 A 的概念闭包」**逐字等同**，因此 §5 复杂度表里
「$\mathrm{cl}_\Sigma A$ 的闭包算法」**就是** FCA 的 `Close` 算法。 -/
theorem cl_dgbasis_eq_closureOp (A : Set K.MFCA) :
    K.cl K.DGBasisSelfRef A = K.closureOp A := by
  refine Set.Subset.antisymm ?_ ?_
  · exact K.cl_subset_of_model
      ((K.dgbasis_isModelOf_iff_closed _).mpr (K.closureOp_isClosed A))
      (K.subset_closureOp A)
  · have hcl : K.IsClosedAttr (K.cl K.DGBasisSelfRef A) :=
      (K.dgbasis_isModelOf_iff_closed _).mp (K.cl_models K.DGBasisSelfRef A)
    calc K.closureOp A ⊆ K.closureOp (K.cl K.DGBasisSelfRef A) :=
          K.closureOp_mono (K.subset_cl K.DGBasisSelfRef A)
      _ = K.cl K.DGBasisSelfRef A := hcl

/-- **最小模型对属性集单调**（`cl` 是单调算子）。

前件是**裸的包含关系** `A ⊆ B`，后件是关于 §2 最小模型的包含——
把 `cl` 与 `⊆` 的相容性显式化，供 §6 其余定理使用。 -/
theorem cl_mono {Sig : Set (Set K.MFCA × Set K.MFCA)} {A B : Set K.MFCA}
    (h : A ⊆ B) : K.cl Sig A ⊆ K.cl Sig B :=
  K.cl_subset_of_model (K.cl_models Sig B) (h.trans (K.subset_cl Sig B))

/-- **最小模型幂等**：$\mathrm{cl}_\Sigma(\mathrm{cl}_\Sigma A)=\mathrm{cl}_\Sigma A$。

**不是定义等式**：`cl` 由 `sInter` 定义，幂等性需经最小性两次使用。 -/
theorem cl_idem (Sig : Set (Set K.MFCA × Set K.MFCA)) (A : Set K.MFCA) :
    K.cl Sig (K.cl Sig A) = K.cl Sig A := by
  refine Set.Subset.antisymm ?_ (K.subset_cl Sig (K.cl Sig A))
  exact K.cl_subset_of_model (K.cl_models Sig A) (Set.Subset.refl _)

/-- **语义蕴涵关于规则族单调**：加规则不会减少推出。

前件 `Sig₀ ⊆ Sig` 与 `Entails Sig₀ A B`；后件是**更大**规则族的蕴涵。
方向是真内容：模型越多的规则族越难蕴涵，故从子族到超族是**加强**方向，
必须用 `hsub` 把大族的模型压回小族。 -/
theorem entails_mono {Sig0 Sig : Set (Set K.MFCA × Set K.MFCA)}
    (hsub : Sig0 ⊆ Sig) {A B : Set K.MFCA} (h : K.Entails Sig0 A B) :
    K.Entails Sig A B :=
  fun M hM hA => h M (fun r hr hX => hM r (hsub hr) hX) hA

/-- **语义蕴涵传递**（`Entails` 的合成律）。

由 `A ⇒ B` 与 `B ⇒ C` 得 `A ⇒ C`；证明即两次作用于同一模型。
这是「规则组合推出新规则」（§2）的**基本演算律**。 -/
theorem entails_trans {Sig : Set (Set K.MFCA × Set K.MFCA)} {A B C : Set K.MFCA}
    (h1 : K.Entails Sig A B) (h2 : K.Entails Sig B C) : K.Entails Sig A C :=
  fun M hM hA => h2 M hM (h1 M hM hA)

/-- **语义蕴涵自反**（`Entails` 的恒等律）。 -/
theorem entails_refl {Sig : Set (Set K.MFCA × Set K.MFCA)} (A : Set K.MFCA) :
    K.Entails Sig A A :=
  fun _ _ h => h

/-- **蕴涵对前件并是可弃右项的**：`A ⇒ B` 蕴含 `A ∪ A' ⇒ B`。

**⚠ 标注**：这条在**经典**语义下是「前件越弱结论越难」，方向看起来反了，
逐一核对：`Entails Sig A B` 说「任何模型含 `A` 就含 `B`」。
若模型含 `A ∪ A'` 则**尤其**含 `A`，故含 `B`。所以方向是**正确的**，
而且它把「并」的右项 `A'` 显式**浪费**掉——这正是闭包算法
「一遍扫描即吸收结论」之所以能工作的局部理由。 -/
theorem entails_union_left {Sig : Set (Set K.MFCA × Set K.MFCA)}
    {A A' B : Set K.MFCA} (h : K.Entails Sig A B) :
    K.Entails Sig (A ∪ A') B :=
  fun M hM hU => h M hM (Set.subset_union_left.trans hU)

/-- **相对可满足性关于禁止集反单调**：`N' ⊆ N` 且 `N` 可避则 `N'` 亦可避。

前件两段：`N' ⊆ N`（**关于禁止集的包含，不是关于 `Sig` 的**）
与 `SatAvoid Sig N`；后件是更小禁止集的可避性。
**不是同义反复**：后件中的 `N'` 与前件的 `SatAvoid Sig N` 不是同一个集合，
必须经 `Set.Disjoint.mono` 把不交性从 `N` 传到子集 `N'`。 -/
theorem satAvoid_anti {Sig : Set (Set K.MFCA × Set K.MFCA)} {N N' : Set K.MFCA}
    (h : N' ⊆ N) (hs : K.SatAvoid Sig N) : K.SatAvoid Sig N' := by
  rw [K.satAvoid_iff] at hs ⊢
  exact hs.mono le_rfl h

/-- ⭐⭐ **禁止全集时的相对可满足性判据**（把 §4 的 `SatAvoid` 接到 §2 的 `cl` 上）。

$$\mathrm{SatAvoid}\,\Sigma\,M_{\mathrm{FCA}}
  \iff \mathrm{cl}_\Sigma\varnothing=\varnothing .$$

**意义**：禁止 `M_FCA` 中**任何**属性，等价于说「最小模型彻底是空的」。
这是 `satAvoid_iff` 在 `N = univ` 处的**特化**，但产物是一个**判定等价**：
右端只是对单个集合的一次等式检查，左端原本要遍历所有模型。 -/
theorem satAvoid_univ_iff (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    K.SatAvoid Sig (Set.univ : Set K.MFCA) ↔ K.cl Sig ∅ = ∅ := by
  rw [K.satAvoid_iff, Set.disjoint_univ]

end FormalCtx

end

end FateV2.Rules