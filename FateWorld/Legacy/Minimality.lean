/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Minimality
阶段：**阶段 1B —— DG 基的最小性**（规格 T1A.10 的「最小」一半）

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
规格 `02-证明路线/01-路线图.md` **T1A.10**：

> `DG 基是最小完备蕴含基`｜前件：**形式背景有限**｜类别 ①

`Fate.Completeness` 已证其中的**完备性**（`completeness_Mod_eq_Int`）。
本文件陈述并（在前置引理之下）证明**最小性**——

> **教材 Theorem 3.49**（Guigues–Duquenne basis is the **smallest** one）.
> If $T$ is the Guigues-Duquenne base and $T'$ is complete then
> $|T| \le |T'|$. **Proof. Direct corollary of the above Lemma.**（即 Lemma 3.48）

---------------------------------------------------------------------------
诚实边界（**务必先读**）
---------------------------------------------------------------------------
本文件**不引入任何 `sorry` / `axiom`**（沿用全库规范）。

因此 **Theorem 3.49 的陈述是「在前置引理之下」的**：

| 前置引理 | 内容 | 本文件状态 |
|---|---|---|
| `Lemma348` | 完备 $T$ 覆盖每个伪内涵的闭包 | **具名前件**（教材 Lemma 3.48） |
| `PseudoIntentClosureInjective` | 不同伪内涵的闭包不同 | **具名前件**（标准事实） |

**为什么这两条是具名前件**：

- **Lemma 3.48** 的教材证明使用「$\mathrm{Mod}(T)$ 是闭包系统」
  「$A^{\downarrow\uparrow}\cap P$ 不是 intent」等**前文结果**
  （原文以「(Thm. on basic connections…)」引用先前编号）。
  完整转写须先形式化那些结果——属**独立工作量**。
- **`PseudoIntentClosureInjective`** 在**教材的伪内涵定义**下
  由「apply to $P$」一步立得；但在**本库为规避自指而采用的
  良基递归定义**（`IsPseudoIntent`，见 `Fate.Implication` §2.1）下，
  该步需要「配对形 ⟹ 扁平形」——**已被实证否证**
  （`Fate.Completeness` §5.1：114/952 反例）。
  故本文件**如实登记为具名前件**，而不写出一个假的证明。

**本文件确已完整证明的部分**：从上述两条前置引理**推出** Theorem 3.49
（`guiguesDuquenne_basis_minimal`）——即教材所说的
「**Direct corollary of the above Lemma**」这一归约本身。
**这归约不是同义反复**：它需要在 DG 基的元素与 $T$ 的元素之间
构造一个**单射**（`coverRule` + `CoverRule` 的 `InjOn` 证明）。
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Powerset
import FateWorld.Legacy.Completeness

namespace Fate

open Set

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ===========================================================================
   §1  一般蕴含集的完备性（教材 Thm 3.40 的转写）
   =========================================================================== -/

/-- **蕴含集 $T$ 完备**（教材 **Theorem 3.40** 的判据，逐字）：

> $T$ is complete in $\langle X,Y,I\rangle$
> **iff** $\mathrm{Mod}(T)=\mathrm{Int}(X,Y,I)$.

**本定义**：$\mathrm{Mod}(T)$ 是 $T$ 的模型类（`IsModelOf`），
$\mathrm{Int}$ 是闭属性集类（`IsClosedAttr`）。完备即二者相等。

**与 §4 的关系**：`Fate.Completeness.completeness_Mod_eq_Int` 证明
$\mathrm{DGBasisSelfRef}$ 满足本定义（见 `dgbasis_isComplete`）。 -/
def IsComplete (Sig : Set (Set K.MFCA × Set K.MFCA)) : Prop :=
  {M : Set K.MFCA | K.IsModelOf Sig M} = {M : Set K.MFCA | K.IsClosedAttr M}

/-- **DG 基是完备的**（`Fate.Completeness` §4 的结果的接口重述）。

**证明**：由 `isModel_iff_isModelOf_dgbasis`，
「$M$ 是 `DGBasisSelfRef` 的模型」$\iff$「$M$ 是 `IsModel`」；
再由 `completeness_Mod_eq_Int` 得 $\mathrm{Mod}=\mathrm{Int}$。∎ -/
theorem dgbasis_isComplete : K.IsComplete K.DGBasisSelfRef := by
  unfold IsComplete
  rw [show {M : Set K.MFCA | K.IsModelOf K.DGBasisSelfRef M}
        = {M : Set K.MFCA | K.IsModel M} from by
      ext M; exact (K.isModel_iff_isModelOf_dgbasis M).symm,
    K.completeness_Mod_eq_Int]

/-! ===========================================================================
   §2  前置引理（教材 Lemma 3.48 与伪内涵闭包单射性）
   =========================================================================== -/

/-- **教材 Lemma 3.48**（逐字）：

> If $T$ is complete, then for each pseudo-intent $P$,
> $T$ contains $A\Rightarrow B$ with $A^{\downarrow\uparrow}=P^{\downarrow\uparrow}$.

**本实现的形式**（把「$A\Rightarrow B\in T$ 且 $A''=P''$」
打包成单个存在量词，以便下游直接 `Classical.choose`）：

$$\forall T,\ T\text{ 完备}\ \Longrightarrow\
  \forall P,\ P\text{ 伪内涵}\ \Longrightarrow\
  \exists r\in T,\ r.1'' = P''.$$

**为何是具名前件**：见文件头「诚实边界」。教材的证明依赖若干前文结果，
完整转写属独立工作量。**本实现不写出一个假的证明。** -/
def Lemma348 : Prop :=
  ∀ Sig : Set (Set K.MFCA × Set K.MFCA), K.IsComplete Sig →
    ∀ P : Set K.MFCA, K.IsPseudoIntent P →
      ∃ r : Set K.MFCA × Set K.MFCA,
        r ∈ Sig ∧ K.closureOp r.1 = K.closureOp P

/-- **前置引理：不同伪内涵的闭包不同**
（标准事实；教材「apply to $P$」一步的推论）。

$$\forall P,Q,\ P,Q\text{ 伪内涵}\ \Longrightarrow\ P''=Q''\ \Longrightarrow\ P=Q.$$

**为何是具名前件**：在**教材的伪内涵定义**下它是「apply to $P$」一步；
但在本库的**良基自指定义** `IsPseudoIntent` 下，
该步需要「配对形 $\Rightarrow$ 扁平形」——**已被实证否证**
（`Fate.Completeness` §5.1）。故如实登记为具名前件。

**注意它与最小性的关系**：本引理正是使
「伪内涵 $\mapsto$（$T$ 中的覆盖规则）」这一段成为**单射**的关键，
从而 Lemma 3.48 给出的覆盖才是**基数下界**（而非仅覆盖）。 -/
def PseudoIntentClosureInjective : Prop :=
  ∀ P Q : Set K.MFCA, K.IsPseudoIntent P → K.IsPseudoIntent Q →
    K.closureOp P = K.closureOp Q → P = Q

/-! ===========================================================================
   §3  DG 基元素的基本结构引理
   =========================================================================== -/

/-- **DG 基元素的第一分量是伪内涵**。 -/
theorem isPseudoIntent_fst_of_mem_DGBasisSelfRef
    {r : Set K.MFCA × Set K.MFCA} (hr : r ∈ K.DGBasisSelfRef) :
    K.IsPseudoIntent r.1 := by
  obtain ⟨P, hP, rfl⟩ := hr
  exact hP

/-- **DG 基元素的第二分量正是第一分量的闭包**：$r=(P,P'')$ 故 $r.2=r.1''$。

这条是「DG 基元素被它的第一分量唯一决定」的形式化，
也是下游 `InjOn` 证明的收尾一步。 -/
theorem snd_eq_closureOp_fst_of_mem_DGBasisSelfRef
    {r : Set K.MFCA × Set K.MFCA} (hr : r ∈ K.DGBasisSelfRef) :
    r.2 = K.closureOp r.1 := by
  obtain ⟨P, _, rfl⟩ := hr
  rfl

/-! ===========================================================================
   §4  覆盖映射（cover map）
   =========================================================================== -/

/-- **覆盖映射**：把 DG 基的元素 $r=(P,P'')$ 送到 $T$ 中一条
「$r.1''=r.2$ 的覆盖规则」，其存在性由 **Lemma 3.48** 保证。

**实现**：对 $r\in\mathrm{DGBasisSelfRef}$，其第一分量 $r.1$ 是伪内涵
（`isPseudoIntent_fst_of_mem_DGBasisSelfRef`），
故 `Lemma348` 给出 $T$ 中一条 $r'$ 满足 $r'.1''=r.1''=r.2$。
本定义对**所有** $r$ 取 `ite`：在 DG 基上取 `Classical.choose`，
否则返回 $r$ 本身（该分支在 `InjOn` 证明中被 `hr` 排除，不影响结论）。

**为何要「所有 $r$」**：`Set.ncard_le_ncard_of_injOn` 要求映射定义在
**整个类型**上，`InjOn` 只在 `DGBasisSelfRef` 上验证。 -/
def coverRule (h348 : K.Lemma348)
    (Sig : Set (Set K.MFCA × Set K.MFCA)) (hT : K.IsComplete Sig)
    (r : Set K.MFCA × Set K.MFCA) : Set K.MFCA × Set K.MFCA := by
  classical
  exact
    if hr : r ∈ K.DGBasisSelfRef then
      Classical.choose
        (h348 Sig hT r.1 (K.isPseudoIntent_fst_of_mem_DGBasisSelfRef hr))
    else r

/-- **覆盖映射的展开引理**（在 DG 基上）。

这把 `coverRule` 的 `if` 在 `hr : r ∈ DGBasisSelfRef` 下化简为
`Classical.choose`，使下游不必反复展开定义。 -/
theorem coverRule_eq_choose (h348 : K.Lemma348)
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (hT : K.IsComplete Sig)
    {r : Set K.MFCA × Set K.MFCA} (hr : r ∈ K.DGBasisSelfRef) :
    K.coverRule h348 Sig hT r =
      Classical.choose
        (h348 Sig hT r.1 (K.isPseudoIntent_fst_of_mem_DGBasisSelfRef hr)) := by
  classical
  rw [coverRule, dif_pos hr]

/-- **覆盖映射落在 $T$ 中**（在 DG 基上）。 -/
theorem coverRule_mem (h348 : K.Lemma348)
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (hT : K.IsComplete Sig)
    {r : Set K.MFCA × Set K.MFCA} (hr : r ∈ K.DGBasisSelfRef) :
    K.coverRule h348 Sig hT r ∈ Sig := by
  classical
  rw [K.coverRule_eq_choose h348 hT hr]
  exact (Classical.choose_spec
    (h348 Sig hT r.1 (K.isPseudoIntent_fst_of_mem_DGBasisSelfRef hr))).1

/-- **覆盖映射保持「第一分量的闭包」**：$(\text{coverRule}\,r).1''=r.2$。 -/
theorem coverRule_closureOp (h348 : K.Lemma348)
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (hT : K.IsComplete Sig)
    {r : Set K.MFCA × Set K.MFCA} (hr : r ∈ K.DGBasisSelfRef) :
    K.closureOp (K.coverRule h348 Sig hT r).1 = r.2 := by
  classical
  rw [K.coverRule_eq_choose h348 hT hr]
  exact (Classical.choose_spec
      (h348 Sig hT r.1 (K.isPseudoIntent_fst_of_mem_DGBasisSelfRef hr))).2.trans
    (K.snd_eq_closureOp_fst_of_mem_DGBasisSelfRef hr).symm

/-- **覆盖映射在 DG 基上是单射**。

**证明**：设 $r,s\in\mathrm{DGBasisSelfRef}$ 且
$\text{coverRule}\,r=\text{coverRule}\,s=:t$。
由 `coverRule_closureOp` 两次得
$$r.2=(\text{coverRule}\,r).1''=t.1''=(\text{coverRule}\,s).1''=s.2.$$
两端第一分量的闭包相等；而 $r.1,s.1$ 都是伪内涵
（`isPseudoIntent_fst_of_mem_DGBasisSelfRef`），故由**前置引理**
`PseudoIntentClosureInjective` 得 $r.1=s.1$。
再由 `snd_eq_closureOp_fst_of_mem_DGBasisSelfRef` 二者第二分量
都等于公共第一分量的闭包，故 $r=s$。∎

**这正是教材「Direct corollary」中真正的组合内容**——
Lemma 3.48 给出**覆盖**，本引理（用伪内涵闭包单射性）把覆盖升级为**单射**，
从而给出**基数下界**。 -/
theorem coverRule_injOn (h348 : K.Lemma348) (hinj : K.PseudoIntentClosureInjective)
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (hT : K.IsComplete Sig) :
    InjOn (K.coverRule h348 Sig hT) K.DGBasisSelfRef := by
  intro r hr s hs heq
  -- 第一分量的闭包相等
  have hc : K.closureOp r.1 = K.closureOp s.1 := by
    rw [← K.snd_eq_closureOp_fst_of_mem_DGBasisSelfRef hr,
        ← K.coverRule_closureOp h348 hT hr, heq,
        K.coverRule_closureOp h348 hT hs,
        K.snd_eq_closureOp_fst_of_mem_DGBasisSelfRef hs]
  -- 伪内涵闭包单射性给出第一分量相等
  have hfst : r.1 = s.1 :=
    hinj r.1 s.1 (K.isPseudoIntent_fst_of_mem_DGBasisSelfRef hr)
      (K.isPseudoIntent_fst_of_mem_DGBasisSelfRef hs) hc
  -- 第二分量都是公共第一分量的闭包
  have hr' : r = (r.1, K.closureOp r.1) := by
    rw [← K.snd_eq_closureOp_fst_of_mem_DGBasisSelfRef hr]
  have hs' : s = (s.1, K.closureOp s.1) := by
    rw [← K.snd_eq_closureOp_fst_of_mem_DGBasisSelfRef hs]
  rw [hr', hs', hfst]

/-! ===========================================================================
   §5  主定理：DG 基的基数最小性（教材 Theorem 3.49）
   =========================================================================== -/

/-- ⭐ **教材 Theorem 3.49**（Guigues–Duquenne basis is the **smallest** one）。

> If $T$ is the Guigues-Duquenne base and $T'$ is complete then $|T|\le|T'|$.

**形式**：设背景属性集有限（`[Fintype K.MFCA]`，即规格 T1A.10 的
「形式背景有限」前件），对**任意完备蕴含集** $T$，

$$|\mathrm{DGBasisSelfRef}|\ \le\ |T|.$$

**前件**：
- `h348 : K.Lemma348` —— 教材 Lemma 3.48（具名，见 §2）；
- `hinj : K.PseudoIntentClosureInjective` —— 伪内涵闭包单射性（具名，见 §2）。

**证明（本文件已完整形式化）**：
1. 定义覆盖映射 $\text{coverRule}\colon\mathrm{DGBasisSelfRef}\to T$
   （§4），其在 DG 基上取值于 $T$（`coverRule_mem`）；
2. 由伪内涵闭包单射性证明 $\text{coverRule}$ 在 DG 基上**单射**
   （`coverRule_injOn`）；
3. 对**有限**目标集用 `Set.ncard_le_ncard_of_injOn` 得到基数下界。∎

**推论（用户所述「非冗余基中基数最小」）**：
任何**非冗余的完备**基 $T$（`IsNonRedundant` 且 `IsComplete`）
都是本定理的特例——故 DG 基在其**基数最小**。∎

**⚠ 关于前件的诚实说明**：本定理本身（归约）已完整证明、
零 `sorry`；其**两条前置引理**未在本库形式化（理由见文件头）。
**本实现不把前件藏进 `sorry`**，而是把它们做成**显式的、可陈述的**
`def ... : Prop`——故本定理是**条件定理**，条件透明。 -/
theorem guiguesDuquenne_basis_minimal [Fintype K.MFCA]
    (h348 : K.Lemma348) (hinj : K.PseudoIntentClosureInjective)
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (hT : K.IsComplete Sig) :
    K.DGBasisSelfRef.ncard ≤ Sig.ncard :=
  Set.ncard_le_ncard_of_injOn (K.coverRule h348 Sig hT)
    (fun _ hr => K.coverRule_mem h348 hT hr)
    (K.coverRule_injOn h348 hinj hT)

/-- **定理 3.49 的「两边都是 DG 基」自反特例**（一致性检查）。

取 $T=\mathrm{DGBasisSelfRef}$，则 $|T|\le|T|$。 -/
theorem dgbasis_minimal_self [Fintype K.MFCA]
    (h348 : K.Lemma348) (hinj : K.PseudoIntentClosureInjective) :
    K.DGBasisSelfRef.ncard ≤ K.DGBasisSelfRef.ncard :=
  K.guiguesDuquenne_basis_minimal h348 hinj K.dgbasis_isComplete

/-! ===========================================================================
   §6  非冗余基版本（用户所述形式）
   =========================================================================== -/

/-- **非冗余的完备基**：同时满足教材 Def 3.38（`IsNonRedundant`，
在 `Fate.Completeness` 中）与 Thm 3.40（`IsComplete`）。

**用户所述「DG 基在非冗余基中基数最小」精确对应本谓词**：
非冗余性保证「没有浪费的规则」，完备性保证「能推出一切真蕴含」。 -/
def IsNonRedundantComplete (Sig : Set (Set K.MFCA × Set K.MFCA)) : Prop :=
  K.IsNonRedundant Sig ∧ K.IsComplete Sig

/-- ⭐ **定理 3.49（非冗余基版本）**：在**非冗余完备基**中，DG 基基数最小。

**证明**：`IsNonRedundantComplete` 投影出 `IsComplete`，
再用 `guiguesDuquenne_basis_minimal`。∎

**注**：教材 Thm 3.49 的原文前件其实**只需完备**（不需非冗余）——
因 Lemma 3.48 给出的下界对**任意**完备 $T$ 都成立。
非冗余性在此**不是必需的**，但它是用户问题的语境；
本实现**如实指出**这一「前件比用户表述更弱」的事实，
**不**假装非冗余性是证明的一部分。 -/
theorem guiguesDuquenne_basis_minimal_nonRedundant [Fintype K.MFCA]
    (h348 : K.Lemma348) (hinj : K.PseudoIntentClosureInjective)
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (hT : K.IsNonRedundantComplete Sig) :
    K.DGBasisSelfRef.ncard ≤ Sig.ncard :=
  K.guiguesDuquenne_basis_minimal h348 hinj hT.2

end FormalCtx

end

end Fate
