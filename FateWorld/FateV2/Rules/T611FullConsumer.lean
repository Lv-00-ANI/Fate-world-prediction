/-
============================================================================
  消费方：T611Full 的消费定理（DG 基完备/不冗余 + ARM 不完备）
============================================================================
本文件**只新增**，不修改任何已有模块。它消费 `FateV2.Rules` 的核心结论：

| T611Full 的结论 | 本文件的消费方式 |
|---|---|
| `dgbasis_represents_iff` | §2 把「完备」展开成逐点判据，用于反证 |
| `t611_DG_models` / `t611_ARM_rule_false` | §3 分离「DG 可靠」与「ARM 不可靠」 |
| `t611_DG_complete_nonredundant` | §4 在具体背景 `exCtx` 上实例化（含 `FiniteAttrs`） |
| `ex_int_eq` / `dgbasis_represents_iff` | §5 逐项算出 `exCtx` 上 DG 基的模型类 |

## 诚实定位
- 本文件是**消费方**：所有实质结果都来自 `FateV2.Rules`；
  这里只做**桥接 / 展开 / 具体化**，不重复证明 T6.11 本身。
- §1 的 `notComplete_of_notClosed_model` 是一个**一般性桥接引理**：
  它从「某集合满足 `Sig\{r}` 但不闭」直接推出「`Sig\{r}` 不完备」，
  用的是 `dgbasis_represents_iff` 的展开。它**不是** `T611Full` 已有的陈述。
- §3 的分离陈述使用的是 `T611Full` 对 `exCtx` 的**逐项核算**
  （`ex_armRulesSup_eq` + `t611_ARM_rule_false`），不是假设。
- §4 的 `FiniteAttrs exCtx` 是本文件新增的 `instance`（`Fin 2` 有限）。

## 无 sorry
本文件零 `sorry` / `admit` / `axiom`。
============================================================================
-/

import FateWorld.FateV2.Rules.T611Full
namespace FateV2.Rules
open Set

variable {K : FormalCtx}

/-!
  # Rules · T611FullConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T611FullConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T611Full
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
   §1  一般桥接引理：非闭模型 ⟹ 不完备
   =========================================================================== -/

/-- **一般桥接**：若某个集合 $M$ 满足 $\Sigma\setminus\{r\}$ 但**不闭**，
则 $\Sigma\setminus\{r\}$ **不是完备表示**。

**证明**：由 `dgbasis_represents_iff`，完备 $\iff$ 每个模型都闭。
而 $M$ 是该规则集的模型且不闭，故不完备。∎

**为什么这不是同义反复**：前件只给「$M$ 满足删后规则集」与「$M$ 不闭」
（两条关于**不同对象**的事实），结论是「规则集不完备」（一个关于
**模型类与闭集类相等**的命题）。中间的翻译由 `dgbasis_represents_iff`
提供，是实质的一步。 -/
theorem notComplete_of_notClosed_model {Sig : Set (Set K.MFCA × Set K.MFCA)}
    {r : Set K.MFCA × Set K.MFCA} (M : Set K.MFCA)
    (hm : K.IsModelOf (Sig \ {r}) M) (hnc : ¬ K.IsClosedAttr M) :
    ¬ K.IsComplete (Sig \ {r}) := by
  intro hcomp
  rw [dgbasis_represents_iff] at hcomp
  exact hnc ((hcomp M).mp hm)

/-- **完备性对规则集的反向用法**：若 $\Sigma$ 完备且 $M$ 满足 $\Sigma$，
则 $M$ 是闭集。

这是 `dgbasis_represents_iff` 的「$\mathrm{Mod}\subseteq\mathrm{Int}$」方向，
本文件把它单独命名以便 §5 引用。 -/
theorem isClosedAttr_of_isComplete {Sig : Set (Set K.MFCA × Set K.MFCA)}
    (hcomp : K.IsComplete Sig) {M : Set K.MFCA} (hm : K.IsModelOf Sig M) :
    K.IsClosedAttr M :=
  ((dgbasis_represents_iff Sig).mp hcomp M).mp hm

/-! ===========================================================================
   §2  DG 基完备 ⟹ 任一模型闭（消费 `t611_DG_complete`）
   =========================================================================== -/

/-- **DG 基完备的逐点消费**：任何满足 DG 基的属性集都是闭集。

直接把 `t611_DG_complete` 代入 §1 的 `isClosedAttr_of_isComplete`。 -/
theorem isClosedAttr_of_isModelOf_dgbasis_selfRef {M : Set K.MFCA}
    (hm : K.IsModelOf K.DGBasisSelfRef M) : K.IsClosedAttr M :=
  isClosedAttr_of_isComplete t611_DG_complete hm

/-- **DG 基可靠性的逐点消费**：对**伪内涵** $P$，规则
$P\Rightarrow P''$ 属于 DG 基，故由 `t611_DG_models` 是真蕴含。 -/
theorem dgRule_models_via_t611 {P : Set K.MFCA} (hP : K.IsPseudoIntent P) :
    K.Models P (K.closureOp P) :=
  t611_DG_models (P, K.closureOp P) ⟨P, hP, rfl⟩

/-! ===========================================================================
   §3  分离：DG 基可靠 vs. ARM 在 `exCtx` 上不可靠
   =========================================================================== -/

/-- ⭐ **T6.11 的核心对比（可靠性维度）**：
DG 基的每条规则都是真蕴含（`t611_DG_models`），
而 $\mathbb{K}_{ex}$ 上阈值 $1$ 的 ARM 输出**包含一条假蕴含**
（`t611_ARM_rule_false`）。

形式化：$\mathrm{ARM}_1$ **不是**「逐条可靠」的规则集——
即存在其中一条规则在 $\mathbb{K}_{ex}$ 上不成立。

**⟹ 「ARM 不漏真」的通俗说法不成立**——它连「不产假」都做不到。 -/
theorem ex_arm_rule_unreliable :
    ∃ r ∈ {r | armRulesSup exCtx 1 r}, ¬ exCtx.Models r.1 r.2 := by
  refine ⟨(∅, ({0} : Set exCtx.MFCA)), ?_, t611_ARM_rule_false⟩
  rw [ex_armRulesSup_eq (by decide) (by decide : (1 : ℕ) ≤ 1)]
  exact Set.mem_singleton _

/-- **DG 基在 `exCtx` 上逐条可靠**（与上一条形成对照）。
把 `t611_DG_models` 实例化到 `exCtx`。 -/
theorem ex_dg_rules_reliable :
    ∀ r ∈ exCtx.DGBasisSelfRef, exCtx.Models r.1 r.2 :=
  fun r hr => t611_DG_models r hr

/-! ===========================================================================
   §4  在具体背景 `exCtx` 上实例化 DG 基的完备且不冗余
   =========================================================================== -/

/-- **`exCtx` 满足 `FiniteAttrs`**：其属性集 `Fin 2` 有限，故 `Set.univ` 有限。 -/
instance exCtx_finiteAttrs : exCtx.FiniteAttrs :=
  ⟨by show (Set.univ : Set (Fin 2)).Finite; exact Set.finite_univ⟩

/-- ⭐ **T6.11 前半在 `exCtx` 上的实例**：
$\mathbb{K}_{ex}$ 的 DG 基**完备且不冗余**。

`FiniteAttrs` 前件由本文件新增的 `exCtx_finiteAttrs` 提供。 -/
theorem ex_dg_complete_nonredundant :
    exCtx.IsComplete exCtx.DGBasisSelfRef ∧ exCtx.IsNonRedundant exCtx.DGBasisSelfRef :=
  t611_DG_complete_nonredundant

/-- **`exCtx` 上 DG 基的强不冗余**（`IsStrongNonRedundant`）的实例。 -/
theorem ex_dg_strongNonredundant :
    IsStrongNonRedundant exCtx.DGBasisSelfRef :=
  (t611_DG_complete_strongNonRedundant (K := exCtx)).2

/-! ===========================================================================
   §5  逐项核算：`exCtx` 上 DG 基的模型类 = `{∅, {a}, univ}`
   =========================================================================== -/

/-- ⭐⭐ **`exCtx` 上 DG 基模型类的完整刻画**：
$$\mathrm{Mod}(\mathrm{DGBasisSelfRef}) = \{\varnothing, \{a\}, \mathrm{univ}\}.$$

**证明**：由 `dgbasis_represents_iff` 与 `t611_DG_complete`，
模型类等于闭集类；再由 `ex_int_eq`，闭集类即三元素集。∎

**这是 T6.11 前半在具体背景上的逐项核算**——
与 §3 的 `ex_arm_rule_unreliable` 一起，说明「完备表示」不是空话。 -/
theorem ex_dg_mod_eq_int :
    {M : Set exCtx.MFCA | exCtx.IsModelOf exCtx.DGBasisSelfRef M}
      = {∅, {0}, Set.univ} := by
  have h := (dgbasis_represents_iff (K := exCtx) exCtx.DGBasisSelfRef).mp
    (t611_DG_complete (K := exCtx))
  show {M : Set exCtx.MFCA | exCtx.IsModelOf exCtx.DGBasisSelfRef M} = {∅, {0}, Set.univ}
  rw [show {M : Set exCtx.MFCA | exCtx.IsModelOf exCtx.DGBasisSelfRef M}
        = {M : Set exCtx.MFCA | exCtx.IsClosedAttr M} from by
      ext M; exact h M]
  exact ex_int_eq

/-- **推论**：`{b} = {1}` **不是** DG 基的模型（因为不闭）。

这给出 §3 反例所依赖的同一个「非闭集」见证。 -/
theorem ex_singleton_b_not_model_dg :
    ¬ exCtx.IsModelOf exCtx.DGBasisSelfRef ({1} : Set exCtx.MFCA) := by
  intro hm
  have hclosed : exCtx.IsClosedAttr ({1} : Set exCtx.MFCA) :=
    isClosedAttr_of_isModelOf_dgbasis_selfRef hm
  have h1 : ({1} : Set exCtx.MFCA) ∈ ({∅, {0}, Set.univ} : Set (Set exCtx.MFCA)) := by
    rw [← ex_int_eq]; exact hclosed
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  -- 三种情形都用「{1} 含 1 但目标集不含 1」或「目标集含 0」矛盾
  have hmem : (1 : exCtx.MFCA) ∈ ({1} : Set exCtx.MFCA) := Set.mem_singleton 1
  rcases h1 with h | h | h
  · rw [h] at hmem; exact absurd hmem (Set.notMem_empty 1)
  · rw [h] at hmem; rw [Set.mem_singleton_iff] at hmem
    exact absurd (congrArg Fin.val hmem) (by decide)
  · have h0 : (0 : exCtx.MFCA) ∈ ({1} : Set exCtx.MFCA) := h ▸ Set.mem_univ 0
    rw [Set.mem_singleton_iff] at h0
    exact absurd (congrArg Fin.val h0) (by decide)

end FateV2.Rules