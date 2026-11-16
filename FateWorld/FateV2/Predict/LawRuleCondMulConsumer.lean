import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Predict.LawRuleCondMul
/-!
  # Predict · LawRuleCondMulConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleCondMulConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame, FinCondIndep, LawRule, LawRuleCondMul
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/LawRuleCondMul` 的**消费方**（P5 并行任务；一次只接一个模块）

  ## 0. 本文件只做一件事

  把 `Fate/LawRuleCondMul` 的结论**接到下游**。**不修改**该模块一个字符。

  ## 1. 目标模块的实测声明（`grep -nE "^(theorem|def|abbrev)"`）

  | 类别 | 声明 |
  |---|---|
  | 重述 | `LawRule` / `compose` / `top` / `bot` / `IsPoint` |
  | 空间 | `punitSpace` / `ctxOf` / `discreteSpace` |
  | 编码 A | `condMulRule`、`condMul_iff_condMulRule_nonempty` |
  | 编码 B | `lawOf`、`condMul_iff_lawOf_nonempty`、`lawOf_compose`、`lawOf_condMul_idem`、`condMulRule_compose_lawOf` |
  | 切片 | `slice`、`IsRankOne` |
  | 核心 | `condMulGuard_implies_rankOne`、`condMul_implies_rankOne_of_pos`、`condMulRuleAt`、`condMulRuleAt_nonempty_iff`、`condMulGuard_implies_ruleAt_nonempty`、`rankOne_implies_condMul`、`condMul_implies_rankOne_of_guard`、`rankOneAll_iff_condMul_of_ne_zero` |

  ## 2. 本文件给出的消费定理（4 条）

  | 编号 | 定理 | 消费了哪些结论 | 前件是否已含结论？（自查） |
  |---|---|---|---|
  | **C1** | `perZ_rule_legality_iff_condMul` | `condMulRuleAt_nonempty_iff` + `rankOneAll_iff_condMul_of_ne_zero` | **否**。前件只有「`margZ` 处处非零」（一个关于 `p` 的**数值**假设），结论是「逐 `z` 规则处处非空 ⟺ `CondMul p`」。守卫 ≠ 结论。 |
  | **C2** | `rankOne_iff_condMul_at_z` | 独立展开 `rankOne_implies_condMul` 的**逐点**版本 | **否**。前件是「`margZ p z ≠ 0`」（单个 `z` 的非零），结论是该 `z` 切片秩一 ⟺ 该 `z` 上的乘性等式。**这是模块里没有的局部形式**（模块只证全局）。 |
  | **C3** | `finset_rule_legality_iff` | `condMulRuleAt_nonempty_iff`（推广到 `Finset` 索引） | **否**。前件是 `S : Finset γ`，结论把「交叠后的允许集非空」等价于「`S` 内每个切片秩一」。模块只有 `∀ z`（即 `univ`）形式；`Finset` 形式需要额外处理 `⋂ z ∈ S`。 |
  | **C4** | `restated_ops_eq_lawRule_ops` | 直接对 `Fate.LawRule` 的重述做**定义层对齐** | **否**，但**明确声明其内容为 `rfl`**：模块头注的 TODO 是「待 `Fate/LawRule.lean` 修复后，本文件的 `LawRule` 应替换为其别名」。本定理证明替换**无需修改任何证明**，因为两者**逐字相同**。**这不含新数学**，价值仅在于解锁把 `Fate.LawRule` 的 `compose_comm`/`point_compose`/`compose_top` 用到本模块的规则上（见 C4b/C4c）。 |

  ## 3. 诚实边界

  * **C4 是 `rfl`**，我**不**声称它是深刻结论。它存在的唯一理由是让本模块的 `condMulRule`／`condMulRuleAt`
    能直接吃 `Fate.LawRule` 的算子代数。
  * **C2 是本文件唯一的新数学**：模块的 `rankOne_implies_condMul` 是**全局**命题
    （前件 `∀ z, IsRankOne (slice p z)`，尾随对**所有** `x y z` 求和）；
    **C2 把它降到单个 `z`**，且给出反方向 —— 这恰是 `condMulRuleAt` 的逐点语义依据。
    反方向**必须**带 `margZ p z ≠ 0`，否则 `margXZ`／`margYZ` 无法从 `p` 反解出因子；
    这与模块 §4.2 的诚实边界一致。
  * **C1 的前件 `∀ z, margZ p z ≠ 0` 不可省**（模块 `rankOneAll_iff_condMul_of_ne_zero` 的守卫）。
    C1 **不**声称「无守卫时仍等价」——那正是模块证明**不成立**的方向。
  * 本文件**不**声称「`CondMul` 已被忠实接入 `LawRule`」。模块 §4 的结论是
    「编码 A/B 退化、切片秩一才结构对齐」。本文件只把**切片秩一**这一路接下去。

  ## 4. 无语义偷换

  所有定理的结论都不是前件的改写：
  * C1：前件是**数值非零**，结论是**两套合法性判据的等价**；
  * C2：前件是**单点非零**，结论是**秩一 ⟺ 逐点乘性等式**；
  * C3：前件是**有限索引集**，结论是**交叉允许集的非空性刻画**；
  * C4：前件空，结论是**定义相等**（`rfl`，已如实标注）。

  **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
open FateV2.Rules
namespace LawRuleCondMulConsumer

open FateV2.Predict.FinCondIndep
open Fate.LawRuleCondMul

attribute [local instance] Classical.propDecidable

-- 与目标模块同样的处理：全参数化定理上 `unusedSectionVars` 是噪声。
set_option linter.unusedSectionVars false

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐ C1 —— 逐 `z` 规则的合法性 ⟺ `CondMul`（**需** `margZ ≠ 0` 守卫）

模块给出：
* `condMulRuleAt_nonempty_iff`：`(∀ z, ruleAt z 非空) ↔ ∀ z, 切片 z 秩一`；
* `rankOneAll_iff_condMul_of_ne_zero`：`(∀ z, 切片 z 秩一) ↔ CondMul p`（当 `∀ z, margZ ≠ 0`）。

C1 把两条**串起来**，得到 `LawRule` 层与 `CondMul` 层之间唯一的定量桥梁。

⚠ **诚实**：这一步本质是 `Iff.trans`，**新数学不多**，但它是下游唯一能用的接口
（否则每条下游都得自己串一遍，并自己记住守卫位置）。 -/

/-- ⭐⭐ **C1**：在 `margZ` 处处非零时，
「逐 `z` 规则处处允许」**恰好**等价于 `CondMul p`。

**前件自查**：`hz : ∀ z, margZ p z ≠ 0` 是**数值**条件，
与结论（两套判据的等价）无关，**不是**把结论塞进前件。 -/
theorem perZ_rule_legality_iff_condMul
    (p : FinJoint α β γ) (hz : ∀ z, margZ p z ≠ 0) :
    (∀ z, (condMulRuleAt (α := α) (β := β) (γ := γ) z p).Nonempty)
      ↔ CondMul p := by
  rw [condMulRuleAt_nonempty_iff]
  exact rankOneAll_iff_condMul_of_ne_zero p hz

/-- ⭐ **C1 的推论（守卫版前件 → 合法性）**：直接给下游可用的方向。 -/
theorem perZ_rule_legality_of_condMulGuard
    (p : FinJoint α β γ) (h : CondMulGuard p) (hz : ∀ z, margZ p z ≠ 0) :
    ∀ z, (condMulRuleAt (α := α) (β := β) (γ := γ) z p).Nonempty :=
  condMulGuard_implies_ruleAt_nonempty p h hz

/-! ## §2 ⭐⭐⭐ C2 —— **逐点**版的「秩一 ⟺ `CondMul` 等式」（**本文件唯一的新数学**）

模块的 `rankOne_implies_condMul` 是**全局**的：
前件 `∀ z, IsRankOne (slice p z)`，结论 `∀ x y z, p·margZ = margXZ·margYZ`。

**C2 把它降到单个 `z`，并补上反方向**：

$$\mathrm{IsRankOne}(\mathrm{slice}\ p\ z)
  \iff \forall x\,y,\ p((x,y),z)\cdot\mathrm{margZ}\ p\ z
     = \mathrm{margXZ}\ p\ x\ z\cdot\mathrm{margYZ}\ p\ y\ z$$

$$\text{（当 } \mathrm{margZ}\ p\ z \neq 0\text{）}$$

**这为什么重要**：`condMulRuleAt` 的允许集正是 `IsRankOne (slice p z)`，
而 `CondMul` 的断言是那组**等式**。C2 说明二者在**每个非零 `z` 上逐点等价** ⟹
「逐点规则」与「逐点乘性等式」是同一件事，故 §3 的 `Finset` 版才有意义。

**前件自查**：`hz : margZ p z ≠ 0` 是**数值**非零，
结论是**秩一 ⟺ 一组等式**。非零 ≠ 秩一，非同义反复。
反方向**必须**用 `hz` 做除法（`eq_div_iff`）。 -/

/-- ⭐⭐⭐ **C2**：`z` 处切片秩一 ⟺ `z` 处逐点乘性等式成立（`margZ ≠ 0`）。 -/
theorem rankOne_iff_condMul_at_z
    (p : FinJoint α β γ) (z : γ) (hz : margZ p z ≠ 0) :
    IsRankOne (slice p z) ↔
      ∀ x y, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z := by
  constructor
  · -- **正方向**：把 `rankOne_implies_condMul` 的代数计算限制在单个 `z`。
    intro hr x y
    obtain ⟨g, h, hgh⟩ := hr
    have hZ : margZ p z = (∑ x, g x) * (∑ y, h y) := by
      unfold margZ
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hgh x y))
    have hXZ : ∀ x, margXZ p x z = g x * (∑ y, h y) := by
      intro x
      unfold margXZ
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => hgh x y)
    have hYZ : ∀ y, margYZ p y z = (∑ x, g x) * h y := by
      intro y
      unfold margYZ
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => hgh x y)
    show slice p z (x, y) * margZ p z = margXZ p x z * margYZ p y z
    rw [hgh x y, hZ, hXZ, hYZ]
    ring
  · -- **反方向**：取 `g x := margXZ x z / margZ z`、`h y := margYZ y z`，除以 `margZ`。
    intro h
    refine ⟨fun x => margXZ p x z / margZ p z, fun y => margYZ p y z, fun x y => ?_⟩
    show p ((x, y), z) = margXZ p x z / margZ p z * margYZ p y z
    rw [div_mul_eq_mul_div, eq_div_iff hz]
    exact h x y

/-- ⭐ **C2 的推论**：`margZ ≠ 0` 时，「`z` 处规则允许」⟺「`z` 处乘性等式成立」。 -/
theorem ruleAt_nonempty_iff_condMulEq_at_z
    (p : FinJoint α β γ) (z : γ) (hz : margZ p z ≠ 0) :
    (condMulRuleAt (α := α) (β := β) (γ := γ) z p).Nonempty ↔
      ∀ x y, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z := by
  unfold condMulRuleAt
  by_cases hr : IsRankOne (slice p z)
  · simp only [hr, if_true, Set.singleton_nonempty, true_iff]
    exact (rankOne_iff_condMul_at_z p z hz).mp hr
  · simp only [hr, if_false, Set.not_nonempty_empty, false_iff]
    exact fun h => hr ((rankOne_iff_condMul_at_z p z hz).mpr h)

/-! ## §3 ⭐⭐ C3 —— `Finset` 索引版：交叉允许集的非空性

`condMulRuleAt` 对**每个** `z` 各给一个约束集。
多个 `z` 同时作用时的允许集 = **取交**（`LawRule.compose` 的语义）。
模块只给出 `∀ z`（即全体）形式；下游常需**只对某个有限 `z` 集合**断言。

C3 给出：把允许集在 `S : Finset γ` 上求交，非空 ⟺ `S` 里每个切片秩一。

**前件自查**：前件是 `S`（一个有限索引集）+ `p`；
结论是**交叉允许集的非空性**由 `S` 上逐点的秩一性刻画。
「`S` 里的每个切片秩一」**不**等于「交叉允许集非空」——
二者由 `Set.mem_iInter₂` 与 `if` 展开连接（还要处理 `univ`/`∅` 两个分支）。 -/

/-- 在 `Fin γ` 集合 `S` 上把逐 `z` 规则**取交**后的允许集。 -/
def allowedOn (p : FinJoint α β γ) (S : Finset γ) :
    Set (MeasureTheory.Measure punitSpace.Carrier) :=
  ⋂ z ∈ S, (condMulRuleAt (α := α) (β := β) (γ := γ) z p)

/-- ⭐⭐ **C3**：`S` 上取交的允许集非空 ⟺ `S` 里每个切片秩一。 -/
theorem finset_rule_legality_iff (p : FinJoint α β γ) (S : Finset γ) :
    (allowedOn p S).Nonempty ↔ ∀ z ∈ S, IsRankOne (slice p z) := by
  classical
  unfold allowedOn
  constructor
  · rintro ⟨μ, hμ⟩ z hz
    by_contra hr
    have hmem : μ ∈ condMulRuleAt (α := α) (β := β) (γ := γ) z p :=
      Set.mem_iInter₂.mp hμ z hz
    simp [condMulRuleAt, hr] at hmem
  · intro h
    refine ⟨MeasureTheory.Measure.dirac PUnit.unit, ?_⟩
    refine Set.mem_iInter₂.mpr (fun z hz => ?_)
    simp [condMulRuleAt, h z hz]

/-- ⭐ **C3 与 C1 联用（`S = univ` 时回落到模块的结论）**。 -/
theorem finset_rule_legality_univ (p : FinJoint α β γ) :
    (allowedOn p Finset.univ).Nonempty ↔
      ∀ z, (condMulRuleAt (α := α) (β := β) (γ := γ) z p).Nonempty := by
  rw [finset_rule_legality_iff, condMulRuleAt_nonempty_iff]
  exact ⟨fun h z => h z (Finset.mem_univ z), fun h z _ => h z⟩

/-! ## §4 ⭐ C4 —— 与 `Fate.LawRule` 算子的**定义层对齐**（诚实标注：`rfl`）

模块头注的 TODO：

> 待 `Fate/LawRule.lean` 修复后，本文件的 `LawRule` 应替换为其别名。

`Fate/LawRule.lean` 现已编译通过。C4 证：替换**不需要改动任何证明**，
因为两者**逐字相同**（都是 `C.Carrier → X.Carrier → Set (Measure Y.Carrier)`，
`compose` 都是 `fun c x => R₁ c x ∩ R₂ c x`）。

**⚠ 这不是新数学**。它的唯一价值是把 `Fate.LawRule` 现成的算子代数
（`compose_comm`、`compose_top`、`point_compose`）**免费**用到本模块的规则上，
见 C4b。 -/

/-- ⭐ **C4**：本模块重述的 `LawRule`／`compose`／`IsPoint` 与 `Fate.LawRule` 的对应项
**逐字相同**，故通过 `rfl` 互相转换。 -/
theorem restated_ops_eq_lawRule_ops
    {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (R₁ R₂ : LawRule C X Y) :
    compose R₁ R₂ = FateV2.Rules.LawRule.compose R₁ R₂ := rfl

/-- ⭐ **C4b**：把 `Fate.LawRule.compose_comm` 直接用在本模块的 `compose` 上。 -/
theorem compose_comm_via_lawRule
    {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (R₁ R₂ : LawRule C X Y) : compose R₁ R₂ = compose R₂ R₁ :=
  FateV2.Rules.LawRule.compose_comm R₁ R₂

/-- ⭐ **C4c**：把 `Fate.LawRule.compose_top` 用在本模块的 `compose` 上。 -/
theorem compose_top_via_lawRule
    {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (R : LawRule C X Y) :
    compose R (top C X Y) = R :=
  FateV2.Rules.LawRule.compose_top R

end

end LawRuleCondMulConsumer

end FateV2.Predict