/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.LawRuleSatisfiability
阶段：**组合的完备性 —— 一族规则的交何时非空**（`LawRule` 载体版）

---------------------------------------------------------------------------
问题
---------------------------------------------------------------------------
`LawRule.LawRule := C → X → Set (Measure Y)`，`∘ := 逐点取交`。
给定 `S : Set (LawRule C X Y)`，问

> **`⋂S`（逐点交）何时非空？** 即：是否存在分布 `μ` 被 `S` 的每条规则允许？

必须区分**两个「交」**：

* **(L)** 格论交：`(sInf S) c x = ⋂ {R c x | R ∈ S}`，**永远存在**
  （`sInf_apply`）；非空性才是问题；
* **(P)** 逐点非空：`∀ c x, (⋂ {R c x | R ∈ S}).Nonempty`（`Compatible`）
  —— 这才是「规则组合相容 / 可满足」。

---------------------------------------------------------------------------
⭐ 判据（本文件实际形式化的全部内容，零 `sorry`）
---------------------------------------------------------------------------
| # | 内容 | 形式名 | 前件 |
|---|---|---|---|
| J1 | 逐点展开 + 成员判据 | `sInf_apply`, `mem_sInf_iff` | — |
| J1' | 二元交：与 `compose` 一致 / 非空判据 | `compose_apply`, `compose_nonempty_iff` | — |
| J2 | ⭐⭐ **基础判据**：相容 $\iff\forall c\,x\,\exists m\,\forall R\in S,\ m\in R(c,x)$ | `compatible_iff` | — |
| J3 | ⭐⭐⭐ **紧致性判据**：相容 $\iff$ 每个**有限**子族相容 | `compatible_iff_finsetwise` | `Tight` |
| J5 | 相容 $\Rightarrow$ 有限相容 $\Rightarrow$ 二元相容（无前件） | `Compatible.finsetwise`, `Compatible.pairwise` | — |
| J6 | 共同允许分布 $\Rightarrow$ 该点 `sInf` 非空 | `sInf_nonempty_of` | — |
| J7 | 单调性：子族相容 $\Leftarrow$ 整族相容 | `compatible_subset` | — |
| J8 | 极值：`{⊤}` 恒相容；`{⊥}` 相容 $\iff$ `C` 或 `X` 为空 | `compatible_singleton_top`, `not_compatible_singleton_bot` | （后者需 `[Nonempty C.Carrier] [Nonempty X.Carrier]`） |

**共 13 条定理 / 引理**：`sInf_apply`、`mem_sInf_iff`、`compose_apply`、
`compose_nonempty_iff`、`compatible_iff`、`Compatible.finsetwise`、
`Compatible.pairwise`、`sInf_nonempty_of`、`compatible_subset`、
`compatible_singleton_top`、`not_compatible_singleton_bot`、
`compatible_iff_finsetwise`（+ 定义 `Compatible`、`FinsetwiseCompatible`、
`PairwiseCompatible`、`Tight`）。

---------------------------------------------------------------------------
⚠⚠ 本次修复（P-006）的实质改动 —— 必须读
---------------------------------------------------------------------------
本模块在 P-006 分诊中被判 **FIX**（11 error / 13 定理，drift=3，`local` 4）。
修复过程中查明并处理了**两条陈述层面**的问题，不是单纯的证明修补：

1. **`not_compatible_singleton_bot` 的原陈述为假。**
   原文：`¬ Compatible ({⊥} : Set (LawRule C X Y))`，**无任何前件**。
   但 `Compatible S := ∀ c x, _`，故当 `C.Carrier` 或 `X.Carrier` **为空**时
   该全称命题**真值为真**，于是其否定为假。
   **修法**：补上前件 `[Nonempty C.Carrier] [Nonempty X.Carrier]`（这是
   陈述真值所必需的前件，不是把结论塞进前件）。前件不含任何关于
   `Compatible` 的假设。
   > 另注：原证明用 `default`，隐含要求 `Inhabited`；本实现改用
   > `Classical.arbitrary`，与 `Nonempty` 前件对应。

2. **`tight_of_finite`（原 §4「有限载体」小节）已删除 —— 该陈述可被推翻。**
   原文声称：`[Finite Y.Carrier] → Tight`，即「`Y` 的载体有限 ⟹
   任意非空集族满足有限交性质则整族交非空」（并据此宣称 J3 在有限载体上
   自动成立、判据可判定）。
   **反例**：取 `Y.Carrier := Unit`（有限）。对 `t : ℝ≥0∞` 令
   `B_t := {μ : Measure Unit | t ≤ μ Set.univ}`。
   每个 `B_t` 非空（`μ := t • dirac ()` 给出 `μ univ = t`）；
   任取有限子族 `{B_{t_i}}`，其交含 `B_{max t_i}`，故有限交性质成立；
   但整族交 `⋂_{t} B_t` 为空（无测度其总质量 `≥` 一切 `t`，`∞` 之外无解
   —— 而 `t` 取遍 `ℝ≥0∞` 时 `t ≤ μ univ` 要求 `μ univ = ⊤`，此时 `t = ⊤`
   仍可行……故更精确地取 `t` 遍历 `ℝ≥0∞` 且族取 `{μ | t < μ univ}` 的闭化形式，
   即见反例族须用**严格**不等式 `μ univ > t`：此时 `B_t` 仍非空、有限交非空，
   而整族交空）。
   **结论**：`Tight` 是关于 `Measure Y` 的**真实紧致性假设**（`Measure` 在
   弱拓扑下**不**紧），不能由 `[Finite Y.Carrier]` 免费得到。
   故 `tight_of_finite` 及其宣称的下游（「有限载体上判据可判定」、
   文件头旧表中的 J9 / J10）**一律删除**：这两个小节在**旧正文中从未存在**
   （旧表把它们列为「已证」，实为**表头虚报**），而 `tight_of_finite` 本身
   为假陈述，不予保留。

其余 12 条定理的**陈述未改**，只修证明（`sInf_apply` 的 API 名、
`FinsetwiseCompatible` 的类型标注、`Tight` 的多余参数 `C`/`X` ——
`Tight` 的陈述只涉及 `Y`，旧代码却用 `Tight (C := C) (X := X)`，
属旧 API 漂移）。

---------------------------------------------------------------------------
诚实边界（**必读**）
---------------------------------------------------------------------------
1. **`LawRule` 上的 Sat 不是 NP-完全问题。** J2 表明它逐点分解；
   J3 表明在 `Tight` 载体上它由**有限**片段决定。
   NP / coNP 只出现在**更强**的语言（否定约束、布尔属性蕴含、
   基数约束的最小模型）上；本文件不声称任何 NP-完全性。
2. **`Tight` 是实质性假设**：`Measure Y` 上「任意非空集族 + 有限交性质
   ⟹ 整族交非空」是紧致性型断言，`Measure Y` 在弱拓扑下**不紧**
   （见上文反例说明），本文件**只把它作为显式假设 `hT` 传递**，
   **不构造**任何 `Tight` 的实例，也不声称它在何处成立。
   **没有它 J3 失效。**
3. **二元判据（每一对规则相容 ⟹ 整族相容）在本文件不成立地陈述**：
   有限交性质**不**由二元相容性推出（这是 Buneman / 单纯复形的经典现象，
   「出处待核实」到具体定理编号）；故本文件只证 J5 的反方向
   （`Compatible.pairwise`），**不**证其逆。
4. **可判定性（旧表 J9 / J10）不在本文件中**，且不随本文件成立 ——
   见上文第 2 条：没有 `Tight` 的实例，就没有「有限化」判据。
5. `Compatible` 是**逐点非空**，**不是** `sInf S ≠ ⊥`（后者在 `C` 或 `X`
   为空时同样落空，这正是第 1 条假陈述的根源）。
6. 不使用 `sorry` / `axiom` / `admit`。
-/

import Mathlib
import FateWorld.FateV2.Rules.LawRuleLattice
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-!
  # Rules · LawRuleSatisfiability

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleSatisfiability.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRuleLattice
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  逐点展开（两个「交」的分离）
    =========================================================================== -/

/-- **格论交的逐点展开**。

⚠ 注意：`LawRule` 是 `def`（非 `abbrev`），故 `Set (LawRule C X Y)` 与
`Set (C → X → Set (Measure Y))` 只在 semireducible 透明层定义相等；
下列 `key` 先把 `sInf` 的载体显式写成展开形式，再用 Mathlib 的
`sInf_apply` / `iInf_apply`。 -/
theorem sInf_apply (S : Set (LawRule C X Y)) (c : C.Carrier) (x : X.Carrier) :
    (sInf S : LawRule C X Y) c x = ⋂ R ∈ S, R c x := by
  have key : ∀ (T : Set (C.Carrier → X.Carrier → Set (Measure Y.Carrier)))
      (c : C.Carrier) (x : X.Carrier), (sInf T) c x = ⋂ R ∈ T, R c x := by
    intro T c x
    rw [_root_.sInf_apply, iInf_apply]
    ext m
    simp
  exact key S c x

/-- **成员判据**：`m` 被 `S` 中每条规则允许。 -/
theorem mem_sInf_iff {S : Set (LawRule C X Y)} {c : C.Carrier} {x : X.Carrier}
    {m : Measure Y.Carrier} :
    m ∈ (sInf S : LawRule C X Y) c x ↔ ∀ R ∈ S, m ∈ R c x := by
  rw [sInf_apply, Set.mem_iInter₂]

/-- 二元情形与 `compose` 一致。 -/
theorem compose_apply (R₁ R₂ : LawRule C X Y) (c : C.Carrier) (x : X.Carrier) :
    (compose R₁ R₂) c x = R₁ c x ∩ R₂ c x := rfl

/-- 二元交非空 ⟺ 存在共同允许分布。 -/
theorem compose_nonempty_iff (R₁ R₂ : LawRule C X Y) (c : C.Carrier) (x : X.Carrier) :
    ((compose R₁ R₂) c x).Nonempty ↔ ∃ m, m ∈ R₁ c x ∧ m ∈ R₂ c x := by
  simp only [compose, Set.Nonempty, Set.mem_inter_iff]

/-! ===========================================================================
    §2  相容性（= 可满足性）与基础判据
    =========================================================================== -/

/-- **`S` 相容 / 可满足**：每个 `(c,x)` 处存在被 `S` 中**全部**规则允许的分布。
⚠ 逐点非空性，不是 `sInf S ≠ ⊥`。 -/
def Compatible (S : Set (LawRule C X Y)) : Prop :=
  ∀ c x, ((sInf S : LawRule C X Y) c x).Nonempty

/-- ⭐⭐ **基础判据（J2）**。 -/
theorem compatible_iff (S : Set (LawRule C X Y)) :
    Compatible S ↔ ∀ c x, ∃ m, ∀ R ∈ S, m ∈ R c x := by
  simp only [Compatible, Set.Nonempty, mem_sInf_iff]

/-- **有限子族相容**。 -/
def FinsetwiseCompatible (S : Set (LawRule C X Y)) : Prop :=
  ∀ T : Finset (LawRule C X Y),
    (↑T : Set (LawRule C X Y)) ⊆ S → Compatible (↑T : Set (LawRule C X Y))

/-- **二元相容**。 -/
def PairwiseCompatible (S : Set (LawRule C X Y)) : Prop :=
  ∀ R₁ ∈ S, ∀ R₂ ∈ S, ∀ c x, ((compose R₁ R₂) c x).Nonempty

/-- **相容 ⟹ 有限子族相容**。 -/
theorem Compatible.finsetwise {S : Set (LawRule C X Y)} (h : Compatible S) :
    FinsetwiseCompatible S := by
  intro T hT c x
  obtain ⟨m, hm⟩ := (compatible_iff S).mp h c x
  exact ⟨m, mem_sInf_iff.mpr (fun R hR => hm R (hT hR))⟩

/-- **相容 ⟹ 二元相容**。 -/
theorem Compatible.pairwise {S : Set (LawRule C X Y)} (h : Compatible S) :
    PairwiseCompatible S := by
  intro R₁ h₁ R₂ h₂ c x
  obtain ⟨m, hm⟩ := (compatible_iff S).mp h c x
  exact (compose_nonempty_iff R₁ R₂ c x).mpr ⟨m, hm R₁ h₁, hm R₂ h₂⟩

/-- **有共同允许分布 ⟹ `sInf` 在该点非空**。 -/
theorem sInf_nonempty_of {S : Set (LawRule C X Y)} {c : C.Carrier} {x : X.Carrier}
    {m : Measure Y.Carrier} (h : ∀ R ∈ S, m ∈ R c x) :
    ((sInf S : LawRule C X Y) c x).Nonempty :=
  ⟨m, mem_sInf_iff.mpr h⟩

/-- **子族相容 ⟸ 整族相容**（J7）。 -/
theorem compatible_subset {S T : Set (LawRule C X Y)} (hST : S ⊆ T)
    (h : Compatible T) : Compatible S :=
  (compatible_iff S).mpr (fun c x => by
    obtain ⟨m, hm⟩ := (compatible_iff T).mp h c x
    exact ⟨m, fun R hR => hm R (hST hR)⟩)

/-- **`{⊤}` 恒相容**（取零测度作见证，不需任何有元假设）。 -/
theorem compatible_singleton_top :
    Compatible ({⊤} : Set (LawRule C X Y)) := by
  intro c x
  refine ⟨0, ?_⟩
  rw [mem_sInf_iff]
  intro R hR
  rw [Set.mem_singleton_iff] at hR
  subst hR
  exact Set.mem_univ _

/-- **`{⊥}` 不相容**（J8 的另一半）。

⚠ **必须带 `Nonempty` 前件**：`Compatible` 是全称命题 `∀ c x, …`，
故 `C.Carrier` 或 `X.Carrier` 为空时 `Compatible {⊥}` **为真**
（空域上的全称命题），此时其否定为假。
这两个前件只保证「存在一个待检查的 `(c,x)`」，**不涉及** `Compatible` 本身。 -/
theorem not_compatible_singleton_bot [Nonempty C.Carrier] [Nonempty X.Carrier] :
    ¬ Compatible ({⊥} : Set (LawRule C X Y)) := by
  intro h
  obtain ⟨m, hm⟩ := h (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier)
  rw [mem_sInf_iff] at hm
  have hmem : m ∈ (⊥ : LawRule C X Y) (Classical.arbitrary C.Carrier)
      (Classical.arbitrary X.Carrier) :=
    hm ⊥ (Set.mem_singleton ⊥)
  have hb : (⊥ : LawRule C X Y) = bot C X Y := bot_eq_bot
  rw [hb] at hmem
  exact hmem

/-! ===========================================================================
    §3  紧致性判据
    =========================================================================== -/

/-- **载体紧致性假设（有限交性质 ⟹ 交非空）**，显式假设。

⚠ 这是**真假设**，本文件不构造其任何实例：
`Measure Y` 在弱拓扑下**不紧**，故 `Tight` 并非总能满足
（旧版曾声称 `[Finite Y.Carrier] → Tight`，该陈述为假，已删除，
见文件头「本次修复」第 2 条）。

`Tight` 的陈述只涉及 `Y`（`C`、`X` 不出现）。 -/
def Tight : Prop :=
  ∀ (A : Set (Set (Measure Y.Carrier))),
    (∀ B ∈ A, B.Nonempty) →
    (∀ A' ⊆ A, A'.Finite → (⋂₀ A').Nonempty) →
    (⋂₀ A).Nonempty

/-- ⭐⭐⭐ **紧致性判据（J3）**：在 `Tight` 载体上，
相容 $\iff$ 每个**有限**子族的交非空。

即：**整族的交非空 $\iff$ 无有限子族能造成局部矛盾**。 -/
theorem compatible_iff_finsetwise (hT : Tight (Y := Y))
    (S : Set (LawRule C X Y)) :
    Compatible S ↔ FinsetwiseCompatible S := by
  refine ⟨Compatible.finsetwise, ?_⟩
  intro h c x
  -- 每一步非空：`{R c x}` 的单点族相容
  have hne : ∀ B ∈ {B | ∃ R ∈ S, B = R c x}, B.Nonempty := by
    rintro B ⟨R, hR, rfl⟩
    obtain ⟨m, hm⟩ := h {R} (by
      intro R' hR'
      rw [Finset.mem_coe, Finset.mem_singleton] at hR'
      rw [hR']; exact hR) c x
    exact ⟨m, mem_sInf_iff.mp hm R (Finset.mem_singleton_self R)⟩
  -- 有限交性质：有限子族的见证规则构成有限子族，用 `FinsetwiseCompatible`
  have hfip : ∀ A' ⊆ {B | ∃ R ∈ S, B = R c x}, A'.Finite → (⋂₀ A').Nonempty := by
    intro A' hA' hA'fin
    classical
    have hwit : ∀ B ∈ A', ∃ R ∈ S, B = R c x := fun B hB => hA' hB
    set f : ↥A' → LawRule C X Y := fun B => Classical.choose (hwit B B.2) with hf
    have hfS : ∀ B : ↥A', f B ∈ S := fun B => (Classical.choose_spec (hwit B B.2)).1
    have hfE : ∀ B : ↥A', f B c x = (B : Set (Measure Y.Carrier)) :=
      fun B => ((Classical.choose_spec (hwit B B.2)).2).symm
    have hrange : ∃ T : Finset (LawRule C X Y),
        (↑T : Set (LawRule C X Y)) = Set.range f := by
      classical
      haveI : Fintype ↥A' := hA'fin.fintype
      exact ⟨((Set.toFinite (Set.univ : Set ↥A')).image f).toFinset, by
        rw [Set.Finite.coe_toFinset, Set.image_univ]⟩
    obtain ⟨T, hTfs⟩ := hrange
    have hsub : (↑T : Set (LawRule C X Y)) ⊆ S := by
      rw [hTfs]
      rintro _ ⟨B, rfl⟩
      exact hfS B
    obtain ⟨m, hm⟩ := h T hsub c x
    refine ⟨m, Set.mem_sInter.mpr (fun B hB => ?_)⟩
    have hmemT : f ⟨B, hB⟩ ∈ T := by
      apply Finset.mem_coe.mp
      rw [hTfs]
      exact Set.mem_range_self _
    have hkey := mem_sInf_iff.mp hm (f ⟨B, hB⟩) hmemT
    rwa [hfE ⟨B, hB⟩] at hkey
  obtain ⟨m, hm⟩ := hT _ hne hfip
  refine ⟨m, mem_sInf_iff.mpr (fun R hR => ?_)⟩
  exact Set.mem_sInter.mp hm (R c x) ⟨R, hR, rfl⟩

end LawRule

end FateV2.Rules