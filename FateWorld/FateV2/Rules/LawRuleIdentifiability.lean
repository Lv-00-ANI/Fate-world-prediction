/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.LawRuleIdentifiability
主题：**把「参数可辨识性」抽成一个抽象定理，两个领域实例归约到它**

---------------------------------------------------------------------------
本模块做什么
---------------------------------------------------------------------------
第 870 轮产出 `Fate/LawRuleTwoDomains.lean`（`linRule` / `markovRule`）与
`Fate/LawRuleInstances.lean`（`linRegRule`），各自**分别**证明了自己的
可辨识性（`linRule_identifiable` / `markovRule_identifiable`），
源码诚实边界如实登记：「没有真正的跨领域『同一个定理』」。

本模块把「可辨识性」抽成一个**抽象形式**，并证明：

§1 `identifiable_of_injective` —— 参数族 `F : P → LawRule C X Y` 单射 ⟹ 可辨识；
§2 `linRule_injective` / `markovRule_injective` —— 两个具体族都是单射
   （直接由各自已有的 `*_identifiable` 得出）；
§3 `identifiable_general` —— 统一的 `∀ {p q}, F p = F q → p = q` 形式；
§4 ⭐ `lawRule_family_ord_embedding` —— **序嵌入**版本（比 §1–§3 强）：
   若族对 `⊓` 保交（`hmono`）且单射，则 `F p ≤ F q ↔ p ≤ q`（格嵌入）；
§5 ⭐ **诚实反例**：`linRule` **不**满足 `hmono`（其值处处单点，两个不同
   斜率的 `⊓` 为空，而 `linRule (a ⊓ b)` 非空）。故 §4 的假设对现有两个
   实例**不成立** —— 这是本模块必须如实登记的关键边界。

---------------------------------------------------------------------------
诚实边界（必读）
---------------------------------------------------------------------------
- **§1–§3 的「统一」是形式上的**：`identifiable_of_injective` 的证明体是
  `hF h`，即「单射的定义直取」。它把两个可辨识性证明归约到
  `Function.Injective` 的**适用**，而非归约到更深的共同数学结构。
  **不**声称这构成实质性的跨领域统一。
- **真正的统一**需要一个**更深的代数结构**，例如「`LawRule` 的族是从参数空间
  到格的点嵌入」。本模块的 §4 给出该方向的一个**抽象**形式（保交 + 单射
  ⟹ 序嵌入），但 **§5 证明现有两实例都不满足其前件**（`hmono` 失败），
  故 §4 对现有实例是**空的** —— 它是未来实例的**接口**，不是当前成果。
- 未修改任何已有模块；仅 `import Fate.LawRuleTwoDomains` 与
  `Fate.LawRuleInstances`。
- 零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats` / `?_`。
-/

import FateWorld.FateV2.Rules.LawRuleInstances
import FateWorld.FateV2.Rules.LawRuleTwoDomains
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRuleIdentifiability

open FateV2.Rules.LawRule

/-!
  # Rules · LawRuleIdentifiability

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleIdentifiability.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRuleInstances, LawRuleTwoDomains
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  可辨识性的抽象形式
    =========================================================================== -/

/-- ⭐⭐⭐ **【可辨识性的抽象形式】**

若一个参数族 `F : P → LawRule C X Y` 是**单射**，则它的参数**可辨识**：
`F p = F q` 蕴含 `p = q`。

⚠ 诚实说明：证明体就是单射的定义（`hF h`）—— 本定理的**价值不在证明**，
而在**统一形状**：两个领域实例的可辨识性都是它的实例（见 §2–§3）。 -/
theorem identifiable_of_injective
    {P : Type*} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier]
    (F : P → LawRule C X Y) (hF : Function.Injective F)
    {p q : P} (h : F p = F q) : p = q :=
  hF h

/-! ===========================================================================
    §2  两个具体族都是单射（归约到 §1）
    =========================================================================== -/

/-- **实例 A 单射**：`linRule : ℝ → LawRule C₀ Xℝ Xℝ` 是单射。

归约：由 `LawRuleTwoDomains.linRule_identifiable`（其内容为 `δ` 单射性）经
`identifiable_of_injective` 的形状得到。 -/
theorem linRule_injective : Function.Injective LawRuleTwoDomains.linRule :=
  fun _a _b h => identifiable_of_injective LawRuleTwoDomains.linRule
    (fun _ _ hh => LawRuleTwoDomains.linRule_identifiable hh) h

/-- **实例 B 单射**：`markovRule : ENNReal → LawRule C₀ XF2 XF2` 是单射。

归约：由 `LawRuleTwoDomains.markovRule_identifiable`（其内容为
`markovRule_val_one` 的总质量计算）经同一形状得到。 -/
theorem markovRule_injective : Function.Injective LawRuleTwoDomains.markovRule :=
  fun _p _q h => identifiable_of_injective LawRuleTwoDomains.markovRule
    (fun _ _ hh => LawRuleTwoDomains.markovRule_identifiable hh) h

/-- **实例 A 的可辨识性（用 §1 的抽象形式重新表述）**。

与 `LawRuleTwoDomains.linRule_identifiable` **同一条结论**，但此处是
`identifiable_of_injective` 的**直接实例** —— 这就是「同一个定理」的证据。 -/
theorem linRule_identifiable_via_abstract {a b : ℝ}
    (h : LawRuleTwoDomains.linRule a = LawRuleTwoDomains.linRule b) : a = b :=
  identifiable_of_injective LawRuleTwoDomains.linRule linRule_injective h

/-- **实例 B 的可辨识性（同一抽象形式的实例）**。 -/
theorem markovRule_identifiable_via_abstract {p q : ENNReal}
    (h : LawRuleTwoDomains.markovRule p = LawRuleTwoDomains.markovRule q) : p = q :=
  identifiable_of_injective LawRuleTwoDomains.markovRule markovRule_injective h

/-! ===========================================================================
    §3  统一的可辨识性定理
    =========================================================================== -/

/-- ⭐⭐⭐ **【统一的可辨识性定理】**

对任意参数族 `F : P → LawRule C X Y`，若 `F` 单射，则所有 `F p = F q`
蕴含 `p = q`。这是 §1 的 `∀` 形式，便于作为**单一引理**被不同领域复用。 -/
theorem identifiable_general {P : Type*} {C : CtxSpace} {X : StateSpace}
    {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (F : P → LawRule C X Y) (hF : Function.Injective F) :
    ∀ {p q : P}, F p = F q → p = q :=
  fun h => identifiable_of_injective F hF h

/-! ===========================================================================
    §4  序嵌入版本（比 §1–§3 强，但对现有实例前件不成立）
    =========================================================================== -/

/-- ⭐ **【序嵌入形式】**：若 `F` **保交**（`hmono`）且**单射**，
则 `F` **反映序**：`F p ≤ F q ↔ p ≤ q`（即 `F` 是半格嵌入）。

证明：`→` 由 `F p ≤ F q` 得 `F p ⊓ F q = F p`，结合 `hmono` 得
`F (p ⊓ q) = F p`，由单射得 `p ⊓ q = p`，即 `p ≤ q`；
`←` 由 `p ≤ q` 得 `p ⊓ q = p`，故 `F p = F (p ⊓ q) = F p ⊓ F q ≤ F q`。

⚠ **前件 `hmono` 对现有的 `linRule` / `markovRule` 不成立**（见 §5），
故本定理目前是**空接口**，不是对现有实例的成果。 -/
theorem lawRule_family_ord_embedding {P : Type*} [SemilatticeInf P]
    {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (F : P → LawRule C X Y)
    (hmono : ∀ p q, F (p ⊓ q) = F p ⊓ F q)
    (hinj : Function.Injective F) :
    ∀ p q, F p ≤ F q ↔ p ≤ q := by
  intro p q
  constructor
  · intro hpq
    have h1 : F p ⊓ F q = F p := inf_eq_left.mpr hpq
    have h2 : F (p ⊓ q) = F p := by rw [hmono, h1]
    exact inf_eq_left.mp (hinj h2)
  · intro hpq
    have h : p ⊓ q = p := inf_eq_left.mpr hpq
    rw [← h, hmono]
    exact inf_le_right

/-- 从 §4 得到 `identifiable_of_injective` 的**格论版本**：
`F` 是格嵌入时，参数相等 ⟺ 规则相等（双向）。 -/
theorem identifiable_and_reflects {P : Type*} [SemilatticeInf P]
    {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (F : P → LawRule C X Y)
    (hmono : ∀ p q, F (p ⊓ q) = F p ⊓ F q)
    (hinj : Function.Injective F) (p q : P) :
    (F p = F q ↔ p = q) ∧ (F p ≤ F q ↔ p ≤ q) :=
  ⟨⟨fun h => hinj h, fun h => by rw [h]⟩, lawRule_family_ord_embedding F hmono hinj p q⟩

/-! ===========================================================================
    §5  ⭐ 诚实反例：`linRule` 不满足 §4 的保交前件
    =========================================================================== -/

/-- ⭐⭐⭐ **【诚实反例】**：`linRule` **不是**保交的。

对 `a ≠ b`，`linRule a ⊓ linRule b` 在每点为空（两个不同单点集的交），
而 `linRule (a ⊓ b)` 处处为单点集 —— 故二者不等。

**这条定理的意义**：§4 的序嵌入定理对现有的两个领域实例**不可用**。
把「抽象统一」误当成「已覆盖现有实例」是本项目最高频的错误之一，
本定理正是防它的护栏。 -/
theorem linRule_not_inf_hom (a b : ℝ) (h : a ≠ b) :
    LawRuleTwoDomains.linRule a ⊓ LawRuleTwoDomains.linRule b
      ≠ LawRuleTwoDomains.linRule (a ⊓ b) := by
  intro he
  have hne : ((LawRuleTwoDomains.linRule a ⊓ LawRuleTwoDomains.linRule b)
      PUnit.unit 1).Nonempty := by
    rw [he]; exact ⟨_, rfl⟩
  obtain ⟨μ, hμa, hμb⟩ := hne
  simp only [LawRuleTwoDomains.linRule, Set.mem_singleton_iff] at hμa hμb
  have heq : (MeasureTheory.Measure.dirac (a * 1) : MeasureTheory.Measure ℝ)
      = MeasureTheory.Measure.dirac (b * 1) := by rw [← hμa, ← hμb]
  apply h
  have hc := congrArg (fun ν : MeasureTheory.Measure ℝ => ν {a * 1}) heq
  rw [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton (a * 1))] at hc
  have hb : (b * 1) ∉ ({a * 1} : Set ℝ) := by
    simp only [Set.mem_singleton_iff]
    intro hh; exact h (by simpa using hh.symm)
  rw [MeasureTheory.Measure.dirac_apply, Set.indicator_of_notMem hb] at hc
  exact absurd hc one_ne_zero

/-- ⭐ **§4 的前件对 `linRule` 不可满足**（由 `linRule_not_inf_hom` 直接得出）：
不存在把 `linRule` 视为保交映射的方式 —— 除非参数相等。 -/
theorem linRule_inf_hom_forces_eq {a b : ℝ}
    (hmono : LawRuleTwoDomains.linRule (a ⊓ b)
      = LawRuleTwoDomains.linRule a ⊓ LawRuleTwoDomains.linRule b) : a = b := by
  by_contra hne
  exact linRule_not_inf_hom a b hne hmono.symm

end LawRuleIdentifiability

end FateV2.Rules