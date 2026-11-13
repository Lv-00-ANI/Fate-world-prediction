import FateWorld.FateV2.Classical.Shell
import FateWorld.FateV2.Meta.ThreeKinds
import Mathlib.Tactic

/-!
  # Meta · Ledger — 假设账本

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：元层 · 假设账本
  - 依赖裁决：**D-001**（判据变更权归作者）、**D-016**（三条公理入账本）、
              **D-022**（反空泛证明）
  - 改动：从空壳补成实现。把散在 `Assumptions.lean`（三条公理）、
          理论假设（A1–A34）、建模假设这三类**统一成一本账**。
  - 状态：已编译

  ## 账本要解决什么问题

  `09-总设计` §11 说账本包含：

  > 三条基础公理 + A1–A34 + 建模假设 + 构造忠实性

  **但它们原本是散的**：三条公理在 `Classical/Assumptions`，
  A1–A34 只在文档里，建模假设在 `Modeling/`。
  于是「这条定理到底承了什么」这个问题，**没有一个地方能完整回答**。

  本模块把「来源」统一为一个可查询的账本，并钉住三条关键性质。

  ## 三条关键性质

  1. **账本只增不减**（`Ledger.subset_insert`）——与 `D-004` 铁律一致
  2. **三条公理是账本条目，不是底座**（`axioms_are_entries`）——D-016 的直接形式化
  3. **账本条目可以分类**（`Entry.kind`）——为门禁 G5 提供判据
-/

namespace FateV2.Meta

open FateV2.Core
open FateV2.Classical

/-! ## §1 · 账本条目的分类 -/

/-- **账本条目的四类来源**。 -/
inductive EntryKind : Type where
  /-- 三条基础公理（`propext` / `Classical.choice` / `Quot.sound`） -/
  | baseAxiom
  /-- 理论假设（A1–A34） -/
  | theoryAssumption
  /-- 建模假设（`σ_emp ≈ σ_model` 之类） -/
  | modelingAssumption
  /-- 构造忠实性（实现与语义的对应） -/
  | faithfulness
  deriving DecidableEq, Repr

/-- **账本条目**：一个假设标识 + 它的类别 + 一句话说明。 -/
structure Entry where
  /-- 与外层 `Support.assumptions` 里出现的字符串一致 -/
  id   : AssumptionId
  /-- 类别 -/
  kind : EntryKind
  /-- 说明（不参与证明，只为可读） -/
  note : String
  deriving Repr

/-! ## §2 · 账本 -/

/-- **假设账本**：一束条目。

    ⚠ 用 `List` 而非 `Set`：账本要能「查某一条的说明」，
    且条目本身的顺序记录登记次序（审计时有用）。 -/
structure Ledger where
  entries : List Entry

namespace Ledger

/-- 空账本。 -/
def empty : Ledger := ⟨[]⟩

/-- 登记一条。 -/
def insert (e : Entry) (L : Ledger) : Ledger := ⟨e :: L.entries⟩

/-- 账本里有哪些**假设标识**（与 `Support.assumptions` 同域）。 -/
def ids (L : Ledger) : List AssumptionId := L.entries.map (·.id)

/-- **查一条**：给定标识，找出它的条目。 -/
def lookup (L : Ledger) (a : AssumptionId) : Option Entry :=
  L.entries.find? (fun e => e.id = a)

/-- **账本包含某来源**：`Support` 里每个假设都在账本中。

    这是「这条定理承的前件**都登记过**」的判据，
    与 `Shell.covers`（前件**被允许**）是两个不同的检查，互补使用。 -/
def covers (L : Ledger) (sup : Support) : Prop :=
  ∀ a ∈ sup.assumptions, a ∈ L.ids

/-! ### 单调性 -/

/-- **登记只会增加账本**：原账本的标识仍都在。 -/
theorem subset_insert (e : Entry) (L : Ledger) :
    ∀ a ∈ L.ids, a ∈ (insert e L).ids := by
  intro a ha
  simp only [insert, ids, List.map_cons]
  exact List.mem_cons_of_mem _ ha

/-- **新条目本身也在**。 -/
theorem id_mem_insert (e : Entry) (L : Ledger) : e.id ∈ (insert e L).ids := by
  simp only [insert, ids, List.map_cons]
  exact List.mem_cons_self

/-- **覆盖单调**：登记更多条目，能覆盖的来源不会减少。 -/
theorem covers_insert (e : Entry) (L : Ledger) (sup : Support)
    (h : L.covers sup) : (insert e L).covers sup :=
  fun a ha => subset_insert e L a (h a ha)

/-- **空来源被任何账本覆盖**。 -/
theorem covers_empty (L : Ledger) : L.covers Support.empty := by
  intro a ha
  exact absurd ha (by simp [Support.empty])

end Ledger

/-! ## §3 · 三条公理是账本条目（D-016 的直接形式化） -/

section AxiomsInLedger

/-- **三条基础公理作为账本条目**。 -/
def baseAxiomEntries : List Entry :=
  [ ⟨axPropext,    .baseAxiom, "命题外延性：等价命题相等"⟩
  , ⟨axChoice,     .baseAxiom, "选择公理：非空族有选择函数"⟩
  , ⟨axQuotSound,  .baseAxiom, "商的可靠性：相关元素在商中相等"⟩ ]

/-- **只含三条基础公理的账本**。 -/
def baseLedger : Ledger := ⟨baseAxiomEntries⟩

/-- **三条公理确实在账本里**——它们不是「底座的一部分」，而是**条目**。

    这是 `D-016` 的核心断言在实现层的落点：
    「底座纯 CIC，三条公理降为基础假设」⟺「三条公理是账本条目」。 -/
theorem axioms_are_entries :
    axPropext ∈ baseLedger.ids ∧
    axChoice ∈ baseLedger.ids ∧
    axQuotSound ∈ baseLedger.ids := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [baseLedger, baseAxiomEntries, Ledger.ids]

/-- **`baseLedger` 覆盖经典外壳的假设表**。 -/
theorem baseLedger_covers_classical :
    baseLedger.covers ⟨FateV2.Classical.classical.assumptions⟩ := by
  intro a ha
  simp [baseLedger, baseAxiomEntries, Ledger.ids, FateV2.Classical.classical] at ha ⊢
  exact ha

/-- **`baseLedger` 不覆盖任意来源**：三条公理之外的东西它管不了。

    反例：一条用 A1 的定理，`baseLedger` 覆盖不了。 -/
theorem baseLedger_not_covers_A1 :
    ¬ baseLedger.covers ⟨["A1"]⟩ := by
  intro h
  have hmem := h "A1" (by simp)
  simp [baseLedger, baseAxiomEntries, Ledger.ids, axPropext, axChoice, axQuotSound] at hmem

end AxiomsInLedger

/-! ## §4 · 账本与三类陈述的接线 -/

section WithKinds

/-- **可证定理的账本判据**：三类中的「可证」对应 `support = ∅`，
    因此它被**任何**账本覆盖（因为空来源没有要查的条目）。

    这解释了「构造性定理不需要登记公理」——不是豁免，而是**它没有前件可登记**。 -/
theorem provable_covers_any_ledger {L : Type u} {j : Judgment L}
    (hj : IsProvable j) (lg : Ledger) : lg.covers j.support := by
  obtain ⟨he, _⟩ := hj
  intro a ha
  rw [he] at ha
  exact absurd ha (by simp)

end WithKinds

/-! ## §5 · 账本的完整性判据 -/

section Completeness

/-- **账本完整**：每条登记在账本里的条目，都能查到。

    这是账本自身的一致性检查——防止「有 id 没说明」的哑目。 -/
def WellFormed (L : Ledger) : Prop :=
  ∀ e ∈ L.entries, L.lookup e.id = some e

/-- **空账本良构**。 -/
theorem empty_wellFormed : WellFormed (Ledger.empty) := by
  intro e he
  simp [Ledger.empty] at he

end Completeness

end FateV2.Meta
