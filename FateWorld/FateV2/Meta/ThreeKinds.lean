import FateWorld.FateV2.Core.Judgment

/-!
  # Meta · ThreeKinds — 三类陈述判据

  ## 迁移登记
  - 来源：新写（原为骨架占位）
  - 动作：C 重写
  - 对应环节：元层 · 三类陈述判据
  - 依赖裁决：**D-001**（验收判据变更权）、**D-016**（纯 CIC + 三条公理降为假设）、
              **D-022**（反空泛证明）
  - 改动：从空壳补成实现。原 `Status` 已有四档（`proven`/`conditional`/`empirical`/`refuted`），
          本模块在其上建立**三类陈述的判据**，并证明二者一致。
  - 状态：已编译

  ## 三类 vs 四档

  `Status` 是**陈述自己的状态**。本模块给的是**「怎么判一条陈述属于哪一类」的判据**：

  | 类 | 判据 |
  |---|---|
  | **可证** | `support = ∅` 且 `status = proven` |
  | **条件** | `support ≠ ∅` 且 `status ∈ {proven, conditional}` |
  | **经验** | `status = empirical` |

  **关键**：`support = ∅` 与 `status = proven` **不能互相推出**，
  这正是本模块要钉住的第一件事（见 `not_support_empty_implies_proven`）。
  对应冲突 C-005「不需要公理」与「已证」被混为一谈。

  ## 诚实边界
  只给**判据与一致性定理**，不给「如何判定任意现实陈述属于哪类」的算法——
  那需要入域判据（`Meta/Domain`），属另一条线。
-/

namespace FateV2.Meta

open FateV2.Core

universe u

/-! ## 三类陈述 -/

/-- **三类陈述**（元层判据的分类标签）。 -/
inductive Kind : Type where
  /-- 可证：无未证前件且已证。 -/
  | provable
  /-- 条件：承了未证前件，但推导链完整。 -/
  | conditional
  /-- 经验：无法证明，只能作为假设登记。 -/
  | empirical
  deriving DecidableEq, Repr

namespace Kind

/-- 三类陈述对应的 `Status`（`refuted` 不在三类之内——被反驳的陈述不再有类）。 -/
def toStatus : Kind → Status
  | .provable    => .proven
  | .conditional => .conditional
  | .empirical   => .empirical

/-- 分类的强度序：可证 > 条件 > 经验。 -/
def rank : Kind → Nat
  | .provable    => 2
  | .conditional => 1
  | .empirical   => 0

/-- `toStatus` 保序。 -/
theorem toStatus_rank_mono {a b : Kind} (h : a.rank ≤ b.rank) :
    (a.toStatus).strength ≤ (b.toStatus).strength := by
  cases a <;> cases b <;> simp_all [rank, toStatus, Status.strength]

end Kind

/-! ## 判据 -/

section Criteria

variable {L : Type u}

/-- **「可证」的判据**：来源为空**且**状态为 `proven`。 -/
def IsProvable (j : Judgment L) : Prop :=
  j.support.assumptions = [] ∧ j.status = .proven

/-- **「条件」的判据**：来源非空，且状态为 `proven` 或 `conditional`。 -/
def IsConditional (j : Judgment L) : Prop :=
  j.support.assumptions ≠ [] ∧ (j.status = .proven ∨ j.status = .conditional)

/-- **「经验」的判据**：状态为 `empirical`。 -/
def IsEmpirical (j : Judgment L) : Prop :=
  j.status = .empirical

/-- 三类**两两互斥**。 -/
theorem kinds_exclusive (j : Judgment L) :
    ¬ (IsProvable j ∧ IsConditional j) ∧
    ¬ (IsProvable j ∧ IsEmpirical j) ∧
    ¬ (IsConditional j ∧ IsEmpirical j) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨he, _⟩, ⟨hn, _⟩⟩; exact hn he
  · rintro ⟨⟨_, hp⟩, he⟩
    simp only [IsEmpirical] at he
    rw [hp] at he
    exact Status.noConfusion he
  · rintro ⟨⟨_, hst⟩, he⟩
    simp only [IsEmpirical] at he
    rcases hst with h | h <;> rw [h] at he <;> exact Status.noConfusion he

end Criteria

/-! ## 一致性：`support` 与 `status` 不能互相推出 -/

section Consistency

variable {L : Type u}

/-- **`support = ∅` 推不出 `status = proven`**。

    反例构造：结论取 `Formula.top`，来源为空，状态标为 `empirical`。
    这类判断在项目中真实存在——「某数据集满足某性质」被直接作经验事实登记，
    它没有未证前件，但状态仍是 `empirical`。

    这就是必须单独钉住的点：**「不需要公理」≠「已证」**（冲突 C-005）。 -/
theorem not_support_empty_implies_proven :
    ∃ (j : Judgment (Fin 1)), j.support.assumptions = [] ∧ j.status ≠ .proven :=
  ⟨⟨Formula.top, Formula.top, Support.empty, .empirical⟩, rfl, by decide⟩

/-- **`status = proven` 也推不出 `support = ∅`**——除非额外要求（即 `IsProvable`）。 -/
theorem proven_allows_support :
    ∃ (j : Judgment (Fin 1)), j.status = .proven ∧ j.support.assumptions ≠ [] :=
  ⟨⟨Formula.top, Formula.top, ⟨["A1"]⟩, .proven⟩, rfl, by decide⟩

end Consistency

/-! ## 与 `Judgment.compose` 的传播：三类在 `∘` 下如何退化 -/

section Propagation

variable {L : Type u}

/-- **可证 ∘ 可证 = 可证**：两个无未证前件的已证判断组合后仍是可证。
    这是「干净与干净组合不产生脏」的形式化。 -/
theorem provable_compose_provable (j₁ j₂ : Judgment L)
    (h₁ : IsProvable j₁) (h₂ : IsProvable j₂) :
    IsProvable (j₁.compose j₂) := by
  obtain ⟨he₁, hs₁⟩ := h₁
  obtain ⟨he₂, hs₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · simp [Judgment.compose, Support.union, he₁, he₂]
  · simp [Judgment.compose, Status.weaker, hs₁, hs₂]

/-- **可证 ∘ 条件：整体不可能回到「可证」**。

    这是「脏会传播」的核心：**组合不会让来源凭空变干净**。

    ⚠ 注意陈述的精确形式：结论是「**不是可证**」（来源非空），
    而不是「一定是条件」——因为若 `j₂` 状态更弱（如 `refuted`），
    组合结果的状态也会跟着变弱，它既不「可证」也不「条件」。
    这正是「脏会传播」的准确含义：**它污染的是来源，不是状态**。 -/
theorem compose_of_conditional_not_provable (j₁ j₂ : Judgment L)
    (h₂ : IsConditional j₂) : ¬ IsProvable (j₁.compose j₂) := by
  obtain ⟨hne, _⟩ := h₂
  rintro ⟨hempty, _⟩
  simp only [Judgment.compose, Support.union, List.append_eq_nil_iff] at hempty
  exact hne hempty.2

/-- **条件 ∘ 可证：来源仍不空**：任一侧带未证前件，组合后来源就不空。 -/
theorem compose_of_not_provable_support (j₁ j₂ : Judgment L)
    (h : j₁.support.assumptions ≠ [] ∨ j₂.support.assumptions ≠ []) :
    (j₁.compose j₂).support.assumptions ≠ [] := by
  intro hempty
  have hpair : j₁.support.assumptions ++ j₂.support.assumptions = [] := by
    simpa [Judgment.compose, Support.union] using hempty
  have := List.append_eq_nil_iff.mp hpair
  rcases h with h | h
  · exact h this.1
  · exact h this.2

end Propagation

/-! ## 自洽性 -/

/-- `Kind` 到 `Status` 的映射是**单射**（三类不同标签不会撞到同一状态）。 -/
theorem kind_toStatus_injective : Function.Injective Kind.toStatus := by
  intro a b h
  cases a <;> cases b <;> simp_all [Kind.toStatus]

/-- 「经验」判据与 `Kind.empirical` 的映射一致。 -/
theorem isEmpirical_iff_kind (j : Judgment L) :
    IsEmpirical j ↔ j.status = Kind.toStatus .empirical := by
  simp [IsEmpirical, Kind.toStatus]

end FateV2.Meta
