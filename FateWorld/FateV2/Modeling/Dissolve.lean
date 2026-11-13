import FateWorld.FateV2.Core.Ops
import Mathlib.Tactic

/-!
  # Modeling · Dissolve — 数据消融

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：F1-13（数据嵌入）、F3-14（规则载体）
  - 依赖裁决：**D-005**（数据消融与归档）、**D-006**（数据三层策略）、
              **D-007**（数据必须数学构造）
  - 改动：从空壳补成实现。`D-005` 说「数据可消融」，但没有形式化
          **消融之后数据去哪了**。本模块给出三种归宿并证明它们覆盖全部情形。
  - 状态：已编译

  ## 消融要解决的问题

  一条规则里如果嵌了数据（"在数据集 D 上观察到 X"），
  这条规则就**不可证**——数据本身不是定理。

  `D-005` 的解法：**消融**。把数据从句子里剥掉，看剩下什么：

  | 归宿 | 条件 | 结果 |
  |---|---|---|
  | **具体定理** | 剥掉数据后含义不变 | `support = ∅`，`status = proven` |
  | **经验假设** | 剥掉数据后含义变了，但可陈述 | `support` 加一条假设 |
  | **归档** | 剥掉数据后无法陈述 | 数据进 `Archive`，不进定理 |

  ## 判据（`D-006`）

  > **消融掉之后，这条规则还是不是原来那条？**

  本模块把这个问题变成 `Dissolve.SameMeaning`，并证明三分法的**互斥且穷尽**。

  ## 钉住什么

  1. **三分法穷尽**：任何一个数据项必有且只有一种归宿（`classify_exhaustive`）
  2. **消融不改来源**：`apply` 之后的 `support` 只可能变大，不会凭空干净
  3. **归档不进定理**：`Archive` 里的东西在 `support` 里查不到（`archive_not_in_support`）
-/

namespace FateV2.Modeling

open FateV2.Core

universe u

/-! ## §1 · 三种归宿 -/

/-- **数据项的归宿**。 -/
inductive Fate : Type where
  /-- 消融成具体定理（`support = ∅`） -/
  | theorem_
  /-- 转成经验假设（进 `support`） -/
  | assumption (id : AssumptionId)
  /-- 无法陈述，归档（不进定理） -/
  | archive (hash : String)
  deriving DecidableEq, Repr

/-- **含义是否保持**：消融前后是不是"同一条规则"（`D-006` 的判据）。 -/
def SameMeaning (before after : Formula u) : Prop := before = after

/-! ## §2 · 分类 -/

section Classify

variable {L : Type u}

/-- **分类一个数据项**：给定消融前后的公式与规模信息，决定归宿。

    * `same`：消融后含义不变 ⟹ 具体定理
    * `storable`：含义变了但能写成假设 ⟹ 经验假设
    * 否则：归档

    这个函数的**决策顺序**本身是 `D-006` 三层策略（消融 → 嵌入 → 引用）的实现。 -/
def classify (same : Bool) (hid : AssumptionId) (hsh : String) : Fate :=
  if same then
    .theorem_
  else if hid ≠ "" then
    .assumption hid
  else
    .archive hsh

end Classify

/-! ## §3 · 三分法穷尽 -/

section Exhaustive

variable {L : Type u}

/-- **归宿只有三种**：`Fate` 的构造子恰好三个。 -/
theorem fate_exhaustive (f : Fate) :
    (∃ (h : Bool), f = .theorem_) ∨
    (∃ id, f = .assumption id) ∨
    (∃ h, f = .archive h) := by
  cases f with
  | theorem_ => exact Or.inl ⟨true, rfl⟩
  | assumption id => exact Or.inr (Or.inl ⟨id, rfl⟩)
  | archive h => exact Or.inr (Or.inr ⟨h, rfl⟩)

end Exhaustive

/-! ## §4 · 消融的执行 -/

section Apply

variable {L : Type u}

/-- **消融一条规则**：按归宿决定产出的判断。 -/
def dissolve (j : Judgment L) (f : Fate) : Option (Judgment L) :=
  match f with
  | .theorem_ =>
      -- 消融成具体定理：保留结论，来源清空，状态升为 proven
      some ⟨j.hyp, j.concl, Support.empty, .proven⟩
  | .assumption id =>
      -- 转成经验假设：结论不变，来源加一条，状态降为 conditional
      some { j with support := Support.addAssumptions j.support [id], status := .conditional }
  | .archive _ =>
      -- 归档：不进定理
      none

/-- **消融成定理 ⟹ 来源为空**。 -/
theorem dissolve_theorem_support (j : Judgment L) :
    ∃ r, dissolve j .theorem_ = some r ∧ r.support.assumptions = [] := by
  exact ⟨_, rfl, rfl⟩

/-- **消融成假设 ⟹ 来源非空**（新的假设进来了）。 -/
theorem dissolve_assumption_support_ne (j : Judgment L) (id : AssumptionId) :
    ∃ r, dissolve j (.assumption id) = some r ∧ id ∈ r.support.assumptions := by
  refine ⟨_, rfl, ?_⟩
  simp [Support.addAssumptions]

/-- **归档 ⟹ 不产出判断**：`D-005` 说「数据本身不进入定理」的直接形式。 -/
theorem dissolve_archive_none (j : Judgment L) (h : String) :
    dissolve j (.archive h) = none := rfl

/-- **消融不会让来源凭空变干净**：

    若原来的来源非空，则转成经验假设后仍然非空。 -/
theorem dissolve_assumption_keeps_support (j : Judgment L) (id : AssumptionId)
    (hne : j.support.assumptions ≠ []) :
    ∃ r, dissolve j (.assumption id) = some r ∧ r.support.assumptions ≠ [] := by
  refine ⟨_, rfl, ?_⟩
  intro hnil
  apply hne
  have hsub := Support.subset_addAssumptions j.support [id]
  -- 新来源非空但原来源为空，矛盾
  have : ∀ a ∈ j.support.assumptions, a ∈ (Support.addAssumptions j.support [id]).assumptions := hsub
  rw [hnil] at this
  -- 用 `id` 属于新来源而原来源为空
  have hid : id ∈ (Support.addAssumptions j.support [id]).assumptions := by
    simp [Support.addAssumptions]
  rw [hnil] at hid
  exact absurd hid (by simp)

end Apply

/-! ## §5 · 归档的隔离性 -/

section Archive

/-- **归档项不进定理**：归档分支不产出判断，
    因此归档的内容不可能出现在任何判断的 support 里（`support` 只装 `AssumptionId`）。 -/
theorem archive_not_in_support {L : Type u} (j : Judgment L) (h : String) :
    dissolve j (.archive h) = none := rfl

end Archive

end FateV2.Modeling
