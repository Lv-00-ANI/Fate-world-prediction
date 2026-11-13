import FateWorld.FateV2.Core.Ops
import FateWorld.FateV2.Rules.RuleSet
import Mathlib.Tactic

/-!
  # Rules · OperatorInstance — 四算子在具体载体上的实例

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：F3-14（规则载体）、F3-17（规则集）
  - 依赖裁决：**D-002**（载体 = IR）、**D-003**（完备性）、**D-004**（单位 = 条件定理）、
              **D-006**（数据三层）
  - 改动：从空壳补成实现。`Core/Ops.lean` 给出了四算子的**策略结构**
          （`GammaPolicy`/`UpsilonPolicy`/`AlphaPolicy` + `composeOp`），
          本模块给出它们在**规则集**这个载体上的具体实例。
  - 状态：已编译

  ## 四算子的载体层语义

  | 算子 | 定义域 | 在规则集上的含义 |
  |---|---|---|
  | **α** 抽象 | 数据 `In` | 数据 → 规则（从数据造出一条判断） |
  | **γ** 泛化 | 判断 | 放宽前件（可能降状态） |
  | **∘** 组合 | 判断 × 判断 | 串接两条规则 |
  | **υ** 完善 | 判断 × 数据 | 用数据加强一条规则 |

  ## 本模块钉住的核心不变量

  **没有任何算子能减少 support**（`D-004` 铁律，`Core/Ops` 已对单条判断证明）。

  本模块把它**提升到规则集层**：对一组规则整体施加算子后，
  **规则集的总来源只会变大**（`lift_operator_support_mono`）。

  这条的实践意义：**不能靠"先抽象再组合"绕过假设**——
  每加上一层算子，来源账本只会更厚，不会更薄。
-/

namespace FateV2.Rules

open FateV2.Core

universe u

/-! ## §1 · 把单条算子提升到规则集 -/

/-- **把算子提升到规则集**：对每条规则分别施加。 -/
def liftOp {L : Type u} (op : Op L) (R : RuleSet L) : RuleSet L :=
  ⟨R.rules.map op⟩

/-- **提升后的来源 ⊇ 原来源**：若算子保持 support 单调，则整体也单调。

    这是 `D-004` 铁律从「单条判断」到「规则集」的**上升**。 -/
theorem liftOp_support_mono {L : Type u} {op : Op L}
    (hmono : SupportMonotone op) (R : RuleSet L) :
    R.support.Subset (liftOp op R).support := by
  intro x hx
  unfold RuleSet.support at *
  unfold liftOp
  -- 在 map 后的列表里逐条找
  obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hx
  refine List.mem_flatMap.mpr ⟨op j, ?_, hmono j x hxj⟩
  exact List.mem_map_of_mem hj

/-! ## §2 · 四个算子的具体实例 -/

/-- **α 的具体实例**：把一个可判定的输入转成无条件判断。

    `α` 的输入是数据（D-006 三层策略的第一层：消融）。
    消融后含义不变的数据，转成 `support = ∅` 的无条件判断。 -/
def alphaOfData {L : Type u} (concl : Formula L)
    (_x : Unit) : Judgment L :=
  Judgment.mkUncond concl Support.empty .proven

/-- **α 产出空来源**：消融路径下，数据不进入 support（D-005）。

    这是 `D-005` 的直接形式化：**能形式化的数据 → 具体定理（support 为空）**。 -/
theorem alphaOfData_support_empty {L : Type u} (concl : Formula L) (x : Unit) :
    (alphaOfData concl x).support.assumptions = [] := rfl

/-- **γ 的具体实例**：弱化状态（泛化的典型后果）。

    `D-004`：`γ` 常把 `proven` 降为 `conditional`。 -/
def gammaWeaken {L : Type u} (j : Judgment L) : Judgment L :=
  { j with status := j.status.weaker .conditional }

/-- **γ 不改变来源**：弱化状态不影响承了哪些前件。 -/
theorem gammaWeaken_support_eq {L : Type u} (j : Judgment L) :
    (gammaWeaken j).support = j.support := rfl

/-- **γ 满足 support 单调**（等式是最强的单调）。 -/
theorem gammaWeaken_supportMonotone : SupportMonotone (@gammaWeaken L) := by
  intro j x hx
  exact hx

/-- **∘ 的具体实例**：把一条规则串到另一条后面。 -/
def composeWith {L : Type u} (j₂ : Judgment L) : Op L := composeOp j₂

/-- **υ 的具体实例**：用一次消融结果加强一条规则。

    `υ` 的定义是「加新假设」，因此 support 只增不减。 -/
def upsilonAdd {L : Type u} (extra : List AssumptionId) (j : Judgment L) : Judgment L :=
  { j with support := j.support.addAssumptions extra }

/-- **υ 只增不减**：新增的假设进来源，原有的一条不丢。 -/
theorem upsilonAdd_support_mono {L : Type u} (extra : List AssumptionId) :
    SupportMonotone (@upsilonAdd L extra) := by
  intro j x hx
  exact Support.subset_addAssumptions j.support extra x hx

/-! ## §3 · 算子的组合：管线来源只增 -/

/-- **一条管线**：若干算子依次施加。 -/
abbrev Pipeline (L : Type u) : Type u := List (Op L)

/-- 施加一条管线。 -/
def runPipeline {L : Type u} (p : Pipeline L) (j : Judgment L) : Judgment L :=
  p.foldl (fun acc op => op acc) j

/-- **空管线是恒等**。 -/
theorem runPipeline_nil {L : Type u} (j : Judgment L) :
    runPipeline ([] : Pipeline L) j = j := rfl

/-- **管线保 support 单调**：每一步都单调，整体就单调。

    这是「不能靠堆算子绕过假设」的完整形式。 -/
theorem runPipeline_support_mono {L : Type u} {p : Pipeline L}
    (hall : ∀ op ∈ p, SupportMonotone op) (j : Judgment L) :
    j.support.Subset (runPipeline p j).support := by
  induction p generalizing j with
  | nil => exact Support.subset_refl j.support
  | cons hd tl ih =>
    simp only [runPipeline, List.foldl_cons]
    have h1 : j.support.Subset (hd j).support := (hall hd (by simp)) j
    have h2 : (hd j).support.Subset (runPipeline tl (hd j)).support :=
      ih (fun op hop => hall op (by simp [hop])) (hd j)
    exact Support.subset_trans h1 h2

/-! ## §4 · 规则集 + 管线：两层的单调合并 -/

/-- **规则集 + 管线**：对整组规则跑一条管线。 -/
def runOnSet {L : Type u} (p : Pipeline L) (R : RuleSet L) : RuleSet L :=
  ⟨R.rules.map (runPipeline p)⟩

/-- **两层单调合并**：规则集经管线处理，来源仍只增不减。

    这条把 §1（规则集层）与 §3（管线层）的单调性合成一条，
    是「四算子不会让系统变干净」的最终形式。 -/
theorem runOnSet_support_mono {L : Type u} {p : Pipeline L}
    (hall : ∀ op ∈ p, SupportMonotone op) (R : RuleSet L) :
    R.support.Subset (runOnSet p R).support := by
  intro x hx
  unfold RuleSet.support at *
  unfold runOnSet
  obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hx
  refine List.mem_flatMap.mpr ⟨runPipeline p j, List.mem_map_of_mem hj, ?_⟩
  exact runPipeline_support_mono hall j x hxj

end FateV2.Rules
