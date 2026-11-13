import FateWorld.FateV2.Predict.Predict
import Mathlib.Data.List.Basic

/-!
  # Export · Modality —— 模态 = 投影（开放注册表）

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F6-10（多模态导出）
  - 依赖裁决：**D-010**（建模可呈现）、**D-011**（模态 = 推导器，开放集）、
              **D-012**（默认导出全部；边界 = 注册表）、
              **D-013**（模态不在模型里，只在导出这一步）、
              **D-023 A3**（模态是可注册的、增加的）、**D-023 B1**（一切可注册化）
  - 改动：原文件空骨架。
  - 状态：已验证

  ## 结构（逐条对应裁决）

  | 裁决 | 落点 |
  |---|---|
  | D-013「模态只是导出轴」 | `Modality.project : Model → ExportVal`，**不**进 `Model` |
  | D-011「模态是推导器」 | `Modality.observed : Bool` 区分观测/推导 |
  | D-011「开放集」 | `Registry` 就是 `List Modality`，随时可加 |
  | D-012「边界 = 注册表」 | `export` 遍历注册表，不设「有意义」判据 |
  | D-012「受限导出须标记」 | `ExportResult.restricted` |

  ## 降级 1：模态载体不是泛型的

  D-011 原写法是 `extract : Model → carrier`（`carrier` 依赖 `Modality` 自身）。
  Lean 里做**异质列表**要么 `Sigma`，要么统一编码。本批取**统一编码**：
  模态值一律记为 `ExportVal.real`（或 `.bool`）。
  ⟹ 加新模态时若其值不是实数/布尔，需要往 `ExportVal` 加构造子，**不是**零成本。
  这是为先把链跑通而做的选型（D-019 允许实现期选型），**不是**理论结论。

  ## 降级 2：`ExportVal` 没有 `Repr`

  `Real` 的 `Repr` 在 Lean 里是 `unsafe`，派生会把整条链拖进 unsafe。
  演示直接打印数值本身，不依赖 `Repr`。
-/

namespace FateV2.Export

universe u

open FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §1  模态
  =========================================================================== -/

/-- **模态标识**：开放，用 `String`（D-011 原文即 `abbrev ModalityId := String`）。 -/
abbrev ModalityId : Type := String

/-- **导出的值**（统一编码，见文件头「降级 1」）。 -/
inductive ExportVal : Type where
  /-- 实数 -/
  | real (x : Real) : ExportVal
  /-- 布尔（例如「是否越界」这类派生模态） -/
  | bool (b : Bool) : ExportVal

/-- **模态**：一个从完整模型到某个视图的**投影**。

  `project` 是该模态的推导器（D-011 措辞是 `extract`）。 -/
structure Modality (Val V E Noise : Type u) where
  /-- 模态标识 -/
  id : ModalityId
  /-- 是否来自原数据（D-011：`true` = 观测模态，`false` = 推导模态） -/
  observed : Bool
  /-- 投影 / 推导器 -/
  project : Model Val V E Noise → ExportVal

/-- **注册表**：模态的开放列表（D-012：边界 = 注册了多少个）。 -/
abbrev Registry (Val V E Noise : Type u) : Type u := List (Modality Val V E Noise)

/-- 注册一个模态。 -/
def Registry.add {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (m : Modality Val V E Noise) : Registry Val V E Noise := m :: reg

/-- 按标识查找。 -/
def Registry.find? {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (id : ModalityId) : Option (Modality Val V E Noise) :=
  List.find? (fun m => m.id == id) reg

/-! ===========================================================================
  §2  导出范围（D-012 §一.4：允许限定，但受限导出必须被标记）
  =========================================================================== -/

/-- **导出范围**：`include_` 非空则只导这些；`exclude` 排除这些。 -/
structure Scope where
  /-- 非空则只导这些 -/
  include_ : List ModalityId
  /-- 排除这些 -/
  exclude : List ModalityId

/-- 默认范围：**全部**（D-012 §一.1：能导出什么就导出什么）。 -/
def Scope.all : Scope := ⟨[], []⟩

/-- 只导这些。 -/
def Scope.only (ids : List ModalityId) : Scope := ⟨ids, []⟩

/-- 这个模态是否在范围内。 -/
def Scope.admits (sc : Scope) (m : ModalityId) : Bool :=
  (sc.include_.isEmpty || sc.include_.contains m) && !sc.exclude.contains m

/-- 范围是否**受限**（即不等于「全部」）。 -/
def Scope.isRestricted (sc : Scope) : Bool :=
  !(sc.include_.isEmpty && sc.exclude.isEmpty)

namespace Scope

/-- 空 `include_` 接受一切（辅助）。 -/
theorem admits_of_include_nil (exclude : List ModalityId) (m : ModalityId) :
    Scope.admits ⟨[], exclude⟩ m = !exclude.contains m := by
  show (([].isEmpty || ([] : List ModalityId).contains m) && !exclude.contains m)
      = !exclude.contains m
  rw [List.isEmpty_nil]
  rfl

/-- **默认范围接受每一个标识**。

  **超出定义之处**：`admits` 的定义是一串布尔运算（`isEmpty || contains` 再与
  `!exclude.contains`）；本定理说明默认范围（两个字段都空）**接受所有**标识——
  即 D-012 的「默认导出全部」不是口号，而是 `Scope.all` 的可检性质。 -/
theorem admits_all (m : ModalityId) : Scope.all.admits m = true := by
  have h := admits_of_include_nil ([] : List ModalityId) m
  show Scope.all.admits m = true
  show Scope.admits ⟨[], []⟩ m = true
  rw [h]
  rfl

/-- 默认范围**不受限**。 -/
theorem all_not_restricted : Scope.all.isRestricted = false := rfl

/-- **「只导 [m]」时，`m` 在范围内**。 -/
theorem only_admits_self (m : ModalityId) :
    (Scope.only [m]).admits m = true := by
  have h : ((m == m) || ([] : List ModalityId).contains m) = true := by
    rw [beq_self_eq_true]
    rfl
  show (((m == m) || ([] : List ModalityId).contains m)
        && (!(([] : List ModalityId).contains m))) = true
  rw [h, List.contains_nil, Bool.not_false]
  rfl

/-- **「只导 [m]」时，`n ≠ m` 被拒**。

  **超出定义之处**：这条把「受限导出」从"字段被填了"升级为**行为**——
  `export` 用 `admits` 过滤，于是「受限」意味着**真的有模态被挡掉**。
  没有这条，`Scope.isRestricted` 只是元数据，与结果无关。 -/
theorem only_rejects (m n : ModalityId) (h : n ≠ m) :
    (Scope.only [m]).admits n = false := by
  have hnm : ¬ (n == m) = true := by
    rw [beq_iff_eq]
    exact h
  have hf : (n == m) = false := by
    cases hb : (n == m)
    · rfl
    · exact absurd hb hnm
  show (((n == m) || ([] : List ModalityId).contains n)
        && (!(([] : List ModalityId).contains n))) = false
  rw [hf, List.contains_nil, Bool.not_false]
  rfl

end Scope

/-! ===========================================================================
  §3  导出结果
  =========================================================================== -/

/-- **导出结果**：一组 `(模态标识, 值)` 对，外加**范围元数据**。

  D-012 代价 3：「若一次导出用了 scope 限制，结果必须是受限子集，
  不能声称『这是完整模型』⟹ 导出结果要带 `scope` 元数据」。 -/
structure ExportResult where
  /-- 导出的模态与值 -/
  items : List (ModalityId × ExportVal)
  /-- 用了什么范围 -/
  scope : Scope

namespace ExportResult

/-- 导出的模态个数。 -/
def count (r : ExportResult) : Nat := r.items.length

/-- 这次导出是否**受限**（据此才能/不能声称「完整模型」）。 -/
def restricted (r : ExportResult) : Bool := r.scope.isRestricted

/-- 取值列表。 -/
def vals (r : ExportResult) : List ExportVal := r.items.map Prod.snd

/-- 标识列表。 -/
def ids (r : ExportResult) : List ModalityId := r.items.map Prod.fst

end ExportResult

end FateV2.Export
