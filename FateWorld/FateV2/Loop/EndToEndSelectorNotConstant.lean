/-
命运理论 · Lean 4 形式化
================================

模块：EndToEndSelectorNotConstant
缺口 3 重写 · 任务 A：**非常函数 selector 存在性**

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
证明：「`linWorld` 上的**常函数 selector**」只是**一个退化特例**；
一般情况下，`Selector.select` **可以依赖** `x`（状态参数）。

即：构造一个具体的 `Selector`，其 `select` 在 `x = true` 与 `x = false`
处返回**不同的二元组** `(Rule × ℝ)`。

---------------------------------------------------------------------------
为什么这不平凡（非平凡性说明）
---------------------------------------------------------------------------
本文件的定理**不是同义反复**：
- 前件只有类型假设（`StateSpace` / `CtxSpace` / `Selector` 的实例）；
- 结论 **存在** 一个 `Selector` 且其 `select` **非** `x₂`-常函数；
- 见证是**显式构造**的：`select := fun _ _ x => if x = true then (ruleA, 1) else (ruleB, 0)`，
  第二个分量 `1 ≠ 0` 即足以区分，与 `Rule` 是否相等无关。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`**。
- **加法式**：不修改任何已有模块。
-/

import FateWorld.FateV2.Predict.WorldModel
import Mathlib

namespace FateV2.Loop

open FateV2.Predict
namespace EndToEndSelectorNotConstant

/-!
  # Loop · EndToEndSelectorNotConstant

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndSelectorNotConstant.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModel
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## 1. 最简单的具体空间 -/

/-- 状态空间：`Bool`（两个元素，足以区分「依赖 `x`」与「常函数」）。 -/
abbrev sBool : FateV2.Modeling.StateSpace where
  Carrier := Bool
  topo := inferInstance
  meas := ⊤
  borel_le := le_top

/-- 上下文空间：`PUnit`（单元素，避免上下文带来的噪声）。 -/
abbrev cUnit : FateV2.Model.CtxSpace where
  Carrier := PUnit

/-- 输出空间 = 状态空间（自反馈）。 -/
abbrev oBool : FateV2.Model.OutSpace := sBool

/-! ## 1b. `MeasurableSpace` 实例（`Structure` 字段不会自动成为实例，需显式登记） -/

/-- `sBool.Carrier` 上的可测结构来自其 `meas` 字段。 -/
instance : MeasurableSpace sBool.Carrier := sBool.meas
/-- `oBool.Carrier` 与 `sBool.Carrier` 定义上相同，但需单独登记实例。 -/
instance : MeasurableSpace oBool.Carrier := oBool.meas

/-! ## 2. 两条不同的规则 -/

/-- 规则 A：`dirac x`（恒等核）。 -/
noncomputable def ruleA : FateV2.Model.Rule cUnit sBool oBool :=
  ⟨fun _ x => MeasureTheory.Measure.dirac x⟩

/-- 规则 B：`dirac false`（常核）。 -/
noncomputable def ruleB : FateV2.Model.Rule cUnit sBool oBool :=
  ⟨fun _ _ => MeasureTheory.Measure.dirac false⟩

/-- 规则集 `Rules` 是 `Set (Rule ...)`，取单元素的两种。 -/
noncomputable def rules : FateV2.Model.Rules cUnit sBool oBool := {ruleA}

/-! ## 3. 非常函数 selector（弱版本，主结论） -/

/-- 核心构造：`select` 依赖 `x`。评值分量 `1` 与 `0` 不同即足以区分。 -/
noncomputable def selW : FateV2.Predict.Selector cUnit sBool oBool where
  select := fun _ _ (x : Bool) =>
    bif x then (ruleA, 1) else (ruleB, 0)
  criterion := fun _ _ _ => 0

/-- ⭐⭐⭐ **【存在非常函数的 selector】**

存在 `Selector`，其 `select` **依赖**状态参数 `x`。 -/
theorem exists_selector_not_constant :
    ∃ S : FateV2.Predict.Selector cUnit sBool oBool,
      ∃ (R : FateV2.Model.Rules cUnit sBool oBool) (c : cUnit.Carrier),
        S.select R c true ≠ S.select R c false := by
  refine ⟨selW, rules, PUnit.unit, ?_⟩
  simp [selW]

/-- 更强形式：`select` 作为 `x` 的函数**不是常数函数**（等价陈述，便于引用）。 -/
theorem exists_selector_select_not_const :
    ∃ S : FateV2.Predict.Selector cUnit sBool oBool,
      ¬ ∀ (x₁ x₂ : sBool.Carrier),
        S.select rules PUnit.unit x₁ = S.select rules PUnit.unit x₂ := by
  refine ⟨selW, ?_⟩
  intro h
  have hstep : selW.select rules PUnit.unit true = selW.select rules PUnit.unit false :=
    h true false
  simp [selW] at hstep

/-- 反衬：存在**常函数** selector（`linWorld` 的退化特例形态），
说明常函数形态本身合法、只是非必然。 -/
noncomputable def selConst : FateV2.Predict.Selector cUnit sBool oBool where
  select := fun _ _ _ => (ruleA, 0)
  criterion := fun _ _ _ => 0

/-- 常函数 selector 的 `select` 确实与 `x` 无关。 -/
theorem selConst_is_constant :
    ∀ (R : FateV2.Model.Rules cUnit sBool oBool) (c : cUnit.Carrier) (x₁ x₂ : sBool.Carrier),
      selConst.select R c x₁ = selConst.select R c x₂ := by
  intro R c x₁ x₂
  rfl

/-- **结论（对比陈述）**：常函数 selector 与非常函数 selector 都合法，
故「常函数」是**退化特例**而非架构上的必然。 -/
theorem both_constant_and_nonconstant_legal :
    (∃ S : FateV2.Predict.Selector cUnit sBool oBool,
        ∀ (R : FateV2.Model.Rules cUnit sBool oBool) (c : cUnit.Carrier) (x₁ x₂ : sBool.Carrier),
          S.select R c x₁ = S.select R c x₂) ∧
      (∃ S : FateV2.Predict.Selector cUnit sBool oBool,
        ∃ (R : FateV2.Model.Rules cUnit sBool oBool) (c : cUnit.Carrier),
          S.select R c true ≠ S.select R c false) :=
  ⟨⟨selConst, selConst_is_constant⟩, exists_selector_not_constant⟩

end EndToEndSelectorNotConstant
end FateV2.Loop