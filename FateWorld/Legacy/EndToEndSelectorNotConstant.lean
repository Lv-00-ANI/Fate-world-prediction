/-
命运理论 · Lean 4 形式化
================================

模块：Fate.EndToEndSelectorNotConstant
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

import FateWorld.Legacy.WorldModel
import Mathlib

namespace Fate
namespace EndToEndSelectorNotConstant

/-! ## 1. 最简单的具体空间 -/

/-- 状态空间：`Bool`（两个元素，足以区分「依赖 `x`」与「常函数」）。 -/
abbrev sBool : Fate.StateSpace where
  Carrier := Bool
  topo := inferInstance
  meas := ⊤
  borel_le := le_top

/-- 上下文空间：`PUnit`（单元素，避免上下文带来的噪声）。 -/
abbrev cUnit : Fate.CtxSpace where
  Carrier := PUnit

/-- 输出空间 = 状态空间（自反馈）。 -/
abbrev oBool : Fate.OutSpace := sBool

/-! ## 1b. `MeasurableSpace` 实例（`Structure` 字段不会自动成为实例，需显式登记） -/

/-- `sBool.Carrier` 上的可测结构来自其 `meas` 字段。 -/
instance : MeasurableSpace sBool.Carrier := sBool.meas
/-- `oBool.Carrier` 与 `sBool.Carrier` 定义上相同，但需单独登记实例。 -/
instance : MeasurableSpace oBool.Carrier := oBool.meas

/-! ## 2. 两条不同的规则 -/

/-- 规则 A：`dirac x`（恒等核）。 -/
noncomputable def ruleA : Fate.Rule cUnit sBool oBool :=
  ⟨fun _ x => MeasureTheory.Measure.dirac x⟩

/-- 规则 B：`dirac false`（常核）。 -/
noncomputable def ruleB : Fate.Rule cUnit sBool oBool :=
  ⟨fun _ _ => MeasureTheory.Measure.dirac false⟩

/-- 规则集 `Rules` 是 `Set (Rule ...)`，取单元素的两种。 -/
noncomputable def rules : Fate.Rules cUnit sBool oBool := {ruleA}

/-! ## 3. 非常函数 selector（弱版本，主结论） -/

/-- 核心构造：`select` 依赖 `x`。评值分量 `1` 与 `0` 不同即足以区分。 -/
noncomputable def selW : Fate.Selector cUnit sBool oBool where
  select := fun _ _ (x : Bool) =>
    bif x then (ruleA, 1) else (ruleB, 0)
  criterion := fun _ _ _ => 0

/-- ⭐⭐⭐ **【存在非常函数的 selector】**

存在 `Selector`，其 `select` **依赖**状态参数 `x`。 -/
theorem exists_selector_not_constant :
    ∃ S : Fate.Selector cUnit sBool oBool,
      ∃ (R : Fate.Rules cUnit sBool oBool) (c : cUnit.Carrier),
        S.select R c true ≠ S.select R c false := by
  refine ⟨selW, rules, PUnit.unit, ?_⟩
  simp [selW]

/-- 更强形式：`select` 作为 `x` 的函数**不是常数函数**（等价陈述，便于引用）。 -/
theorem exists_selector_select_not_const :
    ∃ S : Fate.Selector cUnit sBool oBool,
      ¬ ∀ (x₁ x₂ : sBool.Carrier),
        S.select rules PUnit.unit x₁ = S.select rules PUnit.unit x₂ := by
  refine ⟨selW, ?_⟩
  intro h
  have hstep : selW.select rules PUnit.unit true = selW.select rules PUnit.unit false :=
    h true false
  simp [selW] at hstep

/-- 反衬：存在**常函数** selector（`linWorld` 的退化特例形态），
说明常函数形态本身合法、只是非必然。 -/
noncomputable def selConst : Fate.Selector cUnit sBool oBool where
  select := fun _ _ _ => (ruleA, 0)
  criterion := fun _ _ _ => 0

/-- 常函数 selector 的 `select` 确实与 `x` 无关。 -/
theorem selConst_is_constant :
    ∀ (R : Fate.Rules cUnit sBool oBool) (c : cUnit.Carrier) (x₁ x₂ : sBool.Carrier),
      selConst.select R c x₁ = selConst.select R c x₂ := by
  intro R c x₁ x₂
  rfl

/-- **结论（对比陈述）**：常函数 selector 与非常函数 selector 都合法，
故「常函数」是**退化特例**而非架构上的必然。 -/
theorem both_constant_and_nonconstant_legal :
    (∃ S : Fate.Selector cUnit sBool oBool,
        ∀ (R : Fate.Rules cUnit sBool oBool) (c : cUnit.Carrier) (x₁ x₂ : sBool.Carrier),
          S.select R c x₁ = S.select R c x₂) ∧
      (∃ S : Fate.Selector cUnit sBool oBool,
        ∃ (R : Fate.Rules cUnit sBool oBool) (c : cUnit.Carrier),
          S.select R c true ≠ S.select R c false) :=
  ⟨⟨selConst, selConst_is_constant⟩, exists_selector_not_constant⟩

end EndToEndSelectorNotConstant
end Fate
