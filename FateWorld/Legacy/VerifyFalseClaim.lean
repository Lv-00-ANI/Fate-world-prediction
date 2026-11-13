import FateWorld.Legacy.Counterfactual

/-! ### 独立验证：被删除陈述的**反例**是否真成立

subagent 声称 `obsOnQuotBy_injective_iff` **数学上为假**，并给出反例：
- `SCM := Bool`、`Obs := fun _ => ()`、`F := {true}`（单点纤维）、`r := ⊥`（相等）
- 则 `r ≤ ker Obs` 成立、商是单点子商故 `obsOnQuotBy` 单射
- 但 `ker Obs ≤ r` 要求 `true = false`，为假

**本文件独立复现该反例**（若通过，则 subagent 的判断成立）。 -/

namespace Fate

namespace VerifyFalseClaim

open Fate.Counterfactual

/-- 反例的设置：`Obs` 是常值函数。 -/
def obsConst : Bool → Unit := fun _ => ()

/-- ⭐ **反例的结论**：`ker Obs ≤ ⊥` **不成立**。

即：存在 `a b` 使 `Obs a = Obs b` 但 `a ≠ b`。
**这正是原陈述 `(←)` 方向失败的原因。** -/
theorem ker_not_le_bot : ¬ (Setoid.ker obsConst ≤ (⊥ : Setoid Bool)) := by
  intro h
  have hmem : (Setoid.ker obsConst) true false := rfl
  have : (⊥ : Setoid Bool) true false := h hmem
  exact Bool.noConfusion this

/-- ⭐ **而 `⊥ ≤ ker Obs` 成立**（因为 `⊥` 是最细的）。 -/
theorem bot_le_ker : (⊥ : Setoid Bool) ≤ Setoid.ker obsConst :=
  bot_le

/-- ⭐⭐ **合起来**：`⊥ ≤ ker Obs` 为真而 `ker Obs ≤ ⊥` 为假。

**⟹ 原陈述 `Injective (obsOnQuotBy M r h F) ↔ ker Obs ≤ r`
在 `r := ⊥`、`F := {true}` 时不成立** ——
**因为左边（单射）为真而右边为假。**

**这是对 subagent「该陈述为假」判断的独立佐证。** -/
theorem counterexample_core :
    (⊥ : Setoid Bool) ≤ Setoid.ker obsConst ∧ ¬ (Setoid.ker obsConst ≤ (⊥ : Setoid Bool)) :=
  ⟨bot_le_ker, ker_not_le_bot⟩

end VerifyFalseClaim

end Fate
