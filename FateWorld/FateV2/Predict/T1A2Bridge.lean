import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Predict.SeparableCondMul
import Mathlib.Tactic

/-!
  # Predict · T1A2Bridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2Bridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FinCondIndep, SeparableCondMul
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/T1A2Bridge` —— `T1A.2` 的 G3 桥（`CondMul` 的乘法形式）

## 内容

把 `FinJoint` 上的 `CondMul` 转换成乘法形式。

## `CondMul`（`FinCondIndep.lean:131`）

```lean
def CondMul (p : FinJoint α β γ) : Prop :=
  ∀ x y z, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z
```

## `marg*`（`FinCondIndep.lean:91,99,107`）

```lean
noncomputable def margZ (p : FinJoint α β γ) (z : γ) : ℝ
noncomputable def margXZ (p : FinJoint α β γ) (x : α) (z : γ) : ℝ
noncomputable def margYZ (p : FinJoint α β γ) (y : β) (z : γ) : ℝ
```
-/

namespace FateV2.Predict.T1A2Bridge

open FateV2.Predict.FinCondIndep

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐⭐⭐⭐ `CondMul` 的除法形式 -/

/-- ⭐⭐⭐⭐ **`CondMul` 的除法形式**：

若 `CondMul p` 且 `margZ p z ≠ 0`，则

$$p((x,y),z) = \frac{\mathrm{margXZ}(x,z)\cdot\mathrm{margYZ}(y,z)}{\mathrm{margZ}(z)}.$$ -/
theorem condMul_div_form
    (p : FinJoint α β γ) (h : CondMul p)
    (x : α) (y : β) (z : γ) (hz : margZ p z ≠ 0) :
    p ((x, y), z) = margXZ p x z * margYZ p y z / margZ p z := by
  have h1 : p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z := h x y z
  rw [eq_div_iff hz]
  exact h1

/-! ## §2 ⭐⭐⭐ 乘法分解 -/

/-- ⭐⭐⭐ **`CondMul` 的乘法分解**（`margZ ≠ 0` 处）。 -/
theorem condMul_factorization
    (p : FinJoint α β γ) (h : CondMul p)
    (x : α) (y : β) (z : γ) (hz : margZ p z ≠ 0) :
    p ((x, y), z) = (margXZ p x z / margZ p z) * margYZ p y z := by
  rw [condMul_div_form p h x y z hz]
  ring

/-! ## §3 ⭐⭐ 可分离性 ⟹ `CondMul` -/

/-- ⭐⭐⭐ **可分离性 ⟹ `CondMul`**（从 `SeparableCondMul` 复述）。 -/
theorem separable_implies_condMul'
    (p : FinJoint α β γ)
    (hsep : ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z) :
    CondMul p :=
  FateV2.Predict.SeparableCondMul.separable_implies_condMul p hsep

/-! ## §4 公理审计 -/

#print axioms condMul_div_form
#print axioms condMul_factorization
#print axioms separable_implies_condMul'

end FateV2.Predict.T1A2Bridge