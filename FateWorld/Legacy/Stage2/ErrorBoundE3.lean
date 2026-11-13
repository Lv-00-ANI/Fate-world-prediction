import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# `Fate/Stage2/ErrorBoundE3` —— `𝖤₃` 模型误差界

## 内容

模型误差的基本工具：**三角不等式 + Lipschitz 传递**。

## 理论形式

$$R(\hat P) - R^* \le 2L_{\mathcal{L}}\cdot\varepsilon_{\text{mis}} + \delta_{\text{approx}} + \text{(E2 项)}$$

**⚠ 完整版需要风险泛函 `R` 的载体。**
本文件只交付**代数核心**：

$$|R(\hat P) - R(P^*)| \le L\cdot d(\hat P, P^*)$$
-/

namespace Fate.Stage2.ErrorBoundE3

variable {Z : Type*}

/-! ## §1 ⭐⭐⭐ Lipschitz 传递 -/

/-- ⭐⭐⭐ **Lipschitz 风险差**：

若风险泛函 `R` 是 `L`-Lipschitz（`L ≥ 0`），
则 `|R P₁ - R P₂| ≤ L * d P₁ P₂`。

**⚠ 这是「模型误差」的**确界形式**（`d` 是任意伪度量）。** -/
theorem risk_lipschitz_bound
    (R : Z → ℝ) (d : Z → Z → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ P Q, |R P - R Q| ≤ L * d P Q)
    (P Q : Z) :
    |R P - R Q| ≤ L * d P Q :=
  hLip P Q

/-! ## §2 ⭐⭐ 三角不等式链 -/

/-- ⭐⭐ **三点链**：`|R A - R C| ≤ |R A - R B| + |R B - R C|`。 -/
theorem risk_triangle
    (R : Z → ℝ) (A B C : Z) :
    |R A - R C| ≤ |R A - R B| + |R B - R C| := by
  have h1 : R A - R C = (R A - R B) + (R B - R C) := by ring
  rw [h1]
  exact abs_add_le _ _

/-- ⭐⭐⭐ **模型误差的三角界**：

若 `R` 是 `L`-Lipschitz，则

$$|R(\hat P) - R(P^*)| \le L\cdot d(\hat P, P) + L\cdot d(P, P^*)$$

**⚠ 这是「近似 + 模型误设」的**分离形式**。** -/
theorem risk_model_error_bound
    (R : Z → ℝ) (d : Z → Z → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ P Q, |R P - R Q| ≤ L * d P Q)
    (Phat P Pstar : Z) :
    |R Phat - R Pstar| ≤ L * d Phat P + L * d P Pstar := by
  calc |R Phat - R Pstar|
      ≤ |R Phat - R P| + |R P - R Pstar| := risk_triangle R Phat P Pstar
    _ ≤ L * d Phat P + L * d P Pstar := by
        have h1 := hLip Phat P
        have h2 := hLip P Pstar
        linarith

/-! ## §3 ⭐⭐ 可分离形式 -/

/-- ⭐⭐⭐ **误差分离**：`L*d₁ + L*d₂ = L*(d₁ + d₂)`。 -/
theorem risk_error_separable
    (d1 d2 L : ℝ) :
    L * d1 + L * d2 = L * (d1 + d2) := by
  ring

/-! ## §4 公理审计 -/

#print axioms risk_lipschitz_bound
#print axioms risk_triangle
#print axioms risk_model_error_bound
#print axioms risk_error_separable

end Fate.Stage2.ErrorBoundE3