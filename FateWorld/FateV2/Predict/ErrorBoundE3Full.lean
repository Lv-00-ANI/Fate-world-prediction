import FateWorld.FateV2.Error.ErrorBoundE3
import Mathlib.Tactic

/-!
  # Predict · ErrorBoundE3Full

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE3Full.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorBoundE3
  - 补充 open 域：FateV2.Error
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/Stage2/ErrorBoundE3Full` —— `𝖤₃` 模型误差界的完整形式

## 内容

在 `Fate.Stage2.ErrorBoundE3` 的代数核心
（`risk_model_error_bound`：`|R P̂ - R P*| ≤ L·d(P̂,P) + L·d(P,P*)`）之上，
交付**误差的两项分解**与 **`2L` 系数形式**。

## 理论形式

$$R(\hat P) - R^* \le 2L_{\mathcal{L}}\cdot\varepsilon_{\text{mis}}
  + \delta_{\text{approx}} + \text{(E2 项)}$$

## 关键思想

`E3` 的「近似误差 + 误设误差」分解**不需要** `d` 满足三角不等式：
`risk_model_error_bound` 已经给出经由中间点 `P` 的三点链
（`P̂ --(近似)-- P --(误设)-- P*`），
再对两段各自夹逼常量 `δ_app` / `ε_mis`，即可得 `L·δ_app + L·ε_mis`。
-/

namespace FateV2.Predict.Stage2.ErrorBoundE3Full

open FateV2.Error

open FateV2.Error.Stage2.ErrorBoundE3

/-! ## §1 ⭐⭐⭐ 模型误差的两项分解 -/

/-- ⭐⭐⭐ **模型误差的两项分解**（近似误差 + 误设误差）：

若 `d(P̂, P*) ≤ δ_app + ε_mis`（三角分解），
则 `|R P̂ - R P*| ≤ L·δ_app + L·ε_mis`。 -/
theorem model_error_decomposition
    {Z : Type*} (R : Z → ℝ) (d : Z → Z → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ P Q, |R P - R Q| ≤ L * d P Q)
    (Phat P Pstar : Z) (dapp dmis : ℝ)
    (hd : d Phat P ≤ dapp) (hdm : d P Pstar ≤ dmis) :
    |R Phat - R Pstar| ≤ L * dapp + L * dmis := by
  have h1 := risk_model_error_bound R d L hL hLip Phat P Pstar
  have h2 : L * d Phat P ≤ L * dapp := by
    exact mul_le_mul_of_nonneg_left hd hL
  have h3 : L * d P Pstar ≤ L * dmis := by
    exact mul_le_mul_of_nonneg_left hdm hL
  linarith

/-! ## §2 ⭐⭐⭐ `2L` 系数的形式 -/

/-- ⭐⭐⭐ **`2L` 形式**：

若 `d(P̂, P*) ≤ ε` 且 `d` 满足三角不等式，则 `|R P̂ - R P*| ≤ 2L·ε`。 -/
theorem model_error_two_L
    {Z : Type*} (R : Z → ℝ) (d : Z → Z → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ P Q, |R P - R Q| ≤ L * d P Q)
    (Phat P Pstar : Z) (eps : ℝ)
    (h1 : d Phat P ≤ eps) (h2 : d P Pstar ≤ eps) :
    |R Phat - R Pstar| ≤ 2 * L * eps := by
  have h := risk_model_error_bound R d L hL hLip Phat P Pstar
  have h3 : L * d Phat P ≤ L * eps := mul_le_mul_of_nonneg_left h1 hL
  have h4 : L * d P Pstar ≤ L * eps := mul_le_mul_of_nonneg_left h2 hL
  linarith

/-! ## §3 公理审计 -/

#print axioms model_error_decomposition
#print axioms model_error_two_L

end FateV2.Predict.Stage2.ErrorBoundE3Full
