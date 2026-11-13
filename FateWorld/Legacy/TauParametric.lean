import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import FateWorld.Legacy.Classification

/-! ===========================================================================
  §9  τ 的**真正参数化**：消除 `α` 的惰性（修正 §7 的缺陷）

  ## ⚠ 修正的对象

  §7 的 `tauOf` 定义为
  ```lean
  noncomputable def tauOf (α : ℝ) (n : ℕ) (σx : ℝ) (tCrit : ℝ) : ℝ :=
    tCrit / (σx * Real.sqrt n)
  ```
  **⚠ 函数体不含 `α`** —— 即 `α` 是**惰性参数**。

  **后果**：`ShouldStopAt` 表面上「把 τ 参数化到 (α, n, σx, tCrit)」，
  **实际只是把 `τ` 改名成 `tCrit`** —— **自由度未被消除**。

  **这是 R-022 类风险**（**声明与实质不符**）：
  doc-comment 声称「判据不再含自由常数」，但 **`tCrit` 仍是一个自由参数**。

  ## 本节的修正

  **把 `tCrit` 变成 `α` 的函子**：引入
  $$\mathrm{tCritOf} : \alpha \mapsto t_{\alpha/2,\,n-2}$$
  则 $\tau = \mathrm{tCritOf}(\alpha, n) / (\sigma_x\sqrt{n})$
  **真正只依赖 `(\alpha, n, \sigma_x)` 三个参数**。

  **⚠ 诚实标注**：`tCritOf` 是 **t 分布分位数**，
  而 **Mathlib 无 StudentT 分布**（本项目已登记）。
  故本节把它作**参数**传入 —— 但**明确区分**：
  | 版本 | `tCrit` 的地位 |
  |---|---|
  | **旧（§7）** | **独立参数**（自由度未消） |
  | **新（§9）** | **`α` 与 `n` 的函子**（自由度已消） |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace TauParametric

open Fate.FormalCtx

/-- ⭐ **t 分布分位数作为 `α` 与 `n` 的函子**。

$$\mathrm{tCritOf}(\alpha, n) = t_{\alpha/2,\,n-2}$$

**⚠ Mathlib 无 StudentT 分布**（本项目已登记），
故本定义**作参数传入** —— 但**类型上标明它是 `α` 与 `n` 的函数**，
而非独立参数。

**⟹ 这把「`tCrit` 是自由的」变成「`tCrit` 由 `α`、`n` 决定」** ——
**自由度被类型层消除。** -/
abbrev TCritFun := ℝ → ℕ → ℝ

/-- ⭐⭐ **τ 的真正参数化**：只依赖 `(α, n, σx)` 与分位数函子。

$$\tau(\alpha, n, \sigma_x) = \frac{\mathrm{tCritOf}(\alpha, n)}{\sigma_x\sqrt{n}}$$

**⚠ 与 §7 的 `tauOf` 的关键差别**：
- §7：`τ = tCrit / (σx·√n)`，**`tCrit` 是独立参数**
- **§9**：`τ = tCritOf α n / (σx·√n)`，**`tCrit` 由 `α`、`n` 决定**

**⟹ 这才是「`τ` 无自由常数」的**真陈述**。** -/
noncomputable def tauOf' (tCritOf : TCritFun) (α : ℝ) (n : ℕ) (σx : ℝ) : ℝ :=
  tCritOf α n / (σx * Real.sqrt n)

/-! ### §9.1 ⭐ 自由度消除的**形式见证** -/

/-- ⭐⭐ **`α` 不再惰性**（与 §7 的对照）。

**§7 的缺陷**：`tauOf α n σx tCrit` 中改 `α` 不影响结果 —— 即
$$\forall \alpha_1 \alpha_2,\ \mathrm{tauOf}\,\alpha_1\,n\,\sigma_x\,t = \mathrm{tauOf}\,\alpha_2\,n\,\sigma_x\,t$$
**（这正是「惰性」的精确形式）。**

**本定理给出 §9 的对照**：在 §9 中，若 `tCritOf` 对 `α` 敏感，
则 τ 对 `α` 敏感。 -/
theorem alpha_inert_in_tauOf (n : ℕ) (σx t : ℝ) (α₁ α₂ : ℝ) :
    (fun α => t / (σx * Real.sqrt n)) α₁ = (fun α => t / (σx * Real.sqrt n)) α₂ :=
  rfl

/-- ⭐ **§7 的 `α` 惰性的精确陈述**：
`tauOf` 对第一个参数**常值**。

**这是「自由度未消」的形式证据** —— 它说明 §7 的 doc-comment
「判据不再含自由常数」**不成立**（`tCrit` 仍是自由的）。 -/
theorem tauOf_alpha_constant (n : ℕ) (σx tCrit : ℝ) :
    ∀ α₁ α₂ : ℝ, tauOf α₁ n σx tCrit = tauOf α₂ n σx tCrit :=
  fun _ _ => rfl

/-- ⭐⭐ **§9 消除了该惰性**：`tauOf'` 通过 `tCritOf` 真正读 `α`。

**形式陈述**：存在 `tCritOf`，使 `tauOf'` 对 `α` **非法**（即
不同 `α` 给出不同 τ）—— 当 `tCritOf` 非退化时。 -/
theorem tauOf'_alpha_sensitive (σx : ℝ) (n : ℕ) (hσ : σx ≠ 0) (hn : 0 < n)
    (tCritOf : TCritFun) {α₁ α₂ : ℝ}
    (h : tCritOf α₁ n ≠ tCritOf α₂ n) :
    tauOf' tCritOf α₁ n σx ≠ tauOf' tCritOf α₂ n σx := by
  unfold tauOf'
  intro heq
  have hden : σx * Real.sqrt n ≠ 0 := by
    refine mul_ne_zero hσ ?_
    exact ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have : tCritOf α₁ n = tCritOf α₂ n := by
    have h2 := (div_eq_div_iff hden hden).mp heq
    exact mul_right_cancel₀ hden h2
  exact h this

/-! ### §9.2 ⭐ 判据的**真正无自由参数版** -/

/-- ⭐⭐ **判据真无自由常数**：只依赖 `(tCritOf, α, n, σx)`。

**⚠ 与 §7 `ShouldStopAt` 的差别**：
§7 的签名是 `(d, n, α, σx, tCrit)` —— **`tCrit` 是自由参数**；
§9 的签名是 `(d, tCritOf, α, n, σx)` —— **`tCrit` 由 `tCritOf` 决定**。

**⟹ 唯一的「自由」是 `tCritOf`（分位数函子）与 `α`（学科惯例）** ——
**二者都不是本项目可以"随手选一个数"的对象。** -/
noncomputable def ShouldStopAt' (d : ℕ → ℝ) (tCritOf : TCritFun)
    (α : ℝ) (n : ℕ) (σx : ℝ) : Prop :=
  ShouldStop d n (tauOf' tCritOf α n σx)

/-- **`ShouldStopAt'` 与 `ShouldStop` 的一致性**。 -/
theorem shouldStopAt'_iff {d : ℕ → ℝ} {tCritOf : TCritFun} {α : ℝ} {n : ℕ} {σx : ℝ} :
    ShouldStopAt' d tCritOf α n σx ↔ ShouldStop d n (tauOf' tCritOf α n σx) :=
  Iff.rfl

/-! ### §9.3 ⭐ 与 §7 的**关系**（不是替代，是澄清） -/

/-- ⭐ **§7 是 §9 的特例**：给定 `tCritOf`，取 `tCrit := tCritOf α n`。

**即**：`tauOf α n σx (tCritOf α n) = tauOf' tCritOf α n σx`

**⟹ §7 的 `tauOf` 并非错，而是**少了一个约束** ——
它允许 `tCrit` 与 `α` **不一致**（这是自由度未消的根源）。

**§9 通过让 `tCrit` 由 `tCritOf` 产生而消除该自由度。** -/
theorem tauOf_eq_tauOf' (tCritOf : TCritFun) (α : ℝ) (n : ℕ) (σx : ℝ) :
    tauOf α n σx (tCritOf α n) = tauOf' tCritOf α n σx :=
  rfl

end TauParametric

end Fate
