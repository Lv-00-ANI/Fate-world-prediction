import FateWorld.FateV2.Error.ErrorBoundChain
import FateWorld.FateV2.Error.ChainErrorBudget

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ErrorBoundChainConsumer.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 8 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Modeling
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
  **接入：ErrorBoundChain 的消费方**

  源模块：`FateV2.Error/ErrorBoundChain.lean`（`namespace FateV2.Error.R253ErrorBound`）
  接入方向：把 `ErrorBoundChain` 的**决策保持判据**（`2ε < |s|` ⟹ `sgn (s+δ) = sgn s`）
            与 `ChainErrorBudget` 的**三段误差预算**（`est + learn + steady`）对接。

  ============================================================================
  目标模块 `ErrorBoundChain` 的**全部核心声明**（实测，见下）
  ============================================================================
  §1 `sgn` / `linScore` / `margin`：`sgn`、`sgn_of_pos`、`sgn_of_neg`、`sgn_of_zero`、
     `sgn_congr_of_pos_of_pos`、`sgn_congr_of_neg_of_neg`、`linScore`、`linScore_eq_sum`、
     `margin`、`margin_nonneg`、`margin_decides`
  §2 `error_bound_gives_correct_classification`（主定理 A）、`..._margin`
  §3 `perturbation_affects_decision`、`tight_bound_degenerates`、`boundary_of_tight_bound`
  §4 `learning_bound_general`、`classifier_function_eq`
  §5 `young`、`cauchy_schwarz_abs`、`norm_sub_sq_real'`、`cos_close_general`、
     `inner_normalized`、`norm_normalized`、`unit_transfer_bound`、
     `sqrt_two_mul_sixteenth`、`concrete_transfer_example`、`sqrt_bound_order_sharp`
  §6 `error_bound_independent_of_tauOf`

  ============================================================================
  本文件消费的定理（无一条是「同义反复」——结论 `sgn ... = sgn ...` 或
  `(fun x => sgn _) = fun x => sgn _` / `‖·‖ ≤ √·` **不在**任何前件中）
  ============================================================================
  - `chain_budget_preserves_classification`：用 `error_bound_gives_correct_classification`
    + `ChainBudget.sum_first_le_budget`。
  - `link_error_preserves_classification`：用 `sum_first_le_budget` 把分量界
    `est ≤ total` 转为分量级别的决策保持（主定理 A）。
  - `learning_bound_of_chain_budget`：用 `learning_bound_general` 把预算判据
    提升到任意输入空间 `X`。
  - `chain_budget_classifier_stable`：用 `classifier_function_eq` 得到分类器**函数相等**。
  - `unit_transfer_bound_sixteenth`：用 `unit_transfer_bound` 在 `K = 1/16` 的实例。

  ⚠ 无 `sorry` / `admit` / `axiom`。
-/


namespace FateV2.Error

namespace ErrorBoundChainConsumer

open FateV2.Error.R253ErrorBound
open FateV2.Error.ChainErrorBudget

noncomputable section

/-! ===========================================================================
  §1  链预算 ⟹ 决策保持（把三段预算当误差界用）
  =========================================================================== -/

/-- **【主消费 1】链总预算保住分类决策**。

若链总预算 `B.total` 满足 `2 * B.total < |s|`，且实际扰动 `δ` 落在预算内
（`|δ| ≤ B.total`），则分类决策不变 `sgn (s+δ) = sgn s`。

**非平凡性**：前提只涉及 `B.total`、`δ`、`s` 的**数值关系**，
结论是 `sgn` 的等式 —— `sgn (s+δ) = sgn s` **不在**前件中，
须由主定理 A 的符号分析得出。 -/
theorem chain_budget_preserves_classification (B : ChainBudget) {s δ : ℝ}
    (hm : 0 < |s|) (hδ : |δ| ≤ B.total) (h2 : 2 * B.total < |s|) :
    sgn (s + δ) = sgn s :=
  error_bound_gives_correct_classification hm hδ h2

/-- **【主消费 2】单链环误差（估计环节）也保住决策**。

在预算一致 `B.consistent`、其余两环非负时，估计分量 `B.est ≤ B.total`；
若总预算满足 `2 * B.total < |s|`，则即便按**最大短板**（估计误差）计，
决策仍不变。

**非平凡性**：用 `sum_first_le_budget` 得到 `B.est ≤ B.total` 的**比较**，
再代入主定理 A；结论 `sgn (s+δ) = sgn s` 不在前件中。 -/
theorem link_error_preserves_classification (B : ChainBudget) {s δ : ℝ}
    (hc : B.consistent) (hl : 0 ≤ B.learn) (hs : 0 ≤ B.steady)
    (hm : 0 < |s|) (hδ : |δ| ≤ B.est) (h2 : 2 * B.total < |s|) :
    sgn (s + δ) = sgn s := by
  have hle : B.est ≤ B.total := ChainBudget.sum_first_le_budget hc hl hs
  have h2' : 2 * B.est < |s| := by linarith only [h2, hle]
  exact error_bound_gives_correct_classification hm hδ h2'

/-! ===========================================================================
  §2  链预算 ⟹ 一般输入空间上的逐点决策保持
  =========================================================================== -/

/-- **【主消费 3】任意输入空间上的链预算判据**。

对每点 `x` 给定标量打分 `f x`、扰动 `δ x`、预算总额 `ε x`：
若逐点 `2 * ε x < |f x|` 且 `|δ x| ≤ ε x`，则逐点决策保持。

这是把 `learning_bound_general` 用于「预算向量」`ε` 的直接消费 ——
`ε x` 可以取为每点链预算之和。 -/
theorem learning_bound_of_chain_budget {X : Type*} (f δ ε : X → ℝ)
    (hm : ∀ x, 0 < |f x|) (hδ : ∀ x, |δ x| ≤ ε x) (h2 : ∀ x, 2 * ε x < |f x|) :
    ∀ x, sgn (f x + δ x) = sgn (f x) :=
  learning_bound_general f δ ε hm hδ h2

/-- **【主消费 4】预算判据下的分类器函数稳定**：把上面提升为由 `funext` 得到的
**函数相等**：扰动后的分类器与原始分类器作为 `X → ℤ` 的映射**完全相同**。

**非平凡性**：结论是函数等式（原本需 `funext` + 逐点符号分析），
不在前件中。 -/
theorem chain_budget_classifier_stable {X : Type*} (f δ ε : X → ℝ)
    (hm : ∀ x, 0 < |f x|) (hδ : ∀ x, |δ x| ≤ ε x) (h2 : ∀ x, 2 * ε x < |f x|) :
    (fun x => sgn (f x + δ x)) = fun x => sgn (f x) :=
  classifier_function_eq f δ ε hm hδ h2

/-! ===========================================================================
  §3  几何侧：归一化转移界的消费（`K = 1/16` 实例）
  =========================================================================== -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **【主消费 5】`K = 1/16` 的归一化转移界**：两非零向量的余弦相似度
`≥ 15/16`（即 `1 - 1/16`）时，归一化距离 `≤ √(2·(1/16)) = √(1/8)`。

由 `unit_transfer_bound` 直接取 `K = 1/16`。 -/
theorem unit_transfer_bound_sixteenth (u v : E) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcos : inner ℝ u v / (‖u‖ * ‖v‖) ≥ 1 - (1/16 : ℝ)) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ≤ Real.sqrt (1/8) := by
  have h := unit_transfer_bound u v hu hv (by norm_num : (0:ℝ) ≤ 1/16) hcos
  have h2 : 2 * (1/16 : ℝ) = 1/8 := by norm_num
  rwa [h2] at h

end Euclidean

end

end ErrorBoundChainConsumer

end FateV2.Error
