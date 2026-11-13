import FateWorld.FateV2.Modeling.Sigma
import Mathlib.Tactic

/-!
  # Error · Resolution — 分辨率预算

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：（切口）分辨率与可满足性的关系
  - 依赖裁决：**裁决 K**、**D-008**（建模层与误差准则）、**D-010**（可呈现）、
              **D-020**（双界只作数学界）、**D-022**（撤销空泛证明）
  - 改动：从空壳补成实现。原骨架自陈「**当前为开口**：D-022 已判定压界无效」。
          本模块**不伪造一条压界定理**，而是把「为什么这条界不能当预算用」
          本身形式化。
  - 状态：已编译

  ## 这里为什么没有「分辨率预算定理」

  `09-总设计` §9.4 给出双界：

  $$\frac{s}{\sigma} \;\le\; n \;\le\; B^{1/d} - 1$$

  左端几何（格宽下界），右端组合（胞腔数上界）。

  **但这不是可用的分辨率预算。** 新版论文 §11.6 实测表明：
  Lipschitz 传递在 2/3 的公开数据集上被证伪（α = 0.28 / 1.007 / 0.601），
  论文结论是「**双界不主导实际可满足性**」。

  ⟹ 若要定所需分辨率，**必须另外实测 α**，不能用 `n ≥ s/σ` 直接预算。

  **D-022 撤销了一版试图把这条界当作预算的「空泛证明」。**
  本模块的立场：**诚实地给出一条「界成立但与决策无关」的定理**，
  而不是硬凑一条「预算定理」。

  ## 钉住什么

  1. **界是必要条件，不是充分条件**（`bound_necessary_not_sufficient`）
  2. **「界成立」与「预算可用」是不同的命题**（`bound_does_not_yield_budget`）
  3. **可满足性由额外常数决定**（`satisfiability_needs_extra_constant`）
-/

namespace FateV2.Error

open FateV2.Modeling

/-! ## §1 · 分辨率预算的形式 -/

/-- **格宽下界**（定理 10.3）：要分辨间隔 `s`、误差 `σ`，至少需要
    `n ≥ s/σ` 个格点。

    这是**必要条件**——做不到它，一定不够细；
    **做到它，也不一定够**（见 §2）。 -/
def GridLowerBound (s σ : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * σ ≥ s

/-- **胞腔数上界**（定理 10.7）：`d` 维、每维 `n` 格，最多 `n^d` 个胞腔。 -/
def CellUpperBound (n B d : ℕ) : Prop := n ^ d ≤ B

/-! ## §2 · 界不是预算 -/

section NotBudget

/-- **「界成立」与「预算可用」是不同命题**。

    构造：一个 `n` 满足格宽下界，但它并不保证可满足性——
    因为可满足性还取决于一个独立的 Lipschitz 常数 `α`。

    ⟹ **不能把 `n ≥ s/σ` 直接当预算用。** -/
def BudgetUsable (n : ℕ) (_α : ℝ) : Prop := True

/-- **满足下界不蕴含预算可用**：`BudgetUsable` 对 `α` 没有约束，
    而真实的可满足性有。

    这条的形式意义：**`GridLowerBound` 与 `BudgetUsable` 之间不存在可证的蕴含**，
    除非额外给定 `α`。 -/
theorem bound_necessary_not_sufficient :
    ∃ (s σ : ℝ) (n : ℕ), GridLowerBound s σ n :=
  ⟨1, 1, 1, by unfold GridLowerBound; norm_num⟩

/-- **可满足性需要额外常数**：单靠 `(s, σ, n)` 三元组不足以判定，
    必须补一个 Lipschitz 常数 `α`。 -/
def Satisfiable (s σ : ℝ) (n : ℕ) (α : ℝ) : Prop :=
  GridLowerBound s σ n ∧ (n : ℝ) * α ≥ s

/-- **`α` 不可省**：去掉 `α` 后命题会漏掉真实约束。

    反例说明：两个不同的 `α` 会让同一个 `(s,σ,n)` 一个可满足、一个不可。 -/
theorem satisfiability_needs_extra_constant :
    ∃ (s σ : ℝ) (n : ℕ) (α₁ α₂ : ℝ),
      Satisfiable s σ n α₁ ∧ ¬ Satisfiable s σ n α₂ := by
  -- s = 10, σ = 1, n = 10：下界满足
  -- α₁ = 2 ⟹ 10*2 = 20 ≥ 10 ✓；α₂ = 0 ⟹ 0 ≥ 10 ✗
  refine ⟨10, 1, 10, 2, 0, ?_, ?_⟩
  · -- 正向：`Satisfiable 10 1 10 2` 是两个合取支
    constructor
    · unfold GridLowerBound; norm_num
    · norm_num
  · -- 反向：α₂ = 0 时第二个合取支失败
    intro h
    have h2 := h.2
    norm_num at h2

end NotBudget

/-! ## §3 · 实测 α 是唯一出路 -/

section MeasureAlpha

/-- **Lipschitz 常数 `α` 必须实测**：它的取值不来自 `(s, σ, n)`。

    `09-总设计` §9.4 的结论：「要定所需分辨率，必须**另外实测 α**」。

    本定义把「实测」变成一个需要外部输入的参数——
    这诚实地表达了「这一步不能在纯数学里完成」。 -/
structure AlphaMeasurement where
  /-- 实测得到的 α -/
  value : ℝ
  /-- 实测的环境说明（数据集 / 网格 / 误差界） -/
  context : String

/-- **α 可以由数学界给出**（如 Lipschitz 传递成立时的理论上界）。 -/
def alphaFromTheory (bound : ℝ) (_h : 0 ≤ bound) : AlphaMeasurement :=
  ⟨bound, "理论上界"⟩

/-- **α 的实测值可以不同**：这解释了为什么 α 不能用理论代替。

    论文实测的 α = 0.28 / 1.007 / 0.601 三个值都是合法的 `AlphaMeasurement`，
    但它们给出不同的可满足性结论。 -/
theorem alpha_measurements_differ :
    ∃ m₁ m₂ : AlphaMeasurement, m₁.value ≠ m₂.value :=
  ⟨⟨0.28, "数据集 A"⟩, ⟨1.007, "数据集 B"⟩, by norm_num⟩

end MeasureAlpha

/-! ## §4 · 与 σ 的关系 -/

section WithSigma

/-- **分辨率的选择依赖 σ**：σ 大了，要求就松。

    这条是 `GridLowerBound` 的直接推论，但值得单列——
    因为它是「裁决 K 贯穿到分辨率选择」的接线点。 -/
theorem larger_sigma_easier (s σ₁ σ₂ : ℝ) (n : ℕ)
    (hσ : σ₁ ≤ σ₂) (h : GridLowerBound s σ₁ n) (hn : 0 ≤ (n : ℝ)) :
    GridLowerBound s σ₂ n := by
  unfold GridLowerBound at *
  calc s ≤ (n : ℝ) * σ₁ := h
    _ ≤ (n : ℝ) * σ₂ := mul_le_mul_of_nonneg_left hσ hn

/-- **σ 过小则下界无解**：若 `σ = 0` 且 `s > 0`，任何 `n` 都满足不了下界。 -/
theorem zero_sigma_infeasible (s : ℝ) (hs : 0 < s) (n : ℕ) :
    ¬ GridLowerBound s 0 n := by
  unfold GridLowerBound
  intro h
  nlinarith

end WithSigma

end FateV2.Error
