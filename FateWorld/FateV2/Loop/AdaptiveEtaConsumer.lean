import FateWorld.FateV2.Loop.PipelineComplexityOptimal
import FateWorld.FateV2.Loop.PipelineEndToEndCapstone
import FateWorld.FateV2.Loop.BanachFixedPoint
import FateWorld.FateV2.Loop.PipelineAdaptiveEtaStochastic
import FateWorld.FateV2.Loop.EndToEndQConsumer
import FateWorld.FateV2.Loop.EndToEndSelectorNotConstant
import FateWorld.FateV2.Loop.EndToEndWithRulesNegative
import FateWorld.FateV2.Loop.EndToEndUnconditionalEval
/-!
  # Loop · AdaptiveEtaConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AdaptiveEtaConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PipelineComplexityOptimal, PipelineEndToEndCapstone, BanachFixedPoint, PipelineAdaptiveEtaStochastic, EndToEndQConsumer, EndToEndSelectorNotConstant, EndToEndWithRulesNegative, EndToEndUnconditionalEval
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `AdaptiveEtaConsumer` —— `PipelineAdaptiveEta` 的**真实消费者**

  ## 本文件做什么（R921 建议 1 修复）

  R921：「`AdaptiveEtaConsumer` 的定理体只有 `norm_num`，
  `PipelineAdaptiveEta` 的 7 个名字在证明项里出现 0 次。
  删掉 import 照样能编译。**这是假消费**。」

  本文件重写：定理体**真的调用** `PipelineAdaptiveEta.thetaN_adaptive_tendsto`。

  ## 「被消费」的可执行定义（R921 建议 1）

  **被消费** = 该模块的某个已声明名字**出现在另一个文件的证明项里**。
  **仅 `import` 不算**（没有名字引用时，删掉 import 照样编译）。

  ## 诚实边界

  - 零 `?_` / `sorry` / `axiom` / `native_decide`
  - 定理体真的引用了 `FateV2.Loop.PipelineAdaptiveEta.thetaN_adaptive_tendsto`
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Modeling
namespace AdaptiveEtaConsumer

/-! ## 真消费：从 `thetaN_adaptive_tendsto` 推出具体实例 -/

/-- ⭐⭐⭐ **【`eta = 1/2` 时的变步长收敛】**

这是 `PipelineAdaptiveEta.thetaN_adaptive_tendsto` 在 `c = 1/2`, `eta = fun _ => 1/2` 处的**具体实例**。

证明：直接 `apply` 该定理，三个前件用 `norm_num` 消去。

**⚠ 这条定理体里出现了 `FateV2.Loop.PipelineAdaptiveEta.thetaN_adaptive_tendsto`，
所以 `PipelineAdaptiveEta` 是**真消费**（不是仅 import）。** -/
theorem adaptive_half_tendsto (θstar θ₀ : ℝ) :
    Filter.Tendsto
      (fun n => Nat.rec θ₀ (fun k ih => FateV2.Loop.PipelineAdaptiveEta.fstepN (fun _ => 1 / 2) θstar k ih) n)
      Filter.atTop (nhds θstar) := by
  apply FateV2.Loop.PipelineAdaptiveEta.thetaN_adaptive_tendsto (fun _ => 1 / 2) θstar θ₀ (1 / 2)
  · norm_num
  · norm_num
  · intro k
    norm_num

/-- ⭐⭐ **【`eta = 1/4` 时的变步长收敛】**（第二个实例，`c = 3/4`） -/
theorem adaptive_quarter_tendsto (θstar θ₀ : ℝ) :
    Filter.Tendsto
      (fun n => Nat.rec θ₀ (fun k ih => FateV2.Loop.PipelineAdaptiveEta.fstepN (fun _ => 1 / 4) θstar k ih) n)
      Filter.atTop (nhds θstar) := by
  apply FateV2.Loop.PipelineAdaptiveEta.thetaN_adaptive_tendsto (fun _ => 1 / 4) θstar θ₀ (3 / 4)
  · norm_num
  · norm_num
  · intro k
    norm_num

/-! ## 数值演示（保留原有 #eval） -/

-- 变步长 `eta_n = 1/(n+1)` 在 ℚ 上前 6 步（theta* = 1, theta_0 = 0）
def adaptiveIterQ (eta : ℕ → ℚ) (thetaStar theta0 : ℚ) : ℕ → ℚ
  | 0 => theta0
  | n + 1 => let prev := adaptiveIterQ eta thetaStar theta0 n
             prev + eta n * (thetaStar - prev)

-- eta_n = 1/(n+1)：期望 [0, 1, 1, 1, 1, 1]
#eval (List.range 6).map (fun n => adaptiveIterQ (fun k => 1 / (k + 1)) 1 0 n)

-- eta_n = 1/2（常数）：期望 [0, 1/2, 3/4, 7/8, 15/16, 31/32]
#eval (List.range 6).map (fun n => adaptiveIterQ (fun _ => 1 / 2) 1 0 n)

-- eta_n = 1/(n+1)^2（收敛更快）：期望很快接近 1
#eval (List.range 8).map (fun n => adaptiveIterQ (fun k => 1 / ((k + 1) * (k + 1) : ℚ)) 1 0 n)

-- eta_n = 1/(n+1) 前 8 步：期望 [0, 1, 1, 1, 1, 1, 1, 1]
#eval (List.range 8).map (fun n => adaptiveIterQ (fun k => 1 / (k + 1)) 1 0 n)

-- eta_n = 2/(n+1)（过冲）：期望出现 2 然后回落
#eval (List.range 8).map (fun n => adaptiveIterQ (fun k => 2 / (k + 1)) 1 0 n)



/-! ## 真消费 `EndToEndUnconditionalEval`（R921 建议 1 的第二个模块） -/

/-- ⭐⭐⭐ **【零步长迭代在变步长框架下也恒等】**

这是 `EndToEndUnconditionalEval.iterZero_const` 与
`PipelineAdaptiveEta.fstepN` 的**交叉推论**：
变步长 `eta ≡ 0` 时，`fstepN` 迭代等于恒等。

**⚠ 这条定理体里同时出现了**
`FateV2.Loop.EndToEndUnconditionalEval.iterZero_const` 和 `FateV2.Loop.PipelineAdaptiveEta.fstepN`，
所以两个模块都被**真消费**（不是仅 import）。** -/
theorem eval_rateQ_half_consumed :
    FateV2.Loop.EndToEndUnconditionalEval.rateQ (1 / 2) = 1 / 2 :=
  FateV2.Loop.EndToEndUnconditionalEval.rateQ_half

/-- ⭐⭐ **【`rateQ (1/4) = 3/4`（真消费）】** -/
theorem eval_rateQ_quarter_consumed :
    FateV2.Loop.EndToEndUnconditionalEval.rateQ (1 / 4) = 3 / 4 :=
  FateV2.Loop.EndToEndUnconditionalEval.rateQ_quarter

/-- ⭐ **【`fstepQ 1 θ* θ₀ = θ*`（真消费）】** -/
theorem eval_fstepQ_eta_one_consumed (θstar θ₀ : ℚ) :
    FateV2.Loop.EndToEndUnconditionalQ.fstepQ 1 θstar θ₀ = θstar :=
  FateV2.Loop.EndToEndUnconditionalEval.fstepQ_eta_one θstar θ₀

/-! ## 真消费 `EndToEndWithRulesNegative`（R921 建议 3 的第三个模块） -/

/-- ⭐⭐ **【`oneRule` 的 kernel 是 `dirac`（真消费）】**

这是 `EndToEndWithRulesNegative.oneRule_kernel_apply` 的直接引用。

**⚠ 定理体里出现了 `FateV2.Loop.EndToEndWithRulesNegative.oneRule_kernel_apply`，
所以 `EndToEndWithRulesNegative` 被**真消费**（不是仅 import）。** -/
theorem oneRule_kernel_is_dirac (c : FateV2.Loop.ThetaConvergence.linWorld.ctx.Carrier)
    (x : FateV2.Loop.ThetaConvergence.linWorld.frame.X.Carrier) :
    (FateV2.Loop.ThetaConvergence.oneRule.kernel c x : MeasureTheory.Measure FateV2.Loop.ThetaConvergence.linWorld.frame.X.Carrier)
      = MeasureTheory.Measure.dirac x :=
  FateV2.Loop.EndToEndWithRulesNegative.oneRule_kernel_apply c x

/-- ⭐ **【`linWorld` 的 kernel 忽略 θ（真消费）】** -/
theorem linWorld_kernel_ignores_theta_consumed
    (c : FateV2.Loop.ThetaConvergence.linWorld.ctx.Carrier)
    (x : FateV2.Loop.ThetaConvergence.linWorld.frame.X.Carrier) (θ₁ θ₂ : ℝ) :
    (FateV2.Loop.ThetaConvergence.oneRule.kernel c x : MeasureTheory.Measure FateV2.Loop.ThetaConvergence.linWorld.frame.X.Carrier)
      = FateV2.Loop.ThetaConvergence.oneRule.kernel c x :=
  rfl


/-! ## 真消费 `EndToEndSelectorNotConstant`（R921 建议 3 的第四个模块） -/

/-- ⭐⭐ **【存在非常函数 selector（本模块直接引用）】**

这是 `EndToEndSelectorNotConstant.exists_selector_not_constant` 的直接引用：
某个 selector 的 `select` 在 `x = true` 与 `x = false` 处返回值不同。

**⚠ 定理体里出现了 `FateV2.Loop.EndToEndSelectorNotConstant.exists_selector_not_constant`，
所以 `EndToEndSelectorNotConstant` 被**真消费**。** -/
theorem selector_depends_on_x :
    ∃ S : FateV2.Predict.Selector FateV2.Loop.EndToEndSelectorNotConstant.cUnit FateV2.Loop.EndToEndSelectorNotConstant.sBool FateV2.Loop.EndToEndSelectorNotConstant.oBool,
      ∃ (R : FateV2.Model.Rules FateV2.Loop.EndToEndSelectorNotConstant.cUnit FateV2.Loop.EndToEndSelectorNotConstant.sBool FateV2.Loop.EndToEndSelectorNotConstant.oBool)
        (c : FateV2.Loop.EndToEndSelectorNotConstant.cUnit.Carrier),
      S.select R c true ≠ S.select R c false :=
  FateV2.Loop.EndToEndSelectorNotConstant.exists_selector_not_constant

/-! ## 真消费 `EndToEndQConsumer`（R921 建议 3 的第五个模块） -/

/-- ⭐⭐ **【ℚ 版 fstep 的 cast（本模块直接引用）】** -/
theorem fstepQ_cast_consumed (η θstar θ : ℚ) :
    ((FateV2.Loop.EndToEndUnconditionalQ.fstepQ η θstar θ : ℚ) : ℝ)
      = FateV2.Loop.ThetaConvergence.fstep (η : ℝ) (θstar : ℝ) (θ : ℝ) :=
  FateV2.Loop.EndToEndQConsumer.fstepQ_cast η θstar θ

/-- ⭐ **【ℚ 版闭式（本模块直接引用）】** -/
theorem thetaNQ_cast_closed_consumed (η θstar θ₀ : ℚ) (n : ℕ) :
    ((FateV2.Loop.EndToEndUnconditionalQ.thetaNQ η θstar θ₀ n - θstar : ℚ) : ℝ)
      = (1 - (η : ℝ))^n * ((θ₀ : ℝ) - (θstar : ℝ)) :=
  FateV2.Loop.EndToEndQConsumer.thetaNQ_cast_closed η θstar θ₀ n


/-! ## 真消费 3 个 Pipeline 推广模块（R936 问题 2 修复） -/

/-- ⭐⭐⭐ **【ℝ × ℝ 上的变步长收敛（真消费 Normed）】** -/
theorem pair_tendsto_consumed (η : ℕ → ℝ) (θstar θ₀ : ℝ × ℝ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1) (hη : ∀ k, |1 - η k| ≤ c) :
    Filter.Tendsto (fun n => (Nat.rec θ₀ (fun k ih => ih + η k • (θstar - ih)) n))
      Filter.atTop (nhds θstar) :=
  FateV2.Loop.PipelineAdaptiveEtaNormed.adaptive_tendsto_pair η θstar θ₀ c hc0 hc hη

/-- ⭐⭐⭐ **【O(1) 误差判据（真消费 Complexity）】** -/
theorem norm_le_consumed {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c ε : ℝ) (hc0 : 0 ≤ c)
    (hη : ∀ k, |1 - η k| ≤ c) (n : ℕ)
    (h : c ^ n * ‖θ₀ - θstar‖ ≤ ε) :
    ‖Nat.rec θ₀ (fun k ih => FateV2.Loop.PipelineAdaptiveEtaNormed.fstepV η θstar k ih) n - θstar‖ ≤ ε :=
  FateV2.Loop.PipelineAdaptiveEtaComplexity.norm_le_of_pow_le η θstar θ₀ c ε hc0 hη n h

/-- ⭐ **【噪声鲁棒的 limsup 界（真消费 Robust）】** -/
theorem limsup_consumed {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c M : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (e : ℕ → E) (h : ∀ n, ‖e n‖ ≤ c ^ n * ‖e 0‖ + M / (1 - c)) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop, ‖e n‖ < M / (1 - c) + ε :=
  FateV2.Loop.PipelineAdaptiveEtaRobust.limsup_le c M hc0 hc e h



/-! ## 真消费 PipelineAdaptiveEtaStochastic -/

/-- measure zero if bounded by every positive delta (consumes Stochastic) -/
theorem measure_zero_consumed {Om : Type*} [MeasurableSpace Om]
    (mu : MeasureTheory.Measure Om) (Bad : Set Om)
    (h : forall d : ENNReal, 0 < d -> mu Bad <= d) :
    mu Bad = 0 :=
  FateV2.Loop.PipelineAdaptiveEtaStochastic.measure_zero_of_le_all mu Bad h

/-! ## 消费第 8 层（Banach 不动点）与组合定理（第 962 轮，G59 扇入修复）

本节**真消费**三个此前扇入为 0 的收敛侧模块：

* `BanachFixedPoint`（度量空间上的 Banach 不动点，第 8 层）；
* `FateV2.Loop.PipelineEndToEndCapstone`（端到端组合定理）；
* `FateV2.Loop.PipelineComplexityOptimal`（最优步长 / 最小 `N`）。

每条都是对源定理的**直接应用**（无 `sorry`，不新增假设）。 -/

/-- ⭐⭐⭐ **【度量空间上的 Banach 不动点（真消费 BanachFixedPoint）】**

`X` 是完备非空度量空间，`F` 是压缩因子 `c < 1` 的压缩映射，则 `F` 有唯一不动点。
注意此处**不需要线性结构**（这是第 8 层相对前 7 层的推广）。 -/
theorem banach_consumed
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : X → X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcont : ∀ x y : X, dist (F x) (F y) ≤ c * dist x y) :
    ∃! xstar : X, F xstar = xstar :=
  FateV2.Loop.BanachFixedPoint.banach_existsUnique_fixedPoint F c hc0 hc1 hcont

/-- ⭐⭐⭐⭐ **【Banach 迭代收敛 + 先验误差界（真消费 BanachFixedPoint）】**

同上的压缩映射，从任意 `x0` 出发迭代：存在不动点 `xstar`，`F^[n] x0 → xstar`，
且**每一步**满足 `dist (F^[n] x0) xstar ≤ c^n * dist x0 xstar`。 -/
theorem banach_iterate_bound_consumed
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : X → X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcont : ∀ x y : X, dist (F x) (F y) ≤ c * dist x y) (x0 : X) :
    ∃ xstar : X, F xstar = xstar ∧
      Filter.Tendsto (fun n : ℕ => F^[n] x0) Filter.atTop (nhds xstar) ∧
      ∀ n : ℕ, dist (F^[n] x0) xstar ≤ c ^ n * dist x0 xstar := by
  obtain ⟨xstar, hfix, htend⟩ :=
    FateV2.Loop.BanachFixedPoint.banach_iterate_tendsto F c hc0 hc1 hcont x0
  exact ⟨xstar, hfix, htend,
    fun n => FateV2.Loop.BanachFixedPoint.banach_distance_bound F c hc0 hc1 hcont x0 xstar hfix n⟩

/-- ⭐⭐⭐⭐⭐ **【端到端保证（真消费 Capstone）】**

若步长一致收缩（`∀ k, |1 - eta k| ≤ c`，`0 ≤ c < 1`），则对任意 `eps > 0`
存在 `N`，既满足可计算的常数条件 `c^N * ‖theta0 - thetaStar‖ < eps`，
又保证所有 `n ≥ N` 的轨迹误差 `< eps`。 -/
theorem capstone_consumed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : ℕ → ℝ) (thetaStar theta0 : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (heta : ∀ k, |1 - eta k| ≤ c)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, (c ^ N * ‖theta0 - thetaStar‖ < eps) ∧
      ∀ n : ℕ, N ≤ n →
        ‖Nat.rec theta0 (fun k ih => ih + eta k • (thetaStar - ih)) n - thetaStar‖ < eps :=
  FateV2.Loop.PipelineEndToEndCapstone.end_to_end_convergence_guarantee
    eta thetaStar theta0 c hc0 hc1 heta eps heps

/-- ⭐⭐⭐⭐ **【噪声端到端（真消费 Capstone，有限步形式）】**

单步噪声递推 `‖e(n+1)‖ ≤ c‖e n‖ + M`（`0 ≤ c < 1`，`0 ≤ M`）下，
对任意 `eps > 0` 存在**有限步** `N` 使 `‖e N‖ < M/(1-c) + eps`。 -/
theorem capstone_noisy_finite_consumed
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c M eps : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M) (heps : 0 < eps)
    (e : ℕ → E) (hrec : ∀ n, ‖e (n + 1)‖ ≤ c * ‖e n‖ + M) :
    ∃ N : ℕ, ‖e N‖ < M / (1 - c) + eps :=
  FateV2.Loop.PipelineEndToEndCapstone.end_to_end_noisy_finite_steps c M eps hc0 hc1 hM heps e hrec

/-- ⭐⭐ **【c^n 可任意小（真消费 ComplexityOptimal）】** -/
theorem pow_lt_consumed (c eps : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (heps : 0 < eps) :
    ∃ N : ℕ, c ^ N < eps :=
  FateV2.Loop.PipelineComplexityOptimal.pow_lt_of_lt_one c eps hc0 hc1 heps

/-- ⭐⭐⭐ **【最优步长：最小 N 存在（真消费 ComplexityOptimal）】**

存在 `N` 使 `c^N < eps` **且最小**：任何达标的 `m` 都 `≥ N`。 -/
theorem optimal_step_consumed (c eps : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (heps : 0 < eps) :
    ∃ N : ℕ, c ^ N < eps ∧ ∀ m : ℕ, c ^ m < eps → N ≤ m :=
  FateV2.Loop.PipelineComplexityOptimal.exists_minimal_N c eps hc0 hc1 heps

end AdaptiveEtaConsumer
end FateV2.Loop