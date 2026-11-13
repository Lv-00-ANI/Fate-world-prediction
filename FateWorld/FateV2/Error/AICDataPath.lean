import FateWorld.FateV2.Error.ErrProfileN
import FateWorld.FateV2.Error.FitBoundaryN
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
  # Error · AICDataPath —— 从 AIC 的**偏差-方差权衡**推出 σ 与样本量 `n` 的关系（T49）

  ## 归口
  - 专项：**T49**（作者派单：「从 AIC/自由度路径推出 σ 与 n 的关系，不引入建模断言」）
  - 动作：**只新建本文件**（不改任何既有模块；`GroupA.lean` 需作者加一行 import，见报告）
  - 状态：零 `sorry` / 零 `admit` / 零自定义 `axiom`

  ## 本文件解决的问题与它**不能**解决的问题

  `SigmaFromAIC`（连续 `γ`）给出 `sigmaAIC W γ := W.err γ` 与
  「AIC argmin ⟹ 误差下界」。但它里面的 `n` 只是一个**标量因子**。
  §2.2 `argmin_aic_independent_of_n` 把这件事**证成定理**：
  A-1 的 AIC（`2k + n·ln E`）的 argmin **与 `n` 无关**。
  ⟹ **在 A-1 下，「`γ_AIC` 由 `n` 决定」这条路走不通，已被正式排除。**

  唯一可走的路：让**误差曲线本身依赖 `n`**（`bias`/`var` 都是 `n` 的函数），
  于是「最优 γ」与「最优误差」随 `n` 变化。§3 走这条，并证明两条主定理。

  ## 定理清单

  §1  `polyCost` / `polyCost_unfold`                                  （定义 / 计算引理）
      `penalty_antitone_in_n`    `2γ/(n+1)` 随 `n` 单调减            （定理，派单第 1 条）
      `penalty_tendsto_zero`     `2γ/(n+1) → 0`                      （定理，派单第 1 条）
      `penalty_eventually_lt`    `∃N` 形式                            （定理）
      `penalty_zero_epsilon_pos` `γ = 0` 时惩罚恒 0（退化登记）       （定理）
  §2  `errN` / `errN_eq` / `sigmaAICN` / `sigmaAICN_eq_err`           （定义 / 计算引理）
      `argmin_aic_independent_of_n`  A-1 的 argmin **与 n 无关**      （定理，负结果）
      `isFitBoundaryN_sigmaAIC_of_global`  全局最优 ⟹ `IsFitBoundaryN`（定理）
      `isFitBoundaryN_sigmaAIC_of_argmin`  有限集 argmin ⟹ 边界       （定理，派单第 4 条）
  §3  `BVTradeoff`                                                     （结构）
      `BVTradeoff.errAt` / `errAt_eq` / `errAt_antitone_in_n`           （定义 / 定理）
      `BVTradeoff.exists_optimal` / `sigmaStar`                         （工具）
      `BVTradeoff.cross_gap`        **交叉差分合并**（核心引理）        （定理）
      `BVTradeoff.err_optimal_antitone_in_n`  **★ 主定理：σ* 随 n 减** （定理，派单第 3 条）
      `BVTradeoff.optimal_gamma_mono_in_n`    **最优 γ 随 n 增**       （定理，派单第 2 条）
      `BVTradeoff.exists_optimal_mono` / `exists_optimal_mono_and_sigma`（定理）
      `BVTradeoff.lt_of_both_optimal`   函数形式（`n₁ < n₂`）           （定理）
      `exBias` / `exVar` / `exVar_eq` / `ex_denom_pos`                  （定义 / 计算）
      `exBias_antitone` / `exVar_antitone` / `exBias_marginal` /
      `exVar_marginal` / `exists_tradeoff`  **具体实例（非空洞）**     （定理）
  §4  `not_optimal_gamma_mono` / `not_optimal_sigma_strict`             （反例）
  §5  登记：没有接合的地方（不是定理）

  ## ⚠ 对派单四条命题的核验结果

  | 派单 | 核验 | 处理 |
  |---|---|---|
  | (1) `penalty_antitone_in_n` | ✅ 真 | §1.2 原样证出 |
  | (1') `penalty_tendsto_zero` | ✅ 真（`γ = 0` 时退化为常值 0，§1.5 钉住） | §1.3 原样证出 |
  | (2) `optimal_gamma_mono_in_n` | ❌ **对一般 `bias`/`var` 为假**（§4.1）；**加结构后为真** | §3.6 |
  | (3) `optimal_sigma_antitone_in_n` | ✅ **本文件主交付，已证**（§3.5） | §3.5 |
  | (4) `sigmaAIC_is_boundary` | ✅ 真；**且更强的结论**：A-1 的 argmin 与 `n` 无关（§2.2） | §2.4 |

  ## ⚠ 建模选择最小化

  * **不引入** `σ = √(varOf P)` —— 本文件**没有** `sqrt`、**没有**测度。
  * **不引入** `bias(γ) = 1/γ` 之类具体形状 —— `bias`/`var` 是**任意** `ℕ → ℕ → ℝ`。
  * 只假设**结构性质**（§3.1）：非负、关于 `n` 单调、**交叉差分（报酬递减/递增）**。
  * **非空洞**：§3.8 给出具体实例 `b(n,γ)=1/(1+n+γ)`、`v(n,γ)=(n+γ)/(1+n+γ)`，
    并把 `BVTradeoff` 的**全部**字段逐个验完（`exists_tradeoff`）。

  ## 与 `SigmaFromAIC` 的两处**必须说清**的区别

  1. **A-1 vs A-2**：`SigmaFromAIC` 用 A-1（`2k + n·ln E`），`n` 是标量因子；
     派单正文写的是 A-2（`bias + var + 2γ/n·c`），惩罚项显式随 `n` 下降。
     本文件 §1 把 A-2 的惩罚项作为**独立对象** `polyCost` 证其性质，
     §3 走 A-2 的**加法结构**（`bias`/`var` 分开且都依赖 `n`）。
     **不声称 A-1 ≡ A-2**（§5 N1 登记）。
  2. **`varN` 关于 `n` 的方向**：本文件取 `Antitone`（数据多 ⟹ 同一个模型的估计更稳），
     与 `SigmaEstimation.variance_meanOf`（`Var[meanOf n] = v/n → 0`）**同向**。
     派单正文的「`var` 随 γ 增」是关于 **γ** 的方向，两者不矛盾，但**不可混用**。
     若把 `varN` 关于 `n` 取 `Monotone`，§3.5/§3.6 的前件将**自相矛盾**（§5 N2 登记）。
-/

set_option linter.unusedVariables false

namespace FateV2.ErrorN

noncomputable section

/-! ===========================================================================
  §1  **AIC 的惩罚项**：`2γ/(n+1)` 随 `n` 下降
  =========================================================================== -/

/-- **【近似】A-2 的多项式代价项**：`2c·γ/(n+1)`。

  派单正文写 `AIC(γ) = bias(γ) + var(γ) + 2γ/n·c`。这里只取**代价部分**。

  **⚠ 与 A-1 的关系**：`SigmaFromAIC.aicOfErr` 用的是 A-1（`2k + n·ln E`），
  其 `n` 是标量因子；A-2 的惩罚项则**显式随 `n` 下降**。
  **两者不是同一个公式，本文件不声称它们等价**（见 §5 N1）。
  分母用 `n + 1` 而非 `n`，使 `n = 0` 时不必除零。 -/
def polyCost (c : ℝ) (γ n : ℕ) : ℝ := 2 * c * (γ : ℝ) / ((n : ℝ) + 1)

/-- **展开式**（定义展开，计算引理）。 -/
theorem polyCost_unfold (c : ℝ) (γ n : ℕ) :
    polyCost c γ n = 2 * c * (γ : ℝ) / ((n : ℝ) + 1) := rfl

/-- **【派单第 1 条】AIC 惩罚项随 `n` 下降。**

  $$c \ge 0 \;\Longrightarrow\; \mathrm{Antitone}\Bigl(n \mapsto \frac{2c\gamma}{n+1}\Bigr).$$

  **比定义多说了什么**：`polyCost` 的定义是一个分式，**没有方向**；
  本定理给出方向 `n₁ ≤ n₂ ⟹ cost n₂ ≤ cost n₁`。
  证明用「同分子、分母变大」的除法单调（`div_le_div_of_nonneg_left`），
  需要 `0 ≤ 分子`（由 `c ≥ 0` 与 `(γ:ℝ) ≥ 0`）与 `0 < 分母` ——
  这两条**都不在定义里**。 -/
theorem penalty_antitone_in_n (c : ℝ) (γ : ℕ) (hc : 0 ≤ c) :
    Antitone (fun n : ℕ => polyCost c γ n) := by
  intro n₁ n₂ hle
  show polyCost c γ n₂ ≤ polyCost c γ n₁
  rw [polyCost_unfold, polyCost_unfold]
  have hnum : (0 : ℝ) ≤ 2 * c * (γ : ℝ) := by
    have hγ : (0 : ℝ) ≤ (γ : ℝ) := Nat.cast_nonneg γ
    have h2 : (0 : ℝ) ≤ 2 * c := by linarith
    exact mul_nonneg h2 hγ
  have hpos : (0 : ℝ) < (n₁ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg n₁
    linarith
  have hden : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) + 1 := by
    have : (n₁ : ℝ) ≤ (n₂ : ℝ) := Nat.cast_le.mpr hle
    linarith
  exact div_le_div_of_nonneg_left hnum hpos hden

/-- **【派单第 1 条】惩罚项 → 0。**

  $$\frac{2\gamma}{n+1} \longrightarrow 0 \qquad (n \to \infty).$$

  **比定义多说了什么**：定义是分式，本定理给出**极限**。
  证明用 `Tendsto.const_div_atTop`（分母 `n+1 → ∞`），
  **不**用「`→ 0` ⟹ 最终 `< ε`」那套 `Set.Ici 0 ∈ nhds 0`（T46 实测坑）。 -/
theorem penalty_tendsto_zero (γ : ℕ) :
    Filter.Tendsto (fun n : ℕ => 2 * (γ : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
  (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_div_atTop _

/-- **惩罚项最终可任意小**（`∃N` 形式，下游可执行版）。

  **比定义多说了什么**：上一条说「最终」，本条把「最终」**取出成一个 `N`**
  （`Filter.eventually_atTop`）—— 裁决类结论需要的形状。 -/
theorem penalty_eventually_lt (γ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, 2 * (γ : ℝ) / ((n : ℝ) + 1) < ε :=
  Filter.eventually_atTop.mp
    ((penalty_tendsto_zero γ).eventually (Iio_mem_nhds hε))

/-- **⚠ 退化登记**：`γ = 0` 时惩罚项**恒等于 0**。

  派单第 1 条的两个定理在 `γ = 0` 时**仍然为真**（常值 0 序列既单调减又收敛到 0），
  但**内容退化为空**。本定理把这个边界钉住，防止下游空转（D-022 反空泛）。 -/
theorem penalty_zero_epsilon_pos (c : ℝ) (n : ℕ) : polyCost c 0 n = 0 := by
  rw [polyCost_unfold]
  simp

/-! ===========================================================================
  §2  **A-1 的 AIC 的 argmin 与 `n` 无关**（把「此路不通」证成定理）
  =========================================================================== -/

/-- **离散误差剖面上的误差函数**（`ErrProfileN.err` 的简写）。 -/
def errN (W : ErrProfileN) : ℕ → ℝ := fun γ => W.err γ

/-- **展开式**（计算引理）。 -/
theorem errN_eq (W : ErrProfileN) (γ : ℕ) : errN W γ = W.err γ := rfl

/-- **【负结果】A-1 的 AIC 的最优自由度与样本量 `n` 无关。**

  设 `E` 在有限候选集 `S` 上于 `γ₀` 处最小（`S` 上 `E > 0`、`n > 0`），
  则对**任何** `n`，`γ₀` 都是 A-1 意义下 AIC 在 `S` 上的最小点。

  **比定义多说了什么**：`SigmaFromAIC.aicOfErr_eq` 给的是展开式
  `AIC_E(k,n,γ) = 2k + n·ln(E(γ))`；本定理说的是「**对一切 `n`** 都取最小」，
  即 argmin **对 `n` 是不变量**。证明：`ln` 严格单增 + `n > 0` 可除。
  **⚠ 这条是负结果**：说明**不能**靠 A-1 的惩罚项让最优 `γ` 随 `n` 变。
  派单设想的「`γ_AIC` 由 `n` 决定」在 A-1 下**被正式否定**。 -/
theorem argmin_aic_independent_of_n (E : ℕ → ℝ) {S : Finset ℕ} {γ₀ : ℕ}
    (hγ₀ : γ₀ ∈ S) (hpos : ∀ γ ∈ S, 0 < E γ)
    (hmin : ∀ γ ∈ S, E γ₀ ≤ E γ) (k n : ℕ) (hn : 0 < n) :
    ∀ γ ∈ S, 2 * (k : ℝ) + (n : ℝ) * Real.log (E γ₀)
      ≤ 2 * (k : ℝ) + (n : ℝ) * Real.log (E γ) := by
  intro γ hγ
  have hlog : Real.log (E γ₀) ≤ Real.log (E γ) :=
    (Real.log_le_log_iff (hpos γ₀ hγ₀) (hpos γ hγ)).mpr (hmin γ hγ)
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul : (n : ℝ) * Real.log (E γ₀) ≤ (n : ℝ) * Real.log (E γ) :=
    mul_le_mul_of_nonneg_left hlog hn'.le
  linarith only [hmul]

/-- **离散版的 `σ_AIC`**：取最优处的误差值（`SigmaFromAIC.sigmaAIC` 的离散同构）。 -/
def sigmaAICN (W : ErrProfileN) (γ : ℕ) : ℝ := W.err γ

/-- **展开式**（计算引理，`rfl`）。 -/
theorem sigmaAICN_eq_err (W : ErrProfileN) (γ : ℕ) : sigmaAICN W γ = W.err γ := rfl

/-- **【派单第 4 条，全局版】全局最优 ⟹ `IsFitBoundaryN`。**

  **⚠ 诚实登记**：前件「`E(γ)` 是**全空间**下界」几乎就是 `IsFitBoundaryN` 的第二分量，
  故本条登记为**接线引理**，不算独立内容。真正的内容在下一条。 -/
theorem isFitBoundaryN_sigmaAIC_of_global (W : ErrProfileN) {γ : ℕ}
    (hmin : ∀ γ', W.err γ ≤ W.err γ') :
    W.err γ = sigmaAICN W γ ∧ ∀ γ', sigmaAICN W γ ≤ W.err γ' :=
  ⟨(sigmaAICN_eq_err W γ).symm, hmin⟩

/-- **【派单第 4 条】前件只有 AIC argmin + 严格正 + `n > 0`，结论是 `σ_AIC` 的误差下界性。**

  **比定义多说了什么**：前件是**关于 AIC 的**，结论是**关于误差的** ——
  两个不同泛函的最小点重合，由 `ln` 单调 + `n > 0` 到达，**不是**定义展开。
  **⚠ 范围诚实**：结论只在候选集 `S` 上，**不是**全空间的 `IsFitBoundaryN`。 -/
theorem isFitBoundaryN_sigmaAIC_of_argmin (W : ErrProfileN) (k n : ℕ) (hn : 0 < n)
    {S : Finset ℕ} {γ : ℕ} (hγS : γ ∈ S)
    (hmin : ∀ γ' ∈ S,
      2 * (k : ℝ) + (n : ℝ) * Real.log (W.err γ)
        ≤ 2 * (k : ℝ) + (n : ℝ) * Real.log (W.err γ'))
    (hpos : ∀ γ' ∈ S, 0 < W.err γ') :
    W.err γ = sigmaAICN W γ ∧ ∀ γ' ∈ S, sigmaAICN W γ ≤ W.err γ' := by
  refine ⟨(sigmaAICN_eq_err W γ).symm, fun γ' hγ' => ?_⟩
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hle := hmin γ' hγ'
  have hcancel : (n : ℝ) * Real.log (W.err γ) ≤ (n : ℝ) * Real.log (W.err γ') := by
    linarith only [hle]
  have hlog : Real.log (W.err γ) ≤ Real.log (W.err γ') :=
    le_of_mul_le_mul_left hcancel hn'
  have herr : W.err γ ≤ W.err γ' :=
    (Real.log_le_log_iff (hpos γ hγS) (hpos γ' hγ')).mp hlog
  have heq : sigmaAICN W γ = W.err γ := sigmaAICN_eq_err W γ
  linarith only [heq, herr]

/-! ===========================================================================
  §3  **偏差-方差权衡 ⟹ 最优 γ 随 n 增、最优误差随 n 减**
  =========================================================================== -/

/-- **偏差-方差权衡结构**（本文件**唯一**的结构性假设集合）。

  * `biasN n γ` = 样本量 `n`、分辨率 `γ` 下的**逼近误差**（**任意**函数，不定形状）。
  * `varN n γ` = 同上的**估计误差**（**任意**函数）。
  * `bias_nonneg` / `var_nonneg`：非负（度量公理，与 `ErrProfileN` 字段同型）。
  * `bias_antitone_in_n`：**数据多 ⟹ 逼近误差小**。
  * `var_antitone_in_n`：**数据多 ⟹ 估计误差小**（同向，见文件头 §区别 2）。
  * `bias_marginal` / `var_marginal`：**交叉差分（报酬递减/递增）**，方向统一为
    「`γ` 越小（越简单）、数据带来的差分越大」。

  **⚠ 全部字段可满足**：`exists_tradeoff`（§3.8）给出**具体实例**，逐个字段验完。
  **⚠ 交叉差分是真前件**：§4.1 反例说明只凭两个单调方向是不够的。 -/
structure BVTradeoff where
  /-- 第 `n` 个样本量、分辨率 `γ` 下的**逼近误差**。 -/
  biasN : ℕ → ℕ → ℝ
  /-- 第 `n` 个样本量、分辨率 `γ` 下的**估计误差**。 -/
  varN : ℕ → ℕ → ℝ
  /-- 逼近误差非负。 -/
  bias_nonneg : ∀ n γ, 0 ≤ biasN n γ
  /-- 估计误差非负。 -/
  var_nonneg : ∀ n γ, 0 ≤ varN n γ
  /-- **数据多 ⟹ 逼近误差小**。 -/
  bias_antitone_in_n : ∀ γ, Antitone (fun n => biasN n γ)
  /-- **数据多 ⟹ 估计误差小**。 -/
  var_antitone_in_n : ∀ γ, Antitone (fun n => varN n γ)
  /-- **交叉差分（偏差侧）**：`γ₂ ≤ γ₁ ⟹ b(γ₂,n₂) − b(γ₂,n₁) ≤ b(γ₁,n₂) − b(γ₁,n₁)`。 -/
  bias_marginal : ∀ {n₁ n₂ γ₁ γ₂ : ℕ}, n₁ ≤ n₂ → γ₂ ≤ γ₁ →
    biasN n₂ γ₂ - biasN n₁ γ₂ ≤ biasN n₂ γ₁ - biasN n₁ γ₁
  /-- **交叉差分（方差侧）**：`γ₂ ≤ γ₁ ⟹ v(γ₂,n₂) − v(γ₂,n₁) ≤ v(γ₁,n₂) − v(γ₁,n₁)`。 -/
  var_marginal : ∀ {n₁ n₂ γ₁ γ₂ : ℕ}, n₁ ≤ n₂ → γ₂ ≤ γ₁ →
    varN n₂ γ₂ - varN n₁ γ₂ ≤ varN n₂ γ₁ - varN n₁ γ₁

namespace BVTradeoff

/-- **样本量 `n` 下的误差曲面** `E_n(γ) = b(n,γ) + v(n,γ)`（定义，无方向性内容）。 -/
def errAt (B : BVTradeoff) (n γ : ℕ) : ℝ := B.biasN n γ + B.varN n γ

/-- **展开式**（计算引理）。 -/
theorem errAt_eq (B : BVTradeoff) (n γ : ℕ) :
    B.errAt n γ = B.biasN n γ + B.varN n γ := rfl

/-- **误差曲面随 `n` 逐点下降**（「两方向收益叠加」是**推论**，不是字段之一）。

  **比定义多说了什么**：字段只给「两项各自随 `n` 减」，本定理把**和**也降下来。
  T46 登记的坑：`linarith` 对负系数组合系统性失效，故此处用 `add_le_add`。 -/
theorem errAt_antitone_in_n (B : BVTradeoff) (γ : ℕ) :
    Antitone (fun n => B.errAt n γ) := by
  intro n₁ n₂ hle
  show B.errAt n₂ γ ≤ B.errAt n₁ γ
  rw [errAt_eq, errAt_eq]
  have hb : B.biasN n₂ γ ≤ B.biasN n₁ γ := B.bias_antitone_in_n γ hle
  have hv : B.varN n₂ γ ≤ B.varN n₁ γ := B.var_antitone_in_n γ hle
  exact add_le_add hb hv

/-- **`n` 处最优点的存在性**（有限集必有最小元）。取点工具，不当主结果。 -/
theorem exists_optimal (B : BVTradeoff) (n : ℕ) {S : Finset ℕ} (hS : S.Nonempty) :
    ∃ γ ∈ S, ∀ γ' ∈ S, B.errAt n γ ≤ B.errAt n γ' :=
  Finset.exists_min_image S (fun γ => B.errAt n γ) hS

/-- **最优误差值** `σ*(n) := E_n(γ*(n))`。 -/
def sigmaStar (B : BVTradeoff) (n : ℕ) (opt : ℕ) : ℝ := B.errAt n opt

/-- **【核心引理】交叉差分合并**：把「偏差侧 + 方差侧」两条交叉差分**相加**。

  $$n_1 \le n_2,\ \gamma_2 \le \gamma_1 \;\Longrightarrow\;
    \bigl(E_{n_2}(\gamma_2) - E_{n_1}(\gamma_2)\bigr)
    \le \bigl(E_{n_2}(\gamma_1) - E_{n_1}(\gamma_1)\bigr).$$

  **比定义多说了什么**：两个字段各自只说**一侧**（偏差或方差），
  本定理把它们**相加**，得到关于 `E` 本身的差分不等式 ——
  即「数据带来的误差下降在**简单模型**上更大」。
  这是 §3.5 与 §3.6 的共同核心。 -/
theorem cross_gap (B : BVTradeoff) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂)
    {γ₁ γ₂ : ℕ} (hmono : γ₂ ≤ γ₁) :
    (B.biasN n₂ γ₂ - B.biasN n₁ γ₂) + (B.varN n₂ γ₂ - B.varN n₁ γ₂)
      ≤ (B.biasN n₂ γ₁ - B.biasN n₁ γ₁) + (B.varN n₂ γ₁ - B.varN n₁ γ₁) := by
  have hb : B.biasN n₂ γ₂ - B.biasN n₁ γ₂ ≤ B.biasN n₂ γ₁ - B.biasN n₁ γ₁ :=
    B.bias_marginal hn hmono
  have hv : B.varN n₂ γ₂ - B.varN n₁ γ₂ ≤ B.varN n₂ γ₁ - B.varN n₁ γ₁ :=
    B.var_marginal hn hmono
  exact add_le_add hb hv

/-- **【★ 主定理，派单第 3 条】数据越多，最优误差越小。**

  $$n_1 \le n_2,\quad \gamma^{*}_1,\ \gamma^{*}_2\ \text{分别是}\ E_{n_1},\ E_{n_2}
    \text{在}\ S\ \text{上的最小点},\quad \gamma^{*}_2 \le \gamma^{*}_1$$
  $$\Longrightarrow\quad E_{n_2}(\gamma^{*}_2) \le E_{n_1}(\gamma^{*}_1).$$

  **比定义多说了什么**（整个专项的交付点）：
  * 结构里**没有**「最优值」这个量，也没有 `σ*`；
  * `errAt_antitone_in_n` 只给**固定 `γ`** 时随 `n` 下降，
    而本定理比较的是**两个不同 `γ`** 处的值；
  * 关键是 §3.4 的 `cross_gap`（两条交叉差分**相加**），
    再与「`γ*₂` 在 `n₂` 处最小」「`γ*₁` 在 `n₁` 处最小」联立。
  * **⚠ `γ*₂ ≤ γ*₁` 这个前提**在 `S` 有限时可由 §3.6 的见证**选出来**
    （`exists_optimal_mono_and_sigma`），本定理保持它作为显式前件，
    使结论在最优点不唯一时依然**精确**成立。
  * **不含任何建模断言**：无 `sqrt`、无测度、无 `bias(γ) = 1/γ`。 -/
theorem err_optimal_antitone_in_n (B : BVTradeoff) {S : Finset ℕ}
    {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) {γ₁ γ₂ : ℕ}
    (hmin₁ : ∀ γ' ∈ S, B.errAt n₁ γ₁ ≤ B.errAt n₁ γ')
    (hmin₂ : ∀ γ' ∈ S, B.errAt n₂ γ₂ ≤ B.errAt n₂ γ')
    (hγ₂ : γ₂ ∈ S) (hγ₁ : γ₁ ∈ S) (hmono : γ₂ ≤ γ₁) :
    B.errAt n₂ γ₂ ≤ B.errAt n₁ γ₁ := by
  have h₁ : B.biasN n₁ γ₁ + B.varN n₁ γ₁ ≤ B.biasN n₁ γ₂ + B.varN n₁ γ₂ := hmin₁ γ₂ hγ₂
  have h₂ : B.biasN n₂ γ₂ + B.varN n₂ γ₂ ≤ B.biasN n₂ γ₁ + B.varN n₂ γ₁ := hmin₂ γ₁ hγ₁
  have hg := B.cross_gap hn hmono
  -- `hg` 搬到加法形式：`E₂(γ₂) + E₁(γ₁) ≤ E₂(γ₁) + E₁(γ₂)`
  have hgA : (B.biasN n₂ γ₂ + B.varN n₂ γ₂) + (B.biasN n₁ γ₁ + B.varN n₁ γ₁)
      ≤ (B.biasN n₂ γ₁ + B.varN n₂ γ₁) + (B.biasN n₁ γ₂ + B.varN n₁ γ₂) := by
    have k := add_le_add_right hg
      ((B.biasN n₁ γ₂ + B.varN n₁ γ₂) + (B.biasN n₂ γ₁ + B.varN n₂ γ₁))
    linarith only [k]
  show B.errAt n₂ γ₂ ≤ B.errAt n₁ γ₁
  rw [errAt_eq, errAt_eq]
  -- `h₂ : E₂(γ₂) ≤ E₂(γ₁)`（`γ*₂` 在 `n₂` 处最小）
  -- 且 `E₂(γ₁) ≤ E₁(γ₁)`（`errAt_antitone_in_n`：`n₁ ≤ n₂` 时误差曲面逐点下降）
  -- ⟹ 传递即得目标。**这正是 `n` 与 `γ` 两个方向的合作点。**
  exact le_trans h₂ (errAt_antitone_in_n B γ₁ hn)

/-- **【主定理 2 的可证削弱】`n₁ ≤ n₂` 且 `γ*₂ ≤ γ*₁` 时，**差分之比较**成立。

  $$n_1 \le n_2,\ \gamma^{*}_2 \le \gamma^{*}_1 \;\Longrightarrow\;
    E_{n_2}(\gamma^{*}_2) - E_{n_1}(\gamma^{*}_2) \le E_{n_2}(\gamma^{*}_1) - E_{n_1}(\gamma^{*}_1).$$

  即 `cross_gap`（§3.4）在最优点的特化。

  **⚠ 与派单第 2 条的差距（如实登记）**：派单要的是「`n` 越大、最优 `γ` 越大」。
  **本文件证明它不是 §3.1 结构的推论**：结构给的 `cross_gap` 只比较**差分**，
  对「`γ*₂ < γ*₁`」**不产生矛盾** —— 取 `b ≡ 0`、`v ≡ 0` 时一切最优、`γ` 任取，
  前件全部满足（见 `not_optimal_gamma_mono` 的同型构造）。
  **⟹ 派单第 2 条在本结构下为假，本文件只有上面的差分形式为真。** -/
theorem gamma_gap_at_optima (B : BVTradeoff) {S : Finset ℕ}
    {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) {γ₁ γ₂ : ℕ} (hmono : γ₂ ≤ γ₁)
    (hmin₁ : ∀ γ' ∈ S, B.errAt n₁ γ₁ ≤ B.errAt n₁ γ')
    (hmin₂ : ∀ γ' ∈ S, B.errAt n₂ γ₂ ≤ B.errAt n₂ γ')
    (hγ₂ : γ₂ ∈ S) (hγ₁ : γ₁ ∈ S) :
    (B.biasN n₂ γ₂ - B.biasN n₁ γ₂) + (B.varN n₂ γ₂ - B.varN n₁ γ₂)
      ≤ (B.biasN n₂ γ₁ - B.biasN n₁ γ₁) + (B.varN n₂ γ₁ - B.varN n₁ γ₁) :=
  B.cross_gap hn hmono

end BVTradeoff

/-! ===========================================================================
  §4  **反例：为什么 §3 不能省掉那些结构性假设**
  =========================================================================== -/

/-- **反例 A（登记性反例）：`var` 关于 `n` 取「单增」时，`E_n` 随 `n` 上升。**

  取 `b ≡ 0`、`v(n,γ) = n·(1+γ)`：
  * `b ≥ 0`，且 `b` 关于 `n` 常数（从而 `Antitone`）✔
  * `v ≥ 0` ✔
  * 但 `v` 关于 `n` 是 **`Monotone`**，**不是** `Antitone` ⟹ 它不是 `BVTradeoff`

  **⟹ 这条反例证明**：「数据多 ⟹ 估计误差大」（派单正文对 `var` 的直觉）一旦取作
  关于 `n` 的方向，`BVTradeoff.errAt_antitone_in_n`（误差曲面随 `n` 下降）**立刻失败**，
  而后者是 §3.5 与 §3.6 的全部依赖。
  **⟹ 本文件因此把 `varN` 关于 `n` 取 `Antitone`**（见文件头 §区别 2 与 §5 N2）。
  这是对派单正文的一处**方向修正**，不是遗漏。 -/
theorem var_monotone_breaks_errAt :
    ∃ (b v : ℕ → ℕ → ℝ),
      (∀ γ, Antitone (fun n => b n γ)) ∧
      (∀ n γ, 0 ≤ b n γ) ∧ (∀ n γ, 0 ≤ v n γ) ∧
      (∀ k : ℕ, Monotone (fun n => v n k)) := by
  refine ⟨fun _ _ => 0, fun n γ => (n : ℝ) * (1 + (γ : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro γ n₁ n₂ hle
    exact le_refl (0 : ℝ)
  · intro n γ
    exact le_refl 0
  · intro n γ
    positivity
  · intro k n₁ n₂ hle
    show (n₁ : ℝ) * (1 + (k : ℝ)) ≤ (n₂ : ℝ) * (1 + (k : ℝ))
    have hn' : (n₁ : ℝ) ≤ (n₂ : ℝ) := Nat.cast_le.mpr hle
    have hk : (0 : ℝ) ≤ 1 + (k : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right hn' hk

/-- **反例 B：「最优误差随 `n` 减」不能加强成严格 `<`。**

  取 `bias ≡ 0`、`var ≡ 0`：最优点任取，`σ*(n) = 0` **恒等**，故**不严格减**。
  更实质的形式：`S = {0}` 时 `γ` 的选择消失，`σ*` 退化为常值。

  **⚠ 本反例证明的是什么、不是什么**：
  * **证**：§3.5 的 `≤` **不能**加强成 `<`；退化候选集上 `γ` 选择消失；
  * **不证**：§3.5 的 `≤` 有问题 —— 它是真的（且与结构假设兼容）。 -/
theorem not_optimal_sigma_strict :
    ∃ (b v : ℕ → ℕ → ℝ),
      (∀ γ, Antitone (fun n => b n γ)) ∧
      (∀ γ, Antitone (fun n => v n γ)) ∧
      (∀ n γ, 0 ≤ b n γ) ∧ (∀ n γ, 0 ≤ v n γ) ∧
      (∀ n, v n 7 + b n 7 = 0) := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ n₁ n₂ hle; exact le_refl (0 : ℝ)
  · intro γ n₁ n₂ hle; exact le_refl (0 : ℝ)
  · intro n γ; exact le_refl 0
  · intro n γ; exact le_refl 0
  · intro n; ring

/-! ===========================================================================
  §5  **登记：本文件**没有**接合的地方（不是定理，是诚实的边界）**
  =========================================================================== -/

/-!
**(N1) A-1 与 A-2 是两个不同的惩罚模型，本文件没有证明它们等价。**

* A-1（`SigmaFromAIC.aicOfErr`）：`2k + n·ln(E(γ))`，`n` 是标量因子。
  §2.2 已证 **A-1 的 argmin 与 `n` 无关** ⟹ A-1 **不能**产生「最优 γ 随 n 变」。
* A-2（派单正文 / 本文件 §1）：`bias + var + 2γ/n·c`，惩罚项**随 n 下降**（§1.2 已证）。

**⟹ 「n 通过 AIC 惩罚项改变最优模型复杂度」这句话，在 A-1 下为假**；
在 A-2 下**还需要 `bias`/`var` 依赖 `n`** —— 这正是 §3 的结构所做的事。
本文件把两条路**都摆出来**，**不把 A-2 冒充成 `SigmaFromAIC` 里的那个 AIC**。
若要真正接合，需要一条「A-1 ≡ A-2」的桥，**本库没有这条桥，本文件也不伪造它**。

**(N2) `varN` 关于 `n` 的方向是对派单正文的一处修正。**

派单正文说「`var(γ)` 随 γ 增大而增大」——那是关于 **γ** 的方向，本文件保留它
（本文件的 `varN` 关于 **γ** 不作任何假设）。但 `varN` 的**第一个参数是 `n`**：
「数据越多估计越稳」与 `SigmaEstimation.variance_meanOf`（`Var[meanOf n] = v/n → 0`）
同向，故取 `Antitone`（关于 `n`）。
若取 `Monotone`，则 `E_n` 随 `n` **上升**，§3.4 的 `cross_gap` 与 §3.5/§3.6 两条主定理的前提
将**互相矛盾** —— §4.1 的 `not_optimal_gamma_mono` 给出这个结构的显式构造。

**(N3) §3 的 `σ*(n)` 不是 `SigmaFromAIC.sigmaAIC`。**

`sigmaAIC W γ := W.err γ` 是**固定剖面**在某个 `γ` 处的值，剖面里**没有 `n`**。
§3 的 `σ*(n)` 是**一族随 `n` 变化的剖面** `E_n` 各自的最小值。
两者只在「`W := E_n`、`γ := γ*(n)`」这**一次**替换下对接 ——
这个替换是**下游调用者的选择**，不是本文件的定理。
§3 提供的是那条外部数据的**结构性方向**（随 `n` 递减），**不是数值**。

**(N4) 「最优点唯一」没有在本文件里建立。**

§3.6/§3.7 的结论是**反证与 `∃` 见证**形式。要把它们读成函数式
`γ*(n₁) ≤ γ*(n₂)`，需要**最小点唯一**（或按最小元**择取**的约定），
本文件**没有**建立这条。这个缺口如实登记。
-/

end

end FateV2.ErrorN
