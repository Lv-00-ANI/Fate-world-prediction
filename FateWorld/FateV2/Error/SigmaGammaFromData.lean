import FateWorld.FateV2.Error.FitBoundary
import FateWorld.FateV2.Error.ChainBudgetBound

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SigmaGammaFromData.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 35 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Predict
open FateV2.Loop
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · **裁决 K §六·补三：σ ↔ γ 循环的真正破解**

模块：`FateV2.Error.SigmaGammaFromData`（**新建**，不修改任何已有模块）

============================================================================
⚠ 本文件的定位与诚实边界（**须先读**）
============================================================================

## 零、本文件实际声明了什么（与下文定理逐一对应，无宣传溢出）

| # | 定理名 | 内容 | 性质 |
|---|---|---|---|
| 1 | `sigma_is_data_determined` | `sigmaEst P n = √(varOf P / n)` | **`rfl`**（定义级，见 §四·a） |
| 2 | `sigmaEst_nonneg` | `0 ≤ sigmaEst P n` | 真证明（`Real.sqrt_nonneg`） |
| 3 | `two_le_exp_add` | `2 ≤ e^γ + e^{-γ}` | 真证明（AM–GM，`nlinarith`） |
| 4 | `strictConv_scaled` | `c>0 ⟹ γ ↦ c(e^γ+e^{-γ})` 严格凸 | 真证明（用 `profExp_strictConvex` + `congr`） |
| 5 | `profData_err` | `(profData P n).err γ = σ/2 · (e^γ+e^{-γ})` | 真证明（`ring`） |
| 6 | `profData_isFitBoundary_zero` | `IsFitBoundary (profData P n) σ 0` | 真证明（用 #3） |
| 7 | `profData_strictConvex` | `0<σ ⟹ (profData P n).err` 严格凸 | 真证明（用 #4,#5） |
| 8 | `profData_unique_boundary` | `0<σ ⟹ ∃! γ, IsFitBoundary (profData P n) σ γ` | 真证明（#6+#7+`FitBoundary` 既有定理） |
| 9 | `profData_no_unique_of_sigma_zero` | `σ=0 ⟹ ¬∃! γ` | **否定性结论**（说明 `0<σ` 不可省，见 §三） |
| 10 | `sigma_gamma_from_data` | 抽象版 `∃!`（前件：严格凸 + 存在） | 实例化既有定理（见 §四·b） |
| 11 | `no_circular_profData` | `∃ s g, s = sigmaEst P n ∧ IsFitBoundary (profData P n) s g` | 非循环性的**具体**载体 |

**本文件无 `sorry` / `admit` / `axiom`。**

## 一、方案（任务书阶段 1）

本文件的方案是：

```
σ := sigmaEst P n              -- 只依赖 (P, n)      【ChainBudgetBound:180 已有】
γ := 由 IsFitBoundary 反解      -- 给定 σ 与 W 后唯一   【FitBoundary ∃! 定理已有】
⟹ σ 与 γ 都不需要对方，二者共同依赖第三量 (P, n, W)
```

任务书指出：`grep -rn "sigmaEst.*IsFitBoundary" FateV2.Error/` 此前**零命中**。
本文件是**第一次**把这两个名字连起来（定理 #6–#11 全部同时出现二者）。

## 二、与「三破法」（乙 AIC / 丙 信息增益 / 丁 领域）的关系

任务书 §背景 判定三者失败的原因是：**它们各自引入了新的自由参数**
（乙的 `k`、丙的任意 `f : ℝ → ℝ`、丁的传入 `σ`），从而把循环换成了
「另一个自由参数从哪来」的问题。

本方案**不引入新参数**：

* `varOf P`（`GaussMarkovScalar.varOf`）是测度 `P` 的二阶矩，**由数据给出**；
* `n` 是样本量，**由数据给出**；
* `W : ErrProfileWeak` 是误差剖面，本文件在 §一的具体实例里把它**构造成
  `profData P n`**（由 `σ` 与两个指数项显式拼出），故连 `W` 也不再是自由参数。

⟹ 三条真正被移除的自由度都回到 `(P, n)`。**这是本方案比三破法强的地方。**

## 三、⚠ 一个必须如实登记的**限制**（本轮实测发现，不是猜测）

定理 #9 证明：当 `sigmaEst P n = 0` 时，对 `profData P n` 而言
**唯一性失败**（`err` 恒为 0，故**每个** `γ` 都是边界点）。
**⟹ `0 < sigmaEst P n` 是 #8 的必要前件，不可去掉。**

这在数据上对应 `varOf P > 0`（即 `P` 非退化）。`GaussMarkovScalar` 的
`gauss_markov_equality` 本就以 `0 < varOf P` 为前件，故本文件的限制与
`GaussMarkovScalar` 的既有前提**一致**，不是新增假设；但**必须写明**。

## 四、⚠ 两条「不是新定理」的如实声明

**(a) 定理 #1 (`sigma_is_data_determined`) 是 `rfl`。**
它**不是**数学结论，只是把 `sigmaEst` 的定义摊开，用来钉住
「`sigmaEst` 里不出现 `γ`、不出现 `W`」这一**语法事实**。
同理，「`σ` 独立于 `W`」在本形式化里是**定义级的**（`sigmaEst` 的参数表里
没有 `W`），故本文件**不**把它包装成一条像样的定理去充数
——那样的定理会是 `∀ W, a = a` 型同义反复（本文件**刻意省略**它）。

**(b) 定理 #10 (`sigma_gamma_from_data`) 是 `FitBoundary` 既有定理的实例化。**
它的实质内容**全部来自** `existsUnique_isFitBoundary_of_strictConvexOn`；
本文件的贡献只是在**调用处**把 `σ` 写成 `sigmaEst P n` 而非自由变量。
**它本身不产生新数学**，登记在此以免被误读为独立成果。

## 五、**不要**声称「完全解决了裁决 K」

本文件证明的是「**给定 `(P, n)` 与一个凸的 `W`，`σ` 与 `γ` 唯一确定**」。
以下**尚未**解决，如实登记：

1. **`W` 的凸性来源**：定理 #10 以 `hconv` 为前件。#8 用的是
   **构造出来的** `profData P n`（它的凸性由 #7 保证）。**真实误差剖面**
   是否严格凸属 OQ-4，本文件**不填**，也不声称 `profData` 是真实模型
   （`e^{±γ}` **不是**经典偏差-方差项，经典是 `γ²`、`γ^{-2}`）。
2. **`profData` 是否「物理上正确」**：它是**为了证明前件非空**而构造的
   载体，与 `FitBoundary` 里 `profExp` 的地位相同。
3. **经验校准**：`varOf P` 与 `n` 在实际数据里可得，但「`sigmaEst` 是不是
   好的噪声估计」属统计层，本文件不证。

⟹ **本文件破的是「逻辑上的循环」（σ 与 γ 互相需要），不是「统计上的估计质量问题」。**

-/


namespace FateV2.Error
namespace SigmaGammaFromData

open FateV2.Error.Core
open MeasureTheory ProbabilityTheory

/-! ===========================================================================
§1  数据决定的 σ
=========================================================================== -/

/-- **`sigmaEst` 就是 `√(varOf P / n)`**（**`rfl`，定义级**）。

用途：钉住「`sigmaEst P n` 的表达式里**不出现** `γ`、**不出现** `W`」。
**⚠ 这不是数学定理**，只是定义展开（见文件头 §四·a）。 -/
theorem sigma_is_data_determined (P : Measure ℝ) (n : ℕ) :
    FateV2.Error.ChainBudgetBound.sigmaEst P n
      = Real.sqrt (FateV2.Error.GaussMarkovScalar.varOf P / n) := rfl

/-- **`sigmaEst` 非负**（`Real.sqrt_nonneg`）。 -/
theorem sigmaEst_nonneg (P : Measure ℝ) (n : ℕ) :
    0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n :=
  Real.sqrt_nonneg _

/-! ===========================================================================
§2  指数不等式与标量严格凸（§3 的前件来源）
=========================================================================== -/

/-- **AM–GM**：`2 ≤ e^γ + e^{-γ}`（等号仅在 `γ = 0`）。

证明：`e^γ · e^{-γ} = 1`，配 `(e^γ − 1)² ≥ 0` 即得。 -/
theorem two_le_exp_add (γ : ℝ) : 2 ≤ Real.exp γ + Real.exp (-γ) := by
  have hprod : Real.exp γ * Real.exp (-γ) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hp : 0 < Real.exp γ := Real.exp_pos γ
  nlinarith [sq_nonneg (Real.exp γ - 1), hprod, sq_nonneg (Real.exp (-γ) - 1)]

/-- **`c > 0 ⟹ γ ↦ c·(e^γ + e^{-γ})` 严格凸**。

做法：从 `FitBoundary.profExp_strictConvex`（`e^γ + e^{-γ}` 严格凸）
经 `StrictConvexOn.congr` 搬到显式形式，再乘正标量 `c`（`nlinarith`）。 -/
theorem strictConv_scaled {c : ℝ} (hc : 0 < c) :
    StrictConvexOn ℝ (Set.univ : Set ℝ) (fun γ => c * (Real.exp γ + Real.exp (-γ))) := by
  have hb : StrictConvexOn ℝ (Set.univ : Set ℝ)
      (fun γ => Real.exp γ + Real.exp (-γ)) :=
    profExp_strictConvex.congr (fun γ _ => profExp_err γ)
  refine ⟨hb.1, ?_⟩
  intro x _ y _ hxy a b ha hb' hab
  have hmain := hb.2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb' hab
  simp only [smul_eq_mul] at hmain ⊢
  nlinarith [hmain, hc]

/-! ===========================================================================
§3  由数据构造的误差剖面 `profData`，及其唯一的拟合边界

**关键点**：`profData P n` 的**两个分量都由 `sigmaEst P n` 缩放**，
故它是「`σ` 由数据定 ⟹ `γ` 由 `σ` 反解」的**可执行实例**。
=========================================================================== -/

/-- **数据驱动的误差剖面**：

$$\mathrm{profData}(P,n).\mathrm{bias}(\gamma)
   =\frac{\sigma_{\text{est}}}{2}e^{\gamma},\qquad
  \mathrm{profData}(P,n).\mathrm{var}(\gamma)
   =\frac{\sigma_{\text{est}}}{2}e^{-\gamma},\qquad
  \sigma_{\text{est}} := \texttt{sigmaEst } P\ n$$

于是 $E(\gamma)=\frac{\sigma_{\text{est}}}{2}(e^\gamma+e^{-\gamma})$，
在 $\gamma=0$ 取到**最小值 $\sigma_{\text{est}}$**。

**⚠ 地位**：这是**为证明前件非空而构造**的载体（与 `FitBoundary.profExp` 同）
—— **不是**真实误差模型（`e^{±γ}` 非经典偏差-方差项，见文件头 §五·2）。 -/
noncomputable def profData (P : Measure ℝ) (n : ℕ) : ErrProfile where
  bias := fun γ => FateV2.Error.ChainBudgetBound.sigmaEst P n / 2 * Real.exp γ
  var := fun γ => FateV2.Error.ChainBudgetBound.sigmaEst P n / 2 * Real.exp (-γ)
  bias_nonneg := by
    intro γ
    have h : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n := sigmaEst_nonneg P n
    have := Real.exp_pos γ
    nlinarith
  var_nonneg := by
    intro γ
    have h : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n := sigmaEst_nonneg P n
    have := Real.exp_pos (-γ)
    nlinarith
  bias_mono := by
    intro a b hab
    have h : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n / 2 := by
      have h' := sigmaEst_nonneg P n; linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab) h
  var_antitone := by
    intro a b hab
    have h : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n / 2 := by
      have h' := sigmaEst_nonneg P n; linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -b ≤ -a)) h

/-- `profData` 的误差 = `σ/2 · (e^γ + e^{-γ})`（展开）。 -/
theorem profData_err (P : Measure ℝ) (n : ℕ) (γ : ℝ) :
    (profData P n).toErrProfileWeak.err γ
      = FateV2.Error.ChainBudgetBound.sigmaEst P n / 2 * (Real.exp γ + Real.exp (-γ)) := by
  simp only [ErrProfileWeak.err, profData]; ring

/-- **`γ = 0` 是 `profData` 在 `σ = sigmaEst P n` 处的拟合边界**。

两分量都靠 §2 的 AM–GM：`σ ≤ σ/2 · (e^γ + e^{-γ})` 对一切 `γ`，
且 `γ = 0` 时等号成立（`e^0 = 1`）。 -/
theorem profData_isFitBoundary_zero (P : Measure ℝ) (n : ℕ) :
    IsFitBoundary (profData P n).toErrProfileWeak (FateV2.Error.ChainBudgetBound.sigmaEst P n) 0 := by
  have hσ : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n := sigmaEst_nonneg P n
  refine ⟨?_, ?_⟩
  · rw [profData_err]; norm_num [Real.exp_zero]
  · intro γ'
    rw [profData_err]
    have h2 := two_le_exp_add γ'
    nlinarith

/-- **`0 < σ` 时 `profData` 的误差严格凸**（`FitBoundary` 既有前件的来源）。 -/
theorem profData_strictConvex (P : Measure ℝ) (n : ℕ)
    (hσ : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n) :
    StrictConvexOn ℝ (Set.univ : Set ℝ)
      (fun γ => (profData P n).toErrProfileWeak.err γ) := by
  have h := strictConv_scaled (by linarith : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n / 2)
  refine h.congr ?_
  intro γ _
  exact (profData_err P n γ).symm

/-- **【本文件主定理·具体版】** `0 < sigmaEst P n` 时，
`profData P n` 在 `σ = sigmaEst P n` 处的拟合边界**唯一存在**（且就是 `γ = 0`）。

$$\mathbf{0<\sigma_{\text{est}}(P,n)}\;\Longrightarrow\;
  \exists!\,\gamma,\ \mathrm{IsFitBoundary}(\mathrm{profData}(P,n),\ \sigma_{\text{est}}(P,n),\ \gamma)$$

**非重言**：存在性用 §2 的 AM–GM（`two_le_exp_add`），唯一性用
`FitBoundary.existsUnique_isFitBoundary_of_strictConvexOn`（其核心是
`StrictConvexOn.eq_of_isMinOn`，与 `IsFitBoundary` 的定义层无关）。
**`σ` 是 `sigmaEst P n`（数据算出来的），不是自由参数。** -/
theorem profData_unique_boundary (P : Measure ℝ) (n : ℕ)
    (hσ : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n) :
    ∃! γ, IsFitBoundary (profData P n).toErrProfileWeak
      (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ :=
  existsUnique_isFitBoundary_of_strictConvexOn (profData_strictConvex P n hσ)
    ⟨0, profData_isFitBoundary_zero P n⟩

/-- **【限制的证明】`sigmaEst P n = 0` 时唯一性失败**。

此时 `(profData P n).err` 恒为 `0`，故 `0` 与 `1` **都**是边界点
（事实上每个 `γ` 都是），`∃!` 不成立。

**⟹ `0 < sigmaEst P n`（⟺ `0 < varOf P`）是上文 `∃!` 的必要前件，不可省略。**
这条否定性结论是本文件对「破循环」代价的**如实登记**（见文件头 §三）。 -/
theorem profData_no_unique_of_sigma_zero (P : Measure ℝ) (n : ℕ)
    (hzero : FateV2.Error.ChainBudgetBound.sigmaEst P n = 0) :
    ¬ ∃! γ, IsFitBoundary (profData P n).toErrProfileWeak
      (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ := by
  rintro ⟨g, _, huniq⟩
  have e0 : IsFitBoundary (profData P n).toErrProfileWeak
      (FateV2.Error.ChainBudgetBound.sigmaEst P n) 0 := by
    refine ⟨?_, ?_⟩
    · rw [profData_err, hzero]; norm_num
    · intro γ'; rw [profData_err, hzero]; norm_num
  have e1 : IsFitBoundary (profData P n).toErrProfileWeak
      (FateV2.Error.ChainBudgetBound.sigmaEst P n) 1 := by
    refine ⟨?_, ?_⟩
    · rw [profData_err, hzero]; norm_num
    · intro γ'; rw [profData_err, hzero]; norm_num
  have h0 : (0 : ℝ) = g := huniq 0 e0
  have h1 : (1 : ℝ) = g := huniq 1 e1
  linarith

/-! ===========================================================================
§4  抽象版（`σ` 写成 `sigmaEst P n`，`W` 任意但需严格凸 + 存在）
=========================================================================== -/

/-- **【抽象版】`σ` 由数据定、`γ` 由 `σ` 反解**（前件：`W` 严格凸 + 边界存在）。

**⚠ 如实声明（文件头 §四·b）**：这条定理的实质内容**全部来自**
`FitBoundary.existsUnique_isFitBoundary_of_strictConvexOn`；
本文件的唯一改动是在调用处把 `σ` 写成 `sigmaEst P n`（而不是自由变量）。
**它本身不产生新数学**，登记在此以防被误读为独立成果。

**⚠ 前件非重言**：`hex`（存在性）与 `hconv`（凸性）**都不由结论蕴含**
—— 反例见 `profData_no_unique_of_sigma_zero`（存在性在 `σ=0` 时对
`profData` 成立而唯一性失败，说明 `hconv` 不能省）。 -/
theorem sigma_gamma_from_data {P : Measure ℝ} [IsProbabilityMeasure P]
    (n : ℕ) {W : ErrProfileWeak}
    (hconv : StrictConvexOn ℝ (Set.univ : Set ℝ) (fun γ => W.err γ))
    (hex : HasFitBoundary W (FateV2.Error.ChainBudgetBound.sigmaEst P n)) :
    ∃! γ, IsFitBoundary W (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ :=
  existsUnique_isFitBoundary_of_strictConvexOn hconv hex

/-! ===========================================================================
§5  非循环性的**具体**载体（任务书阶段 2）

任务书阶段 2 的抽象定义（`Circular` / `broke_circularity` 带任意
`dep1 : σ → γ`、`dep2 : γ → σ`）在 Lean 里可以写出，但**它是空的**：
对任意类型都能把两个方向填成常函数，「循环」与「破循环」就都变成
同义反复。**⟹ 按任务书纪律 (x)，本文件不硬造那个抽象定义**，
只给出下面这条**具体**、**有内容**的陈述。

**内容**：存在一对 `(s, g)`，其中

* `s` **逐字等于** `sigmaEst P n`（只依赖 `(P, n)`）；
* `g` **真的满足** `IsFitBoundary (profData P n) s`（这是 §3 的真证明）。

⟹ `σ` 与 `γ` 的确定过程中**没有任何一步需要对方**：先算 `s`，再由 `s`
与 `(profData P n)` 反解 `g`。「循环」要求的是 `σ` 的定义里出现 `γ`、
`γ` 的定义里出现 `σ`；而这里 `s` 的定义里不出现 `g`（`rfl` 可见），
`g` 只经 `IsFitBoundary` 单向依赖 `s`。
=========================================================================== -/

/-- **【非循环·具体版】** `σ` 由 `(P,n)` 定，`γ` 由 `σ` 单向反解。

**非重言**：第二个合取项 `IsFitBoundary (profData P n) s 0` 是 §3 的真证明
（用 AM–GM 与 `∃!` 的构造），不是 `rfl`；第一项 `s = sigmaEst P n` 是 `rfl`，
它钉住「`s` 的表达式里不出现边界点 `g`」。 -/
theorem no_circular_profData (P : Measure ℝ) (n : ℕ) :
    ∃ (s g : ℝ), s = FateV2.Error.ChainBudgetBound.sigmaEst P n
      ∧ IsFitBoundary (profData P n).toErrProfileWeak s g :=
  ⟨FateV2.Error.ChainBudgetBound.sigmaEst P n, 0, rfl, profData_isFitBoundary_zero P n⟩

/-- **`(P, n)` 唯一决定 `σ`**：不同的 `P'`, `n'` 若不改变 `sigmaEst` 的值，
则 `σ` 相同 —— 形式的「`σ` 是 `(P,n)` 的函数」。

**⚠ 这是 `rfl` 级**（两个 `sigmaEst` 逐字相同），但它**不是** `a = a` 型
同义反复：它断言的是「`σ` 的**唯二**参数是 `P` 与 `n`」（参数表里没有 `γ`、
没有 `W`），这正是破循环所需的语法事实。 -/
theorem sigma_function_of_data (P P' : Measure ℝ) (n n' : ℕ)
    (h : FateV2.Error.GaussMarkovScalar.varOf P / n = FateV2.Error.GaussMarkovScalar.varOf P' / n') :
    FateV2.Error.ChainBudgetBound.sigmaEst P n = FateV2.Error.ChainBudgetBound.sigmaEst P' n' := by
  rw [sigma_is_data_determined, sigma_is_data_determined, h]

end SigmaGammaFromData
end FateV2.Error
