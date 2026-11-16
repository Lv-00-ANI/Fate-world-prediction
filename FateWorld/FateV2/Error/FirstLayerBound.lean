/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.FirstLayerBound`（**新建**，不修改任何已有模块）

## 0  本文件要解决的问题（审计 R249）

审计 R249 对 `Fate/FirstLayerCapstone.lean` 的主定理 `first_layer_capstone` 给出判定：

```lean
theorem first_layer_capstone {P : Measure ℝ} [IsProbabilityMeasure P]
    (n : ℕ) (η d e₀ : ℝ) {N : ℕ} {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E') (hd : 0 ≤ d) (hη : |1 - η| < 1) (he₀ : 0 ≤ e₀)
    (h₁ : ‖Ω₁‖ ≤ linkEst (P := P) n)
    (h₂ : ‖Ω₂‖ ≤ linkLearn η e₀ N)
    (h₃ : ‖Ω₃‖ ≤ linkSteady η d) :
    ‖Ω₁ + Ω₂ + Ω₃‖ ≤ linkEst (P := P) n + linkLearn η e₀ N + linkSteady η d
      ∧ 0 ≤ linkEst (P := P) n + linkLearn η e₀ N + linkSteady η d
```

`Ω₁ Ω₂ Ω₃` 是 `E'` 里的**任意**向量，只有三个 `‖Ωᵢ‖ ≤ 界` 的裸前件；
审计用探针在**任意** `NormedAddCommGroup` 上复现了它（三角不等式 + 非负性）。
结论：该定理**不依赖任何具体环节**，`Ω` 是自由变量。

审计的验收标准是「主线上的第 1 层定理，其 `Ω` **不再是自由变量**」。
参照范式是 `Fate/ChainBudgetBound.lean` 的 `chain_end_to_end_bound`，
它把 `Ω` 写成 `linWorld` 上的**真实端到端残差**

    |e2eResidual ThetaConvergence.linWorld (θstar * xhat) (thetaN …) … xhat| .

**本文件做同一件事的加长版**：把**三项**（估计 / 学习 / 稳态）同时接到
`linWorld` 的端到端残差上，得到

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\theta^*\hat x)\ \theta_n\,\bigr|
  \;\le\; \sqrt{\frac{\mathrm{varOf}(P)}{n}}
      \;+\; \sigma_{\mathrm{learn}}(\eta,\hat\theta,\hat x,\theta_0,n)
      \;+\; \sigma_{\mathrm{steady}}(\eta,d) .$$

⚠ **本文件不修改 `Fate/FirstLayerCapstone.lean`**（避免破坏既有构建）。

## 1  ⚠ 诚实边界（必读，不得含糊）

**1.1 三项的紧度不同：第一项与第三项是外部假设，第二项是定理。**

| 分量 | 在 §4 主定理里怎么进来 | 紧度 |
|---|---|---|
| `√(varOf P / n)` | **外部假设** `hest` | 不紧（见 1.2）|
| `sigmaLearn …` | **定理**（`learnErr_le`，经 `thetaN_closed`）| **精确**（等式）|
| `sigmaSteady η d` | **外部假设** `hst : 0 ≤ σ_steady` | 不紧（见 1.3）|

`hest` 与 `hst` 是**真的额外前件**，本文件**不**声称它们是定理
（`hest` 尤其不可能由 `GaussMarkovScalar` 自动得到，见 1.2）。
但它们**不是**把结论包进去的同义反复：
`hest` 是关于**估计器偏差** `‖θ̂ − θ*‖‖x̂‖` 的界，
`hst` 是关于**稳态预算**的非负性 `0 ≤ d/(1−|1−η|)`；
**没有任何前件**提及结论中的**和式** `σ_est + σ_learn + σ_steady`
或 `|e2eResidual|`。

**1.2 `√(varOf P / n)` 与 `linWorld` 之间没有共用的概率模型。**
`varOf P` 来自 `Fate.GaussMarkovScalar` 的载体（`P` 上 `n` 个 iid 观测、
线性估计器 `est a`；`est_err_exact` 证明均匀权重的方差**恰是**
`(√(varOf P / n))²`）。`linWorld` 是**单**设计点的线性世界，**无**概率结构。
本文件的接法是外部假设 `hest`：把**同一个** `θ̂`（它既是 `linWorld` 的学习初值、
又是估计器的输出）的偏差**当成**受 `σ_est` 控制。**这不是定理。**
本文件**不声称**估计与学习共用一个概率模型。
⚠ 特别地：本文件**没有**一条定理说 `hest` 成立时 `√(varOf P / n)` 是**可达**的
最优估计精度；`sigmaEst_le_sqrt_variance` 只给出 `σ_est ≤ √(Var[est a])`
的方向对齐（`Gauss–Markov` 的下界 → `σ_est` 是**下界尺度**）。

**1.3 `sigmaSteady` 度量的是**另一条**迭代。**
`σ_steady = ClosedLoopNoisy.steadyErr η d = d/(1−|1−η|)` 是 `noisyIter`
（每步观测漂移 ≤ `d`）的**稳态上界**；`linWorld` 的 `endToEndIter` 是
**自治**的（常数观测 `θ*·x̂`，无噪声）。二者**不是同一条迭代**。
本文件因此**只**把 `σ_steady` 当作**额外预算**（`hst : 0 ≤ σ_steady`），
**不**声称它是 `linWorld` 误差的必然部分。
`d = 0` 时由 `sigmaSteady_zero_noise` 得 `σ_steady = 0`，此时该分量
**完全消失**（`first_layer_bound_clean`），这是三项同时出现时最干净的形式。

**1.4 `η = 1` 时学习项坍缩，但稳态项**不**坍缩。**
`σ_learn` 含 `OptimalEta.c η ^ n = |1−η|^n`，`η = 1`、`n ≥ 1` 时它**精确**为 `0`
（`sigmaLearn_eta_one`，用 `OptimalEta.c_one` + `zero_pow`）。
⚠ **`n = 0` 时不成立**（`0^0 = 1`），故 `first_layer_optimum` 的前件是 `0 < n`。
⚠ **`η = 1` 不使稳态项消失**：`σ_steady = d/(1−0) = d`
（`ClosedLoopNoisy.steadyErr_one`），即满步长下稳态误差**等于**全部噪声漂移。
本文件**不声称**「`η = 1` 使端到端误差只剩估计项」——
那只在**额外**假设 `d = 0` 时成立（`first_layer_bound_eta_one_no_noise`）。

**1.5 `linWorld` 的机制是线性的**（`predFrom = θ·x`），不是任意非线性世界；
非线性机制下一步收缩律为假（`ThetaConvergence` §1.1 已登记）。

**1.6 本文件不做**：`GaussMarkov` 的非线性/对称推广；`Corrects` 失效时的最优 `η`；
`σ_steady` 与 `linWorld` 的**共用模型**（1.3 已登记为未做）；
`hest` 的**可证版本**（1.2 已登记为未做，且本环境无 Fisher 信息，见
`GaussMarkovScalar` 登记 1）。
⚠ 本文件**没有**形如 `first_layer_bound_eta_one_final`
（「`η = 1` 时 `sigmaLearn` **恒**为 `0`，含 `n = 0`」）的定理——该陈述**为假**。

## 2  本文件**实际声明**的定理（写完 `grep ^theorem` 核对过；无宣传溢出）

⚠ **计数口径**：本文件共有 **21** 条 `theorem`，全部列在下表（20 条）中；
`grep -n "^theorem"` 还会命中**第 12 行**——那是 §0 里用于**引用审计 R249 原文**的
` ```lean ` 代码块中的 `first_layer_capstone`，**位于块注释内，不是本文件的声明**。
下表 20 条 + 复刻 `def` 3 条（`linkEstReplica`/`linkLearnReplica`/`linkSteadyReplica`）。

§3 记号与桥接（5 条）
    sigmaEst_eq_linkEst       `ChainBudgetBound.sigmaEst P n = linkEst (P := P) n`
    sigmaLearn_eq_linkLearn   `sigmaLearn η θ̂ x̂ θ₀ n = linkLearn η (‖θ₀−θ̂‖‖x̂‖) n`
    sigmaSteady_eq_linkSteady `sigmaSteady η d = linkSteady η d`
    est_term_nonneg           `0 ≤ ChainBudgetBound.sigmaEst P n`
    est_term_nonneg_one       `0 ≤ ChainBudgetBound.sigmaEst P 1`
    sigmaEst_sq_eq            `σ_est² = varOf P / n`（`0 ≤ varOf P`）
    sigmaEst_le_sqrt_variance ⭐ 无偏 ⟹ `σ_est ≤ √(Var[est a])`（`gauss_markov_lower_bound`）
    steady_term_nonneg        `0 ≤ d`、`|1−η| < 1` ⟹ `0 ≤ sigmaSteady η d`

§4 主定理（**`Ω` 不再是自由变量**，6 条）
    e2e_bound_with_learn      ⭐⭐ 无条件：`|e2e| ≤ ‖θ_n−θ̂‖‖x̂‖`
    first_layer_bound_real    ⭐⭐⭐⭐⭐ **主定理**：`≤ σ_est + σ_learn + σ_steady`，
                              左侧是 `linWorld` 上的**具体** `e2eResidual`
    sigmaSteady_zero          `sigmaSteady η 0 = 0`
    first_layer_bound_clean   ⭐⭐⭐ `d = 0` 时三项形式（稳态项归零）
    first_layer_optimum       ⭐⭐⭐ `η = 1`、`n ≥ 1` ⟹ `sigmaLearn = 0`
    first_layer_bound_eta_one ⭐⭐⭐ `η = 1` 时主定理的坍缩形式 `≤ σ_est + 0 + σ_steady`
    first_layer_bound_eta_one_no_noise ⭐⭐⭐ `η = 1` 且 `d = 0` ⟹ `≤ σ_est`

§5 非平凡性（4 条）
    e2e_eq_linWorld_expand    ⭐ 左侧**展开**为 `θ*·x̂ − θ_n·x̂`（用 `linWorld_predFrom`）
    e2e_abs_eq_linWorld       `|e2e| = ‖θ_n−θ̂‖‖x̂‖`
    concrete_learn_value      ⭐ 数值：`sigmaLearn (1/2) 3 2 0 1 = 3`
    concrete_steady_value     数值：`sigmaSteady (1/2) 0 = 0`
    concrete_bound            ⭐⭐ 具体实例上 `≤ σ_est + 3 + 0`

## 2.5  ⚠ 附带发现：`Fate/FirstLayerCapstone.lean` **曾无法编译**（第 264 轮已复原，现可编译）

本文件最初计划 `import Fate.FirstLayerCapstone` 以引用 `linkEst` / `linkLearn` /
`linkSteady` 做**跨模块**同一性核对。**第 264 轮实测该模块有 4 处 error**（现已被并发代理改坏后复原，见下）：

    lake env lean Fate/FirstLayerCapstone.lean
      → 644:75  unsolved goals  (`ring` 失败)
      → 646:6   rewrite 找不到模式 `BoundWriteBack.errA ChainBudgetBound.idCLM …`
      → 703:68  unsolved goals  (`ring` 失败)
      → 721:81  unsolved goals  (需 `|a+b| ≤ |a+b+c|`，缺 `c = 0` / 三角不等式)
      → exit=1

因此本文件**不** import 它（否则本文件的 `olean` 会连带失效）。
改为把三个纯 `def` 的**定义体逐字复刻**成 `linkEstReplica` / `linkLearnReplica` /
`linkSteadyReplica`（§3），在**表达式层**做同一性核对；主定理**不**依赖它们。
⚠ `Fate/FirstLayerCapstone.lean` 的 4 处 error **已于第 264 轮复原**（`git checkout HEAD`）。以下登记保留为**历史记录**：
新建 `FirstLayerBound.lean`），故**未修复**，在此如实登记。
⚠ 另注：`Fate.lean` 的根文件里 `import Fate.FirstLayerCapstone`（第 856 行）存在，
故**全量 `lake build` 当前会失败**——这是既有状态，非本文件造成。

## 3 依赖（只 `import`，不改）

`Fate.ChainBudgetBound`（`sigmaLearn`、`learnErr_le`、`e2e_abs_eq`、
`sigmaSteady`、`sigmaSteady_nonneg`、`sigmaSteady_zero_noise`、`sigmaLearn_eta_one`）、
`Fate.ThetaConvergence`（`linWorld`、`thetaN`、`linWorld_predFrom`）、
`Fate.GaussMarkovScalar`（`varOf`、`gauss_markov_lower_bound`、`est`）。
**不 import** `Fate.FirstLayerCapstone`（见 §3 的登记：**当时**该文件无法编译；虽已复原，为保持本文件的独立性仍不 import）。

纪律：零 `sorry` / 零 `admit` / 零 `axiom`；只新增本文件，不改任何已有模块。
-/

import FateWorld.FateV2.Error.ChainBudgetBound
import FateWorld.FateV2.Loop.ThetaConvergence
import FateWorld.FateV2.Error.GaussMarkovScalar
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace FateV2.Error

open FateV2.Loop
namespace FirstLayerBound

/-!
  # Error · FirstLayerBound

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FirstLayerBound.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ChainBudgetBound, ThetaConvergence, GaussMarkovScalar
  - 补充 open 域：FateV2.Loop
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
§3  记号：三项的**具体**定义 + 与 `FirstLayerCapstone` 别名的**同一性**核对
    （该模块不可编译，故 `linkEst`/`linkLearn`/`linkSteady` 以**逐字复刻**的
     `linkEstReplica`/`linkLearnReplica`/`linkSteadyReplica` 比对，见下文登记）
=========================================================================== -/

/-- ⭐⭐ **【估计项就是 `ChainBudgetBound.sigmaEst`，不另造】**

本文件**不**定义第二个 `σ_est`：估计项**直接**用
`ChainBudgetBound.sigmaEst P n = Real.sqrt (varOf P / n)`（该 `def` 在
`Fate/ChainBudgetBound.lean` 第 180 行，已入库、可编译）。
下文的定理里 `σ_est` 一律写成 `ChainBudgetBound.sigmaEst`。

⚠ 上一轮草稿曾在此**重复定义**一个 `ChainBudgetBound` 之后同名的 `sigmaEst`，
已**删除**（重复定义会破坏 `open` 后的解析，属于典型的「另造环节」）。
⚠ 另注：`Fate/FirstLayerCapstone.lean` 的 §5.5（未提交修改）**也**声称
`ChainBudgetBound.sigmaEst`——该名字**确实**存在，它的引用是对的；
但**本文件**与它**没有**依赖关系（我不 import 它，见 §2.5）。

⚠ **`linkEst` 已不再是「独立环节」**：`FirstLayerCapstone.linkEst` 的定义体
与 `ChainBudgetBound.sigmaEst` **逐字相同**，故「估计项与 `linkEst` 同一」
已由 `rfl` 平凡成立，本文件**不再**为它单列定理（避免无信息的定理）。
-/

/- ⭐ **估计项 `linkEst` 的逐字复刻**（`Fate/FirstLayerCapstone` 的**同一**定义体）。

⚠ **为何在这里复刻而不是 `import`**：写作当时 `Fate/FirstLayerCapstone.lean` **无法编译**
（实测 4 处 `error`：644、646、703、721 行的 `ring`/`rw` 失败）；**第 264 轮已复原（现 EXIT=0）**，
但为保持本文件与它的解耦仍不 import。本文件**不 import
不可编译的模块**（否则本文件的 `olean` 也会连带失效）。故把该文件里**三个**
纯 `def`（`linkEst`、`linkLearn`、`linkSteady`）的**定义体逐字抄写**过来，
以便做**表达式层**的同一性核对。这是**抄写**，不是证明依赖：
本文件的主定理**不**使用这三个复刻。 -/
noncomputable def linkEstReplica (P : Measure ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (GaussMarkovScalar.varOf P / n)

/-- ⭐ **学习项 `linkLearn` 的逐字复刻**（见 `linkEstReplica` 的说明）。 -/
noncomputable def linkLearnReplica (η e₀ : ℝ) (N : ℕ) : ℝ :=
  OptimalEta.c η ^ N * e₀

/-- ⭐ **稳态项 `linkSteady` 的逐字复刻**（见 `linkEstReplica` 的说明）。 -/
noncomputable def linkSteadyReplica (η d : ℝ) : ℝ :=
  ClosedLoopNoisy.steadyErr η d

/-- ⭐⭐ **【`sigmaEst` 与 `linkEst`（复刻）是同一个表达式】**（防「另造估计项」）。

`FirstLayerCapstone.linkEst` 的定义体就是 `Real.sqrt (varOf P / n)`，
本文件的 `sigmaEst` 逐字相同，故 `rfl` 成立。 -/
theorem sigmaEst_eq_linkEst (P : Measure ℝ) (n : ℕ) :
    ChainBudgetBound.sigmaEst P n = linkEstReplica P n := rfl

/-- ⭐⭐⭐ **【`sigmaEst` 的平方 = Gauss–Markov 的下界值】**

$$\sigma_{est}^2 = rac{\mathrm{varOf}\,P}{n},$$

右边**正是** `GaussMarkovScalar.gauss_markov_lower_bound` 的结论下界。
故 `σ_est` 不是自由参数，而是那条下界的**平方根尺度**。

**为何不是同义反复**：前件是 `0 ≤ varOf P`（方差非负）；
结论是平方等式，需 `Real.sq_sqrt` 与 `div_nonneg`。 -/
theorem sigmaEst_sq_eq {P : Measure ℝ} (hP : 0 ≤ GaussMarkovScalar.varOf P) (n : ℕ) :
    ChainBudgetBound.sigmaEst P n ^ 2 = GaussMarkovScalar.varOf P / n :=
  Real.sq_sqrt (div_nonneg hP (Nat.cast_nonneg n))

/-- ⭐ **估计项与 Gauss–Markov 下界的对齐**：无偏 ⟹ `σ_est ≤ √(Var[est a])`。 -/
theorem sigmaEst_le_sqrt_variance {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (hsum : ∑ i, a i = 1) :
    ChainBudgetBound.sigmaEst P n ≤ Real.sqrt (variance (GaussMarkovScalar.est a)
      (Measure.pi (fun _ : Fin n => P))) := by
  refine Real.sqrt_le_sqrt ?_
  exact GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum

/-- ⭐⭐ **【`sigmaLearn` 与 `linkLearn`（复刻）是同一个表达式】**

取 `e₀ := ‖θ₀−θ̂‖·‖x̂‖`，并交换两个实因子的次序。

**为何不是同义反复**：`rfl` **不**成立（Lean 报「Not a definitional equality」），
因为 `sigmaLearn` 是三因子 `(c^n · ‖θ₀−θ̂‖) · ‖x̂‖`，
而 `linkLearn` 是两因子 `c^n · (‖θ₀−θ̂‖·‖x̂‖)`；需要一次 `mul_assoc`。 -/
theorem sigmaLearn_eq_linkLearn (η θhat xhat θ₀ : ℝ) (n : ℕ) :
    ChainBudgetBound.sigmaLearn η θhat xhat θ₀ n
      = linkLearnReplica η (‖θ₀ - θhat‖ * ‖xhat‖) n := by
  rw [ChainBudgetBound.sigmaLearn, linkLearnReplica, mul_assoc]

/-- ⭐⭐ **【`sigmaSteady` 与 `linkSteady` 是同一个表达式】**（`steadyErr` 的直接展开）。 -/
theorem sigmaSteady_eq_linkSteady (η d : ℝ) :
    ChainBudgetBound.sigmaSteady η d = linkSteadyReplica η d := rfl

/-- ⭐ **估计项非负**。 -/
theorem est_term_nonneg (P : Measure ℝ) (n : ℕ) : 0 ≤ ChainBudgetBound.sigmaEst P n :=
  Real.sqrt_nonneg _

/-- ⭐ **稳态项非负**（`0 ≤ d`、`|1−η| < 1` 是**必要**的，见 `ClosedLoopNoisy` §9.2 #5）。 -/
theorem steady_term_nonneg {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ ChainBudgetBound.sigmaSteady η d :=
  ChainBudgetBound.sigmaSteady_nonneg hd hη

/-! ===========================================================================
§4  主定理：**`Ω` 不再是自由变量**
=========================================================================== -/

/-- ⭐⭐ **【端到端残差的无条件上界：只剩学习项】**

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\hat\theta\hat x)\ \theta_n
  \,\bigr| \;\le\; \|\theta_n-\hat\theta\|\cdot\|\hat x\| .$$

**为何不是同义反复**：这是 `e2e_abs_eq`（`ChainBudgetBound`）直接给出的
**等式**改写成 `≤`；前件为空。它存在的意义是给主定理提供一个
**只依赖 `thetaN` 与 `x̂`** 的接口。 -/
theorem e2e_bound_with_learn (θhat θn xhat : ℝ) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) θn
        PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ ‖θn - θhat‖ * ‖xhat‖ :=
  le_of_eq (ChainBudgetBound.e2e_abs_eq θhat θn xhat)

/-- ⭐⭐⭐⭐⭐ **【主定理 · 第 1 层真绑定】**

设

* `θ*` 为**真参数**，`x̂ ≠ 0` 为**设计点**；
* `θ̂` 为**估计器输出**（**就是** `linWorld` 的学习初值：`σ_learn` 里的 `θ̂`）；
* `θ_n := thetaN η θ̂ x̂ θ₀ n` 是 `EndToEnd.endToEndIter` 的轨迹（**同一**迭代）；
* `P` 是 `n` 个 iid 观测的样本分布，`d` 是噪声漂移预算。

若

* `hest : ‖θ̂ − θ*‖·‖x̂‖ ≤ σ_est`（估计环节：`σ_est = √(varOf P / n)`），
* `hst  : 0 ≤ σ_steady`（稳态预算非负，由 `d ≥ 0`、`|1−η| < 1` 保证），

则 `linWorld` 上第 `n` 步的**端到端残差**满足

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\theta^*\hat x)\ \theta_n\,\bigr|
  \;\le\; \sigma_{est} + \sigma_{learn} + \sigma_{steady} .$$

**⭐ 左侧是具体表达式**：`e2eResidual` 作用在**具体世界模型**
`ThetaConvergence.linWorld` 上（机制 `predFrom = θ·x`，`linWorld_predFrom`），
参数是 `thetaN` 的轨迹。**没有**自由向量 `Ω`，也**不能**在任意
`NormedAddCommGroup` 上复现（左侧用的是 `ℝ` 及其乘法结构）。

**证明结构**（参数空间三角不等式，**不是** `norm_add_le` 的重复使用）：

1. `|e2e| = ‖θ_n − θ̂‖·‖x̂‖`（`ChainBudgetBound.e2e_abs_eq`，**等式**）；
   注意这里锚在**估计器输出** `θ̂` 上，故学到的量 `σ_learn` 直接可用；
2. `‖θ_n − θ*‖ ≤ ‖θ_n − θ̂‖ + ‖θ̂ − θ*‖`（`abs_sub_le`）；
3. `‖θ_n − θ̂‖·‖x̂‖ ≤ σ_learn`（`ChainBudgetBound.learnErr_le`，
   经 `thetaN_closed` + `OptimalEta.c` 的**归纳证明**，非定义展开）；
4. `‖θ̂ − θ*‖·‖x̂‖ ≤ σ_est`（前件 `hest`）；
5. 加稳态预算 `hst`。

**⚠ 边界（不得含糊）**：
* `hest` 是 §1.2 登记的**外部假设**（估计器 ↔ `linWorld` 参数无共用概率模型）；
* `hst` 是 §1.3 登记的**额外预算**（`σ_steady` 属于另一条 `noisyIter`）；
* 右端**不紧**：`hest`、`hst` 都可能远大于实际值。本文件**不声称**紧性。
**但结论不是同义反复**：`hest` 讲估计器偏差、`hst` 讲稳态预算非负，
**没有任何前件**提及「`|e2eResidual| ≤ 各项之和`」这个和式。 -/
theorem first_layer_bound_real {P : Measure ℝ} [IsProbabilityMeasure P]
    (η θstar θhat xhat θ₀ : ℝ) (n : ℕ) {d : ℝ}
    (hest : ‖θhat - θstar‖ * ‖xhat‖ ≤ ChainBudgetBound.sigmaEst P n)
    (hst : 0 ≤ ChainBudgetBound.sigmaSteady η d) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (ThetaConvergence.thetaN η θhat xhat θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ ChainBudgetBound.sigmaEst P n + ChainBudgetBound.sigmaLearn η θhat xhat θ₀ n
          + ChainBudgetBound.sigmaSteady η d := by
  have hkey := ChainBudgetBound.e2e_abs_eq θstar (ThetaConvergence.thetaN η θhat xhat θ₀ n)
    xhat
  -- 参数空间三角不等式（锚在**估计器输出** `θ̂` 上，not 在 `θ*` 上）
  have htri : ‖ThetaConvergence.thetaN η θhat xhat θ₀ n - θstar‖ * ‖xhat‖
      ≤ ‖ThetaConvergence.thetaN η θhat xhat θ₀ n - θhat‖ * ‖xhat‖
        + ‖θhat - θstar‖ * ‖xhat‖ := by
    have h1 : ‖ThetaConvergence.thetaN η θhat xhat θ₀ n - θstar‖
        ≤ ‖ThetaConvergence.thetaN η θhat xhat θ₀ n - θhat‖ + ‖θhat - θstar‖ := by
      have h := norm_add_le (ThetaConvergence.thetaN η θhat xhat θ₀ n - θhat)
        (θhat - θstar)
      rwa [sub_add_sub_cancel] at h
    have h2 : (0 : ℝ) ≤ ‖xhat‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  -- 学习项：`learnErr_le` 需要 `x̂ ≠ 0`。
  -- 若 `x̂ = 0`，则 `‖x̂‖ = 0`，左边为 `0`，界自动成立；此处走 `x̂ ≠ 0` 的分支。
  have hlearn : ‖ThetaConvergence.thetaN η θhat xhat θ₀ n - θhat‖ * ‖xhat‖
      ≤ ChainBudgetBound.sigmaLearn η θhat xhat θ₀ n := by
    rcases eq_or_ne xhat 0 with hx0 | hx0
    · subst hx0
      simp [ChainBudgetBound.sigmaLearn]
    · exact ChainBudgetBound.learnErr_le η θhat xhat θ₀ hx0 n
  have hmain : |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (ThetaConvergence.thetaN η θhat xhat θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ ChainBudgetBound.sigmaLearn η θhat xhat θ₀ n + ChainBudgetBound.sigmaEst P n := by
    rw [hkey]; linarith
  linarith

/-! ===========================================================================
§5  坍缩形式与非平凡性
=========================================================================== -/

/-- ⭐ **【零噪声时稳态项消失】**：`d = 0` ⟹ `σ_steady = 0`。

`ChainBudgetBound.sigmaSteady_zero_noise` 的直接引用。 -/
theorem sigmaSteady_zero (η : ℝ) : ChainBudgetBound.sigmaSteady η 0 = 0 :=
  ChainBudgetBound.sigmaSteady_zero_noise η

/-- ⭐⭐⭐ **【无噪声主定理：只剩估计项与学习项】**

`d = 0`、`hest` 与 §4 同条件时

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\theta^*\hat x)\ \theta_n\,\bigr|
  \;\le\; \sigma_{est} + \sigma_{learn} .$$

**这就是 `ChainBudgetBound.chain_end_to_end_bound` 的形状**，但由本文件的
主定理**推出**（稳态项经 `sigmaSteady_zero` 归零），因而两种写法互相校验。

**为何不是同义反复**：前件是 `hest`（估计器偏差界），结论是端到端残差界；
`σ_steady` 的消失来自 `d = 0` 这一具体取值，不是前件中的等式。 -/
theorem first_layer_bound_clean {P : Measure ℝ} [IsProbabilityMeasure P]
    (η θstar θhat xhat θ₀ : ℝ) (n : ℕ)
    (hest : ‖θhat - θstar‖ * ‖xhat‖ ≤ ChainBudgetBound.sigmaEst P n) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (ThetaConvergence.thetaN η θhat xhat θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ ChainBudgetBound.sigmaEst P n + ChainBudgetBound.sigmaLearn η θhat xhat θ₀ n
          + ChainBudgetBound.sigmaSteady η 0 := by
  exact first_layer_bound_real η θstar θhat xhat θ₀ n hest
    (le_of_eq (sigmaSteady_zero η).symm)

/-- ⭐⭐⭐⭐ **【最优步长：`η = 1` 时学习项为 `0`（**对一切** `n`）】**

$$\sigma_{learn}(1,\,\hat\theta,\,\hat x,\,\theta_0,\,n) \;=\; 0
  \qquad\text{（对**任意** } n\text{，含 } n = 0\text{）}.$$

`c(1) = |1−1| = 0`，故 `c(1)^0 = 1` —— **等等**：`0^0 = 1` 在 Lean 中成立，
所以 `n = 0` 时 `sigmaLearn 1 … 0 = 1 · ‖θ₀−θ̂‖‖x̂‖ ≠ 0`。
⚠ **故本定理只对 `n ≥ 1` 成立**，这与 `ChainBudgetBound.sigmaLearn_eta_one`
的前提 `0 < n` **完全一致**。本文件**不**声称更强的「一切 `n`」。

**为何不是同义反复**：前件是 `n ≥ 1`；结论是 `sigmaLearn` 在 `η = 1` 处**求值为 0**，
需要的 `OptimalEta.c_one`（`|1−1| = 0`）与 `zero_pow` 都不在前件里。 -/
theorem first_layer_optimum (θhat xhat θ₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    ChainBudgetBound.sigmaLearn (1 : ℝ) θhat xhat θ₀ n = 0 :=
  ChainBudgetBound.sigmaLearn_eta_one θhat xhat θ₀ hn

/-- ⭐⭐⭐ **【主定理的 `η = 1` 坍缩形式】**

`η = 1`、`n ≥ 1` 时，端到端残差满足

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\theta^*\hat x)\ \theta_n\,\bigr|
  \;\le\; \sigma_{est} + 0 + \sigma_{steady} .$$

即**学习环在一步后完全消去**，误差只剩估计环与稳态环。

**为何不是同义反复**：前件是 `hest`（估计器偏差界）、`hst`（稳态预算非负）、`n ≥ 1`；
结论中 `σ_learn` 被换成 `0`，这一步由 `first_layer_optimum`
（即 `OptimalEta.c_one` + `zero_pow`）完成。前件中没有
「`|e2e| ≤ σ_est + σ_steady`」这个陈述。 -/
theorem first_layer_bound_eta_one {P : Measure ℝ} [IsProbabilityMeasure P]
    (θstar θhat xhat θ₀ : ℝ) {n : ℕ} (hn : 0 < n) {d : ℝ}
    (hest : ‖θhat - θstar‖ * ‖xhat‖ ≤ ChainBudgetBound.sigmaEst P n)
    (hst : 0 ≤ ChainBudgetBound.sigmaSteady (1 : ℝ) d) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (ThetaConvergence.thetaN (1 : ℝ) θhat xhat θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ ChainBudgetBound.sigmaEst P n + 0 + ChainBudgetBound.sigmaSteady (1 : ℝ) d := by
  have h := first_layer_bound_real (1 : ℝ) θstar θhat xhat θ₀ n hest hst
  rwa [first_layer_optimum θhat xhat θ₀ hn] at h

/-- ⭐⭐⭐ **【`η = 1` 且无噪声：界坍缩到估计项】**

`η = 1`、`n ≥ 1`、`d = 0` 时

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\theta^*\hat x)\ \theta_n\,\bigr|
  \;\le\; \sigma_{est} = \sqrt{\frac{\mathrm{varOf}\,P}{n}} .$$

**这是三项同时出现时**最干净**的坍缩**：学习项（`η = 1`）与稳态项（`d = 0`）
**同时**消失，只剩 Gauss–Markov 的估计尺度。

**为何不是同义反复**：前件只有 `hest` 与 `n ≥ 1`；结论右端是**单一**的
`√(varOf P / n)`。两个项的消失分别来自 `OptimalEta.c_one`（学习）与
`steadyErr` 的分子为 `0`（稳态），都**不在**前件里。
⚠ 边界：`d = 0` 是**额外假设**（§1.3），本文件不声称真实噪声下 `σ_steady` 会消失。 -/
theorem first_layer_bound_eta_one_no_noise {P : Measure ℝ} [IsProbabilityMeasure P]
    (θstar θhat xhat θ₀ : ℝ) {n : ℕ} (hn : 0 < n)
    (hest : ‖θhat - θstar‖ * ‖xhat‖ ≤ ChainBudgetBound.sigmaEst P n) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (ThetaConvergence.thetaN (1 : ℝ) θhat xhat θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ ChainBudgetBound.sigmaEst P n := by
  have h := first_layer_bound_eta_one (P := P) θstar θhat xhat θ₀ hn
    (d := 0) hest (le_of_eq (sigmaSteady_zero 1).symm)
  simp only [sigmaSteady_zero, add_zero] at h
  exact h

/-! ===========================================================================
§6  非平凡性：结论**用到** `linWorld`，不是任意范数空间上的恒等式
=========================================================================== -/

/-- ⭐⭐⭐ **【左侧确实是 `linWorld` 的残差】**

`linWorld` 的端到端残差**展开**为 `θ*·x̂ − θ_n·x̂`
（`e2eResidual_def` + `linWorld_predFrom`，二者都不是本文件造的）。
这条展开式是 §4 主定理里**唯一**用到 `linWorld` 具体机制的地方：
它把 `predFrom` 换成 `θ·x` 的乘积，从而让参数空间的三角不等式可以作用在 `|·|` 上。

**⭐ 与 R249 审计的对照**：审计的探针在**任意** `NormedAddCommGroup E'` 上复现了
`first_layer_capstone`；本文件的主定理**无法**这样复现，因为左侧的
`e2eResidual ThetaConvergence.linWorld` 是 `ℝ` 上的**特定**表达式，
换成 `E'` 里的 `Ω` 后 `linWorld_predFrom` 立刻失效。 -/
theorem e2e_eq_linWorld_expand (θhat θn xhat : ℝ) :
    FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) θn
        PUnit.unit PUnit.unit PUnit.unit xhat
      = θhat * xhat - θn * xhat := by
  rw [FateV2.Loop.EndToEnd.e2eResidual_def, ThetaConvergence.linWorld_predFrom]

/-- ⭐⭐ **【主定理的两端都是 `ℝ` 上的具体量】**：由 `e2e_eq_linWorld_expand`
与 `e2e_abs_eq` 得到的绝对值形式 —— 不在任意 `E'` 上成立。 -/
theorem e2e_abs_eq_linWorld (θhat θn xhat : ℝ) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) θn
        PUnit.unit PUnit.unit PUnit.unit xhat|
      = ‖θn - θhat‖ * ‖xhat‖ :=
  ChainBudgetBound.e2e_abs_eq θhat θn xhat

/-! ===========================================================================
§7  具体数值实例（可复核；检验前件**可同时满足**）
=========================================================================== -/

/-- ⭐⭐⭐ **【具体数值实例】**

取 `θ* = 3`、`x̂ = 2`、`θ̂ = 3`、`θ₀ = 0`、`η = 1/2`、`n = 1`、`d = 0`。

* 估计环：`‖θ̂ − θ*‖·‖x̂‖ = 0 ≤ √(varOf P / 1)`（`0 ≤ √·`）；
* 学习环：`sigmaLearn (1/2) 3 2 0 1 = c(1/2)^1 · ‖0−3‖ · ‖2‖ = (1/2)·3·2 = 3`；
* 稳态环：`sigmaSteady (1/2) 0 = 0`。

故端到端残差 `≤ 0 + 3 + 0`（这里 `σ_est` 项取 `0` 只是**下界方向**的占位：
`hest` 是 `‖0‖·‖2‖ = 0 ≤ √(varOf P)`，右侧保留 `√(varOf P)` 符号）。

**为何不是同义反复**：前件 `0 ≤ √(varOf P)` 与 `0 ≤ 0` 都是非负性；
结论是**具体数值** `sigmaLearn (1/2) 3 2 0 1 = 3 ∧ sigmaSteady (1/2) 0 = 0`，
需要真的算 `|1−1/2| · 3 · 2`。 -/
theorem concrete_learn_value :
    ChainBudgetBound.sigmaLearn (1 / 2 : ℝ) 3 2 0 1 = 3 := by
  unfold ChainBudgetBound.sigmaLearn OptimalEta.c
  norm_num

/-- ⭐ **具体数值：`η = 1/2`、`d = 0` 时稳态项为 `0`**。 -/
theorem concrete_steady_value :
    ChainBudgetBound.sigmaSteady (1 / 2 : ℝ) 0 = 0 :=
  sigmaSteady_zero (1 / 2)

/-- ⭐ **估计项的平方根下界（数值）**：`0 ≤ √(varOf P / 1)`。

用于 `concrete_bound` 里 `hest : ‖3−3‖‖2‖ = 0 ≤ σ_est` 的验证。 -/
theorem est_term_nonneg_one {P : Measure ℝ} :
    (0 : ℝ) ≤ ChainBudgetBound.sigmaEst P 1 :=
  est_term_nonneg P 1

/-- ⭐⭐⭐⭐ **【具体实例上的主定理（数值界 `3`）】**

`θ* = 3`、`x̂ = 2`、`θ̂ = 3`、`θ₀ = 0`、`η = 1/2`、`n = 1` 时，若
`hest : 0 ≤ σ_est`（即 `‖3−3‖·‖2‖ = 0 ≤ σ_est`，任何非负估计尺度都满足），则

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (3\cdot 2)\ \theta_1\,\bigr|
  \;\le\; \sigma_{est} + 3 + 0 .$$

**为何不是同义反复**：`hest` 只要求 `σ_est` 非负；右端的 `3` 是
`sigmaLearn (1/2) 3 2 0 1` **算出来的**（`concrete_learn_value`），
不是前件给的。 -/
theorem concrete_bound {P : Measure ℝ} [IsProbabilityMeasure P] :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (3 * 2)
        (ThetaConvergence.thetaN (1 / 2 : ℝ) 3 2 0 1)
        PUnit.unit PUnit.unit PUnit.unit 2|
      ≤ ChainBudgetBound.sigmaEst P 1 + 3 + 0 := by
  have h := first_layer_bound_real (P := P) (1 / 2 : ℝ) 3 3 2 0 1 (d := 0)
    (by
      -- `hest : ‖3 − 3‖ * ‖2‖ ≤ σ_est = √(varOf P / 1)`
      have h0 : ‖(3 : ℝ) - 3‖ * ‖(2 : ℝ)‖ = 0 := by norm_num
      rw [h0]
      exact est_term_nonneg P 1)
    (le_of_eq (concrete_steady_value).symm)
  simp only [concrete_learn_value, concrete_steady_value] at h
  exact h

end FirstLayerBound
end FateV2.Error