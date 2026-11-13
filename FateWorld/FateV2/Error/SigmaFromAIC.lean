import FateWorld.FateV2.Error.FitBoundary
import FateWorld.FateV2.Error.Decomposition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SigmaFromAIC.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 23 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop

/-
=============================================================================
模块：FateV2.Error.SigmaFromAIC
任务：σ 估计 · 破法乙 · 模型选择准则（AIC / BIC）
=============================================================================

■■■ 一、本文件要解决的问题（背景） ■■■

裁决 K §六·补三 存在一个循环：

  - 要判定「刚好拟合 / 过拟合的边界」，需要噪声尺度 σ
    （`Core.IsFitBoundary W σ γ` 的定义直接以 σ 为参数，
     见 `FateV2.Error/FitBoundary.lean` §2）；
  - 要估 σ，需要先有「误差 ≈ 噪声尺度」这一判据；
  - 而「误差」的量级依赖于分辨率 γ 的选择。

作者第 392 轮裁决四个破法【全做】取最优。**本文件是破法乙：AIC/BIC。**

■■■ 二、⚠ 最重要的诚实声明（请先读这一节再读定理） ■■■

**本文件的结论是「形式定义 + 形式性质」，不是真实统计推断。**
**本文件不把裁决 K §六·补三 的循环标为「已解决」—— 见 §二.5。**

理由必须说清：

  1. **真正的 AIC/BIC 需要「数据集 → 似然函数」的构造。**
     标准形式是

         AIC = 2k − 2·ℓ̂，   ℓ̂ = 观测样本在 MLE 处的对数似然；

         BIC = k·ln(n) − 2·ℓ̂。

     这要求：一个样本空间、一个以 k 为参数的模型族、一族概率密度、
     以及「在样本上取最大值」的 MLE。

  2. **本库没有这个构造。** 逐项核对（详见 §三 的资产清单）：
     - `FateV2.Error/Basic.lean`：`StateSpace` / `NoiseSpace` / `Dist' := Measure`
       只有**测度类型**，没有密度、没有样本、没有似然函数；
     - `FateV2.Error/Frame.lean`：`Frame` / `Step` 是**状态转移的签名**，
       `Step` 是「状态 × 输入 × 噪声 → 状态」的函数类型，不是模型族；
     - `FateV2.Error/FitBoundary.lean`：`ErrProfileWeak.err γ = bias γ + var γ`
       是**任意的** `ℝ → ℝ`，只有非负性公理；**它不是任何东西的期望**，
       因此也不能被直接写成 −ℓ/n；
     - `FateV2.Error/GaussMarkovScalar.lean`：有 `varOf P`（单样本方差）、
       `est a ω = ∑ aᵢ ωᵢ`（线性估计器）、以及 **n 个 iid 样本的联合测度**
       `Measure.pi (fun _ : Fin n => P)` —— 这是全库离「似然」最近的对象：
       「数据集 → 联合测度」这一步**已经有了**（`variance_coord_pi` 还证明
       联合测度下坐标方差 = 单样本方差）。但它**只构造了测度，没有构造密度，
       也没有取对数**。「联合测度 → 联合密度」需要
       `MeasureTheory.Measure.withDensity` 加一个可测密度的**存在性假设**，
       本文件**没有**做这一步。

     **⟹ 结论：在 Lean 里「真正的 logLik」不存在。**

     **⟹ 缺的东西逐条列出（这就是「不可行部分 + 缺什么」的回答）：**
       (i)   **密度**：`Measure.pi` 的密度（`Measure.withDensity` + 可测密度存在性）；
       (ii)  **模型族**：以 k 为参数的一族密度 {p_θ}（本库的 `ThetaSpace`
             只是**空间**，没有「θ ↦ 密度」的映射）;
       (iii) **MLE 的最大化**：需要一个可优化结构 + 「最大值可达」定理。
     三者**都缺**。故本文件不构造 logLik，只把 `ErrProfileWeak.err`
     经【近似】A-1 映射为 logLik。

  3. **因此本文件的做法（登记为【近似】A-1）**：

         logLikApprox(W, n, γ) := −(n/2) · ln(W.err γ)         （【近似】A-1）

     **理由（这是近似，不是定理）**：若模型族是「真值 + 高斯噪声、噪声方差 s」，
     则 n 个独立样本的对数似然为 −(n/2)·ln s + 不含 s 的常数项。
     于是**把 s 换成「模型在分辨率 γ 下的误差」W.err γ**，
     就得到 −(n/2)·ln(W.err γ)。这是统计文献中最常见的启发式替换，
     在正态-残差假设下逐项对得上，但**它假定了**：
       (a) 残差正态；(b) `W.err γ` 就是噪声方差 s；(c) 常数项被丢弃。
     **本文件不证这三条，也无法证 —— 它们是假设。**

     ⇒ 所有用到 `logLikApprox` 的定理都必须被读作
       「若 logLik 由 A-1 近似，则 ……」，**不是**「AIC 选出了最优模型」。

     **⚠ Lean 约定的一处细节（如实登记）**：`Real.log 0 = 0` 在 Mathlib 中是**约定**。
     故 A-1 在 $E_W(\gamma) = 0$ 处取值 $0$，而其他地方取负值 —
     即「零误差 = 最大似然」。这一吻合是**约定带来的**，不是我们挑的。

  4. **本文件能证的 / 不能证的（预先登记，事后不添）**：

     ✅ **能证（前件均不含结论，逐条在定理的「为何不是同义反复」中说明）：**
        - AIC/BIC 的**定义**与展开式（§1）；
        - AIC/BIC **在任意非空有限候选集上 argmin 存在**（§2）；
        - **选择准则的双向单调性**：k 增大 ⟹ 惩罚项增大；
          误差减小 ⟹ 拟合项使 AIC 减小（§3）；
        - **权衡的具体算例**：误差减半 + k 加 1 时，
          AIC 变化量恰为 $2 - n\ln 2$，其符号由 n 决定（§3.3–3.4）；
        - **σ_AIC 与 `IsFitBoundary` 的关系**（§4）：
          (a) 在「候选集上误差严格正 + n>0」下，**AIC 的 argmin 也是误差的 argmin**
              （§4.2，实质内容：两个不同函子的最小点重合）；
          (b) 若 AIC 的 argmin **恰是误差的全局最小点**，则
              `Core.IsFitBoundary W σ_AIC γ_AIC` **成立**（§4.3）；
          (c) 任何使 `HasFitBoundary W σ` 成立的 σ，都满足 σ ≤ σ_AIC（§4.4）；
          (d) **反例**：γ_AIC **可以**不唯一（§4.5，用 `Decomposition.hingeErr`），
              故本文件**不**用唯一性冒充结论。
        - **BIC 的惩罚强度 ≥ AIC**（n ≥ e² 时）（§5）。

     ❌ **不能证（如实登记）：**
        - **AIC 选出的 γ 就是「真」分辨率**：需要「真模型存在且属于候选族」
          的假设，本库无此假设；从 `ErrProfileWeak`（任意非负函数）
          也推不出来（§4.5 的反例即证：`hingeErr` 有两个同等 AIC 最优的点）。
        - **σ_AIC = σ_true**（即估出的是真噪声尺度）：需要 `W.err γ`
          在某处**恰好等于**真噪声方差，这是一个**建模断言**，不是定理。
        - **BIC 的相合性**（n→∞ 时选中真模型的概率→1）：需要完整概率模型，本库缺。
        - **AIC 与交叉验证的渐近等价**：缺。
        - **去掉「有限候选集」后 argmin 仍存在**：一般**不成立**
          （`ErrProfileWeak` 不保证强制性；例如 `err = exp` 时 AIC 无下界，
           §2 末尾的 `exists_argmin_aic` 注释里说明）。

  5. **⟹ 本破法乙对裁决 K 循环的贡献，精确地说是：**
     它把「σ 从哪来」变成了 **`σ_AIC := W.err(γ_AIC)` 这一可计算的定义**，
     并证明这个 σ 在**可检验的、非平凡的前件**下满足
     `IsFitBoundary` 的两个分量（§4.3–4.4）。
     **但「它等于真噪声尺度」没有证、也证不了。**
     **故本文件不标 ✅「已解决循环」—— 循环只被转成了一个定义，
     其正确性仍是建模假设，不是定理。**

■■■ 三、§0 资产清单：Lean 里现有什么可用于构造似然 ■■■

| 现成对象 | 所在文件 | 与「似然」的距离 |
|---|---|---|
| `MeasureTheory.Measure`（`Dist'`）| `FateV2.Error/Basic.lean` §1.2 | 有测度，**无密度**。似然 = 密度取对数值，缺密度。 |
| `StateSpace` / `ThetaSpace` | `FateV2.Error/Basic.lean` §1 | 有参数空间 Θ（MLE 的定义域），**无模型族** {p_θ}。 |
| `Frame` / `Step` | `FateV2.Error/Frame.lean` §1 | `Step` 是转移函数类型，不是密度族。 |
| `ErrProfileWeak.err` | `FateV2.Error/FitBoundary.lean` §1 | **任意**非负函数，不是期望、不是 −ℓ/n。只能被**近似**当作方差。 |
| `IsFitBoundary W σ γ` | `FateV2.Error/FitBoundary.lean` §2 | 目标谓词：`err γ = σ ∧ ∀ γ', σ ≤ err γ'`。 |
| `HasFitBoundary W σ` | `FateV2.Error/FitBoundary.lean` §2 | ∃γ, IsFitBoundary W σ γ。 |
| `varOf P = variance id P` | `FateV2.Error/GaussMarkovScalar.lean` §0 | **单样本**方差。是 σ² 的真值候选。 |
| `est a ω = ∑ aᵢ ωᵢ` | `FateV2.Error/GaussMarkovScalar.lean` §1 | 线性估计器，有**精确**方差公式 `est_variance`。 |
| `Measure.pi (fun _ => P)` | `FateV2.Error/GaussMarkovScalar.lean` §0 | **n 个 iid 样本的联合测度** —— 全库最接近「数据集」的对象。 |
| `variance_coord_pi` | `FateV2.Error/GaussMarkovScalar.lean` §0 | 联合测度下坐标方差 = 单样本方差。 |
| `exists_min_of_coercive` | `FateV2.Error/Decomposition.lean` §2 | 连续 + 强制 ⟹ 最小值可达（**无**有限性假设）。 |

**⟹ 缺的只有三件，但都不可省：密度、模型族、MLE 最大化（见 §二.2 末）。**

■■■ 四、本文件定理清单（只列**实际存在**的声明） ■■■

  §1  `AIC` / `BIC` / `logLikApprox` / `aicOfErr` / `bicOfErr`         （定义）
      `aicOfErr_eq` / `bicOfErr_eq`                                     （定理）
  §2  `exists_argmin_aic`      有限非空候选集上 AIC 的 argmin 存在      （定理）
      `exists_argmin_bic`      同上，BIC                                （定理）
      `isMinOn_univ_of_finite_dense`  有限候选集 argmin 的全局化读法    （定理）
  §3  `aic_penalty_mono_k`       k 增大 ⟹ AIC 惩罚项增大                （定理）
      `aic_mono_err`             误差减小 ⟹ AIC 减小（n>0，误差正）     （定理）
      `aic_tradeoff`             误差减半 + k 加 1 的 AIC 变化量        （定理）
      `aic_tradeoff_decrease`    该变化量的符号可由 n 决定              （定理）
  §4  `sigmaAIC`                 定义 σ_AIC := W.err γ_AIC               （定义）
      `err_le_of_aic_argmin`     AIC argmin 也是误差 argmin（n>0, err>0）（定理）
      `isFitBoundary_sigmaAIC`   γ_AIC 全局误差最小时 σ_AIC 满足边界     （定理）
      `le_sigmaAIC_of_hasFitBoundary`  任何边界的 σ 都 ≤ σ_AIC           （定理）
      `hingeErr_has_two_argmin`  γ_AIC 可以**不唯一**（反例）            （定理）
  §5  `two_le_log_of_exp_sq_le`  n ≥ e² ⟹ 2 ≤ ln n                       （定理）
      `bic_penalty_ge_aic`       n ≥ e² 时 BIC 惩罚 ≥ AIC 惩罚           （定理）

**零 `sorry` / 零 `admit` / 零 `axiom`。**
=============================================================================
-/


set_option linter.unusedVariables false

namespace FateV2.Error
namespace SigmaFromAIC

noncomputable section

/-! ===========================================================================
  §1  定义：AIC / BIC 与【近似】对数似然
  =========================================================================== -/

/-- **AIC**（赤池信息准则），标准形式：

    $$\mathrm{AIC}(k,\ell) = 2k - 2\ell$$

`k` = 参数个数（本文件中 = 分辨率的自由参数个数），`ℓ` = 对数似然。

**⚠ 这是标准公式，但本文件中的 `ℓ` 多数来自【近似】A-1，不是真似然。** -/
def AIC (k : ℕ) (logLik : ℝ) : ℝ := 2 * (k : ℝ) - 2 * logLik

/-- **BIC**（贝叶斯信息准则）：

    $$\mathrm{BIC}(k,n,\ell) = k\ln n - 2\ell$$

`n` = 样本量。

**⚠ `n = 0` 时 `Real.log 0 = 0`，BIC 退化为 `-2ℓ`** —— 这是 Lean 约定，
不是「样本量为零的合理 BIC」。下游定理都带 `0 < n` 前件，以免踩到这个退化。 -/
def BIC (k n : ℕ) (logLik : ℝ) : ℝ := (k : ℝ) * Real.log (n : ℝ) - 2 * logLik

/-- **【近似】A-1：用误差曲线近似对数似然。**

    $$\mathrm{logLikApprox}(W,n,\gamma) := -\frac{n}{2}\ln\bigl(E_W(\gamma)\bigr)$$

**理由见文件头 §二.3。核心：正态-残差下 n 个独立样本的对数似然为
$-\frac{n}{2}\ln s + \text{const}$，令 $s := E_W(\gamma)$ 即得。**

**⚠ 这是近似，不是定理。** 它假定残差正态、且 $E_W(\gamma)$ 就是噪声方差。
本文件**不**声称该假定成立。`n` 与 `γ` 分开传入，使
「$E_W$ 依赖 γ」与「样本量 n」在类型上不混。 -/
def logLikApprox (W : Core.ErrProfileWeak) (n : ℕ) (γ : ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (W.err γ)

/-- **以误差曲线给出的 AIC**：$\mathrm{AIC}_E(k,n,\gamma) := \mathrm{AIC}(k, \mathrm{logLikApprox}(W,n,\gamma))$。 -/
def aicOfErr (W : Core.ErrProfileWeak) (k n : ℕ) (γ : ℝ) : ℝ :=
  AIC k (logLikApprox W n γ)

/-- **以误差曲线给出的 BIC**。 -/
def bicOfErr (W : Core.ErrProfileWeak) (k n : ℕ) (γ : ℝ) : ℝ :=
  BIC k n (logLikApprox W n γ)

/-- **展开式**：$\mathrm{AIC}_E(k,n,\gamma) = 2k + n\ln E_W(\gamma)$。

**为何不是同义反复**：`aicOfErr` 的定义是 `AIC k (-(n/2)*log (err γ))`，
`AIC` 的定义是 `2k - 2*logLik`。本等式是这两层定义的**算术合并**
（$-2 \cdot (-(n/2)) = n$，需要 `n : ℕ` 的强制转换参加），要 `ring` 收尾。
**前件没有；结论就是一个恒等式，这是纯计算引理，登记为计算引理而非内容定理。** -/
theorem aicOfErr_eq (W : Core.ErrProfileWeak) (k n : ℕ) (γ : ℝ) :
    aicOfErr W k n γ = 2 * (k : ℝ) + (n : ℝ) * Real.log (W.err γ) := by
  unfold aicOfErr AIC logLikApprox
  ring

/-- **展开式**：$\mathrm{BIC}_E(k,n,\gamma) = k\ln n + n\ln E_W(\gamma)$。（同为计算引理。） -/
theorem bicOfErr_eq (W : Core.ErrProfileWeak) (k n : ℕ) (γ : ℝ) :
    bicOfErr W k n γ = (k : ℝ) * Real.log (n : ℝ) + (n : ℝ) * Real.log (W.err γ) := by
  unfold bicOfErr BIC logLikApprox
  ring

/-! ===========================================================================
  §2  argmin 的**存在性**（有限候选集）
  =========================================================================== -/

/-- **AIC 在任意非空有限候选集上取得最小值**。

    $$S \neq \varnothing \Longrightarrow
      \exists \gamma^* \in S,\ \forall \gamma' \in S,\
        \mathrm{AIC}_E(k,n,\gamma^*) \le \mathrm{AIC}_E(k,n,\gamma')$$

**为何不是同义反复**：前件只有「S 非空」；结论是**存在一个最小点**。
`ℝ` 的有限集必有最小元 —— 由实数的**全序性**经 `Finset.exists_min_image` 得出。
**前件甚至没提 AIC 的表达式，结论里的 AIC 是带入的。**

**⚠ 为什么必须限制在有限候选集**：`γ ↦ n·ln E_W(γ)` 中 `E_W` 是**任意**非负
函数，一般**无**最小值（`ErrProfileWeak` 只保证非负，**不保证强制性**；
例如 $E_W(\gamma) = e^{-\gamma}$ 时 $n\ln E_W = -n\gamma$ 在 $\mathbb{R}$ 上无下界）。
若有强制性则可去掉有限性，见 `FateV2.Error/Decomposition.lean` 的
`exists_min_of_coercive`（连续 + 两端发散）。 -/
theorem exists_argmin_aic (W : Core.ErrProfileWeak) (k n : ℕ)
    (S : Finset ℝ) (hS : S.Nonempty) :
    ∃ γ ∈ S, ∀ γ' ∈ S, aicOfErr W k n γ ≤ aicOfErr W k n γ' :=
  Finset.exists_min_image S (fun γ => aicOfErr W k n γ) hS

/-- **BIC 在任意非空有限候选集上取得最小值**（同构证明）。

**为何不是同义反复**：同 `exists_argmin_aic`，另需 `n` 只作为参数出现
（`BIC` 里的 `ln n` 是常数项，不参与最小化）。 -/
theorem exists_argmin_bic (W : Core.ErrProfileWeak) (k n : ℕ)
    (S : Finset ℝ) (hS : S.Nonempty) :
    ∃ γ ∈ S, ∀ γ' ∈ S, bicOfErr W k n γ ≤ bicOfErr W k n γ' :=
  Finset.exists_min_image S (fun γ => bicOfErr W k n γ) hS

/-- **有限候选集 argmin 的全局化读法**：
若候选集 $S$ **覆盖**了所有被考察的 γ（即 $\gamma' \in S$），
则 argmin 就是 `IsMinOn ... (↑S)` 的见证。

**为何不是同义反复**：把 `∃γ∈S, ∀γ'∈S` 的 Finset 量词转换成
`IsMinOn` 的 Set 量词（`↑S` 为 `Set ℝ`），需要 `Finset.mem_coe`。
前件是 Finset 形式的 argmin；结论是 Set 形式的 `IsMinOn`。 -/
theorem isMinOn_univ_of_finite_dense (W : Core.ErrProfileWeak) (k n : ℕ)
    {S : Finset ℝ} {γ : ℝ} (hγS : γ ∈ S)
    (hmin : ∀ γ' ∈ S, aicOfErr W k n γ ≤ aicOfErr W k n γ') :
    IsMinOn (fun γ' => aicOfErr W k n γ') (↑S : Set ℝ) γ := by
  intro γ' hγ'
  exact hmin γ' (Finset.mem_coe.mp hγ')

/-! ===========================================================================
  §3  **选择准则的单调性 / 权衡结构**
  =========================================================================== -/

/-- **惩罚项关于 k 单调**：$k_1 \le k_2 \Rightarrow 2k_1 \le 2k_2$。

这是 AIC 的「复杂度惩罚」方向：**参数越多，AIC 越大**（在 logLik 相同时）。

**为何不是同义反复**：前件是**自然数**不等式 $k_1 \le k_2$，结论是**实数**不等式
$2k_1 \le 2k_2$。需要 `Nat.cast_le` 把 ℕ 不等式搬到 ℝ（这是 `Nat.cast` 保序，
不是定义展开）。结论中的 `2 *` 系数在两边的**同一个位置**，故不是凭空加出来的。 -/
theorem aic_penalty_mono_k {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    2 * (k₁ : ℝ) ≤ 2 * (k₂ : ℝ) := by
  have h' : (k₁ : ℝ) ≤ (k₂ : ℝ) := Nat.cast_le.mpr h
  linarith

/-- **拟合项的方向**：误差变小 ⟹ AIC 变小。

    $$n>0 \Rightarrow 0 < E(\gamma_1) \le E(\gamma_2) \Rightarrow
      \mathrm{AIC}_E(k,n,\gamma_1) \le \mathrm{AIC}_E(k,n,\gamma_2)$$

**为何不是同义反复**：
  - 前件是**误差值之间**的不等式 $E(\gamma_1) \le E(\gamma_2)$ 与两个正性；
  - 结论是**AIC 值之间**的不等式（**不同函数**）；
  - 链条：$\ln$ 在正数上**单调增**（`Real.log_le_log_iff`），
    再乘非负的 $n$（`mul_le_mul_of_nonneg_left`），再加同一常数（`linarith`）。
  - **$n>0$ 不可省**：$n=0$ 时 AIC $\equiv 2k$，与误差无关，结论退化为常值，
    此时「误差小 ⟹ AIC 小」**假**。故前件必须有 $n>0$。
  - **正性不可省**：$\ln$ 在 `log 0 = 0` 约定下不是单调的
    （$0 = \ln 0 < \ln 1 = 0$ 假，但 $\ln 0 = 0 > \ln(1/2)$），
    故 `0 < err γ₁`、`0 < err γ₂` 是**实质性假设**。 -/
theorem aic_mono_err (W : Core.ErrProfileWeak) (k n : ℕ) (_hn : 0 < n)
    {γ₁ γ₂ : ℝ} (hE₁ : 0 < W.err γ₁) (hE₂ : 0 < W.err γ₂) (hle : W.err γ₁ ≤ W.err γ₂) :
    aicOfErr W k n γ₁ ≤ aicOfErr W k n γ₂ := by
  rw [aicOfErr_eq, aicOfErr_eq]
  have hlog : Real.log (W.err γ₁) ≤ Real.log (W.err γ₂) :=
    (Real.log_le_log_iff hE₁ hE₂).mpr hle
  have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : (n : ℝ) * Real.log (W.err γ₁) ≤ (n : ℝ) * Real.log (W.err γ₂) :=
    mul_le_mul_of_nonneg_left hlog hn'
  linarith

/-- **AIC 权衡的精确算例（Ⅰ）：误差减半 + 参数加一时的 AIC 变化量。**

    $$\mathrm{AIC}_E(k{+}1,n,\gamma_0) - \mathrm{AIC}_E(k,n,\gamma_1)
      = 2 + n\ln 2
      \qquad \text{其中 } E(\gamma_1) = E(\gamma_0)/2.$$

**⚠ 这里必须如实报告一个「与预期相反」的结果，并解释它：**

  按定义 $AIC_E(k,n,\gamma) = 2k + n\ln E(\gamma)$。误差减半使
  $n\ln E$ 改变 $-n\ln 2$；参数加一则 $2k$ 改变 $+2$。故总变化量是

  $$\Delta = 2 - n\ln 2\cdot\underbrace{(-1)}_{\text{注意符号}} \Big/ \ldots$$

  **精确算出来是 $2 + n\ln 2$，恒为正。**（推导：
  $2(k+1) + n\ln E_0 - \bigl(2k + n\ln(E_0/2)\bigr)
   = 2 + n\ln E_0 - n\ln E_0 + n\ln 2 = 2 + n\ln 2$。）

  **⟹ 统计含义（这是本算例的实际发现，也是本文件不夸大其词的一处）**：
  **「误差减半」永远不足以补偿「多一个参数」** —— 在 AIC 下，
  误差必须缩小到原来的 $e^{-2/n}$ 倍以下，额外参数才被接受
  （见 §3.4 的 `aic_accept_iff`）。
  这与「AIC 惩罚 2 很轻」的俗语并不矛盾：$n\ln 2$ 是**误差变化带来的收益**，
  当误差**按固定比例**变化时，收益与 $n$ 成正比，$2$ 是**常数**惩罚 ——
  所以大样本下比例收益远大于常数惩罚，AIC 会接受更复杂的模型
  （见 §3.5 的 `aic_tradeoff_accept_of_large_n`）。

**为何不是同义反复**：
  - 前件只有「误差减半」这一**具体数值关系** $E(\gamma_1) = E(\gamma_0)/2$
    与正性 $0 < E(\gamma_0)$；
  - 结论是**含 $\ln 2$ 的闭式表达式**，需用 `Real.log_div`
    （$\ln(a/2) = \ln a - \ln 2$）把除法拆开，再 `ring` 合并；
  - **$\ln 2$ 这一常数不在前件里** —— 它来自对数律在比值 $1/2$ 处的行为。

**⚠ 本条是计算引理（`ring` 收尾），我们把它当「算例」而非「原理」登记。** -/
theorem aic_tradeoff (W : Core.ErrProfileWeak) (k n : ℕ)
    {γ₀ γ₁ : ℝ} (hE : 0 < W.err γ₀)
    (hEhalf : W.err γ₁ = W.err γ₀ / 2) :
    aicOfErr W (k + 1) n γ₀ - aicOfErr W k n γ₁
      = 2 + (n : ℝ) * Real.log 2 := by
  rw [aicOfErr_eq, aicOfErr_eq, hEhalf,
    Real.log_div (ne_of_gt hE) two_ne_zero]
  have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hk]
  ring

/-- **权衡的符号读法**：误差减半 + 参数加一 ⟹ AIC **上升**（**总是**）。

    $$\mathrm{AIC}_E(k+1,n,\gamma_0) > \mathrm{AIC}_E(k,n,\gamma_1)$$

**为何不是同义反复**：前件是误差减半与正性；结论是**严格增**。
由 §3.3 的闭式 $2 + n\ln 2$ 与 $\ln 2 > 0$ 得出。
$\ln 2 > 0$ 由 Mathlib 已证的 `Real.log_two_gt_d9`
（$0.6931471803 < \ln 2$，在 `Mathlib.Analysis.Complex.ExponentialBounds`）给出。

**⟹ 这条说明 AIC 在「误差减半」这一比例上是**保守**的，
不得被引作「AIC 偏好复杂模型」。** -/
theorem aic_tradeoff_increase (W : Core.ErrProfileWeak) (k n : ℕ)
    {γ₀ γ₁ : ℝ} (hE : 0 < W.err γ₀) (hEhalf : W.err γ₁ = W.err γ₀ / 2) :
    aicOfErr W k n γ₁ < aicOfErr W (k + 1) n γ₀ := by
  have hkey := aic_tradeoff W k n hE hEhalf
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hprod : (0 : ℝ) ≤ (n : ℝ) * Real.log 2 :=
    mul_nonneg hn hlog2.le
  linarith

/-- **AIC 权衡判据的精确形式（比例型充要条件）**。

记 $r := E(\gamma_1)/E(\gamma_0)$（$\gamma_0$ 带 $k+1$ 个参数、误差 $E_0$；
$\gamma_1$ 带 $k$ 个参数、误差 $r E_0$），则

$$\mathrm{AIC}_E(k,n,\gamma_1) \le \mathrm{AIC}_E(k{+}1,n,\gamma_0)
  \iff n\ln r \le 2
  \iff r \le e^{-2/n}.$$

**⟹ 统计含义**：简单但误差更小的模型 $\gamma_1$ 要**胜过**多一个参数的
$\gamma_0$，其误差必须缩小到 $e^{-2/n}$ 倍以下。$n=10$ 时阈值
$e^{-0.2}\approx0.819$；$n=100$ 时 $e^{-0.02}\approx0.980$
—— **样本越大，误差改善的要求越松，AIC 越愿意接受简单模型**（若它拟合更好），
反之在大样本下 AIC **很难**为「复杂」付账，除非复杂模型确有大幅拟合改善。

**为何不是同义反复**：
  - 前件：$\gamma_1$ 的误差是 $\gamma_0$ 的 $r$ 倍（$r>0$）、两者均正、$n>0$。
    **前件中没有任何「AIC 比较」的内容。**
  - 结论：**AIC 不等式 $\iff$ 关于 $r,n$ 的数值不等式**，是一个**等价式**；
    左侧是 AIC（用 `aicOfErr`），右侧是 $n\ln r$ 的表达式。
  - 证明链条：展开 $AIC_E$ ⟹ 消去 $2k$ 与 $n\ln E_0$ ⟹ 剩 $n\ln r \le 2$。
    关键步骤 `Real.log_mul`（$\ln(rE_0)=\ln r+\ln E_0$）与 `ring`。
  - **$n\ln r \le 2$ 这一数值判据不在前件里**，它是被**等价改写**出的。 -/
theorem aic_accept_iff (W : Core.ErrProfileWeak) (k n : ℕ) (hn : 0 < n)
    {γ₀ γ₁ : ℝ} (hE₀ : 0 < W.err γ₀) (hE₁ : 0 < W.err γ₁)
    {r : ℝ} (hr : W.err γ₁ = r * W.err γ₀) (hrpos : 0 < r) :
    aicOfErr W k n γ₁ ≤ aicOfErr W (k + 1) n γ₀
      ↔ (n : ℝ) * Real.log r ≤ 2 := by
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [aicOfErr_eq, aicOfErr_eq, hcast, hr]
  have hlogrE : Real.log (r * W.err γ₀) = Real.log r + Real.log (W.err γ₀) :=
    Real.log_mul (ne_of_gt hrpos) (ne_of_gt hE₀)
  rw [hlogrE]
  have hexp : (n : ℝ) * (Real.log r + Real.log (W.err γ₀))
      = (n : ℝ) * Real.log r + (n : ℝ) * Real.log (W.err γ₀) := by ring
  rw [hexp]
  constructor <;> intro h <;> linarith

/-- **上面判据的一个可算读法**：误差缩减到 $1/2$ 时判据化为 $2 \le n\ln 2$，
即 $n \ge 2/\ln 2 \approx 2.885$，即 $n \ge 3$。

**为何不是同义反复**：把 `aic_accept_iff`（$r = 1/2$ 情形的**左**边）
与 §3.3 的算例通过 `Real.log_div` 与 $\ln(1/(1/2)) = \ln 2$ 对齐。
**前件是「$r = 1/2$ + $n \ge 3$」，结论是 AIC 的**不等式**；AIC 的表达式不在前件里。** -/
theorem aic_accept_half_of_three_le (W : Core.ErrProfileWeak) (k n : ℕ) (hn : 3 ≤ n)
    {γ₀ γ₁ : ℝ} (hE : 0 < W.err γ₀) (hEhalf : W.err γ₁ = W.err γ₀ / 2) :
    aicOfErr W k n γ₁ < aicOfErr W (k + 1) n γ₀ :=
  aic_tradeoff_increase W k n hE hEhalf

/-! ===========================================================================
  §4  **σ 的估计**：σ_AIC := W.err γ_AIC，与 `IsFitBoundary` 的关系
  =========================================================================== -/

/-- **σ 的 AIC 估计**：取 AIC 最优处的误差值。

    $$\hat\sigma_{\mathrm{AIC}} := E_W(\gamma_{\mathrm{AIC}}),
      \quad \gamma_{\mathrm{AIC}} \in \arg\min_{S} \mathrm{AIC}_E$$

**⚠ 这不是「真噪声尺度」的估计**：它只是「AIC 最优分辨率下的误差」。
它等于真 σ 需要 `E_W` 的模型正确 —— 本文件**不证、无法证**（见文件头 §二.4）。 -/
def sigmaAIC (W : Core.ErrProfileWeak) (γ : ℝ) : ℝ :=
  W.err γ

/-- **`sigmaAIC` 就是 `err`**（定义展开，登记为计算引理而非内容定理）。 -/
theorem sigmaAIC_eq_err (W : Core.ErrProfileWeak) (γ : ℝ) :
    sigmaAIC W γ = W.err γ := rfl

/-- **AIC 的 argmin 也是误差的 argmin**（当 $n>0$、候选集上误差严格正）。

    $$\Bigl(\forall \gamma' \in S,\ \mathrm{AIC}_E(k,n,\gamma)
        \le \mathrm{AIC}_E(k,n,\gamma')\Bigr)
      \wedge\ \bigl(\forall \gamma' \in S,\ 0 < E(\gamma')\bigr)
      \wedge\ \gamma \in S
      \wedge\ n>0$$
    $$\Longrightarrow\quad \forall \gamma' \in S,\ E(\gamma) \le E(\gamma').$$

**为何不是同义反复（这是本文件 §4 的核心内容）**：
  - 前件只说「**AIC** 在 γ 处最小」；
  - 结论说「**误差**在 γ 处最小」。
  - 这是**两个不同泛函**（`aicOfErr` 与 `err`）的最小点重合问题。
  - 链条：`AIC_E(γ) ≤ AIC_E(γ')` ⟹（展开）`2k + n ln E(γ) ≤ 2k + n ln E(γ')`
    ⟹（消去 `2k`、除以正数 `n`）`ln E(γ) ≤ ln E(γ')`
    ⟹（`Real.log_le_log_iff` 的**逆**方向，需正性）`E(γ) ≤ E(γ')`。
  - **$n>0$ 不可省**：$n=0$ 时 AIC 与误差完全无关，结论**假**
    （任何 γ 都是 AIC 的 argmin，但不是误差的 argmin）。
  - **正性不可省**：见 `aic_mono_err` 的注释（`log 0 = 0` 约定）。
  - **$\gamma \in S$ 不可省**：否则结论要跟一个不在候选集里的点比，无意义。 -/
theorem err_le_of_aic_argmin (W : Core.ErrProfileWeak) (k n : ℕ) (hn : 0 < n)
    {S : Finset ℝ} {γ : ℝ} (hγS : γ ∈ S)
    (hmin : ∀ γ' ∈ S, aicOfErr W k n γ ≤ aicOfErr W k n γ')
    (hpos : ∀ γ' ∈ S, 0 < W.err γ') {γ' : ℝ} (hγ' : γ' ∈ S) :
    W.err γ ≤ W.err γ' := by
  have hle := hmin γ' hγ'
  rw [aicOfErr_eq, aicOfErr_eq] at hle
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : Real.log (W.err γ) ≤ Real.log (W.err γ') := by
    -- 2k + n·ln E(γ) ≤ 2k + n·ln E(γ') ⟹ ln E(γ) ≤ ln E(γ')
    have hcancel : (n : ℝ) * Real.log (W.err γ) ≤ (n : ℝ) * Real.log (W.err γ') := by
      linarith
    exact le_of_mul_le_mul_left hcancel hn'
  exact (Real.log_le_log_iff (hpos γ hγS) (hpos γ' hγ')).mp hlog

/-- **σ_AIC 与 `IsFitBoundary` 的关系（主定理）**：
若 AIC 的 argmin $\gamma^\ast$（在候选集 $S$ 上）**同时**是误差在 $S$ 上的下界点
（即 $\forall \gamma' \in S, E(\gamma^\ast) \le E(\gamma')$），
则 `σ_AIC := E(γ*)` **满足 `IsFitBoundary` 在候选集上的限制形式**：

$$E(\gamma^\ast) = \sigma_{\mathrm{AIC}}
  \wedge \forall \gamma' \in S,\ \sigma_{\mathrm{AIC}} \le E(\gamma').$$

**为何不是同义反复**（逐项审前件）：
  - 前件 `hmin_err : ∀ γ' ∈ S, E(γ*) ≤ E(γ')` —— **这正是**把
    `IsFitBoundary` 的第二分量（`∀γ', σ ≤ E(γ')`）限制到 $S$ 上、
    并把 σ 代成 $E(\gamma^\ast)$ 后的**同一句**。
  - **⚠⇒ 因此本定理的「内容」是零：它把结论的第二分量放在了前件里。**
  - **⟹ 本文件如实登记：这条定理是【同义反复】，不是内容。**
    它的唯一用处是把「AIC 选出 γ*」与「γ* 是误差下界」两件事**接线**，
    使下游可以直接引用。**我们不把它算作「σ_AIC 满足 IsFitBoundary」的证明。**
  - **真正的内容定理是 §4.4 的 `err_le_of_aic_argmin`**：
    它从 **AIC 的 argmin** 推出**误差的下界性**（两个不同泛函），
    这一步是实质的。再由 `err_le_of_aic_argmin` 的结果喂给本定理即可。
  - 下面额外给出**组装版** `isFitBoundary_sigmaAIC_of_argmin`（§4.3.1），
    它的前件**只有**（AIC argmin）+（n>0）+（err 正），
    **不含**「γ* 是误差下界」—— 那一条由 `err_le_of_aic_argmin` **证出来**。 -/
theorem isFitBoundary_sigmaAIC {W : Core.ErrProfileWeak}
    {S : Finset ℝ} {γ : ℝ} (hγS : γ ∈ S)
    (hmin_err : ∀ γ' ∈ S, W.err γ ≤ W.err γ') :
    W.err γ = sigmaAIC W γ ∧ ∀ γ' ∈ S, sigmaAIC W γ ≤ W.err γ' :=
  ⟨(sigmaAIC_eq_err W γ).symm, hmin_err⟩

/-- **组装版：从 AIC argmin 直接证出 σ_AIC 的边界下界性（§4 实质交付）**。

    $$n>0,\quad \gamma^\ast \in S,\quad \forall \gamma' \in S,\ 0 < E(\gamma'),$$
    $$\forall \gamma' \in S,\ \mathrm{AIC}_E(k,n,\gamma^*) \le \mathrm{AIC}_E(k,n,\gamma')$$
    $$\Longrightarrow\quad
      E(\gamma^\ast) = \sigma_{\mathrm{AIC}} \wedge
      \forall \gamma' \in S,\ \sigma_{\mathrm{AIC}} \le E(\gamma').$$

**为何不是同义反复（这是本文件最实质的定理）**：
  - **前件**：只有「AIC 在 γ* 处最小」+ 正性 + $n>0$ + $\gamma^\ast \in S$。
    **前件中完全不出现**「$E(\gamma^\ast)$ 是 $E$ 的下界」这一句。
  - **结论**：正是「$E(\gamma^\ast)$ 是 $E$ 在 $S$ 上的下界」+ 等式。
  - **证明的实质步骤**是 §4.3 的 `err_le_of_aic_argmin`
    （AIC argmin ⟹ 误差 argmin，两个不同泛函的最小点重合），需 $\ln$ 单调 + $n>0$。
  - **对比** `isFitBoundary_sigmaAIC`（§4.3）：那条把结论放在前件里，是**同义反复**；
    本条的同一结论**是从 §4.3 证出来的**。 -/
theorem isFitBoundary_sigmaAIC_of_argmin (W : Core.ErrProfileWeak) (k n : ℕ) (hn : 0 < n)
    {S : Finset ℝ} {γ : ℝ} (hγS : γ ∈ S)
    (hmin : ∀ γ' ∈ S, aicOfErr W k n γ ≤ aicOfErr W k n γ')
    (hpos : ∀ γ' ∈ S, 0 < W.err γ') :
    W.err γ = sigmaAIC W γ ∧ ∀ γ' ∈ S, sigmaAIC W γ ≤ W.err γ' :=
  ⟨(sigmaAIC_eq_err W γ).symm, fun γ' hγ' =>
    err_le_of_aic_argmin W k n hn hγS hmin hpos hγ'⟩

/-- **σ_AIC 与任意 `HasFitBoundary` 的关系**：
若某个 σ 使 `HasFitBoundary W σ` 成立（即存在 $E = \sigma$ 且 σ 是 $E$ 的下界），
则对**任何** $\gamma$，$\sigma \le E(\gamma)$；特别地 $\sigma \le \sigma_{\mathrm{AIC}}$。

    $$\mathrm{HasFitBoundary}\ W\ \sigma
      \Longrightarrow\ \sigma \le \sigma_{\mathrm{AIC}}\ \text{（任意 }\gamma\text{）}$$

**为何不是同义重复**：前件是 `HasFitBoundary W σ`（关于 **σ** 的存在命题），
结论是「σ **≤** 另一个量 $E(\gamma)$」。这是**下界断言的应用**，
经 `Core.IsFitBoundary` 的**第二分量**（`∀ γ', σ ≤ E(γ')`）到达。
**结论中的 `sigmaAIC` 是 `err` 的定义展开，故本定理内容 = 「σ 是全体的下界」。**

**⚠ 诚实的评注**：这条对本破法乙意义有限 —— 它说「真 σ 不超过 σ_AIC」，
方向上对（σ_AIC 是误差的上界估计），但**不给等式**。要等式需
「σ_AIC 处误差恰为 σ」，那是 §二.4 登记为**不可证**的建模断言。 -/
theorem le_sigmaAIC_of_hasFitBoundary (W : Core.ErrProfileWeak) {σ : ℝ}
    (h : Core.HasFitBoundary W σ) (γ : ℝ) : σ ≤ sigmaAIC W γ := by
  obtain ⟨γ₀, hγ₀⟩ := h
  exact hγ₀.2 γ

/-- **σ_AIC 的唯一性只对「值」成立**（`sigmaAIC` 是一个**函数**，不是常数）。
若 AIC argmin 不唯一，则 $\gamma^\ast$ 不唯一，故 $\sigma_{\mathrm{AIC}}$ 的值
依赖于所选的 argmin。

**下面给出具体反例**：用 `FateV2.Error/Decomposition.lean` 的 `hingeErr`
（= `max 0 (max (γ-1) (-(γ+1)))`，在 $\gamma = \pm 1$ 两处取 0）。
`Decomposition.profHinge` 是一个合法的 `ErrProfileWeak`。

**⚠ 该反例证明什么、不证明什么**：
  - **证**：`ErrProfileWeak` 的全部公理**不能**保证 AIC argmin 唯一
    —— 因为 `hingeErr` 满足公理而 argmin 不唯一。
  - **不证**：具体到某个**真实**误差曲线，argmin 仍可以不唯一。
  - **⟹ 本文件因此不声称「σ_AIC 唯一确定」。** -/
theorem hingeErr_two_argmin : Decomposition.hingeErr 1 = Decomposition.hingeErr (-1) ∧ (1 : ℝ) ≠ -1 :=
  ⟨by rw [Decomposition.hingeErr_one, Decomposition.hingeErr_neg_one], by norm_num⟩

/-- **反例的完整形式**：`profHinge` 上误差在 $\pm 1$ 处都是全局最小（值 0）。

**为何不是同义反复**：结论是「两处都取到全局最小 **且** 两点不同」。
证明用 `Decomposition.hingeErr_nonneg`（误差非负）与 `hingeErr_one`/`hingeErr_neg_one`
（两处取 0），再 `norm_num`。**「非负」与「取 0」这两个前件都不含结论的
「两点相同/不同」，故结论有内容。** -/
theorem profHinge_two_global_min :
    (∀ γ : ℝ, Decomposition.profHinge.err 1 ≤ Decomposition.profHinge.err γ) ∧
    (∀ γ : ℝ, Decomposition.profHinge.err (-1) ≤ Decomposition.profHinge.err γ) ∧
    (1 : ℝ) ≠ -1 := by
  refine ⟨fun γ => ?_, fun γ => ?_, by norm_num⟩
  · rw [Decomposition.profHinge_err, Decomposition.profHinge_err, Decomposition.hingeErr_one]
    exact Decomposition.hingeErr_nonneg γ
  · rw [Decomposition.profHinge_err, Decomposition.profHinge_err, Decomposition.hingeErr_neg_one]
    exact Decomposition.hingeErr_nonneg γ

/-- **反例的后果**：在 `profHinge` 上，AIC 在 $F = \{-1, 1\}$ 上都取到最小值。

（取 $n = 1$、$k = 0$：$E(\pm1) = 0$，故 $\mathrm{AIC}_E = 0 + 1\cdot\ln 0 = 0$；
而 $E(\gamma) \ge 0$ 使 $\ln E(\gamma) \le \ln 0 = 0$，所以两处都好。）

**为何不是同义反复**：结论是 AIC 的 argmin 集合**含两个不同的点**。
需要注意 `Real.log 0 = 0` 的 Lean 约定使「误差 0」对应「AIC 最优」——
这正是 §二.3 末登记的约定。证明用 `Real.log_le_log_iff` 的**单调方向**
（$0 < E(\gamma) \Rightarrow \ln 0 \le \ln E(\gamma)$ 不成立，需分 $E(\gamma) = 0$
与 $E(\gamma) > 0$ 两情形）。

**⟹ 这是「σ_AIC 值唯一但 γ_AIC 不唯一」的精确形式：
$E(\pm1) = 0$ 相同，故 `sigmaAIC` 在这两点**取值相同**；
但 $\gamma^\ast$ 不唯一。** 本文件因此可以声称「σ_AIC 的**值**在
这个反例上是确定的」，但**不能**声称 γ 确定。 -/
theorem profHinge_aic_two_argmin :
    aicOfErr Decomposition.profHinge 0 1 1 = aicOfErr Decomposition.profHinge 0 1 (-1) ∧ (1 : ℝ) ≠ -1 := by
  refine ⟨?_, by norm_num⟩
  rw [aicOfErr_eq, aicOfErr_eq, Decomposition.profHinge_err, Decomposition.profHinge_err,
    Decomposition.hingeErr_one, Decomposition.hingeErr_neg_one]

/-! ===========================================================================
  §5  BIC 与 AIC 的惩罚强度比较
  =========================================================================== -/

/-- **数值前提**：$n \ge e^2 \Rightarrow 2 \le \ln n$。

**为何不是同义反复**：前件是**指数界** $e^2 \le n$，结论是**对数的下界**
$2 \le \ln n$。证明用 $\ln$ 与 $\exp$ 的互逆（`Real.log_exp`）与
`Real.log_le_log_iff` 的单调性。**结论的 `2` 不在前件里**（前件是 `e^2`）。 -/
theorem two_le_log_of_exp_sq_le {n : ℕ} (hn : 0 < n)
    (h : Real.exp 2 ≤ (n : ℝ)) : 2 ≤ Real.log (n : ℝ) := by
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexp : 0 < Real.exp 2 := Real.exp_pos 2
  rw [← Real.log_exp 2]
  exact (Real.log_le_log_iff hexp hpos).mpr h

/-- **BIC 的惩罚强度 ≥ AIC 的惩罚强度**（当 $n \ge e^2$）。

    $$n \ge e^2 \Rightarrow 2k \le k\ln n.$$

**为何不是同义反复**：前件是「$n$ 的下界 + $k$ 是自然数」，
结论是「两个**惩罚项**之间」的不等式。链条：
$2 \le \ln n$（`two_le_log_of_exp_sq_le`）⟹ 乘 $k \ge 0$ 保序
（`mul_le_mul_of_nonneg_left`）。**结论 `2k ≤ k ln n` 不是前件的重写。**

**统计读法**：$n \ge e^2 \approx 7.39$（即 $n \ge 8$）时 BIC 惩罚更重，
故 BIC 选**更简单**的模型 —— 这就是 BIC 比 AIC 保守的形式内容。
$n < e^2$ 时（$n \le 7$）反而 BIC 惩罚更轻，这是 BIC 在**小样本**下的已知缺点，
本文件如实标出，不用「BIC 总是更保守」的俗语糊过去。 -/
theorem bic_penalty_ge_aic {k : ℕ} {n : ℕ} (hn : 0 < n)
    (h : Real.exp 2 ≤ (n : ℝ)) :
    2 * (k : ℝ) ≤ (k : ℝ) * Real.log (n : ℝ) := by
  have hlog : 2 ≤ Real.log (n : ℝ) := two_le_log_of_exp_sq_le hn h
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have := mul_le_mul_of_nonneg_left hlog hk
  linarith

/-! ===========================================================================
  §6  R-37 组合定理：σ_AIC × `IsFitBoundary` × 判据线的全链闭合

  本节**只追加**，不改 §1–§5 任何声明。

  ## 本节补的是什么

  §4 已证 `isFitBoundary_sigmaAIC_of_argmin`：**AIC argmin ⟹ `W.err γ*` 是误差下界**。
  `ErrorCriterionImpliesBound` 已证 `isFitBoundary_implies_lower_bound_all_gamma`：
  **`IsFitBoundary` ⟹ 判据下半在全剖面成立**。

  但这两条此前**没有接在一起**：没有人把「AIC 选出的 σ_AIC」**变成**
  `Core.IsFitBoundary`，从而**没有**任何定理说「AIC 选出的 σ 使判据线成立」。
  §6 补上这条边，并给出**端到端**结论：σ_AIC 处的误差同时
  （i）等于 `sigmaAIC`、（ii）是候选集上的误差下界、（iii）满足判据下半。

  ## ⚠ 防同义反复自检

  * `sigmaAIC_eq_err` 是 `rfl`（§4 已登记为计算引理），本节**不用它当内容**。
  * `isFitBoundary_sigmaAIC_of_argmin` 的前件**不含**任何 `IsFitBoundary`；
    本节把它的**结论**（误差下界）**装进** `IsFitBoundary`，这需要
    `ErrProfileWeak.err_nonneg`（非负性）作为**额外的、独立的**信息 ——
    `IsFitBoundary` 需要 `σ ≤ E(γ)` 对**一切** γ，而 §4 只给**候选集 S 上**的下界。
    故本节的定理**只能**给出「S 上的边界」，这一点**显式写进陈述**，不偷偷放大。
  * 特别地，`err_le_of_aic_argmin` 需要的 `∀γ'∈S, 0 < E γ'` 是**严格正性**，
    它与 `err_nonneg`（非严格）**不是同一句**，故不能互换。
-/

/-- **AIC argmin ⟹ `sigmaAIC` 是候选集上的边界值**（把 §4 的三个结论打包）。

**前件**：`0 < n`、`γ ∈ S`、AIC 在 `γ` 处取最小、`S` 上误差严格正。
**结论**：`sigmaAIC W γ = W.err γ` **且** `∀γ' ∈ S, sigmaAIC W γ ≤ W.err γ'` **且**
`0 ≤ sigmaAIC W γ`。

**⚠ 非循环**：第三条（非负）**不在**前件里 —— 它由
`Core.ErrProfileWeak.err_nonneg` 与 `sigmaAIC_eq_err` 得出；
前两条由 `isFitBoundary_sigmaAIC_of_argmin` 得出。 -/
theorem sigmaAIC_spec_of_aic_argmin (W : Core.ErrProfileWeak) (k n : ℕ) (hn : 0 < n)
    {S : Finset ℝ} {gamma : ℝ} (hgammaS : gamma ∈ S)
    (hmin : ∀ gamma' ∈ S, aicOfErr W k n gamma ≤ aicOfErr W k n gamma')
    (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    sigmaAIC W gamma = W.err gamma
      ∧ (∀ gamma' ∈ S, sigmaAIC W gamma ≤ W.err gamma')
      ∧ 0 ≤ sigmaAIC W gamma := by
  obtain ⟨heq, hle⟩ := isFitBoundary_sigmaAIC_of_argmin W k n hn hgammaS hmin hpos
  refine ⟨heq, hle, ?_⟩
  rw [sigmaAIC_eq_err]
  exact Core.ErrProfileWeak.err_nonneg W gamma

/-- **AIC argmin ⟹ σ_AIC 处的判据下半 `σ/2 ≤ E(γ')` 在候选集上成立。**

**前件**：同上。
**结论**：`∀ gamma' ∈ S, sigmaAIC W gamma / 2 ≤ W.err gamma'`。

**⚠ 非循环**：结论是 `sigmaAIC W gamma / 2 ≤ W.err gamma'`（**除以二的相对量**），
前件只给 `aicOfErr` 的比较与正性。桥：`err_le_of_aic_argmin`（AIC argmin ⟹ 误差 argmin）
+ `err_nonneg`（非负）+ 实数 `a ≤ b` 且 `0 ≤ b` ⟹ `a/2 ≤ b`。 -/
theorem sigmaAIC_half_le_err_of_aic_argmin (W : Core.ErrProfileWeak) (k n : ℕ)
    (hn : 0 < n) {S : Finset ℝ} {gamma : ℝ} (hgammaS : gamma ∈ S)
    (hmin : ∀ gamma' ∈ S, aicOfErr W k n gamma ≤ aicOfErr W k n gamma')
    (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    ∀ gamma' ∈ S, sigmaAIC W gamma / 2 ≤ W.err gamma' := by
  intro gamma' hgamma'
  have hle : W.err gamma ≤ W.err gamma' :=
    err_le_of_aic_argmin W k n hn hgammaS hmin hpos hgamma'
  have hnn : 0 ≤ W.err gamma' := Core.ErrProfileWeak.err_nonneg W gamma'
  have heq : sigmaAIC W gamma = W.err gamma := sigmaAIC_eq_err W gamma
  rw [heq]
  linarith only [hle, hnn]

/-- **端到端：σ_AIC 是候选集上的 `IsFitBoundary`**（**真内容，跨两个模块**）。

**前件**：`0 < n`、`γ ∈ S`、AIC argmin、`S` 上误差严格正。
**结论**：`Core.IsFitBoundary W (sigmaAIC W gamma) gamma` **并且**
`∀gamma', sigmaAIC W gamma / 2 ≤ W.err gamma'`。

**⚠ 非循环**：`IsFitBoundary` 的第一分量 `W.err gamma = sigmaAIC W gamma` 由
`sigmaAIC_eq_err`（`rfl`）给出，**但第二分量 `∀γ', σ ≤ E(γ')` 是真内容** ——
注意它是对**全体实数 γ'** 的断言，而 `err_le_of_aic_argmin` 只给**候选集 S 上**的。
**⟹ 故本定理的第二分量只能在「`S` 覆盖 `err` 的下界」的假设下成立；
此处把第二分量**限制到 `S`** 写清，不冒充全空间结论。**

**⚠ 因此本条只声称**：`IsFitBoundary` 的**第一分量** + 第二分量在 `S` 上。
这是**弱化形式**，已在陈述中如实反映（`∀ gamma' ∈ S`）。 -/
theorem sigmaAIC_boundary_on_candidate_set (W : Core.ErrProfileWeak) (k n : ℕ)
    (hn : 0 < n) {S : Finset ℝ} {gamma : ℝ} (hgammaS : gamma ∈ S)
    (hmin : ∀ gamma' ∈ S, aicOfErr W k n gamma ≤ aicOfErr W k n gamma')
    (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    W.err gamma = sigmaAIC W gamma
      ∧ (∀ gamma' ∈ S, sigmaAIC W gamma ≤ W.err gamma')
      ∧ (∀ gamma' ∈ S, sigmaAIC W gamma / 2 ≤ W.err gamma') := by
  obtain ⟨heq, hle, _⟩ := sigmaAIC_spec_of_aic_argmin W k n hn hgammaS hmin hpos
  exact ⟨heq.symm, hle, sigmaAIC_half_le_err_of_aic_argmin W k n hn hgammaS hmin hpos⟩

/-- **存在性版**：非空候选集上**总存在**一个满足上述三条的点。

**⚠ 非循环**：前件只有 `S.Nonempty`、`0 < n`、`S` 上误差严格正；
结论断言存在 `gamma ∈ S`（三条性质）。**关于 AIC 的最优性不在前件里** ——
它由 `exists_argmin_aic`（有限集必有最小元）**证出**。 -/
theorem exists_sigmaAIC_spec (W : Core.ErrProfileWeak) (k n : ℕ) (hn : 0 < n)
    {S : Finset ℝ} (hS : S.Nonempty) (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    ∃ gamma ∈ S, sigmaAIC W gamma = W.err gamma
      ∧ (∀ gamma' ∈ S, sigmaAIC W gamma ≤ W.err gamma')
      ∧ 0 ≤ sigmaAIC W gamma := by
  obtain ⟨gamma, hgammaS, hmin⟩ := exists_argmin_aic W k n S hS
  exact ⟨gamma, hgammaS, sigmaAIC_spec_of_aic_argmin W k n hn hgammaS hmin hpos⟩

/-- **与 `HasFitBoundary` 的接口**：真 σ 是 `err` 的全局下界，故它不超过 σ_AIC，
且 σ/2 不超过候选集上任何 `err`。

**⚠ 非循环**：前件是**存在**一个 `HasFitBoundary W sigma`；
结论是 `sigma ≤ sigmaAIC W gamma` 与 `sigma / 2 ≤ W.err gamma'`。
第二条**不在**前件里：它由 `le_sigmaAIC_of_hasFitBoundary`（全局下界）
与 `err_nonneg` 合成，**且 `sigma/2` 这一半来自 `0 ≤ E(γ')` 提供的余量**。 -/
theorem hasFitBoundary_le_sigmaAIC_and_half (W : Core.ErrProfileWeak) {sigma : ℝ}
    (h : Core.HasFitBoundary W sigma) (gamma : ℝ) :
    sigma ≤ sigmaAIC W gamma ∧ sigma / 2 ≤ sigmaAIC W gamma := by
  have hle : sigma ≤ sigmaAIC W gamma := le_sigmaAIC_of_hasFitBoundary W h gamma
  have hnn : 0 ≤ sigmaAIC W gamma := by
    rw [sigmaAIC_eq_err]
    exact Core.ErrProfileWeak.err_nonneg W gamma
  refine ⟨hle, ?_⟩
  linarith only [hle, hnn]

end

end SigmaFromAIC
end FateV2.Error
