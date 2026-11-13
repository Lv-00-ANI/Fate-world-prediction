import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FateWorld.FateV2.Error.FitBoundary
import FateWorld.FateV2.Error.ErrorBound
import FateWorld.FateV2.Modeling.ObsEstimationWeak

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ErrorBoundChain.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 12 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Error
open FateV2.Loop

/-
  命运理论 · **阶段 2：误差界** —— 缺口 4 的**真内容**
  **第 253 轮 · L4 修复版**（源：`FateV2.Error/ErrorBound.lean`，第 252 轮从服务器找回的 594 行稿）

  ============================================================================
  ⚠ **本轮（R253）改了什么**（）
  ============================================================================

  第 252 轮存档的 `ErrorBound.lean` 有 **20 个编译错误**（Lean 实际报 9 处，
  其余为级联）。修复过程中发现：**其中 2 条命题是假的**，已按任务要求
  **删除并改写**，并给出**具体反例**。

  ### A. 逐条修复清单

  | # | 位置（原行号） | 症状 | 根因 | 处置 |
  |---|---|---|---|---|
  | 1 | `179:2` | `No goals to be solved` | `rw [← hs]` 已把目标化为 `sgn s = sgn s` 并**关闭**，其后的 `rw [sgn_of_pos hm]` 无目标 | 删除多余行；并**同时指出 `margin_decides` 本身是 `rfl` 级同义反复**（见 §1.2 诚实说明） |
  | 2 | `216:27` | `linarith failed` | `linarith only [h2, hs1]` 想从 `2ε < s` 推出 `ε < s`，**缺 `0 ≤ ε`** | `only` 列表补 `hε` |
  | 3 | `222:28` | 同上（负支） | 同上 | 同上 |
  | 4 | `260:6` | `rw` 找不到 `sgn 0` | 目标是 `sgn (1 + -1) ≠ sgn 1`，`1 + -1` **尚未**归约为 `0` | 先 `show`，再用 `show (1:ℝ)+-1 = 0` 显式归约 |
  | 5 | `416:4` | `linarith failed`（`hzz`） | **该子目标在数学上是假的**：`hzz : 0 ≤ K·2PQ − 2⟨u,v⟩` 在 `K=0`、`⟨u,v⟩>0` 时不成立 | 整段证明**重写**（见 B） |
  | 6 | `419:69` | `unsolved goals`（`ring` 失败） | 等式两边原子形状不一致（`K*P*Q*2` vs `K*(P*Q)*2`），`ring` 未归一并留下主项 | 同上重写 |
  | 7 | `423:2` | `linarith failed` | 承 5/6，主链本身依赖假命题 | 同上重写 |
  | 8 | `489:8` | `rw` 找不到 `√(1/8)*2` | 目标里是 `√(1/8)*(1+1)`，`1+1` 未归一为 `2` | 先 `show (1:ℝ)+1 = 2` |
  | 9 | `490:10` | 同上（嵌套 `rw`） | `Real.sqrt_sq_eq_abs` + `abs_of_nonneg` 组合在本 Mathlib 下不匹配 | 改用 `← Real.sqrt_sq` + `congr 1` + `mul_pow` |

  ### B. ⚠ **被删掉的两条假命题**（核心诚实点）

  原文件 §5.2 / §5.3 的两条"技术核心"定理：

  ```
  cos_close_implies_norm_close (u v : E) (K : ℝ) (hK : 0 ≤ K)
      (hcos : inner ℝ u v / (‖u‖*‖v‖) ≥ 1 - K) :
      ‖u - v‖ ^ 2 ≤ K * 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)
  ```

  **这是假的。** 反例（具体数字，实数域，可直接数值验算）：

  > 取 $\|u\|=1$、$\|v\|=2$、$\cos\angle(u,v)=\dfrac{\langle u,v\rangle}{\|u\|\|v\|}=0.99$
  > （即 $K=0.01$，满足 $K\ge0$）。则
  > $\|u-v\|^2=\|u\|^2+\|v\|^2-2\langle u,v\rangle=1+4-2(0.99\cdot1\cdot2)=5-3.96=1.04$，
  > 而右端 $=K\cdot2(\|u\|^2+\|v\|^2)=0.01\cdot2\cdot5=0.1$。
  > **$1.04\not\le 0.1$** ⟹ 命题假。

  **错在哪**：原证明把「$P^2+Q^2-2\langle u,v\rangle$」上限中的
  **$(P-Q)^2$ 项丢掉了**。正确的展开是
  $$\|u-v\|^2\ \le\ (P-Q)^2+2K\,PQ,$$
  而 $(P-Q)^2$ 与 $K$ **无关**，$K\to0$ 时它不趋于 $0$ ——
  原式把 $K=0$ 时本应强制的 $P=Q$ 给漏了。

  **推论（`euclid_transfer_bound`）也假**：
  $$\text{原式}\ \|u-v\|\le\sqrt{2K}\,(\|u\|+\|v\|)$$
  同一反例：$1.04$ 的平方根 $=1.0198$，右端 $=\sqrt{0.02}\cdot3=0.1342$。
  **假** ⟹ 删除。

  ### C. 替换为**真**命题（已证，见 §5.2′ / §5.3′）

  | 新名 | 内容 | 状态 |
  |---|---|---|
  | `cos_close_general` | $\|u-v\|^2\le(\|u\|-\|v\|)^2+2K\|u\|\|v\|$ | ✅ 已证，**是原式的正确化** |
  | `unit_transfer_bound` | 归一化后：$\bigl\|\tfrac{u}{\|u\|}-\tfrac{v}{\|v\|}\bigr\|\le\sqrt{2K}$ | ✅ 已证，**这才是 $\sqrt\cdot$ 的正确落点** |

  **$\sqrt{2K}$ 的结论本身是真的**，但**只在归一化尺度上成立**（$\|u\|=\|v\|$
  时两式重合 —— 这正是原文件 §5.3 的 $K=1/16$ 例所假设的）。
  原文件把「单位向量」的结论**错推广到任意范数**，这是 2 条假命题的根源。

  ### D. 登记的**同义反复**（真实但实质度为 0，保留并标注）

  | 定理 | 为何是同义反复 |
  |---|---|
  | `margin_decides` | `hs : s = σ*m` 代入后目标即 `sgn s = sgn s`，`rw` 一步关闭 |
  | `sqrt_bound_order_sharp` | 结论是 `P ∨ √(2K)>0`，**右支恒真**（`K>0` ⟹ `√(2K)>0`），左支从未用到 |
  | `error_bound_independent_of_tauOf` | 只是把 `error_bound_gives_correct_classification` 包一层 `∀`，`α n σx tCrit` **完全未用** |

  ---
  ## 一、一句话结论（**成立**的部分）

  $$\boxed{\ \mathrm{sgn}(s+\delta)=\mathrm{sgn}(s)\ }
    \quad\text{由}\quad
    \boxed{\ |\delta|\le\varepsilon \ \wedge\ 2\varepsilon<|s|\ }$$

  以及其几何对应（**归一化**）：
  $$\cos\angle(u,v)\ge 1-K \ \Longrightarrow\
    \Bigl\|\tfrac{u}{\|u\|}-\tfrac{v}{\|v\|}\Bigr\|\le\sqrt{2K}.$$

  ---
  ## 二、关于裁决 K 的**诚实说明**

  **裁决 K 原文是经验性的**（「误差必须小到不影响」）。
  本文件**不能**证明「裁决 K 的字面陈述为真」——那是**定义问题**。
  本文件做的是：把「不影响」精确化为「决策不变」，
  证明该含义下的**定量充分条件**，并证明条件**在常数上是紧的**。

  **⚠ 三条本文件**不做**的事**：
  1. **不证** $\varepsilon$ 的**统计估计**；
  2. **不证** $\varepsilon<m/2$ 在实际数据上是否成立（经验问题）；
  3. **不修改** `FateV2.Error.Classification` 的冻签名。

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
  ============================================================================
-/

-- R-36：与 `ObsEstimationWeak`（观测等价类）**真接线**（噪声 ⟹ 分类稳健）。

namespace FateV2.Error

namespace R253ErrorBound

open Set

noncomputable section

/-! ===========================================================================
  §1  基础层：**决策 = 符号**，与**间隔**的定义
  =========================================================================== -/

/-- **符号函数**（分类器的输出）：`t>0 ↦ 1`，`t<0 ↦ -1`，`t=0 ↦ 0`（未决）。 -/
def sgn (t : ℝ) : ℤ :=
  if 0 < t then 1 else if t < 0 then -1 else 0

/-- 符号刻画（$t>0$）。 -/
theorem sgn_of_pos {t : ℝ} (h : 0 < t) : sgn t = 1 := by simp [sgn, h]

/-- 符号刻画（$t<0$）。 -/
theorem sgn_of_neg {t : ℝ} (h : t < 0) : sgn t = -1 := by
  simp [sgn, not_lt.mpr (le_of_lt h), h]

/-- 符号刻画（$t=0$）。 -/
theorem sgn_of_zero : sgn 0 = 0 := by simp [sgn]

/-- 同正 ⟹ 同号。 -/
theorem sgn_congr_of_pos_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    sgn a = sgn b := by
  rw [sgn_of_pos ha, sgn_of_pos hb]

/-- 同负 ⟹ 同号。 -/
theorem sgn_congr_of_neg_of_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) :
    sgn a = sgn b := by
  rw [sgn_of_neg ha, sgn_of_neg hb]

/-- **线性打分函数** $\mathrm{score}(x)=\sum_i w_i x_i$。 -/
def linScore {ι : Type*} [Fintype ι] (w x : ι → ℝ) : ℝ := ∑ i, w i * x i

/-- `linScore` 的显式求和形式（`rfl`）。 -/
theorem linScore_eq_sum {ι : Type*} [Fintype ι] (w x : ι → ℝ) :
    linScore w x = ∑ i, w i * x i := rfl

/-- **间隔** $\mathrm{margin}(w,x):=|\langle w,x\rangle|$（打分尺度）。 -/
def margin {ι : Type*} [Fintype ι] (w x : ι → ℝ) : ℝ := |linScore w x|

/-- 间隔非负。 -/
theorem margin_nonneg {ι : Type*} [Fintype ι] (w x : ι → ℝ) : 0 ≤ margin w x :=
  abs_nonneg _

/-! ### §1.2 ⚠ **同义反复登记**：`margin_decides`

  **原文**（第 176–184 行）：
  ```
  theorem margin_decides {s m : ℝ} (σ : ℤ) (hσ : sgn s = σ) (hm : 0 < m)
      (hs : s = σ * m) : sgn (σ * m) = sgn s
  ```
  **它是真的，但实质度为 0**：`hs : s = σ*m` 直接给出
  `sgn (σ*m) = sgn s` 是 `rfl` 级的同一式 —— 整条证明只需
  `rw [← hs]`，其余全部多余（这正是原文件 `179:2: No goals to be solved` 的成因）。

  **处置**：**保留**（不假），但改写为**诚实的最简证明**，不再假装用 `linarith`，
  且在文档中明确标注「同义反复、不含实质」。 -/

/-- ⚠ **同义反复（实质度 0，仅保留名字）**：
由 `hs : s = σ*m` 立即得 `sgn (σ*m) = sgn s`。 -/
theorem margin_decides {s m : ℝ} (σ : ℤ) (_hσ : sgn s = σ) (_hm : 0 < m)
    (hs : s = σ * m) : sgn (σ * m) = sgn s := by
  rw [← hs]

/-! ===========================================================================
  §2  **选项 A：误差界 ⟹ 分类正确**（打分尺度，紧常数 $1/2$）
  =========================================================================== -/

/-- **【主定理 A】误差界 ⟹ 分类正确**（**本文件唯一的实质主定理**）。

前提：`0 < |s|`（真值不在边界）、`|δ| ≤ ε`、`2ε < |s|`。
结论：`sgn (s + δ) = sgn s`。

**常数 $1/2$ 紧**：§3 给出 `ε = m/2` 时决策退化为未决的具体例子。 -/
theorem error_bound_gives_correct_classification {s δ ε : ℝ} (hm : 0 < |s|)
    (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    sgn (s + δ) = sgn s := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg δ) hδ
  obtain ⟨hlo, hhi⟩ := abs_le.mp hδ
  rcases abs_cases s with ⟨hs1, _⟩ | ⟨hs1, _⟩
  · -- |s| = s：真侧为 +
    rw [hs1] at hm
    have hspos : 0 < s := hm
    have h2' : ε < s := by linarith only [h2, hs1, hε]
    have hgt : 0 < s + δ := by linarith only [hlo, h2']
    exact sgn_congr_of_pos_of_pos hgt hspos
  · -- |s| = -s：真侧为 -
    rw [hs1] at hm
    have hsneg : s < 0 := by linarith only [hm]
    have h2' : ε < -s := by linarith only [h2, hs1, hε]
    have hlt : s + δ < 0 := by linarith only [hhi, h2']
    exact sgn_congr_of_neg_of_neg hlt hsneg

/-- **主定理 A 的「间隔版」**：给出非零的 $\sigma$ 见证。 -/
theorem error_bound_gives_correct_classification_margin {s δ ε : ℝ}
    (hm : 0 < |s|) (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    ∃ σ : ℤ, σ ≠ 0 ∧ sgn (s + δ) = σ ∧ sgn s = σ := by
  refine ⟨sgn s, ?_, error_bound_gives_correct_classification hm hδ h2, rfl⟩
  rcases abs_cases s with ⟨hs1, _⟩ | ⟨hs1, _⟩
  · have : 0 < s := by linarith only [hm, hs1]
    rw [sgn_of_pos this]; norm_num
  · have : s < 0 := by linarith only [hm, hs1]
    rw [sgn_of_neg this]; norm_num

/-! ===========================================================================
  §3  **选项 C：紧性** —— 常数 $1/2$ **不能**改进
  =========================================================================== -/

/-- **【紧性】存在 `2ε ≮ |s|` 而决策翻转的具体例子**。

取 $s=1$、$\delta=-1$、$\varepsilon=1$：`sgn 0 = 0 ≠ 1 = sgn 1`。 -/
theorem perturbation_affects_decision :
    ∃ s δ ε : ℝ, 0 < |s| ∧ |δ| ≤ ε ∧ ¬ (2 * ε < |s|) ∧ sgn (s + δ) ≠ sgn s := by
  refine ⟨1, -1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  show sgn ((1:ℝ) + -1) ≠ sgn 1
  rw [show (1:ℝ) + -1 = 0 by norm_num, sgn_of_zero, sgn_of_pos (by norm_num)]
  norm_num

/-- **$2\varepsilon=m$ 时决策退化为未决**：`sgn (m-m) = 0`，而 `sgn m = 1`。 -/
theorem tight_bound_degenerates (m : ℝ) (hm : 0 < m) :
    sgn (m + (-m)) = 0 ∧ sgn m = 1 := by
  rw [show m + (-m) = 0 by ring, sgn_of_zero, sgn_of_pos hm]
  exact ⟨rfl, rfl⟩

/-- **紧性的精确陈述**：`2ε = m` 且 `ε>0` 时，
取 `δ = -ε` 使扰动点恰为 `ε > 0`（**真侧 +，扰动侧仍 +**）。

⚠ 注意这里**不**发生翻转（`sgn ε = sgn m = 1`）——
本定理说明的是「`2ε=m` 时**可**出现边界退化」（见 `tight_bound_degenerates`），
而**不是**「必翻转」。原文件的措辞已如实保留。 -/
theorem boundary_of_tight_bound {m ε : ℝ} (hε : 0 < ε) (hm : 2 * ε = m) :
    sgn (m + (-ε)) = sgn (ε) ∧ sgn m = 1 ∧ sgn ε = 1 := by
  have hmpos : 0 < m := by linarith only [hε, hm]
  have hme : m + (-ε) = ε := by linarith only [hm]
  rw [hme]
  exact ⟨rfl, sgn_of_pos hmpos, sgn_of_pos hε⟩

/-! ===========================================================================
  §4  **一般形式**：任意输入空间 $X$、逐点误差界 $\varepsilon:X\to\mathbb R$
  =========================================================================== -/

/-- **【主定理 A'：一般输入空间】**：逐点误差界版本的 `∀`。 -/
theorem learning_bound_general {X : Type*} (f δ : X → ℝ) (ε : X → ℝ)
    (hm : ∀ x, 0 < |f x|) (hδ : ∀ x, |δ x| ≤ ε x) (h2 : ∀ x, 2 * ε x < |f x|) :
    ∀ x, sgn (f x + δ x) = sgn (f x) :=
  fun x => error_bound_gives_correct_classification (hm x) (hδ x) (h2 x)

/-- **推论（函数相等）**：`sgn ∘ (f+δ)` 与 `sgn ∘ f` 作为**函数**相等。 -/
theorem classifier_function_eq {X : Type*} (f δ : X → ℝ) (ε : X → ℝ)
    (hm : ∀ x, 0 < |f x|) (hδ : ∀ x, |δ x| ≤ ε x) (h2 : ∀ x, 2 * ε x < |f x|) :
    (fun x => sgn (f x + δ x)) = fun x => sgn (f x) :=
  funext (learning_bound_general f δ ε hm hδ h2)

/-! ===========================================================================
  §5  **欧氏情形**：几何间隔与 $\sqrt\cdot$ 转移

  ⚠ **本节是 R253 的重灾区**：原文 2 条「技术核心」定理**是假的**，
  已删除并用**真命题**替换（`cos_close_general` / `unit_transfer_bound`）。
  反例与推导见文件头 §B、§C。
  =========================================================================== -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### §5.1 **Young 不等式** 与 **Cauchy–Schwarz** -/

/-- **Young 不等式**（实数形式）：$2ab\le c a^2+c^{-1}b^2$（$c>0$）。 -/
theorem young (a b : ℝ) (c : ℝ) (hc : 0 < c) :
    2 * a * b ≤ c * a ^ 2 + c⁻¹ * b ^ 2 := by
  have h2 := two_mul_le_add_sq (Real.sqrt c * a) (Real.sqrt c⁻¹ * b)
  rw [mul_pow, mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt (inv_nonneg.mpr hc.le)] at h2
  have e1 : (Real.sqrt c * a) * (Real.sqrt c⁻¹ * b) = a * b := by
    rw [show Real.sqrt c⁻¹ = (Real.sqrt c)⁻¹ by rw [← Real.sqrt_inv]]
    field_simp
  linarith only [h2, e1]

/-- **Cauchy–Schwarz 的绝对值形式（实内积）**。 -/
theorem cauchy_schwarz_abs (u v : E) : |inner ℝ u v| ≤ ‖u‖ * ‖v‖ :=
  abs_real_inner_le_norm _ _

/-- 范数差的平方公式：`‖u-v‖² = ‖u‖² - 2⟨u,v⟩ + ‖v‖²`。 -/
theorem norm_sub_sq_real' (u v : E) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
  rw [@norm_sub_sq ℝ, real_inner_comm v u]
  simp only [RCLike.re_to_real]

/-! ### §5.2′ **正确的定量核心**（**替换**原假定理 `cos_close_implies_norm_close`）

  原式 $\|u-v\|^2\le 2K(\|u\|^2+\|v\|^2)$ **假**（反例 $\|u\|=1,\|v\|=2,K=0.01$）。
  正确式是
  $$\|u-v\|^2\le(\|u\|-\|v\|)^2+2K\,\|u\|\,\|v\|,$$
  其推导只用一行代数：
  由 `hcos` 得 $\langle u,v\rangle\ge(1-K)PQ$，故
  $$P^2+Q^2-2\langle u,v\rangle\le P^2+Q^2-2(1-K)PQ=(P-Q)^2+2K\,PQ.$$ -/

/-- **正确的几何核心**：`cos ≥ 1-K` ⟹ `‖u-v‖² ≤ (‖u‖-‖v‖)² + 2K‖u‖‖v‖`。 -/
theorem cos_close_general (u v : E) (K : ℝ) (_hK : 0 ≤ K)
    (hcos : inner ℝ u v / (‖u‖ * ‖v‖) ≥ 1 - K) :
    ‖u - v‖ ^ 2 ≤ (‖u‖ - ‖v‖) ^ 2 + 2 * K * (‖u‖ * ‖v‖) := by
  by_cases hu : u = 0
  · subst hu
    simp only [inner_zero_left, norm_zero, zero_mul, zero_div] at hcos ⊢
    have h2 : 1 ≤ K := by linarith only [hcos]
    simp only [zero_sub, norm_neg, mul_zero]
    nlinarith only [h2, sq_nonneg ‖v‖]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  by_cases hv : v = 0
  · subst hv
    simp only [inner_zero_right, norm_zero, zero_div] at hcos ⊢
    have hK1 : 1 ≤ K := by linarith only [hcos]
    simp only [mul_zero, sub_zero]
    nlinarith only [hK1, sq_nonneg ‖u‖]
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hp' : 0 < ‖u‖ * ‖v‖ := mul_pos hu' hv'
  have h3 : inner ℝ u v ≥ (1 - K) * (‖u‖ * ‖v‖) := by
    have h4 := mul_le_mul_of_nonneg_right hcos (le_of_lt hp')
    rwa [div_mul_cancel₀ _ (ne_of_gt hp')] at h4
  rw [norm_sub_sq_real']
  set P := ‖u‖
  set Q := ‖v‖
  have h3' : (1 - K) * (P * Q) ≤ inner ℝ u v := h3
  nlinarith only [h3']

/-! ### §5.3′ **归一化转移界**（**替换**原假定理 `euclid_transfer_bound`）

  原式 $\|u-v\|\le\sqrt{2K}(\|u\|+\|v\|)$ **假**（同一反例：$1.02\not\le0.134$）。
  **正确的、也是 $\sqrt\cdot$ 真正落点的形式**是**归一化**版本：
  $$\Bigl\|\tfrac{u}{\|u\|}-\tfrac{v}{\|v\|}\Bigr\|^2=2-2\cos\angle(u,v)\le 2K.$$
  这恰是原文件 §5.3 的 $K=1/16$ 例（$\|u\|=\|v\|=1$）所验证的那条。 -/

/-- 归一向量的内积公式。 -/
theorem inner_normalized (u v : E) :
    inner ℝ ((‖u‖⁻¹ : ℝ) • u) ((‖v‖⁻¹ : ℝ) • v) = inner ℝ u v / (‖u‖ * ‖v‖) := by
  rw [real_inner_smul_left, real_inner_smul_right]; ring

/-- 归一向量的范数为 1。 -/
theorem norm_normalized (u : E) (hu : u ≠ 0) : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := by
  have h : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_cancel₀ (ne_of_gt h)]

/-- **【主定理 B（正确版）：归一化转移界】**

`u,v ≠ 0`、`cos∠(u,v) ≥ 1-K`（`K ≥ 0`）⟹
$\bigl\|\tfrac{u}{\|u\|}-\tfrac{v}{\|v\|}\bigr\|\le\sqrt{2K}$。

**$\sqrt{\cdot}$ 的来源**：$2-2\cos\theta\le 2K$，且 $2-2\cos\theta=2\sin^2(\theta/2)\approx\theta^2/2$。

**⚠ 与原文的差别**：原文结论是关于 `‖u-v‖`（**任意范数**）的，**假**；
本定理限定在**单位向量**上，**真**且已证。 -/
theorem unit_transfer_bound (u v : E) (hu : u ≠ 0) (hv : v ≠ 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hcos : inner ℝ u v / (‖u‖ * ‖v‖) ≥ 1 - K) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ≤ Real.sqrt (2 * K) := by
  have hnu : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := norm_normalized u hu
  have hnv : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_normalized v hv
  have h1 : ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ^ 2
      = 2 - 2 * (inner ℝ u v / (‖u‖ * ‖v‖)) := by
    rw [@norm_sub_sq ℝ, real_inner_comm ((‖v‖⁻¹ : ℝ) • v) ((‖u‖⁻¹ : ℝ) • u)]
    simp only [RCLike.re_to_real]
    rw [inner_normalized v u, real_inner_comm v u, hnu, hnv]; ring
  have h2 : ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ^ 2 ≤ 2 * K := by
    rw [h1]; linarith only [hcos]
  have h3 : (0:ℝ) ≤ ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ := norm_nonneg _
  have h4 : (0:ℝ) ≤ Real.sqrt (2 * K) := Real.sqrt_nonneg _
  nlinarith only [h2, h3, h4, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * K)]

/-! ### §5.4 **具体实数计算** -/

/-- **实算 1**：$K=1/16$ 时 $\sqrt{2K}=\sqrt{1/8}$，且 $\sqrt{1/8}\cdot\sqrt8=1$。 -/
theorem sqrt_two_mul_sixteenth :
    Real.sqrt (2 * ((1:ℝ)/16)) = Real.sqrt (1/8) ∧
      Real.sqrt ((1:ℝ)/8) * Real.sqrt 8 = 1 := by
  constructor
  · norm_num
  · rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/8)]
    norm_num

/-- **实算 2（主定理 B 的具体实例）**：

`‖u‖=‖v‖=1`、`⟨u,v⟩=15/16` 时 `K=1/16`，归一化界给 $\sqrt{1/8}\cdot 2=\sqrt{1/2}$；
而真实距离由余弦定理 $\|u-v\|^2=2-2\cdot\frac{15}{16}=\frac18$，即 $\sqrt{1/8}$。
$\sqrt{1/8}<\sqrt{1/2}$ ⟹ 界**不紧**但**正确**（差 $\sqrt2$ 倍）。

⚠ 注意：`‖u‖=‖v‖=1` 时归一化距离**就是** `‖u-v‖`，故本实算与
`unit_transfer_bound` **一致**；原文此处套用的是**假**的任意范数版本，
虽说数值在单位情形下侥幸正确，但**定理陈述**仍须改正。 -/
theorem concrete_transfer_example :
    Real.sqrt (2 * ((1:ℝ)/16)) * (1 + 1) = Real.sqrt (1/2) ∧
      Real.sqrt (2 - 2 * ((15:ℝ)/16)) = Real.sqrt (1/8) ∧
      Real.sqrt (1/8) < Real.sqrt (1/2) := by
  refine ⟨?_, ?_, ?_⟩
  · have h2 : (2:ℝ) * (1/16) = 1/8 := by norm_num
    rw [h2, show (1:ℝ) + 1 = 2 by norm_num]
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ Real.sqrt (1/8) * 2)]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/8)]
    norm_num
  · norm_num
  · exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- ⚠ **同义反复登记（实质度 0）**：结论是 `P ∨ Q`，而 `Q := √(2K)>0`
由 `K>0` **恒真**，故整个 `∨` 恒真，`P` 从未被使用。

**处置**：**保留**（不假，但无内容），改写为**诚实的最简证明**并标注。 -/
theorem sqrt_bound_order_sharp :
    ∀ K : ℝ, 0 < K → Real.sqrt (2 * (1 - Real.cos (Real.sqrt (2 * K)))) ≤ 4 * K ∨
      Real.sqrt (2 * K) > 0 := by
  intro K hK
  right
  exact Real.sqrt_pos.mpr (by linarith only [hK])

end Euclidean

/-! ===========================================================================
  §6  与既有 `tauOf` / `ShouldStop` 的**接口**（顺带澄清）
  =========================================================================== -/

/-- **主定理 A 不依赖 `FateV2.Loop.ShouldStop`**（前提里没有它）。 -/
example {s δ ε : ℝ} (hm : 0 < |s|) (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    sgn (s + δ) = sgn s :=
  error_bound_gives_correct_classification hm hδ h2

/-- ⚠ **同义反复登记（实质度 0）**：本定理只是把主定理 A 包进一层 `∀`，
参数 `α n σx tCrit` **完全未出现**于结论中。

**处置**：**保留**（不假），但改写为**显式注明未用参数**的最简形式。 -/
theorem error_bound_independent_of_tauOf (_α : ℝ) (_n : ℕ) (_σx _tCrit : ℝ) :
    (∀ s δ ε : ℝ, 0 < |s| → |δ| ≤ ε → 2 * ε < |s| → sgn (s + δ) = sgn s) :=
  fun s δ ε hm hδ h2 => error_bound_gives_correct_classification hm hδ h2

/-! ===========================================================================
  §7  ⚠ **诚实边界**（本文件**不**做的事）
  =========================================================================== -/

/-!
### §7.1 关于**裁决 K** 的如实说明

**裁决 K 逐字**：「误差必须小到不影响，就是刚好拟合和过拟合的边界」。

**本文件能证的**：给定「不影响」$=$「决策不变」，
则**定量充分条件**是 $2\varepsilon<\mathrm{margin}$（逐点）。

**本文件**不能**证的**：裁决 K 的原话**就是**指决策不变 —— 那是**定义**问题。

### §7.2 与 `FateV2.Error.FitBoundary.IsFitBoundary` 的关系（只登记，不证）

- `IsFitBoundary` 回答「**在哪个分辨率**误差最小」；
- 本文件回答「**误差多小**才不影响决策」。
- 两者**独立**：「有边界」≠「分类正确」。

### §7.3 ⚠ **R253 删除清单**（**重点**）

| 原定理 | 状态 | 原因 |
|---|---|---|
| `cos_close_implies_norm_close` | **假 → 已删** | 反例 $\|u\|=1,\|v\|=2,K=0.01$；正确化为 `cos_close_general` |
| `euclid_transfer_bound` | **假 → 已删** | 同一反例；正确化为 `unit_transfer_bound`（归一化） |

**替换后的真命题**（均已证）：`cos_close_general`、`unit_transfer_bound`。

### §7.4 ⚠ **同义反复清单**（真但无实质，已保留并标注）

| 定理 | 原因 |
|---|---|
| `margin_decides` | `hs` 代入后即 `sgn s = sgn s` |
| `sqrt_bound_order_sharp` | `∨` 右支由 `K>0` 恒真 |
| `error_bound_independent_of_tauOf` | 只包一层 `∀`，参数未用 |
| `linScore_eq_sum` | `rfl` |

### §7.5 未解项

| # | 未解项 | 为何未解 |
|---|---|---|
| 1 | $\varepsilon$ 的**统计估计** | 需固定编码/损失函数（OQ-4） |
| 2 | $\sqrt{2K}$ 在**归一化**下是否最优 | 本文件只证 $\le\sqrt{2K}$；最优常数需更精细分析 |
| 3 | **多类**（$>2$）情形 | `sgn` 是二类；多类需 `argmax` |
| 4 | **非线性打分器**的几何版 | §4 给任意 $f$ 的逐点版，几何版需内积 |
| 5 | 任意范数下的 $\sqrt\cdot$ 型界 | **不存在**（见 §B 反例）；只能保留 $(P-Q)^2$ 项 |

**⚠ 无 `sorry` / `admit` / `axiom`。**
-/

end

end R253ErrorBound

end FateV2.Error

/-! ===========================================================================
  §R36  **R-36 接线：观测噪声链 ⟹ 分类稳健性**

  `FateV2.Error/ObsEstimationWeak` 只给「观测集 `obsClass η h y`」及其**集合论 / 度量**性质
  （含 `dist_le_two_mul_of_mem_obsClass`：同类的两点观测值差 ≤ `2η`），
  但**从未**把它接到分类决策上。本文件（`ErrorBoundChain`）**只**做
  「误差界 ⟹ 符号不变」的纯实数命题 (`error_bound_gives_correct_classification`)。

  本节把两块接起来，**这是二者的第一次接线**：

  | 名字 | 内容 |
  |---|---|
  | `score_diff_le_two_mul` | 观测同类 ⟹ 打分差 ≤ `2η`（实数域特化）|
  | `obsClass_sgn_stable`   | **观测噪声 ≤ η 且 `4η < |f x|` ⟹ 同类点同号** |
  | `obsModel_sgn_stable`   | 模型版（用 `ObsModel.NoiseRespects`）|
  | `obsClass_sgn_stable_general` | 逐点 `ε` 的一般输入空间版 |
  | `obsClass_zero_sgn_eq`  | 零噪声退化：同类点打分数值相等 |

  ⚠ **非平凡处**：`ObsEstimationWeak` 的结论是**度量**不等式 `dist (h x₁) (h x₂) ≤ 2η`，
  本文件的结论是 **符号**相等 `sgn (f x₂) = sgn (f x₁)`。中间必须
  （a）在 `Y = ℝ` 上把 `dist` 翻成 `|·|`，并把 `|f x₁|` 的扰动写成
  `f x₁ + (f x₂ - f x₁)`；（b）调用本文件的**主定理 A**（常数 `1/2` 紧）。
  两条结论属于**完全不同的语言**，此前没有任何定理连接它们。

  ⚠ **诚实边界**：`4η < |f x₁|` 是**真前件**（不是结论的重述）：
  它把观测噪声 `2η` 严格压在间隔的一半以下。该常数**不可改进**
  到 `4η = |f x₁|`（那是本文件 §3 的 `perturbation_affects_decision` 情形）。
  =========================================================================== -/

namespace FateV2.Error

namespace R253ErrorBound

open Set

section R36ObsChain

variable {X : Type*}

/-- **同一观测类内的打分数值差 ≤ `2η`**（`ObsEstimationWeak` ⟹ 实数域）。

前件：`x₁`、`x₂` 同属 `obsClass η f y`（`f` 同时充当观测函数与打分函数）。
结论：`|f x₁ - f x₂| ≤ 2η`。

⚠ 非平凡处：`ObsEstimationWeak.dist_le_two_mul_of_mem_obsClass` 给的是
`dist (f x₁) (f x₂) ≤ 2η`（`Y = ℝ` 上的距离），本定理把它翻成 `|·|` 形式
（`Real.dist_eq`），这是后续调用 `error_bound_gives_correct_classification`
（其前件是 `|δ| ≤ ε`）**必须**的一步。前件不含结论。 -/
theorem score_diff_le_two_mul {f : X → ℝ} {y : ℝ} {η : ℝ} {x₁ x₂ : X}
    (h₁ : x₁ ∈ ObsEstimationWeak.obsClass η f y)
    (h₂ : x₂ ∈ ObsEstimationWeak.obsClass η f y) :
    |f x₁ - f x₂| ≤ 2 * η := by
  have h := ObsEstimationWeak.dist_le_two_mul_of_mem_obsClass h₁ h₂
  rwa [Real.dist_eq] at h

/-- **【主定理】观测噪声 ⟹ 分类稳健**。

若 `x₁, x₂` 落在同一观测类 `obsClass η f y` 中，且间隔**严格大于**噪声的两倍
（`4η < |f x₁|`），则两点的**分类符号相同**。

证明：`score_diff_le_two_mul` 给 `|δ| ≤ ε`（取 `δ := f x₂ - f x₁`、`ε := 2η`），
再把 `2 * ε < |f x₁|` 由 `4η < |f x₁|` 读出，交给本文件 §2 的主定理 A。

⚠ 非平凡处：前件是**两个模块各自的**假设（集合成员 + 间隔下界），
结论是符号等式；**符号不出现在任何前件里**。 -/
theorem obsClass_sgn_stable {f : X → ℝ} {y : ℝ} {η : ℝ} {x₁ x₂ : X}
    (h₁ : x₁ ∈ ObsEstimationWeak.obsClass η f y)
    (h₂ : x₂ ∈ ObsEstimationWeak.obsClass η f y)
    (hgap : 4 * η < |f x₁|) :
    sgn (f x₂) = sgn (f x₁) := by
  have hd : |f x₂ - f x₁| ≤ 2 * η := by
    have := score_diff_le_two_mul h₁ h₂
    rwa [abs_sub_comm] at this
  have hη : (0:ℝ) ≤ 2 * η := by
    have := hd; rw [abs_sub_comm] at this; linarith [abs_nonneg (f x₁ - f x₂)]
  have hpos : 0 < |f x₁| := by linarith
  have hkey := error_bound_gives_correct_classification (s := f x₁) (δ := f x₂ - f x₁)
    (ε := 2 * η) hpos hd (by linarith)
  have he : f x₁ + (f x₂ - f x₁) = f x₂ := by ring
  rwa [he] at hkey

/-- **模型版**：用 `ObsModel.NoiseRespects`（而非裸集合成员）给出同一结论。

⚠ 非平凡处：`ObsModel` 把「观测函数 + 噪声上界」打包；`NoiseRespects`
是关于 `etaMax` 的**单点**陈述，而结论是**两点**的符号一致 ——
中间必须经 `ObsModel.true_mem_obsSet` 把两点都送进同一个 `obsClass`，
再调用 `obsClass_sgn_stable`。 -/
theorem obsModel_sgn_stable {Y : Type*} [PseudoMetricSpace Y]
    (M : ObsEstimationWeak.ObsModel X ℝ) {y : ℝ} {x₁ x₂ : X}
    (h₁ : M.NoiseRespects x₁ y) (h₂ : M.NoiseRespects x₂ y)
    (hgap : 4 * M.etaMax < |M.h x₁|) :
    sgn (M.h x₂) = sgn (M.h x₁) :=
  obsClass_sgn_stable (ObsEstimationWeak.ObsModel.true_mem_obsSet M h₁)
    (ObsEstimationWeak.ObsModel.true_mem_obsSet M h₂) hgap

/-- **逐点 `ε` 的一般版**（任意输入空间，噪声界可逐点变化）。

`ε : X → ℝ` 为逐点噪声预算：`|f x₁ − f x₂| ≤ ε`、`2ε < |f x₁|` ⟹ 同号。

⚠ 非平凡处：把本文件 §4 的 `learning_bound_general` 的**逐点形式**
落到「两点比较」上（`learning_bound_general` 原本陈述为 `∀ x`）。
前件是实数的逐点不等式，结论是对**不同点**的符号比较。 -/
theorem obsClass_sgn_stable_general {f : X → ℝ} {ε : ℝ} {x₁ x₂ : X}
    (hd : |f x₂ - f x₁| ≤ ε) (hgap : 2 * ε < |f x₁|) :
    sgn (f x₂) = sgn (f x₁) := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) hd
  have hpos : 0 < |f x₁| := by linarith
  have hkey := error_bound_gives_correct_classification (s := f x₁) (δ := f x₂ - f x₁)
    (ε := ε) hpos hd hgap
  have he : f x₁ + (f x₂ - f x₁) = f x₂ := by ring
  rwa [he] at hkey

/-- **零噪声退化**：`η = 0` 时观测类退化为精确纤维（`ObsEstimationWeak` 的
`obsClass_zero_eq_hFiber`），此时同类点打分数值**相等**，从而符号相同。

⚠ 非平凡处：结论把 `ObsEstimationWeak.obsClass_zero_eq_hFiber`
（集合层面）与本文件的主定理 A 在 `ε = 0` 的端点情形**串联**；
主定理 A 的前件 `2 * ε < |s|` 在 `ε = 0` 时要求 `0 < |s|`，不可省。 -/
theorem obsClass_zero_sgn_eq {f : X → ℝ} {y : ℝ} {x₁ x₂ : X}
    (hx₁ : f x₁ = y) (h₂ : x₂ ∈ ObsEstimationWeak.obsClass 0 f y)
    (hpos : 0 < |f x₁|) :
    sgn (f x₂) = sgn (f x₁) := by
  have hmem : x₁ ∈ ObsEstimationWeak.obsClass 0 f y := by
    rw [ObsEstimationWeak.obsClass_zero_eq_hFiber]
    simpa [ObsEstimationWeak.hFiber] using hx₁
  have hd : |f x₂ - f x₁| ≤ 2 * (0 : ℝ) := score_diff_le_two_mul h₂ hmem
  have hzero : f x₂ = f x₁ := by
    have : |f x₂ - f x₁| = 0 := le_antisymm (by linarith) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp this)
  exact congrArg sgn hzero

end R36ObsChain

end R253ErrorBound

end FateV2.Error
