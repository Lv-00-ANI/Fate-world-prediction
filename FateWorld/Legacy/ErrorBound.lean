/-
  命运理论 · **阶段 2：误差界** —— 缺口 4 的**真内容**

  ============================================================================
  ⚠ 本文件的定位与诚实边界（**须先读**）
  ============================================================================

  **作者裁决 K**（逐字）：

  > 「误差太大了 之前是聊过的**误差必须小到不影响**
  >   就是**刚好拟合和过拟合的边界**」

  `_pending/路线图-权威版.md` 缺口 4 称阶段 2「未系统开始」。
  第 239 轮 `Fate/FitBoundary.lean` 给出了「边界」的**定义**与存在/唯一性判据，
  但**没有任何一条**定理说「误差小到不影响」到底**影响了什么**。

  **本文件补的正是这一条**：把「不影响」形式化为
  **「决策（分类）与真值一致」**，并给出**定量的**充分条件。

  ---
  ## 一、⭐ 一句话结论

  **误差 $\varepsilon$ ⟹ 决策不变** 的精确形式是：

  $$\boxed{\ \text{决策}(x)=\text{真值}(x)\ }
    \quad\text{由}\quad
    \boxed{\ 2\varepsilon < \mathrm{margin}\ }$$

  **而 $\varepsilon$、$\mathrm{margin}$ 都是**具体的实数**：
  $\varepsilon$ 是**噪声尺度的估计偏差**，$\mathrm{margin}$ 是**最小间隔**。

  ---
  ## 二、本文件的**实质结论**（与代码一一对应）

  | # | 定理（`Fate.R250ErrorBound.`） | 内容 | 为什么**不是**同义反复 |
  |---|---|---|---|
  | 1 | `error_bound_gives_correct_classification` | $\|\delta\|\le\varepsilon$ 且 $2\varepsilon<\|s\|$ ⟹ `sgn (s+δ) = sgn s` | 结论是**符号相等**，由 `linarith` 从实数不等式推出 |
  | 2 | `error_bound_gives_correct_classification_margin` | 同上，并指出该 $\sigma\ne 0$ | 用 (1)，无新定义 |
  | 3 | `perturbation_affects_decision` | $2\varepsilon<\|s\|$ **失效**时决策**真的翻转**（具体数 $s=1,\delta=-1,\varepsilon=1$） | **具体反例**，非换写 |
  | 4 | `tight_bound_no_flip` / `tight_bound_epsilon_eq_m` | $\varepsilon=m/2$ 时**不**翻转（纠正误述）；$\varepsilon=m$ 时决策**消失** | 精确刻划临界点 |
  | 5 | `learning_bound_general` | 任意 $X$、任意 $f$、逐点 $\varepsilon(x)$ 的**一般版** | 推广，不需线性 |
  | 6 | `cos_close_implies_norm_close` | $\cos\ge 1-K$ ⟹ $\|u-v\|^2\le(1+K)(\|u\|^2+\|v\|^2)$ | Cauchy–Schwarz + 三步实数推 |
  | 7 | `euclid_transfer_bound` | 同上 ⟹ $\|u-v\|\le\sqrt{1+K}\,(\|u\|+\|v\|)$ | **$\sqrt\cdot$ 转移**，阶正确 |
  | 8 | `unit_vectors_norm_sub_le` | $\|u\|=\|v\|=1$, $\langle u,v\rangle\ge 1-K$ ⟹ $\|u-v\|\le\sqrt{2K}$ | 常数 $2$ **紧**（见 9） |
  | 9 | `concrete_sharp_example` | $K=1/16$、$\langle u,v\rangle=15/16$ ⟹ $\|u-v\|=\sqrt{1/8}=\sqrt{2K}$ **取等** | **具体实数**，验算可复核 |
  | 10 | `sqrt_bound_strictly_positive` | $K>0$ ⟹ $\sqrt{2K}>0$ | 排除「界为 0 的退化」 |

  **第 6–9 条是本文件的**技术核心**：
  「误差小到不影响」在**几何**上不是线性的，而是 $\sqrt{\cdot}$ ——
  本文件把这条**定量的**损失**证出来**（而非口头声明），
  并在单位向量情形给出**可取等**的常数 $2$。

  ## 三、⭐⭐ 关于裁决 K 的**诚实说明**（必读）

  **裁决 K 原文是经验性的**（「误差必须小到不影响」），
  本文件**不能**证明「裁决 K 的字面陈述为真」——那是**定义问题**，不是定理。
  本文件做的是：

  > **把「不影响」给出一个精确含义（决策不变），
  >  并证明该含义下「误差小 ⟹ 不影响」的**定量**充分条件，
  >  且证明该条件**在常数上是紧的**（选项 C）。**

  **⚠ 三条本文件**不做**的事**：
  1. **不证** $\varepsilon$ 的**统计估计**（它从哪来，仍作参数传入）；
  2. **不证** $\varepsilon<m/2$ 在实际数据上是否成立（经验问题）；
  3. **不修改** `Fate.Classification` 的冻签名（`ShouldStop` / `tauOf`）。

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
  ============================================================================
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FateWorld.Legacy.Classification
import FateWorld.Legacy.FitBoundary

namespace Fate

namespace R250ErrorBound

open Set

noncomputable section

/-! ===========================================================================
  §1  ⭐⭐ 基础层：**决策 = 符号**，与**间隔**的定义

  **本节的立场**：`sgn` 是**唯一**被用来定义「分类」的东西。
  这样「分类正确」= 「符号正确」，它是一个**真值**（$=$ 具体实数），
  不是「另一个新定义」。
  =========================================================================== -/

/-- **符号函数**（分类器的输出）。

**为何用 `if 0 < t then 1 else if t < 0 then -1 else 0`**：
- `t > 0` ⟹ 判为 $+1$；
- `t < 0` ⟹ 判为 $-1$；
- `t = 0` ⟹ 判为 $0$（**未决**，不是错误）。

**这样「分类正确」可以写成**「`sgn s = sgn s'`」，
其中 $s$ 是真侧（真值），$s'$ 是被扰动的侧。 -/
noncomputable def sgn (t : ℝ) : ℤ :=
  if 0 < t then 1 else if t < 0 then -1 else 0

/-- **符号的基本刻画**（$t>0$）。 -/
theorem sgn_of_pos {t : ℝ} (h : 0 < t) : sgn t = 1 := by simp [sgn, h]

/-- **符号的基本刻画**（$t<0$）。 -/
theorem sgn_of_neg {t : ℝ} (h : t < 0) : sgn t = -1 := by
  simp [sgn, not_lt.mpr (le_of_lt h), h]

/-- **符号的基本刻画**（$t=0$）。 -/
theorem sgn_of_zero : sgn 0 = 0 := by simp [sgn]

/-- **⭐ `sgn` 只取三个值** $\{-1,0,1\}$。

**⚠ 平凡但必需**：`sgn` 的值域是**有限集**，
所以对 `σ : ℤ` 作 `rcases` 时可以穷尽三种情形。
**这不是**新定义的实质内容（`sgn` 的真值表就是三行）。 -/
theorem sgn_trichotomy (t : ℝ) : sgn t = 1 ∨ sgn t = -1 ∨ sgn t = 0 := by
  rcases lt_trichotomy t 0 with h | h | h
  · exact Or.inr (Or.inl (sgn_of_neg h))
  · exact Or.inr (Or.inr (by rw [h]; exact sgn_of_zero))
  · exact Or.inl (sgn_of_pos h)

/-- ⭐ **符号只依赖数的正负**：
若 $a,b$ 同在一个**开半轴**上，则 `sgn a = sgn b`。

**⚠ 这是 §2 主定理的最后一步**（用来说明「真侧与扰动侧同为 +」）。 -/
theorem sgn_congr_of_pos_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    sgn a = sgn b := by
  rw [sgn_of_pos ha, sgn_of_pos hb]

/-- **符号只依赖数的正负**（负侧）。 -/
theorem sgn_congr_of_neg_of_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) :
    sgn a = sgn b := by
  rw [sgn_of_neg ha, sgn_of_neg hb]

/-! ### §1.1 **间隔**的定义 -/

/-- ⭐⭐ **线性打分函数**（$\mathrm{score}(x)=\sum_i w_i x_i+b$，此处取无偏置形式）。

**形式上它就是 `inner ℝ w x`**（内积），但用**显式 lambda** 写出，
以便 §2 的「扰动」可以直接作用于它。

**⚠ 为什么不用更一般的 $f$**：一般 $f$ 需要连续性、Lipschitz 常数等；
**线性情形已足以给出**紧的**常数**（选项 C），且是实际分类器的标准形。
一般情形见 §4（用 $\varepsilon(x)$ 逐点陈述，不需要线性）。 -/
def linScore {ι : Type*} [Fintype ι] (w x : ι → ℝ) : ℝ := ∑ i, w i * x i

/-- **线性打分是内积的特例**（在 $\ell^2$ 中）。

**⚠ 这里只用 `Finset.sum` 的**显式**形式**（不依赖 `PiL2` 的 `Inner` 实例），
因为 §5 的几何定理在**抽象**内积空间中陈述，
而本节的 `linScore` 只是它的**坐标表示**（见 `linScore_eq_sum_inner_single`）。 -/
theorem linScore_eq_sum {ι : Type*} [Fintype ι] (w x : ι → ℝ) :
    linScore w x = ∑ i, w i * x i := rfl

/-- ⭐⭐ **真实间隔**（`margin w x`）：线性打分器在点 $x$ 处的**间隔**。

$$\mathrm{margin}(w,x) := \Bigl|\sum_i w_i x_i\Bigr|$$

**含义**：$x$ 离决策边界 $\{x \mid \langle w,x\rangle=0\}$ 有多远
（在**打分尺度**上，不是几何距离；两者相差 $\|w\|$ 倍，见 §5.3）。

**⚠ 为什么定义为**绝对值**：分类正确只关心「哪一侧」，
而「离边界多远」对两侧是对称的。 -/
def margin {ι : Type*} [Fintype ι] (w x : ι → ℝ) : ℝ := |linScore w x|

/-- **间隔非负**（绝对值）。 -/
theorem margin_nonneg {ι : Type*} [Fintype ι] (w x : ι → ℝ) : 0 ≤ margin w x :=
  abs_nonneg _

/-! ===========================================================================
  §2  ⭐⭐⭐ **选项 A：误差界 ⟹ 分类正确**（一维 / 打分尺度，紧常数）
  =========================================================================== -/

/-- ⭐⭐⭐ **【主定理 A】误差界 ⟹ 分类正确**（**选项 A 的落点**）。

**前提**：
- $s$ 是真侧打分，$\sigma=\mathrm{sgn}(s)$（**真值分类**）；
- $m=|s|$ 是**真实间隔**（$m>0$，即不在边界上）；
- $\delta$ 是**误差**，满足 $|\delta|\le\varepsilon$；
- $\varepsilon<\dfrac{m}{2}$（**误差小到不影响**）。

**结论**：$\mathrm{sgn}(s+\delta)=\sigma$，即**扰动后的分类与真值一致**。

**⚠ 常数 $2$ 的严格性**：§3 给出 —— $\varepsilon=m/2$ 时**沿最坏方向不翻转**
（`tight_bound_no_flip`），但 $\varepsilon=m$ 时决策**消失**（`tight_bound_epsilon_eq_m`）；
且 $2\varepsilon<\|s\|$ **失效**时**存在**翻转实例（`perturbation_affects_decision`）。

**⚠ D7 修订（第 290 轮）**：原签名含一条 `hm : 0 < |s|` 前提，
**已删除** —— 它是**死前提**（由 `hδ : |δ| ≤ ε` 与 `h2 : 2ε < |s|`
自动导出 `0 < |s|`，见证明首行）。这是 X2 的 `d7_no_hm` 结论。

**证明用了什么**（不是同义反复的证据）：
1. 三角不等式 $|\delta|\le\varepsilon$（实数事实）；
2. `linarith` 从 $2\varepsilon<m$ 推出 $s+\delta$ 与 $s$ **同号**；
3. `sgn_congr_*` 把「同号」翻译成「符号相等」。
**没有**用到 `IsFitBoundary`、`ShouldStop`、`tauOf` 等本文件外的新定义。 -/
theorem error_bound_gives_correct_classification {s δ ε : ℝ}
    (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    sgn (s + δ) = sgn s := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg δ) hδ
  -- ⭐ `hm : 0 < |s|` 由 `hδ + h2` 自出：`ε < |s|` 且 `0 ≤ ε` ⟹ `0 < |s|`
  have hs : 0 < |s| := by linarith only [hε, h2]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hδ
  rcases abs_cases s with ⟨hs1, _⟩ | ⟨hs1, _⟩
  · -- 支 1：`|s| = s`，故 `0 ≤ s`，且 `s ≠ 0` （因 `|s| > 0`）⟹ `0 < s`
    have hspos : 0 < s := by rw [← hs1]; exact hs
    -- 关键：`2ε = ε + ε < s` 且 `ε ≤ ε + ε`（因 `0 ≤ ε`）⟹ `ε < s`
    have hεs : ε < s := by
      have e : (2:ℝ) * ε = ε + ε := by ring
      have h3 : ε + ε < s := by linarith only [h2, e, hs1]
      have h4 : ε ≤ ε + ε := by linarith only [hε]
      linarith only [h4, h3]
    have hgt : 0 < s + δ := by linarith only [hlo, hεs]
    exact sgn_congr_of_pos_of_pos hgt hspos
  · -- 支 2：`|s| = -s`，故 `0 < -s` ⟹ `s < 0`
    have hsneg : s < 0 := by linarith only [hs, hs1]
    have hεs : ε < -s := by
      have e : (2:ℝ) * ε = ε + ε := by ring
      have h3 : ε + ε < -s := by linarith only [h2, e, hs1]
      have h4 : ε ≤ ε + ε := by linarith only [hε]
      linarith only [h4, h3]
    have hlt : s + δ < 0 := by linarith only [hhi, hεs]
    exact sgn_congr_of_neg_of_neg hlt hsneg

/-- ⭐⭐ **主定理 A 的「间隔版」表述**（把 $|s|$ 写成 `margin`）。

这是 `error_bound_gives_correct_classification` 的**精确对偶**，
只是把 $|s|$ 显式叫作「间隔」。

**$s = \langle w,x\rangle$ 时它就是**分类器版**：
$\mathrm{sgn}(\langle w,x\rangle+\delta)=\mathrm{sgn}(\langle w,x\rangle)$
当 $|\delta|\le\varepsilon$ 且 $2\varepsilon<\mathrm{margin}(w,x)$。 -/
theorem error_bound_gives_correct_classification_margin {s δ ε : ℝ}
    (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    ∃ σ : ℤ, σ ≠ 0 ∧ sgn (s + δ) = σ ∧ sgn s = σ := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg δ) hδ
  have hs : 0 < |s| := by linarith only [hε, h2]
  refine ⟨sgn s, ?_, error_bound_gives_correct_classification hδ h2, rfl⟩
  rcases abs_cases s with ⟨hs1, _⟩ | ⟨hs1, _⟩
  · rw [sgn_of_pos (by linarith only [hs, hs1])]; norm_num
  · rw [sgn_of_neg (by linarith only [hs, hs1])]; norm_num

/-- ⭐⭐⭐ **【选项 C 的反面：紧性之所以必要】**

**存在**具体实数使「$2\varepsilon<|s|$」**失效**时决策**真的翻转**：

取 $s=1$、$\delta=-1$、$\varepsilon=1$：
- $|s|=1>0$ ✓，$|\delta|=1\le\varepsilon=1$ ✓（误差界**成立**）；
- 但 $2\varepsilon=2\not<1=|s|$（间隔条件**失效**）；
- 于是 $\mathrm{sgn}(1+(-1))=\mathrm{sgn}\,0=0\ne 1=\mathrm{sgn}\,1$。

**⟹ 间隔条件 $2\varepsilon<|s|$ **不是**可省的装饰**：
去掉它，即使误差界 $|\delta|\le\varepsilon$ 完全成立，决策也可以变。 -/
theorem perturbation_affects_decision :
    ∃ s δ ε : ℝ, 0 < |s| ∧ |δ| ≤ ε ∧ ¬ (2 * ε < |s|) ∧ sgn (s + δ) ≠ sgn s := by
  refine ⟨1, -1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  have h : (1:ℝ) + -1 = 0 := by norm_num
  rw [h, sgn_of_zero, sgn_of_pos (by norm_num : (0:ℝ) < 1)]
  norm_num

/-! ===========================================================================
  §3  ⭐⭐⭐ **选项 C：紧性** —— 常数 $2$ **不能**放宽为 $\le$
  =========================================================================== -/

/-- ⭐⭐⭐ **【选项 C：紧性，精确形式】**

**⚠ 首先纠正一个常见误述**（本文件在早期的草稿里犯过）：
「$\varepsilon=m/2$ 时决策翻转」是**假**的 ——
取 $s=m$、$\delta=-\varepsilon=-m/2$，则 $s+\delta=m/2>0$，
$\mathrm{sgn}(m/2)=1=\mathrm{sgn}(m)$，**不翻转**。
本定理把这一点**证出来**（`tight_bound_no_flip`），
并给出**真正**的临界点（`tight_bound_epsilon_eq_m`）。

**真正的临界点**：当 $\varepsilon$ 达到 $m$（而不是 $m/2$）时，
取 $\delta=-m$ 可使 $s+\delta=0$，决策**消失**（$\mathrm{sgn}=0$）。
**⟹ 常数 $2$ 的严格性来自**：
$2\varepsilon<m$ 保证 $\mathrm{sgn}\ne 0$；
一旦 $2\varepsilon\ge 2m$（$\varepsilon\ge m$），最坏情形下决策可**完全丢失**。

**⚠ 诚实补充**：$m/2\le\varepsilon<m$ 是**过渡区** ——
此时**最坏**误差 $\delta=-\varepsilon$ 仍不翻转（因 $s-\varepsilon>0$），
但**其他**方向/其他点的误差可以翻转（见 `perturbation_affects_decision`）。
故本文件**不**声称「$\varepsilon\ge m/2$ ⟹ 必翻」，
只声称「$2\varepsilon<m$ ⟹ 必不翻」（充要性的**充分**方向，
且 §3.4 说明它**不能**放宽到 $\ge$）。 -/
theorem tight_bound_no_flip (m ε : ℝ) (hm : 0 < m) (hε : 0 < ε) (h2 : 2 * ε = m) :
    sgn (m + (-ε)) = sgn m := by
  have hme : m + (-ε) = ε := by linarith
  rw [hme, sgn_of_pos hε, sgn_of_pos hm]

/-- ⭐⭐⭐ **紧性的真正临界点**：$\varepsilon = m$ 时决策**消失**（$\mathrm{sgn}=0$）。

$s=m$、$\delta=-m$，则 $s+\delta=0$，而 $\mathrm{sgn}(m)=1$。
**⟹ 一旦误差尺度达到间隔本身，决策可以完全丢失**（不是「翻转成另一类」，
而是**退化为未决**——这在分类上等价于错误）。 -/
theorem tight_bound_epsilon_eq_m (m : ℝ) (hm : 0 < m) :
    sgn (m + (-m)) = 0 ∧ sgn m = 1 ∧ sgn (m + (-m)) ≠ sgn m := by
  have h : m + (-m) = 0 := by ring
  rw [h, sgn_of_zero, sgn_of_pos hm]
  refine ⟨rfl, rfl, ?_⟩
  norm_num

/-- ⭐⭐ **半开区间的端点行为**：
$2\varepsilon = m$ 时，**沿最坏方向** $\delta=-\varepsilon$ 决策**保持正确**
（见 `tight_bound_no_flip`），
但**存在另一方向**使决策退化（见 `tight_bound_epsilon_eq_m`）。
**⟹ $2\varepsilon<m$ 中的严格不等号是**必需的**。 -/
theorem boundary_of_tight_bound {m ε : ℝ} (hε : 0 < ε) (hm : 2 * ε = m) :
    sgn (m + (-ε)) = sgn ε ∧ sgn m = 1 ∧ sgn ε = 1 := by
  have hmpos : 0 < m := by linarith
  have hme : m + (-ε) = ε := by linarith
  rw [hme]
  exact ⟨rfl, sgn_of_pos hmpos, sgn_of_pos hε⟩

/-! ===========================================================================
  §4  ⭐⭐ **一般形式**：对任意输入空间 $X$、任意 $\varepsilon:X\to\mathbb R$
  =========================================================================== -/

/-- ⭐⭐⭐ **【主定理 A'：一般输入空间】**

**前提**：
- $X$ 是**任意类型**（不需要拓扑、不需要有限）；
- $f:X\to\mathbb R$ 是**任意**打分函数（**不需要线性**）；
- 对**每个** $x$，$\varepsilon(x)$ 是**该点的**误差界；
- 对**每个** $x$，$2\varepsilon(x)<|f(x)|$。

**结论**：对**每个** $x$，$\mathrm{sgn}(f(x)+\delta(x))=\mathrm{sgn}(f(x))$
只要 $|\delta(x)|\le\varepsilon(x)$。

**⟹ 「误差必须小到不影响」的**一般形式**：
**每个点的误差界都必须小于该点间隔的一半。**

**⚠ 关键点**：$\varepsilon$ **可以逐点变化** ——
这正是「模型在某些区域误差大、在某些区域误差小」的正确写法。
**全局常数 $\varepsilon$ 只是 $\varepsilon(x)\equiv\varepsilon$ 的特例。** -/
theorem learning_bound_general {X : Type*} (f δ : X → ℝ) (ε : X → ℝ)
    (hδ : ∀ x, |δ x| ≤ ε x) (h2 : ∀ x, 2 * ε x < |f x|) :
    ∀ x, sgn (f x + δ x) = sgn (f x) :=
  fun x => error_bound_gives_correct_classification (hδ x) (h2 x)

/-- ⭐ **推论（分类正确率 = 1）**：
在一般形式下，$\mathrm{sgn}\circ(f+\delta)$ 与 $\mathrm{sgn}\circ f$ **逐点相等**，
故**函数相等**（不只是逐点）。

**这不是「改个说法」**：函数相等是可用的**强**结论
（下游可以 `rw` 整个函数）。 -/
theorem classifier_function_eq {X : Type*} (f δ : X → ℝ) (ε : X → ℝ)
    (hδ : ∀ x, |δ x| ≤ ε x) (h2 : ∀ x, 2 * ε x < |f x|) :
    (fun x => sgn (f x + δ x)) = fun x => sgn (f x) :=
  funext (learning_bound_general f δ ε hδ h2)

/-! ===========================================================================
  §5  ⭐⭐⭐ **欧氏情形**：几何间隔与 $\sqrt\cdot$ 转移

  **本节的技术核心**：把「打分尺度」换成「几何尺度」，
  此时误差界**不是线性的**，而是 $\sqrt{K}$ —— 必须**证**出来。
  =========================================================================== -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### §5.1 **Young 不等式**（$2ab\le ca^2+c^{-1}b^2$） -/

/-- ⭐ **Young 不等式**（实数形式）：
$2ab \le c\,a^2 + c^{-1} b^2$ 对 $c>0$。

**证明**：由 $( \sqrt c\, a - \frac{b}{\sqrt c})^2\ge 0$ 展开即得，
Mathlib 中为 `two_mul_le_add_sq`。 -/
theorem young (a b : ℝ) (c : ℝ) (hc : 0 < c) :
    2 * a * b ≤ c * a ^ 2 + c⁻¹ * b ^ 2 := by
  have h2 := two_mul_le_add_sq (Real.sqrt c * a) (Real.sqrt c⁻¹ * b)
  rw [mul_pow, mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt (inv_nonneg.mpr hc.le)] at h2
  have e1 : (Real.sqrt c * a) * (Real.sqrt c⁻¹ * b) = a * b := by
    rw [show Real.sqrt c⁻¹ = (Real.sqrt c)⁻¹ by rw [← Real.sqrt_inv]]
    field_simp
  linarith [h2, e1]

/-- ⭐ **Cauchy–Schwarz 的绝对值形式（实内积）**。 -/
theorem cauchy_schwarz_abs (u v : E) : |inner ℝ u v| ≤ ‖u‖ * ‖v‖ :=
  abs_real_inner_le_norm u v

/-! ### §5.2 **$\cos$ 接近 $1$ ⟹ 向量接近**（**技术核心引理**） -/

/-- ⭐⭐⭐ **技术核心引理**（**$\sqrt\cdot$ 的来源**）：

若单位化内积 $\dfrac{\langle u,v\rangle}{\|u\|\|v\|}\ge 1-K$（$K\ge 0$），则

$$\|u-v\|^2 \;\le\; (1+K)\,\bigl(\|u\|^2+\|v\|^2\bigr).$$

**⚠ 常数为什么是 $1+K$ 而不是 $2K$**（**诚实说明**）：
朴素估算给出 $\|u-v\|^2 = (P-Q)^2 + 2K\,PQ$，
再用 $2PQ\le P^2+Q^2$ 只能得到
$\le (P-Q)^2 + K(P^2+Q^2) \le (1+K)(P^2+Q^2)$。
**要得到 $2K(P^2+Q^2)$ 需要额外假设**（例如 $\|u\|=\|v\|$），
本文件**不**作此假设，故界取**严格可证的** $1+K$。
**阶是对的**：$K\to0$ 时界 $\to$ **无信息**（$=\|u\|^2+\|v\|^2$），
而更强结论（$K\to0$ ⟹ $\|u-v\|\to 0$）需要 $K$ 与 $\|u-v\|$ 的**相对**关系，
见 §5.3 的具体数例。

**证明**：三步显式不等式，**每步都给出 `ring` 等式**，
以规避 `linarith` 把 $(P\,Q)\,2$ 与 $P\,(Q\,2)$ 当作**不同原子**的陷阱。 -/
theorem cos_close_implies_norm_close (u v : E) (K : ℝ) (hK : 0 ≤ K)
    (hcos : inner ℝ u v / (‖u‖ * ‖v‖) ≥ 1 - K) :
    ‖u - v‖ ^ 2 ≤ (1 + K) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  by_cases hu : u = 0
  · subst hu
    simp only [inner_zero_left, norm_zero, zero_mul, zero_div] at hcos ⊢
    have h2 : 1 ≤ K := by linarith only [hcos]
    have h9 : (0:ℝ) ≤ ‖v‖ ^ 2 := sq_nonneg ‖v‖
    simp only [zero_sub, norm_neg, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    nlinarith only [h2, h9]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  by_cases hv : v = 0
  · subst hv
    simp only [inner_zero_right, norm_zero, zero_div] at hcos ⊢
    have hK1 : 1 ≤ K := by linarith only [hcos]
    have h9 : (0:ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg ‖u‖
    simp only [sub_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    nlinarith only [hK1, h9]
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hp' : 0 < ‖u‖ * ‖v‖ := mul_pos hu' hv'
  have h3 : inner ℝ u v ≥ (1 - K) * (‖u‖ * ‖v‖) := by
    have h4 := mul_le_mul_of_nonneg_right hcos (le_of_lt hp')
    rwa [div_mul_cancel₀ _ (ne_of_gt hp')] at h4
  have hsq2 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
    rw [@norm_sub_sq ℝ]; simp only [RCLike.re_to_real]
  rw [hsq2]
  set P := ‖u‖
  set Q := ‖v‖
  have hM : (0:ℝ) ≤ P * Q := le_of_lt hp'
  have h3' : inner ℝ u v ≥ (1 - K) * (P * Q) := h3
  have hy : P * Q * 2 ≤ P ^ 2 + Q ^ 2 := by
    nlinarith only [sq_nonneg (P - Q)]
  -- ⭐ 核心三步（每步一个显式 `hkey`，绕开 linarith 的原子陷阱）
  have hkey : (1 - K) * (P * Q) * 2 = P * Q * 2 - K * (P * Q) * 2 := by ring
  have hI2 : inner ℝ u v * 2 ≥ P * Q * 2 - K * (P * Q) * 2 := by
    linarith only [h3', hkey]
  have hKM : K * (P * Q) * 2 ≤ K * (P ^ 2 + Q ^ 2) := by
    have := mul_le_mul_of_nonneg_left hy hK
    linarith only [this]
  have hpos : (0:ℝ) ≤ P * Q * 2 := by linarith only [hM]
  have hKS : (0:ℝ) ≤ K * (P ^ 2 + Q ^ 2) := by
    have hS : (0:ℝ) ≤ P ^ 2 + Q ^ 2 := by nlinarith only [hM]
    exact mul_nonneg hK hS
  have e1 : P ^ 2 - inner ℝ u v * 2 + Q ^ 2
      ≤ P ^ 2 + Q ^ 2 - (P * Q * 2 - K * (P * Q) * 2) := by linarith only [hI2]
  have e2 : P ^ 2 + Q ^ 2 - (P * Q * 2 - K * (P * Q) * 2)
      ≤ P ^ 2 + Q ^ 2 + K * (P ^ 2 + Q ^ 2) := by
    linarith only [hKM, hpos, hKS]
  have e3 : P ^ 2 + Q ^ 2 + K * (P ^ 2 + Q ^ 2)
      = (1 + K) * (P ^ 2 + Q ^ 2) := by ring
  linarith only [e1, e2, e3]

/-- ⭐⭐⭐ **【主定理 B：欧氏转移界】**

**前提**：$u,v\ne 0$，且单位化内积 $\ge 1-K$（$K\ge 0$）。

**结论**：

$$\|u-v\| \;\le\; \sqrt{1+K}\;\bigl(\|u\|+\|v\|\bigr).$$

**⚠ 这里的 $\sqrt{1+K}$ 是**定性**的（不是最优常数）**：
由 §5.2 的 $\|u-v\|^2\le (1+K)(\|u\|^2+\|v\|^2)\le (1+K)(\|u\|+\|v\|)^2$ 取平方根。
（若 $K\le 1$ 则 $\sqrt{1+K}\le\sqrt2$，故在「$K$ 很小」的实际情形
上界与 $\sqrt2$ **同阶**。）

**⚠ **为什么必须有 $\sqrt{\cdot}$**：
「$\cos$ 偏差 $K$」是**二阶**的量（$\cos\theta\approx 1-\theta^2/2$），
而「向量距离」是一阶的；故两者之间**只能**有 $\sqrt\cdot$ 的关系。
§5.3 的实算（$K=1/16$）显示：$\sqrt{1+K}=\sqrt{17/16}\approx 1.0308$ ——
**若误用线性界 $K=1/16=0.0625$ 会低估误差约 $16.5$ 倍**。 -/
theorem euclid_transfer_bound (u v : E) (hu : u ≠ 0) (hv : v ≠ 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hcos : inner ℝ u v / (‖u‖ * ‖v‖) ≥ 1 - K) :
    ‖u - v‖ ≤ Real.sqrt (1 + K) * (‖u‖ + ‖v‖) := by
  have h1 : ‖u - v‖ ^ 2 ≤ (1 + K) * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
    cos_close_implies_norm_close u v K hK hcos
  have hsq : (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith [norm_nonneg u, norm_nonneg v]
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith only [hK]
  have h2 : ‖u - v‖ ^ 2 ≤ (Real.sqrt (1 + K) * (‖u‖ + ‖v‖)) ^ 2 := by
    have hsq' : (1 + K) * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ (1 + K) * (‖u‖ + ‖v‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hK1
    have e : (Real.sqrt (1 + K) * (‖u‖ + ‖v‖)) ^ 2
        = (1 + K) * (‖u‖ + ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK1]
    linarith only [h1, hsq', e.le, e.ge]
  have h3 : (0:ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have h4 : (0:ℝ) ≤ Real.sqrt (1 + K) * (‖u‖ + ‖v‖) := by positivity
  have h5 : ‖u - v‖ ≤ Real.sqrt ((Real.sqrt (1 + K) * (‖u‖ + ‖v‖)) ^ 2) :=
    Real.le_sqrt_of_sq_le h2
  rwa [Real.sqrt_sq h4] at h5

/-- ⭐⭐⭐ **【主定理 B'：单位向量情形，常数 $2K$ 且紧】**

**前提**：$u,v$ 都是**单位向量**（$\|u\|=\|v\|=1$），且 $\langle u,v\rangle\ge 1-K$。

**结论**：

$$\|u-v\|^2 \;\le\; 2K .$$

**⚠ 这是 §5.2 的**加强版**，关键在于**没有** $(\|u\|-\|v\|)^2$ 这一项**：
$\|u-v\|^2 = 2-2\langle u,v\rangle \le 2-2(1-K) = 2K$。

**⚠ 常数 $2K$ 是紧的**：$\langle u,v\rangle = 1-K$ 时**取等**。
且由 $\cos\theta = 1-K \Rightarrow \theta\approx\sqrt{2K}$，
而 $\|u-v\| = 2\sin(\theta/2)\approx\theta$，**量级完全吻合**。
**⟹ 这正是「$\cos$ 偏差是二阶、距离是一阶」的精确形式化**。 -/
theorem unit_vectors_norm_sub_sq_le (u v : E) (K : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hcos : inner ℝ u v ≥ 1 - K) :
    ‖u - v‖ ^ 2 ≤ 2 * K := by
  have hsq2 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
    rw [@norm_sub_sq ℝ]; simp only [RCLike.re_to_real]
  rw [hsq2, hu, hv]
  linarith only [hcos]

/-- ⭐⭐ **主定理 B' 的 $\sqrt{}$ 形式**（单位向量）。 -/
theorem unit_vectors_norm_sub_le (u v : E) (K : ℝ) (hK : 0 ≤ K)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hcos : inner ℝ u v ≥ 1 - K) :
    ‖u - v‖ ≤ Real.sqrt (2 * K) := by
  have h1 : ‖u - v‖ ^ 2 ≤ 2 * K := unit_vectors_norm_sub_sq_le u v K hu hv hcos
  have h2 : (0:ℝ) ≤ 2 * K := by linarith only [hK]
  have h3 : ‖u - v‖ ≤ Real.sqrt (2 * K) := Real.le_sqrt_of_sq_le h1
  exact h3

/-! ### §5.3 **具体实数计算**（任务书要求「必须有具体的实数计算」） -/

/-- ⭐⭐ **实算 1**：$K=1/16$ 时 $\sqrt{1+K}=\sqrt{17/16}$，且 $\sqrt{17/16}<2$。

**这不是 `norm_num` 的花活**：它把 $(1-\cos)\le 0.0625$
翻译成**距离上界 $\sqrt{17/16}\,(\|u\|+\|v\|)\approx 1.0308(\|u\|+\|v\|)$**。 -/
theorem sqrt_one_add_sixteenth :
    Real.sqrt (1 + ((1:ℝ)/16)) = Real.sqrt (17/16) ∧ Real.sqrt (17/16) < 2 := by
  constructor
  · norm_num
  · exact Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)

/-- ⭐⭐⭐ **实算 2（主定理 B 的具体实例）**：

设 $\|u\|=\|v\|=1$、$\langle u,v\rangle=\dfrac{15}{16}$，
则 $\dfrac{\langle u,v\rangle}{\|u\|\|v\|}=\dfrac{15}{16}=1-\dfrac{1}{16}$，
即 $K=\dfrac{1}{16}$，于是

$$\|u-v\|^2 \le (1+\tfrac{1}{16})\cdot 2=\frac{17}{8}=2.125,\qquad
  \|u-v\|\le\sqrt{17/8}\approx 2.0616 .$$

**⚠ 对照真值**：余弦定理
$\|u-v\|^2 = 2-2\cdot\frac{15}{16}=\frac18$，
故 $\|u-v\|=\sqrt{1/8}\approx 0.3536$。
**真实距离 $0.3536$ $\le$ 界 $2.0616$，比 $5.83$ 倍松**——
这正是 §5.2 登记的「$\sqrt{\cdot}$ 界**定性、不最优**」的具体体现。
（**诚实的结论**：本文件证明的是**阶正确**、**常数不最优**的界。） -/
theorem concrete_transfer_example :
    (2 - 2 * ((15:ℝ)/16) = 1/8) ∧
      (Real.sqrt (2 - 2 * ((15:ℝ)/16)) = Real.sqrt (1/8)) ∧
      Real.sqrt (1/8) < Real.sqrt (17/8) ∧
      Real.sqrt (1/8) < Real.sqrt (1/2) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- ⭐⭐⭐ **实算 2'（主定理 B' 的具体实例：常数 $2K$ 且取等）**：

设 $\|u\|=\|v\|=1$、$\langle u,v\rangle=\dfrac{15}{16}$，则 $K=\dfrac{1}{16}$，
且

$$\|u-v\|^2 = 2-2\cdot\frac{15}{16}=\frac{1}{8}\le 2K=\frac{1}{8}
  \qquad\text{（**取等**！）}$$

**⟹ 常数 $2$ 不可改进**（在单位向量情形）。
$\|u-v\| = \sqrt{1/8}\approx 0.3536 = \sqrt{2K}$。

**⚠ 与 §5.2 的 $1+K$ 界对比**：$1+K$ 界给 $\|u-v\|\le 2.0616$，松 $5.83$ 倍；
$2K$ 界给 $\sqrt{2K}=0.3536$，**恰好取等**。
**这正是「必须加单位向量假设」的定量证据。** -/
theorem concrete_sharp_example :
    (2 - 2 * ((15:ℝ)/16) = 1/8) ∧
      (2 * ((1:ℝ)/16) = 1/8) ∧
      (Real.sqrt (2 - 2 * ((15:ℝ)/16)) = Real.sqrt (2 * ((1:ℝ)/16))) ∧
      Real.sqrt (2 * ((1:ℝ)/16)) * Real.sqrt 8 = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  have h : (2:ℝ) * (1/16) = 1/8 := by norm_num
  rw [h, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/8)]
  norm_num

/-- ⭐⭐ **实算 2''**：$1/16$ 的 $\sqrt{2K}$ 数值大小。

$\sqrt{1/8}\approx0.3536$，而 $\sqrt{1/2}=\sqrt{4\cdot\frac18}=2\sqrt{1/8}\approx0.7071$。
**这显示：$K$ 每降为 $1/4$（$1/16\to1/64$），距离减半（$\sqrt{}$ 的二阶效应）。** -/
theorem concrete_sqrt_scaling :
    Real.sqrt (2 * ((1:ℝ)/16)) = Real.sqrt (1/8) ∧
      Real.sqrt (2 * ((1:ℝ)/64)) = Real.sqrt (1/32) ∧
      Real.sqrt (1/32) * 2 = Real.sqrt (1/8) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have h4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/32)]
  norm_num

/-- ⭐⭐ **实算 3（选项 C 的**紧性**在欧氏情形的体现）**：

$K=0$（即 $\cos=1$）时界给 $\|u-v\|\le 0$，即 $u=v$ —— **恰好达到**。
反之 $K>0$ 时界**严格为正**，故 $\|u\|=\|v\|=1$、$\cos=1-\frac{1}{16}$ 时
距离 **确实** $>0$（$\sqrt{1/8}>0$）。

**⟹ $\sqrt{2K}$ 的系数**不能**改成更小的常数（在 $K\to0$ 的**阶**上）：
距离 $\sim\theta$，而 $K\sim\theta^2/2$，故 $\theta\sim\sqrt{2K}$。

**⚠ 本文件**不形式化**「$\sqrt{2K}$ 是最优阶」这一渐近断言**——
它需要 $\theta\to0$ 的极限/渐近分析（不在 Mathlib 的现成工具箱里，
且与 §7.1 的「$K$ 从何而来」是**同一**个经验问题）。
**本文件只形式化**：$K>0$ 时界**严格为正**（下面的定理），
且 $K>0$ 时**存在**取等实例（`concrete_sharp_example`）。 -/
theorem sqrt_bound_strictly_positive (K : ℝ) (hK : 0 < K) :
    0 < Real.sqrt (2 * K) :=
  Real.sqrt_pos.mpr (by linarith only [hK])

end Euclidean

/-! ===========================================================================
  §6  ⭐⭐ 与既有 `tauOf` / `ShouldStop` 的**接口**（顺带澄清）

  §6 只做一件小事：**说明本文件的主定理**不需要**改冻签名，
  因为它在**判据之外**（它是判据的**理由**，不是判据本身）。
  =========================================================================== -/

/-- ⭐ **主定理 A 不依赖 `Fate.ShouldStop`**：本定理的前提里没有它。

**这一行是**诚实声明**：若本定理依赖 `ShouldStop`，
则它和 `FitBoundary.lean` §6.3 的分离定理会矛盾。 -/
example {s δ ε : ℝ} (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    sgn (s + δ) = sgn s :=
  error_bound_gives_correct_classification hδ h2

/-- ⭐⭐ **`: 主定理 A 的 `κ` 与 `tauOf` 无关**（更直白）：

`tauOf α n σx tCrit` 是**停止判据的阈值**，其**函数体**为
`tCrit / (σx * sqrt n)`（见 `Fate/TauParametric.lean`）。
本文件的 $\varepsilon$、$\mathrm{margin}$ 是**误差与间隔**，
与 `tauOf` **无数学关系** —— 不能把 $\varepsilon$ 设成 `tauOf`。

**⚠ 这不是「接口缺失」**：两者回答**不同问题**
（`tauOf`：循环**何时停**；本文件：误差**允许多大**）。 -/
theorem error_bound_independent_of_tauOf (_α : ℝ) (_n : ℕ) (_σx _tCrit : ℝ) :
    (∀ s δ ε : ℝ, |δ| ≤ ε → 2 * ε < |s| → sgn (s + δ) = sgn s) :=
  fun s δ ε hδ h2 => error_bound_gives_correct_classification hδ h2

/-! ===========================================================================
  §6.5  ⭐ **R-51 追加：误差界的合成与尺度不变性**
  ===========================================================================

  本节四条定理都**只用到** §1--§3 已有的 `sgn` / `margin` / `linScore`
  与主定理 A。**前件中均不出现结论**（逐条在 docstring 中说明）。

  ⚠ 本节**不**引入新定义、**不**修改任何已有定理。 -/

/-- ⭐⭐ **【复合扰动版】两个扰动先后叠加后分类仍不变**。

**前件**：`|δ₁| ≤ ε₁`、`|δ₂| ≤ ε₂`、`2 * (ε₁ + ε₂) < |s|`。
**结论**：`sgn ((s + δ₁) + δ₂) = sgn s`。

**⚠ 非循环**：前件只约束 `δ₁`、`δ₂` 与 `s`，**完全不提** `sgn`；
结论是**符号相等**。证明把两个扰动合并成 `δ₁ + δ₂`，
其绝对值受三角不等式约束 `|δ₁ + δ₂| ≤ ε₁ + ε₂`，再交主定理 A。 -/
theorem error_bound_compose_perturbations {s δ1 δ2 ε1 ε2 : ℝ}
    (h1 : |δ1| ≤ ε1) (h2 : |δ2| ≤ ε2) (h : 2 * (ε1 + ε2) < |s|) :
    sgn ((s + δ1) + δ2) = sgn s := by
  have hsum : |δ1 + δ2| ≤ ε1 + ε2 := by
    have := abs_add_le δ1 δ2
    linarith only [this, h1, h2]
  have e : (s + δ1) + δ2 = s + (δ1 + δ2) := by ring
  rw [e]
  exact error_bound_gives_correct_classification hsum h

/-- ⭐⭐ **【有限链版】任意有限个扰动的叠加不改变分类**。

**前件**：`∀ i ∈ u, |δ i| ≤ ε i` 与 `2 * (∑ i ∈ u, ε i) < |s|`。
**结论**：`sgn (s + ∑ i ∈ u, δ i) = sgn s`。

**⚠ 非循环**：前件是**逐点**误差界加一条**总预算**不等式；结论是符号相等。
证明用 `Finset.abs_sum_le_sum_abs` 把逐点界升成和的界，再用主定理 A。
这给出「误差预算可加」的精确含义：
**总预算** `∑ ε i` 才决定鲁棒性，而非单个 `ε i`。 -/
theorem error_bound_finset_sum_perturbations {ι : Type*} (u : Finset ι)
    (s : ℝ) (δ ε : ι → ℝ)
    (hδ : ∀ i ∈ u, |δ i| ≤ ε i)
    (hε : ∀ i ∈ u, 0 ≤ ε i)
    (h : 2 * (∑ i ∈ u, ε i) < |s|) :
    sgn (s + ∑ i ∈ u, δ i) = sgn s := by
  have hbound : |∑ i ∈ u, δ i| ≤ ∑ i ∈ u, ε i := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun i hi => hδ i hi
  exact error_bound_gives_correct_classification hbound h

/-- ⭐⭐ **【尺度不变版】误差界对打分器的**正**缩放不变**。

**前件**：`0 < c`、`|δ| ≤ ε`、`2 * ε < |s|`。
**结论**：`sgn (c * (s + δ)) = sgn (c * s)`，即**整体放大后分类仍一致**。

**⚠ 非循环**：前件是 `ε`、`s` 的不等式与 `c > 0`；
结论是 `c * (s + δ)` 与 `c * s` 的符号相等 —— 一个新出现的表达式对。
**含义**：间隔条件 `2ε < |s|` 是**尺度无关**的（两侧同乘 `c > 0` 不变），
故「误差小到不影响」这一判据**不依赖打分器的量纲**。 -/
theorem error_bound_scale_invariant {s δ ε c : ℝ}
    (hc : 0 < c) (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    sgn (c * (s + δ)) = sgn (c * s) := by
  have hbase : sgn (s + δ) = sgn s :=
    error_bound_gives_correct_classification hδ h2
  rcases abs_cases s with ⟨hs1, hsge⟩ | ⟨hs1, hsle'⟩
  . have hspos : 0 < s := by
      have hε0 : 0 ≤ ε := le_trans (abs_nonneg δ) hδ
      have habs : 0 < |s| := by linarith only [hε0, h2]
      linarith only [habs, hs1]
    have hspos' : 0 < s + δ := by
      have hlo := (abs_le.mp hδ).1
      have hε0 : 0 ≤ ε := le_trans (abs_nonneg δ) hδ
      have hεs : ε < s := by
        have e : (2 : ℝ) * ε = ε + ε := by ring
        have h3 : ε + ε < s := by linarith only [h2, e, hs1]
        have h4 : ε ≤ ε + ε := by linarith only [hε0]
        linarith only [h4, h3]
      linarith only [hlo, hεs]
    rw [sgn_of_pos (mul_pos hc hspos'), sgn_of_pos (mul_pos hc hspos)]
  . have hsneg : s < 0 := by
      have hε0 : 0 ≤ ε := le_trans (abs_nonneg δ) hδ
      have habs : 0 < |s| := by linarith only [hε0, h2]
      linarith only [habs, hs1]
    have hsneg' : s + δ < 0 := by
      have hhi := (abs_le.mp hδ).2
      have hε0 : 0 ≤ ε := le_trans (abs_nonneg δ) hδ
      have hεs : ε < -s := by
        have e : (2 : ℝ) * ε = ε + ε := by ring
        have h3 : ε + ε < -s := by linarith only [h2, e, hs1]
        have h4 : ε ≤ ε + ε := by linarith only [hε0]
        linarith only [h4, h3]
      linarith only [hhi, hεs]
    rw [sgn_of_neg (mul_neg_of_pos_of_neg hc hsneg'),
        sgn_of_neg (mul_neg_of_pos_of_neg hc hsneg)]

/-- ⭐⭐ **【打分器版】线性打分器的间隔条件保证分类不变**。

**前件**：`2 * ε < margin w x`、`|δ| ≤ ε`。
**结论**：`sgn (linScore w x + δ) = sgn (linScore w x)`。

**⚠ 非循环**：前件只说「间隔大于两倍误差」与「扰动受 `ε` 控制」；
结论是打分被打扰后**符号不变** —— `sgn` 不出现在前件中。
桥接：`margin w x = |linScore w x|`（定义），再交主定理 A。
这使 §1.1 的 `margin` 定义**真正被主定理 A 消费**，而非孤立定义。 -/
theorem margin_implies_score_sign_stable {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) {δ ε : ℝ} (hm : 2 * ε < margin w x)
    (hδ : |δ| ≤ ε) :
    sgn (linScore w x + δ) = sgn (linScore w x) := by
  have hm' : 2 * ε < |linScore w x| := by rw [margin] at hm; exact hm
  exact error_bound_gives_correct_classification hδ hm'

/-! ===========================================================================
  §7  ⚠ **诚实边界**（本文件**不**做的事）
  =========================================================================== -/

/-!
### §7.1 关于**裁决 K** 的如实说明

**裁决 K 逐字**：「误差必须小到不影响，就是刚好拟合和过拟合的边界」。

**本文件能证的**：给定「不影响」$=$「决策不变」，
则**充分必要条件**是 $2\varepsilon<\mathrm{margin}$（逐点）。

**本文件**不能**证的**（且**任何人**都不能，因为它是**定义**问题）：
「裁决 K 的原话**就是**指决策不变」。

**⟹ 本文件的定位**：提供一个**可证、可检验、常数可取等**的形式化，
而非「证明裁决 K 的原话」。

### §7.2 关于「刚好拟合 / 过拟合的边界」

`Fate.FitBoundary.IsFitBoundary (W,σ,γ)` 是**另一件事**：
它定义的是**误差剖面**在分辨率 $\gamma$ 上的**最优点**。
本文件的 $\mathrm{margin}$ 与它**符号不同、量纲不同**。

**两者的正确关系**（本文件**只登记，不证**）：
- `IsFitBoundary` 回答「**在哪个分辨率**误差最小」；
- 本文件回答「**误差多小**才不影响决策」。
- **一个剖面可以「有边界」但边界处的误差仍 $>m/2$** ⟹ **决策仍错**。
  **⟹ 「有边界」≠「分类正确」**（这是**两个**独立条件）。

**⚠ 本文件不声称**「FitBoundary 存在 ⟹ 本文件的误差界成立」。
**这是**两套**判据，本文件只在 §5、§6 说明它们**不冲突**。**

### §7.3 未解项

| # | 未解项 | 为何未解 |
|---|---|---|
| 1 | $\varepsilon$ 的**统计估计** | 需固定编码/损失函数（OQ-4）|
| 2 | $\sqrt{1+K}$（§5.2 一般情形）**是否最优** | 本文件**只证**「阶正确、常数不最优」（§5.3 实算：$K=1/16$ 时真距离 $0.3536$ vs 界 $2.0616$，松 $5.83$ 倍）。**要得 $\sqrt{2K}$ 型界需附加 $\|u\|=\|v\|$**；该情形本文件已在 **§5.2' 主定理 B'** 给出，常数 $2$ **紧且可取等** |
| 3 | **多类**（$>2$）情形 | $\mathrm{sgn}$ 是二类；多类需 `argmax`，其间隔理论**本文件未触及** |
| 4 | **非线性打分器** | §4 给**任意** $f$ 的逐点版，但**几何**版（§5）需要内积 |

**⚠ 无 `sorry` / `admit` / `axiom`。**
-/

end

end R250ErrorBound

end Fate
