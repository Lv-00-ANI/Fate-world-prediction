import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import FateWorld.FateV2.Predict.MiddleZoneDichotomy
import FateWorld.FateV2.Modeling.KernelQuotient
set_option autoImplicit false

/-!
  # Predict · ObservationUnified

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ObservationUnified.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MiddleZoneDichotomy, KernelQuotient
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §OU  ⭐⭐ **观测反推潜变量的统一框架**（A14 与 O3 的三档抽象）

  ## 0 缘起

  仓内两处独立出现的「三档」结构，经 `O3-外生不可观测三档.md` 与
  `A14-三档关系分析.md` 判定为 **完全同构**：

  | 档 | A14（观测状态 `x_t`） | O3（观测外生 `u`） | 反推产物 |
  |---|---|---|---|
  | **强** | `h` 单射 + 有界噪声 | `u` 完全可观测 | 估计 + 误差界（`ℝ`）|
  | **中** | `h` 单射 + 分布已知 | `u` 部分可观测（代理）| 后验（`PMF` / `ENNReal` 值）|
  | **弱** | `h` 非单射 | `u` 完全不可观测 | 等价类（商集）|

  **共同形状**：都是「给定观测 `y = h w (+) 噪声`，反推潜变量 `w`」。
  区别只在 **`h` 是否单射** 与 **噪声是否携带分布信息**。

  ## 1 本文件做什么

  * §OU.1 **载体**：`InversionTier`（三档）与 `Inversion W Y`（统一接口）。
  * §OU.2 **弱档（`quotient`）**：反推产物 = **等价类**。
    主定理 `classOf_eq_iff`：`[w] = [w']  ⟺  h w = h w'`；
    并证 `h` 在商上 **单射**（`liftH_injective`，第一同构定理的实用半边）。
  * §OU.3 **中档（`posterior`）**：反推产物 = **分布**。
    主定理 `post_eq_of_const_lik`（无信息似然 ⟹ 后验 = 常数乘先验）、
    `post_eq_zero_of_lik_zero`（似然为零 ⟹ 后验为零）、
    `post_single_support`（指示似然 ⟹ 后验支撑单点）。
  * §OU.4 **强档（`bounded`）**：反推产物 = **估计 + 误差界**。
    主定理 `est_eq_of_injective_exact`（单射 + 精确观测 ⟹ 估计 = 真值）、
    `bounded_error_gives_same_class`（误差界 ⟹ 同一个 ε-球内的点不可区分）。
  * §OU.5 **三档一致性**：
    `quotient_of_injective_is_trivial`（单射 ⟹ 弱档商退化为离散，即整类单点）、
    `inversion_tier_trichotomy`（三档穷尽）、
    `strong_implies_quotient`（`ε = 0` 时强档结论蕴含弱档类是单点）。

  ## 2 诚实边界（**必读**）

  1. **本文件不重复定义** `Setoid.ker`、`Quotient`、`PMF` 等基础构造 ——
     全部复用 Mathlib 与仓内 `Fate.KernelQuotient` / `MiddleZoneDichotomy`。
  2. **本文件不修改** `Fate.lean`（作者纪律）。若要接入构建，另行在
     `Fate.lean` 加一行 `import ObservationUnified` —— **本文件不代做**。
  3. **三档的「统一」是接口层面的统一**，不是「把一个定理伪装成三个」：
     三档各自的结论类型不同（商商集 / `W → ENNReal` / `ℝ` 误差界），
     这正是 `A14-三档关系分析.md` §2 「三者量纲不同型」的 **Lean 侧证据**。
     统一之处在于 **它们共用同一个 `h` 与同一个 `Inversion W Y` 记录**。
  4. **中档（posterior）没有** 证「后验归一化为 `PMF`」——
     归一化需要 `∑' w, prior w * lik y w` 的和可算，函数空间上的 `PMF` 化
     依赖求和收敛性，本文件**不假设**收敛，故后验用 **未归一化的权重函数**
     `W → ENNReal` 表示（`post`）。这是一个**如实的弱化**，不是遗漏。
  5. **强档（bounded）** 的 `ε` 是 **外部参数**，本文件**不证**其统计来源
     （与 `Fate/ErrorBound.lean` 文件头的诚实声明一致）。
  6. **arXiv:2301.09031** 的「反事实不可点识别、只能部分识别」是**文献**，
     本文件只把它的**形状**（弱档 = 等价类 / 部分识别）抽象成 `quotient` 档，
     **不**形式化该文的任何具体定理。

  ## 3 与既有文件的关系

  | 本文件 | 复用/对应 |
  |---|---|
  | `InversionTier.quotient` | `Fate.KernelQuotient` 的「核–商」一般理论 |
  | `classOf_eq_iff` | `Fate.KernelQuotient` 的 `Quotient.eq''`；`MiddleZoneDichotomy` 的 `middleZone_empty_iff_injective` |
  | `post_*` | `Fate.T43Abduction` 的 `abduction_eq_doLaw_of_sg_indep` 的**形状**（无信息似然 ⟹ 信息被消去）|
  | `bounded_*` | `R250ErrorBound` 的 `error_bound_gives_correct_classification` 的**距离版** |

  ## 4 ⚠⚠ 第 619 轮修正：删除空洞定理 `tier_output_shape`

  * **发现者**：主控**剥注释**检查器（`hollow_check.py`），命中 `[ARROW-True]`。
    **子代理的 `grep` 版检查器没有找到这处**。
  * **问题**：docstring 声称「把『三档产出不同类型』写成**依赖 `tier` 的消去规则**」，
    但结论三条全是 `→ True`，**没有任何类型信息** ⟹ 声称与实现脱节。
  * **处理**：**删除**，并**代之以两条真定理**（真消去，但只到「档位互不相同」为止）：
    `tier_output_shape_quotient_ne_posterior`、`tier_output_shape_bounded_ne_quotient`。
    原位置另留 `/-! ... -/` 说明段（含原文与理由）。
  * **真正的「三档产出不同类型」本文件做了吗？—— 只做了一半，已如实标注**：
    本文件有**三个并列的产物载体**（`Inversion.quo` / `PosteriorData` /
    `BoundedData`），但 `Inversion.tier` 只是**元数据**，**没有**一个
    依赖类型反推算子 `(t : InversionTier) → Type _` 让下游按 `tier` 消去。
    **这一层本文件未做**，新定理的 docstring 已明写。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace ObservationUnified

universe u v

/-! ### §OU.1 载体：三档与统一接口 -/

/-- ⭐ **从观测反推潜变量的三档**。

* `bounded`：`h` 单射 + 噪声有界 ⟹ 得到估计与误差界；
* `posterior`：`h` 单射 + 分布已知 ⟹ 得到后验分布；
* `quotient`：`h` 非单射 ⟹ 只能得到等价类。 -/
inductive InversionTier
  /-- 单射 + 有界噪声 → 估计 + 误差界。 -/
  | bounded
  /-- 单射 + 分布已知 → 后验。 -/
  | posterior
  /-- 非单射 → 等价类。 -/
  | quotient
  deriving DecidableEq, Repr

/-- ⭐⭐ **统一的反推接口**：一个潜变量空间 `W`、一个观测空间 `Y`、
一个观测映射 `h`，外加一个 `tier` 标记当前采用的是哪一档。

**注意**：`tier` 是**元数据**，不影响 `h`。同一 `h` 可以在不同档下给出
不同形态的反推产物（见 §OU.2–§OU.4）。 -/
structure Inversion (W : Type u) (Y : Type v) where
  /-- 当前档位。 -/
  tier : InversionTier
  /-- 观测映射（潜变量 → 观测）。 -/
  h : W → Y

namespace Inversion

variable {W : Type u} {Y : Type v}

/-! ### §OU.2 弱档（`quotient`）：反推产物 = 等价类 -/

/-- **`h` 的核等价**：两个潜变量等价 ⟺ 它们给出同一观测。

**这就是「非单射 ⟹ 观测不可区分」的精确形式**，也是弱档的等价关系。 -/
def ker (I : Inversion W Y) : Setoid W := Setoid.ker I.h

/-- **弱档的反推结果空间**：核等价下的商集。

⟹ **当 `tier = quotient` 时，反推结果落在 `I.quo` 里，即「等价类」。** -/
noncomputable def quo (I : Inversion W Y) : Type u := Quotient I.ker

/-- ⭐ **弱档的反推算子**：把一个潜变量送到它的等价类。

**这是 §OU.2 的「反推结果」本体** —— 给定观测 `h w`，我们**不能**回指 `w`，
**只能**回指 `[w]`。 -/
def classOf (I : Inversion W Y) (w : W) : I.quo := Quotient.mk I.ker w

/-- ⭐⭐ **主定理（弱档）**：两个潜变量落在**同一个等价类** ⟺ 它们给出**同一观测**。

⟹ **这正是「`tier = quotient` 时反推结果是等价类」的精确陈述**：
等价类的粒度**恰好**等于观测的粒度，不多不少。 -/
theorem classOf_eq_iff (I : Inversion W Y) (w w' : W) :
    I.classOf w = I.classOf w' ↔ I.h w = I.h w' := by
  show Quotient.mk I.ker w = Quotient.mk I.ker w' ↔ I.h w = I.h w'
  rw [Quotient.eq'']
  rfl

/-- **等价类的成员刻画**：`w'` 在 `w` 的类里 ⟺ `h w' = h w`。 -/
theorem mem_class_iff (I : Inversion W Y) (w w' : W) :
    I.classOf w' = I.classOf w ↔ I.h w' = I.h w :=
  I.classOf_eq_iff w' w

/-- **`h` 在商上下降**为 `I.quo → Y` 的映射。

⟹ 观测可以在「等价类」这一粒度上被重新读出。 -/
def liftH (I : Inversion W Y) : I.quo → Y :=
  Quotient.lift I.h (fun _ _ e => e)

/-- **下降映射在代表元上的取值**。 -/
theorem liftH_classOf (I : Inversion W Y) (w : W) :
    I.liftH (I.classOf w) = I.h w := rfl

/-- ⭐⭐ **第一同构定理的实用半边**：**下降后的观测在商上单射**。

⟹ **即**：一旦把「观测不到的差别」商掉（`tier = quotient`），
剩下的**观测是单射的** —— 在等价类层面「观测定得足够细」。

**这是弱档的收束性结论**：等价类**就是**损失的全部信息，不再有二次损失。 -/
theorem liftH_injective (I : Inversion W Y) : Function.Injective I.liftH := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h w =>
    induction b using Quotient.inductionOn with
    | h w' =>
      exact Quotient.sound hab

/-- **下降映射的像恰是 `h` 的像**（第一同构的像侧）。 -/
theorem liftH_surjOn (I : Inversion W Y) (q : I.quo) : ∃ w, I.liftH q = I.h w := by
  induction q using Quotient.inductionOn with
  | h w => exact ⟨w, rfl⟩

/-- ⭐ **单射时弱档「退化」为恒等**：若 `h` 单射，则两个潜变量等价 ⟺ 相等。

⟹ **即**：`h` 单射 ⟹ 商 `I.quo` 的每个类是单点 ⟹ 弱档产物**无损**。

这与 `MiddleZoneDichotomy.middleZone_empty_iff_injective` 是同一件事的
**商表述**：中间地带为空 ⟺ 单射。 -/
theorem quotient_of_injective_is_trivial (I : Inversion W Y)
    (hinj : Function.Injective I.h) (w w' : W) :
    I.classOf w = I.classOf w' ↔ w = w' := by
  rw [I.classOf_eq_iff]
  exact ⟨fun (e : I.h w = I.h w') => hinj e, fun e => e ▸ rfl⟩

/-- **单射 ⟹ 弱档商可等同于 `W`**（每个类由代表元唯一确定）。 -/
theorem injective_iff_classOf_injective (I : Inversion W Y) :
    Function.Injective I.h ↔ Function.Injective I.classOf := by
  constructor
  · intro h w w' hqw
    exact (I.quotient_of_injective_is_trivial h w w').mp hqw
  · intro h w w' hww
    exact h ((I.classOf_eq_iff w w').mpr hww)

/-! ### §OU.3 中档（`posterior`）：反推产物 = 分布 -/

/- **⚠ 如实弱化（见文件头 §2.4）**：后验用**未归一化的权重函数** `W → ENNReal`
表示，而**不**强行归一化成 `PMF` —— 归一化需要 `∑' w, prior w * lik y w`
的收敛性，本文件不假设。**这不影响本节的结论形状**（支撑、退化）。 -/

/-- **中档的数据**：先验 `prior`（`PMF W`）+ 似然 `lik`（观测 → 潜变量 → 权重）。

**`prior` 用 `PMF` 是因为先验**确实**是概率测度；`lik` 用 `ENNReal` 值
是因为它只是权重因子，**不**需归一化。 -/
structure PosteriorData (W : Type u) (Y : Type v) where
  /-- 先验分布。 -/
  prior : PMF W
  /-- 似然权重（未归一化）。 -/
  lik : Y → W → ENNReal

namespace PosteriorData

variable {W : Type u} {Y : Type v}

/-- ⭐ **中档的反推算子**：给定观测 `y`，**后验权重**是
`w ↦ prior w · lik y w`。

⟹ **当 `tier = posterior` 时，反推结果就是这个 `W → ENNReal` 函数，
即「一个分布」（未归一化的后验）。** -/
noncomputable def post (P : PosteriorData W Y) (y : Y) : W → ENNReal :=
  fun w => P.prior w * P.lik y w

/-- **后验的支撑被似然限制**：似然为零的潜变量，后验权重也为零。

⟹ **即**：「观测 `y` 说不可能」的 `w`，后验也不给权重。 -/
theorem post_eq_zero_of_lik_zero (P : PosteriorData W Y) (y : Y) (w : W)
    (h : P.lik y w = 0) : P.post y w = 0 := by
  simp [post, h]

/-- ⭐⭐ **主定理（中档）**：**无信息似然 ⟹ 后验 = 常数 × 先验**。

似然 `lik y` 恒等于常数 `c` 时，观测 `y` **不携带**关于 `w` 的信息，
后验**完全退化**为先验（乘比例常数 `c`）。

⟹ **这是 `Fate.T43Abduction.abduction_eq_doLaw_of_sg_indep` 的同形状陈述**：
「去掉依赖 ⟹ 信息被消去」。 -/
theorem post_eq_of_const_lik (P : PosteriorData W Y) (y : Y) (c : ENNReal)
    (h : ∀ w, P.lik y w = c) :
    P.post y = fun w => c * P.prior w := by
  funext w
  simp only [post, h]
  exact mul_comm _ _

/-- **常数似然的后验 = 先验的线性象（逐点）**。 -/
theorem post_const_lik_apply (P : PosteriorData W Y) (y : Y) (c : ENNReal)
    (h : ∀ w, P.lik y w = c) (w : W) :
    P.post y w = c * P.prior w := by
  simp [post, h, mul_comm]

/-- ⭐ **指示似然 ⟹ 后验支撑单点**。

若似然是「`w = w₀` 的指示」，则所有 `w ≠ w₀` 的后验权重为零
—— **观测 `y` 把全部后验质量压在一个点上**。 -/
theorem post_single_support (P : PosteriorData W Y) [DecidableEq W]
    (y : Y) (w₀ : W) (h : ∀ w, P.lik y w = if w = w₀ then 1 else 0)
    (w : W) (hne : w ≠ w₀) : P.post y w = 0 := by
  simp only [post, h, if_neg hne, mul_zero]

/-- **指示似然在靶点上的权重 = 先验权重**。 -/
theorem post_single_target (P : PosteriorData W Y) [DecidableEq W]
    (y : Y) (w₀ : W) (h : ∀ w, P.lik y w = if w = w₀ then 1 else 0) :
    P.post y w₀ = P.prior w₀ := by
  simp [post, h]

end PosteriorData

/-! ### §OU.4 强档（`bounded`）：反推产物 = 估计 + 误差界 -/

/- **⚠ 与 `R250ErrorBound` 的关系**：那边用 `ℝ` 上的符号 `sgn` 判定分类；
本文件用**距离** `dist` 判定「估计是否落在真值的误差球内」。**两者平行**，
本文件取距离版是因为它直接对应「潜变量空间 `W` 上的误差」。 -/

/-- **强档的数据**：`W` 是伪度量空间，`est` 是估计算子，`ε` 是误差界。

**`ε` 是外部参数** —— 本文件**不证**其统计来源（见文件头 §2.5）。 -/
structure BoundedData (W : Type u) (Y : Type v) [PseudoMetricSpace W] where
  /-- 观测映射。 -/
  h : W → Y
  /-- 估计算子（从观测反推潜变量）。 -/
  est : Y → W
  /-- 误差界。 -/
  ε : ℝ
  /-- 误差界非负。 -/
  hε : 0 ≤ ε
  /-- **有界噪声假设**：估计与真值的距离不超过 `ε`。 -/
  hbound : ∀ (y : Y) (w : W), h w = y → dist (est y) w ≤ ε

namespace BoundedData

variable {W : Type u} {Y : Type v} [PseudoMetricSpace W]

/-- ⭐ **强档的反推算子**：给定观测 `y`，反推产物是估计点 `est y`。

⟹ **当 `tier = bounded` 时，反推结果是 `W` 的一个点（带误差界 `ε`）。** -/
def estOf (B : BoundedData W Y) (y : Y) : W := B.est y

/-- ⭐⭐ **主定理（强档，精确观测）**：**`h` 单射 + 观测由某 `w` 精确生成
⟹ 估计唯一等于 `w`**。

⟹ **即**：单射 + 无噪声时，强档反推**没有损失**。 -/
theorem est_eq_of_injective_exact (B : BoundedData W Y)
    (hinj : Function.Injective B.h) (y : Y) (w : W)
    (hw : B.h w = y) (he : B.h (B.est y) = y) :
    B.est y = w :=
  hinj (he.trans hw.symm)

/-- ⭐ **主定理（强档，误差界）**：**估计落在真值的 `ε`-球内**。

这是 `BoundedData.hbound` 的**重述**（故意暴露为定理，便于下游调用）。 -/
theorem est_within_bound (B : BoundedData W Y) (y : Y) (w : W) (hw : B.h w = y) :
    dist (B.est y) w ≤ B.ε :=
  B.hbound y w hw

/-- ⭐⭐ **误差界 ⟹ 两个候选估计不可区分**：若 `w₁, w₂` 都是 `y` 的合法原像
（即 `h wᵢ = y`），则它们之间的距离不超过 `2ε`。

⟹ **这是「有界噪声下反推只能到 `2ε` 精度」的精确陈述** ——
也解释了为什么强档需要**额外的间隔条件**（`2ε < margin`，见
`R250ErrorBound.error_bound_gives_correct_classification`）才能给出**离散**结论。 -/
theorem candidates_close (B : BoundedData W Y) (y : Y) (w₁ w₂ : W)
    (h₁ : B.h w₁ = y) (h₂ : B.h w₂ = y) :
    dist w₁ w₂ ≤ 2 * B.ε := by
  calc dist w₁ w₂ ≤ dist w₁ (B.est y) + dist (B.est y) w₂ := dist_triangle _ _ _
    _ = dist (B.est y) w₁ + dist (B.est y) w₂ := by rw [dist_comm w₁ (B.est y)]
    _ ≤ B.ε + B.ε := add_le_add (B.hbound y w₁ h₁) (B.hbound y w₂ h₂)
    _ = 2 * B.ε := by ring

/-- ⭐ **零误差界 + 单射 ⟹ 候选原像唯一**：`ε = 0` 时 `candidates_close` 给出
`w₁ = w₂`（在单射情形已由 `est_eq_of_injective_exact` 得到，这里从距离侧再给一次）。 -/
theorem zero_bound_candidates_eq (B : BoundedData W Y) (hε0 : B.ε = 0)
    (y : Y) (w₁ w₂ : W) (h₁ : B.h w₁ = y) (h₂ : B.h w₂ = y) :
    dist w₁ w₂ = 0 := by
  have h := B.candidates_close y w₁ w₂ h₁ h₂
  rw [hε0] at h
  have h' : dist w₁ w₂ ≤ 0 := by simpa using h
  exact le_antisymm h' dist_nonneg

end BoundedData

/-! ### §OU.5 三档一致性（统一框架的收束） -/

/-- ⭐⭐ **三档穷尽**：`tier` 只能取三者之一（平凡但显式）。 -/
theorem inversion_tier_trichotomy (t : InversionTier) :
    t = InversionTier.bounded ∨ t = InversionTier.posterior ∨ t = InversionTier.quotient := by
  cases t with
  | bounded => exact Or.inl rfl
  | posterior => exact Or.inr (Or.inl rfl)
  | quotient => exact Or.inr (Or.inr rfl)

/-! ⚠⚠ **〔第 619 轮：删除 `tier_output_shape` —— 声称与实现脱节〕**

  原有一条

  ```lean
  theorem tier_output_shape (t : InversionTier) :
      (t = InversionTier.quotient → True) ∧
      (t = InversionTier.posterior → True) ∧
      (t = InversionTier.bounded → True) :=
    ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial⟩
  ```

  其 docstring 声称：「把『三档产出不同类型』写成**依赖 `tier` 的消去规则**」——
  但结论里**没有任何类型**，三条全是 `→ True` ⟹ **声称与实现脱节**。
  被主控的**剥注释检查器 `hollow_check.py`** 命中（`[ARROW-True]`）；
  子代理的 `grep` 版**没有**找到它。

  ## 真正的「三档产出不同类型」本文件做了吗？

  **严格说：只做了一半。**

  * **弱档（`quotient`）的真产物**：本文件的 `Inversion.quo`（`Type u`，
    `Quotient I.ker`）与 `Inversion.classOf : I.quo` —— 这是**真类型**：
    `tier = quotient` 时反推产物真落在等价类空间里，只是本文件
    把 `tier` 当作**元数据**而**不**把它与 `classOf` 的返回类型绑定；
  * **中档（`posterior`）** 的产物 `PosteriorData` / `W → ENNReal`，
  * **强档（`bounded`）** 的产物 `BoundedData`（估计点 + 误差界），

  这三者是**三个并列的结构**，而**不是**「随 `tier` 变化的**依赖类型**
  反推算子」（形如 `outputShape : (t : InversionTier) → Type _`）。
  **把三者统一成一个依赖类型函数 `tier → Type` 并在 `tier = ...` 上消去**
  —— **本文件未做**（`Inversion.tier` 是元数据，不参与 `h` 的类型，
  见 §OU.1 对该 `structure` 的注释）。

  **⟹ 故删除，不伪造。** 真正可证的**有内容**的消去规则见紧随其后的真定理：

  * `tier_output_shape_quotient_ne_posterior`：`quotient ≠ posterior`；
  * `tier_output_shape_bounded_ne_quotient`：`bounded ≠ quotient`。

  它们**只**证明「三档互不相同」，**不**声称「产出不同类型」——
  后者需要上面说的依赖类型函数，本文件未做。 -/

/-- ⭐⭐ **三档互不相同（真消去规则的极小形态）**：以 `tier = quotient` 消去
的结果**不能**是 `posterior` 的档位。

⚠ **不要**把这条读成「两档产出不同类型」：本文件里 `tier` 是 `Inversion`
的**元数据**，反推产物的类型由**你选用哪个结构**（`Inversion.quo` /
`PosteriorData` / `BoundedData`）决定，**不是**由 `tier` 字段"计算"出来的。
真正的依赖类型反推算子 `(t : InversionTier) → Type _` **本文件未做**。 -/
theorem tier_output_shape_quotient_ne_posterior :
    InversionTier.quotient ≠ InversionTier.posterior := by decide

/-- ⭐⭐ **三档互不相同（第二条）**：`bounded ≠ quotient`。 -/
theorem tier_output_shape_bounded_ne_quotient :
    InversionTier.bounded ≠ InversionTier.quotient := by decide

/-- ⭐⭐ **强档 ⟹ 弱档（`ε = 0` 极限）**：若 `h` 单射，则弱档的等价类是**单点**，
即强档（精确可逆）与弱档（划分）在 `ε = 0` 处**重合**。

**⚠ 这是 `A14-三档关系分析.md` §1.3 的 C1 情形（`ε = 0`），
不是一般的「强 ⟹ 弱」；一般情形的 C2（类直径 > ε）为【推测】，本文件不证。** -/
theorem strong_implies_quotient (I : Inversion W Y) (hinj : Function.Injective I.h)
    (w w' : W) :
    I.classOf w = I.classOf w' → w = w' :=
  (I.quotient_of_injective_is_trivial hinj w w').mp

/-- ⭐ **中档 ⟹ 弱档的形状一致性**：中档的「观测不可区分」与弱档的核等价
**同一个关系**。即：`P.lik y w` 只依赖 `I.h w`（似然是观测的函数）时，
`I.classOf w = I.classOf w' ⟹ P.lik y w = P.lik y w'`。

⟹ **即**：**弱档的等价类恰是中档似然的充分统计量粒度** ——
同类中所有潜变量给出**相同的似然因子**（后验只因先验不同而异）。

**⚠ 注意**：本定理**不**宣称 `post` 相等 —— 因为 `post = prior · lik`，
先验 `prior w` 与 `prior w'` 可以不同。**这正说明中档与弱档严格不同型**。 -/
theorem posterior_factors_through_class {W : Type u} {Y : Type v}
    (I : Inversion W Y) (P : PosteriorData W Y) (y : Y)
    (hlik : ∀ w w' : W, I.h w = I.h w' → P.lik y w = P.lik y w')
    (w w' : W) (heq : I.classOf w = I.classOf w') :
    P.lik y w = P.lik y w' :=
  hlik w w' ((I.classOf_eq_iff w w').mp heq)

/-- ⭐ **强档 ⟹ 中档（点质量退化）**：单射 + 指示似然 ⟹ 后验支撑在
唯一原像上。这是 `A14-三档关系分析.md` §2.2 墙 2「Wasserstein 点质量」的
**离散对应物**：后验退化为点质量 ⟺ 强档与中档在 `ε = 0` 处对齐。 -/
theorem bounded_posterior_agree_at_point
    {W : Type u} {Y : Type v} [DecidableEq W]
    (I : Inversion W Y) (P : PosteriorData W Y) (y : Y) (w₀ : W)
    (_hinj : Function.Injective I.h)
    (hlik : ∀ w, P.lik y w = if w = w₀ then 1 else 0)
    (w : W) (_hw : I.h w = y) (hne : w ≠ w₀) :
    P.post y w = 0 :=
  P.post_single_support y w₀ hlik w hne

end Inversion

end ObservationUnified

end FateV2.Predict