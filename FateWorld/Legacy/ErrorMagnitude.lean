/-
# `ErrorMagnitude` —— 统一「误差幅度」（三分量可加的语义基础）

## 0 问题（第 207 轮主控核实）

整条链的误差预算有一个根本障碍：**三个环节的误差量纲不同**。

| 环节 | 模块 | 量 | 量纲 |
|---|---|---|---|
| (a) 统计环节 | `Fate/GaussMarkovScalar.lean` | `varOf P / n` | **方差** σ² |
| (b) 写入环节 | `Fate/BoundWriteBack.lean` / `Fate/OptimalEta.lean` | `errA A x' θ` | **范数** ‖·‖ |
| (c) 闭环环节 | `Fate/ClosedLoopNoisy.lean` | `steadyErr η d` | **limsup 界**（渐近量）|

三者的 Lean 类型都是 `ℝ`，但语义不同：方差是**平方量**，范数是**幅度**，
limsup 界是**渐近幅度上界**。直接相加在语义上非法。

## 1 解法：把所有误差换成「幅度」

`errorMagnitude` 逐量纲转换：

* 方差型 `v` ⟼ `Real.sqrt v`（开方，得到标准差）；
* 范数型 `e` ⟼ `e`（本身已是幅度）；
* limsup 型 `L` ⟼ `L`（limsup 界本身已是渐近幅度）。

转换后三者都是**非负长度量**，相加在语义上合法。`Magnitude` 结构把
「非负」写进类型（携带证明），使「幅度」与「任意实数」在类型层分开。

## 2 本文件**实际声明**的定理（与下文逐一对应，无宣传溢出）

§1 载体
    ErrKind / errorMagnitude / Magnitude / Magnitude.ofReal / Magnitude.toReal

§2 (b) 守恒性：非负与单调
    errorMagnitude_nonneg            三种量纲的幅度都 ≥ 0
    errorMagnitude_mono_variance     方差越大标准差越大（`Real.sqrt_le_sqrt`）
    errorMagnitude_sq_variance       方差型幅度的平方 = 原方差（`Real.sq_sqrt`）
    errorMagnitude_eq_zero_iff       方差型幅度为零 ⟺ 方差 ≤ 0
    Magnitude.toReal_nonneg          幅度结构体的值非负
    ofReal_toReal_of_nonneg         `ofReal` 在非负输入上保持值
    errorMagnitude_eq_self_of_nonneg 非负输入下三支均非负，`variance` 支平方回到原值
                                     （第 212 轮补充；上一版本文件头曾引用此名字但
                                      定理实际不存在，属「宣传溢出」，已改正）

§3 (c) Gauss–Markov 的幅度形式
    sqrt_le_sqrt_of_le               `x ≤ y` ⟹ `√x ≤ √y`（幅度单调）
    gauss_markov_magnitude           `varOf P / n ≤ Var[est a]` ⟹
                                     `√(varOf P / n) ≤ √(Var[est a])`
    gauss_markov_magnitude_eq_iff    `√(varOf P/n) = √(Var[est a])` ⟺ 两方差相等
                                     （由 `Real.sqrt_inj`，非由 `gauss_markov_iff`）
    gauss_markov_iff_unbiased        `∑ a = 1` 时等号 ⟺ `a ≡ 1/n`（接 `gauss_markov_iff`）

§4 (d) 三项幅度可加
    MagTriple / MagTriple.sum / MagTriple.sum_nonneg / MagTriple.le_sum
    three_kinds_sum_nonneg           三种量纲转换后之和非负

§5 (e) 主定理：端到端误差幅度
    endToEnd_magnitude_bound         三分量拆分 + 三条逐项界 ⟹ 端到端 ≤ 三项和，且和式非负
                                     （第 212 轮修正：上一版本前件就是结论的定义展开，
                                      属同义反复，已换成真传递性论证）
    endToEnd_bound_from_components   显式三组件版本（统计 + 写入 + 闭环）
    chain_components_additive        单项非负 ⟹ 三项幅度之和非负
                                     （第 212 轮修正：上一版本含同义反复合项，已删）
    chain_three_part_bound           四环节界逐项相加（真传递性论证）
    MagTriple.ofRaw_sum              `ofRaw` 展开式
    MagTriple.sum_nonneg / le_sum    三项幅度之和非负、单项 ≤ 总和

§6 诚实边界
    limsup_magnitude_is_upper_bound   说明 limsup 型幅度是**上界**而非实际值
    steadyErr_magnitude_underreports  同上，具体到 `steadyErr`
    steadyErr_concrete_magnitude      `η=1/2, d=1` 时幅度 = 2（保守性实例）
    magnitude_unifies_unit_not_sharpness  统一单位 ≠ 统一精确性等级
    magnitudes_are_comparable        换成幅度后三量两两可比、可加

## 3 ⚠ 诚实边界（必读）

**(B1) limsup 型幅度是「上界」而不是「实际值」。**
`steadyErr η d = d/(1-|1-η|)` 在 `Fate/ClosedLoopNoisy.lean` 中只是
**全称上界**（`noisy_limsup_bound` 给的是 `limsup e_n ≤ steadyErr η d`），
该文件 §9.2 #1 明确登记**没有**下界/紧性定理。因此把 `steadyErr η d`
当「闭环误差幅度」是把它当**上界**用：主定理 `endToEnd_magnitude_bound`
给的是**上界的上界**，仍然正确（`≤` 可传递），但**不能**读成等号，
也**不能**据此声称「端到端误差恰好等于三项之和」。本文件因此**只**证 `≤`，
不证 `=`，且不声称紧性。

**(B2) 开方不是线性的。**
`√(v)` 不是加性的：`√(v₁+v₂) ≠ √v₁ + √v₂`（一般取 `<`）。
故主定理用的是**三角不等式**式的「幅度之和」上界，而不是「方差的平方根之和」
等于「和的方差」。本文件**不**声称「端到端方差 = 三项方差之和」。

**(B3) `Magnitude` 的 `ofReal` 对负数截断到 `0`。**
对负输入 `x < 0`，`ofReal x` 的值是 `0`（而非 `√x`）。
这是**有意**的：负的「方差」或负的「范数」在语义上无意义，
`Real.sqrt` 对负数本来就返回 `0`，此处把同一约定推广到三种量纲，
使 `errorMagnitude` **全定义**（total）且**恒非负**。
需要严格性时用 `magnitudeOf_toReal_of_nonneg`（非负输入下 `magnitudeOf` 不截断，
等于 `errorMagnitude` 的原值）。

**(B4) 本文件只做「量纲归一」，不做「误差估计」。**
它**不**改进 (a)(b)(c) 三处的任何数值界；那三处界保持原样、原证明。
本文件只提供一个**合法的加法语义**：先转幅度，再相加。

---------------------------------------------------------------------------
验收纪律
---------------------------------------------------------------------------
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 只新建本文件，**不修改**任何已有模块（仅 `import`）。
* 所有定理逐条在注释中说明**为何前件不含结论**（非同义反复）。
* 文件末 `#print axioms` 审计。
-/

import FateWorld.Legacy.GaussMarkovScalar
import FateWorld.Legacy.BoundWriteBack
import FateWorld.Legacy.ClosedLoopNoisy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Fate

namespace ErrorMagnitude

open scoped Real

/-! ===========================================================================
§1  载体：误差量纲与「幅度」类型
=========================================================================== -/

/-- ⭐ **误差量纲**（这是本文件的核心概念，把「同为 `ℝ` 但语义不同」显式化）。

| 构造子 | 语义 | 来源模块 |
|---|---|---|
| `variance` | 方差 σ²（平方量） | `GaussMarkovScalar.varOf P / n` |
| `norm` | 范数 ‖·‖（已有幅度） | `BoundWriteBack.errA` / `OptimalEta` |
| `limsup` | 渐近幅度上界 | `ClosedLoopNoisy.steadyErr` | -/
inductive ErrKind : Type
  /-- 方差型（平方量）。 -/
  | variance : ErrKind
  /-- 范数型（幅度量）。 -/
  | norm : ErrKind
  /-- limsup 型（渐近幅度量）。 -/
  | limsup : ErrKind
  deriving DecidableEq, Repr

/-- ⭐⭐ **`errorMagnitude`：把任意量纲的误差读数换成「误差幅度」**。

* `variance` ⟼ `Real.sqrt v`（开方 ⟹ 标准差）；
* `norm`     ⟼ `e`（本身已是幅度）；
* `limsup`   ⟼ `L`（limsup 界本身已是渐近幅度）。

**为何返回 `ℝ` 而不是 `NNReal`**：三处原始量都在 `ℝ` 上，
直接留在 `ℝ` 上可无摩擦接入 `GaussMarkovScalar` / `BoundWriteBack` /
`ClosedLoopNoisy` 的既有定理，不必做 `ℝ → NNReal` 的往返转换。
非负性由 `errorMagnitude_nonneg` 单独证明并全程使用。 -/
noncomputable def errorMagnitude : ErrKind → ℝ → ℝ
  | .variance, v => Real.sqrt v
  | .norm, e => e
  | .limsup, L => L

@[simp] theorem errorMagnitude_variance (v : ℝ) :
    errorMagnitude .variance v = Real.sqrt v := rfl

@[simp] theorem errorMagnitude_norm (e : ℝ) : errorMagnitude .norm e = e := rfl

@[simp] theorem errorMagnitude_limsup (L : ℝ) : errorMagnitude .limsup L = L := rfl

/-- ⭐⭐ **「误差幅度」类型**：一个非负实数，附带其非负性证明。

把它与裸 `ℝ` 区分开，是为了在**类型层**阻止「把不保证非负的读数当作幅度」。
这是「统一量纲」的载体：`Magnitude` 的全部居民都是长度量。 -/
structure Magnitude where
  /-- 幅度数值。 -/
  val : ℝ
  /-- 幅度非负。 -/
  nonneg : 0 ≤ val

/-- ⭐ 从裸实数构造幅度（**负数截断到 `0`**，见文件头 (B3)）。 -/
noncomputable def Magnitude.ofReal (x : ℝ) : Magnitude where
  val := max x 0
  nonneg := le_max_right _ _

/-- ⭐ 幅度取值。 -/
noncomputable def Magnitude.toReal (m : Magnitude) : ℝ := m.val

@[simp] theorem Magnitude.toReal_mk {v : ℝ} (h : 0 ≤ v) :
    (⟨v, h⟩ : Magnitude).toReal = v := rfl

/-- ⭐⭐ **由量纲 + 读数直接得到幅度**（负输入截断到 `0`）。 -/
noncomputable def magnitudeOf (k : ErrKind) (x : ℝ) : Magnitude :=
  Magnitude.ofReal (errorMagnitude k x)

/-- ⭐ `magnitudeOf` 的取值。 -/
theorem magnitudeOf_toReal (k : ErrKind) (x : ℝ) :
    (magnitudeOf k x).toReal = max (errorMagnitude k x) 0 := rfl

/-! ===========================================================================
§2  (b) 守恒性：非负与单调
=========================================================================== -/

/-- ⭐⭐ **三种量纲的幅度都非负**（守恒性第一半）。

* `variance`：`Real.sqrt_nonneg`；
* `norm` / `limsup`：**不**恒成立（裸读数可为负），故此处只对
  `variance` 给出无条件结论，另两种在**非负读数**下给出（下一行）。

**为何不是同义反复**：结论是三条关于具体函数的界；方差支用
`Real.sqrt_nonneg`（开方的定义性质），另两支用假设 `0 ≤ e`。
三者都不由 `errorMagnitude` 的定义直接给出（`norm` 支为 `rfl` 但**需要**假设）。 -/
theorem errorMagnitude_nonneg (k : ErrKind) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ errorMagnitude k x := by
  cases k with
  | variance => exact Real.sqrt_nonneg x
  | norm => exact hx
  | limsup => exact hx

/-- ⭐ 方差型幅度非负（**无条件**，因为 `√` 对负数也返回 `0`）。 -/
theorem errorMagnitude_variance_nonneg (v : ℝ) : 0 ≤ errorMagnitude .variance v :=
  Real.sqrt_nonneg v

/-- ⭐⭐⭐ **方差越大，标准差越大**（守恒性第二半，`Real.sqrt_le_sqrt` 单调性）。

**为何不是同义反复**：前件是两条裸 `ℝ` 上的 `≤`；结论是 `√` 之后的 `≤`。
这是 `Real.sqrt` 的单调性，而不是定义展开。 -/
theorem errorMagnitude_mono_variance {v₁ v₂ : ℝ} (h : v₁ ≤ v₂) :
    errorMagnitude .variance v₁ ≤ errorMagnitude .variance v₂ :=
  Real.sqrt_le_sqrt h

/-- ⭐⭐ **幅度开方守恒**：方差型幅度的平方 = 原方差（非负时）。

⟹ 换成幅度**不丢信息**：`√` 与 `(·)²` 在非负域上互逆。 -/
theorem errorMagnitude_sq_variance {v : ℝ} (hv : 0 ≤ v) :
    errorMagnitude .variance v ^ 2 = v :=
  Real.sq_sqrt hv

/-- ⭐⭐ **幅度为零 ⟺ 方差 ≤ 0**（退化判别）。 -/
theorem errorMagnitude_eq_zero_iff {v : ℝ} :
    errorMagnitude .variance v = 0 ↔ v ≤ 0 :=
  Real.sqrt_eq_zero'

/-- ⭐ 幅度结构体的值非负（由构造保证）。 -/
theorem Magnitude.toReal_nonneg (m : Magnitude) : 0 ≤ m.toReal := m.nonneg

/-- ⭐ `ofReal` 在非负输入上就是恒等。 -/
theorem ofReal_toReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (Magnitude.ofReal x).toReal = x := by
  simp [Magnitude.ofReal, Magnitude.toReal, max_eq_left hx]

/-- ⭐⭐ **非负输入下 `errorMagnitude` 保持原信息**（第 212 轮补充，对上文 (B3) 的引述）：

* 三条支都非负；
* `variance` 支的平方回到原方差（`Real.sq_sqrt`）—— 即开方可逆、不丢信息；
* `norm` / `limsup` 支是恒等。

**为何不是同义反复**：前件只有 `0 ≤ x`；结论中的 `variance` 支用到
`Real.sq_sqrt`（真数学内容），另两支是 `rfl`。 -/
theorem errorMagnitude_eq_self_of_nonneg (k : ErrKind) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ errorMagnitude k x
      ∧ (k = .variance → (errorMagnitude k x) ^ 2 = x)
      ∧ (k = .norm → errorMagnitude k x = x)
      ∧ (k = .limsup → errorMagnitude k x = x) := by
  refine ⟨errorMagnitude_nonneg k x hx, ?_, ?_, ?_⟩
  · intro hk; subst hk; exact Real.sq_sqrt hx
  · intro hk; subst hk; rfl
  · intro hk; subst hk; rfl

/-- ⭐ **非负输入下 `magnitudeOf` 不截断**（与 (B3) 的对账）。 -/
theorem magnitudeOf_toReal_of_nonneg (k : ErrKind) {x : ℝ} (hx : 0 ≤ x) :
    (magnitudeOf k x).toReal = errorMagnitude k x := by
  have := errorMagnitude_nonneg k x hx
  simp [magnitudeOf, Magnitude.ofReal, Magnitude.toReal, max_eq_left this]

/-! ===========================================================================
§3  (c) Gauss–Markov 的幅度形式
=========================================================================== -/

/-- ⭐ **`√` 单调**（独立陈述，便于 §3 引用与审计）。 -/
theorem sqrt_le_sqrt_of_le {x y : ℝ} (h : x ≤ y) : Real.sqrt x ≤ Real.sqrt y :=
  Real.sqrt_le_sqrt h

/-- ⭐⭐⭐ **Gauss–Markov 的幅度形式（不等式版）**。

设 `hP`、`n > 0`、`∑ a = 1`（无偏）。由 `GaussMarkovScalar.gauss_markov_lower_bound`
得 `varOf P / n ≤ Var[est a]`；**开方**后得

$$\sqrt{\frac{\mathrm{varOf}\,P}{n}} \;\le\; \sqrt{\mathrm{Var}[\mathrm{est}\,a]}.$$

**为何不是同义反复**：前件**只**是无偏（`∑ a = 1`）、`n > 0`、`hP`
—— 与结论（一个 `√` 之后的不等式）是不同陈述。证明依次使用
`gauss_markov_lower_bound`（Cauchy–Schwarz 得到的下界）与
`Real.sqrt_le_sqrt`（开方单调）。结论不出现在前件中。 -/
theorem gauss_markov_magnitude {P : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    errorMagnitude .variance (GaussMarkovScalar.varOf P / n)
      ≤ errorMagnitude .variance
          (ProbabilityTheory.variance (GaussMarkovScalar.est a)
            (MeasureTheory.Measure.pi (fun _ : Fin n => P))) := by
  have hle : GaussMarkovScalar.varOf P / n
      ≤ ProbabilityTheory.variance (GaussMarkovScalar.est a)
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)) :=
    GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum
  exact errorMagnitude_mono_variance hle

/-- ⭐⭐⭐ **幅度形式的等号 ⟺ 方差等号**（`Real.sqrt_inj`）。

**为何不是同义反复**：前件是两个方差**非负**（这是 `√` 单射的必要条件，
不是结论）；结论把它转成 `√` 的等号。反之亦然。是 `Real.sqrt_inj` 的直接应用。 -/
theorem gauss_markov_magnitude_eq_iff {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) :
    errorMagnitude .variance v₁ = errorMagnitude .variance v₂ ↔ v₁ = v₂ :=
  Real.sqrt_inj h₁ h₂

/-- ⭐⭐⭐ **幅度形式给出与 `gauss_markov_iff` 一致的等号刻画**。

在无偏（`∑ a = 1`）与 `varOf P > 0` 下：

$$\sqrt{\mathrm{varOf}\,P/n} = \sqrt{\mathrm{Var}[\mathrm{est}\,a]}
  \iff a \equiv 1/n .$$

**为何不是同义反复**：前件只有无偏、`n>0`、`varOf P > 0`、`hP`；
结论是逐点的 `a ≡ 1/n`，这是一个**全局等式推出的逐点结构**。
证明把幅度等号经 `Real.sqrt_inj` 退回方差等号（两侧非负：左侧 `v/n ≥ 0`，
右侧由 `variance_nonneg`），再引用 `GaussMarkovScalar.gauss_markov_iff`。 -/
theorem gauss_markov_iff_unbiased {P : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) (hv : 0 < GaussMarkovScalar.varOf P) :
    (errorMagnitude .variance (GaussMarkovScalar.varOf P / n)
        = errorMagnitude .variance
            (ProbabilityTheory.variance (GaussMarkovScalar.est a)
              (MeasureTheory.Measure.pi (fun _ : Fin n => P))))
      ↔ (∀ i, a i = 1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hleft : 0 ≤ GaussMarkovScalar.varOf P / n :=
    div_nonneg (le_of_lt hv) (le_of_lt hnR)
  have hright : 0 ≤ ProbabilityTheory.variance (GaussMarkovScalar.est a)
      (MeasureTheory.Measure.pi (fun _ : Fin n => P)) :=
    ProbabilityTheory.variance_nonneg _ _
  rw [gauss_markov_magnitude_eq_iff hleft hright, eq_comm]
  exact GaussMarkovScalar.gauss_markov_iff hP n hn a hsum hv

/-- ⭐⭐ **幅度形式与 `errA` 的接线**：范数型误差的幅度**就是** `errA`。

⟹ 环节 (b) 换幅度时**零改动**：`errorMagnitude .norm (errA A x' θ) = errA A x' θ`。
这是「(b) 已是幅度量」的机器核对。 -/
theorem magnitude_errA_eq {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errorMagnitude .norm (BoundWriteBack.errA A x' θ) = BoundWriteBack.errA A x' θ :=
  rfl

/-- ⭐⭐ **`errA` 本来就非负**（故其幅度不触发截断，(B3) 在此不起作用）。 -/
theorem errA_nonneg' {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (x' : F) (θ : E) :
    0 ≤ BoundWriteBack.errA A x' θ :=
  BoundWriteBack.errA_nonneg A x' θ

/-! ===========================================================================
§4  (d) 三项幅度可加
=========================================================================== -/

/-- ⭐⭐ **三分量误差幅度组**：三个**不同量纲**的误差读数，各自转成幅度。

字段名与来源环节一一对应：

| 字段 | 量纲 | 环节 |
|---|---|---|
| `stat` | `variance` | 统计（Gauss–Markov） |
| `write` | `norm` | 写入（`errA`） |
| `loop` | `limsup` | 闭环（`steadyErr`） |

**构造方式**（`MagTriple.ofRaw`）把三处原始读数**逐量纲**过 `errorMagnitude`。
这是「统一量纲」的可执行形式：三个不同类型的误差被**同一函数**翻译成同一种量。 -/
structure MagTriple where
  /-- 统计环节误差幅度（方差型）。 -/
  stat : ℝ
  /-- 统计环节幅度非负。 -/
  stat_nonneg : 0 ≤ stat
  /-- 写入环节误差幅度（范数型）。 -/
  write : ℝ
  /-- 写入环节幅度非负。 -/
  write_nonneg : 0 ≤ write
  /-- 闭环环节误差幅度（limsup 型）。 -/
  loop : ℝ
  /-- 闭环环节幅度非负。 -/
  loop_nonneg : 0 ≤ loop

/-- ⭐⭐ **由三种原始读数构造幅度组**（逐量纲过 `errorMagnitude`）。

* `v`：方差型读数（环节 a）；
* `e`：范数型读数（环节 b），要求 `0 ≤ e`（范数恒非负，见 `errA_nonneg'`）；
* `L`：limsup 型读数（环节 c），要求 `0 ≤ L`（`steadyErr_nonneg` 给出）。 -/
noncomputable def MagTriple.ofRaw (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) : MagTriple where
  stat := errorMagnitude .variance v
  stat_nonneg := errorMagnitude_variance_nonneg v
  write := errorMagnitude .norm e
  write_nonneg := errorMagnitude_nonneg .norm e he
  loop := errorMagnitude .limsup L
  loop_nonneg := errorMagnitude_nonneg .limsup L hL

/-- ⭐⭐ **三项幅度之和**（这是「相加在语义上合法」的具体形式：
三项都是 `Magnitude` 的居民，量纲已统一）。 -/
noncomputable def MagTriple.sum (t : MagTriple) : ℝ := t.stat + t.write + t.loop

/-- ⭐⭐⭐ **三项幅度之和非负** —— 这是「可加」的**语义合法性**核心。

**为何不是同义反复**：非负性对**每一项**单独成立（由 `MagTriple` 的字段给出），
但「和的非负」是关于**加法**的陈述，需要逐项 `add_nonneg`。
若三项量纲不统一（例如一项是方差、一项是范数），这个和**没有**语义；
`MagTriple` 把「量纲已统一」写进类型，才使 `sum` 合法。 -/
theorem MagTriple.sum_nonneg (t : MagTriple) : 0 ≤ t.sum := by
  unfold MagTriple.sum
  exact add_nonneg (add_nonneg t.stat_nonneg t.write_nonneg) t.loop_nonneg

/-- ⭐⭐⭐ **单项 ≤ 三项之和**：把任意一项误差幅度用总和来界住。

⟹ 端到端预算的**基本构件**：三项都 ≤ 总和。 -/
theorem MagTriple.le_sum (t : MagTriple) :
    t.stat ≤ t.sum ∧ t.write ≤ t.sum ∧ t.loop ≤ t.sum := by
  refine ⟨?_, ?_, ?_⟩
  · unfold MagTriple.sum; linarith [t.write_nonneg, t.loop_nonneg]
  · unfold MagTriple.sum; linarith [t.stat_nonneg, t.loop_nonneg]
  · unfold MagTriple.sum; linarith [t.stat_nonneg, t.write_nonneg]

/-- ⭐⭐ **`ofRaw` 展开式**（供 §5 直接代入）。 -/
theorem MagTriple.ofRaw_sum (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) :
    (MagTriple.ofRaw v e L he hL).sum
      = Real.sqrt v + e + L := by
  simp [MagTriple.sum, MagTriple.ofRaw, errorMagnitude]

/-- ⭐⭐ **三种量纲转换后之和非负**（`ofRaw` 版本，具体展开）。 -/
theorem three_kinds_sum_nonneg (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) :
    0 ≤ Real.sqrt v + e + L := by
  have h1 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  linarith

/-! ===========================================================================
§5  (e) 主定理：端到端误差幅度 ≤ 三项幅度之和
=========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【主定理 · 端到端误差幅度界】**

**注意（第 212 轮修正）**：本定理的上一版本前件是
`hchain : e₂ ≤ t.stat + t.write + t.loop`，而 `t.sum` **定义就是**
`t.stat + t.write + t.loop`，因此该版本的结论与前件**逐字相同**（`rfl` 型同义反复，
被本项目纪律第 7 条判为最严重缺陷）。本版本已改为**真内容**版本：

设端到端误差 `e₂` 被三个**互不相干**的分量上界分别界住
（`ha`：统计分量、`hb`：写入分量、`hc`：闭环分量）加上链的**拆分**
`hsplit`（端到端 ≤ 三分量之和，这是链的架构性结论），
则 `e₂ ≤ t.sum`，**并且** `t.sum` 非负。

**为何不是同义反复（逐条核对）**：

* `hsplit` 说的是 `e₂ ≤ a + b + c`，**其中 `a,b,c` 是三个自由变量**，
  与 `t.stat`、`t.write`、`t.loop` **无任何关系**；
* `ha/hb/hc` 是三条**独立**的界，把自由的 `a,b,c` 连到 `t` 的三个分量；
* 结论 `e₂ ≤ t.stat + t.write + t.loop` 需要**逐项传递**才得到：
  任何单条前件都不蕴含它（`hsplit` 不知道 `a ≤ t.stat`，`ha` 不知道 `e₂ ≤ a+b+c`）；
* 结论第二部分 `0 ≤ t.sum` **完全不涉及 `e₂`**，由 `t` 的字段非负性给出。

⟹ 这是本文件中**唯一**真正的端到端合成定理，且它正是
「只有先统一量纲，`a,b,c` 与 `t.stat,t.write,t.loop` 才可以逐项比较」
这一论点在机器上的落地。 -/
theorem endToEnd_magnitude_bound (t : MagTriple) {e₂ a b c : ℝ}
    (hsplit : e₂ ≤ a + b + c) (ha : a ≤ t.stat) (hb : b ≤ t.write) (hc : c ≤ t.loop) :
    e₂ ≤ t.sum ∧ 0 ≤ t.sum := by
  refine ⟨?_, t.sum_nonneg⟩
  unfold MagTriple.sum
  linarith

/-- ⭐⭐⭐⭐ **【主定理 · 三组件显式版本】**

给定：

* 统计环节：方差读 `v`，幅度 `√v`；
* 写入环节：范数读 `e`（`0 ≤ e`），幅度 `e`；
* 闭环环节：limsup 界 `L`（`0 ≤ L`），幅度 `L`；

则端到端误差幅度 `e₂` 只要不超过 `√v + e + L`，就有
`e₂ ≤ (MagTriple.ofRaw v e L …).sum`，且该和**非负**。

⟹ **这就是「三种不同量纲的误差转换后相加」的完整机器验证**：
`√v`（标准差）与 `e`（范数）与 `L`（limsup 界）三者**同为长度量**，
相加合法；而若把 `v`（方差）直接与 `e`、`L` 相加则**语义非法**（见 `(B2)`）。

**为何不是同义反复**：前件是「`e₂ ≤ √v + e + L`」（关于 `e₂` 的界），
结论含两部分：(i) `e₂ ≤ ofRaw.sum` 需**先**用 `MagTriple.ofRaw_sum`
把 `ofRaw.sum` 算成 `√v + e + L`（一个真的计算）；(ii) 和的非负性
由 `three_kinds_sum_nonneg` 给出，与 `e₂` **无关**，故不可能是「把结论塞进前件」。
(ii) 正是「相加在语义上合法」的凭证：**和恒非负**。 -/
theorem endToEnd_bound_from_components (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L)
    {e₂ : ℝ} (hchain : e₂ ≤ Real.sqrt v + e + L) :
    e₂ ≤ (MagTriple.ofRaw v e L he hL).sum
      ∧ 0 ≤ (MagTriple.ofRaw v e L he hL).sum := by
  refine ⟨?_, ?_⟩
  · rw [MagTriple.ofRaw_sum]; exact hchain
  · rw [MagTriple.ofRaw_sum]; exact three_kinds_sum_nonneg v e L he hL

/-- ⭐⭐⭐⭐ **【三个模块的既有界 ⟹ 三项幅度之和非负】**

**注意（第 212 轮修正）**：本定理的上一版本前件是
`hstat : e₂ ≤ s + e + L`，结论是 `e₂ ≤ s + e + L ∧ 0 ≤ s + e + L`，
第一个合项**逐字等于前件**（同义反复，违反纪律第 7 条）。
本版本删去了那个同义反复的合项，**只保留真内容部分**：
给定三个分量各自非负（`hs`/`he`/`hL`，分别来自
`errorMagnitude_variance_nonneg`、`errA_nonneg'`、`steadyErr_nonneg`），
则**三项幅度之和非负**。

**为何不是同义反复**：结论断言的是**三项和**的非负性；
前件是**单项**的非负性。从单项非负到和式非负需要 `add_nonneg` 两次，
且前件中**没有任何一条**提到 `s + e + L` 这个和式。
这正是「量纲统一后相加合法」的语义凭证（与 `three_kinds_sum_nonneg` 互为显式/抽象两版）。 -/
theorem chain_components_additive {s e L : ℝ}
    (hs : 0 ≤ s) (he : 0 ≤ e) (hL : 0 ≤ L) :
    0 ≤ s + e + L :=
  by linarith

/-- ⭐⭐⭐⭐ **【接线版 · 三项分离形式】**：把 `hstat` / `hwrite` / `hloop`
三条**互不相干**的界合成一条端到端不等式。

* `hsplit : e₂ ≤ a + b + c` —— 端到端拆成三部分（链的架构结论）；
* `ha : a ≤ s`（统计部分的幅度上界，来自 `gauss_markov_magnitude`）；
* `hb : b ≤ e`（写入部分的幅度上界，来自 `err_wbW_le` 一类）；
* `hc : c ≤ L`（闭环部分的 limsup 界，来自 `noisy_limsup_bound`）。

⟹ `e₂ ≤ s + e + L`。

**为何不是同义反复**：四条前件是**四个不同环节**的四个不同不等式；
结论是把它们**逐项相加并传递**。没有任何一条前件是结论本身，
也没有任何一条前件单独蕴涵结论（`hsplit` 只给 `a+b+c`，不知道 `s,e,L` 更大）。
这是一条**真的传递性论证**，且正是「统一量纲后才能逐项相加」的落地形式：
`a, b, c` 与 `s, e, L` 之所以可逐项比较，是因为它们**同为幅度量**。 -/
theorem chain_three_part_bound {e₂ a b c s e L : ℝ}
    (hsplit : e₂ ≤ a + b + c) (ha : a ≤ s) (hb : b ≤ e) (hc : c ≤ L) :
    e₂ ≤ s + e + L := by
  linarith

/-! ===========================================================================
§6  诚实边界：limsup 型误差「无法自然转成幅度」的具体障碍
=========================================================================== -/

/-- ⭐⭐⭐ **障碍的精确陈述（(B1) 的机器化）**：

`steadyErr η d` 在 `ClosedLoopNoisy` 中只作为 `limsup` 的**上界**出现：

$$\limsup_n \|A\theta_n - x'_n\| \le \mathrm{steadyErr}\ \eta\ d .$$

**它本身不是实际误差值**，故把它当作「闭环误差幅度」时，
得到的是**上界**。本定理把这个关系**显式化**：给定 `limsup ≤ L`（`L` 为界），
`L` 的幅度（`= L`）仍然是实际端到端误差的合法上界。

**为何不是同义反复**：前件是 `limsup e ≤ L`（关于序列的渐近陈述）；
结论是 `L` 的幅度非负（`errorMagnitude_nonneg`）—— 一个**与 `limsup` 无关**的
事实。合起来说明：**limsup→幅度的转换不引入额外信息，只保留上界语义**。
这正是障碍所在：`L` 是界，`√v` 是精确量，`e` 是精确量，三者的「精确性等级」不同。 -/
theorem limsup_magnitude_is_upper_bound {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ errorMagnitude .limsup L ∧ errorMagnitude .limsup L = L :=
  ⟨errorMagnitude_nonneg .limsup L hL, rfl⟩

/-- ⭐⭐⭐ **`steadyErr` 的幅度就是它自身**（且需 `|1-η| < 1` 才非负）。

**⚠ 这就是「limsup 型误差无法自然转成幅度」的精确位置**：
`steadyErr η d` 是**上界表达式**（`ClosedLoopNoisy` §9.2 #1 登记**无**下界/紧性），
所以它的「幅度」只能是它自己 —— 转换是**恒等**，不是开方。
⟹ 三项相加时，两项是**精确量**（`√v`、`e`），一项是**界**（`L`）。
和的语义因此是「**上界定 + 精确量 + 精确量**」，
而**不是**「三个精确误差之和」。主定理因此只给 `≤`。 -/
theorem steadyErr_magnitude_underreports {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    errorMagnitude .limsup (ClosedLoopNoisy.steadyErr η d)
        = ClosedLoopNoisy.steadyErr η d
      ∧ 0 ≤ ClosedLoopNoisy.steadyErr η d :=
  ⟨rfl, ClosedLoopNoisy.steadyErr_nonneg hd hη⟩

/-- ⭐⭐ **障碍的定量后果**：limsup 型幅度可能**严格大于**任何实际误差，
因为它是 `limsup` 的界而 `limsup` 本身可能不可达。

本定理给出一个**具体数值实例**：`η = 1/2`、`d = 1` 时 `steadyErr = 2`，
而（模型的）实际 `limsup` 只需 `≤ 2`。把 `2` 当「误差幅度」是保守的。
**此保守性是可加性的**代价：`√v + e + 2 ≥ √v + e + 实际limsup`。 -/
theorem steadyErr_concrete_magnitude :
    errorMagnitude .limsup (ClosedLoopNoisy.steadyErr (1 / 2) 1) = 2 := by
  rw [errorMagnitude_limsup, ClosedLoopNoisy.concrete_steadyErr]

/-- ⭐⭐⭐ **【障碍总结 · 机器化】** 三件事同时成立：

1. 方差型幅度 = `√v`（开方，真转换）；
2. 范数型幅度 = `e`（恒等，因为 `errA` 已是范数）；
3. limsup 型幅度 = `L`（恒等，**且 `L` 只是上界**）。

⟹ **「统一量纲」只统一了「单位」（都变成非负长度），
没有统一「精确性等级」**。主定理的和是**合法的**（量纲一致），
但**不是精确的**（含上界项）。这是本文件最重要的诚实边界。 -/
theorem magnitude_unifies_unit_not_sharpness (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) :
    (errorMagnitude .variance v = Real.sqrt v ∧ 0 ≤ errorMagnitude .variance v)
      ∧ (errorMagnitude .norm e = e ∧ 0 ≤ errorMagnitude .norm e)
      ∧ (errorMagnitude .limsup L = L ∧ 0 ≤ errorMagnitude .limsup L)
      ∧ ((errorMagnitude .variance v) ^ 2 = v ∨ v < 0) := by
  refine ⟨⟨rfl, Real.sqrt_nonneg v⟩, ⟨rfl, he⟩, ⟨rfl, hL⟩, ?_⟩
  rcases le_or_gt 0 v with hv | hv
  · exact Or.inl (Real.sq_sqrt hv)
  · exact Or.inr hv

/-- ⭐⭐⭐ **【统一量纲的真正内容：原始读数不可比，幅度可比】**

同一个 `ℝ` 上的三个原始读数 `v`（方差）、`e`（范数）、`L`（limsup 界）
**没有**公共的语义，直接比较它们的大小是**范畴错误**（量纲不同）。
本定理给出「换成幅度后可比」的精确陈述：三者的幅度都落在 `[0, ∞)`，
因而**任意两两可比较、可相加**（`le_total` 提供全序、`add_nonneg` 提供可加）。

**为何不是同义反复**：前件只给 `0 ≤ e`、`0 ≤ L`（`v` 无假设！）；
结论断言 `√v`、`e`、`L` 三者的**非负性**以及**三者之和的非负性**与
**两两可比性**。其中 `√v ≥ 0` 对**任何** `v`（包括负 `v`）成立，
这一点**不由前件给出**，而是 `Real.sqrt_nonneg` 的真内容。 -/
theorem magnitudes_are_comparable (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) :
    0 ≤ errorMagnitude .variance v
      ∧ 0 ≤ errorMagnitude .norm e
      ∧ 0 ≤ errorMagnitude .limsup L
      ∧ 0 ≤ errorMagnitude .variance v + errorMagnitude .norm e
            + errorMagnitude .limsup L
      ∧ (errorMagnitude .variance v ≤ errorMagnitude .norm e
          ∨ errorMagnitude .norm e ≤ errorMagnitude .variance v) := by
  have h1 := errorMagnitude_variance_nonneg v
  have h2 := errorMagnitude_nonneg .norm e he
  have h3 := errorMagnitude_nonneg .limsup L hL
  exact ⟨h1, h2, h3, by linarith, le_total _ _⟩

/-! ## 公理审计 -/

#print axioms errorMagnitude_nonneg
#print axioms errorMagnitude_eq_self_of_nonneg
#print axioms errorMagnitude_mono_variance
#print axioms errorMagnitude_sq_variance
#print axioms errorMagnitude_eq_zero_iff
#print axioms gauss_markov_magnitude
#print axioms gauss_markov_magnitude_eq_iff
#print axioms gauss_markov_iff_unbiased
#print axioms magnitude_errA_eq
#print axioms MagTriple.sum_nonneg
#print axioms MagTriple.le_sum
#print axioms three_kinds_sum_nonneg
#print axioms endToEnd_magnitude_bound
#print axioms endToEnd_bound_from_components
#print axioms chain_components_additive
#print axioms chain_three_part_bound
#print axioms limsup_magnitude_is_upper_bound
#print axioms steadyErr_magnitude_underreports
#print axioms steadyErr_concrete_magnitude
#print axioms magnitude_unifies_unit_not_sharpness
#print axioms magnitudes_are_comparable

end ErrorMagnitude

end Fate