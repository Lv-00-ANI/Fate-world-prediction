/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.OptimalityPattern`
任务：**把「界紧唯一性」抽象成通用模式**，并证明它同时覆盖
`Fate.GaussMarkovScalar`（最优权重 `a ≡ 1/n`）与
`Fate.OptimalEta`（最优步长 `η = 1`）两个模块。

===========================================================================
本文件**实际声明**的定理/定义（与下文逐一对应，无宣传溢出）
===========================================================================

§1 结构定义
    OptimalityPattern                    「界紧 + 取到 + 唯一」三元组（结构体）

§2 模式定理（抽象层，**不依赖任何具体模块**）
    OptimalityPattern.ext                五个字段相等 ⟹ 模式相等
    OptimalityPattern.unique_opt         `f p = lb ⟹ p = p_star`（最优点唯一）
    OptimalityPattern.opt_le             对一切 `p`，`f p_star ≤ f p`
    OptimalityPattern.opt_eq_lb          `f p_star = lb`
    OptimalityPattern.value_unique       `f p = lb ⟹ f p = f p_star`（**最优值唯一**）
    OptimalityPattern.opt_value_unique   最优点 ∧ 最优值 同时唯一（合取包装）
    OptimalityPattern.lb_unique          同一 `f` 同一 `p_star` ⟹ 下界唯一
    OptimalityPattern.star_unique        同一 `f` 同一下界 ⟹ 最优点唯一
    OptimalityPattern.of_bound_eq        组装器
    OptimalityPattern.gap_zero_iff       `f p - lb = 0 ↔ p = p_star`（间隙刻画）

§3 Gauss–Markov 实例（**用已有定理填字段**）
    gaussMarkovPattern                   `varOf P / n` 是 `Var[est a]` 在 `∑ a = 1` 下的
                                         界紧唯一最小值（参数空间 `Fin n → ℝ`）
    gaussMarkov_opt_unique               模式定理 ⟹ 达到 `v/n` 的 `a` 逐个等于 `1/n`
    gaussMarkov_opt_value_eq             模式定理 ⟹ 达到 `v/n` 的点都有相同方差
    gaussMarkov_star                     `p_star` 的底层权重向量 `= fun _ => 1/n`

§4 OptimalEta 实例（**用已有定理填字段**）
    optimalEtaPattern                    `0` 是 `c(η)` 在 `η : ℝ` 上的界紧唯一最小值
    optimalEta_opt_unique                模式定理 ⟹ `c η = 0` ⟹ `η = 1`
    optimalEta_opt_value_eq              模式定理 ⟹ `c η = 0` 的点都有相同 `c`
    optimalEta_gap_zero_iff              模式定理 ⟹ `c η - 0 = 0 ↔ η = 1`
    optimalEta_star_one                  `p_star = 1`（识别最优点）
    optimalEta_lb_zero                   `lb = 0`（识别下界）
    optimalEta_opt_le                    对一切 `η`，`c 1 ≤ c η`（经模式 `opt_le`）

§5 两个实例共享同一模式（结构同构的精确表述）
    two_instances_share_pattern          两个模式的 `lb / p_star / unique` 并列陈述

===========================================================================
⚠ 诚实边界（必读）
===========================================================================

**1. 这是「抽象的抽象」，本身不产生新的数学内容。**
`OptimalityPattern` 的三个字段 `bound / attained / unique` **字面上就是**
「下界 + 取到 + 唯一」三句话。模式定理（§2）的全部内容是把这三句话
**逻辑上重排**（`f p_star ≤ f p`、`f p = f p_star`、间隙为零 ⟺ 最优）。
这些重排都**真的成立**，但都**短**。本文件的价值在**统一**与**可复用**，
不在难度。**不得**把本文件宣传为新的不等式或新的最优性结论。

**2. 两个实例的数学内容 100% 来自已有模块。**
§3 的 `gaussMarkovPattern` 只**调用** `GaussMarkovScalar.gauss_markov_lower_bound`
与 `GaussMarkovScalar.gauss_markov_equality / gauss_markov_attained`；
§4 的 `optimalEtaPattern` 只**调用**
`OptimalEta.c_nonneg / c_one / c_eq_zero_iff`。
本文件**不重新证明**任何方差不等式或绝对值性质。

**3. `unique` 字段对 Gauss–Markov 只在 `varOf P > 0` 时成立。**
`v = 0` 时任意权重都给出零方差（`n = 2`、`a = (1,0)` 即反例，见
`GaussMarkovScalar.gauss_markov_equality` 注释）。故 §3 的实例**带**
`hv : 0 < varOf P`。**这不是装饰前件**：删掉它该实例为假。

**4. Gauss–Markov 实例的参数空间不是「全体估计器」。**
`GaussMarkovScalar` 只覆盖**线性**估计器 `est a = ∑ a_i ω_i`，
故 `gaussMarkovPattern` 的 `P` 取 `Fin n → ℝ`（权重向量空间），
**不是**「全体无偏估计器」空间。与 `GaussMarkovScalar §登记 1` 一致。

**5. `optimalEtaPattern` 的目标函数是 `c(η) = |1 - η|`，不是载体误差。**
把 `c` 的界紧唯一性搬回**误差层**需要 `OptimalEta.err_eq_c_pow` 与 `n ≥ 1`，
那是 `OptimalEta` 自己的定理（`eta_one_minimizes_any` 等），
本文件**不重复**也不声称。

**6. 前件自查**：见 §6 逐条表。**无**任何定理把结论放进前件。
特别地 §5 的四条 `_opt_unique` / `_opt_value_eq` 的结论
（`a ≡ 1/n`、`η = 1`、值相等）**都不出现在前件里**——
前件只有「取到下界」，结论是**逐点/标识**陈述，
中间必须经过模式的 `unique` 字段与 `Fin`-求和 / `abs` 零点的真内容。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 本文件**无删减项**：§1–§6 全部陈述均已证出（§6 登记）。
-/

import FateWorld.Legacy.OptimalEta
import FateWorld.Legacy.GaussMarkovScalar

namespace Fate

/-! ===========================================================================
    §1  ⭐ **结构定义：界紧 + 取到 + 唯一**
    =========================================================================== -/

/-- ⭐ **「界紧唯一」模式**（`Fate.OptimalityPattern`）。

参数空间 `P`、目标函数 `f : P → ℝ`、下界 `lb : ℝ`、最优点 `p_star : P`。

三个字段就是最优性的三句话：
* `bound`     —— `lb` 是**下界**；
* `attained`  —— `lb` 在 `p_star` **取到**；
* `unique`    —— 取到 `lb` 的点**唯一**（`= p_star`）。

**⚠ 这不是定理**，而是把两个模块里**已经证出**的三句话装进一个结构。
它本身不含数学内容。 -/
structure OptimalityPattern (P : Type*) where
  /-- 目标函数（要最小化的量）。 -/
  f : P → ℝ
  /-- 下界。 -/
  lb : ℝ
  /-- 最优点。 -/
  p_star : P
  /-- `lb` 是下界。 -/
  bound : ∀ p : P, lb ≤ f p
  /-- `lb` 在最优点取到。 -/
  attained : f p_star = lb
  /-- 取到 `lb` 的点唯一。 -/
  unique : ∀ p : P, f p = lb → p = p_star

namespace OptimalityPattern

variable {P : Type*}

/-! ===========================================================================
    §2  ⭐⭐ **模式定理（抽象层）**
    =========================================================================== -/

/-- ⭐ **结构外延性**：三个「定义数据」字段相等则模式相等。

（`bound / attained / unique` 是 `Prop` 值字段，由 `proof irrelevance` 自动对齐。） -/
theorem ext {S T : OptimalityPattern P} (hf : S.f = T.f) (hlb : S.lb = T.lb)
    (hp : S.p_star = T.p_star) : S = T := by
  obtain ⟨f₁, lb₁, ps₁, b₁, a₁, u₁⟩ := S
  obtain ⟨f₂, lb₂, ps₂, b₂, a₂, u₂⟩ := T
  simp only at hf hlb hp
  subst hf hlb hp
  rfl

/-- ⭐⭐⭐ **【模式定理 1：最优点唯一】** 若 `p` 也取到 `lb`，则 `p = p_star`。

**⚠ 这是 `unique` 字段的直接读取**，不是新内容；列出是因为它是
「模式定理」在定义上的第一句（任务 (d) 项的一半）。 -/
theorem unique_opt (S : OptimalityPattern P) (p : P) (h : S.f p = S.lb) :
    p = S.p_star :=
  S.unique p h

/-- ⭐⭐ **【模式定理 2：最优性传回目标层】** `f p_star ≤ f p` 对一切 `p`。

**推导**：`f p_star = lb ≤ f p`（`attained` 组合 `bound`）。
**⚠ 这条确实是把两个字段组合出的新陈述**，但仍很短。 -/
theorem opt_le (S : OptimalityPattern P) (p : P) : S.f S.p_star ≤ S.f p := by
  rw [S.attained]
  exact S.bound p

/-- ⭐ **【模式定理 3：最优值】** `f p_star = lb`（`attained` 的读取）。 -/
theorem opt_eq_lb (S : OptimalityPattern P) : S.f S.p_star = S.lb :=
  S.attained

/-- ⭐⭐⭐ **【模式定理 4：最优值唯一】**

任何取到下界的点，其目标值都等于最优点处的目标值：

$$(f\,p = lb)\;\Longrightarrow\; f\,p = f\,p_{\star}.$$

**推导**：`f p = lb = f p_star`。
**⭐ 意义**：这是「最优**值**唯一」——与「最优**点**唯一」是两个不同陈述。 -/
theorem value_unique (S : OptimalityPattern P) (p : P) (h : S.f p = S.lb) :
    S.f p = S.f S.p_star := by
  rw [h, S.attained]

/-- ⭐⭐⭐ **【模式定理 5：最优点 ∧ 最优值 同时唯一】**（任务 (d) 项的合取形态）

取到 `lb` 的任一 `p`，既等于 `p_star`，又与 `p_star` 同值。

**⚠ 诚实说明**：这是定理 1 与定理 4 的**合取包装**，
数学内容等于两者之和，没有额外信息。 -/
theorem opt_value_unique (S : OptimalityPattern P) (p : P) (h : S.f p = S.lb) :
    p = S.p_star ∧ S.f p = S.f S.p_star :=
  ⟨S.unique p h, S.value_unique p h⟩

/-- ⭐⭐⭐ **【模式定理 6：下界唯一（跨模式）】**

若 `T` 是与 `S` **同一个 `f`、同一个 `p_star`** 的另一个模式，
则 `T.lb = S.lb`。

**证明**：`T.lb = T.f T.p_star = S.f S.p_star = S.lb`
（`T.attained`、`T.p_star = S.p_star`、`T.f = S.f`、`S.attained`）。

**⚠ 前件的 `T.f = S.f` 与 `T.p_star = S.p_star` 不是把结论包进去**：
它们只说「同一个最优化问题的两种表述」。删掉它们结论**为假**
（不同 `f` 的下界当然可以不同）。 -/
theorem lb_unique (S T : OptimalityPattern P) (hf : T.f = S.f)
    (hp : T.p_star = S.p_star) : T.lb = S.lb := by
  rw [← T.attained, hp, hf, S.attained]

/-- ⭐⭐⭐ **【模式定理 7：最优点唯一（跨模式）】**

若 `T` 与 `S` **同一个 `f`、同一个 `lb`**，则 `T.p_star = S.p_star`。

**证明**：`T.p_star` 取到 `T.lb = S.lb`，由 `S.unique` 得 `= S.p_star`。 -/
theorem star_unique (S T : OptimalityPattern P) (hf : T.f = S.f)
    (hlb : T.lb = S.lb) : T.p_star = S.p_star := by
  apply S.unique
  show S.f T.p_star = S.lb
  rw [← hf, ← hlb]
  exact T.attained

/-- ⭐⭐ **【组装器】** 给出三句话，得到模式。 -/
def of_bound_eq (f : P → ℝ) (lb : ℝ) (p_star : P)
    (bound : ∀ p : P, lb ≤ f p) (attained : f p_star = lb)
    (unique : ∀ p : P, f p = lb → p = p_star) : OptimalityPattern P :=
  ⟨f, lb, p_star, bound, attained, unique⟩

/-- ⭐⭐⭐ **【间隙刻画】** `f p - lb = 0 ↔ p = p_star`。

**⭐ 意义**：这是「界**紧**」的最细形式——目标与下界的**间隙**
（optimality gap）恰在**唯一**一点为零。

**证明**：`⟹` 由 `unique`；`⟸` 由 `attained` + 代入。 -/
theorem gap_zero_iff (S : OptimalityPattern P) (p : P) :
    S.f p - S.lb = 0 ↔ p = S.p_star := by
  constructor
  · intro h
    exact S.unique p (sub_eq_zero.mp h)
  · intro h
    rw [h, S.attained, sub_self]

end OptimalityPattern

/-! ===========================================================================
    §3  ⭐⭐⭐ **Gauss–Markov 实例：`Var[est a]` 的界紧唯一最小值 `v/n`**
    =========================================================================== -/

namespace GaussMarkovInstance

open MeasureTheory ProbabilityTheory
open Fate.GaussMarkovScalar

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐⭐⭐⭐ **【实例 A：Gauss–Markov 满足 `OptimalityPattern`】**

固定 `n ≥ 1`、`hP : MemLp id 2 P`、`hv : 0 < varOf P`，以及无偏约束
`∑ a = 1`。令

* 参数空间 `P₀ := {a : Fin n → ℝ // ∑ i, a i = 1}`（**无偏权重**）；
* `f a := variance (est a.val) (Measure.pi (fun _ => P))`；
* `lb := varOf P / n`；
* `p_star := ⟨fun _ => 1 / n, _⟩`（`a ≡ 1/n`，无偏性由 `gauss_markov_attained` 给出）。

三个字段的**来源**（**全部**来自 `Fate.GaussMarkovScalar`）：
* `bound`    ← `gauss_markov_lower_bound`；
* `attained` ← `gauss_markov_attained`（的方差半边）；
* `unique`   ← `gauss_markov_equality`（`hv` 必需）。

**⚠ 本定义不重新证明任何不等式**，只做「填字段」。 -/
noncomputable def gaussMarkovPattern (n : ℕ) (hn : 0 < n)
    (hP : MemLp (fun x : ℝ => x) 2 P) (hv : 0 < varOf P) :
    OptimalityPattern {a : Fin n → ℝ // ∑ i, a i = 1} :=
  OptimalityPattern.of_bound_eq
    (fun a => variance (est (a : Fin n → ℝ)) (Measure.pi (fun _ : Fin n => P)))
    (varOf P / (n : ℝ))
    ⟨fun (_ : Fin n) => (1 : ℝ) / (n : ℝ),
      (gauss_markov_attained hP n hn (fun _ => (1 : ℝ) / (n : ℝ))
        (fun _ => rfl)).1⟩
    (fun a => gauss_markov_lower_bound hP n hn (a : Fin n → ℝ) a.2)
    (show variance (est (fun (_ : Fin n) => (1 : ℝ) / (n : ℝ)))
            (Measure.pi (fun _ : Fin n => P)) = varOf P / (n : ℝ) from
      (gauss_markov_attained hP n hn (fun _ => (1 : ℝ) / (n : ℝ))
        (fun _ => rfl)).2)
    (fun a ha => Subtype.ext
      (funext (gauss_markov_equality hP n hn (a : Fin n → ℝ) a.2 hv ha)))

/-- ⭐⭐⭐ **【实例 A 的模式定理展开：最优点唯一】**

达到下界 `v/n` 的无偏权重向量**逐个坐标**等于 `1/n`。

**⭐ 这是推导链**：`a` 取到 `v/n`（**一个关于方差的全局等式**）
⟹ `a = p_star`（`OptimalityPattern.unique_opt`）
⟹ 逐坐标 `a i = 1/n`（`p_star` 的定义）。
结论 `∀ i, a i = 1/n` **不**在前件中出现。 -/
theorem gaussMarkov_opt_unique (n : ℕ) (hn : 0 < n)
    (hP : MemLp (fun x : ℝ => x) 2 P) (hv : 0 < varOf P)
    (a : {a : Fin n → ℝ // ∑ i, a i = 1})
    (ha : (gaussMarkovPattern n hn hP hv).f a = (gaussMarkovPattern n hn hP hv).lb) :
    ∀ i, (a : Fin n → ℝ) i = (1 : ℝ) / (n : ℝ) := by
  have h := OptimalityPattern.unique_opt (gaussMarkovPattern n hn hP hv) a ha
  have hval : ((a : Fin n → ℝ)) = ((gaussMarkovPattern n hn hP hv).p_star :
      Fin n → ℝ) := congrArg Subtype.val h
  rw [hval]
  show ∀ i, ((⟨fun (_ : Fin n) => (1 : ℝ) / (n : ℝ),
      (gauss_markov_attained hP n hn (fun _ => (1 : ℝ) / (n : ℝ))
        (fun _ => rfl)).1⟩ :
    {a : Fin n → ℝ // ∑ i, a i = 1}) : Fin n → ℝ) i = (1 : ℝ) / (n : ℝ)
  intro i
  rfl

/-- ⭐⭐⭐ **【实例 A 的模式定理展开：最优值唯一】**

任何达到 `v/n` 的无偏权重，其方差都等于最优点的方差。 -/
theorem gaussMarkov_opt_value_eq (n : ℕ) (hn : 0 < n)
    (hP : MemLp (fun x : ℝ => x) 2 P) (hv : 0 < varOf P)
    (a : {a : Fin n → ℝ // ∑ i, a i = 1})
    (ha : (gaussMarkovPattern n hn hP hv).f a = (gaussMarkovPattern n hn hP hv).lb) :
    (gaussMarkovPattern n hn hP hv).f a
      = (gaussMarkovPattern n hn hP hv).f (gaussMarkovPattern n hn hP hv).p_star :=
  OptimalityPattern.value_unique _ a ha

/-- ⭐⭐ **【实例 A 的最优点识别】** `p_star` 的底层权重向量是 `a ≡ 1/n`。 -/
theorem gaussMarkov_star (n : ℕ) (hn : 0 < n)
    (hP : MemLp (fun x : ℝ => x) 2 P) (hv : 0 < varOf P) :
    ∀ i, (((gaussMarkovPattern n hn hP hv).p_star : {a : Fin n → ℝ // ∑ i, a i = 1}) :
      Fin n → ℝ) i = (1 : ℝ) / (n : ℝ) := by
  intro i
  show ((⟨fun (_ : Fin n) => (1 : ℝ) / (n : ℝ),
      (gauss_markov_attained hP n hn (fun _ => (1 : ℝ) / (n : ℝ))
        (fun _ => rfl)).1⟩ :
    {a : Fin n → ℝ // ∑ i, a i = 1}) : Fin n → ℝ) i = (1 : ℝ) / (n : ℝ)
  rfl

end GaussMarkovInstance

/-! ===========================================================================
    §4  ⭐⭐⭐ **OptimalEta 实例：`c(η) = |1-η|` 的界紧唯一最小值 `0`**
    =========================================================================== -/

namespace OptimalEtaInstance

open Fate.OptimalEta

/-- ⭐⭐⭐⭐⭐ **【实例 B：收缩因子最小化满足 `OptimalityPattern`】**

* 参数空间：`ℝ`（全部步长）；
* `f η := c η = |1 - η|`；
* `lb := 0`；
* `p_star := 1`。

三个字段的**来源**（**全部**来自 `Fate.OptimalEta`）：
* `bound`    ← `c_nonneg`（`0 ≤ c η`）；
* `attained` ← `c_one`（`c 1 = 0`）；
* `unique`   ← `c_eq_zero_iff`（`c η = 0 ↔ η = 1`）。

**⚠ 本定义不重新证明任何绝对值性质**，只做「填字段」。 -/
noncomputable def optimalEtaPattern : OptimalityPattern ℝ :=
  OptimalityPattern.of_bound_eq c 0 1
    (fun η => c_nonneg η)
    c_one
    (fun η h => (c_eq_zero_iff η).mp h)

/-- ⭐⭐⭐ **【实例 B 的模式定理展开：最优点唯一】**

`c η = 0` ⟹ `η = 1`（经模式 `unique` 字段，而非直接用 `c_eq_zero_iff`）。

**⭐ 这是推导链**：`η` 取到下界 `0`（`c η = 0`）
⟹ `η = p_star`（`OptimalityPattern.unique_opt`）
⟹ `η = 1`（`p_star` 的定义，`optimalEta_star_one`）。
结论 `η = 1` **不**在前件中出现（前件只说 `c η = 0`）。 -/
theorem optimalEta_opt_unique (η : ℝ)
    (h : optimalEtaPattern.f η = optimalEtaPattern.lb) : η = 1 := by
  have h' := OptimalityPattern.unique_opt optimalEtaPattern η h
  simpa [optimalEtaPattern, OptimalityPattern.of_bound_eq] using h'

/-- ⭐⭐⭐ **【实例 B 的模式定理展开：最优值唯一】**

任何取到下界 `0` 的步长，其收缩因子都等于 `η = 1` 处的收缩因子。 -/
theorem optimalEta_opt_value_eq (η : ℝ)
    (h : optimalEtaPattern.f η = optimalEtaPattern.lb) :
    optimalEtaPattern.f η = optimalEtaPattern.f optimalEtaPattern.p_star :=
  OptimalityPattern.value_unique _ η h

/-- ⭐⭐⭐ **【实例 B 的间隙刻画】** `c η - 0 = 0 ↔ η = 1`。 -/
theorem optimalEta_gap_zero_iff (η : ℝ) :
    optimalEtaPattern.f η - optimalEtaPattern.lb = 0 ↔ η = 1 := by
  rw [OptimalityPattern.gap_zero_iff]
  simp [optimalEtaPattern, OptimalityPattern.of_bound_eq]

/-- ⭐⭐ **【实例 B 的最优点识别】** `p_star = 1`。 -/
theorem optimalEta_star_one : optimalEtaPattern.p_star = (1 : ℝ) := rfl

/-- ⭐⭐ **【实例 B 的下界识别】** `lb = 0`。 -/
theorem optimalEta_lb_zero : optimalEtaPattern.lb = 0 := rfl

/-- ⭐⭐ **【实例 B 的最优性】** 对一切步长，`c 1 ≤ c η`（经模式 `opt_le`）。 -/
theorem optimalEta_opt_le (η : ℝ) : c 1 ≤ c η := by
  have h := OptimalityPattern.opt_le optimalEtaPattern η
  simpa [optimalEtaPattern, OptimalityPattern.of_bound_eq] using h

end OptimalEtaInstance

/-! ===========================================================================
    §5  ⭐⭐⭐ **两个实例落在**同一**模式上（结构同构的精确表述）**
    =========================================================================== -/

section SharedPattern

open MeasureTheory

variable {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]

/-- ⭐⭐⭐ **【两个实例同构：唯一的共同结构】**

`GaussMarkov` 与 `OptimalEta` 的界紧唯一性**只**共享三元组
「下界 / 取到 / 唯一」。两者都已**具体构造**出模式实例
（`GaussMarkovInstance.gaussMarkovPattern` 与
`OptimalEtaInstance.optimalEtaPattern`），故都享有 §2 的全部模式定理
（`unique_opt / value_unique / gap_zero_iff` 等）。

**⚠ 诚实说明**：本定理只主张两者**满足同一组公理**，
**不**主张两个实例的 `f` 之间有保序映射——`variance` 与 `|1-η|` 之间
不存在这样的对应（§6.2 登记 1）。 -/
theorem two_instances_share_pattern (n : ℕ) (hn : 0 < n)
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    (hv : 0 < GaussMarkovScalar.varOf P) :
    (GaussMarkovInstance.gaussMarkovPattern n hn hP hv).lb
        = GaussMarkovScalar.varOf P / (n : ℝ)
      ∧ OptimalEtaInstance.optimalEtaPattern.lb = 0
      ∧ OptimalEtaInstance.optimalEtaPattern.p_star = (1 : ℝ)
      ∧ (∀ a : {a : Fin n → ℝ // ∑ i, a i = 1},
          (GaussMarkovInstance.gaussMarkovPattern n hn hP hv).f a
            = (GaussMarkovInstance.gaussMarkovPattern n hn hP hv).lb →
          a = (GaussMarkovInstance.gaussMarkovPattern n hn hP hv).p_star)
      ∧ (∀ η : ℝ, OptimalEtaInstance.optimalEtaPattern.f η
            = OptimalEtaInstance.optimalEtaPattern.lb → η = 1) :=
  ⟨rfl,
   OptimalEtaInstance.optimalEta_lb_zero,
   OptimalEtaInstance.optimalEta_star_one,
   fun a ha => OptimalityPattern.unique_opt _ a ha,
   fun η hη => OptimalEtaInstance.optimalEta_opt_unique η hη⟩

end SharedPattern

/-! ===========================================================================
    §6  ⚠ **诚实边界 + 前件自查表**
    =========================================================================== -/

/-!
### §6.1 前件自查（**逐条确认无同义反复**）

| 定理 | 前件 | 结论 | 结论是否被前件包含？ |
|---|---|---|---|
| `OptimalityPattern.ext` | `f/ lb / p_star` 相等 | 模式相等 | ❌ 否（需结构外延）|
| `OptimalityPattern.unique_opt` | `f p = lb` | `p = p_star` | ❌ 否（**读取 `unique` 字段**；该字段本身是具体模块的真内容）|
| `OptimalityPattern.opt_le` | 无 | `f p_star ≤ f p` | ❌ 否（需 `attained` + `bound` 组合）|
| `OptimalityPattern.value_unique` | `f p = lb` | `f p = f p_star` | ❌ 否（需 `attained` 代换）|
| `OptimalityPattern.opt_value_unique` | `f p = lb` | `p = p_star ∧ 同值` | ❌ 否（合取包装，登记为弱）|
| `OptimalityPattern.lb_unique` | `T.f = S.f`、`T.p_star = S.p_star` | `T.lb = S.lb` | ❌ 否（前件不含 `lb` 信息）|
| `OptimalityPattern.star_unique` | `T.f = S.f`、`T.lb = S.lb` | `T.p_star = S.p_star` | ❌ 否（前件不含 `p_star` 信息）|
| `OptimalityPattern.gap_zero_iff` | 无 | `f p - lb = 0 ↔ p = p_star` | ❌ 否（需 `unique` + `attained`）|
| `gaussMarkov_opt_unique` | `f a = lb`（方差 = `v/n`）| `∀ i, a i = 1/n` | ❌ 否（全局等式 ⟹ 逐点，经 `unique` 字段）|
| `gaussMarkov_opt_value_eq` | `f a = lb` | 方差相等 | ❌ 否（同上）|
| `optimalEta_opt_unique` | `c η = 0` | `η = 1` | ❌ 否（经 `unique` 字段，非直接 `c_eq_zero_iff`）|
| `optimalEta_opt_value_eq` | `c η = 0` | `c η = c 1` | ❌ 否（同上）|
| `optimalEta_gap_zero_iff` | 无 | `c η - 0 = 0 ↔ η = 1` | ❌ 否（组合 `gap_zero_iff` + 实例）|
| `optimalEta_opt_le` | 无 | `c 1 ≤ c η` | ❌ 否（经 `opt_le`）|
| `gaussMarkov_star` | 无（仅 `n ≥ 1`）| `p_star` 的权重 `= 1/n` | ❌ 否（`p_star` 的 `val` 是构造出来的）|
| `two_instances_share_pattern` | `hv`、`hP`、`n ≥ 1` | 五个并列事实 | ❌ 否（合取包装，各分量均另证）|

**⚠ 需要额外解释的两条**：

1. `OptimalityPattern.unique_opt` **字面上就是** `unique` 字段的读取。
   它的「真内容」**外包**给了具体实例（`gauss_markov_equality` 用 Cauchy–Schwarz
   等号结构；`c_eq_zero_iff` 用 `abs` 零点）。本文件**如实登记**：
   模式定理本身是**组合**，不是新的不等式。

2. `gaussMarkovPattern` 与 `optimalEtaPattern` **是 `def` 不是 `theorem`**：
   它们是「填字段」，其内容的真伪完全由被引用的已有定理承担。
   本文件**不**声称自己证了什么新的方差界或新的收缩率界。

### §6.2 未做项（明确登记，**非**删除项）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | 两个实例之间的**函子**（保序映射）| `variance` 与 `c(η)` 是不同载体上的量，之间**不存在**自然的保序双射；强行构造会得到假陈述。本文件只主张「共享同一组公理」 |
| 2 | 把 `c` 的模式最优性搬回**误差层** | 需 `err_eq_c_pow` + `n ≥ 1`；已由 `OptimalEta.eta_one_minimizes_any` / `eta_ne_one_strictly_slower` 给出，本文件不重复 |
| 3 | Gauss–Markov 推广到**一般（非线性）无偏估计器** | 本环境无 Fisher 信息（`GaussMarkovScalar §登记 1` 已实测登记），不可做 |
| 4 | `varOf P = 0` 时的模式 | `unique` 字段**为假**（任意权重均零方差）；故 `gaussMarkovPattern` 带 `hv`。**如实不做**，不是遗漏 |
| 5 | 模式的最大/最小**存在性**（一般拓扑下）| 模式**自带** `p_star`（字段），故不涉及存在性证明；讨论「何时存在 `p_star`」是另一问题，本文件不做 |

**⚠ 无 `sorry` / `admit` / `axiom`。**
**⚠ 本文件无**删除定理：§1–§5 全部陈述均已证出。
-/

end Fate
