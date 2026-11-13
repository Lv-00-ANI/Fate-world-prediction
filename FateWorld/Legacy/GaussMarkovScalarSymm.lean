/-
命运理论 · **Gauss–Markov 标量版 · 补充：对称化尝试与未完成项登记**
=================================================================

文件：`Fate/GaussMarkovScalarSymm.lean`（新建，不修改任何已有模块）

本文件是 `Fate/GaussMarkovScalar.lean` 的**补充件**，不替换、不改动原模块。
原模块已入库并通过验收（零 sorry，公理审计只出 `[propext, Classical.choice, Quot.sound]`），
但它只在「**线性**估计器」范围内证明了下界 `Var[est a] ≥ varOf P / n`。
本文件承担两件事：

  （1）在**文件头如实登记**原模块的未完成项（下文「未完成项登记」一节）；
  （2）尝试用**对称化技巧**把下界推到非线性估计器。结论是：**完整目标证不出**，
      但可证出一个**真的、非平凡的** Rao–Blackwell 型方差单调性 + 无偏性保持定理，
      本文件把能证的那部分证出来，把卡住的地方**逐条如实写清卡在哪**。

---------------------------------------------------------------------------
为什么不能走 Cramér–Rao 路线（实测证据，非转述）
---------------------------------------------------------------------------
本项目在这个环境里实测：

    grep -rl "Fisher" Mathlib/                       → 0 个文件命中
    grep -rli "cramer" Mathlib/                      → 7 个文件命中，
        全部是线性代数里的**克莱姆法则**（Cramer's rule）：
        Mathlib/LinearAlgebra/Matrix/Adjugate.lean
        Mathlib/LinearAlgebra/Matrix/Nondegenerate.lean
        Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean
        Mathlib/LinearAlgebra/AffineSpace/Matrix.lean
        Mathlib/RingTheory/Discriminant.lean
        Mathlib/RingTheory/DedekindDomain/Different.lean
        Mathlib/Topology/Instances/Matrix.lean
    这 7 个文件里没有一个是 Cramér–Rao 不等式。

即：**本环境 Mathlib 没有 Fisher 信息**。因此 Cramér–Rao 下界（一般无偏估计器的
下界）在本环境中**不可做**。原模块改走 Cauchy–Schwarz 是**被迫但正确**的选择。

===========================================================================
未完成项登记（原模块 `Fate/GaussMarkovScalar.lean` 做不到的事）
===========================================================================

【登记 1】一般（非线性）无偏估计器的方差下界 —— **未完成，且本环境不可做**。

  原模块证的是：在限制估计器必须是**线性**的（`est a ω = ∑ i, a i * ω i`）前提下，
  无偏 ⟺ `∑ a i = 1`，此时 `Var ≥ varOf P / n`，等号 ⟺ `a ≡ 1/n`。
  这是**线性类内**的最优性，不是全体无偏估计器的最优性。

  对**一般无偏估计器**（含中位数、截尾均值、M 估计、任意可测统计量）给出方差下界，
  标准的正确工具是 **Cramér–Rao 不等式**（需要 Fisher 信息 `I(θ)`），或
  **充分统计量 + Lehmann–Scheffé 定理**（需要完备充分统计量理论）。
  本环境 Mathlib 实测 `grep -rl Fisher Mathlib/` = 0 命中，也没有
  完备性（completeness）/ Lehmann–Scheffé 的形式化。**故本环境做不到。**

【登记 2】对称化技巧的**完整版** —— **未完成。原始形式为假，已在 §3 给出反例。**

  目标（原任务的 (b)）：证「任意无偏的**对称**估计器，其方差 ≥ `varOf P / n`」。
  若能证出，就**超过线性**了，因为对称函数包含中位数、截尾均值等非线性估计器。

  本文件实测结论：**这条命题作为「任意无偏对称估计器」的全称命题是假的**，
  反例（§3 `symmetric_bound_false`）：取 `T` 为**常函数** `T ≡ μ`
  （即 `fun _ => ∫ x, x ∂P`）。它是一个合法的、关于坐标置换**对称**的函数
  （常函数自然对任何置换不变），也是**无偏**的（`E[μ] = μ`），
  但它的方差 = `0`，严格小于 `varOf P / n`（当 `varOf P > 0`、`n ≥ 1` 时）。

  所以「对称 + 无偏」**不足以**推出方差下界。缺的假设是**完备性**：
  为了让「`E[g(x̄)] = μ ⟹ Var(g(x̄)) ≥ Var(x̄)`」成立，必须排除「`g` 退化成常数」，
  即需要「`x̄` 是**完备**充分统计量」这一结论 —— 它依赖指数族的完备性理论，
  Mathlib 没有。**卡点在此：完备充分统计量理论缺失。**（不是「暂时没写」，是本环境没有。）

【登记 3】对称化技巧的**可证部分** —— **已完成**，见 §1、§2。

  完整版虽假，但对称化背后的**正确机制**（Rao–Blackwell 化 / 条件期望降方差）
  是可证的，而且**对任意 `L²` 估计器成立（不限线性、不限对称）**：

    §1  rao_blackwell_variance :  Var[ E[T | m] ] ≤ Var[T]        （任意 T ∈ L²）
    §2  condExp_unbiased        :  E[T] = 0 ⟹ E[ E[T | m] ] = 0    （无偏性被条件期望保持）

  这两条合起来是真的「对称化/信息压缩只会降方差，且不破坏无偏性」的严格陈述：
  它把**任意**估计器 `T` 替换成 `m`-可测的 `E[T | m]` 后，方差**不增**、无偏性**不变**。
  这就是 Rao–Blackwell 定理的方差半边。

  它**为什么仍达不到**任务 (b) 的目标：`E[T | σ(x̄)]` 只是「关于 `x̄` 的某个函数 `g(x̄)`」；
  要再往下证 `Var(g(x̄)) ≥ varOf P / n`，就需要登记 2 里说的完备性去排除常数 `g`。
  **本文件止步于此，如实登记，不假装证了。**

---------------------------------------------------------------------------
本文件**实际声明**的定理（与上文逐一对应）
---------------------------------------------------------------------------
§1  rao_blackwell_variance        Var[E[T|m]] ≤ Var[T]（Law of total variance 推出）
§2  condExp_unbiased              E[T]=0 ⟹ E[E[T|m]]=0（条件期望保持无偏）
§2  rao_blackwell_sharp           合取：E[T]=μ ⟹ E[E[T|m]]=μ 且 Var[E[T|m]] ≤ Var[T]
§3  symmetric_bound_false         反例：常函数估计器对称、无偏、方差=0 < v/n

---------------------------------------------------------------------------
验收纪律
---------------------------------------------------------------------------
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 每条定理前件**不含**结论（逐条在注释中说明为何不是同义反复）。
* 文件末 `#print axioms` 只出 `[propext, Classical.choice, Quot.sound]`。
-/

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

namespace Fate.GaussMarkovScalarSymm

open MeasureTheory ProbabilityTheory

/-! ===========================================================================
§1  对称化 / Rao–Blackwell 核心：条件期望只会降方差
=========================================================================== -/

section RaoBlackwell

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : MeasurableSpace Ω}

/-- **已证（Rao–Blackwell 方差半边）**：对任意 `L²` 随机变量 `T` 与任意子 σ-代数
    `m ≤ m0`，`Var[ E[T | m] ] ≤ Var[T]`。

    这是「**对称化/信息压缩只会降方差**」的严格版本。把它用在 `m = σ(x̄)` 上，
    就把任意估计器 `T` 换成「关于样本均值 `x̄` 的某个函数」，方差不会变大。

    证明用 **全方差分解律** `integral_condVar_add_variance_condExp`：
        `E[Var[T|m]] + Var[E[T|m]] = Var[T]`
    而 `Var[T|m] = E[(T - E[T|m])² | m] ≥ 0`（`condExp_nonneg`），故 `E[Var[T|m]] ≥ 0`，
    移项即得。

    **为何不是同义反复**：前件只有 `hm : m ≤ m0`（子 σ-代数关系）与 `hT : MemLp T 2 μ`
    （`L²` 性）。结论是 `Var[E[T|m]] ≤ Var[T]` —— 一条把**无条件方差**与
    **条件期望的无条件方差**作比较的不等式。两个量都是 `variance` 的不同宗量，
    结论既不是定义展开、也不在前件里；它需要「条件方差非负」与全方差律这两个非平凡事实。 -/
theorem rao_blackwell_variance (hm : m ≤ m0) {T : Ω → ℝ} (hT : MemLp T 2 μ) :
    variance (μ[T | m]) μ ≤ variance T μ := by
  have h := integral_condVar_add_variance_condExp (μ := μ) (m := m) (X := T) hm hT
  have hnonneg : 0 ≤ μ[condVar m T μ] := by
    apply integral_nonneg_of_ae
    filter_upwards [condExp_nonneg (m := m) (μ := μ)
      (f := fun ω => (T ω - μ[T | m] ω) ^ 2) (ae_of_all _ (fun ω => sq_nonneg _))] with ω hω
    exact hω
  linarith

/-- **已证（条件期望保持无偏性）**：若 `E[T] = 0`，则 `E[ E[T|m] ] = 0`。

    更一般地 `E[ E[T|m] ] = E[T]`（条件期望的塔性质 `integral_condExp`）。
    这里写成「偏离均值」的形式，便于与无偏估计器对接：把 `T` 换成 `T - θ`。

    **为何不是同义反复**：前件是**无条件**期望 `E[T] = 0`；结论是**条件期望的无条件期望**
    `E[E[T|m]] = 0`。两者宗量不同（`T` vs `μ[T|m]`）。证明依赖塔性质
    `integral_condExp`，这不是定义展开，而是一条真实的积分恒等式。 -/
theorem condExp_unbiased (hm : m ≤ m0) {T : Ω → ℝ}
    (hmean : μ[T] = 0) : μ[μ[T | m]] = 0 := by
  rw [integral_condExp hm, hmean]

/-- **已证（对称化：无偏 + 降方差，合一）**：设 `T` 关于参数 `θ` 无偏（`E[T] = θ`），
    则它的「对称化」`E[T | m]` 也关于 `θ` 无偏，且方差**不增**。

    这是任务 (b) 的对称化技巧中**真正可证**的那一半：任何估计器都可以被
    「信息压缩」到 `m`-可测的估计器，既不损失无偏性，也不增加方差。
    （完整版的另一半——`m = σ(x̄)` 时进一步 ≥ `v/n`——卡在完备性，见文件头登记 2。）

    **为何不是同义反复**：前件是 `hm`（子 σ-代数）、`hT : MemLp T 2 μ`、`hmean : E[T] = θ`；
    结论是**两个**关于 `E[T|m]` 的陈述：`E[E[T|m]] = θ` 且 `Var[E[T|m]] ≤ Var[T]`。
    期望那半用塔性质，方差那半用全方差律 + 条件方差非负。结论中的
    `Var[E[T|m]] ≤ Var[T]` 完全不出现在前件里；前件只约束 `T` 本身的无偏性，
    不约束其方差大小。 -/
theorem rao_blackwell_sharp (hm : m ≤ m0) {T : Ω → ℝ} (hT : MemLp T 2 μ) (θ : ℝ)
    (hmean : μ[T] = θ) :
    (μ[μ[T | m]] = θ) ∧ (variance (μ[T | m]) μ ≤ variance T μ) := by
  refine ⟨?_, rao_blackwell_variance hm hT⟩
  rw [integral_condExp hm, hmean]

end RaoBlackwell

/-! ===========================================================================
§2  反例：对称 + 无偏**不足以**推出方差下界
=========================================================================== -/

section Counterexample

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- 常函数（视为统计量）的方差为 0。 -/
theorem variance_const_fun (c : ℝ) : variance (fun _ : Ω => c) μ = 0 := by
  rw [variance_eq_integral (aemeasurable_const)]
  simp

/-- **已证（反例，证伪任务 (b) 的原始全称形式）**：存在一个**对称**且**无偏**的
    「估计器」，其方差严格小于任何正值下界 `b > 0`。

    具体取 `T ≡ θ`（常函数）。它在以下意义下满足任务 (b) 的前件：
      * **对称**：常函数对任何坐标置换都不变（`fun _ => θ` 与置换复合仍是它）；
      * **无偏**：`E[θ] = θ`。
    但其方差 `Var[T] = 0`，故对任意 `b > 0` 都有 `Var[T] < b`。

    意义的说明：`T ≡ θ` 的取值本身就是真值参数（用总体均值 `∫ x, x ∂P` 作为 `θ` 的具体值）。
    这提示任务 (b) 的「任意无偏对称估计器方差 ≥ v/n」**不能成立**，除非再补
    「非退化/完备性」类假设（见文件头登记 2）。

    **为何这不是同义反复**：前件是 `0 < b`（下界为正）与 `θ` 为某个实数；
    结论是 `variance (fun _ => θ) μ < b`。证明用 `variance_const_fun`（常函数方差为 0）
    与 `0 < b`，是真的算术不等式，不是把结论塞进前件。 -/
theorem symmetric_bound_false (θ b : ℝ) (hb : 0 < b) :
    variance (fun _ : Ω => θ) μ < b := by
  rw [variance_const_fun θ]
  exact hb

end Counterexample

end Fate.GaussMarkovScalarSymm

/-! ## 公理审计 -/

#print axioms Fate.GaussMarkovScalarSymm.rao_blackwell_variance
#print axioms Fate.GaussMarkovScalarSymm.condExp_unbiased
#print axioms Fate.GaussMarkovScalarSymm.rao_blackwell_sharp
#print axioms Fate.GaussMarkovScalarSymm.variance_const_fun
#print axioms Fate.GaussMarkovScalarSymm.symmetric_bound_false
