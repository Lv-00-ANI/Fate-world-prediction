/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Rules.CompNotCommutative`
阶段：**规则层 · 补 `Fate.ComposeSemantics` §4 登记的「未证项」**

---------------------------------------------------------------------------
(a) 本文件补什么
---------------------------------------------------------------------------
`Fate/ComposeSemantics.lean` 的文件头 §4「诚实边界」逐字登记：

> **本文件【没有】证明什么**
> - **没有证明「`comp` 一般不可交换」**。要证这个需要一个**具体的非确定反例**
>   （两条真分布的 `MeasurableRule` 使 `comp R₂ R₁ ≠ comp R₁ R₂`），本文件**未做**。

**本文件补上的正是这一条**：给出一个**具体的、完全显式的**反例，
在 `C := Unit`、`X := Y := Fin 2` 上构造两条 `MeasurableRule` `R₁`、`R₂`，
并证明

  `(R₂.comp R₁).rule.kernel () 0 {1} = 1/2`
  `(R₁.comp R₂).rule.kernel () 0 {1} = 0`

故二者**不相等**，即 `comp` **不可交换**。

**「非确定」在哪**：`R₂` 在 `x = 0` 处的核是 `1/2 • δ₀ + 1/2 • δ₁`，
**两个原子都有正质量**（不是任何 Dirac），这正是区别于
`ComposeSemantics.fin2_comp_not_comm`（纯确定性 / 函数复合）的关键。

---------------------------------------------------------------------------
(b) 它排除了什么
---------------------------------------------------------------------------
`comp` 是 `Fate/ComposeOperator.lean` §3.4 给出的**核复合（边缘化）**实现，
对应净版开放问题 5.1 的**候选 1「两条规则前后相接」/ 候选 2「条件分布的边缘化」**
（本文件的 `comp` 逐字就是 `Measure.bind`，见 `comp_kernel_apply`）。

**⟹ 本文件证明：核复合（边缘化）这一族实现不满足交换律。**

**⚠ 但它【不】排除候选 1/候选 2**——候选 1/候选 2 需要的只是「是一个合法的
∘ 实现」，而**规格 §5.3.4 明文不要求 ∘ 交换**
（「本章保留三个算子，但**不以三者间存在任何交换律、结合律或优先序为前提**」）。
本文件只是把「若某人主张 ∘ 就是核复合、且 ∘ 应交换」这一**联合主张**判为不可能。

**精确形式（已定理化，见 `no_commutative_marginalisation`）**：

  `¬ ∃ comp : MeasurableRule CX SS2 SS2 → MeasurableRule CX SS2 SS2 →
        MeasurableRule CX SS2 SS2,
      (∀ R₁ R₂, comp R₂ R₁ = R₂.comp R₁) ∧ (∀ R₁ R₂, comp R₁ R₂ = comp R₂ R₁)`

即：**不存在一个算子，它既逐字实现核复合（边缘化）又交换。**
这是「若 ∘ = 核复合 且 ∘ 交换」这一联合主张的**否证**。
**它仍然【不】排除「∘ = 核复合」单独成立**——那一支不需要交换性。

---------------------------------------------------------------------------
(c) 它【不】证明什么（逐条如实登记）
---------------------------------------------------------------------------
1. **不证明「候选 3（并 + 闭包）是唯一正确的 ∘」**。
   本文件与 `ComposeSemantics.two_semantics_incompatible` 合起来只给出
   「`combClosure` 可交换」+「`comp` 不可交换」，
   这**只说明两者是不同运算**，**不说明哪个是「规格要的那个」**——
   规格的开放问题 5.1 至今**未回答**，本文件**不替它回答**。
2. **不证明「候选 2（边缘化）」被排除**。
   候选 2 与 `comp` 在 `ComposeOperator` 的实现里**是同一个东西**
   （`comp_kernel_apply` 就是边缘化公式）；本文件证明它不交换，
   而不可交换**不构成**对它的排除（见 (b)）。
3. **不证明「任何 ∘ 都不可交换」**。
   本文件证明的是:**存在**一对具体的 `MeasurableRule` 使 `comp R₂ R₁ ≠ comp R₁ R₂`
   （`comp_not_commutative_witness`），从而核复合**不是**交换运算
   （`comp_not_commutative`）。
   它**不**蕴含「所有可能的 ∘ 语义都不可交换」——`combClosure` 就是可交换的反例。
4. 本文件的反例取在 `Fin 2`（有限、全离散）上，
   **不**主张该反例在任意 `StateSpace` 上都可移植。

---------------------------------------------------------------------------
(d) 构造链条（每一步都实际证出，无空格）
---------------------------------------------------------------------------
* `SS2` / `CX`：`Carrier := Fin 2` / `Unit` 的 `StateSpace` / `CtxSpace`；
* `fin2Measure c₀ c₁ := c₀ • δ₀ + c₁ • δ₁`：`Fin 2` 上的有限背包测度；
* `R₁`：核恒为 `Measure.dirac 0`（两条都到 0）；
* `R₂`：`0 ↦ 1/2 • δ₀ + 1/2 • δ₁`（**非确定**，两原子都是正质量），`1 ↦ δ₁`；
* `measurableSet_singleton_one`：`{1} ⊆ Fin 2` 可测；
* `dirac_zero_singleton_one` / `dirac_one_singleton_one`：`δ₀{1} = 0` / `δ₁{1} = 1`；
* `fin2Measure_singleton_one`：`fin2Measure c₀ c₁ {1} = c₁`；
* `R₂compR₁_apply`：`(R₂.comp R₁) … {1} = 1/2`（用 `comp_kernel_apply` + `dirac` 的积分）；
* `R₁compR₂_apply`：`(R₁.comp R₂) … {1} = 0`（用 `comp_kernel_apply` + 常函数积分）；
* `comp_not_commutative_witness`：`∃ A B, B.comp A ≠ A.comp B`（见证 = 上面的 `R₁`、`R₂`）；
* `comp_not_commutative`：`¬ ∀ R₁ R₂, R₂.comp R₁ = R₁.comp R₂`；
* `no_commutative_marginalisation`：不存在既逐字实现核复合又交换的算子；
* `comp_values`：上面两条定量事实 + 不相等，打包成合取。

---------------------------------------------------------------------------
诚实声明
---------------------------------------------------------------------------
本文件**零 `sorry`、零 `admit`、零 `axiom`**。所用引理全部为 Mathlib 已有定理
或本文件内实际证出的定理。文件头只列**实际存在**的定理名。
-/

import FateWorld.FateV2.Rules.ComposeOperator
namespace FateV2.Rules.CompNotCommutative

open FateV2.Model
open FateV2.Modeling

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Fate.ComposeOperator

universe u

noncomputable section

/-!
  # Rules · CompNotCommutative

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CompNotCommutative.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ComposeOperator
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  载体：`Unit` 与 `Fin 2`
    =========================================================================== -/

/-- 状态空间 `Fin 2`，带离散拓扑与（相应地）离散可测结构。

本文件取 `topo := ⊤`、`meas := ⊤`（`Fin 2` 上的**离散**结构），
故 `borel_le` 由 `le_top` 直接得到（`borel ⊤ ≤ ⊤` 恒真）。
**⚠ 诚实标注**：这比「标准」结构更粗——它使**一切**集合可测，
从而反例中所需的可测性见证**无条件成立**。
这不削弱结论：反例只依赖 `Fin 2` 上的**有限和**计算，与拓扑粗精无关。 -/
abbrev SS2 : StateSpace where
  Carrier := Fin 2
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 上下文空间 `Unit`（**单个**上下文，故 `comp` 的 `c` 参数不承载信息）。

⚠ 用 `Unit` 而非 `PUnit`：`PUnit.{u}` 的 universe 是多态的，
会让 `Rule.kernel` 的 universe 元变量无法收敛（实测报
「contains universe level metavariables」）。`Unit` 是定 universe 的。 -/
abbrev CX : CtxSpace where
  Carrier := Unit

/-! ===========================================================================
    §2  两条 `MeasurableRule`
    =========================================================================== -/

/-- 把 `Fin 2` 上的 `ENNReal` 背包成 `Measure (Fin 2)`（`Fin 2` 上积分 = 有限和）。

$$\sum_{i} c_i\,\delta_i \quad\text{写作}\quad
  \texttt{fin2Measure}\; c_0\; c_1 .$$

用 `1/2 • δ₀ + 1/2 • δ₁` 而非「`(δ₀+δ₁)/2`」，是为了让它对单点集的取值
（`fin2Measure_singleton_one`）可由 `Measure.add_apply` + `Measure.smul_apply`
**逐项**算出。 -/
def fin2Measure (c₀ c₁ : ℝ≥0∞) : Measure (Fin 2) :=
  c₀ • Measure.dirac 0 + c₁ • Measure.dirac 1

/-- **`R₁`**：两条输入状态**都**送到 `δ₀`（「把所有东西压到 0」）。

$$R_1.\mathrm{kernel}\;c\;0 = \delta_0,\qquad
  R_1.\mathrm{kernel}\;c\;1 = \delta_0 .$$

可测性：核是**常函数**，故 `measurable_const`。 -/
def R₁ : MeasurableRule CX SS2 SS2 where
  rule := { kernel := fun _ _ => MeasureTheory.Measure.dirac 0 }
  measurable_kernel := fun _ => measurable_const

/-- **`R₂`**：`0 ↦ (δ₀+δ₁)/2`（均匀），`1 ↦ δ₁`（确定）。

$$R_2.\mathrm{kernel}\;c\;0 = \tfrac12\delta_0 + \tfrac12\delta_1,\qquad
  R_2.\mathrm{kernel}\;c\;1 = \delta_1 .$$

可测性：`Fin 2` 上函数必可测（`measurable_of_countable`）。 -/
def R₂ : MeasurableRule CX SS2 SS2 where
  rule :=
    { kernel := fun _ x =>
        if x = 0 then fin2Measure (1/2) (1/2) else fin2Measure 0 1 }
  measurable_kernel := fun _ => measurable_of_countable _

/-! ===========================================================================
    §3  单点集的测度：`{1} ⊆ Fin 2`
    =========================================================================== -/

/-- `{1} ⊆ Fin 2` 可测（`Fin 2` 有 `MeasurableSingletonClass`）。 -/
theorem measurableSet_singleton_one : MeasurableSet ({1} : Set (Fin 2)) :=
  measurableSet_singleton 1

/-- `δ₀({1}) = 0`（`0 ≠ 1`）。 -/
theorem dirac_zero_singleton_one : (Measure.dirac (0 : Fin 2)) {1} = 0 := by
  rw [Measure.dirac_apply' _ (measurableSet_singleton 1)]
  simp

/-- `δ₁({1}) = 1`。 -/
theorem dirac_one_singleton_one : (Measure.dirac (1 : Fin 2)) {1} = 1 := by
  rw [Measure.dirac_apply' _ (measurableSet_singleton 1)]
  simp

/-- `fin2Measure c₀ c₁ {1} = c₁`：`Fin 2` 上单点集的背包测度就是该点系数。 -/
theorem fin2Measure_singleton_one (c₀ c₁ : ℝ≥0∞) :
    fin2Measure c₀ c₁ {1} = c₁ := by
  simp only [fin2Measure, Measure.add_apply, Measure.smul_apply,
    dirac_zero_singleton_one, dirac_one_singleton_one, smul_eq_mul, mul_zero,
    mul_one, zero_add]

/-! ===========================================================================
    §4  ⭐ `R₂ ∘ R₁` 在 `x = 0` 上，`{1}` 的测度 `= 1/2`
    =========================================================================== -/

/-- ⭐ **`(R₂.comp R₁) … {1} = 1/2`**。

由 `comp_kernel_apply`：
`(R₂.comp R₁)(c,0){1} = ∫⁻ y, R₂.kernel y {1} ∂(R₁.kernel 0)`
而 `R₁.kernel 0 = δ₀`，故积分退化为在 `y = 0` 处的取值
`R₂.kernel 0 {1} = (1/2 • δ₀ + 1/2 • δ₁){1} = 1/2`。 -/
theorem R₂compR₁_apply :
    (R₂.comp R₁).rule.kernel () (0 : Fin 2) ({1} : Set (Fin 2)) = 1/2 := by
  rw [MeasurableRule.comp_kernel_apply R₂ R₁ () (0 : Fin 2)
    measurableSet_singleton_one]
  -- `R₁.rule.kernel c 0 = δ₀`
  show (∫⁻ y : Fin 2, R₂.rule.kernel () y {1} ∂Measure.dirac 0) = 1/2
  rw [lintegral_dirac]
  -- 只剩 `R₂.rule.kernel () 0 {1} = fin2Measure (1/2) (1/2) {1} = 1/2`
  show fin2Measure (1/2) (1/2) {1} = 1/2
  rw [fin2Measure_singleton_one]

/-! ===========================================================================
    §5  ⭐ `R₁ ∘ R₂` 在 `x = 0` 上，`{1}` 的测度 `= 0`
    =========================================================================== -/

/-- ⭐ **`(R₁.comp R₂) … {1} = 0`**。

由 `comp_kernel_apply`：
`(R₁.comp R₂)(c,0){1} = ∫⁻ y, R₁.kernel y {1} ∂(R₂.kernel 0)`
而 `R₂.kernel 0 = 1/2 • δ₀ + 1/2 • δ₁`，被积函数恒为 `δ₀{1} = 0`，
故积分为 `0`。 -/
theorem R₁compR₂_apply :
    (R₁.comp R₂).rule.kernel () (0 : Fin 2) ({1} : Set (Fin 2)) = 0 := by
  rw [MeasurableRule.comp_kernel_apply R₁ R₂ () (0 : Fin 2)
    measurableSet_singleton_one]
  -- 被积函数是常函数 `δ₀{1} = 0`
  have hfun : (fun y : Fin 2 => R₁.rule.kernel () y ({1} : Set (Fin 2)))
      = fun _ => (0 : ℝ≥0∞) := by
    funext y
    show (Measure.dirac (0 : Fin 2)) ({1} : Set (Fin 2)) = 0
    exact dirac_zero_singleton_one
  show (∫⁻ y : Fin 2, R₁.rule.kernel () y ({1} : Set (Fin 2))
      ∂fin2Measure (1/2) (1/2)) = 0
  rw [hfun, lintegral_zero]

/-! ===========================================================================
    §6  ⭐⭐ 主结论：`comp` 不可交换
    =========================================================================== -/

/-- ⭐⭐ **`comp` 不可交换（具体反例）**。

存在一对 `MeasurableRule` `A B : MeasurableRule CX SS2 SS2`，使
`B.comp A ≠ A.comp B`。**见证取本文件 §2 构造的 `R₁`、`R₂`**（反之亦然）。

**证明**：先证 `R₂.comp R₁ ≠ R₁.comp R₂`（用 §4、§5 的数值），
再换算量词。 -/
theorem comp_not_commutative_witness :
    ∃ A B : MeasurableRule CX SS2 SS2, B.comp A ≠ A.comp B := by
  refine ⟨R₁, R₂, ?_⟩
  intro h
  -- `h` 是 `R₂.comp R₁ = R₁.comp R₂`，直接把它重写到两边的 `rule.kernel` 上
  have hpt : ((R₂.comp R₁).rule.kernel () (0 : Fin 2)) ({1} : Set (Fin 2))
      = ((R₁.comp R₂).rule.kernel () (0 : Fin 2)) ({1} : Set (Fin 2)) := by
    rw [h]
  -- 左边按定义是 `1/2`，右边是 `0`
  rw [R₂compR₁_apply, R₁compR₂_apply] at hpt
  -- `1/2 ≠ 0` 在 `ℝ≥0∞` 中
  exact (by norm_num : (1/2 : ℝ≥0∞) ≠ 0) hpt

/-- ⭐⭐ **主结论**：`Fate.ComposeOperator.MeasurableRule.comp` **不满足交换律**。

即：核复合（边缘化）**不是**交换运算。

$$\lnot\,\forall R_1 R_2,\ R_2\circ R_1 = R_1\circ R_2 .$$

**推论（与 `ComposeSemantics.two_semantics_incompatible` 的关系）**：
「并 + 闭包」可交换（`combClosure_comm`），而本定理说「核复合」不可交换，
**⟹ 二者是不同的运算**（这条已被 `two_semantics_incompatible` 独立证明，
本定理换用**非确定反例**——`ComposeSemantics` §4 登记的那个缺口）。

**⚠ 诚实边界**：本定理**不**主张「所有 ∘ 语义都不可交换」，
也**不**主张「候选 3（并）已被选为唯一正确」——见文件头 (b)(c)。 -/
theorem comp_not_commutative :
    ¬ ∀ R₁ R₂ : MeasurableRule CX SS2 SS2, R₂.comp R₁ = R₁.comp R₂ := by
  intro h
  obtain ⟨a, b, hab⟩ := comp_not_commutative_witness
  exact hab (h a b)

/-- ⭐⭐ **不存在一个既实现核复合（边缘化）又交换的算子**。

  `¬ ∃ comp, (∀ R₁ R₂, comp R₂ R₁ = R₂.comp R₁) ∧ (∀ R₁ R₂, comp R₁ R₂ = comp R₂ R₁)`

**意义**：这把「∘ = 核复合」与「∘ 交换」两个断言的**联合**判为不可能。
它**只**排除了该联合，**不**排除「∘ = 核复合」单独成立。

**证明**：若存在这样的 `comp`，则
`R₂.comp R₁ = comp R₂ R₁ = comp R₁ R₂ = R₁.comp R₂`，
与 `comp_not_commutative` 矛盾。 -/
theorem no_commutative_marginalisation :
    ¬ ∃ comp : MeasurableRule CX SS2 SS2 → MeasurableRule CX SS2 SS2 →
        MeasurableRule CX SS2 SS2,
      (∀ R₁ R₂, comp R₂ R₁ = R₂.comp R₁) ∧ (∀ R₁ R₂, comp R₁ R₂ = comp R₂ R₁) := by
  rintro ⟨comp, hmarg, hcomm⟩
  -- 由 `hmarg` 与 `hcomm` 得到「`comp` 实现了核复合」且「核复合交换」
  apply comp_not_commutative
  intro a b
  -- `b.comp a = comp b a = comp a b = a.comp b`
  calc b.comp a = comp b a := (hmarg a b).symm
    _ = comp a b := hcomm b a
    _ = a.comp b := hmarg b a

/-- 三条定量事实的**打包**（便于下游一次引用，且便于核对数值）。

* `(R₂.comp R₁) … {1} = 1/2`
* `(R₁.comp R₂) … {1} = 0`
* 二者不相等 -/
theorem comp_values :
    (R₂.comp R₁).rule.kernel () (0 : Fin 2) ({1} : Set (Fin 2)) = 1/2
      ∧ (R₁.comp R₂).rule.kernel () (0 : Fin 2) ({1} : Set (Fin 2)) = 0
      ∧ (R₂.comp R₁) ≠ (R₁.comp R₂) :=
  ⟨R₂compR₁_apply, R₁compR₂_apply, by
    intro h
    have hpt : ((R₂.comp R₁).rule.kernel () (0 : Fin 2)) ({1} : Set (Fin 2))
        = ((R₁.comp R₂).rule.kernel () (0 : Fin 2)) ({1} : Set (Fin 2)) := by
      rw [h]
    rw [R₂compR₁_apply, R₁compR₂_apply] at hpt
    exact (by norm_num : (1/2 : ℝ≥0∞) ≠ 0) hpt⟩

end

end FateV2.Rules.CompNotCommutative
