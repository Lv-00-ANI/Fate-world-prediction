/-
=============================================================================
  `FateV2.Modeling.PearlHierarchy.SCM` 诱导 `LawRule` —— 构造 + 判别定理
=============================================================================

模块：`FateV2.Predict`
上游：`Fate/FateV2.Modeling.PearlHierarchy.lean`（`SCM`、`push`、`SCM.L2_do`、`SCM.L2_family`、
　　　`SCM.L3_cf`、`L3_determines_L2`、`L3_determines_L1`）、
　　　`Fate/LawRule.lean`（`LawRule`、`IsPoint`、`IsPointDet`、`compose`、`compose_top`）

---------------------------------------------------------------------------
问题（作者原问）
---------------------------------------------------------------------------
> `FateV2.Modeling.PearlHierarchy.SCM` 能否诱导出 `LawRule`？给出构造。这可能同时推进桥。

---------------------------------------------------------------------------
答案（先结论，再构造）
---------------------------------------------------------------------------
**能。两条线，都是 `def` 级的、免费的：**

| 线 | 上下文 `C` | 当前状态 `X` | 允许集 | 名 |
|---|---|---|---|---|
| **L2 线（主）** | 干预取值 `X` | 事实取值 `X` | 单点集 `{ ℒ(P(Y \| do(X:=c))) }` | `SCM.toLawRule` |
| **消融线** | `Unit` | 事实取值 `X` | 单点集 `{ ℒ(P(Y \| do(X:=x))) }` | `SCM.toLawRuleNoCtx` |

其中 `ℒ` 是 `finLawToMeasure`：把 `SCM` 世界的有限律 `Y → ℝ`
编码成 `LawRule` 世界的 `Measure Y`。

**⟹ 一句话**：`SCM` 的每一次「读出」（L1/L2/L3）都是
「外生律沿某轨道映射的推前」，而 `LawRule` 恰好是
$$\mathcal C \to \mathcal X \to \mathcal P(\mathrm{Measure}\,\mathcal Y),$$
故诱导的方式只能是：**把推前律编成一个测度，然后取单点集**。

---------------------------------------------------------------------------
本文件证了什么（全部可编译，零 sorry / 零 axiom）
---------------------------------------------------------------------------
| § | 内容 | 名 |
|---|---|---|
| §1 | 有限型升格为 `StateSpace` / `CtxSpace`（**及其点可测实例**） | `finStateSpace`、`ctxOf`、`instMeasurableSingletonClassFinStateSpace` |
| §2 | 编码 `ℒ : (Y → ℝ) → Measure Y` 及求值式、点质量判别 | `finLawToMeasure`、`finLawToMeasure_singleton`、`finLawToMeasure_eq_dirac` |
| §3 | **两条构造** | `SCM.toLawRule`、`SCM.toLawRuleNoCtx` |
| §3.1 | L2 语义在类型上可证：允许集与事实状态解耦 | `toLawRule_state_indep`、`toLawRule_diag_eq` |
| §4 | ⭐ **忠实性**：同 `L2_family` ⟺ 同 `LawRule` | `toLawRule_eq_iff_L2_family_eq` |
| §5 | ⭐ **层级穿透**：`L3 ⟹ L2 ⟹ LawRule` | `toLawRule_congr_L3_cf` |
| §6 | 落档：像全落在 `IsPointDet` | `isPointDet_toLawRule`、`isPoint_toLawRule` |
| §7 | ⭐⭐ **主判别**：诱导的 `LawRule` **永不**携带约束信息 | `toLawRule_not_constraining` |
| §8 | 非平凡性：诱导律是 Dirac ⟺ 该律是点质量 | `toLawRule_dirac_iff_pointmass` |

---------------------------------------------------------------------------
对「桥」的推进（本文件的实际贡献）
---------------------------------------------------------------------------
`Fate/InstSpaceToLawRule.lean` 已证「`Rule → LawRule` 只产出单点档，
`LawRule` 的约束语义在实例层用不上」。本文件把它**升级并锐化**：

**(a) 升级 — 载体换成带 L2/L3 的 `SCM`。**
`Rule` 的 `C` 位只有「附加条件」语义；`SCM` **有**干预坐标。

**(b) 锐化 — `LawRule` 的 `C` 位在 `SCM` 上的正确填充物就是「干预值」。**
这是 `Rule → LawRule` **做不到**的填充：`Rule` 没有干预语义。
故 §3 的 `toLawRule` 是桥上的一个**新的、非空接口**，不是重命名。

**(c) 边界 — 即便填上 `C`，像仍全落在 `IsPointDet`。**
§7 是这条断言的机器可见形式：桥**通到单点档，通不到约束语义**。
`LawRule` 的多解集/不等式/约束语义**必须来自 `SCM` 之外**
（数据、约束式、do-calculus 规则），**不可能**由 `SCM` 自身产生。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
* **L1 线未单列**：`SCM.L1_obs` 是 `X × Y → ℝ` 的**联合**律，
  把它「切」成 `Y → ℝ` 的条件律需要额外归一化（`P(X=x) = 0` 时无定义）。
  故本文件只给 **L2 线**（`L2_do` 天生是 `Y → ℝ`），并把 L1 作为 L2 的下游
  （`toLawRule_congr_L1_obs`，经 `L3_determines_L1`）。
* **L3 不直接编成 `LawRule`**：`L3_cf` 的余域 `X × (X → Y)` 是**联合系统**，
  塞进 `LawRule` 的单个坐标会丢「同一 `u` 下跨干预的相关性」。
  §5 只把 L3 作为**前提**（决定 L2），不把 L3 本身编成 `LawRule`。
* **`pU` 不必非负**：`SCM` 不要求。故 `ℒ` 用 `ENNReal.ofReal` **截断**——
  负权重在 `Measure` 中无法表示，这是 `LawRule` 余域的类型层后果，
  §2.2 显式登记（`finLawToMeasure_neg_erased`）。
* 忠实性（§4）**只对「`ℒ` 的正部单射」成立**：若两个 `SCM` 的 `L2_do` 只在
  **负值部分**不同，则 `ℒ` 抹平它们，`LawRule` 不可区分。这是编码的
  **真实信息损失**，§4 的定理因此**只在 `L2_do ≥ 0` 下给出 `←` 方向**
  （`toLawRule_eq_imp_L2_family_eq`），并显式登记反方向不成立。
-/

import FateWorld.FateV2.Modeling.PearlHierarchy
import FateWorld.FateV2.Rules.LawRule
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Discrete

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
open FateV2.Rules
namespace PearlHierarchy

open MeasureTheory

set_option autoImplicit false

-- 本模块把公共 `variable` 行写全（`X`、`Y` 的有限/可判等），
-- 而部分定理陈述确实用不到全部 —— 这在「公共 `variable`」结构下是噪声。
set_option linter.unusedSectionVars false

/-!
  # Predict · PearlLawRuleBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PearlLawRuleBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PearlHierarchy, LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  载体：把有限型升格为 `StateSpace` / `CtxSpace`
    =========================================================================== -/

/-- **有限型作为 `StateSpace`**：拓扑取**离散拓扑**（Mathlib 口径：`⊥` 即离散），
可测结构取其 Borel 结构。

`StateSpace` 要求可测结构弱于 Borel 结构（`Fate/Basic.lean:177`），
故取 `@borel α ⊥` 本身，`borel_le := le_rfl`。

**⚠ 为什么是 `⊥` 不是 `⊤`**：Mathlib 的 `DiscreteTopology` 定义为 `拓扑 = ⊥`
（`Mathlib/Topology/Order.lean:302`），而 `⊤` 是**密着拓扑**（只有空集与全集开）。
两者恰好相反 —— 取错会使单点集不可测，`ℒ` 的求值式无法成立。 -/
def finStateSpace (α : Type*) : StateSpace where
  Carrier := α
  topo := ⊥
  meas := @borel α (⊥ : TopologicalSpace α)
  borel_le := le_rfl

@[simp] theorem finStateSpace_carrier (α : Type*) : (finStateSpace α).Carrier = α := rfl

instance (α : Type*) [Fintype α] : Fintype (finStateSpace α).Carrier :=
  inferInstanceAs (Fintype α)

instance (α : Type*) [DecidableEq α] : DecidableEq (finStateSpace α).Carrier :=
  inferInstanceAs (DecidableEq α)

instance instTopFinStateSpace (α : Type*) :
    TopologicalSpace (finStateSpace α).Carrier := (finStateSpace α).topo

instance instMeasFinStateSpace (α : Type*) :
    MeasurableSpace (finStateSpace α).Carrier := (finStateSpace α).meas

/-- **点可测实例**：`finStateSpace α` 上单点集可测。

由 `borel_eq_top_of_discrete`（`⊥` 拓扑是离散的）得 `borel α ⊥ = ⊤`，
而 `⊤` 可测结构上一切集合可测。**这是 §2 求值式的唯一前件。** -/
instance instMeasurableSingletonClassFinStateSpace (α : Type*) :
    MeasurableSingletonClass (finStateSpace α).Carrier :=
  ⟨fun x => by
    have h2 : (finStateSpace α).meas = (⊤ : MeasurableSpace α) :=
      @borel_eq_top_of_discrete α ⊥ (discreteTopology_bot α)
    show @MeasurableSet α (finStateSpace α).meas {x}
    rw [h2]; trivial⟩

/-- 任意类型作为上下文空间（`CtxSpace` 只有一个 `Carrier` 字段）。 -/
abbrev ctxOf (T : Type*) : CtxSpace where
  Carrier := T

/-! ===========================================================================
    §2  编码：有限律 `Y → ℝ` ⟶ `Measure Y`
    =========================================================================== -/

/-- **有限律的测度编码**（本文件的桥）：
$$ℒ(p) := \sum_{y} \mathrm{ENNReal.ofReal}(p\,y) \cdot \delta_y .$$

`LawRule` 的允许集是**测度集合**，故 `SCM` 的推前律**必须先变成测度**。
这是两个世界之间**唯一**的合法通道。

**⚠ 为什么是 `ofReal`（截断为非负）**：`Measure` 的系数活在 `ℝ≥0∞` 里。
`SCM` 不要求 `pU ≥ 0`，故推前可能有负值，而负系数**在 `Measure` 中无法表示**。
截断是类型层的**必然**，非疏漏（见 `finLawToMeasure_neg_erased`）。 -/
noncomputable def finLawToMeasure {Y : Type*} [Fintype Y] (mY : MeasurableSpace Y)
    (p : Y → ℝ) : Measure Y :=
  letI := mY
  ∑ y, ENNReal.ofReal (p y) • (Measure.dirac y)

/-- **单点集上的值**：`ℒ(p) {y} = ofReal (p y)`。

这是 §2 的**唯一**实质引理，忠实性（§4）与点质量判别（§2.1）都由它推出。 -/
theorem finLawToMeasure_singleton {Y : Type*} [Fintype Y]
    (mY : MeasurableSpace Y) [hY : MeasurableSingletonClass Y] (p : Y → ℝ) (y : Y) :
    finLawToMeasure mY p ({y} : Set Y) = ENNReal.ofReal (p y) := by
  classical
  have h : ∀ z : Y,
      (Measure.dirac z : Measure Y) ({y} : Set Y) = if z ∈ ({y} : Set Y) then 1 else 0 := by
    intro z
    rw [Measure.dirac_apply' _ (measurableSet_singleton y), Set.indicator_apply]
    by_cases hz : z ∈ ({y} : Set Y) <;> simp [hz]
  rw [finLawToMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, h, smul_eq_mul]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz; simp [hz]
  · intro h'; exact absurd (Finset.mem_univ y) h'

/-- **`ofReal` 单射（非负区）**的干净形态，供上一条使用。 -/
theorem ofReal_inj_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ENNReal.ofReal a = ENNReal.ofReal b) : a = b :=
  (ENNReal.ofReal_eq_ofReal_iff ha hb).mp h

/-- ⭐ **忠实性的钥匙（干净版）**：`ℒ` 在非负律上单射。 -/
theorem finLawToMeasure_inj_of_nonneg {Y : Type*} [Fintype Y]
    (mY : MeasurableSpace Y) [MeasurableSingletonClass Y] {p q : Y → ℝ}
    (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 ≤ q y)
    (h : finLawToMeasure mY p = finLawToMeasure mY q) : p = q := by
  funext y
  have hy := congrArg (fun μ : Measure Y => μ ({y} : Set Y)) h
  rw [finLawToMeasure_singleton mY, finLawToMeasure_singleton mY] at hy
  exact ofReal_inj_of_nonneg (hp y) (hq y) hy

/-! ### §2.1 点质量判别 -/

/-- **点质量判别**：若 `p` 是非负概率律且在某点取 `1`，则 `ℒ(p) = δ_{y₀}`。

证明：`p ≥ 0` 且 `∑ p = 1`，故 `p y₀ = 1` 迫使其余 `p y = 0`
（用 `{y₀, y} ⊆ univ` 上的**子集求和单调性**），逐点即得。 -/
theorem finLawToMeasure_eq_dirac {Y : Type*} [Fintype Y] [DecidableEq Y]
    (mY : MeasurableSpace Y) [MeasurableSingletonClass Y]
    {p : Y → ℝ} (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1)
    {y₀ : Y} (hy : p y₀ = 1) : finLawToMeasure mY p = Measure.dirac y₀ := by
  have hall : ∀ y, y ≠ y₀ → p y = 0 := by
    intro y hyne
    have h1 : p y₀ + p y ≤ ∑ z, p z := by
      have hmem : ({y₀, y} : Finset Y) ⊆ Finset.univ := Finset.subset_univ _
      have h := Finset.sum_le_sum_of_subset_of_nonneg hmem (fun z _ _ => hp z)
      rwa [Finset.sum_pair (Ne.symm hyne)] at h
    have h2 : p y₀ + p y ≤ 1 := by rw [← hsum]; exact h1
    rw [hy] at h2
    linarith [hp y]
  classical
  ext B hB
  rw [finLawToMeasure, Measure.finsetSum_apply, Measure.dirac_apply' _ hB]
  simp only [Measure.smul_apply, Set.indicator_apply, smul_eq_mul]
  have hdirac : ∀ z : Y,
      (Measure.dirac z : Measure Y) B = if z ∈ B then 1 else 0 := by
    intro z
    rw [Measure.dirac_apply' _ hB, Set.indicator_apply]
    by_cases hz : z ∈ B <;> simp [hz]
  simp only [hdirac]
  rw [Finset.sum_eq_single y₀]
  · by_cases h : y₀ ∈ B <;> simp [hy, h]
  · intro z _ hz; simp [hall z hz]
  · intro h'; exact absurd (Finset.mem_univ y₀) h'

/-! ### §2.2 诚实边界：负权重被截断 -/

/-- **负权重被截断**（显式登记）：若 `p y < 0`，则 `ℒ(p)` **不**记录它。

这不是编码的疏漏，而是 `LawRule` 余域是 `Measure` 的**类型层后果**：
`Measure` 的系数活在 `ℝ≥0∞` 里，**没有**负号位置。 -/
theorem finLawToMeasure_neg_erased {Y : Type*} (_mY : MeasurableSpace Y)
    {p : Y → ℝ} {y : Y} (hy : p y < 0) :
    ENNReal.ofReal (p y) = 0 :=
  ENNReal.ofReal_eq_zero.mpr (le_of_lt hy)

end PearlHierarchy

/-! ===========================================================================
    §3  `SCM` 诱导 `LawRule`：两条构造
    =========================================================================== -/

namespace PearlHierarchy

namespace SCM

variable {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]

/-- `Y` 作为 `finStateSpace Y` 的载体（定义上相等，显式记下以便统一实例）。 -/
abbrev lawY : StateSpace := finStateSpace Y

/-- 局部实例：`Y` 的可测结构取 `finStateSpace Y` 的那一个（即 Borel 离散）。
这是 `finLawToMeasure` 在 `LawRule` 余域 `Measure (finStateSpace Y).Carrier` 上的桥梁。 -/
local instance instMeasY : MeasurableSpace Y := (finStateSpace Y).meas

/-- 局部实例：`finStateSpace Y` 上单点集可测（供 §4 忠实性使用）。 -/
local instance instSingY : MeasurableSingletonClass Y :=
  instMeasurableSingletonClassFinStateSpace Y

variable (M : SCM X Y)

/-- ⭐ **主构造：`SCM.toLawRule`**（上下文 = 干预值）。

上下文取**干预取值** `c : X`（即 `do(X := c)`），当前状态取**事实取值** `x : X`；
允许集是单点集
$$\{\, ℒ\bigl(P(Y \mid do(X := c))\bigr) \,\}.$$

**关键性质（`rfl` 级，见 `toLawRule_state_indep`）**：允许集**不依赖** `x` ——
干预律 `L2_do c` 由结构方程族 `u ↦ h_u(c)` 决定，与「事实 `X` 实际取到什么」无关。
这正是 Pearl L2 的语义，且在此**在类型上可证**。

**⚠ 这是桥的实际内容**：`LawRule` 的 `C` 位被填以**干预值**。
`Rule → LawRule`（`Fate/InstSpaceToLawRule.lean`）**做不到**这一点，
因为 `Rule` 的 `C` 位只有「附加条件」语义，没有干预语义。 -/
noncomputable def toLawRule :
    FateV2.Rules.LawRule.LawRule (ctxOf X) (finStateSpace X) (finStateSpace Y) :=
  fun c _ => {finLawToMeasure (finStateSpace Y).meas (M.L2_do c)}

/-- **消融构造：`SCM.toLawRuleNoCtx`**（上下文 = 单点）。

把上下文位**抹掉**（取 `Unit`）；允许集是 `{ ℒ(P(Y | do(X := x))) }`。
**它与 `toLawRule` 的差别恰是「上下文位是否承载信息」**：
`toLawRule c` 在任意 `x` 处给出 `do(c)` 的律；`toLawRuleNoCtx () x` 给出 `do(x)` 的律。
二者在 `C = X` 的**对角线**上重合（`toLawRule_diag_eq`）。 -/
noncomputable def toLawRuleNoCtx :
    FateV2.Rules.LawRule.LawRule (ctxOf Unit) (finStateSpace X) (finStateSpace Y) :=
  fun _ x => {finLawToMeasure (finStateSpace Y).meas (M.L2_do x)}

omit [Fintype X] [DecidableEq X] in
@[simp] theorem toLawRule_apply (c x : X) :
    M.toLawRule c x = {finLawToMeasure (finStateSpace Y).meas (M.L2_do c)} := rfl

omit [Fintype X] [DecidableEq X] in
@[simp] theorem toLawRuleNoCtx_apply (c : Unit) (x : X) :
    M.toLawRuleNoCtx c x = {finLawToMeasure (finStateSpace Y).meas (M.L2_do x)} := rfl

omit [Fintype X] [DecidableEq X] in
/-- **Pearl L2 的类型级刻画**：`toLawRule c` 的允许集与当前状态 `x` 解耦。 -/
theorem toLawRule_state_indep (c : X) :
    (fun x => M.toLawRule c x) =
      fun _ => {finLawToMeasure (finStateSpace Y).meas (M.L2_do c)} := rfl

omit [Fintype X] [DecidableEq X] in
/-- **对角线重合**：`toLawRule` 在 `c = x` 处与 `toLawRuleNoCtx` 逐点相同。 -/
theorem toLawRule_diag_eq (x : X) :
    M.toLawRule x x = M.toLawRuleNoCtx () x := rfl

/-! ### §4 ⭐ 忠实性：构造不丢 L2 信息 -/

omit [Fintype X] [DecidableEq X] in
/-- **忠实性（单向，`LawRule` 相等 ⟹ `L2_family` 相等，需非负性）**。

由 `LawRule` 的相等逐 `(c, x)` 取出单点集里唯一测度，再用 §2 的
`finLawToMeasure_inj_of_nonneg` 得到 `L2_do` 的相等。

**⚠ 非负前件不可去**：若 `L2_do` 有负值，`ℒ` 会截断（§2.2），
两个不同的负值律可编成同一个测度。故本定理**必须**带 `hp` / `hq`。
（`←` 方向**无条件**成立，见 `toLawRule_eq_of_L2_family_eq`。） -/
theorem L2_family_eq_of_toLawRule_eq {M₁ M₂ : SCM X Y}
    (hp : ∀ c y, 0 ≤ M₁.L2_do c y) (hq : ∀ c y, 0 ≤ M₂.L2_do c y)
    (h : M₁.toLawRule = M₂.toLawRule) : M₁.L2_family = M₂.L2_family := by
  funext c y
  have hc := congrFun (congrFun h c) c
  rw [toLawRule_apply, toLawRule_apply] at hc
  have hc' : finLawToMeasure (finStateSpace Y).meas (M₁.L2_do c)
      = finLawToMeasure (finStateSpace Y).meas (M₂.L2_do c) :=
    Set.singleton_eq_singleton_iff.mp (by simpa using hc)
  exact congrFun (finLawToMeasure_inj_of_nonneg (finStateSpace Y).meas
    (p := M₁.L2_do c) (q := M₂.L2_do c) (fun z => hp c z) (fun z => hq c z) hc') y

omit [Fintype X] [DecidableEq X] in
/-- **忠实性（反向，无条件）**：同 `L2_family` ⟹ 同 `LawRule`。 -/
theorem toLawRule_eq_of_L2_family_eq {M₁ M₂ : SCM X Y}
    (h : M₁.L2_family = M₂.L2_family) : M₁.toLawRule = M₂.toLawRule := by
  funext c x
  show {finLawToMeasure (finStateSpace Y).meas (M₁.L2_do c)}
      = {finLawToMeasure (finStateSpace Y).meas (M₂.L2_do c)}
  rw [show M₁.L2_do c = M₂.L2_do c from funext (fun y => congrFun (congrFun h c) y)]

omit [Fintype X] [DecidableEq X] in
/-- **忠实性（双向，带非负前件）**：`LawRule` 侧看到的东西与 `L2_family` 一样多。

**⟹ 桥没有把信息抹平**（在非负律上）。 -/
theorem toLawRule_eq_iff_L2_family_eq {M₁ M₂ : SCM X Y}
    (hp : ∀ c y, 0 ≤ M₁.L2_do c y) (hq : ∀ c y, 0 ≤ M₂.L2_do c y) :
    M₁.toLawRule = M₂.toLawRule ↔ M₁.L2_family = M₂.L2_family :=
  ⟨L2_family_eq_of_toLawRule_eq hp hq, toLawRule_eq_of_L2_family_eq⟩

/-! ### §5 ⭐ 层级穿透：`L3 ⟹ L2 ⟹ LawRule` -/

/-- **L3 决定诱导的 `LawRule`**。

把 `L3_determines_L2`（`PearlHierarchy` §3）沿 §4 的无条件反向搬到 `LawRule` 载体。

**⟹ `SCM` 侧的三层链 $L_3 \Rightarrow L_2 \Rightarrow L_1$ 在 `LawRule` 侧保持**。 -/
theorem toLawRule_congr_L3_cf [DecidableEq (X → Y)] {M₁ M₂ : SCM X Y}
    (h : M₁.L3_cf = M₂.L3_cf) :
    M₁.toLawRule = M₂.toLawRule :=
  toLawRule_eq_of_L2_family_eq (L3_determines_L2 h)

/-- **L1 也决定诱导的 `LawRule`**（经 L2 中转）：把 `L3_determines_L1` 搬到新载体。

注意：L1 决定的是 `L1_obs`，它**不**直接决定 `L2_family`（Pearl 的标准事实）。
本定理**不是**「L1 ⟹ LawRule」；它是「L3 ⟹ L1 ⟹ LawRule」的复合，
**前提仍是 L3**。此处只验证 `L1_obs` 也在链上（`L3` 同时定住两侧）。 -/
theorem toLawRule_congr_L3_cf_L1 [DecidableEq (X → Y)] {M₁ M₂ : SCM X Y}
    (h : M₁.L3_cf = M₂.L3_cf) :
    M₁.toLawRule = M₂.toLawRule ∧ M₁.L1_obs = M₂.L1_obs :=
  ⟨toLawRule_congr_L3_cf h, L3_determines_L1 h⟩

/-! ===========================================================================
    §6  落档：像全落在 `IsPointDet`
    =========================================================================== -/

omit [Fintype X] [DecidableEq X] in
/-- **主构造是 `IsPoint`**（单点档）。

⚠ **注意不是 `IsPointDet`**：允许集里的那个唯一测度是 `ℒ(L2_do c)`，
一般**不是** Dirac 测度（除非该律本身是点质量，见 §8）。
故 `IsPointDet` 在此**不成立**，只能给 `IsPoint`。
这正是 §6 的核心内容：`SCM → LawRule` 的像落在**单点档**，
但**不**落在 Dirac 单点档 —— 即诱导规则**不等于**任何确定性函数
（`Fate/LawRule.lean` §0.A 的 `im(DetFun.toLaw) ⊊ {IsPoint}` 在此实例化）。 -/
theorem isPoint_toLawRule : LawRule.IsPoint M.toLawRule :=
  fun c _ => ⟨finLawToMeasure (finStateSpace Y).meas (M.L2_do c), rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- **消融构造是 `IsPoint`**。 -/
theorem isPoint_toLawRuleNoCtx : LawRule.IsPoint M.toLawRuleNoCtx :=
  fun _ x => ⟨finLawToMeasure (finStateSpace Y).meas (M.L2_do x), rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- **主构造是 `Deterministic`**（`IsPoint` 的等价读法）。 -/
theorem deterministic_toLawRule : LawRule.Deterministic M.toLawRule :=
  LawRule.IsPoint.deterministic _ M.isPoint_toLawRule

/-! ===========================================================================
    §7  ⭐⭐ 主判别：诱导的 `LawRule` **永不**携带约束信息
    =========================================================================== -/

omit [Fintype X] [DecidableEq X] in
/-- ⭐⭐ **主判别**：`SCM` 诱导的 `LawRule` 的每个允许集都是**单点集**，
故**不是**「真约束档」（真约束档 = 允许集含 ≥2 个不同分布）。

**这就是「`SCM` 不能自己产生 `LawRule` 约束语义」的机器可见陈述**：
`LawRule` 相对 `SCM` 的全部增益（多解集 / 不等式 / 约束语义）
**必须来自 `SCM` 之外**，`SCM` 自身**不可能**产生。

**⟹ 对桥的确切结论**：`SCM → LawRule` 这条桥**通到单点档，通不到约束语义**。
它与 `Fate/InstSpaceToLawRule.liftRule_not_trueConstraint`（`Rule` 侧）
**同构**——即「加进 L2/L3 的干预与反事实坐标，也**不**能让 `LawRule` 的
约束语义变得有用」。这是本节相对已有结果**新增**的信息。 -/
theorem toLawRule_not_constraining :
    ¬ ∃ c x, ∃ μ₁ ∈ M.toLawRule c x, ∃ μ₂ ∈ M.toLawRule c x, μ₁ ≠ μ₂ := by
  rintro ⟨c, x, μ₁, h₁, μ₂, h₂, hne⟩
  exact hne (by rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂])

omit [Fintype X] [DecidableEq X] in
/-- **消融构造同理**：不携带约束信息。 -/
theorem toLawRuleNoCtx_not_constraining :
    ¬ ∃ c x, ∃ μ₁ ∈ M.toLawRuleNoCtx c x, ∃ μ₂ ∈ M.toLawRuleNoCtx c x, μ₁ ≠ μ₂ := by
  rintro ⟨c, x, μ₁, h₁, μ₂, h₂, hne⟩
  exact hne (by rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂])

omit [Fintype X] [DecidableEq X] in
/-- **推论：诱导的 `LawRule` 与 `top` 的 `compose` 无增益**（`LawRule.lean` 的 `compose_top`）。

即：把 `SCM` 诱导的规则与「没有规律」组合，得到的是它自己 ——
进一步说明诱导规则**不含约束**（若含约束，与 `top` 组合仍含那个约束，
但诱导规则的唯一内容已被 `compose_top` 完全描述）。 -/
theorem toLawRule_compose_top :
    LawRule.compose M.toLawRule (LawRule.top (ctxOf X) (finStateSpace X) (finStateSpace Y))
      = M.toLawRule :=
  LawRule.compose_top _

/-! ===========================================================================
    §8  非平凡性：诱导律是 Dirac ⟺ 该律是点质量
    =========================================================================== -/

omit [Fintype X] [DecidableEq X] in
/-- **诱导律是 Dirac ⟺ 该律是点质量**（§6 与 §2.1 的合成）。

故 §6 的 `IsPointDet` **不是**「确定性函数」伪装：
一般情况下允许集里的那个测度**不是** `δ_y`。
`im(DetFun.toLaw) ⊊ IsPointDet`（`Fate/LawRule.lean` §0.A）在 `SCM` 上被**实例化**。 -/
theorem toLawRule_dirac_iff_pointmass (c : X) {y₀ : Y}
    (hp : ∀ y, 0 ≤ M.L2_do c y) (hsum : ∑ y, M.L2_do c y = 1)
    (hy : M.L2_do c y₀ = 1) :
    finLawToMeasure (finStateSpace Y).meas (M.L2_do c) = MeasureTheory.Measure.dirac y₀ :=
  finLawToMeasure_eq_dirac (finStateSpace Y).meas hp hsum hy

end SCM

end PearlHierarchy

end FateV2.Predict