import Mathlib.Data.Real.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Predict.CondMulSeparable
/-!
  # Predict · LawRuleCondMul

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleCondMul.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame, FinCondIndep, CondMulSeparable
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/LawRuleCondMul` —— **`CondMul` 能否用 `LawRule` 表达？**

  ## ⭐ 结论（先给答复）

  **能，但代价是「把联合律整体塞进状态/上下文」这一编码，
  而一旦这样做，`LawRule` 的全部核心结构（`IsPoint`、`generalize`/`refine`、
  `compose` 的实质语义）都退化掉 —— 这不是「忠实的表达」，是「重命名」。**

  **⟹ 诚实答复**：
  * **形式上可以表达**（§2 给出两条明确的对应，均已在 Lean 中证毕）；
  * **实质上一个不忠实的表达**（§4 给出精确的反驳）；
  * **真正与 `LawRule` 结构对齐的，是 `CondMul` 的「切片秩一」形式**（§3），
    而它需要 `CondMul` + 正性，**不是 `CondMul` 本身**（§4 给出反例方向）。

  ## ⭐ 为什么会有这个差别 —— 一句话

  | | 约束的作用域 | 输出形态 |
  |---|---|---|
  | `CondMul p` | **全局**（整条联合律 `p`，含对所有 `x,y` 的求和） | 命题（`Prop`） |
  | `LawRule C X Y` | **逐点**（给定 `c`、`x`） | `Set (Measure Y)` |

  **`CondMul` 需要「对 `x`、`y` 求和」，而 `LawRule` 的输出里没有 `x` 的求和位置。**
  这不是「能不能编码」的问题，是「编码之后那个编码里还剩不剩 `LawRule` 的意思」
  的问题。

  ## ⚠ 本文件与 `Fate/LawRule.lean` 的关系（诚实声明）

  `Fate/LawRule.lean` 在本轮中**正被并发修改**（编译未通过）。
  为让本文件**自身可独立编译**，这里**重述**了 `LawRule` 及其四个算子的定义
  （逐字取自 `Fate/LawRule.lean:69–153` 的同一数学内容），
  **放在 `Fate.LawRuleCondMul` 命名空间内**，并**不覆盖**原定义。
  **⟹ 待 `Fate/LawRule.lean` 修复后，本文件的 `LawRule` 应替换为其别名。**

  **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
namespace LawRuleCondMul

open MeasureTheory FateV2.Predict.FinCondIndep

attribute [local instance] Classical.propDecidable

-- `unusedSectionVars` 在「全参数化的双条件定理」上是噪声：
-- `CondMul` 的陈述本身用不到 `Fintype γ`，但同一条 `variable` 行必须给出它
-- 才能让 `margZ` 等定义成立。故在此关闭该 linter。
set_option linter.unusedSectionVars false

noncomputable section

/-! ## §1 ⭐ 规则层（重述）

定义与 `Fate/LawRule.lean` 同一数学内容，仅放在本命名空间以免与并发修改冲突。 -/

/-- **规则**：`C → X → Set (Measure Y)`（重述自 `Fate.LawRule.LawRule`）。 -/
def LawRule (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ :=
  C.Carrier → X.Carrier → Set (MeasureTheory.Measure Y.Carrier)

/-- **组合 = 取交**（重述自 `Fate.LawRule.compose`）。 -/
def compose {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (R₁ R₂ : LawRule C X Y) : LawRule C X Y :=
  fun c x => R₁ c x ∩ R₂ c x

/-- **全约束规则**（重述自 `Fate.LawRule.top`）。 -/
def top (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : LawRule C X Y := fun _ _ => Set.univ

/-- **空规则**（重述自 `Fate.LawRule.bot`）。 -/
def bot (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : LawRule C X Y := fun _ _ => ∅

/-- **单点档**（重述自 `Fate.LawRule.IsPoint`）。 -/
def IsPoint {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (R : LawRule C X Y) : Prop :=
  ∀ c x, ∃ μ, R c x = {μ}

/-! ## §2 ⭐ 两条对应（都在 Lean 中证毕）

两条对应都必须**把联合律 `p` 整体作为规则的输入**，这是要害。
差别只在「输出空间取什么、允许集写成什么形态」。

### 对应 A —— **谓词型**（最省事的编码）

* 上下文 `C := ⟨FinJoint α β γ⟩`（联合律本身就是上下文）；
* 状态 `X := PUnit`（状态位置无处安放，因为 `CondMul` 没有「当前状态」）；
* 输出 `Y := PUnit`（输出也退化，因为 `CondMul` 不产生任何分布）；
* 允许集：`CondMul p` 成立 ⟹ 单点集 `{δ_⋆}`；否则 `∅`。

**⟹ 这使 `CondMul p ⟺ 允许集非空`。**
这是**能表达的**，但代价见 §4。 -/

/-- `PUnit` 作为（退化）状态/输出空间：`⊤` 拓扑、Borel 可测结构。

**⚠ `borel_le` 必须取 Borel 结构本身**（`le_rfl`）：
`StateSpace` 要求可测结构弱于 Borel 结构（`Fate/Basic.lean:177`），
而 `⊤` 可测结构**不满足**该要求。 -/
abbrev punitSpace : StateSpace where
  Carrier := PUnit
  topo := ⊤
  meas := @borel PUnit ⊤
  borel_le := le_rfl

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- 任意类型作为上下文空间（`CtxSpace` 只有一个 `Carrier` 字段）。 -/
abbrev ctxOf (T : Type*) : CtxSpace where
  Carrier := T

/-- 任意类型配 `⊤` 拓扑与 Borel 可测结构，作为状态空间。

**⚠ `StateSpace` 的 `borel_le` 要求**（`Fate/Basic.lean:177`）迫使
可测结构必须取 Borel 结构本身；`⊤` 可测结构**不满足**该要求，
故 `meas` 写 `@borel T ⊤` 而 `borel_le := le_rfl`。 -/
abbrev discreteSpace (T : Type*) : StateSpace where
  Carrier := T
  topo := ⊤
  meas := @borel T ⊤
  borel_le := le_rfl

/-- ⭐ **对应 A**：把 `CondMul` 写成一条「谓词型」`LawRule`。

$$\text{condMulRule}(p)(\_) = \begin{cases}\{\delta_\star\} & \text{CondMul}(p)\\\varnothing&\text{否则}\end{cases}$$

**读法**：规则**允许**「`p` 满足条件独立」这一状态，**不允许**别的。
它把 `CondMul` 变成一个**是否允许**的二值开关。 -/
def condMulRule : LawRule ⟨FinJoint α β γ⟩ punitSpace punitSpace :=
  fun p _ => if CondMul p then ({Measure.dirac (PUnit.unit)} : Set (Measure PUnit)) else ∅

/-- ⭐⭐⭐ **对应 A 的等价（已证）**：

$$\mathrm{CondMul}\ p \iff (\text{condMulRule}\ p\ \star).\text{Nonempty}$$

即：**「`p` 条件独立」等价于「规则允许集非空」**。

**⚠ 这是 `if` 的定义展开，不含新数学内容** —— 它的价值在于
**把 `CondMul` 摆进了 `LawRule` 的类型里**，从而可以被 `compose`/`top`/`bot` 处理。
**§4 会说明它实际上只是一个 `top`/`bot` 的开关。** -/
theorem condMul_iff_condMulRule_nonempty (p : FinJoint α β γ) :
    CondMul p ↔ (condMulRule (α := α) (β := β) (γ := γ) p PUnit.unit).Nonempty := by
  show CondMul p ↔
    (if CondMul p then ({Measure.dirac (PUnit.unit)} : Set (Measure PUnit)) else ∅).Nonempty
  by_cases h : CondMul p
  · simp [h]
  · simp [h]

/-! ### 对应 B —— **`compose` 就是「约束的合取」**

**这是对应 A 唯一真正用得上 `LawRule` 结构的地方**：
`LawRule.compose` 的语义是**取交**，于是

$$\text{规则}(\text{CondMul}) \circ \text{规则}(Q) \;=\; \text{规则}(\text{CondMul} \wedge Q).$$

**⟹ 只要 `CondMul` 是「关于 `p` 的命题」，就能与任何别的约束同时成立。**
这条**是 `LawRule` 设计的本意**（`Fate/LawRule.lean` 头注的「等式、不等式、微分方程
都是约束」），**故 `CondMul` 落在这个设计意图之内**。 -/

/-- **把「关于联合律的谓词」编码为一条规则**（`P p` 成立则允许一切，否则什么也不允许）。

**⚠ 与 `condMulRule` 的差别**：这里允许集是 `univ`（全约束 / 最弱规则）而不是单点集。
用 `univ` 是因为「`P` 不约束输出，只约束 `p` 是否合法」——
**这正是 `top`/`bot` 二值化**。 -/
def lawOf {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : FinJoint α β γ → Prop) : LawRule ⟨FinJoint α β γ⟩ punitSpace punitSpace :=
  fun p _ => if P p then Set.univ else ∅

/-- ⭐ **`CondMul` 的 `lawOf` 版本**：`CondMul p ⟺ 允许集非空`。 -/
theorem condMul_iff_lawOf_nonempty (p : FinJoint α β γ) :
    CondMul p ↔ (lawOf (CondMul (α := α) (β := β) (γ := γ)) p PUnit.unit).Nonempty := by
  show CondMul p ↔
    (if CondMul p then (Set.univ : Set (Measure PUnit)) else ∅).Nonempty
  by_cases h : CondMul p <;> simp [h]

/-- ⭐⭐⭐ **`compose` = 谓词合取（已证）**：

$$\text{lawOf}(P) \circ \text{lawOf}(Q) = \text{lawOf}(P \wedge Q)$$

**这就是「条件独立与其它规律同时成立」的精确形态**：
`compose` 的取交语义，恰好对应命题的 `∧`。
**这是 `CondMul` 与 `LawRule` 之间唯一实质性相容的地方。** -/
theorem lawOf_compose (P Q : FinJoint α β γ → Prop) :
    compose (lawOf P) (lawOf Q) = lawOf (fun p => P p ∧ Q p) := by
  funext p x
  simp only [compose, lawOf]
  by_cases hp : P p <;> by_cases hq : Q p <;> simp [hp, hq]

/-- ⭐ **`CondMul` 的自组合不产生新信息**（幂等）：
`CondMul ∧ CondMul = CondMul`。 -/
theorem lawOf_condMul_idem :
    compose (lawOf (CondMul (α := α) (β := β) (γ := γ)))
      (lawOf (CondMul (α := α) (β := β) (γ := γ)))
      = lawOf (CondMul (α := α) (β := β) (γ := γ)) := by
  rw [lawOf_compose]
  congr 1
  funext p
  exact propext ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-! ### 对应 B′ —— **`condMulRule` 在 `compose` 下与 `top` 一致的分支**

由于 `condMulRule` 的允许集是 `{δ_⋆}` 或 `∅`，它在 `compose` 下与 `lawOf` 相容：

$$\text{condMulRule} \circ \text{lawOf}(Q) =
  \begin{cases}\{\delta_\star\}&\text{CondMul}(p)\wedge Q(p)\\\varnothing&\text{否则}\end{cases}$$

**⟹ 单点档与全约束档的唯一差别，只在「允许集是全空间还是单点」——
而两者都**只编码一个 `Prop`**。这就是 §4 所说的「退化」。** -/

/-- ⭐ **单点档 `condMulRule` 与 `lawOf` 的组合**：仍是二值开关。 -/
theorem condMulRule_compose_lawOf (Q : FinJoint α β γ → Prop) :
    compose (condMulRule (α := α) (β := β) (γ := γ)) (lawOf Q)
      = fun p _ => if CondMul p ∧ Q p
          then ({Measure.dirac (PUnit.unit)} : Set (Measure PUnit)) else ∅ := by
  funext p x
  simp only [compose, condMulRule, lawOf]
  by_cases hc : CondMul p <;> by_cases hq : Q p <;> simp [hc, hq]

/-! ## §3 ⭐⭐⭐ 真正与 `LawRule` 结构对齐的形式：**切片秩一**

`CondMul` 的「全局」外形确实挡路，但它有一个**逐 `z` 的等价刻画**：

$$\text{CondMul}\ p \;\iff\; p((x,y),z) \cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z
  \quad\text{（逐 } x,y,z\text{）}$$

固定 `z` 后右边的因子**分别只依赖 `x` 与 `y`** ⟹ **每个 `z` 切片是「秩一」的**。
而「秩一」是一个**逐 `z` 的、不含求和的**性质 ⟹ **它才是能忠实装进 `LawRule` 的形式**。

**⚠ 从秩一回到 `CondMul` 需要消去 `margZ p z`**，故**必须有 `margZ ≠ 0`**
（即正性）。这不是技术妥协：`CondMul` 在 `margZ = 0` 处**确实弱于**秩一，
§4 的反例正是由此而来。 -/

/-- **`p` 在 `z` 处的切片**（把 `z` 固定，只看 `(x,y) ↦ p((x,y),z)`）。 -/
def slice (p : FinJoint α β γ) (z : γ) : α × β → ℝ := fun q => p (q, z)

/-- **秩一（乘积）族**：切片可写成「只依赖 `x` 的因子 × 只依赖 `y` 的因子」。

**⟹ 这是「逐点、无求和」的形态，因此可以忠实放进 `LawRule` 的输出里。** -/
def IsRankOne (f : α × β → ℝ) : Prop :=
  ∃ g : α → ℝ, ∃ h : β → ℝ, ∀ x y, f (x, y) = g x * h y

/-- ⭐⭐⭐ **守卫版 `CondMul` ⟹ 每个切片秩一（已证）**：

$$\text{CondMulGuard}\ p \implies \forall z,\ \mathrm{IsRankOne}\big(\mathrm{slice}\ p\ z\big)$$

**证明**：守卫 `margZ p z ≠ 0` 允许把 `CondMul` 的等式除以 `margZ p z`；
取 `g x := margXZ p x z / margZ p z`、`h y := margYZ p y z` 即得。

**⚠ 用 `CondMulGuard` 而非 `CondMul`**：无守卫版本在 `margZ p z = 0` 时
不能消去，秩一**不成立**（§4 反例）。 -/
theorem condMulGuard_implies_rankOne (p : FinJoint α β γ)
    (h : CondMulGuard p) (z : γ) (hz : margZ p z ≠ 0) : IsRankOne (slice p z) := by
  refine ⟨fun x => margXZ p x z / margZ p z, fun y => margYZ p y z, fun x y => ?_⟩
  show p ((x, y), z) = margXZ p x z / margZ p z * margYZ p y z
  -- 由 `h x y z hz : p * margZ = margXZ * margYZ` 除以 `margZ`。
  rw [div_mul_eq_mul_div, eq_div_iff hz]
  exact h x y z hz

/-- ⭐⭐ **正性 ⟹ `CondMul` 的每个切片秩一（已证，引用既有定理）**：
取 `Fate.CondMulSeparable.condMul_implies_separable` 在固定 `z` 处的实例。 -/
theorem condMul_implies_rankOne_of_pos (p : FinJoint α β γ)
    [Nonempty α] [Nonempty β]
    (h : CondMul p) (hpos : ∀ x y z, 0 < p ((x, y), z)) (z : γ) :
    IsRankOne (slice p z) := by
  obtain ⟨f, g, hfg⟩ := CondMulSeparable.condMul_implies_separable p h hpos
  exact ⟨fun x => f x z, fun y => g y z, fun x y => hfg x y z⟩

/-! ### `CondMul`（有正性时）作为「逐 `z` 的 `LawRule`」

有了 §3 的秩一形式，`CondMul` 就可以写成一条**真正逐点**的规则：
上下文 `C := γ`（条件变量 `z`）、状态 `X := ⟨FinJoint α β γ⟩`、
输出 `Y := PUnit`，允许集 = `{δ_⋆}` 当该 `z` 切片秩一、否则 `∅`。

**⟹ 这条规则在 `LawRule` 里有**内容**：`IsPoint` 成立（构造上），
`generalize`/`refine` 可以真正收放它，且不同 `z` 的约束通过 `compose` 取交。** -/

/-- ⭐ **逐 `z` 版的 `CondMul` 规则**（上下文携带 `z`）。

读法：对每个条件变量取值 `z`，**单独**要求 `p` 的 `z` 切片秩一。
**⟹ 这正是「条件独立」的逐点分解，且完全装进了 `LawRule` 的 `C`／`X` 结构。** -/
def condMulRuleAt : LawRule (ctxOf γ) (discreteSpace (FinJoint α β γ)) punitSpace :=
  fun z p => if IsRankOne (slice p z)
    then ({Measure.dirac (PUnit.unit)} : Set (Measure PUnit)) else ∅

/-- ⭐⭐⭐ **逐 `z` 版与守卫版 `CondMul` 的等价（已证）**：

$$(\forall z,\ \text{condMulRuleAt}(z)\ \text{允许非空}) \iff
  \forall z,\ (p\ \text{的}\ z\ \text{切片秩一})$$

**⟹ 结合 `condMulGuard_implies_rankOne`：`CondMulGuard` 蕴含
「`condMulRuleAt` 在每个 `z` 上非空」。
反方向（秩一 ⟹ `CondMulGuard`）需要切片非零，见 §4。** -/
theorem condMulRuleAt_nonempty_iff (p : FinJoint α β γ) :
    (∀ z, (condMulRuleAt (α := α) (β := β) (γ := γ) z p).Nonempty)
      ↔ ∀ z, IsRankOne (slice p z) := by
  constructor
  · intro h z
    have hz := h z
    unfold condMulRuleAt at hz
    by_cases hr : IsRankOne (slice p z)
    · exact hr
    · simp [hr] at hz
  · intro h z
    unfold condMulRuleAt
    simp [h z]

/-- ⭐⭐ **`CondMulGuard` ⟹ 逐 `z` 规则处处非空（已证）**。 -/
theorem condMulGuard_implies_ruleAt_nonempty (p : FinJoint α β γ)
    (h : CondMulGuard p) (hz : ∀ z, margZ p z ≠ 0) :
    ∀ z, (condMulRuleAt (α := α) (β := β) (γ := γ) z p).Nonempty :=
  (condMulRuleAt_nonempty_iff p).mpr
    (fun z => condMulGuard_implies_rankOne p h z (hz z))

/-! ## §4 ⭐⭐⭐⚠ 诚实边界：精确的强弱关系

### 4.1 对应 A 退化为 `top`/`bot` 的二值开关

`condMulRule p _` 只可能取 `{δ_⋆}` 或 `∅` 两种值，**不随状态变化**。于是：

* `IsPoint (condMulRule)` **恒成立**（构造上就是单点或空）；
* `generalize` / `refine` **无事可做**（值域只有两点）；
* `compose` 只相当于命题 `∧`。

**⟹ 对应 A 用满了 `LawRule` 的**类型**，没用上 `LawRule` 的**结构**。**

### 4.2 秩一与 `CondMul` 的**精确**关系（两个方向都已证）

| 方向 | 是否需假设 | 位置 |
|---|---|---|
| **秩一 ⟹ `CondMul`** | **无条件** | `rankOne_implies_condMul` |
| **`CondMul` ⟹ 秩一** | 需 `margZ p z ≠ 0` | `condMulGuard_implies_rankOne` |

**⟹ 在 `margZ ≠ 0` 的 `z` 上，`CondMul ⟺ 秩一`**（Pearl 1.2.4）。
**在 `margZ = 0` 的 `z` 上，`CondMul` 只要求 `margXZ·margYZ = 0`，
比秩一**更弱**。**

**⟹ 于「用秩一规则表达 `CondMul`」这件事的准确说法是**：

* 秩一规则**蕴含** `CondMul` —— 它在 `margZ = 0` 处**过多地**要求了乘积结构，
  故它是 `refine`（**收窄**，`R₂ ⊆ R₁`），**不是**等价；
* 要让秩一与 `CondMul` **等价**，必须**补上 `margZ ≠ 0` 的守卫**——
  而守卫是对 `p` 的**全局求和**的条件，**无法写进 `LawRule` 的逐点输出**。

**这就是本问题答案的数学核心**：
**`CondMul` 与 `LawRule` 之间的障碍不是「类型放不下」，
而是「`margZ = 0` 这一处的让步无法在逐点规则里表达」。** -/

/-- ⭐⭐⭐ **秩一 ⟹ `CondMul`（无条件，已证）**。

**证明**：设 `p((x,y),z) = g x · h y`。则
`margZ = (Σ g)(Σ h)`、`margXZ = g x · (Σ h)`、`margYZ = (Σ g) · h y`，
代入 `CondMul` 的等式后两边都等于 `g x · h y · (Σ g) · (Σ h)`。

**⟹ 这是 §4.2 表格的第一行：秩一是 `CondMul` 的充分条件。** -/
theorem rankOne_implies_condMul (p : FinJoint α β γ)
    (h : ∀ z, IsRankOne (slice p z)) : CondMul p := by
  intro x y z
  obtain ⟨g, hh, hgh⟩ := h z
  have hp : p ((x, y), z) = g x * hh y := hgh x y
  have hZ : margZ p z = (∑ x, g x) * (∑ y, hh y) := by
    unfold margZ
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun y _ => hgh x y))
  have hXZ : ∀ x, margXZ p x z = g x * (∑ y, hh y) := by
    intro x
    unfold margXZ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => hgh x y)
  have hYZ : ∀ y, margYZ p y z = (∑ x, g x) * hh y := by
    intro y
    unfold margYZ
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun x _ => hgh x y)
  rw [hp, hZ, hXZ, hYZ]
  ring

/-- ⭐⭐⭐ **逐 `z` 版与 `CondMul` 的关系（已证，合并 §3 与 §4.2）**：

$$\text{CondMul}\ p \;⟹\; \forall z,\ \mathrm{IsRankOne}(\mathrm{slice}\ p\ z)
  \quad\text{（需 } \forall z,\ \mathrm{margZ}\ p\ z \neq 0\text{）}$$

**⚠ 守卫 `margZ ≠ 0` 不可省**：它是 §4.2 所说「无法写进逐点规则」的那一部分，
也是唯一阻止 `CondMul` 与秩一**完全**等价的障碍。 -/
theorem condMul_implies_rankOne_of_guard (p : FinJoint α β γ)
    (h : CondMulGuard p) (hz : ∀ z, margZ p z ≠ 0) :
    ∀ z, IsRankOne (slice p z) :=
  fun z => condMulGuard_implies_rankOne p h z (hz z)

/-- ⭐ **逐 `z` 等价（在 `margZ ≠ 0` 处）**：

$$(\forall z,\ \mathrm{IsRankOne}(\mathrm{slice}\ p\ z)) \iff \mathrm{CondMul}\ p
  \quad\text{（当 } \forall z,\ \mathrm{margZ}\ p\ z \neq 0\text{）}$$

**⚠ 这正是 `condMulRuleAt` 与 `CondMul` 的桥梁**：
在 `margZ` 处处非零时，「逐 `z` 规则处处非空」**恰好等价**于 `CondMul p`。
**一旦允许 `margZ = 0`，右到左仍成立而左到右失效**（§4.2）。 -/
theorem rankOneAll_iff_condMul_of_ne_zero (p : FinJoint α β γ)
    (hz : ∀ z, margZ p z ≠ 0) :
    (∀ z, IsRankOne (slice p z)) ↔ CondMul p :=
  ⟨rankOne_implies_condMul p,
   fun hcm => condMul_implies_rankOne_of_guard p (fun x y z _ => hcm x y z) hz⟩

end

end LawRuleCondMul

end FateV2.Predict