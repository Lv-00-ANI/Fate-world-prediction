import FateWorld.FateV2.Predict.T1DegeneracyVerify
import FateWorld.FateV2.Rules.LawRule
/-!
  # Predict · T1DegeneracyVerifyConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1DegeneracyVerifyConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1DegeneracyVerify, LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.T1DegeneracyVerifyConsumer` —— **T-1 退化判据接入 `LawRule.IsPoint`**

  ## 0  接入方向（任务书「激活 → `IsPoint` 判定」+「反例 → 反例登记」）

  `Fate/T1DegeneracyVerify.lean` 的 §1、§4、§5 给出了「零残差 θ 集」的
  **形状判据**（纤维 / 单点 / 直线），但这个判据在框架里**没有下家**：
  它停在 `Set Θ` 这一层，没有接上任何**规则层**的类型。

  本文件把它接到 `Fate.LawRule.IsPoint`
  （「允许集是单点集」，即**规律唯一确定一个分布**）。

  **桥的语义**：把「零残差 θ 的集合」编码成一条 `LawRule` 的**允许分布集** ——
  每个零残差 θ 对应一个 `Measure.dirac θ`。于是

  > **`IsPoint`（规律唯一确定） ⟺ 零残差 θ 唯一（不退化）**。

  这不是同义反复：`IsPoint` 说的是 `Set (Measure Θ)` 是单点集，
  而 T-1 的判据说的是 `Set Θ` 不含异于 `θ₀` 的元素。两者的桥
  **必须**用 `Measure.dirac` 的单射性（`dirac_inj'`，本文件 §1 自证），
  这一步是**真内容**（没有它，`Measure` 层的单点性推不出 `Θ` 层的唯一性）。

  ## 1  本文件新证明的引理

  * `dirac_inj'`：`Measure.dirac a = Measure.dirac b → a = b`
    （`[MeasurableSingletonClass]` 下）。**⚠ Mathlib 里 `Measure.dirac_inj` 在本
    Mathlib 版本不可用**（实测 `unknownIdentifier`），故本文件自带证明。

  ## 2  消费的定理（4 条）

  | # | 定理 | 消费 T-1 的哪条 | 内容 |
  |---|---|---|---|
  | C1 | `residLawZ_isPoint_iff_noCollision` | `zeroResidualSet_eq_fiber`、`degenerate_iff_exists_other` | **非空**时：`IsPoint` ⟺ 无碰撞（**接入主链**） |
  | C1′ | `residLawZZ_isPoint_iff_noCollision` | 同上 | 同上，`ℤ × ℤ` 版 |
  | C2 | `isPoint_of_x_ne_zero` | `nonzero_x_zeroResidualSet_singleton` | `x ≠ 0` ⟹ **不退化** ⟹ `IsPoint` |
  | C3 | `not_isPoint_rankDeficient` | `rank_deficient_not_unique` | 降秩 ⟹ **退化** ⟹ **¬ `IsPoint`**（反例登记） |
  | C4 | `not_isPoint_x_zero_y_ne_zero` | `residual_x_zero`（+ §0.5 的语义修正） | `x = 0, y ≠ 0` ⟹ 零残差集**空** ⟹ **¬ `IsPoint`** |

  ### ⚠ 2.0  **发现并登记：C1 必须带非空前件**（本文件实测，重要）

  第一版 C1 写成**无条件**「`IsPoint` ⟺ 无碰撞」，**证不出且命题为假**：

  * 若 `¬∃θ, R θ = y`（零残差 θ **不存在**），允许集是**空集** `∅`；
  * 「无碰撞」（`∀ θ θ', Rθ = y → Rθ' = y → θ = θ'`）在 `Rθ=y` 无解时**空洞地为真**；
  * 但 `IsPoint` 要求 `∃ μ, (允许集) = {μ}`，**空集不等于任何单点集** ⟹ `IsPoint` 为**假**。

  **⟹ 两边的非空性不对称**：`IsPoint` ⟹ 非空，而「无碰撞」**不**蕴含非空。
  故 C1 必须显式带前件 `hne : ∃ θ, R θ = y`。**这不是技术性补丁，而是 T-1 判据的
  一处真实边界**：T-1 的 `degenerate_iff_exists_other` 只区分「唯一」与「存在异解」，
  **没有**覆盖「无解」这一第三态 —— 而 C4 正是第三态（空集）的算例。
  本文件**不改 T-1 的定理**，只在消费层把这条边界**显式写出**。

  ## 3  ⚠ 诚实边界

  **3.1** 本文件只 `import Fate.T1DegeneracyVerify` 与 `Fate.LawRule`，
  **不改任何已有模块**，不引入公理，零 `sorry`。

  **3.2** **C4 是「空集 ⟹ 非 `IsPoint`」**，它消费的是 T-1 §0.5 明确登记的语义修正
  （「`x = 0` 时零残差集是**空集**，不是全空间」）。C4 **不**复述那条已删除的错误陈述；
  它把更正后的语义**正面接入**：`x = 0 ∧ y ≠ 0` 时没有任何 θ 使残差为零 ⟹
  规律层是**空允许集** ⟹ 既非 `IsPoint` 也非「唯一」。

  **3.3** 本文件**不**声称「退化判据已在框架内被使用」——它只声称
  「T-1 的判据与 `LawRule.IsPoint` **等价**（C1），且 T-1 的具体算例给出
  `IsPoint` / 非 `IsPoint` 的具体实例（C2、C3、C4）」。**是否接入 `LawRule` 主链
  （`compose` / `refine` 等算子）留给后续批次。**

  **3.4 防同义反复检查**（任务书第 7 条）：
  - C1 的前件是「`R` 无碰撞」（`Θ` 层）**加非空**，结论是「`residLaw` 是 `IsPoint`」（`Measure` 层）。
    两者经由 `dirac` 单射互推，**前件不含结论**。
  - C2 / C3 / C4 的前件是 `x ≠ 0` / 降秩 / `x = 0 ∧ y ≠ 0`
    （**机制参数的最简数值条件**），结论是 `IsPoint` / `¬ IsPoint`（**规律层的性质**）。
    **前件只说机制，结论是规则类型档位**，不是同义反复。

  **3.5 ⚠ C1 的 `hne` 前件**：见 §2.0。这是本文件证明过程中**发现**的
  T-1 判据边界（「无解」第三态不在 T-1 的 iff 覆盖范围内），
  不是为通过编译而加的技术前提 —— 去掉它命题**为假**（空集反例）。

  **3.6 命名提示**：`LawRule` 既是**命名空间**（`Fate.LawRule`）又是**定义**
  （`Fate.LawRule.LawRule`）。在 `namespace Fate` 内裸写 `LawRule` 解析为**命名空间**，
  故本文件一律写全名 `Fate.LawRule.LawRule` / `Fate.LawRule.IsPoint`。

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
open FateV2.Rules
namespace T1DegeneracyVerifyConsumer

open MeasureTheory

universe u v

/-! ===========================================================================
    §1  桥引理：`Measure.dirac` 的单射性（本 Mathlib 版本 `Measure.dirac_inj` 不可用）
    =========================================================================== -/

/-- **`Measure.dirac` 单射**（`[MeasurableSingletonClass]` 下）。

**为什么自带证明**：本 Mathlib 版本中 `Measure.dirac_inj` /
`Measure.dirac_eq_dirac_iff` **均不可用**（实测 `unknownIdentifier`）。
证明用「取单点集 `{a}` 的测度」：`dirac a {a} = 1`，而 `dirac b {a} = 0`（当 `b ≠ a`）。 -/
theorem dirac_inj' (α : Type*) [MeasurableSpace α] [MeasurableSingletonClass α] {a b : α}
    (h : Measure.dirac a = Measure.dirac b) : a = b := by
  by_contra hne
  have h1 : Measure.dirac a ({a}) = Measure.dirac b ({a}) := by rw [h]
  rw [Measure.dirac_apply_of_mem (show a ∈ ({a} : Set α) from rfl),
    Measure.dirac_apply' b (measurableSet_singleton a)] at h1
  have h2 : b ∉ ({a} : Set α) := by simp [Ne.symm hne]
  rw [Set.indicator_of_notMem h2] at h1
  simp at h1

/-! ===========================================================================
    §2  **零残差 θ 集 → `LawRule`**：C1 的载体

    载体取 `C := ⟨PUnit⟩`、`X := ⟨PUnit⟩`、`Y := ⟨θ 的载体⟩`。
    这样 `LawRule C X Y = PUnit → PUnit → Set (Measure Θ)`，
    允许集**只依赖**零残差 θ 集合，不含其它自由度。
    =========================================================================== -/

/-- 单点上下文空间（`LawRule` 的形式参数）。 -/
abbrev lrC : CtxSpace where Carrier := PUnit

/-- 单点状态空间（`LawRule` 的形式参数）。 -/
abbrev lrX : StateSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 把 `ℤ` 包装成 `StateSpace`（`Y` 位，对标 `OutSpace = StateSpace`）。 -/
abbrev lrZ : StateSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 把 `ℤ × ℤ` 包装成 `StateSpace`（降秩算例的 `Y` 位）。 -/
abbrev lrZZ : StateSpace where
  Carrier := ℤ × ℤ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

instance instLrZMeas : MeasurableSpace lrZ.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instLrZZMeas : MeasurableSpace lrZZ.Carrier := inferInstanceAs (MeasurableSpace (ℤ × ℤ))
instance instLrXMeas : MeasurableSpace lrX.Carrier := inferInstanceAs (MeasurableSpace PUnit)

/-- ⭐ **零残差 θ 集编码成 `LawRule`**（`Y = lrZ`）：

$$\text{residLawZ}(R, y) := \{\,\mathrm{dirac}\,\theta \mid R\,\theta = y\,\}.$$

「允许的下一分布」这一栏里放的是**哪些 θ 是零残差的**。
于是 `IsPoint` ⇔ 允许集是单点集 ⇔ 零残差 θ 集是单点集。 -/
def residLawZ (R : ℤ → ℤ) (y : ℤ) : FateV2.Rules.LawRule.LawRule lrC lrX lrZ :=
  fun _ _ => {μ | ∃ θ : ℤ, R θ = y ∧ μ = Measure.dirac θ}

/-- ⭐ **降秩情形**（`Y = lrZZ`）：`R : ℤ × ℤ → ℤ × ℤ`。 -/
def residLawZZ (R : ℤ × ℤ → ℤ × ℤ) (y : ℤ × ℤ) : FateV2.Rules.LawRule.LawRule lrC lrX lrZZ :=
  fun _ _ => {μ | ∃ θ : ℤ × ℤ, R θ = y ∧ μ = Measure.dirac θ}

/-- **`residLawZ` 的展开式**（`rfl`）：`LawRule.LawRule` 是 `def`，
`Membership` 不会自动穿透，故所有成员断言都必须先 `rw` 这一条。 -/
theorem residLawZ_apply (R : ℤ → ℤ) (y : ℤ) (c : lrC.Carrier) (x : lrX.Carrier) :
    residLawZ R y c x = {μ | ∃ θ : ℤ, R θ = y ∧ μ = Measure.dirac θ} := rfl

/-- **`residLawZZ` 的展开式**（`rfl`）。 -/
theorem residLawZZ_apply (R : ℤ × ℤ → ℤ × ℤ) (y : ℤ × ℤ)
    (c : lrC.Carrier) (x : lrX.Carrier) :
    residLawZZ R y c x = {μ | ∃ θ : ℤ × ℤ, R θ = y ∧ μ = Measure.dirac θ} := rfl

/-- **成员刻画（`ℤ` 版）**：`dirac θ ∈ residLawZ R y ⟺ R θ = y`。 -/
theorem mem_residLawZ {R : ℤ → ℤ} {y : ℤ} (θ : ℤ) [MeasurableSingletonClass ℤ] :
    Measure.dirac θ ∈ residLawZ R y PUnit.unit PUnit.unit ↔ R θ = y := by
  rw [residLawZ_apply]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨θ', h', hμ⟩
    have heq : θ = θ' := dirac_inj' ℤ hμ
    rw [heq]; exact h'
  · intro h
    exact ⟨θ, h, rfl⟩

/-- **成员刻画（`ℤ × ℤ` 版）**：`dirac θ ∈ residLawZZ R y ⟺ R θ = y`。 -/
theorem mem_residLawZZ {R : ℤ × ℤ → ℤ × ℤ} {y : ℤ × ℤ} (θ : ℤ × ℤ)
    [MeasurableSingletonClass (ℤ × ℤ)] :
    Measure.dirac θ ∈ residLawZZ R y PUnit.unit PUnit.unit ↔ R θ = y := by
  rw [residLawZZ_apply]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨θ', h', hμ⟩
    have heq : θ = θ' := dirac_inj' (ℤ × ℤ) hμ
    rw [heq]; exact h'
  · intro h
    exact ⟨θ, h, rfl⟩

/-! ===========================================================================
    §3  ⭐ C1：**接入主链**（`IsPoint` ⟺ 无碰撞）
    =========================================================================== -/

/-- ⭐⭐⭐ **C1（接入）**：`residLawZ R y` 是 `IsPoint` **⟺** 零残差 θ 唯一。

$$\text{IsPoint}(\text{residLawZ}\,R\,y)
  \iff \forall \theta\, \theta',\ R\,\theta = y \to R\,\theta' = y \to \theta = \theta'.$$

**消费**：T-1 的 `zeroResidualSet_eq_fiber`（零残差集 = 纤维）与
`degenerate_iff_exists_other`（退化 ⟺ 存在同值异参）。

**⭐ 这一条是本文件接入的核心**：它把 T-1 §1 的判据
**翻译成 `LawRule` 层的类型档位**（「规律唯一确定」）。
**⚠ 前件不含结论**：左侧是 `Measure ℤ` 层的单点性，右侧是 `ℤ` 层的唯一性，
桥是 `dirac_inj'`（真内容）。 -/
theorem residLawZ_isPoint_iff_noCollision (R : ℤ → ℤ) (y : ℤ) (hne : ∃ θ : ℤ, R θ = y)
    [MeasurableSingletonClass ℤ] :
    FateV2.Rules.LawRule.IsPoint (residLawZ R y)
      ↔ ∀ θ θ' : ℤ, R θ = y → R θ' = y → θ = θ' := by
  constructor
  · intro h θ θ' hθ hθ'
    obtain ⟨μ, hμ⟩ := h PUnit.unit PUnit.unit
    have h1 : Measure.dirac θ ∈ ({μ} : Set (Measure ℤ)) := by
      rw [← hμ]; exact (mem_residLawZ θ).mpr hθ
    have h2 : Measure.dirac θ' ∈ ({μ} : Set (Measure ℤ)) := by
      rw [← hμ]; exact (mem_residLawZ θ').mpr hθ'
    rw [Set.mem_singleton_iff] at h1 h2
    exact dirac_inj' ℤ (h1.trans h2.symm)
  · intro h c x
    obtain ⟨θ₀, hθ₀⟩ := hne
    refine ⟨Measure.dirac θ₀, ?_⟩
    rw [residLawZ_apply]
    ext μ
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      rw [Set.mem_singleton_iff]
      exact congrArg Measure.dirac (h θ θ₀ hθ hθ₀)
    · intro hμ
      rw [Set.mem_singleton_iff] at hμ
      exact ⟨θ₀, hθ₀, hμ⟩

/-- ⭐⭐⭐ **C1′（降秩版）**：`residLawZZ R y` 是 `IsPoint` **⟺** 零残差 θ 唯一。 -/
theorem residLawZZ_isPoint_iff_noCollision (R : ℤ × ℤ → ℤ × ℤ) (y : ℤ × ℤ)
    (hne : ∃ θ : ℤ × ℤ, R θ = y) [MeasurableSingletonClass (ℤ × ℤ)] :
    FateV2.Rules.LawRule.IsPoint (residLawZZ R y)
      ↔ ∀ θ θ' : ℤ × ℤ, R θ = y → R θ' = y → θ = θ' := by
  constructor
  · intro h θ θ' hθ hθ'
    obtain ⟨μ, hμ⟩ := h PUnit.unit PUnit.unit
    have h1 : Measure.dirac θ ∈ ({μ} : Set (Measure (ℤ × ℤ))) := by
      rw [← hμ]; exact (mem_residLawZZ θ).mpr hθ
    have h2 : Measure.dirac θ' ∈ ({μ} : Set (Measure (ℤ × ℤ))) := by
      rw [← hμ]; exact (mem_residLawZZ θ').mpr hθ'
    rw [Set.mem_singleton_iff] at h1 h2
    exact dirac_inj' (ℤ × ℤ) (h1.trans h2.symm)
  · intro h c x
    obtain ⟨θ₀, hθ₀⟩ := hne
    refine ⟨Measure.dirac θ₀, ?_⟩
    rw [residLawZZ_apply]
    ext μ
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      rw [Set.mem_singleton_iff]
      exact congrArg Measure.dirac (h θ θ₀ hθ hθ₀)
    · intro hμ
      rw [Set.mem_singleton_iff] at hμ
      exact ⟨θ₀, hθ₀, hμ⟩

/-! ===========================================================================
    §4  ⭐ C2：`x ≠ 0` ⟹ **不退化** ⟹ `IsPoint`

    消费 T-1 §4 的 `nonzero_x_zeroResidualSet_singleton`
    （`x ≠ 0` 时零残差集是单点集）。
    =========================================================================== -/

/-- ⭐⭐⭐ **C2**：`R θ = x * θ`（T-1 §2 的最小机制）、`y = x * θ₀`、`x ≠ 0`
⟹ `residLawZ` 是 `IsPoint`（**规律唯一确定 ⟹ 不退化**）。

**消费**：`nonzero_x_zeroResidualSet_singleton`（T-1 §4）。

**⚠ 前件是机制参数**（`x ≠ 0`），**结论是 `LawRule` 层档位**。不是同义反复。 -/
theorem isPoint_of_x_ne_zero (x θ₀ : ℤ) (hx : x ≠ 0) [MeasurableSingletonClass ℤ] :
    FateV2.Rules.LawRule.IsPoint (residLawZ (fun θ : ℤ => x * θ) (x * θ₀)) := by
  rw [residLawZ_isPoint_iff_noCollision _ _ ⟨θ₀, rfl⟩]
  intro θ θ' h h'
  have key : ∀ u : ℤ, x * u = x * θ₀ → u = θ₀ := by
    intro u hu
    rcases mul_eq_zero.mp (show x * (u - θ₀) = 0 by rw [mul_sub, hu, sub_self]) with h2 | h2
    · exact absurd h2 hx
    · exact sub_eq_zero.mp h2
  rw [key θ h, key θ' h']

/-! ===========================================================================
    §5  ⚠ C3：**降秩 ⟹ 退化 ⟹ ¬ `IsPoint`**（反例登记）

    消费 T-1 §5 的 `rank_deficient_not_unique`：
    `R θ = (θ.1, 0)` 时零残差集是**整条直线** ⟹ 不唯一 ⟹ 不是 `IsPoint`。
    =========================================================================== -/

/-- ⭐⭐⭐ **C3（反例登记）**：`R θ = (θ.1, 0)`（**只观测第一坐标**）⟹
`residLawZZ` **不是** `IsPoint`。

**⭐ 这是对 `LawRule.IsPoint` 的**具体反例**：降秩机制下，
「允许的 θ」是整条竖直直线，规律**不能**唯一确定一个分布 ⟹ 退化。

**消费**：`rank_deficient_not_unique`（T-1 §5）。 -/
theorem not_isPoint_rankDeficient (a : ℤ) [MeasurableSingletonClass (ℤ × ℤ)] :
    ¬ FateV2.Rules.LawRule.IsPoint (residLawZZ (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (a, 0)) := by
  intro h
  rw [residLawZZ_isPoint_iff_noCollision _ _ ⟨(a, 0), rfl⟩] at h
  have hne : (a, (0 : ℤ)) ≠ (a, (1 : ℤ)) := by simp
  exact hne (h (a, 0) (a, 1) rfl rfl)

/-! ===========================================================================
    §6  ⚠ C4：`x = 0 ∧ y ≠ 0` ⟹ 零残差集**空** ⟹ ¬ `IsPoint`

    消费 T-1 §3 的 `residual_x_zero`：`x = 0` 时残差恒 `= y`，与 θ 无关。
    若 `y ≠ 0`，**没有任何** θ 使残差为零 ⟹ 允许集空 ⟹ 非 `IsPoint`。

    ⚠ 这是 T-1 §0.5 **已登记的语义修正**的正面接入：
    旧陈述「零残差集 = 全空间」是错的；正确结论是 **空集**。
    =========================================================================== -/

/-- **`x = 0`、`y ≠ 0` ⟹ 零残差集是空集**（不唯一性的极限形态：**零解**）。 -/
theorem zeroResidualSet_x_zero_eq_empty {y : ℤ} (hy : y ≠ 0) :
    T1DegeneracyVerify.zeroResidualSet (fun θ : ℤ => (0 : ℤ) * θ) y = ∅ := by
  ext θ
  simp only [T1DegeneracyVerify.zeroResidualSet, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  rw [zero_mul]
  exact fun h => hy h.symm

/-- ⭐⭐⭐ **C4（反例登记）**：`x = 0` 且 `y ≠ 0` ⟹ `residLawZ` **不是** `IsPoint`。

**⭐ 语义**：`x = 0` 时残差 `= y`（T-1 `residual_x_zero`，**读不到 θ**）；
`y ≠ 0` 时**无** θ 使残差为零 ⟹ 允许集**空** ⟹ 规律层**既非单点也非全空间**，
而是**空**（「无解」型退化）。

**⚠ 这一条明确替代 T-1 §0.5 删除的错误陈述**：
错误版说「零残差集 = 全空间」，正确版说「**空集**」；
本定理把**正确版**接到 `LawRule.IsPoint` 的**否定**上。 -/
theorem not_isPoint_x_zero_y_ne_zero {y : ℤ} (hy : y ≠ 0) [MeasurableSingletonClass ℤ] :
    ¬ FateV2.Rules.LawRule.IsPoint (residLawZ (fun θ : ℤ => (0 : ℤ) * θ) y) := by
  intro h
  -- `IsPoint` 给出见证 `μ`；`residLawZ` 的允许集是空集，矛盾
  obtain ⟨μ, hμ⟩ := h PUnit.unit PUnit.unit
  have hmem : μ ∈ ({μ} : Set (Measure ℤ)) := Set.mem_singleton μ
  rw [← hμ, residLawZ_apply] at hmem
  obtain ⟨θ, hθ, -⟩ := hmem
  -- `(0 : ℤ) * θ = 0 ≠ y`
  simp only [zero_mul] at hθ
  exact hy hθ.symm

/-! ===========================================================================
    §7  自检清单
    =========================================================================== -/

/-- **自检 1**：`dirac` 单射（C1 的桥）。 -/
example {a b : ℤ} (h : Measure.dirac a = Measure.dirac b) : a = b := dirac_inj' ℤ h

/-- **自检 2**：`residLawZ` 的成员刻画与零残差集一致。 -/
example (R : ℤ → ℤ) (y : ℤ) (θ : ℤ) [MeasurableSingletonClass ℤ] :
    Measure.dirac θ ∈ residLawZ R y PUnit.unit PUnit.unit
      ↔ θ ∈ T1DegeneracyVerify.zeroResidualSet R y := by
  rw [mem_residLawZ]; rfl

/-- **自检 3**：三条判据**可同时**成立且不冲突
（`x ≠ 0` 是 `IsPoint`；降秩不是；`x = 0 ∧ y ≠ 0` 不是）。 -/
example [MeasurableSingletonClass ℤ] [MeasurableSingletonClass (ℤ × ℤ)] :
    FateV2.Rules.LawRule.IsPoint (residLawZ (fun θ : ℤ => 1 * θ) (1 * 0))
      ∧ ¬ FateV2.Rules.LawRule.IsPoint (residLawZZ (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (0, 0))
      ∧ ¬ FateV2.Rules.LawRule.IsPoint (residLawZ (fun θ : ℤ => (0 : ℤ) * θ) 1) :=
  ⟨isPoint_of_x_ne_zero 1 0 one_ne_zero, not_isPoint_rankDeficient 0,
   not_isPoint_x_zero_y_ne_zero one_ne_zero⟩

end T1DegeneracyVerifyConsumer
end FateV2.Predict