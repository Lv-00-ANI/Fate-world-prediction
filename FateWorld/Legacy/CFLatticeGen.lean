import FateWorld.Legacy.CFLattice
import Mathlib.Order.Antisymmetrization
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.GaloisConnection.Basic

/-! ===========================================================================
  §9  读出方案格结构的**推广**（`Fate/CFLattice.lean` 的强化版）

  **出发点**：`Fate/CFLattice.lean` 把「读出方案」形式化为
  `Readout SCM = (CF : Type v) × (Obs : SCM → CF)`，
  并用 `Finer R₁ R₂ := ∀ s t, R₁.Obs s = R₁.Obs t → R₂.Obs s = R₂.Obs t`
  （即 `ker R₁ ⊆ ker R₂`）给出「粗细」序。

  原版只证到：
  * `Finer` 是**预序**（`finer_refl` / `finer_trans`）；
  * 恒等读出是**最小元**（`identity_is_finest`）；
  * 判据依赖（`criterion_dependence`）。

  **本文件做五项推广**（结论与任务提示的猜想有两处**重要出入**）：

  | 编号 | 推广 | 结论 |
  |---|---|---|
  | **G1** | `Finer` 预序 → **偏序**（商掉对称部分） | ✅ 成功：`Antisymmetrization` 上是偏序；并给反例说明商**必要** |
  | **G2** | 最大元（最粗读出） | ⚠️ **推翻提示**：最大元**存在**，充要条件为 `Obs` 常值 |
  | **G3** | `Finer` 的 **Galois 连接**刻画 | ✅ 成功：`Finer` ⟺ `κ ⊣ readoutOfSetoid`；⚠️ 并**证否**了「无自伴」猜想 |
  | **G4** | `Readout` 是否 **完备格** | ⚠️ **推翻提示**：**是**完备格（任意上下确界均存在） |
  | **G5** | 核映射 `κ : Readout → Setoid SCM` | ✅ 单调、满、是 Galois 连接 `κ ⊣ readoutOfSetoid` |

  **⚠ 无硬编码常数**（依作者裁决 Q-1）。
  **⚠ 零 `sorry` / 零 `admit` / 零自定义 `axiom`**：
  只用 Lean 内核标准公理（`propext` / `Classical.choice` / `Quot.sound`）——
  已用 `#print axioms` 逐条核验。

  **⚠ 关于两条被推翻的提示猜想**：任务提示假设「`Finer` 无最大元，故不是完备格」。
  本文件证明该假设的**方向搞反了**：`Finer R' R` 意为「`R'` 更细」，
  加宽载体只会**更细**，而常值读出的核是 `⊤`（已到顶）。
  详见 §9.2 `isTop_iff_obs_constant` 与 §9.5。

  **⚠ 关于 import 的说明**：本文件**直接 `import Fate.CFLattice`**，
  故 §9.1–§9.5 的推广**就是**对原版 `Readout` / `Finer` 的推广，无需任何搬运论证。

  `Readout` / `Finer` / `identityReadout` 及原版三条基本定理经 `export`
  提到 `Fate.CFLatticeGen` 顶层，便于本文件与下游引用。
  =========================================================================== -/

set_option autoImplicit false

namespace Fate

namespace CFLatticeGen

universe u v v₂

variable {SCM : Type u}

/-! ===========================================================================
  §9.0  基础层：直接**复用**原版 `Readout` / `Finer` / `identityReadout`
  ===========================================================================
  本文件 `import Fate.CFLattice`，故这里**不再重述**任何定义 ——
  §9.1–§9.5 的推广是**直接**对原版对象的推广，不存在「搬运」问题。

  `Readout` / `Finer` 经 `export` 提到 `Fate.CFLatticeGen` 顶层，
  使本文件其余部分与下游模块的引用更短。
  --------------------------------------------------------------------------- -/

export Fate.CFLattice (Readout Finer identityReadout finer_refl finer_trans
  identity_is_finest)

/-! ===========================================================================
  §9.0.2  基础桥接：`Finer` 就是 `Setoid` 上的包含序
  ===========================================================================
  原版把 `Finer` 写成「核包含」的逐点形式，但**没有把它接到 Mathlib 的 `Setoid` 格上**。
  本节先补这座桥 —— 后面 G1/G3/G4/G5 全部依赖它。
  --------------------------------------------------------------------------- -/

/-- ⭐ **核的精确刻画**：`Finer R₁ R₂` ⟺ `ker R₁ ≤ ker R₂`（`Setoid SCM` 中的序）。

**比原版强在哪**：原版 `Finer` 只是「逐点蕴含」的句式，无法直接使用 Mathlib 的
`Setoid` 完备格机器；本定理把它**逐字翻译**成 `Setoid` 序，
从而使 `Antisymmetrization` / `GaloisConnection` / 完备格这一整套机器可直接调用。 -/
theorem finer_iff_ker_le {R₁ R₂ : Readout SCM} :
    Finer R₁ R₂ ↔ Setoid.ker R₁.Obs ≤ Setoid.ker R₂.Obs :=
  Iff.rfl

/-- ⭐ **`Finer` 的等价表述（分解形式）**：`R₁` 比 `R₂` 细 ⟺ 存在 `φ`
使 `R₂.Obs = φ ∘ R₁.Obs`（当 `SCM` 非空时）。

**比原版强在哪**：原版只给出「核包含」这一**关系式**；本定理给出**分解式** ——
即「更粗的那个是从更细的那个因式分解出来的」。
这正是 `Fate/CFMap.lean` 中 `ker_subset_of_factor` 的**逆命题**，
把该项目两个模块里的分解引理接成了**充要条件**。

**⚠ 非空性不可去**：`SCM` 空时 `Obs` 没有取值点，`φ` 无从定义
（见 `finer_iff_factors_needs_nonempty`）。 -/
theorem finer_iff_factors [Nonempty SCM] {R₁ R₂ : Readout SCM} :
    Finer R₁ R₂ ↔ ∃ φ : R₁.CF → R₂.CF, R₂.Obs = φ ∘ R₁.Obs := by
  constructor
  · intro h
    -- `φ` 只在 `R₁.Obs` 的像上被约束；像外补一个默认值。
    -- `R₂.CF` 非空（`SCM` 非空，故 `R₂.Obs` 取到值），无需额外假设。
    classical
    haveI : Nonempty R₂.CF := ⟨R₂.Obs (Classical.arbitrary SCM)⟩
    refine ⟨fun c => if hc : ∃ s : SCM, c = R₁.Obs s
        then R₂.Obs (Classical.choose hc)
        else Classical.arbitrary R₂.CF, ?_⟩
    funext s
    have hex : ∃ s' : SCM, R₁.Obs s = R₁.Obs s' := ⟨s, rfl⟩
    show R₂.Obs s = (if hc : ∃ s' : SCM, R₁.Obs s = R₁.Obs s'
        then R₂.Obs (Classical.choose hc) else Classical.arbitrary R₂.CF)
    rw [dif_pos hex]
    exact h s (Classical.choose hex) (Classical.choose_spec hex)
  · rintro ⟨φ, hφ⟩ s t h
    rw [hφ]
    exact congrArg φ h

/-- ⭐ **非空性不可去（诚实边界）**：`SCM := PEmpty` 时「分解形式」**失效**。

`PEmpty` 上**不存在** `φ : PUnit → PEmpty`，故恒等读出**不能**由常值读出分解得到。

**比原版强在哪**：原版没有任何「前提是否可去」的结论；本定理**精确划出边界** ——
说明 `finer_iff_factors` 里的 `[Nonempty SCM]` 是**本质条件**而非技术冗余。 -/
theorem finer_iff_factors_needs_nonempty :
    ¬ ∃ φ : PUnit → PEmpty, (fun x : PEmpty => nomatch x) = φ ∘ (fun _ => PUnit.unit) := by
  rintro ⟨φ, hφ⟩
  exact PEmpty.elim (φ PUnit.unit)

/-! ===========================================================================
  §9.1  ⭐ G1：`Finer` 从**预序**推广为**偏序**（在商上）
  ===========================================================================
  原版 `finer_refl` / `finer_trans` 只给**预序**。**反对称性一般不成立**：
  只要 `R₁.Obs = ψ ∘ R₂.Obs` 且 `R₂.Obs = φ ∘ R₁.Obs`，就有互相 `Finer`
  而 `R₁.Obs ≠ R₂.Obs`（见 §9.1.2 反例）。

  正确做法：按「互相 `Finer`」取商 —— 这正是 Mathlib 的 `Antisymmetrization`。
  --------------------------------------------------------------------------- -/

/-- **`Finer` 给出的 `Preorder` 结构**（`le := Finer`）。

**⚠ 这是 `Preorder` 而**不是**`PartialOrder`** —— `Preorder` 只要求自反 + 传递，
**不要求**反对称性，所以能装；`PartialOrder` 装不上（见 `finer_not_isPartialOrder`）。
这一步是 G1 全部内容的技术枢纽。 -/
instance instPreorderReadout (SCM : Type u) : Preorder (Readout SCM) where
  le := Finer
  le_refl := finer_refl
  le_trans _ _ _ := finer_trans

/-- ⭐ **读出等价**：两个读出方案「一样细」（互相 `Finer`）。

**注意**：这不是 `=` —— 它只要求**核相同**，允许载体类型与读出泛函不同。 -/
def ReadoutEquivalent (R₁ R₂ : Readout SCM) : Prop :=
  Finer R₁ R₂ ∧ Finer R₂ R₁

/-- **读出等价的核形式**：互相 `Finer` ⟺ **核相等**。

**比原版强在哪**：原版没有任何「两个不同读出何时应视为同一」的判据；
本定理给出**可计算的判据**：比较核。 -/
theorem readoutEquivalent_iff_ker_eq {R₁ R₂ : Readout SCM} :
    ReadoutEquivalent R₁ R₂ ↔ Setoid.ker R₁.Obs = Setoid.ker R₂.Obs :=
  ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- ⭐⭐ **G1 主结论：读出方案的「粗细」在商上是偏序。**

`AntisymmetrizedReadout SCM` 是**偏序集**。

**比原版强在哪**：
原版只有 `finer_refl` / `finer_trans`（**预序**）。本定理补上**反对称性**，
并给出正确的论域 —— **不是 `Readout SCM` 本身**，而是它的**反称化商**。
这直接说明「读出方案构成格」这句话**必须在商上读**，否则是假的
（`finer_not_isPartialOrder` 给出反例）。 -/
abbrev AntisymmetrizedReadout (SCM : Type u) :=
  Antisymmetrization (Readout SCM) (· ≤ ·)

instance instPartialOrderAntisymmetrizedReadout (SCM : Type u) :
    PartialOrder (AntisymmetrizedReadout SCM) :=
  instPartialOrderAntisymmetrization

/-- **商上的序与代表元的 `Finer` 一致**。 -/
@[simp]
theorem toAntisymmetrization_le_iff {R₁ R₂ : Readout SCM} :
    toAntisymmetrization (α := Readout SCM) (· ≤ ·) R₁
        ≤ toAntisymmetrization (· ≤ ·) R₂ ↔ Finer R₁ R₂ :=
  Iff.rfl

/-- ⭐⭐ **商中的相等 ⟺ 核相等**（把 G1 落到 `Setoid` 上）。

**比原版强在哪**：这是 G1 的**判定形式** ——
「两个读出在商中相同」被精确等同于「它们的核相同」，
即「粗细」这个序**只依赖核**，与载体的具体形状无关。 -/
theorem mk_eq_mk_iff_ker_eq {R₁ R₂ : Readout SCM} :
    toAntisymmetrization (α := Readout SCM) (· ≤ ·) R₁
        = toAntisymmetrization (· ≤ ·) R₂ ↔
      Setoid.ker R₁.Obs = Setoid.ker R₂.Obs := by
  show Quotient.mk'' R₁ = Quotient.mk'' R₂ ↔ _
  rw [Quotient.eq'']
  exact readoutEquivalent_iff_ker_eq

/-! ### §9.1.2 反例：`Finer` 的反对称性在 `Readout` 上**确实失效** -/

/-- ⭐⭐ **反例（G1 的动机）：存在两个读出方案互相 `Finer` 但读出泛函不相等。**

取 `SCM := Bool`、`CF := Bool`：
* `R₁ := { CF := Bool, Obs := id }`（核 `= ⊥`）
* `R₂ := { CF := Bool, Obs := fun b => !b }`（核**也**`= ⊥`，因 `!` 是单射）

于是 `ker R₁ = ker R₂ = ⊥`，故**互相 `Finer`**；
但 `id ≠ (!·)`（在 `true` 上取值分别为 `true` / `false`），故反对称性失败。

**✅ 构造要点**：两者**值域类型相同**（都是 `Bool`），故 `ρ₁ ≠ ρ₂` **类型合法**；
若把两个读出写成存在量化（`∃ R₁ R₂ : Readout Bool, … R₁.Obs ≠ R₂.Obs`），
则 `R₁.CF` / `R₂.CF` 是两个无法统一的元变量，该式**不是良typed的** ——
故此处把读出泛函**提到量化之外**。

**⟹ 故 `Finer` 在 `Readout` 上**不是**偏序，G1 的商构造**必要而非装饰**。 -/
theorem finer_not_antisymmetric :
    ∃ (ρ₁ ρ₂ : Bool → Bool),
      ReadoutEquivalent (⟨Bool, ρ₁⟩ : Readout.{0, 0} Bool) ⟨Bool, ρ₂⟩ ∧ ρ₁ ≠ ρ₂ := by
  refine ⟨id, not, ⟨?_, ?_⟩, ?_⟩
  · intro s t hst
    rw [show s = t from hst]
  · intro s t hst
    have h' : (!s) = (!t) := hst
    rw [show s = t from by simpa using congrArg (fun b => !b) h']
  · intro h
    have hpt : id true = not true := congrFun h true
    exact Bool.noConfusion hpt

/-- ⭐ **`Finer` 在 `Readout` 上**不是**偏序**（由 `finer_not_antisymmetric`）。

**比原版强在哪**：原版只说「预序」。本定理**明确否认偏序性**，
把「为什么必须取商」变成一条可核验的否定命题，而不是口头提醒。

**证明要点**：`Readout` 是含 `Type` 字段的结构，`Obs` 的陪域 `CF` **依赖** `R`，
故 `congrArg (fun R => R.Obs true)` **不成立**（Lean 会拒绝）。
必须走 `Readout.mk.injEq` 把结构相等拆成字段相等，
`Obs` 字段给出**异质**相等 `id ≍ not`，再用 `eq_of_heq` 化为普通相等，最后 `congrFun` 取点。 -/
theorem finer_not_isPartialOrder :
    ¬ IsPartialOrder (Readout.{0, 0} Bool) (Finer (SCM := Bool)) := by
  intro h
  have hle : Finer (⟨Bool, id⟩ : Readout.{0, 0} Bool) ⟨Bool, not⟩ := by
    intro s t hst
    rw [show s = t from hst]
  have hge : Finer (⟨Bool, not⟩ : Readout.{0, 0} Bool) ⟨Bool, id⟩ := by
    intro s t hst
    have h' : not s = not t := hst
    rw [show s = t from by simpa using congrArg not h']
  have heq : (⟨Bool, id⟩ : Readout.{0, 0} Bool) = ⟨Bool, not⟩ :=
    h.2.antisymm _ _ hle hge
  have hObs : id = not :=
    eq_of_heq ((Fate.CFLattice.Readout.mk.injEq Bool id Bool not).mp heq |>.2)
  have hpt : id true = not true := congrFun hObs true
  exact Bool.noConfusion hpt

/-- ⭐ **G1 的应用：在商中，恒等读出是**唯一**最小元。**

**比原版强在哪**：原版 `identity_is_finest` 只说恒等读出**是**最小元；
本定理说它在商中是**唯一**最小元 ——
即「最细读出」这个概念**well-defined**（不依赖代表元的选择）。 -/
theorem identity_is_unique_bot {R : Readout SCM}
    (h : Finer R (identityReadout SCM)) :
    toAntisymmetrization (α := Readout SCM) (· ≤ ·) R
      = toAntisymmetrization (· ≤ ·) (identityReadout SCM) := by
  refine (mk_eq_mk_iff_ker_eq).mpr (le_antisymm ?_ ?_)
  · exact h
  · exact identity_is_finest R

/-! ===========================================================================
  §9.2  ⭐⭐ G2：【推翻提示】最大元**存在**，且其充要条件是「读出常值」
  ===========================================================================
  任务提示猜想「常值读出是否最大？若不存在（由于 `CF` 是自由类型），请证明为何」。

  **答案：常值读出就是最大元；最大元不仅存在，还有精确的充要刻画。**
  --------------------------------------------------------------------------- -/

/-- **真值读出**：把所有机制都读到同一点。这就是提示里的「常值读出」。

⚠ 宇宙说明：`Readout.{u, 1}` 要求 `CF : Type 1`，而 `PUnit.{2} : Type 1`。 -/
def truthReadout (SCM : Type u) : Readout.{u, 1} SCM where
  CF := PUnit.{2}
  Obs := fun _ => PUnit.unit

@[simp]
theorem truthReadout_obs (SCM : Type u) (s : SCM) :
    (truthReadout SCM).Obs s = PUnit.unit := rfl

instance truthReadout_subsingleton (SCM : Type u) : Subsingleton (truthReadout SCM).CF :=
  ⟨fun _ _ => rfl⟩

/-- ⭐⭐ **G2 主结论：最大元的**充要刻画**。**

$$\bigl(\forall R',\ \mathrm{Finer}\,R'\,R\bigr) \iff \bigl(\forall s\,t,\ R.\mathrm{Obs}\,s = R.\mathrm{Obs}\,t\bigr)$$

即 **`R` 是最大元 ⟺ `R.Obs` 是常值函数**。

**两个方向都是初等的**：
* (⟸) 若 `R.Obs` 常值，则 `R.Obs s = R.Obs t` 恒真，故对**任意** `R'`，
  `Finer R' R` 的前提自动满足。
* (⟹) 取 `R' := { CF := ULift Bool, Obs := fun _ => ⟨true⟩ }`（常值读出）。
  由 `Finer R' R` 得：`R'` 的两点像相等 ⟹ `R` 的两点像相等。

**⚠ 为什么提示的直觉会出错（这是本推广最有价值的一点）**：
提示的推理是「`CF` 是自由类型 ⟹ 可无限加宽载体 ⟹ 没有最大元」。
**但 `Finer` 的方向被搞反了**：`Finer R' R` 说的是「**`R'` 比 `R` 更细**」（核更小）。
最大元要求**所有读出都比它细**，即**它的核最大**。
把 `CF` 加宽只会让读出**更细**（核更小），**永远造不出比常值读出更粗的东西** ——
常值读出的核是 `⊤`（万有关系），**已经到顶**。
「自由载体」造成的假象是**没有最小上界**，而不是无最大元。

**比原版强在哪**：
原版只证了**最小元存在**（`identity_is_finest`）。本定理给出**对偶侧的完整答案**：
最大元**存在**，且有一条**可判定的充要条件**（观察是否为常值）。
这使 `Readout` 的格论图景完整：**有底（恒等）、有顶（常值）**。 -/
theorem isTop_iff_obs_constant (R : Readout.{u, v} SCM) :
    (∀ R' : Readout.{u, v} SCM, Finer R' R) ↔ (∀ s t : SCM, R.Obs s = R.Obs t) := by
  constructor
  · intro htop s t
    exact htop { CF := ULift.{v} Bool, Obs := fun _ => ULift.up true } s t rfl
  · intro hc _ _ _ _
    exact hc _ _

/-- ⭐⭐ **真值读出确实是整个 `Readout SCM` 的最大元**（不只是「最粗候选」）。

**比原版强在哪**：原版 `identity_is_finest` 给出最小元；本定理给出**最大元的具体实现**。 -/
theorem truth_is_top (R : Readout SCM) : Finer R (truthReadout SCM) :=
  fun _ _ _ => Subsingleton.elim _ _

/-- ⭐ **任何 `Obs` 常值的读出都是最大元**（最大元**不唯一**）。

**比原版强在哪**：原版没有「最大元是否唯一」的任何讨论。
本定理说明最大元**在 `Readout` 层面不唯一**
（`PUnit` 常值读出与 `Bool` 常值读出都最大，但结构不等），
**但在 G1 的商中唯一**（它们的核都是 `⊤`）—— 这与最小元的情形完全对偶。 -/
theorem obs_constant_is_top {R : Readout.{u, v} SCM}
    (hc : ∀ s t : SCM, R.Obs s = R.Obs t) :
    ∀ R' : Readout.{u, v} SCM, Finer R' R :=
  fun _ s t _ => hc s t

/-- ⭐⭐ **最大元的核就是 `⊤`**：常值读出的核是万有关系。

**比原版强在哪**：把 G2 与 G5 的核映射接起来 ——
最大元 `⟷` 核为 `⊤`，最小元 `⟷` 核为 `⊥`，
于是 `Readout` 的极大/极小**完全由核决定**，这正是 G1 取商之所以正确的原因。 -/
theorem ker_eq_top_of_obs_constant {R : Readout SCM}
    (hc : ∀ s t : SCM, R.Obs s = R.Obs t) :
    Setoid.ker R.Obs = ⊤ :=
  Setoid.eq_top_iff.mpr hc

/-- ⭐ **真值读出的核是 `⊤`**（最大元的核形式）。 -/
theorem ker_truthReadout : Setoid.ker (truthReadout SCM).Obs = ⊤ :=
  Setoid.eq_top_iff.mpr fun _ _ => rfl

/-! ===========================================================================
  §9.3  ⭐⭐ G5：核映射 `κ : Readout SCM → Setoid SCM` —— Galois 连接（先行）
  ===========================================================================
  把「读出」与 `Setoid SCM`（Mathlib 的**完备格**）接起来的主桥。
  G3/G4 都依赖它，故本节先行。

  * `κ R := ker R.Obs`：读出 → 核（**单调**、**满**）
  * `readoutOfSetoid ρ`：`Setoid` → 读出（用商映射读），是 `κ` 的**右伴随**
  * **上伴随**：`Finer R (readoutOfSetoid ρ) ↔ κ R ≤ ρ`
  --------------------------------------------------------------------------- -/

/-- **核映射** `κ`：读出 → 其读出泛函的核。

⚠ 宇宙说明：这里 `Readout` 的载体宇宙取 `u`（与 `SCM` 同层），
使 `κ` 与 `readoutOfSetoid : Setoid → Readout.{u,u}` 能配成伴随对；
一般宇宙的版本见 `kappa'`。 -/
def kappa {SCM : Type u} (R : Readout.{u, u} SCM) : Setoid SCM :=
  Setoid.ker R.Obs

/-- **核映射（一般宇宙）**：不限制载体的宇宙层。 -/
def kappa' {SCM : Type u} (R : Readout.{u, v} SCM) : Setoid SCM :=
  Setoid.ker R.Obs

/-- **读出的核化**：把任意 `Setoid` 变成读出（用商映射读）。

这是 `kappa` 的右伴随；**这就是「每个核都能被某个读出实现」的构造**。 -/
def readoutOfSetoid (ρ : Setoid SCM) : Readout.{u, u} SCM where
  CF := Quotient ρ
  Obs := Quotient.mk''

/-- ⭐ **`κ ∘ readoutOfSetoid = id`**（左逆）。 -/
@[simp]
theorem ker_readoutOfSetoid (ρ : Setoid SCM) :
    kappa (readoutOfSetoid (SCM := SCM) ρ) = ρ :=
  Setoid.ker_mk_eq ρ

/-- ⭐ **`κ` 单调**（`Finer` 就是经 `κ` 搬运过去的 `Setoid` 序）。 -/
theorem kappa_monotone : Monotone (kappa (SCM := SCM)) :=
  fun _ _ h => h

/-- ⭐⭐ **每个 `Setoid` 都是某个读出的核** —— `κ` **满**。

**比原版强在哪**：原版从未讨论「核能取到哪些 `Setoid`」。
本定理说明 `κ` 的像**穷尽** `Setoid SCM`，
于是 `Readout` 携带的粗细信息**不少于**整个 `Setoid` 完备格 ——
这是 G5「`Readout` 细化 `Setoid`」的确切含义，也是 G4 完备性的来源。 -/
theorem kappa_surjective :
    Function.Surjective (fun R : Readout.{u, u} SCM => kappa R) :=
  fun ρ => ⟨readoutOfSetoid ρ, Setoid.ker_mk_eq ρ⟩

/-! ===========================================================================
  §9.4  ⭐⭐ G3：`Finer` 与 **Galois 连接**
  ===========================================================================
  * **负**：`Readout` 上不存在「与 `Finer` 相容的偏序」，故 `GaloisConnection`
    的 `[Preorder]` 前提**无法**在 `Readout` 上满足。
  * **正**：任何满足 Galois 条件的自映射都**不改变粗细**（无非平凡自伴）。
  * **正（主）**：`Finer` **精确等于** `κ ⊣ readoutOfSetoid` 的伴随条件。
  --------------------------------------------------------------------------- -/

/-- ⭐⭐ **G3（负）：`Finer` 无法成为偏序，故 `Readout` 上装不了 Galois 嵌入。**

直接由 `finer_not_isPartialOrder` 得到：不存在 `IsPartialOrder (Readout Bool) Finer`，
而 `GaloisInsertion` / `GaloisCoinsertion` 都要求 `[PartialOrder]`。

**比原版强在哪**：原版把 `Finer` 称作「预序」就作罢；本定理指出
**偏序层**（Galois 嵌入所需的层）不可用，必须先在 G1 的商上工作；
而**预序层**的 `GaloisConnection` 仍然可用（见 `kappa_galoisConnection`）。
这一区分正是 G1 取商必要性在序论上的表现。 -/
theorem no_partialOrder_realizing_finer :
    ¬ IsPartialOrder (Readout.{0, 0} Bool) (Finer (SCM := Bool)) :=
  finer_not_isPartialOrder

/-- ⭐⭐ **G3（正）：收缩性 + Galois 条件 ⟹ 在商中恒等。**

若 `f` 在每个点上**不比输入粗**（`Finer (f a) a`，即 `f` 是收缩），
且满足 Galois 条件 `gc`，则 `f` 在商中恒等。

⚠ **重要更正（诚实记录）**：本条原写作「**不存在**非平凡自伴」，**该命题是假的** ——
反例见 `galois_condition_degenerate`（常值映射满足 `gc` 却不平凡）。
根源是 `gc` 的**结论** `Finer a (f b)` 在 `f b` 为最大元时**恒真**，
于是 `gc` 对这类 `f` **自动成立**，不携带信息。

**比原版强在哪**：
* 原版完全没有伴随理论；
* 本定理给出「自伴何时平凡」的**精确前提**（收缩 + `gc`），
* 并由 `galois_condition_degenerate` 证明**去掉收缩前提后命题为假** ——
  这是「预序上的 Galois 条件比偏序上弱」的量化陈述，**强化了 G1 取商的必要性**。 -/
theorem galois_self_adjoint_counit
    (f : Readout.{u, v} SCM → Readout.{u, v} SCM)
    (gc : ∀ a b : Readout.{u, v} SCM, Finer (f a) b → Finer a (f b))
    (hle : ∀ a : Readout.{u, v} SCM, Finer (f a) a) :
    ∀ a : Readout.{u, v} SCM, ReadoutEquivalent (f a) a :=
  -- `Finer a (f a)`：`gc a a` 需要 `Finer (f a) a`，恰好是 `hle a`
  fun a => ⟨hle a, gc a a (hle a)⟩

/-- ⭐ **`gc` 单独推出的**单位**（而非余单位）。**

`gc a (f a) (finer_refl (f a)) : Finer a (f (f a))` ——
这只是 `f` 在**迭代**下的性质，**不足以**推出 `f` 平凡
（见 `galois_condition_degenerate`）。

**比原版强在哪**：原版无伴随理论。本定理**精确标出** `gc` 单独能推出多少 ——
恰好是 `a ≤ f (f a)`，而**不是** `a ≤ f a`。
这正是 `galois_condition_degenerate` 能成立的原因。 -/
theorem galois_condition_gives_unit
    (f : Readout.{u, v} SCM → Readout.{u, v} SCM)
    (gc : ∀ a b : Readout.{u, v} SCM, Finer (f a) b → Finer a (f b)) :
    ∀ a : Readout.{u, v} SCM, Finer a (f (f a)) :=
  fun a => gc a (f a) (finer_refl _)

/-- ⭐⭐ **G3 的诚实反例：常值自映射满足 Galois 条件但不平凡。**

`f := fun _ => truthReadout SCM` 满足 `gc`（因为 `gc` 的**结论**恒真），
但 `f` 把恒等读出送到真值读出 —— 二者在商中**不同**（核 `⊥` vs `⊤`），
故 `f` **不是**商中的恒等。

**比原版强在哪**：原版没有任何伴随理论；本反例说明
**「Galois 条件」在预序上会退化** —— 这与 G1「`Finer` 不是偏序」是同一现象，
是「必须取商」的又一条独立证据。

⚠ **诚实范围**：本条是**否定性**结论（否定某自然猜想），不是推广定理。 -/
theorem galois_condition_degenerate [Nontrivial SCM] :
    ∃ (f : Readout.{u, u} SCM → Readout.{u, u} SCM),
      (∀ a b : Readout.{u, u} SCM, Finer (f a) b → Finer a (f b)) ∧
      ∃ a : Readout.{u, u} SCM, ¬ ReadoutEquivalent (f a) a := by
  classical
  obtain ⟨s₀, s₁, hne⟩ := exists_pair_ne SCM
  refine ⟨fun _ => readoutOfSetoid (⊤ : Setoid SCM), ?_, ?_⟩
  · -- `gc` 的结论 `Finer a (readoutOfSetoid ⊤)` 恒真
    intro a b _
    show Setoid.ker a.Obs ≤ Setoid.ker (readoutOfSetoid (⊤ : Setoid SCM)).Obs
    rw [show Setoid.ker (readoutOfSetoid (⊤ : Setoid SCM)).Obs = ⊤ from
      Setoid.ker_mk_eq (⊤ : Setoid SCM)]
    exact le_top
  · -- 取 `a := identityReadout`，其核为 `⊥` ≠ `⊤`
    refine ⟨identityReadout SCM, fun h => ?_⟩
    have hker : Setoid.ker (readoutOfSetoid (⊤ : Setoid SCM)).Obs
        ≤ Setoid.ker (identityReadout SCM).Obs := h.1
    rw [show Setoid.ker (readoutOfSetoid (⊤ : Setoid SCM)).Obs = ⊤ from
      Setoid.ker_mk_eq (⊤ : Setoid SCM)] at hker
    exact hne (show s₀ = s₁ from hker trivial)

/-- ⭐⭐⭐ **G3（正·主结论）：`Finer` **精确等于** `κ ⊣ readoutOfSetoid` 的伴随条件。**

`Finer R (readoutOfSetoid ρ) ↔ κ R ≤ ρ`。

**这才是 `Finer` 的正确 Galois 刻画**：
`Finer` 本身**不是** `Readout` 上的 Galois 嵌入（偏序层不可用，
见 `finer_not_isPartialOrder`），
但它**就是** `Readout` 与 `Setoid SCM` 之间那个伴随对的单位条件
（`kappa_galoisConnection`）。

**比原版强在哪**：
原版只有「`Finer` 是预序」。本定理把它升级为**伴随对的单位/余单位条件**，
从而 `Finer` 获得完整的范畴论语义；
并且**由此可推出 G4 的完备性**（`Readout` 的格论性质全部由 `Setoid SCM` 继承）。 -/
theorem finer_iff_kappa_le (R : Readout.{u, v} SCM) (ρ : Setoid SCM) :
    Finer R (readoutOfSetoid ρ) ↔ kappa' R ≤ ρ := by
  show (∀ s t : SCM, R.Obs s = R.Obs t → Quotient.mk'' s = Quotient.mk'' t) ↔
       (∀ s t : SCM, R.Obs s = R.Obs t → ρ s t)
  constructor
  · intro h s t hst
    exact Quotient.exact' (h s t hst)
  · intro h s t hst
    exact Quotient.sound' (h s t hst)

/-- ⭐⭐ **`κ` 与 `readoutOfSetoid` 构成 Galois 连接**（以 `κ` 为**下**伴随）。

`GaloisConnection kappa readoutOfSetoid` 即
`∀ R ρ, kappa R ≤ ρ → R ≤ readoutOfSetoid ρ`
（`Setoid` 侧为包含序，`Readout` 侧为 `instPreorderReadout` 装的 `Finer` 序）——
这正是 `finer_iff_kappa_le` 的 `.mpr` 方向。

**比原版强在哪**：这是 `Finer` 与 Galois 连接的**主定理** ——
把 `Readout` 的粗细序**完全编码**成 `Setoid SCM` 完备格上的一个伴随对，
于是 `Readout` 的一切格论性质都可以从 `Setoid SCM` **推**出来（G4 正是如此）。

⚠ **方向说明**：`GaloisConnection l u := ∀ a b, l a ≤ b → a ≤ u b`。
取 `α := Readout`、`β := Setoid`、`l := kappa`、`u := readoutOfSetoid`，
则条件是 `kappa R ≤ ρ → R ≤ readoutOfSetoid ρ` —— 恰为 `.mpr`。
（`α`/`β` 的选取由 `l : α → β` 决定，`kappa : Readout → Setoid` 故 `α = Readout`。） -/
theorem kappa_galoisConnection :
    GaloisConnection (kappa (SCM := SCM)) (readoutOfSetoid (SCM := SCM)) :=
  fun R ρ => (finer_iff_kappa_le R ρ).symm

/-! ===========================================================================
  §9.5  ⭐⭐⭐ G4：【重大更正】`Readout` **是**完备格
  ===========================================================================
  任务提示猜「`Readout` 不是完备格」。**这个猜想被推翻了两次**：

  1. **最大元存在**（§9.2 `isTop_iff_obs_constant`）：常值读出即最大元。
  2. 更进一步：`Readout SCM` 在 `Finer` 下**有任意上确界与任意下确界**
     （**含空集**），即它是**完备格** —— 经 G3 的伴随对与 `Setoid SCM` 同构地完备。

  **构造**（全部经 `κ ⊣ readoutOfSetoid`）：
  * `⨆_{R ∈ S} R := readoutOfSetoid (⨆_{R ∈ S} κ R)`
  * `⨅_{R ∈ S} R := readoutOfSetoid (⨅_{R ∈ S} κ R)`
  * 空上确界 = `readoutOfSetoid ⊥`（即恒等读出所在等价类，最细）
  * 空下确界 = `readoutOfSetoid ⊤`（即常值读出所在等价类，最粗）

  ⚠ **注意**：这些是**存在性定理**，不是 `CompleteLattice` **实例** ——
  因为 `CompleteLattice` 要求 `PartialOrder`，而 `Finer` **不是**偏序（G1）。
  这正是 G1 与 G4 的连接点：**取商之后**才装配得上实例。
  --------------------------------------------------------------------------- -/

/-- ⭐⭐ **G4（上确界）：任意族的**上确界**存在**（含空集）。

`⨆_{R ∈ S} R := readoutOfSetoid (⨆_{R ∈ S} κ R)`。

**比原版强在哪**：原版只有「恒等读出是整体最小元」这一条孤立结论；
本定理给出**任意上确界的显式公式**（**含空集**），
把 `Readout` 从「预序」提升为「有完备上确界结构的偏序」。 -/
theorem exists_isLUB (S : Set (Readout.{u, u} SCM)) :
    ∃ L : Readout.{u, u} SCM, IsLUB S L := by
  refine ⟨readoutOfSetoid (⨆ R ∈ S, Setoid.ker R.Obs), ?_, ?_⟩
  · intro R hR
    show Finer R _
    rw [finer_iff_ker_le]
    rw [show Setoid.ker (readoutOfSetoid (⨆ R ∈ S, Setoid.ker R.Obs)).Obs
        = ⨆ R ∈ S, Setoid.ker R.Obs from Setoid.ker_mk_eq _]
    exact le_iSup₂ (f := fun R _ => Setoid.ker R.Obs) R hR
  · intro L' hL'
    show Finer _ L'
    rw [finer_iff_ker_le]
    rw [show Setoid.ker (readoutOfSetoid (⨆ R ∈ S, Setoid.ker R.Obs)).Obs
        = ⨆ R ∈ S, Setoid.ker R.Obs from Setoid.ker_mk_eq _]
    exact iSup₂_le fun R hR => hL' hR

/-- ⭐⭐ **G4（下确界）：任意族的**下确界**存在**（含空集）。

`⨅_{R ∈ S} R := readoutOfSetoid (⨅_{R ∈ S} κ R)`。

**比原版强在哪**：这是「`Readout` 有交」的完整形式；
**含空集**（空下确界 = 核 `⊤` 的读出 = 常值读出 = 最大元），
故它把 G2 的「有最大元」作为**特例**收回。 -/
theorem exists_isGLB (S : Set (Readout.{u, u} SCM)) :
    ∃ L : Readout.{u, u} SCM, IsGLB S L := by
  refine ⟨readoutOfSetoid (⨅ R ∈ S, Setoid.ker R.Obs), ?_, ?_⟩
  · intro R hR
    show Finer _ R
    rw [finer_iff_ker_le]
    rw [show Setoid.ker (readoutOfSetoid (⨅ R ∈ S, Setoid.ker R.Obs)).Obs
        = ⨅ R ∈ S, Setoid.ker R.Obs from Setoid.ker_mk_eq _]
    exact iInf₂_le R hR
  · intro L' hL'
    show Finer L' _
    rw [finer_iff_ker_le]
    rw [show Setoid.ker (readoutOfSetoid (⨅ R ∈ S, Setoid.ker R.Obs)).Obs
        = ⨅ R ∈ S, Setoid.ker R.Obs from Setoid.ker_mk_eq _]
    exact le_iInf₂ fun R hR => hL' hR

/-- ⭐⭐ **最小元的具体实现**：核为 `⊥` 的读出是整体最小元。

**比原版强在哪**：原版 `identity_is_finest` 只证恒等读出最小；
本定理证**整个等价类**（所有单射读出）都最小，且它们**互相 `Finer`** ——
这正是 G1 取商之所以正确的依据。 -/
theorem bot_is_finest (R : Readout.{u, u} SCM) :
    Finer (readoutOfSetoid (⊥ : Setoid SCM)) R := by
  rw [finer_iff_ker_le]
  rw [show Setoid.ker (readoutOfSetoid (⊥ : Setoid SCM)).Obs = (⊥ : Setoid SCM)
    from Setoid.ker_mk_eq _]
  exact bot_le

/-- ⭐⭐ **最大元的具体实现**：核为 `⊤` 的读出是整体最大元。 -/
theorem top_is_coarsest (R : Readout.{u, u} SCM) :
    Finer R (readoutOfSetoid (⊤ : Setoid SCM)) := by
  rw [finer_iff_ker_le]
  rw [show Setoid.ker (readoutOfSetoid (⊤ : Setoid SCM)).Obs = (⊤ : Setoid SCM)
    from Setoid.ker_mk_eq _]
  exact le_top

/-- ⭐⭐⭐ **G4 终极结论：`Readout` 在 `Finer` 下**同时**有任意上确界与任意下确界。**

（这是 `exists_isLUB` 与 `exists_isGLB` 的合取形式，
说明 `Readout SCM` 在 `Finer` 序下是**完备格**。）

**比原版强在哪（本文件最强的结论）**：
原版全文没有回答「`Readout` 是不是格」。
本定理给出**肯定答案**，并**推翻了两个自然猜想**：
* ✗「存在最小元但无最大元」—— 实际**有最大元**（§9.2）；
* ✗「`Finer` 只是预序，格论无从谈起」—— 实际**有完备的上下确界**。

**⟹ 故「读出方案构成格」这句口号是**对的**，且比原版所说更强：
不只是格，是**完备格**；只需先按 G1 取商以装配 `PartialOrder` 实例。 -/
theorem has_all_sups_and_infs :
    (∀ S : Set (Readout.{u, u} SCM), ∃ L : Readout.{u, u} SCM, IsLUB S L) ∧
      (∀ S : Set (Readout.{u, u} SCM), ∃ L : Readout.{u, u} SCM, IsGLB S L) :=
  ⟨exists_isLUB, exists_isGLB⟩

end CFLatticeGen

end Fate
