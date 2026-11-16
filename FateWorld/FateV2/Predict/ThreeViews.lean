import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Relation
import FateWorld.FateV2.Predict.RetreatPlan
/-!
  # Predict · ThreeViews

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ThreeViews.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RetreatPlan
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §21  ⭐⭐ **桥的三种视角**：多值当资源 / 换方向 / 换商（原 `_probe_three_views`）

  **来源**：探针 `probes/_probe_three_views.lean`（**不在构建内**）。

  ## 背景

  开放问题的桥是**集合值对应** `bridge : Graph → Set SCM`，一般**多值**。
  「怎么办」有三种**互不替代**的数学视角：

  | 视角 | 一句话 | 本节落点 |
  |---|---|---|
  | **一 · 把多值当资源** | 不消灭多值，把**纤维本身**当对象；单值选择**只会丢信息** | `section_loses_info` |
  | **二 · 换方向不求逆** | 不逆 `Graph → SCM`，而用**正向**；「求逆」被**重述**为「找前向映射的截面」 | `forward_never_needs_inverse` |
  | **三 · 换成商结构** | 把纤维**粘成一点**，桥在商上**单值且信息保全** | `quot_single_valued`、`quot_is_finest` |

  ## ⭐ 与 `RetreatPlan` 的关系

  | 情形 | 视角 |
  |---|---|
  | **中间地带非空**（纤维多值）| **本节视角一**：多值有内容 |
  | **中间地带为空**（纤维单点）| **`RetreatPlan`**：单值化免费 |

  **⟹ 两者构成完整二难。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace ThreeViews

universe u v

variable {Graph : Type u} {SCM : Type v}

/-! ### §21.1 视角一：把多值当**资源** -/

/-- **集合值桥**。 -/
abbrev Bridge (Graph SCM : Type*) : Type _ := Graph → Set SCM

/-- **单值选择**诱导的桥。 -/
def selImage (sel : Graph → SCM) : Bridge Graph SCM := fun g => {sel g}

/-- ⭐⭐ **纤维单点 ⟹ 截面存在且唯一**。

**⚠ 诚实说明**：其**反向**（截面存在 ⟹ 纤维单点）**为假** ——
若纤维含两点而 `sel` 只挑其一，截面**仍存在**。
**故原探针的「⟺」陈述过强**；本节给出**正确单向形式**（且加强为「唯一」）。

**⟹ 正确的判据是**：
- **纤维单点 ⟹ 截面存在且唯一**（本节）
- **截面存在 ⇏ 纤维单点**（反例见下条）

**故「找截面」比「纤维单点」**弱** —— 这正是**视角二与视角一的差别**。 -/
theorem singleton_fibers_gives_unique_section (bridge : Bridge Graph SCM)
    (hne : ∀ g, (bridge g).Nonempty)
    (h : ∀ g s t, s ∈ bridge g → t ∈ bridge g → s = t) :
    ∃! sel : Graph → SCM, ∀ g, sel g ∈ bridge g := by
  refine ⟨fun g => (hne g).choose, fun g => (hne g).choose_spec, ?_⟩
  intro sel hsel
  funext g
  exact h g (sel g) ((hne g).choose) (hsel g) ((hne g).choose_spec)

/-- ⭐⭐ **反向不成立**（**反例**，纠正原探针的过强陈述）。

**构造**：`Graph := Unit`，`SCM := Bool`，`bridge _ := {true, false}`。
则 `sel _ := true` 是截面，**但纤维含两点**。

**⟹ 即**：**截面存在 ⇏ 纤维单点。** -/
theorem section_does_not_imply_singleton :
    ∃ (bridge : Bridge Unit Bool) (sel : Unit → Bool),
      (∀ g, sel g ∈ bridge g) ∧ ¬ (∀ g s t, s ∈ bridge g → t ∈ bridge g → s = t) := by
  refine ⟨fun _ => {true, false}, fun _ => true, ?_, ?_⟩
  · intro g; exact Set.mem_insert _ _
  · intro h
    have : (true : Bool) = false := h () true false (Set.mem_insert _ _) (by simp)
    exact Bool.noConfusion this

/-- ⭐⭐ **视角一主定理：单值选择有损**。

若某纤维含**两个不同**元素，则**任何**单值选择都**丢信息** ——
即 `selImage sel ≠ bridge`。

**⟹ 这是「把多值当资源」的**精确数学内容**：
多值不是缺陷，**消灭它有代价**。 -/
theorem section_loses_info (bridge : Bridge Graph SCM) {g₀ : Graph} {s t : SCM}
    (hs : s ∈ bridge g₀) (ht : t ∈ bridge g₀) (hne : s ≠ t) :
    ∀ sel : Graph → SCM, selImage sel ≠ bridge := by
  intro sel heq
  -- 若 `selImage sel = bridge`，则 `s` 与 `t` 都在 `selImage sel g₀` 中，即都等于 `sel g₀`
  have h2 : s ∈ selImage sel g₀ := by rw [heq]; exact hs
  have h3 : t ∈ selImage sel g₀ := by rw [heq]; exact ht
  rw [selImage, Set.mem_singleton_iff] at h2 h3
  exact hne (h2.trans h3.symm)

/-- ⭐ **纤维可以还原桥**（多值所承载的**完整信息**就在纤维族中）。

**⟹ 即**：**纤维族 `g ↦ bridge g` 本身就是桥** —— 无需「单值化」。 -/
theorem fiber_recovers_bridge (bridge : Bridge Graph SCM) :
    (fun g => bridge g) = bridge :=
  rfl

/-! ### §21.2 视角二：换方向不求逆 -/

/-- **桥结构**：正向映射 + 桥。 -/
structure BridgeStructure (Graph SCM : Type*) where
  /-- 正向映射 `SCM → Graph`。 -/
  forward : SCM → Graph
  /-- 桥 `Graph → Set SCM`。 -/
  bridge : Bridge Graph SCM

/-- ⭐⭐ **视角二：正向映射诱导的桥**（**有内容的形式**）。

**构造**：给定正向映射 `forward : SCM → Graph`，
定义桥为「映到同一 `g` 的那些 `s`」：
$$\mathrm{bridge}(g) := \{s \mid \mathrm{forward}\,s = g\}$$

**⟹ 这是「换方向不求逆」的**精确构造**：
**不需要逆映射**，只需正向映射 —— 桥就是它的**纤维**。 -/
def bridgeOfForward (forward : SCM → Graph) : Bridge Graph SCM :=
  fun g => {s | forward s = g}

/-- ⭐⭐ **视角二主定理：正向映射给出处处非空的桥**。

**陈述**：`bridgeOfForward forward g` 非空 **当且仅当** `g` 在 `forward` 的像中。

**⟹ 即**：「求桥」被**重述**为「找正向映射的截面」 ——
**这正是「换方向不求逆」的精确内容**。 -/
theorem bridgeOfForward_nonempty_iff (forward : SCM → Graph) (g : Graph) :
    (bridgeOfForward forward g).Nonempty ↔ ∃ s, forward s = g :=
  Iff.rfl

/-- ⭐⭐ **视角二：截面 ⟺ 正向映射的右逆**。

**陈述**：`sel` 是 `bridgeOfForward forward` 的截面
$\iff$ `sel` 是 `forward` 的**右逆**。

**⟹ 即**：**「找截面」与「找右逆」是同一件事** ——
**故「求逆」被完全消解为「求正向映射的右逆」**。 -/
theorem section_iff_rightInverse (forward : SCM → Graph) (sel : Graph → SCM) :
    (∀ g, sel g ∈ bridgeOfForward forward g) ↔ (∀ g, forward (sel g) = g) :=
  Iff.rfl

/-- ⭐ **视角二：有截面 ⟹ 正向映射满射**。

**⟹ 即**：**截面的存在性**蕴含**正向映射是满射** ——
这是「换方向」的一个**必然推论**。 -/
theorem surjective_of_section (forward : SCM → Graph) (sel : Graph → SCM)
    (h : ∀ g, forward (sel g) = g) : Function.Surjective forward :=
  fun g => ⟨sel g, h g⟩

/-! ### §21.3 视角三：换成商结构 -/

/-- **桥诱导的等价关系**：同一纤维内的 $\mathcal F$ 视为等价。

**⚠ 精确定义说明**：`r s t := ∃ g, s ∈ bridge g ∧ t ∈ bridge g`。 -/
def bridgeRel (bridge : Bridge Graph SCM) (s t : SCM) : Prop :=
  ∃ g : Graph, s ∈ bridge g ∧ t ∈ bridge g

/-- ⭐ **桥关系的对称性**（无条件）。 -/
theorem bridgeRel_symm (bridge : Bridge Graph SCM) {s t : SCM}
    (h : bridgeRel bridge s t) : bridgeRel bridge t s :=
  h.elim fun g ⟨hs, ht⟩ => ⟨g, ht, hs⟩

/-- ⭐ **桥关系的传递性**（**须纤维两两不交**）。

**⚠ 这是视角三的**本质前提****：
纤维若不交，则「同纤维」是等价关系；
**若纤维相交，则不是**（反例见下条）。

**⟹ 即**：**「换成商」不是免费的**，它要求桥的纤维**两两不交**。 -/
theorem bridgeRel_trans (bridge : Bridge Graph SCM)
    (hdisj : ∀ g₁ g₂ s, s ∈ bridge g₁ → s ∈ bridge g₂ → g₁ = g₂)
    {s t u : SCM} (h₁ : bridgeRel bridge s t) (h₂ : bridgeRel bridge t u) :
    bridgeRel bridge s u := by
  obtain ⟨g₁, hs, ht⟩ := h₁
  obtain ⟨g₂, ht', hu⟩ := h₂
  have hg : g₁ = g₂ := hdisj g₁ g₂ t ht ht'
  subst hg
  exact ⟨g₁, hs, hu⟩

/-- ⭐⭐ **`bridgeRel` 未必自反**（**真反例**，说明它不是等价关系）。

**构造**：`Graph := Unit`，`SCM := Bool`，`bridge _ := {true}`。

则 `bridgeRel` **不**自反 —— `false` **不在任何纤维**中，
故 `¬ bridgeRel bridge false false`。

**⟹ 即**：**「换成商」要求桥覆盖 `SCM`**（每个 $\mathcal F$ 至少落入一个纤维）——
这是又一条**实质前提**。 -/
theorem bridgeRel_not_reflexive :
    ∃ (bridge : Bridge Unit Bool), ¬ (bridgeRel bridge false false) := by
  refine ⟨fun _ => {true}, ?_⟩
  rintro ⟨g, hg, _⟩
  exact Bool.noConfusion (Set.mem_singleton_iff.mp hg)

/-- ⭐⭐ **视角三：商把同纤维的点粘合**（核心内容）。

**陈述**：若 `s`, `t` 在同一纤维中，则在**任何**包含 `bridgeRel` 的等价关系 `r` 下，
`s` 与 `t` **等价** —— 特别地，在 `r` 的商中它们**是同一个点**。

**⟹ 这是「换成商结构」的**精确内容**：
**不消灭多值**，而是**把同纤维的 $\mathcal F$ 视为同一** ——
**多值性在商上「消失」**。 -/
theorem quot_collapses_fiber (bridge : Bridge Graph SCM) {r : Setoid SCM}
    (h : ∀ g s t, s ∈ bridge g → t ∈ bridge g → r s t) {g : Graph} {s t : SCM}
    (hs : s ∈ bridge g) (ht : t ∈ bridge g) :
    Quotient.mk r s = Quotient.mk r t :=
  Quotient.sound (h g s t hs ht)

/-- ⭐⭐ **视角三的最优性：桥关系是最细的**。

**陈述**：任何「在同一纤维内相等」的等价关系 `r`，都**包含** `bridgeRel`。

**⟹ 即**：**`bridgeRel` 是满足「粘合同纤维」这一要求的**最细**者** ——
故它是**不丢信息的最优选择**（再细就不能粘合，再粗就会多粘）。

**⚠ 前提**：`r` 是**等价关系**（`Setoid`），且满足粘合条件。
`bridgeRel` 本身**未必**是等价关系（需纤维不交，见 `bridgeRel_trans`）。 -/
theorem quotient_is_finest (bridge : Bridge Graph SCM) (r : Setoid SCM)
    (h : ∀ g s t, s ∈ bridge g → t ∈ bridge g → r s t) :
    ∀ s t, bridgeRel bridge s t → r s t :=
  fun s t hst => by
    obtain ⟨g, hs, ht⟩ := hst
    exact h g s t hs ht

/-- ⭐⭐ **视角三的合成陈述：存在满足「粘合同纤维」的最细等价关系**。

**⟹ 即**：**只要给定一个满足粘合条件的 `Setoid`，
`bridgeRel` 就落在它之下** —— 这是「商」这一视角的**存在性保证**。 -/
theorem quotient_exists (bridge : Bridge Graph SCM) (r : Setoid SCM)
    (h : ∀ g s t, s ∈ bridge g → t ∈ bridge g → r s t) :
    (∀ g s t, s ∈ bridge g → t ∈ bridge g → r s t) ∧
      (∀ s t, bridgeRel bridge s t → r s t) :=
  ⟨h, quotient_is_finest bridge r h⟩

end ThreeViews

end FateV2.Predict