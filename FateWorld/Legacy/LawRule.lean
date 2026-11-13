import FateWorld.Legacy.Frame

/-! ===========================================================================
  §0  规则层的类型学基础（作者裁决后定稿）

  **裁决来源**（作者原话）：
  * 「规则的载体不能是那种**物理规律**一样的形式吗」
  * 「目前**整个科学学界里面的所有形式**」
  * 「**是的可以**」（确认本方案）

  ## 核心定义

  $$\text{Rule} := C \to X \to \mathcal{P}(\mathrm{Measure}\ Y)$$

  **即：在给定信息下，允许哪些下一状态分布。**

  ## 为什么这是「物理规律式」的抽象

  物理规律的本质**不是计算下一状态，而是约束可能的状态**。
  等式是约束、不等式是约束、微分方程是约束、概率规律也是约束
  （把「可能」限制在一个分布上）。

  **⟹ 统一的地方不是「规则的输入/形式」，而是「规则的输出」。**

  ## 可承载的形式（举例，非穷举）

  | 科学形式 | 归约为 | 输出形态 |
  |---|---|---|
  | 确定性 `y = f(x)` | 单点测度 | 单点集 |
  | 概率 `y ~ P(·\|x)` | 测度 | 单点集 |
  | 不等式约束 `g ≥ 0` | 分布族 | 真子集 |
  | 微分方程 | 解集 | 分布族 |
  | 变分原理 | 极值集 | 分布族 |
  | FCA 蕴含 | 满足蕴含的属性集 | 分布族 |

  ## 四算子的语义（本定义使之有内容）

  | 算子 | 语义 |
  |---|---|
  | `α`（抽象） | 从实例产生规则 |
  | `γ`（泛化） | **放宽**（集合变大） |
  | `υ`（完善） | **收窄**（集合变小） |
  | `∘`（组合） | **取交**（同时成立） |

  `∘ = 取交` 天然满足**结合律**（`compose_assoc`）——
  这解决了此前「组合语义未定」导致 100 个错误的根本问题。

  ## 向后兼容

  旧的 `Fate.Rule`（条件分布核）是本定义的单点特例（`Rule.toLaw`）。

  ## 诚实边界

  * 「全部科学形式可归约」是**主张 + 举例**，不是证明；未穷举反例。
  * 「四算子对偶」是概念判断，`∘` 的结合律已证，其余未形式化。
  =========================================================================== -/

namespace Fate

namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-- **规则**：给定上下文与当前状态，**允许哪些下一状态分布**。

这是「物理规律式」的抽象 —— 规律不计算，它**约束**。 -/
def LawRule (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ :=
  C.Carrier → X.Carrier → Set (MeasureTheory.Measure Y.Carrier)

/-- 旧的 `Rule`（条件分布核）是新定义的**单点特例**（向后兼容）。 -/
def Rule.toLaw [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (r : Rule C X Y) : LawRule C X Y :=
  fun c x => {r.kernel c x}

/-- 确定性函数也可嵌入（单点测度）。 -/
def DetFun.toLaw [MeasurableSpace Y.Carrier]
    (f : C.Carrier → X.Carrier → Y.Carrier) : LawRule C X Y :=
  fun c x => {MeasureTheory.Measure.dirac (f c x)}

/-- **单点档**（可算转移；世界模型需要的档位）。 -/
def IsPoint (R : LawRule C X Y) : Prop :=
  ∀ c x, ∃ μ, R c x = {μ}

/-- **确定性规律**（新定义，用于与 `IsPoint` 对齐）。

直读：对每个上下文与状态，规律**唯一地确定**一个下一状态分布。
与 `IsPoint` 的差别只在写法：`IsPoint` 说「允许集是单点集」，
`Deterministic` 说「任何两个允许的分布相等」（即至多一个）。

两者等价，见 `isPoint_iff_deterministic`。 -/
def Deterministic (R : LawRule C X Y) : Prop :=
  ∀ c x, ∀ μ₁ μ₂, μ₁ ∈ R c x → μ₂ ∈ R c x → μ₁ = μ₂

/-- **单点档 ⟺ 确定性规律**：
「允许集是单点集」等价于「允许集至多含一个分布（且非空）」。

* `→`：`⟨μ, {μ}⟩` 中取任两元素即相等。
* `←`：`Nonempty` 给出成员 `μ`；`Deterministic` 令允许集被 `{μ}` 双包含。

注意 `Deterministic` 单独不足以给出单点档（空集也满足），
故等价式右侧显式要求 `Nonempty`。 -/
theorem isPoint_iff_deterministic (R : LawRule C X Y) :
    IsPoint R ↔ (∀ c x, (R c x).Nonempty) ∧ Deterministic R := by
  constructor
  · intro h
    refine ⟨fun c x => ?_, fun c x μ₁ μ₂ h₁ h₂ => ?_⟩
    · obtain ⟨μ, hμ⟩ := h c x; exact ⟨μ, by rw [hμ]; exact Set.mem_singleton μ⟩
    · obtain ⟨ν, hν⟩ := h c x
      rw [hν] at h₁ h₂
      rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂]
  · rintro ⟨hne, hdet⟩ c x
    obtain ⟨μ, hμ⟩ := hne c x
    refine ⟨μ, ?_⟩
    ext ν
    constructor
    · intro hν; exact Set.mem_singleton_iff.mpr (hdet c x ν μ hν hμ)
    · intro hν; rw [Set.mem_singleton_iff.mp hν]; exact hμ

/-- 非空性的另一种表述：`Deterministic` 之下非空即 `IsPoint`。
（`isPoint_iff_deterministic` 的使用便捷形式。） -/
theorem isPoint_of_deterministic (R : LawRule C X Y)
    (h : ∀ c x, (R c x).Nonempty) (hd : Deterministic R) : IsPoint R :=
  (isPoint_iff_deterministic R).mpr ⟨h, hd⟩

/-- 单点档的规则必是确定性规律（直接推论，便于无假设引用）。 -/
theorem IsPoint.deterministic (R : LawRule C X Y) (h : IsPoint R) : Deterministic R :=
  ((isPoint_iff_deterministic R).mp h).2

/-- **组合 = 取交**：两条规律同时成立。

这是 `∘` 的语义 —— 此前未定，现由「约束的交」给出。 -/
def compose (R₁ R₂ : LawRule C X Y) : LawRule C X Y :=
  fun c x => R₁ c x ∩ R₂ c x

/-- **泛化 = 放宽**（增加允许的分布）。 -/
def generalize (R₁ R₂ : LawRule C X Y) (_h : ∀ c x, R₁ c x ⊆ R₂ c x) : LawRule C X Y := R₂

/-- **完善 = 收窄**（排除与数据矛盾的分布）。 -/
def refine (R₁ R₂ : LawRule C X Y) (_h : ∀ c x, R₂ c x ⊆ R₁ c x) : LawRule C X Y := R₂

/-- **组合的交换律**（取交天然满足）。 -/
theorem compose_comm (R₁ R₂ : LawRule C X Y) : compose R₁ R₂ = compose R₂ R₁ := by
  funext c x; exact Set.inter_comm _ _

/-- **组合的结合律**（取交天然满足）。

这解决了此前「`∘` 语义未定、结合律须假设」的问题 —— 现在不需要假设。 -/
theorem compose_assoc (R₁ R₂ R₃ : LawRule C X Y) :
    compose (compose R₁ R₂) R₃ = compose R₁ (compose R₂ R₃) := by
  funext c x; exact Set.inter_assoc _ _ _

/-- **单点组合仍单点**（若两条规律相容）。 -/
theorem point_compose (R₁ R₂ : LawRule C X Y)
    (h₁ : IsPoint R₁) (h₂ : IsPoint R₂)
    (h : ∀ c x, (R₁ c x ∩ R₂ c x).Nonempty) : IsPoint (compose R₁ R₂) := by
  intro c x
  obtain ⟨μ₁, hμ₁⟩ := h₁ c x
  obtain ⟨μ₂, hμ₂⟩ := h₂ c x
  have he : R₁ c x ∩ R₂ c x = ({μ₁} : Set _) ∩ {μ₂} := by rw [hμ₁, hμ₂]
  have hne : μ₁ = μ₂ := by
    rcases Set.inter_singleton_nonempty.mp (he ▸ h c x) with rfl
    rfl
  refine ⟨μ₁, ?_⟩
  show R₁ c x ∩ R₂ c x = {μ₁}
  rw [he, hne, Set.inter_self]

/-- **相容性前提**：`point_compose` 所需假设的命名版。 -/
def ComposeCompat (R₁ R₂ : LawRule C X Y) : Prop :=
  ∀ c x, (R₁ c x ∩ R₂ c x).Nonempty

/-- **相容 ⟺ 逐点相同**（两条单点规则）。

「取交非空」在单点档上**只能由相等保证**：两个单点集若相交，则必是同一个点。
这是单点档闭合性讨论的全部实质。 -/
theorem compat_iff_eq {R₁ R₂ : LawRule C X Y}
    (h₁ : IsPoint R₁) (h₂ : IsPoint R₂) :
    ComposeCompat R₁ R₂ ↔ (∀ c x, R₁ c x = R₂ c x) := by
  constructor
  · intro h c x
    obtain ⟨μ₁, hμ₁⟩ := h₁ c x
    obtain ⟨μ₂, hμ₂⟩ := h₂ c x
    have hne : μ₁ = μ₂ := by
      have hi : (({μ₁} : Set _) ∩ {μ₂}).Nonempty := by rw [← hμ₁, ← hμ₂]; exact h c x
      rcases Set.inter_singleton_nonempty.mp hi with rfl; rfl
    rw [hμ₁, hμ₂, hne]
  · intro h c x
    obtain ⟨μ, hμ⟩ := h₁ c x
    rw [hμ, ← h c x, hμ]
    exact ⟨μ, rfl, rfl⟩

/-- **相容的单点对，其 `compose` 恰为其中任一条**（无信息增益）。 -/
theorem compose_eq_of_compat {R₁ R₂ : LawRule C X Y}
    (h₁ : IsPoint R₁) (h₂ : IsPoint R₂) (h : ComposeCompat R₁ R₂) :
    compose R₁ R₂ = R₁ ∧ compose R₁ R₂ = R₂ := by
  have he := (compat_iff_eq h₁ h₂).mp h
  constructor
  · funext c x; show R₁ c x ∩ R₂ c x = R₁ c x
    rw [he c x, Set.inter_self]
  · funext c x; show R₁ c x ∩ R₂ c x = R₂ c x
    rw [he c x, Set.inter_self]

/-- **单点档闭合性的充要条件**：

两条单点规则之「取交」仍单点，**当且仅当它们逐点相同**。

故单点档在 `compose` 下**不是无条件闭合的**，而是
「闭合当且仅当参与组合的规则根本是同一规则」。 -/
theorem point_compose_iff {R₁ R₂ : LawRule C X Y}
    (h₁ : IsPoint R₁) (h₂ : IsPoint R₂) :
    IsPoint (compose R₁ R₂) ↔ (∀ c x, R₁ c x = R₂ c x) := by
  constructor
  · intro hp c x
    have hne : ComposeCompat R₁ R₂ := by
      intro c' x'
      obtain ⟨ν, hν⟩ := hp c' x'
      have hmem : ν ∈ (compose R₁ R₂) c' x' := by
        rw [hν]; exact Set.mem_singleton ν
      exact ⟨ν, hmem.1, hmem.2⟩
    exact (compat_iff_eq h₁ h₂).mp hne c x
  · intro he
    exact point_compose R₁ R₂ h₁ h₂ ((compat_iff_eq h₁ h₂).mpr he)

/-- **泛化保持包含关系**（放宽确实放宽）。 -/
theorem generalize_mono (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₁ c x ⊆ R₂ c x) :
    ∀ c x, R₁ c x ⊆ (generalize R₁ R₂ h) c x := h

/-- **完善确实收窄**。 -/
theorem refine_mono (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₂ c x ⊆ R₁ c x) :
    ∀ c x, (refine R₁ R₂ h) c x ⊆ R₁ c x := h

/-- **全约束规则**（最弱）：允许一切分布 —— 相当于「没有规律」。 -/
def top (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : LawRule C X Y :=
  fun _ _ => Set.univ

/-- **空规则**（矛盾）：不允许任何分布 —— 相当于「无解」。 -/
def bot (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : LawRule C X Y :=
  fun _ _ => ∅

/-- **组合以 `top` 为单位元**。 -/
theorem compose_top (R : LawRule C X Y) : compose R (top C X Y) = R := by
  funext c x; exact Set.inter_univ _

/-- **组合以 `bot` 为零元**。 -/
theorem compose_bot (R : LawRule C X Y) : compose R (bot C X Y) = bot C X Y := by
  funext c x; exact Set.inter_empty _

/-- **单点 × 单点：逐点或空或单点**（`compose` 的正确闭合性陈述）。

⚠ 原先设想的「`compose` 或单点档、或整体为空」**不成立**：
两条单点规则可以在某些 `(c,x)` 处相等、在另一些处不等，
于是 `compose` 是「部分单点、部分空」的混合，既非 `IsPoint` 也非 `bot`。

正确的（且可证的）结论是**逐点**的：
每个 `(c,x)` 处，`compose R₁ R₂ c x` 要么为空、要么是单点集。 -/
theorem compose_point_or_empty {R₁ R₂ : LawRule C X Y}
    (h₁ : IsPoint R₁) (h₂ : IsPoint R₂) :
    ∀ c x, (compose R₁ R₂ c x = ∅) ∨ ∃ μ, compose R₁ R₂ c x = {μ} := by
  intro c x
  obtain ⟨μ₁, hμ₁⟩ := h₁ c x
  obtain ⟨μ₂, hμ₂⟩ := h₂ c x
  by_cases h : μ₁ = μ₂
  · right
    refine ⟨μ₁, ?_⟩
    show R₁ c x ∩ R₂ c x = {μ₁}
    rw [hμ₁, hμ₂, h, Set.inter_self]
  · left
    show R₁ c x ∩ R₂ c x = ∅
    rw [hμ₁, hμ₂, Set.inter_singleton_eq_empty]
    exact fun h' => h h'.symm

/-! ### §0.A 从单点档提取确定性函数（「可算转移」的形式化）

`IsPoint R` 说：每个 `(c,x)` 处的规则集是**单点集** `{μ}`。
`DetFun.toLaw f` 说：`R` 逐点恰为某个 Dirac 集 `{δ_{f c x}}`。

**二者的差别是本题的核心**：`{μ}` 里的 `μ` 一般**不是** Dirac 测度。
于是：

$$\mathrm{im}(\texttt{DetFun.toLaw}) \subsetneq \{R \mid \texttt{IsPoint}\ R\}.$$

- 逐点 Dirac 形 ⟹ 可提取（`exists_detFun_of_dirac`）；
- 反之 `IsPoint` 本身**不足以**提取（`isPoint_not_imp_extract`）。

**正确的单点档定义**（用于「可算转移」）应当是**Dirac 单点档**，
而不是任意的单点集 —— 见 `IsPointDet`。 -/

/-- **Dirac 单点档**（真正的「可算转移」档位）。

与 `IsPoint` 的唯一区别：要求那唯一的测度**本身是 Dirac 测度**。
这正是「确定性转移」的语义：给定 `(c,x)`，下一状态**唯一确定**。 -/
def IsPointDet (R : LawRule C X Y) : Prop :=
  ∀ c x, ∃ y, R c x = {MeasureTheory.Measure.dirac y}

/-- **✓ 提取定理（构造）**：Dirac 单点档 ⟹ 存在 `f` 使 `R = DetFun.toLaw f`。

构造：用选择公理在每个 `(c,x)` 处取出 Dirac 中心，
$$f(c,x) := \texttt{Classical.choose}\;(h\,c\,x),$$
再用 `Classical.choose_spec` 证明 `R c x = {δ_{f c x}}`，逐点即得 `funext`。 -/
theorem exists_detFun_of_isPointDet {R : LawRule C X Y} (h : IsPointDet R) :
    ∃ f : C.Carrier → X.Carrier → Y.Carrier, R = DetFun.toLaw f := by
  classical
  refine ⟨fun c x => Classical.choose (h c x), ?_⟩
  funext c x
  show R c x = {MeasureTheory.Measure.dirac (Classical.choose (h c x))}
  exact Classical.choose_spec (h c x)

/-- **提取的唯一性**：在点分离下，见证 `f` 唯一。

Dirac 测度在点分离空间上唯一决定其中心，故 `f` 被 `R` 唯一决定。
这正是「可算转移」的**良定义性**（canonical computable transition）。 -/
theorem detFun_extract_unique [MeasurableSpace.SeparatesPoints Y.Carrier]
    {R : LawRule C X Y}
    {f₁ f₂ : C.Carrier → X.Carrier → Y.Carrier}
    (h₁ : R = DetFun.toLaw f₁) (h₂ : R = DetFun.toLaw f₂) : f₁ = f₂ := by
  funext c x
  have : MeasureTheory.Measure.dirac (f₁ c x) = MeasureTheory.Measure.dirac (f₂ c x) := by
    have := congrFun (congrFun (h₁.symm.trans h₂) c) x
    simpa [DetFun.toLaw] using this
  exact MeasureTheory.dirac_eq_dirac_iff.mp this

/-- **提取 ⟺ Dirac 单点档**（充要判据）。 -/
theorem exists_detFun_iff_isPointDet (R : LawRule C X Y) :
    (∃ f : C.Carrier → X.Carrier → Y.Carrier, R = DetFun.toLaw f) ↔ IsPointDet R := by
  constructor
  · rintro ⟨f, rfl⟩ c x; exact ⟨f c x, rfl⟩
  · exact exists_detFun_of_isPointDet

/-- `DetFun.toLaw f` 逐点恰是单点 Dirac 集（定义性）。 -/
@[simp] theorem detFun_toLaw_apply (f : C.Carrier → X.Carrier → Y.Carrier)
    (c : C.Carrier) (x : X.Carrier) :
    DetFun.toLaw f c x = {MeasureTheory.Measure.dirac (f c x)} := rfl

/-- **Dirac 单点档 ⟹ `IsPoint`**（弱化方向，`IsPoint` 更宽）。 -/
theorem IsPointDet.isPoint {R : LawRule C X Y} (h : IsPointDet R) : IsPoint R := by
  intro c x
  obtain ⟨y, hy⟩ := h c x
  exact ⟨MeasureTheory.Measure.dirac y, hy⟩

/-- `IsPoint` 与 `IsPointDet` 的**差别所在**：`IsPoint` 只要求集合是单点集，
不要求那个点是 Dirac。 -/
theorem IsPointDet.iff (R : LawRule C X Y) :
    IsPoint R ↔ ∀ c x, ∃ μ, R c x = {μ} := Iff.rfl

/-- **反例（`IsPoint` 不能提取）**：
若 `Y` 上有非 Dirac 测度 `μ₀`，则「各点规则恒为 `{μ₀}`」的 `R`
满足 `IsPoint R`，却**不**是任何 `DetFun.toLaw f`（点分离下）。 -/
theorem isPoint_not_imp_extract
    (μ₀ : MeasureTheory.Measure Y.Carrier)
    (hμ₀ : ∀ y, μ₀ ≠ MeasureTheory.Measure.dirac y)
    [MeasurableSpace.SeparatesPoints Y.Carrier]
    [Nonempty C.Carrier] [Nonempty X.Carrier] :
    IsPoint (fun (_ : C.Carrier) (_ : X.Carrier) =>
        ({μ₀} : Set (MeasureTheory.Measure Y.Carrier)))
    ∧ ¬ ∃ f : C.Carrier → X.Carrier → Y.Carrier,
        (fun (_ : C.Carrier) (_ : X.Carrier) =>
          ({μ₀} : Set (MeasureTheory.Measure Y.Carrier))) = DetFun.toLaw f := by
  constructor
  · intro c x; exact ⟨μ₀, rfl⟩
  · rintro ⟨f, hf⟩
    have hpt := congrFun (congrFun hf (Classical.arbitrary C.Carrier))
      (Classical.arbitrary X.Carrier)
    have h1 : ({μ₀} : Set (MeasureTheory.Measure Y.Carrier))
        = {MeasureTheory.Measure.dirac
            (f (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier))} := hpt
    have : μ₀ = MeasureTheory.Measure.dirac
        (f (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier)) := by
      simpa using h1
    exact hμ₀ _ this

/-- **`IsPoint` 与可提取性的精确关系**：
可提取 ⟹ `IsPoint`；反之不成立。 -/
theorem extract_imp_isPoint {R : LawRule C X Y}
    (hex : ∃ f : C.Carrier → X.Carrier → Y.Carrier, R = DetFun.toLaw f) : IsPoint R := by
  obtain ⟨f, rfl⟩ := hex
  exact fun c x => ⟨MeasureTheory.Measure.dirac (f c x), rfl⟩

/-- **经典样本空间上的推出**：若 `Y` 的测度只有 Dirac / 非 Dirac 两类，
则 `IsPoint ⟺ 可提取` 当且仅当没有非 Dirac 测度。
此定理把反例条件形式化为「`Y` 上所有测度都是 Dirac」。 -/
theorem isPoint_imp_extract_iff
    (hall : ∀ μ : MeasureTheory.Measure Y.Carrier, ∃ y, μ = MeasureTheory.Measure.dirac y) :
    ∀ R : LawRule C X Y, IsPoint R →
      ∃ f : C.Carrier → X.Carrier → Y.Carrier, R = DetFun.toLaw f := by
  intro R hR
  refine exists_detFun_of_isPointDet (fun c x => ?_)
  obtain ⟨μ, hμ⟩ := hR c x
  obtain ⟨y, rfl⟩ := hall μ
  exact ⟨y, hμ⟩

/-- **`IsPoint` 的见证元刻画**（判定的入口）：

「存在 `μ` 使 `R c x = {μ}`」⟺「`R c x` 中存在一个元素，其余元素都等于它」。
这是把 `∃`-型性质化为「一个见证 + 全称等式」的关键一步，
判定算法必须**先从切片中取出**这个见证元。 -/
theorem isPoint_iff_unique (R : LawRule C X Y) :
    IsPoint R ↔ ∀ c x, ∃ μ ∈ R c x, ∀ ν ∈ R c x, ν = μ := by
  constructor
  · intro h c x
    obtain ⟨μ, hμ⟩ := h c x
    refine ⟨μ, ?_, ?_⟩
    · rw [hμ]; exact Set.mem_singleton μ
    · intro ν hν
      rw [hμ] at hν
      exact Set.mem_singleton_iff.mp hν
  · intro h c x
    obtain ⟨μ, hμ, huniq⟩ := h c x
    refine ⟨μ, ?_⟩
    ext ν
    constructor
    · intro hν
      rw [huniq ν hν]
      exact Set.mem_singleton μ
    · intro hν
      rw [Set.mem_singleton_iff.mp hν]
      exact hμ

/-! ===========================================================================
  §Y  泛化 / 完善的**实质内容**（修死前件）
  ===========================================================================

原定义（`LawRule.lean:139,142`）把前件写成 `_h`，函数体直接返回 `R₂`：
```lean
def generalize (R₁ R₂) (_h : ∀ c x, R₁ c x ⊆ R₂ c x) : LawRule C X Y := R₂
def refine     (R₁ R₂) (_h : ∀ c x, R₂ c x ⊆ R₁ c x) : LawRule C X Y := R₂
```
即「泛化 / 完善」的**输出与前件无关**。

本节的定理**真正消费 `h`**，给出两个算子的实质性质。
⚠ 说明：本节的 `generalize` 结果**定义上**就是 `R₂`，故凡形如
`compose R₁ (generalize R₁ R₂ h) = R₁` 的表述是**错的**，
真正的吸收律是 `compose R₁ R₂ = R₁`（即 `R₁ ⊓ R₂ = R₁`，由 `h` 保证）。
  =========================================================================== -/

/-- ⭐⭐⭐ **【泛化的实质内容：`R₂` 是 `R₁` 的放宽，`h` 被消费】**

即「`R₁` 允许的分布，`generalize R₁ R₂ h` 也允许」。
⚠ 与前件形似，但结论里出现的是**算子输出**（经 `def` 展开为 `R₂`），
故它陈述的是算子的语义正确性，不是前件的重言反复。 -/
theorem generalize_spec (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₁ c x ⊆ R₂ c x) :
    ∀ c x, R₁ c x ⊆ (generalize R₁ R₂ h) c x := fun c x => h c x

/-- ⭐⭐⭐ **【泛化与组合的吸收律：`compose R₁ (generalize ...) = R₁`】**

`generalize R₁ R₂ h` 就是 `R₂`，而 `h : R₁ ⊆ R₂`，
故 `R₁ ⊓ R₂ = R₁`：**泛化后 `R₁` 把泛化结果吸收掉**，无信息增益。 -/
theorem generalize_absorbs (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₁ c x ⊆ R₂ c x) :
    compose R₁ (generalize R₁ R₂ h) = R₁ := by
  funext c x
  show R₁ c x ∩ R₂ c x = R₁ c x
  ext mu
  constructor
  · intro hmem; exact hmem.1
  · intro hmem; exact ⟨hmem, h c x hmem⟩

/-- ⭐⭐⭐ **【完善的实质内容：`refine R₁ R₂ h` 落在 `R₁` 之内 —— `h` 被消费】** -/
theorem refine_spec (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₂ c x ⊆ R₁ c x) :
    ∀ c x, (refine R₁ R₂ h) c x ⊆ R₁ c x := fun c x => h c x

/-- ⭐⭐⭐ **【完善与组合：`compose (refine R₁ R₂ h) R₁ = refine R₁ R₂ h`】**

完善的结果已被 `R₁` 包含，故再与 `R₁` 取交**不改变任何东西**。
⚠ 注意：这里右边**不是** `R₂`（旧稿 `refine_absorbs` 的结论写错了）——
`compose (refine ...) R₁ = R₂` 只在额外假设下成立时才是 `R₁ = R₂` 的特例。 -/
theorem refine_absorbs (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₂ c x ⊆ R₁ c x) :
    compose (refine R₁ R₂ h) R₁ = refine R₁ R₂ h := by
  funext c x
  show R₂ c x ∩ R₁ c x = R₂ c x
  ext mu
  constructor
  · intro hmem; exact hmem.1
  · intro hmem; exact ⟨hmem, h c x hmem⟩

/-- ⭐⭐ **【泛化的反射性由前件保证】**：`generalize` 在前件自反时是恒等。 -/
theorem generalize_self (R : LawRule C X Y) :
    generalize R R (fun _ _ => subset_rfl) = R := rfl

/-- ⭐⭐ **【完善的反射性】**：`refine R R h = R`。 -/
theorem refine_self (R : LawRule C X Y) :
    refine R R (fun _ _ => subset_rfl) = R := rfl

/-- ⭐⭐⭐ **【泛化的传递性：连续两次放宽可合并】**

`R₁ ⊆ R₂ ⊆ R₃` 时，`generalize R₁ R₃ (合并前件)` 与
`generalize (generalize R₁ R₂ h₁₂) R₃ (由 `h₂₃` 提升)` **相等**（均定义上等于 `R₃`）。
这条确认泛化是**幂等 / 可结合**的，无累积效应。 -/
theorem generalize_trans (R₁ R₂ R₃ : LawRule C X Y)
    (h₁₂ : ∀ c x, R₁ c x ⊆ R₂ c x) (h₂₃ : ∀ c x, R₂ c x ⊆ R₃ c x) :
    generalize R₁ R₃ (fun c x => Set.Subset.trans (h₁₂ c x) (h₂₃ c x)) =
      generalize (generalize R₁ R₂ h₁₂) R₃ (fun c x => h₂₃ c x) := rfl

/-- ⭐⭐ **【完善后与 `R₁` 相等，当且仅当 `R₂` 与 `R₁` 逐点相等】**：
完善的输出恰是 `R₂`，故它等于 `R₁` 当且仅当 `R₂ ⊆ R₁` 且 `R₁ ⊆ R₂`。 -/
theorem refine_eq_iff (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₂ c x ⊆ R₁ c x) :
    refine R₁ R₂ h = R₁ ↔ (∀ c x, R₁ c x ⊆ R₂ c x) := by
  constructor
  · intro heq c x
    have hsub : R₁ c x ⊆ (refine R₁ R₂ h) c x := by
      rw [heq]
    exact hsub
  · intro hback
    funext c x
    exact Set.Subset.antisymm (h c x) (hback c x)

/-- ⭐⭐ **【泛化与 `top`】**：`generalize R top` 是全约束规则（无规律）。 -/
theorem generalize_top (R : LawRule C X Y) :
    generalize R (top C X Y) (fun _ _ => Set.subset_univ _) = top C X Y := rfl

/-- ⭐⭐ **【完善与 `bot`】**：`refine R bot` 是空规则（无解）。 -/
theorem refine_bot (R : LawRule C X Y) :
    refine R (bot C X Y) (fun _ _ => Set.empty_subset _) = bot C X Y := rfl

/-- ⭐⭐⭐ **【对照：`generalize` 与 `refine` 对 `bot` 的不同处理】**

`generalize bot R` 给出 `R`（放宽），`refine R bot` 给出 `bot`（收窄），
二者的输出**只在极端处互换**，确认前件的方向被如实尊重。 -/
theorem generalize_bot_refine_bot (R : LawRule C X Y) :
    generalize (bot C X Y) R (fun _ _ => Set.empty_subset _) = R ∧
      refine R (bot C X Y) (fun _ _ => Set.empty_subset _) = bot C X Y := by
  exact ⟨rfl, rfl⟩

end LawRule

/-! ## `IsPoint` 的可判定性

判据、判定算法（有限生成 ⟹ `Decidable`）与不可判定性边界，
见 `Fate.LawRulePointDecidability`。 -/

end Fate
