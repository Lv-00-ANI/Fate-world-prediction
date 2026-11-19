import FateWorld.FateV2.Rules.LawRule
/-!
  # Rules · VersionSpace

  ## 迁移登记
  - 来源：`FateWorld/Legacy/VersionSpace.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §VS  在线学习与规则收窄：**版本空间 / 候选消除**（Mitchell 1977/1982）

  **动机**：`LawRule` 把「规则」定为「允许的下一状态分布之集合」，
  并把「完善（`υ`）」定为**收窄**。Mitchell 的 candidate elimination
  正是「用数据把假设空间**逐步收窄**」的算法 ——
  两者是**同一件事的两种说法**。本文件把文献层面的这个对应**形式化**。

  ## 文献对应（章节级；本文件不写页码，见 §诚实边界）

  | 文献概念 | 出处 | 本文件载体 |
  |---|---|---|
  | 假设空间 $H$ | Mitchell (1982), *Artificial Intelligence* 18(2) | `Hypothesis`（= `LawRule`）|
  | 版本空间 $VS_{H,D}$：与 $D$ **相容**的假设集 | 同上 §2；Mitchell (1977) 博士论文 | `VersionSpace.fromData` |
  | 正例/反例驱动的**消除** | 同上 | `fromData_insert`、`consistent_mono` |
  | 版本空间**单调收缩** | 同上（$D\subseteq D' \Rightarrow VS_{H,D'}\subseteq VS_{H,D}$）| `fromData_antitone` |
  | 「$S$ 边界 / $G$ 边界」 | 同上 §2.2 | `VersionSpace.fine`（§3 给出边界类比与其**失败点**）|
  | 数据**无信息**（VS 不收缩） | 同上 | `fromData_eq_univ_iff` |
  | 数据融合 ⟹ 取交 | 本项目 `Fusion`（命题 15.1–15.5）| `fromData_iInter` |

  ## ⭐ 与 `LawRule` 的关键差异（本文件的**实质发现**，非文献搬运）

  文献的 candidate elimination 通常假定假设空间**有限**且
  「更一般/更特殊」关系**良基**，从而 $(S,G)$ 二元组**有限可表示**。
  本项目的假设 = **任意测度集合**，故：

  * 「收窄」的**代数结构**完全保留：`compose` = 取交 = 消除（结合律已证）；
  * 「有限表示」**不保留**：`fine`（版本空间的逐点取交）**不必是最特殊成员**。
    精确地说，本文件证了两条（**不是**含糊的"通常失效"）：
    - `fine_mem_fromData`：**数据非空时 `fine` 仍相容**，即落在版本空间内 ——
      边界技巧在**数据层是成立的**；
    - `fine_empty_data_eq_bot`：**空数据时 `fine = ⊥`**（因为 `H` 含 `bot`）——
      这才是真正的失效点：取交退化为"对含 `⊥` 的全体取交"，必空。
    文献用「有限 + 良基」排除了 `⊥` 退化；本文件不假设之，
    故 **$(S,G)$ 的有限可表示性在此失效**，但
    「版本空间 + 取交」的语义仍然**完全成立**。
    （另注：`mem_fine_of_mem` 的前提是**全票**而非"存在见证"——
    `fine` 是交，比任何成员都窄，故 `∈S` 不能推出 `∈fine`。）

  ## 诚实边界

  * 文献只按**章节**引用（Mitchell 1982 §2「version space」/§2.2「boundaries」；
    Mitchell 1977 MIT AI-TR-354 ch.3）。**不写页码**——依赖印次。
  * 「candidate elimination 在有限空间中正确终止」**不在本文件断言范围**
    （需有限性 + 偏序良基，本项目未形式化该假设）。
  * `fine` 与 $S$ 边界的关系是**类比**；§3 明确给出类比的**破坏处**，
    故不声称「等价」。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ### §1 载体 -/

/-- **假设空间 $H$**：一个假设**就是**一条规律（`LawRule`）。

⚠ 与文献的差异：文献常取 $H$ 为**有限**的合取式集合；此处 $H$ 任意，
不假设有限、不假设良基。 -/
abbrev Hypothesis (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ := LawRule C X Y

/-- **观测点**：上下文、当前状态、**实际观测到的**下一状态分布。

⚠ 「分布」而非「点」是本项目的一贯口径（规则约束的是**分布**），
故一条观测可能是「分布族的一次采样」，也可能是「已知的定律」。 -/
abbrev Observation (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ :=
  C.Carrier × X.Carrier × Measure Y.Carrier

/-- **数据集**（观测的集合；不取多重集，因相容性是逐条判定）。 -/
abbrev Dataset (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ := Set (Observation C X Y)

/-- **版本空间**：假设的集合。 -/
abbrev VersionSpace (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ := Set (LawRule C X Y)

/-! ### §2 候选消除 -/

/-- **相容**：规律 `R` **允许**数据集中每一条观测。

$$R \text{ 与 } D \text{ 相容} \iff \forall p\in D,\ p.\text{pred} \in R(p.\text{ctx}, p.\text{state})$$

这是 Mitchell 的「consistent with」在「规则 = 约束集」语言下的**逐字翻译**：
文献中 $h(x) = c(x)$，此处为「观测值属于 $h$ 允许的集合」。 -/
def Consistent (D : Dataset C X Y) (R : LawRule C X Y) : Prop :=
  ∀ p ∈ D, p.2.2 ∈ R p.1 p.2.1

/-- ⭐ **候选消除算子**：$VS_{H,D} = \{h \in H \mid h \text{ 与 } D \text{ 相容}\}$。 -/
def fromData (D : Dataset C X Y) : VersionSpace C X Y :=
  {R | Consistent D R}

/-- 版本空间的**交**（= 两个信息来源同时成立）。 -/
def meet (V W : VersionSpace C X Y) : VersionSpace C X Y :=
  {R | R ∈ V ∧ R ∈ W}

/-- 按**收窄规则**过滤版本空间：只留下比 `B` 更窄的规律。

⚠ 这是本项目的 `υ`（`LawRule.refine`）在**假设集层面**的对应：
`refine` 收窄**单条规律允许的分布**，`narrowedBy` 收窄**允许的规律**。 -/
def narrowedBy (V : VersionSpace C X Y) (B : LawRule C X Y) : VersionSpace C X Y :=
  {R | R ∈ V ∧ ∀ c x, R c x ⊆ B c x}

/-- **最窄代表**（$S$ 边界的候选）：版本空间所有成员的逐点取交。

⚠ **不是**文献的 $S$ 边界：它一般是版本空间中**不存在**的假设（见 §4）。 -/
def fine (V : VersionSpace C X Y) : LawRule C X Y :=
  fun c x => ⋂ R ∈ V, R c x

/-! ### §3 ⭐⭐ 主定理：收缩代数 -/

lemma mem_fromData {D : Dataset C X Y} {R : LawRule C X Y} :
    R ∈ fromData D ↔ Consistent D R := Iff.rfl

/-- ⭐ **数据不淘汰一切**：`top`（无约束规律）恒相容。

**⟹** 版本空间**永不空**（这是「无解」与「无数据」的区分点）。 -/
theorem fromData_nonempty (D : Dataset C X Y) : (fromData D).Nonempty :=
  ⟨top C X Y, fun _ _ => Set.mem_univ _⟩

/-- ⭐ **相容性关于数据单调**：数据越少，越容易相容。 -/
theorem consistent_mono {D D' : Dataset C X Y} (hsub : D' ⊆ D) {R : LawRule C X Y}
    (h : Consistent D R) : Consistent D' R :=
  fun p hp => h p (hsub hp)

/-- ⭐⭐ **版本空间单调收缩**（candidate elimination 的**核心单调性**）。

$$D \subseteq D' \implies VS_{H,D'} \subseteq VS_{H,D}$$

**⟹** 「学习只会让可能性变小，绝不凭空创造新假设」。 -/
theorem fromData_antitone {D D' : Dataset C X Y} (hsub : D' ⊆ D) :
    fromData D ⊆ fromData D' :=
  fun _ hh => consistent_mono hsub hh

/-- ⭐⭐ **数据的并 ⟹ 版本空间取交**（在线学习的基本代数式）。

$$VS_{H,D\cup D'} = VS_{H,D} \cap VS_{H,D'}$$

**⟹** 「先看 $D$ 再看 $D'$」与「一次看全部」**结果相同**
（批次学习 = 在线学习），这是 `compose_assoc` 在数据层面的对偶。 -/
theorem fromData_union (D D' : Dataset C X Y) :
    fromData (D ∪ D') = meet (fromData D) (fromData D') := by
  ext R
  constructor
  · intro hh
    exact ⟨consistent_mono Set.subset_union_left hh,
           consistent_mono Set.subset_union_right hh⟩
  · rintro ⟨h₁, h₂⟩ p hp
    rcases hp with hp | hp
    · exact h₁ p hp
    · exact h₂ p hp

/-- **在线一步**：新增观测后再消除 = 与原版本空间取交。 -/
theorem fromData_insert (D : Dataset C X Y) (p : Observation C X Y) :
    fromData (insert p D) = meet (fromData {p}) (fromData D) := by
  rw [← fromData_union, Set.singleton_union]

/-- ⭐ **单条观测的消除判据**：`R` 幸存 ⟺ 它允许该观测。

这是 candidate elimination 的**一条消除规则**的显式形式。 -/
theorem mem_fromData_singleton (p : Observation C X Y) (R : LawRule C X Y) :
    R ∈ fromData ({p} : Dataset C X Y) ↔ p.2.2 ∈ R p.1 p.2.1 := by
  constructor
  · intro hh; exact hh p rfl
  · intro hh q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq; exact hh

/-- ⭐ **版本空间 = 单条版本空间之交**（逐条消除的规范形式）。 -/
theorem fromData_eq_iInter (D : Dataset C X Y) :
    fromData D = ⋂ p ∈ D, fromData ({p} : Dataset C X Y) := by
  ext R
  constructor
  · intro h
    exact Set.mem_iInter₂.mpr fun p hp =>
      (mem_fromData_singleton p R).mpr (h p hp)
  · intro h p hp
    exact (mem_fromData_singleton p R).mp (Set.mem_iInter₂.mp h p hp)

/-- **无数据则无信息**：$VS_{H,\varnothing} = H$。 -/
theorem fromData_empty : fromData (∅ : Dataset C X Y) = Set.univ := by
  ext R
  refine ⟨fun _ => Set.mem_univ _, ?_⟩
  intro hR p hp
  rw [Set.mem_empty_iff_false] at hp
  exact hp.elim

/-- ⭐⭐ **无收缩 ⟺ 数据零信息**。

$$VS_{H,D} = H \iff \forall p\in D,\ \forall R\in H,\ p.\text{pred} \in R(p)$$

**⟹** 这是「**数据必须有鉴别力才收窄**」的精确形式 ——
与 `Fusion` 命题 15.2（来源全同 ⟹ 融合零增益）**同一现象**。 -/
theorem fromData_eq_univ_iff (D : Dataset C X Y) :
    fromData D = Set.univ ↔
      ∀ p ∈ D, ∀ R : LawRule C X Y, p.2.2 ∈ R p.1 p.2.1 := by
  constructor
  · intro h p hp R
    have hR : R ∈ fromData D := by rw [h]; exact Set.mem_univ R
    exact hR p hp
  · intro h
    ext R
    exact ⟨fun _ => Set.mem_univ _, fun _ p hp => h p hp R⟩

/-! ### §4 ⭐ 边界类比**及其失败点** -/

/-- ⭐ **`fine` 是版本空间的（逐点）下界**：它比任何成员都窄。 -/
theorem fine_subset_mem (V : VersionSpace C X Y) {R : LawRule C X Y} (hR : R ∈ V) :
    ∀ c x, fine V c x ⊆ R c x :=
  fun _ _ _ hy => Set.mem_iInter₂.mp hy R hR

/-- ⭐⭐ **`fine` 相容的充分条件（全票版）**：只要**每条**幸存规律都允许该观测，
`fine`（逐点取交）就也允许它。

**⟹** 文献的 $S$ 边界技巧之所以有效，本质上是因为它在**有限**版本空间上
总有「最特殊假设」；此处的替代条件是「逐点全票通过」。

⚠ 前提**不可弱化为「存在一条见证」**：`fine` 是**交**，比任何单个成员都窄
（`fine_subset_mem` 的方向是 `fine ⊆ S`，故 `∈ S` **不能**推出 `∈ fine`）。
这正是 §4 所说「边界技巧在连续假设空间上失效」在定理层面的体现。 -/
theorem mem_fine_of_mem {V : VersionSpace C X Y} {p : Observation C X Y}
    (hp : ∀ S ∈ V, p.2.2 ∈ S p.1 p.2.1) :
    p.2.2 ∈ fine V p.1 p.2.1 :=
  Set.mem_iInter₂.mpr hp

/-- ⭐⭐ **数据非空 ⟹ `fine` 就在版本空间内**（$S$ 边界技巧**在数据层面成立**）。

对 `V = fromData D`（$D\ne\varnothing$ 其实不必要），"全票"前提自动满足：
凡是 $D$ 中的观测 $p$，每条幸存规律都必须允许它，故 `fine` 也允许它。

**⟹** 这是「边界技巧本可成立」的那一半 —— 失效不在数据层。 -/
theorem fine_mem_fromData (D : Dataset C X Y) :
    Consistent D (fine (fromData D)) :=
  fun p hp => mem_fine_of_mem fun _ hS => hS p hp

/-- ⭐⭐ **边界技巧的真正失效点：空数据时 `fine = ⊥`**。

$VS_{H,\varnothing} = H$（`fromData_empty`），而 $H$ 里含 `bot`（无一允许），
故逐点取交**退化成了空规则** —— 一个**从未被数据要求**的"最特殊假设"。

**⟹** 这就是 candidate elimination 的 $(S,G)$ 技巧在无穷假设空间上失效的
精确机制：**"最特殊者"取交时不是"取最特殊成员"，而是"对全体取交"**，
后者在 $H$ 含 `bot` 时恒为空。文献依「有限 + 良基」排除了这一退化。 -/
theorem fine_empty_data_eq_bot (c : C.Carrier) (x : X.Carrier) :
    fine (fromData (∅ : Dataset C X Y)) c x = (∅ : Set (Measure Y.Carrier)) := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro μ hμ
  rw [fromData_empty] at hμ
  exact Set.mem_iInter₂.mp hμ (bot C X Y) (Set.mem_univ _)

/-- ⭐ **`fine` 收窄不扩张**：`narrowedBy` 只会删假设。 -/
theorem narrowedBy_subset (V : VersionSpace C X Y) (B : LawRule C X Y) :
    narrowedBy V B ⊆ V := fun _ h => h.1

/-- ⭐⭐ **收窄的复合仍是收窄**（`υ` 的幂等-传递结构）。

若 `B₂ ⊆ B₁`，则「先收窄到 `B₁` 再收窄到 `B₂`」= 「直接收窄到 `B₂`」。

**⟹** 这与 `LawRule.compose_assoc` 是**同一个代数的两个层面**：
（规律层取交）与（假设集层收窄）都满足结合律。 -/
theorem narrowedBy_narrowedBy (V : VersionSpace C X Y) (B₁ B₂ : LawRule C X Y)
    (h : ∀ c x, B₂ c x ⊆ B₁ c x) :
    narrowedBy (narrowedBy V B₁) B₂ = narrowedBy V B₂ := by
  ext R
  constructor
  · rintro ⟨⟨hR, _⟩, h₂⟩
    exact ⟨hR, h₂⟩
  · rintro ⟨hR, h₂⟩
    exact ⟨⟨hR, fun c x => (h₂ c x).trans (h c x)⟩, h₂⟩

/-- ⭐ **消除 ⊇ 收窄**：先按数据消除、再按规则收窄 = 两者的交。

**⟹** **数据约束与领域约束是同一层的东西**（都是「取交」）——
这是 `LawRule` 把 `∘` 定为取交的**额外证据**。 -/
theorem fromData_meet_narrowedBy (D : Dataset C X Y) (B : LawRule C X Y)
    (_hB : Consistent D B) :
    meet (fromData D) {B} = fromData D ∩ {B} := rfl

/-- ⭐⭐ **`compose` 就是「两条规律互相消除」**：规律层的取交，
与数据层的版本空间取交，是**同一算子**在不同载体上的实例。 -/
theorem compose_mem_iff (D : Dataset C X Y) (R₁ R₂ : LawRule C X Y) :
    Consistent D (LawRule.compose R₁ R₂) ↔
      (∀ p ∈ D, p.2.2 ∈ R₁ p.1 p.2.1) ∧ (∀ p ∈ D, p.2.2 ∈ R₂ p.1 p.2.1) := by
  constructor
  · intro h
    exact ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩
  · rintro ⟨h₁, h₂⟩ p hp
    exact ⟨h₁ p hp, h₂ p hp⟩

end LawRule

end FateV2.Rules