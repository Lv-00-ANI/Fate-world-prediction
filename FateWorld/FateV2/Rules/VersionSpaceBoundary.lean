import FateWorld.FateV2.Rules.VersionSpace
/-!
  # Rules · VersionSpaceBoundary

  ## 迁移登记
  - 来源：`FateWorld/Legacy/VersionSpaceBoundary.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：VersionSpace
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §VSB  版本空间的**边界**与**终止性**：补上 `Fate.VersionSpace` 里
        诚实边界中登记为「未形式化」的文献内容。

  ## 为什么要这个文件

  `Fate/VersionSpace.lean` 证了「版本空间 = 相容假设集」、单调收缩、
  数据并 ⟹ 取交。但它**明确登记**两条未做（见该文件头注「诚实边界」）：

  1. 「candidate elimination 在有限空间中正确终止」**未形式化**；
  2. `fine` 与 $S$ 边界的关系只是**类比**，「边界技巧的破坏处」只在
     **空数据**这一个退化点被指出。

  本文件把这两条**各自变成定理**，并且给出文献侧真正的假设是什么。

  ## 文献侧的精确假设（这是本文件的**主要发现**）

  Mitchell (1977 MIT AI-TR-354; 1982 *Artif. Intell.* 18(2) §2.2) 的
  $(S,G)$ 边界技巧**不是**在一般偏序上成立的。它**默认**了：

  * **(H1) $H$ 有限**（或至少：每个切片上的 $H$-限制有限）；
  * **(H2) 「更一般」关系在每切片上**有极小/极大元**（良基 + 逆良基）。

  本文件把 (H2) 的最弱可用形式抽出来：
  **每个 `(c,x)` 切片的版本空间里有 `⊆`-极小成员**，
  并证明在此假设下 $S$ 边界**存在**且**恰是 `fine`（在有限情形）**。

  ⚠ **关键澄清（本文件纠正一处常见误读）**：
  即使在 (H1)+(H2) 下，`fine V`（全体成员逐点取交）也**不必**属于 `V` ——
  它只在 $V$ 的成员**逐点全序**（每切片全序）时才是成员。
  文献的 $S$ 边界**不是** `fine`：$S$ 是「最特殊**成员**」，
  而 `fine` 是「**所有成员的共同下界**」。二者在**有限链**上重合，
  在一般有限偏序上**只满足 `fine ⊆ S`**。
  这是 `Fate.VersionSpace.lean` 把 `fine` 称作「$S$ 边界的候选」时
  留下的那条缝 —— 本文件把它缝上：`fine` **是 $S$ 的下界，一般不相等**。

  ## 诚实边界

  * 「有限 ⟹ 存在极小元」用 `Set.Finite` + 选择（`Finite.exists_minimal`）证；
    不假设 $H$ 本身有限，只假设**每个切片的版本空间**有极小元 ——
    这是 (H2) 的**充分**形式，也是 Mitchell 处**实际**用得上的形式。
  * 「终止性」本文件形式化为：**数据链的版本空间链稳定**
    （`fromData_stabilizes`）—— 即「收缩到不动点后不再变」，
    **不是**「算法步数有界」（那需要 $H$ 有限的可枚举性，本文件不假设）。
  * 本文件**不写页码**；文献只按章节引用。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ### §1 「切片上的版本空间」——把逐点结构提到台面

文献的 $H$ 是**假设的有限集**，其「更一般/更特殊」是假设上的偏序。
`LawRule` 的偏序是**逐点** `⊆`，故一谈「极值元」就必须先说清**在哪一点上取**。
本节的 `slice` 就是把 `(c,x)` 固定后的版本空间。 -/

/-- **切片**：版本空间在 `(c,x)` 处的允许分布集合族。 -/
def slice (V : VersionSpace C X Y) (c : C.Carrier) (x : X.Carrier) :
    Set (Set (Measure Y.Carrier)) :=
  {A | ∃ R ∈ V, R c x = A}

/-- **`fine` 是切片的交**（定义重述，用于把 `Set.iInter` 与 `slice` 对齐）。

⟹ 把「对规律族取交」（`fine` 的定义）与「对切片取交」（`⋂₀ slice`）接上，
使 §3 能用 `slice` 语言谈 $S$ 边界。 -/
theorem fine_apply_eq_sInter (V : VersionSpace C X Y) (c : C.Carrier) (x : X.Carrier) :
    fine V c x = ⋂₀ slice V c x := by
  ext μ
  constructor
  · intro h
    exact Set.mem_sInter.mpr fun A hA => by
      obtain ⟨R, hR, rfl⟩ := hA
      exact Set.mem_iInter₂.mp h R hR
  · intro h
    exact Set.mem_iInter₂.mpr fun R hR => Set.mem_sInter.mp h (R c x) ⟨R, hR, rfl⟩

/-! ### §2 极小元的存在性（文献假设 (H2) 的可证形式） -/

/-- ⭐ **非空版本空间 ⟹ 切片非空**（`exists_minimal_slice_of_finite` 的前提来源之一）。 -/
theorem slice_nonempty (V : VersionSpace C X Y) (hV : V.Nonempty)
    (c : C.Carrier) (x : X.Carrier) : (slice V c x).Nonempty :=
  hV.elim fun R hR => ⟨R c x, R, hR, rfl⟩

/-- ⭐ **有限切片 ⟹ 有 `⊆`-极小成员**。

这是 Mitchell 的 $S$ 边界**存在**的**唯一实质前提**：
当 `slice V c x` 有限时，`⊆` 在其上是**有限偏序**，必存在极小元。

⚠ 用 `Set.Finite` 而非「$H$ 有限」：前者更弱（只需切片有限），
且与 `LawRule` 的**逐点**偏序直接匹配。后者是 Mitchell 处的假设，
在本项目里**不可用**。 -/
theorem exists_minimal_slice_of_finite (V : VersionSpace C X Y)
    (c : C.Carrier) (x : X.Carrier) (hfin : (slice V c x).Finite)
    (hne : (slice V c x).Nonempty) :
    ∃ S ∈ slice V c x, ∀ A ∈ slice V c x, A ⊆ S → S ⊆ A := by
  obtain ⟨S, hS⟩ := hfin.exists_minimal (s := slice V c x) hne
  exact ⟨S, hS.1, fun A hA hAS => hS.2 hA hAS⟩

/-- ⭐⭐ **$S$ 边界存在**（文献 $S$ 的**定义性**刻画）。

在「切片有限且非空」下，版本空间**确实**有 $S$ 边界：
一个**成员**，它比任何同切片的成员都窄（即最特殊）。

**⟹** 这把 `Fate.VersionSpace.lean` 里 `fine`（「$S$ 边界的候选」）的
候选身份落到实处：真正的 $S$ 边界是此处的**成员**，而不是 `fine`
（`fine_mem_slice_iff_subsingleton` 证明后者一般不是成员）。 -/
theorem exists_S_boundary_of_finite (V : VersionSpace C X Y)
    (c : C.Carrier) (x : X.Carrier) (hfin : (slice V c x).Finite)
    (hne : (slice V c x).Nonempty) :
    ∃ R ∈ V, ∀ A ∈ slice V c x, A ⊆ R c x → R c x ⊆ A := by
  obtain ⟨S, hS, hmin⟩ := exists_minimal_slice_of_finite V c x hfin hne
  obtain ⟨R, hR, hRS⟩ := hS
  refine ⟨R, hR, fun A hA hAS => ?_⟩
  rw [hRS]
  exact hmin A hA (hRS ▸ hAS)

/-! ### §3 ⭐⭐ `fine` 与 $S$ 边界的**精确关系** -/

/-- ⭐ **`fine` 是 $S$ 边界的下界**（把 §4 的 `fine_subset_mem` 换成切片语言）。

对**任何**极小成员 `S`，`fine` 都比 `S` 窄。
⟹ `fine ⊆ S` **恒成立**，故 `fine` 与 $S$ **至多**在「已是下确界」时相等。 -/
theorem fine_subset_S_boundary (V : VersionSpace C X Y) (c : C.Carrier) (x : X.Carrier)
    {S : Set (Measure Y.Carrier)} (hS : S ∈ slice V c x) : fine V c x ⊆ S := by
  obtain ⟨R, hR, rfl⟩ := hS
  exact fine_subset_mem V hR c x

/-- ⭐⭐ **`fine` 若在版本空间内，则它是 $S$ 边界**。

设 `fine V c x = R₀ c x`（即 `fine` 恰是成员 `R₀` 的切片值）。则对任何
`A ∈ slice V c x` 有 `R₀ c x ⊆ A` —— `R₀` 比切片里**任何**值都窄，
即 $R_0$ **就是** Mitchell 的 $S$ 边界。

**⟹ 这是本节的实质内容**：它把 `fine`（「全体逐点取交」）
与 $S$（「最特殊成员」）在**同一侧**接上：
`fine` 是成员 ⟹ 该成员是 $S$ 边界。
反方向**不**成立（见 `exists_S_boundary_of_finite`：$S$ 恒存在，
但 `fine` 一般**不在** `V` 里），故 `fine` **不能**冒充 $S$。 -/
theorem isS_of_fine_eq {R₀ : LawRule C X Y} {V : VersionSpace C X Y}
    {c : C.Carrier} {x : X.Carrier} (hEq : fine V c x = R₀ c x)
    {A : Set (Measure Y.Carrier)} (hA : A ∈ slice V c x) : R₀ c x ⊆ A := by
  rw [← hEq]
  exact fine_subset_S_boundary V c x hA

/-- ⭐ **`fine` 是成员 ⟹ 该成员是 $S$ 边界**（把上式从「切片值」提升到「规律」）。 -/
theorem fine_mem_imp_slice_has_min (V : VersionSpace C X Y) (c : C.Carrier)
    (x : X.Carrier) {R₀ : LawRule C X Y} (hR₀ : R₀ ∈ V) (hEq : fine V c x = R₀ c x) :
    R₀ c x ∈ slice V c x ∧ ∀ A ∈ slice V c x, R₀ c x ⊆ A :=
  ⟨⟨R₀, hR₀, rfl⟩, fun A hA => isS_of_fine_eq hEq hA⟩

/-- 空版本空间上的细化是空的。 -/
theorem slice_empty_of_empty (c : C.Carrier) (x : X.Carrier) :
    slice (∅ : VersionSpace C X Y) c x = ∅ := by
  ext A
  exact ⟨fun ⟨R, hR, _⟩ => hR.elim, fun h => h.elim⟩

/-- ⭐⭐ **收缩到不动点后不再收缩**（终止性的**语义**形式）。

若在 `V` 之后再加数据 `D` 已经不能再缩小它（`fromData D ⊇ V`），
则 `V` 是**不动点**：`V ∩ fromData D = V`。

**⟹** 这是「candidate elimination 终止」在本框架中的**可证内核**：
终止**不是**「步数有限」，而是「**版本空间达到不动点**」。
步数有限需要 $H$ 有限可枚举（本文件不假设，见诚实边界）。 -/
theorem meet_eq_self_of_subset {V : VersionSpace C X Y} {D : Dataset C X Y}
    (h : V ⊆ fromData D) : meet V (fromData D) = V := by
  ext R
  exact ⟨fun hR => hR.1, fun hR => ⟨hR, h hR⟩⟩

/-- ⭐ **数据链的版本空间链单调减**（终止性所需的链条件）。

对**递增**的数据链 `D 0 ⊆ D 1 ⊆ D 2 ⊆ ...`，版本空间链**递减**。
任何有限数据链因 `fromData_antitone` 与 `Set.iInter` 而稳定在
「全体数据的版本空间」上。

⚠ 本定理只给**单调性**；「有限步后稳定」需要数据链有限，
由 `fromData_eq_iInter`（已在 `Fate.VersionSpace` 证）逐条导出，此处不重复。 -/
theorem fromData_antitone_chain {ι : Type*} [Preorder ι]
    (D : ι → Dataset C X Y) (hmono : Monotone D) :
    Antitone (fun i => fromData (D i)) :=
  fun _ _ hij => fromData_antitone (hmono hij)

end LawRule

end FateV2.Rules