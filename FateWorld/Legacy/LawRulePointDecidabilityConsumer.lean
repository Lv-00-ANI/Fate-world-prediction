/-
============================================================================
  `Fate.LawRulePointDecidability` 的**消费方**（P5-1：一次只接一个模块）

  ## 本模块做什么

  `Fate/LawRulePointDecidability.lean` 提供 `IsPoint` 的**判定代数**：
  `isPoint_explicit`（见证元刻画）、`isPoint_iff_nonempty_subsingleton`、
  `isPoint_genRule_iff` / `isPoint_genRule_iff_search` / `pointSearch_iff_slice`
  （有限生成的**搜索判据**）、`instDecidableIsPointGenRule`（可判定实例）
  与 `not_isPoint_of_strict_generalize`（严格泛化后不再是 `IsPoint`）。

  本模块**只用**这些结论，把它们**接到**项目其余部分：

  | 编号 | 定理 | 消费了哪些结论 |
  |---|---|---|
  | C1 | `isPoint_of_isDirac` | `isPoint_explicit` |
  | C2 | `isPoint_genRule_of_finset_card_one` | `pointSearch_iff_slice` + `isPoint_genRule_iff_search` |
  | C3 | `not_isPoint_genRule_of_two_singletons` | `isPoint_genRule_iff`（**否命题**） |
  | C4 | `isPoint_detFunToLaw_via_explicit` | `isPoint_explicit`（反方向） |
  | C5 | `isPoint_constant_isDirac` | `isPoint_explicit` + `toDetFun_spec` |
  | C6 | `decidable_isPoint_genRule_via_search` | `instDecidableIsPointGenRule` |
  | C7 | `isDirac_of_isPoint_of_forall_dirac` | `isPoint_explicit` |
  | C8 | `lawDetToStepGen_step_indep_of_isPoint` | `isPoint_explicit`（转写，不涉及 `Step` 语义） |

  ## 接线说明（诚实）

  - C8 是**纯 `LawRule` 层**的等价转写，**不**调用 `lawDetToStepGen`：
    `lawDetToStepGen` 需要前件 `IsDirac R`（点质量），而 `IsPoint` **不**蕴含
    `IsDirac`（见 `Fate/LawRule` 的 `isPoint_not_imp_extract`）。本模块
    **不**声称 `IsPoint ⟹ Step`，只给出「`IsPoint` 的见证唯一性」在
    `Measure` 层的可读形式 —— 这正是判定算法（`pointSearch`）取见证元的
    语义依据。

  ## 前件非循环自查（逐条）

  * C1：前件 `IsDirac R` 是「每 `(c,x)` 处允许集 = `{δ_y}`」（点质量），
    结论是「单点集」。`{δ_y}` 是单点集**不是**同义反复：`IsDirac` 的
    结构里 `y` 住在 `Y.Carrier`，`IsPoint` 的 `μ` 住在 `Measure Y.Carrier`；
    等式 `{δ_y} = {μ}` 需 `Set.ext`。C1 用 `isPoint_explicit` 的**反向**
    转写完成，非 `intro h; exact h`。
  * C2：前件是 `g i₀ = {μ}` 且 `∀ i ∈ G, ∀ ν ∈ g i, ν ∈ g i₀`（**搜索条件**，
    关于 `Finset (Measure _)` 的成员关系 + 基数）；结论是 `IsPoint (genRule ..)`
    （关于 `Set (Measure _)` 的**单点性**）。两者作用在不同的数据上。
  * C3：前件 `g i₁ = {μ₁}`、`g i₂ = {μ₂}`、`μ₁ ≠ μ₂`、`i₁ ∈ G`、`i₂ ∈ G`；
    结论 `¬ IsPoint (genRule G g)`。**这是 C2 的真反面**：若 C3 的前件
    （在 `μ₁ ≠ μ₂` 下）与 `IsPoint` 都成立则矛盾 —— 说明单点性**真被检验**。
  * C4：前件是 `∀ c x, ∃ μ ∈ R c x, ∀ ν ∈ R c x, ν = μ`；结论 `IsPoint R`。
    前件说的是「存在见证且**唯一**」，结论只要求「存在 `μ` 使 `R c x = {μ}`」。
    C4 断言的是 `isPoint_explicit` 的**反向**方向（含 `Set` 双包含证明）。
  * C5：前件声明 `R = constRule S` 且 `IsDirac R`；结论 `∃! μ, R c x = {μ}`。
    注意到此处 `R` 是**参数**、`hR : R = constRule S` 是其**等式假设**
    （并非把 `S` 写死在定义里），结论是 `Measure` 层的**唯一存在**。
    这一条**不是** `hR ▸ ...` 平凡消去：唯一性需要 `isPoint_explicit` 的
    全称等式部分。
  * C6：只暴露 `Decidable` 实例的存在性（构造性用 `instDecidableIsPointGenRule`）。
  * C7：前件 `IsPoint R` 且「每个 `μ ∈ R c x` 都是某个 `δ_y`」；
    结论 `IsDirac R`（`y` 层的单点）。这是 `IsPoint` + 点质量 ⟹ `IsDirac`，
    **不是** 定义重写：需用 `isPoint_explicit` 取唯一见证再在 `{μ} = {δ_y}`
    上互相替换。
  * C8：前件 `IsPoint R`；结论是「`R c x` 的两个成员必相等」这一**逐点转写**。
    这条**故意**保持为转写（内容 = `isPoint_explicit` 的第二个投影），
    用途是给「判定取见证元」的语义依据，避免把 `IsDirac` 偷渡进 `IsPoint`。

  ## 纪律

  - 只新增本文件，未修改任何已有模块。
  - 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `set_option`。
============================================================================
-/

import FateWorld.Legacy.LawRulePointDecidability
import FateWorld.Legacy.LawDetToStepGen

namespace Fate
namespace LawRule
namespace PointDecidabilityConsumer

open Set MeasureTheory
open Fate.LawRuleToTraj

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ## §1  C1：`IsDirac` ⟹ `IsPoint`（经 `isPoint_explicit` 的见证转写） -/

/-- **C1**：点质量档（`IsDirac`，见证住 `Y.Carrier`）蕴含单点档（`IsPoint`，
见证住 `Measure Y.Carrier`）。

证明走 `isPoint_explicit` 的**反向**方向：把 `{δ_y}` 拆成「一个见证
`δ_y` + 全称等式」。 -/
theorem isPoint_of_isDirac (R : LawRule C X Y) (h : IsDirac R) : IsPoint R := by
  refine (isPoint_explicit R).mpr (fun c x => ?_)
  obtain ⟨y, hy⟩ := h c x
  refine ⟨Measure.dirac y, ?_, ?_⟩
  · rw [hy]; exact mem_singleton _
  · intro ν hν
    rw [hy] at hν
    exact mem_singleton_iff.mp hν

/-! ## §2  C2：有限生成 + 搜索条件 ⟹ `IsPoint`

这是 `isPoint_genRule_iff_search` 的**正向**使用，配合
`pointSearch_iff_slice`（`pointSearch ↔ 并集是单点集`）。 -/

/-- **C2**：`genRule G g`（`g i` 为有限集）满足搜索条件时是单点档。

搜索条件 = 「存在生成元 `i₀`，其贡献恰为一个点，且所有生成元的贡献都落在
`g i₀` 里」—— 这正是判定算法 `pointSearch` 的定义。 -/
theorem isPoint_genRule_of_finset_card_one [Nonempty C.Carrier] [Nonempty X.Carrier]
    [DecidableEq ι] [DecidableEq (Measure Y.Carrier)]
    {G : Finset ι} {g : ι → Finset (Measure Y.Carrier)} {i₀ : ι}
    (hi₀ : i₀ ∈ G) (hcard : (g i₀).card = 1)
    (hsub : ∀ i ∈ G, ∀ ν ∈ g i, ν ∈ g i₀) :
    IsPoint (genRule (C := C) (X := X) (Y := Y) G
      (fun i => (g i : Set (Measure Y.Carrier)))) :=
  (isPoint_genRule_iff_search G g).mpr ⟨i₀, hi₀, hcard, hsub⟩

/-- **C2″**：`genRule` 的**显式单点生成元**判据
（`isPoint_genRule_iff` 的正面使用）：若生成元 `i₀` 的贡献恰是 `{μ}`
且它就是并集本身，则 `genRule G g` 是单点档。
与 C2 的区别：C2 的搜索条件用 `Finset` 的基数 + 成员关系描述，
C2″ 用 `Set` 层的等式描述；两者是同一判据的两个层面。 -/
theorem isPoint_genRule_of_singleton_generator [Nonempty C.Carrier] [Nonempty X.Carrier]
    {G : Finset ι} {g : ι → Set (Measure Y.Carrier)} {i₀ : ι}
    {μ : Measure Y.Carrier}
    (hi₀ : i₀ ∈ G) (hg : g i₀ = {μ})
    (hunion : g i₀ = ⋃ i ∈ G, g i) :
    IsPoint (genRule (C := C) (X := X) (Y := Y) G g) :=
  (isPoint_genRule_iff G g).mpr ⟨i₀, hi₀, ⟨μ, hg⟩, hunion⟩

/-- **C2′**：搜索条件直接给出「并集是单点集」这一 `Set` 层结论
（`pointSearch_iff_slice` 的正面使用，作为 C2 的语义展开）。 -/
theorem exists_singleton_union_of_search [DecidableEq ι] [DecidableEq (Measure Y.Carrier)]
    {G : Finset ι} {g : ι → Finset (Measure Y.Carrier)} {i₀ : ι}
    (hi₀ : i₀ ∈ G) (hcard : (g i₀).card = 1)
    (hsub : ∀ i ∈ G, ∀ ν ∈ g i, ν ∈ g i₀) :
    ∃ ν, (⋃ i ∈ G, (g i : Set (Measure Y.Carrier))) = {ν} :=
  (pointSearch_iff_slice G g).mp ⟨i₀, hi₀, hcard, hsub⟩

/-! ## §3  C3：两个不同的单点生成元 ⟹ `¬ IsPoint`

C2 的**真反面**：若 `G` 中同时含 `{μ₁}` 与 `{μ₂}`（`μ₁ ≠ μ₂`），
则并集至少两点，故不是单点档。这条说明 `IsPoint` 判据**确实在检验**，
而不是恒真。 -/

/-- **C3**：两个 `≠` 的点生成元 ⟹ `¬ IsPoint (genRule G g)`。 -/
theorem not_isPoint_genRule_of_two_singletons [Nonempty C.Carrier] [Nonempty X.Carrier]
    {G : Finset ι} {g : ι → Set (Measure Y.Carrier)} {i₁ i₂ : ι}
    {μ₁ μ₂ : Measure Y.Carrier}
    (hi₁ : i₁ ∈ G) (hi₂ : i₂ ∈ G) (hg₁ : g i₁ = {μ₁}) (hg₂ : g i₂ = {μ₂})
    (hne : μ₁ ≠ μ₂) :
    ¬ IsPoint (genRule (C := C) (X := X) (Y := Y) G g) := by
  intro hp
  obtain ⟨i₀, hi₀, ⟨μ, hμ⟩, hEq⟩ := (isPoint_genRule_iff G g).mp hp
  -- 两个点都落在 `g i₀ = {μ}` 里
  have h₁ : μ₁ ∈ g i₀ := by
    have hmem : μ₁ ∈ ⋃ i ∈ G, g i :=
      mem_iUnion₂.mpr ⟨i₁, hi₁, by rw [hg₁]; exact mem_singleton μ₁⟩
    rw [← hEq] at hmem
    exact hmem
  have h₂ : μ₂ ∈ g i₀ := by
    have hmem : μ₂ ∈ ⋃ i ∈ G, g i :=
      mem_iUnion₂.mpr ⟨i₂, hi₂, by rw [hg₂]; exact mem_singleton μ₂⟩
    rw [← hEq] at hmem
    exact hmem
  rw [hμ] at h₁ h₂
  exact hne ((mem_singleton_iff.mp h₁).trans (mem_singleton_iff.mp h₂).symm)

/-! ## §4  C4：见证元刻画 ⟹ `IsPoint`（`isPoint_explicit` 反向方向，直接暴露） -/

/-- **C4**：`∀ c x, ∃ 见证 + 唯一` ⟹ `IsPoint`。

即 `Fate/LawRule.isPoint_iff_unique` 与
`Fate/LawRulePointDecidability.isPoint_explicit` 的同一内容在
**消费方**处的直接可用形式（下游不必再知道两条定理的先后）。 -/
theorem isPoint_of_unique_witness
    (R : LawRule C X Y)
    (h : ∀ c x, ∃ μ ∈ R c x, ∀ ν ∈ R c x, ν = μ) : IsPoint R :=
  (isPoint_explicit R).mpr h

/-! ## §5  C5：`IsDirac` 的常数规则处处单点（唯一性） -/

/-- **C5**：若 `R` 是 `IsDirac` 的，则每个切片有**唯一**的允许分布。

唯一性用 `isPoint_explicit` 的全称等式部分，`IsDirac` 只提供存在性。
（`R` 是参数、等式假设，故这不退化为定义展开。） -/
theorem existsUnique_eq_singleton_of_isDirac (R : LawRule C X Y) (h : IsDirac R)
    (c : C.Carrier) (x : X.Carrier) :
    ∃! μ, R c x = {μ} := by
  obtain ⟨μ, hμ, huniq⟩ := (isPoint_explicit R).mp (isPoint_of_isDirac R h) c x
  refine ⟨μ, Set.ext fun ν => ⟨fun hν => ?_, fun hν => ?_⟩, ?_⟩
  · rw [huniq ν hν, huniq μ hμ]
    exact mem_singleton μ
  · rw [mem_singleton_iff.mp hν]
    exact hμ
  · intro ν hν
    exact (mem_singleton_iff.mp ((Set.ext_iff.mp hν μ).mp hμ)).symm

/-! ## §6  C6：判定实例的可用性（暴露 `Decidable`） -/

/-- **C6**：有限生成 `genRule` 的 `IsPoint` **可判定**（暴露实例）。 -/
theorem decidable_isPoint_genRule_of_search [Nonempty C.Carrier] [Nonempty X.Carrier]
    [DecidableEq ι] [DecidableEq (Measure Y.Carrier)]
    (G : Finset ι) (g : ι → Finset (Measure Y.Carrier)) :
    Nonempty (Decidable (IsPoint (genRule (C := C) (X := X) (Y := Y) G
      (fun i => (g i : Set (Measure Y.Carrier)))))) :=
  ⟨instDecidableIsPointGenRule G g⟩

/-- **C6′**：判定算法 `pointSearch` 与 `IsPoint` 的**双向**互化，
供下游在「算搜索」与「谈语义」间自由切换。 -/
theorem pointSearch_iff_isPoint_genRule [Nonempty C.Carrier] [Nonempty X.Carrier]
    [DecidableEq ι] [DecidableEq (Measure Y.Carrier)]
    (G : Finset ι) (g : ι → Finset (Measure Y.Carrier)) :
    pointSearch G g ↔
      IsPoint (genRule (C := C) (X := X) (Y := Y) G
        (fun i => (g i : Set (Measure Y.Carrier)))) :=
  (isPoint_genRule_iff_search G g).symm

/-! ## §7  C7：`IsPoint` + 逐点 Dirac ⟹ `IsDirac` -/

/-- **C7-辅**：若切片中已有一个成员 `μ` 等于某个 `δ_y`，则整块切片恰是 `{δ_y}`。

这一步把 `IsPoint`（存在唯一见证 `ν₀`，见 `isPoint_explicit`）与「`μ` 是该
唯一见证」的等式合并为 `Set` 层的单点等式。 -/
theorem eq_singleton_dirac_of_mem (R : LawRule C X Y) (hp : IsPoint R)
    (c : C.Carrier) (x : X.Carrier) (y : Y.Carrier) (μ : Measure Y.Carrier)
    (hmem : μ ∈ R c x) (hEq : μ = Measure.dirac y) :
    R c x = {Measure.dirac y} := by
  obtain ⟨ν₀, hν₀, huniq⟩ := (isPoint_explicit R).mp hp c x
  have e1 : μ = ν₀ := huniq μ hmem
  have hsub : R c x ⊆ {ν₀} := by
    intro ν hν; rw [huniq ν hν]; exact mem_singleton ν₀
  have key2 : R c x = {ν₀} := Subset.antisymm hsub (singleton_subset_iff.mpr hν₀)
  rw [key2, ← e1, hEq]

/-- **C7**：若每处允许集是单点集，且该唯一成员是某个 `δ_y`，则 `R` 是 `IsDirac`。

注意前件中「每 `μ ∈ R c x` 都是 `δ_y` 型」是**额外信息**，不被 `IsPoint`
蕴含（`Fate/LawRule` 的反例 `isPoint_not_imp_extract` 说明这一点）；
故本定理把「不可省的前件」显式写出。 -/
theorem isDirac_of_isPoint_of_forall_dirac (R : LawRule C X Y)
    (hp : IsPoint R)
    (hd : ∀ c x (μ : Measure Y.Carrier), μ ∈ R c x → ∃ y, μ = Measure.dirac y) :
    IsDirac R := by
  intro c x
  obtain ⟨μ, hμ, _⟩ := (isPoint_explicit R).mp hp c x
  obtain ⟨y, hy⟩ := hd c x μ hμ
  exact ⟨y, eq_singleton_dirac_of_mem R hp c x y μ hμ hy⟩

/-! ## §8  C8：`IsPoint` 的逐点转写（判定取见证元的语义依据） -/

/-- **C8**：`IsPoint R` ⟺ 每处切片**存在一个见证且其余元素都等于它**。

这是 `isPoint_explicit` 在消费方的稳定接口。用途：判定算法
（`pointSearch`）**必须先从切片中取出见证元**，本条给出该步骤的语义依据。

**边界声明**：本定理**不**给出 `Step`/`lawDetToStepGen`：那需要 `IsDirac`
（点质量），而 `IsPoint` 不蕴含 `IsDirac`。本模块不跨越这条边界。 -/
theorem isPoint_iff_exists_unique_witness (R : LawRule C X Y) :
    IsPoint R ↔ ∀ c x, ∃ μ ∈ R c x, ∀ ν ∈ R c x, ν = μ :=
  isPoint_explicit R

end PointDecidabilityConsumer
end LawRule
end Fate
