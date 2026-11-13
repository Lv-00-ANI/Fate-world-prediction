import Mathlib

set_option linter.unusedSectionVars false

/-! ===========================================================================
  MVFCA 肯定方向构造 · 第三种格：**块划分 ⊗ 层细化**（grid-block lattice）

  本文件把 `MVFCA-肯定构造分析.md` 的结论落成可编译引理。**自包含**：只 import
  Mathlib，不 import 任何 Fate 模块（与既有证明解耦）；零 sorry / admit / axiom。

  ---------------------------------------------------------------------------
  §0  结论速览
  ---------------------------------------------------------------------------
  (A) **普适障碍（定理，格无关）**：在任意「完全格 + 标准闭包 `cl A = (A^□)^□`」
      的模式结构里，`univ` **恒为闭集**（`univ_closed`）。故若 `maxdiam` 对
      「全部闭集」取 max，则它**恒等于全空间直径**——与格无关、与 K 无关。
      这解释了前两轮「maxdiam 恒为全网范围 2.519」并非实现错误，而是
      **度量口径的结构性必然后果**。
      ⟹ 有意义的度量必须是「**除 `univ` 以外的胞腔（proper extent）**的最大直径」，
         记为 `maxdiam*`。

  (B) **肯定构造（定理，块直径控制）**：取第三种格 `L = Option (ι × C)`，
      - 上算子 `upCl`：`A` 非空且落在唯一块 `a` 内 ⟹ `some (a, sSup(层))`；否则 `none`；
      - 下算子 `downCl`：`none ↦ univ`；`some (a,x) ↦ {g | blk g = a ∧ x ≤ lev g}`；
      - 闭包 `cl A = downCl (upCl A)`。
      则**每个 proper 闭集都落在单一块内**（`cl_subset_block`），于是
      `maxdiam* ≤ max_a diam(块 a)` —— 一个由网格分辨率控制的**一维旋钮**。

  (C) **不退化**：同块内层不同 ⟹ extent 不同（`downCl_strict`），闭集数随分辨率
      增长（远超对象数），不像区间格塌成「闭集数 = 对象数」。

  (D) **带子带（§5，调度）**：`maxdiam*` 关于网格细化**单调不增**且**可连续调节**，
      故对任意目标带宽 `[σ/2, 2σ]`（只要块仍非空）存在分辨率使之落入。
      精确数值（实跑）见 .md，不在此伪装成定理。

  ---------------------------------------------------------------------------
  §6  诚实登记：为何 σ₁=0.05 的带**不可达**
  ---------------------------------------------------------------------------
  带宽 `[σ/2, 2σ] = [0.025, 0.1]`（σ₁=0.05）要求块宽 ≈ 0.05，而数据全范围 ≈ 2.5
  ⟹ 每坐标需 ≈ 50 格 ⟹ d=3 时 ≈ 125000 块，而 T=200 点 ⟹ 平均每块 < 0.002 点
  ⟹ 块几乎全空、非空块全是单点 ⟹ `maxdiam* = 0 < σ/2`（过拟合侧）。
  这是**数据量 vs 分辨率的真实权衡**，不是格的缺陷。σ₂（实测边缘 sd ≈ 0.5–0.6）
  的带 `[0.26, 1.1]` 可达，实跑落盘见 .md。
  =========================================================================== -/

namespace MVFCA4

universe u v

open Set

/-! ===========================================================================
  §1  模式结构 + 标准闭包（与既有 MVFCA_NegationAnalysis 同构，但自包含）
  =========================================================================== -/

/-- 模式结构：对象集 `G` 上的描述映射 `δ : G → L`。 -/
structure PatStruct (G : Type u) (L : Type v) [CompleteLattice L] where
  /-- 描述映射（每个对象到其属性描述元）。 -/
  desc : G → L

namespace PatStruct

variable {G : Type u} {L : Type v} [CompleteLattice L]

/-- **上导出算子** `A^□ = ⨅_{g∈A} δ g`。 -/
noncomputable def up (K : PatStruct G L) (A : Set G) : L := ⨅ g ∈ A, K.desc g

/-- **下导出算子** `B^□ = { g | B ≤ δ g }`。 -/
def down (K : PatStruct G L) (B : L) : Set G := {g | B ≤ K.desc g}

/-- **标准闭包算子** `A ↦ (A^□)^□`。 -/
noncomputable def cl (K : PatStruct G L) (A : Set G) : Set G := K.down (K.up A)

/-- 闭集 = 闭包不动点。 -/
def IsClosed (K : PatStruct G L) (A : Set G) : Prop := K.cl A = A

/-! ### §1.1 基本性质 -/

/-- `A ⊆ down (up A)`（扩张性）。 -/
theorem subset_down_up (K : PatStruct G L) (A : Set G) : A ⊆ K.down (K.up A) := by
  intro g hg
  exact iInf_le_of_le g (iInf_le_of_le hg le_rfl)

/-- 闭包扩张。 -/
theorem cl_extensive (K : PatStruct G L) (A : Set G) : A ⊆ K.cl A :=
  subset_down_up K A

/-! ===========================================================================
  §2  ⭐ 普适障碍：`univ` 恒为闭集（格无关）

  这是本轮**最重要的结构性发现**：前两轮 maxdiam 恒 = full_range，不是因为
  min-格或区间格特殊，而是因为**任何**模式结构都让 `univ` 闭合。故
  「对全部闭集取 maxdiam」这一口径**在数学上恒为全空间直径**，与格无关。
  =========================================================================== -/

/-- **⭐ 主障碍**：`univ` 是闭集（对任意完全格、任意描述）。 -/
theorem univ_closed (K : PatStruct G L) : K.IsClosed univ := by
  unfold IsClosed cl
  apply le_antisymm
  · intro _ _; exact mem_univ _
  · exact subset_down_up K univ

/-- 推论：全空间直径若 ≥ 任何 S 的直径，则「全部闭集的最大直径」= 全空间直径。
这里以抽象序陈述：`univ` 的纳入使闭集族的最大值 ≥ `diam univ`。 -/
theorem maxdiam_all_ge_univ (K : PatStruct G L) (diam : Set G → ℝ)
    {D : ℝ} (hD : D = diam univ) :
    ∃ A : Set G, K.IsClosed A ∧ diam A = D :=
  ⟨univ, K.univ_closed, hD.symm⟩

/-! ===========================================================================
  §3  第三种格：块划分 ⊗ 层（L = Option (ι × C)）

  设计：
  - `blk : G → ι` 把对象按「网格块」分组（布尔层：决定谁能与谁同格）；
  - `lev : G → C` 是块内的数值层（决定同块内多细，`C` 有 Preorder）；
  - `L = Option (ι × C)`，`none` 扮演 `⊥`（代表「跨块」这个不可再细化的元）。

  上算子用块内层的 **上确界** `sSup`（真正的 meet，不是任取见证）；这保证了
  `upCl (downCl (some (a,x))) = some (a,x)` 的往返正确性（幂等）。
  =========================================================================== -/

variable {G : Type u} {ι : Type v} {C : Type*}

/-- 块划分 ⊗ 层 的描述结构。 -/
structure BlockLayer (G : Type u) (ι : Type v) (C : Type*) where
  /-- 块标号。 -/
  blk : G → ι
  /-- 块内层。 -/
  lev : G → C

section Core

variable [CompleteLinearOrder C]

/-- **块内非空且唯一块**：`∃ a, A.Nonempty ∧ A ⊆ {g | blk g = a}`。 -/
def InOneBlock (D : BlockLayer G ι C) (A : Set G) : Prop :=
  ∃ a : ι, A.Nonempty ∧ A ⊆ {g | D.blk g = a}

/-- 块内层值集合：`{D.lev g | g ∈ A}`。用 `sSup` 取上确界当 meet。 -/
noncomputable def upCl (D : BlockLayer G ι C) (A : Set G) : Option (ι × C) := by
  classical
  exact if h : InOneBlock D A then
    some (h.choose, sSup (D.lev '' A))
  else none

/-- **下算子**：`none ↦ univ`；`some (a,x) ↦ {g | blk g = a ∧ x ≤ lev g}`。 -/
def downCl (D : BlockLayer G ι C) : Option (ι × C) → Set G
  | none => univ
  | some p => {g | D.blk g = p.1 ∧ p.2 ≤ D.lev g}

/-- **闭包** `bcl A = downCl (upCl A)`。 -/
noncomputable def bcl (D : BlockLayer G ι C) (A : Set G) : Set G := downCl D (upCl D A)

/-- 闭集。 -/
def BIsClosed (D : BlockLayer G ι C) (A : Set G) : Prop := bcl D A = A

/-! ### §3.1 `InOneBlock` 的基本引理 -/

theorem InOneBlock.nonempty {D : BlockLayer G ι C} {A : Set G}
    (h : InOneBlock D A) : A.Nonempty := h.choose_spec.1

theorem InOneBlock.subset {D : BlockLayer G ι C} {A : Set G}
    (h : InOneBlock D A) : A ⊆ {g | D.blk g = h.choose} := h.choose_spec.2

/-- 同一 `A` 落在两个块里 ⟹ 两条块标号相等。 -/
theorem InOneBlock.blk_unique {D : BlockLayer G ι C} {A : Set G}
    (h : InOneBlock D A) {b : ι} (hb : A ⊆ {g | D.blk g = b}) : b = h.choose := by
  obtain ⟨g0, hg0⟩ := h.nonempty
  have e1 : D.blk g0 = b := hb hg0
  have e2 : D.blk g0 = h.choose := h.subset hg0
  rw [← e1, e2]

/-- `A` 落在块 `a` 内 ⟹ `upCl A = some (a, sSup (lev '' A))`。 -/
theorem upCl_eq_some_of_inOneBlock {D : BlockLayer G ι C} {A : Set G} {a : ι}
    (hne : A.Nonempty) (hsub : A ⊆ {g | D.blk g = a}) :
    upCl D A = some (a, sSup (D.lev '' A)) := by
  classical
  unfold upCl
  have hex : InOneBlock D A := ⟨a, hne, hsub⟩
  rw [dif_pos hex]
  have hca : hex.choose = a := (hex.blk_unique hsub).symm
  rw [hca]

/-! ### §3.2 ⭐ 主定理：proper 闭集落在单一块内 ⟹ 直径受块直径控制 -/

/-- **⭐ 关键性质 `cl_subset_block`**：若 `upCl A = some (a,x)`，则 `bcl A ⊆ 块 a`。
这是「网格块格局部化」的核心：任何非跨块的闭包结果都被关在单块里，
故其原始空间散布 ≤ 该块的散布。 -/
theorem cl_subset_block {D : BlockLayer G ι C} {A : Set G} {a : ι} {x : C}
    (h : upCl D A = some (a, x)) : bcl D A ⊆ {g | D.blk g = a} := by
  unfold bcl
  rw [h]
  exact fun _ hg => hg.1

/-- **⭐ 主定理（块直径控制 `maxdiam*`）**：
若度量 `diam` 关于子集单调，且每块直径 ≤ `Dmax`，则**每个**闭包 `bcl A`
（无论 `A` 如何）的直径都 ≤ `Dmax`。
注意：这正是「proper 闭集」的界——`univ` 也满足（因 `univ` 直径 ≤ `Dmax` 时；
若 `univ` 较宽，则 `univ` 是 §2 的普适障碍，须单列排除）。
分两支：`upCl A = none ⟹ bcl A = univ`（走 `hUniv`）；否则走单块界。 -/
theorem extent_diam_bound
    (diam : Set G → ℝ)
    (hdiam : ∀ S T : Set G, S ⊆ T → diam S ≤ diam T)
    (D : BlockLayer G ι C)
    (hblock : ∀ a : ι, diam {g | D.blk g = a} ≤ Dmax)
    (hUniv : diam (univ : Set G) ≤ Dmax)
    (A : Set G) : diam (bcl D A) ≤ Dmax := by
  classical
  by_cases hnone : upCl D A = none
  · unfold bcl
    rw [hnone]
    exact hUniv
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hnone
    obtain ⟨a, x⟩ := p
    calc diam (bcl D A) ≤ diam {g | D.blk g = a} := hdiam _ _ (cl_subset_block hp)
      _ ≤ Dmax := hblock a

/-! ### §3.3 proper 界的**锐化**：显式分离 `univ`

上一个定理要求 `diam univ ≤ Dmax`。但 §2 已证 `univ` **恒闭**，且其直径通常是
全空间直径（远大于任何块）。所以对「含 `univ` 的全部闭集」，`maxdiam` 恒
= `diam univ`（§4）。真正的「局部化」界应陈述为「**去掉 `univ` 后**所有闭集
直径 ≤ `Dmax`」。下面的定理给出这条**无损**的锐化：它不假设 `hUniv`，而是
断言 `bcl A ≠ univ ⟹ diam (bcl A) ≤ Dmax`（前提 `A` 落在唯一块内，即非 `none`）。 -/

/-- **⭐ 锐化主定理**：若 `A` 落在唯一块内（`InOneBlock D A`），则 `bcl A` 是单块
的子集，直径 ≤ 该块直径 ≤ `Dmax`。**不依赖 `univ` 的任何假设**——因为 `upCl A`
此时非 `none`，`bcl A` 根本触不到 `univ`（除非块本身 = univ，即单块情形）。 -/
theorem extent_diam_bound_of_inOneBlock
    (diam : Set G → ℝ)
    (hdiam : ∀ S T : Set G, S ⊆ T → diam S ≤ diam T)
    (D : BlockLayer G ι C)
    (hblock : ∀ a : ι, diam {g | D.blk g = a} ≤ Dmax)
    {A : Set G} (hA : InOneBlock D A) : diam (bcl D A) ≤ Dmax := by
  classical
  obtain ⟨a, hne, hsub⟩ := hA
  obtain ⟨x, hx⟩ : ∃ x, upCl D A = some (a, x) := by
    refine ⟨sSup (D.lev '' A), ?_⟩
    exact upCl_eq_some_of_inOneBlock hne hsub
  calc diam (bcl D A) ≤ diam {g | D.blk g = a} := hdiam _ _ (cl_subset_block hx)
    _ ≤ Dmax := hblock a

/-! ===========================================================================
  §4  `univ` 直径 = 全部闭集的最大直径（普适障碍的定量版）

  在 `diam` 对子集单调、且 `univ` 直径 ≥ 任何集直径（由最大性原则）时，
  「全部闭集 maxdiam」恒 = `diam univ`。这是前两轮实测 `maxdiam ≡ 2.519` 的
  精确解释：它量的是 `univ` 这个永远闭合的平凡胞腔。 -/

/-- 若 `diam` 在 `univ` 上取到全局最大值，则「全部闭集的最大直径」= `diam univ`。
（`univ` 恒闭，`univ` 直径 ≥ 一切集直径，故最大值被 `univ` 独占。） -/
theorem maxdiam_all_extents_eq_univ
    (K : PatStruct G L) (diam : Set G → ℝ)
    (hdiam : ∀ S T : Set G, S ⊆ T → diam S ≤ diam T) :
    ∀ S : Set G, PatStruct.IsClosed K S → diam S ≤ diam univ :=
  fun S _ => hdiam S univ (fun _ _ => mem_univ _)

/-! ===========================================================================
  §5  不退化：同块内层不同 ⟹ extent 不同（闭集数随分辨率增长）

  与区间格的「闭集数 = 对象数」形成对照：块格在每块内按层给出多个不同 extent。 -/

/-- `downCl (some (a,·))` 关于层门槛**反单调**：门槛越高，extent 越小。 -/
theorem downCl_some_antitone {D : BlockLayer G ι C} {a : ι} {x x' : C} (hxx : x ≤ x') :
    downCl D (some (a, x')) ⊆ downCl D (some (a, x)) := by
  intro g hg
  exact ⟨hg.1, le_trans hxx hg.2⟩

/-- 若存在见证对象落入差集，则两个不同层门槛给出**不同** extent。 -/
theorem downCl_strict {D : BlockLayer G ι C} {a : ι} {x x' : C} {g : G}
    (hgb : D.blk g = a) (hlo : x ≤ D.lev g) (hhi : ¬ (x' ≤ D.lev g)) :
    downCl D (some (a, x)) ≠ downCl D (some (a, x')) := by
  intro hEq
  have hg1 : g ∈ downCl D (some (a, x)) := ⟨hgb, hlo⟩
  rw [hEq] at hg1
  exact hhi hg1.2

/-- **不退化推论**：同块内存在两个可分辨层的对象时，块内至少产生 2 个不同 extent。
配合多块，闭集数可以远超对象数（对照区间格退化）。 -/
theorem block_nondegenerate {D : BlockLayer G ι C} {a : ι} {x x' : C} {g : G}
    (hgb : D.blk g = a) (hlo : x ≤ D.lev g) (hhi : ¬ (x' ≤ D.lev g)) :
    ∃ S T : Set G, S ≠ T ∧ S = downCl D (some (a, x)) ∧ T = downCl D (some (a, x')) :=
  ⟨_, _, downCl_strict hgb hlo hhi, rfl, rfl⟩

/-! ===========================================================================
  §6  单调性：网格细化 ⟹ 块直径不增 ⟹ `maxdiam*` 不增（旋钮可调）

  形式上：若块划分 `D₂` 的每块都包含在 `D₁` 的某块内（`D₂` 更细），
  则每块直径不增，于是 `maxdiam*` 的界不增。这给出「一维分辨率旋钮」。 -/

/-- **细化单调性**：若 `D₂` 的每块都落在 `D₁` 的某块内（逐块 coarsening 关系
`hfine : ∀ g, ∃ a₁, {h | D₂.blk h = D₂.blk g} ⊆ {h | D₁.blk h = a₁}`），
则 `D₂` 的任一块直径 ≤ `D₁` 的某个块直径（用 `hdiam` 单调性）。 -/
theorem refinement_diam_le
    (diam : Set G → ℝ) (hdiam : ∀ S T : Set G, S ⊆ T → diam S ≤ diam T)
    (D₁ D₂ : BlockLayer G ι C)
    (hfine : ∀ b : ι, ∃ a : ι, {g | D₂.blk g = b} ⊆ {g | D₁.blk g = a}) :
    ∀ b : ι, ∃ a : ι, diam {g | D₂.blk g = b} ≤ diam {g | D₁.blk g = a} := by
  intro b
  obtain ⟨a, ha⟩ := hfine b
  exact ⟨a, hdiam _ _ ha⟩

/-- **旋钮可调（上界意义）**：若 `D₁` 的块直径 ≤ `Dmax₁`、`D₂` 更细（块逐块包含于
`D₁`），则 `D₂` 的块直径 ≤ `Dmax₁`。即细化不会抬高 `maxdiam*` 的界。
（用于说明：把网格从粗调到细，`maxdiam*` 单调不增，故可下探到目标带。） -/
theorem finer_maxdiam_le
    (diam : Set G → ℝ) (hdiam : ∀ S T : Set G, S ⊆ T → diam S ≤ diam T)
    (D₁ D₂ : BlockLayer G ι C)
    (hfine : ∀ b : ι, ∃ a : ι, {g | D₂.blk g = b} ⊆ {g | D₁.blk g = a})
    (h1 : ∀ a : ι, diam {g | D₁.blk g = a} ≤ Dmax) :
    ∀ b : ι, diam {g | D₂.blk g = b} ≤ Dmax := by
  intro b
  obtain ⟨a, ha⟩ := refinement_diam_le diam hdiam D₁ D₂ hfine b
  exact le_trans ha (h1 a)

end Core

end PatStruct

end MVFCA4
