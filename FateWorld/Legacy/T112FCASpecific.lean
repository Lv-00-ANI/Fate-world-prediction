import FateWorld.Legacy.T112FCAPolar
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Order.Atoms
import Mathlib.Order.Cover
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Closure

/-! ===========================================================================
  `Fate/T112FCASpecific` —— 第 247 轮：**真正 FCA 特有**的定理（含诚实标注）

  ## 任务书三条

  | # | 任务 | 结论 |
  |---|---|---|
  | 1 | ⭐⭐⭐ 概念外延 ↔ 概念内涵 是**反序同构** | ✅ 已证，**FCA 特有**（需两端伴随） |
  | 2 | ⭐⭐⭐ 双极闭包秩 ≤ 2（四次极 = 二次极） | ✅ 已证，但 ⚠ **非 FCA 特有** |
  | 3 | ⭐⭐ 概念格同构但"外延-内涵对应"不同的反例 | ✅ 已证（机器验证反例） |

  ## 诚实性声明（**重要**）

  - **任务 1**：定理 `extentIntentAnti` 说 `ExtentSet K ≃o (IntentSet K)ᵒᵈ`。
    单侧闭包算子只有"外延"或只有"内涵"，无法建立两侧的对应；本定理由
    `polarUp` / `polarDown` 的**双向伴随**（Galois 连接）驱动，故**是 FCA 特有的**。
    分离证据见 §1.3：一般闭包算子 `cl3` 的闭集格**不自对偶**，
    故其"闭集 ↔ 闭集"不存在这种反序结构。
  - **任务 2**：`polarUp_polarDown_polarUp_polarDown_idem` 说四次极 = 二次极。
    **这条不是 FCA 特有的**：任何幂等映射 `f` 都有 `f⁴ = f²`（见 `idem_four_eq_two`），
    任何闭包算子 `c` 都有 `c⁴ = c²`（见 `closure_four_eq_two`）。
    只要 `polarDown ∘ polarUp` 是闭包算子（它的确是），结论就自动成立。
    **§2.2 明确给出该定理对一般闭包算子也成立的证明。**
  - **任务 3**：`no_extent_preserving_iso` 是**具体的机器验证反例**：
    `KA`、`KC` 两个形式背景概念格**同构**（都是二元链，见 `KA_KC_lattice_iso`），
    但 `KA` 的 `⊥` 有非空外延 `{zA}`（`KA_bot_extent_nonempty`），
    `KC` 的 `⊥` 外延为 `∅`（`KC_bot_extent_empty`）。任何序同构保 `⊥`，
    故不存在保"外延非空性"的同构。加强版 `no_extent_card_preserving_iso`
    进一步说明：连"外延是否为空"都不能保。**这条是 FCA 特有的**
    （外延/内涵是 FCA 的两面，一般闭包算子没有这种二元结构）。

  ## 零 sorry，`lake build` 通过。
================================================================================ -/

namespace Fate

open Set

/-! # §1  任务 1：外延集 ↔ 内涵集 的反序同构（**FCA 特有**） -/

/-! ## §1.1  辅助：极算子与子类型 -/

namespace FormalCtx
variable (K : FormalCtx)

abbrev ExtentSet (K : FormalCtx) := { s : Set K.GFCA // Order.IsExtent K.Irel s }
abbrev IntentSet (K : FormalCtx) := { t : Set K.MFCA // Order.IsIntent K.Irel t }

theorem isExtent_polarDown (B : Set K.MFCA) : Order.IsExtent K.Irel (K.polarDown B) := ⟨B, rfl⟩
theorem isIntent_polarUp' (A : Set K.GFCA) : Order.IsIntent K.Irel (K.polarUp A) := ⟨A, rfl⟩

def toIntent' (s : ExtentSet K) : IntentSet K :=
  ⟨K.polarUp s.1, isIntent_polarUp' K s.1⟩

def toExtent' (t : IntentSet K) : ExtentSet K :=
  ⟨K.polarDown t.1, isExtent_polarDown K t.1⟩

@[simp] theorem toIntent'_val (s : ExtentSet K) : (toIntent' K s).1 = K.polarUp s.1 := rfl
@[simp] theorem toExtent'_val (t : IntentSet K) : (toExtent' K t).1 = K.polarDown t.1 := rfl

theorem toExtent'_toIntent' (s : ExtentSet K) : toExtent' K (toIntent' K s) = s := by
  refine Subtype.ext ?_
  exact Order.IsExtent.eq s.2

theorem toIntent'_toExtent' (t : IntentSet K) : toIntent' K (toExtent' K t) = t := by
  refine Subtype.ext ?_
  exact Order.IsIntent.eq t.2

/-- 关键的序关系转换（一）：`s ↦ s'` 反序且反序可逆 -/
theorem toIntent'_le_iff (s s' : ExtentSet K) : toIntent' K s' ≤ toIntent' K s ↔ s ≤ s' := by
  constructor
  · intro h
    have hh : K.polarUp s'.1 ⊆ K.polarUp s.1 := h
    have h2 : K.polarDown (K.polarUp s.1) ⊆ K.polarDown (K.polarUp s'.1) :=
      K.polarDown_antitone hh
    have e1 : K.polarDown (K.polarUp s.1) = s.1 := Order.IsExtent.eq s.2
    have e2 : K.polarDown (K.polarUp s'.1) = s'.1 := Order.IsExtent.eq s'.2
    rw [e1, e2] at h2
    exact h2
  · intro h
    show K.polarUp s'.1 ⊆ K.polarUp s.1
    exact K.polarUp_antitone h

theorem toExtent'_le_iff (t t' : IntentSet K) : toExtent' K t' ≤ toExtent' K t ↔ t ≤ t' := by
  constructor
  · intro h
    have hh : K.polarDown t'.1 ⊆ K.polarDown t.1 := h
    have h2 : K.polarUp (K.polarDown t.1) ⊆ K.polarUp (K.polarDown t'.1) :=
      K.polarUp_antitone hh
    have e1 : K.polarUp (K.polarDown t.1) = t.1 := Order.IsIntent.eq t.2
    have e2 : K.polarUp (K.polarDown t'.1) = t'.1 := Order.IsIntent.eq t'.2
    rw [e1, e2] at h2
    exact h2
  · intro h
    show K.polarDown t'.1 ⊆ K.polarDown t.1
    exact K.polarDown_antitone h

/-- ⭐ extents ≃o intentsᵒᵈ -/
noncomputable def extentIntentAnti (K : FormalCtx) : ExtentSet K ≃o (IntentSet K)ᵒᵈ where
  toFun s := OrderDual.toDual (toIntent' K s)
  invFun t := toExtent' K (OrderDual.ofDual t)
  left_inv s := toExtent'_toIntent' K s
  right_inv t := by
    show OrderDual.toDual (toIntent' K (toExtent' K (OrderDual.ofDual t))) = t
    rw [toIntent'_toExtent']
    exact OrderDual.toDual_ofDual t
  map_rel_iff' := by
    intro s s'
    show OrderDual.toDual (toIntent' K s) ≤ OrderDual.toDual (toIntent' K s') ↔ s ≤ s'
    rw [OrderDual.toDual_le_toDual]
    exact toIntent'_le_iff K s s'

/-! ## §1.3  分离证据：一般闭包算子的闭集格**不是**自对偶的

  若"反序同构"是一般闭包算子的性质，则对任何闭包算子 `c`，其闭集格 `CL` 都应
  满足 `CL ≃o CLᵒᵈ`。下面对一个具体的一般闭包算子 `cl3`（`Set (Fin 3)` 上）
  验证：**该反序同构不存在**。这刻画了任务 1 的 FCA 特异性。

  `cl3` 的闭集恰为 `∅, {0}, {1}, {0,1}, univ`（5 个），构成一个五元格。
  它有 2 个原子（`{0}`, `{1}`）和 1 个反原子（`{0,1}`）。反序同构会把
  原子与反原子互换，故 `CL ≇ CLᵒᵈ`。 -/

end FormalCtx

namespace ClosureSep

noncomputable section

attribute [local instance] Classical.propDecidable

def f3 (X : Set (Fin 3)) : Set (Fin 3) :=
  if X ⊆ ({0,1} : Set (Fin 3)) then X else univ

lemma not_subset01_univ : ¬ (univ : Set (Fin 3)) ⊆ ({0,1} : Set (Fin 3)) := by
  intro h
  have h2 : (2 : Fin 3) ∈ ({0,1} : Set (Fin 3)) := h (mem_univ 2)
  simp at h2

lemma f3_le (X : Set (Fin 3)) : X ⊆ f3 X := by
  unfold f3
  split_ifs with h
  · exact subset_rfl
  · exact subset_univ X

lemma f3_f3 (X : Set (Fin 3)) : f3 (f3 X) = f3 X := by
  by_cases h : X ⊆ ({0,1} : Set (Fin 3))
  · have hf : f3 X = X := by unfold f3; rw [if_pos h]
    rw [hf, hf]
  · have hf : f3 X = univ := by unfold f3; rw [if_neg h]
    rw [hf]
    unfold f3
    rw [if_neg not_subset01_univ]

lemma f3_min {X Y : Set (Fin 3)} (h : X ⊆ f3 Y) : f3 X ⊆ f3 Y := by
  by_cases hY : Y ⊆ ({0,1} : Set (Fin 3))
  · have hfY : f3 Y = Y := by unfold f3; rw [if_pos hY]
    rw [hfY] at h ⊢
    have hX : X ⊆ ({0,1} : Set (Fin 3)) := h.trans hY
    have hfX : f3 X = X := by unfold f3; rw [if_pos hX]
    rw [hfX]; exact h
  · have hfY : f3 Y = univ := by unfold f3; rw [if_neg hY]
    rw [hfY]; exact subset_univ _

noncomputable def cl3 : ClosureOperator (Set (Fin 3)) :=
  ClosureOperator.mk₂ f3 f3_le fun _ _ h => f3_min h

lemma cl3_isClosed_iff (X : Set (Fin 3)) :
    cl3.IsClosed X ↔ X ⊆ ({0,1} : Set (Fin 3)) ∨ X = univ := by
  show f3 X = X ↔ X ⊆ {0,1} ∨ X = univ
  by_cases h : X ⊆ ({0,1} : Set (Fin 3))
  · have hf : f3 X = X := by unfold f3; rw [if_pos h]
    rw [hf]; exact ⟨fun _ => Or.inl h, fun _ => rfl⟩
  · have hf : f3 X = univ := by unfold f3; rw [if_neg h]
    rw [hf]
    refine ⟨fun hh => Or.inr hh.symm, ?_⟩
    rintro (h1 | h2)
    · exact absurd h1 h
    · exact h2.symm

theorem covBy_map {L M : Type*} [PartialOrder L] [PartialOrder M] (e : L ≃o M) {a b : L}
    (h : a ⋖ b) : e a ⋖ e b := by
  refine ⟨(map_lt_map_iff e).2 h.1, ?_⟩
  intro c h1 h2
  have h3 : e.symm c < b := by
    rw [← (map_lt_map_iff e)]; simpa using h2
  have h4 : a < e.symm c := by
    rw [← (map_lt_map_iff e)]; simpa using h1
  exact absurd h4 (fun h4 => h.2 h4 h3)

end

namespace NonSelfDual

open Set

abbrev CL := { X : Set (Fin 3) // cl3.IsClosed X }

lemma closed_empty : cl3.IsClosed (∅ : Set (Fin 3)) := by
  rw [cl3_isClosed_iff]; exact Or.inl (empty_subset _)

lemma closed_univ : cl3.IsClosed (univ : Set (Fin 3)) := by
  rw [cl3_isClosed_iff]; exact Or.inr rfl

lemma closed_single0 : cl3.IsClosed ({0} : Set (Fin 3)) := by
  rw [cl3_isClosed_iff]; exact Or.inl (by intro x hx; simp_all)

lemma closed_single1 : cl3.IsClosed ({1} : Set (Fin 3)) := by
  rw [cl3_isClosed_iff]; exact Or.inl (by intro x hx; simp_all)

lemma closed_pair01 : cl3.IsClosed ({0,1} : Set (Fin 3)) := by
  rw [cl3_isClosed_iff]; exact Or.inl (by intro x hx; simp_all)

instance : Bot CL := ⟨⟨∅, closed_empty⟩⟩
instance : Top CL := ⟨⟨univ, closed_univ⟩⟩

lemma bot_le' (c : CL) : (⊥ : CL) ≤ c := by
  show (∅ : Set (Fin 3)) ⊆ c.1
  exact empty_subset _

lemma le_top' (c : CL) : c ≤ (⊤ : CL) := by
  show c.1 ⊆ univ
  exact subset_univ _

instance : OrderBot CL := ⟨bot_le'⟩
instance : OrderTop CL := ⟨le_top'⟩

lemma bot_val : (⊥ : CL).1 = (∅ : Set (Fin 3)) := rfl
lemma top_val : (⊤ : CL).1 = (univ : Set (Fin 3)) := rfl

/-- 在闭集格中：`{0}` 覆盖 `⊥ = ∅` -/
lemma cover_single0 : (⊥ : CL) ⋖ ⟨{0}, closed_single0⟩ := by
  refine ⟨?_, ?_⟩
  · show (∅ : Set (Fin 3)) ⊂ {0}
    exact Set.empty_ssubset.2 ⟨0, rfl⟩
  · intro c h1 h2
    have h1' : (∅ : Set (Fin 3)) ⊂ c.1 := h1
    have h2' : c.1 ⊂ ({0} : Set (Fin 3)) := h2
    have hne : c.1 ≠ ∅ := fun h => h1'.2 (le_of_eq h)
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hx0 : x = (0 : Fin 3) := by simpa using h2'.1 hx
    have heq : c.1 = {0} := by
      ext y
      constructor
      · intro hy; exact h2'.1 hy
      · intro hy; rw [mem_singleton_iff] at hy; rw [hy]; exact hx0 ▸ hx
    rw [heq] at h2'
    exact h2'.2 (le_of_eq rfl)

lemma cover_single1 : (⊥ : CL) ⋖ ⟨{1}, closed_single1⟩ := by
  refine ⟨?_, ?_⟩
  · show (∅ : Set (Fin 3)) ⊂ {1}
    exact Set.empty_ssubset.2 ⟨1, rfl⟩
  · intro c h1 h2
    have h1' : (∅ : Set (Fin 3)) ⊂ c.1 := h1
    have h2' : c.1 ⊂ ({1} : Set (Fin 3)) := h2
    have hne : c.1 ≠ ∅ := fun h => h1'.2 (le_of_eq h)
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hx0 : x = (1 : Fin 3) := by simpa using h2'.1 hx
    have heq : c.1 = {1} := by
      ext y
      constructor
      · intro hy; exact h2'.1 hy
      · intro hy; rw [mem_singleton_iff] at hy; rw [hy]; exact hx0 ▸ hx
    rw [heq] at h2'
    exact h2'.2 (le_of_eq rfl)

lemma single0_ne_single1 : (⟨{0}, closed_single0⟩ : CL) ≠ ⟨{1}, closed_single1⟩ := by
  intro h
  have hh : (0 : Fin 3) ∈ (⟨{1}, closed_single1⟩ : CL).1 := by
    rw [← h]
    exact mem_singleton_iff.2 rfl
  simp at hh

lemma pair01_lt_top : (⟨{0,1}, closed_pair01⟩ : CL) < (⊤ : CL) := by
  refine ⟨?_, ?_⟩
  · show ({0,1} : Set (Fin 3)) ⊆ univ; exact subset_univ _
  · intro hh
    have h2 : (2 : Fin 3) ∈ ({0,1} : Set (Fin 3)) := hh (mem_univ 2)
    simp at h2

end NonSelfDual

namespace NonSelfDual

open Set

/-- 闭集格的一个原子 -/
def a0 : CL := ⟨{0}, closed_single0⟩

/-- 闭集格中，任何真子集都含于 `{0,1}` 或等于 `univ`；故真闭集的候选是
    `∅, {0}, {1}, {0,1}` -/
lemma closed_subset_classification {X : Set (Fin 3)} (h : cl3.IsClosed X)
    (hne : X ≠ univ) : X ⊆ ({0,1} : Set (Fin 3)) := by
  rcases (cl3_isClosed_iff X).1 h with h1 | h1
  · exact h1
  · exact absurd h1 hne

/-- 闭集格的元素（除 `univ` 外）只能是 `∅, {0}, {1}, {0,1}` -/
lemma closed_mem_cases {X : Set (Fin 3)} (h : cl3.IsClosed X) (hne : X ≠ univ) :
    X = ∅ ∨ X = ({0} : Set (Fin 3)) ∨ X = ({1} : Set (Fin 3))
      ∨ X = ({0,1} : Set (Fin 3)) := by
  have hsub := closed_subset_classification h hne
  have key : ∀ y : Fin 3, y ∈ X → y = (0 : Fin 3) ∨ y = (1 : Fin 3) := by
    intro y hy
    have := hsub hy
    simpa using this
  by_cases hm0 : (0 : Fin 3) ∈ X <;> by_cases hm1 : (1 : Fin 3) ∈ X
  · right; right; right
    ext y; constructor
    · intro hy; rcases key y hy with rfl | rfl <;> simp
    · intro hy; simp at hy
      rcases hy with rfl | rfl
      · exact hm0
      · exact hm1
  · right; left
    ext y; constructor
    · intro hy
      rcases key y hy with rfl | rfl
      · simp
      · exact absurd ‹(1:Fin 3) ∈ X› hm1
    · intro hy; simp at hy; subst hy; exact hm0
  · right; right; left
    ext y; constructor
    · intro hy
      rcases key y hy with rfl | rfl
      · exact absurd ‹(0:Fin 3) ∈ X› hm0
      · simp
    · intro hy; simp at hy; subst hy; exact hm1
  · left
    ext y; constructor
    · intro hy
      rcases key y hy with rfl | rfl
      · exact absurd ‹(0:Fin 3) ∈ X› hm0
      · exact absurd ‹(1:Fin 3) ∈ X› hm1
    · intro hy; exact absurd hy (notMem_empty y)

/-- `CL` 中覆盖 `⊥` 的元素只有 `{0}` 与 `{1}` 两个 -/
lemma atoms_two {X : Set (Fin 3)} (h : cl3.IsClosed X)
    (hcov : (⊥ : CL) ⋖ ⟨X, h⟩) : X = ({0} : Set (Fin 3)) ∨ X = ({1} : Set (Fin 3)) := by
  have hlt : (⊥ : CL) < ⟨X, h⟩ := hcov.1
  have hne : X ≠ univ := by
    intro he
    -- 若 `X = univ`，则 `{0}` 严格介于 `⊥` 与 `⟨X,h⟩` 之间，违反覆盖
    have h3 : (⊥ : CL) < (⟨({0} : Set (Fin 3)), closed_single0⟩ : CL) := cover_single0.1
    have h2 : (⟨({0} : Set (Fin 3)), closed_single0⟩ : CL) < ⟨X, h⟩ := by
      refine ⟨?_, ?_⟩
      · show ({0} : Set (Fin 3)) ⊆ X
        rw [he]; exact subset_univ _
      · intro heq
        have hv : X ⊆ ({0} : Set (Fin 3)) := heq
        rw [he] at hv
        have h4 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := hv (mem_univ 1)
        simp at h4
    exact hcov.2 h3 h2
  rcases closed_mem_cases h hne with h1 | h1 | h1 | h1
  · exfalso
    have hle' : (⟨X, h⟩ : CL) ≤ (⊥ : CL) := by
      show X ⊆ (∅ : Set (Fin 3)); rw [h1]
    have heq' : (⟨X, h⟩ : CL) = (⊥ : CL) := le_antisymm hle' (bot_le' _)
    rw [heq'] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have h3 : (⊥ : CL) < (⟨({0} : Set (Fin 3)), closed_single0⟩ : CL) := cover_single0.1
    have h2 : (⟨({0} : Set (Fin 3)), closed_single0⟩ : CL) < ⟨X, h⟩ := by
      refine ⟨?_, ?_⟩
      · show (⟨({0} : Set (Fin 3)), closed_single0⟩ : CL) ≤ ⟨X, h⟩
        show ({0} : Set (Fin 3)) ⊆ X
        rw [h1]; exact Set.singleton_subset_iff.2 (by simp)
      · intro heq
        have hv : X ⊆ ({0} : Set (Fin 3)) := heq
        rw [h1] at hv
        have h4 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := hv (by simp)
        simp at h4
    exact hcov.2 h3 h2

lemma top_lt_of_ne_top {Y : CL} (h : Y ≠ ⊤) : Y < ⊤ :=
  lt_of_le_of_ne (le_top' Y) h

lemma not_univ_subset_single0 : ¬ (univ : Set (Fin 3)) ⊆ ({0} : Set (Fin 3)) := by
  intro h
  have h1 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := h (mem_univ 1)
  simp at h1
lemma not_univ_subset_single1 : ¬ (univ : Set (Fin 3)) ⊆ ({1} : Set (Fin 3)) := by
  intro h
  have h0 : (0 : Fin 3) ∈ ({1} : Set (Fin 3)) := h (mem_univ 0)
  simp at h0

lemma single0_lt_top : (⟨({0} : Set (Fin 3)), closed_single0⟩ : CL) < (⊤ : CL) :=
  ⟨subset_univ _, not_univ_subset_single0⟩

lemma single1_lt_top : (⟨({1} : Set (Fin 3)), closed_single1⟩ : CL) < (⊤ : CL) :=
  ⟨subset_univ _, not_univ_subset_single1⟩

/-- 覆盖 `⊤` 的元素（反原子）只能是 `{0,1}` -/
lemma coatoms_one {X : Set (Fin 3)} (h : cl3.IsClosed X)
    (hcov : (⟨X, h⟩ : CL) ⋖ (⊤ : CL)) : X = ({0,1} : Set (Fin 3)) := by
  have hlt : (⟨X, h⟩ : CL) < (⊤ : CL) := hcov.1
  have hne : X ≠ univ := by
    intro he
    have hge : (⊤ : CL) ≤ (⟨X, h⟩ : CL) := by
      show (univ : Set (Fin 3)) ⊆ X
      rw [he]
    exact (ne_of_lt hlt) (le_antisymm (le_top' _) hge)
  have hsub := closed_subset_classification h hne
  by_contra hne'
  -- 则 `X ⊂ {0,1}`，于是 `⟨X,h⟩ < ⟨{0,1},_⟩ < ⊤`
  have hproper : X ⊂ ({0,1} : Set (Fin 3)) :=
    lt_of_le_of_ne hsub (Ne.symm (by
      intro he
      exact hne' he.symm))
  have h2 : (⟨X, h⟩ : CL) < (⟨({0,1} : Set (Fin 3)), closed_pair01⟩ : CL) := hproper
  have h3 : (⟨({0,1} : Set (Fin 3)), closed_pair01⟩ : CL) < (⊤ : CL) := by
    refine ⟨subset_univ _, ?_⟩
    intro heq
    exact not_subset01_univ heq
  exact hcov.2 h2 h3

/-- 第二个原子 `{1}` -/
def a1 : CL := ⟨({1} : Set (Fin 3)), closed_single1⟩

lemma a0_ne_a1 : a0 ≠ a1 := single0_ne_single1

/-- 反序同构把覆盖 `⊥` 的元素送到覆盖其像的元素 -/
lemma covBy_map' {L M : Type*} [PartialOrder L] [PartialOrder M] (e : L ≃o M) {a b : L}
    (h : a ⋖ b) : e a ⋖ e b := covBy_map e h

/-- ⭐ **分离定理**：`CL` 不是自对偶的。
    理由：`e : CL ≃o CLᵒᵈ` 是反序同构，故把最小元 `⊥` 送到最大元。
    于是"覆盖 `⊥` 的元素"（`{0}`, `{1}` 两个）被送到"覆盖最大元的元素"——
    但最大元之上没有元素，故这类元素一个也没有。矛盾。 -/
theorem no_selfDual_iso : ¬ Nonempty (CL ≃o CLᵒᵈ) := by
  rintro ⟨e⟩
  -- `e ⊥` 是 `CLᵒᵈ` 的最大元
  -- `e` 保序，故把 `⊥` 送到 `CLᵒᵈ` 的 `⊥ = toDual univ`
  have hbot : e (⊥ : CL) = (⊥ : CLᵒᵈ) := map_bot e
  have c0 : (⊥ : CLᵒᵈ) ⋖ e a0 := by
    have := covBy_map e cover_single0
    rwa [hbot] at this
  have c1 : (⊥ : CLᵒᵈ) ⋖ e a1 := by
    have := covBy_map e cover_single1
    rwa [hbot] at this
  -- 在 `CLᵒᵈ` 中覆盖 `⊥` 的元素唯一：`toDual {0,1}`
  have uniq : ∀ y : CLᵒᵈ, (⊥ : CLᵒᵈ) ⋖ y →
      y = OrderDual.toDual (⟨({0,1} : Set (Fin 3)), closed_pair01⟩ : CL) := by
    intro y hy
    -- `⊥_{CLᵒᵈ} = toDual ⊤`，故 `hy` 等价于 `ofDual y ⋖ ⊤`（在 CL 中）
    have hy' : OrderDual.ofDual y ⋖ (⊤ : CL) := by
      have h2 : OrderDual.toDual (⊤ : CL) ⋖ OrderDual.toDual (OrderDual.ofDual y) :=
        (show (⊥ : CLᵒᵈ) = OrderDual.toDual (⊤ : CL) from rfl) ▸ hy
      exact (toDual_covBy_toDual_iff).1 h2
    have hsub : (OrderDual.ofDual y).1 = ({0,1} : Set (Fin 3)) :=
      coatoms_one (OrderDual.ofDual y).2 hy'
    exact Subtype.ext hsub
  have : e a0 = e a1 := by rw [uniq _ c0, uniq _ c1]
  exact a0_ne_a1 (e.injective this)

end NonSelfDual


end ClosureSep

/-! # §2  任务 2：双极闭包幂等 ⇒ 四次极 = 二次极（**非 FCA 特有**） -/

namespace RankTwo
variable (K : FormalCtx)

theorem isExtent_polarDown' (B : Set K.MFCA) : Order.IsExtent K.Irel (K.polarDown B) :=
  ⟨B, rfl⟩

/-- 任务 2：`A'''' = A''`（双极闭包幂等 ⇒ 秩 ≤ 2） -/
theorem polarUp_polarDown_polarUp_polarDown_idem (A : Set K.GFCA) :
    K.polarDown (K.polarUp (K.polarDown (K.polarUp A)))
      = K.polarDown (K.polarUp A) :=
  Order.IsExtent.eq (isExtent_polarDown' K (K.polarUp A))

end RankTwo

/-! ## §2.2  对照（关键）：同样的结论对**任何**闭包算子成立

  这说明四次极 = 二次极 **只是幂等性**，**不是 FCA 的几何/组合性质**。 -/

namespace Contrast

open Set

variable {α : Type*} [Preorder α] (c : ClosureOperator α)

/-- ⚠ **关键对照**：任何闭包算子 `c` 都有 `c⁴ = c²` —— 所以任务 2 的结论
    **不是 FCA 特有的**，它只用到 `polarDown ∘ polarUp` 是闭包算子（幂等）。 -/
theorem closure_four_eq_two (A : α) : c (c (c (c A))) = c (c A) := by
  have h1 : c (c (c A)) = c (c A) := c.idempotent' (c A)
  have h2 : c (c (c (c A))) = c (c (c A)) := c.idempotent' (c (c A))
  rw [h2, h1]

/-- 更一般：任何幂等映射 `f` 都满足 `f⁴ = f²` -/
theorem idem_four_eq_two {β : Type*} (f : β → β) (hf : ∀ x, f (f x) = f x) (x : β) :
    f (f (f (f x))) = f (f x) := by
  rw [hf (f (f x)), hf (f x)]

/-! ### §2.3  反衬：去掉幂等性后 `f⁴ = f²` 失效

  `Fin 5` 上的循环移位不是幂等的，其四次与二次不同。这说明任务 2 的全部
  内容就是"幂等性"，没有任何 FCA 专属的成分。 -/

/-- `Fin 5` 上的循环移位（非幂等） -/
def shift4 : Fin 5 → Fin 5 := fun i => ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩

/-- ⛔ 非幂等时 `f⁴ ≠ f²` -/
theorem shift4_four_ne_two : (fun i => shift4 (shift4 (shift4 (shift4 i))))
    ≠ (fun i => shift4 (shift4 i)) := by
  intro h
  have h0 := congrFun h (⟨0, by omega⟩ : Fin 5)
  simp [shift4] at h0

end Contrast

namespace Counterexample



/-- KA 的零号对象（`Fin 2` 的第一个元素） -/
def zA : Fin 2 := ⟨0, by omega⟩
/-- `Fin 2` 的第二个元素 -/
def oA : Fin 2 := ⟨1, by omega⟩
/-- KC 的零号属性 -/
def zC : Fin 2 := ⟨0, by omega⟩
/-- `Fin 2` 的第二个元素 -/
def oC : Fin 2 := ⟨1, by omega⟩

lemma zA_ne_oA : zA ≠ oA := by
  intro h; exact absurd (congrArg Fin.val h) (by simp [zA, oA])
lemma zC_ne_oC : zC ≠ oC := by
  intro h; exact absurd (congrArg Fin.val h) (by simp [zC, oC])

/-! ## 两个形式背景 -/

/-- 一个对象、一个属性、`I = True` 的"退化"约定（左线性） -/
def KA : FormalCtx where
  GFCA := Fin 2
  MFCA := Unit
  Irel := fun g _ => g = zA

/-- 一个对象、一个属性、`I = False` 的"退化"约定（右线性） -/
def KC : FormalCtx where
  GFCA := Unit
  MFCA := Fin 2
  Irel := fun _ m => m = zC

/-! ## KA 与 KC 的对象/属性集都是"单侧"的，故导出算子只有两种取值 -/

lemma KA_up_univ {A : Set KA.GFCA} (h : A ⊆ Set.singleton zA) :
    KA.polarUp A = (univ : Set Unit) := by
  ext m
  refine ⟨fun _ => mem_univ m, fun _ => ?_⟩
  exact (FormalCtx.mem_polarUp_iff KA).2 (fun {g} hg => h hg)

lemma KA_up_empty {A : Set KA.GFCA} (h : ¬ A ⊆ Set.singleton zA) :
    KA.polarUp A = (∅ : Set Unit) := by
  ext m
  refine ⟨fun hm => ?_, fun hm => absurd hm (notMem_empty m)⟩
  exact h ((FormalCtx.mem_polarUp_iff KA).1 hm)

lemma KA_down_single {B : Set KA.MFCA} (h : B.Nonempty) :
    KA.polarDown B = Set.singleton zA := by
  ext g
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨m, hm⟩ := h
    exact mem_singleton_iff.2 ((FormalCtx.mem_polarDown_iff KA).1 hg hm)
  · have hg' : g = zA := mem_singleton_iff.1 hg
    exact (FormalCtx.mem_polarDown_iff KA).2 (fun {m} _ => hg')

lemma KA_down_univ {B : Set KA.MFCA} (h : ¬ B.Nonempty) :
    KA.polarDown B = (univ : Set KA.GFCA) := by
  ext g
  refine ⟨fun _ => mem_univ g, fun _ => ?_⟩
  exact (FormalCtx.mem_polarDown_iff KA).2 (fun {m} hm => absurd ⟨m, hm⟩ h)

lemma KC_up_single {A : Set KC.GFCA} (h : A.Nonempty) :
    KC.polarUp A = Set.singleton zC := by
  ext m
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · obtain ⟨g, hg⟩ := h
    exact mem_singleton_iff.2 ((FormalCtx.mem_polarUp_iff KC).1 hm hg)
  · have hm' : m = zC := mem_singleton_iff.1 hm
    exact (FormalCtx.mem_polarUp_iff KC).2 (fun {g} _ => hm')

lemma KC_up_univ {A : Set KC.GFCA} (h : ¬ A.Nonempty) :
    KC.polarUp A = (univ : Set KC.MFCA) := by
  ext m
  refine ⟨fun _ => mem_univ m, fun _ => ?_⟩
  exact (FormalCtx.mem_polarUp_iff KC).2 (fun {g} hg => absurd ⟨g, hg⟩ h)

lemma KC_down_univ {B : Set KC.MFCA} (h : B ⊆ Set.singleton zC) :
    KC.polarDown B = (univ : Set KC.GFCA) := by
  ext g
  refine ⟨fun _ => mem_univ g, fun _ => ?_⟩
  exact (FormalCtx.mem_polarDown_iff KC).2 (fun {m} hm => h hm)

lemma KC_down_empty {B : Set KC.MFCA} (h : ¬ B ⊆ Set.singleton zC) :
    KC.polarDown B = (∅ : Set KC.GFCA) := by
  ext g
  refine ⟨fun hg => ?_, fun hg => absurd hg (notMem_empty g)⟩
  exact h ((FormalCtx.mem_polarDown_iff KC).1 hg)

lemma KA_up_empty_set : KA.polarUp (∅ : Set KA.GFCA) = (univ : Set KA.MFCA) :=
  KA_up_univ (A := (∅ : Set KA.GFCA)) (by simp)

lemma KA_up_single_set : KA.polarUp (Set.singleton zA) = (univ : Set KA.MFCA) :=
  KA_up_univ (A := Set.singleton zA) (by simp)

lemma KA_up_univ_set : KA.polarUp (univ : Set KA.GFCA) = (∅ : Set KA.MFCA) := by
  apply KA_up_empty
  intro hc
  have : (oA : KA.GFCA) ∈ Set.singleton zA := hc (mem_univ oA)
  exact zA_ne_oA (Set.mem_singleton_iff.1 this).symm

lemma KA_down_empty_set : KA.polarDown (∅ : Set KA.MFCA) = (univ : Set KA.GFCA) :=
  KA_down_univ (B := (∅ : Set KA.MFCA)) (Set.not_nonempty_empty)

lemma KA_down_univ_set : KA.polarDown (univ : Set KA.MFCA) = Set.singleton zA :=
  KA_down_single (B := (univ : Set KA.MFCA)) ⟨(), mem_univ ()⟩

lemma KC_up_empty_set : KC.polarUp (∅ : Set KC.GFCA) = (univ : Set KC.MFCA) :=
  KC_up_univ (A := (∅ : Set KC.GFCA)) (Set.not_nonempty_empty)

lemma KC_up_univ_set : KC.polarUp (univ : Set KC.GFCA) = Set.singleton zC :=
  KC_up_single (A := (univ : Set KC.GFCA)) ⟨(), mem_univ ()⟩

lemma KC_down_univ_set : KC.polarDown (univ : Set KC.MFCA) = (∅ : Set KC.GFCA) := by
  apply KC_down_empty
  intro hc
  have : (oC : KC.MFCA) ∈ Set.singleton zC := hc (mem_univ oC)
  exact zC_ne_oC (Set.mem_singleton_iff.1 this).symm

lemma KC_down_single_set : KC.polarDown (Set.singleton zC) = (univ : Set KC.GFCA) :=
  KC_down_univ (B := Set.singleton zC) (by simp)

/-! ## 具体概念 -/

/-- KA 的 `⊥ = (univ, ∅)` -/
def KA_concept_EU : ConceptLattice KA :=
  ⟨univ, ∅, KA_up_univ_set, KA_down_empty_set⟩

/-- KA 的 `⊤ = ({zA}, univ)` -/
def KA_concept_ZU : ConceptLattice KA :=
  ⟨Set.singleton zA, univ, KA_up_single_set, KA_down_univ_set⟩

/-- KC 的 `⊥ = (∅, univ)` -/
def KC_concept_EU : ConceptLattice KC :=
  ⟨∅, univ, KC_up_empty_set, KC_down_univ_set⟩

/-- KC 的 `⊤ = (univ, {zC})` -/
def KC_concept_UZ : ConceptLattice KC :=
  ⟨univ, Set.singleton zC, KC_up_univ_set, KC_down_single_set⟩

/-! ## 概念格中 extent 只有两种取值 -/

lemma KA_extent_cases (c : ConceptLattice KA) :
    c.extent = Set.singleton zA ∨ c.extent = (univ : Set KA.GFCA) := by
  have hd : KA.polarDown c.intent = c.extent := c.lowerPolar_intent
  by_cases hn : c.intent.Nonempty
  · left; rw [← hd]; exact KA_down_single hn
  · right; rw [← hd]; exact KA_down_univ hn

lemma KC_extent_cases (c : ConceptLattice KC) :
    c.extent = (univ : Set KC.GFCA) ∨ c.extent = (∅ : Set KC.GFCA) := by
  have hd : KC.polarDown c.intent = c.extent := c.lowerPolar_intent
  by_cases hn : c.intent ⊆ Set.singleton zC
  · left; rw [← hd]; exact KC_down_univ hn
  · right; rw [← hd]; exact KC_down_empty hn

open Set

/-! ## 概念格的完备格结构下 `⊥`/`⊤` 的 extent -/

lemma KA_extent_ZU_le (c : ConceptLattice KA) :
    (Set.singleton zA : Set KA.GFCA) ⊆ c.extent := by
  rcases KA_extent_cases c with h | h
  · rw [h]; exact subset_rfl
  · rw [h]; exact subset_univ _

lemma KC_extent_EU_le (c : ConceptLattice KC) :
    (∅ : Set KC.GFCA) ⊆ c.extent := empty_subset _

lemma KA_bot_eq : (⊥ : ConceptLattice KA) = KA_concept_ZU := by
  apply le_antisymm
  · exact bot_le
  · rw [concept_le_iff_extent_subset]
    exact KA_extent_ZU_le _

lemma KC_bot_eq : (⊥ : ConceptLattice KC) = KC_concept_EU := by
  apply le_antisymm
  · exact bot_le
  · rw [concept_le_iff_extent_subset]
    exact KC_extent_EU_le _

lemma KA_bot_extent : (⊥ : ConceptLattice KA).extent = Set.singleton zA := by
  rw [KA_bot_eq]; rfl

lemma KC_bot_extent : (⊥ : ConceptLattice KC).extent = (∅ : Set KC.GFCA) := by
  rw [KC_bot_eq]; rfl

/-! ## 主要反例 -/

lemma KA_top_eq : (⊤ : ConceptLattice KA) = KA_concept_EU := by
  apply le_antisymm
  · rw [concept_le_iff_extent_subset]; exact subset_univ _
  · exact le_top

lemma KC_top_eq : (⊤ : ConceptLattice KC) = KC_concept_UZ := by
  apply le_antisymm
  · rw [concept_le_iff_extent_subset]; exact subset_univ _
  · exact le_top

lemma extent_KA_concept_EU : KA_concept_EU.extent = (univ : Set KA.GFCA) := rfl
lemma extent_KA_concept_ZU : KA_concept_ZU.extent = Set.singleton zA := rfl
lemma extent_KC_concept_EU : KC_concept_EU.extent = (∅ : Set KC.GFCA) := rfl
lemma extent_KC_concept_UZ : KC_concept_UZ.extent = (univ : Set KC.GFCA) := rfl

lemma KA_bot_extent' : (⊥ : ConceptLattice KA).extent = Set.singleton zA := KA_bot_extent
lemma KC_bot_extent' : (⊥ : ConceptLattice KC).extent = (∅ : Set KC.GFCA) := KC_bot_extent

lemma univ_ne_singleton_zA : (univ : Set KA.GFCA) ≠ Set.singleton zA := by
  intro h
  have h3 : oA ∈ Set.singleton zA := by rw [← h]; exact Set.mem_univ oA
  exact zA_ne_oA (Set.mem_singleton_iff.1 h3).symm

lemma univ_ne_empty_KC : (univ : Set KC.GFCA) ≠ (∅ : Set KC.GFCA) := by
  intro h
  have h3 : (() : KC.GFCA) ∈ (∅ : Set KC.GFCA) := by rw [← h]; exact Set.mem_univ ()
  exact h3

lemma KA_top_ne_bot : (⊤ : ConceptLattice KA) ≠ ⊥ := by
  intro hh
  have h := congrArg (fun x : ConceptLattice KA => x.extent) hh
  rw [KA_top_eq, extent_KA_concept_EU, KA_bot_extent] at h
  exact univ_ne_singleton_zA h

lemma KC_top_ne_bot : (⊤ : ConceptLattice KC) ≠ ⊥ := by
  intro hh
  have h := congrArg (fun x : ConceptLattice KC => x.extent) hh
  rw [KC_top_eq, extent_KC_concept_UZ, KC_bot_extent] at h
  exact univ_ne_empty_KC h

lemma KA_lattice_two (c : ConceptLattice KA) : c = ⊥ ∨ c = ⊤ := by
  rcases KA_extent_cases c with h | h
  · left
    have hb : c.extent ⊆ (⊥ : ConceptLattice KA).extent := by
      rw [KA_bot_extent, h]; exact subset_rfl
    exact le_antisymm ((concept_le_iff_extent_subset KA c ⊥).2 hb) bot_le
  · right
    have ht : (⊤ : ConceptLattice KA).extent ⊆ c.extent := by
      rw [KA_top_eq]; show (univ : Set KA.GFCA) ⊆ c.extent; rw [h]
    exact le_antisymm le_top ((concept_le_iff_extent_subset KA ⊤ c).2 ht)

lemma KC_lattice_two (c : ConceptLattice KC) : c = ⊥ ∨ c = ⊤ := by
  rcases KC_extent_cases c with h | h
  · right
    have ht : (⊤ : ConceptLattice KC).extent ⊆ c.extent := by
      rw [KC_top_eq]; show (univ : Set KC.GFCA) ⊆ c.extent; rw [h]
    exact le_antisymm le_top ((concept_le_iff_extent_subset KC ⊤ c).2 ht)
  · left
    have hb : c.extent ⊆ (⊥ : ConceptLattice KC).extent := by
      rw [KC_bot_extent, h]
    exact le_antisymm ((concept_le_iff_extent_subset KC c ⊥).2 hb) bot_le

/-- 把 KA 的概念映射到 KC 的概念（二元链之间的唯一单调双射） -/
noncomputable def phi : ConceptLattice KA → ConceptLattice KC := by
  classical
  exact fun c => if c = (⊥ : ConceptLattice KA) then ⊥ else ⊤

/-- `phi` 的逆 -/
noncomputable def psi : ConceptLattice KC → ConceptLattice KA := by
  classical
  exact fun d => if d = (⊥ : ConceptLattice KC) then ⊥ else ⊤

lemma phi_bot : phi (⊥ : ConceptLattice KA) = ⊥ := by simp [phi]

lemma phi_top : phi (⊤ : ConceptLattice KA) = ⊤ := by simp [phi, KA_top_ne_bot]

lemma psi_bot : psi (⊥ : ConceptLattice KC) = ⊥ := by simp [psi]

lemma psi_top : psi (⊤ : ConceptLattice KC) = ⊤ := by simp [psi, KC_top_ne_bot]

lemma phi_le_iff (c d : ConceptLattice KA) : phi c ≤ phi d ↔ c ≤ d := by
  have h3 : ¬ ((⊤ : ConceptLattice KA) ≤ (⊥ : ConceptLattice KA)) :=
    not_le_of_gt (lt_of_le_of_ne bot_le (Ne.symm KA_top_ne_bot))
  rcases KA_lattice_two c with rfl | rfl <;> rcases KA_lattice_two d with rfl | rfl
  · show phi (⊥ : ConceptLattice KA) ≤ phi ⊥ ↔ _
    rw [phi_bot]; exact iff_of_true bot_le bot_le
  · show phi (⊥ : ConceptLattice KA) ≤ phi ⊤ ↔ _
    rw [phi_bot, phi_top]; exact iff_of_true bot_le bot_le
  · show phi (⊤ : ConceptLattice KA) ≤ phi ⊥ ↔ _
    rw [phi_top, phi_bot]
    exact iff_of_false (not_le_of_gt (lt_of_le_of_ne bot_le (Ne.symm KC_top_ne_bot))) h3
  · show phi (⊤ : ConceptLattice KA) ≤ phi ⊤ ↔ _
    rw [phi_top]; exact iff_of_true le_top le_top

lemma psi_phi (c : ConceptLattice KA) : psi (phi c) = c := by
  rcases KA_lattice_two c with rfl | rfl
  · rw [phi_bot, psi_bot]
  · rw [phi_top, psi_top]

lemma phi_psi (d : ConceptLattice KC) : phi (psi d) = d := by
  rcases KC_lattice_two d with rfl | rfl
  · rw [psi_bot, phi_bot]
  · rw [psi_top, phi_top]

/-- **反例主定理**：两个形式背景的概念格同构。 -/
theorem KA_KC_lattice_iso : Nonempty (ConceptLattice KA ≃o ConceptLattice KC) := by
  classical
  refine ⟨{ toEquiv := ⟨phi, psi, psi_phi, phi_psi⟩, map_rel_iff' := ?_ }⟩
  intro c d
  exact phi_le_iff c d

/-- 但两面在"extent 在哪一端"上不同：KA 的 `⊥` 有非空 extent `{zA}`。 -/
theorem KA_bot_extent_nonempty : (⊥ : ConceptLattice KA).extent.Nonempty := by
  rw [KA_bot_extent]; exact ⟨zA, Set.mem_singleton zA⟩

/-- 而 KC 的 `⊥` 的 extent 为空。 -/
theorem KC_bot_extent_empty : (⊥ : ConceptLattice KC).extent = (∅ : Set KC.GFCA) :=
  KC_bot_extent

/-- **核心断言**：不存在同时保持 extent 的概念格同构 ——
即概念格同构无法恢复 extent/ intent 的对应关系。 -/
theorem no_extent_preserving_iso :
    ¬ ∃ e : ConceptLattice KA ≃o ConceptLattice KC,
        ∀ c : ConceptLattice KA, (e c).extent.Nonempty ↔ c.extent.Nonempty := by
  rintro ⟨e, hpres⟩
  have hbot : e (⊥ : ConceptLattice KA) = (⊥ : ConceptLattice KC) := map_bot e
  have h1 : ¬ (e (⊥ : ConceptLattice KA)).extent.Nonempty := by
    rw [hbot, KC_bot_extent]
    exact Set.not_nonempty_empty
  have h2 := (hpres ⊥).2
  exact h1 (h2 KA_bot_extent_nonempty)

/-- 更强的形式：**连 extent 的基数**都不能保 —— `|⊥.extent| = 1`（KA）
    对 `|⊥.extent| = 0`（KC）。 -/
theorem no_extent_card_preserving_iso :
    ¬ ∃ e : ConceptLattice KA ≃o ConceptLattice KC,
        ∀ c : ConceptLattice KA,
          (e c).extent = (∅ : Set KC.GFCA) ↔ c.extent = (∅ : Set KA.GFCA) := by
  rintro ⟨e, hpres⟩
  have hbot : e (⊥ : ConceptLattice KA) = (⊥ : ConceptLattice KC) := map_bot e
  have h1 : (e (⊥ : ConceptLattice KA)).extent = (∅ : Set KC.GFCA) := by
    rw [hbot, KC_bot_extent]
  have h2 := (hpres ⊥).1 h1
  rw [KA_bot_extent] at h2
  have h3 : zA ∈ (∅ : Set KA.GFCA) := by
    rw [← h2]; exact Set.mem_singleton zA
  exact h3

/-! ### 反例的"两面性"：`⊤` 侧恰好反向

  KA 的 `⊤` 的 extent 是 `univ`（非空），KC 的 `⊤` 的 extent 也是 `univ`。
  所以**差别只在 `⊥` 侧**，且是"extent 与 intent 的角色对调"：
  KA 的 `⊥ = ({zA}, univ)` 是"extent 小、intent 大"；
  KC 的 `⊥ = (∅, univ)` 是"extent 空、intent 大"。
  任何格同构都无法把这两种"非空性"对上。 -/

/-- KC 的 `⊤` extent 是 `univ`（与 KA 一致，说明差异在 `⊥` 侧） -/
theorem KC_top_extent : (⊤ : ConceptLattice KC).extent = (univ : Set KC.GFCA) := by
  rw [KC_top_eq]; rfl

/-- KA 的 `⊤` extent 也是 `univ` -/
theorem KA_top_extent : (⊤ : ConceptLattice KA).extent = (univ : Set KA.GFCA) := by
  rw [KA_top_eq]; rfl

end Counterexample

end Fate
