import FateWorld.FateV2.Rules.LawRule
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic

/-!
  # Rules · LawRulePointDecidability

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRulePointDecidability.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! **Verified, zero-sorry replacement** for `FateV2.Rules`.
  Kept under a separate module name so the in-progress edit of the original file is not clobbered.
  To promote: copy this file over `Fate/LawRulePointDecidability.lean`. -/

/-! Corrected decidability module (development copy). -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open Set MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

theorem isPoint_explicit (R : LawRule C X Y) :
    IsPoint R ↔ ∀ c x, ∃ μ ∈ R c x, ∀ ν ∈ R c x, ν = μ := by
  constructor
  · intro h c x
    obtain ⟨μ, hμ⟩ := h c x
    refine ⟨μ, ?_, ?_⟩
    · rw [hμ]; exact mem_singleton μ
    · intro ν hν; rw [hμ] at hν; exact mem_singleton_iff.mp hν
  · intro h c x
    obtain ⟨μ, hμ, huniq⟩ := h c x
    exact ⟨μ, Subset.antisymm (fun ν hν => mem_singleton_iff.mpr (huniq ν hν))
      (singleton_subset_iff.mpr hμ)⟩

theorem singleton_iff_nonempty_subsingleton {α : Type*} {S : Set α} :
    (∃ μ, S = {μ}) ↔ S.Nonempty ∧ S.Subsingleton := by
  constructor
  · rintro ⟨μ, rfl⟩
    exact ⟨singleton_nonempty μ, subsingleton_singleton⟩
  · rintro ⟨⟨μ, hμ⟩, hsub⟩
    exact ⟨μ, hsub.eq_singleton_of_mem hμ⟩

theorem isPoint_iff_nonempty_subsingleton (R : LawRule C X Y) :
    IsPoint R ↔ ∀ c x, (R c x).Nonempty ∧ (R c x).Subsingleton := by
  rw [isPoint_explicit]
  constructor
  · intro h c x
    obtain ⟨μ, hμ, huniq⟩ := h c x
    exact ⟨⟨μ, hμ⟩, fun a ha b hb => (huniq a ha).trans (huniq b hb).symm⟩
  · intro h c x
    obtain ⟨⟨μ, hμ⟩, hsub⟩ := h c x
    exact ⟨μ, hμ, fun ν hν => hsub hν hμ⟩

def genRule (G : Finset ι) (g : ι → Set (Measure Y.Carrier)) : LawRule C X Y :=
  fun _ _ => ⋃ i ∈ G, g i

@[simp] theorem genRule_apply (G : Finset ι)
    (g : ι → Set (Measure Y.Carrier)) (c x) :
    genRule (C := C) (X := X) (Y := Y) G g c x = ⋃ i ∈ G, g i := rfl

theorem isPoint_genRule_iff [Nonempty C.Carrier] [Nonempty X.Carrier]
    (G : Finset ι) (g : ι → Set (Measure Y.Carrier)) :
    IsPoint (genRule (C := C) (X := X) (Y := Y) G g) ↔
      ∃ i₀ ∈ G, (∃ μ, g i₀ = {μ}) ∧ g i₀ = ⋃ i ∈ G, g i := by
  constructor
  · intro hp
    obtain ⟨μ, hμ⟩ := hp (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier)
    have hU : (⋃ i ∈ G, g i) = ({μ} : Set (Measure Y.Carrier)) := hμ
    have hmem : μ ∈ ⋃ i ∈ G, g i := by rw [hU]; exact mem_singleton μ
    obtain ⟨i₀, hi₀G, hi₀μ⟩ := mem_iUnion₂.mp hmem
    have hsub : g i₀ ⊆ ({μ} : Set (Measure Y.Carrier)) := by
      intro ν hν
      have : ν ∈ ⋃ i ∈ G, g i := mem_iUnion₂.mpr ⟨i₀, hi₀G, hν⟩
      rw [hU] at this; exact this
    have hsing : g i₀ = ({μ} : Set (Measure Y.Carrier)) :=
      Subset.antisymm hsub (singleton_subset_iff.mpr hi₀μ)
    exact ⟨i₀, hi₀G, ⟨μ, hsing⟩, hsing.trans hU.symm⟩
  · rintro ⟨i₀, hi₀G, ⟨μ, hg⟩, hEqu⟩ c x
    exact ⟨μ, by rw [genRule_apply, ← hEqu, hg]⟩

theorem finset_coe_singleton_iff [DecidableEq (Measure Y.Carrier)]
    (s : Finset (Measure Y.Carrier)) :
    (∃ μ, (s : Set (Measure Y.Carrier)) = {μ}) ↔ s.card = 1 := by
  constructor
  · rintro ⟨μ, hμ⟩
    have hs : s = {μ} := by
      apply Finset.coe_inj.mp
      rw [hμ]
      simp
    rw [hs, Finset.card_singleton]
  · intro h
    obtain ⟨μ, hμ⟩ := Finset.card_eq_one.mp h
    exact ⟨μ, by rw [hμ]; simp⟩

/-- The decidable predicate used by the algorithm.
`G` is the finite generating set; `g i` the (finite) set contributed by generator `i`. -/
abbrev pointSearch [DecidableEq ι] (G : Finset ι)
    (g : ι → Finset (Measure Y.Carrier)) : Prop :=
  ∃ i₀ ∈ G, (g i₀).card = 1 ∧ ∀ i ∈ G, ∀ ν ∈ g i, ν ∈ g i₀

/-- **Core slice lemma**: the search criterion is exactly single-pointedness of the union. -/
theorem pointSearch_iff_slice [DecidableEq ι] [DecidableEq (Measure Y.Carrier)]
    (G : Finset ι) (g : ι → Finset (Measure Y.Carrier)) :
    pointSearch G g ↔ (∃ μ, (⋃ i ∈ G, (g i : Set (Measure Y.Carrier))) = {μ}) := by
  constructor
  · rintro ⟨i₀, hi₀, hcard, hsub⟩
    obtain ⟨μ, hμ⟩ := (finset_coe_singleton_iff (g i₀)).mpr hcard
    refine ⟨μ, Subset.antisymm (fun ν hν => ?_) (fun ν hν => ?_)⟩
    · obtain ⟨i, hi, hν'⟩ := mem_iUnion₂.mp hν
      have hmem : ν ∈ ((g i₀ : Finset (Measure Y.Carrier)) : Set (Measure Y.Carrier)) :=
        hsub i hi ν hν'
      rw [hμ] at hmem
      exact hmem
    · exact mem_iUnion₂.mpr ⟨i₀, hi₀, by rw [hμ]; exact hν⟩
  · rintro ⟨μ, hU⟩
    have hmem : μ ∈ ⋃ i ∈ G, (g i : Set (Measure Y.Carrier)) := by
      rw [hU]; exact mem_singleton μ
    obtain ⟨i₀, hi₀, hi₀μ⟩ := mem_iUnion₂.mp hmem
    -- `g i₀ ⊆ ⋃ = {μ}`, and it is nonempty, so it *is* `{μ}`
    have hsubU : ((g i₀ : Finset (Measure Y.Carrier)) : Set (Measure Y.Carrier)) ⊆ {μ} := by
      intro a ha
      have : a ∈ ⋃ j ∈ G, ((g j : Finset (Measure Y.Carrier)) : Set (Measure Y.Carrier)) :=
        mem_iUnion₂.mpr ⟨i₀, hi₀, ha⟩
      rw [hU] at this
      exact this
    have hg : ((g i₀ : Finset (Measure Y.Carrier)) : Set (Measure Y.Carrier)) = {μ} :=
      Subset.antisymm hsubU (singleton_subset_iff.mpr hi₀μ)
    refine ⟨i₀, hi₀, (finset_coe_singleton_iff (g i₀)).mp ⟨μ, hg⟩, ?_⟩
    intro i hi ν hν
    have : ν ∈ ⋃ j ∈ G, ((g j : Finset (Measure Y.Carrier)) : Set (Measure Y.Carrier)) :=
      mem_iUnion₂.mpr ⟨i, hi, hν⟩
    rw [hU] at this
    show ν ∈ ((g i₀ : Finset (Measure Y.Carrier)) : Set (Measure Y.Carrier))
    rw [hg]
    exact this

/-- **Finite-generation criterion** (semantic, for `genRule`). -/
theorem isPoint_genRule_iff_search [Nonempty C.Carrier] [Nonempty X.Carrier]
    [DecidableEq ι] [DecidableEq (Measure Y.Carrier)]
    (G : Finset ι) (g : ι → Finset (Measure Y.Carrier)) :
    IsPoint (genRule (C := C) (X := X) (Y := Y) G
        (fun i => (g i : Set (Measure Y.Carrier)))) ↔ pointSearch G g := by
  rw [isPoint_genRule_iff]
  constructor
  · rintro ⟨i₀, hi₀, ⟨μ, hμ⟩, hEq⟩
    refine (pointSearch_iff_slice G g).mpr ⟨μ, ?_⟩
    rw [← hEq, hμ]
  · intro h
    obtain ⟨μ, hU⟩ := (pointSearch_iff_slice G g).mp h
    have hmem : μ ∈ ⋃ i ∈ G, (g i : Set (Measure Y.Carrier)) := by
      rw [hU]; exact mem_singleton μ
    obtain ⟨i₀, hi₀, hi₀μ⟩ := mem_iUnion₂.mp hmem
    have hg : (g i₀ : Set (Measure Y.Carrier)) = {μ} := by
      refine Subset.antisymm (fun a ha => ?_) ?_
      · have : a ∈ ⋃ j ∈ G, ((g j : Finset (Measure Y.Carrier)) : Set (Measure Y.Carrier)) :=
          mem_iUnion₂.mpr ⟨i₀, hi₀, ha⟩
        rw [hU] at this; exact this
      · exact singleton_subset_iff.mpr hi₀μ
    exact ⟨i₀, hi₀, ⟨μ, hg⟩, by rw [hg, hU]⟩

instance instDecidableIsPointGenRule [Nonempty C.Carrier] [Nonempty X.Carrier]
    [DecidableEq ι] [DecidableEq (Measure Y.Carrier)] (G : Finset ι)
    (g : ι → Finset (Measure Y.Carrier)) :
    Decidable (IsPoint (genRule (C := C) (X := X) (Y := Y) G
      (fun i => (g i : Set (Measure Y.Carrier))))) :=
  decidable_of_iff (pointSearch G g) (isPoint_genRule_iff_search G g).symm

def genRuleDep (G : Finset ι)
    (g : ι → C.Carrier → X.Carrier → Set (Measure Y.Carrier)) : LawRule C X Y :=
  fun c x => ⋃ i ∈ G, g i c x

theorem genRuleDep_apply (G : Finset ι)
    (g : ι → C.Carrier → X.Carrier → Set (Measure Y.Carrier)) (c x) :
    genRuleDep (Y := Y) G g c x = ⋃ i ∈ G, g i c x := rfl

/-- **Global criterion** for `(c,x)`-dependent generators. -/
theorem isPoint_genRuleDep_iff [Fintype C.Carrier] [Fintype X.Carrier]
    [DecidableEq ι] [DecidableEq (Measure Y.Carrier)]
    (G : Finset ι) (g : ι → C.Carrier → X.Carrier → Finset (Measure Y.Carrier)) :
    IsPoint (genRuleDep (Y := Y) G (fun i c x => (g i c x : Set (Measure Y.Carrier))))
      ↔ ∀ c x, pointSearch G (fun i => g i c x) := by
  constructor
  · intro h c x
    obtain ⟨μ, hμ⟩ := h c x
    exact (pointSearch_iff_slice G (fun i => g i c x)).mpr ⟨μ, by rw [← hμ, genRuleDep_apply]⟩
  · intro h c x
    exact (pointSearch_iff_slice G (fun i => g i c x)).mp (h c x)

instance instDecidableIsPointGenRuleDep [Fintype C.Carrier] [Fintype X.Carrier]
    [DecidableEq ι] [DecidableEq (Measure Y.Carrier)] (G : Finset ι)
    (g : ι → C.Carrier → X.Carrier → Finset (Measure Y.Carrier)) :
    Decidable (IsPoint (genRuleDep (Y := Y) G
      (fun i c x => (g i c x : Set (Measure Y.Carrier))))) :=
  decidable_of_iff (∀ c x, pointSearch G (fun i => g i c x))
    (isPoint_genRuleDep_iff G g).symm

def constRule (S : Set (Measure Y.Carrier)) : LawRule C X Y := fun _ _ => S

theorem isPoint_constRule_iff [Nonempty C.Carrier] [Nonempty X.Carrier]
    (S : Set (Measure Y.Carrier)) :
    IsPoint (constRule (C := C) (X := X) (Y := Y) S) ↔ ∃ μ, S = {μ} := by
  constructor
  · intro h
    exact h (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier)
  · rintro ⟨μ, hμ⟩ _ _; exact ⟨μ, hμ⟩

theorem isPoint_reduces_to_singleton_search [Nonempty C.Carrier] [Nonempty X.Carrier] :
    (∀ S : Set (Measure Y.Carrier),
        Nonempty (Decidable (IsPoint (constRule (C := C) (X := X) (Y := Y) S)))) ↔
      (∀ S : Set (Measure Y.Carrier), Nonempty (Decidable (∃ μ, S = {μ}))) := by
  constructor
  · intro h S
    obtain ⟨d⟩ := h S
    letI := d
    exact ⟨decidable_of_iff (IsPoint (constRule (C := C) (X := X) (Y := Y) S))
      (isPoint_constRule_iff S)⟩
  · intro h S
    obtain ⟨d⟩ := h S
    letI := d
    exact ⟨decidable_of_iff (∃ μ, S = {μ}) (isPoint_constRule_iff S).symm⟩

theorem subsingleton_decidable_of_singleton_search {α : Type*} [Nonempty α]
    (h : ∀ S : Set α, Nonempty (Decidable (∃ a, S = ({a} : Set α)))) :
    Nonempty (Decidable (Subsingleton α)) := by
  obtain ⟨d⟩ := h Set.univ
  letI := d
  exact ⟨decidable_of_iff (∃ a, (Set.univ : Set α) = ({a} : Set α))
    ⟨fun ⟨a, ha⟩ => ⟨fun x y => by
        have hx : x ∈ ({a} : Set α) := ha ▸ mem_univ x
        have hy : y ∈ ({a} : Set α) := ha ▸ mem_univ y
        exact (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm⟩,
      fun hsub => ⟨Classical.arbitrary α,
        Set.eq_singleton_iff_unique_mem.mpr
          ⟨mem_univ _, fun y _ => Subsingleton.elim y _⟩⟩⟩⟩

theorem isPoint_ruleToLaw [MeasurableSpace X.Carrier] (r : Rule C X Y) :
    IsPoint (Rule.toLaw r) := fun _ _ => ⟨_, rfl⟩

theorem isPoint_detFunToLaw (f : C.Carrier → X.Carrier → Y.Carrier) :
    IsPoint (DetFun.toLaw f) := fun _ _ => ⟨_, rfl⟩

theorem not_isPoint_of_strict_generalize {R₁ R₂ : LawRule C X Y}
    (hsub : ∀ c x, R₁ c x ⊆ R₂ c x)
    (hs : ∃ c x μ, R₂ c x = {μ} ∧ ∃ ν ∈ R₁ c x, ν ≠ μ) :
    ¬ IsPoint (generalize R₁ R₂ hsub) := by
  obtain ⟨c₀, x₀, μ, hR₂, ν, hν, hνμ⟩ := hs
  intro hp
  obtain ⟨μ', hμ'⟩ := hp c₀ x₀
  have hEq : ({μ} : Set (Measure Y.Carrier)) = {μ'} := hR₂ ▸ hμ'
  have hνS : ν ∈ ({μ} : Set (Measure Y.Carrier)) := by
    rw [← hR₂]; exact hsub c₀ x₀ hν
  have hν' : ν = μ' := mem_singleton_iff.mp (hEq ▸ hνS)
  have hμμ' : μ = μ' := mem_singleton_iff.mp (hEq ▸ mem_singleton μ)
  exact hνμ (hν'.trans hμμ'.symm)

end LawRule
end FateV2.Rules