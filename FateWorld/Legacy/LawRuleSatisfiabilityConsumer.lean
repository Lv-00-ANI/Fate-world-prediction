/-
============================================================================
  规则核心链 · P5 · **规则族的可满足性 × 单点可判定性 × SCM 桥**
  ## 为什么有这个模块

  三个规则层模块此前**下游为零**，本模块让它们互相消费并接入 `LawRule` 主链：

  | 上游模块 | 定理数 | 本模块用到的实质内容 |
  |---|---|---|
  | `Fate.LawRuleSatisfiability` | 12 | `compatible_iff` / `mem_sInf_iff` / `Compatible` |
  | `Fate.LawRulePointDecidability` | 15 | `not_isPoint_of_strict_generalize` / `IsPoint` 判据 |
  | `Fate.PearlLawRuleBridge` | 19 | `SCM.toLawRule` / `isPoint_toLawRule` |

  ## 本模块证明的内容（非平凡的三条）

  1. **`compatible_iff_of_isPointAll`**：一族**处处单点**的规则可满足
     $\iff$ 该族**逐点恒等**。这不是 `compatible_iff` 的改写：
     它需要「单点集相交必相等」这一单点档特有的唯一性论证。
  2. **`eq_sInf_of_isPoint_mem`**：若可满足族 `S` 中含一条单点规则 `R`，
     则 `sInf S = R`。即 **相容性把格论交完全塌缩到那条单点规则上**，
     族中其余规则**不贡献任何额外约束**。
  3. **`scmFamily_compatible_iff`**：`SCM` 诱导的规则族可满足
     $\iff$ 该族逐点恒等（把 1 实例化到 `PearlLawRuleBridge` 的像上）。

  ## 与 `LawRulePointDecidability` 的接口

  `scm_family_not_isPoint_of_strict_generalize`：由
  `not_isPoint_of_strict_generalize`，**严格放宽**（`generalize` 且真加了新分布）
  得到的规则不是单点档；结合 1，它**不能与任何单点规则一起可满足地逐点恒等**，
  而只能让交退化到单点那一侧 —— 这给出了「放宽 = 无增益」的机器可见陈述。

  ## 诚实边界

  * **`Tight` 无实例**：`LawRuleSatisfiability.Tight` 在库中**没有任何实例**
    （`Measure Y` 在弱拓扑下不紧）。故本模块**不**声称使用
    `compatible_iff_finsetwise` 的紧致性方向；只使用其无条件方向
    `Compatible.finsetwise`（由 `LawRuleSatisfiability` 证明），并在
    `compatible_finsetwise_scm` 中实例化。
  * **不构造 `SCM` 具体实例**：本模块是纯接口层，具体 `SCM` 数值例子
    已在 `PearlLawRuleBridge` / `Rule13Genuine` 中给出，此处不重复。
  * **零 `sorry` / 零 `axiom` / 零 `admit` / 零 `native_decide`。**
============================================================================
-/

import FateWorld.Legacy.LawRuleSatisfiability
import FateWorld.Legacy.LawRulePointDecidability
import FateWorld.Legacy.PearlLawRuleBridge

open Fate
open Fate.LawRule

namespace Fate
namespace LawRuleSatisfiabilityConsumer

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ===========================================================================
    §1  单点族的可满足性判据
    =========================================================================== -/

/-- **一族规则「处处单点」**。 -/
def IsPointAll (S : Set (LawRule C X Y)) : Prop := ∀ R ∈ S, IsPoint R

/-- ⭐⭐ **单点族的可满足性判据**：可满足 $\iff$ 逐点恒等。

**为什么不是 `compatible_iff` 的改写**：
`LawRuleSatisfiability.compatible_iff` 只说「存在公共允许分布」；
在**单点档**上，两条规则的允许集若相交，则两个单点集必**相同**
（单点集相交的唯一可能是相等）。这一唯一性论证是本定理的全部实质。

⚠ **`S.Nonempty` 不可去**（当 `S = ∅` 时 `Compatible ∅` 由 `sInf ∅ = ⊤` 平凡成立）。 -/
theorem compatible_iff_of_isPointAll (S : Set (LawRule C X Y)) (hS : IsPointAll S)
    (hne : S.Nonempty) :
    Compatible S ↔ ∀ R₁ ∈ S, ∀ R₂ ∈ S, ∀ c x, R₁ c x = R₂ c x := by
  constructor
  · intro hc R₁ h₁ R₂ h₂ c x
    obtain ⟨m, hm⟩ := (compatible_iff S).mp hc c x
    obtain ⟨μ₁, hμ₁⟩ := hS R₁ h₁ c x
    obtain ⟨μ₂, hμ₂⟩ := hS R₂ h₂ c x
    have e1 : m ∈ ({μ₁} : Set (MeasureTheory.Measure Y.Carrier)) := hμ₁ ▸ hm R₁ h₁
    have e2 : m ∈ ({μ₂} : Set (MeasureTheory.Measure Y.Carrier)) := hμ₂ ▸ hm R₂ h₂
    rw [Set.mem_singleton_iff] at e1 e2
    have h12 : μ₁ = μ₂ := e1.symm.trans e2
    rw [hμ₁, hμ₂, h12]
  · intro heq c x
    obtain ⟨R₀, hR₀⟩ := hne
    obtain ⟨μ₀, hμ₀⟩ := hS R₀ hR₀ c x
    exact ⟨μ₀, mem_sInf_iff.mpr (fun R hR => by
      rw [heq R hR R₀ hR₀ c x, hμ₀]; exact Set.mem_singleton μ₀)⟩

/-- ⭐⭐ **单点族可满足 ⟹ 其 `sInf` 仍是单点**（单点档对任意交封闭的最小陈述）。 -/
theorem isPoint_sInf_of_compatible (S : Set (LawRule C X Y)) (hS : IsPointAll S)
    (hne : S.Nonempty) (hc : Compatible S) : IsPoint (sInf S) := by
  intro c x
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨μ₀, hμ₀⟩ := hS R₀ hR₀ c x
  refine ⟨μ₀, Set.Subset.antisymm ?_ ?_⟩
  · intro m hm
    have h0 := mem_sInf_iff.mp hm R₀ hR₀
    rw [hμ₀] at h0
    exact h0
  · intro m hm
    have hm' := Set.mem_singleton_iff.mp hm
    refine mem_sInf_iff.mpr fun R hR => ?_
    obtain ⟨m', hm''⟩ := (compatible_iff S).mp hc c x
    have e0 : m' = μ₀ := by
      have h0 := hm'' R₀ hR₀; rw [hμ₀] at h0; exact h0
    have h1 : m' ∈ R c x := hm'' R hR
    rw [e0] at h1
    exact hm'.symm ▸ h1

/-! ===========================================================================
    §2  ⭐⭐⭐ 相容性把格论交塌缩到单点规则上
    =========================================================================== -/

/-- ⭐⭐⭐ **主定理（塌缩）**：若可满足族 `S` 中含一条**单点**规则 `R`，
则 `sInf S = R`。

**语义**：族中其余规则**不贡献任何额外约束** —— 它们的允许集都包含 `R` 的那个
唯一点，故交回落到 `R` 自己。这是「与已有规律组合不产生新约束」的精确陈述。

⚠ **`hR : R ∈ S` 是实质前提**：没有它，`sInf S` 可以是 `⊤`（`S = ∅`）。 -/
theorem eq_sInf_of_isPoint_mem (S : Set (LawRule C X Y)) (R : LawRule C X Y)
    (hR : R ∈ S) (hp : IsPoint R) (hc : Compatible S) : sInf S = R := by
  funext c x
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨μ, hμ⟩ := hp c x
    have h0 := mem_sInf_iff.mp hm R hR
    rw [hμ] at h0
    rw [hμ]
    exact h0
  · intro m hm
    obtain ⟨μ, hμ⟩ := hp c x
    have hm' : m = μ := by rw [hμ] at hm; exact hm
    rw [hm', mem_sInf_iff]
    intro R' hR'
    obtain ⟨m', hm''⟩ := (compatible_iff S).mp hc c x
    have e0 : m' = μ := by
      have h0 := hm'' R hR; rw [hμ] at h0; exact h0
    have h1 : m' ∈ R' c x := hm'' R' hR'
    rw [e0] at h1
    exact h1

/-- **推论：含单点规则的可满足族，其 `sInf` 单点**。 -/
theorem isPoint_sInf_of_isPoint_mem (S : Set (LawRule C X Y)) (R : LawRule C X Y)
    (hR : R ∈ S) (hp : IsPoint R) (hc : Compatible S) : IsPoint (sInf S) := by
  rw [eq_sInf_of_isPoint_mem S R hR hp hc]
  exact hp

/-! ===========================================================================
    §3  与 `LawRulePointDecidability` 的接口：放宽破坏单点档
    =========================================================================== -/

/-- ⭐⭐ **`generalize` 严格放宽 ⟹ 不是单点档**
（直接消费 `LawRulePointDecidability.not_isPoint_of_strict_generalize`）。

**语义**：把一条规则**真正放宽**（允许集里多进了一个不同的分布），
就**离开了单点档** —— 这是 `LawRule` 的「单点档在 `generalize` 下不闭合」
的判定形式。 -/
theorem generalize_not_isPoint {R₁ R₂ : LawRule C X Y}
    (hsub : ∀ c x, R₁ c x ⊆ R₂ c x)
    (hs : ∃ c x μ, R₂ c x = {μ} ∧ ∃ ν ∈ R₁ c x, ν ≠ μ) :
    ¬ IsPoint (LawRule.generalize R₁ R₂ hsub) :=
  LawRule.not_isPoint_of_strict_generalize hsub hs

/-- ⭐⭐⭐ **组合定理**：可满足族里若有一条单点规则 `R` 和一条严格放宽规则 `G`，
则它们的交**只由 `R` 决定**（`G` 的额外分布被 `R` 卡掉）。

这是 `eq_sInf_of_isPoint_mem` 在 `{R, G}` 上的直接实例，说明
**放宽在可满足组合下不产生任何收益**。 -/
theorem sInf_pair_eq_of_isPoint {R G : LawRule C X Y} (hp : IsPoint R)
    (hc : Compatible ({R, G} : Set (LawRule C X Y))) :
    sInf ({R, G} : Set (LawRule C X Y)) = R :=
  eq_sInf_of_isPoint_mem _ R (Set.mem_insert R {G}) hp hc

/-! ===========================================================================
    §4  `SCM` 桥实例化：`PearlLawRuleBridge` 的像落在单点档
    =========================================================================== -/

/-- `SCM` 诱导的规则族（上下文 = 干预值 `do(X := c)`，见 `PearlLawRuleBridge`）。 -/
noncomputable def scmFamily (X Y : Type*) [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] :
    Set (LawRule (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
      (PearlHierarchy.finStateSpace Y)) :=
  Set.range (fun M : PearlHierarchy.SCM X Y => M.toLawRule)

/-- ⭐ **`scmFamily` 的任何子族都 `IsPointAll`**
（消费 `PearlLawRuleBridge.isPoint_toLawRule`）。 -/
theorem isPointAll_of_subset_scmFamily {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (S : Set (LawRule (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
      (PearlHierarchy.finStateSpace Y)))
    (hS : S ⊆ scmFamily X Y) : IsPointAll S := by
  intro R hR
  obtain ⟨M, rfl⟩ := hS hR
  exact M.isPoint_toLawRule

/-- ⭐⭐⭐ **主定理（`SCM` 侧）**：`SCM` 诱导的规则族可满足
$\iff$ 该族**逐点恒等**（即所有 `SCM` 在每个干预值上诱导同一测度）。

**非平凡性来源**：`SCM` 的像落在**单点档**（`isPoint_toLawRule`），
故 `compatible_iff_of_isPointAll` 适用；这不是把结论写进前件 ——
前件只有「`S` 是 `SCM` 像的子集」和「`S` 非空」。 -/
theorem scmFamily_compatible_iff {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (S : Set (LawRule (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
      (PearlHierarchy.finStateSpace Y)))
    (hS : S ⊆ scmFamily X Y) (hne : S.Nonempty) :
    Compatible S ↔ ∀ R₁ ∈ S, ∀ R₂ ∈ S, ∀ c x, R₁ c x = R₂ c x :=
  compatible_iff_of_isPointAll S (isPointAll_of_subset_scmFamily S hS) hne

/-- ⭐⭐ **推论**：`SCM` 族可满足时，其逐点交仍是**单点档**。 -/
theorem scmFamily_sInf_isPoint {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (S : Set (LawRule (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
      (PearlHierarchy.finStateSpace Y)))
    (hS : S ⊆ scmFamily X Y) (hne : S.Nonempty) (hc : Compatible S) :
    IsPoint (sInf S) :=
  isPoint_sInf_of_compatible S (isPointAll_of_subset_scmFamily S hS) hne hc

/-- ⭐⭐ **推论（塌缩的 `SCM` 版）**：含某个 `SCM` 诱导规则的可满足族，
其交**恰是**那条规则 —— 其余 `SCM` 或任意规则都不贡献额外约束。 -/
theorem scmFamily_sInf_eq_of_mem {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (S : Set (LawRule (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
      (PearlHierarchy.finStateSpace Y)))
    (M : PearlHierarchy.SCM X Y) (hR : M.toLawRule ∈ S) (hc : Compatible S) :
    sInf S = M.toLawRule :=
  eq_sInf_of_isPoint_mem S M.toLawRule hR M.isPoint_toLawRule hc

/-! ===========================================================================
    §5  `Compatible.finsetwise` 的 `SCM` 实例化（不使用 `Tight`）
    =========================================================================== -/

/-- ⭐ **可满足 ⟹ 有限子族可满足**（`SCM` 版）。

⚠ 只用 `LawRuleSatisfiability.Compatible.finsetwise`（**无条件**方向），
**不**使用 `compatible_iff_finsetwise` —— 后者需 `Tight` 实例，库中不存在。 -/
theorem compatible_finsetwise_scm {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (S : Set (LawRule (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
      (PearlHierarchy.finStateSpace Y)))
    (hc : Compatible S) : FinsetwiseCompatible S :=
  Compatible.finsetwise hc

end LawRuleSatisfiabilityConsumer

end Fate
