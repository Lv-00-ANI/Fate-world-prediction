import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation

/-! ===========================================================================
  §23  ⭐⭐ **数据融合的桥论形式化**（原 `_probe_fusion` 的正式化）

  **来源**：探针 `probes/_probe_fusion.lean`（**不在构建内**）。

  ## 问题

  **多个不同来源的数据集（不同人群／不同时期）能否联合识别？**

  ## ⭐ 形式化：**桥的纤维之交**

  | 概念 | 定义 |
  |---|---|
  | **识别域** | 来源 `e` 允许的 SCM 集合 `B e` |
  | **联合识别域** | `fused B := ⋂ e, B e` |

  ## ⭐⭐ 五条已证性质

  | # | 命题 | 内容 |
  |---|---|---|
  | **15.1** | `fused_subset_source` | **融合永不扩大识别域**（单调性）|
  | **15.2** | `fusion_no_gain_of_common` | ⭐ **来源全同 ⟹ 融合零增益** |
  | **15.3** | `fusion_single_iff` | 融合压成单点 $\iff$ 交是 `Subsingleton` 且非空 |
  | **15.4** | `single_source_sufficient_of_subsingleton` | 单来源已单值 ⟹ 融合冗余 |
  | **15.5** | `strict_gain_implies_no_single_source` | ⭐ **严格增益 ⟹ 无单来源已单值** |

  ## ⭐⭐ 核心洞察

  **153.2 是本节最重要的结论**：
  **「多来源」本身不产生鉴别力** ——
  **增益必须来自来源之间的**差异****。

  ## ⚠ 诚实边界（模块自标）

  **本节只证**集合论层面**的性质** ——
  「来源差异是否**统计上可检验**、差异是否**足以**收缩纤维」
  是**统计学**问题，**不在本节断言范围内**。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace Fusion

universe u v

variable {Source : Type u} {SCM : Type v}

/-! ### §23.1 载体 -/

/-- **识别域**：来源 `e` 允许的 SCM 集合。 -/
abbrev IdentifiedSet (Source : Type u) (SCM : Type v) : Type _ := Source → Set SCM

/-- ⭐ **联合识别域**：所有来源识别域的**交**。

**「联合识别」的精确含义** = 同时满足全部来源的全部约束，**故取交**。 -/
def fused (B : IdentifiedSet Source SCM) : Set SCM :=
  {s | ∀ e, s ∈ B e}

/-- **单来源识别域**。 -/
def source (B : IdentifiedSet Source SCM) (e : Source) : Set SCM := B e

/-! ### §23.2 ⭐ 命题 15.1：单调性 -/

/-- ⭐ **命题 15.1（融合永不扩大识别域）**。

$$\mathrm{fused}\,B \subseteq B\,e \quad (\forall e)$$

**⟹ 这是「数据融合无害」的集合论部分**：
融合只会（弱）**收缩**识别域，不会反向放大。 -/
theorem fused_subset_source (B : IdentifiedSet Source SCM) (e : Source) :
    fused B ⊆ source B e :=
  fun _ hs => hs e

/-! ### §23.3 ⭐⭐ 命题 15.2：零增益 -/

/-- ⭐⭐ **命题 15.2（来源全同 ⟹ 融合零增益）**。

**陈述**：若所有来源诱导**同一**识别域 `S`，则 $\mathrm{fused}\,B = S$。

**⟹ 即**：**「把同一数据复制多份」不产生任何鉴别力。**

**⭐ 这是本节最重要的结论** ——
**增益必须来自来源之间的**差异**，而非来源的**数量**。** -/
theorem fusion_no_gain_of_common (B : IdentifiedSet Source SCM) (S : Set SCM)
    (hne : Nonempty Source) (h : ∀ e, B e = S) :
    fused B = S := by
  obtain ⟨e₀⟩ := hne
  ext s
  constructor
  · intro hs
    rw [← h e₀]
    exact hs e₀
  · intro hs e
    rw [h e]
    exact hs

/-! ### §23.4 ⭐ 命题 15.3：单点刻画 -/

/-- ⭐ **命题 15.3（单点刻画）**。

$$\bigl(\exists s_0,\ \mathrm{fused}\,B = \{s_0\}\bigr) \iff (\mathrm{fused}\,B).\mathrm{Subsingleton}
  \quad(\text{给定非空})$$

**⟹ 即**：**「联合识别是否成功」的精确判据** ——
数据融合能给出**唯一点识别** $\iff$ **所有来源约束的公共解唯一**。 -/
theorem fusion_single_iff (B : IdentifiedSet Source SCM) (hne : (fused B).Nonempty) :
    (∃ s₀, fused B = {s₀}) ↔ (fused B).Subsingleton := by
  constructor
  · rintro ⟨s₀, hs₀⟩
    rw [hs₀]
    exact Set.subsingleton_singleton
  · intro hsub
    obtain ⟨s₀, hs₀⟩ := hne
    exact ⟨s₀, hsub.eq_singleton_of_mem hs₀⟩

/-! ### §23.5 ⭐ 命题 15.4：单来源充分则融合冗余 -/

/-- ⭐ **命题 15.4（单来源充分则融合冗余）**。

**陈述**：若某来源 `e₀` 的识别域已**单点**，则融合**不可能**比它更小（至多相等）。

**⟹ 即**：**「再融合其它来源」对该参数不带来任何新信息。** -/
theorem single_source_sufficient_of_subsingleton
    (B : IdentifiedSet Source SCM) (e₀ : Source)
    (hsub : (source B e₀).Subsingleton) :
    (fused B).Subsingleton :=
  hsub.anti (fused_subset_source B e₀)

/-! ### §23.6 ⭐⭐ 命题 15.5：严格增益的必要条件 -/

/-- ⭐⭐ **命题 15.5（严格增益的必要条件）**。

**陈述**：若融合**严格**收缩了某来源的识别域，
则**所有**来源的识别域都**非单点**。

**⟹ 即**：**严格增益只可能发生在「没有任何单一来源已单值」时。**

**⚠ 这是「融合有用」的**必要条件**（非充分）。** -/
theorem strict_gain_implies_no_single_source
    (B : IdentifiedSet Source SCM) (e₀ : Source)
    (hstrict : fused B ⊂ source B e₀)
    (hne : (fused B).Nonempty) :
    ¬ (source B e₀).Subsingleton := by
  intro hsub
  have hle : fused B ⊆ source B e₀ := fused_subset_source B e₀
  obtain ⟨s₀, hs₀⟩ := hne
  have hmem : s₀ ∈ source B e₀ := hle hs₀
  have hsrc : source B e₀ = {s₀} := hsub.eq_singleton_of_mem hmem
  have hfus : fused B = {s₀} := (hsub.anti hle).eq_singleton_of_mem hs₀
  rw [hfus, hsrc] at hstrict
  exact (Set.ssubset_iff_subset_ne.mp hstrict).2 rfl

/-! ### §23.7 ⭐ 非空性检验（说明框架不空转） -/

/-- **命题 15.6（互不相容 ⟹ 交为空）**：两来源约束**冲突**时，联合识别**失败**。

**构造**：`Source := Bool`，`SCM := Bool`，
`B true := {true}`，`B false := {false}` —— 交为 $\varnothing$。 -/
theorem incompatible_sources_empty :
    ∃ (B : IdentifiedSet Bool Bool), fused B = ∅ := by
  refine ⟨fun e => if e then {true} else {false}, ?_⟩
  ext s
  constructor
  · intro hs
    have h1 : s = true := by
      have := hs true
      simpa using this
    have h2 : s = false := by
      have := hs false
      simpa using this
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro hs
    exact absurd hs (Set.notMem_empty s)

/-- **命题 15.7（相容且互补 ⟹ 交为单点）**：联合识别**成功**。

**构造**：`Source := Bool`，`SCM := Bool × Bool`，
`B true := {(true,true), (true,false)}`（第一坐标固定），
`B false := {(true,true), (false,true)}`（第二坐标固定）——
交为 `{(true,true)}`。 -/
theorem complementary_sources_singleton :
    ∃ (B : IdentifiedSet Bool (Bool × Bool)), fused B = {(true, true)} := by
  refine ⟨fun e => if e then {(true, true), (true, false)} else {(true, true), (false, true)}, ?_⟩
  ext ⟨a, b⟩
  constructor
  · intro hs
    have h1 := hs true
    have h2 := hs false
    simp only [if_true] at h1
    simp only [Bool.false_eq_true, if_false] at h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2 ⊢
    tauto
  · intro hs
    rw [Set.mem_singleton_iff] at hs
    obtain ⟨rfl, rfl⟩ := hs
    intro e
    by_cases he : e <;> simp [he]

end Fusion

end Fate
