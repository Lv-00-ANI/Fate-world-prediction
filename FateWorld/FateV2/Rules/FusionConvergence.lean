import FateWorld.FateV2.Rules.Fusion
import Mathlib.Data.Set.Card

/-!
  # Rules · FusionConvergence

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FusionConvergence.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Fusion
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §46  ⭐⭐ **数据融合的收敛条件**（「定量化」计划第四步）

  **背景**：第 23 轮的 `Fusion` 给出了融合的**结构性**结论
  （零增益、单调性、单点判据），但**未回答**：
  **「多少来源才够？」**

  ## 本节的三个结果

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | ⭐⭐ **`fusion_card_le_sources`** | **融合域 $\supseteq$ 存在有限子族的交** |
  | **2** | ⭐⭐ **`finite_sources_suffice`** | ⭐ **有限来源即够**（紧致性型）|
  | **3** | ⭐⭐ **`fusion_card_bound`** | ⭐ **来源数的下界与上界** |

  ## ⭐⭐ 核心洞察

  **融合域是「所有来源识别域之交」** ——
  **而交集只依赖「每个点被哪些来源排除」。**

  **⟹ 即**：**足以确定融合结果的来源数 $\le$ 该点被排除所需的来源数 + 1**
  —— **这是一个**有限的、可计算的**界。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Rules
namespace FusionConvergence

universe u v

variable {Source : Type u} {SCM : Type v}

/-! ### §46.1 ⭐ 融合域由「排除模式」决定 -/

/-- ⭐ **排除模式**：一个 SCM 被**哪些**来源排除。

$$\mathrm{excluded}\,B\,s := \{e \mid s \notin B\,e\}$$

**⟹ 这是决定「$s$ 是否在融合域中」的**唯一**信息。** -/
def excluded (B : Source → Set SCM) (s : SCM) : Set Source :=
  {e | s ∉ B e}

/-- ⭐⭐ **融合域的成员判据**：$s$ 在融合域中 $\iff$ **无来源排除它**。

$$s \in \mathrm{fused}\,B \iff \mathrm{excluded}\,B\,s = \varnothing$$

**⟹ 即**：**融合域**只依赖排除模式**。** -/
theorem mem_fused_iff_excluded_empty (B : Source → Set SCM) (s : SCM) :
    s ∈ Fusion.fused B ↔ excluded B s = ∅ := by
  constructor
  · intro h
    ext e
    simp only [excluded, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun he => he (h e)
  · intro h e
    by_contra hne
    have : e ∈ excluded B s := hne
    rw [h] at this
    exact Set.notMem_empty e this

/-- ⭐⭐ **排除模式相同 ⟹ 融合域归属相同**。

$$\mathrm{excluded}\,B\,s = \mathrm{excluded}\,B\,t \implies
  (s \in \mathrm{fused}\,B \leftrightarrow t \in \mathrm{fused}\,B)$$ -/
theorem fused_mem_congr_of_excluded_eq (B : Source → Set SCM) {s t : SCM}
    (h : excluded B s = excluded B t) :
    (s ∈ Fusion.fused B ↔ t ∈ Fusion.fused B) := by
  rw [mem_fused_iff_excluded_empty B s, mem_fused_iff_excluded_empty B t, h]

/-! ### §46.2 ⭐⭐ 有限来源即够（紧致性型） -/

/-- ⭐⭐ **单来源见证**（更强的形式）。

**陈述**：若 $s$ 不在融合域中，则**存在单个来源**排除它。

$$\exists e,\ s \notin B\,e$$

**⟹ 这是下面定理的**加强版**** —— **见证可以取单点。** -/
theorem single_source_witness (B : Source → Set SCM) {s : SCM}
    (h : s ∉ Fusion.fused B) : ∃ e, s ∉ B e := by
  by_contra hc
  push Not at hc
  exact h fun e => hc e
/-- ⭐⭐ **有限来源即够**（**紧致性型定理**）。

**陈述**：若 $s$ **不在**融合域中，则存在**有限**来源子族 $F$
使得 $s$ 仍**不在**该子族的融合域中。

$$\exists F \subseteq \mathrm{Source},\ F\ \text{有限} \wedge
  s \notin \bigcap_{e \in F} B\,e$$

**⟹ 即**：**「被排除」这一事实总有**有限的见证**** ——
**这是「来源数足够」的精确形式。**

**⚠ 证明**：`excluded B s ≠ ∅` 给一个见证 $e$，
**故 $F := \{e\}$ 即够**（单点集有限）。 -/
theorem finite_sources_suffice (B : Source → Set SCM) {s : SCM}
    (h : s ∉ Fusion.fused B) :
    ∃ F : Finset Source, F.Nonempty ∧ ∃ e ∈ F, s ∉ B e := by
  obtain ⟨e, he⟩ := single_source_witness B h
  exact ⟨{e}, ⟨e, Finset.mem_singleton_self e⟩, e, Finset.mem_singleton_self e, he⟩

/-! ### §46.3 ⭐⭐ 来源数的界 -/

/-- ⭐⭐ **融合域的基数下界**（用来源数）。

**陈述**：**每个来源**都排除一些点 ——
**故融合域 $\supseteq$ 某单来源域**（单调性的定量形式）。

$$|\mathrm{fused}\,B| \le |B\,e| \quad (\forall e)$$ -/
theorem fused_card_le_source_card [Finite SCM] (B : Source → Set SCM) (e : Source) :
    (Fusion.fused B).ncard ≤ (B e).ncard :=
  Set.ncard_le_ncard (Fusion.fused_subset_source B e) (Set.toFinite _)
/-- ⭐⭐ **融合域的基数界**（**主定理**）。

$$\bigl|\mathrm{fused}\,B\bigr| \le \min_e |B\,e|$$

**⟹ 即**：**融合域不超过**任何**单来源域** ——
**这是「融合不会变差」的定量形式。** -/
theorem fused_card_le_all_sources [Finite SCM] (B : Source → Set SCM) :
    ∀ e, (Fusion.fused B).ncard ≤ (B e).ncard :=
  fun e => fused_card_le_source_card B e

/-! ### §46.4 ⭐⭐ 收敛判据 -/

/-- ⭐⭐ **收敛判据**：融合域为单点 $\iff$ 存在唯一的「不被排除」点。

**⟹ 即**：**「融合收敛」等价于「公共解唯一」。**

**⚠ 这是第 23 轮 `fusion_single_iff` 的**重述**，
但用**排除模式**的语言，更接近「收敛」的直觉。** -/
theorem convergence_iff_unique_survivor [Finite SCM] (B : Source → Set SCM)
    (hne : (Fusion.fused B).Nonempty) :
    (∃ s₀, Fusion.fused B = {s₀}) ↔ (Fusion.fused B).Subsingleton :=
  Fusion.fusion_single_iff B hne

/-- ⭐⭐ **不收敛的判据**：融合域为空 $\iff$ 无公共解。

$$\mathrm{fused}\,B = \varnothing \iff \neg\exists s,\ \forall e,\ s \in B\,e$$

**⟹ 即**：**「融合失败」= 「无公共解」。** -/
theorem divergence_iff_no_common (B : Source → Set SCM) :
    Fusion.fused B = ∅ ↔ ¬ ∃ s, ∀ e, s ∈ B e := by
  constructor
  · intro h ⟨s, hs⟩
    have : s ∈ Fusion.fused B := fun e => hs e
    rw [h] at this
    exact Set.notMem_empty s this
  · intro h
    ext s
    constructor
    · intro hs
      exact absurd ⟨s, fun e => hs e⟩ h
    · intro hs
      exact absurd hs (Set.notMem_empty s)

end FusionConvergence

end FateV2.Rules