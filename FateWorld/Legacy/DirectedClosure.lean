import FateWorld.Legacy.Implication

/-! ===========================================================================
  §18  ⭐⭐ **有向并的闭性失效**：FCA 闭包算子**非代数**

  **来源**：探针 `probes/_probe_directed.lean`（**不在构建内**）。
  本节取其**核心反例**正式化。

  ## 问题

  FCA 的闭包算子 $B \mapsto B''$ 是否**代数**（finitary）？
  即：**闭集族的**有向并**是否仍闭？**

  ## ⭐ 结论：**不成立**

  **反例背景**：
  $$G := \mathbb{N},\qquad M := \mathrm{Option}\,\mathbb{N},\qquad
    g \mathrel{I} m \iff \exists n,\ m = \mathrm{some}\,n \wedge n \le g$$

  **取有限初始段** $\mathrm{seg}\,n := \{\mathrm{some}\,k \mid k \le n\}$。

  ## ⭐⭐ 核心机制

  设 $U := \bigcup_n \mathrm{seg}\,n = \{\mathrm{some}\,k \mid k \in \mathbb{N}\}$。

  | 断言 | 理由 |
  |---|---|
  | $\mathrm{none} \notin U$ | $U$ 只含 $\mathrm{some}\,k$ |
  | $U' = \varnothing$ | 设 $g \in U'$，则 $g \mathrel{I} \mathrm{some}\,(g+1)$，但后者要求 $g+1 \le g$ —— **矛盾** |
  | 故 $U''$ = 全集 | 空集的上极是全空间 |
  | 故 $\mathrm{none} \in U''$ | 而 $\mathrm{none} \notin U$ |

  **⟹ 即**：$U'' \neq U$ —— **$U$ 不闭**，尽管它是闭集族的有向并。

  ## ⭐⭐ 深层意义

  **FCA 闭包算子非代数**：
  $\mathrm{none} \in U''$ 的见证需要**每个** $g$ 都参与，
  即**无穷多个**对象同时作见证；而任何单个 $\mathrm{seg}\,n$ 只提供**有限个**。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace DirectedClosure

open Fate.FormalCtx

/-- ⭐ **反例背景 $\mathbb{K}_c$**。

**⚠ 用 `abbrev` 而非 `def`** —— 使 `Kc.GFCA` 归约为 `ℕ`，
从而 `g + 1` 等算术可正常进行。 -/
abbrev Kc : FormalCtx where
  GFCA := ℕ
  MFCA := Option ℕ
  Irel := fun g m => ∃ n, m = some n ∧ n ≤ g

namespace Kc

/-- **有限初始段** $\mathrm{seg}\,n$。 -/
abbrev seg (n : ℕ) : Set Kc.MFCA := {m | ∃ k, k ≤ n ∧ m = some k}

/-- ⭐⭐ **有向并不闭**（核心反例）。

$$\left(\bigcup_n \mathrm{seg}\,n\right)'' \neq \bigcup_n \mathrm{seg}\,n$$ -/
theorem union_not_closed :
    (⋃ n, seg n) ≠ Kc.polarUp (Kc.polarDown (⋃ n, seg n)) := by
  intro heq
  have hnotmem : (none : Option ℕ) ∉ (⋃ n, seg n) := by
    intro hmem
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨k, _, hk⟩ := hn
    exact absurd hk (by simp)
  have hmem : (none : Option ℕ) ∈ Kc.polarUp (Kc.polarDown (⋃ n, seg n)) := by
    simp only [FormalCtx.polarUp, FormalCtx.polarDown, upperPolar, lowerPolar,
      Set.mem_setOf_eq]
    intro g hg
    have hb : (some (g + 1) : Option ℕ) ∈ (⋃ n, seg n) := by
      refine Set.mem_iUnion.mpr ⟨g + 1, ?_⟩
      exact ⟨g + 1, le_rfl, rfl⟩
    obtain ⟨k, hk_eq, hk_le⟩ := hg hb
    have hk : k = g + 1 := Option.some_inj.mp hk_eq.symm
    subst hk
    exact absurd hk_le (by omega)
  have : (none : Option ℕ) ∈ (⋃ n, seg n) := by
    rw [heq]; exact hmem
  exact hnotmem this

/-- ⭐ **每个 $\mathrm{seg}\,n$ 都是闭集**（为「有向并」提供前提）。 -/
theorem closed_seg (n : ℕ) : Kc.IsClosedAttr (seg n) := by
  show Kc.polarUp (Kc.polarDown (seg n)) = seg n
  ext m
  constructor
  · intro hm
    simp only [FormalCtx.polarUp, FormalCtx.polarDown, upperPolar, lowerPolar,
      Set.mem_setOf_eq] at hm
    have h1 : Kc.Irel n m := hm (fun {b} hb => by
      obtain ⟨k, hk, rfl⟩ := hb
      exact ⟨k, rfl, hk⟩)
    obtain ⟨k, hkm, hk_le⟩ := h1
    exact ⟨k, hk_le, hkm⟩
  · intro hm
    -- 扩张性：`seg n ⊆ (seg n)''`
    -- 需证：对任意 `g`，若 `g` 与 `seg n` 中每个属性相关，则 `g I m`
    -- 其中 `m ∈ seg n`（`hm` 给出）。取 `m = some k`，`k ≤ n`。
    -- `g I (some k')` 对所有 `k' ≤ n` 成立，特别取 `k' = k`，得 `k ≤ g`。
    simp only [FormalCtx.polarUp, FormalCtx.polarDown, upperPolar, lowerPolar,
      Set.mem_setOf_eq]
    intro g hg
    obtain ⟨k, hk_le, hk_eq⟩ := hm
    -- `hg (some k) ⟨k, hk_le, rfl⟩ : Kc.Irel g (some k)` 即 `∃ j, some k = some j ∧ j ≤ g`
    have hk_in : (some k : Option ℕ) ∈ seg n := ⟨k, hk_le, rfl⟩
    obtain ⟨j, hj_eq, hj_le⟩ := hg hk_in
    have hjk : j = k := Option.some_inj.mp hj_eq.symm
    rw [hjk] at hj_le
    exact ⟨k, hk_eq, hj_le⟩

/-- ⭐ **族 $\{\mathrm{seg}\,n\}_n$ 有向**。 -/
theorem directed_seg : Directed (· ⊆ ·) (fun n : ℕ => seg n) := by
  intro m n
  refine ⟨max m n, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k, le_trans hk (le_max_left m n), rfl⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k, le_trans hk (le_max_right m n), rfl⟩

/-- ⭐⭐ **主定理（合成）**：**FCA 的闭包算子非代数**。

**陈述**：存在**有向**的闭集族，其**并**不闭。 -/
theorem closureOp_not_algebraic :
    (∀ n : ℕ, Kc.IsClosedAttr (seg n)) ∧
      Directed (· ⊆ ·) (fun n : ℕ => seg n) ∧
      ¬ Kc.IsClosedAttr (⋃ n, seg n) :=
  ⟨closed_seg, directed_seg, fun h => union_not_closed h.symm⟩

end Kc

end DirectedClosure

end Fate
