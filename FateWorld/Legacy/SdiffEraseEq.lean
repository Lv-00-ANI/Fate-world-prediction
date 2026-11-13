import FateWorld.Legacy.MassSdiffConst
import FateWorld.Legacy.SinkPeelDiagnosis

/-! ===========================================================================
  §0  `univ \ (T \ {s}) = {s} ∪ (univ \ T)` —— `sink_peel` 的补集分解

  ## 背景

  `sink_peel`（`Fate/Strategy9SinkPeelNorm.lean`）在 `T = {s}` 时有反例
  （`Fate/SinkPeelCounterexample.lean`）。

  其修正需要理解 `T \ {s}` 与 `T` 的补集关系：

  $$univ \setminus (T \setminus \{s\}) = \{s\} \cup (univ \setminus T)$$

  ⟹ `bar (T\{s})` 的被积函数是 `f_s · ∏_{v ∉ T} f_v`，
  比 `bar T` 的被积函数多一个 `f_s` 因子。

  ## 本文件

  `sdiff_erase_eq`：上述集合恒等式。

  ## 诚实边界

  这只是集合层面的分解。要把 `f_s` 从 `mass` 中提出来，还需要
  「`f_s` 只读 `s`」的额外前提（见 `Fate/SinkPeelDiagnosis.lean` 的诊断）。
  =========================================================================== -/

namespace Fate.C14
open Finset Fate Fate.DAGFactorization
open Causalean.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- 手工两方向，不用 simp only 过度化简
theorem sdiff_erase_eq {T : Finset V} {s : V} (hsT : s ∈ T) :
    (univ \ (T.erase s) : Finset V) = insert s (univ \ T) := by
  ext u
  constructor
  · intro hu
    have h1 : u ∈ (univ : Finset V) := Finset.mem_univ u
    have h2 : u ∉ T.erase s := (Finset.mem_sdiff.mp hu).2
    by_cases hus : u = s
    · exact Finset.mem_insert.mpr (Or.inl hus)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      exact Finset.mem_sdiff.mpr ⟨h1, fun hut => h2 (Finset.mem_erase.mpr ⟨hus, hut⟩)⟩
  · intro hu
    rcases Finset.mem_insert.mp hu with hus | hu'
    · subst hus
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hcon => ?_⟩
      exact (Finset.mem_erase.mp hcon).1 rfl
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun hcon => (Finset.mem_sdiff.mp hu').2 (Finset.mem_erase.mp hcon).2⟩

end Fate.C14
