import FateWorld.FateV2.Predict.FactorizesToHyper
/-!
  # Predict · TailTailCollapse

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailTailCollapse.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorizesToHyper
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⚠ 重要发现：主定理 D 的 `hTail` 前提蕴含「无尾块」

  ## 事实

  `Fate/TailBlockBridge.lean` 的 `condIndep_tail_block` 需要：
  ```
  hTail : ∀ v, v ∉ X ∪ Y ∪ Z → readSetOf G v ⊆ Z
  ```

  但 `readSetOf G v = insert v (G.parents v)`，**包含 `v` 本身**。
  而 `Z ⊆ X ∪ Y ∪ Z`，所以 `v ∉ A ⟹ v ∉ Z`。

  **⟹ `readSetOf G v ⊆ Z` 要求 `v ∈ Z`，与 `v ∉ Z` 矛盾。**

  **⟹ 因此 `hTail` 只在 `outSet A = ∅`（即 `A = univ`）时可能成立。**

  **⟹ 主定理 D 的 `hTail` 前提与「无尾块」等价，没有真正处理有尾块情形。**

  ## 为什么之前的证明还能过？

  因为 `hTail` 是**假设**。证明在假设下成立，但该假设本身把情形限制回了无尾块。
  这也解释了为什么 `outSet A` 在 `mass_extract_out` 里从未真正起作用。

  ## 本文件的定理

  `hTail_implies_univ`：`Z ⊆ A` 且 `hTail` 成立 ⟹ `A = univ`。
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open FateV2.Modeling

open Finset FateV2.Error

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `v ∉ A` 且 `Z ⊆ A` ⟹ `v ∉ Z`。 -/
theorem notMem_of_notMem_of_subset {A Z : Finset V} (hZA : Z ⊆ A) {v : V}
    (hv : v ∉ A) : v ∉ Z :=
  fun h => hv (hZA h)

/-- ⚠ **`hTail` 蕴含 `A = univ`**（尾块为空）。

**⟹ 主定理 D 的 `hTail` 前提等价于「无尾块」**，没有真正处理有尾块的情形。 -/
theorem hTail_implies_univ {G : FateV2.Modeling.Graph.DAG V} {A Z : Finset V}
    (hZA : Z ⊆ A)
    (hTail : ∀ v, v ∉ A → FateV2.Predict.FactorizesToHyper.readSetOf G v ⊆ Z) :
    A = Finset.univ := by
  by_contra hne
  have ⟨v, hv⟩ : ∃ v, v ∉ A := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_of_forall h)
  have hsub := hTail v hv
  have hmem : v ∈ FateV2.Predict.FactorizesToHyper.readSetOf G v := by
    unfold FateV2.Predict.FactorizesToHyper.readSetOf
    simp
  exact hv (hZA (hsub hmem))

end FateV2.Predict.GraphToProbView7
