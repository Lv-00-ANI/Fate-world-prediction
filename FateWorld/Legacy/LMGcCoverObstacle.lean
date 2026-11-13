import FateWorld.Legacy.LMGcCondIndepEquiv
import FateWorld.Legacy.BridgeDSepGeneral

/-! ===========================================================================
  §0  ⚠ `LMGc` 与现有桥之间的**障碍**：cover 条件不成立

  ## 已证

  `LMGc p G ↔ ∀ v, CondIndep p {v} (nd v) (pa v)`
  （`Fate/LMGcCondIndepEquiv.lean`）

  ## 现有桥

  `Fate/BridgeDSepGeneral.condIndep_of_factorizes_dSep_general`：
  ```lean
  (hfac : Factorizes p G) (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ) :
      CondIndep p X Y Z
  ```

  ## ⚠ 障碍

  取 `X = {v}`、`Y = nd v`、`Z = pa v`：

  `nd v = {w | ¬isAncestor v w ∧ w ≠ v}` ⟹ `v ∉ nd v`
  ⟹ `{v} ∪ nd v = univ \\ descendants(v)`
  ⟹ `{v} ∪ nd v ∪ pa v = univ` 等价于 **`descendants(v) ⊆ pa v`**

  **⟹ 只有 `v` 的所有后代都是它的直接父节点时才成立——一般不可能。**

  ## 结论

  **`LMGc` 不能用现有桥直接推出**：
  桥要求的 `hcover`，在 `LMGc` 的场景下几乎总是不满足。

  ⟹ 需要**不需要 cover 的 `CondIndep` 版本**，或
     直接针对 `LMGc` 的四个 `mass` 做计算。

  ## 下一步方向

  1. 检查 `CondIndep` 在 `X ∪ Y ∪ Z ⊊ univ` 时是否仍有意义
     （`mass` 只依赖 `X ∪ Y ∪ Z` 的话，可以「投影」到该子集上）
  2. 或者直接在 `Factorizes` + `dSep` 下对 `LMGc` 的四个 `mass` 计算

  ## 诚实边界

  本文件只做障碍分析，不含新定理。
  =========================================================================== -/
