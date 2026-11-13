import FateWorld.Legacy.MultSUnify
import FateWorld.Legacy.CondIndepGeneralNZ

/-! ===========================================================================
  §0  两条独立路线的架构说明（**不是定理，是文档登记**）

  ## 背景

  本会话发现「mass S 不是单点」这一系统性盲点，并找到了两条处理路线：

  ### 路线 A：`multS` 因子（`Fate/TowerExactLaw.lean`）
  ```lean
  multS S x = ∑ w, if (∀ u ∈ S, w u = x u) then 1 else 0 = |α|^(|V|-|S|)
  mass S (mass T p) x = multS S x * mass T p x      （T ⊆ S）
  ```
  **⟹ 精确塔定律**：塔性质差一个 `multS` 因子。

  ### 路线 B：因子提取 + 配平（`Fate/CondIndepGeneralNZ.lean`）
  ```lean
  condIndep_general : HyperFactorizes → ReadSet → Split → 三不交 → A = univ →
      CondIndep p X Y Z
  ```
  用 `mass_mul`（只读因子提取）+ `mass_prod_cover`（乘积覆盖）+ `mass_sep_Z`（分离）
  + `mass_univ`（`mass univ = p`）完成四个 `mass` 的配平。
  **不用 `multS`。**

  ## 两条路线的关系

  * **独立**：路线 B 不依赖路线 A，反之亦然。
  * **互补**：路线 A 处理「塔」（`mass ∘ mass`），路线 B 处理「四 mass 配平」。
  * **都正确**：路线 A 的定理在 `TowerExactLaw` 里零 sorry；
    路线 B 的定理在 `CondIndepGeneralNZ` 里零 sorry。

  ## 本会话的补充

  * `mass_self_insert`（`MassInsertCorrected.lean`）= 路线 A 的一种表述
  * `multS_eq_card_pow`（`MultSUnify.lean`）连接 `multS` 与 `|α|` 幂
  * `card_sub_fib'`（`SubFibCard.lean`）提供子类型版本的基数

  ## 诚实边界

  本文件**不含定理**，只是登记本会话对两条路线的理解。
  =========================================================================== -/
