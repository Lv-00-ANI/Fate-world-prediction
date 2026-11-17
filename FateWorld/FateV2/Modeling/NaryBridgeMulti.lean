import FateWorld.FateV2.Modeling.NaryBridge
import FateWorld.FateV2.Modeling.NaryAlgebra
/-!
  # Modeling · NaryBridgeMulti

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryBridgeMulti.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryBridge, NaryAlgebra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNBridgeMulti ⭐⭐⭐⭐⭐ **N 元桥：多坐标的乘积形式**（**第 189 轮**）

  ## 填补缺口 2b（N 元桥的**最后一步**）

  ## 目标

  $$\kappa_a\Big(\bigcap_i t_i\Big) \cdot M^{|\iota|-1}
    = \prod_i \kappa_a(t_i) \cdot M^{|\iota|-1}$$

  其中 $t_i = \mathrm{coordSet}\ i\ S_i$，$M = \mu.\mathrm{real}(\mathrm{fiberN}\ a_2)$。

  ## ⭐ 证明思路

  1. `⋂ i, coordSet i S_i = {w | ∀ i, w.1 i ∈ S_i}`（`iInter_coordSet`）
  2. 用 `NaryAlgebra.condIndepN_sum_factorize`：
     `(∑ xs∈S, p) * M^(n-1) = ∏ i, (∑ a∈S_i, marg i a)`
  3. 用 `NaryFinal.bridgeKernelValue_mul_fiberN` 把核值化成 `μ(t ∩ fiberN)/μ(fiberN)`
  4. 消去分母

  ## ⚠ 语义前提

  **必须有 `hp : ∀ w, 0 ≤ p w`**（`weightedCountN` 的 `ofReal` 截断负值）。
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section InterCoordSet

variable {ι : Type*}
variable {fam : ι → Type*}
variable {γ : Type*}

/-- ⭐⭐ **多个 `coordSet` 的交 = 「所有坐标各落在各自集合中」**。 -/
theorem iInter_coordSet (S : ∀ i, Set (fam i)) :
    (⋂ i, coordSet i (S i) : Set ((∀ j, fam j) × γ)) = {w | ∀ i, w.1 i ∈ S i} := by
  ext w
  simp [coordSet]

end InterCoordSet

end FateV2.Modeling.GenN
