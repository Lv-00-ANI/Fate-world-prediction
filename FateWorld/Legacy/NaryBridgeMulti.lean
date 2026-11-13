import FateWorld.Legacy.NaryBridge
import FateWorld.Legacy.NaryAlgebra

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

namespace Fate.GenN

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

end Fate.GenN
