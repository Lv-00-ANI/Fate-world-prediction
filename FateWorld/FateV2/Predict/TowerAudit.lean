import FateWorld.FateV2.Predict.DAGFactorizationGeneral
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.MarkovEquivalence
/-!
  # Predict · TowerAudit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TowerAudit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorizationGeneral, DAGFactorization, MarkovEquivalence
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Predict.TowerAudit` —— **塔性质诊断的独立复核 + 文献标准做法**

  ## 0 本文目的

  对主控的诊断做**独立机检复核**（不采信），并登记文献标准做法
  （Pearl《Causality》2nd ed. Thm 1.2.7；Koller & Friedman Ch. 3）的诊断结论。

  ## 1 复核结论一览（每条都在本文件机检）

  | 编号 | 事实 | 状态 |
  |---|---|---|
  | **A1** | `mass` 定义 = 纤维求和（固定 `S`、对其余坐标同时求和）| ✅ 见 `DAGFactorization.lean:237`，逐字一致 |
  | **A2** | 塔反例 `tower_counter_lhs/rhs` 数值成立（`1 ≠ 0`）| ✅ `tower_property_false` |
  | **A3** | ⚠ **主控诊断需修正**：`mass` 是**非归一化纤维和**，故连「正确方向」的塔 `mass S (mass T p) = mass S p`（`S ⊆ T`）**也为假** | ✅ 本文 `mass_idempotent_fails` |
  | **A4** | `mass (univ \ {v}) p x = ∑_a p (unpin v x a)`（`V∖{v}` 上的边缘 = 对 `v` 求和）| ✅ 本文 `mass_compl_singleton_eq` |

  ## 2 关键修正（对主控诊断）

  主控 §1.3 说「正确塔性质是 `mass (S ∪ T) p = mass T (mass S p)`（`S ⊆ T`）」。
  **这一条在本仓库的 `mass` 口径下也为假**：因为 `mass` **不归一化**，
  嵌套 `mass ∘ mass` 会把纤维大小乘进去。
  `mass {false} (mass {false} ptri)` 在 `x false = true` 处等于 **2**，
  而 `mass {false} ptri` 在该处等于 **1**（见 `mass_idempotent_fails`）。
  故「塔性质为假」的**根因不是 S/T 的包含关系**，
  而是 **`mass` 的语义是「纤维和」而非「概率边缘 / 条件概率」**。

  ## 3 文献标准做法（Pearl 1.2.7 / KF Ch.3）—— **不需要边缘塔性质**

  标准证明走 **拓扑序归纳**，**从不**用 `mass S (mass T p)` 这种嵌套。

  Pearl Thm 1.2.7（有序 Markov / 因子分解 ⟺ 局部 Markov）的骨架：

  * **(i) 拓扑序**：取 `v₁,…,vₙ` 使父节点先于子节点。
  * **(ii) 链式法则**（概率的、**归一化**的）：
    `p(x₁,…,xₙ) = ∏ᵢ p(xᵢ | x₁,…,xᵢ₋₁)`。
    这一步用的是**条件概率** `p(·|·) := p(·,·)/p(·)`，**不是** `mass`。
  * **(iii) 父集判据**：`p(xᵢ | x₁,…,xᵢ₋₁) = p(xᵢ | x_{pa(i)})`
    当且仅当 `Xᵢ ⊥ {X₁,…,Xᵢ₋₁}∖pa(i) | X_{pa(i)}`（**有序**局部 Markov）。
  * **(iv) 于是** `p = ∏ᵢ p(xᵢ|x_{pa(i)})`，即因子分解。

  反向（局部 ⟹ 全局）用 **Bayes-ball / d-分离的四条引理**逐路径归纳，
  **全程在概率（归一化）层面做除法**，不出现 `mass` 塔。

  **⭐ 结论**：标准做法**不需要**、也**不能**用 `mass S (mass T p)`；
  它需要的是 **(a) 归一化条件概率 `p(·|·)` 的链式法则**，
  **(b) 拓扑序归纳**。这正是路线甲（`condMass`）+ 路线乙（拓扑序）的合成，
  **而非**试图修补 `mass` 的塔。

  ## 4 对三条路线的裁定（文献视角）

  * **路线甲（`condMass`）**：**文献标准做法**。但必须(1)显式归一化除以 `mass S p x`
    （需 `mass S p x ≠ 0`），(2)塔性质只在**条件概率**上成立：
    `p(y|x) = Σ_z p(y|z) p(z|x)`，这是**概率的**塔，输入输出都是**归一化**分布。
  * **路线乙（拓扑序 + 因子递归）**：**文献标准做法**，且**回避 `mass` 语义问题**。
    Pearl 1.2.7 / KF 3.2 的证明本质就是它。**推荐**。
  * **路线丙（`Marginal S p : (S→α)→ℝ`）**：与文献的「把边缘写成型别」一致
    （KF 用 `P(X_{pa})` 型），但改动面大；且在 Lean 里需 `S` 的子类型/等价类，
    成本高。

  ## 5 零 `sorry`

  `lake env lean Fate/TowerAudit.lean` 无输出。
  =========================================================================== -/

namespace FateV2.Predict.TowerAudit

open FateV2.Modeling

open Finset FateV2.Predict.DAGFactorization

/-! ===========================================================================
  §1 复核 A3：`mass` 非归一化 ⟹ 幂等失败（连「正确方向」的塔也假）
  =========================================================================== -/

/-- ⚠ **A3**：`mass {false} (mass {false} ptri)` 在 `x false = true` 处 `= 2`，
而 `mass {false} ptri` 在该处 `= 1`。

**⟹ 「`mass S (mass T p) = mass S p`（`S ⊆ T`）」为假**，
故主控 §1.3 的「正确塔性质」在本载体上也**不成立**。
根因：`mass` 是**非归一化纤维和**，嵌套会把纤维大小乘进去。 -/
theorem mass_idempotent_fails :
    mass ({(false : Bool)}) (fun w => mass ({(false : Bool)}) ptri w) (fun _ => true) = 2
    ∧ mass ({(false : Bool)}) ptri (fun _ => true) = 1 := by
  constructor
  · unfold mass
    rw [univ_boolFun]
    simp only [Finset.sum_insert (by decide : bTrue ∉ ({bId, bNot, bFalse} : Finset (Bool → Bool))),
      Finset.sum_insert (by decide : bId ∉ ({bNot, bFalse} : Finset (Bool → Bool))),
      Finset.sum_insert (by decide : bNot ∉ ({bFalse} : Finset (Bool → Bool))),
      Finset.sum_singleton]
    norm_num [ptri, bTrue, bId, bNot, bFalse]
  · unfold mass
    rw [univ_boolFun]
    simp only [Finset.sum_insert (by decide : bTrue ∉ ({bId, bNot, bFalse} : Finset (Bool → Bool))),
      Finset.sum_insert (by decide : bId ∉ ({bNot, bFalse} : Finset (Bool → Bool))),
      Finset.sum_insert (by decide : bNot ∉ ({bFalse} : Finset (Bool → Bool))),
      Finset.sum_singleton]
    norm_num [ptri, bTrue, bId, bNot, bFalse]

/-- ⚠ 幂等性失败的直接表述：`mass {false} ∘ mass {false}` 在多处 ≠ 自身。 -/
theorem mass_not_idempotent :
    mass ({(false : Bool)}) (fun w => mass ({(false : Bool)}) ptri w) (fun _ => true)
      ≠ mass ({(false : Bool)}) ptri (fun _ => true) := by
  rw [mass_idempotent_fails.1, mass_idempotent_fails.2]
  norm_num

/-! ===========================================================================
  §2 复核 A4：`V∖{v}` 上的 `mass` = 对 `v` 位求和（说明它是「边缘」不是「条件」）
  =========================================================================== -/

/-- ⭐ **A4**：`mass (univ \ {v}) p x = ∑_a p (unpin v x a)`。

即「固定除 `v` 外所有坐标」= 「对 `v` 求和」——**这是纯边缘**，
没有任何条件化的除法。标准做法要的是**条件概率**
`p(v | 其余) = p(全部) / p(除 v 外)`，本载体**没有**、也不该由 `mass` 提供。 -/
theorem mass_compl_singleton_eq {V : Type} [DecidableEq V] [Fintype V]
    {α : Type} [Fintype α] [DecidableEq α]
    (v : V) (p : (V → α) → ℝ) (x : V → α) :
    mass (Finset.univ \ {v}) p x = ∑ a : α, p (unpin v x a) := by
  have h1 : mass (Finset.univ \ {v} : Finset V) p x
      = ∑ a : α, mass (insert v (Finset.univ \ {v})) p (unpin v x a) :=
    (mass_insert_sum v (Finset.univ \ {v}) (by simp) p x).symm
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (insert v (Finset.univ \ {v}) : Finset V) = Finset.univ := by
    ext u; by_cases hu : u = v <;> simp [hu]
  rw [this, mass_univ]

/-! ===========================================================================
  §3 复核 A2：主控塔反例逐字重现（确认真伪）
  =========================================================================== -/

/-- **A2**：主控给出的塔反例仍是仓库既有的 `tower_property_false`（`1 ≠ 0`）。 -/
theorem tower_counterexample_reproduced :
    mass ({(true : Bool)}) (fun w => mass ({(false : Bool)}) ptri w) (fun _ => false)
      ≠ mass ({(true : Bool)} ∪ {(false : Bool)}) ptri (fun _ => false) :=
  tower_property_false

end FateV2.Predict.TowerAudit
