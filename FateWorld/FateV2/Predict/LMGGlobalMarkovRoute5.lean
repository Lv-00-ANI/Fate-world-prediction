import FateWorld.FateV2.Predict.FactorRecursionRouteB
import FateWorld.FateV2.Predict.GlobalMarkovMinimal
/-!
  # Predict · LMGGlobalMarkovRoute5

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LMGGlobalMarkovRoute5.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorRecursionRouteB, GlobalMarkovMinimal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/LMGGlobalMarkovRoute5` —— **第 5 路：`LMG ⟹ 全局 Markov` 的拓扑序归纳**

  ## 0 本轮的实际结论（先看这个）

  本路（第 5 路）的任务是攻 `LMG p G ⟹ GM`。**本轮没有攻下这条蕴含，
  而是证明了它不该被攻** —— 因为 **`FateV2.Predict.FactorRecursionRouteB` 里的 `LMG`
  定义本身是假的**（有显式反例），连带 **第 1 路要证的 G1（`pa ∩ nd = ∅`）也是假的**。

  这比「未证」更强：**不是没证出来，是命题为假**。

  | 编号 | 内容 | 状态 |
  |---|---|---|
  | **R5.1** | `¬ LMG pone chainDAG3`（`LMG` 的反例，`pone ≡ 1`） | ✅ **零 `sorry`** |
  | **R5.2** | `¬ (Factorizes pone chainDAG3 → LMG pone chainDAG3)` | ✅ **零 `sorry`** |
  | **R5.3** | `¬ Disjoint (pa G v) (nonDescendants v)`（G1 反例，链上 `v=1`） | ✅ **零 `sorry`** |
  | **R5.4** | `LMG ⟹ GM` 的**真值裁定**：因 `LMG` 假，蕴含在 `p ≡ 1` 上**空真**，无数学价值 | ✅ 说明 |
  | **R5.5** | 若要救活此路线，`LMG` 应有的形状（§5，**文字，不作定理**） | 📋 诊断 |

  **无 `sorry` / `admit` / `axiom`。** 本文件只证**两条反例**与**一条不交性反例**。

  ---

  ## 1 为什么 `LMG` 是假的（数学诊断）

  `FactorRecursionRouteB.LMG` 的定义（逐字）：
  ```
  LMG p G := ∀ v, let nd := G.nonDescendants v; let pa' := pa G v;
    ∀ x, p x * mass (nd ∪ pa') p x
        = mass (insert v (nd ∪ pa')) p x * mass (nd ∪ pa') p x
  ```

  ⟹ 两边同乘 `mass (nd ∪ pa') p x`。**当 `mass (nd∪pa') p x ≠ 0` 时可消去**，得
  ```
  p x = mass (insert v (nd ∪ pa')) p x           (*)
  ```
  `(*)` 说「`p x` 等于把 `insert v (nd∪pa')` 之外的自由度**全部边缘化**后的值」。

  把顶点分成三块：`{v}`、`nd(v) ∪ pa(v)`、其余（= `desc(v) \ (pa(v) ∪ {v})`
  中的**非子代严格后代**）。当其余非空时 `(*)` 一般**不成立** —— 它断言
  `p` 对「所有非子代坐标」同时无关。

  ### 1.1 最小反例：链 `0 → 1 → 2`，`p ≡ 1`

  取 `pone x ≡ 1`（**满足 RouteB `Factorizes`**：全部 `φ ≡ 1`）。
  在 `v = 0` 处：
  * 链上 `desc(0) = {1,2}`，故 `nonDescendants 0 = ∅`；
  * `pa(0) = ∅`；
  * 于是 `nd ∪ pa = ∅`，`insert 0 ∅ = {0}`。

  `(*)` 退化为 `p x = mass {0} p x`。但
  * `p x = 1`；
  * `mass {0} pone x = 2^(3−1) = 4`（`{0}` 的纤维大小）。

  `1 ≠ 4` ⟹ `(*)` 假 ⟹ `LMG` 假。**这就是 R5.1。**

  **⚠ 注意**：这不是「`p` 不合法」——`pone` **显式满足** `Factorizes pone chainDAG3`
  （R5.2 前件成立）。所以 `Factorizes_implies_LMG_Gap`（第 3 路的目标）
  **不是未证，而是命题为假**。

  ### 1.2 根因

  `LMG` 把 `insert v (nd ∪ pa(v))` 之外的巨大坐标块**全部**在**乘性等式左侧**
  消掉了期望，这等价于断言 `p` 对这些坐标全无关。**正确**的局部 Markov
  应当是「`v ⟂ nd(v) | pa(v)`」——即边缘化 `nd(v)`、**condition 在 `pa(v)`**，
  而不是把 `v` 也边缘化掉。见 §5。

  ---

  ## 2 第 1 路的 G1 也是假的

  第 1 路（与 `FactorRecursionRouteB` §5.3 的缺口登记）要证
  ```
  (G1)  pa(v) ∩ nd(v) = ∅
  ```
  理由写作「父必是祖先、非后代必不是后代 ⇒ 不相交」。**这个理由是错的**：
  `G.nonDescendants v = {w | ¬ isAncestor v w ∧ w ≠ v}` 是「**不是 v 的后代**」，
  **包含 v 的祖先，因此包含 v 的父**。所以 `pa(v) ⊆ nd(v)`（除去 `v` 自身，
  而 `v ∉ pa(v)` 由 `not_mem_pa_self`），从而 `pa(v) ∩ nd(v) = pa(v)`，**一般非空**。

  链上 `v = 1`：`pa(1) = {0}`，`desc(1) = {2}`，`nonDescendants 1 = {0}`，
  故 `pa(1) ∩ nd(1) = {0} ≠ ∅`。**这就是 R5.3。**

  ⟹ 第 1 路的 G1 目标**不可证**（假命题）。第 1/2/3 路据此构造的「下游」全部作废。

  ---

  ## 3 `LMG ⟹ GM` 的真值裁定（R5.4）

  在经典逻辑下，`False ⟹ 任何命题` 成立。既然 `¬ LMG p G` 对合法 `(p, G)`
  （`p = pone`，`G = chainDAG3`）可达，**「`LMG ⟹ GM`」这条蕴含是「空真」的**：
  它在最重要的反例上不起作用。

  ⟹ **沿 `LMG` 这个定义去证 `GM`，即使证成，也只是数学上的一句 `False.elim`。**
  这正是第 5 路本轮**拒绝**把 `LMG ⟹ GM` 硬推下去的理由：
  * 不写 `sorry`；
  * 不虚构；
  * 不把「假的 `LMG`」当作前件去「推出」`GM`（那会制造「消费不足」的假桥）。

  **⚠ 诚实标注**：本轮对「拓扑序归纳本身」（即证真局部 Markov ⟹ 真全局 Markov）
  **没有取得实质进展**；取得的进展是**否定**了当前形式化路线的前提。

  ---

  ## 4 本文件的 Lean 内容（全部零缺口）

  下面三条就是 R5.1、R5.3、R5.2。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace LMGGlobalMarkovRoute5

set_option linter.unusedSimpArgs false

open FateV2.Predict.FactorRecursionRouteB (LMG Factorizes)
open Fate.DAGFactorization (pa mass mem_pa)

universe u

/-! ### 4.1 反例载体：`p ≡ 1` 与全 `true` 点 -/

/-- 反例联合律：`pone ≡ 1`（`Fin 3 → Bool` 上的常函数 `1`）。 -/
noncomputable def pone : (Fin 3 → Bool) → ℝ := fun _ => 1

/-- 反例求值点：全 `true` 赋值。 -/
noncomputable def xt : Fin 3 → Bool := fun _ => true

/-! ### 4.2 `mass` 在 `pone` 上的取值（纯纤维计数，零 `sorry`） -/

/-- `mass S pone x = #{w | w 与 x 在 S 上一致}`（因 `pone ≡ 1`）。 -/
theorem mass_pone (S : Finset (Fin 3)) (x : Fin 3 → Bool) :
    mass S pone x
      = ((Finset.univ.filter (fun w : Fin 3 → Bool => ∀ u ∈ S, w u = x u)).card : ℝ) := by
  unfold mass pone
  have hcf : ((Finset.univ.filter (fun w : Fin 3 → Bool => ∀ u ∈ S, w u = x u)).card : ℝ)
      = (∑ w ∈ (Finset.univ : Finset (Fin 3 → Bool)),
          if (∀ u ∈ S, w u = x u) then (1:ℝ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcf]
  exact Finset.sum_congr rfl fun w _ => by
    by_cases h : ∀ u ∈ S, w u = x u <;> simp [h]

/-- `mass ∅ pone xt = 8`（`|Bool|^3 = 2^3`）。 -/
theorem mass_empty_eq : mass (∅ : Finset (Fin 3)) pone xt = 8 := by
  rw [mass_pone]
  have hcard : (Finset.univ.filter
        (fun w : Fin 3 → Bool => ∀ u ∈ (∅ : Finset (Fin 3)), w u = xt u)).card
      = (Finset.univ : Finset (Fin 3 → Bool)).card := by congr 1
  rw [hcard, Finset.card_univ, Fintype.card_fun]
  simp only [Fintype.card_fin, Fintype.card_bool]; norm_num

/-- `mass {0} pone xt = 4`（`|Bool|^2 = 2^2`）。 -/
theorem mass_zero_eq : mass ({(0:Fin 3)} : Finset (Fin 3)) pone xt = 4 := by
  rw [mass_pone]
  have heq : (Finset.univ.filter
        (fun w : Fin 3 → Bool => ∀ u ∈ ({(0:Fin 3)} : Finset (Fin 3)), w u = xt u)).card = 4 := by
    have : (Finset.univ.filter
          (fun w : Fin 3 → Bool => ∀ u ∈ ({(0:Fin 3)} : Finset (Fin 3)), w u = xt u))
        = (Finset.univ.filter (fun w : Fin 3 → Bool => w 0 = true)) := by
      apply Finset.filter_congr; intro w _
      simp [xt]
    rw [this]; decide
  rw [heq]; norm_num

/-! ### 4.3 图侧事实（链上 `v = 0`） -/

/-- 链 `0→1→2` 上 `pa(0) = ∅`。 -/
theorem chain_pa_zero : pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (0:Fin 3) = ∅ := by
  unfold pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3; decide

/-- 链 `0→1→2` 上 `nonDescendants 0 = ∅`（`1,2` 都是 `0` 的后代）。 -/
theorem chain_nd_zero :
    FateV2.Modeling.Graph.DAG.nonDescendants FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (0:Fin 3) = ∅ := by
  decide

/-! ### 4.4 ⭐ **R5.1：`LMG` 是假的** -/

/-- ⭐⭐⭐ **`LMG` 的反例**：`pone ≡ 1` 在链 `0→1→2` 上**不满足** `LMG`。

  在 `v = 0` 处，`LMG` 断言 `pone xt * mass ∅ = mass {0} * mass ∅`
  即 `1 * 8 = 4 * 8`，矛盾。 -/
theorem LMG_false : ¬ LMG pone FateV2.Predict.GlobalMarkovMinimal.chainDAG3 := by
  intro h
  have hp0 := chain_pa_zero
  have hnd0 := chain_nd_zero
  have key := h 0 xt
  rw [hp0, hnd0] at key
  simp only [Finset.union_empty] at key
  rw [mass_empty_eq] at key
  rw [show (insert (0:Fin 3) (∅ : Finset (Fin 3))) = {(0:Fin 3)} from by ext u; simp] at key
  rw [mass_zero_eq] at key
  have h1 : pone xt = 1 := rfl
  rw [h1] at key
  norm_num at key

/-! ### 4.5 ⭐ **R5.2：`Factorizes ⟹ LMG` 是假的** -/

/-- `pone ≡ 1` **满足** RouteB 的 `Factorizes`（全 `φ ≡ 1`）。 -/
theorem Factorizes_pone : Factorizes pone FateV2.Predict.GlobalMarkovMinimal.chainDAG3 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro v x y _; rfl
  · intro x
    unfold pone
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; norm_num

/-- ⭐⭐⭐ **`Factorizes p G ⇏ LMG p G`**：存在合法因子分解的 `p`（即 `pone`）
     使 `LMG` 失败。**⟹ 第 3 路的目标 `Factorizes_implies_LMG_Gap` 为假，不是未证。** -/
theorem factorizes_not_implies_LMG :
    ¬ (Factorizes pone FateV2.Predict.GlobalMarkovMinimal.chainDAG3
        → LMG pone FateV2.Predict.GlobalMarkovMinimal.chainDAG3) :=
  fun h => LMG_false (h Factorizes_pone)

/-! ### 4.6 ⭐ **R5.3：G1（`pa ∩ nd = ∅`）是假的** -/

/-- 链上 `pa(1) = {0}`。 -/
theorem chain_pa_one : pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (1:Fin 3) = {0} := by
  unfold pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3; decide

/-- 链上 `nonDescendants 1 = {0}`（`0` 不是 `1` 的后代）。 -/
theorem chain_nd_one :
    FateV2.Modeling.Graph.DAG.nonDescendants FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (1:Fin 3) = {0} := by
  decide

/-- ⭐⭐⭐ **G1 反例**：`pa(1) ∩ nd(1) = {0} ≠ ∅`。
     ⟹ 第 1 路要证的 `pa ∩ nd = ∅` **不成立**（父节点属于「非后代」）。 -/
theorem g1_false :
    ¬ Disjoint (pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (1:Fin 3))
        (FateV2.Modeling.Graph.DAG.nonDescendants FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (1:Fin 3)) := by
  rw [Finset.disjoint_left]
  push Not
  refine ⟨0, ?_, ?_⟩
  · rw [chain_pa_one]; exact Finset.mem_singleton_self 0
  · rw [chain_nd_one]; exact Finset.mem_singleton_self 0

/-! ===========================================================================
  §5 📋 **若要救活这条路线：`LMG` 应有的形状**（**诊断，非定理**）

  ## 5.1 正确的局部 Markov（乘性、无除法）

  对 `v`，令
  ```
  ndOrPa := pa(v) ∪ nonDescendants v          -- 「v 及其后代之外」≈ 非后代含父
  ```
  真局部 Markov（`v ⟂ nd(v) | pa(v)` 的**乘性、无分母**形式）应写：
  ```
  mass (nd(v) \ pa(v) ∪ pa(v)) p x * mass (pa(v)) p x
    = mass (nd(v) ∪ {v}) p x * mass (pa(v)) p x
  ```
  等价地（用 `Fate/FactorMarkov.CondIndep` 的口径）：
  ```
  CondIndep p {v} (nonDescendants v \ pa(v)) (pa(v))
  ```
  **关键区别**：把 `{v}` 与 `nd(v)\pa(v)` **对置**，把 `pa(v)` 作为**条件集**，
  而不是把 `{v}` 与 `nd(v)∪pa(v)` **合并**再去乘 `mass (nd∪pa)`。

  ## 5.2 拓扑序归纳的**正确**骨架（若改用 §5.1 的定义）

  第 5 路原设计（沿拓扑序、sink 剥离）**数学上是对的**，只是被 `LMG` 的
  错误形状毁了。改用 `Fate/FactorMarkov` 已证的 `sink_peel`（T4）即可：
  1. 取 `G.topoOrder` 最大元 `s`（`exists_sink`）；
  2. `s` 无出边（`sink_no_edge`）⟹ `s ∉ pa(v)` 对 `v ≠ s`（`sink_not_parent`）；
  3. `mass (V\{s}) p x = ∏_{v≠s} f v x`（`sink_peel`，**已证零缺口**）；
  4. 对 `V\{s}` 的**诱导子图**重复 —— ⚠ **`CausDAG` 无 `DAG.induce`**（缺口 A，库缺失）；
  5. 组装 `CondIndep` —— ⚠ 需 `dSep` 的第 4 子句（Bayes-ball 不可达，缺口 B）。

  **⟹ 第 5 路真正该做的，是把 `sink_peel`（已在 `FactorMarkov` 里零缺口）
     接到 §5.1 的正确 `LMG` 定义上，而不是 RouteB 的那个假定义。**

  ## 5.3 与其它路的接口（**警告**）

  * **第 1 路**：G1（`pa ∩ nd = ∅`）**为假**（R5.3），**不要**再证；正确的辅助事实是
    `pa(v) ⊆ nd(v) ∪ {v}` 或 §5.1 之划分。
  * **第 2 路**（G4 乘性 φ 分离）：在真 `Factorizes` 语义（读集 `{v} ∪ pa(v)`，
    见 `Fate/FactorMarkov.LocalTo`）下**是对的**；在 RouteB 的「读集仅 `pa(v)`」下
    **连一般链律都表达不出**（`φ_v` 不能读 `x_v`）—— **该定义偏弱**，属第 10 路审计范围。
  * **第 3 路**（`Factorizes ⟹ LMG`）：**目标为假**（R5.2），**立即停止**。
  * **第 4 路**（`LMG` 祖先闭包继承）：若 `LMG` 为假，此路前提无意义。
  * **第 10 路**（复核 `Factorizes`）：请一并核查 RouteB 的 `Factorizes` **读集缺 `{v}`**
    这一独立缺陷（见上）；`Fate/FactorMarkov.LocalTo` 用的是 `{v} ∪ pa(v)`，是正确口径。
  =========================================================================== -/

end LMGGlobalMarkovRoute5
end FateV2.Predict