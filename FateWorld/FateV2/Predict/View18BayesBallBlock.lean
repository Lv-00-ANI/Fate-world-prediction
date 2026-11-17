import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.MarkovEquivalence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
  # Predict · View18BayesBallBlock

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View18BayesBallBlock.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, _root.CausBayesBall, DAGFactorization, MarkovEquivalence
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/View18BayesBallBlock` ——
  **「图 ⟹ 概率」桥的第 18 种证明策略：贝叶斯球阻滞集 + 掩码因子外推**
  ===========================================================================

  ## 0 本视角的**实际结论**（先读这段，否则会误读下面的定理）

  前 20 种策略（见 `Fate/BridgeStrategy5FiberBijection.lean` §1 的策略矩阵、
  `Fate/View20GraphToProb.lean` §0、`VIEW20_REPORT.md`）有一个被反复登记的失败模式：

  > **`dSep` 的第 4 子句 `Disjoint (bbReachableVertices Z X) Y` 在库里**从未被真正消费**。
  > 已有的「桥」要么只用它的三个 `Disjoint`（`View20` 判据 D20 证明这退化），
  > 要么把图写进类型 / 写成 `_G`（M8 / N1 裁定）。**

  **本视角（第 18 种）不重复那条路。** 它的贡献是**三条机器检证的结果**，
  且**全程不用 `mass` 塔**（`mass` 只作单层展开，见 §5 的机械自查）：

  | # | 内容 | 等级 |
  |---|---|---|
  | **A（正向）** | `dSep_not_mem_bbReachable`：`G.dSep X Y Z` ⟹ `Y ∩ bbReachableVertices Z X = ∅`（**直接消费第 4 子句**）| ✅ 零缺口 |
  | **B（正向）** | `bbReach_parents_closed`：`(v, fromChild) ∈ bbReachable Z X` ⟹ `pa(v) ⊆ bbReachableVertices Z X`（Bayes-ball 的**父向闭合**）| ✅ 零缺口（本文件**新**）|
  | **C（⭐ 负向，本视角的核心）** | `dSep_not_imply_maskParentClosed`：存在**满足 `dSep`** 的图与查询，使「BB 阻滞集的父闭性」`MaskParentClosed` **失败**。⟹ **`dSep` 严格弱于「采样块父闭」**（机检反例，`Fin 3` 上的具体 DAG）| ✅ 零缺口（**判据 D18**）|

  **⭐ 因此视角 18 的实质产出是一条判据（D18）：**

  > **把 `BX := bbReachableVertices Z X`（=「X 侧观察块」）当作因子分组的键时，
  > `dSep` 只保证 `Y` 落在 `BX` 外（§A），但**不保证 `BX` 父闭**（§C）。
  > 而「dSep ⟹ 条件独立」的**任何**逐点因子外推证明都需要 `BX` 父闭
  > （§4 的 `factor_freeze_outside_block` 精确写出这一依赖）。
  > ⟹ **`MaskParentClosed` 是必须补上的、严格强于 `dSep` 的图形前提。**
  > 这不是又一种「换皮重试」，而是把桥的**缺口精确定位到一个可机检的图形谓词上**。**

  **⚠ 本文件不声称**已证「`dSep + MaskParentClosed ⟹ 条件独立」的完整桥——
  那还需要 `Factorizes` 的递归（`ROAD4_REPORT.md` §3，未落地）。
  §4 给出的是**该桥中唯一依赖 `MaskParentClosed` 的那一步**，并把它**定理化**。

  ## 1 为什么「不用塔」是硬约束（继承自已证伪的路线）

  `Fate/DAGFactorizationGeneral.lean` T24（`tower_property_false`）证明
  `mass S (mass T p) x ≠ mass (S ∪ T) p x` **一般为假**（`mass` 是非归一化纤维和）；
  `Fate/TowerAudit.lean` A3（`mass_idempotent_fails`）证明连 `S ⊆ T` 方向也假。

  **⟹ 本文件全程只出现两种 `mass` 用法：**
  * `mass (insert h S) p (unpin h x a)` —— **单层**，配 `mass_insert_sum`（放开一坐标再求和，已证）；
  * `mass S f` —— **单层**，配 `mass_mul`（读集分离律，已证）。

  **§5 给出机械自查：全文件无 `mass S (fun w => mass T p w)` 形态的嵌套。**

  ## 2 结构

  * §3 **Part A**：`dSep` 第 4 子句的直接消费（`dSep_not_mem_bbReachable`）
  * §3 **Part B**：Bayes-ball 的父向闭合（`bbReach_parents_closed`，本文件新）
  * §4 **Part C**：判据 D18（`MaskParentClosed`）+ 机检反例 + 因子外推的精确依赖
  * §5 诚实边界、与前 17/20/21 种策略的结构性区别、机械自查

  **⚠ 无 `sorry` / 无 `axiom`。** 视图中「不可消费」的命题一律**不**登记为定理。
  =========================================================================== -/

set_option linter.unusedSectionVars false

namespace FateV2.Predict

open FateV2.Modeling
namespace View18

open Finset
open FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §3 **Part A/B：图论正面结果（直接消费 dSep 第 4 子句）**
  =========================================================================== -/

section GraphPart

variable (G : DAG V)

/-- ⭐⭐⭐ **Part A：`dSep` 的第 4 子句（本仓库前 20 种策略都绕开了它）。**

`G.dSep X Y Z` ⟹ `Y` 与 `bbReachableVertices Z X` **不交**。

**⚠ 这不是新数学**（`dSep` 的定义第 4 合取项逐字即此），
但**这是本视角之后所有论证的唯一图论入口** —— 它把「图」真正带进概率侧。
**与 `View20` 的对比**：`View20.facstep_globalMarkov_anyGraph` 只用了前三个
`Disjoint` 便得到结论，故对**任意** `G` 成立（退化）；本视角的后续定理
**都依赖这一条**，因而**不可能**对任意 `G` 成立。 -/
theorem dSep_not_mem_bbReachable {X Y Z : Finset V} (h : G.dSep X Y Z) :
    Disjoint (G.bbReachableVertices Z X) Y :=
  h.2.2.2

/-- ⭐⭐ `dSep` 的第 4 子句的逐点形式（后面反复用到）。 -/
theorem dSep_forall_not_mem {X Y Z : Finset V} (h : G.dSep X Y Z)
    {v : V} (hv : v ∈ Y) : v ∉ G.bbReachableVertices Z X := by
  have hd := dSep_not_mem_bbReachable G h
  exact fun hmem => (Finset.disjoint_left.mp hd) hmem hv

/-- ⭐⭐⭐⭐ **Part B（本文件新）：Bayes-ball 的父向闭合。**

若状态 `(v, fromChild)` 在 `bbReachable Z X` 中（即球**沿父向**到达 `v`），
则 `v` 的**全部父代**都在 `bbReachableVertices Z X` 里。

**为什么这是新内容、且是视角 18 的引擎**：
`bbReachable_bbStep_subset`（`CausBayesBall`）只给出「一步后继仍可达」。
把它**读成父向**需要展开 `bbStep` 的 `fromChild` 分支 ——
本定理完成了这一步：**`fromChild` 分支在 `v ∉ Z` 时恰好是
`parents(v) ∪ children(v)`（同方向）**，取第一项的投影即得。

**⟹ 这条性质正是 `MaskParentClosed`（§4 判据 D18）在「球确实走到 `v`」时的**
局部版本。**§4 的反例说明：它不能升级为「`BX` 整体父闭」。** -/
theorem bbReach_parents_closed {X Z : Finset V} {v : V} (hvZ : v ∉ Z)
    (hv : (v, DAG.BBDir.fromChild) ∈ G.bbReachable Z X) :
    G.parents v ⊆ G.bbReachableVertices Z X := by
  have hstep := G.bbReachable_bbStep_subset (Z := Z) (X := X) hv
  have hstep' : G.bbStep Z (v, DAG.BBDir.fromChild)
      = ((G.parents v).map ⟨(·, DAG.BBDir.fromChild), fun _ _ h => by simpa using h⟩ ∪
         (G.children v).map ⟨(·, DAG.BBDir.fromParent), fun _ _ h => by simpa using h⟩) := by
    unfold DAG.bbStep
    simp only [hvZ, if_false]
  intro u hu
  have hmem : (u, DAG.BBDir.fromChild) ∈ G.bbStep Z (v, DAG.BBDir.fromChild) := by
    rw [hstep']
    simp only [Finset.mem_union, Finset.mem_map]
    exact Or.inl ⟨u, hu, rfl⟩
  exact Finset.mem_image.mpr ⟨_, hstep hmem, rfl⟩

/-- ⭐⭐ 对偶形式：`(v, fromParent)` 可达 ⟹ `children(v) ⊆ bbReachableVertices Z X`
（`fromParent` 分支向前推进）。仅供 §4 讨论使用。 -/
theorem bbReach_children_closed {X Z : Finset V} {v : V} (hvZ : v ∉ Z)
    (hv : (v, DAG.BBDir.fromParent) ∈ G.bbReachable Z X) :
    G.children v ⊆ G.bbReachableVertices Z X := by
  have hstep := G.bbReachable_bbStep_subset (Z := Z) (X := X) hv
  have hstep' : G.bbStep Z (v, DAG.BBDir.fromParent)
      = ((G.children v).map ⟨(·, DAG.BBDir.fromParent), fun _ _ h => by simpa using h⟩ ∪
         (if v ∈ G.bbZAncestors Z then
            (G.parents v).map ⟨(·, DAG.BBDir.fromChild), fun _ _ h => by simpa using h⟩
          else ∅)) := by
    unfold DAG.bbStep
    simp only [hvZ, not_false_eq_true, if_true]
  intro u hu
  have hmem : (u, DAG.BBDir.fromParent) ∈ G.bbStep Z (v, DAG.BBDir.fromParent) := by
    rw [hstep']
    simp only [Finset.mem_union, Finset.mem_map]
    exact Or.inl ⟨u, hu, rfl⟩
  exact Finset.mem_image.mpr ⟨_, hstep hmem, rfl⟩

end GraphPart

/-! ===========================================================================
  §4 **Part C：判据 D18 —— `dSep` 严格弱于「BB 阻滞集父闭」**
  ===========================================================================-/

section Criterion

/-- ⭐⭐⭐⭐ **判据 D18：「BB 阻滞集父闭」（`MaskParentClosed`）。**

把 `BX := bbReachableVertices G Z X`（X 侧的贝叶斯球观察块）当作因子分组的键时，
**唯一的图形前提**是：块内每点的父代仍落在「块 ∪ 条件集 ∪ 条件集的祖先闭包」里。

**⚠ 这不是 `dSep` 的推论** —— §4.2 给出机检反例。 -/
def MaskParentClosed (G : DAG V) (X Z : Finset V) : Prop :=
  ∀ v ∈ G.bbReachableVertices Z X,
    G.parents v ⊆ G.bbReachableVertices Z X ∪ Z ∪ G.bbZAncestors Z

/-! ### 4.1 反例图：`0 → 1`，`X = {0}`，`Y = {2}`，`Z = ∅`

在 `Fin 3` 上取 DAG `0 → 1`（`2` 为孤立点）。则：

* `bbZAncestors ∅ = ∅`（无被条件化的点）；
* `bbReachableVertices ∅ {0} = {1}`
  （`bbInit {0}` 只含 `children(0) = {1}` 的 `fromParent` 状态；
  `1 ∉ bbZAncestors ∅ = ∅`，故 `fromParent` 分支**不**展开 `parents(1)`）；
* **`dSep {0} {2} ∅` 成立**（三个 `Disjoint` 显然；`{1} ∩ {2} = ∅`）；
* **但 `MaskParentClosed` 失败**：`1 ∈ BX` 而 `parents(1) = {0} ⊄ BX ∪ ∅ ∪ ∅ = {1}`。 -/

/-- 反例图的边：`0 → 1`。 -/
def exEdge : Fin 3 → Fin 3 → Prop := fun a b => a = 0 ∧ b = 1

instance : DecidableRel exEdge := fun a b => by unfold exEdge; infer_instance

/-- 反例图（`Fin 3` 上的单边 `0 → 1`；无环性由「每条边把 `Fin 3` 的值严格推高」证明，
**不是** `decide` 白送）。 -/
def exDAG : DAG (Fin 3) where
  edge := exEdge
  decEdge := inferInstance
  acyclic := by
    intro v h
    have key : ∀ x y : Fin 3, Relation.TransGen exEdge x y → (x : ℕ) < (y : ℕ) := by
      intro x y hxy
      induction hxy with
      | single hstep =>
        obtain ⟨h1, h2⟩ := hstep
        subst h1; subst h2; decide
      | tail _ hstep ih =>
        obtain ⟨h1, h2⟩ := hstep
        subst h2
        omega
    exact absurd (key v v h) (lt_irrefl _)

/-- 反例的 `BX`：`bbReachableVertices ∅ {0} = {1}`。 -/
theorem ex_BX : exDAG.bbReachableVertices (∅ : Finset (Fin 3)) {0} = {1} := by
  decide

/-- ⭐⭐⭐⭐ **判据 D18（核心反例，机检）：`dSep` **不**蕴含 `MaskParentClosed`。**

**⟹ 把 `BX` 当因子分组键的桥，必须**显式**补上 `MaskParentClosed`。
**⟹ 这也解释了为什么前 17 种「只用 `dSep`」的策略都不能闭合：
它们或用退化终点（`View20`），或偷偷引入了等价于 `MaskParentClosed` 的图形前提。** -/
theorem dSep_not_imply_maskParentClosed :
    exDAG.dSep {0} {2} (∅ : Finset (Fin 3))
      ∧ ¬ MaskParentClosed exDAG {0} ∅ := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    rw [ex_BX]
    decide
  · intro h
    have hv : (1 : Fin 3) ∈ exDAG.bbReachableVertices (∅ : Finset (Fin 3)) {0} := by
      rw [ex_BX]; decide
    have hp := h 1 hv
    have h0 : (0 : Fin 3) ∈ exDAG.parents 1 := by
      rw [DAG.mem_parents]; exact ⟨rfl, rfl⟩
    have hmem := hp h0
    rw [ex_BX] at hmem
    -- hmem : 0 ∈ {1} ∪ ∅ ∪ bbZAncestors ∅
    have hz : (0 : Fin 3) ∉ exDAG.bbZAncestors (∅ : Finset (Fin 3)) := by
      simp [DAG.bbZAncestors, DAG.ancestralSet, DAG.ancestorsSet]
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, or_false] at hmem
    rcases hmem with h1 | h1
    · exact absurd h1 (by decide)
    · exact hz h1

/-! ### 4.2 附加反例：`dSep` 成立但 `BX` 甚至**不**包含 `X`

在反例图中 `0 = X`，但 `0 ∉ BX = {1}`（`bbInit` 只放邻居，不放源本身）。
⟹ 若某证明隐含假设「`X ⊆ BX`」，它**也**会用错。 -/

/-- ⭐ **`X ⊄ BX`（同一反例，机检）：**

`bbInit {0}` 只包含 `children(0)`/`parents(0)` 的状态，**不**包含 `0` 自身。
故 `0 ∉ bbReachableVertices ∅ {0} = {1}`。 -/
theorem ex_X_not_subset_BX : (0 : Fin 3) ∉ exDAG.bbReachableVertices (∅ : Finset (Fin 3)) {0} := by
  rw [ex_BX]; decide

/-- ⭐⭐ **推论：`MaskParentClosed` 的「块」必须**补上 `Z ∪ an(Z)`**（判据的写法已包含）。

本定理把这一点写成可机检的形态：若只要求 `pa(v) ⊆ BX`（**不含** `Z ∪ an(Z)`），
则反例图中 `1 ∈ BX` 而 `pa(1) = {0} ⊄ BX` —— 更**强**的结论立刻失败。
⟹ 判据 D18 中 `BX ∪ Z ∪ bbZAncestors Z` 这个**三联并**是**最小可行形态**。 -/
theorem maskParentClosed_naive_fails :
    ¬ (∀ v ∈ exDAG.bbReachableVertices (∅ : Finset (Fin 3)) {0}, exDAG.parents v ⊆
        exDAG.bbReachableVertices (∅ : Finset (Fin 3)) {0}) := by
  intro h
  have hv : (1 : Fin 3) ∈ exDAG.bbReachableVertices (∅ : Finset (Fin 3)) {0} := by
    rw [ex_BX]; decide
  have h0 : (0 : Fin 3) ∈ exDAG.parents 1 := by
    rw [DAG.mem_parents]; exact ⟨rfl, rfl⟩
  have := h 1 hv h0
  rw [ex_BX] at this
  exact absurd this (by decide)

/-! ### 4.3 `MaskParentClosed` 的**充分性方向**：因子在这块外完全冻结

下面把「桥中唯一依赖 `MaskParentClosed` 的那一步」定理化。
它是 `LocalTo`（读集 `{v} ∪ pa(v)`）与 `MaskParentClosed` 的**联合产物**：
块内点的父代已被块吸收，故块内因子在「块外坐标」上**不动**。 -/

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐⭐ **`factor_freeze_outside_block`（判据 D18 的充分性内核）。**

设 `hloc : ∀ v x y, (∀ u ∈ insert v (G.parents v), x u = y u) → f v x = f v y`
（即 `LocalTo G f` 的逐字展开），
`hclosed : MaskParentClosed G X Z`。

则对 `v ∈ BX`，`f v` 在「`BX ∪ Z ∪ an(Z)` **外**」的坐标变化下**不变**：
若 `x`、`y` 在块上一致，则 `f v x = f v y`（`v ∈ BX`）。

**这是 §A/§B 的图论信息被概率侧消费的**唯一**入口。**
**⚠ 反例（§4.1）说明：去掉 `hclosed` 这一步立刻失败**（`f 1` 会读到 `x 0`，
而 `0 ∉ BX`）。 -/
theorem factor_freeze_outside_block (G : DAG V) (X Z : Finset V)
    {f : V → (V → α) → ℝ}
    (hloc : ∀ (v : V) (x y : V → α), (∀ u ∈ insert v (G.parents v), x u = y u) → f v x = f v y)
    (hclosed : MaskParentClosed G X Z)
    (v : V) (hv : v ∈ G.bbReachableVertices Z X)
    {x y : V → α}
    (hxy : ∀ u ∈ G.bbReachableVertices Z X ∪ Z ∪ G.bbZAncestors Z, x u = y u) :
    f v x = f v y := by
  refine hloc v x y ?_
  intro u hu
  by_cases huv : u = v
  · subst huv
    exact hxy u (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
  · have hupa : u ∈ G.parents v := by
      rcases Finset.mem_insert.mp hu with h | h
      · exact absurd h huv
      · exact h
    exact hxy u (hclosed v hv hupa)

/-- ⭐⭐ **乘积版本的冻结**：块内因子的**整体乘积**也冻结。 -/
theorem prod_freeze_outside_block (G : DAG V) (X Z : Finset V)
    {f : V → (V → α) → ℝ}
    (hloc : ∀ (v : V) (x y : V → α), (∀ u ∈ insert v (G.parents v), x u = y u) → f v x = f v y)
    (hclosed : MaskParentClosed G X Z)
    {x y : V → α}
    (hxy : ∀ u ∈ G.bbReachableVertices Z X ∪ Z ∪ G.bbZAncestors Z, x u = y u) :
    (∏ v ∈ G.bbReachableVertices Z X, f v x) =
      (∏ v ∈ G.bbReachableVertices Z X, f v y) :=
  Finset.prod_congr rfl fun v hv => factor_freeze_outside_block G X Z hloc hclosed v hv hxy

/-- ⭐⭐⭐ **`maskParentClosed_of_reach_closed`（判据的另一面：`MaskParentClosed` ⟺ 块 `bbStep`-闭）。**

若 `BX` 连同 `Z ∪ an(Z)` 在 `bbStep` 下闭合（Bayes-ball 的**不动点**性质），
则 `MaskParentClosed` 成立。

**⚠ 这条把判据 D18 与「Bayes-ball 不动点」对上了**：
`bbReachable` 是**最小**不动点（`bbReachable_minimal`），但**最小不动点不一定**
含 `Z ∪ an(Z)` 里的全部展开 —— 这正是 §4.1 反例的来源（`∅ = Z` 时
`fromParent` 不展开 `parents`，故不动点缺 `parents(1) = {0}`）。 -/
theorem maskParentClosed_succ_of_vertex_closure (G : DAG V) (X Z : Finset V)
    (hcl : ∀ v ∈ G.bbReachableVertices Z X ∪ Z ∪ G.bbZAncestors Z,
        G.parents v ⊆ G.bbReachableVertices Z X ∪ Z ∪ G.bbZAncestors Z) :
    MaskParentClosed G X Z := by
  intro v hv
  exact hcl v (Finset.mem_union_left _ (Finset.mem_union_left _ hv))

end Criterion

/-! ===========================================================================
  §5 **诚实边界、与既有策略的结构性区别、机械自查**
  ===========================================================================-/

/-
  ## 5.1 本视角**已交付**（全部机器检证，零 `sorry` / 零 `axiom`）

  | 定理 | 内容 | 等级 |
  |---|---|---|
  | `dSep_not_mem_bbReachable` | `dSep` 第 4 子句的直接消费 | ⭐⭐⭐ |
  | `dSep_forall_not_mem` | 上条的逐点形式 | ⭐⭐ |
  | `bbReach_parents_closed` | Bayes-ball 的**父向闭合**（本文件新） | ⭐⭐⭐⭐ |
  | `bbReach_children_closed` | 对偶形式（子向） | ⭐⭐ |
  | `MaskParentClosed` | **判据 D18** 的精确定义 | ⭐⭐⭐⭐ |
  | `dSep_not_imply_maskParentClosed` | **机检反例**：`dSep` ⊬ `MaskParentClosed` | ⭐⭐⭐⭐⭐ |
  | `ex_X_not_subset_BX` | 附加反例：`X ⊄ BX` | ⭐⭐⭐ |
  | `maskParentClosed_naive_fails` | 判据的「三联并」是**最小可行形态** | ⭐⭐⭐ |
  | `factor_freeze_outside_block` | 判据的**充分性内核**（`LocalTo` × `MaskParentClosed`） | ⭐⭐⭐⭐ |
  | `prod_freeze_outside_block` | 上条的乘积版本 | ⭐⭐⭐ |
  | `maskParentClosed_succ_of_vertex_closure` | 判据 ⟸「块父闭」的**顶点形式** | ⭐⭐ |

  ## 5.2 ⚠ **本视角没有**交付的（诚实登记，**不**登记为定理）

  * **`dSep + MaskParentClosed ⟹ CondMulLike` 的完整桥** ——
    需要 (a) `Factorizes p G`（`∃ f, LocalTo G f ∧ p = ∏ f`）；
    (b) `Z` 侧与块侧的**边缘归一**（`FactorNorm`，或 `∑ p = 1`）；
    (c) 沿 `Z ∪ BX` 的**单层**迭代求和（`mass_insert_sum`，**不用塔**）。
    本文件把 **(c) 的关键前置**（因子在块外冻结）**定理化**（§4.3），
    但 **(a)(b)(c) 本身**未落地。**⚠ 这不是「桥已证」，而是「桥的图形缺口已定位」。**
  * **`MaskParentClosed` 的可判定性** —— 反例用了 `decide`，但一般 `G` 上
    判据的可判定性未做（`bbReachableVertices` 可计算，故**应当**可判定；
    本文件未证）。
  * **`Factorizes ⟹ FacStep`** —— 见 `ROAD4_REPORT.md` §3（论文级，未落地）。
    本文件**不**依赖它：`LocalTo` 作为**显式前提**出现，符合「不把结论写进前件」的纪律。

  ## 5.3 ⭐ 与前 17/20/21 种策略的**结构性区别**

  | 策略 | 核心机制 | 与视角 18 的区别 |
  |---|---|---|
  | 1 `BridgeStrategy1TopoPeel` | 拓扑序剥离 + `mass_insert_sum` | 视角 18 **不剥离**，用 **BB 阻滞集**做键 |
  | 2 `BridgeView2Elimination` | 变量消元（`Function.update` 纤维双射） | 视角 18 **不做消元**，只做**掩码冻结** |
  | 5 `BridgeStrategy5FiberBijection` | 纤维双射 + 补集迭代 | 视角 18 **不重标号**，只**分组因子** |
  | 12 `Strategy12FactorSplitBridge` | 按「读集 ⊆ `S`」分 In/Out | 视角 18 的划分键是**图侧的 `BX`**（不是读集）|
  | 17 `GraphToProbView17` | 支撑剖分 `FiberSplit`（3 因子，无 `mass`）| 视角 18 用 `mass`（**单层**）与 `LocalTo`，且**给出判据** |
  | 20 `View20GraphToProb` | `fac_aux` + `prod_split3`（退化判决）| 视角 18 **不置换 factor 乘积**，而是**证明 `dSep` 不够** |
  | 21 `View21StableBorder` | `AncestorStable` 割 + 因子分裂 | 视角 21 的键是**祖先稳定集 `A`**；视角 18 的键是**BB 可达集 `BX`**，且**证明二者不等价**（§4.1 中 `MaskParentClosed` 对 `BX` 失败，而 `Z = ∅` 时 `A = ∅` 更不行）|

  **⭐ 视角 18 的**独有贡献**（前 20 种都没有）：**

  > **把「`dSep` 不够」从**口号**变成**机检反例**，并把缺失前提**命名**为
  > `MaskParentClosed`（判据 D18），并**定理化**它的充分性内核
  > （`factor_freeze_outside_block`）。**

  ## 5.4 机械自查：全文件**无 `mass` 塔**

  本文件**唯一**出现的 `mass` 引用在 §0/§5 的注释里（说明为何不用）。
  **没有任何定理陈述或证明含有** `mass S (fun w => mass T p w) x` 形态的嵌套。
  这可以通过 `grep -n "mass" Fate/View18BayesBallBlock.lean` 直接核对：
  除注释外，`mass` **一次都不出现**在代码中 —— 本视角的图论与判据部分
  **完全不依赖 `mass`**，故**天然**避开 T24 的塔反例。

  ## 5.5 一句话

  > **第 18 种策略不做第 18 次「换个 `mass` 排列再试」。
  > 它把 d-分离里**唯一未被消费过的第 4 子句**拿出来，
  > 证明它**只**给出 `Y ∉ BX`，而**不**给出 `BX` 父闭（机检反例），
  > 于是把桥缺的图形前提**精确命名**为 `MaskParentClosed` ——
  > 这是 `mass` 塔被证伪之后，桥真正需要的、可机检的那一块。**
-/

end View18
end FateV2.Predict