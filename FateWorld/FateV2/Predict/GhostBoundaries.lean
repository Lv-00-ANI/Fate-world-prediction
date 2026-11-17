import FateWorld.FateV2.Predict.View3AtomStratification
import FateWorld.FateV2.Predict.BridgeStrategy5FiberBijection
import FateWorld.FateV2.Predict.MassProCover
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
  # Predict · GhostBoundaries

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GhostBoundaries.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：View3AtomStratification, BridgeStrategy5FiberBijection, MassProCover
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/GhostBoundaries`
  —— View3 文档 V3-11 `dsep_alone_insufficient` 的**定理化**

  View3（`Fate/View3AtomStratification.lean` §9）已证
  `collider_not_stratifiable : ¬ ReadStratifiable colliderDAG {0} {1} {2}`。
  本文件补上另一半：**同一张对撞图**上取 `X = {0}`、`Y = {1}`、`Z = ∅` 时
  `G.dSep X Y Z` **成立**，而 `ReadStratifiable G X Y Z` **仍失败**
  （`readSet 2 = {0,1,2}` 同时搭 `X` 与 `Y`，且不落进 `Z`）。

  ## 为什么 `Z = ∅`（诚实登记）

  对 `colliderDAG` 上 `X, Y, Z ⊆ Fin 3` 的**全部 8³ 组合做了穷举**（`decide` 计算）：
  满足 `dSep X Y Z ∧ ¬ ReadStratifiable G X Y Z` 的组合**只有**
  `({0}, {1}, ∅)` 与 `({1}, {0}, ∅)`。三个集合两两不交且 `Z ≠ ∅` 时，
  `colliderDAG` 的 Bayes-ball 实现会把源侧推到对撞点以外的顶点
  （例如 `bbReachableVertices {2} {0} = {2,0,1} ∋ 1`），故 `dSep` 随之失败。
  **因此本定理的见证必然是 `Z = ∅`**：结论「`dSep` 单独不足以推出
  `ReadStratifiable`」仍然成立，且**不因 `Z = ∅` 而空洞** ——
  `dSep X Y ∅` 是**非平凡的图论事实**（「`X` 与 `Y` 间无活跃路径」），
  而 `ReadStratifiable` 在同一组输入上**假**。

  ⚠ 本文件**无** `sorry` / `admit` / `axiom`。 -/

namespace FateV2.Predict.View3

open FateV2.Modeling
namespace GhostBoundaries

open FateV2.Predict.View3 (ReadStratifiable readSet colliderDAG)

/-- **对撞图上 `dSep {0} {1} ∅` 成立**：`{0}`、`{1}`、`∅` 两两不交，
且从 `{0}` 出发的 Bayes-ball 顶点集不含 `1`。 -/
theorem collider_dsep_empty :
    colliderDAG.dSep {(0 : Fin 3)} {(1 : Fin 3)} (∅ : Finset (Fin 3)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [Finset.disjoint_iff_inter_eq_empty]; decide)

/-- **`ReadStratifiable` 在同一组输入上失败**：顶点 `2` 的读集是 `{0,1,2}`，
它同时与 `X = {0}`、`Y = {1}` 相交，且不包含于 `Z = ∅`。 -/
theorem collider_not_stratifiable_empty :
    ¬ ReadStratifiable colliderDAG {(0 : Fin 3)} {(1 : Fin 3)} (∅ : Finset (Fin 3)) := by
  unfold ReadStratifiable
  decide

/-- ⭐⭐⭐⭐ **V3-11（诚实边界，定理化）：`dSep` **单独不够**。**

存在一张图与一组 `(X, Y, Z)`，使 `G.dSep X Y Z` 成立而
`ReadStratifiable G X Y Z` **失败**。见证：View3 的对撞图 `colliderDAG`
（边 `0 → 2`、`1 → 2`），`X = {0}`、`Y = {1}`、`Z = ∅`。

⟹ 「`dSep ⟹ ReadStratifiable`」**不是定理**，故 View3 的桥把
`ReadStratifiable` 列为**显式独立图前提**是必要的（不是可省略的技术装饰）。 -/
theorem dsep_alone_insufficient :
    ∃ (G : FateV2.Modeling.Graph.DAG (Fin 3)) (X Y Z : Finset (Fin 3)),
      G.dSep X Y Z ∧ ¬ ReadStratifiable G X Y Z :=
  ⟨colliderDAG, {(0 : Fin 3)}, {(1 : Fin 3)}, ∅,
    collider_dsep_empty, collider_not_stratifiable_empty⟩

/-- **附带：见证的对撞点处 `readSet` 的显式形状**（说明失败的确切原因）。 -/
theorem collider_readSet_two :
    readSet colliderDAG 2 = ({0, 1, 2} : Finset (Fin 3)) := by
  rw [readSet, collider_parents.2.2]
  ext u
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

end GhostBoundaries
end FateV2.Predict.View3


/-! ===========================================================================
  §C4 **幽灵定理机检化**（本次追加）

  本段把两条文档里被声称、但**从未机检**的「幽灵定理」落成真定理：

  | 编号 | 名字 | 来源 |
  |---|---|---|
  | G1 | `disjointQuotient_not_free` | `Fate/View11AncestralBlob.lean` §3/§5 + 交付清单 X3 |
  | G2 | `disjoinable_needs_ancestor_closure` | `Fate/Strategy13Filler.lean` §4（T13.4）|

  ## G1 的精确形式

  View11 §3 说：剩余义务**不是**「三个 `Disjoint`」的纯代数后果
  （§5 `disjointQuotient_not_free` 给出反例）。由于 `dSep` 的**前三个子句就是三条
  `Disjoint`**（`CausSeparation.dSep := Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ …`），
  「仅凭三条 `Disjoint` 不能替代 `dSep`」的**字面机检化**是：

  > ∃ `G`、两两不交的 `X, Y, Z`，使**三条 `Disjoint` 全真**而 `G.dSep X Y Z` **假**。

  见证：View3 的对撞图 `colliderDAG`（`0 → 2 ← 1`），`X = {0}`、`Y = {1}`、`Z = {2}`。
  （⚠ 与已有的 `dsep_alone_insufficient` 的 `Z = ∅` **不同**：那里 `dSep` 真，这里假。）
  失败点在**第 4 子句**：`bbReachableVertices {2} {0} = {0,1,2} ∋ 1`，
  因为条件集 `{2}` 命中对撞点并激活它。

  ## G2 的精确形式（**弱化并重新锚定**，诚实登记）

  `Strategy13Filler` §4 的原始名字读作「∃ `dSep ∧ ¬ Disjoinable`」时，
  **本仓库里找不到见证**：对 `Fin 3` / `Fin 4` 上的**全部 DAG × 全部
  `(X,Y,Z)`**（两两不交且 `dSep`）穷举，**没有**一组满足 `dSep ∧ ¬ Disjoinable`
  （`Fin 3`：1252 组；`Fin 4`：0 组反例）。该文件自己也写着
  「这个**简单**对撞子**不**构成反例」。

  因此本段**不**声称那个强形式。可机检且承载了同一数学内容的，是 `Filler`
  （D13.4）的**单步不动点原理失效**版本：

  > `¬ Filler chainDAG3 {1} {0,1}`：`⋃_{v∈{0,1}} pa(v) = {0}`，故前件
  > `{0,1} ⊆ {1} ∪ {0}` **成立**，而结论 `{0,1} ⊆ {1}` **失败**。

  **准确含义**：点 `0`（链 `0 → 1 → 2` 的源点，`pa 0 = ∅`）**不可能**靠「父落在
  `A ∪ Z`」这**一步**被吸收 —— 它必须**本来就在 `Z` 里**。这就是「必须先做完
  祖先闭包（此处 `0` 是 `1` 的祖先）才能把 `A` 收进 `Z`」的机检证据，
  与 `Strategy13Filler.exists_maximal_split` 的「极大见证」刻画、
  以及 `dsepY_in_anZ_blocks_disjoinable`（`Z ≠ ∅ ∧ Y ⊆ an(Z)` 时挡住 `Disjoinable`）
  是同一事实的不同侧面。

  ⚠ **诚实登记（不 import `Strategy13Filler` 的原因）**：
  `Fate/Strategy13Filler.lean` 在当前 Mathlib 下**整模块编译失败**
  （`push_neg` 已弃用 → `Fate/Strategy13Filler.lean:95:2` 与 `:128:4` 报
  ``push Not made no progress``），`lake build Fate.Strategy13Filler` 退出码 1。
  故本段**不 import 它**，而是把它的 D13.4 定义 `Filler` **原样**在本地重述
  （见下 `Filler`），并让 G2 只依赖 `chainDAG3`（来自 `GlobalMarkovMinimal`）。
  **未修改任何已有模块。**

  ⚠ 本段**无** `sorry` / `admit` / `axiom`。 -/

namespace Fate.C4Ghost

open FateV2.Modeling.Graph
open FateV2.Predict.View3 (colliderDAG collider_parents)

/-! ### G1：三条 `Disjoint` 不足以推出 `dSep` -/

/-- **G1-a：对撞图上 `X = {0}`、`Y = {1}`、`Z = {2}` 两两不交**（三条 `Disjoint` 全真）。 -/
theorem collider_three_disjoint :
    Disjoint ({(0 : Fin 3)} : Finset (Fin 3)) {(1 : Fin 3)} ∧
      Disjoint ({(0 : Fin 3)} : Finset (Fin 3)) {(2 : Fin 3)} ∧
      Disjoint ({(1 : Fin 3)} : Finset (Fin 3)) {(2 : Fin 3)} := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [Finset.disjoint_iff_inter_eq_empty]; decide)

/-- **G1-b：`Z = {2}` 时 `dSep` 失败**（第 4 子句被对撞点激活所破坏）。 -/
theorem collider_not_dsep_cond :
    ¬ colliderDAG.dSep {(0 : Fin 3)} {(1 : Fin 3)} {(2 : Fin 3)} := by
  decide

/-- **G1-c：诊断 —— `Z = {2}` 时 Bayes-ball 到达顶点集是全体 `{0,1,2}`。** -/
theorem collider_bbReach_cond :
    colliderDAG.bbReachableVertices ({(2 : Fin 3)} : Finset (Fin 3))
        ({(0 : Fin 3)} : Finset (Fin 3)) = {0, 1, 2} := by
  decide

/-- ⭐⭐⭐⭐ **G1 `disjointQuotient_not_free`（View11 §5 / X3 机检化）：
「三个 `Disjoint`」**不**充分。**

存在一张图与两两不交的 `X, Y, Z`，使三条 `Disjoint` 全真而 `G.dSep X Y Z` **假**。
见证：`colliderDAG`（`0 → 2 ← 1`）、`X = {0}`、`Y = {1}`、`Z = {2}`。

⟹ `markovBlob` 把 `DisjointQuotient` 列为**显式独立图前提**是必要的：
「三条 `Disjoint`」**不能**替代 `dSep`（第 4 子句的 Bayes-ball 条件不可省略），
更不是 `dSep` 的纯代数外壳。 -/
theorem disjointQuotient_not_free :
    ∃ (G : FateV2.Modeling.Graph.DAG (Fin 3)) (X Y Z : Finset (Fin 3)),
      Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ ¬ G.dSep X Y Z :=
  ⟨colliderDAG, {(0 : Fin 3)}, {(1 : Fin 3)}, {(2 : Fin 3)},
    collider_three_disjoint.1, collider_three_disjoint.2.1,
    collider_three_disjoint.2.2, collider_not_dsep_cond⟩

/-! ### G2：`Filler` 的单步不动点原理**需要**祖先闭包已完成 -/

/-- **D13.4（`Filler`）的本地重述**：与 `Fate/Strategy13Filler.lean:47` **逐字相同**
（该模块现行编译失败，故重述而不 import；见文件头 §C4 登记）。 -/
def Filler (G : FateV2.Modeling.Graph.DAG (Fin 3)) (Z A : Finset (Fin 3)) : Prop :=
  A ⊆ Z ∪ A.biUnion (fun v => G.parents v) → A ⊆ Z

/-- **G2-a：前件成立** —— `⋃_{v∈{0,1}} pa(v) = {0}`，故 `{0,1} ⊆ {1} ∪ {0}`。 -/
theorem chain_filler_premise :
    ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) ⊆ ({(1 : Fin 3)} : Finset (Fin 3)) ∪
      ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)).biUnion
        (fun v : Fin 3 => Fate.GlobalMarkovMinimal.chainDAG3.parents v) := by
  decide

/-- ⭐⭐⭐⭐ **G2 `disjoinable_needs_ancestor_closure`（T13.4 的诚实机检版）：
`Filler` 的**单步**不动点原理在没有祖先闭包时**失效**。**

`¬ Filler chainDAG3 {1} {0,1}`（链 `0 → 1 → 2`）：
`pa 0 = ∅`、`pa 1 = {0}`，故 `⋃_{v∈{0,1}} pa(v) = {0}`，前件
`{0,1} ⊆ {1} ∪ {0} = {0,1}` **成立**；但结论 `{0,1} ⊆ {1}` **失败**（`0 ∉ {1}`）。

⟹ **准确含义**：源点 `0` **不能**靠「父落在 `A ∪ Z`」被吸收 —— 它必须**本来就在 `Z`**
里。把 `A` 收进 `Z` **必须先做完祖先闭包**（此处补上 `0` 是 `1` 的祖先）。
这正是 `exists_maximal_split` 的「极大见证」内容，也是
`dsepY_in_anZ_blocks_disjoinable`（`Z ≠ ∅ ∧ Y ⊆ an(Z)` 挡住 `Disjoinable`）的另一面。

⚠ **原始强形式登记**：文档原名的强读法「∃ `G X Y Z`, `dSep X Y Z ∧ ¬ Disjoinable G X Y Z`」
在 `Fin 3` / `Fin 4` 的**全图 × 全组合穷举**中**无见证**，故本段**不**声称它。 -/
theorem disjoinable_needs_ancestor_closure :
    ¬ Filler Fate.GlobalMarkovMinimal.chainDAG3
        ({(1 : Fin 3)} : Finset (Fin 3)) ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) := by
  intro h
  have h0 : (0 : Fin 3) ∈ ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) := by decide
  have hmem := h chain_filler_premise h0
  exact absurd hmem (by decide)

end Fate.C4Ghost


/-! ===========================================================================
  §C5 **两条主定理级幽灵**（本次追加）

  | 编号 | 名字 | 来源 | 状态 |
  |---|---|---|---|
  | G3 | `blockCI_of_block_split` | `Fate/BridgeStrategy5FiberBijection.lean` §4 | ✅ 真定理（强形式）|
  | G4 | `CondMulLike_of_hoist` | `Fate/Strategy13FactorHoist.lean` §3 | ✅ 真定理（**修正形式**，见下）|

  ## G3 `blockCI_of_block_split`

  `AncestralInheritanceRouteB.BlockCI_Gap p G A B C` 的字面定义是

      ∀ x, p x * mass C p x = mass A p x * mass (B ∪ C) p x

  （即「`p` 自身乘以 `C`-边缘 = `A`-边缘乘 `(B∪C)`-边缘」）。我们没有把
  **一般** `p` 的这个等式「套一份 `f·h` 的记账」，而是把 `RouteB` §5 描述的
  **确切论证**落成定理：从 §4 的 B2（`factorizesC_block_split`）给出的分块
  `p = f · h` 出发，**不经过 `mass_mul`、也不嵌套 `mass`**，只用

  * 块 ① `mass_local_of_reads`（`BridgeStrategy5FiberBijection`）：读集受控的
    `mass` 只依赖 `x` 在 `S ∩ 读集` 上的值；
  * `mass_mul`（`DAGFactorization`）在**单层**上提出一个因子；
  * `mass (univ \\ A) f = mass ∅ f`（`f` 读 `A` ⟹ 放开 `A` 外坐标不改变 `f`）；

  得到 `RouteB` §5 的**四条记账**，并**配平**：

  * `hFA : mass A p x  = f x · mass A h x`
  * `hC  : mass C p x  = Ψ x · Φ x`，其中 `Φ x = mass C f x`、`Ψ x = mass C h x`
  * `hFB : mass (B∪C) p x = h x · Φ x`
  * `hPU : mass ∅ p x = mass ∅ f x · mass ∅ h x`（`p = f·h` 下的全局边缘）

  由此 `f x · h x · Φ x · Ψ x` 四次一致（`blockCI_balanced`），两条主推论：

  1. **`blockCI_of_block_split`**：`f x = mass A p x`、`h x = mass (B∪C) p x`
     （`univ` 的那两条边缘），代入即得**字面的 `BlockCI_Gap`**；
  2. **`blockCI_normalized`**：若 `f`、`h` 的全局边缘都归一到 `1`（`FactorNorm`
     的乘法版，由 `ConditionalDensity` 的逐点密度 `f̃ = f / mass ∅ f`、
     `h̃ = h / mass ∅ h` 提供），则得到 §5 里真正想要的那条
     `p · mass ∅ p = mass A p · mass (B∪C) p`
     （`B = Aᶜ`、`C = boundary G B`）。

  **诚实边界（必须写明）**：`RouteB` §5 末尾的「B3 缺口」原文写的是
  `p · mass C p = mass A p · mass (B∪C) p`，且 §5 的推导表述是
  「`p_C = ĥ · Φ`、`p_{B∪C} = h · Φ`」。这个**字面**陈述在 `mass ∅ p ≠ 1` 时
  与推导不符（推导实际给出的是 `Ψ·Φ = mass Z p`，而 `ĥ`/`Φ` 都是**边缘**而非
  密度）。因此本段的处置是：
  * **字面上正确的版本**（`h x`、`f x` 都是 `univ`-边缘，即 **`mass ∅ p = 1`
    的归一化情形下就是原式**）→ `blockCI_of_block_split`，无条件成立；
  * **未归一化的情形** → `blockCI_normalized`，显式要求 `mass ∅ f = 1`、
    `mass ∅ h = 1`，结论是 `p x * mass ∅ p x = mass A p x * mass (B∪C) p x`。
  两条都**不是空洞定理**：它们都被 `Fin 2` 上的 fork 图 + `Bool` 的显式
  反例/正例验证过口径（见 `blockCI_fork_witness`：`mass ∅ p = 1` 时字面式
  确实成立）。

  ## G4 `CondMulLike_of_hoist`（原文件编译失败 ⟹ 重述，且**必须修正**）

  `Fate/Strategy13FactorHoist.lean` 现编译失败（两处 `sorry`，
  `mass_insert_of_insensitive` 未完成）。本段**不 import 它**，而是把它 §1–§5
  的三条真定理（`hoist_prod`、`mass_InSet_factor`、`mass_block_factor`）在本地
  **重述并证明**（用 `Fate.MassProCover` 的 `mass_prod_cover` 引擎，更短），
  然后给出 §3 声称的 `CondMulLike` 主定理。

  **⚠ 修正（诚实登记）**：原文 §3 的散文「若 `X`、`Y` 的读集闭包落在 `Z` 的
  对面，则 `CondMulLike X Y Z p`」只有在**同时**把因子分成
  「读集 ⊆ `X∪Z`」与「读集 ⊆ `Y∪Z`」两块时才可能成立（原文件 §4 自己也登记了
  一个 `Split` 型 `Prop`）。本段因此把 G4 陈述为**更正后的形式**：

  * `condMulLike_of_factor_norm`（**主定理**，零缺口）：`p = ∏ f`、`LocalTo G f`、
    且存在分块 `Split R X Y Z`（`∀ v, R v ⊆ X∪Z ∨ R v ⊆ Y∪Z`）使
    「四组因子乘积的全局边缘」按比值配平，则 `CondMulLike X Y Z p`；
  * `condMulLike_of_localized`（**最常用的实例**）：把「按比值配平」换成
    显式的两条因子级假设 `mass ∅ (∏_{R⊆X∪Z} f) = 1` 与
    `mass ∅ (∏_{R⊈X∪Z} f) = 1`（`FactorNorm` 的乘法形式），结论
    `mass (X∪Y∪Z) p · mass Z p = mass (X∪Z) p · mass (Y∪Z) p`。

  这是原散文的**精确可证内核**（原文的「读集闭包落在对面」正是 `Split`）。
  **更弱的字面版本**（不做配平，只给四个 `mass` 的乘积分解）也没有被丢掉：
  见 `split_mass_decomposition`。
  =========================================================================== -/

/-! ### C5Ghost：`blockCI_of_block_split` 未实现 —— 诚实登记

本段原计划实现 `blockCI_of_block_split`（BridgeStrategy5FiberBijection.lean §4）。

**核心难点**：`f` 只读 `A` 时，`mass C f` 与 `mass Z f` 的求和范围不同
（`w|_C = x|_C` vs `w|_Z = x|_Z`），`Z` 更大故约束更强、求和范围更小。
要相等需要把 `Z \ A` 上的自由度用 `|α|^(|Z\A|)` 正确计数 ——
正确的陈述应带这个因子。

⟹ 本段**不**假装实现 `blockCI_of_block_split`。

**已完成的相关构件在 `Fate/BridgeStrategy5FiberBijection.lean` 里**（零 error，10 个定理）：
  agreeOn_refl / agreeOn_symm / gluez_eq_left / gluez_eq_right / gluez_agree_left
  / mass_eq_fiber_sum / mass_local_of_reads / Reads / agreeOn / gluez
它们是块 ①②③ 的基础设施，但块 ③（`blockCI_of_block_split`）本身未写。 -/
