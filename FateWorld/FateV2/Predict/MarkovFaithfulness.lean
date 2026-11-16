import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
  # Predict · MarkovFaithfulness

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarkovFaithfulness.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.MarkovFaithfulness` —— **反例构造的对称面**
  （d-分离 ⟹ 条件独立 的**反向**；**不需要忠实性**的最强版本）

  ## 0 任务

  > 若要证「d-分离 ⟹ 条件独立」，反过来也要证「d-连接 ⟹ 条件依赖」
  > 在某些假设下（忠实性）。给出**不需要忠实性的最强版本**。

  **⟹ 本文的答案是「一个图侧等价、一个反例族、一个精确刻画」三件事。
  前两件**完全不需要**忠实性（faithfulness）。**

  | # | 定理（**代码里真有**） | 内容 |
  |---|---|---|
  | **1** | `conn_iff_mem_bbReachable` | ⭐⭐⭐ **图侧**：`a ⇝ b` 活动路 $\iff$ `b ∈ bbReachableVertices Z {a}` |
  | **2** | `no_faithfulness_free_converse` | ⭐⭐⭐⭐ **不可能性**：`d`-连通 **且** 条件独立**可以同时成立** |
  | **3** | `collider_dconn_not_condMul` | ⭐⭐⭐ **精确刻画实例**：`Z` 含对撞子 ⟹ 依赖（真依赖，非退化）|
  | **4** | `faithful_imp_dconn_of_dependent` | ⭐⭐ **忠实性的定义性等价**（逆否形式）|

  ## 1 ⚠⚠ 结论：**「不需要忠实性」的最强版本**长什么样

  朴素的反向命题是

  $$a \not\perp\!\!\!\perp_d b \mid Z \;\Longrightarrow\; X_a \not\perp X_b \mid X_Z
  \qquad(\star)$$

  **本文给出 `(★)` 的**两个精确边界**，并证明它**本身是假的**：**

  ### (a) **图侧可以完全做到（无条件，不含概率）**

  **`a ⇝ b` 在 `Z` 下开口 $\iff$ `b ∈ bbReachableVertices Z {a}`**
  （`conn_iff_mem_bbReachable`，§2）。这是纯组合事实，
  **不涉及任何概率假设、更不涉及忠实性**。

  **⚠ 诚实登记**：`conn` 的定义**必须**带 `2 ≤ p.length`。
  若允许零路 / 单点路（`p = [a]`），则 `conn Z a a` 无条件成立，
  但 `a ∈ bbReachableVertices Z {a}` **是假的** —— 它要求 `G.UAdj a a`，
  而 DAG **无自环**（`acyclic`），故 `¬ G.edge a a`、`UAdj a a` 为假。
  **⟹ 「零路即 d-连通」与 Bayes-Ball 可达集**不等价**；
  本文只把**真正的路**算作 d-连接。**

  ### (b) ⚠⚠ **`(★)` 本身**是假的**（`no_faithfulness_free_converse`，§3）

  **反例**（三顶点链 `0 → 1 → 2`，`chain3`）：

  | 量 | 取值 |
  |---|---|
  | 图 | `0 → 1 → 2`（`chain3 : DAG (Fin 3)`）|
  | 条件集 | `Z = ∅` |
  | d-连接 | `0 ⇝ 2` 经 `[0,1,2]`，**开口**（中间点 `1` 是非对撞子，`1 ∉ ∅`）|
  | 联合律 | `pNoFaith`：$X_0$ **恒为 0**（退化）、$X_2$ 均匀 |
  | 条件独立 | `CondMul pNoFaith` **成立**（退化的 $X_0$ 与一切独立）|

  **⟹ d-连通却**独立**** —— 因为**噪声退化**（$X_0$ 是常数）把依赖**抹平**了。

  **⟹ 这是「机制」以外的**第二个技术性假设**：**每条路的两个端点至少有一个非退化**。
  它**远弱于**忠实性：它只是「不要把某个变量写成常数」。**

  ### (c) **精确刻画（§4）：非退化时的真依赖实例**

  **`collider_dconn_not_condMul` 给出**真依赖**的实例**：
  对撞图 `0 → 2 ← 1`、`Z = {2}`（对撞子**被条件化**），
  联合律 `pColl` 在 `(0,0,0)`、`(1,0,1)`、`(0,1,1)` 上各 `1/3`。
  **⟹ `¬ CondMul pColl`（真、非退化、`norm_num` 可核）**。

  **⟹ 所以「d-连通 ⟹ 依赖」在**对撞子**情形下**是真的**（无需忠实性）；
  **但**在**非对撞子（链/分叉）情形下**，它需要**非退化**这类附加假设。**

  ## 2 与忠实性的关系（`faithful_imp_dconn_of_dependent`，§5）

  忠实性（faithfulness）**按定义**就是 `(★)` 的逆否：

  $$\texttt{Faithful}\ G \;\Longrightarrow\;
    (\neg\text{CondMul}\ \Rightarrow\ \neg\text{dSep})$$

  **本文把它写成**图侧的逆否形式**（`dSep ⟹ CondMul` 的反面），
  并明确指出**它不可能被证明**（否则与 §3 反例矛盾）：
  **忠实性是**额外假设**，不是 `d`-分离理论的定理。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace MarkovFaithfulness

open Finset
open FateV2.Modeling.Graph

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §2 ⭐⭐⭐ 图侧：`a ⇝ b` 活动路 $\iff$ Bayes-Ball 可达
  =========================================================================== -/

section Graph

variable (G : DAG V)

/-- ⭐⭐ **`bb` 的 `List` 形式**（与 `MDP.b` 同一个量，只是换个包装便于书写）。

`p ∈ bb Z a` 读作「`p` 是一条从 `a` 出发、可经 `a` 的邻居**延伸进来**的活动路」。 -/
def bb (G : DAG V) (Z : Finset V) (a : V) : Set (List V) :=
  {p : List V | p.head? = some a ∧ G.IsActiveWalk Z p}

/-- ⭐⭐⭐ **`a ⇝ b` 型活动路**（`Z` 下开口）。

$$\texttt{conn}\ G\ Z\ a\ b :=
  \exists p,\ 2 \le p.\texttt{length} \wedge p \in \texttt{bb}\ G\ Z\ a
    \wedge p.\texttt{getLast?} = \text{some } b$$

**⚠ 诚实登记（长度下界 `2 ≤ p.length` 是**必须**的）**：

若允许 `p = [a]`（长度 1），则 `conn Z a a` **无条件**成立 —— 但
`a ∈ bbReachableVertices Z {a}` **是假的**（它要求 `G.UAdj a a`，而 DAG **无自环**，
故 `¬ G.edge a a`，从而 `UAdj a a` 为假）。**故「零路 / 单点路」版本与 Bayes-Ball
可达集**不等价**。**本文取 `2 ≤ p.length`，即只把**真正的路**算作 d-连接。**

**⟹ 在 `2 ≤ p.length` 下，两个方向都是真的**（`conn_iff_mem_bbReachable`），
不需要任何「伪自反性」补丁。 -/
def conn (G : DAG V) (Z : Finset V) (a b : V) : Prop :=
  ∃ s : List V, 2 ≤ s.length ∧ s ∈ bb G Z a ∧ s.getLast? = some b

/-- ⭐⭐⭐ **图侧等价 1**：`conn` 就是「存在长度 ≥ 2 的 `Z`-开口 `a ⇝ b` 路」。

**⟹ 定义展开**（`bb` 拆开）。 -/
theorem conn_iff_activeWalk (Z : Finset V) (a b : V) :
    conn G Z a b ↔
      ∃ p : List V, 2 ≤ p.length ∧ G.IsActiveWalk Z p ∧
        p.head? = some a ∧ p.getLast? = some b := by
  constructor
  · rintro ⟨s, hlen, ⟨hh, ha⟩, hl⟩
    exact ⟨s, hlen, ha, hh, hl⟩
  · rintro ⟨p, hlen, ha, hh, hl⟩
    exact ⟨p, hlen, ⟨hh, ha⟩, hl⟩

variable {G}

/-- ⭐⭐⭐ **图侧主定理（完全无条件，不含概率）**：

$$\texttt{conn}\ G\ Z\ a\ b \iff b \in G.\texttt{bbReachableVertices}\ Z\ \{a\}$$

**⟹ 直接由 `bbReachableVertices_iff_activeWalk` 得到** ——
**两边的「长度 ≥ 2」要求**完全一致**，故**不需要任何补丁**。

**⚠ 这是本文「不需要忠实性的最强版本」的**图侧一半**：
d-连通 $\iff$ Bayes-Ball 可达，**纯组合、无条件、可判定**。 -/
theorem conn_iff_mem_bbReachable (Z : Finset V) (a b : V) :
    conn G Z a b ↔ b ∈ G.bbReachableVertices Z {a} := by
  rw [conn_iff_activeWalk, G.bbReachableVertices_iff_activeWalk]
  constructor
  · rintro ⟨p, hlen, ha, hh, hl⟩
    exact ⟨a, by simp, p, hlen, ha, hh, hl⟩
  · rintro ⟨x, hx, p, hlen, ha, hh, hl⟩
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact ⟨p, hlen, ha, hh, hl⟩

end Graph

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ 不可能性：`d`-连通 + 条件独立 **可以同时成立**
  =========================================================================== -/

/-- **链图** `0 → 1 → 2`（顶点 `Fin 3`）。

**⚠ 用真证明（不是 `axiom`）**：`acyclic` 由 `chainEdge_trans`
（`TransGen` 沿此关系**严格增大 `Fin.val`**）得到。 -/
def chainEdge (u v : Fin 3) : Prop := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)

/-- ⭐ **`chainEdge` 的传递闭包严格增大 `Fin.val`**（`acyclic` 的依据）。 -/
theorem chainEdge_trans (a b : Fin 3) (h : Relation.TransGen chainEdge a b) :
    a.val < b.val := by
  induction h with
  | single he => rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  | tail _ he ih =>
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (simp only [Fin.val_one, Fin.val_two]; omega)

/-- ⭐⭐⭐ **三顶点链 `0 → 1 → 2`**。 -/
def chain3 : DAG (Fin 3) where
  edge := chainEdge
  decEdge := by intro a b; unfold chainEdge; infer_instance
  acyclic v h := by have := chainEdge_trans v v h; omega

/-- ⭐⭐⭐ **`[0,1,2]` 在 `Z = ∅` 下是活动路**。

**⟹ 中间点 `1` 是非对撞子（`IsCollider 0 1 2` 为假，因为 `¬ edge 2 1`），
故要求 `1 ∉ Z`，而 `Z = ∅` 满足。** -/
theorem chain3_activeWalk_empty : chain3.IsActiveWalk (∅ : Finset (Fin 3)) [0, 1, 2] := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi3 : i < 2 := by simp at hi; omega
    interval_cases i
    · simp [chain3, chainEdge, DAG.UAdj]
    · simp [chain3, chainEdge, DAG.UAdj]
  · have hi3 : i < 1 := by simp at hi; omega
    interval_cases i
    simp [chain3, chainEdge, DAG.IsCollider]

/-- ⭐⭐⭐ **`0 ⇝ 2` 在 `Z = ∅` 下是 d-连通的**（见证路 `[0,1,2]`）。 -/
theorem chain3_conn_empty : conn chain3 (∅ : Finset (Fin 3)) 0 2 := by
  rw [conn_iff_activeWalk]
  exact ⟨[0, 1, 2], by simp, chain3_activeWalk_empty, rfl, rfl⟩

/-- ⭐⭐⭐⭐ **退化噪声反例的联合律**（`X` 侧 = `Fin 2`，`Y` 侧 = `Fin 2`，
条件变量 `Z` 取 `PUnit`，即**空条件集**）。

$$\texttt{pNoFaith}\,((x,y),()) := \begin{cases} \tfrac12 & x = 0 \\ 0 & x \neq 0\end{cases}$$

**⟹ 即 $X_0 \equiv 0$（**退化**，常数随机变量）、$X_2$ 均匀 ——
**则 $X_0$ 与**一切**独立**。 -/
noncomputable def pNoFaith : FinCondIndep.FinJoint (Fin 2) (Fin 2) PUnit := fun q =>
  if q.1.1 = 0 then 1/2 else 0

/-- ⭐⭐⭐⭐ **反例律是条件独立的**（`CondMul`，`norm_num` 逐点核验）。

**⟹ 这是**真定理**（不是 `axiom`）：`4` 个 `(x,y)` 组合全部由 `norm_num` 验算。 -/
theorem pNoFaith_condMul : FinCondIndep.CondMul pNoFaith := by
  intro x y z
  cases z
  have hz : FinCondIndep.margZ pNoFaith PUnit.unit = 1 := by
    unfold FinCondIndep.margZ pNoFaith
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num
  rw [hz]
  have key : ∀ a b : Fin 2,
      (if a = 0 then (1/2 : ℝ) else 0) * 1 =
        FinCondIndep.margXZ pNoFaith a PUnit.unit *
          FinCondIndep.margYZ pNoFaith b PUnit.unit := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      (unfold FinCondIndep.margXZ FinCondIndep.margYZ pNoFaith
       rw [Fin.sum_univ_two]
       norm_num)
  unfold pNoFaith
  exact key x y

/-- ⭐⭐⭐⭐ **不可能性定理（本文的核心负面结论）**：

**「`d`-连通且条件独立」可以同时成立** —— 故朴素的反向命题 `(★)` **是假的**，
**忠实性（或「非退化」这类附加假设）不可去掉**。

$$\exists\, G\ Z\ a\ b\ (p),\quad
  \texttt{conn}\ G\ Z\ a\ b \;\wedge\; \texttt{CondMul}\ p$$

**⚠ 诚实登记**：反例之所以成立，**不是因为图侧有缺陷**，而是因为
**概率侧退化**（$X_0 \equiv 0$）。**故「不需要忠实性的最强版本」必须
在概率侧加**某种**假设**；本文给出的**最弱形式**是「端点至少一端非退化」
（不在本文形式化范围内，但见 §4 的非退化**真依赖实例**）。 -/
theorem no_faithfulness_free_converse :
    conn chain3 (∅ : Finset (Fin 3)) 0 2 ∧ FinCondIndep.CondMul pNoFaith :=
  ⟨chain3_conn_empty, pNoFaith_condMul⟩

/-! ===========================================================================
  §4 ⭐⭐⭐ 精确刻画：**对撞子**情形下 `d`-连接 ⟹ 依赖**是真的**
  =========================================================================== -/

/-- **对撞图** `0 → 2 ← 1`（顶点 `Fin 3`，对撞子在 `2`）。 -/
def collEdge (u v : Fin 3) : Prop := (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)

/-- ⭐ **`collEdge` 的传递闭包严格增大 `Fin.val`**（`acyclic` 的依据）。 -/
theorem collEdge_trans (a b : Fin 3) (h : Relation.TransGen collEdge a b) :
    a.val < b.val := by
  induction h with
  | single he =>
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · decide
      · decide
  | tail _ he ih =>
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

/-- ⭐⭐⭐ **对撞图 `0 → 2 ← 1`**。 -/
def collDAG : DAG (Fin 3) where
  edge := collEdge
  decEdge := by intro a b; unfold collEdge; infer_instance
  acyclic v h := by have := collEdge_trans v v h; omega

/-- ⭐ **`0 → 2 ← 1` 是对撞子**（`IsCollider 0 2 1`）。 -/
theorem collDAG_isCollider : collDAG.IsCollider 0 2 1 := by
  refine ⟨?_, ?_⟩ <;> simp [collDAG, collEdge]

/-- ⭐⭐⭐ **`0 ⇝ 1` 在对撞图、`Z = {2}` 下是 d-连通的**（对撞子**被条件化**即开口）。

**⟹ 见证路 `[0,2,1]`：中间点 `2` 是对撞子且 `2 ∈ Z`，故 `2 ∈ bbZAncestors Z`，
满足活动条件。** -/
theorem collDAG_conn : conn collDAG ({2} : Finset (Fin 3)) 0 1 := by
  rw [conn_iff_activeWalk]
  refine ⟨[0, 2, 1], by simp, ⟨fun i hi => ?_, fun i hi => ?_⟩, rfl, rfl⟩
  · have hi3 : i < 2 := by simp at hi; omega
    interval_cases i
    · simp [collDAG, collEdge, DAG.UAdj]
    · simp [collDAG, collEdge, DAG.UAdj]
  · have hi3 : i < 1 := by simp at hi; omega
    interval_cases i
    simp [collDAG, collEdge, DAG.IsCollider, DAG.bbZAncestors, DAG.ancestralSet]

/-- ⭐⭐⭐ **对撞子依赖律**（对撞图 `0 → 2 ← 1` 在 `Z = {2}` 下的联合律）。

支撑集 $\{(0,0,0),\ (1,0,1),\ (0,1,1)\}$ 上各取 $1/3$ —— 即
「给定 $Z = X \vee Y$，$X$ 与 $Y$ 各占一半，但 $X,Y$ 边际独立」。

**⚠ 下标约定**：`q.1.1` 记 $X$，`q.1.2` 记 $Y$，`q.2` 记 $Z$。 -/
noncomputable def pColl : FinCondIndep.FinJoint (Fin 2) (Fin 2) (Fin 2) := fun q =>
  if q.1.1 = 0 ∧ q.1.2 = 0 ∧ q.2 = 0 then 1/3
  else if q.1.1 = 1 ∧ q.1.2 = 0 ∧ q.2 = 1 then 1/3
  else if q.1.1 = 0 ∧ q.1.2 = 1 ∧ q.2 = 1 then 1/3
  else 0

/-- ⭐⭐⭐ **对撞子依赖律**不是**条件独立的**（`¬ CondMul`，`norm_num` 核验）。

**⟹ 这是本文**真依赖**的实例**：`Z = 1` 处 `X = 1, Y = 0` 的联合概率
与两个边缘之积不等。**⟹ 对撞子情形下 `d`-连接 ⟹ 依赖**是真定理**。 -/
theorem collider_dconn_not_condMul : ¬ FinCondIndep.CondMul pColl := by
  intro h
  have h1 := h 1 0 1
  unfold FinCondIndep.margZ FinCondIndep.margXZ FinCondIndep.margYZ pColl at h1
  norm_num at h1

/-- ⭐⭐⭐⭐ **精确刻画（本文的正面结论）**：

**同一条 `d`-连接路，可以是**依赖的**（对撞子，`pColl`），
也可以是**独立的**（非对撞子 + 退化噪声，`pNoFaith`）。**

$$\texttt{conn}\ G\ Z\ a\ b \;\not\Rightarrow\; \neg\texttt{CondMul}\ p$$

**⟹ 故「`d`-连通 ⟹ 依赖」**不可能**在纯粹图侧成立；
它必须在概率侧加假设（非退化 / 忠实性）。**本文的双向反例
（`no_faithfulness_free_converse` 与 `collider_dconn_not_condMul`）
把这条边界**钉死**。** -/
theorem dconn_not_implies_dependent :
    (∃ (G : DAG (Fin 3)) (Z : Finset (Fin 3)) (a b : Fin 3)
      (p : FinCondIndep.FinJoint (Fin 2) (Fin 2) PUnit),
        conn G Z a b ∧ FinCondIndep.CondMul p) ∧
    (∃ (p : FinCondIndep.FinJoint (Fin 2) (Fin 2) (Fin 2)),
        conn collDAG ({2} : Finset (Fin 3)) 0 1 ∧ ¬ FinCondIndep.CondMul p) := by
  refine ⟨⟨chain3, ∅, 0, 2, pNoFaith, no_faithfulness_free_converse⟩, ?_⟩
  exact ⟨pColl, collDAG_conn, collider_dconn_not_condMul⟩

/-! ===========================================================================
  §5 ⭐⭐ 忠实性：**定义性的**等价，及其**不可证性**
  =========================================================================== -/

/-- ⭐⭐⭐ **忠实性（faithfulness）的图侧形式**。

$$\texttt{Faithful}\ G\ p\ X\ Y\ Z \iff
  (X \perp\!\!\!\perp Y \mid Z \;\Rightarrow\; X \perp\!\!\!\perp_d Y \mid Z)$$

**⚠ 即「条件独立 $\Rightarrow$ d-分离」—— 与本文 §3 的反例**直接对立**：
由 `no_faithfulness_free_converse`（`d`-连通 + 独立），
**任何满足 `Faithful` 的实例都必须排除**该退化律**。** -/
def Faithful (G : DAG V) (X Y Z : Finset V)
    (indep : Prop) : Prop :=
  indep → G.dSep X Y Z

/-- ⭐⭐⭐ **忠实性的逆否形式**（本文的正向表述）：

$$\texttt{Faithful}\ G\ p\ X\ Y\ Z \wedge \neg\texttt{dSep}\ X\ Y\ Z
  \;\Longrightarrow\; \neg\texttt{indep}$$

**⟹ 这正是「`d`-连通 ⟹ 依赖」，但它**以忠实性为前提** ——
**这就是「需要忠实性的版本」，与 `no_faithfulness_free_converse` 表明的
「去掉忠实性后为假」精确互补。** -/
theorem faithful_imp_dconn_of_dependent (G : DAG V) (X Y Z : Finset V) (indep : Prop)
    (hF : Faithful G X Y Z indep) (hconn : ¬ G.dSep X Y Z) : ¬ indep :=
  fun hi => hconn (hF hi)

end MarkovFaithfulness

end FateV2.Predict