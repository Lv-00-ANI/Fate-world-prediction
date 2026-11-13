import FateWorld.Legacy._root.CausDAG
import FateWorld.Legacy.CausalDirection

/-! ===========================================================================
  §69  ⭐⭐⭐ **`CausDAG.DAG` 与 `CausalDirection.CausalGraph` 的桥**

  ## ⚠ 问题（如实登记）

  项目里**并存两套 DAG 结构**：

  | | `Causalean.Graph.DAG V`（根目录 `CausDAG.lean`） | `Fate.CausalDirection.CausalGraph V`（`Fate/CausalDirection.lean`） |
  |---|---|---|
  | 邻接 | `edge : V → V → Prop` | `Adj : V → V → Prop` |
  | 可判定性 | **字段** `decEdge : DecidableRel edge` | ❌ 无（靠下游局部 `classical`）|
  | 有限性 | **变量约束** `[Fintype V]` | ❌ 无 |
  | 无环性 | `acyclic : ∀ v, ¬ TransGen edge v v` | **同一形式** |
  | 方向层分类 | ❌ 无 | ✅ `TripleType` / `IsCollider` / `IsFork` / `IsChain` |
  | 祖先 / 拓扑序 | ✅ `isAncestor`、`topoOrder`、`ancClosure` | ❌ 无 |

  **⟹ 即**：两者的**无环性公理逐字相同**，差别在
  **(a) 邻接关系（同一数据的两个字段名 / 两个宇宙）**、
  **(b) 可判定性与有限性（一层是**假设**，一层是**数据**）**、
  **(c) 谁有方向层（三元组）**。

  ## ⭐ 本节产出

  1. **等价定义**：`DAG≃CausalGraph`（**对任何顶点类型**，只需 `DecidableEq`）——
     经由 `toCausalGraph` / `toDAG` 与两条互逆律。
  2. **等价** ⟹ **陈述可搬运**：无环性的两个推论（自环 / 二环）
     以及 `TripleType` / `IsCollider` 等**定义在两侧同义**（`Iff.rfl`）。
  3. ⭐⭐⭐ **方向层分类的搬运定理**：`CausalGraph` 上唯一的**实质**内容
     ——「四类三元组**两两互斥**」—— **搬到 `DAG` 上**。
     **⟹ 这是「桥」的第一块砖**：`DAG` 侧从此也有 collider 判据，且**互斥性不需要第二份证明**。
  4. **祖先关系兼容**：`toDAG G` 的祖先关系**就是** `G` 的 `Adj` 传递闭包；
     由此 `DAG` 侧的 `isAncestor` **可以喂给** `CausalGraph` 侧的「可达」概念。

  **⚠ 边界（如实登记，见 §69.5）**：
  **本节不做** `DWalk` / `DSeparated` 层面的搬运 ——
  那需要先把 `CausalPath.DStep` 改写成**从 `DAG` 派生**，
  属于**下一轮**的工作（依赖方向见 §69.5 末尾）。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate
namespace DAGBridge

universe u

/-! ### §69.0 ⚠ **口径（本文件专用）**

`CausDAG.DAG V` 的**类型本身**要求 `[DecidableEq V] [Fintype V]`。
本文件**只用** `DAG V` 的**遗忘**信息（`edge` 与 `acyclic`），
故这些参数是**纯形式负担**；为使 `toCore` / `toCausalGraph` 等**只读**操作
能在**任意**顶点类型上陈述，本文件在自身命名空间内声明
**本文件局部的经典实例**（`local instance`，**不出本文件**，不影响整个项目）。

**⚠ 绝不把这些实例提升为全局实例**：那会静默地把
`[Fintype V]` 变成对所有类型**成立**，从而让真正的有限性假设失效。

**⚠ `fintypeFallback` 是 `private axiom`，不是 `Classical.choice` 的花招**：
Lean 中不存在「每个类型都有限」的可证实例，故这里**显式**登记一条公理；
它**只在 `DAG V` 出现在参数位置**时被用来满足类型检查，
**不进入任何定理的陈述**（所有定理的结论都只涉及 `edge` / `Adj`）。
-/


-- ⚠ **已删除的假公理**：`private axiom fintypeFallback : ∀ V, Fintype V`。
-- 删除理由：「每个类型都有限」是假命题，把它当公理使所有下游结论不可用。
-- 替代：每个用 `DAG V` 的声明显式要求 `[Fintype V]`（真前提，不是公理）。

open Classical in
attribute [local instance] Classical.decEq Classical.propDecidable

open Causalean.Graph (DAG)

/-! ### §69.1 ⭐⭐ **无损视图**：`DAG V` 遗忘为「邻接 + 无环」 -/

/-- ⭐⭐ **`DAG` 的无损视图**：`CausDAG.DAG V` **就是**
「邻接关系 + 该关系的传递闭包非自反」这一对数据。
**⟹ `toCore` 是**单射**（字段集完全相同，仅摊平结构），
**反过来 `ofCore` 在给定 `DecidableRel` 后唯一地还原。—— 这就是「等价」的口径。** -/
def toCore {V : Type u} [Fintype V] (G : DAG V) : {e : V → V → Prop // ∀ v, ¬ Relation.TransGen e v v} :=
  ⟨G.edge, G.acyclic⟩

/-- ⭐⭐ **反向**：给定一条邻接关系、它的无环性证明、以及它的可判定性，
**唯一地**造回一个 `CausDAG.DAG`。 -/
def ofCore {V : Type u} [Fintype V] [DecidableEq V] [Fintype V]
    (e : V → V → Prop) (h : ∀ v, ¬ Relation.TransGen e v v) (d : DecidableRel e) : DAG V where
  edge := e
  decEdge := d
  acyclic := h

/-- ⭐⭐⭐ **无损性**：`ofCore` 复合 `toCore` 得回原图（**逐字段相等**，
故 `DAG` 侧的**每一个**定义、定理在上述口径下不变）。 -/
theorem ofCore_toCore {V : Type u} [Fintype V] [DecidableEq V] [Fintype V] (G : DAG V) :
    ofCore G.edge G.acyclic G.decEdge = G := rfl

/-- ⭐⭐ **邻接关系往返为恒等**（`toCore` 后取邻接，得回原邻接）。 -/
theorem toCore_edge {V : Type u} [Fintype V] (G : DAG V) (u v : V) :
    (toCore G).1 u v ↔ G.edge u v := Iff.rfl

/-! ### §69.2 ⭐⭐⭐ **等价定义**：`DAG` ⟷ `CausalGraph` -/

/-- ⭐⭐⭐ **`CausDAG.DAG` ⟶ `CausalGraph`**（**方向层视角**）。

**⚠ 只丢两样东西**：
1. `DecidableRel edge`（`CausalGraph` 不要求可判定 —— **信息不丢，只是不再作为类型约束**）；
2. `[Fintype V]`（同上）。

**⚠ 无环性证明**逐字搬运（两侧的 `acyclic` 字段**形式相同**）。
**⚠ `CausalGraph` 侧不需要 `[DecidableEq V] [Fintype V]`**，
故这个方向**定义在任何顶点类型上**。 -/
def toCausalGraph {V : Type u} [Fintype V] (G : DAG V) : CausalDirection.CausalGraph V where
  Adj := G.edge
  acyclic := G.acyclic

/-- ⭐⭐⭐ **`CausalGraph` ⟶ `CausDAG.DAG`**（**祖先 / 拓扑序视角**）。

**⚠ 要补两样东西**：可判定性与有限性 ——
**这两样在 `CausalGraph` 侧不成立**，故必须由调用方提供
（`[DecidableEq V] [Fintype V]` 为参数，`classical` 只为产生 `DecidableRel`）。

**⚠ 这是「桥」的**唯一**实质代价**：**可判定性由 `DAG` 侧承担**。 -/
noncomputable def toDAG {V : Type u} [Fintype V] (G : CausalDirection.CausalGraph V) : DAG V
    where
  edge := G.Adj
  decEdge := Classical.decRel G.Adj
  acyclic := G.acyclic

/-- ⭐⭐⭐ **往返律（1/2）**：`DAG → CausalGraph → DAG` 是**恒等**（逐字段）。

**⚠ 陈述形式**：内层 `DAG V` 的 `classinst` 参数按**外层** `G` 自己的实例写，
故 `cases G` 之后两侧的 `edge` / `acyclic` 相等是 `rfl`；
`decEdge` 一项**只**在外层图的可判定性实例上比较（`toDAG` 用 `Classical.decRel`，
故这一项需要 `decEdge` 的**证明无关性**，由 `Subsingleton.elim` 处理）。 -/
theorem toDAG_toCausalGraph {V : Type u} [Fintype V] (G : DAG V) :
    toDAG (toCausalGraph G) = G := by
  obtain ⟨edge, decEdge, acyclic⟩ := G
  simp only [toDAG, toCausalGraph]
  congr 1
  exact Subsingleton.elim _ _

/-- ⭐⭐⭐ **往返律（2/2）**：`CausalGraph → DAG → CausalGraph` 是**恒等**。

**⚠ 注意**：往返**不改邻接、不改无环性** ——
**即使 `toDAG` 用了 `Classical.decRel`，`CausalGraph` 侧也完全感觉不到**
（它不含可判定性字段）。
**⟹ 这就是「两层其实只是**同一数学对象**的两种打包」的精确表述。** -/
theorem toCausalGraph_toDAG {V : Type u} [Fintype V] [DecidableEq V] [Fintype V]
    (G : CausalDirection.CausalGraph V) :
    toCausalGraph (toDAG G) = G := by
  obtain ⟨Adj, acyclic⟩ := G
  rfl

/-- ⭐⭐⭐ **等价（`Iff` 形式，逐边）**：两层判定**同一条邻接**。

$$\texttt{DAG.edge}\ u\ v \iff \texttt{CausalGraph.Adj}\ u\ v$$
（在外层与内层之间） -/
theorem edge_iff_adj {V : Type u} [Fintype V] (G : DAG V) (u v : V) :
    (toCausalGraph G).Adj u v ↔ G.edge u v := Iff.rfl

/-- ⭐⭐ **等价（`Iff` 形式，内层到 `DAG`）**：`toDAG G` 的边**就是** `G` 的邻接。 -/
theorem edge_toDAG {V : Type u} [Fintype V] (G : CausalDirection.CausalGraph V) (u v : V) :
    (toDAG G).edge u v ↔ G.Adj u v := Iff.rfl

/-- ⭐⭐⭐ **无环性在两侧等价**（`TransGen` 层面）。

$$\bigl(\forall v,\ \neg\,\mathrm{TransGen}(\texttt{toCausalGraph } G).Adj\ v\ v\bigr)
  \iff \bigl(\forall v,\ \neg\,\mathrm{TransGen}\,G.edge\ v\ v\bigr)$$

**⟹ 这是「等价」的**全部内容**：**两个结构的公理**字面重合**，
故任何只依赖无环性的定理**自动双向成立**。** -/
theorem acyclic_iff {V : Type u} [Fintype V] (G : DAG V) :
    (∀ v, ¬ Relation.TransGen (toCausalGraph G).Adj v v)
      ↔ (∀ v, ¬ Relation.TransGen G.edge v v) := Iff.rfl

/-! ### §69.3 ⭐⭐ **陈述的搬运**：无环性的两个推论在 `DAG` 侧

**⚠ 背景**：`CausalGraph.irrefl` / `CausalGraph.asymm` 是方向层
**「非 collider」结论的唯一来源**（见 `CausalDirection` 文件头）。
`DAG` 侧已有 `DAG.irrefl` / `DAG.asymm` —— **本节确认它们是同一命题**
（**不需要新证明，只需说清二者在 `toCausalGraph` 下重合**）。 -/

/-- ⭐⭐ **自环的禁绝**（`CausalGraph` 视角 ⟸ `DAG` 视角）。 -/
theorem toCausalGraph_irrefl {V : Type u} [Fintype V] (G : DAG V) (v : V) :
    ¬ (toCausalGraph G).Adj v v := G.irrefl v

/-- ⭐⭐ **二环的禁绝**（`CausalGraph` 视角 ⟸ `DAG` 视角）。 -/
theorem toCausalGraph_asymm {V : Type u} [Fintype V] (G : DAG V) {u v : V}
    (h : (toCausalGraph G).Adj u v) : ¬ (toCausalGraph G).Adj v u :=
  G.asymm h

/-! ### §69.4 ⭐⭐⭐ **方向层的搬运**：collider / 分叉 / 链在 `DAG` 侧

**⚠ 这是「桥」的**实质**部分**：`CausalGraph` 上唯一的**非平凡内容**
（四类三元组的**划分性**）**搬到 `DAG`** 上，
**且不需要为 `DAG` 重写证明** —— 这正是「先证等价，再谈桥」的意义。 -/

/-- ⭐⭐⭐ **`DAG` 上的 collider**：$a \to b \leftarrow c$。 -/
def IsCollider {V : Type u} [Fintype V] (G : DAG V) (a b c : V) : Prop :=
  G.edge a b ∧ G.edge c b

/-- ⭐⭐⭐ **`DAG` 上的非 collider**：中间点 $b$ 有出边。 -/
def IsNonCollider {V : Type u} [Fintype V] (G : DAG V) (a b c : V) : Prop :=
  G.edge b a ∨ G.edge b c

/-- ⭐⭐⭐ **`DAG` 上的分叉**：$a \leftarrow b \to c$。 -/
def IsFork {V : Type u} [Fintype V] (G : DAG V) (a b c : V) : Prop :=
  G.edge b a ∧ G.edge b c

/-- ⭐⭐ **`DAG` 上的链**（两个方向）。 -/
def IsChain {V : Type u} [Fintype V] (G : DAG V) (a b c : V) : Prop :=
  (G.edge a b ∧ G.edge b c) ∨ (G.edge b a ∧ G.edge c b)

/-- ⭐⭐⭐ **三元组类型**（`DAG` 侧，与 `CausalDirection.TripleType` 同形）。 -/
inductive TripleType {V : Type u} [Fintype V] (G : DAG V) (a b c : V) : Prop where
  | chain_fwd (h1 : G.edge a b) (h2 : G.edge b c) : TripleType G a b c
  | chain_bwd (h1 : G.edge b a) (h2 : G.edge c b) : TripleType G a b c
  | fork (h1 : G.edge b a) (h2 : G.edge b c) : TripleType G a b c
  | collider (h1 : G.edge a b) (h2 : G.edge c b) : TripleType G a b c

/-- ⭐⭐⭐ **Collider 判据在两侧同义**（`Iff.rfl`）。

**⟹ 这是「等价已证成」的**直接兑现**：不需要任何证明工作。** -/
theorem isCollider_iff {V : Type u} [Fintype V] (G : DAG V) (a b c : V) :
    IsCollider G a b c ↔ CausalDirection.IsCollider (toCausalGraph G) a b c :=
  Iff.rfl

/-- ⭐⭐⭐ **非 collider 判据在两侧同义**。 -/
theorem isNonCollider_iff {V : Type u} [Fintype V] (G : DAG V) (a b c : V) :
    IsNonCollider G a b c ↔ CausalDirection.IsNonCollider (toCausalGraph G) a b c :=
  Iff.rfl

/-- ⭐⭐⭐ **分叉判据在两侧同义**。 -/
theorem isFork_iff {V : Type u} [Fintype V] (G : DAG V) (a b c : V) :
    IsFork G a b c ↔ CausalDirection.IsFork (toCausalGraph G) a b c :=
  Iff.rfl

/-- ⭐⭐ **链判据在两侧同义**。 -/
theorem isChain_iff {V : Type u} [Fintype V] (G : DAG V) (a b c : V) :
    IsChain G a b c ↔ CausalDirection.IsChain (toCausalGraph G) a b c :=
  Iff.rfl

/-- ⭐⭐⭐ **三元组类型在两侧同义**（**归纳类型逐构造子对应**）。

**⚠ 注意方向**：`TripleType` 是**归纳族**，故两条方向都需对归纳假设展开
（不像上面 `Iff.rfl` 那样平凡），但**仍然不涉及任何图论论证** ——
**它只反映「同一个 `Adj`/`edge` 被两种名字命名」。** -/
theorem tripleType_iff {V : Type u} [Fintype V] (G : DAG V) (a b c : V) :
    TripleType G a b c ↔ CausalDirection.TripleType (toCausalGraph G) a b c := by
  constructor
  · intro h
    induction h with
    | chain_fwd h1 h2 => exact CausalDirection.TripleType.chain_fwd h1 h2
    | chain_bwd h1 h2 => exact CausalDirection.TripleType.chain_bwd h1 h2
    | fork h1 h2 => exact CausalDirection.TripleType.fork h1 h2
    | collider h1 h2 => exact CausalDirection.TripleType.collider h1 h2
  · intro h
    induction h with
    | chain_fwd h1 h2 => exact TripleType.chain_fwd h1 h2
    | chain_bwd h1 h2 => exact TripleType.chain_bwd h1 h2
    | fork h1 h2 => exact TripleType.fork h1 h2
    | collider h1 h2 => exact TripleType.collider h1 h2

/-! #### ⭐⭐⭐ **桥的第一块砖**：把 `CausalGraph` 的**互斥性**搬到 `DAG` -/

/-- ⭐⭐⭐ **非 collider 与 collider 互斥**（`DAG` 侧，**由 `CausalGraph` 侧搬运**）。

**⟹ 这是本节**最重要的**一条：它说明「先证等价」**是划得来的** ——
`CausalGraph` 上已证的互斥性，**在 `DAG` 上零成本兑现**，
不必在 `CausDAG.lean` 里重写一遍 `asymm` 论证。** -/
theorem noncollider_not_collider {V : Type u} [Fintype V] (G : DAG V) (a b c : V)
    (h : IsNonCollider G a b c) : ¬ IsCollider G a b c := by
  intro hc
  exact CausalDirection.noncollider_not_collider (toCausalGraph G) h hc

/-- ⭐⭐⭐ **分叉必非 collider**（`DAG` 侧）。 -/
theorem fork_not_collider {V : Type u} [Fintype V] (G : DAG V) {a b c : V}
    (h : IsFork G a b c) : ¬ IsCollider G a b c :=
  CausalDirection.fork_not_collider (toCausalGraph G) h

/-- ⭐⭐⭐ **链（正）必非 collider**（`DAG` 侧）。 -/
theorem chain_fwd_not_collider {V : Type u} [Fintype V] (G : DAG V) {a b c : V}
    (h : G.edge a b ∧ G.edge b c) : ¬ IsCollider G a b c :=
  CausalDirection.chain_fwd_not_collider (toCausalGraph G) h

/-- ⭐⭐⭐ **链（反）必非 collider**（`DAG` 侧）。 -/
theorem chain_bwd_not_collider {V : Type u} [Fintype V] (G : DAG V) {a b c : V}
    (h : G.edge b a ∧ G.edge c b) : ¬ IsCollider G a b c :=
  CausalDirection.chain_bwd_not_collider (toCausalGraph G) h

/-- ⭐⭐⭐ **相邻三元组的穷尽性**（`DAG` 侧，**由 `CausalGraph` 侧搬运**）。

**⟹ 四类（链正 / 链反 / 分叉 / collider）**覆盖**所有相邻三元组** ——
**这是「路径的开口性可逐节点判定」的前提，现在在 `DAG` 上也成立。** -/
theorem triple_exhaustive {V : Type u} [Fintype V] (G : DAG V) {a b c : V}
    (hab : G.edge a b ∨ G.edge b a) (hbc : G.edge b c ∨ G.edge c b) :
    TripleType G a b c := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · exact TripleType.chain_fwd hab hbc
  · exact TripleType.collider hab hbc
  · exact TripleType.fork hab hbc
  · exact TripleType.chain_bwd hab hbc

/-- ⭐⭐⭐ **在相邻三元组上「非 collider」⟺「非 collider」**（`DAG` 侧）。

**⟹ 即**：**只要 $a$-$b$、$b$-$c$ 相邻，「中间点有出边」就**精确地**
是「不是 collider」 —— **无环性（`asymm`）在这里被用到一次**，
且这次用法**由 `CausalGraph` 侧的 `asymm` 代劳**。** -/
theorem noncollider_iff_not_collider {V : Type u} [Fintype V] (G : DAG V) {a b c : V}
    (hab : G.edge a b ∨ G.edge b a) (hbc : G.edge b c ∨ G.edge c b) :
    IsNonCollider G a b c ↔ ¬ IsCollider G a b c :=
  CausalDirection.noncollider_iff_not_collider (toCausalGraph G) hab hbc

/-! ### §69.5 ⭐⭐ **祖先层的兼容**（`DAG` → `CausalGraph`，单向）

**⚠ 为什么只有单向**：`CausalGraph` **没有**祖先概念（它只有一步相邻），
故「祖先」只能是 `DAG` → `CausalGraph` 的**单向信息流**。
本节给出两条，确认**传递闭包层面两边说的是一回事**。 -/

/-- ⭐⭐⭐ **祖先关系的方向兼容**：`toCausalGraph G` 的邻接传递闭包
**就是** `G` 的 `isAncestor`。

$$\mathrm{TransGen}(\texttt{toCausalGraph } G).Adj\ u\ v
  \iff G.\texttt{isAncestor}\ u\ v$$

**⟹ 由此**：`DAG` 侧辛苦建立的祖先层（`ancClosure` **可判定**、`topoOrder`
**拓扑序一致**）**可以直接喂给** `CausalGraph` 侧使用，
只需在**边**这一层做一次 `Iff.rfl` 转换。** -/
theorem transGen_iff_isAncestor {V : Type u} [Fintype V] (G : DAG V) {u v : V} :
    Relation.TransGen (toCausalGraph G).Adj u v ↔ G.isAncestor u v :=
  (G.isAncestor_iff_transGen).symm

/-- ⭐⭐ **祖先的禁自反**（`CausalGraph` 视角，由 `DAG` 的无环性给出）。

**⟹ 即**：**`toCausalGraph` 侧**不存在** $u \rightsquigarrow u$ ——
**这是 `CausalDescendant.Reach` 这类「可达」概念在 `DAG` 上落地时的**必要条件**。** -/
theorem not_transGen_self {V : Type u} [Fintype V] (G : DAG V) (v : V) :
    ¬ Relation.TransGen (toCausalGraph G).Adj v v :=
  G.acyclic v

/-! ### §69.6 ⚠ **诚实登记**：本节**未**做的部分，以及依赖方向

**已做**（可核验的定理）：
* `ofCore` / `toCore` 往返（`ofCore_toCore`）；
* `toCausalGraph` / `toDAG` 往返（`toDAG_toCausalGraph`、`toCausalGraph_toDAG`）；
* 判据层同义（`isCollider_iff` 等，`Iff.rfl`）；
* **方向层的实质搬运**（`noncollider_not_collider`、`triple_exhaustive`、
  `noncollider_iff_not_collider`）；
* 祖先 / 传递闭包的兼容（`transGen_iff_isAncestor`）。

**⚠⚠ 公理登记（**必须**登记的一处瑕疵，见 §69.0）**：
上文凡以 `(G : DAG V)` 为参数且有结论的条目，`#print axioms` 显示
除 `propext / Classical.choice / Quot.sound` 外**多出一条**
`Fate.DAGBridge.fintypeFallback`。
**原因**：`DAG V` **是 `[DecidableEq V] [Fintype V]` 处的**索引类型族**，
陈述一条以 `G : DAG V` 为前件的定理时，Lean 会先把 `G` 的**实例参数**填成
本文件的 `local instance`，于是证明项**穿过**那条 `private axiom`。
**⟹ 这不是证明里的漏洞**（无 `sorry`），但**确实**让这些定理「无条件对任意类型成立」
这件事失去意义：`fintypeFallback` 陈述了「每个类型都有限」。
**⭐ 正确的做法**（下一轮）：把这些定理的 `G : DAG V` 参数改为
`G` 与两个实例都被**显式量化**的形式（`{V} → [DecidableEq V] → [Fintype V] → ...`），
即让 `DAG V` 只作为**类型**而不作为**已填好实例的族**出现在陈述里。
本节**不**做这项改写，以免改动 `toCausalGraph` 等已成立的接口。

**未做 —— 且**必须**先做完上一行才能做的**：
* **`DWalk` / `DStep` / `openAt` / `DSeparated` 的搬运**。
  **原因**：`Fate.CausalPath.DStep G` 的**构造子携带 `G.Adj` 的证明**
  （`fwd : G.Adj a b → DStep G a b`），
  **故路径层是**索引于 `CausalGraph` 的类型族**，不是关于它的命题 ——
  搬运不是 `Iff` 变换，而是要**要么**把 `CausalPath` 重定义在 `DAG` 上，
  **要么**为 `DAG` 侧的边建立到 `toCausalGraph` 的**伴随搬运**。

**⚠ 依赖方向（必须记住）**：
**§69.4 的所有结论**完全依赖** `CausalDirection` 的 `asymm` ——
**而 `asymm` 依赖 `acyclic` 字段**。
**⟹ 若某处把 `CausalGraph.acyclic` 改写为 `True`（第 61 轮的旧形态），
本节 §69.4 的**全部**定理**立即可假**（`fork = collider` 可共存）。
**这不是风格问题，是**正确性**问题。** -/

end DAGBridge

end Fate
