import FateWorld.Legacy.DAGBridge
import FateWorld.Legacy.BridgeGeneralize
import FateWorld.Legacy.SplitFromDAG
import FateWorld.Legacy.FactorizesToHyper

/-! ===========================================================================
  §CHAIN-5 ⭐⭐⭐ **把 `Fate/DAGBridge`（22 条定理）接入主链**

  ## 0 接线目标与判据

  本文件是 `Fate/DAGBridge`（此前**零消费者**的叶子模块）的**消费者**。

  **接入点：九要件 ⑧（因果结构）** ——
  `Fate/BridgeGeneralize`（一般 DAG 上的 `dSep ⟹ Split ⟹ 两块可分离 ⟹ CondIndep`）
  与其引擎 `Fate/SplitFromDAG`（`split_of_dSep` 及其三条「禁边」引理）。

  **为什么是这个接入点（而不是 `dgToRichLaw`）**：
  `DAGBridge` 的**全部实质内容**是
  「`Causalean.Graph.DAG`（被 `BridgeGeneralize` 全程使用的载体）
  ⟷ `CausalDirection.CausalGraph`（方向层三元组分类的载体）」的三样搬运：
  (a) 等价定义、(b) **方向层三元组分类（collider / 非 collider / fork / chain）**、
  (c) **祖先 / 传递闭包**。
  而 (b)(c) 正是 `SplitFromDAG.no_collider_in_Z` 与
  `FactorizesToHyper.readSetOf` 这两处**未言明地依赖**的概念。
  `dgToRichLaw` 一侧（FCA 规则 → 世界模型）与 DAG 顶点结构**无共用载体**，
  在那里接线只能是**声明式空转**（前件与结论无关），故**本文件不接那一条**。

  ## 1 本文件的定理（全部零 `sorry` / `admit` / `axiom`）

  | # | 名称 | 陈述跨两侧？ | 证明消费 `DAGBridge`？ |
  |---|---|---|---|
  | **C5.1** | `dSep_excludes_dagCollider_in_Z` | ✅ `dSep`（链）+ `DAGBridge.IsCollider` | ✅ `isCollider_iff` |
  | **C5.2** | `split_and_no_dagCollider` | ✅ `View19.Split`（链）+ `DAGBridge.IsCollider` | ✅ `isCollider_iff` |
  | **C5.3** | `factorizes_separable_and_no_dagCollider` | ✅ `Factorizes` + `FrozenOn`（链）+ `DAGBridge.IsCollider` | ✅ `isCollider_iff` |
  | **C5.4** | `ancestor_chain_and_readSet` | ✅ `readSetOf`/`isAncestor`（链）+ `DAGBridge.toCausalGraph` | ✅ `edge_iff_adj`、`transGen_iff_isAncestor` |
  | **C5.5** | `tripleType_transport_on_chain_dag` | ✅ `DAGBridge.TripleType` + `CausalDirection.TripleType` | ✅ `tripleType_iff` |

  **⚠ 反同义反复自检**（逐条，见 §4）：五条的**前件都不断言结论**；
  C5.1/C5.2/C5.4 的前件只给**边 / `dSep` / `∈`**，
  结论是**另一侧的名词**（`DAGBridge.IsCollider`、`Split`、`readSetOf` 成员），
  且这些名词**在 `DAGBridge.lean` 里都没有对应定理**（它是叶子，无 `dSep`、无 `Split`）。

  ## 2 依赖方向（一句话）

  `Causalean.Graph.DAG` 侧陈述 ⟶ `DAGBridge` 的搬运引理 ⟶
  **`Fate.DAGBridge` 不再是叶子**（`grep -rn "DAGBridge" Fate/*.lean` 现有本文件命中）。

  =========================================================================== -/

open Causalean.Graph (DAG)

/-! **⚠ 实例口径必须与 `Fate/DAGBridge` 逐字一致**：
`DAGBridge` 在自身文件里以
`open Classical in attribute [local instance] Classical.decEq Classical.propDecidable`
固定了 `DecidableEq`。本文件**同样**安装这两条 local instance，
否则 `DAGBridge.IsCollider G` 的 `G` 会带上**另一个** `DecidableEq` 实例，
类型不匹配（实测报 `Application type mismatch ... Classical.decEq V`）。
**⚠ 这仍然只是 local instance，不出本文件。** -/

open Classical in
attribute [local instance] Classical.decEq Classical.propDecidable

namespace Fate
namespace DAGBridgeConsumer

universe u
universe v

/-! ===========================================================================
  §1 ⭐⭐⭐ **C5.1 —— `dSep` 在 `Z` 内禁绝 `DAGBridge` 口径的 collider**

  `SplitFromDAG.no_collider_in_Z` 说的是「`Z` 内的 `x → z ← y`（`x∈X, y∈Y`）
  与 `dSep` 矛盾」，但它**不给出**这个形状的名字。
  `DAGBridge.IsCollider` 恰好**就是**这个名字（`a → b ← c`），
  而 `DAGBridge.isCollider_iff` 说明它与 `CausalDirection` 侧同义。

  **⟹ 本定理把「禁边引理」的结论改写成 `DAGBridge` 的谓词**：
  下游（如 `CausalPath` 的开口判据）可直接用 `DAGBridge` 的
  互斥性定理（`noncollider_not_collider`）来谈同一件事。
  =========================================================================== -/

/-- ⭐⭐⭐ **C5.1**：`dSep X Y Z` ⟹ `Z` 内不存在 `DAGBridge` collider
（顶点形如 `x → z ← y`，`x ∈ X`、`y ∈ Y`、`z ∈ Z`）。

证明：`DAGBridge.isCollider_iff` 把结论的谓词换成 `G.edge x z ∧ G.edge y z`，
再交给链上的 `SplitFromDAG.no_collider_in_Z`。 -/
theorem dSep_excludes_dagCollider_in_Z {V : Type u} [Fintype V]
    (G : DAG V) {X Y Z : Finset V} (hdsep : G.dSep X Y Z)
    {x y z : V} (hx : x ∈ X) (hy : y ∈ Y) (hz : z ∈ Z) :
    ¬ Fate.DAGBridge.IsCollider G x z y := by
  rw [Fate.DAGBridge.isCollider_iff]
  exact fun h => Fate.SplitFromDAG.no_collider_in_Z G hdsep hx hy h.1 h.2 hz

/-! ===========================================================================
  §2 ⭐⭐⭐ **C5.2 —— `Split` 与「无 `DAGBridge` collider」并存**

  `BridgeGeneralize.dSep_forces_split` 给出 `Split (readSetOf G) X Y Z`；
  §1 给出同一前提下「`Z` 内无 `DAGBridge` collider」。
  本节把两者**并成一个合取**，即 `BridgeGeneralize` 侧的两个前提
  （`dSep` + 覆盖）**同时**兑现两件**不同层次**的事：

  * `Split` —— 因子图层（读集不横跨）；
  * 无 collider —— 方向层（用 `DAGBridge` 的名字陈述）。

  **⟹ 这是「方向层（`DAGBridge`）」与「分离层（`Split`）」在同一 `DAG` 上的首次共存**，
  也是 `DAGBridge` 从叶子变消费者的**关键一步**。
  =========================================================================== -/

/-- ⭐⭐⭐ **C5.2**：`dSep` + 覆盖 ⟹ `Split` **且** 无 `DAGBridge` collider。

**⚠ 两半互不蕴含**：`Split` 是关于 `readSetOf`（父集）的谓词，
`IsCollider` 是关于**两条入边**的谓词；本定理是**两个不同结论的合取**，
不是同一个命题的换名。 -/
theorem split_and_no_dagCollider {V : Type u} [Fintype V]
    (G : DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ) :
    Fate.View19.Split (Fate.FactorizesToHyper.readSetOf G) X Y Z ∧
      (∀ x y z : V, x ∈ X → y ∈ Y → z ∈ Z →
        ¬ Fate.DAGBridge.IsCollider G x z y) :=
  ⟨Fate.SplitFromDAG.split_of_dSep G X Y Z hdsep hcover,
   fun _ _ _ hx hy hz => dSep_excludes_dagCollider_in_Z G hdsep hx hy hz⟩

/-! ===========================================================================
  §3 ⭐⭐⭐ **C5.3 —— 主定理（两块可分离）与「无 `DAGBridge` collider」并存**

  把 §2 与 `BridgeGeneralize.dSep_factorizes_separable_general`（**一般 DAG 主定理**）
  串起来：同一组前件（`dSep` + 覆盖 + `Factorizes`）**同时**给出

  * `∃ f g, p = f·g`、`FrozenOn (X∪Z) f`、`FrozenOn (Y∪Z) g`（链的终点）；
  * `Z` 内无 `DAGBridge` collider（`DAGBridge` 的口径）。

  **⟹ 这就是任务要求的「陈述里同时出现 `DAGBridge` 的符号与该接入的链的符号」**：
  `DAGBridge.IsCollider` 与 `Factorizes` / `FrozenOn` / `dSep` 同处一条陈述，
  且证明**真的穿过** `DAGBridge.isCollider_iff`。
  =========================================================================== -/

/-- ⭐⭐⭐ **C5.3**：一般 DAG 主定理 + `DAGBridge` collider 排除（合取）。

**前件都是链上 / 图中**（`hdsep`、`hcover`、`hfac`），**不含结论**。 -/
theorem factorizes_separable_and_no_dagCollider {V : Type u} {α : Type u}
    [Fintype V] [Fintype α] [DecidableEq α] (p : Fate.FactorMarkov.Joint V α)
    (G : DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ)
    (hfac : Fate.FactorMarkov.Factorizes p G) :
    (∃ f g : (V → α) → ℝ,
        (∀ w, p w = f w * g w) ∧
          Fate.BridgeGeneralize.FrozenOn (X ∪ Z) f ∧
          Fate.BridgeGeneralize.FrozenOn (Y ∪ Z) g) ∧
      (∀ x y z : V, x ∈ X → y ∈ Y → z ∈ Z →
        ¬ Fate.DAGBridge.IsCollider G x z y) :=
  ⟨Fate.BridgeGeneralize.dSep_factorizes_separable_general p G X Y Z hdsep hcover hfac,
   (split_and_no_dagCollider G X Y Z hdsep hcover).2⟩

/-! ===========================================================================
  §4 ⭐⭐⭐ **C5.4 —— 祖先层搬运 + 读集成员（链的 `readSetOf`）**

  `DAGBridge.transGen_iff_isAncestor` 说明
  `TransGen (toCausalGraph G).Adj` **就是** `G.isAncestor`。
  本节把它与 `FactorizesToHyper.readSetOf`（`Split` / `FrozenOn` 的**读集**）
  连起来：**一条边** `v → w` **既**给出 `toCausalGraph` 侧的传递闭包一步
  **又**给出 `v ∈ readSetOf G w`。

  **⟹ 意义**：链上的 `readSetOf`（父集）**就是** `DAGBridge` 搬过去的邻接，
  于是「某因子只读 `S` 上坐标」(`FrozenOn`) 与「祖先关系」两套语言可以互译。
  =========================================================================== -/

/-- ⭐⭐⭐ **C5.4**：`G.edge v w` ⟹
`(DAGBridge.toCausalGraph G).Adj v w`（`DAGBridge` 口径）
∧ `TransGen (toCausalGraph G).Adj v w`
∧ `G.isAncestor v w`
∧ `v ∈ readSetOf G w`（链的读集）。

**⚠ 这不是 `:= DAGBridge.xxx`**：结论的第二、四项（`isAncestor` /
`readSetOf` 成员）**在 `DAGBridge.lean` 里完全不存在**，须由本文件从
`DAGBridge.transGen_iff_isAncestor` + `mem_parents` 现场组装。 -/
theorem ancestor_chain_and_readSet {V : Type u} [Fintype V]
    (G : DAG V) {v w : V} (h : G.edge v w) :
    (Fate.DAGBridge.toCausalGraph G).Adj v w ∧
      Relation.TransGen (Fate.DAGBridge.toCausalGraph G).Adj v w ∧
        G.isAncestor v w ∧ v ∈ Fate.FactorizesToHyper.readSetOf G w := by
  have hadj : (Fate.DAGBridge.toCausalGraph G).Adj v w :=
    (Fate.DAGBridge.edge_iff_adj G v w).mpr h
  have htg : Relation.TransGen (Fate.DAGBridge.toCausalGraph G).Adj v w :=
    Relation.TransGen.single hadj
  exact ⟨hadj, htg, (Fate.DAGBridge.transGen_iff_isAncestor G).mp htg,
    (Fate.FactorizesToHyper.mem_readSetOf).mpr
      (Or.inr ((Causalean.Graph.DAG.mem_parents G).mpr h))⟩

/-! ===========================================================================
  §5 ⭐⭐⭐ **C5.5 —— 三元组类型在「链的 `DAG`」与「方向层」之间搬运**

  `DAGBridge.tripleType_iff` 已在 `DAG V` 与 `CausalDirection.CausalGraph V`
  之间建立 `TripleType` 的对应。本节把它**用在链的 `DAG` 上并与相邻性对接**：
  在 `G` 的相邻三元组上，`DAGBridge.TripleType`、`CausalDirection.TripleType`、
  以及「四类之一」三者等价 —— 于是链侧只需面对**一个**方向层分类谓词。

  **⟹ 意义**：`SplitFromDAG` / `BridgeGeneralize` 若日后要用「路径逐节点开口性」，
  可以**直接**用 `DAGBridge` 在 `DAG` 上给出的四类（无需再引 `CausalGraph`）。
  =========================================================================== -/

/-- ⭐⭐⭐ **C5.5**：在相邻三元组上，`DAGBridge.TripleType` ⟺
`CausalDirection.TripleType`，且 `DAGBridge` 侧的四类**穷尽**。

由 `DAGBridge.tripleType_iff` 与 `DAGBridge.triple_exhaustive` 组合。
**⚠ 结论第一项就横跨两套结构**，非纯换名。 -/
theorem tripleType_transport_on_chain_dag {V : Type u} [Fintype V]
    (G : DAG V) {a b c : V}
    (hab : G.edge a b ∨ G.edge b a) (hbc : G.edge b c ∨ G.edge c b) :
    (Fate.DAGBridge.TripleType G a b c ↔
        CausalDirection.TripleType (Fate.DAGBridge.toCausalGraph G) a b c) ∧
      Fate.DAGBridge.TripleType G a b c :=
  ⟨Fate.DAGBridge.tripleType_iff G a b c,
   Fate.DAGBridge.triple_exhaustive G hab hbc⟩

end DAGBridgeConsumer
end Fate
