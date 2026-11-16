import FateWorld.FateV2.Predict.DoCalculus
import FateWorld.FateV2.Predict.CausalDirection
/-!
  # Predict · GraphOps

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GraphOps.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DoCalculus, CausalDirection
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §65  ⭐⭐⭐ **图操作**（$G_{\underline{X}}$ / $G_{\overline{X}}$）—— do-calculus 的前提

  ## 背景

  | 轮次 | 已做 |
  |---|---|
  | **61** | `CausalGraph`（有向图 + 无环字段）|
  | **64** | do-算子的**语义层代数** |

  **⚠ 第 64 轮的边界登记**：
  > **Pearl 的三条规则都涉及**图操作**（$G_{\underline{X}}$ / $G_{\overline{X}}$）——
  > **本项目的 `CausalGraph` 尚无删边运算**

  **⟹ 本轮实现图操作，使三条规则的**陈述**可写出。**

  ## ⭐ Pearl 的两类图操作（定义 3.2.2）

  | 记号 | 操作 | 语义 |
  |---|---|---|
  | $G_{\underline{X}}$ | **删去 $X$ 的入边** | 「$X$ 不再被其父决定」|
  | $G_{\overline{X}}$ | **删去 $X$ 的出边** | 「$X$ 不再影响其后代」|

  **⚠ $do(X=x)$ 对应的正是 $G_{\overline{X}}$** ——
  **因为干预切断 $X$ 的出边（$X$ 的影响被替换为常数）。**

  ## ⭐ 本节的产出

  | # | 内容 |
  |---|---|
  | **1** | ⭐⭐⭐ **`delIn`**：$G_{\underline{X}}$（删入边）|
  | **2** | ⭐⭐⭐ **`delOut`**：$G_{\overline{X}}$（删出边）|
  | **3** | ⭐⭐ **`delIn_adj`** / **`delOut_adj`**：邻接的展开判据 |
  | **4** | ⭐⭐⭐ **`delOut_mono`**：删边**只减不加** |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace GraphOps

universe u

variable {V : Type u}

/-! ### §65.1 ⭐⭐⭐ 删入边（$G_{\underline{X}}$） -/

/-- ⭐⭐⭐ **删入边保持无环性**（**第 68 轮补的真证明**）。

**⚠ 第 65 轮此处填的是 `acyclic := trivial`** ——
**那是**空洞的****（因为当时 `CausalGraph.acyclic` 是 `True`）。
**第 68 轮把无环性改为真条件后，此处的证明义务**浮现****。

**陈述**：**$G_{\underline{X}}$ 的传递闭包仍非自反。**

**证明思路**：**$G_{\underline{X}} \subseteq G$ 且传递闭包单调
（`Relation.TransGen.mono`）** ⟹ **$G$ 的无环性继承下来。** -/
theorem delIn_acyclic (G : CausalDirection.CausalGraph V) (X : Set V) :
    ∀ v : V, ¬ Relation.TransGen (fun a b => G.Adj a b ∧ b ∉ X) v v := by
  intro v h
  exact G.acyclic v
    (@Relation.TransGen.mono V (fun a b => G.Adj a b ∧ b ∉ X) G.Adj
      (fun a b hab => hab.1) v v h)

/-- ⭐⭐⭐ **删入边 $G_{\underline{X}}$**：**删去所有指向 $X$ 的边**。

$$\mathrm{Adj}_{G_{\underline{X}}}(a,b) :=
  \mathrm{Adj}_G(a,b) \wedge b \notin X$$

**⚠ 即**：**$X$ 中的顶点不再有入边**（「$X$ 不再被其父决定」）。** -/
def delIn (G : CausalDirection.CausalGraph V) (X : Set V) : CausalDirection.CausalGraph V where
  Adj := fun a b => G.Adj a b ∧ b ∉ X
  acyclic := delIn_acyclic G X

/-- ⭐⭐ **删入边的邻接判据**（定义性展开）。 -/
theorem delIn_adj (G : CausalDirection.CausalGraph V) (X : Set V) (a b : V) :
    (delIn G X).Adj a b ↔ G.Adj a b ∧ b ∉ X :=
  Iff.rfl

/-! ### §65.2 ⭐⭐⭐ 删出边（$G_{\overline{X}}$） -/

/-- ⭐⭐⭐ **删出边保持无环性**（**第 68 轮补的真证明**）。

**⚠ 与 `delIn_acyclic` 同理**，但此处是**删出边**。 -/
theorem delOut_acyclic (G : CausalDirection.CausalGraph V) (X : Set V) :
    ∀ v : V, ¬ Relation.TransGen (fun a b => G.Adj a b ∧ a ∉ X) v v := by
  intro v h
  exact G.acyclic v
    (@Relation.TransGen.mono V (fun a b => G.Adj a b ∧ a ∉ X) G.Adj
      (fun a b hab => hab.1) v v h)

/-- ⭐⭐⭐ **删出边 $G_{\overline{X}}$**：**删去所有从 $X$ 出发的边**。

$$\mathrm{Adj}_{G_{\overline{X}}}(a,b) :=
  \mathrm{Adj}_G(a,b) \wedge a \notin X$$

**⚠ 即**：**$X$ 中的顶点不再有出边**（「$X$ 不再影响其后代」）——
**这正是 $do(X=x)$ 的图论对应。** -/
def delOut (G : CausalDirection.CausalGraph V) (X : Set V) : CausalDirection.CausalGraph V where
  Adj := fun a b => G.Adj a b ∧ a ∉ X
  acyclic := delOut_acyclic G X

/-- ⭐⭐ **删出边的邻接判据**（定义性展开）。 -/
theorem delOut_adj (G : CausalDirection.CausalGraph V) (X : Set V) (a b : V) :
    (delOut G X).Adj a b ↔ G.Adj a b ∧ a ∉ X :=
  Iff.rfl

/-! ### §65.3 ⭐⭐⭐ 图操作的基本性质 -/

/-- ⭐⭐⭐ **删边只减不加**（**核心性质**）。

$$G_{\underline{X}} \subseteq G, \qquad G_{\overline{X}} \subseteq G$$

**⟹ 即**：**两类图操作都**只会删边**** ——
**这是「干预不创造新因果」的精确形式。** -/
theorem delIn_subset (G : CausalDirection.CausalGraph V) (X : Set V) (a b : V)
    (h : (delIn G X).Adj a b) : G.Adj a b :=
  h.1

theorem delOut_subset (G : CausalDirection.CausalGraph V) (X : Set V) (a b : V)
    (h : (delOut G X).Adj a b) : G.Adj a b :=
  h.1

/-- ⭐⭐⭐ **删出边消除了 $X$ 的出边**（**核心性质**）。

$$\forall x \in X,\ \forall b,\ \neg\,(G_{\overline{X}}).\mathrm{Adj}\,x\,b$$

**⟹ 即**：**$X$ 中的顶点在 $G_{\overline{X}}$ 中**无出边**** ——
**这是「$do(X=x)$ 切断 $X$ 的下游影响」的精确形式。** -/
theorem delOut_no_out (G : CausalDirection.CausalGraph V) (X : Set V)
    {a b : V} (ha : a ∈ X) : ¬ (delOut G X).Adj a b :=
  fun h => h.2 ha

/-- ⭐⭐⭐ **删入边消除了 $X$ 的入边**（**核心性质**）。

$$\forall a,\ \forall x \in X,\ \neg\,(G_{\underline{X}}).\mathrm{Adj}\,a\,x$$ -/
theorem delIn_no_in (G : CausalDirection.CausalGraph V) (X : Set V)
    {a b : V} (hb : b ∈ X) : ¬ (delIn G X).Adj a b :=
  fun h => h.2 hb

/-! ### §65.4 ⭐⭐ 单调性（**集合论层面**） -/

/-- ⭐⭐ **删入边关于 $X$ 的单調性**（**反单调**）。

$$X \subseteq X' \implies G_{\underline{X'}} \subseteq G_{\underline{X}}$$

**⟹ 即**：**删得越多，图越小** ——
**这是「条件集越大，图越稀疏」的精确形式。** -/
theorem delIn_anti_mono (G : CausalDirection.CausalGraph V) {X X' : Set V}
    (h : X ⊆ X') {a b : V} (hab : (delIn G X').Adj a b) : (delIn G X).Adj a b :=
  ⟨hab.1, fun hb => hab.2 (h hb)⟩

/-- ⭐⭐ **删出边关于 $X$ 的单調性**（**反单调**）。 -/
theorem delOut_anti_mono (G : CausalDirection.CausalGraph V) {X X' : Set V}
    (h : X ⊆ X') {a b : V} (hab : (delOut G X').Adj a b) : (delOut G X).Adj a b :=
  ⟨hab.1, fun ha => hab.2 (h ha)⟩

/-! ### §65.5 ⭐⭐ 与 do-算子的**对应** -/

/- ⭐⭐⭐ **$do(X=x)$ 对应 $G_{\overline{X}}$**（**语义-图层的接口**）。

**陈述**：**$do(X:=x)$ 抹掉的结构信息，恰是 $G_{\overline{X}}$ 抹掉的图的边。**

**⚠ 本节只给出**构造性描述**（无法在本节内证「对应」，
**因为那需要「图的语义 = SCM 的语义」这一层元定理**）——
**但本定理记录了**对应关系**，作为后续工作的锚点。**

**⟹ 即**：**`DoCalculus.doX`（语义）与 `delOut`（图）是同一操作的两个面。**

**⚠ 本段是**未做项的登记，不是定理** ——
**先前此处有一条 `theorem do_delOut_correspondence_anchor : True`（`:= trivial`）**
**作占位，不承载任何数学内容，第 229 轮已删除；本说明本身即为登记。** -/
end GraphOps

end FateV2.Predict