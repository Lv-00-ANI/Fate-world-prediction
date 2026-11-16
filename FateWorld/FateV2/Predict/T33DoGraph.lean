import FateWorld.FateV2.Predict.GraphOps
import FateWorld.FateV2.Predict.T34DoPushforward
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

/-!
  # Predict · T33DoGraph

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T33DoGraph.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GraphOps, T34DoPushforward
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/_r230_B2` —— **T3.3：`do` 的删边与模型替换是同一操作的两个投影**
  （**第 230 轮 B2**）

  ## 清单原文（T3.3）

  > **`do` 的删边与模型替换是同一操作的两个投影**：对 `M` 与 `X ⊆ V`，
  > `M_{do(X=x)}` 诱导的图 `G_do` 恰好等于 `G_{\overline{X}}`
  > （删去一切指向 `X` 的边）。

  ## ⭐⭐ 层次辨析（**本文件要说的第一件事**）

  清单里的两个操作**不在同一层次**：

  | 侧 | 操作 | 所在数学宇宙 | 本项目的载体 |
  |---|---|---|---|
  | **图侧** | 删边 | **关系** `V → V → Prop` | `GraphOps.delIn` / `delOut` |
  | **语义侧** | 把方程换成常数 | **结构映射** `E → V → (V → D) → D` | `T34.doMap` |

  **⟹ 「它们给出同一个图」这句话**字面上跨了层**：
  `delIn` 的输出是图，`doMap` 的输出是结构映射。
  **要让这句话成为定理，必须补上**从语义到图的函子 `graphOf`。**

  ## ⭐⭐⭐ 本文件的主要结论（**逐条对应清单要求**）

  | 清单要求 | 本文件的定理 | 状态 |
  |---|---|---|
  | **第 1 条**：`graphOf` 与 `graphOf (doMap M x) = delIn (graphOf M) X` | `t33_graph_eq_doIn`（§4.3）| ✅ **证明**（但方向见下）|
  | **第 2 条**：`doGraph`、`doGraph_fixpoint`、`doGraph_no_incoming`（⚠ `doGraph_no_incoming` **只作为「错误签名」出现在下方 ⚠ 小节**，**本文件并未证它（且它不成立）**；第 258 轮更正）| §1.1、§1.2、§1.3 | ⚠ **见下方⚠小节** |
  | **第 3 条**：`doGraph_acyclic_preserved` | §2.1 | ✅ |

  ## ⚠⚠⚠ **一处必须登记的实质性出入**（**本文件最重要的部分**）

  **清单第 2 条给的代码**是
  ```lean
  def doGraph (G) (X) : V → V → Prop := fun a b => G a b ∧ a ∉ X
  theorem doGraph_no_incoming (a) (ha : a ∈ X) (b) : ¬ doGraph G X b a
  ```
  **这两行里 `a ∉ X` 与 `¬ doGraph G X b a`（要求 `b ∉ X`）**不是同一件事** ——
  **本文件已用 Lean 实测：该定理在清单给出的签名下**不成立****
  （`Fate/_r230_B2.lean` 编译期即报
  `Application type mismatch: ha has type a ∈ X but is expected to have type b ∈ X`）。

  **⭐ 但这不是笔误可以一改了之的：它牵出一个**数学事实****：

  **`doMap`（方程换常数）与「删去指向 `X` 的边」**不是同一个操作**。
  本文件给出**一个完整的反例**（§4.4）：两个变量 `{false, true}`，`true` 的方程读 `false`；
  干预 `X = {true}` 把 `true` 的方程变常数 ⟹ **删掉的是**从 `true` 出发**的边**，
  **而不是**指向 `true` 的边**。

  **⟹ 正确的配对是**：

  | 语义侧 | 图侧 | 删的边 |
  |---|---|---|
  | `doMap` 把 `X` 的方程换常数 | **`delIn`**（判据 `b ∉ X`，`b` 是**方程索引**）| 指向 `X` 的边 |

  **⭐ 本文件证明的就是这一配对**（`t33_graph_eq_doIn`）：
  $$\mathrm{graphOf}(M_{\mathrm{do}(X=x)}) = \mathrm{delIn}(\mathrm{graphOf}(M), X)$$
  **前提是 `graphOf` 的**边方向与 `delIn` 的**变量索引约定一致**（见 §4.1 的定义）。

  **⚠ 与清单原话的差异（如实登记）**：清单写的是 `G_{\overline X}`，
  **而 `GraphOps` 文件头把 `G_{\overline X}` 定义为**删出边**、`G_{\underline X}` 为**删入边**
  **（与 Pearl 通行记号相反）。本文件**不修改 `GraphOps` 的记号**，
  只说：**T3.3 的数学内容是**「`doMap` 的图侧投影 = 删掉指向被干预变量的边」**，
  **本文件以 `doInGraph`（= `GraphOps.delIn` 的邻接关系）作为该投影的精确形式。** -/

namespace FateV2.Predict
namespace R230

universe u

/-! ## §1 ⭐⭐ 图层的 `do(X)`：**抽象版本**（清单第 2 条）

**⚠ 本节刻意不用 `CausalGraph`**，只用裸关系 `V → V → Prop` ——
**因为幂等性与「无入边」是**纯关系论**事实，与无环性无关。**

**⚠ 本节保留清单给的两份代码**（`doGraph` 与 `doGraph_no_incoming`），
**但**同时**给出它们的正确版本**（`doInGraph` 与 `doGraph_no_outgoing`）。** -/

/-- ⭐⭐ **图层的 `do(X)`**（**清单第 2 条原样**）：删去**从** `X` 出发的边。

$$(\mathrm{doGraph}\,G\,X)(a,b) := G(a,b) \wedge a \notin X$$

**⭐ 这等价于 `GraphOps.delOut` 的邻接关系。** -/
def doGraph {V : Type*} (G : V → V → Prop) (X : Set V) : V → V → Prop :=
  fun a b => G a b ∧ a ∉ X

/-- ⭐⭐⭐ **图层的 `do(X)`（删入边版）**：删去**指向** `X` 的边。

$$(\mathrm{doInGraph}\,G\,X)(a,b) := G(a,b) \wedge b \notin X$$

**⭐ 这等价于 `GraphOps.delIn` 的邻接关系**（`delIn_adj` 逐字相同）——
**它是 T3.3 里 `G_{\overline X}`（「删去一切指向 `X` 的边」）的精确形式。** -/
def doInGraph {V : Type*} (G : V → V → Prop) (X : Set V) : V → V → Prop :=
  fun a b => G a b ∧ b ∉ X

/-! ### §1.1 ⭐⭐⭐ 幂等性（清单第 2 条第一式） -/

/-- ⭐⭐⭐ **`doGraph` 是幂等的**：**删两次等于删一次**。

$$\mathrm{doGraph}(\mathrm{doGraph}(G,X),X) = \mathrm{doGraph}(G,X)$$

**证明**：**两个方向都是「提取第一分量」/「第一分量 + 原有的 `a ∉ X`」** ——
**即**：条件 `a ∉ X` 在第一次删边后**已经成立**，第二次删**不改变任何东西**。** -/
theorem doGraph_fixpoint {V : Type*} (G : V → V → Prop) (X : Set V) :
    doGraph (doGraph G X) X = doGraph G X := by
  funext a b
  exact propext ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩

/-- ⭐⭐⭐ **`doInGraph` 同样是幂等的**（**删入边版**）。 -/
theorem doInGraph_fixpoint {V : Type*} (G : V → V → Prop) (X : Set V) :
    doInGraph (doInGraph G X) X = doInGraph G X := by
  funext a b
  exact propext ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩

/-- ⭐⭐ **`do(X)` 只减不加**：`doGraph G X ⊆ G`。

**⟹ 这是 §2「保持无环」的唯一来源。** -/
theorem doGraph_subset {V : Type*} (G : V → V → Prop) (X : Set V)
    {a b : V} (h : doGraph G X a b) : G a b :=
  h.1

/-- ⭐⭐ **`doInGraph` 只减不加**。 -/
theorem doInGraph_subset {V : Type*} (G : V → V → Prop) (X : Set V)
    {a b : V} (h : doInGraph G X a b) : G a b :=
  h.1

/-! ### §1.2 ⭐⭐⭐ 干预后**没有边指向 `X`**（清单第 2 条第二式）

**⚠⚠ 这里必须把两件事分开说**（见文件头「出入登记」）：

- **清单给的签名** `(a) (ha : a ∈ X) (b) : ¬ doGraph G X b a`
  **要的是「`X` 中顶点没有入边」**；
- **但 `doGraph` 的条件是 `a ∉ X`（边的**起点**）** ——
  **故原样签名下该命题**不成立**（需 `b ∉ X`，而前提给的是 `a ∈ X`）。**

**⟹ 本文件给出**两条正确的定理**，并保留清单的措辞在 `doInGraph` 上。** -/

/-- ⭐⭐⭐ **干预后**没有边指向 `X`**（**清单第 2 条第三个定理的正确载体**）。

$$\forall a \in X,\ \forall b,\ \neg\,(\mathrm{doInGraph}\,G\,X)\,b\,a$$

**⭐ 这正是清单说的**：「干预后**没有边指向 `X`** ——
**这正是 `G_{\overline X}` 的定义」**。

**⚠ 与清单签名的差别**：载体是 `doInGraph` 而非 `doGraph` ——
**原因见文件头出入登记，以及 §4.4 的反例。** -/
theorem doInGraph_no_incoming {V : Type*} (G : V → V → Prop) (X : Set V)
    (a : V) (ha : a ∈ X) (b : V) : ¬ doInGraph G X b a :=
  fun h => h.2 ha

/-- ⭐⭐⭐ **`doGraph` 干预后 `X` 中顶点**无出边**（清单同一条的镜像版）。

$$\forall a \in X,\ \forall b,\ \neg\,(\mathrm{doGraph}\,G\,X)\,a\,b$$ -/
theorem doGraph_no_outgoing {V : Type*} (G : V → V → Prop) (X : Set V)
    (a : V) (ha : a ∈ X) (b : V) : ¬ doGraph G X a b :=
  fun h => h.2 ha

/-- ⭐⭐ **两个版本在转置下互为镜像**：**「删出边」转置 = 「删入边」**。 -/
theorem doGraph_transpose {V : Type*} (G : V → V → Prop) (X : Set V) (a b : V) :
    doGraph (fun x y => G y x) X b a ↔ doInGraph G X a b :=
  Iff.rfl

/-! ### §1.3 ⭐⭐ 干预的组合律（**多变量干预**） -/

/-- ⭐⭐ **两次干预 = 一次联合干预**（**`do` 的组合律**）。

$$\mathrm{doGraph}(\mathrm{doGraph}(G,X),X') = \mathrm{doGraph}(G, X \cup X')$$ -/
theorem doGraph_comp {V : Type*} (G : V → V → Prop) (X X' : Set V) :
    doGraph (doGraph G X) X' = doGraph G (X ∪ X') := by
  funext a b
  refine propext ⟨fun h => ⟨h.1.1, ?_⟩, fun h => ⟨⟨h.1, ?_⟩, ?_⟩⟩
  · intro hmem
    rcases hmem with hmem | hmem
    · exact h.1.2 hmem
    · exact h.2 hmem
  · intro hmem; exact h.2 (Or.inl hmem)
  · intro hmem; exact h.2 (Or.inr hmem)

/-- ⭐⭐ **幂等性是组合律的推论**（`X ∪ X = X`）。 -/
theorem doGraph_fixpoint' {V : Type*} (G : V → V → Prop) (X : Set V) :
    doGraph (doGraph G X) X = doGraph G X := by
  rw [doGraph_comp, Set.union_self]

/-! ## §2 ⭐⭐⭐ **干预保持无环性**（清单第 3 条） -/

/-- ⭐⭐⭐ **`doGraph` 保持无环性**（**删边不会创造环**）。

**陈述**：**若 `G` 无环，则 `doGraph G X` 的邻接关系也无环。**

$$\bigl(\forall v,\ \neg\,\mathrm{TransGen}(G)\,v\,v\bigr)
  \implies \bigl(\forall v,\ \neg\,\mathrm{TransGen}(\mathrm{doGraph}\,G\,X)\,v\,v\bigr)$$

**证明**：**`doGraph G X ⊆ G`**（`doGraph_subset`），
**传递闭包单调**（`Relation.TransGen.mono`）⟹ **`G` 的无环性直接继承**。

**⭐ 这是清单第 3 条的逐字形式化**，
**也是「干预不创造新因果」在图层的精确表述。** -/
theorem doGraph_acyclic_preserved {V : Type*} (G : CausalDirection.CausalGraph V)
    (X : Set V) : ∀ v : V, ¬ Relation.TransGen (doGraph G.Adj X) v v := by
  intro v h
  exact G.acyclic v (Relation.TransGen.mono (fun a b hab => hab.1) v v h)

/-- ⭐⭐⭐ **`doInGraph` 保持无环性**（**删入边版**）。 -/
theorem doInGraph_acyclic_preserved {V : Type*} (G : CausalDirection.CausalGraph V)
    (X : Set V) : ∀ v : V, ¬ Relation.TransGen (doInGraph G.Adj X) v v := by
  intro v h
  exact G.acyclic v (Relation.TransGen.mono (fun a b hab => hab.1) v v h)

/-- ⭐⭐ **干预后的图本身是一个 `CausalGraph`**（**可直接用于 `do-calculus`**）。

**⟹ 这填补了 `GraphOps.lean` §65.5 登记的空缺**：那里说
「`do` 与 `delOut` 的对应需元定理」，**本文件 §4 给出该元定理的一半
（语义侧 ⟹ 图侧），另一半（图侧 → 语义）不属于 T3.3。** -/
def doGraphCG (G : CausalDirection.CausalGraph V) (X : Set V) : CausalDirection.CausalGraph V where
  Adj := doGraph G.Adj X
  acyclic := doGraph_acyclic_preserved G X

/-! ## §3 ⭐⭐⭐ 语义层：**逐坐标 SCM** 与 `doMap`

**⚠ 背景**：`T34.doMap` 是**单变量**版本（`M : SCM X Y`，干预 `x : X`）。
**清单说「对 `M` 与 `X ⊆ V`」** —— **即**多变量**。
**本节的 `VecSCM` 是把「每个变量一条方程」抽象出来的**最小载体**：
外生 `E`、变量 `V`、取值域 `D`，`f e v assign` 是「外生 `e` 下变量 `v`
在父取值 `assign` 处的方程值」。** -/

/-- ⭐⭐ **逐坐标 SCM**：外生 `E`、变量 `V`、取值域 `D`，
结构映射 `f : E → V → (V → D) → D`。

**⭐ 读法**：`assign : V → D` 是「父变量的当前取值」，
`f e v` 是变量 `v` 在外生 `e` 下的结构方程。** -/
structure VecSCM (E V D : Type*) where
  /-- 结构方程族。 -/
  f : E → V → (V → D) → D

namespace VecSCM

variable {E V D : Type*}

/-- ⭐⭐ **方程 `eq` 是否真的读变量 `v`**：
**存在两个只在 `v` 处不同的赋值，使方程值不同。** -/
def Reads (M : VecSCM E V D) (exi : E) : V → V → Prop :=
  fun eq v => ∃ c d : V → D, (∀ w, w ≠ v → c w = d w) ∧ M.f exi eq c ≠ M.f exi eq d

/-- ⭐⭐⭐ **语义层的 `do(X = x)`**：**把 `X` 中每个变量的方程换成常数 `x`**。

$$(\mathrm{doMap}\,M\,X\,x).f\,e\,v := \begin{cases}
  x\,v & v \in X\\
  M.f\,e\,v & v \notin X
\end{cases}$$

**⭐ 这正是清单说的「`X` 的方程换成常数」的多变量版本。** -/
def doMap (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)] (x : V → D) :
    VecSCM E V D where
  f := fun exi v assign => if v ∈ X then x v else M.f exi v assign

/-- ⭐⭐ **干预后 `X` 中的方程是常数**（**与 `assign` 无关**）。 -/
theorem doMap_const (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)]
    (x : V → D) (exi : E) {eq : V} (heq : eq ∈ X) (assign : V → D) :
    (doMap M X x).f exi eq assign = x eq := by
  show (if eq ∈ X then x eq else M.f exi eq assign) = x eq
  rw [if_pos heq]

/-- ⭐⭐ **干预后 `X` 外的方程不变**。 -/
theorem doMap_unchanged (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)]
    (x : V → D) (exi : E) {eq : V} (heq : eq ∉ X) (assign : V → D) :
    (doMap M X x).f exi eq assign = M.f exi eq assign := by
  show (if eq ∈ X then x eq else M.f exi eq assign) = M.f exi eq assign
  rw [if_neg heq]

/-- ⭐⭐⭐ **干预后 `X` 中的方程不读任何变量**（**纯语义事实**）。

$$\forall eq \in X,\ \forall v,\ \neg\,\mathrm{Reads}(M_{\mathrm{do}(X=x)})\,e\,eq\,v$$

**⭐ 这是「`do` 切断了 `X` 的入边」在**语义层的直接体现** ——
**它不经过任何图，是纯语义结论。** -/
theorem doMap_no_reads (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)]
    (x : V → D) (exi : E) {eq : V} (heq : eq ∈ X) (v : V) :
    ¬ Reads (doMap M X x) exi eq v := by
  rintro ⟨c, d, _, hne⟩
  exact hne (by rw [doMap_const M X x exi heq c, doMap_const M X x exi heq d])

/-- ⭐⭐ **`X` 外的依赖关系在干预下不变**（**双向**）。 -/
theorem doMap_reads_iff (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)]
    (x : V → D) (exi : E) {eq v : V} (heq : eq ∉ X) :
    Reads (doMap M X x) exi eq v ↔ Reads M exi eq v := by
  constructor
  · rintro ⟨c, d, hsame, hne⟩
    exact ⟨c, d, hsame, by
      rw [doMap_unchanged M X x exi heq c, doMap_unchanged M X x exi heq d] at hne
      exact hne⟩
  · rintro ⟨c, d, hsame, hne⟩
    exact ⟨c, d, hsame, by
      rw [doMap_unchanged M X x exi heq c, doMap_unchanged M X x exi heq d]
      exact hne⟩

end VecSCM

/-! ## §4 ⭐⭐⭐⭐ **T3.3 主定理**：`doMap` 与删边是同一操作的两个投影

```
        语义侧                             图侧
   VecSCM.doMap  ───── graphOf ─────►  doInGraph
        │                                  │
        │ （方程换常数）                     │ （删指向 X 的边）
        ▼                                  ▼
   VecSCM.doMap            graphOf (doMap M X x) = doInGraph (graphOf M) X
```

**即**：**「换方程」与「删边」在 `graphOf` 下**交换** —— **这就是 T3.3。** -/

/-- ⭐⭐⭐ **从语义导出图**：**`a → b` 当且仅当方程 `b` 读变量 `a`**。

$$\mathrm{graphOf}(M)(a,b) := \exists e,\ M.\mathrm{Reads}\,e\,b\,a$$

**⭐ 读法**：**「`b` 的方程真的用到 `a`」** ——
**这就是「`a` 是 `b` 的父」的**语义定义**。**

**⚠ 与清单第 1 条的差别（必要修正，如实登记）**：
清单写 `graphOf : CausalGraph V`，**但这**做不到**** ——
**`graphOf` 的像**一般不是 DAG**（可以是自环，也可以有环），
**故装不进要求 `acyclic` 字段的 `CausalGraph`。**
**本文件返回裸关系，并在 §4.3 给出带无环性假设的 `CausalGraph` 版本。** -/
def graphOf {E V D : Type*} (M : VecSCM E V D) : V → V → Prop :=
  fun a b => ∃ exi : E, VecSCM.Reads M exi b a

/-- ⭐⭐ **`graphOf` 的展开判据**。 -/
theorem graphOf_iff {E V D : Type*} (M : VecSCM E V D) (a b : V) :
    graphOf M a b ↔ ∃ exi : E, VecSCM.Reads M exi b a :=
  Iff.rfl

/-! ### §4.1 ⭐⭐⭐⭐ **T3.3 主定理** -/

/-- ⭐⭐⭐⭐ **T3.3（`do` 的删边 = 模型替换的图侧投影）**。

$$\mathrm{graphOf}\bigl(M_{\mathrm{do}(X=x)}\bigr)
  = \mathrm{doInGraph}\bigl(\mathrm{graphOf}(M),\, X\bigr)$$

**🔹 对应清单**：T3.3 的逐字内容 ——
**「`M_{do(X=x)}` 诱导的图恰好等于删去一切指向 `X` 的边」**
（`doInGraph` 即 `GraphOps.delIn` 的邻接关系）。**

**⭐ 证明结构**（**两个方向各用一条语义引理**）：

| 方向 | 用到的引理 | 内容 |
|---|---|---|
| `⊆`（干预后**只减不增**）| `doMap_no_reads` + `doMap_reads_iff` | `X` 内方程是常数，故**不读任何变量** |
| `⊇`（干预后**保留 `X` 外的边**）| `doMap_reads_iff` | `X` 外的方程**逐字未动** |

**⭐⭐ 这正是清单说的「同一操作的两个投影」**：
- 左边：`doMap`（**把方程换成常数**）；
- 右边：`doInGraph`（**删边**）；
- 等号：**两个投影给出同一个图。** -/
theorem t33_graph_eq_doIn {E V D : Type*} (M : VecSCM E V D) (X : Set V)
    [DecidablePred (· ∈ X)] (x : V → D) :
    graphOf (VecSCM.doMap M X x) = doInGraph (graphOf M) X := by
  funext a b
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨exi, he⟩ := h
    -- `b` 在干预后必须不读 `a`，故 `b ∉ X`（否则 `b` 的方程是常数）
    have hb : b ∉ X := fun h1 => VecSCM.doMap_no_reads M X x exi h1 a he
    exact ⟨⟨exi, (VecSCM.doMap_reads_iff M X x exi hb).mp he⟩, hb⟩
  · obtain ⟨⟨exi, he⟩, hb⟩ := h
    exact ⟨exi, (VecSCM.doMap_reads_iff M X x exi hb).mpr he⟩

/-- ⭐⭐⭐ **T3.3（与 `GraphOps.delIn` 的直接对接）**：
**`graphOf (doMap M X x)` 恰是 `GraphOps.delIn (fromGraph (graphOf M)) X` 的邻接关系**。

**⚠ 因为 `graphOf` 不保证无环，本定理以**邻接关系**的形式陈述；
**它是 `t33_graph_eq_doIn` 与 `GraphOps.delIn_adj` 的直接复合。** -/
theorem t33_graph_eq_delIn {E V D : Type*} (M : VecSCM E V D) (G : CausalDirection.CausalGraph V)
    (hG : ∀ a b, G.Adj a b ↔ graphOf M a b) (X : Set V) [DecidablePred (· ∈ X)]
    (x : V → D) :
    ∀ a b, graphOf (VecSCM.doMap M X x) a b ↔ (GraphOps.delIn G X).Adj a b := by
  intro a b
  rw [t33_graph_eq_doIn M X]
  rw [GraphOps.delIn_adj]
  exact ⟨fun h => ⟨(hG a b).mpr h.1, h.2⟩, fun h => ⟨(hG a b).mp h.1, h.2⟩⟩

/-- ⭐⭐ **`graphOf` 的无环版本**：**给定无环性假设，`graphOf` 就是一个 `CausalGraph`。** -/
def graphOfCG {E V D : Type*} (M : VecSCM E V D)
    (h : ∀ v : V, ¬ Relation.TransGen (graphOf M) v v) : CausalDirection.CausalGraph V where
  Adj := graphOf M
  acyclic := h

/-- ⭐⭐⭐ **T3.3 的 `CausalGraph` 形式**：
**在无环性假设下，干预后的图恰是 `doGraphCG` 给出的图。** -/
theorem t33_graph_eq_doInGraphCG {E V D : Type*} (M : VecSCM E V D)
    (h : ∀ v : V, ¬ Relation.TransGen (graphOf M) v v)
    (X : Set V) [DecidablePred (· ∈ X)] (x : V → D) :
    graphOf (VecSCM.doMap M X x) = doInGraph (graphOfCG M h).Adj X := by
  rw [t33_graph_eq_doIn M X]
  rfl

/-! ### §4.2 ⭐⭐⭐ **T3.3 的推论**：干预后主效应的「切断」 -/

/-- ⭐⭐⭐ **干预后 `X` 中变量**没有父**（**T3.3 的直接语义推论**）。

$$\forall x_0 \in X,\ \neg\,\mathrm{graphOf}(M_{\mathrm{do}(X=x)})\,a\,x_0$$

**⟹ 即**：**`do(X=x)` 后 `X` 不再被其父决定** ——
**这正是「删去指向 `X` 的边」的语义等价表述。** -/
theorem t33_no_parents_after_do {E V D : Type*} (M : VecSCM E V D) (X : Set V)
    [DecidablePred (· ∈ X)] (x : V → D) {x₀ : V} (hx : x₀ ∈ X) (a : V) :
    ¬ graphOf (VecSCM.doMap M X x) a x₀ := by
  rw [t33_graph_eq_doIn M X]
  exact doInGraph_no_incoming (graphOf M) X x₀ hx a

/-! ### §4.3 ⚠⚠ **反例：`doMap` 的图侧投影**不是**「删出边」**

**本文件最重要的**负结果****：**用 Lean 实际验证**
**`graphOf (doMap M X x) ≠ doGraph (graphOf M) X`**。

**反例**：两个变量 `{false, true}`，`true` 的方程读 `false`。
干预 `X = {true}` 使 `true` 的方程变常数 ⟹ **删掉的是**从 `true` 出发**的边**
（这里 `true` 本来无出边，故**什么也没删**），
**而 `doGraph` 若要删「指向 `true`」的边，就会删掉 `false → true`** ——
**两者不同。** -/

/-- ⚠ **反例的 SCM**：`true` 的方程读 `false`。 -/
def ceM : VecSCM Unit Bool Bool where
  f := fun _ v assign => if v then !(assign false) else assign false

/-- ⚠ **反例中的边**：`graphOf ceM false true` 成立。 -/
theorem ceM_edge : graphOf ceM false true :=
  ⟨(), fun _ => false, fun w => if w = false then true else false,
   by intro w hw; show false = (if w = false then true else false); rw [if_neg hw],
   by show (if true then !((fun _ : Bool => false) false) else false) ≠
        (if true then !((fun w => if w = false then true else false) false) else false)
      simp⟩

/-- ⚠⚠ **反例（Lean 验证）**：**`doMap` 的图侧投影不是 `doGraph`**。

即：**存在 `M, X, x` 使 `graphOf (doMap M X x) ≠ doGraph (graphOf M) X`。** -/
theorem ce_not_doGraph :
    ∃ (x : Bool → Bool), ¬ (graphOf (VecSCM.doMap ceM ({true} : Set Bool) x)
      = doGraph (graphOf ceM) ({true} : Set Bool)) := by
  refine ⟨fun _ => false, fun hEq => ?_⟩
  -- RHS 在 (false, true) 处为真（ceM_edge 且 false ∉ {true}）
  have hR : doGraph (graphOf ceM) ({true} : Set Bool) false true :=
    ⟨ceM_edge, by decide⟩
  -- 故 LHS 也为真
  have hL : graphOf (VecSCM.doMap ceM ({true} : Set Bool) (fun _ => false)) false true := by
    rw [hEq]; exact hR
  -- 但 LHS 实为假：`true` 的方程被换成常数
  obtain ⟨_, c, d, _, hne⟩ := hL
  clear hR hEq
  have h1 : (VecSCM.doMap ceM ({true} : Set Bool) (fun _ => false)).f () true c = false :=
    VecSCM.doMap_const ceM ({true} : Set Bool) (fun _ => false) () (by decide) c
  have h2 : (VecSCM.doMap ceM ({true} : Set Bool) (fun _ => false)).f () true d = false :=
    VecSCM.doMap_const ceM ({true} : Set Bool) (fun _ => false) () (by decide) d
  exact hne (by rw [h1, h2])

/-- ⭐⭐ **反例的正面解读**：**正确的配对是 `doInGraph`** ——
**`doMap` 删掉的是**指向**被替换方程变量的边**（因为那是方程索引），
这正是 `GraphOps.delIn` 的语义。** -/
theorem ce_doIn_holds :
    graphOf (VecSCM.doMap ceM ({true} : Set Bool) (fun _ => false))
      = doInGraph (graphOf ceM) ({true} : Set Bool) :=
  t33_graph_eq_doIn ceM ({true} : Set Bool) (fun _ => false)

/-! ## §5 ⭐ **与 `GraphOps` / `T34` 既有设施的对接** -/

/-- ⭐⭐ **`doInGraph` 与 `GraphOps.delIn` 的邻接关系一致**（**逐字对应**）。 -/
theorem doInGraph_eq_delIn_adj {V : Type*} (G : CausalDirection.CausalGraph V) (X : Set V)
    (a b : V) : doInGraph G.Adj X a b ↔ (GraphOps.delIn G X).Adj a b :=
  Iff.rfl

/-- ⭐⭐ **`doGraph` 与 `GraphOps.delOut` 的邻接关系一致**。 -/
theorem doGraph_eq_delOut_adj {V : Type*} (G : CausalDirection.CausalGraph V) (X : Set V)
    (a b : V) : doGraph G.Adj X a b ↔ (GraphOps.delOut G X).Adj a b :=
  Iff.rfl

/-- ⭐⭐ **`T34.doMap` 是本文件 `VecSCM.doMap` 的单变量特例**（**语义对接说明**）。

**⚠ `T34.doMap` 作用在 `PearlHierarchy.SCM X Y`（单结果口径）上，
**故不能与 `VecSCM.doMap` 直接相等**；**本定理只登记**二者共享的**结构**：

**`T34.doMap M x` 把第一个分量换成常数 `x`（`doMap_fst`），
**而 `VecSCM.doMap` 把 `X` 索引的方程换成常数（`doMap_const`）** ——
**同一种「换方程」，只是坐标不同。** -/
theorem doMap_shared_structure :
    (∀ {X Y : Type*} (M : PearlHierarchy.SCM X Y) (x : X) (u : M.U),
        (FateV2.Predict.T34.doMap M x u).1 = x)
    ∧ (∀ {E V D : Type*} (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)]
        (x : V → D) (exi : E) {eq : V}, eq ∈ X → ∀ assign : V → D,
        (VecSCM.doMap M X x).f exi eq assign = x eq) :=
  ⟨fun _ _ _ => rfl, fun M X _ x exi _ heq assign =>
    VecSCM.doMap_const M X x exi heq assign⟩

end R230

end FateV2.Predict