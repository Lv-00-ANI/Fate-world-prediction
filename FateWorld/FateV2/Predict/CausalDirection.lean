import FateWorld.FateV2.Predict.DSeparation

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/CausalDirection.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 3 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict

/-! ===========================================================================
  §61  **d-分离的**方向层****：collider / 分叉 / 链

  ## 背景

  | 轮次 | 已做 |
  |---|---|
  | **60** | d-分离的**图论层**（路径、顶点集、阻断）|

  **⚠ 第 60 轮的边界登记**：
  > **本节只做**图论层**的形式化** ——
  > **不含「collider / 分叉 / 链」的**方向性**区分**

  **⟹ 本轮补上这一层。**

  ## ⚠ 关键发现：**Mathlib 的 `Digraph` 不足以支撑**

  **实测核查**：
  | 项 | Mathlib 是否提供 |
  |---|---|
  | `Digraph`（有向图的类型）| ✅ |
  | `Digraph.Adj` | ✅ |
  | **`Digraph.Walk`**（有向路径）| ❌ **无** |
  | **`Digraph.IsAcyclic`** | ❌ **无** |
  | **`Digraph.Path`** | ❌ **无** |

  **⟹ 即**：**Mathlib 的 `Digraph` **只是「邻接关系的格」**，
  **不含**路径与无环性** —— **方向层须**自建**。**

  ## 本节的产出

  **自建**因果图的方向结构**：
  1. **因果图**（`CausalGraph`：有向 + 无环）
  2. **三元组类型**（链 / 分叉 / collider）—— **d-分离的方向核心**
  3. **开口 / 阻断的路径层判据**

  **⚠ 边界（如实登记）**：
  **本节只形式化**单个三元组的方向分类**；
  **「整条路径的 d-连通」需要逐节点的开口性归纳** ——
  **这是**下一步**的工作。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

namespace CausalDirection

universe u

variable {V : Type u}

/-! ### §61.1 因果图（有向 + 无环，自建） -/

/-- **因果图**：有向图的邻接关系 + **无环性**公理。

**⚠ 为何自建**：**Mathlib 的 `Digraph` 无 `Walk` / `IsAcyclic`**
（见文件头核查），**故 d-分离所需的方向结构须自建。**

**⚠ 第 68 轮的**实质修正****：
**第 61 轮我最初把无环性写成 `acyclic : True`** ——
**那是**空洞的****：该字段**不携带任何信息**，
**且没有任何证明读过它**（全树 grep 确认）。

**⟹ 后果**：**建在 `CausalGraph` 上的每一个 d-分离定理
都**悄悄继承了一个未陈述的假设**** ——
**其散文声称图是无环的，而类型层面**什么都没说**。**

**本轮的修正**：**改为**真正的无环性条件**
（与项目内 `CausDAG.DAG` 的形式一致）：
$$\mathrm{acyclic} : \forall v,\ \neg\,\mathrm{TransGen}(\mathrm{Adj})\,v\,v$$

**⚠ 代价（如实登记）**：
**`GraphOps.delIn` / `delOut` 的 `acyclic := trivial` 填充**须改为真证明**
（删边保持无环 —— **成立但**不平凡**）。** -/
structure CausalGraph (V : Type u) where
  /-- 有向邻接。 -/
  Adj : V → V → Prop
  /-- **无环性**：邻接关系的传递闭包是**非自反**的。

  **即**：**不存在有向环** —— **这是 DAG 的定义性质。**

  **⚠ 形式与 `CausDAG.DAG.acyclic` 一致**（`∀ v, ¬ Relation.TransGen edge v v`）。 -/
  acyclic : ∀ v : V, ¬ Relation.TransGen Adj v v

namespace CausalGraph

/-! #### 无环性的**两个直接推论**（**第 68 轮补**）

**⚠ 背景**：**第 61 轮把无环性写成 `acyclic : True`** ——
**故当时以下两条**无法证明**（它们在**任何**自环/二环图上都假）。
**第 68 轮把无环性改为真条件后，它们**成为具体定理****。

**⚠ 这两条是方向层一切「非 collider」结论的**唯一来源****：
**没有它们，`fork_implies_noncollider` 只能给「中间点有出边」，
**无法排除「中间点同时也是 collider」**。** -/

variable (G : CausalGraph V)

/-- **无自环**：**任何顶点都没有到自己的边**。

**证明**：**自环 `a → a` 即长度 1 的有向环**，
**其传递闭包含 `a → a`，与无环性矛盾。** -/
theorem irrefl (a : V) : ¬ G.Adj a a :=
  fun h => G.acyclic a (Relation.TransGen.single h)

/-- **反对称**：**有 `a → b` 则无 `b → a`**（**无二环**）。

**证明**：**`a → b → a` 即长度 2 的有向环**，
**与无环性矛盾。**

**⟹ 这是「collider 与非 collider 互斥」的**结构基础**** ——
**见下方 `fork_not_collider` 等。** -/
theorem asymm {a b : V} (h : G.Adj a b) : ¬ G.Adj b a :=
  fun h' => G.acyclic a ((Relation.TransGen.single h).tail h')

end CausalGraph

/-! ### §61.2 三元组的方向分类（**d-分离的方向核心**） -/

/-- **三元组的方向类型**（**本节的核心定义**）。

$$\text{Triple}(a, b, c) :=
  \begin{cases}
    \textbf{链} & a \to b \to c \ \text{或}\ a \leftarrow b \leftarrow c\\
    \textbf{分叉} & a \leftarrow b \to c\\
    \textbf{collider} & a \to b \leftarrow c
  \end{cases}$$

**⟹ 这是 d-分离的**方向核心**：
**collider 与非 collider 在「是否被 `Z` 阻断」上**行为相反**：
**非 collider 被 `Z` 含中间点即阻断；
**collider 反而被**不含**中间点（且不含其后代）阻断。** -/
inductive TripleType (G : CausalGraph V) (a b c : V) : Prop where
  /-- **链**：$a \to b \to c$。 -/
  | chain_fwd (h1 : G.Adj a b) (h2 : G.Adj b c) : TripleType G a b c
  /-- **链**：$a \leftarrow b \leftarrow c$。 -/
  | chain_bwd (h1 : G.Adj b a) (h2 : G.Adj c b) : TripleType G a b c
  /-- **分叉**：$a \leftarrow b \to c$。 -/
  | fork (h1 : G.Adj b a) (h2 : G.Adj b c) : TripleType G a b c
  /-- **collider**：$a \to b \leftarrow c$。 -/
  | collider (h1 : G.Adj a b) (h2 : G.Adj c b) : TripleType G a b c

/-- **collider 判据**：$a \to b \leftarrow c$。

**⟹ collider 是 d-分离中**唯一**行为反转的结构。** -/
def IsCollider (G : CausalGraph V) (a b c : V) : Prop :=
  G.Adj a b ∧ G.Adj c b

/-- **非 collider 判据**：$a$ 与 $c$ 中至少一条边**离开** $b$。

$$\text{NonCollider}(a,b,c) := (b \to a) \vee (b \to c)$$ -/
def IsNonCollider (G : CausalGraph V) (a b c : V) : Prop :=
  G.Adj b a ∨ G.Adj b c

/-- **分叉判据**：$a \leftarrow b \to c$。 -/
def IsFork (G : CausalGraph V) (a b c : V) : Prop :=
  G.Adj b a ∧ G.Adj b c

/-- **链判据**（两个方向）。 -/
def IsChain (G : CausalGraph V) (a b c : V) : Prop :=
  (G.Adj a b ∧ G.Adj b c) ∨ (G.Adj b a ∧ G.Adj c b)

/-! ### §61.3 方向层的**核心对偶** -/

/-- **分叉必非 collider**（**本节核心定理**）。

$$\text{Fork}(a,b,c) \implies \text{NonCollider}(a,b,c)$$

**⟹ 即**：**分叉时中间点 $b$ 有出边，故不是 collider** ——
**这是 d-分离「条件集对两类三元组作用相反」的**结构基础**。**

**⚠ 历史说明**：**第 61 轮此处的注释称「$\neg\,\text{Collider}$ 须无环性，
**故只证非 collider 部分」** ——
**那是因当时 `acyclic : True` 而**真的无法证明****。
**第 68 轮无环性落地后，其中的真 `¬` 版本由 `fork_not_collider` 给出
（见下）。**

**⚠ 本条仍保留为「构造型」结论**（直接给出 HasOut 见证），
**不依赖无环性** —— **故适用于任何有向图，而非仅 DAG。** -/
theorem fork_implies_noncollider (G : CausalGraph V) {a b c : V}
    (h : IsFork G a b c) : IsNonCollider G a b c :=
  Or.inl h.1

/-- **分叉必非 collider（真 `¬` 版本）**（**第 68 轮补**）。

$$\text{Fork}(a,b,c) \implies \neg\,\text{Collider}(a,b,c)$$

**⚠ 与 `fork_implies_noncollider` 的差别**：
**后者只给「$b$ 有出边」（构造型），**
**本条给出**真正的否定** —— **需要无环性**：
**`IsCollider` 要求 $a \to b$，而分叉给 $b \to a$，
由 `CausalGraph.asymm` 二者不能共存。**

**⟹ 这是 d-分离「collider 与非 collider **互斥**」的精确形式** ——
**没有它，一条路径的中间点可能「同时是两类」，
开口性判据便不可能是**良定义**的。** -/
theorem fork_not_collider (G : CausalGraph V) {a b c : V}
    (h : IsFork G a b c) : ¬ IsCollider G a b c :=
  fun hc => CausalGraph.asymm G h.1 hc.1

/-- **链必非 collider**（第一个方向）。

**⚠ 注意**：**$a \to b \to c$ 中 $b$ 有出边，故非 collider。** -/
theorem chain_fwd_implies_noncollider (G : CausalGraph V) {a b c : V}
    (h : G.Adj a b ∧ G.Adj b c) : IsNonCollider G a b c :=
  Or.inr h.2

/-- **链（正向）必非 collider（真 `¬` 版本）**（**第 68 轮补**）。

**⚠ 需要无环性**：**`IsCollider` 要求 $c \to b$，而链给 $b \to c$。** -/
theorem chain_fwd_not_collider (G : CausalGraph V) {a b c : V}
    (h : G.Adj a b ∧ G.Adj b c) : ¬ IsCollider G a b c :=
  fun hc => CausalGraph.asymm G h.2 hc.2

/-- **链（反向）必非 collider**。 -/
theorem chain_bwd_implies_noncollider (G : CausalGraph V) {a b c : V}
    (h : G.Adj b a ∧ G.Adj c b) : IsNonCollider G a b c :=
  Or.inl h.1

/-- **链（反向）必非 collider（真 `¬` 版本）**（**第 68 轮补**）。

**⚠ 需要无环性**：**`IsCollider` 要求 $a \to b$，而反向链给 $b \to a$。** -/
theorem chain_bwd_not_collider (G : CausalGraph V) {a b c : V}
    (h : G.Adj b a ∧ G.Adj c b) : ¬ IsCollider G a b c :=
  fun hc => CausalGraph.asymm G h.1 hc.1

/-- **非 collider 与 collider 互斥**（**第 68 轮补，核心对偶**）。

$$\text{NonCollider}(a,b,c) \implies \neg\,\text{Collider}(a,b,c)$$

**⟹ 即**：**「中间点有出边」排除「中间点是 collider」** ——
**这是 `openAt` 的分支不重叠的结构保证。** -/
theorem noncollider_not_collider (G : CausalGraph V) {a b c : V}
    (h : IsNonCollider G a b c) : ¬ IsCollider G a b c := by
  rcases h with h | h
  · exact fun hc => CausalGraph.asymm G h hc.1
  · exact fun hc => CausalGraph.asymm G h hc.2

/-- **相邻三元组上「非 collider」⟺「非 collider」**（**第 68 轮补**）。

**⚠ 前提**：**$a$-$b$ 与 $b$-$c$ **相邻**（方向任意）——
**即这是一个合法的三元组**（见 `triple_exhaustive`）。
**此时「有出边」与「非 collider」**等价**。**

**⟹ 即**：**`IsNonCollider` 这个名字名副其实** ——
**它就是 `IsCollider` 的否定**（**在合法三元组上**）。
**正向不需要无环性；反向需要（用 `asymm`）。** -/
theorem noncollider_iff_not_collider (G : CausalGraph V) {a b c : V}
    (hab : G.Adj a b ∨ G.Adj b a) (hbc : G.Adj b c ∨ G.Adj c b) :
    IsNonCollider G a b c ↔ ¬ IsCollider G a b c := by
  refine ⟨noncollider_not_collider G, fun h => ?_⟩
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · -- a→b 且 b→c：非 collider（右支）
      exact Or.inr hbc
    · -- a→b 且 c→b：这正是 collider，与 h 矛盾
      exact absurd ⟨hab, hbc⟩ h
  · -- b→a：非 collider（左支）
    exact Or.inl hab

/-- **「中间点有出边」⟺ 非 collider**（**统一判据**）。

$$\text{NonCollider}(a,b,c) \iff (b \to a) \vee (b \to c)$$

**⟹ 即**：**d-分离中判「是否 collider」只需看中间点是否有**出边**** ——
**这是判据的**最简形式**。** -/
theorem noncollider_iff_has_out (G : CausalGraph V) (a b c : V) :
    IsNonCollider G a b c ↔ G.Adj b a ∨ G.Adj b c :=
  Iff.rfl

/-! ### §61.4 三元组的**穷尽性** -/

/-- **三元组分类的穷尽性**（**结构定理**）。

**陈述**：**若 $a$-$b$ 与 $b$-$c$ 相邻**（两个方向任意），
**则三元组必属**链 / 分叉 / collider** 之一。**

**⟹ 即**：**四类（链正、链反、分叉、collider）**穷尽**了所有相邻三元组** ——
**这是「路径的开口性可逐节点判定」的前提。** -/
theorem triple_exhaustive (G : CausalGraph V) {a b c : V}
    (hab : G.Adj a b ∨ G.Adj b a) (hbc : G.Adj b c ∨ G.Adj c b) :
    TripleType G a b c ∨ TripleType G a b c ∨
      TripleType G a b c ∨ TripleType G a b c := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · -- a→b, b→c：链（正）
    exact Or.inl (TripleType.chain_fwd hab hbc)
  · -- a→b, c→b：collider
    exact Or.inr (Or.inr (Or.inr (TripleType.collider hab hbc)))
  · -- b→a, b→c：分叉
    exact Or.inr (Or.inr (Or.inl (TripleType.fork hab hbc)))
  · -- b→a, c→b：链（反）
    exact Or.inr (Or.inl (TripleType.chain_bwd hab hbc))

/-- **collider 的方向刻画**（与 `TripleType` 对接）。 -/
theorem isCollider_iff (G : CausalGraph V) (a b c : V) :
    IsCollider G a b c ↔ G.Adj a b ∧ G.Adj c b :=
  Iff.rfl

/-! ### §61.5 四类三元组的**两两互斥**（**第 68 轮补**）

**⚠ 背景**：`triple_exhaustive` 只说四类**覆盖**所有相邻三元组 ——
**但**未说它们**互斥****。
**第 61 轮时这是**无法证**的：**无环性为空，$a \to b \to a$ 同时落进两类。**

**无环性落地后，四类**两两不相容** ——
**故 `TripleType` 真正是**四类划分**（而非「覆盖」）。** -/

/-- **链（正）与分叉互斥**。 -/
theorem chain_fwd_not_fork (G : CausalGraph V) {a b c : V}
    (h : G.Adj a b ∧ G.Adj b c) : ¬ IsFork G a b c :=
  fun hf => CausalGraph.asymm G h.1 hf.1

/-- **链（正）与链（反）互斥**。 -/
theorem chain_fwd_not_chain_bwd (G : CausalGraph V) {a b c : V}
    (h : G.Adj a b ∧ G.Adj b c) : ¬ (G.Adj b a ∧ G.Adj c b) :=
  fun h' => CausalGraph.asymm G h.1 h'.1

/-- **分叉与链（反）互斥**。 -/
theorem fork_not_chain_bwd (G : CausalGraph V) {a b c : V}
    (h : IsFork G a b c) : ¬ (G.Adj b a ∧ G.Adj c b) :=
  fun h' => CausalGraph.asymm G h.2 h'.2

/-- **collider 与链（反）互斥**。 -/
theorem collider_not_chain_bwd (G : CausalGraph V) {a b c : V}
    (h : IsCollider G a b c) : ¬ (G.Adj b a ∧ G.Adj c b) :=
  fun h' => CausalGraph.asymm G h.1 h'.1

end CausalDirection

end FateV2.Predict
