import FateWorld.FateV2.Predict.GraphOps
/-!
  # Predict · ParentMap

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ParentMap.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GraphOps
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §67  ⭐⭐⭐ **父集映射**（$\mathrm{pa} : V \to \mathrm{Set}\,V$）—— SCM 结构方程的图侧接口

  ## 背景

  | 轮次 | 已做 |
  |---|---|
  | **61** | `CausalGraph`（有向邻接 + 无环字段）|
  | **62** | 带向路径、逐节点开口性 |
  | **63** | 后代层（`Reach`）|
  | **65** | 图操作 `delIn`（$G_{\underline{X}}$）/ `delOut`（$G_{\overline{X}}$）|

  ## ⭐ 本节补上的缺口

  **SCM 的结构方程写作**
  $$V_i = f_i\bigl(\mathrm{pa}(V_i)\bigr) + \varepsilon_i,$$
  **其图侧只用到「父集」这一概念** ——
  **但本项目尚无 `pa` 的定义**（第 61–65 轮只用 `Adj` 与路径）。

  **⟹ 本轮定义**父集映射**，并证明它与**图操作**的关系** ——
  **这是「结构方程」与「图操作」两套语言的**接口**。

  ## ⭐ 本节的产出

  | # | 内容 |
  |---|---|
  | **1** | ⭐⭐⭐ **`pa`**：父集映射 $v \mapsto \{u \mid u \to v\}$ |
  | **2** | ⭐⭐ **`mem_pa`**：成员判据（定义性展开）|
  | **3** | ⭐⭐⭐ **`pa_mono`**：**单调性**（边包含 $\implies$ 父集包含）|
  | **4** | ⭐⭐⭐ **`pa_delIn_self`** / **`pa_delIn_of_notMem`**：与删入边的关系 |
  | **5** | ⭐⭐⭐ **`pa_delOut`**：与删出边的关系（$\mathrm{pa}_{G_{\overline X}}(v) = \mathrm{pa}_G(v) \setminus X$）|
  | **6** | ⭐⭐ **`pa_delIn_subset`** / **`pa_delOut_subset`**：两类操作都**只减不加** |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace ParentMap

universe u

variable {V : Type u}

/-! ### §67.1 ⭐⭐⭐ 父集映射的定义 -/

/-- ⭐⭐⭐ **父集映射** $\mathrm{pa} : V \to \mathrm{Set}\,V$。

$$\mathrm{pa}_G(v) := \{\,u \mid \mathrm{Adj}_G\,u\,v\,\}$$

**即**：**$v$ 的父 = 所有以 $v$ 为终点的边的起点。**

**⚠ 读法**：**`u ∈ pa G v` 表示「`u` 是 `v` 的父」** ——
**这是 SCM 结构方程 $V_i = f_i(\mathrm{pa}(V_i)) + \varepsilon_i$ 的图侧对象。** -/
def pa (G : CausalDirection.CausalGraph V) (v : V) : Set V :=
  {u | G.Adj u v}

/-- ⭐⭐ **父集的成员判据**（**定义性展开**）。

$$u \in \mathrm{pa}_G(v) \iff \mathrm{Adj}_G\,u\,v$$

**⟹ 即**：**父关系就是邻接关系（按终点分组）** ——
**这是把 `pa` 与 `Adj` 相互翻译的唯一入口。** -/
theorem mem_pa (G : CausalDirection.CausalGraph V) (u v : V) :
    u ∈ pa G v ↔ G.Adj u v :=
  Iff.rfl

/-- ⭐⭐ **父集映射的外延判据**。

$$\mathrm{pa}_G = \mathrm{pa}_{G'} \iff
  \forall u\,v,\ \mathrm{Adj}_G\,u\,v \leftrightarrow \mathrm{Adj}_{G'}\,u\,v$$

**⟹ 即**：**父集映射**决定**邻接关系**（反之亦然）——
**故「以父集为原始数据」与「以邻接为原始数据」等价。** -/
theorem pa_ext_iff (G G' : CausalDirection.CausalGraph V) :
    pa G = pa G' ↔ ∀ u v : V, G.Adj u v ↔ G'.Adj u v := by
  constructor
  · intro h u v
    have hv : pa G v = pa G' v := congrFun h v
    rw [← mem_pa G u v, ← mem_pa G' u v, hv]
  · intro h
    funext v
    ext u
    rw [mem_pa G u v, mem_pa G' u v]
    exact h u v

/-! ### §67.2 ⭐⭐⭐ 单调性 -/

/-- ⭐⭐⭐ **父集映射的单调性**（**本节核心定理**）。

**若 $G'$ 的边集包含于 $G$ 的边集**（即 $G'$ 只删边不增边），
**则对每个顶点 $v$，$\mathrm{pa}_{G'}(v) \subseteq \mathrm{pa}_G(v)$。**

$$(\forall u\,v,\ \mathrm{Adj}_{G'}\,u\,v \to \mathrm{Adj}_G\,u\,v)
  \implies \mathrm{pa}_{G'}(v) \subseteq \mathrm{pa}_G(v)$$

**⟹ 即**：**删边只会**缩小**父集** ——
**这是「干预不创造新父」的精确形式。** -/
theorem pa_mono {G G' : CausalDirection.CausalGraph V}
    (h : ∀ u v : V, G'.Adj u v → G.Adj u v) (v : V) :
    pa G' v ⊆ pa G v :=
  fun _ hu => h _ _ hu

/-- ⭐⭐⭐ **父集的**逐点包含**判据**（**等价形式**）。

$$\mathrm{pa}_{G'}(v) \subseteq \mathrm{pa}_G(v)
  \iff \forall u,\ \mathrm{Adj}_{G'}\,u\,v \to \mathrm{Adj}_G\,u\,v$$

**⟹ 即**：**父集包含与「该顶点的入边包含」是同一件事。** -/
theorem pa_subset_iff (G G' : CausalDirection.CausalGraph V) (v : V) :
    pa G' v ⊆ pa G v ↔ ∀ u : V, G'.Adj u v → G.Adj u v :=
  Iff.rfl

/-- ⭐⭐ **父集映射在全体顶点上单调**（**合取形式**）。

**⟹ 即**：**`pa_mono` 可整体陈述，无须固定 $v$。** -/
theorem pa_mono_all {G G' : CausalDirection.CausalGraph V}
    (h : ∀ u v : V, G'.Adj u v → G.Adj u v) :
    ∀ v : V, pa G' v ⊆ pa G v :=
  fun v => pa_mono h v

/-! ### §67.3 ⭐⭐⭐ 与删入边（$G_{\underline{X}}$）的关系 -/

/-- ⭐⭐⭐ **删入边后的父集（$v \in X$ 的情形）：空集**（**核心性质**）。

$$v \in X \implies \mathrm{pa}_{G_{\underline{X}}}(v) = \varnothing$$

**⟹ 即**：**$do(X=x)$ 使 $X$ 中的顶点**失去全部父**** ——
**这正是「$X$ 不再被其父决定」的精确形式**，
**也是结构方程 $\mathrm{pa}$ 层的对应。** -/
theorem pa_delIn_self (G : CausalDirection.CausalGraph V) {X : Set V} {v : V}
    (hv : v ∈ X) : pa (GraphOps.delIn G X) v = ∅ := by
  ext u
  simp only [mem_pa, GraphOps.delIn_adj, Set.mem_empty_iff_false, iff_false]
  exact fun h => h.2 hv

/-- ⭐⭐⭐ **删入边后的父集（$v \notin X$ 的情形）：不变**（**核心性质**）。

$$v \notin X \implies \mathrm{pa}_{G_{\underline{X}}}(v) = \mathrm{pa}_G(v)$$

**⟹ 即**：**删入边**只影响 $X$ 中的顶点**，
**其余顶点的父集**原封不动**。** -/
theorem pa_delIn_of_notMem (G : CausalDirection.CausalGraph V) {X : Set V} {v : V}
    (hv : v ∉ X) : pa (GraphOps.delIn G X) v = pa G v := by
  ext u
  simp only [mem_pa, GraphOps.delIn_adj]
  exact ⟨fun h => h.1, fun h => ⟨h, hv⟩⟩

/-- ⭐⭐⭐ **删入边后的父集 ⊆ 原父集**（**单调性实例**）。

$$\mathrm{pa}_{G_{\underline{X}}}(v) \subseteq \mathrm{pa}_G(v)$$

**⟹ 即**：**这是 `pa_mono` 在 `delIn` 上的实例** ——
**删入边只减不加。** -/
theorem pa_delIn_subset (G : CausalDirection.CausalGraph V) (X : Set V) (v : V) :
    pa (GraphOps.delIn G X) v ⊆ pa G v :=
  pa_mono (fun _ _ (hab : (GraphOps.delIn G X).Adj _ _) => hab.1) v

/-! ### §67.4 ⭐⭐⭐ 与删出边（$G_{\overline{X}}$）的关系 -/

/-- ⭐⭐⭐ **删出边后的父集：去掉 $X$ 中的父**（**核心定理**）。

$$\mathrm{pa}_{G_{\overline{X}}}(v) = \mathrm{pa}_G(v) \setminus X$$

**⟹ 即**：**$do(X=x)$ 切断 $X$ 的出边，
**故 $X$ 中的顶点不再是任何顶点的父**** ——
**这是「$X$ 不再影响其后代」在 $\mathrm{pa}$ 层的精确形式。** -/
theorem pa_delOut (G : CausalDirection.CausalGraph V) (X : Set V) (v : V) :
    pa (GraphOps.delOut G X) v = pa G v \ X := by
  ext u
  simp only [mem_pa, GraphOps.delOut_adj, Set.mem_sdiff]

/-- ⭐⭐⭐ **删出边后的父集 ⊆ 原父集**（**单调性实例**）。

$$\mathrm{pa}_{G_{\overline{X}}}(v) \subseteq \mathrm{pa}_G(v)$$

**⟹ 即**：**这是 `pa_mono` 在 `delOut` 上的实例** ——
**删出边只减不加。** -/
theorem pa_delOut_subset (G : CausalDirection.CausalGraph V) (X : Set V) (v : V) :
    pa (GraphOps.delOut G X) v ⊆ pa G v :=
  pa_mono (fun _ _ (hab : (GraphOps.delOut G X).Adj _ _) => hab.1) v

/-- ⭐⭐⭐ **删出边后 $X$ 中的顶点不再是父**（**核心性质**）。

$$u \in X \implies u \notin \mathrm{pa}_{G_{\overline{X}}}(v)$$

**⟹ 即**：**$do(X=x)$ 之后，$X$ 中的顶点不再出现在任何父集中** ——
**这是「切断下游影响」的最直接表述。** -/
theorem notMem_pa_delOut (G : CausalDirection.CausalGraph V) (X : Set V)
    {u v : V} (hu : u ∈ X) : u ∉ pa (GraphOps.delOut G X) v := by
  rw [mem_pa, GraphOps.delOut_adj]
  exact fun h => h.2 hu

/-- ⭐⭐ **删出边后父集与原父集的关系（成员形式）**。

$$u \in \mathrm{pa}_{G_{\overline{X}}}(v) \iff
  u \in \mathrm{pa}_G(v) \wedge u \notin X$$ -/
theorem mem_pa_delOut (G : CausalDirection.CausalGraph V) (X : Set V) (u v : V) :
    u ∈ pa (GraphOps.delOut G X) v ↔ u ∈ pa G v ∧ u ∉ X := by
  rw [mem_pa, GraphOps.delOut_adj, mem_pa]

/-! ### §67.5 ⭐⭐ 父集映射与「根 / 叶」 -/

/-- ⭐⭐ **根**（无父的顶点）。
$$\mathrm{Root}_G(v) := \mathrm{pa}_G(v) = \varnothing$$ -/
def IsRoot (G : CausalDirection.CausalGraph V) (v : V) : Prop :=
  pa G v = ∅

/-- ⭐⭐ **删入边使 $X$ 中的顶点成为根**。

$$v \in X \implies \mathrm{Root}_{G_{\underline{X}}}(v)$$

**⟹ 即**：**$do(X=x)$ 后 $X$ 中的顶点无父** ——
**`pa_delIn_self` 的直接改写。** -/
theorem isRoot_delIn (G : CausalDirection.CausalGraph V) {X : Set V} {v : V}
    (hv : v ∈ X) : IsRoot (GraphOps.delIn G X) v :=
  pa_delIn_self G hv

/-- ⭐⭐⭐ **父集的基数上界可由入度刻画**（**接口**）。

**若某顶点 $v$ 在 $G$ 中入度为 $0$，则 $\mathrm{pa}_G(v) = \varnothing$。**

**⚠ 说明**：**入度的定义需要 `Fintype V` 与 `DecidableRel`**，
**本节不引入该依赖，故此条以「无入边」的形式陈述**（等价且无需额外假设）。 -/
theorem pa_eq_empty_iff (G : CausalDirection.CausalGraph V) (v : V) :
    pa G v = ∅ ↔ ∀ u : V, ¬ G.Adj u v := by
  constructor
  · intro h u hu
    have : u ∈ pa G v := hu
    rw [h] at this
    exact this
  · intro h
    ext u
    simp only [mem_pa, Set.mem_empty_iff_false, iff_false]
    exact h u

end ParentMap

end FateV2.Predict