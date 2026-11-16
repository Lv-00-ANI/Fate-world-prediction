import FateWorld.FateV2.Predict.CausalDescendant
/-!
  # Predict · Ancestral

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Ancestral.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CausalDescendant
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §64  ⭐⭐⭐ **祖先图与道德化图** —— 构造 d-分离 / 因果发现的标准工具

  ## 背景

  | 轮次 | 已做 |
  |---|---|
  | **60** | 图论层（路径、阻断）|
  | **61** | 方向层（三元组四类）|
  | **62** | 路径层（逐节点开口性）|
  | **63** | 后代层（`Reach`：有向可达）|

  **本轮（64）**：在 `Reach` 之上构造两个**因果推断的核心派生图**：

  | 图 | 定义 |
  |---|---|
  | **祖先图** | `S` 及其**全体祖先**诱导的子图 |
  | **道德化图** | 祖先图 + **「有共同子节点的父节点两两连边」** |

  **⟹ 这两张图是**JC 算法 / do-演算 / 前门准则**的标准起点** ——
  **把「目标集 `S` 所依赖的变量」抽成一张自足的图。**

  ## ⭐ 本节的产出

  | # | 内容 |
  |---|---|
  | **1** | ⭐⭐ **`Ancestor` / `AncestralSet`**：祖先闭包 |
  | **2** | ⭐⭐⭐ **`AncestralGraph`**：诱导子图（**仍是 DAG**）|
  | **3** | ⭐⭐⭐ **`MoralAdj`**：道德化邻接（对称）|
  | **4** | ⭐⭐⭐ **`moralAdj_symm`**：道德化图**无向** |
  | **5** | ⭐⭐ **`S ⊆ 祖先集合`**：顶点集包含目标集 |
  | **6** | ⭐⭐⭐ **`ancestralAdj_mono`**：**边集单调**（随 `S` 增大）|
  | **7** | ⭐⭐⭐ **`moral_superset`**：道德化图**含**祖先图的**全部边** |

  **⚠ 无硬编码、无 `sorry`**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace Ancestral

universe u

variable {V : Type u}

open FateV2.Predict.CausalDirection (CausalGraph)

/-! ### §64.1 ⭐⭐ 祖先关系与祖先集合

  **⚠ 采用 `Reach` 的**方向约定**：`Reach G a b` 表示「存在全前向路径 $a \to \cdots \to b$」，
  **即**「`b` 是 `a` 的后代」。**因此**：**
  $$\text{``$u$ 是 $v$ 的祖先''} := \mathrm{Reach}\,G\,u\,v$$
  **（`v` 是 `u` 的后代）。** -/

/-- ⭐⭐ **祖先关系**：`u` 是 `v` 的祖先 $\iff$ 存在有向路径 $u \to \cdots \to v$。

**⟹ 直接复用第 63 轮的 `Reach`**（`Reach G u v` = `v` 是 `u` 的后代）。 -/
def Ancestor (G : CausalGraph V) (u v : V) : Prop :=
  CausalDescendant.Reach G u v

/-- ⭐⭐⭐ **祖先集合**：`S` **及其全体祖先**。

$$\mathrm{Anc}(S) := \{v \mid v \in S \vee \exists s \in S,\ u \to \cdots \to s\}$$

**⟹ 即**：**把 `S` 以及「`S` 所依赖的一切」都卷入**。 -/
def AncestralSet (G : CausalGraph V) (S : Set V) : Set V :=
  {v | v ∈ S ∨ ∃ s ∈ S, Ancestor G v s}

/-- ⭐⭐ **`S` 含于其祖先集合**（**顶点集包含目标集** —— 性质 1，第一半）。 -/
theorem subset_ancestralSet (G : CausalGraph V) (S : Set V) : S ⊆ AncestralSet G S :=
  fun _ hv => Or.inl hv

/-- ⭐⭐ **祖先关系自反**：每个点都是自己的祖先（长度为 0 的路径）。 -/
theorem ancestor_refl (G : CausalGraph V) (v : V) : Ancestor G v v :=
  CausalDescendant.reach_refl G v

/-- ⭐⭐⭐ **祖先集合是传递闭包**：若 `u` 是 `v` 的祖先、`v` 在祖先集合中，则 `u` 也在。

**⟹ 即**：**祖先集合对「取祖先」封闭**（**祖先闭包**）。 -/
theorem ancestor_mem_ancestralSet (G : CausalGraph V) {S : Set V} {v u : V}
    (hv : v ∈ AncestralSet G S) (hu : Ancestor G u v) : u ∈ AncestralSet G S := by
  rcases hv with hv | ⟨s, hs, hvs⟩
  · exact Or.inr ⟨v, hv, hu⟩
  · exact Or.inr ⟨s, hs, CausalDescendant.reach_trans G hu hvs⟩

/-- ⭐⭐⭐ **取两次祖先 = 取一次祖先**（**幂等性**）。

$$\mathrm{Anc}(\mathrm{Anc}(S)) = \mathrm{Anc}(S)$$

**⟹ 这是「祖先集合」作为**闭包算子**的核心性质。** -/
theorem ancestralSet_idem (G : CausalGraph V) (S : Set V) :
    AncestralSet G (AncestralSet G S) = AncestralSet G S := by
  apply Set.Subset.antisymm
  · -- 左边 ⊆ 右边：祖先的祖先还是祖先
    rintro v (hv | ⟨w, hw, hvw⟩)
    · exact hv
    · exact ancestor_mem_ancestralSet G hw hvw
  · -- 右边 ⊆ 左边：由 `S ⊆ Anc(S)` 与单调性
    exact subset_ancestralSet G (AncestralSet G S)

/-! ### §64.2 ⭐⭐⭐ 祖先图（诱导子图）

  **⚠ 关键设计**：祖先图是**保持有向结构**的**诱导子图** ——
  **顶点为 `Anc(S)`，边为「两端都在 `Anc(S)` 中的原图边」**。
  **⟹ 因此它**仍是一个 `CausalGraph`（仍是 DAG）**。** -/

/-- ⭐⭐⭐ **祖先图的邻接**：原图边 + **两端都在祖先集合中**（诱导子图）。

$$u \rightsquigarrow v \iff G.\mathrm{Adj}\,u\,v \wedge u \in \mathrm{Anc}(S) \wedge v \in \mathrm{Anc}(S)$$ -/
def AncestralAdj (G : CausalGraph V) (S : Set V) (u v : V) : Prop :=
  G.Adj u v ∧ u ∈ AncestralSet G S ∧ v ∈ AncestralSet G S

/-- ⭐⭐ **传递闭包的单调性**（**从「边集子集」推「环保持」的核心引理**）。

$$r \le p \implies \mathrm{TransGen}\,r \le \mathrm{TransGen}\,p$$ -/
theorem transGen_mono {r p : V → V → Prop} (h : ∀ {a b : V}, r a b → p a b) :
    ∀ {a b : V}, Relation.TransGen r a b → Relation.TransGen p a b := by
  intro a b hr
  induction hr with
  | single hab => exact Relation.TransGen.single (h hab)
  | tail hab hbc ih => exact ih.tail (h hbc)

/-- ⭐⭐⭐ **祖先图**：以 `AncestralAdj` 为邻接、**沿用 `G` 的无环性**的 `CausalGraph`。

**⟹ 无环性证明**：祖先图的每条边都是 `G` 的边（**边集子集**），
**故 `G` 中任何环在祖先图中也是环，与 `G` 无环矛盾。** -/
def AncestralGraph (G : CausalGraph V) (S : Set V) : CausalGraph V where
  Adj := AncestralAdj G S
  acyclic := by
    intro v hcycle
    -- 祖先图的边 ⊆ 原图的边 ⟹ 原图中也有环，矛盾
    exact G.acyclic v (transGen_mono (fun {_ _} h => h.1) hcycle)

/-- ⭐⭐⭐ **祖先图的顶点集含 `S`**（**性质 1 的形式化**）。

**⟹ 祖先图的顶点集恰为 `Anc(S)`；由 `S ⊆ Anc(S)`，目标集被完整含入。**
**⚠ 此处以「顶点集定义」显式陈述**： -/
theorem ancestral_vertex_contains (G : CausalGraph V) (S : Set V) :
    S ⊆ {v | v ∈ AncestralSet G S} :=
  subset_ancestralSet G S

/-- ⭐⭐ **祖先图的边 ⊆ 原图的边**（**诱导子图不新增边**）。 -/
theorem ancestralAdj_sub (G : CausalGraph V) (S : Set V) {u v : V}
    (h : AncestralAdj G S u v) : G.Adj u v :=
  h.1

/-- ⭐⭐⭐ **祖先图边集的**单调性**（性质 2，祖先图版）。

$$S \subseteq T \implies \mathrm{Anc}(S) \subseteq \mathrm{Anc}(T)
  \implies \mathrm{Adj}_{\mathrm{anc}}(S) \subseteq \mathrm{Adj}_{\mathrm{anc}}(T)$$

**⟹ 即**：**目标集越大，祖先图的边越多** ——
**（顶点集与边集**同时单调**，因为祖先集合本身随 `S` 单调）。** -/
theorem ancestralAdj_mono (G : CausalGraph V) {S T : Set V} (hST : S ⊆ T) :
    ∀ {u v : V}, AncestralAdj G S u v → AncestralAdj G T u v := by
  intro u v h
  obtain ⟨hadj, hu, hv⟩ := h
  -- 先用「祖先集合随 `S` 单调」把两个端点搬过去
  have hanc : AncestralSet G S ⊆ AncestralSet G T := by
    intro w hw
    rcases hw with hw | ⟨s, hs, hws⟩
    · exact Or.inl (hST hw)
    · exact Or.inr ⟨s, hST hs, hws⟩
  exact ⟨hadj, hanc hu, hanc hv⟩

/-! ### §64.3 ⭐⭐⭐ 道德化图

  **道德化**：**把「有共同子节点的父节点」两两连边**（**使「共享子节点」的
  隐藏混杂结构显式化**）。

  **⚠ 关键观察：道德化图**不是 DAG**。
  **若 `u, v` 同为一个子节点 `w` 的双亲，道德化会同时加 $u \to v$ 与 $v \to u$**
  **（无向边）** —— **这立即形成 2-环，故**不可**再当作 `CausalGraph`。**
  **⟹ 因此本节**如实**把道德化图建模为一个**无向**邻接关系**，
  **并显式证明其对称性**。** -/

/-- ⭐⭐⭐ **道德化邻接**：祖先图的边（**取对称**）$\cup$ **「同为某节点的双亲」的配对**。

$$u \operatorname{MoralAdj} v :=
  \underbrace{u \rightsquigarrow v \vee v \rightsquigarrow u}_{\text{祖先图的边（无向化）}}
  \;\vee\; \underbrace{\exists w,\ u \rightsquigarrow w \wedge v \rightsquigarrow w}_{\text{共享子节点 } w}$$

**⟹ 第一项把祖先图的**有向**边**无向化**（道德化图是**无向图**）；
**第二项即**：**「`u, v` 都有边指向同一个 `w`，则 `u, v` 连边」**
—— **这是道德化（moralization）的本质操作。** -/
def MoralAdj (G : CausalGraph V) (S : Set V) (u v : V) : Prop :=
  AncestralAdj G S u v ∨ AncestralAdj G S v u ∨
    ∃ w, AncestralAdj G S u w ∧ AncestralAdj G S v w

/-- ⭐⭐⭐ **道德化图无向**（**对称性**）。

$$u \operatorname{MoralAdj} v \implies v \operatorname{MoralAdj} u$$

**⟹ 这是「道德化」把有向图**变成无向图**的形式化保证** ——
**同时也是道德化图**不能**是 `CausalGraph`（会形成 2-环）的**同一枚硬币的另一面**。** -/
theorem moralAdj_symm (G : CausalGraph V) (S : Set V) {u v : V}
    (h : MoralAdj G S u v) : MoralAdj G S v u := by
  rcases h with h | h | ⟨w, huw, hvw⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨w, hvw, huw⟩)

/-- ⭐⭐⭐ **道德化图含祖先图的全部边**（**性质 2 的加强：道德化 ⊇ 祖先**）。

$$u \rightsquigarrow v \implies u \operatorname{MoralAdj} v$$

**⟹ 即**：**道德化只**新增**边（共享子节点的配对），**绝不删除**原有边**。** -/
theorem moral_superset (G : CausalGraph V) (S : Set V) :
    ∀ {u v : V}, AncestralAdj G S u v → MoralAdj G S u v := by
  intro u v h
  exact Or.inl h

/-- ⭐⭐⭐ **道德化邻接的**单调性**（性质 2，道德化版）。

$$S \subseteq T \implies \operatorname{MoralAdj}(S) \subseteq \operatorname{MoralAdj}(T)$$

**⟹ 即**：**目标集越大，道德化图的边也越多** ——
**（第一、二项随祖先图单调；第三项的「共享子节点」随祖先图单调）。** -/
theorem moralAdj_mono (G : CausalGraph V) {S T : Set V} (hST : S ⊆ T) :
    ∀ {u v : V}, MoralAdj G S u v → MoralAdj G T u v := by
  intro u v h
  have hanc : ∀ {a b : V}, AncestralAdj G S a b → AncestralAdj G T a b :=
    ancestralAdj_mono G hST
  rcases h with h | h | ⟨w, huw, hvw⟩
  · exact Or.inl (hanc h)
  · exact Or.inr (Or.inl (hanc h))
  · exact Or.inr (Or.inr ⟨w, hanc huw, hanc hvw⟩)

/-! ### §64.4 ⭐⭐ 道德化与「共同子节点」的显式刻画

  **把道德化的**语义**抽成一条引理**：
  **道德化图的两点要么在原祖先图中相邻，要么**共享一个子节点**。** -/

/-- ⭐⭐ **道德化边的**分类刻画**（正向）。

**⟹ 即**：**每一条道德化边，或来自祖先图（无向化），或来自「共享子节点」** ——
**这是道德化的**完备性陈述**（定义即此，此处固定为可复用的引理形式）。** -/
theorem moralAdj_cases (G : CausalGraph V) (S : Set V) {u v : V}
    (h : MoralAdj G S u v) :
    AncestralAdj G S u v ∨ AncestralAdj G S v u ∨
      ∃ w, AncestralAdj G S u w ∧ AncestralAdj G S v w :=
  h

/-- ⭐⭐ **共同子节点判据**：**若 `u, v` 都指向 `w` 且 `w` 在祖先集合中，则 `u, v` 道德化相邻**。

**⟹ 这是**道德化「连父节点」操作**的直接入口。** -/
theorem moralAdj_of_common_child (G : CausalGraph V) (S : Set V) {u v w : V}
    (hu : AncestralAdj G S u w) (hv : AncestralAdj G S v w) :
    MoralAdj G S u v :=
  Or.inr (Or.inr ⟨w, hu, hv⟩)

/-- ⭐⭐ **祖先邻接判据**：**原图边 + 两端在祖先集合中 ⟹ 祖先图相邻**。

**⟹ 这是**从原图构造祖先图**的直接入口。** -/
theorem ancestralAdj_of (G : CausalGraph V) (S : Set V) {u v : V}
    (hadj : G.Adj u v) (hu : u ∈ AncestralSet G S) (hv : v ∈ AncestralSet G S) :
    AncestralAdj G S u v :=
  ⟨hadj, hu, hv⟩

end Ancestral

end FateV2.Predict