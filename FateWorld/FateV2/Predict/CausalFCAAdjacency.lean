/-
命运理论 · Lean 4 形式化实现
================================

模块：CausalFCAAdjacency
定位：**裁决 B-1 · 邻接级** —— 把因果 DAG 装进 FCA 形式背景，
      使 `gazeUp` / `gazeDown` 能作用在因果图上。

===========================================================================
⚠ 一、语义诚实登记（本文件最先要读的部分）
===========================================================================

**本文件属于「邻接级」，不是「因果进入分类」。**

本文件的 `Irel` 只用了一阶邻域（`G.edge a b ∨ G.edge b a`），
即**有向边的对称化 → 无向邻接**。它**不承载任何 d-分离语义**：

* **方向被抹掉**：`ctxOf_Irel_eq_UAdj` 证明本 `Irel` 逐字等于无向邻接谓词；
  同一骨架（skeleton）可对应多个方向性不同、d-分离集合不同的 DAG。
  故「同一 `Irel`、不同 DAG」是可能的（`ctxOf_forgets_direction` 给出形式证据：
  两个方向相反的双点 DAG 给出**逐点相同**的 `Irel`）。
* **d-分离是三元关系**：`dSep X Y Z` 有**三个**参数，
  而 `FormalCtx.Irel` 是**二元**关系（`GFCA → MFCA → Prop`）。
  ⟹ 用 `FormalCtx` 装 d-分离语义在**类型层就装不下**。
  这是本文件最重要的技术边界，**不是实现偷懒**。
* **两种目光在本构造下同形**：因 `Irel` 对称，
  `gazeUp {o}` 与 `gazeDown {o}` 给出**同一个**无向邻域
  （`gazeUp_gazeDown_singleton_eq`）。而在哲学解读里
  向上（归类）与向下（解构）应当**相反**。**此同形本身即是
  「语义未接入」的形式证据**，不应被读成「两种目光等价」。

**⟹ 因此本文件证明的一切都只是「接口能接上、算子能复合、类型能通过」。**
**本文件不声称「因果进入分类」。** 需要语义接入时，
必须改造 `FormalCtx`（把 `Irel` 换成三元或带上下文的编码），
那是**另一个**构造，须重新核验 Galois 结构是否仍成立——**很可能不成立**。

===========================================================================
⚠ 二、与既有模块 Fate/CausalClassificationBridge.lean 的关系
===========================================================================

核实（`ls Fate/CausalClassificationBridge.lean` + `grep -n` 两种模式）：
该文件**已存在**且**编译通过**，内容与本文件高度重叠
（同一定义 `ctxOf`、同一批单点目光定理、同一份语义诚实声明）。

**但**：`grep -n 'CausalClassificationBridge' lean` **无结果**，
即该文件**未被根模块 `lean` import**，**不在构建图中**。

本文件按裁决 B-1 的指示**新建、自足、不改任何已有模块**（含不改 `lean`）。
本文件**自带**命名空间 `CausalFCAAdjacency`，与上述文件的
`CausalClassificationBridge` **不冲突**（同名不同命名空间）。
**本文件不声称**取代或修正该文件；两者可并存，取舍由主控裁决。

===========================================================================
⚠ 三、本文件实际证明的定理（共 10 条，`grep -c '^theorem'` = 10 可核对）
===========================================================================

§1  定义与 `rfl` / `Iff.rfl` 级相容性引理
  · `ctxOf`                                    （定义，非定理）
  · `ctxOf_GFCA_eq`        : `(ctxOf G).GFCA = V`                   （`rfl`）
  · `ctxOf_Irel_eq`        : `(ctxOf G).Irel a b ↔ E a b ∨ E b a`   （`Iff.rfl`）
  · `ctxOf_Irel_eq_UAdj`   : `(ctxOf G).Irel a b ↔ G.UAdj a b`      （`Iff.rfl`）

§2  向上目光
  · `mem_gazeUp_singleton` : `w ∈ gazeUp {o} ↔ E o w ∨ E w o`
  · `gazeUp_singleton`     : `gazeUp {o} = {w | E o w ∨ E w o}`     ← 目标定理 (b)

§3  向下目光的对偶
  · `mem_gazeDown_singleton` : `v ∈ gazeDown {w} ↔ E v w ∨ E w v`
  · `gazeDown_singleton`     : `gazeDown {w} = {v | E v w ∨ E w v}` ← 目标定理 (c)

§4  语义诚实登记的形式化证据
  · `fwd_ne_bwd_edge`      : 两个反向双点 DAG 的边关系**不同**
  · `ctxOf_forgets_direction` : 两个反向双点 DAG 的 `Irel` **逐点等价**
  · `gazeUp_gazeDown_singleton_eq` : `gazeUp {o} = gazeDown {o}`（两目光同形）

**未证明的、本文件不声称的**：任何 d-分离相关结论（见 §一）。

===========================================================================
⚠ 四、技术要点：类型透明度（上一轮卡死处）
===========================================================================

上一轮的障碍是 Lean 的 semireducible definition unfolding 让 `rw` 找不准式子。
本文件的做法：**先 `show` 把目标类型显式写成 `unfold` 后的形状，
再 `ext` / `simp only`**。具体：

* `gazeUp_singleton` 里先 `show` 出 `{w : V | _}` 形式（把 `(ctxOf G).MFCA`
  这个投影项换成 `V`），`ext w` 后目标即退化为纯 `Prop` 等价，可 `simp` 关闭。
* 若直接 `rw [mem_upperPolar_iff]` 而不先 `show`，`upperPolar` 的隐式参数
  `α β` 会与 `(ctxOf G).GFCA` / `(ctxOf G).MFCA` 的**投影形式**对不上，
  报 "motive is not type correct" 或 "rw 找不到匹配"。
  **先 `show` 固定类型，再走纯 `simp only`。**（实测：换成 `rw` 即失败。）

===========================================================================
⚠ 五、上一轮的失败与本次修正（如实记录）
===========================================================================

`_quarantine/_broken/CausalFCAAdjacency.lean` 记录的上一版实测为
**EXIT=1，3 error + 2 处 `sorry`**，错误是：

1. `Invalid field UAdj` —— **猜错位置**：`UAdj` 不在 `CausDAG` 里，
   而在 `CausActivePath.lean`（`Causalean.Graph.DAG.UAdj`）。
   **修正**：`import CausActivePath`。
2. `Type mismatch when assigning motive`（`fwd`/`bwd` 的 `acyclic`，两处）——
   `Relation.TransGen` 的归纳在目标为 `v v`（端点相同）时无法泛化。
   **修正**：改为对**任意端点**陈述的辅助命题（路径起点恒为 `0`、终点恒为 `1`），
   再合并两式得 `0 = 1` 矛盾。

上一版残留的 2 处 `sorry` **已全部消除**：`fwd` / `bwd` 的 `acyclic` 现已
给出完整证明（见 §4）。**本文件零 `sorry` / `admit` / `axiom`。**

===========================================================================
⚠ 六、纪律
===========================================================================

两遍 `lake env lean Fate/CausalFCAAdjacency.lean`，两遍 EXIT=0（见交付说明）。
不跑全量 `lake build`。不改任何已有文件（含 `lean`）。
-/

import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Classification
import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausActivePath
import Mathlib.Tactic

namespace FateV2.Predict

open FateV2.Modeling
open FateV2.Rules
namespace CausalFCAAdjacency

open FateV2.Modeling.Graph
open Set

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-!
  # Predict · CausalFCAAdjacency

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausalFCAAdjacency.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FCA, Classification, _root.CausDAG, _root.CausActivePath
  - 补充 open 域：FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  定义与 `rfl` / `Iff.rfl` 级相容性引理
    ======================================================================== -/

/-- **把因果 DAG 装进形式背景**（邻接级的核心构造）。

给定 $G=(V,E)$，令

* `GFCA := V`（顶点 = 对象）
* `MFCA := V`（顶点 = 属性，自反背景）
* `Irel a b := E(a,b) ∨ E(b,a)`（**有向边对称化 = 无向邻接**）

**⚠ 语义边界（见文件头 §一）**：此 `Irel` 只用一阶邻域，
方向信息在此处即被抹掉，**不承载 d-分离语义**。
本构造是**邻接级接入**，不是「因果进入分类」。 -/
def ctxOf (G : DAG V) : FateV2.Rules.FormalCtx where
  GFCA := V
  MFCA := V
  Irel := fun a b => G.edge a b ∨ G.edge b a

/-- **相容性引理（`rfl`）**：`ctxOf G` 的对象集就是 `V`。

`rfl` 级——因为 `ctxOf` 的定义里 `GFCA` 直接取 `V`，
本引理把「投影后仍是 `V`」这一事实固化为可复用的重写规则。 -/
theorem ctxOf_GFCA_eq (G : DAG V) : (ctxOf G).GFCA = V := rfl

/-- **相容性引理（`Iff.rfl`）**：`ctxOf G` 的关系就是对称化的有向边。

`Iff.rfl` 级——两侧在定义上**逐字相同**，故本引理**不含任何数学内容**，
作用是给下游一条**不被 `ctxOf` 的 semireducible 展开卡住**的入口。 -/
theorem ctxOf_Irel_eq (G : DAG V) (a b : V) :
    (ctxOf G).Irel a b ↔ G.edge a b ∨ G.edge b a := Iff.rfl

/-- **本构造只记住无向邻接**：`ctxOf G` 的 `Irel` 逐字等于 `DAG.UAdj`。

`Iff.rfl` 级（`UAdj` 本身就是对称化的边）。**这是「邻接级」的正式标记**：
本条给出「本 `Irel` 不含方向信息」的第一条形式证据。

**依据位置**：`UAdj` 定义在 `CausActivePath.lean:65`（`Causalean.Graph.DAG.UAdj`），
**不在** `CausDAG.lean`——故本文件显式 `import CausActivePath`。 -/
theorem ctxOf_Irel_eq_UAdj (G : DAG V) (a b : V) :
    (ctxOf G).Irel a b ↔ G.UAdj a b := Iff.rfl

/-! ===========================================================================
    §2  向上目光 `gazeUp` 的单点定理（目标定理 (b)）
    ======================================================================== -/

/-- ⭐ **成员判据**：`w` 属于「`o` 的向上目光」⟺ `o` 与 `w` 无向相邻。

**技术要点**：先 `show` 把 `MFCA` 投影换成裸 `V`，再做纯 `simp only`，
避免类型透明度过低导致 `rw` 失配（见文件头 §四）。 -/
theorem mem_gazeUp_singleton (G : DAG V) (o w : V) :
    w ∈ (ctxOf G).gazeUp ({o} : Set (ctxOf G).GFCA) ↔ (G.edge o w ∨ G.edge w o) := by
  show (∀ ⦃a⦄, a ∈ ({o} : Set V) → (G.edge a w ∨ G.edge w a)) ↔ _
  simp only [Set.mem_singleton_iff, forall_eq]

/-- ⭐⭐ **目标定理 (b)**：向上目光作用在单点集上 = **该点的无向邻域**。

$$\mathrm{gazeUp}_{G}(\{o\}) = \{w \mid E(o,w)\lor E(w,o)\}$$

**⚠ 语义裁定**：右侧是**无向邻域**，不是任何因果判据
（见文件头 §一）。本定理证明的是「接口能接上、算子能复合」，
**不是**「因果进入分类」。

**⚠ 非同义反复核对**：前件只有 `G : DAG V` 与 `o : V`，
结论是一个**集合等式**（需逐点核验 `gazeUp` 的展开式）；
右侧 `{w | E o w ∨ E w o}` **不是**从前件直接抄来的命题。 -/
theorem gazeUp_singleton (G : DAG V) (o : V) :
    (ctxOf G).gazeUp ({o} : Set (ctxOf G).GFCA) =
      {w : V | G.edge o w ∨ G.edge w o} := by
  show {w : V | ∀ ⦃a⦄, a ∈ ({o} : Set V) → (G.edge a w ∨ G.edge w a)}
      = {w : V | G.edge o w ∨ G.edge w o}
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]

/-! ===========================================================================
    §3  向下目光 `gazeDown` 的对偶（目标定理 (c)）
    ======================================================================== -/

/-- **成员判据（`gazeUp` 的对偶）**：`v` 属于「`w` 的向下目光」⟺ `v` 与 `w` 无向相邻。 -/
theorem mem_gazeDown_singleton (G : DAG V) (v w : V) :
    v ∈ (ctxOf G).gazeDown ({w} : Set (ctxOf G).MFCA) ↔ (G.edge v w ∨ G.edge w v) := by
  show (∀ ⦃b⦄, b ∈ ({w} : Set V) → (G.edge v b ∨ G.edge b v)) ↔ _
  simp only [Set.mem_singleton_iff, forall_eq]

/-- ⭐⭐ **目标定理 (c)**：向下目光作用在单点集上 = **该点的无向邻域**。

$$\mathrm{gazeDown}_{G}(\{w\}) = \{v \mid E(v,w)\lor E(w,v)\}$$

**⚠ 与 `gazeUp_singleton` 合看**：因 `Irel` 对称，两式右侧只是
「`o` 与 `w` 相邻」的不同书写，**结果同形**——见
`gazeUp_gazeDown_singleton_eq`。**这本身是语义未接入的证据**：
哲学上应**相反**的两种目光，在邻接级构造下**给出同一集合**。 -/
theorem gazeDown_singleton (G : DAG V) (w : V) :
    (ctxOf G).gazeDown ({w} : Set (ctxOf G).MFCA) =
      {v : V | G.edge v w ∨ G.edge w v} := by
  show {v : V | ∀ ⦃b⦄, b ∈ ({w} : Set V) → (G.edge v b ∨ G.edge b v)}
      = {v : V | G.edge v w ∨ G.edge w v}
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]

/-! ===========================================================================
    §4  语义诚实登记的形式化证据
    ======================================================================== -/

/-- **`fwd`**：双点图上的单边 `0 → 1`（合法 DAG）。

无环性证法：`Relation.TransGen` 中每条路径的**起点恒为 `0`**、**终点恒为 `1`**
（见两个内层 `have`），故自反路径需 `0 = 1`，矛盾。
**上一轮此处用 `TransGen` 直接归纳失败**（端点同为 `v` 时无法泛化 motive），
改为对**任意端点**陈述的辅助命题后才通过。 -/
def fwd : DAG (Fin 2) where
  edge := fun a b => a = 0 ∧ b = 1
  decEdge := by infer_instance
  acyclic := by
    intro v h
    have src : ∀ a b : Fin 2,
        Relation.TransGen (fun a b : Fin 2 => a = 0 ∧ b = 1) a b → a = 0 := by
      intro a b hh
      induction hh with
      | single he => exact he.1
      | tail _ he ih => exact ih
    have tgt : ∀ a b : Fin 2,
        Relation.TransGen (fun a b : Fin 2 => a = 0 ∧ b = 1) a b → b = 1 := by
      intro a b hh
      induction hh with
      | single he => exact he.2
      | tail _ he ih => exact he.2
    have hv0 : v = 0 := src v v h
    have hv1 : v = 1 := tgt v v h
    rw [hv0] at hv1
    exact absurd hv1 (by decide)

/-- **`bwd`**：与 `fwd` **方向相反**的 DAG（单边 `1 → 0`，同为合法 DAG）。 -/
def bwd : DAG (Fin 2) where
  edge := fun a b => a = 1 ∧ b = 0
  decEdge := by infer_instance
  acyclic := by
    intro v h
    have src : ∀ a b : Fin 2,
        Relation.TransGen (fun a b : Fin 2 => a = 1 ∧ b = 0) a b → a = 1 := by
      intro a b hh
      induction hh with
      | single he => exact he.1
      | tail _ he ih => exact ih
    have tgt : ∀ a b : Fin 2,
        Relation.TransGen (fun a b : Fin 2 => a = 1 ∧ b = 0) a b → b = 0 := by
      intro a b hh
      induction hh with
      | single he => exact he.2
      | tail _ he ih => exact he.2
    have hv1 : v = 1 := src v v h
    have hv0 : v = 0 := tgt v v h
    rw [hv1] at hv0
    exact absurd hv0 (by decide)

/-- `fwd` 与 `bwd` 的边关系**不同**（前者 `edge 0 1` 成立，后者不成立）。

**这是 `ctxOf_forgets_direction` 的「前件确实有区别」的证据**——
保证后者不是在比较两个相同对象（非同义反复）。 -/
theorem fwd_ne_bwd_edge : fwd.edge (0 : Fin 2) 1 ∧ ¬ bwd.edge (0 : Fin 2) 1 := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  simp [bwd]

/-- ⭐⭐ **方向在 `ctxOf` 处被抹掉**：`fwd` 与 `bwd` 的 `Irel` **逐点等价**。

尽管 `fwd_ne_bwd_edge` 说明两者边关系**不同**，对称化后
`ctxOf fwd` 与 `ctxOf bwd` 的关系**完全相同**。
**⟹ 只依赖 `ctxOf` 的目光算子不可能恢复方向**，d-分离语义无从接入。

**非同义反复核对**：前件 `fwd`、`bwd` 是**两个实际不同**的 DAG
（`fwd_ne_bwd_edge` 已证其边关系不同），结论是它们经 `ctxOf` 后关系等价。
这是**真命题**，需逐点分情况核验 `∨` 两侧的交换，**不能由前件直接抄出**；
若两者是同一个 DAG 则本定理将退化为 `rfl`——**但它们不是**。 -/
theorem ctxOf_forgets_direction (a b : Fin 2) :
    (ctxOf fwd).Irel a b ↔ (ctxOf bwd).Irel a b := by
  simp only [ctxOf_Irel_eq, fwd, bwd]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩

/-- ⭐ **两种目光在单点上给出同一集合**（语义未接入的形式证据）。

`gazeUp {o}` 与 `gazeDown {o}` 作为集合**相等**——
两者都等于 `o` 的无向邻域。

**⚠ 解读纪律**：本定理**不**表示「向上目光 = 向下目光」在哲学上成立；
它表示**在邻接级构造下两者无法区分**，因为 `Irel` 对称
（`ctxOf_Irel_eq` 的右侧是 `∨`，交换即可）。**这正是需要语义接入的理由**。 -/
theorem gazeUp_gazeDown_singleton_eq (G : DAG V) (o : V) :
    (ctxOf G).gazeUp ({o} : Set (ctxOf G).GFCA)
      = (ctxOf G).gazeDown ({o} : Set (ctxOf G).MFCA) := by
  show {w : V | ∀ ⦃a⦄, a ∈ ({o} : Set V) → (G.edge a w ∨ G.edge w a)}
      = {v : V | ∀ ⦃b⦄, b ∈ ({o} : Set V) → (G.edge v b ∨ G.edge b v)}
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, or_comm]

end CausalFCAAdjacency
end FateV2.Predict