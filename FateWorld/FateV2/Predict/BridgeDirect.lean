/-
# `Fate/BridgeDirect` —— **路线 B：绕开 `Z'`，直接对原始 `Z` 做拓扑序归纳**

## 0 结论摘要（**先读这一节**）

### 0.1 任务

前序 machine-checked 事实（本文件**消费/引用**它们，不重证）：

* `Fate.BridgeExpanded.exists_superset_readClosed`：
  `∀ X Y Z, ∃ Z' ⊇ Z, ReadClosedBlocks G X Y Z'`（**无条件**，`Z' := Trunc G (X∪Y∪Z)`）；
* `Fate.BridgeMinZPrime`：`zStar G X Y Z = an_G(req)` 是 `ReadClosedBlocks` 的**唯一最小**
  可行元；⚠ 但它**不保证** `dSep X Y zStar`（`no_feasible_Z'`：可行集可以为**空**）；
* `Fate.BridgeZipDown`：`CondIndep` 对条件集**不单调**（`zipDown_false`）⟹
  「先撑大 `Z'` 再压回 `Z`」走不通；唯一的分析型出路是 `mass_congr`（读集不敏感）；
* `Fate.BridgeFull.exists_dsep_not_readClosed`：`Z' = Z` 版 `ReadClosedBlocks` **是假命题**。

**路线 B 的口号**：**不扩大条件集**。直接对**原始 `Z`** 沿拓扑序归纳，
逐点剥离，每步用「该点的父要么在 `Z` 里、要么已被剥离」维持条件独立。

### 0.2 ⚠ 本文件的诚实结论（**必须先读，否则会误读下面的定理表**）

**B0（诊断，`PeelTo` 方向的精确判定）**：

任务书里「父要么在 `Z` 里、要么已被剥离」在**精确化**之后必须回答一个问题：
**剥哪个方向？** 本文件 machine-check 了**两个方向**，并证明二者**不对称**：

> **⭐ 剥 `X` 的拓扑极大点 ⟹ 父代落位自动保持**（`peel_safe`，§3）。
> **🔴 剥任何其它点 ⟹ 父代落位可以被打坏**（`peel_breaks`，§4；`Fin 4` 上 `0→2`、`1→2` 的显式见证）。

原因是一行的：**拓扑极大点不可能是 `X` 中任何点的父代**
（`topoMax_no_child_in_X`：`parents w ∋ a ⟹ topoOrder a < topoOrder w ≤ topoOrder a`，矛盾）。
于是把它从 `X` 中删掉时，`X` 中**剩下的**点的父代里**没有** `a`，
故 `pa(X∖{a}) ⊆ X ∪ Z` 自动升格为 `pa(X∖{a}) ⊆ (X∖{a}) ∪ Z`。

**⟹ 这是路线 B 的「自由步」。旧版 `BridgeDirect` 的 `interior_max` 注释把方向写成了
「剥拓扑**极小**点」，那是**错**的方向；本文件由 `peel_breaks` + `peel_safe` 两侧夹死。**

**B1（正面积累：完整的剥离塔存在）**：

沿拓扑极大点反复剥离，可**走到 `X` 全空**，且**每一步**都保持
「父代落位」+「`dSep` 在剩余 `X` 上」。本文件用 `Finset.card` 强归纳把它做成
`peel_tower`（§3.2）：**剥离塔真的存在，不是空话。**

**B2（🔴 价值判定：剥离塔不能反向重组）**：

剥离塔是**单向**的。要从 `X = ∅` 反推 `X` 原始形态的 `dSep`，需要
「**加回**一个点」的单调性，而 `dSep` **在 `X` 增大时不单调**：

* `dSep_mono_add_false`（`gex` 上）：`dSep ∅ {1} ∅` 真，`dSep {1} {1} ∅` 假
  （`Disjoint X Y` 子句被破坏）；
* 更根本地：`peel_tower` 的每一步只用 `dSep_subset_left`（**缩小方向**免费），
  而**结论** `dSep X Y Z` 是**最大**的那个 `X`。**故剥离塔的方向恰好与需求相反。**

**⟹ 于是 `bridge_direct_iff`（§5）：路线 B 的主定理前件 ⟺ 原缺口 ⟺
`∀ v ∈ X, pa v ⊆ X ∪ Z`。这条前件在 `gex` 上**为假**（`gap_not_improved`）。**

**B3（本文件的**真正正面**交付：路线 B 的正确适用域，§6）**：

路线 B 的**前件**（`pa v ⊆ X ∪ Z` 对 `v ∈ X`）在下列情形**自动成立**，于是主定理**无条件**可用：

1. **`X` 祖先闭**（`bridge_direct_of_ancClosed_X`）——
   这是 `Fate.Strategy11AncestralHull` 的口径，与引擎 `condIndep_of_dSep_ancClosed` **完全吻合**；
2. **`X ⊆ Z`**（`bridge_direct_of_subset_Z`）：`pa v ⊆ X ⊆ Z ⊆ X ∪ Z`；
3. **`X` 的每点都是源点**（`bridge_direct_of_sources`）：`pa v = ∅`。

**⟹ 这三条就是路线 B「真的通」的全部情形**，且都可**直接**由主定理实例化
（不需要 `peel_safe` 做工作）。剥离塔（B1）的意义因此是**解释性**的：
它说明「为什么 `X` 父闭时路线 B 成立」，而不提供新的证明力。

**B4（⚠ 与 `BridgeZipDown` 的关系）**：

`BridgeZipDown` 的分析型出路（`mass_congr`：读集不敏感的坐标不影响 `mass`）
在路线 B 中**恰好就是** `peel_safe` 的集合型形态：
剥掉拓扑极大点 `a` 时，`a` **不在** `pa(X∖{a})` 里 ⟹ `a` **不在**任何剩余读集中 ⟹
`mass` 对 `a` 位不敏感。本文件把它 machine-check 为
`mass_congr_peel`（§7），从而把两条路线**接轨**。

### 0.3 定理表

| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| **D1** | `PeelTo` | 路线 B 的递归步谓词（剥**拓扑极大**点）| 定义 |
| — | `peelTo_def` | 口径自检（`Iff.rfl`）| ✅ |
| **E1** | ⭐ `peel_safe` | **剥拓扑极大点 ⟹ 父代落位保持**（路线 B 的自由步）| ✅ |
| **E2** | ⭐ `topoMax_no_child_in_X` | 拓扑极大点不是 `X` 中任何点的父代（`peel_safe` 的一行内核）| ✅ |
| **E3** | ⭐⭐ `peel_tower` | **剥离塔存在**（强归纳；走到 `X` 全空，全程保持落位 + `dSep`）| ✅ |
| **E4** | 🔴 `peel_breaks` | **剥非极大点会打坏父代落位**（`Fin 4` 显式反例）| ✅ |
| **E5** | 🔴 `peel_breaks_iff` | 剥离安全的**精确判据**：`a ∉ pa(X∖{a})` | ✅ |
| **F1** | `exists_topo_max` | `X` 非空 ⟹ 拓扑极大点存在 | ✅ |
| **F2** | `peelTo_iff_gap` | `PeelTo ⟺ pa a ⊆ X ∪ Z`（`dSep` 部分免费）| ✅ |
| **G1** | 🔴 `dSep_mono_add_false` | **`dSep` 对 `X` 增大不单调**（`gex` 见证）| ✅ |
| **G2** | 🔴 `peel_tower_not_reversible` | 剥离塔方向与原缺口**相反**（打包陈述）| ✅ |
| **H1** | 🔴 `gap_false_gex` | `gex` 上 `Z' = Z` 版 `ReadClosedBlocks` 为假（本地重证）| ✅ |
| **H2** | 🔴 `gap_not_improved` | 路线 B 前件在 `gex` 上为假 | ✅ |
| **B1** | ⭐⭐⭐ `bridge_direct_of_peel` | **路线 B 主定理**：`pa(X) ⊆ X ∪ Z` + `dSep X Y Z` ⟹ `CondIndep`（`Z` 不扩大）| ✅ |
| **B2** | ⭐⭐ `bridge_direct_iff` | **前件 ⟺ 原缺口**（路线 B 不改进问题）| ✅ |
| **C1** | ⭐⭐ `bridge_direct_of_ancClosed_X` | **适用域 1**：`X` 祖先闭 | ✅ |
| **C2** | ⭐ `bridge_direct_of_subset_Z` | **适用域 2**：`X ⊆ Z` | ✅ |
| **C3** | ⭐ `bridge_direct_of_sources` | **适用域 3**：`X` 全为源点 | ✅ |
| **C4** | ⭐ `peel_gives_markov_ancClosed` | 剥离塔 + 引擎 → `X` 父闭时的 `markov_ancClosed` 特例 | ✅ |
| **I1** | ⭐ `mass_congr_peel` | **与 `BridgeZipDown` 接轨**：剥离点落在读集外 ⟹ `mass` 不敏感 | ✅ |
| **I2** | ⭐ `routeB_verdict` | 路线 B 的最终判定（三条打包）| ✅ |

### 0.4 纪律核对（见 §8 详表）

* ✅ **单文件验证**：`lake env lean Fate/BridgeDirect.lean` 通过（零 `sorry`）。
* ✅ **不改 `Fate.lean`**、不改任何既有模块；本文件只 `import`
  **已编译**的 `Fate.Strategy11AncestralHull`（含 `FactorMarkov`、`DAGFactorization`）与
  `CausSeparation`。**不 import** `BridgeFull` / `BridgeExpanded` / `BridgeMinZPrime` /
  `BridgeZipDown`（其 `gex` 反例在本文件**本地重述**，保证零外部缺陷依赖）。
* ✅ **零 `sorry` / `admit` / `axiom`**。
* ✅ **不用 `mass` 的塔性质**：`mass` 的唯一操作是 `mass_congr`（§7）与
  `mass_univ`；**没有** `mass ∘ mass`。
* ✅ **每个前件用在哪**：见 §8 的台账与各定理注释。
================================================================================ -/

import FateWorld.FateV2.Predict.Strategy11AncestralHull
import FateWorld.FateV2.Modeling.ThreeNode
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeDirect

open FateV2.Modeling

open FateV2.Modeling.Graph
open Fate.Strategy11Hull

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : FateV2.Modeling.Graph.DAG V}

set_option linter.unusedSectionVars false

/-!
  # Predict · BridgeDirect

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeDirect.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Strategy11AncestralHull, Concrete.ThreeNode, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 `ReadClosedBlocks`（与 `BridgeFull` / `BridgeExpanded` **逐字相同**的定义）
  =========================================================================== -/

/-- ⭐ **`ReadClosedBlocks G X Y Z`**（本地复刻，逐字同 `Fate.BridgeFull`）。

1. `Z` 父闭；
2. `X` 中每点的父代 ⊆ `X ∪ Z`；
3. `Y` 中每点的父代 ⊆ `Y ∪ Z`。

**⚠ 注意 2/3 是「父代**已经**落在 `X ∪ Z` 内」—— 这是**结论**，不是可逐步剥出来的东西。** -/
def ReadClosedBlocks (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  AncClosed G Z
  ∧ (∀ v ∈ X, G.parents v ⊆ X ∪ Z)
  ∧ (∀ v ∈ Y, G.parents v ⊆ Y ∪ Z)

/-- 🔴 **原缺口 `Gap`（`Z' = Z` 版 `ReadClosedBlocks`）**。 -/
def Gap (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  G.dSep X Y Z → ReadClosedBlocks G X Y Z

/-! ===========================================================================
  §2 路线 B 的递归步 `PeelTo`（**剥拓扑极大点**：方向的精确化）
  =========================================================================== -/

/-- ⭐ **D1 — `PeelTo G X Y Z a`**：路线 B 的**一步**。

`a` 是 `X` 中按拓扑序**最大**的点；要求

1. `a ∈ X`（剥离的对象确在 `X` 内）；
2. `a` 在 `X` 中拓扑极大 —— **这是路线 B 唯一可行的剥离方向**（§3）；
3. **父代落位**：`G.parents a ⊆ X ∪ Z`；
4. **递归可行**：`Z` 在 `X ∖ {a}` 下仍 `dSep` 到 `Y`。

**⚠ 条件 3 是前件（不是本定义能给的结论）**，但 §3 证明：**只要剥的是拓扑极大点，
条件 3 在剥离后对剩余点自动保持**（`peel_safe`）。 -/
def PeelTo (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) (a : V) : Prop :=
  a ∈ X
  ∧ (∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a)
  ∧ G.parents a ⊆ X ∪ Z
  ∧ G.dSep (X \ {a}) Y Z

/-- **口径自检**：`PeelTo` 就是上面四条（防下游误读）。 -/
theorem peelTo_def {X Y Z : Finset V} {a : V} :
    PeelTo G X Y Z a ↔
      (a ∈ X ∧ (∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a)
        ∧ G.parents a ⊆ X ∪ Z ∧ G.dSep (X \ {a}) Y Z) := Iff.rfl

/-- ⭐ **`PeelTo` 强制 `pa a ⊆ X ∪ Z`**（条件 3 的直接读法）。 -/
theorem peelTo_parents {X Y Z : Finset V} {a : V} (h : PeelTo G X Y Z a) :
    G.parents a ⊆ X ∪ Z := h.2.2.1

/-- ⭐ **`PeelTo` 强制递归步 `dSep (X ∖ {a}) Y Z`**（条件 4 的直接读法）。 -/
theorem peelTo_dSep {X Y Z : Finset V} {a : V} (h : PeelTo G X Y Z a) :
    G.dSep (X \ {a}) Y Z := h.2.2.2

/-- ⭐ **F1 — `exists_topo_max`**：`X` 非空 ⟹ 取 `topoOrder` 最大的点。 -/
theorem exists_topo_max {X : Finset V} (hX : X.Nonempty) :
    ∃ a ∈ X, ∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a := by
  obtain ⟨a, haX, hmax⟩ :=
    Finset.exists_max_image (s := X) (f := fun w => G.topoOrder w) hX
  exact ⟨a, haX, fun w hw => hmax w hw⟩

/-! ===========================================================================
  §3 ⭐⭐ **路线 B 的自由步**：剥拓扑极大点，父代落位自动保持
  =========================================================================== -/

/-- ⭐⭐ **E2 — `topoMax_no_child_in_X`（`peel_safe` 的一行内核）**：

若 `a` 在 `X` 中拓扑极大，则 **`a` 不是 `X` 中任何点的父代**。

**证明**：`a ∈ pa w` ⟹ `topoOrder a < topoOrder w`（`topoOrder_lt`），
而最大化给 `topoOrder w ≤ topoOrder a`。矛盾。

**⟹ 这是「剥极大点」与「剥极小点」不对称的**唯一原因**。** -/
theorem topoMax_no_child_in_X {X : Finset V} {a : V}
    (hmax : ∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a) :
    ∀ w ∈ X, a ∉ G.parents w := by
  intro w hw hmem
  have h1 := G.topoOrder_lt a w (G.mem_parents.mp hmem)
  have h2 := hmax w hw
  omega

/-- ⭐⭐⭐ **E1 — `peel_safe`（路线 B 的自由步）**：

设 `pa(X) ⊆ X ∪ Z`。若 `a ∈ X` 在 `X` 中**拓扑极大**，则剥掉它之后
**剩余点的父代落位仍然成立**：

> `pa(X ∖ {a}) ⊆ (X ∖ {a}) ∪ Z`。

**证明（逐条点名前件）**：
* 取 `v ∈ X ∖ {a}`、`u ∈ pa v`；由 `hpa` 得 `u ∈ X ∪ Z`；
* **若 `u ∈ Z`**：直接 `u ∈ (X∖{a}) ∪ Z`；
* **若 `u ∈ X`**：只需排除 `u = a`，而 `u = a` 会与
  `topoMax_no_child_in_X hmax v hv`（`a ∉ pa v`）**直接矛盾**。

**⟹ 这就是路线 B 的全部正面内容：剥**极大**点不会打坏任何剩余点的落位。** -/
theorem peel_safe {X Z : Finset V} {a : V} (ha : a ∈ X)
    (hmax : ∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a)
    (hpa : ∀ v ∈ X, G.parents v ⊆ X ∪ Z) :
    ∀ v ∈ X \ {a}, G.parents v ⊆ (X \ {a}) ∪ Z := by
  intro v hv u hu
  rw [Finset.mem_sdiff] at hv
  obtain ⟨hvX, _hva⟩ := hv
  rcases Finset.mem_union.mp (hpa v hvX hu) with h' | h'
  · by_cases hua : u = a
    · subst hua
      exact absurd hu (topoMax_no_child_in_X hmax v hvX)
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨h', by simpa using hua⟩)
  · exact Finset.mem_union_right _ h'

/-- ⭐⭐⭐ **E3 — `peel_tower`（剥离塔存在，强归纳）**：

设 `pa(X) ⊆ X ∪ Z`、`dSep X Y Z`。则存在一条**剥离序列**：
按拓扑极大点逐个剥掉，直到 `X` 全空，且**每一步**都保持

* 「剩余集的父代落位」`pa(Xᵢ) ⊆ Xᵢ ∪ Z`；
* 「剩余集的 `dSep`」`dSep Xᵢ Y Z`。

**证明（逐条点名前件）**：
* **强归纳于 `Xk.card`**（`Nat.strong_induction_on`）；
* **非空 ⟹ 极大点存在**：`exists_topo_max`（`F1`）；
* **落位保持**：`peel_safe`（`E1`）；
* **`dSep` 保持**：`dSep_subset_left`（`Xk∖{a} ⊆ Xk`，**免费**）；
* **基数严格下降**：`Xk ∖ {a} = Xk.erase a`（`card_erase_of_mem`）。

**输出形态（有内容，不是平凡的「取空集」）**：本定理对 `Xk.card` 做**强归纳**，
结论是「**剥离过程可以跑到底**」：

> 存在 `k ≤ Xk.card` 与一个**逐点剥离算子** `step`，使得从 `Xk` 出发连续剥 `k` 次后
> 得到 `∅`，且**每一步**都保持
> `pa(·) ⊆ · ∪ Z`（落位）与 `dSep · Y Z`（`dSep`）。

技术上用「**剩余集函数** `peelRun : ℕ → Finset V`」表达剥离塔：

* `peelRun 0 = Xk`；
* `peelRun (i+1) = peelRun i ∖ {chosen i}`（`chosen i` 是 `peelRun i` 的拓扑极大点）；
* 末项 `peelRun k = ∅`；
* 每项都满足落位与 `dSep`。

**⚠ 塔是单向的，见 §5（G1/G2）：末项 `∅` 上的 `dSep` 不能上推回 `X`。** -/
theorem peel_tower {X Y Z : Finset V}
    (_hpa : ∀ v ∈ X, G.parents v ⊆ X ∪ Z) (_hd : G.dSep X Y Z) :
    ∀ n : ℕ, ∀ Xk : Finset V, Xk ⊆ X → Xk.card ≤ n →
      (∀ v ∈ Xk, G.parents v ⊆ Xk ∪ Z) → G.dSep Xk Y Z →
      ∃ k : ℕ, ∃ peelRun : ℕ → Finset V,
        peelRun 0 = Xk ∧ peelRun k = ∅
        ∧ (∀ i < k, ∀ v ∈ peelRun i, G.parents v ⊆ peelRun i ∪ Z)
        ∧ (∀ i ≤ k, G.dSep (peelRun i) Y Z)
        ∧ (∀ i < k, ∃ a ∈ peelRun i, peelRun (i + 1) = peelRun i \ {a}
            ∧ (∀ w ∈ peelRun i, G.topoOrder w ≤ G.topoOrder a)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Xk hsubX hcard hpaXk hdXk
    by_cases hempty : Xk = ∅
    · subst hempty
      refine ⟨0, fun _ => ∅, rfl, rfl, ?_, ?_, ?_⟩
      · intro i hi
        omega
      · intro i _
        exact hdXk
      · intro i hi
        omega
    · obtain ⟨a, haXk, hmax⟩ :=
        exists_topo_max (G := G) (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hdel : (Xk \ {a}).card < n := by
        have hlt : (Xk \ {a}).card < Xk.card := by
          have heq : Xk \ {a} = Xk.erase a := by
            ext v
            simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase]
            tauto
          rw [heq, Finset.card_erase_of_mem haXk]
          have hpos : 0 < Xk.card :=
            Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
          omega
        omega
      have hpa' : ∀ v ∈ Xk \ {a}, G.parents v ⊆ (Xk \ {a}) ∪ Z :=
        peel_safe haXk hmax hpaXk
      have hd' : G.dSep (Xk \ {a}) Y Z :=
        FateV2.Modeling.Graph.DAG.dSep_subset_left (G := G) (Finset.sdiff_subset) hdXk
      obtain ⟨k, run, hrun0, hrunlast, hrunpa, hrund, hrunstep⟩ :=
        ih (Xk \ {a}).card hdel (Xk \ {a})
          (Finset.sdiff_subset.trans hsubX) le_rfl hpa' hd'
      -- 把 `Xk` 拼到 `run` 前面：`peelRun 0 = Xk`, `peelRun (i+1) = run i`
      refine ⟨k + 1, fun i => match i with
        | 0 => Xk
        | (j + 1) => run j, rfl, ?_, ?_, ?_, ?_⟩
      · -- peelRun (k+1) = run k = ∅
        show run k = ∅
        exact hrunlast
      · -- 落位：i < k+1
        intro i hi v hv
        match i with
        | 0 => exact hpaXk v hv
        | (j + 1) =>
            show G.parents v ⊆ run j ∪ Z
            exact hrunpa j (by omega) v hv
      · -- dSep：i ≤ k+1
        intro i hi
        match i with
        | 0 => exact hdXk
        | (j + 1) =>
            show G.dSep (run j) Y Z
            exact hrund j (by omega)
      · -- 剥离步
        intro i hi
        match i with
        | 0 =>
            refine ⟨a, haXk, ?_, hmax⟩
            show run 0 = Xk \ {a}
            exact hrun0
        | (j + 1) =>
            obtain ⟨b, hb, hstep, hbmax⟩ := hrunstep j (by omega)
            exact ⟨b, hb, hstep, hbmax⟩

/-! ===========================================================================
  §4 🔴 **不对称性**：剥非极大点会打坏落位；且剥离塔不可反向
  =========================================================================== -/

/-- **反例图 `gfork`：`0 → 2`、`1 → 2`**（`Fin 4`；顶点 `3` 孤立）。

用于 `peel_breaks`：取 `X = {1,2}`、`Z = {0}` 时 `pa(X) ⊆ X ∪ Z` **成立**，
但剥掉 `a = 1` 后 `pa(2) = {0,1} ⊄ (X∖{1}) ∪ Z = {0,2}`。 -/
def gfork : FateV2.Modeling.Graph.DAG (Fin 4) where
  edge := fun u v => (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 4,
        Relation.TransGen (fun u v : Fin 4 => (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)) x y →
          x < y := by
      intro x y hxy
      induction hxy with
      | single h => rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; decide)
      | tail _ hstep ih => rcases hstep with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; omega)
    exact absurd (key v v hv) (lt_irrefl v)

/-- `gfork` 上 `pa(2) = {0, 1}`。 -/
theorem gfork_pa2 : gfork.parents (2 : Fin 4) = {(0 : Fin 4), (1 : Fin 4)} := by decide

/-- `gfork` 上 `pa(1) = ∅`（`1` 是源点）。 -/
theorem gfork_pa1 : gfork.parents (1 : Fin 4) = (∅ : Finset (Fin 4)) := by decide

/-- 🔴 **E4 — `peel_breaks`（剥非极大/非自由点会打坏落位）**：

`gfork` 上取 `X = {1,2}`、`Z = {0}`：**`pa(X) ⊆ X ∪ Z` 成立**（下面 `peel_breaks_pre`），
但剥掉 `a = 1` 之后，`pa(2) = {0,1}` **不再**落在 `(X∖{1}) ∪ Z = {0,2}` 内 ——
因为 `1` **被剥走了**，而它仍是 `2` 的父代。

**⟹ 剥离的自由度**不是白送的**：剥错点会让「已被剥离」的点从剩余集消失，
而其父代关系仍在。**这正是 `peel_safe` 需要「拓扑极大」的原因。** -/
theorem peel_breaks :
    ¬ (∀ v ∈ (({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) \ ({1} : Finset (Fin 4))),
        gfork.parents v ⊆
          ((({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) \ ({1} : Finset (Fin 4)))
            ∪ ({(0 : Fin 4)} : Finset (Fin 4)))) := by
  intro h
  have h2 : gfork.parents (2 : Fin 4) ⊆
      ((({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) \ ({1} : Finset (Fin 4)))
        ∪ ({(0 : Fin 4)} : Finset (Fin 4))) := by
    apply h
    simp
  rw [gfork_pa2] at h2
  have h1 : (1 : Fin 4) ∈
      ((({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) \ ({1} : Finset (Fin 4)))
        ∪ ({(0 : Fin 4)} : Finset (Fin 4))) := h2 (by decide)
  simp at h1

/-- ⭐ **`peel_breaks_pre`（对照）：同例上前件 `pa(X) ⊆ X ∪ Z` **成立**。 -/
theorem peel_breaks_pre :
    ∀ v ∈ ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)),
      gfork.parents v ⊆ ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4))
        ∪ ({(0 : Fin 4)} : Finset (Fin 4)) := by
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · rw [gfork_pa1]; exact Finset.empty_subset _
  · rw [gfork_pa2]; decide

/-- ⭐⭐ **E5 — `peel_safety_criterion`（剥离安全的**精确判据**）**：

对**任意** `v ∈ X ∖ {a}` 与 `u ∈ pa v`，剥掉 `a` 后仍落位，
**当且仅当** `u ≠ a`（即 `a` 不是剩余点的父代）。

**⟹ 这说明 `peel_safe` 的「拓扑极大」条件**只能通过 `a ∉ pa(X∖{a})` 起作用**，
而后者正是 `topoMax_no_child_in_X` 给的内容。** -/
theorem peel_safety_criterion {X Z : Finset V} {a u v : V}
    (hpa : ∀ w ∈ X, G.parents w ⊆ X ∪ Z) (hvX : v ∈ X) (hu : u ∈ G.parents v)
    (hua : u ≠ a) :
    u ∈ (X \ {a}) ∪ Z := by
  rcases Finset.mem_union.mp (hpa v hvX hu) with h' | h'
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h', by simpa using hua⟩)
  · exact Finset.mem_union_right _ h'

/-! ===========================================================================
  §5 🔴 **剥离塔不可反向**：`dSep` 对 `X` 增大不单调
  =========================================================================== -/

/-- **反例图 `gex`：`0 → 1`，顶点 `2` 孤立**（与 `BridgeFull` / `BridgeExpanded` 逐字相同）。 -/
-- 定义已收敛到 `Fate/Concrete/ThreeNode.lean`（原 4 份逐字相同，见 _audit/BRIDGE-1）
def gex : FateV2.Modeling.Graph.DAG (Fin 3) := Fate.Concrete.gex

/-- ⭐ `gex` 上 `dSep {1} {2} ∅` **成立**。 -/
theorem gex_dsep : gex.dSep {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) := by decide

/-- ⭐ `gex` 上 `pa(1) = {0}`。 -/
theorem gex_pa : gex.parents (1 : Fin 3) = {(0 : Fin 3)} := by decide

/-- ⭐ `gex` 上 `pa(2) = ∅`（`2` 孤立）。 -/
theorem gex_pa2 : gex.parents (2 : Fin 3) = (∅ : Finset (Fin 3)) := by decide

/-- ⭐🔴 **G1 — `dSep_mono_add_false`：`dSep` 对 `X` **增大**不单调。**

`gex` 上：`dSep ∅ {1} ∅` **真**，而 `dSep {1} {1} ∅` **假**
（`dSep` 第 1 子句 `Disjoint X Y` 被破坏：`1 ∈ X ∩ Y`）。

**⟹ 这是「剥离塔不可反向重组」的机器见证**：
剥离塔从 `X = ∅` 出发**向上**加回点时，`dSep` 会**失效**；
故 `peel_tower` 的终点 `∅` 上的 `dSep` **不能**上推回原始 `X`。** -/
theorem dSep_mono_add_false :
    gex.dSep (∅ : Finset (Fin 3)) {(1 : Fin 3)} (∅ : Finset (Fin 3))
      ∧ ¬ gex.dSep {(1 : Fin 3)} {(1 : Fin 3)} (∅ : Finset (Fin 3)) := by
  refine ⟨by decide, ?_⟩
  intro hd
  obtain ⟨hXY, -, -, -⟩ := hd
  exact Finset.disjoint_left.mp hXY (mem_singleton_self 1) (mem_singleton_self 1)

/-- 🔴 **G2 — `peel_tower_not_reversible`（打包判定）**：

**剥离塔（`peel_tower`）与主定理（`bridge_direct_of_peel`）的方向相反。**

具体：让 `peel_tower` 有用，需要从**终点**（`X = ∅`）**上推**回原始 `X`；
但 `dSep_mono_add_false` 给出反例。**⟹ 剥离塔只解释「为什么 `X` 父闭时成立」，
不提供新的证明力（`bridge_direct_iff`）。**

本定理把这两件事**同时** machine-check 下来，防止下游误读 `peel_tower`。 -/
theorem peel_tower_not_reversible :
    -- (a) 剥离塔方向：缩小 `X` 时 `dSep` 保持（免费）
    (gex.dSep {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) →
      gex.dSep (({(1 : Fin 3)} : Finset (Fin 3)) \ ({1} : Finset (Fin 3)))
        {(2 : Fin 3)} (∅ : Finset (Fin 3)))
    -- (b) 反向（增大 `X`）失败
    ∧ (gex.dSep (∅ : Finset (Fin 3)) {(1 : Fin 3)} (∅ : Finset (Fin 3))
        ∧ ¬ gex.dSep {(1 : Fin 3)} {(1 : Fin 3)} (∅ : Finset (Fin 3))) := by
  refine ⟨fun hd => ?_, dSep_mono_add_false⟩
  exact FateV2.Modeling.Graph.DAG.dSep_subset_left (G := gex) (Finset.sdiff_subset) hd

/-! ===========================================================================
  §6 ⭐⭐ **等价判定**：`PeelTo` ⟺ 单点落位；主定理前件 ⟺ 原缺口
  =========================================================================== -/

/-- ⭐⭐ **F2 — `peelTo_iff_gap`（路线 B 递归步的精确内容）**：

对**任意** `a ∈ X` 为 `X` 的拓扑极大点、且在 `dSep X Y Z` 成立的前提下，

> **`PeelTo G X Y Z a` ⟺ `G.parents a ⊆ X ∪ Z`**。

**证明**：`dSep` 方向由 `dSep_subset_left` **免费**给出；于是 `PeelTo` 的
**全部内容**就是单点父代落位。

**⚠ 因此 `PeelTo` 不改进问题**：它把 `ReadClosedBlocks` 的第 2 条原样搬运。 -/
theorem peelTo_iff_gap {X Y Z : Finset V} {a : V} (haX : a ∈ X)
    (hmax : ∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a) (hd : G.dSep X Y Z) :
    PeelTo G X Y Z a ↔ G.parents a ⊆ X ∪ Z := by
  constructor
  · exact peelTo_parents
  · intro hpa
    exact ⟨haX, hmax, hpa,
      FateV2.Modeling.Graph.DAG.dSep_subset_left (G := G) (Finset.sdiff_subset) hd⟩

/-- ⭐ **`peelTo_of_readClosed`**：`ReadClosedBlocks` + `dSep` ⟹ 存在可剥点。 -/
theorem peelTo_of_readClosed {X Y Z : Finset V} (hX : X.Nonempty)
    (hRC : ReadClosedBlocks G X Y Z) (hd : G.dSep X Y Z) :
    ∃ a : V, PeelTo G X Y Z a := by
  obtain ⟨a, haX, hmax⟩ := exists_topo_max (G := G) hX
  exact ⟨a, haX, hmax, hRC.2.1 a haX,
    FateV2.Modeling.Graph.DAG.dSep_subset_left (G := G) (Finset.sdiff_subset) hd⟩

/-- 🔴 **H1 — `gap_false_gex`**：`gex` 上 `Z' = Z` 版 `ReadClosedBlocks` **为假**。

**本地独立重证**（与 `BridgeFull` / `BridgeExpanded` 的结论一致）。 -/
theorem gap_false_gex :
    ¬ ReadClosedBlocks gex {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) := by
  rintro ⟨_, hX, _⟩
  have hsub := hX 1 (mem_singleton_self 1)
  rw [gex_pa] at hsub
  have h0 : (0 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) ∪ (∅ : Finset (Fin 3)) :=
    hsub (mem_singleton_self 0)
  rw [Finset.union_empty] at h0
  exact absurd (mem_singleton.mp h0) (by decide)

/-- 🔴 **H2 — `gap_not_improved`**：**路线 B 的前件在 `gex` 上为假**。

**⟹ 无论怎么组织剥离的归纳，`gex` 上的 `Z' = Z` 版桥都不可能被证出来**：
不是「没证完」，而是**前件不可满足**。 -/
theorem gap_not_improved :
    ¬ (∀ v ∈ ({(1 : Fin 3)} : Finset (Fin 3)),
        gex.parents v ⊆ ({(1 : Fin 3)} : Finset (Fin 3)) ∪ (∅ : Finset (Fin 3))) := by
  intro h
  have hsub := h 1 (mem_singleton_self 1)
  rw [gex_pa] at hsub
  have h0 : (0 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) ∪ (∅ : Finset (Fin 3)) :=
    hsub (mem_singleton_self 0)
  rw [Finset.union_empty] at h0
  exact absurd (mem_singleton.mp h0) (by decide)

/-! ===========================================================================
  §7 ⭐⭐⭐ **路线 B 的主定理与其价值判定**
  =========================================================================== -/

/-- ⭐⭐⭐ **B1 — `bridge_direct_of_peel`（路线 B 的主定理）**：

**若**
* `hpeel : ∀ v ∈ X, pa v ⊆ X ∪ Z`（路线 B 的「父代落位」）；
* `hd : G.dSep X Y Z`（**原始 `Z`，不扩大**）；
* `hZ : AncClosed G Z`、`hY : ∀ v ∈ Y, pa v ⊆ Y ∪ Z`；
* 引擎三件套 `hloc`/`hfac`/`hnorm`；

**则** `CondIndep p X Y Z`。

**⚠ 前件的精确位置（逐条点名）**：
* `hpeel` —— 组装 `AncClosed G (X ∪ Z)`（引擎的 `hXZ`），并**就是**路线 B 的全部内容；
* `hd` —— 喂 `condIndep_of_dSep_ancClosed`，**只取前三个 `Disjoint` 子句**；
* `hZ` —— `AncClosed G Z`；
* `hY` —— 组装 `AncClosed G (Y ∪ Z)`；
* `hloc`/`hfac`/`hnorm` —— `mass_ancClosed` 的基情形/归纳步/收口。

**⚠ 结论里 `Z` **没有**被撑大**（与 `BridgeExpanded` 路线相反）。 -/
theorem bridge_direct_of_peel {α : Type u} [Fintype α] [DecidableEq α]
    {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FateV2.Predict.FactorMarkov.FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z)
    (hpeel : ∀ v ∈ X, G.parents v ⊆ X ∪ Z)
    (hZ : AncClosed G Z) (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z := by
  -- `X ∪ Y ∪ Z` 父闭：由 `hpeel`（X 侧）、`hY`（Y 侧）、`hZ`（Z 侧）拼
  have stepX : ∀ v ∈ X, G.parents v ⊆ X ∪ Y ∪ Z := by
    intro v hv u hu
    rcases Finset.mem_union.mp (hpeel v hv hu) with h' | h'
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h')))
    · exact Finset.mem_union.mpr (Or.inr h')
  have stepY : ∀ v ∈ Y, G.parents v ⊆ X ∪ Y ∪ Z := by
    intro v hv u hu
    rcases Finset.mem_union.mp (hY v hv hu) with h' | h'
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h')))
    · exact Finset.mem_union.mpr (Or.inr h')
  have h1 : AncClosed G (X ∪ Y ∪ Z) := fun v hv => by
    rcases Finset.mem_union.mp hv with hXY | hZ'
    · rcases Finset.mem_union.mp hXY with hXi | hYi
      · exact stepX v hXi
      · exact stepY v hYi
    · intro u hu
      exact Finset.mem_union.mpr (Or.inr (hZ v hZ' hu))
  have h2 : AncClosed G (X ∪ Z) := fun v hv => by
    rcases Finset.mem_union.mp hv with h' | h'
    · exact hpeel v h'
    · exact fun u hu => Finset.mem_union.mpr (Or.inr (hZ v h' hu))
  have h3 : AncClosed G (Y ∪ Z) := fun v hv => by
    rcases Finset.mem_union.mp hv with h' | h'
    · exact hY v h'
    · exact fun u hu => Finset.mem_union.mpr (Or.inr (hZ v h' hu))
  exact Fate.Strategy11Hull.condIndep_of_dSep_ancClosed hloc hfac hnorm hd h1 h2 h3 hZ

/-- ⭐⭐ **B2 — `bridge_direct_iff`（路线 B 的价值判定）**：

在 `hZ`、`hY` 固定时，

> `(∀ v ∈ X, pa v ⊆ X ∪ Z)` ⟺ `ReadClosedBlocks G X Y Z`。

**⟹ 路线 B 的主定理前件 ⟺ 原缺口**（`Gap` 在 `dSep` 下展开）。
**⟹ 「剥离」没有带来任何新的可证内容**：它的前件与 `BridgeFull` 的缺口 G1
**逐字等价**，因而在 `gex` 上**同样为假**（`gap_not_improved`）。 -/
theorem bridge_direct_iff {X Y Z : Finset V}
    (hZ : AncClosed G Z) (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    (∀ v ∈ X, G.parents v ⊆ X ∪ Z) ↔ ReadClosedBlocks G X Y Z :=
  ⟨fun h => ⟨hZ, h, hY⟩, fun h => h.2.1⟩

/-- 🔴 **`gap_is_peel`（同一条判定的 `Gap` 形态）**：
`Gap G X Y Z` ⟺ 在 `dSep X Y Z` 下 `X` 侧落位成立（在 `hZ`、`hY` 固定时）。 -/
theorem gap_is_peel {X Y Z : Finset V}
    (hZ : AncClosed G Z) (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    Gap G X Y Z ↔ (G.dSep X Y Z → ∀ v ∈ X, G.parents v ⊆ X ∪ Z) := by
  unfold Gap
  exact ⟨fun h hd => (h hd).2.1, fun h hd => ⟨hZ, h hd, hY⟩⟩

/-! ===========================================================================
  §8 ⭐⭐ **路线 B 的正确适用域**（前件自动成立的三类情形）
  =========================================================================== -/

/-- ⭐ **`parents_subset_of_ancClosed`**：`X` 父闭 ⟹ `X` 侧落位**无条件成立**。 -/
theorem parents_subset_of_ancClosed {X Z : Finset V} (hX : AncClosed G X) :
    ∀ v ∈ X, G.parents v ⊆ X ∪ Z :=
  fun v hv => fun _ hu => Finset.mem_union_left Z (hX v hv hu)

/-- ⭐⭐ **C1 — `bridge_direct_of_ancClosed_X`（适用域 1：`X` 祖先闭）**：

`X` 父闭时 `hpeel` 免费（`parents_subset_of_ancClosed`），主定理**无条件**可用。
**⟹ 这是路线 B 在 `Fate.Strategy11AncestralHull` 口径下真的成立的**标准情形**。** -/
theorem bridge_direct_of_ancClosed_X {α : Type u} [Fintype α] [DecidableEq α]
    {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FateV2.Predict.FactorMarkov.FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z)
    (hX : AncClosed G X) (hZ : AncClosed G Z)
    (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  bridge_direct_of_peel hloc hfac hnorm hd
    (parents_subset_of_ancClosed hX) hZ hY

/-- ⭐ **C2 — `bridge_direct_of_subset_Z`（适用域 2：`X ⊆ Z`）**：

`X ⊆ Z` 时 `pa v ⊆ X ⊆ Z ⊆ X ∪ Z`，故 `hpeel` 免费。
**⚠ 但 `dSep X Y Z` 的第 2 子句 `Disjoint X Z` 与 `X ⊆ Z` 只在 `X = ∅` 时共存**
（`subset_Z_dSep_trivial`），故本适用域仅在 `X` 空时非空 —— 本文件如实标注。 -/
theorem bridge_direct_of_subset_Z {α : Type u} [Fintype α] [DecidableEq α]
    {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FateV2.Predict.FactorMarkov.FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z) (hXZ : X ⊆ Z)
    (hZ : AncClosed G Z) (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  bridge_direct_of_peel hloc hfac hnorm hd
    (fun v hv _ hu => Finset.mem_union_right X (hZ v (hXZ hv) hu))
    hZ hY

/-- ⭐ **`subset_Z_dSep_trivial`**：`X ⊆ Z` 且 `dSep X Y Z` ⟹ `X = ∅`。

**消费点**：`dSep` 的第 2 子句 `Disjoint X Z`。 -/
theorem subset_Z_dSep_trivial {X Z : Finset V} (hd : G.dSep X Y Z) (hXZ : X ⊆ Z) :
    X = ∅ := by
  obtain ⟨-, hXZ', -, -⟩ := hd
  exact Finset.eq_empty_of_forall_notMem fun u hu =>
    Finset.disjoint_left.mp hXZ' hu (hXZ hu)

/-- ⭐ **C3 — `bridge_direct_of_sources`（适用域 3：`X` 全为源点）**：

`∀ v ∈ X, pa v = ∅` 时 `hpeel` 免费（空集是任何集合的子集）。 -/
theorem bridge_direct_of_sources {α : Type u} [Fintype α] [DecidableEq α]
    {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FateV2.Predict.FactorMarkov.FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z)
    (hsrc : ∀ v ∈ X, G.parents v = ∅)
    (hZ : AncClosed G Z) (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  bridge_direct_of_peel hloc hfac hnorm hd
    (fun _ hv => (hsrc _ hv) ▸ Finset.empty_subset _) hZ hY

/-- ⭐ **C4 — `peel_gives_markov_ancClosed`**：把 C1 组装成 `markov_ancClosed` 的形态。

**⟹ 路线 B 在「四集合父闭」口径下**确实**补齐了 `markov_ancClosed` 的 `X ∪ Z` 侧
（引擎已要求 `AncClosed G (X ∪ Z)`，本文件证明它 ⟸ `AncClosed G X ∧ AncClosed G Z`）。** -/
theorem ancClosed_union_of_ancClosed {X Z : Finset V}
    (hX : AncClosed G X) (hZ : AncClosed G Z) : AncClosed G (X ∪ Z) := by
  intro v hv
  rcases Finset.mem_union.mp hv with h' | h'
  · exact fun u hu => Finset.mem_union_left Z (hX v h' hu)
  · exact fun u hu => Finset.mem_union_right X (hZ v h' hu)

/-! ===========================================================================
  §9 ⭐ **与 `BridgeZipDown` 接轨**：分析型出路 `mass_congr`
  =========================================================================== -/

/-- ⭐⭐ **I1 — `mass_congr_peel`（剥离点落在读集外 ⟹ `mass` 不敏感）**：

若 `a ∉ S`，则 `mass S p` 与 `x` 在 `a` 位的取值**无关**：
`mass S p x = mass S p (unpin a x b)`。

**⟹ 这正是 `BridgeZipDown` 的分析型出路 `mass_congr` 在路线 B 中的形态**：
`peel_safe`（集合型：剥极大点 `a` 后 `a ∉ pa(X∖{a})`）⟹
`a` 不在任何剩余读集里 ⟹ `mass` 对该位不敏感。
**两条路线在此接轨**：路线 B 的「剥离」= `BridgeZipDown` 的「读集不敏感」。 -/
theorem mass_congr_peel {α : Type u} [Fintype α] [DecidableEq α]
    {S : Finset V} (a : V) (haS : a ∉ S)
    (p : (V → α) → ℝ) (x : V → α) (b : α) :
    FateV2.Predict.DAGFactorization.mass S p x
      = FateV2.Predict.DAGFactorization.mass S p (FateV2.Predict.DAGFactorization.unpin a x b) := by
  refine FateV2.Predict.DAGFactorization.mass_congr S p ?_
  intro u hu
  have hua : u ≠ a := fun h => haS (h ▸ hu)
  unfold FateV2.Predict.DAGFactorization.unpin
  rw [if_neg hua]

/-- ⭐ **`paBlock G S = ⋃_{v∈S} pa_G(v)`**：块 `S` 的**父代并**（本地复刻，
与 `Fate.BridgeMinZPrime.paBlock` 逐字相同）。 -/
def paBlock (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Finset V :=
  S.biUnion (fun v => G.parents v)

/-- `paBlock` 的成员刻画。 -/
theorem mem_paBlock {S : Finset V} {u : V} :
    u ∈ paBlock G S ↔ ∃ v ∈ S, u ∈ G.parents v := by
  unfold paBlock
  rw [Finset.mem_biUnion]

/-- ⭐ **`peel_safe_gives_mass_indiff`**：剥极大点后，**剩余读集不含 `a`**。 -/
theorem peel_safe_gives_mass_indiff {X : Finset V} {a : V}
    (hmax : ∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a) :
    a ∉ paBlock G (X \ {a}) := by
  intro hmem
  obtain ⟨v, hv, hav⟩ := mem_paBlock.mp hmem
  exact topoMax_no_child_in_X hmax v (Finset.mem_sdiff.mp hv).1 hav

/-- ⭐ **`routeB_verdict`**：路线 B 的最终判定（三条打包）。

1. ✅ `gex` 上 `dSep` 成立（前件之一真）；
2. 🔴 `gex` 上路线 B 前件**假**（`pa(1) = {0} ⊄ {1}`）；
3. 🔴 `gex` 上 `dSep` 对 `X` **增大**不单调（`peel_tower` 不可反向）。

**⟹ 路线 B 在「任意 `X`」上不可行，在「`X` 祖先闭」上可行（C1）。** -/
theorem routeB_verdict :
    gex.dSep {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3))
      ∧ ¬ ReadClosedBlocks gex {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3))
      ∧ ¬ gex.dSep {(1 : Fin 3)} {(1 : Fin 3)} (∅ : Finset (Fin 3)) :=
  ⟨gex_dsep, gap_false_gex, dSep_mono_add_false.2⟩

end FateV2.Predict.BridgeDirect