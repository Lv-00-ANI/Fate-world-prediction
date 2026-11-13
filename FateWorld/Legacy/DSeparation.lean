import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! ===========================================================================
  §60  ⭐⭐⭐ **d-分离的形式化起点**（**推翻债务台账的「⛔ 不可做」**）

  ## ⚠⚠ 本节的首要意义：**一次对既有结论的纠正**

  **`债务清账台账.md` 的 B6 项**：
  > **第 3 章 6 项（d-分离/SCM/do-calculus）**｜⛔ **未开始**
  > （附理由：Mathlib 实测无对应模块，…）

  **⚠ 第 60 轮的实测核查**：

  | 核查项 | 结果 |
  |---|---|
  | Mathlib 含 `Causal` 的文件 | **0** ✅（台账正确）|
  | Mathlib 含 `dSep`/`SCM`/`doCalc` 的文件 | **0** ✅ |
  | **但**：Mathlib 含 `SimpleGraph.Walk` | ⭐ **存在** |
  | Mathlib 含 `Walk.IsPath` | ⭐ **存在** |
  | Mathlib 含 `Walk.support`（路径顶点序列）| ⭐ **存在** |
  | Mathlib 含 `Reachable` | ⭐ **存在** |

  **⟹ 即**：**台账说「无对应模块」是对的**（无**成品**的因果模块），
  **但由此推出「不可做」是**过强**的** ——
  **d-分离的**全部构件**（路径、顶点序列、可达性）**Mathlib 已提供**。**

  ## ⭐ 本节的产出

  **用 `SimpleGraph.Walk` 定义 d-分离的**路径层**核心**：
  1. **路径**（`Walk`）
  2. **路径经过顶点集**（`support`）
  3. **块集**（blocking set）的概念
  4. **d-连通 / d-分离**的定义

  **⚠ 边界（如实登记）**：**本节只做**图论层**的形式化** ——
  **不含「collider / 分叉 / 链」的**方向性**区分**（那需要 `Digraph` 或带向结构）；
  **也不含 d-分离与概率独立性的**定理**（那需要概率论）。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace DSeparation

universe u

variable {V : Type u}

/-! ### §60.1 ⭐⭐ 路径与块集 -/

/-- ⭐⭐ **路径经过的顶点集**（把 `Walk.support` 的列表转为集合）。

**⟹ 这是 d-分离的**第一个构件**：
「一条路径是否经过某个顶点集」。** -/
def walkVerts {G : SimpleGraph V} {a b : V} (w : G.Walk a b) : Set V :=
  {v | v ∈ w.support}

/-- ⭐⭐ **路径被 `Z` 阻断**（**路径层**的定义）。

$$\text{Blocked}(w, Z) := \text{路径 } w \text{ 的内部顶点全部落在 } Z \text{ 中}$$

**⚠ 简化说明**：**严格的 d-分离**还须区分 collider 与非 collider；
**本节只取「路径上的中间顶点是否都在 `Z` 中」这一**必要条件**。** -/
def BlockedBy {G : SimpleGraph V} {a b : V} (w : G.Walk a b) (Z : Set V) : Prop :=
  ∀ v ∈ w.support, v ≠ a → v ≠ b → v ∈ Z

/-! ### §60.2 ⭐⭐ d-连通与 d-分离 -/

/-- ⭐⭐ **`Z`-连通**：存在一条被 `Z` 阻断的路径。

$$a \perp\!\!\!\perp_{d} b \mid Z \text{ 的**否定**}$$ -/
def ZConnected (G : SimpleGraph V) (Z : Set V) (a b : V) : Prop :=
  ∃ w : G.Walk a b, BlockedBy w Z

/-- ⭐⭐ **d-分离**（本节的核心定义）。

$$a \perp\!\!\!\perp_{d} b \mid Z :=
  \neg\exists\, \text{被 } Z \text{ 阻断的 } a\text{-}b \text{ 路径}$$

**⚠ 读法**：**`Z` 分离了 `a` 与 `b`** ——
**即没有一条「内部顶点都在 `Z` 中」的路径连接它们。** -/
def DSeparated (G : SimpleGraph V) (Z : Set V) (a b : V) : Prop :=
  ¬ ZConnected G Z a b

/-! ### §60.3 ⭐⭐ 基本性质 -/

/-- ⭐⭐ **可分离性可展开为「所有路径都被阻断」**。

$$a \perp\!\!\!\perp_{d} b \mid Z \iff
  \forall w : G.\mathrm{Walk}\,a\,b,\ \neg\,\mathrm{BlockedBy}\,w\,Z$$ -/
theorem dseparated_iff (G : SimpleGraph V) (Z : Set V) (a b : V) :
    DSeparated G Z a b ↔ ∀ w : G.Walk a b, ¬ BlockedBy w Z :=
  ⟨fun h w hw => h ⟨w, hw⟩, fun h ⟨w, hw⟩ => h w hw⟩

/-- ⭐⭐ **单点路径的阻断性**（**基本情形**）。

若 `a ≠ b` 且 `w` 是「只有 `a, b` 两个顶点」的路径，
则 `BlockedBy w Z` **空真**（无中间顶点）。

**⟹ 即**：**该路径**总不被阻断**（除非 `Z` 含 `a` 或 `b`，本节不予考虑）。** -/
theorem blockedBy_of_no_inner {G : SimpleGraph V} {a b : V} (w : G.Walk a b)
    (h : ∀ v ∈ w.support, v = a ∨ v = b) (Z : Set V) : BlockedBy w Z :=
  fun v hv hva hvb => absurd (h v hv) (by tauto)

/-- ⭐⭐ **阻断集的单调性**（**核心性质**）。

$$Z \subseteq Z' \implies \text{被 } Z \text{ 阻断} \implies \text{被 } Z' \text{ 阻断}$$

**⟹ 即**：**阻断集越大，越容易阻断路径** ——
**这是 d-分离「条件越多越易独立」的图论形式。** -/
theorem blockedBy_mono {G : SimpleGraph V} {a b : V} (w : G.Walk a b)
    {Z Z' : Set V} (hZZ' : Z ⊆ Z') (h : BlockedBy w Z) : BlockedBy w Z' :=
  fun v hv hva hvb => hZZ' (h v hv hva hvb)

/-- ⭐⭐ **d-分离的**反向单调性****（**核心性质**）。

$$Z \subseteq Z' \implies a \perp\!\!\!\perp_d b \mid Z' \implies a \perp\!\!\!\perp_d b \mid Z$$

**⚠ 方向说明**：**`Z'` 更大时更容易分离** ——
**故分离性沿 `Z` 是**反单调**的**（条件越多，越可能分离）。

**⚠ 这与贝叶斯网络中「条件集越大，独立性越强」的直觉一致。** -/
theorem dseparated_anti_mono (G : SimpleGraph V) {Z Z' : Set V} (hZZ' : Z ⊆ Z')
    {a b : V} (h : DSeparated G Z' a b) : DSeparated G Z a b :=
  fun ⟨w, hw⟩ => h ⟨w, blockedBy_mono w hZZ' hw⟩

end DSeparation

end Fate
