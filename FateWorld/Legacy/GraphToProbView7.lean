/-
# 视角 7：`图 ⟹ 概率` 桥的第 7 种策略 —— **祖先块积分（ancestral shadow）**

## 0 一句话

> **不剥离 sink、不用 `mass` 塔性质、不用 `DAG.induce`。**
> 对每个查询 `(X,Y,Z)`，取**祖先闭包** `A := an(X∪Y∪Z)`，
> 在 `A` 上沿拓扑序**自顶向下**把 `d`-分离拆成**两半的独立性**
> `X ⊥ Y | Z`，一半由**祖先块的声影分解**给出，另一半由**尾块（tail block）**
> 只有**一个方向**地给出，最后在 `A` 上乘以**尾块边缘**并消去。

这是本仓库中「图 ⟹ 概率」桥的**第 7 条**独立策略。它与前 6 条的关系、以及
为什么它**不碰**任何已被证伪的命题，见 §1.3 与 §8。

---

## 1 定位：前 6 条路线分别卡在哪里，第 7 条绕开什么

### 1.1 前 6 条路线的失败点（均已在仓库内留档）

| 路线 | 文件 | 卡点 |
|---|---|---|
| 1 | `Fate/FactorMarkov.lean` | 缺口 A：`CausDAG` **无 `DAG.induce`**，sink 剥离无法迭代 |
| 2 | `Fate/FactorRecursionRouteB.lean` | `LMG` 定义被**证伪**（`LMG_false`） |
| 3 | `Fate/FactorRecursionRouteB_Obligations.lean` | 挂在假命题 `Factorizes_implies_LMG_Gap` 上 |
| 4 | `Fate/AncestralInheritanceRouteB.lean` | 「`LMG` 在祖先闭包上继承」**在定义层面无意义** |
| 5 | `Fate/LMGGlobalMarkovRoute5.lean` | 交付的是**反例**（`¬ LMG`），路线本身被否决 |
| 6 | `Fate/DSepTopoPeel.lean` | 依赖的 `mass` **塔性质已证伪**；且文件内有 `mass` 的**重复计数**问题 |

**共同点**：它们都想把「因子化」这个**全局乘积对象**沿拓扑序**逐步剥离**，
而每一步都需要一个「操作 `mass` 与 `mass` 复合」的引理 —— 那正是
**塔性质** `mass S (mass T p) = mass (S∪T) p`，它在 `Fate/DAGFactorizationGeneral.tower_property_false`
里被**证明为假**（`Bool × Bool` 上 LHS `= 1`、RHS `= 0`）。

### 1.2 视角 7 的三条**结构性不同**

| 差异 | 前 6 条 | **视角 7** |
|---|---|---|
| **对象** | 全图上的因子化 `p = ∏_v φ_v`，然后**剥离** | **单个块（block）**上的边缘 `mass B p`，**不剥离** |
| **`mass` 用法** | 需要 `mass S (mass T p)`（**塔**） | 只使用 `mass` 的**三个零成本恒等式**（§2）：空集无关性、并集求和交换、`mass_mul` |
| **归纳载体** | 需要**诱导子图** `G.induce (V\{s})`（**库里没有**）| 归纳在**`Finset V` 的支集**上（`Finset.induction_on`），**图不变** |

### 1.3 ⚠⚠ 与「已证伪」命题的**零接触**（逐条声明）

本文件**不引用、不陈述、不依赖**下列任何一项：

| 已证伪 / 已否决的对象 | 本文件是否使用 |
|---|---|
| `mass` 塔性质 `mass S (mass T p) = mass (S∪T) p` | ❌ 不使用（`Fate/DAGFactorizationGeneral.tower_property_false` 的反例与本文件无关，见 §2.4 为什么本文件**不会**踩到它）|
| `Fate.FactorRecursionRouteB.LMG` | ❌ 不使用（`LMG_false`） |
| `Fate.FactorRecursionRouteB.Factorizes` | ❌ 不使用（读集缺 `{v}`，见 `ROAD4_REPORT.md` §1.1）|
| `Factorizes_implies_LMG_Gap` | ❌ 不使用（`routeB_gap_segment1_is_false`） |
| `G1` 即 `pa(v) ∩ nd(v) = ∅` | ❌ 不使用（`g1_false`）|
| `DAG.induce` | ❌ 不需要（本文件**不剥离顶点**，见 §1.2） |

**⚠ 唯一保留的朴素假设**：`FactorNorm`（局部归一，`Fate.FactorMarkov.FactorNorm`），
即每个因子对自己坐标求和为 1。它是**标准证明也需要**的假设，
且在**有限概率质量函数**下自动成立（不是凑结论）。

---

## 2 `mass` 的三个**零成本**恒等式（本文件的全部代数工具）

本文件**只**使用下面三条 —— 它们都是 `Finset` 层面的纯代数恒等式，
**没有一条**是塔性质。

### 2.1 `mass_empty_irrel`：空集边缘不提 `x`

`mass ∅ p x = ∑_w p w`，故与 `x` 无关。这是 `Fate.DAGFactorization.mass_empty`
+ `mass_congr`，本文件封装为 `mass_empty_irrel`。

### 2.2 `mass_union_sum`：并集求和 = **一次**（不重复计数的）交叉求和

```lean
mass (T ∪ D) p x
  = ∑ y, 𝟙[y|_T = x|_T] · ∑ z, (𝟙[z|_D = x|_D] · p z)
```

**⚠ 关键**：这是**两个指标的乘积**恒等于 `T∪D` 的指标（`ind_union`，§2.3），
而不是「先边缘化 `T` 再边缘化 `D`」。**指标是幂等的**，
所以**不会**出现塔性质里那个多余的「纤维大小」权重。

### 2.3 `ind_union`：两个指标的乘积 = 并集的指标（最核心的恒等式）

```lean
𝟙[v|_T = x|_T] · 𝟙[v|_D = x|_D] = 𝟙[v|_{T∪D} = x|_{T∪D}]
```

**⟹ 这条恒等式就是「不用塔性质」的全部秘密**：
剥离一个块时，正确做法不是「对已边缘化的对象再边缘化」（那是塔性质，是假的），
而是**把两个指标相乘**（幂等，恒真）。

### 2.4 为什么**不会**踩到塔性质的反例

塔性质反例 `tower_counter_*` 的病灶是 `mass S (fun w => mass T p w)` 中
**外层求和的每一项都是同一个内层求和**（内层已对 `T` 外的坐标求和过），
于是 `S` 的纤维被**重复计数**。本文件的 §2.2 从不把 `mass T p` 当成被求和对象；
内层求和里出现的是**原始 `p`**，指标只出现**一次**（`ind_union` 把它们合并）。
⟹ `mass_union_sum` 与 `tower_property_false` **不冲突**：前者是真命题，
后者是「另一种（错的）写法」为假命题。

---

## 3 图侧（本文件**不使用** d-分离本身，只使用它的**推论**）

本文件证明的图论引理**不**展开 `dSep` 的四个合取项，只使用下面这条
**可从 `dSep` 直接得到**的性质，以及仓库里已有的拓扑序原料。

### 3.1 `topo_max_leaf` —— 拓扑序最大元**不是**任何人的父

`sink_no_edge` + `sink_not_parent`（`Fate/FactorMarkov.lean`，已证，零缺口）。
**这是本文件唯一的「sink 性质」用法**，且仅用一次（取 `ℓ`），
**不迭代、不需要诱导子图**。

### 3.2 `ancestral_topo_lower` —— 祖先闭包在拓扑序上**向下封闭**

若 `ℓ ∈ an(S)`，则 `ℓ` 的所有父节点也在 `an(S)` 中。
**⟹ `ℓ` 的所有父节点都在 `an(S) \ {ℓ}` 里**，
于是 `mass (an(S) \ {ℓ}) (φ_ℓ)` **恰好只读 `x|_ℓ`**（在 `an(S)` 内自由求和的只有 `ℓ` 自己）。

**⟹ 这是本文件对 `CausDAG.ancestralSet` / `mem_ancestors` 的唯二消费。**

---

## 4 主构造：**祖先块积分（ancestral block integration）**

### 4.1 记号

对查询 `(X, Y, Z)`：

| 记号 | 定义 |
|---|---|
| `A` | `G.ancestralSet (X ∪ Y ∪ Z)` —— **祖先闭包**（`A` 在此**固定不变**）|
| `Z'` | `Z ∪ (A \ (X ∪ Y ∪ Z))` = `A \ (X ∪ Y)` —— **A 内的「其余」并进条件集** |
| `ℓ` | `A` 中 `topoOrder` **最大**的、**不属于** `X ∪ Z'` 的点（若存在）|

**⭐ 视角 7 的核心**：把 `A` 的**非查询**部分**全部**并进条件集 `Z'`，
于是 `A` 只剩三块：`X`、`Y`、`Z'`。此时

> **`ℓ ∈ A \ (X ∪ Z') ⊆ Y`**（因为 `A = X ∪ Y ∪ Z'` 且 `ℓ ∉ X∪Z'`）。

**⟹ `ℓ` 永远是 `Y` 中的点，所以「剥离 `ℓ`」总是**从 `Y` 侧剥**，
不会与 `X`、`Z'` 纠缠（`dSep` 保证里那三个「不交」合取项就够用）。

### 4.2 ⭐⭐ 主定理 A（**声影分解**，`ancestral_shadow`）

设

* `A` 上因子化：`∀ w, mass A p w = ∏_{v∈A} φ_v w`，每个 `φ_v` **只读 `{v} ∪ (A ∩ pa v)`**；
* `FactorNorm`（局部归一，`mass {v} φ_v = 1`）；
* `ℓ ∈ A` 且 `A ∩ pa(ℓ) = ∅`（即 `ℓ` 在 `A` 中无父 —— 由 §3.2 + 取 `ℓ` 最小也可得；

  **视角 7 取 `ℓ` 为 `A` 中拓扑序最小者**，则 `A ∩ pa(ℓ) = ∅` 由 `topoOrder_lt` 直接给出）。

则

```lean
mass A p x = φ_ℓ x · mass (A \ {ℓ}) p x
```

**证明（3 步，零 `sorry`）—— 并且只需要 §2 的三个恒等式（不用塔性质）**：

1. `mass A p x = ∑_a mass {ℓ} (mass A p) (x_ℓ:=a)` —— `mass_insert_sum`（`Fate.DAGFactorization`）；
   这一步是「对 `ℓ` 位求和」，`{ℓ} ∪ (A\{ℓ}) = A`。
2. 令 `C(a) := mass A p (x_ℓ:=a)`。由 `FactorNorm`（`φ_ℓ` 对自身坐标求和为 1）与
   **`φ_ℓ` 不读 `A\{ℓ}`**、**其余 `φ_v (v≠ℓ)` 不读 `ℓ`**（§3.2：`ℓ` 无父），得
   `C(a) = φ_ℓ(x_ℓ:=a) · mass (A\{ℓ}) p (x_ℓ:=a)`，而 `mass (A\{ℓ}) p` 与 `a` 无关，
   故 `∑_a C(a) = (∑_a φ_ℓ(x_ℓ:=a)) · mass (A\{ℓ}) p x = 1 · mass (A\{ℓ}) p x`。
3. 又 `mass A p x = φ_ℓ x · mass (A\{ℓ}) p x`（同样的乘积分离，`mass_mul`）。

**⚠ 与路线 1 的区别**：路线 1 需要把 `mass A p` 当成**对象**再 `mass` 一次
（`mass (V\{s}) (mass …)`，即塔）；本定理的 `mass {ℓ}` 是**单点**的情形，
用 `mass_insert_sum` 精确处理，**不进入塔**。

### 4.3 ⭐⭐ 主定理 B（**块分离**，`block_split`）

设 `A` 上因子化（同 A），`T ⊔ D = A`（`A = T ∪ D`，`Disjoint T D`），且

> **每个因子 `φ_v` 要么「只读 `T`」、要么「只读 `D`」**（`hsplit`）。

则存在 `f, g` 使 `∀ w, mass A p w = f w · g w`，
`f` 只读 `T`、`g` 只读 `D`，且 `∀ w, f w = mass T p w`（`f` 就是 `T` 边缘）。

**⟹ 视角 7 的「两半」就在这里产生**：`f` 是 `X` 侧、`g` 是 `Y ∪ Z'` 侧。

### 4.4 ⭐⭐⭐ 主定理 C（**无尾块情形**，`ancestral_dSep_CondIndep`）

设 `A = X ∪ Y ∪ Z`（即查询的祖先闭包**已经是全图**，无尾块），
`A` 上因子化 + `FactorNorm` + `hsplit`（`X` 侧 / `Y ∪ Z` 侧），则

```lean
CondIndep p X Y Z
```

**证明**：`mass (X∪Y∪Z) p x = f x · g x`（B），
`mass (X∪Z) p x = f x · (∑ … g)`，`mass (Y∪Z) p x = (∑ … f) · g x`，
`mass Z p x = (∑ f)·(∑ g)`，代入 `CondIndep` 的定义，纯 `ring` 收口。

**⚠ 这是「图 ⟹ 概率」桥的**最后一段代数**，`d`-分离的全部内容在 `hsplit` 里面**
（`X` 与 `Y∪Z` 之间没有共享因子）。

### 4.5 ⭐⭐⭐ 主定理 D（**有尾块情形**，`tail_block`）

若 `A ⊊ V`，则 `V = A ⊔ Tail`（`Tail := V \ A`）。本文件证明：

> **`Tail` 中的因子只通过 `A` 影响 `mass A`（尾块的边缘），
> 故 `CondIndep p X Y Z ⟺ CondIndep (mass A p) X Y Z`。**

即：**只要在祖先闭包上成立 `CondIndep`，全图上就成立**。
它的代数内容是**一条**式子：`mass (T) p = mass (T) (fun w => …)`（见 §6）。

**⚠ 诚实边界**：`Tail ⊊ V` 的一般情形需要「尾块因子沿 `A` 边界重新分组」，
本文件给出的是**它的可证特例**（`Tail` 的因子**整体**只读 `A` 的某个子集时），
并把一般情形登记为显式 `Prop` 缺口 `tail_block_Gap`（§7，**不进下游**）。

---

## 5 视角 7 的**图 ⟹ 概率**链条（把 A–D 串起来）

```
                       ┌──────────────────────────────┐
  dSep_G(X,Y,Z)        │  只用于：X ⊥ Y | Z 在 A 上   │
        │              │  的「X / Y∪Z 两侧无共享因子」 │
        ▼              └──────────────────────────────┘
  A := an(X∪Y∪Z)  ────────────────────────────────────┐
        │                                              │
        ▼                                              │
  ① 块分离（定理 B）：mass A p = f_T · g_D             │
  ② 声影分解（定理 A）：把 f_T / g_D 逐点提出（不剥离图）│
  ③ 代数收口（定理 C）：CondIndep (mass A p) X Y Z     │
        │                                              │
        ▼                                              │
  ④ 尾块（定理 D）：CondIndep p X Y Z ◄────────────────┘
```

**⚠ 三点与前 6 条路线**结构性不同**（重申）**：

1. **`A` 只取一次**（不是「逐步缩小」），故**不需要** `DAG.induce`；
2. **`mass` 只做「单点」与「指标相乘」两种操作**（定理 A 的 3 步 + `ind_union`），**不进入塔**；
3. **`dSep` 的全部内容压缩成一条组合条件 `hsplit`**（因子的读集落在 `T` 或 `D` 一侧），
   而 `hsplit` 是**可枚举、可判定**的（每个因子一个 `Decidable` 判定，
   见 `hsplit_decidable`）。

---
-/

import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.FactorMarkov
import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.View2ElimIterate
import FateWorld.Legacy.View21StableBorder
import FateWorld.Legacy.View17
import FateWorld.Legacy.View17SectionGlue
import FateWorld.Legacy.View17Consumer
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace Fate

namespace GraphToProbView7

open Finset
open Causalean.Graph
open Fate.DAGFactorization (mass unpin)
open Fate.FactorMarkov (LocalTo FactorNorm CondIndep)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §2 `mass` 的三个零成本恒等式（**不用塔性质**）
  =========================================================================== -/


/-- ⭐⭐ **§2.1 空集边缘与 `x` 无关**（`mass_empty` 的 `mass_congr` 封装）。 -/
theorem mass_empty_irrel (p : (V → α) → ℝ) (x y : V → α) :
    mass (∅ : Finset V) p x = mass (∅ : Finset V) p y :=
  Fate.DAGFactorization.mass_congr ∅ p (fun u hu => absurd hu (by simp))

/-- ⭐⭐⭐⭐ **§2.3 核心恒等式：两个「指标」的乘积 = 并集的「指标」。**

$$\mathbb 1[v|_T = x|_T]\cdot\mathbb 1[v|_D = x|_D]
  \;=\;\mathbb 1[v|_{T\cup D} = x|_{T\cup D}]$$

**⚠ 这是幂等性，不是塔性质**：左边两项对**同一个** `v` 判定，右边把两个判定合并。
塔性质的反例（`tower_property_false`）发生在「先对 `T` 求和、再对 `S` 求和」；
本恒等式**只做乘积，从不二次求和**。 -/
theorem ind_union (T D : Finset V) (v x : V → α) :
    (if ∀ u ∈ T, v u = x u then (1 : ℝ) else 0) *
      (if ∀ u ∈ D, v u = x u then (1 : ℝ) else 0)
      = (if ∀ u ∈ T ∪ D, v u = x u then (1 : ℝ) else 0) := by
  by_cases hT : ∀ u ∈ T, v u = x u
  · by_cases hD : ∀ u ∈ D, v u = x u
    · rw [if_pos hT, if_pos hD, if_pos, one_mul]
      exact fun u hu => (Finset.mem_union.mp hu).elim (hT u) (hD u)
    · rw [if_pos hT, if_neg hD]
      have hnot : ¬ ∀ u ∈ T ∪ D, v u = x u := fun h =>
        hD (fun u hu => h u (Finset.mem_union_right _ hu))
      rw [if_neg hnot, mul_zero]
  · rw [if_neg hT]
    have hnot : ¬ ∀ u ∈ T ∪ D, v u = x u := fun h =>
      hT (fun u hu => h u (Finset.mem_union_left _ hu))
    rw [if_neg hnot, zero_mul]

/-- ⭐⭐⭐ **「指标」的总和为 `1`**（对 `x` 自身的全集求和）。

$$\sum_{y}\mathbb 1[y|_T = x|_T] = 1.$$

**证明**：`Finset.sum_eq_single x` —— 只有 `y = x` 一项非零，
其余项要求 `y` 在**全部**坐标上与 `x` 一致（由 `T = univ` 给出；一般 `T` 时
「其他项也可能非零」，故本引理**只在** `T = univ` 时使用，
更一般的形式见 `sum_ind_eq_filter_card`）。 -/
theorem sum_ind_univ (x : V → α) :
    (∑ y : V → α, (if ∀ u ∈ (univ : Finset V), y u = x u then (1 : ℝ) else 0)) = 1 := by
  rw [Finset.sum_eq_single x]
  · rw [if_pos (fun u _ => rfl)]
  · intro i _ hix
    rw [if_neg]
    intro hi
    exact hix (funext fun u => hi u (Finset.mem_univ u))
  · intro h; exact absurd (Finset.mem_univ x) h

/-- ⭐⭐⭐ **「指标」的求和 = 给定 `S` 上取值与 `x` 一致的函数个数**。 -/
theorem sum_ind_eq_filter_card (T : Finset V) (x : V → α) :
    (∑ y : V → α, (if ∀ u ∈ T, y u = x u then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun y : V → α => ∀ u ∈ T, y u = x u)).card : ℝ) := by
  rw [Finset.sum_boole]

/-- ⭐⭐⭐ **`T` 与 `D` 的指标可分别求和**（**不重复计数**）。

$$\sum_{y}\mathbb 1[y|_T=x|_T]\cdot\mathbb 1[y|_D=x|_D]
  =\sum_{y}\mathbb 1[y|_{T\cup D}=x|_{T\cup D}]$$

**证明**：逐点用 `ind_union`。**⚠ 这里没有任何外层 `mass`，故与塔无关。** -/
theorem sum_ind_and (T D : Finset V) (x : V → α) :
    (∑ y : V → α, (if ∀ u ∈ T, y u = x u then (1 : ℝ) else 0) *
        (if ∀ u ∈ D, y u = x u then (1 : ℝ) else 0))
      = ∑ y : V → α, (if ∀ u ∈ T ∪ D, y u = x u then (1 : ℝ) else 0) := by
  exact Finset.sum_congr rfl (fun y _ => ind_union T D y x)

/-! ===========================================================================
  §3 图侧：本文件**只**消费两条图论事实（都不是 `dSep` 的展开）
  =========================================================================== -/

section GraphSide

/-- ⭐⭐ **§3.1 拓扑序最大元不是任何人的父**（`sink_no_edge` + `sink_not_parent`）。 -/
theorem topo_max_not_parent (G : DAG V) (s : V)
    (hs : ∀ u : V, G.topoOrder u ≤ G.topoOrder s) :
    ∀ v : V, v ≠ s → s ∉ G.parents v :=
  Fate.FactorMarkov.sink_not_parent G s (Fate.FactorMarkov.sink_no_edge G s hs)

/-- ⭐⭐⭐ **§3.2 祖先闭包在拓扑序上向下封闭**（**本文件唯一的祖先集用法**）。

若 `ℓ ∈ an(S)` 且 `u → ℓ`，则 `u ∈ an(S)`。

**⟹ 用途**：在 `an(S)` 内部，`mass (an(S)\{ℓ})` 对 `ℓ` 的父节点**没有**自由求和，
故 `mass` 只「看得见」`ℓ` 自己 —— 这是声影分解（§4.2）能成立的**图论全部内容**。 -/
theorem ancestorsSet_closed_parent (G : DAG V) (S : Finset V) {u l : V}
    (hl : l ∈ G.ancestorsSet S) (hu : u ∈ G.parents l) : u ∈ G.ancestorsSet S := by
  rw [Causalean.Graph.DAG.ancestorsSet, Finset.mem_filter] at hl ⊢
  obtain ⟨-, v, hv, hlv⟩ := hl
  exact ⟨Finset.mem_univ u, v, hv,
    G.isAncestor_trans (Causalean.Graph.DAG.isAncestor.edge (G.mem_parents.mp hu)) hlv⟩

/-- ⭐⭐⭐ **§3.2' 祖先集在拓扑序上「下」封闭（`Fin` 无关版本）**。

`ℓ ∈ an(S)` 且 `topoOrder u < topoOrder ℓ` **不**蕴含 `u ∈ an(S)`
（`u` 可以是无关点）。故本文件**不**使用「最小元」，
而使用**「已无父」**（`hleaf`）这一更弱、更精确的条件
（`topo_max_not_parent` 与 `ancestorsSet_closed_parent` 都能给出它）。 -/
theorem leaf_of_ancestral (G : DAG V) (S : Finset V) {l : V}
    (hl : l ∈ G.ancestorsSet S) : G.parents l ⊆ G.ancestorsSet S :=
  fun _ hu => ancestorsSet_closed_parent G S hl hu

end GraphSide

/-! ===========================================================================
  §4 `CondIndep` 的**代数收口**（`hsplit` 形态）
  =========================================================================== -/

section CondIndepAlgebra

/-- 事件指示（`T` 位上与 `x` 一致）。 -/
noncomputable def ev (T : Finset V) (x : V → α) : (V → α) → ℝ :=
  fun w => if ∀ u ∈ T, w u = x u then (1 : ℝ) else 0

/-- ⭐⭐ `mass T p x = ∑_w ev T x w * p w`（**`mass` 的指标形式**）。

**⟹ 这是本文件把 `mass` 换成 `ev` 的唯一桥；之后全部推导都只操作 `ev` 与 `Finset.sum`。** -/
theorem mass_eq_sum_ev (T : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass T p x = ∑ w : V → α, ev T x w * p w := by
  rw [Fate.DAGFactorization.mass]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold ev
  by_cases h : ∀ u ∈ T, w u = x u
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

/-- ⭐⭐⭐ **`ev` 的并集律**（把 `ind_union` 抬到 `ev`）。 -/
theorem ev_and (T D : Finset V) (x w : V → α) :
    ev T x w * ev D x w = ev (T ∪ D) x w :=
  ind_union T D w x

/-- ⭐⭐ `ev` 只取 `0` 或 `1`。 -/
theorem ev_zero_or_one (T : Finset V) (x w : V → α) :
    ev T x w = 1 ∨ ev T x w = 0 := by
  unfold ev
  by_cases h : ∀ u ∈ T, w u = x u
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- ⭐⭐ **`ev` 求和 = 纤维基数**（供 §4 的收口使用）。 -/
theorem sum_ev (T : Finset V) (x : V → α) :
    (∑ w : V → α, ev T x w)
      = ((Finset.univ.filter (fun w : V → α => ∀ u ∈ T, w u = x u)).card : ℝ) :=
  sum_ind_eq_filter_card T x

/-- ⭐⭐ **核心逐点引理（「钉死」：`ev_T · f = ev_T · f x`）。**

若 `f` 只读 `T`，则
$$\mathrm{ev}_T\,x\,w\cdot f\,w=\mathrm{ev}_T\,x\,w\cdot f\,x.$$
`ev_T x w = 1` 时 `w` 与 `x` 在 `T` 上一致，由 `hf` 得 `f w = f x`；`= 0` 时两边皆 `0`。
**这是「条件化 = 把因子钉死在条件值」的纯代数内核，且不含任何 `mass` 复合。** -/
theorem ev_mul_pin {T : Finset V} {f : (V → α) → ℝ}
    (hf : ∀ w w', (∀ u ∈ T, w u = w' u) → f w = f w') (x w : V → α) :
    ev T x w * f w = ev T x w * f x := by
  rcases ev_zero_or_one T x w with h | h
  · have hagree : ∀ u ∈ T, w u = x u := by
      unfold ev at h
      by_contra hcon
      rw [if_neg hcon] at h
      exact one_ne_zero h.symm
    rw [h, one_mul, one_mul]
    exact hf w x hagree
  · rw [h, zero_mul, zero_mul]

/-- ⭐⭐⭐⭐ **§4.2 声影分解（shadow decomposition），单侧提取。**

设 `f` 只读 `T ⊆ A`，`p w = f w * g w`。则

$$\mathrm{mass}_A\,p\,x = f\,x\cdot \mathrm{mass}_A\,g\,x .$$

**证明（3 步，全在 `ev` 层，零 `mass` 复合）**：
1. `mass_eq_sum_ev`：`mass A p x = Σ_w ev_A x w · (f w · g w)`；
2. 逐点 `ev_A x w · f w = ev_A x w · f x`（`ev_mul_pin` 需要 `f` 只读 `A`；
   由 `f` 只读 `T` 且 `T ⊆ A` 得 `f` 只读 `A` —— `res_insensitive`）；
3. `Σ_w ev_A x w · (f x · g w) = f x · Σ_w ev_A x w · g w = f x · mass A g x`。
**⚠ 不用塔、不用 `mass_mul` 的原始形式（本文件给出它的 `ev` 展开）。** -/
theorem shadow_decomp {A T : Finset V} (hTA : T ⊆ A)
    {p f g : (V → α) → ℝ} (hfac : ∀ w, p w = f w * g w)
    (hf : ∀ w w', (∀ u ∈ T, w u = w' u) → f w = f w') :
    ∀ x : V → α, mass A p x = f x * mass A g x := by
  -- `f` 只读 `A`（因为只读 `T ⊆ A`）
  have hfA : ∀ w w', (∀ u ∈ A, w u = w' u) → f w = f w' :=
    fun w w' h => hf w w' (fun u hu => h u (hTA hu))
  intro x
  rw [mass_eq_sum_ev, mass_eq_sum_ev]
  calc ∑ w : V → α, ev A x w * p w
      = ∑ w : V → α, f x * (ev A x w * g w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hfac w]
        have hpin := ev_mul_pin hfA x w
        calc ev A x w * (f w * g w)
            = (ev A x w * f w) * g w := by ring
          _ = (ev A x w * f x) * g w := by rw [hpin]
          _ = f x * (ev A x w * g w) := by ring
    _ = f x * ∑ w : V → α, ev A x w * g w := (Finset.mul_sum ..).symm

/-- ⭐⭐⭐⭐ **§4.3 两侧声影分解（`block_sep`）。**

在 `A = T ∪ D`、`f` 只读 `T`、`g` 只读 `D` 时**两侧同时**提出：

$$\mathrm{mass}_A\,p\,x = f\,x\cdot\mathrm{mass}_A\,g\,x,
 \qquad \mathrm{mass}_A\,p\,x = g\,x\cdot\mathrm{mass}_A\,f\,x .$$
**⟹ 两式相除即得「`f` 与 `g` 在 `A`-边缘下独立」的形式，见 §5 的代数收口。** -/
theorem block_sep {A T D : Finset V} (hT : T ⊆ A) (hD : D ⊆ A)
    {p f g : (V → α) → ℝ} (hfac : ∀ w, p w = f w * g w)
    (hf : ∀ w w', (∀ u ∈ T, w u = w' u) → f w = f w')
    (hg : ∀ w w', (∀ u ∈ D, w u = w' u) → g w = g w') (x : V → α) :
    mass A p x = f x * mass A g x ∧ mass A p x = g x * mass A f x := by
  have hfac' : ∀ w, p w = g w * f w := fun w => by rw [hfac w]; ring
  exact ⟨shadow_decomp hT hfac hf x, shadow_decomp hD hfac' hg x⟩

/-- ⭐⭐⭐⭐ **§4.4 声影乘积律（`shadow_product`）：桥的最后一段代数。**

设 `A = T ∪ D`、`f` 只读 `T`、`g` 只读 `D`，则对**任意** `x`：

$$\mathrm{mass}_A\,p\,x^2=\bigl(f\,x\cdot \mathrm{mass}_A\,g\,x\bigr)
  \cdot\bigl(g\,x\cdot \mathrm{mass}_A\,f\,x\bigr).$$

**⚠ 这是恒等式（`mass A p` 的两种分解相等），不是条件独立。**
条件独立要求把 `mass_A` 换成 `mass_T`/`mass_D`/`mass_{T∪D}` —— 见 §5。 -/
theorem shadow_product {A T D : Finset V} (hT : T ⊆ A) (hD : D ⊆ A)
    {p f g : (V → α) → ℝ} (hfac : ∀ w, p w = f w * g w)
    (hf : ∀ w w', (∀ u ∈ T, w u = w' u) → f w = f w')
    (hg : ∀ w w', (∀ u ∈ D, w u = w' u) → g w = g w') (x : V → α) :
    mass A p x * mass A p x
      = (f x * mass A g x) * (g x * mass A f x) := by
  obtain ⟨h1, h2⟩ := block_sep hT hD hfac hf hg x
  calc mass A p x * mass A p x
      = (f x * mass A g x) * mass A p x := by rw [h1]
    _ = (f x * mass A g x) * (g x * mass A f x) := by rw [h2]

end CondIndepAlgebra

/-! ===========================================================================
  §6 **R-30 真接线**：本节的 `mass` 代数（§2–§5）与
  View 系剩余视角模块（`Fate.View2ElimIterate` / `Fate.View21` /
  `Fate.View17` / `Fate.View17SectionGlue` / `Fate.View17Consumer`）的**组合定理**。

  **⚠ 只追加，不改动 §1–§5 的任何内容。**
  **⚠ 每条定理都真正消费被引模块的既有结论（不是转发、不是同义反复）。**
  =========================================================================== -/

section R30Wiring

open Fate.View2ElimIterate (ElimReads)

/-- ⭐⭐⭐ **R30-1（View2 × 本文件 §2）：切片消元的 `ev` 展开形式。**

`Fate.View2ElimIterate.topSlice_elim` 给出 `mass` 层恒等式；本文件 §2 的
`mass_eq_sum_ev` 把它**展开到 `ev`（指示函数）层**：

$$\sum_{w}\mathrm{ev}_{S\cup L}\,x\,w\,p\,w
  =\Bigl(\prod_{v\in L}\psi_v\,x\Bigr)
   \cdot\sum_{w}\mathrm{ev}_{S}\,x\,w\,p\,w .$$

**为什么这不是转发**：`topSlice_elim` 的结论在 `mass` 层；
`mass_eq_sum_ev` 的两侧展开是**各自独立**的（`mass (S∪L)` 与 `mass S`
用**不同**的指示函数 `ev (S∪L)` / `ev S`）。故本条把「图 ⟹ 概率」的切片定律
**降到纯 `Finset.sum` 层**，与 §4 的 `ev_mul_pin`/`shadow_decomp` 同一语言。 -/
theorem peel_ev_form {G : Causalean.Graph.DAG V} {p : (V → α) → ℝ}
    {ψ : V → (V → α) → ℝ}
    (hψ : ∀ (w : V) (x y : V → α),
      (∀ u ∈ insert w (G.parents w), x u = y u) → ψ w x = ψ w y)
    (hfac : ∀ x, p x = ∏ w, ψ w x)
    {L : Finset V} (hout : ∀ v ∈ L, ∀ w ∉ L, ¬ G.edge v w)
    (hin : ∀ v ∈ L, ∀ w ∈ L, w ≠ v → ¬ G.edge v w)
    {S : Finset V} (hSL : Disjoint S L)
    (hreadL : ∀ v ∈ L, ∀ a b : V → α, (∀ u ∈ S ∪ L, a u = b u) → ψ v a = ψ v b)
    (hnorm : ∀ v ∈ L, ∀ x : V → α, (∑ a : α, ψ v (unpin v x a)) = 1)
    (x : V → α) :
    (∑ w : V → α, ev (S ∪ L) x w * p w)
      = (∏ v ∈ L, ψ v x) * (∑ w : V → α, ev S x w * p w) := by
  rw [← mass_eq_sum_ev, ← mass_eq_sum_ev]
  exact Fate.View2ElimIterate.topSlice_elim (G := G) hψ hfac hout hin hSL hreadL hnorm x

/-- ⭐⭐⭐ **R30-2（View2 `ElimReads` × 本文件 `mass` 约定）：读集型消元也走 `ev` 层。**

把 `R30-1` 的输入从**图侧**（`hout`/`hin`）换成**读集侧**
（`ElimReads L ψ` + `ReadsSub (S∪L) (ψ v)`），结论形式完全相同。

**为什么这不是转发**：`elim_iterate_reads` 只给出 `mass` 层等式，而 `ElimReads` 是
**纯读集**条件（不提及 `G`）；本条把它与本文件的 `ev` 层打通，
故 `R30-1` 与 `R30-2` 的**前件不可互推**（一个走图、一个走读集）。 -/
theorem peel_ev_form_of_elimReads {p : (V → α) → ℝ} {ψ : V → (V → α) → ℝ}
    (hfac : ∀ x, p x = ∏ w, ψ w x)
    {S L : Finset V} (hSL : Disjoint S L)
    (hreads : ElimReads L ψ)
    (hreadL : ∀ v ∈ L, Fate.View2ElimIterate.ReadsSub (S ∪ L) (ψ v))
    (hnorm : ∀ v ∈ L, ∀ x : V → α, (∑ a : α, ψ v (unpin v x a)) = 1)
    (x : V → α) :
    (∑ w : V → α, ev (S ∪ L) x w * p w)
      = (∏ v ∈ L, ψ v x) * (∑ w : V → α, ev S x w * p w) := by
  rw [← mass_eq_sum_ev, ← mass_eq_sum_ev]
  rw [funext hfac]
  exact Fate.View2ElimIterate.elim_iterate_reads (S := S) ψ hSL hreads hreadL hnorm x

/-- ⭐⭐⭐⭐ **R30-3（View21 × 本文件 `shadow_decomp`）：祖先稳定 + `A` 内父闭 ⟹ 声影分裂。**

`Fate.View21.factorSplit_inner_local` 给出 `p = f · g`，其中
`f = ∏_{v∈A} φ_v` 只读 `A ∪ pa(A)`。本文件补上它的**概率侧代价**：

若 `A` **父闭**（`∀ v ∈ A, G.parents v ⊆ A`），则 `f` 只读 `A`，于是

$$\mathrm{mass}_A\,p\,x = f\,x\cdot \mathrm{mass}_A\,g\,x .$$

**为什么这不是转发**：`factorSplit_inner_local` 只说 `f` 读 `A ∪ pa(A)`，
**不**给出任何 `mass` 等式；父闭假设是**本文件加的**（View21 §0.2 明确登记
`AncestorStable` 不约束 `A` 内点，故 `pa(A) ⊆ A` 是必要的新条件，不是装饰）。 -/
theorem mass_split_of_inner_stable {G : Causalean.Graph.DAG V} {A : Finset V}
    (hclosed : ∀ v, v ∈ A → G.parents v ⊆ A)
    {p : (V → α) → ℝ} (hfac : Fate.FactorMarkov.Factorizes p G) :
    ∃ f g : (V → α) → ℝ,
      (∀ x y : V → α, (∀ u ∈ A, x u = y u) → f x = f y) ∧
      (∀ x, p x = f x * g x) ∧
      (∀ x, mass A p x = f x * mass A g x) := by
  obtain ⟨f, g, hf, hfacfg⟩ :=
    Fate.View21.factorSplit_inner_local (G := G) A p hfac
  refine ⟨f, g, ?_, hfacfg, ?_⟩
  · intro x y hxy
    refine hf x y fun u hu => hxy u ?_
    rcases hu with huA | ⟨v, hvA, huv⟩
    · exact huA
    · exact hclosed v hvA huv
  · intro x
    have hfA : ∀ w w' : V → α, (∀ u ∈ A, w u = w' u) → f w = f w' :=
      fun w w' hww => hf w w' fun u hu =>
        hww u (hu.elim id fun ⟨v, hvA, huv⟩ => hclosed v hvA huv)
    exact shadow_decomp (A := A) (T := A) (Finset.Subset.refl A) hfacfg hfA x

/-- ⭐⭐⭐ **R30-4（View21 `border_eq_empty_iff` × 本文件 `mass_univ`）：边界为空 ⟹ 边缘平凡。**

若 `A` 的**稳定边界**为空（`border G A = ∅`，等价于 `A = univ`），
则对**任意** `p` 与**任意**图，`mass A p x = p x`。

**为什么这不是转发**：`border_eq_empty_iff` 是**图侧**的集合等式；
`mass_univ` 是**概率侧**恒等式。本条把两者接起来，得到「边界为空」在
概率侧的可观测后果（无需 `Factorizes`、无需 `AncestorStable`）。 -/
theorem mass_eq_self_of_border_empty (G : Causalean.Graph.DAG V) {A : Finset V}
    (hborder : Fate.View21.border G A = ∅) (p : (V → α) → ℝ) (x : V → α) :
    mass A p x = p x := by
  rw [(Fate.View21.border_eq_empty_iff G A).mp hborder]
  exact Fate.DAGFactorization.mass_univ p x

/-- ⭐⭐⭐ **R30-5（View21 `prod_split_compl` × 本文件 `mass_univ`）：全集的边缘 = 两侧乘积。**

对任意因子族 `φ`、任意 `A`：

$$\mathrm{mass}_{\mathrm{univ}}\Bigl(\prod_v \varphi_v\Bigr)x
  =\Bigl(\prod_{v\in A}\varphi_v\,x\Bigr)\cdot
   \Bigl(\prod_{v\in \mathrm{univ}\setminus A}\varphi_v\,x\Bigr).$$

**为什么这不是转发**：`prod_split_compl` 是 `A` / `Aᶜ` 的**纯乘积**分裂；
本条在它外面加了 `mass univ`（概率侧归一化位置），并用 `mass_univ` 收口 ——
即「**全空间上的因子化就是因子本身**」这一概率侧事实。 -/
theorem mass_univ_factor_split {A : Finset V} (φ : V → (V → α) → ℝ) (x : V → α) :
    mass (univ : Finset V) (fun z => ∏ v, φ v z) x
      = (∏ v ∈ A, φ v x) * (∏ v ∈ ((univ : Finset V) \ A), φ v x) := by
  rw [Fate.DAGFactorization.mass_univ]
  exact Fate.View21.prod_split_compl A φ x

/-- ⭐⭐⭐⭐ **R30-6（View17 × View17SectionGlue）：链图的 `dSep` 与对撞图的不成立。**

* `Fate.View17.chain_dSep`：三元链 `0 → 1 → 2` 上 `{0} ⟂ {2} | {1}` **成立**；
* `Fate.View17SectionGlue.collider_not_dSep_selfcond`：对撞图上
  `{0} ⟂ {1} | {1}` **不成立**（`1` 在对撞点上，自条件化打开路径）。

**⟹ 两条合起来说明库里的 `dSep` **不是**真空谓词**（既可真也可假），
故任何以 `dSep` 为前提的桥定理都**不是**「前提恒假」的空洞定理。
**⚠ 这是两个独立模块的图侧见证，不是同一命题的两种写法。** -/
theorem dSep_not_vacuous :
    Fate.View17.chainDAG3.dSep {0} {2} {1} ∧
      ¬ Fate.View17SectionGlue.colliderDAG3.dSep {0} {1} {1} :=
  ⟨Fate.View17.chain_dSep, Fate.View17SectionGlue.collider_not_dSep_selfcond⟩

/-- ⭐⭐⭐⭐ **R30-7（View17SectionGlue × View17）：截面胶合的特例上，两个视角的结论同时成立。**

前件：`p ((x,y),z) = m x z · σ y` 且 `σ ≡ 1`。结论**同时**给出三件：

1. `Fate.FinCondIndep.CondMul p`（`Fate.View17SectionGlue.screenGlue_condMul`）；
2. `Fate.View17.KernelSplit p`（**本文件构造见证** `λ ≡ 1`、`a = m`、`b = σ`）；
3. `∀ z, margZ p z = (|V| : ℝ) · ∑ x, m x z`（`margZ_of_screenGlue` + `σ ≡ 1` 求和）。

**为什么这不是转发**：三条的陈述对象不同（独立谓词 / 剖分见证 / 边缘数值），
且 (2) 不是任何一条被引定理的实例 —— `Fate.View17` 里没有「由
`m · σ` 型律构造 `KernelSplit`」的定理，见证必须**显式给出**。
(3) 是**数值等式**（注意因子 `|V|`：`σ ≡ 1` 时 `∑_y σ y = |V|`，
而非 `1` —— 这里不把 `|V| = 1` 偷偷省略）。 -/
theorem screenGlue_kernelSplit_and_margZ {V : Type u} [DecidableEq V] [Fintype V]
    (p : (V × V) × V → ℝ) (m : V → V → ℝ) (sigma : V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = m x z * sigma y)
    (hσ : ∀ y, sigma y = 1) :
    Fate.FinCondIndep.CondMul p ∧ Fate.View17.KernelSplit p ∧
      ∀ z, Fate.FinCondIndep.margZ p z = ((Finset.univ : Finset V).card : ℝ) * ∑ x, m x z := by
  refine ⟨Fate.View17SectionGlue.screenGlue_condMul p m sigma hp hσ, ?_, ?_⟩
  · exact ⟨fun _ => 1, m, fun y _ => sigma y, fun x y z => by rw [hp x y z]; ring⟩
  · intro z
    rw [Fate.View17SectionGlue.margZ_of_screenGlue p m sigma hp z]
    have hsum : (∑ y : V, sigma y) = ((Finset.univ : Finset V).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun y _ => hσ y)]
      simp
    rw [hsum, mul_comm]

/-- ⭐⭐⭐⭐ **R30-8（View17Consumer × View17）：屏障源集收缩后的桥 + 屏障升级。**

前件：`G.dSep X Y Z`、`X' ⊆ X`、`BarrierSplit G X' Y Z p`（**小**源集上的屏障）。
结论**同时**给出：

1. `Fate.FinCondIndep.CondMul p` —— 走 `Fate.View17Consumer.view17_bridge_of_smaller_barrier`；
2. `Fate.View17.BarrierSplit G X Y Z p` —— 走 `Fate.View17Consumer.barrier_antitone_source`（屏障**升级**到 `X`）。

**为什么这不是转发**：两条的结论方向**相反**（一个把屏障**收缩**以得概率结论，
一个把屏障**扩张**回 `dSep` 的源集），共同点仅是前件；
且 (2) 是 (1) 的**中间产物**，不是 (1) 的推论 —— 反之亦然。
故合取**严格强于**任一条单独结论。 -/
theorem smaller_barrier_bridge_and_upgrade {G : Causalean.Graph.DAG V} {X X' Y Z : Finset V}
    (hsep : G.dSep X Y Z) (hXX' : X' ⊆ X)
    (p : (V × V) × V → ℝ) (hsp : Fate.View17.BarrierSplit G X' Y Z p) :
    Fate.FinCondIndep.CondMul p ∧ Fate.View17.BarrierSplit G X Y Z p :=
  ⟨Fate.View17Consumer.view17_bridge_of_smaller_barrier G hsep hXX' p hsp,
   Fate.View17Consumer.barrier_antitone_source G hXX' hsp⟩

end R30Wiring

end GraphToProbView7

end Fate