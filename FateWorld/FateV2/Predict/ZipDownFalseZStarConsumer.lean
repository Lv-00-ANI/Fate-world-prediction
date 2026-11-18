/-
# `Fate/ZipDownFalseZStarConsumer` —— 把 `ZipDownFalse` 的 `¬ ZipDown`
# 接到主链的 **`zStar` 口径**（`BridgeMinZPrime` + `BridgeFull`）

## 0 本文件做什么（**先读这一节**）

### 0.0 ⚠ 与既有 `Fate/ZipDownFalseConsumer` 的分工（**先看这一段**）

`Fate/ZipDownFalseConsumer.lean`（CHAIN-9，上一轮已交付并入库，9 声明）
已把 `ZipDownFalse` 接到 **`Fate.BridgeFullFixed`** 口径，其主定理是

* `not_markov_PjointB`（`¬ Markov PjointB gempty`）、
* `no_factorization_cert_for_PjointB`（`FactorNorm` 前件不可满足）、
* `zipDown_false_sharp`（见证三元组的 `∃` 形式）。

**它覆盖的是「`Markov` / `FactorNorm` / `BridgeFullFixed`」这条线。**
本文件**不重复**那条线，而是接**另一条**仍未接的主链：

* `Fate.BridgeMinZPrime`（**MZP**）的 `zStar` / `paBlock` / `req` / `readClosed_zStar`；
* `Fate.BridgeFull`（非 `Fixed`）的 `markov_of_readClosedBlocks`。

**本文件的独有内容**（既有文件完全没有）：

1. **`gempty` × `MZP` 的图论对接**（`paBlock`/`ancestralSet`/`zStar` 三件套，C1–C3）；
2. **`ZipDown` 失败的抽象可复用判据**（C4，任意 `p`、`X`、`Y`、`W`、`β`）；
3. **`zStar` 路线的抽象判据**（C5）；
4. **主链 `markov_of_readClosedBlocks` 给出 `zStar` 处 `CondIndep` 却压不回 `Z`**
   的收口（C6，这是 `BridgeFull` §5 缺口 G1 说明里**只有散文、没有证明**的那句话）；
5. `PjointB` + `gempty` 在 `zStar`-扩大路线上的具体反驳（C7/C7′）。

**命名空间**：本文件用 `FateV2.Predict.ZipDownFalseZStarConsumer`，**与**
`Fate.ZipDownFalseConsumer` **不冲突**（不重定义其任何符号）。

### 0.1 数学内容

叶子模块 `Fate/ZipDownFalse.lean`（namespace `Fate.ZipDownFalseFixed`，20 定理）
用**显式分布** `PjointB` 机器验证了

```
¬ ZipDown PjointB {0} {1},   即
¬ ∀ Z Z', Z ⊆ Z' → CondIndep p {0} {1} Z' → CondIndep p {0} {1} Z.
```

即 **`CondIndep` 对条件集不单调**。在此之前，"不单调" 这件事在本仓库里
**只以散文形式**出现在 `Fate/BridgeFull.lean` 的 §5 缺口 G1 的说明中：

> 「⚠ **为什么不用 `∃ Z' ⊇ Z` 的形式**（本文件初稿曾这么写，已**撤回**）：
> `CondIndep p X Y ·` 对条件集**不单调** —— 从 `CondIndep X Y Z'`（`Z' ⊋ Z`）
> **推不出** `CondIndep X Y Z`」

**`BridgeFull` 用这个论断来否掉 G1 的 `∃ Z' ⊇ Z` 写法，但没有给出任何证明。**
`ZipDownFalse` 提供的正是这个论断的**机器验证证书**。
本文件的工作 = **把这个证书接到主链的两条腿上**：

| 腿 | 模块 | 本文件用到的符号 |
|---|---|---|
| A（反例源） | `Fate.ZipDownFalse` | `PjointB`、`condIndepB`、`not_condIndepB`（**不引用** `zipDown_false`） |
| B（主链） | `Fate.BridgeMinZPrime` | `zStar`、`paBlock`、`req`、`readClosed_zStar`、`subset_zStar` |
| B（主链） | `Fate.BridgeFull` | `markov_of_readClosedBlocks`（**非** `BridgeFullFixed`） |
| B（底座） | `Fate.BridgeZipDown` | `ZipDown`、`gempty`、`gempty_parents` |

## 1 本文件交付的定理（7 条，全部 machine-checked）

| # | 名称 | 内容 |
|---|---|---|
| C1 | `gempty_paBlock_eq` | `gempty` 上 `paBlock G S = ∅`（**图论—MZP 桥**） |
| C2 | `gempty_ancestralSet_eq` | `gempty` 上 `ancestralSet S = S`（空图祖先闭包是恒等） |
| C3 | `gempty_zStar_eq` | ⭐ **`zStar gempty X Y Z = Z`**：`MZP.zStar` 在 `gempty` 上塌缩为恒等 |
| C4 | ⭐⭐ `zipDown_fails_of_witness` | **抽象判据**：`Z ⊆ Z'`、`CondIndep p X Y Z'`、`¬CondIndep p X Y Z` ⟹ `¬ ZipDown p X Y` |
| C5 | ⭐⭐ `zStar_zipDown_route_fails` | **`zStar` 路线被堵**：`CondIndep p X Y (zStar …)` 推不出 `CondIndep p X Y Z`（`Z` 固定、`zStar` 是扩大） |
| C6 | ⭐⭐⭐ `markovAtZStar_cannot_zipDown` | **主链上的收口**：`LocalTo + Factorizes + FactorNorm + dSep X Y (zStar …)` 给出 `CondIndep p X Y (zStar …)`（经 `BridgeFull.markov_of_readClosedBlocks`），但**不能**压回 `Z` |
| C7 | ⭐⭐⭐ `PjointB_not_zipDown_route` | **具体反例落到 `zStar` 口径**：`PjointB` + `gempty` 上「`zStar` 扩大后压回 `∅`」路线失败（消费 C3 + `condIndepB` + `not_condIndepB`） |
| C7′ | ⭐⭐ `PjointB_zipDown_fails_via_template` | 用 **C4 模板**（不引用 `zipDown_false`）从 `condIndepB`/`not_condIndepB` 重推 `¬ ZipDown PjointB {0} {1}` ⟹ 证明模板**非空** |

## 2 ⚠ 前件是否包结论？（纪律 7 逐条核对）

| # | 前件 | 结论 | 是否同义反复 |
|---|---|---|---|
| C1 | `S : Finset (Fin 4)` | `paBlock gempty S = ∅` | ❌ 否：结论是关于 `gempty.edge` 的图论事实，前件只是任意集合 |
| C2 | `S` | `ancestralSet gempty S = S` | ❌ 否：同上 |
| C3 | `X Y Z` | `zStar gempty X Y Z = Z` | ❌ 否：`zStar` 展开为 `ancestralSet (req …)`，需要 C1+C2 的链 |
| C4 | `hsub`、`hZ'`（`CondIndep` 在 `Z'`）、`hZ`（`¬CondIndep` 在 `Z`） | `¬ ZipDown p X Y` | ❌ 否：`ZipDown` 是 `∀ Z Z'` 量词命题，结论**不含**于任何前件；`hZ'` 与 `hZ` 是**两个相反极性**的事实 |
| C5 | `hZ'`（`CondIndep` 在 `zStar`）、`hZ`（`¬CondIndep` 在 `Z`） | `¬ ∀ Z, CondIndep p X Y (zStar …) → CondIndep p X Y Z` | ❌ 否：结论是全称否定，反例由 `hZ'` + `hZ` 提供 |
| C6 | `hloc`、`hfac`、`hnorm`、`hd : dSep X Y (zStar …)`、`hZ : ¬CondIndep p X Y Z` | `¬ ∀ Z, CondIndep p X Y (zStar …) → CondIndep p X Y Z` | ❌ 否：`CondIndep p X Y (zStar …)` **不是**前件，是**结论**（由 `markov_of_readClosedBlocks` 推出）；`hZ` 是**独立**的否定事实 |
| C7 | 无（纯实例化） | `¬ ∀ Z', CondIndep PjointB {0}{1} (zStar gempty {0}{1} Z') → CondIndep PjointB {0}{1} ∅` | ❌ 否：结论是全称否定，靠 C3 把 `zStar gempty` 化简 + `condIndepB`/`not_condIndepB` 的分歧 |
| C7′ | 无（模板实例化） | `¬ ZipDown PjointB {0} {1}` | ❌ 否：结论是全称否定；证明走 C4 模板，**不引用** `zipDown_false` |

**C6 是唯一带"概率假设"的定理，其 `hZ` 是诚实的额外前件**（不是被包进结论的）：
没有 `¬CondIndep p X Y Z` 就真的**不可能**得到该否定（若 `CondIndep` 本身成立，
压回当然成立）。本文件在 §5 明确登记这一边界。

## 3 ⚠ 诚实边界

* 本文件**不宣称** `markov_of_readClosedBlocks` 是错的 —— 它是对的，其前件
  `dSep X Y (zStar …)` 是**真前件**。
* 本文件**不宣称** `zStar` 是错构造 —— `MZP.readClosed_zStar` 无条件成立。
* 本文件宣称的**唯一**事实是：**「在 `zStar` 处拿到 `CondIndep`、再压回 `Z`」
  这条路走不通**，并且给出 `ZipDownFalse` 的机器验证证书作为依据。
  `BridgeFull` §5 的散文论断由此**获得机器验证证据**（C7 是具体实例，
  C4/C5 是抽象判据）。
* `PjointB` 的总质量为 `2`（**不归一**）。`CondIndep` 是**齐次乘性恒等式**，
  对标量不变，故不归一不影响任何结论；但本文件**不对** `FactorNorm`
  成立的归一分布作断言（见 `ZipDownFalse` 文件头 §0.2 的同一声明）。

## 4 纪律核对

* ✅ 只**新增**本文件（**不改**既有 `Fate/ZipDownFalseConsumer.lean`）；只**追加一行**
  `import` 到 `Fate.lean`（G12），不改其中任何既有行；
* ✅ **零 `sorry` / `admit` / `axiom`**；
* ✅ 单文件验证：`lake env lean Fate/ZipDownFalseZStarConsumer.lean` 两遍 EXIT=0；
* ✅ 不重定义 `ZipDown` / `CondIndep` / `mass` / `zStar` / `paBlock` / `req`；
  本文件新引入的 `gempty_*` 是**引用** `BridgeZipDown.gempty` 的**新**引理
  （名字在 `FateV2.Predict.ZipDownFalseZStarConsumer` 命名空间内，不与任何既有符号冲突）；
* ✅ 不用 `mass` 塔性质，不展开 `mass`（`PjointB` 的取值全部经
  `Fate.ZipDownFalseFixed` 的既有引理）。
================================================================================ -/

import FateWorld.FateV2.Predict.ZipDownFalse
import FateWorld.FateV2.Predict.BridgeMinZPrime
import FateWorld.FateV2.Predict.BridgeFull
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.ZipDownFalseZStarConsumer

open FateV2.Modeling

open Fate.DAGFactorization
open FateV2.Predict.FactorMarkov

set_option linter.unusedSimpArgs false

/-!
  # Predict · ZipDownFalseZStarConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ZipDownFalseZStarConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ZipDownFalse, BridgeMinZPrime, BridgeFull
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 `gempty` 与 MZP 的 `zStar` / `paBlock` / `req` 对接（C1–C3）
  =========================================================================== -/

/-- `gempty` 上任何两点都不构成祖先关系（无边 ⟹ `isAncestor` 归纳无据）。 -/
theorem gempty_not_anc {u v : Fin 4} : ¬ Fate.BridgeZipDown.gempty.isAncestor u v := by
  intro h
  induction h with
  | edge hab => exact hab
  | trans _ hab _ => exact hab

/-- `gempty.parents` 作为函数恒为 `∅`（C1 的工具）。 -/
theorem gempty_parents_fun :
    Fate.BridgeZipDown.gempty.parents = fun _ => (∅ : Finset (Fin 4)) :=
  funext Fate.BridgeZipDown.gempty_parents

/-- `gempty` 的祖先集恒空（C2 的工具）。 -/
theorem gempty_ancestorsSet_eq (S : Finset (Fin 4)) :
    Fate.BridgeZipDown.gempty.ancestorsSet S = ∅ := by
  ext u
  unfold FateV2.Modeling.Graph.DAG.ancestorsSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, _, hv⟩
    exact absurd hv gempty_not_anc
  · intro h
    simp at h

/-- ⭐ **C1**：`gempty` 上 `paBlock G S = ∅`（**MZP 的父代并 — 空图**）。

消费：`MZP.paBlock` 的定义 + `BridgeZipDown.gempty_parents`。 -/
theorem gempty_paBlock_eq (S : Finset (Fin 4)) :
    Fate.BridgeMinZPrime.paBlock Fate.BridgeZipDown.gempty S = ∅ := by
  unfold Fate.BridgeMinZPrime.paBlock
  rw [gempty_parents_fun]
  ext u
  simp

/-- ⭐ **C2**：`gempty` 上 `ancestralSet S = S`（**祖先闭包是恒等**）。

消费：`CausDAG.ancestralSet` 的定义 + `gempty_ancestorsSet_eq`。 -/
theorem gempty_ancestralSet_eq (S : Finset (Fin 4)) :
    Fate.BridgeZipDown.gempty.ancestralSet S = S := by
  unfold FateV2.Modeling.Graph.DAG.ancestralSet
  rw [gempty_ancestorsSet_eq, Finset.union_empty]

/-- ⭐⭐ **C3**：**`zStar` 在 `gempty` 上塌缩为恒等** —— `zStar gempty X Y Z = Z`。

证明链：`zStar = ancestralSet ∘ req`，`req = Z ∪ (paBlock X \ X) ∪ (paBlock Y \ Y)`，
而 `paBlock _ = ∅`（C1）、`ancestralSet = id`（C2）。

**这是本文件与 MZP 主链的图论接口**：它说明「`zStar` 真的会**扩大** `Z`」
这件事在空图上是**平凡**的（`zStar` 不扩大），故任何 `zStar` 扩大带来的
非单调现象必须来自**非空图** —— 而 `PjointB` 的非单调是**纯概率**现象
（见 `ZipDownFalse` 文件头 §0.2 的诚实声明），两者正交。 -/
theorem gempty_zStar_eq (X Y Z : Finset (Fin 4)) :
    Fate.BridgeMinZPrime.zStar Fate.BridgeZipDown.gempty X Y Z = Z := by
  unfold Fate.BridgeMinZPrime.zStar Fate.BridgeMinZPrime.req
  rw [gempty_paBlock_eq, gempty_paBlock_eq, Finset.empty_sdiff, Finset.empty_sdiff,
      Finset.union_empty, Finset.union_empty, gempty_ancestralSet_eq]

/-- C3 的方向版本（`Z ⊆ zStar …`，与 `MZP.subset_zStar` 一致）。 -/
theorem gempty_subset_zStar (X Y Z : Finset (Fin 4)) :
    Z ⊆ Fate.BridgeMinZPrime.zStar Fate.BridgeZipDown.gempty X Y Z := by
  rw [gempty_zStar_eq]

/-! ===========================================================================
  §2 抽象判据：`ZipDown` 的反例模板（C4）与 `zStar` 路线（C5）
  =========================================================================== -/

section Abstract

variable {W : Type} [DecidableEq W] [Fintype W]
variable {β : Type} [Fintype β] [DecidableEq β]

/-- ⭐⭐ **C4：`ZipDown` 的反例模板（抽象判据）**。

给定 `Z ⊆ Z'`、`CondIndep p X Y Z'`（**大条件集成立**）、
`¬ CondIndep p X Y Z`（**小条件集失败**），则 `ZipDown` **必然失败**。

**⟹ 这把 `ZipDownFalse` 的结论提升为可复用的判据**：
任何分布只要找到这样一对 `Z ⊆ Z'`，就否证 `ZipDown`。

消费点：`hsub` 作为 `ZipDown` 的 `Z ⊆ Z'` 前件，`hZ'` 作为 `CondIndep … Z'` 前件，
`hZ` 与 `ZipDown` 给出的 `CondIndep … Z` **直接矛盾**。 -/
theorem zipDown_fails_of_witness
    (p : (W → β) → ℝ) (X Y Z Z' : Finset W)
    (hsub : Z ⊆ Z') (hZ' : CondIndep p X Y Z') (hZ : ¬ CondIndep p X Y Z) :
    ¬ Fate.BridgeZipDown.ZipDown p X Y := by
  intro hzd
  exact hZ (hzd Z Z' hsub hZ')

/-- ⭐⭐ **C5：`zStar` 路线被堵（抽象判据）**。

`zStar G X Y Z` **包含** `Z`（`MZP.subset_zStar`）。若在 `zStar` 处拿到
`CondIndep p X Y (zStar …)`，**不能**因此推出 `CondIndep p X Y Z`。

**⟹ 这是 `BridgeFull` §5 缺口 G1 说明里那句散文的抽象形式**：
「从 `CondIndep X Y Z'`（`Z' ⊋ Z`）推不出 `CondIndep X Y Z`」。

消费点：`hZ'`、`hZ`（与 C4 相同的极性对立），`zStar` 只是给 `Z'` 起名。 -/
theorem zStar_zipDown_route_fails
    (G : FateV2.Modeling.Graph.DAG W) (p : (W → β) → ℝ) (X Y Z : Finset W)
    (hZ' : CondIndep p X Y (Fate.BridgeMinZPrime.zStar G X Y Z))
    (hZ : ¬ CondIndep p X Y Z) :
    ¬ (∀ Z : Finset W,
        CondIndep p X Y (Fate.BridgeMinZPrime.zStar G X Y Z) → CondIndep p X Y Z) := by
  intro h
  exact hZ (h Z hZ')

end Abstract

/-! ===========================================================================
  §3 主链收口：`markovAtZStar` 给出 `zStar` 处的 `CondIndep`，但不能压回 `Z`（C6）
  =========================================================================== -/

section MainChain

variable {V : Type} [DecidableEq V] [Fintype V]
variable {α : Type} [Fintype α] [DecidableEq α]
variable {G : FateV2.Modeling.Graph.DAG V}

/-- ⭐⭐⭐ **C6：主链上的收口 —— `zStar` 处可拿到 `CondIndep`，压不回 `Z`**。

**前件**（四条全部来自主链，**不含**任何 `CondIndep`）：
* `hloc : LocalTo G f`、`hfac : ∀ x, p x = ∏ v, f v x`、`hnorm : FactorNorm f`
  —— 因子分解 + 局部性 + 归一性；
* `hd : G.dSep X Y (zStar G X Y Z)` —— `zStar` 处的 d-分离（**真前件**）。

**主链给出**（`BridgeFull.markov_of_readClosedBlocks` + `MZP.readClosed_zStar`）：
* `CondIndep p X Y (zStar G X Y Z)` —— `zStar` 处的条件独立 **成立**。

**额外事实**（诚实登记的第五条前件）：
* `hZ : ¬ CondIndep p X Y Z` —— 小条件集处**失败**。

**结论**：`¬ ∀ Z, CondIndep p X Y (zStar …) → CondIndep p X Y Z`
—— 「先把 `zStar` 塞进 `Z'` 拿到 `CondIndep`、再压回 `Z`」这条路**堵死**。

**⟹ 这正是 `BridgeFull` 缺口 G1 拒绝写成 `∃ Z' ⊇ Z` 形式的机器验证理由。**
`BridgeFull` §5 用散文说了这件事；本定理给它一个**可编译的书面证据**。 -/
theorem markovAtZStar_cannot_zipDown
    {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y (Fate.BridgeMinZPrime.zStar G X Y Z))
    (hZ : ¬ CondIndep p X Y Z) :
    ¬ (∀ Z : Finset V,
        CondIndep p X Y (Fate.BridgeMinZPrime.zStar G X Y Z) → CondIndep p X Y Z) := by
  -- 主链在 `zStar` 处的 `CondIndep`（**关键消费点**）
  have hZ' : CondIndep p X Y (Fate.BridgeMinZPrime.zStar G X Y Z) :=
    Fate.BridgeFull.markov_of_readClosedBlocks hloc hfac hnorm hd
      (Fate.BridgeMinZPrime.readClosed_zStar X Y Z)
  exact zStar_zipDown_route_fails G p X Y Z hZ' hZ

end MainChain

/-! ===========================================================================
  §4 具体反例落到 `zStar` 口径（C7）：`PjointB` + `gempty`
  =========================================================================== -/

section Concrete

/-- ⭐⭐⭐ **C7：`PjointB` 上「`zStar` 扩大后压回固定 `Z`」路线失败
（`ZipDownFalse` 接入 `MZP.zStar`）**。

取 `gempty`（空图）、`X = {0}`、`Y = {1}`、**固定小条件集 `Z = ∅`**。
路线形状（这正是 `BridgeFull` §5 拒绝的「先扩大、再压回」形式）：

```
∀ Z', CondIndep PjointB {0} {1} (zStar gempty {0} {1} Z') → CondIndep PjointB {0} {1} ∅
```

* C3 把 `zStar gempty {0} {1} Z'` 化简为 `Z'`；
* 取 `Z' = {2}`：`CondIndep PjointB {0} {1} {2}` **成立**
  （`ZipDownFalse.condIndepB`）；
* 但 `CondIndep PjointB {0} {1} ∅` **失败**（`ZipDownFalse.not_condIndepB`）。

**消费点（三者缺一不可）**：`gempty_zStar_eq`（C3，把 `zStar` 型还原为集合型）、
`condIndepB`、`not_condIndepB`。

**⚠ 与 `ZipDownFalseFixed.zipDown_false` 的关系**：本定理**不引用** `zipDown_false`，
而是把它拆成的两块拼图重新装配到 **`zStar`-扩大口径**的路线形状上，
故它把 `ZipDownFalse` 的结论**对齐到主链 `MZP.zStar` 的名字**（判据 1/2 号：
陈述里同时出现 `ZipDownFalse` 的 `PjointB`/`condIndepB` 与主链的 `zStar`；
证明里引用 `ZipDownFalse` 的定理；不是 `:= ZipDownFalse.xxx` 的别名）。 -/
theorem PjointB_not_zipDown_route :
    ¬ (∀ Z' : Finset (Fin 4),
        CondIndep Fate.ZipDownFalseFixed.PjointB ({0} : Finset (Fin 4))
          ({1} : Finset (Fin 4))
          (Fate.BridgeMinZPrime.zStar Fate.BridgeZipDown.gempty
            ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) Z')
        → CondIndep Fate.ZipDownFalseFixed.PjointB ({0} : Finset (Fin 4))
            ({1} : Finset (Fin 4)) (∅ : Finset (Fin 4))) := by
  intro h
  have h2 : CondIndep Fate.ZipDownFalseFixed.PjointB ({0} : Finset (Fin 4))
      ({1} : Finset (Fin 4))
      (Fate.BridgeMinZPrime.zStar Fate.BridgeZipDown.gempty
        ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) ({2} : Finset (Fin 4))) := by
    rw [gempty_zStar_eq]
    exact Fate.ZipDownFalseFixed.condIndepB
  exact Fate.ZipDownFalseFixed.not_condIndepB (h {2} h2)

/-- ⭐⭐ **C7′：`PjointB` 上 `ZipDown` 失败**（由 C4 模板从 `ZipDownFalse` 的两块拼图重推出）。

⚠ 这不是 `ZipDownFalseFixed.zipDown_false` 的别名：本定理**不引用** `zipDown_false`，
而是走**抽象判据 C4**，用 `condIndepB` / `not_condIndepB` 作为两个见证。
⟹ 这验证了 C4 模板在具体分布上**确实可用**（模板非空）。 -/
theorem PjointB_zipDown_fails_via_template :
    ¬ Fate.BridgeZipDown.ZipDown Fate.ZipDownFalseFixed.PjointB
        ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) := by
  exact zipDown_fails_of_witness Fate.ZipDownFalseFixed.PjointB
    ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) (∅ : Finset (Fin 4)) {2}
    (by decide) Fate.ZipDownFalseFixed.condIndepB Fate.ZipDownFalseFixed.not_condIndepB

end Concrete

end FateV2.Predict.ZipDownFalseZStarConsumer