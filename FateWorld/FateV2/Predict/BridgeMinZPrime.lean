/-
# `Fate/BridgeMinZPrime` —— `ReadClosedBlocks` 的**最小 `Z' ⊇ Z`**

## 0 结论（**先读这一节**）

`Fate/BridgeFull.lean` 把 `dSep ⟹ CondIndep` 收口成

```
markov_of_gap :  G.dSep X Y Z  +  ReadClosedBlocks G X Y Z  ⟹  CondIndep p X Y Z
```

而 `ReadClosedBlocks G X Y Z`（**`Z' = Z` 版本**）已由
`BridgeFull.exists_dsep_not_readClosed` 证伪。本文件回答：

> **是否存在 `Z' ⊇ Z` 使 `ReadClosedBlocks G X Y Z'` 成立？最小的是谁？**

### 0.1 ⭐ 答案分三层（**不要只读第一层**）

| 层 | 问题 | 答案 | 定理 |
|---|---|---|---|
| **L1** | `Z' ⊇ Z` 使 `ReadClosedBlocks` 成立，存在吗？ | ✅ **恒存在**（无条件，不用 `dSep`） | `exists_readClosed` |
| **L2** | 只是 `ReadClosedBlocks`，**最小**的 `Z'` 是？ | ⭐ `zStar G X Y Z = an_G(req)`，**存在且唯一** | `zStar_minimal` / `existsUnique_min_readClosed` |
| **L3** | 最小 `Z'` 还要求 `dSep X Y Z'`，**还存在吗**？ | 🔴 **不一定**——`gch` 上**一个都没有** | `no_feasible_Z'` ⭐⭐ |

**⟹ 本文件最重要的结论是 L3**：`zStar`（L2 的最小元）**只是 `ReadClosedBlocks` 的最小元**，
它**不保证** `dSep X Y zStar`。把 `Z` 撑大到父闭与 `dSep` 的 `Disjoint X Z` 子句
**可以刚性冲突**：两者可以**同时不可满足**。

### 0.2 ⭐⭐ L3 的机器验证反例（`gch`：链 `0 → 1 → 2`）

取 `X = {0}`、`Y = {2}`、`Z = {1}`：

* `dSep {0} {2} {1}` **成立**（`gch_dsep`，`decide` 判定）——链中点被条件化，路径阻断；
* `req = {1} ∪ (pa{0}\{0}) ∪ (pa{2}\{2}) = {1} ∪ ∅ ∪ {1} = {1}`；
* `zStar = an({1}) = {0,1}`（`gch_zStar`）——**含 `0 ∈ X`**；
* 故 `dSep {0} {2} {0,1}` **失败**（`Disjoint X Z'` 被破坏）；
* 且这**不是** `zStar` 选的不好：**任何**可行的 `Z'` 都含 `0`
  （`pa(2) = {1} ⟹ 1 ∈ Z'` 由 `ReadClosedBlocks`，`Z'` 父闭 ⟹ `0 ∈ Z'`），
  于是 `Disjoint {0} Z'` 恒失败。
* ⟹ **不存在** `Z' ⊇ {1}` 使 `ReadClosedBlocks gch {0} {2} Z' ∧ dSep gch {0} {2} Z'`
  （`no_feasible_Z'`）。

### 0.3 ⭐⭐ 一般障碍（不是这一个图的偶然）

`obstruction_of_no_feasible`：若存在 `u ∈ paBlock G Y \ Y`（`Y` 的父代溢出的点），
且存在 `x ∈ X` 使 `G.isAncestor x u`，则**任何**满足 `ReadClosedBlocks G X Y Z'`
的 `Z'` 都含 `x`（`req` 含 `u`，`Z'` 父闭 ⟹ `u` 的祖先 `x` 也在 `Z'`）。

⟹ 若 `dSep X Y Z` 的 `Disjoint X Z'` 要保住，必须 `x ∉ Z'` —— 冲突。

**⚠ 注意这不直接与 `dSep X Y Z` 矛盾**（`x → … → u → y` 这条有向路径
**可以被 `Z` 中某个点阻断**，正如 `gch` 里 `Z = {1}` 阻断了 `0 → 1 → 2`）。
于是「`dSep X Y Z` 成立」与「不可行」**可以同真**，`gch` 就是见证。

### 0.4 与 `BridgeFull` 的关系 / 仓库状态

`Fate/BridgeFull.lean` 当前第 187 行 `factorizes_standard_implies_routeB` 报
`Application type mismatch`（该引理**为假**：`RouteB.Factorizes` 读 `pa(v)`，
标准 `Factorizes` 读 `{v} ∪ pa(v)`，前者**更松**，推不出更紧的那条）。
故本文件**不 `import FateV2.Predict.BridgeFull`**，而是把 `ReadClosedBlocks` 等定义**逐字复制**
（§1.1），并用 `rfl` 固化口径（`readClosedBlocks_def_eq`）。
**不修改** `BridgeFull`（纪律：不改既有模块）。

### 0.5 纪律核对

* ✅ 单文件验证：`lake env lean Fate/BridgeMinZPrime.lean` 通过。
* ✅ 不改 `Fate.lean`，不改 `BridgeFull` / 任何既有模块。
* ✅ **零 `sorry` / `admit` / `axiom`**。
* ✅ **不用 `mass` 塔性质**（本文件完全不涉及 `mass`、`CondIndep`；
  只做**纯图论**：`Finset` + `parents` + `isAncestor` + `dSep`）。
* ✅ 每个前件的消费点见各定理注释。
================================================================================ -/

import FateWorld.FateV2.Predict.Strategy11AncestralHull
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeMinZPrime

open FateV2.Modeling

open FateV2.Modeling.Graph
open FateV2.Predict.Strategy11Hull

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : FateV2.Modeling.Graph.DAG V}

set_option linter.unusedVariables false

/-!
  # Predict · BridgeMinZPrime

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeMinZPrime.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Strategy11AncestralHull, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 核心定义
  =========================================================================== -/

/-! ## 1.1 被分析的谓词（`Fate/BridgeFull.lean` §1 的**逐字副本**） -/

/-- ⭐⭐⭐ **`ReadClosedBlocks G X Y Z`**：「`X` 块与 `Y` 块在 `Z` 下各自读封闭」。

与 `FateV2.Predict.BridgeFull.ReadClosedBlocks` **逐字相同**，但**独立定义**
（`BridgeFull` 当前不可编译，见文件头 §0.4）。

1. `Z` 父闭（`Z` 上的因子只读 `Z`）；
2. `X` 的每点的父代都在 `X ∪ Z` 内；
3. `Y` 的每点的父代都在 `Y ∪ Z` 内。 -/
def ReadClosedBlocks (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  AncClosed G Z
  ∧ (∀ v ∈ X, G.parents v ⊆ X ∪ Z)
  ∧ (∀ v ∈ Y, G.parents v ⊆ Y ∪ Z)

/-- **口径自检**：本文件 `ReadClosedBlocks` 的定义体与 `BridgeFull` 的**逐字一致**。
（`rfl` 固化，防止下游误以为两者不同。） -/
theorem readClosedBlocks_def_eq (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) :
    ReadClosedBlocks G X Y Z =
      (AncClosed G Z
        ∧ (∀ v ∈ X, G.parents v ⊆ X ∪ Z)
        ∧ (∀ v ∈ Y, G.parents v ⊆ Y ∪ Z)) := rfl

/-! ## 1.2 ⭐ `paBlock` / `req` / `zStar`（本文件的核心构造） -/

/-- ⭐ **`paBlock G S = ⋃_{v∈S} pa_G(v)`**：块 `S` 的**父代并**。

`ReadClosedBlocks` 的第 2/3 条等价于 `paBlock G X ⊆ X ∪ Z`、`paBlock G Y ⊆ Y ∪ Z`，
故 **`paBlock G X \ X` 与 `paBlock G Y \ Y` 必须被 `Z` 吞下**。 -/
def paBlock (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Finset V :=
  S.biUnion (fun v => G.parents v)

/-- `paBlock` 的成员刻画。 -/
theorem mem_paBlock {S : Finset V} {u : V} :
    u ∈ paBlock G S ↔ ∃ v ∈ S, u ∈ G.parents v := by
  unfold paBlock
  rw [Finset.mem_biUnion]

/-- ⭐ **`req`（required part）**：`Z` 加上 `X` / `Y` 两侧「父代越出自身」的部分。

**任何**可行的 `Z'` 必须包含它 —— 见 `req_subset_of_readClosed`。 -/
def req (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Finset V :=
  Z ∪ (paBlock G X \ X) ∪ (paBlock G Y \ Y)

/-- `Z ⊆ req`。 -/
theorem subset_req (X Y Z : Finset V) : Z ⊆ req G X Y Z :=
  fun _ hu => mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hu)))

/-- ⭐⭐⭐ **`zStar G X Y Z`：只论 `ReadClosedBlocks` 时的最小可行 `Z'`**。

即 `req` 的**祖先闭包**：`Z` 加两侧溢出的父代，再把整块父闭化。
（父闭化**必须**：`ReadClosedBlocks` 第 1 条要求 `Z'` 父闭，
故 `Z'` 既含 `req` 又父闭 ⟹ 必含 `req` 的**全部祖先**。） -/
def zStar (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Finset V :=
  G.ancestralSet (req G X Y Z)

/-- `zStar` 的展开（`rfl`）。 -/
theorem zStar_eq (X Y Z : Finset V) :
    zStar G X Y Z = G.ancestralSet (req G X Y Z) := rfl

/-! ## 1.3 祖先闭包的三个工具引理 -/

/-- `S ⊆ an_G(S)`。 -/
theorem subset_ancestralSet (S : Finset V) : S ⊆ G.ancestralSet S :=
  fun _ hu =>
    Finset.mem_union_left _ hu

/-- ⭐ **父闭集含其成员的一切祖先**：`A` 父闭、`T ⊆ A` ⟹ `an_G(T) ⊆ A`。

**消费点**：`zStar_minimal`（`Z'` 父闭 ⟹ `Z'` 含 `req` 的全部祖先）。 -/
theorem ancestralSet_subset_of_ancClosed {T A : Finset V} (hA : AncClosed G A)
    (hTA : T ⊆ A) : G.ancestralSet T ⊆ A := by
  intro u hu
  unfold FateV2.Modeling.Graph.DAG.ancestralSet FateV2.Modeling.Graph.DAG.ancestorsSet at hu
  rcases Finset.mem_union.mp hu with huT | huA
  · exact hTA huT
  · obtain ⟨-, v, hvT, hanc⟩ := Finset.mem_filter.mp huA
    exact FateV2.Modeling.Graph.DAG.isAncestor_mem_of_closed (G := G) hA hanc (hTA hvT)

/-- 祖先闭包单调。 -/
theorem ancestralSet_mono {S T : Finset V} (h : S ⊆ T) :
    G.ancestralSet S ⊆ G.ancestralSet T := by
  intro u hu
  simp only [FateV2.Modeling.Graph.DAG.ancestralSet, FateV2.Modeling.Graph.DAG.ancestorsSet,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with huS | ⟨v, hvS, hanc⟩
  · exact Or.inl (h huS)
  · exact Or.inr ⟨v, h hvS, hanc⟩

/-! ===========================================================================
  §2 ⭐⭐ **L2：`zStar` 是 `ReadClosedBlocks` 的最小可行 `Z'`**
  =========================================================================== -/

/-- `Z ⊆ zStar G X Y Z`。 -/
theorem subset_zStar (X Y Z : Finset V) : Z ⊆ zStar G X Y Z :=
  (subset_req X Y Z).trans (subset_ancestralSet (req G X Y Z))

/-- `zStar` 父闭（`ReadClosedBlocks` 第 1 条）。**消费点**：`blob_ancClosed`。 -/
theorem zStar_ancClosed (X Y Z : Finset V) : AncClosed G (zStar G X Y Z) :=
  blob_ancClosed (req G X Y Z)

/-- `zStar ⊆ Z ⟹ Z` 父闭（`zStar` 的最小性方向要用的**反向**包含）。 -/
theorem ancClosed_of_zStar_subset {X Y Z Z' : Finset V}
    (h : zStar G X Y Z ⊆ Z') : AncClosed G (zStar G X Y Z) :=
  zStar_ancClosed X Y Z

/-- ⭐ `paBlock G X \ X ⊆ zStar`（左侧溢出）。 -/
theorem paBlock_left_sdiff_subset_zStar (X Y Z : Finset V) :
    paBlock G X \ X ⊆ zStar G X Y Z :=
  fun _ hu =>
    subset_ancestralSet _ (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hu))))

/-- ⭐ `paBlock G Y \ Y ⊆ zStar`（右侧溢出）。 -/
theorem paBlock_right_sdiff_subset_zStar (X Y Z : Finset V) :
    paBlock G Y \ Y ⊆ zStar G X Y Z :=
  fun _ hu =>
    subset_ancestralSet _ (mem_union.mpr (Or.inr hu))

/-- ⭐⭐ **`paBlock G X ⊆ X ∪ zStar`**：`X` 侧因子的读集条件。 -/
theorem paBlock_left_subset (X Y Z : Finset V) :
    paBlock G X ⊆ X ∪ zStar G X Y Z := by
  intro u hu
  by_cases huX : u ∈ X
  · exact mem_union.mpr (Or.inl huX)
  · exact mem_union.mpr (Or.inr
      (paBlock_left_sdiff_subset_zStar X Y Z (Finset.mem_sdiff.mpr ⟨hu, huX⟩)))

/-- ⭐⭐ **`paBlock G Y ⊆ Y ∪ zStar`**：`Y` 侧因子的读集条件。 -/
theorem paBlock_right_subset (X Y Z : Finset V) :
    paBlock G Y ⊆ Y ∪ zStar G X Y Z := by
  intro u hu
  by_cases huY : u ∈ Y
  · exact mem_union.mpr (Or.inl huY)
  · exact mem_union.mpr (Or.inr
      (paBlock_right_sdiff_subset_zStar X Y Z (Finset.mem_sdiff.mpr ⟨hu, huY⟩)))

/-- ⭐⭐⭐ **`ReadClosedBlocks` 在 `zStar` 处成立（无条件）**。

**不用 `dSep`、不用任何假设** —— 这是 L1 的见证。
**消费点**：`zStar_ancClosed`（第 1 条）+ `paBlock_left_subset` / `paBlock_right_subset`
（第 2/3 条，经 `mem_paBlock` 展开）。 -/
theorem readClosed_zStar (X Y Z : Finset V) :
    ReadClosedBlocks G X Y (zStar G X Y Z) := by
  refine ⟨zStar_ancClosed X Y Z, ?_, ?_⟩
  · intro v hv u hu
    exact paBlock_left_subset X Y Z (mem_paBlock.mpr ⟨v, hv, hu⟩)
  · intro v hv u hu
    exact paBlock_right_subset X Y Z (mem_paBlock.mpr ⟨v, hv, hu⟩)

/-- ⭐⭐ **`req ⊆ Z'`**：任何可行 `Z' ⊇ Z` 都吞下两侧溢出的父代。

**消费点**（逐条点名）：
* **`hZZ' : Z ⊆ Z'`** → 只用 `req` 的第一个分量 `Z`；
* **`h.2.1`（`X` 侧读集）** → `u ∈ pa(v)`、`v ∈ X`、`u ∉ X` ⟹ `u ∈ X ∪ Z'` 且 `u ∉ X` ⟹ `u ∈ Z'`；
* **`h.2.2`（`Y` 侧读集）** → 对称；
* **`h.1`（`Z'` 父闭）** → 本引理**不用**，留给 `zStar_minimal`。 -/
theorem req_subset_of_readClosed {X Y Z Z' : Finset V} (hZZ' : Z ⊆ Z')
    (h : ReadClosedBlocks G X Y Z') : req G X Y Z ⊆ Z' := by
  obtain ⟨-, hX, hY⟩ := h
  intro u hu
  rcases mem_union.mp hu with hu | hu
  · rcases mem_union.mp hu with huZ | huX
    · exact hZZ' huZ
    · obtain ⟨hpa, hnotX⟩ := Finset.mem_sdiff.mp huX
      obtain ⟨v, hvX, hmem⟩ := mem_paBlock.mp hpa
      rcases mem_union.mp (hX v hvX hmem) with h' | h'
      · exact absurd h' hnotX
      · exact h'
  · obtain ⟨hpa, hnotY⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨v, hvY, hmem⟩ := mem_paBlock.mp hpa
    rcases mem_union.mp (hY v hvY hmem) with h' | h'
    · exact absurd h' hnotY
    · exact h'

/-- ⭐⭐⭐ **`zStar` 的最小性（L2 主定理）**：

任何 `Z' ⊇ Z` 只要满足 `ReadClosedBlocks`，就含 `zStar`。

**消费点**：`req_subset_of_readClosed`（得 `req ⊆ Z'`）+ **`h.1`（`Z'` 父闭）**
经 `ancestralSet_subset_of_ancClosed` ⟹ `an(req) ⊆ Z'`。 -/
theorem zStar_minimal {X Y Z Z' : Finset V} (hZZ' : Z ⊆ Z')
    (h : ReadClosedBlocks G X Y Z') : zStar G X Y Z ⊆ Z' :=
  ancestralSet_subset_of_ancClosed h.1 (req_subset_of_readClosed hZZ' h)

/-- ⭐⭐ **最小可行 `Z'` 存在**（可行性 + 最小性一并在内）。

**条件全空**：`ReadClosedBlocks` 的可行集永不空（含 `zStar`，也含 `univ`）。 -/
theorem exists_min_readClosed (X Y Z : Finset V) :
    ∃ Zs : Finset V,
      Z ⊆ Zs ∧ ReadClosedBlocks G X Y Zs ∧
      (∀ Z' : Finset V, Z ⊆ Z' → ReadClosedBlocks G X Y Z' → Zs ⊆ Z') :=
  ⟨zStar G X Y Z, subset_zStar X Y Z, readClosed_zStar X Y Z,
    fun Z' hZZ' h => zStar_minimal hZZ' h⟩

/-- ⭐⭐ **最小元唯一**：两个「最小可行 `Z'`」相等。

**消费点**：`hmin₁`（配 `h₂`+`hRC₂`）与 `hmin₂`（配 `h₁`+`hRC₁`）互相给出包含，再反称。 -/
theorem min_readClosed_unique {X Y Z Z₁ Z₂ : Finset V}
    (h₁ : Z ⊆ Z₁) (hRC₁ : ReadClosedBlocks G X Y Z₁)
    (hmin₁ : ∀ Z', Z ⊆ Z' → ReadClosedBlocks G X Y Z' → Z₁ ⊆ Z')
    (h₂ : Z ⊆ Z₂) (hRC₂ : ReadClosedBlocks G X Y Z₂)
    (hmin₂ : ∀ Z', Z ⊆ Z' → ReadClosedBlocks G X Y Z' → Z₂ ⊆ Z') :
    Z₁ = Z₂ :=
  Finset.Subset.antisymm (hmin₁ Z₂ h₂ hRC₂) (hmin₂ Z₁ h₁ hRC₁)

/-- ⭐⭐ **`zStar` 是唯一的 `∃!` 型最小元**（打包版）。

**消费点**：存在部分用 `zStar_minimal (subset_zStar …)`；唯一部分用
`hmin` 对 `zStar` 的实例 + `zStar_minimal` 对 `Zs` 的实例。 -/
theorem existsUnique_min_readClosed (X Y Z : Finset V) :
    ∃! Zs : Finset V, Z ⊆ Zs ∧ ReadClosedBlocks G X Y Zs ∧
      (∀ Z' : Finset V, Z ⊆ Z' → ReadClosedBlocks G X Y Z' → Zs ⊆ Z') := by
  refine ⟨zStar G X Y Z, ⟨subset_zStar X Y Z, readClosed_zStar X Y Z,
    fun Z' hZZ' h => zStar_minimal hZZ' h⟩, ?_⟩
  rintro Zs ⟨hsub, hRC, hmin⟩
  exact Finset.Subset.antisymm
    (hmin (zStar G X Y Z) (subset_zStar X Y Z) (readClosed_zStar X Y Z))
    (zStar_minimal hsub hRC)

/-- ⭐⭐ **精确判据**：`Z` 本身可行 **⟺** `zStar` 不增长。

⟹ 「缺口 G1 在 `Z' = Z` 处成立」与「`zStar` 退化为 `Z`」是**同一件事**
（这解释了 `zStar_eq_iff_readClosed` 为何是 `BridgeFull` G1 的最自然形态）。 -/
theorem zStar_eq_iff_readClosed (X Y Z : Finset V) :
    ReadClosedBlocks G X Y Z ↔ zStar G X Y Z = Z := by
  constructor
  · intro h
    exact Finset.Subset.antisymm (zStar_minimal (subset_refl Z) h) (subset_zStar X Y Z)
  · intro h
    rw [← h]
    exact readClosed_zStar X Y Z

/-- ⭐ `zStar` 对 `Z` 单调（**消费点**：`ancestralSet_mono` 喂 `req` 的单调性）。 -/
theorem zStar_mono {X Y : Finset V} {Z₁ Z₂ : Finset V} (h : Z₁ ⊆ Z₂) :
    zStar G X Y Z₁ ⊆ zStar G X Y Z₂ := by
  refine ancestralSet_mono ?_
  intro u hu
  rcases mem_union.mp hu with hu | hu
  · rcases mem_union.mp hu with hu | hu
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (h hu))))
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hu)))
  · exact mem_union.mpr (Or.inr hu)

/-! ===========================================================================
  §3 **L1：`∃ Z' ⊇ Z` 形式的「G1」恒真（故它不是正确的缺口形态）**
  =========================================================================== -/

/-- `BridgeFull` 缺口 G1 的 **`∃ Z' ⊇ Z` 形式**。 -/
def DSepGivesReadClosedBigger (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z →
    ∃ Z' : Finset V, Z ⊆ Z' ∧ ReadClosedBlocks G X Y Z'

/-- ⭐⭐⭐ **存在性版恒真**（**无条件**，甚至不用 `dSep` —— `zStar` 就是见证）。 -/
theorem exists_readClosed (X Y Z : Finset V) :
    ∃ Z' : Finset V, Z ⊆ Z' ∧ ReadClosedBlocks G X Y Z' :=
  ⟨zStar G X Y Z, subset_zStar X Y Z, readClosed_zStar X Y Z⟩

/-- ⭐⭐ **`DSepGivesReadClosedBigger` 对每个 DAG 成立**。

⟹ 只要求 `ReadClosedBlocks`，缺口**消失** —— 这正说明「扩大 `Z'`」**不是**正确的缺口形态（§4）。 -/
theorem dSepGivesReadClosedBigger (G : FateV2.Modeling.Graph.DAG V) :
    DSepGivesReadClosedBigger G :=
  fun X Y Z _ => exists_readClosed X Y Z

/-! ===========================================================================
  §4 ⭐⭐⭐ **L3：还要求 `dSep` 时，最小 `Z'` 可以**根本不存在**
  =========================================================================== -/

/-- **`Z'` 形式的「真正可用」缺口 G1**：

存在 `Z' ⊇ Z`，使得**同一个 `Z'`** 同时满足
* `ReadClosedBlocks G X Y Z'`（桥的前件），且
* `G.dSep X Y Z'`（桥的另一个前件）。

**⚠ 这两个前件在 `markov_of_gap` 里是**同时**被消费的**
（`hd` 分别喂给 `hg` 与 `markov_of_readClosedBlocks`），
所以「扩大 `Z'`」**必须**同时保住两者，否则桥不可用。 -/
def FeasibleReadClosed (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  ∃ Z' : Finset V, Z ⊆ Z' ∧ ReadClosedBlocks G X Y Z' ∧ G.dSep X Y Z'

/-! ### 4.1 反例图 `gch`：链 `0 → 1 → 2` -/

/-- **`gch`：链 `0 → 1 → 2`**（`Z = {1}` 阻断 `0 → 1 → 2`，故 `dSep {0}{2}{1}` 真）。 -/
def gch : FateV2.Modeling.Graph.DAG (Fin 3) where
  edge := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 3,
        Relation.TransGen (fun u v : Fin 3 => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)) x y →
          x < y := by
      intro x y hxy
      induction hxy with
      | single h =>
          rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; decide)
      | tail _ hstep ih =>
          rcases hstep with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; omega)
    exact absurd (key v v hv) (lt_irrefl v)

/-- ⭐ **L3.a**：`gch` 上 `dSep {0} {2} {1}` **成立**（`decide` 判定）。 -/
theorem gch_dsep : gch.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} := by decide

/-- ⭐ **L3.b**：`gch` 上 `pa(2) = {1}`。 -/
theorem gch_pa2 : gch.parents (2 : Fin 3) = {(1 : Fin 3)} := by decide

/-- ⭐ **L3.c**：`gch` 上 `pa(0) = ∅`。 -/
theorem gch_pa0 : gch.parents (0 : Fin 3) = (∅ : Finset (Fin 3)) := by decide

/-- ⭐ **L3.d**：`gch` 上 `req {0} {2} {1} = {1}`。 -/
theorem gch_req : req gch {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} = {(1 : Fin 3)} := by
  decide

/-- ⭐⭐ **L3.e（核心）**：`zStar = {0, 1}` —— **含 `0 ∈ X`**。

⟹ `dSep {0} {2} {0,1}` **必失败**（`dSep` 第一子句要求 `Disjoint X Z`），
即 **L2 的最小元 `zStar` 在 `dSep` 口径下不可用**。 -/
theorem gch_zStar :
    zStar gch {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} = {(0 : Fin 3), (1 : Fin 3)} := by
  decide

/-- ⭐⭐ **L3.f**：`dSep {0} {2} {0,1}` **失败**（`0 ∈ X ∩ Z'`）。 -/
theorem gch_dsep_zStar_false :
    ¬ gch.dSep {(0 : Fin 3)} {(2 : Fin 3)}
        (zStar gch {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)}) := by
  rw [gch_zStar]
  intro hd
  obtain ⟨-, hXZ, -, -⟩ := hd
  exact Finset.disjoint_left.mp hXZ (mem_singleton_self 0) (by simp)

/-- ⭐⭐⭐ **L3.g（关键一般引理）**：**任何**可行的 `Z'` 都含 `0`。

**证明（不靠 `decide`，纯 `ReadClosedBlocks` 的消费）**：
`pa(2) = {1}` 且 `2 ∈ Y` ⟹ 由 `h.2.2`（`Y` 侧读集）`1 ∈ Y ∪ Z' = {2} ∪ Z'` 且 `1 ≠ 2`
⟹ `1 ∈ Z'`；再由 `h.1`（`Z'` 父闭）+ `pa(1) ∋ 0` ⟹ `0 ∈ Z'`。

**⟹ 这一步是 `gch` 上「不可行」的**全部**内容**（`ReadClosedBlocks` 单独就强制 `0 ∈ Z'`）。 -/
theorem gch_feasible_contains_zero (Z' : Finset (Fin 3))
    (h : ReadClosedBlocks gch {(0 : Fin 3)} {(2 : Fin 3)} Z') : (0 : Fin 3) ∈ Z' := by
  obtain ⟨hanc, -, hY⟩ := h
  have h1 : (1 : Fin 3) ∈ Z' := by
    have hmem : (1 : Fin 3) ∈ gch.parents (2 : Fin 3) := by
      rw [gch_pa2]; exact mem_singleton_self 1
    have := hY 2 (mem_singleton_self 2) hmem
    rcases mem_union.mp this with h' | h'
    · simp at h'
    · exact h'
  have hmem0 : (0 : Fin 3) ∈ gch.parents (1 : Fin 3) := by decide
  exact hanc 1 h1 hmem0

/-- ⭐⭐⭐ **L3.h（主结论）**：`gch` 上**不存在**可行的 `Z' ⊇ {1}`。

**`dSep` 的第一个前件 `Disjoint X Z'`** 与 **`ReadClosedBlocks`** 在 `gch` 上**矛盾**：
前者要求 `0 ∉ Z'`，后者强制 `0 ∈ Z'`。

⟹ **「最小 `Z'`」在同时要求 `dSep` 时**不一定存在**——这不是「最小元难算」，
而是**可行集为空**。** 故本文件对用户问题的最终回答是：
**能给出最小元（`zStar`），但只在忽略 `dSep` 时才可用；桥真正需要的形式没有最小元。** -/
theorem no_feasible_Z' :
    ¬ FeasibleReadClosed gch {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} := by
  rintro ⟨Z', -, hRC, hd⟩
  obtain ⟨-, hXZ, -, -⟩ := hd
  have h0Z : (0 : Fin 3) ∈ Z' := gch_feasible_contains_zero Z' hRC
  exact Finset.disjoint_left.mp hXZ (mem_singleton_self 0) h0Z

/-- ⭐⭐ **L3.i**：`zStar` 本身在 `gch` 上仍**满足** `ReadClosedBlocks`
（与 `gch_dsep_zStar_false` 并读：`zStar` 是 `ReadClosedBlocks` 的最小元，
但**不是** `FeasibleReadClosed` 的元素）。

（`readClosed_zStar` 的无条件实例，此处显式写下以形成**对照**。） -/
theorem gch_zStar_readClosed :
    ReadClosedBlocks gch {(0 : Fin 3)} {(2 : Fin 3)}
      (zStar gch {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)}) :=
  readClosed_zStar _ _ _

/-! ===========================================================================
  §5 ⭐⭐ **一般障碍：`Y` 的溢出父代若是 `X` 的后代，就必撞 `Disjoint X Z'`**
  =========================================================================== -/

/-- ⭐⭐⭐ **`obstruction_of_descendant_parent`（一般图论定理）**：

若
* `hRC : ReadClosedBlocks G X Y Z'`（`Z'` 可行），
* `u ∈ paBlock G Y \ Y`（`Y` 的**溢出**父代：`y ∈ Y` 有父 `u ∉ Y`），
* `x ∈ X` 且 `x` 是 `u` 的**祖先**（`G.isAncestor x u`），

则 `x ∈ Z'`。

**证明（逐前件消费）**：
* `hRC.2.2`（`Y` 侧读集）+ `u ∈ pa(y)`、`y ∈ Y`、`u ∉ Y` ⟹ `u ∈ Z'`；
* `hRC.1`（`Z'` 父闭）`+ G.isAncestor x u` ⟹ `x ∈ Z'`（`isAncestor_mem_of_closed`）。

**⟹ 推论（`obstruction_no_feasible`）**：若还要求 `dSep X Y Z'`，
则 `Disjoint X Z'` 要求 `x ∉ Z'` ⟹ **矛盾** ⟹ `Z'` 不存在。 -/
theorem obstruction_of_descendant_parent {X Y Z' : Finset V} {u x : V}
    (hRC : ReadClosedBlocks G X Y Z') (hu : u ∈ paBlock G Y \ Y)
    (hx : x ∈ X) (hanc : G.isAncestor x u) : x ∈ Z' := by
  obtain ⟨hanc', -, hY⟩ := hRC
  obtain ⟨hpa, hnotY⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨y, hyY, hmem⟩ := mem_paBlock.mp hpa
  have huZ : u ∈ Z' := by
    rcases mem_union.mp (hY y hyY hmem) with h' | h'
    · exact absurd h' hnotY
    · exact h'
  exact FateV2.Modeling.Graph.DAG.isAncestor_mem_of_closed (G := G) hanc' hanc huZ

/-- ⭐⭐⭐ **`obstruction_no_feasible`（一般障碍的正确形态）**：

若存在 `Y` 的溢出父代 `u` 与 `x ∈ X` 使 `x` 是 `u` 的祖先，
则**任何** `Z'` **不能**同时满足 `ReadClosedBlocks G X Y Z'` 与 `dSep X Y Z'`。

**⟹ 这不是 `gch` 的偶发，而是**结构性**的：
「把 `Z` 撑到父闭」与「`Z ∩ X = ∅`」在**有向路径 `x → … → u → y` 被 `Z` 阻断**
的场合会**刚性冲突**。 -/
theorem obstruction_no_feasible {X Y Z' : Finset V} {u x : V}
    (hRC : ReadClosedBlocks G X Y Z') (hu : u ∈ paBlock G Y \ Y)
    (hx : x ∈ X) (hanc : G.isAncestor x u) : ¬ G.dSep X Y Z' := by
  intro hd
  obtain ⟨-, hXZ, -, -⟩ := hd
  exact Finset.disjoint_left.mp hXZ hx
    (obstruction_of_descendant_parent hRC hu hx hanc)

/-! ===========================================================================
  §6 交付清单与纪律核对
  =========================================================================== -/

/-
| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| L1 | `exists_readClosed` | `∃ Z' ⊇ Z` 使 `ReadClosedBlocks`（**无条件**） | ✅ 真证明 |
| L1 | `dSepGivesReadClosedBigger` | `∃ Z'` 形式 G1 对**每个** DAG 成立 | ✅ 真证明 |
| L2 | `readClosed_zStar` | `zStar` **总满足** `ReadClosedBlocks` | ✅ 真证明 |
| L2 | `zStar_minimal` | 最小性：任何可行 `Z' ⊇ Z` 含 `zStar` | ✅ 真证明 |
| L2 | `existsUnique_min_readClosed` | 最小元 `∃!` | ✅ 真证明 |
| L2 | `min_readClosed_unique` | 最小元唯一 | ✅ 真证明 |
| L2 | `zStar_eq_iff_readClosed` | `ReadClosedBlocks G X Y Z ↔ zStar = Z` | ✅ 真证明 |
| L2 | `zStar_mono` | `zStar` 对 `Z` 单调 | ✅ 真证明 |
| L3 | `gch_dsep` | 反例图：`dSep {0}{2}{1}` 真 | ✅ `decide` |
| L3 | `gch_zStar` | `zStar = {0,1} ∋ 0` | ✅ `decide` |
| L3 | `gch_dsep_zStar_false` | `dSep {0}{2}{zStar}` **假** | ✅ 真证明 |
| L3 | `gch_feasible_contains_zero` | **任何**可行 `Z'` 含 `0` | ✅ 真证明 |
| L3 | ⭐ `no_feasible_Z'` | `gch` 上**不存在** `ReadClosedBlocks ∧ dSep` 的 `Z'` | ✅ 真证明 |
| L3 | `gch_zStar_readClosed` | `zStar` 仍满足 `ReadClosedBlocks`（对照） | ✅ 真证明 |
| §5 | ⭐ `obstruction_of_descendant_parent` | 一般障碍：`Y` 溢出父代的 `X`-祖先必进 `Z'` | ✅ 真证明 |
| §5 | ⭐ `obstruction_no_feasible` | 一般障碍：此时 `dSep X Y Z'` 不可能 | ✅ 真证明 |

**最终结论（对用户问题）**：

1. **`ReadClosedBlocks` 单独看**：`zStar G X Y Z = an_G(Z ∪ (paBlock X \ X) ∪ (paBlock Y \ Y))`
   **总是**是最小可行 `Z' ⊇ Z`，**存在且唯一**（`existsUnique_min_readClosed`）。
2. **但 `zStar` 不保证 `dSep X Y zStar`**（`gch_dsep_zStar_false`）；
   且**没有任何 `Z'`** 能同时满足两者（`no_feasible_Z'`）。
3. **⟹ 桥 `markov_of_gap` 需要的「`Z'`」形式不存在最小元——可行集可以**为空**。**
   故 `BridgeFull` 的诚实结论（缺口在 `Z' = Z` 口径下为假、且不能被 `Z'` 撑大救回）
   在本文件中得到**完整的机器验证加强**：不是「最小元难求」，而是**根本没有可行元**。

纪律核对：

1. ✅ 单文件验证：`lake env lean Fate/BridgeMinZPrime.lean` **通过**（见 §0.5）。
2. ✅ 不改 `Fate.lean`；不改 `BridgeFull` / `BridgeThreeNode` / 任何既有模块
   （`ReadClosedBlocks` 等定义**逐字复制**，见 `readClosedBlocks_def_eq`）。
3. ✅ **零 `sorry` / `admit` / `axiom`**（`grep` 为空）。
4. ✅ **不用 `mass` 塔性质**：本文件**完全不涉及** `mass` / `CondIndep`，
   只做**纯图论**（`Finset` + `parents` + `isAncestor` + `dSep`）。
   故「不用 mass 塔」自动满足。
5. ✅ **真假证区分 / 前件消费点**：
   * `subset_zStar` / `readClosed_zStar`：无前件（无条件）；
   * `zStar_minimal`：消费 `hZZ'`（`Z ⊆ Z'`）、`h.1`（`Z'` 父闭）、`h.2.1`/`h.2.2`（两侧读集）；
   * `zStar_eq_iff_readClosed`：消费 `zStar_minimal` + `subset_zStar`；
   * `gch_feasible_contains_zero`：消费 `h.2.2`（`Y` 读集）+ `h.1`（父闭）；
   * `no_feasible_Z'`：消费 `gch_feasible_contains_zero` + **`dSep` 的**第一**子句 `Disjoint X Z'`**；
   * `obstruction_no_feasible`：同结构的一般化。
   **`dSep` 的**第 4 子句（Bayes-ball）在本文件中**从未被消费**——
   这是**诚实标注**：本文件只研究 `ReadClosedBlocks` 的 `Z'` 最小化，不涉及
   `dSep` 的阻断语义对概率结论的作用（那是 `BridgeFull` 的 `hRC` 承担的内容）。
-/

end FateV2.Predict.BridgeMinZPrime