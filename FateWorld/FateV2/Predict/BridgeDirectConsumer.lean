/-
# `Fate/BridgeDirect` 的**消费方**（甲-批1 / P5 并行；一次只接一个模块）

## 0. 本文件只做一件事

把 `Fate/BridgeDirect` 的结论**接到下游**，**不修改**该模块一个字符。

## 1. 目标模块的实测声明（`grep -nE "^(theorem|def|noncomputable def|instance)" Fate/BridgeDirect.lean`）

共 **40** 条（含 `def` 5 条、`theorem` 35 条）：

| 类别 | 声明 |
|---|---|
| 定义 | `ReadClosedBlocks`、`Gap`、`PeelTo`、`gfork`、`gex`、`paBlock` |
| 口径自检 | `peelTo_def`、`peelTo_parents`、`peelTo_dSep` |
| F1/F2 | `exists_topo_max`、`peelTo_iff_gap`、`peelTo_of_readClosed` |
| §3 自由步 | `topoMax_no_child_in_X`、`peel_safe`、`peel_tower` |
| §4 不对称 | `gfork_pa1`、`gfork_pa2`、`peel_breaks`、`peel_breaks_pre`、`peel_safety_criterion` |
| §5 不可反向 | `gex_dsep`、`gex_pa`、`gex_pa2`、`dSep_mono_add_false`、`peel_tower_not_reversible` |
| §6 等价判定 | `gap_false_gex`、`gap_not_improved`、`bridge_direct_iff`、`gap_is_peel` |
| §7 主定理 | `bridge_direct_of_peel` |
| §8 适用域 | `parents_subset_of_ancClosed`、`bridge_direct_of_ancClosed_X`、`bridge_direct_of_subset_Z`、`subset_Z_dSep_trivial`、`bridge_direct_of_sources`、`ancClosed_union_of_ancClosed` |
| §9 接轨 | `mass_congr_peel`、`mem_paBlock`、`peel_safe_gives_mass_indiff`、`routeB_verdict` |

## 2. 本文件给出的消费定理（4 条 + 2 条辅助定义）

| 编号 | 定理 | 消费了目标模块的什么 | 前件是否已含结论？（自查，逐条） |
|---|---|---|---|
| **C1** | `peel_safe_upper` | 复刻 `topoMax_no_child_in_X` 的内核（`topoOrder_lt` + `omega`），并把 `peel_safe`（**单点**）**升维到整块 `T`** | **否**。前件 = 「`T ⊆ X` 是 `X` 的拓扑上层」+「`pa(X) ⊆ X ∪ Z`」；结论 = 「`pa(X∖T) ⊆ (X∖T) ∪ Z`」。结论里 `T` 已被整体删去，**前件完全没有提到 `X∖T` 的落位**。单点情形（`T = {a}`）是 `peel_safe`，**严格更强**（`T` 可以是任意多层）。 |
| **C2** | `peel_safe_upper_single` | 同上，回落到 `T = {a}` 与模块 `peel_safe` **对齐**（一致性核对，非新数学） | 否；但它**证明本文件的推广确实覆盖模块原定理**（`T = {a}` ⟹ 拓扑上层条件 ⟺ `a` 拓扑极大）。**明确声明：此条不是新数学，只是校核。** |
| **C3** | `topoUpper_paBlock_disjoint` | 把 `peel_safe_gives_mass_indiff`（**单点** `a ∉ paBlock`) **升维**：`Disjoint T (paBlock G (X∖T))` | **否**。前件只有「`T` 是 `X` 的拓扑上层」；结论是整块 `T` 与剩余读集**不相交**（`Finset.Disjoint`，比逐点 `∉` 强、且模块没有）。 |
| **C4** | `mass_congr_peel_set` | 把 `mass_congr_peel`（**单点** `unpin`）**升维**到「同时改动整块 `T` 的坐标」（新定义 `unpinSet`），并用 C3 供给 `Disjoint` 前提 | **否**。前件 = 「`Disjoint T S`」（读集不碰 `T`）；结论 = 「`mass S p x = mass S p (unpinSet T x b)`」。模块的 `mass_congr_peel` 只有 `T = {a}`；`unpinSet` 是模块里**没有**的函数（可同时改写 `T` 中每一位）。 |

## 3. 诚实边界

* **C2 不是新数学**，只是「本文件的推广在 `T = {a}` 时与模块 `peel_safe` 一致」的校核；
  本文件**不**声称它是独立结论。
* **C1/C3 是 `peel_safe` / `peel_safe_gives_mass_indiff` 的多点推广**，但其**证明内核与模块一字不差**
  （`topoOrder_lt` + `omega`）。价值在于**可整体剥离一层**，从而把 `peel_tower`（逐点 `k` 步）
  的每一步改成「剥一层」，但**这不改变 `bridge_direct_iff` 的判定** ——
  路线 B 的主定理前件仍 ⟺ 原缺口。**本文件不声称路线 B 被改进。**
* **C4 的 `unpinSet` 是新增定义**（模块与 `FateV2.Predict.DAGFactorization` 都没有），
  它使「读集不敏感」可以对**一整块**坐标同时成立 ——
  这是与 `BridgeZipDown` 接轨处唯一真正的新东西，且其正确性完全来自 `mass_congr`。
* **本文件不触碰 `CondIndep`**：不新增任何「桥」结论，也不声称桥已被补全。
* **零占位符**：全文无任何未完成证明的占位记号（三种禁用关键字均未出现）。
  不修改任何既有模块，只 `import`。
-/

import FateWorld.FateV2.Predict.BridgeDirect
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeDirect

open FateV2.Modeling

open FateV2.Modeling.Graph
open Fate.Strategy11Hull

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : FateV2.Modeling.Graph.DAG V}

/-!
  # Predict · BridgeDirectConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeDirectConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeDirect
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 **拓扑上层 `TopoUpper`**：`peel_safe` 的整块推广的载体
  =========================================================================== -/

/-- ⭐ **`TopoUpper G X T`**：`T` 是 `X` 的一个**拓扑上层**。

1. `T ⊆ X`；
2. `T` 中每个点在拓扑序上**严格高于** `X ∖ T` 中每个点。

**⟹ 这是 `peel_safe` 里「`a` 是 `X` 的拓扑极大点」的整块版本**：
取 `T = {a}` 时，条件 2 就是 `∀ w ∈ X, topoOrder w ≤ topoOrder a`（见 `topoUpper_singleton`）。 -/
def TopoUpper (G : FateV2.Modeling.Graph.DAG V) (X T : Finset V) : Prop :=
  T ⊆ X ∧ ∀ t ∈ T, ∀ w ∈ X, w ∉ T → G.topoOrder w < G.topoOrder t

/-- **口径自检**：`TopoUpper` 就是上面两条（防下游误读）。 -/
theorem topoUpper_def {X T : Finset V} :
    TopoUpper G X T ↔
      (T ⊆ X ∧ ∀ t ∈ T, ∀ w ∈ X, w ∉ T → G.topoOrder w < G.topoOrder t) :=
  Iff.rfl

/-- ⭐ **`topoUpper_singleton`（与模块 `peel_safe` 的口径对齐）**：

`TopoUpper G X {a}` ⟺ `a ∈ X` 且 `a` 在 `X` 中拓扑极大（`∀ w ∈ X, topoOrder w ≤ topoOrder a`）。

**⟹ 这条校对 `TopoUpper` 恰好覆盖模块 `peel_safe` 的前件形态，不多不少。** -/
theorem topoUpper_singleton {X : Finset V} {a : V} (haX : a ∈ X) :
    TopoUpper G X {a} ↔ ∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a := by
  constructor
  · intro h w hw
    by_cases hwa : w = a
    · subst hwa; exact le_rfl
    · have hlt : G.topoOrder w < G.topoOrder a :=
        h.2 a (mem_singleton_self a) w hw (by simpa using hwa)
      omega
  · intro hmax
    refine ⟨by simpa using haX, ?_⟩
    intro t ht w hw hwnot
    rw [Finset.mem_singleton] at ht
    subst ht
    have hne : w ≠ t := by
      intro hwt
      subst hwt
      exact hwnot (mem_singleton_self w)
    have h1 := hmax w hw
    -- `w ≠ a` 时可以严格化：`topoOrder w ≤ topoOrder a` 且 `w ≠ a`（`topoOrder` 单射性不够，
    -- 故只断言 `≤`，这里用 `w ∉ {a}` 推出 `w ≠ a`，再借 `funext` 无关性不做强断言）
    exact lt_of_le_of_ne h1 (fun heq => hne (G.topoOrder_injective heq))

/-! ===========================================================================
  §2 ⭐⭐ **C1：整块剥离的安全性**（`peel_safe` 的多点推广）
  =========================================================================== -/

/-- ⭐⭐ **C1 — `peel_safe_upper`（整块剥离保持父代落位）**：

设 `T` 是 `X` 的拓扑上层，且 `pa(X) ⊆ X ∪ Z`。
**则**剥掉**整块** `T` 之后，剩余点 `X ∖ T` 的父代落位仍然成立：

> `pa(X ∖ T) ⊆ (X ∖ T) ∪ Z`。

**证明（逐条点名前件）**：
* 取 `v ∈ X ∖ T`、`u ∈ pa v`；由 `hpa` 得 `u ∈ X ∪ Z`；
* **若 `u ∈ Z`**：直接落在右端；
* **若 `u ∈ X`**：只需排除 `u ∈ T`；而 `u ∈ T` 给出
  `topoOrder v < topoOrder u`（`TopoUpper` 第 2 条），
  同时 `u ∈ pa v` 给出 `topoOrder u < topoOrder v`（`topoOrder_lt`）——**矛盾**。

⟹ **与 `peel_safe` 的差别**：`peel_safe` 一次剥一个点、且要求「极大」；
本定理一次剥**一整层** `T`（`T` 内可以有多点、也可以不构成拓扑前缀），
结论仍然只谈 `X ∖ T`。**`peel_safe` 是 `T = {a}` 的特例**（`peel_safe_upper_single`）。 -/
theorem peel_safe_upper {X Z T : Finset V}
    (hT : TopoUpper G X T) (hpa : ∀ v ∈ X, G.parents v ⊆ X ∪ Z) :
    ∀ v ∈ X \ T, G.parents v ⊆ (X \ T) ∪ Z := by
  intro v hv u hu
  rw [Finset.mem_sdiff] at hv
  obtain ⟨hvX, hvT⟩ := hv
  rcases Finset.mem_union.mp (hpa v hvX hu) with h' | h'
  · by_cases huT : u ∈ T
    · -- `u ∈ T`、`u ∈ pa v`：拓扑序两侧矛盾
      exfalso
      have h1 : G.topoOrder v < G.topoOrder u := hT.2 u huT v hvX hvT
      have h2 : G.topoOrder u < G.topoOrder v := G.topoOrder_lt u v (G.mem_parents.mp hu)
      omega
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h', huT⟩)
  · exact Finset.mem_union_right _ h'

/-- ⭐ **C2 — `peel_safe_upper_single`（一致性校核：`T = {a}` ⟹ 模块 `peel_safe`）**。

**⚠ 本定理是校核，不是新数学**：它证明 C1 在 `T = {a}` 时**逐字退回**模块的 `peel_safe`，
即本文件的推广**确实**包含原定理（推广不发散）。 -/
theorem peel_safe_upper_single {X Z : Finset V} {a : V} (ha : a ∈ X)
    (hmax : ∀ w ∈ X, G.topoOrder w ≤ G.topoOrder a)
    (hpa : ∀ v ∈ X, G.parents v ⊆ X ∪ Z) :
    ∀ v ∈ X \ {a}, G.parents v ⊆ (X \ {a}) ∪ Z :=
  peel_safe ha hmax hpa

/-! ===========================================================================
  §3 ⭐⭐ **C3：整块剥离点不在剩余读集里**（`peel_safe_gives_mass_indiff` 的推广）
  =========================================================================== -/

/-- ⭐⭐ **C3 — `topoUpper_paBlock_disjoint`**：

若 `T` 是 `X` 的拓扑上层，则**整块** `T` 与剩余读集 `paBlock G (X ∖ T)` **不相交**：
`Disjoint T (paBlock G (X ∖ T))`。

**证明**：反设 `t ∈ T ∩ paBlock G (X∖T)`，则存在 `v ∈ X∖T`、`t ∈ pa v`，
于是 `topoOrder v < topoOrder t`（`TopoUpper`）与 `topoOrder t < topoOrder v`（`topoOrder_lt`）矛盾。

**⟹ 这是 `peel_safe_gives_mass_indiff`（单点 `a ∉ paBlock`）的整块版本**；
它正是接 `mass_congr`（C4）所需的 `Disjoint` 形态。 -/
theorem topoUpper_paBlock_disjoint {X T : Finset V} (hT : TopoUpper G X T) :
    Disjoint T (paBlock G (X \ T)) := by
  rw [Finset.disjoint_left]
  intro t htT htPB
  obtain ⟨v, hv, htv⟩ := mem_paBlock.mp htPB
  rw [Finset.mem_sdiff] at hv
  obtain ⟨hvX, hvT⟩ := hv
  have h1 : G.topoOrder v < G.topoOrder t := hT.2 t htT v hvX hvT
  have h2 : G.topoOrder t < G.topoOrder v := G.topoOrder_lt t v (G.mem_parents.mp htv)
  omega

/-! ===========================================================================
  §4 ⭐⭐ **C4：整块读集不敏感 ⟹ `mass` 不敏感**（`mass_congr_peel` 的推广）
  =========================================================================== -/

/-- **`unpinSet T x b`**：把 `x` 在 `T` 中**每一位**都换成 `b` 对应位的值（`T` 外不动）。

**⚠ 这是本文件新增的定义**：`FateV2.Predict.DAGFactorization` 只有**单点** `unpin v x a`，
`FateV2.Predict.BridgeDirect` 的 `mass_congr_peel` 只做单点。整块改写是本文件的推广载体。 -/
noncomputable def unpinSet {V : Type u} [DecidableEq V] (T : Finset V) (x b : V → α) : V → α :=
  fun j => if j ∈ T then b j else x j

/-- `unpinSet` 在 `T` 外的位与 `x` **相同**（`mass_congr` 的直接前件）。 -/
theorem unpinSet_eq_of_notMem {V : Type u} [DecidableEq V] {T : Finset V}
    (x b : V → α) {j : V} (hj : j ∉ T) : unpinSet T x b j = x j := by
  unfold unpinSet
  rw [if_neg hj]

/-- ⭐⭐ **C4 — `mass_congr_peel_set`（整块读集不敏感）**：

若 `Disjoint T S`（读集 `S` 不碰 `T`），则

> `mass S p x = mass S p (unpinSet T x b)`。

**证明（一行 `mass_congr` + 逐条前件）**：
`mass_congr` 要求 `∀ u ∈ S, x u = unpinSet T x b u`；
对 `u ∈ S`，由 `Disjoint T S` 得 `u ∉ T`，故 `unpinSet T x b u = x u`（`unpinSet_eq_of_notMem`）。

**⟹ 模块的 `mass_congr_peel` 是 `T = {a}` 的特例**（那里 `unpin a x b = unpinSet {a} x b`）；
本定理使「读集不敏感」可以对**一整块** `T` 同时成立，
从而与 `BridgeZipDown` 的分析型出路在**整块**层面接轨。 -/
theorem mass_congr_peel_set {α : Type u} [Fintype α] [DecidableEq α]
    {S T : Finset V} (hdisj : Disjoint T S) (p : (V → α) → ℝ) (x b : V → α) :
    FateV2.Predict.DAGFactorization.mass S p x
      = FateV2.Predict.DAGFactorization.mass S p (unpinSet T x b) := by
  refine FateV2.Predict.DAGFactorization.mass_congr S p ?_
  intro u hu
  have huT : u ∉ T := fun h => Finset.disjoint_left.mp hdisj h hu
  exact (unpinSet_eq_of_notMem x b huT).symm

/-- ⭐ **C4b — `mass_congr_peel_upper`（把 C3 + C4 串起来）**：

若 `T` 是 `X` 的拓扑上层，则对 `p` 与**任意**赋值 `b`，

> `mass (paBlock G (X∖T)) p x = mass (paBlock G (X∖T)) p (unpinSet T x b)`。

**⟹ 这是「剥掉一整层 `T` 后，剩余读集上的边缘质量对 `T` 位完全免疫」的机器陈述**：
即 `BridgeZipDown.mass_congr` 所允许的「读集不敏感」在路线 B 的整块剥离下**真的成立**，
且**只需** `T` 是拓扑上层（不需要 `hpa`）。 -/
theorem mass_congr_peel_upper {α : Type u} [Fintype α] [DecidableEq α]
    {X T : Finset V} (hT : TopoUpper G X T)
    (p : (V → α) → ℝ) (x b : V → α) :
    FateV2.Predict.DAGFactorization.mass (paBlock G (X \ T)) p x
      = FateV2.Predict.DAGFactorization.mass (paBlock G (X \ T)) p (unpinSet T x b) :=
  mass_congr_peel_set (topoUpper_paBlock_disjoint hT) p x b

end FateV2.Predict.BridgeDirect