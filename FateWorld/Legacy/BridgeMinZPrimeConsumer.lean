/-
# `Fate/BridgeMinZPrimeConsumer` —— 把 `BridgeMinZPrime` 的 `zStar` 接到 `BridgeFull` 主链

## 0 本文件做什么（**先读这一节**）

`Fate/BridgeMinZPrime.lean`（下称 **MZP**）独立地（在自己的 namespace `Fate.BridgeMinZPrime`
里）把 `ReadClosedBlocks` / `paBlock` / `req` / `zStar` **逐字复制**了一遍，
理由写在 MZP 文件头 §0.4：**当时** `Fate/BridgeFull.lean` 因
`factorizes_standard_implies_routeB` 报 `Application type mismatch` 而**不编译**，
所以 MZP **不 import `BridgeFull`**。

**现状（本文件实测）**：`lake env lean Fate/BridgeFull.lean` **EXIT=0** ——
`BridgeFull` 已经能编译，`markov_of_readClosedBlocks` / `markov_of_gap` 都在。
于是 MZP 的「绕开」理由**已经过期**，而两者之间的**重复定义**就成了
「同一谓词的两份拷贝，各自证了一堆引理，但从未对接」。

本文件就是**这两份拷贝的对接证**。**不改任何既有模块**（纪律 2），只新建本文件。

## 1 本文件的 5 条结果

| # | 名称 | 内容 | 消费点 |
|---|---|---|---|
| C1 | `readClosedBlocks_iff` | `MZP.ReadClosedBlocks G X Y Z ↔ BridgeFull.ReadClosedBlocks G X Y Z` | 两者定义体**逐字相同**，`unfold` 即得 |
| C2 | `zStar_minimal_full` | MZP 的 `zStar` 最小性 **移植到 `BridgeFull.ReadClosedBlocks`** | `MZP.zStar_minimal` + C1 |
| C3 | ⭐ `existsUnique_min_readClosed_full` | `BridgeFull.ReadClosedBlocks` 口径下**最小可行 `Z'` 存在且唯一**，且就是 `zStar` | C1 + `MZP.existsUnique_min_readClosed` |
| C4 | ⭐⭐ `markov_at_zStar` | **收口**：`LocalTo + Factorizes + FactorNorm + dSep X Y (zStar …) ⟹ CondIndep p X Y (zStar …)` | `BridgeFull.markov_of_readClosedBlocks` + `MZP.readClosed_zStar` |
| C5 | ⭐⭐ `not_dSepGivesReadClosed_gch` | **缺口 G1 在 `gch` 上假**：`¬ BridgeFull.DSepGivesReadClosed gch` | `MZP.gch_dsep` + `MZP.gch_zStar` + `MZP.zStar_eq_iff_readClosed` |

## 2 ⚠ 诚实边界（**必须读**）

* **本文件不证明「`dSep ⟹ CondIndep` 无条件成立」**。恰恰相反：
  **C5 机器验证了 `BridgeFull` 的缺口 `DSepGivesReadClosed` 在 `gch` 上为假**
  （MZP 的 `no_feasible_Z'` 已证 `gch` 上连**存在性**形式都不成立，C5 是它在
  `BridgeFull` 的 `def` 口径上的直接落点）。
* **C4 是条件版**：它的 `hd : G.dSep X Y (zStar G X Y Z)` 是**真前件**，不是自动成立。
  MZP 的 `gch_dsep_zStar_false` 已证它**可以失败**。故 C4 **不是**「无条件收口」。
* MZP 文件头 §0.4 说「`BridgeFull` 当前不可编译」——**本文件不改 MZP**（纪律 2），
  但在此**如实标注该陈述已过期**（实测 `BridgeFull` EXIT=0）。
  这正是本文件存在的意义：**用对接证替代「绕开」**。

## 3 真假证 / 前件消费点逐条核对（纪律 7：不许同义反复）

* `readClosedBlocks_iff`：**无前件**，两边都是 `def` 展开 ⟹ 不是同义反复（是两个**独立**定义的相等性）。
* `zStar_minimal_full`：前件 `hZZ' : Z ⊆ Z'` 与 `h : BridgeFull.ReadClosedBlocks G X Y Z'`
  **都不含结论 `zStar ⊆ Z'`**；结论由 `MZP.zStar_minimal` 的**父闭 + 两侧读集消费**得到。
* `existsUnique_min_readClosed_full`：结论是 `∃!`，前件**空**。不可能是同义反复。
* `markov_at_zStar`：结论 `CondIndep p X Y (zStar …)`，前件 `hloc/hfac/hnorm/hd`
  **一个都不是** `CondIndep`。`hd` 与 `readClosed_zStar` 是**两个不同**的前件
  （前者 `dSep`、后者 `ReadClosedBlocks`），在 `markov_of_readClosedBlocks` 里**分别**被消费。
* `not_dSepGivesReadClosed_gch`：结论是**否定**，前件是 MZP 已证的**具体事实**
  （`gch_dsep`、`gch_zStar` 都是 `decide` 出来的）。非同义反复。

## 4 纪律核对

* ✅ 不改 `Fate.lean` 以外的任何既有文件（本文件只新增；`Fate.lean` 只加一行 import）。
* ✅ **零 `sorry` / `admit` / `axiom`**。
* ✅ 单文件验证：`lake env lean Fate/BridgeMinZPrimeConsumer.lean` 通过（见交付报告）。
* ✅ 不涉及 `mass` 塔性质；C4 的 `mass` 消费全在 `BridgeFull` / `Strategy11Hull` 内。
================================================================================ -/

import FateWorld.Legacy.BridgeMinZPrime
import FateWorld.Legacy.BridgeFull
import Mathlib.Tactic

open Finset
namespace Fate.BridgeMinZPrimeConsumer

open Causalean.Graph
open Fate.Strategy11Hull
open Fate.BridgeMinZPrime

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : Causalean.Graph.DAG V}

/-! ===========================================================================
  §1 **两份 `ReadClosedBlocks` 是同一个谓词**（C1）
  =========================================================================== -/

/-- ⭐ **C1**：`Fate.BridgeMinZPrime.ReadClosedBlocks` 与
`Fate.BridgeFull.ReadClosedBlocks` **逐字相同**（两个独立定义，`unfold` 后同形）。

**意义**：MZP 关于 `ReadClosedBlocks` 的全部结论（`zStar_minimal`、`req_subset_of_readClosed`、
`readClosed_zStar` ……）可以**无条件**搬到 `BridgeFull` 的口径上，
反之亦然。这是 §2–§4 全部定理的**唯一**桥梁。

**不是同义反复**：两边是**各自独立** `def` 出来的 `Prop`（分别写在两个模块里），
本定理证明它们的**可证等价**，不是 `P ↔ P`。 -/
theorem readClosedBlocks_iff (G : Causalean.Graph.DAG V) (X Y Z : Finset V) :
    Fate.BridgeMinZPrime.ReadClosedBlocks G X Y Z ↔
      Fate.BridgeFull.ReadClosedBlocks G X Y Z := by
  unfold Fate.BridgeMinZPrime.ReadClosedBlocks Fate.BridgeFull.ReadClosedBlocks
  exact Iff.rfl

/-- C1 的**等式**版（`Prop` 的外延相等）——便于 `rw`。 -/
theorem readClosedBlocks_eq (G : Causalean.Graph.DAG V) (X Y Z : Finset V) :
    Fate.BridgeMinZPrime.ReadClosedBlocks G X Y Z =
      Fate.BridgeFull.ReadClosedBlocks G X Y Z :=
  propext (readClosedBlocks_iff G X Y Z)

/-! ===========================================================================
  §2 **`zStar` 最小性移植到 `BridgeFull` 口径**（C2）
  =========================================================================== -/

/-- ⭐⭐ **C2**：**MZP 的 `zStar` 是 `BridgeFull.ReadClosedBlocks` 口径下的最小可行 `Z'`**。

若 `Z ⊆ Z'` 且 `Z'` 在 **`BridgeFull`** 的意义下可行，则 `zStar G X Y Z ⊆ Z'`。

**消费点（逐前件点名）**：
* `hZZ' : Z ⊆ Z'` → 传给 `MZP.zStar_minimal`；
* `h : BridgeFull.ReadClosedBlocks G X Y Z'` → 经 **C1** 转成 MZP 口径，
  再由 `MZP.zStar_minimal` 内部消费 `h.1`（`Z'` 父闭）+ `h.2.1` / `h.2.2`（两侧读集）。

**⟹ 结论 `zStar ⊆ Z'` 不出现在任何前件里**（纪律 7 核对通过）。 -/
theorem zStar_minimal_full {X Y Z Z' : Finset V} (hZZ' : Z ⊆ Z')
    (h : Fate.BridgeFull.ReadClosedBlocks G X Y Z') : zStar G X Y Z ⊆ Z' :=
  zStar_minimal hZZ' ((readClosedBlocks_iff G X Y Z').mpr h)

/-- C2 的**反向**用法：`BridgeFull` 口径下的可行 `Z'` 与 `zStar` 的**差距**刻画。 -/
theorem zStar_subset_of_full {X Y Z Z' : Finset V} (hZZ' : Z ⊆ Z')
    (h : Fate.BridgeFull.ReadClosedBlocks G X Y Z') : zStar G X Y Z ⊆ Z' :=
  zStar_minimal_full hZZ' h

/-- ⭐ **C2′**：`zStar` 在 `BridgeFull` 口径下**总是**可行（无条件）。 -/
theorem readClosed_zStar_full (X Y Z : Finset V) :
    Fate.BridgeFull.ReadClosedBlocks G X Y (zStar G X Y Z) :=
  (readClosedBlocks_iff G X Y (zStar G X Y Z)).mp (readClosed_zStar X Y Z)

/-! ===========================================================================
  §3 **`BridgeFull` 口径下的最小元 `∃!`**（C3）
  =========================================================================== -/

/-- ⭐⭐ **C3**：**`BridgeFull.ReadClosedBlocks` 的最小可行 `Z' ⊇ Z` 存在且唯一**，
且**就是** `zStar G X Y Z`。

前件**空**。结论是 `∃!` ⟹ 不可能是同义反复。

**消费链**：`MZP.existsUnique_min_readClosed`（MZP 口径）+ **C1**（口径搬运）。 -/
theorem existsUnique_min_readClosed_full (X Y Z : Finset V) :
    ∃! Zs : Finset V,
      Z ⊆ Zs ∧ Fate.BridgeFull.ReadClosedBlocks G X Y Zs ∧
      (∀ Z' : Finset V, Z ⊆ Z' →
        Fate.BridgeFull.ReadClosedBlocks G X Y Z' → Zs ⊆ Z') := by
  obtain ⟨Zs, ⟨hsub, hRC, hmin⟩, huniq⟩ := existsUnique_min_readClosed (G := G) X Y Z
  refine ⟨Zs, ⟨hsub, (readClosedBlocks_iff G X Y Zs).mp hRC, ?_⟩, ?_⟩
  · intro Z' hZZ' hRC'
    exact hmin Z' hZZ' ((readClosedBlocks_iff G X Y Z').mpr hRC')
  · rintro Zs' ⟨hsub', hRC', hmin'⟩
    exact huniq Zs' ⟨hsub', (readClosedBlocks_iff G X Y Zs').mpr hRC',
      fun Z' hZZ' hRC' => hmin' Z' hZZ' ((readClosedBlocks_iff G X Y Z').mp hRC')⟩

/-- C3 的**具体化**：`zStar` 本身是 `BridgeFull` 口径的唯一最小元。 -/
theorem zStar_is_min_full (X Y Z : Finset V) :
    Z ⊆ zStar G X Y Z ∧ Fate.BridgeFull.ReadClosedBlocks G X Y (zStar G X Y Z) ∧
      (∀ Z' : Finset V, Z ⊆ Z' →
        Fate.BridgeFull.ReadClosedBlocks G X Y Z' → zStar G X Y Z ⊆ Z') :=
  ⟨subset_zStar X Y Z, readClosed_zStar_full X Y Z,
    fun Z' hZZ' h => zStar_minimal_full hZZ' h⟩

/-! ===========================================================================
  §4 ⭐⭐⭐ **收口：`BridgeFull` 的桥在 `zStar` 处给出 `CondIndep`**（C4）
  =========================================================================== -/

/-- ⭐⭐⭐ **C4（本文件主定理）**：**`zStar` 上的条件独立性** ——

```
hloc   LocalTo G f
hfac   p x = ∏ v, f v x
hnorm  FactorNorm f
hd     G.dSep X Y (zStar G X Y Z)          ← 真前件（可以失败，见 §5）
⟹      CondIndep p X Y (zStar G X Y Z)
```

**这是「两个模块对接」的实际产出**：
* `hd` 由**调用者**提供（`BridgeFull` 的桥只吃 `dSep`）；
* `ReadClosedBlocks G X Y (zStar …)` **由 MZP 的 `readClosed_zStar` 无条件供给**
  （经 C1 转成 `BridgeFull` 口径）—— **这正是 MZP L1/L2 的用途**：
  桥的 `ReadClosedBlocks` 前件在 `zStar` 处**永远不需要人肉验证**。

**消费点（逐前件点名）**：
* `hloc` / `hfac` / `hnorm` → `BridgeFull.markov_of_readClosedBlocks`
  内部的 `Strategy11Hull.mass_ancClosed` 引擎（本文件不碰）；
* `hd` → 同一个定理的 `hd`（**只**取其两两不交子句，见 `condIndep_of_dSep_ancClosed`）；
* `readClosed_zStar X Y Z` → 该定理的 `hRC`（经 C1）。

**⟹ 结论 `CondIndep p X Y (zStar …)` 不是前件的任何一行**；
`hd`（`dSep`）与 `readClosed_zStar`（`ReadClosedBlocks`）是**两个独立**义务。 -/
theorem markov_at_zStar {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : Fate.FactorMarkov.FactorNorm f)
    (X Y Z : Finset V) (hd : G.dSep X Y (zStar G X Y Z)) :
    Fate.FactorMarkov.CondIndep p X Y (zStar G X Y Z) :=
  Fate.BridgeFull.markov_of_readClosedBlocks hloc hfac hnorm hd
    (readClosed_zStar_full X Y Z)

/-- ⭐ **C4′**：**只差 `dSep` 一条**的版本 —— 把 `dSep` 义务显式留在前提里，
便于与 `BridgeFull.markov_of_readClosedBlocks` 直接对齐比较口径。 -/
theorem markov_of_dSep_zStar {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : Fate.FactorMarkov.FactorNorm f) :
    ∀ X Y Z : Finset V, G.dSep X Y (zStar G X Y Z) →
      Fate.FactorMarkov.CondIndep p X Y (zStar G X Y Z) :=
  fun X Y Z hd => markov_at_zStar hloc hfac hnorm X Y Z hd

/-! ===========================================================================
  §5 ⭐⭐ **缺口 G1 在 `gch` 上假**（C5）—— 对接的**反面**落点
  =========================================================================== -/

/-- ⭐⭐ **C5**：**`BridgeFull` 的缺口 `DSepGivesReadClosed` 在 `gch` 上为假**。

**⟹ `BridgeFull` 的登记「G1 未证」在 `gch` 上可以升级为「G1 为假」**
（不是「没证完」，而是**不存在**这样的 `Z`）。

**证明链（逐前件点名）**：
1. 假设 `hg : Fate.BridgeFull.DSepGivesReadClosed gch`；
2. **`MZP.gch_dsep`**（`decide` 证出 `gch.dSep {0}{2}{1}`）⟹ 取 `X={0}, Y={2}, Z={1}`；
3. `hg …` 给出 `BridgeFull.ReadClosedBlocks gch {0}{2}{1}`；
4. **C1** 搬到 MZP 口径，再用 **`MZP.zStar_eq_iff_readClosed`** 得 `zStar = {1}`；
5. 但 **`MZP.gch_zStar`** 已 `decide` 出 `zStar = {0,1} ≠ {1}` ⟹ 矛盾。

**⟹ 这不是「某条引理没证完」，而是 MZP 的 `gch` 反例在 `BridgeFull` 的 `def` 上有直接落点。** -/
theorem not_dSepGivesReadClosed_gch :
    ¬ Fate.BridgeFull.DSepGivesReadClosed gch := by
  intro hg
  have hRC : Fate.BridgeFull.ReadClosedBlocks gch {(0 : Fin 3)} {(2 : Fin 3)}
      {(1 : Fin 3)} := hg {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} gch_dsep
  have hz : zStar gch {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} = {(1 : Fin 3)} :=
    (zStar_eq_iff_readClosed (G := gch) _ _ _).mp
      ((readClosedBlocks_iff gch _ _ _).mpr hRC)
  rw [gch_zStar] at hz
  exact absurd hz (by decide)

/-- ⭐ **C5′**：**C5 的一般形式** —— 若某个 `dSep` 三元组上 `zStar ≠ Z`，
则该 DAG **不**满足缺口 G1。

**⟹ 这是 G1 的**可判定判据**：只需查 `zStar G X Y Z = Z`。
（`Z` 本身可行 ⟺ `zStar` 不增长，见 `MZP.zStar_eq_iff_readClosed`。） -/
theorem not_dSepGivesReadClosed_of_zStar_ne {X Y Z : Finset V}
    (hd : G.dSep X Y Z) (hz : zStar G X Y Z ≠ Z) :
    ¬ Fate.BridgeFull.DSepGivesReadClosed G := by
  intro hg
  have hRC : Fate.BridgeFull.ReadClosedBlocks G X Y Z := hg X Y Z hd
  exact hz ((zStar_eq_iff_readClosed (G := G) X Y Z).mp
    ((readClosedBlocks_iff G X Y Z).mpr hRC))

/-- ⭐⭐ **C5″（正面版）**：**缺口 G1 ⟺ 所有 `dSep` 三元组上 `zStar` 不增长**。

**⟹ 这给出了 `BridgeFull` 缺口 `DSepGivesReadClosed` 的一个**等价的、纯图论**的重述**：
「G1 成立」与「`dSep X Y Z ⟹ zStar G X Y Z = Z`」是**同一件事**。
这**不是**把 G1 证掉了（后者同样未证、且 `gch` 上是假的），
而是把「概率/读集口径的缺口」翻译成「`zStar` 不动点口径的缺口」——

⚠ **诚实标注**：这条**不构成**对 G1 的证明；它只是**等价重述**，
其价值在于：`zStar` 是**有限可算**的（`Finset` 上 `decide` 可判），
故 G1 的**每个实例**都是可机械检验的（`gch` 上即为假，见 C5）。 -/
theorem dSepGivesReadClosed_iff_zStar_eq :
    Fate.BridgeFull.DSepGivesReadClosed G ↔
      ∀ X Y Z : Finset V, G.dSep X Y Z → zStar G X Y Z = Z := by
  constructor
  · intro hg X Y Z hd
    exact (zStar_eq_iff_readClosed (G := G) X Y Z).mp
      ((readClosedBlocks_iff G X Y Z).mpr (hg X Y Z hd))
  · intro hz X Y Z hd
    exact (readClosedBlocks_iff G X Y Z).mp
      ((zStar_eq_iff_readClosed (G := G) X Y Z).mpr (hz X Y Z hd))

/-! ===========================================================================
  §6 交付清单
  =========================================================================== -/

/-
| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| C1 | `readClosedBlocks_iff` | 两份 `ReadClosedBlocks` 可证等价 | ✅ 真证明 |
| C1 | `readClosedBlocks_eq` | 等式版（`propext`） | ✅ 真证明 |
| C2 | ⭐ `zStar_minimal_full` | MZP 最小性移植到 `BridgeFull` 口径 | ✅ 真证明 |
| C2 | `zStar_subset_of_full` | C2 的别名（下游易搜） | ✅ 真证明 |
| C2 | `readClosed_zStar_full` | `zStar` 在 `BridgeFull` 口径下可行 | ✅ 真证明 |
| C3 | ⭐ `existsUnique_min_readClosed_full` | `BridgeFull` 口径最小元 `∃!` | ✅ 真证明 |
| C3 | `zStar_is_min_full` | `zStar` 是唯一最小元（具体版） | ✅ 真证明 |
| C4 | ⭐⭐ `markov_at_zStar` | **收口**：`dSep X Y zStar ⟹ CondIndep p X Y zStar` | ✅ 真证明 |
| C4 | `markov_of_dSep_zStar` | C4 的 `∀`-形式 | ✅ 真证明 |
| C5 | ⭐⭐ `not_dSepGivesReadClosed_gch` | **缺口 G1 在 `gch` 上为假** | ✅ 真证明 |
| C5 | `not_dSepGivesReadClosed_of_zStar_ne` | G1 失败的一般判据 | ✅ 真证明 |
| C5 | ⭐ `dSepGivesReadClosed_iff_zStar_eq` | **G1 ⟺ `zStar` 在 `dSep` 下不动** | ✅ 真证明 |

**诚实结论**：

1. **两个模块已对接**（C1–C5 全部机器验证，零 `sorry`）。
2. **`BridgeFull` 的桥在 `zStar` 处可无条件调用**（C4）：
   唯一遗留义务是 `dSep X Y (zStar G X Y Z)`，**不是** `ReadClosedBlocks`。
3. **缺口 G1 没有被证掉，反而在 `gch` 上被机器验证为假**（C5）；
   C5″ 把它等价重述为 `zStar` 的不动点条件 —— 这是**等价**，不是证明。
4. MZP 文件头 §0.4 的「`BridgeFull` 不可编译」**已过期**（实测 EXIT=0）；
   本文件**不改** MZP（纪律 2），仅在此如实标注。
-/

end Fate.BridgeMinZPrimeConsumer