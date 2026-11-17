/-
# `Fate/BridgeExpandedT7` —— **T7 的形式化**：`strong_enlargement_false`

## 0 背景与交付说明（**先读这一节**）

`Fate/BridgeExpanded.lean:553-561` 有一段完整的数学论证（T7），但注释里写的
**定理名** `strong_enlargement_false` 在全库从未以 `theorem` 声明出现过
（`grep -rn "theorem strong_enlargement_false" Fate/` → 0 命中；
`grep -rn "strong_enlargement_false" Fate/` → 仅第 553 行注释命中）。

⚠ **诚实申明（重要）**：

* 该论证的**数学内容**在 `Fate/BridgeExpanded.lean` 里**已经**被形式化为
  `disjoint_ancClosed_superset_false`（T7，第 563 行）与
  `strong_enlargement_with_dsep_false`（T7′，第 578 行），二者**均已 machine-checked**。
* 因此本文件**不是**「补一个缺失的证明」，而是**按任务书要求把注释里的名字
  `strong_enlargement_false` 落成 `theorem` 声明**，并把注释里的三步走论证
  **独立地、逐步地**重写一遍（不套用上述两个既有定理作为黑箱），
  使「名字 ↔ 陈述 ↔ 证明」三者对齐、可被下游按注释里的名字直接引用。
* 本文件**不修改** `Fate/BridgeExpanded.lean`（纪律第 2 条）。

## 1 依赖的既有形式化（**无需新造定义**）

| 需要的东西 | 库里现成形式 | 位置 |
|---|---|---|
| 图 `g2`（`Fin 4`，唯一边 `1 → 3`）| `Fate.BridgeExpanded.g2` | `BridgeExpanded.lean:530` |
| 祖先闭集 `AncClosed` | `Fate.Strategy11Hull.AncClosed`（`∀ v ∈ A, G.parents v ⊆ A`）| `Strategy11AncestralHull.lean:82` |
| `pa(3) = {1}`（`g2` 上）| `Fate.BridgeExpanded.g2_pa` | `BridgeExpanded.lean:543` |
| T7.a（`3 ∈ Z'` + 祖先闭 ⟹ `1 ∈ Z'`）| `Fate.BridgeExpanded.g2_ancClosed_forces_X` | `BridgeExpanded.lean:547` |

⟹ **不缺任何定义**；`AncClosed`、`parents`、`Disjoint`、`⊆` 全部是库内/Mathlib 现成的。

## 2 目标定理

$$\textbf{T7：}\quad
\neg\,\exists Z' \supseteq \{3\},\ \mathrm{AncClosed}(g_2, Z') \wedge \mathrm{Disjoint}(\{1\}, Z').$$

**证明**（照注释三步走）：

1. `3 ∈ Z'`（因 `Z = {3} ⊆ Z'`）；
2. `pa(3) = {1} ⊆ Z'`（祖先闭 + 步骤 1，即 T7.a）；
3. `1 ∈ Z'` 且 `1 ∈ {1}` ⟹ `{1} ∩ Z' ≠ ∅` ⟹ 与 `Disjoint {1} Z'` 矛盾。
-/
import FateWorld.FateV2.Predict.BridgeExpanded
open Finset

namespace FateV2.Predict.BridgeExpandedT7

open FateV2.Modeling

open Fate.BridgeExpanded
open FateV2.Modeling.Graph

/-!
  # Predict · BridgeExpandedT7

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeExpandedT7.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeExpanded
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 T7 的三步走，逐步形式化
  =========================================================================== -/

/-- **步骤 1**：`Z ⊢ {3} ⊆ Z'` 给出 `3 ∈ Z'`。

（这一步在注释里是「因 `Z = {3}` 包含于 `Z'`」，是 `⊆` 的直接应用。） -/
theorem step1_mem_three {Z' : Finset (Fin 4)}
    (hsub : ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ Z') : (3 : Fin 4) ∈ Z' :=
  hsub (mem_singleton_self 3)

/-- **步骤 2**：`Z'` 祖先闭且 `3 ∈ Z'` ⟹ `pa(3) = {1} ⊆ Z'`，从而 `1 ∈ Z'`（即 T7.a）。 -/
theorem step2_mem_one {Z' : Finset (Fin 4)}
    (hanc : Fate.Strategy11Hull.AncClosed g2 Z') (h3 : (3 : Fin 4) ∈ Z') :
    (1 : Fin 4) ∈ Z' :=
  g2_ancClosed_forces_X hanc h3

/-- **步骤 3**：`1 ∈ Z'` ⟹ 破坏 `Disjoint {1} Z'`。 -/
theorem step3_not_disjoint {Z' : Finset (Fin 4)} (h1 : (1 : Fin 4) ∈ Z') :
    ¬ Disjoint ({(1 : Fin 4)} : Finset (Fin 4)) Z' := by
  intro hdis
  exact (Finset.disjoint_left.mp hdis) (mem_singleton_self 1) h1

/-! ===========================================================================
  §2 ⭐⭐⭐ **T7 — `strong_enlargement_false`**（本文件最重要的否定结论）
  =========================================================================== -/

/-- ⭐⭐⭐ **T7 — `strong_enlargement_false`**：
**不存在 `Z' ⊇ {3}` 同时满足「`Z'` 祖先闭」与「`Disjoint {1} Z'`」。**

证明序列（与注释逐字对应）：
`3 ∈ Z'`（步骤 1）⟹ `pa(3) = {1} ⊆ Z'`（步骤 2，即 T7.a）⟹ `1 ∈ Z'`
⟹ `1 ∈ {1} ∩ Z'` ⟹ 破坏 `Disjoint {1} Z'`（步骤 3）。

**⟹** `Z' ⊋ Z` 路线在 `g2` 上**死穴**：`dSep {1} {2} {3}` 成立（见 `g2_dsep`），
但任何祖先闭的 `Z' ⊇ {3}` 必含 `pa(3) = {1} ⊆ X`，与 `Disjoint X Z'` 冲突。 -/
theorem strong_enlargement_false :
    ¬ ∃ Z' : Finset (Fin 4), ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ Z'
        ∧ Fate.Strategy11Hull.AncClosed g2 Z'
        ∧ Disjoint ({(1 : Fin 4)} : Finset (Fin 4)) Z' := by
  rintro ⟨Z', hsub, hanc, hdis⟩
  -- 步骤 1：`3 ∈ Z'`
  have h3 : (3 : Fin 4) ∈ Z' := step1_mem_three hsub
  -- 步骤 2：`1 ∈ Z'`（T7.a）
  have h1 : (1 : Fin 4) ∈ Z' := step2_mem_one hanc h3
  -- 步骤 3：破坏不交性
  exact step3_not_disjoint h1 hdis

/-! ===========================================================================
  §3 与既有形式的对齐（一致性核查，非新数学）
  =========================================================================== -/

/-- **核对 1**：`strong_enlargement_false` 与既有的 `disjoint_ancClosed_superset_false`
**陈述逐字相同**（同一 `Prop`），因此可互相直接应用。
这是「名字对齐」的证据：注释里的论证早已被 machine-check（只是叫另一个名字）。 -/
theorem strong_enlargement_false_from_existing :
    ¬ ∃ Z' : Finset (Fin 4), ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ Z'
        ∧ Fate.Strategy11Hull.AncClosed g2 Z'
        ∧ Disjoint ({(1 : Fin 4)} : Finset (Fin 4)) Z' :=
  disjoint_ancClosed_superset_false

/-- 核对 1 的另一方向：既有名字也可直接由新名字给出。 -/
theorem existing_from_strong_enlargement_false :
    ¬ ∃ Z' : Finset (Fin 4), ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ Z'
        ∧ Fate.Strategy11Hull.AncClosed g2 Z'
        ∧ Disjoint ({(1 : Fin 4)} : Finset (Fin 4)) Z' :=
  strong_enlargement_false

/-- **核对 2**：`strong_enlargement_false` 就是 `strong_enlargement_with_dsep_false` 的后半，
且该打包版本额外给出 `dSep {1} {2} {3}` **成立** —— 即前件并非空转。 -/
theorem strong_enlargement_false_with_dsep :
    g2.dSep {(1 : Fin 4)} {(2 : Fin 4)} {(3 : Fin 4)}
      ∧ ¬ ∃ Z' : Finset (Fin 4), ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ Z'
          ∧ Fate.Strategy11Hull.AncClosed g2 Z'
          ∧ Disjoint ({(1 : Fin 4)} : Finset (Fin 4)) Z' :=
  ⟨g2_dsep, strong_enlargement_false⟩

/-! ===========================================================================
  §4 非空转核查：前件确实可被满足的一半（`Z' = {3}` 祖先闭的检验）
  =========================================================================== -/

/-- **`{3}` 自身不是祖先闭**（`pa(3) = {1} ⊄ {3}`）：这说明 T7 的张力
**不是** `Z' = Z` 特例，而是在 `Z' ⊇ Z` 的每一个候选上都生效。 -/
theorem not_ancClosed_singleton_three :
    ¬ Fate.Strategy11Hull.AncClosed g2 ({(3 : Fin 4)} : Finset (Fin 4)) := by
  intro hanc
  have h1 : (1 : Fin 4) ∈ ({(3 : Fin 4)} : Finset (Fin 4)) :=
    step2_mem_one hanc (mem_singleton_self 3)
  exact absurd h1 (by decide)

end FateV2.Predict.BridgeExpandedT7