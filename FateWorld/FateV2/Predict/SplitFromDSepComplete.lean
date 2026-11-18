/-
# C3 缺口核查：`dSep + 覆盖 ⟹ Split` 到底缺不缺「长路径」论证？

本文件是对任务「填 C3 缺口：长路径情形的 dSep ⟹ Split」的**判决性回答**，
全部机检（零 `sorry` / 零 `admit` / 零 `axiom`）。

## 0 结论（一句话）

> **(a) `split_of_dSep` 的陈述为真，反例不存在**（`kept_split_of_dSep` 重新机检确认）。
> **(b) 当前证明已经完全覆盖所有情形**：它**不需要**任何长路径论证。

而且原因是**结构性的**，不是「证明偷懒」：

> `Split (readSetOf G) X Y Z` 只谈论读集 `R v = {v} ∪ pa(v)`，
> 而 `R v` 只涉及长度 ≤ 1 的边（`v` 与它的直接父）。
> 因此 `Split` 是一个**深度 1（depth-1）谓词**；
> `dSep` 的 Bayes-Ball 长路径语义（`bbReachableVertices` 的传递闭包部分）
> 在**逻辑上不可能**对 `Split` 有额外贡献。

本文件把这个「深度 1 归约」**形式化**（§2），并据此给出与 `split_of_dSep`
同陈述的**第二次独立证明** `split_of_dSep_complete`（§4），
其证明结构为：

1. **§2 深度 1 归约**：`¬ Split` 等价于「存在跨侧见证对 `(a,b)`」——
   `a, b ∈ R v`、`a ∈ X`、`b ∈ Y`（`not_split_iff_crossing`）。
   这是对「每个情形都已覆盖」的**形式化**：`Split` 的失效只可能由
   一个深度 1 的跨侧读集造成。
2. **§3 `dSep` 的 one-hop 成分**：把 `dSep` 的三条「禁边」结论打包成
   谓词 `dSepOneHop`（`dSep_implies_oneHop`），并说明每条对应 `dSep`
   的哪个合取项。
3. **§4 主定理**：`dSepOneHop → ¬ ∃ 跨侧见证对`（对 `(a,b)` 在
   `{v} ∪ pa v` 里的 4 种落位做**一致**分类），再由 §2 得 `Split`。

⚠ 关键点：§3 的 `dSepOneHop` **完全不提** `bbReachableVertices`（Bayes-Ball），
而 §4 只用 `dSepOneHop`。这就机检地证明了：
**`split_of_dSep` 的证明不需要、也不可能需要长路径论证。**

## 1 逐条回答任务的问题

* **(a) 陈述是否对任意 `dSep` 成立？** 是。反例只可能出现在
  **去掉覆盖条件** 时（`Fate/SplitFromDAG.lean` §5 的 `colliderDAG`：
  `V = Fin 3`、`0 → 2 ← 1`、`X = {0}`、`Y = {1}`、`Z = ∅`，
  顶点 `2 ∉ X∪Y∪Z` 的读集 `{0,1,2}` 横跨两侧）。
  加上覆盖 `X ∪ Y ∪ Z = univ` 后，唯一可能的「漏网」顶点 `v ∉ X∪Y∪Z`
  被排除，于是失效只可能来自深度 1 的跨侧读集，而后者被
  `not_edge_of_dSep_left/right` 与 `no_collider_in_Z` 三条逐一堵死。
  **故不存在反例；本文件不提供（也不可能有）`split_of_dSep_false`。**
* **(b) 当前证明是否已完整覆盖？** 是。`Fate/SplitFromDAG.lean` 的
  `split_of_dSep` 按 `v ∈ X` / `v ∈ Y` / `v ∈ Z` 三分类（覆盖保证齐全），
  每类内部再对 `pa(v)` 的三分类（`X`/`Y`/`Z`；覆盖保证非 `X∪Y∪Z` 的父不存在）
  穷尽。分支数 3×3 = 9，全部堵死，**无缺口**。
  **因此「这是弱结论」的判断是错的**：它不弱 —— 它恰好是
  `dSep` 在深度 1 上**能**给出的全部，而 `Split` 要的恰好也只有深度 1。

## 2 文件结构

* §1 基础：`mem_readSetOf`、覆盖下的三分
* §2 **深度 1 归约**：`crossing`、`not_split_iff_crossing`、`split_of_no_crossing`
* §3 **one-hop 成分**：`dSepOneHop`、`dSep_implies_oneHop`
* §4 **主定理**：`no_crossing_of_oneHop`、`split_of_dSep_complete`
* §5 **分类引理**（「每个情形都已覆盖」的形式化）：`split_case_classification`
* §6 与既有模块的一致性：`kept_split_of_dSep`、`split_of_dSep_agree`
* §7 诚实边界

## 3 依赖

* `FateV2.Predict.SplitFromDAG` —— 既有结论 `split_of_dSep` 及三条禁边引理（本文件不改动它）
* `FateV2.Predict.FactorizesToHyper.readSetOf` / `mem_readSetOf`
* `FateV2.Predict.View19.Split`
* `Causalean.Graph.DAG.dSep` / `mem_parents`

**本文件不修改任何既有模块；不写 `Fate/` 目录；不改 `Fate.lean`。**
-/

import FateWorld.FateV2.Predict.SplitFromDAG
namespace FateV2.Predict

open FateV2.Modeling
namespace SplitFromDSepComplete

open Finset FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-!
  # Predict · SplitFromDSepComplete

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SplitFromDSepComplete.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SplitFromDAG
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 基础
  =========================================================================== -/

/-- 读集的成员判定（展开版，避免依赖 `readSetOf` 的 `def` 形态）。 -/
theorem mem_R (G : FateV2.Modeling.Graph.DAG V) {v u : V} :
    u ∈ FateV2.Predict.FactorizesToHyper.readSetOf G v ↔ u = v ∨ G.edge u v := by
  rw [FateV2.Predict.FactorizesToHyper.mem_readSetOf, FateV2.Modeling.Graph.DAG.mem_parents]

/-- ⭐ **覆盖下的三分**：若 `X ∪ Y ∪ Z = univ`，则每个 `v` 落在 `X` 或 `Y` 或 `Z`。

覆盖条件是 §4 唯一用到的**非 `dSep`** 前提：它排除「读集横跨两侧、
但宿主顶点 `v` 本身不在查询集内」这一 `Split` 的唯一「逃逸口」。 -/
theorem mem_three_of_cover {X Y Z : Finset V} (hcover : X ∪ Y ∪ Z = univ) (v : V) :
    v ∈ X ∨ v ∈ Y ∨ v ∈ Z := by
  have hv : v ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ v
  rcases Finset.mem_union.mp hv with h | h
  · rcases Finset.mem_union.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h)

/-! ===========================================================================
  §2 **深度 1 归约**：`Split` 的失效 ⟺ 存在深度 1 的跨侧读集见证

  这一节把任务里「每个情形是否都已覆盖」形式化。
  它说明 `Split` 只可能被「同一个读集同时碰到 `X` 与 `Y`」破坏，
  而读集 `R v = {v} ∪ pa(v)` 只含 `v` 与 `v` 的直接父 —— 深度 1。
  =========================================================================== -/

/-- ⭐⭐ **跨侧见证**：读集 `R v` 同时含 `X` 中的 `a` 与 `Y` 中的 `b`。 -/
def Crossing (G : FateV2.Modeling.Graph.DAG V) (X Y : Finset V) : Prop :=
  ∃ v a b, a ∈ FateV2.Predict.FactorizesToHyper.readSetOf G v ∧
    b ∈ FateV2.Predict.FactorizesToHyper.readSetOf G v ∧ a ∈ X ∧ b ∈ Y

/-- ⭐⭐⭐ **深度 1 归约（反向）**：若无跨侧见证，则 `Split` 成立。

证明：若 `Split` 在某 `v` 处失效，则 `R v ⊄ X∪Z` 且 `R v ⊄ Y∪Z`，
取 `a ∈ R v ∖ (X∪Z)`、`b ∈ R v ∖ (Y∪Z)`；由覆盖
`a ∈ X∪Y∪Z` 且 `a ∉ X∪Z` 得 `a ∈ Y`，同理 `b ∈ X`，
于是 `(b, a)` 是一个跨侧见证（`b ∈ X`、`a ∈ Y`）。

⚠ 这里**只**用覆盖，不用 `dSep`。 -/
theorem split_of_no_crossing (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hcover : X ∪ Y ∪ Z = univ)
    (hnc : ¬ Crossing G X Y) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z := by
  intro v
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnXZ, hnYZ⟩ := hcon
  rw [Finset.not_subset] at hnXZ hnYZ
  obtain ⟨a, haR, haNZ⟩ := hnXZ
  obtain ⟨b, hbR, hbNZ⟩ := hnYZ
  have ha3 : a ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ a
  have hb3 : b ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ b
  have haY : a ∈ Y := by
    rcases Finset.mem_union.mp ha3 with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact absurd (Finset.mem_union.mpr (Or.inl h')) haNZ
      · exact h'
    · exact absurd (Finset.mem_union.mpr (Or.inr h)) haNZ
  have hbX : b ∈ X := by
    rcases Finset.mem_union.mp hb3 with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact h'
      · exact absurd (Finset.mem_union.mpr (Or.inl h')) hbNZ
    · exact absurd (Finset.mem_union.mpr (Or.inr h)) hbNZ
  exact hnc ⟨v, b, a, hbR, haR, hbX, haY⟩

/-- ⭐⭐ **深度 1 归约（正向）**：若有跨侧见证，则 `Split` 失效。

（这一半不需要覆盖：若 `R v` 含 `a ∈ X` 与 `b ∈ Y`，
则 `R v ⊆ X∪Z` 会给出 `b ∈ X∪Z`，`R v ⊆ Y∪Z` 会给出 `a ∈ Y∪Z`，
结合 `X, Y, Z` 两两不交（`dSep` 的前三个合取项）导出矛盾。
为保持本引理不依赖 `dSep`，这里用其纯集合形式。） -/
theorem not_split_of_crossing (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hc : Crossing G X Y) :
    ¬ FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z := by
  rintro hsplit
  obtain ⟨v, a, b, haR, hbR, haX, hbY⟩ := hc
  rcases hsplit v with h | h
  · have hb : b ∈ X ∪ Z := h hbR
    rcases Finset.mem_union.mp hb with hbX | hbZ
    · exact Finset.disjoint_left.mp hXY hbX hbY
    · exact Finset.disjoint_left.mp hYZ hbY hbZ
  · have ha : a ∈ Y ∪ Z := h haR
    rcases Finset.mem_union.mp ha with haY | haZ
    · exact Finset.disjoint_left.mp hXY haX haY
    · exact Finset.disjoint_left.mp hXZ haX haZ

/-- ⭐⭐⭐ **`Split` 是深度 1 谓词**（双向等价，`dSep` 的集合不交项一并纳入）。

`Split (readSetOf G) X Y Z ↔ 不存在深度 1 的跨侧读集见证`。

**这就是「每个情形都已覆盖」的精确形式化**：`Split` 的成立与否
完全由「读集的成员落在哪一侧」决定，而读集只含长度 ≤ 1 的信息，
所以长路径（长度 ≥ 2 的 Bayes-Ball 行走）**在原理上无法**影响 `Split`。 -/
theorem split_iff_no_crossing (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hcover : X ∪ Y ∪ Z = univ)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z ↔
      ¬ Crossing G X Y :=
  ⟨fun h hc => not_split_of_crossing G X Y Z hXY hXZ hYZ hc h,
    split_of_no_crossing G X Y Z hcover⟩

/-! ===========================================================================
  §3 `dSep` 的 **one-hop 成分**

  `dSep X Y Z` 是四个合取项。§5 的反例说明：只有**第四项**
  （`Disjoint (bbReachableVertices Z X) Y`，Bayes-Ball 部分）有内容，
  前三项是纯集合不交。而第四项对`深度 1` 的贡献**恰好是三条**：

  | 分量 | 内容 | 来源 |
  |---|---|---|
  | `hop₁` | 无 `X → Y` 边 | `not_edge_of_dSep_left` |
  | `hop₂` | 无 `Y → X` 边 | `not_edge_of_dSep_right`（= `dSep_symm` + `hop₁`）|
  | `hop₃` | `Z` 内无 `x → z ← y` 的 collider | `no_collider_in_Z` |

  `dSepOneHop` 把这三条打包，**完全不提 `bbReachableVertices`**。
  =========================================================================== -/

/-- ⭐⭐ **`dSep` 的 one-hop 骨架**：三条禁边结论。**不含任何 Bayes-Ball 量。** -/
def dSepOneHop (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  (∀ u v, u ∈ X → v ∈ Y → ¬ G.edge u v) ∧
  (∀ u v, u ∈ Y → v ∈ X → ¬ G.edge u v) ∧
  (∀ x y z, x ∈ X → y ∈ Y → z ∈ Z → G.edge x z → G.edge y z → False)

/-- ⭐⭐⭐ **`dSep ⟹ dSepOneHop`**：三条禁边全部由 `dSep` 的
**第四合取项** `Disjoint (bbReachableVertices Z X) Y` 产出
（前三个合取项 `Disjoint X Y`、`Disjoint X Z`、`Disjoint Y Z` 在 §4 另有用处）。

这是「长路径部分用不上」这一判断的**机检证据**：
我们把 `dSep` 削弱到 `dSepOneHop`（丢掉全部 Bayes-Ball 传递信息）后，
§4 仍然推得出 `Split`。 -/
theorem dSep_implies_oneHop (G : FateV2.Modeling.Graph.DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) : dSepOneHop G X Y Z :=
  ⟨fun _ _ hu hv => FateV2.Predict.SplitFromDAG.not_edge_of_dSep_left G h hu hv,
   fun _ _ hu hv => FateV2.Predict.SplitFromDAG.not_edge_of_dSep_right G h hu hv,
   fun _ _ _ hx hy hz hxz hyz =>
     FateV2.Predict.SplitFromDAG.no_collider_in_Z G h hx hy hxz hyz hz⟩

/-! ===========================================================================
  §4 **主定理**：`dSepOneHop` ⟹ 无跨侧见证 ⟹ `Split`

  核心是 `no_crossing_of_oneHop`：对见证 `a, b ∈ R v` 的**落位**
  做**一致**分类。`R v = {v} ∪ pa v`（`mem_R`）给出 `a` 与 `b` 各两种落位，
  共 4 种组合；每种的矛盾来源如下表。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **one-hop 骨架 ⟹ 无跨侧见证**。

对 `a ∈ R v`、`b ∈ R v`、`a ∈ X`、`b ∈ Y` 的 4 种落位逐一堵死：

| `a` | `b` | 矛盾来源 |
|---|---|---|
| `= v` | `= v` | `a = b ∈ X ∩ Y`，与 `Disjoint X Y` 矛盾（`dSep` 第 1 合取项）|
| `= v` | `∈ pa v` | 边 `b → v` 是 `Y → X` 边 ⟹ `hop₂`（`dSep` 第 4 合取项）|
| `∈ pa v` | `= v` | 边 `a → v` 是 `X → Y` 边 ⟹ `hop₁`（`dSep` 第 4 合取项）|
| `∈ pa v` | `∈ pa v` | `v` 落在 `X`/`Y` ⟹ 边是 `Y→X`/`X→Y`（`hop₂`/`hop₁`）；`v ∈ Z` ⟹ `Z` 内 collider ⟹ `hop₃`（`dSep` 第 4 合取项）| -/
theorem no_crossing_of_oneHop (G : FateV2.Modeling.Graph.DAG V) {X Y Z : Finset V}
    (hXY : Disjoint X Y)
    (hOne : dSepOneHop G X Y Z)
    (hcover : X ∪ Y ∪ Z = univ) :
    ¬ Crossing G X Y := by
  rintro ⟨v, a, b, haR, hbR, haX, hbY⟩
  obtain ⟨hop₁, hop₂, hop₃⟩ := hOne
  rw [mem_R] at haR hbR
  -- `a = v` 或 `a → v`；`b = v` 或 `b → v`
  rcases haR with hav | haEd
  · -- a = v
    subst hav
    rcases hbR with hbv | hbEd
    · -- b = v：a = b 同时属于 X 与 Y
      subst hbv
      exact Finset.disjoint_left.mp hXY haX hbY
    · -- b → a（a = v ∈ X，b ∈ Y）：Y → X 边，hop₂
      exact hop₂ b a hbY haX hbEd
  · -- a → v
    rcases hbR with hbv | hbEd
    · -- b = v ∈ Y，a ∈ X：X → Y 边，hop₁
      subst hbv
      exact hop₁ a b haX hbY haEd
    · -- a → v 且 b → v：按 v 的归属三分（覆盖给出）
      rcases mem_three_of_cover hcover v with hvX | hvY | hvZ
      · -- v ∈ X ⟹ b → v 是 Y → X 边
        exact hop₂ b v hbY hvX hbEd
      · -- v ∈ Y ⟹ a → v 是 X → Y 边
        exact hop₁ a v haX hvY haEd
      · -- v ∈ Z ⟹ Z 内的 x → v ← y collider
        exact hop₃ a b v haX hbY hvZ haEd hbEd

/-- ⭐⭐⭐⭐⭐ **主定理（与 `split_of_dSep` 同陈述，第二次独立证明）**：
`dSep X Y Z` + 覆盖 `X ∪ Y ∪ Z = univ` ⟹ `Split (readSetOf G) X Y Z`。

**证明路线（与 `Fate/SplitFromDAG.lean` 的逐 `v` 分情形路线不同，但等价）：**

1. `dSep ⟹ dSepOneHop`（`dSep_implies_oneHop`）：只取 `dSep` 第 4 合取项的
   三条**深度 1** 推论 —— **丢掉** `bbReachableVertices` 的全部传递信息。
2. `dSepOneHop + Disjoint X Y + 覆盖 ⟹ ¬ Crossing`（`no_crossing_of_oneHop`）。
3. `¬ Crossing + 覆盖 ⟹ Split`（`split_of_no_crossing`）。

**⚠ 步骤 1 是纯粹的「深度 1」降级**：`dSepOneHop` 里没有任何
`bbReachableVertices` / `bbStep` / `bbReachable` 出现。因此
「`X` 与 `Y` 之间隔着长度 ≥ 3 的路径」这一情形所需的全部信息，
在第 1 步就已被**丢弃且无损**——它对本定理的结论没有任何贡献。 -/
theorem split_of_dSep_complete (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z)
    (hcover : X ∪ Y ∪ Z = univ) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z := by
  have hXY : Disjoint X Y := hdsep.1
  exact split_of_no_crossing G X Y Z hcover
    (no_crossing_of_oneHop G hXY (dSep_implies_oneHop G hdsep) hcover)

/-! ===========================================================================
  §5 **分类引理**：把「每个情形都已覆盖」形式化为单条定理

  任务要求「把『每个情形都已覆盖』形式化为一个分类引理」。这里给出
  **逐 `v` 的显式分类**：对每个 `v`，`Split` 所需的那一侧包含关系
  由 `v` 的归属**完全决定**，且三类穷尽（覆盖保证），每类的证明依据
  都精确对应 `dSep` 的一个成分。
  =========================================================================== -/

/-- 三类归属 + 每类的读集归属（`Split` 的逐点分类）。

结论的**逻辑内容**与 `split_of_dSep_complete` 相同，但它把
「`v` 属于哪一侧 ⟹ 读集落在哪一侧」显式写成三分，
便于审计「哪些情形被覆盖、各自用什么前提」：

* `v ∈ X`：`R v ⊆ X ∪ Z`，只需要 `hop₂`（无 `Y → X` 边）。
* `v ∈ Y`：`R v ⊆ Y ∪ Z`，只需要 `hop₁`（无 `X → Y` 边）。
* `v ∈ Z`：`R v ⊆ X ∪ Z` 或 `R v ⊆ Y ∪ Z` 二者之一，
  只需要 `hop₃`（`Z` 内无 collider）。
  **这里正是「二分」的来源**：读集在 `Z` 处只能倒向一侧。 -/
theorem split_case_classification (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ) :
    (∀ v ∈ X, FateV2.Predict.FactorizesToHyper.readSetOf G v ⊆ X ∪ Z) ∧
    (∀ v ∈ Y, FateV2.Predict.FactorizesToHyper.readSetOf G v ⊆ Y ∪ Z) ∧
    (∀ v ∈ Z, FateV2.Predict.FactorizesToHyper.readSetOf G v ⊆ X ∪ Z ∨
              FateV2.Predict.FactorizesToHyper.readSetOf G v ⊆ Y ∪ Z) := by
  have hXY : Disjoint X Y := hdsep.1
  obtain ⟨hop₁, hop₂, hop₃⟩ := dSep_implies_oneHop G hdsep
  have key : ∀ v u, u ∈ FateV2.Predict.FactorizesToHyper.readSetOf G v → u = v ∨ G.edge u v :=
    fun v u hu => (mem_R G).mp hu
  refine ⟨?_, ?_, ?_⟩
  · -- v ∈ X：只需要「无 Y → X 边」
    intro v hv u hu
    rcases key v u hu with rfl | hEd
    · exact Finset.mem_union.mpr (Or.inl hv)
    · rcases mem_three_of_cover hcover u with huX | huY | huZ
      · exact Finset.mem_union.mpr (Or.inl huX)
      · exact absurd hEd (hop₂ u v huY hv)
      · exact Finset.mem_union.mpr (Or.inr huZ)
  · -- v ∈ Y：只需要「无 X → Y 边」
    intro v hv u hu
    rcases key v u hu with rfl | hEd
    · exact Finset.mem_union.mpr (Or.inl hv)
    · rcases mem_three_of_cover hcover u with huX | huY | huZ
      · exact absurd hEd (hop₁ u v huX hv)
      · exact Finset.mem_union.mpr (Or.inl huY)
      · exact Finset.mem_union.mpr (Or.inr huZ)
  · -- v ∈ Z：只需要「Z 内无 collider」，按「是否有 X-父」二分
    intro v hv
    by_cases hXp : ∃ u, G.edge u v ∧ u ∈ X
    · left
      intro u hu
      rcases key v u hu with rfl | hEd
      · exact Finset.mem_union.mpr (Or.inr hv)
      · rcases mem_three_of_cover hcover u with huX | huY | huZ
        · exact Finset.mem_union.mpr (Or.inl huX)
        · obtain ⟨x, hxEd, hxX⟩ := hXp
          exact absurd (hop₃ x u v hxX huY hv hxEd hEd) id
        · exact Finset.mem_union.mpr (Or.inr huZ)
    · right
      intro u hu
      rcases key v u hu with rfl | hEd
      · exact Finset.mem_union.mpr (Or.inr hv)
      · rcases mem_three_of_cover hcover u with huX | huY | huZ
        · exact absurd ⟨u, hEd, huX⟩ hXp
        · exact Finset.mem_union.mpr (Or.inl huY)
        · exact Finset.mem_union.mpr (Or.inr huZ)

/-- ⭐ **分类引理直接重推出 `Split`**（说明 §5 的分类确实穷尽且充分）。 -/
theorem split_of_classification (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z := by
  obtain ⟨hX, hY, hZ⟩ := split_case_classification G X Y Z hdsep hcover
  intro v
  rcases mem_three_of_cover hcover v with hvX | hvY | hvZ
  · exact Or.inl (hX v hvX)
  · exact Or.inr (hY v hvY)
  · exact hZ v hvZ

/-! ===========================================================================
  §6 与既有模块的一致性

  三条独立证明（`FateV2.Predict.SplitFromDAG.split_of_dSep` 的逐点路线、
  §4 的跨侧见证路线、§5 的分类路线）给出**同一陈述**，
  且 `Agreement` 机检它们互相蕴含（因陈述相同，这里是 `Iff.rfl` 级的核对）。
  =========================================================================== -/

/-- ⭐ **既有结论的重新机检**：`split_of_dSep` 无需任何补丁。 -/
theorem kept_split_of_dSep (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z :=
  FateV2.Predict.SplitFromDAG.split_of_dSep G X Y Z hdsep hcover

/-- ⭐ **三条证明路线一致**：陈述逐字相同，故互相等价。 -/
theorem split_three_routes_agree (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ) :
    FateV2.Predict.SplitFromDAG.split_of_dSep G X Y Z hdsep hcover =
      split_of_dSep_complete G X Y Z hdsep hcover ∧
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z :=
  ⟨rfl, split_of_classification G X Y Z hdsep hcover⟩

/-! ===========================================================================
  §7 诚实边界

  * 本文件**不提供** `split_of_dSep_false`，也**无法**提供 ——
    因为 (a) 为真：不存在反例。真正的反例需要去掉覆盖条件，
    见 `Fate/SplitFromDAG.lean` §5 的 `dSep_not_implies_split_fin3`。
  * 本文件**没有**任何地方使用 `bbReachableVertices_iff_activeWalk` /
    `dSep_source_to_cond` / `bbZAncestors_mono_edge` 等长路径工具 ——
    这不是遗漏，而是**结论所需**：§3 的 `dSepOneHop` 已把全部
    Bayes-Ball 传递信息丢掉而结论不变。
  * 若将来需要 `dSep` 的**长路径**内容，用武之地不在 `Split`
    （深度 1 谓词），而在 `CondIndep` / `Factorizes` 的**全局**形式
    （例如 `MainTheoremC*` 系列需要对整条轨迹做 Markov 论证）。
  =========================================================================== -/

end SplitFromDSepComplete

end FateV2.Predict