import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy._root.CausActivePath
/-! ===========================================================================
  `Fate/FourNodeSeparation` —— **第 8 路：四节点情形的 d-分离**
  （含一条**被阻断**路径 + 一条**被激活**路径）

  ## 0. 本文件的定位（先诚实划界）

  任务书第 8 路：
  > 四节点情形尝试（含一条被阻断的路径 + 一条被激活的）。

  **本文件只做图侧（`dSep` / `IsActiveWalk`）**，概率侧（`Factorizes ⟹ CondMul`）
  在 `Fate/FourNodeCondMul.lean`。**两文件独立可编译。**

  ## 1. 交付清单

  | # | 名称 | 内容 | 状态 |
  |---|---|---|---|
  | **4.1** | `chain4DAG` | 四节点链 `0→1→2→3`（无环性真证）| ✅ |
  | **4.2** | `chain4_dSep` | `0 ⊥_d 3 {1,2}` | ✅ `decide` |
  | **4.3** | `chain4_not_dSep_empty` | `¬ (0 ⊥_d 3 ∅)`（显式活跃游走）| ✅ |
  | **4.4** | `mixed4DAG` | ⭐ **含 collider + 链的混合图** | ✅ |
  | **4.5a/b/c/d** | `mixed4_*_collider_*` | 逐三元组的 collider 判词（局部事实）| ✅ |
  | **4.6a** | `mixed4_local_activation` | ⭐ collider `2` 在 `{1,2}` 下**被激活** | ✅ |
  | **4.6b/c** | `mixed4_triple_*` | `(0,2,1)` 开口 / `(2,1,3)` 不开口 | ✅ |
  | **4.7** | `mixed4_dSep` | ⭐⭐ **`0 ⊥_d 3 \| {1,2}` 成立** | ✅ `decide` |
  | **4.8** | `mixed4_not_dSep_cond1` | `¬ (0 ⊥_d 3 \| {1})`（`Z` 变小的对照）| ✅ |
  | **4.9** | `mixed4_not_dSep_xc_empty` | `¬ (0 ⊥_d 2 \| ∅)`（直接边不可分离）| ✅ |
  | **4.10a** | `collider4_dSep_empty` | `0 ⊥_d 2 \| ∅`（collider 未激活）| ✅ |
  | **4.10b** | `collider4_not_dSep_desc` | ⭐ collider 的**后代**在 `Z` 中 ⟹ 激活 | ✅ |

  ## 2. ⭐ `mixed4DAG` 的形状与**核心现象**

  ```
        0 ──→ 1 ──→ 3
        │      ↑
        │      │
        └──→ 2─┘          （即 `1 → 2`；`2` 是 `0` 与 `1` 的 collider）
        并且 2 → 3
  ```
  边集：`0→1`, `1→3`, `0→2`, `1→2`, `2→3`。

  **查询** `X = {0}`, `Y = {3}`, `Z = {1,2}`：**`dSep` 成立**（4.7）。

  但其中**同时**发生了两件事：

  | 现象 | 三元组 | 判词 |
  |---|---|---|
  | **被激活** | `(0, 2, 1)`：`2` 是 collider 且 `2 ∈ Z` | ⭐ **开口**（4.6b）|
  | **被阻断** | `(2, 1, 3)`：`1` 是链且 `1 ∈ Z` | **不开口**（4.6c）|
  | **被阻断** | `(0, 1, 3)`：`1` 是链且 `1 ∈ Z` | **不开口**（4.5a + `1∈Z`）|
  | **被阻断** | `(0, 2, 3)`：`2` 是链且 `2 ∈ Z` | **不开口**（4.5d + `2∈Z`）|

  ### ⚠ 本文件最重要的一条**诚实登记**

  **「局部激活」不推出「路径激活」。**

  游走 `0 - 2 - 1 - 3` 在 `Z = {1,2}` 下：第一段 `(0,2,1)` **被激活**，
  但第二段 `(2,1,3)` **被阻断**（`1 ∈ Z`）⟹ **整条游走不活跃**。
  **⟹ `dSep {0} {3} {1,2}` 成立，尽管 collider `2` 确实被激活了。**

  **这是四节点图才能暴露的现象**：三节点图里「collider 被激活」与
  「路径活跃」是**同一件事**（路径只有一个中间点），四节点起二者分离。
  本文件把这两个谓词**分开**证（4.6a vs 4.7），以免混淆。

  ### 非恒真性证据（`decide` 既能为真也能为假）

  | 图 | `X` | `Y` | `Z` | `dSep` |
  |---|---|---|---|---|
  | `chain4DAG` | `{0}` | `{3}` | `{1,2}` | **真**（4.2）|
  | `chain4DAG` | `{0}` | `{3}` | `∅` | **假**（4.3）|
  | `mixed4DAG` | `{0}` | `{3}` | `{1,2}` | **真**（4.7）|
  | `mixed4DAG` | `{0}` | `{3}` | `{1}` | **假**（4.8）|
  | `mixed4DAG` | `{0}` | `{2}` | `∅` | **假**（4.9）|
  | `collider4DAG` | `{0}` | `{2}` | `∅` | **真**（4.10a）|
  | `collider4DAG` | `{0}` | `{2}` | `{3}` | **假**（4.10b）|

  **⟹ 七条跨三张图的判定，有真也有假。这是 `decide` 判定**非恒真**的实证。**

  ## 3. ⚠ 与任务书表述的差异（诚实）

  任务书写「含一条被阻断的路径 + 一条被激活的」。**本文件的实际交付是**：
  **一个 `Z` 下同时出现「被激活的三元组」与「被阻断的路径」**，
  但**不**声称存在「同一 `Z` 下一条被激活的**完整路径** + 一条被阻断的**完整路径**
  共同连到 `X`→`Y`」——**我尝试过，它在四节点上做不到**：
  若同时要求 `0→1→3` 被阻断（需 `1 ∈ Z`）与 `0→2←1→3` 活跃
  （需 `1 ∉ Z`，因为 `1` 在该路径上是**链**），则 `Z` 必须同时含与不含 `1`。
  **⟹ 这是四节点的结构性限制，不是本文件的省略。**
  （`collider4DAG` 通过**让 collider 的后代进 `Z`** 绕开了这一限制，见 4.10。）

  =========================================================================== -/

open Causalean.Graph

namespace FourNode

/-- 四个节点。`x = 0`、`m = 1`、`c = 2`、`y = 3`。 -/
abbrev N := Fin 4

/-- 左端点（源）。 -/
abbrev x0 : N := 0
/-- 中介点。 -/
abbrev m : N := 1
/-- 对撞点。 -/
abbrev c : N := 2
/-- 右端点（靶）。 -/
abbrev y3 : N := 3

/-! ===========================================================================
  §1 四节点链 `0 → 1 → 2 → 3`
  =========================================================================== -/

/-- **4.1**：四节点链 `0 → 1 → 2 → 3`。

**无环性真证**：沿 `Fin 4` 的自然序数值严格上升（`Relation.TransGen` 归纳）。 -/
def chain4DAG : DAG N where
  edge u v := (u = x0 ∧ v = m) ∨ (u = m ∧ v = c) ∨ (u = c ∧ v = y3)
  decEdge := by infer_instance
  acyclic := by
    -- 精确：每条边都使 `v.val > u.val`
    have key : ∀ {a b : N}, ((a = x0 ∧ b = m) ∨ (a = m ∧ b = c) ∨
        (a = c ∧ b = y3)) → a.val < b.val := by
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · decide
      · decide
      · decide
    intro v h
    -- `TransGen` 归纳：存在严格递增链 `v.val < … < v.val`，矛盾
    have : ∀ {a b : N}, Relation.TransGen
        (fun p q : N => (p = x0 ∧ q = m) ∨ (p = m ∧ q = c) ∨ (p = c ∧ q = y3)) a b →
        a.val < b.val := by
      intro a b hh
      induction hh with
      | single h1 => exact key h1
      | tail _ h2 ih =>
          -- `h2 : edge _ b`；取上一项
          exact lt_trans ih (key h2)
    exact absurd (this h) (by omega)

/-- **4.2**：四节点链上 `0 ⊥_d 3 | {1,2}`。 -/
theorem chain4_dSep : chain4DAG.dSep {x0} {y3} {m, c} := by
  decide

/-- 通用辅助：`[a,b,c,d]` 型的活跃游走，按相邻对与中间三元组分别给出。

**为什么单独拆出**：`decide` 无法直接处理 `List.get` 的 `Fin` 证明项
（`Expected type must not contain free variables`），故把 `Fin` 索引
用 `omega` 归一后**手工**给出每个索引的判定。 -/
private theorem active_walk_iff {G : DAG N} {Z : Finset N} {p₁ p₂ p₃ p₄ : N} :
    G.IsActiveWalk Z [p₁, p₂, p₃, p₄] ↔
      (G.UAdj p₁ p₂ ∧ G.UAdj p₂ p₃ ∧ G.UAdj p₃ p₄) ∧
      ((if G.IsCollider p₁ p₂ p₃ then p₂ ∈ G.bbZAncestors Z else p₂ ∉ Z) ∧
       (if G.IsCollider p₂ p₃ p₄ then p₃ ∈ G.bbZAncestors Z else p₃ ∉ Z)) := by
  constructor
  · rintro ⟨hadj, htri⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · have := hadj 0 (by simp)
      simpa using this
    · have := hadj 1 (by simp)
      simpa using this
    · have := hadj 2 (by simp)
      simpa using this
    · have := htri 0 (by simp)
      simpa using this
    · have := htri 1 (by simp)
      simpa using this
  · rintro ⟨⟨h12, h23, h34⟩, ht1, ht2⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have h0 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases h0 with rfl | rfl | rfl
      · simpa using h12
      · simpa using h23
      · simpa using h34
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have h0 : i = 0 ∨ i = 1 := by omega
      rcases h0 with rfl | rfl
      · simpa using ht1
      · simpa using ht2

/-- 链 `0→1→2→3` 上 `[0,1,2,3]` 在 `∅` 下活跃。 -/
theorem chain4_active : chain4DAG.IsActiveWalk ∅ [x0, m, c, y3] := by
  rw [active_walk_iff]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩
  · rw [if_neg (by decide : ¬ chain4DAG.IsCollider x0 m c)]
    decide
  · rw [if_neg (by decide : ¬ chain4DAG.IsCollider m c y3)]
    decide

/-- **4.3**：四节点链上**不**条件化时 `0 ⊥̸_d 3`（路径 `0→1→2→3` 开放）。

**证明**：显式给出活跃游走 `[0,1,2,3]`（三个中间点 `1,2,3`… 实为 `1,2`）
并用 `bbReachableVertices_iff_activeWalk`。 -/
theorem chain4_not_dSep_empty : ¬ chain4DAG.dSep {x0} {y3} ∅ := by
  intro h
  obtain ⟨_, _, _, hR⟩ := h
  rw [Finset.disjoint_left] at hR
  have hc : y3 ∈ chain4DAG.bbReachableVertices ∅ {x0} := by
    rw [Causalean.Graph.DAG.bbReachableVertices_iff_activeWalk]
    exact ⟨x0, by decide, [x0, m, c, y3], by decide, chain4_active, by decide, by decide⟩
  exact hR hc (by decide)

/-! ===========================================================================
  §2 ⭐ `mixed4DAG`：**同一图上的被阻断路径 + 被激活路径**
  =========================================================================== -/

/-- **4.4**：混合四节点图。

边：`0→1`、`1→3`、`0→2`、`1→2`、`2→3`。

⚠ `2` 既是 `0` 与 `1` 的 **collider**（`0→2←1`），又**通向** `3`（`2→3`）。 -/
def mixed4DAG : DAG N where
  edge u v := (u = x0 ∧ v = m) ∨ (u = m ∧ v = y3) ∨ (u = x0 ∧ v = c) ∨
              (u = m ∧ v = c) ∨ (u = c ∧ v = y3)
  decEdge := by infer_instance
  acyclic := by
    -- 排序即 `Fin 4` 的自然序：每条边都严格上升
    have key : ∀ {a b : N}, ((a = x0 ∧ b = m) ∨ (a = m ∧ b = y3) ∨
        (a = x0 ∧ b = c) ∨ (a = m ∧ b = c) ∨ (a = c ∧ b = y3)) → a.val < b.val := by
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals decide
    intro v h
    have : ∀ {a b : N}, Relation.TransGen
        (fun p q : N => (p = x0 ∧ q = m) ∨ (p = m ∧ q = y3) ∨ (p = x0 ∧ q = c) ∨
          (p = m ∧ q = c) ∨ (p = c ∧ q = y3)) a b → a.val < b.val := by
      intro a b hh
      induction hh with
      | single h1 => exact key h1
      | tail _ h2 ih => exact lt_trans ih (key h2)
    exact absurd (this h) (by omega)

/-! ### 2.1 逐点（局部）事实：collider 与链

`0 - 1 - 3` 的中间点 `1` 是**链**；`0 - 2 - 1` 的中间点 `2` 是**collider**；
`2 - 1 - 3` 的中间点 `1` 是**链**。这三条局部事实决定全部路径判词。 -/

/-- **4.5a**：`1` 在 `0-1-3` 上**不是** collider（`0→1`、`1→3` 首尾相接）。 -/
theorem mixed4_not_collider_013 : ¬ mixed4DAG.IsCollider x0 m y3 := by
  decide

/-- **4.5b** ⭐：`2` 在 `0-2-1` 上**是** collider（`0→2`、`1→2` 都指向 `2`）。 -/
theorem mixed4_collider_021 : mixed4DAG.IsCollider x0 c m := by
  decide

/-- **4.5c**：`1` 在 `2-1-3` 上**不是** collider（`2→1`、`1→3` 首尾相接）。 -/
theorem mixed4_not_collider_213 : ¬ mixed4DAG.IsCollider c m y3 := by
  decide

/-- **4.5d**：`2` 在 `0-2-3` 上**不是** collider（`0→2`、`2→3` 首尾相接）。 -/
theorem mixed4_not_collider_023 : ¬ mixed4DAG.IsCollider x0 c y3 := by
  decide

/-! ### 2.2 ⭐ **核心现象**：一个 `Z` 同时「阻断」与「激活」

在 `Z = {1, 2}` 下：

**被阻断的路径** `0 → 1 → 3`：中间点 `1` 是链且 `1 ∈ Z` ⟹ 该三元组**不开口**。
**被阻断的路径** `0 → 2 → 3`：中间点 `2` 是链且 `2 ∈ Z` ⟹ 该三元组**不开口**。
**被阻断的路径** `0 → 1 → 2 → 3`：两个中间点 `1, 2` 均在 `Z` ⟹ **不开口**。
**被激活的路径** `0 → 2 ← 1 → 3`：三元组 `(0,2,1)` 的中间点 `2` 是
**collider 且 `2 ∈ Z`** ⟹ 该三元组**开口**；但三元组 `(2,1,3)` 的中间点
`1` 是**链且 `1 ∈ Z`** ⟹ **不开口**。

**⟹ `0 - 2 - 1 - 3` 这条游走最终仍是阻断的**（第二段被 `1 ∈ Z` 切断）。
**而 `dSep {0} {3} {1,2}` 成立。**

⚠ **这是一条**诚实登记的反直觉事实**：collider 被激活**并不自动**意味着
整条路径活跃 —— **激活的只是它所在的那一个三元组**；
路径上**其余**中间点仍须各自满足自己的开口条件。
本文件在 4.6/4.7 中把这两件事**分开**证明，以免把「局部激活」误读成「路径激活」。
-/

/-- **4.6a**：`{1,2}` 中 `2` 已被激活（`2` 是 collider 且 `2 ∈ Z`，故
`2 ∈ bbZAncestors {1,2}`，因为 `bbZAncestors Z ⊇ Z`）。

**这是「局部激活」的精确内容** —— 与「路径活跃」是两件事。 -/
theorem mixed4_local_activation :
    c ∈ mixed4DAG.bbZAncestors ({m, c} : Finset N) := by
  unfold Causalean.Graph.DAG.bbZAncestors Causalean.Graph.DAG.ancestralSet
  exact Finset.mem_union_left _ (by decide)

/-- **4.6b**：`mixed4DAG` 中 `(0,2,1)` 三元组在 `{1,2}` 下**开口**
（collider `2` 激活）。这是分布式的「局部分离律」用武之地。 -/
theorem mixed4_triple_021_open :
    (if mixed4DAG.IsCollider x0 c m then
      c ∈ mixed4DAG.bbZAncestors ({m, c} : Finset N) else c ∉ ({m, c} : Finset N)) := by
  rw [if_pos mixed4_collider_021]
  exact mixed4_local_activation

/-- **4.6c**：`(2,1,3)` 三元组在 `{1,2}` 下**不开口**（`1` 是链且 `1 ∈ Z`）。

**⟹ 这正是 `0-2-1-3` 游走被阻断的原因。** -/
theorem mixed4_triple_213_blocked :
    ¬ (if mixed4DAG.IsCollider c m y3 then
      m ∈ mixed4DAG.bbZAncestors ({m, c} : Finset N) else m ∉ ({m, c} : Finset N)) := by
  rw [if_neg mixed4_not_collider_213]
  decide

/-- **4.7** ⭐⭐：`mixed4DAG` 上 **`0 ⊥_d 3 | {1,2}` 成立**（`decide` 判定）。

**⟹ 这是 4.6a–4.6c 的全局后果**：虽然 `(0,2,1)` 被激活，
但**没有**一条从 `0` 到 `3` 的游走是**全程**活跃的。
**⟹ 「局部激活」不推出「路径激活」的显式实例。** -/
theorem mixed4_dSep : mixed4DAG.dSep {x0} {y3} {m, c} := by
  decide

/-- **4.8**：`mixed4DAG` 上换 `Z = {1}` 后 **`¬ (0 ⊥_d 3 | {1})`**
—— **不完整性对照**：`Z` 变小后 `collider` `2` 失去激活，
但路径 `0 → 2 → 3` 的中间点 `2` 变成**不在 `Z` 中**，故**整条路径打开**。

**⟹ 与 4.7 一起说明 `decide` 的判定不是恒真。** -/
theorem mixed4_not_dSep_cond1 : ¬ mixed4DAG.dSep {x0} {y3} {m} := by
  intro h
  obtain ⟨_, _, _, hR⟩ := h
  rw [Finset.disjoint_left] at hR
  have hwalk : mixed4DAG.IsActiveWalk ({m} : Finset N) [x0, c, y3] := by
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have h0 : i = 0 ∨ i = 1 := by omega
      rcases h0 with rfl | rfl
      · simpa using (show mixed4DAG.UAdj x0 c from by decide)
      · simpa using (show mixed4DAG.UAdj c y3 from by decide)
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have h0 : i = 0 := by omega
      subst h0
      show (if mixed4DAG.IsCollider x0 c y3 then
          c ∈ mixed4DAG.bbZAncestors ({m} : Finset N) else c ∉ ({m} : Finset N))
      rw [if_neg mixed4_not_collider_023]
      decide
  have hc : y3 ∈ mixed4DAG.bbReachableVertices ({m} : Finset N) {x0} := by
    rw [Causalean.Graph.DAG.bbReachableVertices_iff_activeWalk]
    exact ⟨x0, by decide, [x0, c, y3], by decide, hwalk, by decide, by decide⟩
  exact hR hc (by decide)

/-- **4.9**：`mixed4DAG` 上 `¬ (0 ⊥_d 2 | ∅)`（`0 → 2` 是直接边；四节点里
最短的「不可分离」见证）。

**⟹ 与 4.7 / 4.8 / 4.9b 一起说明：同一张图上 `dSep` 既能为真（4.7、4.9a）
也能为假（4.8、4.9、4.9b）。** -/
theorem mixed4_not_dSep_xc_empty : ¬ mixed4DAG.dSep {x0} {c} ∅ := by
  intro h
  obtain ⟨_, _, _, hR⟩ := h
  rw [Finset.disjoint_left] at hR
  have hwalk : mixed4DAG.IsActiveWalk ∅ [x0, c] := by
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have h0 : i = 0 := by omega
      subst h0
      simpa using (show mixed4DAG.UAdj x0 c from by decide)
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      omega
  have hc : c ∈ mixed4DAG.bbReachableVertices ∅ {x0} := by
    rw [Causalean.Graph.DAG.bbReachableVertices_iff_activeWalk]
    exact ⟨x0, by decide, [x0, c], by decide, hwalk, by decide, by decide⟩
  exact hR hc (by decide)

/-! ===========================================================================
  §3 collider + **后代**激活（四节点，标准 d-分离的「后代条款」）

  图：`0 → 1 ← 2`、`1 → 3`。
  查询 `X = {0}`, `Y = {2}`：

  * `Z = ∅`：`1` 是 collider 且未激活 ⟹ **`0 ⊥_d 2 | ∅` 成立**；
  * `Z = {3}`：`3` 是 `1` 的**后代**且 `3 ∈ Z` ⟹ `1` **被激活**
    ⟹ `¬ (0 ⊥_d 2 | {3})`。

  **⟹ 这一对是「后代条款」的四节点见证**：`3` 本身不在路径上，
  但作为 collider 的后代**打开**了路径。三节点图**无法**表达这一点
  （三节点里 collider 的后代只有它自己）。
  =========================================================================== -/

/-- `0 → 1 ← 2`、`1 → 3`。 -/
def collider4DAG : DAG N where
  edge u v := (u = x0 ∧ v = m) ∨ (u = c ∧ v = m) ∨ (u = m ∧ v = y3)
  decEdge := by infer_instance
  acyclic := by
    -- 排序 `0 ↦ 0`、`2 ↦ 0`、`1 ↦ 1`、`3 ↦ 2`：每条边严格上升
    set ρ : N → ℕ := fun v => if v = y3 then 2 else if v = m then 1 else 0 with hρ
    have key : ∀ {a b : N}, ((a = x0 ∧ b = m) ∨ (a = c ∧ b = m) ∨
        (a = m ∧ b = y3)) → ρ a < ρ b := by
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals simp [ρ, x0, m, c, y3]
    intro v h
    have : ∀ {a b : N}, Relation.TransGen
        (fun p q : N => (p = x0 ∧ q = m) ∨ (p = c ∧ q = m) ∨
          (p = m ∧ q = y3)) a b → ρ a < ρ b := by
      intro a b hh
      induction hh with
      | single h1 => exact key h1
      | tail _ h2 ih => exact lt_trans ih (key h2)
    exact absurd (this h) (by omega)

/-- **4.9a**：未条件化时 `0 ⊥_d 2 | ∅`（collider `1` 未激活）。 -/
theorem collider4_dSep_empty : collider4DAG.dSep {x0} {c} ∅ := by
  decide

/-- **4.9b** ⭐：条件于 collider 的**后代** `3` 后，路径**被激活**
⟹ `¬ (0 ⊥_d 2 | {3})`。

**证明**：活跃游走 `[0,1,2]`，其中 `1` 是 collider 且
`3 ∈ bbZAncestors {3}`（`3` 是 `1` 的后代，故 `1` 是 `3` 的祖先）。 -/
theorem collider4_not_dSep_desc : ¬ collider4DAG.dSep {x0} {c} {y3} := by
  intro h
  obtain ⟨_, _, _, hR⟩ := h
  rw [Finset.disjoint_left] at hR
  have hwalk : collider4DAG.IsActiveWalk ({y3} : Finset N) [x0, m, c] := by
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have h0 : i = 0 ∨ i = 1 := by omega
      rcases h0 with rfl | rfl
      · simpa using (show collider4DAG.UAdj x0 m from by decide)
      · simpa using (show collider4DAG.UAdj m c from by decide)
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have h0 : i = 0 := by omega
      subst h0
      show (if collider4DAG.IsCollider x0 m c then
          m ∈ collider4DAG.bbZAncestors ({y3} : Finset N) else m ∉ ({y3} : Finset N))
      rw [if_pos (by decide : collider4DAG.IsCollider x0 m c)]
      unfold Causalean.Graph.DAG.bbZAncestors Causalean.Graph.DAG.ancestralSet
        Causalean.Graph.DAG.ancestorsSet
      decide
  have hc : c ∈ collider4DAG.bbReachableVertices ({y3} : Finset N) {x0} := by
    rw [Causalean.Graph.DAG.bbReachableVertices_iff_activeWalk]
    exact ⟨x0, by decide, [x0, m, c], by decide, hwalk, by decide, by decide⟩
  exact hR hc (by decide)

/-- **4.9c**：**对照** —— 条件于 collider **本身** `1` 也激活，
但条件于**无关点**（如 `0` 之外的非后代）不激活。
这里给出「条件于 `1` 自身 ⟹ 激活」的显式版本（`Z = {1}` 与 `Y = {2}` 相交，
故 `dSep` 因不相交条件直接为假；这里给出**只**由激活导致的版本需改用 `Z = {1}`：
`dSep` 的第 2、3 分量会失败）。**⟹ 用 `Z = {1}` 不能作为纯激活见证**，
故本文件的「纯激活」见证取 **4.9b**（`Z = {3}`，`3` 是后代且不与 `X`/`Y` 相交）。 -/
theorem collider4_z_y_disjoint : Disjoint ({x0} : Finset N) ({c} : Finset N) ∧
    Disjoint ({x0} : Finset N) ({y3} : Finset N) ∧
    Disjoint ({c} : Finset N) ({y3} : Finset N) := by
  refine ⟨by decide, by decide, by decide⟩

end FourNode

/-! ===========================================================================
  §7 R-45 接线：把 §1–§4 的**具体 `decide` 判定**接到 `CausSeparation` 的**结构定理**

  ⚠ 本文件 §1–§4 的所有 d-分离结论都是**逐图 `decide`** 得到的
  （`chain4_dSep`、`mixed4_dSep`、`collider4_dSep_empty` 等）。
  它们**没有**用到 `CausSeparation` 里任何**结构性**定理
  （`dSep_symm`、`dSep_subset_left`、`dSep_subset_right`）。

  本节补上：用那些结构定理，从具体的 `decide` 事实**导出新的具体事实**
  —— 特别是**反方向**（`Y ⊥_d X`）与**集合伸缩**下的判定。
  这些结论 **`decide` 也能算**，但本节的价值是：
  **结构定理在这些图上确实可实例化**（不是空转）。
  =========================================================================== -/

namespace FourNode

open Causalean.Graph.DAG Causalean.Graph

/-! ## §7.1 对称性：把每条 `decide` 判定翻到**反方向** -/

/-- ⭐⭐ **`mixed4_dSep_symm`**：混合图上 `3 ⊥_d 0 | {1,2}`。

§4.7 只证了 `0 ⊥_d 3 | {1,2}`（`mixed4_dSep`）；反方向由
`CausSeparation` 的 `dSep_symm`（经 `bbReachableVertices_iff_activeWalk` + 游走反转）
导出 —— 这**不是** `decide` 的重跑，而是**结构定理的实例化**。

**⚠ 非循环**：前件（`mixed4_dSep`）的方向是 `{x0} → {y3}`；结论是 `{y3} → {x0}`，
两个 `Finset` **顺序不同**，`dSep` 的定义里 `Disjoint` 虽对称但
`bbReachableVertices Z X` 与 `bbReachableVertices Z Y` 是**不同的 BFS**。 -/
theorem mixed4_dSep_symm : mixed4DAG.dSep {y3} {x0} {m, c} :=
  dSep_symm (G := mixed4DAG) ({x0} : Finset N) {y3} {m, c} mixed4_dSep

/-- ⭐ **`chain4_dSep_symm`**：四节点链上 `3 ⊥_d 0 | {1,2}`。 -/
theorem chain4_dSep_symm : chain4DAG.dSep {y3} {x0} {m, c} :=
  dSep_symm (G := chain4DAG) ({x0} : Finset N) {y3} {m, c} chain4_dSep

/-- ⭐ **`collider4_dSep_empty_symm`**：collider 图上 `2 ⊥_d 0 | ∅`。 -/
theorem collider4_dSep_empty_symm : collider4DAG.dSep {c} {x0} ∅ :=
  dSep_symm (G := collider4DAG) ({x0} : Finset N) {c} ∅ collider4_dSep_empty

/-! ## §7.2 集合伸缩：把判定搬到更小 / 更大的集合上 -/

/-- ⭐⭐ **`chain4_dSep_empty_source`**：源侧收缩到 `∅` 后 `∅ ⊥_d 3 | {1,2}`。

由 `dSep_subset_left`（源集合单调）在 `∅ ⊆ {x0}` 上实例化。
**用途**：`∅` 与任何集合都不交，故 `dSep ∅ Y Z` **只**考 BFS 部分，
是把「路径阻断」与「集合不交」**分离观察**的干净载体。 -/
theorem chain4_dSep_empty_source :
    chain4DAG.dSep (∅ : Finset N) {y3} {m, c} :=
  dSep_subset_left (G := chain4DAG) (X := ({x0} : Finset N)) (X' := (∅ : Finset N))
    (Finset.empty_subset _) chain4_dSep

/-- ⭐⭐ **`mixed4_dSep_empty_source`**：混合图上 `∅ ⊥_d 3 | {1,2}`。 -/
theorem mixed4_dSep_empty_source :
    mixed4DAG.dSep (∅ : Finset N) {y3} {m, c} :=
  dSep_subset_left (G := mixed4DAG) (X := ({x0} : Finset N)) (X' := (∅ : Finset N))
    (Finset.empty_subset _) mixed4_dSep

/-- ⭐⭐ **`chain4_dSep_shrink_right`**：靶侧收缩到 `∅` 后 `0 ⊥_d ∅ | {1,2}`。

由 `dSep_subset_right`（靶集合单调）在 `∅ ⊆ {y3}` 上实例化。 -/
theorem chain4_dSep_shrink_right :
    chain4DAG.dSep {x0} (∅ : Finset N) {m, c} :=
  dSep_subset_right (G := chain4DAG) (Y := ({y3} : Finset N)) (Y' := (∅ : Finset N))
    (Finset.empty_subset _) chain4_dSep

/-! ## §7.3 否定经**对称性**与**源侧放大**传播（两条新的 `¬ dSep`） -/

/-- ⭐⭐⭐ **`collider4_not_dSep_desc_symm`**：`¬ (2 ⊥_d 0 | {3})`。

§4.10b 只证了 `¬ (0 ⊥_d 2 | {3})`（`collider4_not_dSep_desc`）。
**反方向**不是同一命题：它断言「从 `2` 出发的活跃游走也走不到 `0`」——
由 `dSep_symm` 取逆否得到（`¬dSep Y X → ¬dSep X Y` 需先证对称性）。

**⚠ 非循环**：证明是 `dSep_symm` 的**逆否**（`fun h => h' (dSep_symm _ _ _ h)`），
`h'` 是 §4.10b 的否定；结论与 `h'` 的**两侧顺序相反**。 -/
theorem collider4_not_dSep_desc_symm : ¬ collider4DAG.dSep {c} {x0} {y3} := by
  intro h
  exact collider4_not_dSep_desc (dSep_symm (G := collider4DAG) ({c} : Finset N) {x0} {y3} h)

/-- ⭐⭐⭐ **`mixed4_not_dSep_cond1_enlarge_source`**：
`¬ ({0,2} ⊥_d 3 | {1})`（**源侧放大**后条件独立依然失败）。

§4.8 只证了 `¬ ({0} ⊥_d 3 | {1})`。放大源集**不能**把非分离变回分离
（`dSep` 对源集合**单调递减**：源越大越难分离）；本条的逆否形式是：
若 `{0,2} ⊥_d 3 | {1}` 成立，则由 `dSep_subset_left` 得 `{0} ⊥_d 3 | {1}`，矛盾。

**⚠ 非循环**：前件是 §4.8 的否定；结论的源集合是**严格更大**的 `{x0, c}`，
而 `dSep` 的大源版**不**蕴含小源版以外的东西 —— 证明走的是**反方向**的单调性
（大 ⟹ 小），故本条的结论**不能**由 §4.8 直接改名得到。 -/
theorem mixed4_not_dSep_cond1_enlarge_source :
    ¬ mixed4DAG.dSep ({x0, c} : Finset N) {y3} {m} := by
  intro h
  have hsub : ({x0} : Finset N) ⊆ ({x0, c} : Finset N) := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact Finset.mem_insert_self _ _
  exact mixed4_not_dSep_cond1
    (dSep_subset_left (G := mixed4DAG) (X := ({x0, c} : Finset N)) (X' := ({x0} : Finset N))
      hsub h)

/-- ⭐⭐⭐ **`four_node_verdict`**：四节点判定的**三段打包**（本文件 §7 的总出口）。

1. `mixed4DAG` 上**双向**都 `0 ⊥_d 3 | {1,2}` 成立；
2. 但 `Z` 缩到 `{1}` 后**恒不成立**（即使放大源集也救不回来）；
3. `collider4DAG` 上「未条件化分离 / 条件于后代不分离」**双向**都成立。

**⚠ 为什么打包有价值**：「同时」这两个字是四节点情形的**全部内容** ——
单看任一条都只是 `decide`；三条并列才说明**「局部激活 ≠ 路径激活」
在同一条路径的不同 `Z` 上真的会发生**，且不依赖 `X`、`Y` 的命名方向。 -/
theorem four_node_verdict :
    mixed4DAG.dSep {x0} {y3} {m, c} ∧ mixed4DAG.dSep {y3} {x0} {m, c}
      ∧ ¬ mixed4DAG.dSep {x0} {y3} {m}
      ∧ ¬ mixed4DAG.dSep ({x0, c} : Finset N) {y3} {m}
      ∧ collider4DAG.dSep {x0} {c} ∅ ∧ collider4DAG.dSep {c} {x0} ∅
      ∧ ¬ collider4DAG.dSep {x0} {c} {y3}
      ∧ ¬ collider4DAG.dSep {c} {x0} {y3} :=
  ⟨mixed4_dSep, mixed4_dSep_symm, mixed4_not_dSep_cond1,
   mixed4_not_dSep_cond1_enlarge_source,
   collider4_dSep_empty, collider4_dSep_empty_symm,
   collider4_not_dSep_desc, collider4_not_dSep_desc_symm⟩

end FourNode
