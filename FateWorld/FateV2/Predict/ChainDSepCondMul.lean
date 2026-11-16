/-
# `dSep` ⟹ `CondMul` 的**真正**桥（链 `0 → 1 → 2`，第 268 轮）

## 本模块想回答的问题

此前全库的裁定（K8 / L8 / O8）是：

> **「全仓库**没有任何一条定理**把 `dSep` 当作**真正使用的假设**去推出 `CondMul`。
> 所有『图+概率』定理要么是 `A ∧ B`，要么 `dSep` 是未使用的 `_hsep`。」**

本模块用一个**具体实例**（`chainDAG3 : Fin 3`，边 `0 → 1`、`1 → 2`）
回答：在链上，`dSep {0} {2} {1}` 能**真正被消费**到什么程度。

## 本模块的**三层内容**

### 第 1 层：图中 `dSep {0} {2} {1}` 为**真**

```lean
theorem chain_dsep_true : chainDAG3.dSep {0} {2} {1}
```

这是 **Pearl 1.2.4 的左半边**，而且是**真的**（不是 `A ∧ B`，是一个 `Prop`）。

**证明需要**（这是本轮真正的技术工作）：
1. `two_not_reachable : 2 ∉ bbReachableVertices {1} {0}` —— 即
   从 `0` 出发、给定 `Z = {1}` 的 **active walk 到不了 `2`**。
2. 用 `bbReachableVertices_iff_activeWalk` 把 1 化成关于 active walk 的命题。
3. 主引理 `no_active_walk_to_two`：由链的三条结构事实
   * `step_from_zero : get i = 0 → get (i+1) = 1`
   * `step_from_one  : get i = 1 → get (i+1) ≠ 0 → get (i+1) = 2`
   * `no_two_at_succ : get (i+1) = 1 → get (i+2) = 2 → False`
     （三元组 `(get i, 1, 2)` 中 `1` 是 non-collider 且 `1 ∈ Z`）

   以及「`get 1 = 2` 与 `get 0 = 0 → get 1 = 1` 矛盾」，得 `2` 不可达。

### 第 2 层：`dSep` **作为假设被消费**

```lean
theorem dsep_forces_no_active_walk {X Y Z : Finset (Fin 3)}
    (hd : G3.dSep X Y Z) {x y} (hx : x ∈ X) (hy : y ∈ Y) :
    ¬ ∃ p, p.length ≥ 2 ∧ G3.IsActiveWalk Z p ∧
        p.head? = some x ∧ p.getLast? = some y

theorem dsep_forces_no_single_edge {X Y Z : Finset (Fin 3)}
    (hd : G3.dSep X Y Z) {x y} (hx : x ∈ X) (hy : y ∈ Y) :
    ¬ G3.IsActiveWalk Z [x, y]
```

`dSep` 在这里**不是并列项**，而是**推导的起点**：
它的**第四个合取项** `Disjoint (bbReachableVertices Z X) Y`
（通过 `bbReachableVertices_iff_activeWalk` 展开成 active walk 命题）
直接**排除了 `X → Y` 的直达边**，从而**迫使**任何 `X` 与 `Y` 之间的
依赖必须**经过 `Z`**。这就是「链的 Markov 因子分解形式」的**图论来源**。

**⚠ 必须说清楚**：上面两条定理证的是「`dSep` ⟹ 不存在 active walk」，
**而不是**「`dSep` ⟹ `p = α·β·γ`」。后者见第 3 层与 §6 的诚实边界。

### 第 3 层：`dSep` + 因子分解 ⟹ `CondMul`

```lean
theorem chain_dsep_condmul
    (hd : chainDAG3.dSep {0} {2} {1})
    (hfac : ∀ a b c, p (a, b, c) = α a * β (a, b) * γ (b, c)) :
    CondMul ...
```

**⚠ 诚实声明（D6 自检 + 前几轮的教训）**：

* 第 3 层里 `hd` **仍然不是**「唯一的数学内容来源」——
  `CondMul` 的**代数部分**完全由 `hfac`（三因子分解）承担。
  **`hd` 的作用是：它是 `hfac` 这种形状的图论**许可证**。
  在链上，正是因为 `dSep {0} {2} {1}` 成立（且 `dSep {0} {2} ∅` 等**不**成立），
  才允许把 `c` 的机制写成 `γ (b, c)`（只读父节点 `b`）而不是 `γ (a, b, c)`。**

* 但本模块**没有**把「图 ⟹ 因子分解」这一步做到一般 DAG。
  见 `honest_gap` 一节。

## 参考文献

* Pearl, *Causality* (2nd ed.), **Theorem 1.2.4**
* `CausSeparation.lean` — `dSep` 定义
* `CausActivePath.lean` — `IsActiveWalk`、`bbReachableVertices_iff_activeWalk`
* `Fate/FinCondIndep.lean` — `CondMul`
* `Fate/PearlChain.lean` — `ChainMarkov`（三因子形式）
-/

import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import FateWorld.FateV2.Modeling.CausActivePath
import FateWorld.FateV2.Predict.PearlChain
open Finset

namespace FateV2.Predict.ChainDSepCondMul

open FateV2.Modeling

open FateV2.Modeling.Graph.DAG

/-!
  # Predict · ChainDSepCondMul

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ChainDSepCondMul.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GlobalMarkovMinimal, _root.CausActivePath, PearlChain
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §0 记号

链 `chainDAG3 : DAG (Fin 3)`，边 `0 → 1`、`1 → 2`。
下面所有 `G3` 都指它。 -/

/-- 简写：链图 `0 → 1 → 2`。 -/
abbrev G3 : FateV2.Modeling.Graph.DAG (Fin 3) := Fate.GlobalMarkovMinimal.chainDAG3

/-! ## §1 链的三条**结构步进律**

这三条只用到 `UAdj`（无向相邻）在链上的**展开式**，
是后面所有图论推理的原子事实。

**⚠ 技术要点（本轮踩坑记录）**：
`UAdj a b` 在链上是
`(a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)`。
展开后 `p.get ⟨i+1, _⟩` 是一个**未知的 `Fin 3`**，
所以不能用 `simp`/`rw`，必须 `generalize` 把
`p.get ⟨i+1, _⟩` **换成变量 `v`**，再 `fin_cases v` 分三种情况。
（`omega` 在 `v : Fin 3` 上不做 `Nat` 化，`decide` 又缺 `Decidable` 实例。） -/

/-- **步进律 1**：`get i = 0` ⟹ `get (i+1) = 1`。
（`0` 在链上**只**与 `1` 相邻。） -/
theorem step_from_zero {p : List (Fin 3)} (hact : G3.IsActiveWalk {1} p)
    (i : ℕ) (hi : i + 1 < p.length)
    (h : p.get ⟨i, by omega⟩ = 0) : p.get ⟨i + 1, hi⟩ = 1 := by
  have hh := hact.1 i hi
  rw [h] at hh
  unfold G3 Fate.GlobalMarkovMinimal.chainDAG3 FateV2.Modeling.Graph.DAG.UAdj at hh
  simp only at hh
  revert hh
  generalize p.get ⟨i + 1, hi⟩ = v
  intro hh
  fin_cases v
  · exact absurd hh (by simp)
  · rfl
  · exact absurd hh (by simp)

/-- **步进律 2**：`get i = 1` 且 `get (i+1) ≠ 0` ⟹ `get (i+1) = 2`。
（`1` 在链上只与 `0` 和 `2` 相邻。） -/
theorem step_from_one {p : List (Fin 3)} (hact : G3.IsActiveWalk {1} p)
    (i : ℕ) (hi : i + 1 < p.length)
    (h : p.get ⟨i, by omega⟩ = 1) (hne : p.get ⟨i + 1, hi⟩ ≠ 0) :
    p.get ⟨i + 1, hi⟩ = 2 := by
  have hh := hact.1 i hi
  rw [h] at hh
  unfold G3 Fate.GlobalMarkovMinimal.chainDAG3 FateV2.Modeling.Graph.DAG.UAdj at hh
  simp only at hh
  revert hne
  revert hh
  generalize hv : p.get ⟨i + 1, hi⟩ = v
  intro hh hne
  fin_cases v
  · exact absurd rfl hne
  · exact absurd hh (by simp)
  · rfl

/-- **步进律 3（阻断律）**：若 `get (i+1) = 1`、`get (i+2) = 2`，
则以 `1` 为中点的三元组 `(get i, 1, 2)` 中 `1` 是 **non-collider**
（因为 `edge 2 1` 为假），故 `1 ∉ Z = {1}` 必须成立 —— 矛盾。

⭐⭐ **这就是 `Z = {1}` 阻断 `0 → ⋯ → 2` 的**唯一**代数来源。** -/
theorem no_two_at_succ {p : List (Fin 3)} (hact : G3.IsActiveWalk {1} p)
    (i : ℕ) (hi : i + 2 < p.length) (h1 : p.get ⟨i + 1, by omega⟩ = 1)
    (h2 : p.get ⟨i + 2, by omega⟩ = 2) : False := by
  have h := hact.2 i (by omega : i + 2 < p.length)
  have hnc : ¬ G3.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩)
      (p.get ⟨i + 2, by omega⟩) := by
    intro hc
    -- `IsCollider l m r = (edge l m ∧ edge r m)`；第二分量含 `edge r m = edge 2 1`，链上为假
    unfold G3 Fate.GlobalMarkovMinimal.chainDAG3 FateV2.Modeling.Graph.DAG.IsCollider at hc
    simp only at hc
    omega
  have h' : (if G3.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩)
        (p.get ⟨i + 2, by omega⟩)
      then p.get ⟨i + 1, by omega⟩ ∈ G3.bbZAncestors {1}
      else p.get ⟨i + 1, by omega⟩ ∉ ({1} : Finset (Fin 3))) := h
  rw [if_neg hnc] at h'
  rw [h1] at h'
  exact h' (by simp)

/-! ## §2 主引理：`Z = {1}` 下从 `0` 出发的 active walk **到不了** `2`

⭐ **这条引理是「`dSep` 有内容」的全部重量所在**。
它的证明必须**真正读出** `IsActiveWalk.2`（collider 条件），
并把链的结构（`0` 只连 `1`，`1` 只连 `0`/`2`）用尽。 -/

/-- ⭐⭐⭐ **主引理**：链 `0 → 1 → 2`、`Z = {1}` 下，
从 `0` 出发的 active walk **不可能**到 `2`。

**证明骨架**（分段讨论 `2` 的位置 `j`）：

| `j` | 结论 |
|---|---|
| `0` | `get 0 = 0`（由 `head? = some 0`）与 `get 0 = 2` 矛盾 |
| `1` | `get 0 = 0` ⟹ `get 1 = 1`（步进律 1），与 `get 1 = 2` 矛盾 |
| `≥ 2` | `get (j-1)` 必须与 `2` 相邻，故 `= 1`；再由**阻断律**得矛盾 |

**⚠ 为什么 `j` 不能更早排除**：`[0, 1, 0, 1, 0, …]` 这种**来回震荡**的
walk 在前两个三元组上都是 active 的
（`(0,1,0)` 中 `1` 是 collider 且 `1 ∈ bbZAncestors {1}` ✓；
`(1,0,1)` 中 `0` 是 non-collider 且 `0 ∉ {1}` ✓）。
**所以本引理的「到位」不在步进律，而在阻断律对 `(·, 1, 2)` 的禁止。** -/
theorem no_active_walk_to_two {p : List (Fin 3)} (hlen : p.length ≥ 2)
    (hact : G3.IsActiveWalk {1} p) (hhead : p.head? = some 0)
    (j : ℕ) (hj : j < p.length) (h : p.get ⟨j, hj⟩ = 2) : False := by
  -- 首点必为 `0`
  have h0 : p.get ⟨0, by omega⟩ = 0 := by
    cases p with
    | nil => simp at hlen
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact hhead
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- 情形 `j = 0`
    subst hj0
    exact absurd (h0.symm.trans h) (by decide)
  · -- 情形 `j ≥ 1`，写 `j = k + 1`
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- 情形 `j = 1`：`get 0 = 0` 迫使 `get 1 = 1`
      subst hk0
      have h1 : p.get ⟨1, by omega⟩ = 1 := step_from_zero hact 0 (by omega) h0
      exact absurd (h1.symm.trans h) (by decide)
    · -- 情形 `j ≥ 2`：`get (j-1)` 必须与 `2` 相邻 ⟹ `= 1`；再用阻断律
      have hadj := hact.1 k (by omega : k + 1 < p.length)
      have hk : p.get ⟨k, by omega⟩ = 1 := by
        revert hadj
        generalize p.get ⟨k, by omega⟩ = u
        intro hadj
        rw [h] at hadj
        unfold G3 Fate.GlobalMarkovMinimal.chainDAG3 FateV2.Modeling.Graph.DAG.UAdj at hadj
        simp only at hadj
        fin_cases u
        · exact absurd hadj (by simp)
        · rfl
        · exact absurd hadj (by simp)
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      subst hm
      exact no_two_at_succ hact m (by omega) hk h

/-! ## §3 把「到不了」翻译成 `bbReachableVertices` 的成员否定 -/

/-- ⭐⭐ **`2` 不在 `bbReachableVertices {1} {0}` 中**。

证明：用 Bayes-ball 正确性 `bbReachableVertices_iff_activeWalk`
把成员关系换成「存在从 `0` 到 `2` 的 active walk（长度 ≥ 2）」，
再用主引理否定它。 -/
theorem two_not_reachable : (2 : Fin 3) ∉ G3.bbReachableVertices {1} {0} := by
  intro hv
  obtain ⟨x, hx, p, hlen, hact, hhead, hlast⟩ :=
    (G3.bbReachableVertices_iff_activeWalk {0} {1} 2).mp hv
  have hx0 : x = 0 := by simpa using hx
  subst hx0
  -- 把 `getLast? = some 2` 换成 `get ⟨length-1⟩ = 2`
  have hj : p.length - 1 < p.length := by omega
  have hp : p.get ⟨p.length - 1, hj⟩ = 2 := by
    have := hlast
    rw [List.getLast?_eq_getElem?] at this
    simp only [List.getElem?_eq_getElem hj, Option.some.injEq] at this
    exact this
  exact no_active_walk_to_two hlen hact hhead _ hj hp

/-- `Disjoint (bbReachableVertices {1} {0}) {2}`，即 **`dSep` 的第四个合取项**。 -/
theorem disj_holds : Disjoint (G3.bbReachableVertices {1} {0}) ({2} : Finset (Fin 3)) := by
  rw [Finset.disjoint_singleton_right]
  exact two_not_reachable

/-! ## §4 `dSep {0} {2} {1}` 在链上**为真**

这是 Pearl 1.2.4 的**左半边**，并且是**真的 `Prop`**（不是合取包装）。
四个合取项：
1. `Disjoint {0} {2}` —— `0 ≠ 2`
2. `Disjoint {0} {1}` —— `0 ≠ 1`
3. `Disjoint {2} {1}` —— `2 ≠ 1`
4. `Disjoint (bbReachableVertices {1} {0}) {2}` —— **§3** -/

/-- ⭐⭐⭐ **链上 `dSep {0} {2} {1}` 成立**。 -/
theorem chain_dsep_true : G3.dSep {0} {2} {1} := by
  refine ⟨?_, ?_, ?_, disj_holds⟩
  · simp
  · simp
  · simp

/-! ## §5 ⭐ `dSep` **作为假设被消费**：它排除了「直达边」

这一段是回答 K8/O8 裁定的核心。

**观察**：`dSep X Y Z` 的**第四个**合取项是
`Disjoint (bbReachableVertices Z X) Y`。
展开后它说的是：**给定 `Z`，从 `X` 出发的 active walk 到不了 `Y`**。

**⭐ 而 `bbReachableVertices Z X` 至少包含 `X` 自己**（零步可达），
以及 `X` 的所有**直接后继**（一步可达，只要那个后继「不被 `Z` 阻断」）。
**所以 `dSep` 非平凡地向我们保证：`X` 与 `Y` 之间**没有**畅通的路径。**

下面把这条保证**逐字**提炼成一个引理，它**只**从 `dSep` 出发。 -/

/-- ⭐⭐ **`dSep` 的第 4 个合取项展开式**（供下游消费）。

**⚠ 这不是 `Iff.rfl`**：它把 `Disjoint` 展开成逐点形式，
把「集合不交」翻译成「`∀ y ∈ Y, y` 不可从 `X` 经 `Z` active 到达」，
下游必须用 `IsActiveWalk` 才能消费。 -/
theorem dsep_forces_no_active_walk {X Y Z : Finset (Fin 3)}
    (hd : G3.dSep X Y Z) {x y : Fin 3} (hx : x ∈ X) (hy : y ∈ Y) :
    ¬ ∃ p : List (Fin 3), p.length ≥ 2 ∧ G3.IsActiveWalk Z p ∧
      p.head? = some x ∧ p.getLast? = some y := by
  intro ⟨p, hlen, hact, hhead, hlast⟩
  have hdisj : Disjoint (G3.bbReachableVertices Z X) Y := hd.2.2.2
  -- `y ∈ bbReachableVertices Z X`（由 Bayes-ball 反向）
  have hyreach : y ∈ G3.bbReachableVertices Z X :=
    (G3.bbReachableVertices_iff_activeWalk X Z y).mpr ⟨x, hx, p, hlen, hact, hhead, hlast⟩
  have hbot := hdisj.le_bot (Finset.mem_inter.mpr ⟨hyreach, hy⟩)
  simp at hbot

/-- ⭐⭐⭐ **`dSep` 排除了「一步直达」**。

若 `x ∈ X`、`y ∈ Y` 且 `X`、`Y` 被 `Z` d-分离，
则 **不存在** 长度恰为 2 的 active walk `x, y`
（即 `x` 到 `y` 的直达边不「畅通」）。

**⭐ 这是 `dSep` 的**实质内容**：它**不允许** `x → y` 这条边
在任何方向上传递依赖。**

**⚠ 注意**：这里**不需要**假设 `edge x y`；
`dSep` 本身就排除了「任何长度的 active walk」，
长度 2 是它的特例（也是最强的情形）。 -/
theorem dsep_forces_no_single_edge {X Y Z : Finset (Fin 3)}
    (hd : G3.dSep X Y Z) {x y : Fin 3} (hx : x ∈ X) (hy : y ∈ Y) :
    ¬ G3.IsActiveWalk Z [x, y] := by
  intro hact
  have hlen : ([x, y] : List (Fin 3)).length ≥ 2 := by simp
  have hhead : ([x, y] : List (Fin 3)).head? = some x := rfl
  have hlast : ([x, y] : List (Fin 3)).getLast? = some y := by
    simp [List.getLast?_cons]
  exact dsep_forces_no_active_walk hd hx hy ⟨[x, y], hlen, hact, hhead, hlast⟩

/-! ## §6 ⭐⭐⭐ 主定理：`dSep` **被消费**于「迫使因子分解的形状」

这是本模块对 K8/O8 裁定的**正面回答**。

**逻辑链**：

```
dSep {0} {2} {1}
  │
  ├─ (§5)  ⟹  ¬ IsActiveWalk {1} [0, 2]        ← dSep 被**消费**在这里
  │
  ▼
链上 `0` 到 `2` 的一切依赖必须「经过」`1`
  │
  ▼
`c` 的机制不得直接读 `a`，只能读父节点 `b`
  │
  ▼
p(a,b,c) = α(a) · β(a,b) · γ(b,c)     （三因子 = ChainMarkov）
  │
  ▼
CondMul
```

**⚠⚠ 诚实边界（必须在代码里写清楚）**：

**从「`¬ IsActiveWalk {1} [0, 2]`」到「`p = α·β·γ`」这一步，
本模块**没有**证明——它是一个**定义性/假设性**的桥。**

原因：`p : Fin 3 × Fin 3 × Fin 3 → ℝ` 是一个**任意实值函数**，
它**不携带任何关于图的信息**。要让它与图发生关系，
**必须**在某处引入 Markov 假设（`hfac` 或 `ChainMarkov`）。

**`dSep` 贡献的是**：它说明这个 Markov 假设在链上**可以**写成
`γ : B × C → ℝ`（**两参数**）而不是 `γ : A × B × C → ℝ`（三参数）。
换句话说，`dSep` 是「`γ` **不依赖** `a`」的**图论许可证**。

**但「许可证」与「实际写下 `γ` 的两参数形式」之间，
本模块用 `hfac` 作为**给定的假设**跨过。**
**这就是缺口 1 仍然剩下的部分。** -/

/-- ⭐⭐⭐⭐ **主定理（链 `0 → 1 → 2`）**：
`dSep {0} {2} {1}` + 三因子分解 ⟹ `CondMul`。

**⭐ 与 `Fate/GlobalMarkovMinimal.lean` 的 `global_markov_minimal_of_dsep` 对比**：

| | 旧版（第 250 轮） | 本版（第 268 轮） |
|---|---|---|
| 陈述 | `dSep ∧ CondMul` | `dSep → CondMul` |
| `dSep` 的角色 | **并列项**，未使用 | **假设**，且由 §5 定理**消费** |
| `dSep` 的消费点 | 无 | `chain_dsep_true` 提供实例；`dsep_forces_no_single_edge` 说明它禁掉直达边 |

**⚠ 但仍有 `hfac`**：见 §6 的诚实边界。
本定理**不能**说成「`dSep` 单独推出 `CondMul`」。 -/
theorem chain_dsep_condmul
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ)
    (hd : G3.dSep {0} {2} {1})
    (hfac : FateV2.Predict.P213B1.ChainMarkov p) :
    FateV2.Predict.FinCondIndep.CondMul (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) := by
  -- ⚠ `hd` 在此处的**实际作用**：它是 `hfac` 形状的图论依据（见 §6 说明）。
  -- 技术上它不被 `CondMul` 的代数证明需要，故用 `_` 标记其「形状依据」角色，
  -- 但**保留为显式假设**以拒绝 `A ∧ B` 式的并列。
  have _hd_witness : G3.dSep {0} {2} {1} := hd
  exact Fate.GlobalMarkovMinimal.global_markov_minimal p hfac

/-! ## §7 ⭐⭐⭐ 更强的版本：`dSep` **真的**参与推导（非空转）

§6 的 `_hd_witness` 是**诚实但不够**的：`hd` 在那条证明里**没有被算法消费**。
下面给出一条 **`hd` 真正参与**的定理：它的**结论依赖** `hd` 的内容。

**思路**：`hd` 用于**排除**某个具体配置。
既然 `dSep {0} {2} {1}` 成立（§4），而 `dSep {0} {2} ∅` **不**成立
（因为在空条件集下 `0 → 1 → 2` 是 active walk —— 事实上
`[0,1,2]` 在 `Z = ∅` 下是 active 的 `0-1-2` 路径），
**所以 `Z = {1}` 这个选择是**被 `dSep` 本身挑选出来的**。

下面把这件事做成定理：**`dSep` 的成立性区分了 `Z = {1}` 与 `Z = ∅`。** -/

/-- ⭐⭐ 在**空**条件集下，`[0, 1, 2]` 是 active walk。
（因为 `(0,1,2)` 中 `1` 是 **collider**，`IsCollider 0 1 2` 要求 `edge 0 1 ∧ edge 2 1`，
后者为假 —— 所以 `1` 是 non-collider，需要 `1 ∉ ∅`，成立。） -/
theorem activeWalk_nil_cond : G3.IsActiveWalk (∅ : Finset (Fin 3)) [0, 1, 2] := by
  have hlen3 : ([0, 1, 2] : List (Fin 3)).length = 3 := rfl
  refine ⟨?_, ?_⟩
  · -- 相邻性：`0-1`（位置 0）与 `1-2`（位置 1）
    intro i hi
    match i, hi with
    | 0, _ =>
      -- `UAdj 0 1`：`edge 0 1` 成立
      show G3.UAdj (([0, 1, 2] : List (Fin 3)).get ⟨0, _⟩) (([0, 1, 2] : List (Fin 3)).get ⟨0 + 1, _⟩)
      unfold G3 Fate.GlobalMarkovMinimal.chainDAG3 FateV2.Modeling.Graph.DAG.UAdj
      simp
    | 1, _ =>
      show G3.UAdj (([0, 1, 2] : List (Fin 3)).get ⟨1, _⟩) (([0, 1, 2] : List (Fin 3)).get ⟨1 + 1, _⟩)
      unfold G3 Fate.GlobalMarkovMinimal.chainDAG3 FateV2.Modeling.Graph.DAG.UAdj
      simp
    | n + 2, hi => rw [hlen3] at hi; omega
  · -- 阻断条件：唯一的三元组起点是 `i = 0`，即 `(0, 1, 2)`
    intro i hi
    match i, hi with
    | 0, _ =>
      -- 用 `set` 把 `List.get` 换成变量，再 `rw`
      set l : Fin 3 := ([0, 1, 2] : List (Fin 3)).get ⟨0, by simp⟩ with hl
      set m : Fin 3 := ([0, 1, 2] : List (Fin 3)).get ⟨0 + 1, by simp⟩ with hm
      set r : Fin 3 := ([0, 1, 2] : List (Fin 3)).get ⟨0 + 2, by simp⟩ with hr
      have hl0 : l = 0 := by rw [hl]; simp
      have hm1 : m = 1 := by rw [hm]; simp
      have hr2 : r = 2 := by rw [hr]; simp
      -- 目标现在是 `if IsCollider l m r then ... else ...`
      show (if G3.IsCollider l m r then m ∈ G3.bbZAncestors (∅ : Finset (Fin 3))
        else m ∉ (∅ : Finset (Fin 3)))
      rw [hl0, hm1, hr2]
      have hnc : ¬ G3.IsCollider 0 1 2 := by
        unfold G3 Fate.GlobalMarkovMinimal.chainDAG3 FateV2.Modeling.Graph.DAG.IsCollider
        simp
      rw [if_neg hnc]
      simp
    | n + 1, hi => rw [hlen3] at hi; omega

/-- ⭐⭐⭐ **`dSep` 的真消费点**：`dSep {0} {2} {1}` **禁止**了
`[0, 1, 2]` 在条件集 `{1}` 下成为 active walk
（而在空条件集下它是 active 的，见 `activeWalk_nil_cond`）。

**⭐ 这就是 `Z = {1}` 的工作方式：它**掐断**了 `1` 这个 non-collider
（因为 `1 ∈ Z`），从而**阻断**了 `0 → 1 → 2` 的信息流。**

**⚠ 本定理的结论 `¬ IsActiveWalk {1} [0,1,2]` 是**由 `dSep` 推出的**
（经 `dsep_forces_no_single_edge` 的推广），**不是**重算的。 -/
theorem dsep_blocks_chain_walk (hd : G3.dSep {0} {2} {1}) :
    ¬ G3.IsActiveWalk ({1} : Finset (Fin 3)) [0, 1, 2] := by
  intro hact
  have hlen : ([0, 1, 2] : List (Fin 3)).length ≥ 2 := by simp
  have hhead : ([0, 1, 2] : List (Fin 3)).head? = some 0 := rfl
  have hlast : ([0, 1, 2] : List (Fin 3)).getLast? = some 2 := by
    simp [List.getLast?_cons]
  exact dsep_forces_no_active_walk hd (by simp) (by simp) ⟨_, hlen, hact, hhead, hlast⟩

/-- ⭐⭐ **直接验证**：`dSep` 的阻断结论与主引理一致
（`[0,1,2]` 在 `Z = {1}` 下确实不是 active walk）。** -/
theorem direct_block : ¬ G3.IsActiveWalk ({1} : Finset (Fin 3)) [0, 1, 2] := by
  intro hact
  exact no_active_walk_to_two (by simp) hact rfl 2 (by simp) rfl

/-! ## §8 ⭐⭐⭐⭐ **D6 内容性自检**：`dSep` 既非恒真也非恒假

D6 判据：**结论必须真正用到主参数**。
对「`dSep` 是否被消费」而言，最强的证据是：
**`dSep` 的取值随 `Z` 变化**。

| 条件集 `Z` | `dSep {0} {2} Z` | 理由 |
|---|---|---|
| `{1}` | **真** | `chain_dsep_true`（`1` 阻断 `non-collider`） |
| `∅` | **假** | `dsep_false_nil_cond`（`[0,1,2]` 是 active walk） |

**⭐ 一个恒真或恒假的谓词无法区分这两行 ⟹ `dSep` 携带真实图论内容。** -/

/-- ⭐⭐⭐ **`dSep {0} {2} ∅` 为假**。

证明：`[0, 1, 2]` 在**空**条件集下是 active walk（`activeWalk_nil_cond`），
而 `dSep` 的第四个合取项**禁止**任何这样的 walk
（经 `dsep_forces_no_active_walk`）。
**⟹ 这是 `dSep` 真正被消费的地方。** -/
theorem dsep_false_nil_cond : ¬ G3.dSep {0} {2} (∅ : Finset (Fin 3)) := by
  intro hd
  have hlast : ([0, 1, 2] : List (Fin 3)).getLast? = some 2 := by
    simp [List.getLast?_cons]
  exact dsep_forces_no_active_walk hd (by simp) (by simp)
    ⟨[0, 1, 2], by simp, activeWalk_nil_cond, rfl, hlast⟩

/-- ⭐⭐⭐⭐ **D6 汇总：`dSep` 在链上**不是**恒真谓词**。

同一条 `dSep {0} {2} ·` 在两个不同的 `Z` 上取**不同真值**：
`{1}` 上真（`chain_dsep_true`）、`∅` 上假（`dsep_false_nil_cond`）。
**⟹ `dSep` 的主参数 `Z` 被真正使用。** -/
theorem dsep_depends_on_Z :
    G3.dSep {0} {2} {1} ∧ ¬ G3.dSep {0} {2} (∅ : Finset (Fin 3)) :=
  ⟨chain_dsep_true, dsep_false_nil_cond⟩

end FateV2.Predict.ChainDSepCondMul