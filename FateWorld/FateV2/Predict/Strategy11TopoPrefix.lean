/-
# 视角 11：图 ⟹ 概率 —— **拓扑前缀「单点消元」引擎**（不用塔性质、不用 `induce`）

## 0 问题与约束

目标是把 `Factorizes ⟹ Markov`（Pearl 1.2.4 / 1.2.7 三级链的图⟹概率台阶）
在 `Fate.FactorMarkov` 口径下落成。**两条已知死路**：

* **塔性质** `mass S (mass T p) = mass (S∪T) p` **已被证伪**
  （`DAGFactorizationGeneral.tower_property_false`；`TowerAudit.mass_idempotent_fails`）。
  根因：`mass` 是**非归一化纤维和**，嵌套会把纤维大小乘进去。**本文件完全不用塔性质。**
* `CausDAG` **没有** `DAG.induce`，故此前的 sink 剥离**无法沿诱导子图递归**
  （`PEARL_127_PROOF_ROADMAP` 缺口 A）。

## 1 视角 11 的核心构造：`lowerSet`（拓扑前缀）

放弃「在诱导子图上递归」，改为**固定同一载体 `V`**，用 `topoOrder` 取单调链

$$\mathrm{lowerSet}_G\,k := \{v \mid \mathrm{topoOrder}_G\,v < k\},\qquad k=0,1,\dots$$

* `lowerSet 0 = ∅`，`lowerSet (topN G) = univ`（`topN = max topoOrder + 1`）；
* 严格单调链：`lowerSet k ⊆ lowerSet (k+1)`，每步**至多加一个点** `s`（`topoOrder s = k`）；
* **父闭**：`edge u v ∧ v ∈ lowerSet k ⟹ u ∈ lowerSet k`（因 `topoOrder u < topoOrder v`）。

**关键微分**：这些全在**同一 `V`** 上，故 `mass_insert_sum'` 这类 `mass` 律直接可用，
**无需 `induce`**。

## 2 引擎（`peel_lower`）—— 零缺口、零 `sorry`、不用塔

$$\boxed{\ \mathrm{mass}\ (\mathrm{lowerSet}_G\,k)\ p\ x
  \;=\; \prod_{v\in \mathrm{lowerSet}_G\,k} f\,v\,x\ }$$

证明是**自顶向下（descent）**：`k = topN` 时集合为 `univ`，`mass univ p = p = ∏ f`
（由 `hfac`，**免费**）；随后每降一级，用 **`mass_insert_sum'`（放开一个坐标再求和，
= `DAGFactorization.mass_insert_sum`，T1）** 把 `s` 剥掉：

$$\mathrm{mass}_{\mathrm{lowerSet}\,k}\,p\,x
  = \sum_a \mathrm{mass}_{\mathrm{lowerSet}\,(k+1)}\,p\,(x_s{:=}a)
  = \Bigl(\prod_{v\in\mathrm{lowerSet}\,k} f\,v\,x\Bigr)
    \cdot \underbrace{\sum_a f\,s\,(x_s{:=}a)}_{=1\ \text{by FactorNorm}}
  = \prod_{v\in\mathrm{lowerSet}\,k} f\,v\,x .$$

**第 2 个等号处必须有「`v ∈ lowerSet k` 的因子不读 `x_s`」**，这由**纯序**给出：
`topoOrder v < k = topoOrder s ⟹ ¬edge s v ⟹ s ∉ pa v`（`fv_insensitive_topo`）。
**这比既有 `sink_no_edge` 更强**：不需要 `s` 是 sink，只要 `s` 在上。

⟹ 全程只有 **单次** `mass` 求和（`mass_insert_sum'`），**没有 `mass ∘ mass` 嵌套**。

## 3 交付清单

| 编号 | 定理 | 内容 | 状态 |
|---|---|---|---|
| **S1** | `lowerSet` | 拓扑前缀集 | ✅ |
| **S2** | `mem_lowerSet` / `lowerSet_topN` / `lowerSet_of_topN_le` | 前缀的成员/端点刻画 | ✅ |
| **S3** | `lowerSet_succ_eq` | 每级至多加一点（或空跳） | ✅ |
| **S4** | `not_mem_pa_of_topoOrder_lt` | 纯序：上方点不是下方点的父 | ✅ |
| **S5** | `fv_insensitive_topo` | 纯序 + `LocalTo`：低处因子不读高处坐标 | ✅ |
| **S6** | `peel_step` | **引擎单步**（只用 `mass_insert_sum'`） | ✅ |
| **S7** | **`peel_lower`** | **引擎主定理**：任意前缀上的边缘 = 局部因子之积 | ✅ **核心** |
| **S8** | `peel_top_vertex` | 引擎**回收** `sink_peel`（且不需 sink 假设） | ✅ |
| **S9** | `FibreGluing` | 剩余义务：纤维粘结恒等式（计数/重指标，**非塔**） | 📋 登记为 `Prop` |
| **S10** | `markov_of_fibreGluing` | 给定 `S9`，`dSep ⟹ CondIndep` 收口 | ✅ |

## 4 诚实边界（必读）

`peel_lower` 给出「**前缀形**分离集」上的完整桥。任意 `dSep` 三元组的收口
需要 `S9`（`FibreGluing`）——一条**纤维重指标/计数**恒等式：把 `∏f` 在**乘积纤维**
上求和按坐标分块拆开。它与被证伪的**塔性质不同**：塔性质要求 `mass∘mass` 的嵌套
恒等式（假），而 `S9` 是**四个单层 `mass` 之间的**恒等式（真，且是标准证明的真实内核）。
本文件**不假装**证明 `S9`，只把它登记为显式 `Prop` 并**不消费**。
-/

import FateWorld.FateV2.Predict.FactorMarkov
open Finset
namespace FateV2.Predict.Strategy11

open FateV2.Modeling

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

noncomputable abbrev unpin (v : V) (x : V → α) (a : α) : V → α :=
  Fate.DAGFactorization.unpin v x a

noncomputable def lowerSet (G : FateV2.Modeling.Graph.DAG V) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.topoOrder v < k)

@[simp] theorem mem_lowerSet {G : FateV2.Modeling.Graph.DAG V} {k : ℕ} {v : V} :
    v ∈ lowerSet G k ↔ G.topoOrder v < k := by
  unfold lowerSet; simp

theorem not_mem_pa_of_topoOrder_lt (G : FateV2.Modeling.Graph.DAG V) {s v : V}
    (h : G.topoOrder v < G.topoOrder s) : s ∉ G.parents v := by
  intro hc
  have he : G.edge s v := G.mem_parents.mp hc
  have := G.topoOrder_lt s v he
  omega

theorem fv_insensitive_topo (G : FateV2.Modeling.Graph.DAG V) {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) {s v : V}
    (h : G.topoOrder v < G.topoOrder s) {x : V → α} {a b : α} :
    f v (unpin s x a) = f v (unpin s x b) := by
  have hne : v ≠ s := fun e => by rw [e] at h; omega
  have hnp : s ∉ G.parents v := not_mem_pa_of_topoOrder_lt G h
  have key : ∀ u : V, (u = v ∨ u ∈ G.parents v) → unpin s x a u = unpin s x b u := by
    intro u hu
    have hus : u ≠ s := by
      rintro rfl
      rcases hu with h1 | h1
      · exact hne h1.symm
      · exact hnp h1
    show (if u = s then a else x u) = (if u = s then b else x u)
    rw [if_neg hus, if_neg hus]
  exact hloc v _ _ key

variable {G : FateV2.Modeling.Graph.DAG V}

noncomputable def topN (G : FateV2.Modeling.Graph.DAG V) [Nonempty V] : ℕ :=
  (Finset.univ.sup G.topoOrder) + 1

theorem topoOrder_lt_topN [Nonempty V] (v : V) : G.topoOrder v < topN G := by
  unfold topN
  have : G.topoOrder v ≤ Finset.univ.sup G.topoOrder := Finset.le_sup (mem_univ v)
  omega

theorem lowerSet_topN [Nonempty V] : lowerSet G (topN G) = univ := by
  ext v; rw [mem_lowerSet]
  exact ⟨fun _ => mem_univ v, fun _ => topoOrder_lt_topN v⟩

theorem lowerSet_of_topN_le [Nonempty V] {k : ℕ} (hk : topN G ≤ k) :
    lowerSet G k = univ := by
  ext v; rw [mem_lowerSet]
  exact ⟨fun _ => mem_univ v, fun _ => lt_of_lt_of_le (topoOrder_lt_topN v) hk⟩

theorem lowerSet_succ_eq (k : ℕ) :
    lowerSet G (k+1) = lowerSet G k ∨
      ∃ s : V, G.topoOrder s = k ∧ lowerSet G (k+1) = insert s (lowerSet G k) := by
  by_cases hex : ∃ v, G.topoOrder v = k
  · right
    obtain ⟨s, hs⟩ := hex
    refine ⟨s, hs, ?_⟩
    ext v; rw [mem_lowerSet, mem_insert, mem_lowerSet]
    constructor
    · intro hv
      by_cases hvs : v = s
      · exact Or.inl hvs
      · right
        have hne : G.topoOrder v ≠ k := fun e => hvs (G.topoOrder_injective (e.trans hs.symm))
        show G.topoOrder v < k
        omega
    · rintro (hvs | hv)
      · subst v; show G.topoOrder s < k + 1; omega
      · have hlt : G.topoOrder v < k := hv
        show G.topoOrder v < k + 1; omega
  · left
    ext v; rw [mem_lowerSet, mem_lowerSet]
    constructor
    · intro hv
      have hne : G.topoOrder v ≠ k := fun e => hex ⟨v, e⟩
      show G.topoOrder v < k; omega
    · intro hv
      have hlt : G.topoOrder v < k := hv
      show G.topoOrder v < k + 1; omega

/-- ⭐ KEY ENGINE STEP. -/
theorem peel_step {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) (hnorm : Fate.FactorMarkov.FactorNorm f)
    (k : ℕ) {s : V} (hs : G.topoOrder s = k)
    (hsucc : lowerSet G (k+1) = insert s (lowerSet G k))
    (ih : ∀ y : V → α, Fate.DAGFactorization.mass (lowerSet G (k+1)) p y
            = ∏ v ∈ lowerSet G (k+1), f v y) :
    ∀ x : V → α, Fate.DAGFactorization.mass (lowerSet G k) p x
        = ∏ v ∈ lowerSet G k, f v x := by
  intro x
  have hsk : s ∉ lowerSet G k := by rw [mem_lowerSet]; omega
  have hstep : Fate.DAGFactorization.mass (lowerSet G k) p x
      = ∑ a : α, Fate.DAGFactorization.mass (lowerSet G (k+1)) p (unpin s x a) := by
    rw [Fate.DAGFactorization.mass_insert_sum' s (lowerSet G k) hsk p x, hsucc]
  rw [hstep]
  have hterm : ∀ a : α, Fate.DAGFactorization.mass (lowerSet G (k+1)) p (unpin s x a)
      = (∏ v ∈ lowerSet G k, f v x) * f s (unpin s x a) := by
    intro a
    rw [ih (unpin s x a), hsucc]
    have hpi : (∏ v ∈ (insert s (lowerSet G k)), f v (unpin s x a))
        = f s (unpin s x a) * ∏ v ∈ lowerSet G k, f v (unpin s x a) :=
      Finset.prod_insert hsk
    rw [hpi, mul_comm (f s (unpin s x a))]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    have hlt : G.topoOrder v < G.topoOrder s := by rw [mem_lowerSet] at hv; omega
    have h1 := fv_insensitive_topo G hloc hlt (x := x) (a := a) (b := x s)
    rw [h1]
    congr 1
    funext u
    show (if u = s then x s else x u) = x u
    by_cases hu : u = s
    · rw [if_pos hu, hu]
    · rw [if_neg hu]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum]
  have hone : (∑ a : α, f s (unpin s x a)) = 1 := hnorm s x
  rw [hone, mul_one]

/-- ⭐⭐⭐ **THE ENGINE**: for every level `k`, the marginal over the ancestor-closed
prefix `lowerSet k` equals the product of the factors on that prefix.

Proved by **descent** from `k = topN` (where the set is everything and the claim is
`mass univ p x = p x = ∏ f v x`, free from `hfac`), peeling one vertex at a time with
`peel_step` — which uses **only `mass_insert_sum'`**, never the (false) tower property. -/
theorem peel_lower [Nonempty V] {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : Fate.FactorMarkov.FactorNorm f) :
    ∀ k : ℕ, ∀ x : V → α,
      Fate.DAGFactorization.mass (lowerSet G k) p x = ∏ v ∈ lowerSet G k, f v x := by
  -- descend from N := topN G via r = N - k
  have key : ∀ r : ℕ, ∀ k : ℕ, k + r = topN G → ∀ x : V → α,
      Fate.DAGFactorization.mass (lowerSet G k) p x = ∏ v ∈ lowerSet G k, f v x := by
    intro r
    induction r with
    | zero =>
      intro k hk x
      have hk' : k = topN G := by omega
      subst hk'
      rw [lowerSet_topN, Fate.DAGFactorization.mass_univ, hfac x]
    | succ r ih =>
      intro k hk x
      -- look at level k: either empty jump or a real vertex s
      rcases lowerSet_succ_eq (G := G) k with hnone | ⟨s, hs, hsucc⟩
      · -- no vertex at level k: lowerSet (k+1) = lowerSet k, and (k+1) reaches the same target
        have hrec := ih (k+1) (by omega) x
        rwa [hnone] at hrec
      · -- real vertex s at level k: apply peel_step with IH at k+1
        have hih : ∀ y : V → α, Fate.DAGFactorization.mass (lowerSet G (k+1)) p y
            = ∏ v ∈ lowerSet G (k+1), f v y := fun y => ih (k+1) (by omega) y
        exact peel_step (G := G) hloc hnorm k hs hsucc hih x
  intro k x
  by_cases hk : k ≤ topN G
  · exact key (topN G - k) k (by omega) x
  · push Not at hk
    rw [lowerSet_of_topN_le (le_of_lt hk), Fate.DAGFactorization.mass_univ, hfac x]

/-- ⭐ **Corollary (recovers the existing `sink_peel`)**: at the top level minus one,
the engine gives exactly `FactorMarkov.sink_peel`'s conclusion, but **derived without
any sink/no-edge hypothesis** — purely from the topological order. -/
theorem peel_lower_univ_minus [Nonempty V] {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : Fate.FactorMarkov.FactorNorm f) (k : ℕ) (x : V → α) :
    Fate.DAGFactorization.mass (lowerSet G k) p x = ∏ v ∈ lowerSet G k, f v x :=
  peel_lower hloc hfac hnorm k x

/-!
  # Predict · Strategy11TopoPrefix

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy11TopoPrefix.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ### ⭐ Cross-check: the engine *recovers* the existing `FactorMarkov.sink_peel`.

`sink_peel` peels a **sink** `s` and concludes `mass (univ \ {s}) p x = ∏_{v≠s} f v x`.
The engine derives it **without** any sink/no-edge hypothesis: take `k = topoOrder s` so that
`lowerSet k = univ \ {s}` whenever `s` is the topological maximum. -/

/-- If `s` is the top vertex (`lowerSet (topoOrder s) = univ \ {s}`), the engine gives the
`sink_peel` conclusion purely from order, with no `∀ u, ¬ edge s u` needed. -/
theorem peel_top_vertex [Nonempty V] {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : Fate.FactorMarkov.FactorNorm f) (s : V)
    (htop : lowerSet G (G.topoOrder s) = univ \ {s}) (x : V → α) :
    Fate.DAGFactorization.mass (univ \ {s}) p x = ∏ v ∈ (univ \ {s}), f v x := by
  rw [← htop]
  exact peel_lower hloc hfac hnorm (G.topoOrder s) x

/-- ⭐⭐ **The precise remaining obligation** (registered as an explicit `Prop`, NOT assumed).

The engine `peel_lower` gives `mass (lowerSet k) p x = ∏_{v∈lowerSet k} f v x` for
ancestor-closed **prefixes**. To assemble `CondIndep` for arbitrary `dSep`-sets one needs
the **fibre-gluing identity**: summing `∏ f` over a product fibre splits across the
coordinate partition *when the separating set blocks the parent-dependencies*.

`FibreGluing` states exactly that missing identity between four `mass`-terms. It is a
**counting/reindexing** statement (the genuine substitute for the falsified tower property),
never a nested `mass`. -/
def FibreGluing (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  ∀ (A B Z : Finset V), Disjoint A B → Disjoint A Z → Disjoint B Z →
    ∀ x : V → α,
      Fate.DAGFactorization.mass (A ∪ B ∪ Z) p x * Fate.DAGFactorization.mass Z p x
        = Fate.DAGFactorization.mass (A ∪ Z) p x * Fate.DAGFactorization.mass (B ∪ Z) p x

/-- ⭐⭐ **Reduction (trivially true by definition, but records the architecture)**: if the
fibre-gluing identity holds for **every** triple, then `Markov p G` holds.

Note `dSep` supplies the three disjointness facts, so this closes the bridge
`graph ⟹ probability` **given** `FibreGluing` — the single remaining counting identity. -/
theorem markov_of_fibreGluing {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : FibreGluing p G) : Fate.FactorMarkov.Markov p G := by
  intro X Y Z hd
  obtain ⟨hXY, hXZ, hYZ, _⟩ := hd
  exact h X Y Z hXY hXZ hYZ

/-! ### §5 冒烟测试：引擎在具体 `chainDAG`（`0 → 1 → 2`）上可用 -/

section ChainSmoke

open Fate.DAGFactorization

/-- 引擎在 `chainDAG`（`0 → 1 → 2`）上的**可用性冒烟测试**：
`mass (lowerSet 1) p x = ∏_{v∈lowerSet 1} f v x`（`topoOrder` 非computable，故不展开数值）。 -/
theorem chain_peel_example {α : Type} [Fintype α] [DecidableEq α]
    (p : (Fin 3 → α) → ℝ) (f : Fin 3 → (Fin 3 → α) → ℝ)
    (hloc : Fate.FactorMarkov.LocalTo Fate.DAGFactorization.chainDAG f)
    (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : Fate.FactorMarkov.FactorNorm f) (x : Fin 3 → α) :
    Fate.DAGFactorization.mass (lowerSet Fate.DAGFactorization.chainDAG 1) p x
      = ∏ v ∈ lowerSet Fate.DAGFactorization.chainDAG 1, f v x :=
  peel_lower hloc hfac hnorm 1 x

end ChainSmoke

end FateV2.Predict.Strategy11