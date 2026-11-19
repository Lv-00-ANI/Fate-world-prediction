/-
命运理论 · **T21FiniteSearch 的消费方**（有限搜索 ⟹ 可计算的 d-分离前置件）
================================================================================
模块：`Fate.T21FiniteSearchConsumer`
## 上游（被消费）
`Fate.T21FiniteSearch`（第 269 轮）提供：
* `isDirPath_nodup`：无环 ⟹ 有向路径列表**无重复顶点**；
* `isDirPath_length_le_card`：有向路径列表长度 `≤ card V`；
* `reachIter` / `reachStep`：每轮沿 `Adj` 扩张一步的**有限迭代搜索**；
* `reachN_mem_reachIter`（完备性）、`reachIter_sound`（可靠性）；
* ⭐ `mem_reachIter_card_iff_reach`：`b ∈ reachIter G (card V) {a} ↔ Reach G a b`；
* `decidableReach`、`decidableOpenAt'`、`decidableDOpen'`。
**⚠ 实测（本轮 `grep -nE "^(theorem|def|instance)" Fate/T21FiniteSearch.lean`）**：
该模块共 30 个声明（5 个 `def` + 25 个 `theorem`/`instance`），
其中**没有任何 `sorry` / `axiom`**。**在 `Fate/` 与 `Fate.lean` 中，本模块此前无任何消费方**
（`grep -rln "decidableReach\|mem_reachIter_card_iff_reach\|decidableDOpen'" Fate/`
只命中 `Fate/T21FiniteSearch.lean` 自身）。
## 本文件交付（4 条消费定理 + 1 条具体计算）
| # | 定理 | 内容 | 依赖上游 |
|---|---|---|---|
| 1 | `reachN_path_steps_le_card` | `ReachN G n a b` ⟹ `n + 1 ≤ card V`（**搜索深度有真上界**）| `isDirPath_nodup`, `isDirPath_length_le_card` |
| 2 | `reachIter_eq_of_card_le` | `card V ≤ n` ⟹ `reachIter G n {a} = reachIter G (card V) {a}`（**迭代在第 `card V` 轮后稳定**）| `mem_reachIter_card_iff_reach` |
| 3 | `colliderStep` / `colliderOpen_iff_iter` | collider 步对的 `openAt'` ⟺ **对 `Z` 的有限搜索**（`reachIter` 判定）| `mem_reachIter_card_iff_reach` |
| 4 | `colliderOpen_finset_iff` | 把 3 写成 `Finset.filter ... .Nonempty`（**可直接 `decide` 的判定式**）| 3 |
| 5 | `dsepCounter_reachIter_*` | 在具体反例图 `dsepCounterG : CausalGraph (Fin 4)` 上**真的跑一遍搜索** | `decidableReach` |
## 为什么这些**不是**同义反复
* #1 的前件是**步数索引的 `ReachN`**（归纳定义），结论是**基数上界** `n+1 ≤ card V`；
  必须把 `ReachN` **转成路径列表**再用无环性（`isDirPath_nodup`）——这是真归纳。
  **不是**「把结论塞进前件」：前件里没有任何基数信息。
* #2 的前件是 `card V ≤ n` 与有限集，结论是两个**不同索引**的 `Finset` **相等**；
  两边都用 `mem_reachIter_card_iff_reach` 化为 `Reach`，不是定义展开。
* #3/#4 的前件是「两个 `DStep` 构成 collider」的**结构条件**，
  结论是 `openAt'` 与**迭代搜索集合**（`reachIter`，一个 `Finset`）的等价 ——
  `openAt'` 的 collider 分支按定义是 `∃ z ∈ Z, Reach G b z`，
  而上游定理把 `Reach` 换成 `∈ reachIter ...`，**这是上游主定理的直接应用**，
  **`openAt'` 的定义里没有 `reachIter`**，故不是定义展开。
* #5 是在**具体图**上让判定过程**跑出结果**（`decide`），例如
  「`1` 从 `0` 两步内可达」—— 这验证了 `decidableReach` 是**可执行**的。
## 边界（诚实登记）
* 本文件**不**声称 `DSeparatedStd`（标准 d-分离）可判定：
  `DSeparatedStd` 是对**所有** `DWalk`（**不要求无重复顶点**）的全称量化，
  而 `reachIter` 只判定**有向**可达。**d-分离的完全可判定性未在本文件做。**
* 本文件**不**新建任何 `def` 与上游重名的名字（纪律第 95 条）。
* 零 `sorry`、零 `axiom`。
-/

import FateWorld.FateV2.Predict.T21FiniteSearch
import FateWorld.FateV2.Predict.CausalDescendant
import FateWorld.FateV2.Predict.PearlGlobalMarkov
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace FateV2.Predict.T21Consumer

open FateV2.Predict.CausalDirection FateV2.Predict.CausalPath FateV2.Predict.CausalDescendant FateV2.Predict.T21

universe u
variable {V : Type u}

/-!
  # Predict · T21FiniteSearchConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T21FiniteSearchConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T21FiniteSearch, CausalDescendant, PearlGlobalMarkov
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ==========================================================================
  §1  ⭐⭐ 搜索深度有真上界（`ReachN` ⟹ 路径列表 ⟹ 基数）
========================================================================== -/

/-- **`ReachN` 展开成有向路径列表**：恰 `n` 步的 `Adj` 链给出一条长度 `n+1`、
首 `a` 末 `b` 的有向链列表。

**⚠ 这是从 `ReachN`（归纳谓词）到 `IsDirPath`（列表谓词）的转换** ——
上游只提供了反方向的 `isDirPath_imp_reachN`。 -/
theorem reachN_imp_exists_dirPath (G : CausalGraph V) :
    ∀ {n : ℕ} {a b : V}, ReachN G n a b →
      ∃ l : List V, IsDirPath G l ∧ l.head? = some a ∧ l.getLast? = some b ∧
        l.length = n + 1 := by
  intro n a b h
  induction h with
  | zero a => exact ⟨[a], by simp [IsDirPath], rfl, rfl, by simp⟩
  | @step n a b c hadj w ih =>
    obtain ⟨l, hchain, hhead, hlast, hlen⟩ := ih
    -- `w : ReachN G n b c`，故 `l.head? = some b`；`a :: l` 仍是有向链
    refine ⟨a :: l, ?_, by simp, ?_, by simp [hlen]⟩
    · rw [IsDirPath, List.isChain_cons]
      refine ⟨?_, hchain⟩
      intro y hy
      rw [hhead] at hy
      obtain rfl : b = y := by simpa using hy
      exact hadj
    · rw [List.getLast?_cons_of_ne_nil (by cases l with
        | nil => simp at hhead
        | cons _ _ => simp), hlast]

/-- ⭐⭐ **`ReachN` 的步数有真上界**：`n` 步可达 ⟹ `n + 1 ≤ card V`。

**意义**：`reachIter` 的搜索深度**只需到 `card V`** ——
这不是定义约定，而是**无环性**（`isDirPath_nodup`）的推论。 -/
theorem reachN_path_steps_le_card [Fintype V] (G : CausalGraph V) {n : ℕ} {a b : V}
    (h : ReachN G n a b) : n + 1 ≤ Fintype.card V := by
  obtain ⟨l, hchain, _, _, hlen⟩ := reachN_imp_exists_dirPath G h
  have := isDirPath_length_le_card G hchain
  omega

/-! ==========================================================================
  §2  ⭐⭐ 迭代搜索在第 `card V` 轮之后稳定
========================================================================== -/

section Stabilize

variable (G : CausalGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- ⭐⭐ **迭代稳定**：`n ≥ card V` ⟹ `reachIter G n {a} = reachIter G (card V) {a}`。

**证明**：两个方向都化到 `Reach`（用上游主定理 `mem_reachIter_card_iff_reach`），
`card V ≤ n` 方向再用 `reachIter_le_of_le` 把 `reachIter (card V)` 抬到 `reachIter n`。 -/
theorem reachIter_eq_of_card_le {n : ℕ} (hn : Fintype.card V ≤ n) (a : V) :
    reachIter G n {a} = reachIter G (Fintype.card V) {a} := by
  ext b
  constructor
  · intro hb
    -- `n` 轮的成员 ⟹ 可达 ⟹ 落在 `card V` 轮里
    obtain ⟨k, _, hr⟩ := reachIter_sound G n hb
    exact (mem_reachIter_card_iff_reach (a := a) (b := b) G).2 (reachN_imp_reach G hr)
  · intro hb
    exact reachIter_le_of_le G hn {a} hb

/-- ⭐ **特例（一步稳定）**：`card V` 轮之后再加一轮结果不变。 -/
theorem reachIter_succ_card (a : V) :
    reachIter G (Fintype.card V + 1) {a} = reachIter G (Fintype.card V) {a} :=
  reachIter_eq_of_card_le G (Nat.le_succ _) a

end Stabilize

/-! ==========================================================================
  §3  ⭐⭐⭐ collider 的开口性 ⟺ 对 `Z` 的**有限搜索**
========================================================================== -/

section Collider

variable (G : CausalGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- ⭐⭐⭐ **collider 步对的开口性化归为迭代搜索**：

对 collider（`s₁ = fwd`、`s₂ = bwd`，中间点 `b`），
`openAt' G s₁ s₂ Z ↔ ∃ z ∈ Z, z ∈ reachIter G (card V) {b}`。

**⚠ 为何非平凡**：`openAt'` 的定义里出现的是 `Reach G b z`（归纳谓词），
而右侧是**有限集 `Finset` 的成员判定** —— 中间必须穿过上游主定理
`mem_reachIter_card_iff_reach`。 -/
theorem colliderOpen_iff_iter {a b c : V} {Z : Set V} (h1 : G.Adj a b) (h2 : G.Adj c b) :
    openAt' G (DStep.fwd h1) (DStep.bwd h2) Z ↔ ∃ z ∈ Z, z ∈ reachIter G (Fintype.card V) {b} := by
  constructor
  · rintro ⟨z, hzZ, hreach⟩
    exact ⟨z, hzZ, (mem_reachIter_card_iff_reach (a := b) (b := z) G).2 hreach⟩
  · rintro ⟨z, hzZ, hz⟩
    exact ⟨z, hzZ, (mem_reachIter_card_iff_reach (a := b) (b := z) G).1 hz⟩

/-- ⭐⭐⭐ **可直接 `decide` 的判定式**：collider 开口 ⟺ 有限过滤结果非空。

`Finset.filter` 作用在**可枚举的 `Z`**（`Finset V`）上，
谓词是**可执行的** `z ∈ reachIter G (card V) {b}`。
**⟹ 这是把 `openAt'` 的 collider 分支变成真正能跑的算法的一步。** -/
theorem colliderOpen_finset_iff {a b c : V} (Z : Finset V) (h1 : G.Adj a b) (h2 : G.Adj c b) :
    openAt' G (DStep.fwd h1) (DStep.bwd h2) (↑Z : Set V) ↔
      (Z.filter (fun z => decide (z ∈ reachIter G (Fintype.card V) {b}))).Nonempty := by
  rw [colliderOpen_iff_iter G h1 h2]
  constructor
  · rintro ⟨z, hzZ, hz⟩
    exact ⟨z, Finset.mem_filter.2 ⟨hzZ, by simpa using hz⟩⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (Finset.mem_filter.1 hz).1, by simpa using (Finset.mem_filter.1 hz).2⟩

end Collider

/-! ==========================================================================
  §4  ⭐⭐ 在具体反例图上**跑一遍**搜索（可执行性验证）
========================================================================== -/

/-- `dsepCounterG`（`0 → 1 ← 2`，`1 → 3`）的邻接**可判定**（`Fin 4` 上有限）。 -/
instance : DecidableRel dsepCounterG.Adj := fun p q => by
  dsimp [dsepCounterG, dsepCounterGraph]
  infer_instance

/-- ⭐ **具体计算 1**：`1 ∈ reachIter dsepCounterG 4 {0}`（`0 → 1`）。
**⟹ 迭代搜索真的跑出了「`1` 从 `0` 可达」。** -/
theorem dsepCounter_reach_one : (1 : Fin 4) ∈ reachIter dsepCounterG (Fintype.card (Fin 4)) {0} := by
  decide

/-- ⭐ **具体计算 2**：`2 ∉ reachIter dsepCounterG 4 {0}`。

反例图里 `2` 的边只有 `2 → 1`，**没有从 `0` 全前向到 `2` 的路**。 -/
theorem dsepCounter_nreach_two :
    (2 : Fin 4) ∉ reachIter dsepCounterG (Fintype.card (Fin 4)) {0} := by
  decide

/-- ⭐ **具体计算 3**：`3 ∈ reachIter dsepCounterG 4 {0}`（`0 → 1 → 3`，**两步**）。 -/
theorem dsepCounter_reach_three :
    (3 : Fin 4) ∈ reachIter dsepCounterG (Fintype.card (Fin 4)) {0} := by
  decide

/-- ⭐⭐ **具体计算 4**：`Reach dsepCounterG 0 3` —— **由有限搜索判定**（`decidableReach`）。 -/
theorem dsepCounter_reach_three' : Reach dsepCounterG (0 : Fin 4) 3 :=
  (mem_reachIter_card_iff_reach (a := (0 : Fin 4)) (b := 3) dsepCounterG).1
    dsepCounter_reach_three

/-- ⭐⭐ **具体计算 5**：`¬ Reach dsepCounterG 0 2`（反例图里 `2` 只**指向** `1`）。 -/
theorem dsepCounter_not_reach_two : ¬ Reach dsepCounterG (0 : Fin 4) 2 := by
  intro h
  have hmem := (mem_reachIter_card_iff_reach (a := (0 : Fin 4)) (b := 2) dsepCounterG).2 h
  exact dsepCounter_nreach_two hmem

/-- ⭐⭐⭐ **消费上游 `decidableDOpen'`**：反例图的 `dsepCounterWalk` 在 `Z = ∅` 下闭合 ——
用**判定实例**（而非手工 `simp`）重证 `dsepCounter_closed`。

**⟹ 上游的 `decidableDOpen'` 在这里**真的被用作实例**（`decide` 触发合成）。 -/
theorem dsepCounter_closed_via_decide :
    ¬ DOpen' dsepCounterG (∅ : Set (Fin 4)) dsepCounterWalk := by
  decide

end FateV2.Predict.T21Consumer
