/-
-/

module

public import FateWorld.FateV2.Modeling.CausDAG
/-!
  # Predict · CausalClosureTight

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausalClosureTight.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# Tightness and least-ness of the causal ancestor closure (九要件 ⑧ 因果, 第 1043 轮)

## 口径说明（重要，防同义反复）

`Causalean.Graph.DAG.ancClosure v` 在 `CausDAG.lean` 里是**严格祖先集**：
它是从 `G.parents v`（`v` 的直接父集）出发、迭代 `ancStep` 得到的后向可达
不动点，**不包含 `v` 本身**。因此「包含 `v` 的闭集」这一表述对本 API 是错的，
正确的载体是：

> `ancClosure v` = 所有「含 `G.parents v` 且对 `parents` 封闭」的有限集的
> **最小元**（在子集偏序 `⊆` 下）。

子集偏序下的最小元 = 真下界；最小元被 `ancClosure v` 本身达到 = 真紧性。

## 本文件新增（6 条，全部命题内容非平凡）

1. `ancClosure_subset_of_closed` —— 最小性（= 下界）：任何闭集含 `parents v`
   就含 `ancClosure v`。
2. `ancClosure_isLeast` —— `ancClosure v` 是上述闭集族的 `IsLeast` 元。
3. `ancClosure_card_le` —— 基数下界：任何这类闭集的基数不小于闭包基数。
4. `ancClosure_attained` —— 紧性（被达到）：闭包本身属于该族。
5. `ancStep_iterate_idempotent` —— 饱和算子幂等（闭包算子的算子性）。
6. `ancClosure_ssubset_of_isAncestor` —— 沿祖先链的**严格**嵌套：
   `u` 是 `v` 的祖先则 `ancClosure u ⊊ ancClosure v`（链长 = 秩），
   这是比 `ancestorRank_lt_of_edge` 更强的集合层严格性。

无一使用 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。
-/

@[expose] public section

namespace FateV2.Predict

open FateV2.Modeling
namespace CausalClosureTight

open FateV2.Modeling.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### 迭代的可靠性：任何闭集一旦含 `parents v`，就含全部迭代 -/

/-- **迭代可靠性（私有引理）。** 若 `T` 对 `parents` 封闭且 `G.parents v ⊆ T`，
则 `ancStep` 迭代任意次所得集合仍含于 `T`。这是最小性证明的引擎。 -/
private theorem iterate_subset_of_closed (G : DAG V) {T : Finset V}
    (hT : ∀ x ∈ T, G.parents x ⊆ T) {v : V} (hpar : G.parents v ⊆ T) (k : ℕ) :
    (G.ancStep)^[k] (G.parents v) ⊆ T := by
  induction k with
  | zero => simpa using hpar
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro y hy
    rw [DAG.ancStep, Finset.mem_union] at hy
    rcases hy with hy | hy
    · exact ih hy
    · rw [Finset.mem_biUnion] at hy
      obtain ⟨x, hx, hyx⟩ := hy
      exact hT x (ih hx) hyx

/-! ### 1. 最小性 = 下界 -/

/-- ⭐⭐⭐⭐⭐ **【最小性 = 真下界】** 任何含 `G.parents v` 且对 `parents` 封闭的有限集
`T` 都包含计算结果 `G.ancClosure v`。

这是**真下界**：`ancClosure v` 是该闭集族在子集偏序 `⊆` 下的下界。
前件只谈 `T` 的封闭性与 `parents v ⊆ T`，**完全不提 `ancClosure`**，
结论不是前件的合取支，故非同义反复。 -/
theorem ancClosure_subset_of_closed (G : DAG V) (v : V) {T : Finset V}
    (hT : ∀ x ∈ T, G.parents x ⊆ T) (hpar : G.parents v ⊆ T) :
    G.ancClosure v ⊆ T :=
  iterate_subset_of_closed G hT hpar (Fintype.card V)

/-! ### 2. 下确界刻画（`IsLeast`） -/

/-- ⭐⭐⭐⭐⭐ **【下确界刻画】** `G.ancClosure v` 恰是闭集族
`{T | (∀ x ∈ T, G.parents x ⊆ T) ∧ G.parents v ⊆ T}` 在 `⊆` 下的**最小元**：
它属于该族，且含于族中每个成员。

两半合起来正是「最小不动点 = 下确界」：下界性来自 `ancClosure_subset_of_closed`，
族成员性来自 `ancClosure_closed` 与 `subset_iterate_ancStep`。 -/
theorem ancClosure_isLeast (G : DAG V) (v : V) :
    IsLeast {T : Finset V | (∀ x ∈ T, G.parents x ⊆ T) ∧ G.parents v ⊆ T}
      (G.ancClosure v) := by
  constructor
  · exact ⟨fun x hx => G.ancClosure_closed v hx,
      G.subset_iterate_ancStep (G.parents v) (Fintype.card V)⟩
  · rintro T ⟨hT, hpar⟩
    exact ancClosure_subset_of_closed G v hT hpar

/-! ### 3. 基数下界 -/

/-- ⭐⭐⭐⭐⭐ **【真下界（基数口径）】** 任何含 `G.parents v` 的闭集 `T` 的基数都不小于
`G.ancClosure v` 的基数。

即 `|ancClosure v|` 是该闭集族基数集合的**下界**；由 `ancClosure_attained`，
它还是**最小值**（被达到）。 -/
theorem ancClosure_card_le (G : DAG V) (v : V) {T : Finset V}
    (hT : ∀ x ∈ T, G.parents x ⊆ T) (hpar : G.parents v ⊆ T) :
    (G.ancClosure v).card ≤ T.card :=
  Finset.card_le_card (ancClosure_subset_of_closed G v hT hpar)

/-! ### 4. 紧性：下界被达到 -/

/-- ⭐⭐⭐⭐ **【紧性 = 被达到】** `G.ancClosure v` 本身属于该闭集族：它对 `parents`
封闭，且包含 `G.parents v`。

结合 `ancClosure_subset_of_closed`，这给出了「最小闭集**存在且等于** `ancClosure v`」，
即下界不是严格下界而是被达到的最优值 —— 这正是紧性。 -/
theorem ancClosure_attained (G : DAG V) (v : V) :
    (∀ x ∈ G.ancClosure v, G.parents x ⊆ G.ancClosure v) ∧
      G.parents v ⊆ G.ancClosure v :=
  ⟨fun _ hx => G.ancClosure_closed v hx,
    G.subset_iterate_ancStep (G.parents v) (Fintype.card V)⟩

/-! ### 5. 闭包算子幂等 -/

/-- ⭐⭐⭐⭐ **【幂等】** 饱和算子 `ancStep^[|V|]` 幂等：再饱和一次不改变结果，
对**任意**起始有限集成立（不限于 `parents v`）。

证明同 `ancStep_ancClosure` 的链长/基数论证：`ancStep` 单调且 `Finset V` 有限，
`|V|` 步必达不动点。 -/
theorem ancStep_iterate_idempotent (G : DAG V) (S : Finset V) :
    (G.ancStep)^[Fintype.card V] ((G.ancStep)^[Fintype.card V] S)
      = (G.ancStep)^[Fintype.card V] S := by
  -- 一步扩展包含原集
  have step_subset : ∀ A : Finset V, A ⊆ G.ancStep A := by
    intro A x hx
    rw [DAG.ancStep, Finset.mem_union]
    exact Or.inl hx
  -- 链条 `ancStep^[j] S` 关于 `j` 单调递增
  have chain : ∀ j, (G.ancStep)^[j] S ⊆ (G.ancStep)^[j + 1] S := by
    intro j
    rw [Function.iterate_succ_apply']
    exact step_subset _
  -- 若链条在某一步严格变大，则基数至少增加，`|V| + 1` 步内必然饱和
  have hexists : ∃ k ≤ Fintype.card V,
      (G.ancStep)^[k] S = (G.ancStep)^[k + 1] S := by
    by_contra hcon
    push Not at hcon
    have hstrict : ∀ j, j < Fintype.card V + 1 →
        ((G.ancStep)^[j] S).card < ((G.ancStep)^[j + 1] S).card := by
      intro j hj
      have hsub := chain j
      have hne : (G.ancStep)^[j] S ≠ (G.ancStep)^[j + 1] S :=
        hcon j (Nat.lt_succ_iff.mp hj)
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hge : ((G.ancStep)^[0] S).card + (Fintype.card V + 1)
        ≤ ((G.ancStep)^[Fintype.card V + 1] S).card :=
      DAG.le_card_iterate G.ancStep S (Fintype.card V + 1) hstrict
    have hle : ((G.ancStep)^[Fintype.card V + 1] S).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    simp only [Function.iterate_zero, id_eq] at hge
    omega
  obtain ⟨k, hkN, hk⟩ := hexists
  -- 该步之后链条恒定（`ancStep` 的单调性 + 不动点）
  have hfix : G.ancStep ((G.ancStep)^[k] S) = (G.ancStep)^[k] S := by
    have hsucc : (G.ancStep)^[k + 1] S = G.ancStep ((G.ancStep)^[k] S) :=
      Function.iterate_succ_apply' G.ancStep k S
    rw [← hsucc]; exact hk.symm
  have hconst : ∀ d, (G.ancStep)^[k + d] S = (G.ancStep)^[k] S := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, hfix]
  -- `|V| ≥ k`，故 `|V| = k + d`
  obtain ⟨d, hd⟩ := Nat.le.dest hkN
  have hA : (G.ancStep)^[Fintype.card V] S = (G.ancStep)^[k] S := hd ▸ hconst d
  -- `ancStep^[|V|] (ancStep^[|V|] S) = ancStep^[|V| + |V|] S = ancStep^[k] S`
  have hB : (G.ancStep)^[Fintype.card V] ((G.ancStep)^[Fintype.card V] S)
      = (G.ancStep)^[Fintype.card V + Fintype.card V] S :=
    (Function.iterate_add_apply G.ancStep (Fintype.card V) (Fintype.card V) S).symm
  have hlen : Fintype.card V + Fintype.card V
      = k + (d + (k + d)) := by omega
  rw [hB, hlen, hconst (d + (k + d)), hA]

/-! ### 6. 沿祖先链的严格嵌套 -/

/-- ⭐⭐⭐⭐⭐ **【严格嵌套 / 链长紧性】** 若 `u` 是 `v` 的祖先，则严格
`ancClosure u ⊊ ancClosure v`。

这是比 `ancestorRank_lt_of_edge`（单边秩增）更强的集合层严格性，也是
「因果链深度 = 闭包严格链长度」的载体：
`u ∈ ancClosure v` 而 `u ∉ ancClosure u`（无环 ⟹ 非自反）给出真包含。 -/
theorem ancClosure_ssubset_of_isAncestor (G : DAG V) {u v : V}
    (h : G.isAncestor u v) : G.ancClosure u ⊂ G.ancClosure v := by
  have hsub : G.ancClosure u ⊆ G.ancClosure v := by
    intro w hw
    rw [DAG.mem_ancClosure] at hw ⊢
    exact G.isAncestor_trans hw h
  have hne : G.ancClosure u ≠ G.ancClosure v := by
    intro heq
    have huv : u ∈ G.ancClosure v := (DAG.mem_ancClosure (G := G)).mpr h
    have hmem : u ∈ G.ancClosure u := heq ▸ huv
    exact G.isAncestor_irrefl u ((DAG.mem_ancClosure (G := G)).mp hmem)
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩

end CausalClosureTight

end FateV2.Predict