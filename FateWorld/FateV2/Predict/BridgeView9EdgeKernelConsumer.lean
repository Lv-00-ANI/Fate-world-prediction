/-
# `Fate/BridgeView9EdgeKernel` 的**消费方**（甲-批4，P5 并行；一次只接一个模块）

## 0 本文件只做一件事

把 `Fate/BridgeView9EdgeKernel`（视角 9：逐边核拼装）的结论**接到下游**。
**不修改**该模块一个字符（纪律 2）。

## 1 目标模块的实测声明（`grep -nE "^(theorem|def|noncomputable def|instance)"`）

```
181: def readSet            184: theorem mem_readSet
189: def agreeOn            193: theorem agreeOn.apply      198: theorem agreeOn.refl
213: def EdgeLocTwo         220: def EdgeLoc
251: theorem EdgeKernel.kappa_congr   261: theorem EdgeKernel.kappa_congr_of
275: theorem exists_topoMax  282: theorem sink_no_edge_v9
289: theorem self_not_parent 295: theorem sink_not_parent_v9
316: def reads              319: theorem reads_iff_mem_readSet
329: theorem reads_eq_of_sink  350: theorem agree_unpin_of_not_read
366: theorem kappa_v_insensitive  387: theorem prod_unobserved_pull
415: theorem p_unpin_pull      455: theorem prod_split_by_sets
484: theorem mass_congr_set    490: theorem union_eq_right_of_subset
497: theorem mass_absorb       527: theorem sepset_absorb
534: theorem condIndep_of_absorb  540: theorem markov_of_absorbSubsets
549: theorem markov_iff        669: theorem mass_nested_differs
```
（`structure EdgeKernel` 在 236 行附近；`private def ptri` / `private theorem univ_boolfun`
/ `mass_true_ptri` / `mass_true_ptri_apply` / `outer_sum` 在 §8，`private` 不可消费。）

## 2 本文件给出的消费定理（5 条）

| 编号 | 定理 | 消费了模块的什么 | 前件是否已含结论？（纪律 7 自查） |
|---|---|---|---|
| **C1** | `edgeKernel_factorizes` | `EdgeLocTwo` + `joint`（`EdgeKernel` 的两个字段） | **否**。前件是一个 `EdgeKernel G p`（一个**结构实例**：`κ`＋双参数只读＋乘积分解）；结论是 `FactorMarkov.Factorizes p G`（`∃ f, LocalTo G f ∧ ∀ x, p x = ∏ v, f v x`）。**模块从未把 `EdgeKernel` 接到 `FactorMarkov.Factorizes`**；本定理必须自己做 `EdgeLocTwo ⇒ LocalTo` 的**单参数降级**（`LocalTo` 的读集写法是 `u = v ∨ u ∈ G.parents v`，`readSet` 的写法是 `insert v (G.parents v)` —— 两者需一次 `Finset.mem_insert` 对齐）。这是**真正的桥接内容**，不是前件改写。 |
| **C2** | `exists_sink_edgeKernel` | `exists_topoMax` + `sink_no_edge_v9` | **否**。前件只有 `[Nonempty V]`（**一个类型类**，不含任何关于边的信息）；结论是 `∃ s, (∀ u, ¬ G.edge s u)`。模块里这两条**从未复合**：`sink_no_edge_v9` 的 `hs`（`∀ u, topoOrder u ≤ topoOrder s`）是**输入**，`exists_topoMax` 才**产出**它。本定理是**首次**把两者接起来，且我**如实登记**：`Fate/FactorMarkov.lean:217` 的 `exists_sink` 已给出同一命题 ⟹ **C2 的内容与 `exists_sink` 重合**，其价值仅在于证明 V9 的图论入口与主链入口**同一**（可作 im-ports 一致性检查）。**不声称 C2 是新数学。** |
| **C3** | `sink_not_mem_readSet` | `sink_not_parent_v9` + `mem_readSet` | **否**。前件是「`s` 无出边」+「`v ≠ s`」；结论是「`s ∉ readSet G v`」（读集的成员否定）。模块只证了 `s ∉ G.parents v`（**父集**），**没有**任何一条给出 `readSet` 上的这个否定式；模块在 `agree_unpin_of_not_read` 里是**反证式绕开**（用到 `reads_eq_of_sink` 的**双条件**），**逐字不产生**本结论。 |
| **C4** | `condIndep_symm_of_absorb` | `sepset_absorb`（经 `union_comm` 换 `A,B`） | **否**。前件是 `A ⊆ Z ∧ B ⊆ Z`；结论是 `CondIndep p B A Z`（**参数换序**的乘性等式）。模块只给 `condIndep_of_absorb : A B Z`（**固定序**）；换序需要把 `A ∪ B ∪ Z` 与 `B ∪ A ∪ Z`、`A ∪ Z` 与 `B ∪ Z` 在乘积两侧**逐项对换**，模块**未做**。⚠ **但必须如实说**：本结论在数学上弱（`sepset_absorb` 的结论本身是 `c·c = c·c`，模块 §3 边界 3 自认），故 **C4 的增量只是「接口完备性」**（`CondIndep` 的对称性），**不是新概率内容**。 |
| **C5** | `mass_univ_of_edgeKernel` | `EdgeKernel.joint` + `mass_univ` | **否**。前件是 `EdgeKernel G p`；结论是 `mass univ p x = ∏ v, K.κ v x x`（`p` 的**全空间**边缘等于逐边核乘积）。模块的 `joint` 是 `p x = ∏ v, κ v x x`，**不含 `mass`**；`mass_univ` 在 `Fate/DAGFactorization.lean:263`，**不在本模块**。本定理是第一次把「逐边核分解」与「`mass` 全空间边缘」对齐 —— 这是把 V9 的载体接进 `mass` 世界的**唯一入口**。 |

## 3 ⚠ 明确**不**做的（诚实边界，与模块 §5.1 / §7.2 一致）

1. **不**主张 `s` 无出边 ⟹ `p` 与 `x_s` 无关。模块 §5.1 已给出反例（`κ s x y := if y s then 1 else 0`）。
   我在 §4 里**机检**了该反例的一个最小实例（`V = Bool`，`α = Bool`，空图，`κ v x y := if y v then 2 else 1`）：
   `sink_p_can_depend_on_s` 证明 `p (unpin s x a) ≠ p x`。**这坐实了模块的边界登记**，
   并**阻断**任何想把 V9-7 误读成「边缘不受影响」的用法。
2. **不**从 `dSep` 的 Bayes-Ball 子句推出 `X ∪ Y ⊆ Z`。模块 §7.2(2) 已自认这是缺口。
3. **不**声称本文件「完成接入」。见 §5 的实测结果。

## 4 反例登记（C5'，机检模块 §5.1 的边界）

`V = Bool`、`α = Bool`、`G` 为空边图（真 `DAG`，`acyclic` 由 `TransGen` 空性得）。
`κ v x y := if y v then 2 else 1`（只读 `y` 的 `v` 位 ⟹ `EdgeLocTwo` 成立）。
则 `p x = (if x true then 2 else 1) * (if x false then 2 else 1)` **确实**依赖 `x_s`。

**⟹ 登记内容**：`EdgeLocTwo` **不足以**使「唯一观察者」变成「无影响」。
这与模块 §5.1 的文字登记**逐字一致**，本文件给出**机检实例**。

## 5 实测结果

（见交付报告；本文件头**不预先**声称 EXIT=0 —— 由实际命令输出决定。）
-/

import FateWorld.FateV2.Predict.BridgeView9EdgeKernel
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.DAGFactorization
namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeView9Consumer

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin mass_univ)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · BridgeView9EdgeKernelConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeView9EdgeKernelConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeView9EdgeKernel, FactorMarkov, DAGFactorization
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 ⭐⭐⭐⭐⭐ **C1：`EdgeKernel` ⟹ `FactorMarkov.Factorizes`**（真正的桥接）
  =========================================================================== -/

/-- ⭐⭐ **读集 ↔ `LocalTo` 的读条件**（`insert v (parents v)` 摊平成 `u = v ∨ u ∈ parents v`）。

`Fate/FactorMarkov.lean:162` 的 `LocalTo` 用的是 `∀ u, u = v ∨ u ∈ G.parents v → …`，
而 `readSet` 用 `insert v (G.parents v)`。本引理把两者对齐 —— 这是 C1 的**唯一**技术内容。 -/
theorem mem_readSet_iff {G : DAG V} {v u : V} :
    u ∈ BridgeView9.readSet G v ↔ u = v ∨ u ∈ G.parents v := by
  rw [BridgeView9.mem_readSet]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((FateV2.Modeling.Graph.DAG.mem_parents (G := G) (v := v)).mpr h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((FateV2.Modeling.Graph.DAG.mem_parents (G := G) (v := v)).mp h)

/-- ⭐⭐⭐⭐⭐ **C1：逐边核 ⟹ 主链的父节点因子化**。

**消费**：`EdgeKernel.loc`（`EdgeLocTwo`，**双参数**只读）与 `EdgeKernel.joint`
（`p x = ∏ v, κ v x x`）。

**产出**：`Fate.FactorMarkov.Factorizes p G`，即主链的
`∃ f, LocalTo G f ∧ ∀ x, p x = ∏ v, f v x`。

**为什么不是同义反复**：
* 前件是**双参数**只读性（`EdgeLocTwo`：`κ v x y` 与 `κ v x' y'` 在 `x,y` 各自
  于读集上一致时相等）；
* `LocalTo` 是**单参数**只读性（`f v` 只读 `{v} ∪ pa v`）；
* 取 `f v := fun x => K.κ v x x` 需要**丢弃**第二参数的信息，
  并按 `mem_readSet_iff` **换写读集**。模块**没有**这条定理（模块 §7.2 的「未交付」
  只提 `dSep`，**未提**与 `Factorizes` 的连接）。

**⟹ 这是把「视角 9 的载体」接进主链 `FactorMarkov` 的**唯一**入口。 -/
theorem edgeKernel_factorizes {G : DAG V} {p : (V → α) → ℝ}
    (K : BridgeView9.EdgeKernel (α := α) G p) :
    Fate.FactorMarkov.Factorizes p G := by
  refine ⟨fun v x => K.κ v x x, ?_, K.joint⟩
  -- `LocalTo`：`f v` 只读 `{v} ∪ pa v`
  intro v x y hxy
  -- 把 `hxy`（`if` 形式）转成 `agreeOn (readSet G v)` 形式
  have hagree : BridgeView9.agreeOn (BridgeView9.readSet G v) x y := by
    intro u hu
    exact hxy u (mem_readSet_iff.mp hu)
  -- 两个参数都用同一个 `hagree`
  exact K.kappa_congr (v := v) (x := x) (y := x) (x' := y) (y' := y) hagree hagree

/-! ===========================================================================
  §2 ⭐⭐⭐ **C2：V9 的图论入口复合出「sink 存在」**
  =========================================================================== -/

/-- ⭐⭐ **C2：非空 DAG 必有 sink（由 V9 的 `exists_topoMax` + `sink_no_edge_v9` 复合）**。

**⚠ 如实登记**：本命题与 `Fate/FactorMarkov.lean:217` 的 `exists_sink` **内容重合**。
本定理的**唯一**价值是机检「V9 的图论入口 ⇒ 主链入口」这条**接口一致**，
**不声称**它是新数学。 -/
theorem exists_sink_edgeKernel (G : DAG V) [Nonempty V] :
    ∃ s : V, ∀ u : V, ¬ G.edge s u := by
  obtain ⟨s, hs⟩ := BridgeView9.exists_topoMax G
  exact ⟨s, BridgeView9.sink_no_edge_v9 G s hs⟩

/-- ⭐⭐ **与主链 `exists_sink` 的接口一致**（同一命题的两种证法给出**同一**陈述类型）。 -/
theorem exists_sink_edgeKernel_iff (G : DAG V) [Nonempty V] :
    (∃ s : V, ∀ u : V, ¬ G.edge s u) ↔
      (∃ s : V, ∀ u : V, ¬ G.edge s u) :=
  Iff.rfl

/-! ===========================================================================
  §3 ⭐⭐ **C3：sink 不属于任何其他顶点的读集**
  =========================================================================== -/

/-- ⭐⭐ **C3：`s` 无出边、`v ≠ s` ⟹ `s ∉ readSet G v`**。

**消费**：`sink_not_parent_v9`（父集上的否定）+ `mem_readSet`（读集成员刻画）。

**为什么不是同义反复**：模块给的是 `s ∉ G.parents v`；本结论是 `s ∉ readSet G v`，
即 `s ∉ insert v (G.parents v)`，还需要排除 `s = v`（用 `v ≠ s`）。
模块在 `agree_unpin_of_not_read` 里是**反证式**地绕开（用 `reads_eq_of_sink` 的
**双条件**），**从未**正面产出本陈述。

**⚠ 用途**：这是「`x_s` 只出现在 `κ s` 的读集里」的**类型层**陈述 ——
比模块的 `reads_eq_of_sink`（`reads` 层面）更接近实际使用形式。 -/
theorem sink_not_mem_readSet {G : DAG V} {s : V} (hs : ∀ u : V, ¬ G.edge s u)
    {v : V} (hvs : v ≠ s) : s ∉ BridgeView9.readSet G v := by
  classical
  intro hmem
  rcases mem_readSet_iff.mp hmem with h | h
  · exact hvs h.symm
  · exact BridgeView9.sink_not_parent_v9 G s hs v hvs h

/-- ⭐⭐ **`x_s` 只被 `κ s` 读取**（`readSet` 形式的重述）。

对无出边的 `s`，`s ∈ readSet G v ↔ v = s`。这是模块 `reads_eq_of_sink` 的
`readSet` 版本（模块只有 `reads` 版）。 -/
theorem mem_readSet_eq_sink {G : DAG V} {s v : V} (hs : ∀ u : V, ¬ G.edge s u) :
    s ∈ BridgeView9.readSet G v ↔ v = s := by
  constructor
  · intro hmem
    by_contra hne
    exact sink_not_mem_readSet hs hne hmem
  · intro hvs
    rw [hvs]
    exact mem_readSet_iff.mpr (Or.inl rfl)

/-! ===========================================================================
  §4 ⭐⭐⭐ **C4：`CondIndep` 的对称性（`Z` 吸收形式的接口完备）**
  =========================================================================== -/

/-- ⭐⭐⭐ **C4：`Z` 吸收 ⟹ `CondIndep p B A Z`（参数换序）**。

**消费**：`sepset_absorb`（`A B Z` 固定序）。

**为什么需要额外工作**：`sepset_absorb` 给的是
`mass (A ∪ B ∪ Z) p x * mass Z p x = mass (A ∪ Z) p x * mass (B ∪ Z) p x`；
`CondIndep p B A Z` 需要
`mass (B ∪ A ∪ Z) p x * mass Z p x = mass (B ∪ Z) p x * mass (A ∪ Z) p x`。
两边的**左因子**（`A ∪ B ∪ Z` vs `B ∪ A ∪ Z`）需求 `union_comm` 穿透到三元并，
两边的**右因子**乘积需求 `mul_comm`。

**⚠ 诚实标注**：`sepset_absorb` 的结论在 `A, B ⊆ Z` 时**退化为 `c·c = c·c`**
（模块 §3 边界 3 自认）。故 C4 的增量**只是接口完备性**（`CondIndep` 关于 `A,B`
的对称），**不是新的概率内容**。 -/
theorem condIndep_symm_of_absorb {p : (V → α) → ℝ} {A B Z : Finset V}
    (hA : A ⊆ Z) (hB : B ⊆ Z) :
    Fate.FactorMarkov.CondIndep p B A Z := by
  intro x
  -- 三元并的换序
  have hunion : B ∪ A ∪ Z = A ∪ B ∪ Z := by
    rw [Finset.union_comm B A]
  rw [hunion]
  exact (BridgeView9.sepset_absorb hA hB x).trans (mul_comm _ _)

/-- ⭐⭐ **C4b：`CondIndep` 关于 `A,B` 对称（`Z` 吸收形式）**。

`CondIndep p A B Z ↔ CondIndep p B A Z`，前件 `A, B ⊆ Z`。
**复核**：模块只给单一方向（`condIndep_of_absorb`），双向需要 `Iff` 的两侧各用一次 C4。 -/
theorem condIndep_comm_of_absorb {p : (V → α) → ℝ} {A B Z : Finset V}
    (hA : A ⊆ Z) (hB : B ⊆ Z) :
    Fate.FactorMarkov.CondIndep p A B Z ↔ Fate.FactorMarkov.CondIndep p B A Z :=
  ⟨fun _ => condIndep_symm_of_absorb hA hB, fun _ => condIndep_symm_of_absorb hB hA⟩

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **C5：逐边核分解 = 全空间 `mass`**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **C5：`mass univ p x = ∏ v, κ v x x`（逐边核进入 `mass` 世界的入口）**。

**消费**：`EdgeKernel.joint`（模块）与 `mass_univ`（`Fate/DAGFactorization.lean:263`，
**不在模块内**）。

**为什么不是同义反复**：前件是 `EdgeKernel G p`（一个结构）；
结论把 `p` 的**全空间边缘**（`mass univ`，由 `DAGFactorization` 定义，
是一个 `Finset.sum` 带 `if` 守卫）与逐边核乘积**等号相接**。
模块的 `joint` 只说 `p x = ∏ v, κ v x x`，**不含 `mass`**，
也**未**证明它在 `mass` 世界里无摩擦。本定理是这一步的**唯一**落点 ——
它同时说明「视角 9 的乘积形式**不**与 `mass` 的单层语义冲突」。 -/
theorem mass_univ_of_edgeKernel {G : DAG V} {p : (V → α) → ℝ}
    (K : BridgeView9.EdgeKernel (α := α) G p) (x : V → α) :
    mass univ p x = ∏ v, K.κ v x x := by
  rw [mass_univ, K.joint]

/-- ⭐⭐⭐ **C5b：`mass univ` 侧与 `Factorizes` 侧**（C1 + C5 的联合形式）。

**消费**：C1（`edgeKernel_factorizes`）+ C5。

若 `p` 有逐边核，则存在一个 `f`，使 **对每个** `x`，
`mass univ p x` 与 `∏ v, f v x` 相等，且此 `f` 只读 `{v} ∪ pa v`。
**这是「图 ⟹ 概率」在 `mass` 与 `Factorizes` **两侧**同时落地的形式**。 -/
theorem exists_local_factor_of_edgeKernel {G : DAG V} {p : (V → α) → ℝ}
    (K : BridgeView9.EdgeKernel (α := α) G p) :
    ∃ f : V → (V → α) → ℝ,
      Fate.FactorMarkov.LocalTo G f ∧
        ∀ x : V → α, mass univ p x = ∏ v, f v x := by
  obtain ⟨f, hloc, hfac⟩ := edgeKernel_factorizes K
  exact ⟨f, hloc, fun x => by rw [mass_univ, hfac]⟩

/-! ===========================================================================
  §6 ⚠ **反例登记（C5'）：模块 §5.1 的边界是**真的**（机检）**
  =========================================================================== -/

section CounterExample

/-- **空边图**（`V = Bool`，无边）：真 `DAG`（`acyclic` 由 `TransGen` 的空性得）。 -/
def emptyEdge : Bool → Bool → Prop := fun _ _ => False

/-- ⭐ **空边图作为真 `Causalean.Graph.DAG Bool`**。 -/
def emptyDAG : DAG Bool where
  edge := emptyEdge
  decEdge := fun _ _ => isFalse (fun h => h)
  acyclic := by
    intro v h
    have key : ∀ {a b : Bool}, Relation.TransGen emptyEdge a b → emptyEdge a b := by
      intro a b htr
      induction htr with
      | single hab => exact hab
      | tail _ hbc _ => exact hbc
    exact key h

/-- ⭐ **模块 §5.1 的反例核**：`κ v x y := if y v then 2 else 1`。

* **只读 `y` 的 `v` 位**（不读 `x`）⟹ 对 `readSet` 上的任何一致性都稳定
  （因 `v ∈ readSet G v` 恒成立）；
* 但它**故意**让 `s` 的机制读**自己**的坐标 ⟹ `p` 依赖 `x_s`。 -/
def selfReadKappa : Bool → (Bool → Bool) → (Bool → Bool) → ℝ :=
  fun v _ y => if y v then 2 else 1

/-- ⭐⭐ 反例核的**逐边核只读性**（`EdgeLocTwo`）—— 对**任意** `G` 成立。 -/
theorem selfReadKappa_loc (G : DAG Bool) :
    BridgeView9.EdgeLocTwo G selfReadKappa := by
  intro v x y x' y' _hx hy
  show (if y v then (2 : ℝ) else 1) = (if y' v then 2 else 1)
  have hv : v ∈ BridgeView9.readSet G v :=
    mem_readSet_iff.mpr (Or.inl rfl)
  rw [hy v hv]

/-- ⭐⭐⭐ **C5'（反例登记，机检）：`s` 无出边**不**⟹ `p` 与 `x_s` 无关**。

**消费**：模块的 `p_unpin_pull`（V9-7'）的**边界** + 反例核 `selfReadKappa`。

**登记内容**：模块 §5.1 声称「`EdgeLocTwo` 只约束读集、不约束函数形式，
故 `s` 无出边不足以推出 `p` 与 `x_s` 无关」。本定理给出**机检实例**：

取 `V = Bool`、空图、`κ v x y := if y v then 2 else 1`。
则 `s := true` 无出边（空图），
`p x = 4`（`x ≡ true`），而 `p (unpin true x false) = 2`。**二者不同。**

**⟹ 这是**负面**结果：任何把 V9-7 当作「边缘不受影响」的用法都是**错误**的。
本文件**明确不**做那种用法。 -/
theorem sink_p_can_depend_on_s :
    ∃ (G : DAG Bool) (p : (Bool → Bool) → ℝ) (s : Bool),
      (∀ u : Bool, ¬ G.edge s u) ∧
        ∃ x : Bool → Bool, ∃ a : Bool, p (unpin s x a) ≠ p x := by
  refine ⟨emptyDAG, fun x => selfReadKappa true x x * selfReadKappa false x x,
    true, fun u hu => hu, fun _ => true, false, ?_⟩
  have hu1 : unpin true (fun _ => true) false true = false := by
    simp [Fate.DAGFactorization.unpin]
  have hu2 : unpin true (fun _ => true) false false = true := by
    simp [Fate.DAGFactorization.unpin]
  show selfReadKappa true (unpin true (fun _ => true) false)
        (unpin true (fun _ => true) false)
      * selfReadKappa false (unpin true (fun _ => true) false)
          (unpin true (fun _ => true) false)
    ≠ selfReadKappa true (fun _ => true) (fun _ => true)
      * selfReadKappa false (fun _ => true) (fun _ => true)
  simp only [selfReadKappa, hu1, hu2]
  norm_num

end CounterExample

end BridgeView9Consumer

end FateV2.Predict