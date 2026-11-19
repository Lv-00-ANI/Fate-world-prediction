import FateWorld.FateV2.Predict.FactorRecursionRouteB
/-!
  # Predict · AncestralInheritanceRouteB

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AncestralInheritanceRouteB.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorRecursionRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/AncestralInheritanceRouteB` —— **第 4 路：`LMG` 在祖先闭包上的继承**

  ## 本文件结论速览

  | # | 名称 | 状态 | 内容 |
  |---|---|---|---|
  | **A1** | `mass_of_reads` | ✅ **零缺口** | `p` 只读 `S` 内 ⟹ `mass S p x = \|α\|^(\|V\|−\|S\|) · p x` |
  | **A2** | `mass_const` | ✅ **零缺口** | 常函数的质量（A1 特例）|
  | **A3** | `lmg_at_sink_trivial` | ✅ **零缺口** | **汇点处 `LMG` 恒真**（无内容）|
  | **A4** | `lmg_forces_desc_marginal` | ✅ **零缺口** | **`LMG` 退化**：`LMG` 在 `v` 处 ⟺ 在 `mass(nd∪pa) ≠ 0` 时 `p` 等于「对后代边缘化」|
  | **A5** | `chain3_const_factorizes` | ✅ **零缺口** | 常值 `p ≡ 2` 在 `chainDAG` 上**确实** `Factorizes` |
  | **A6** | `chain3_const_not_lmg` | ✅ **零缺口** | 同一 `p` **不满足** `LMG` |
  | **A7** | **`routeB_gap_segment1_is_false`** | ✅ **零缺口** | ⟹ `Factorizes_implies_LMG_Gap`（路线乙登记的段 1 缺口）**是假命题** |
  | **A8** | `factorizes_single_const` | ✅ **零缺口** | 既有 `Factorizes` 在**单点图**上只能表达常值 `p`（**不是**因子分解）|
  | **A9** | `not_factorizes_single` | ✅ **零缺口** | 非常值分布在单点图上**不**可（既有定义下）因子分解 |
  | **A8** | `FactorizesC` / `LMGc`（定义）| ✅ 定义 | **修正版**：因子读 `{v} ∪ pa(v)`；`LMGc` = 正确的乘性条件独立 |
  | **B1** | `ancestorClosed`（定义）| ✅ 定义 | 祖先闭包（对 `pa` 封闭）|
  | **B2** | **`factorizesC_block_split`** | ✅ **零缺口** | **继承的**真正**可证一半**：祖先闭集 `A` 上 `p = f · h`，`f` 只读 `A`，`h` 只读 `B ∪ C` |
  | **B3** | `factorizesC_block_CI` | ⚠ **`Prop` 缺口**（不进前件）| 由 B2 推出的乘性 CI `(A\C) ⊥ B \| C`（证明卡点见 §5）|
  | **B4** | ~~`AncestralInheritance_Gap`~~ | ⚠ **文字登记（原 `:- True` 占位已删除）**| 段 2 所需的「`LMG` 在祖先闭包上继承」——**文字版被 §6 反例否定**；原 `Prop` 以 `→ True` 结尾故恒真，第 6 条子代理审计已删（无下游引用）|
  | **B5** | `inducedEdge` / `inducedSubgraph` | ✅ **定义 + 零缺口引理** | **诱导子图 `G[A]`（`B级 #7` 的缺口登记项现已落地为真实定义）**，见 §7 |
  | **B6** | `mem_pa_inducedSubgraph` 等 | ✅ **零缺口** | 诱导子图的父集 / 祖先 / 边子集与原图的关系（§7）|

  **无 `sorry` / 无 `axiom`**；所有未证目标都写成显式 `Prop` 并注明「不进下游」。

  ### ⚠ `B级 #7` 缺口登记：「缺 `InducedSubgraph`」——本轮的处置结论

  `B级 #7` 的原始形态是一个 `def … := LMGc p G → True` 的占位（第 618 轮已删）。
  它背后的**真实**缺口是：`CausDAG`（即 `Causalean.Graph.DAG`）**没有诱导子图构造**，
  所以 §6 的「`mass B p` 在诱导子图上满足 `LMGc`」**连陈述都写不出来**。

  **本轮实测（`grep` 两种模式确认，见下）的结论**：

  1. `Causalean.Graph.DAG` 的结构字段只有 `edge / decEdge / acyclic`（**无**顶点集字段，
     `V` 是类型参数）⟹ 「诱导子图」在 **同一顶点类型 `V`** 上只能是
     **边关系过滤**，不能是子类型 `↥A` 版本（两者是不同口径，见下）。
  2. Mathlib/Causalean **没有**提供 `DAG.induce` 之类的通用 API。唯一的同名前例是
     `Causalean.Graph.SWIGGraph.inducedDag`（在 `Causalean/Graph/Induce.lean`），
     但它的定义域是 **`SWIGGraph N`** 的 split node，**不是** `DAG V`，
     **无法直接复用**。
  3. 本项目此前已在 **两处**各自重造过（**均为本文件之外的模块，本文件不修改它们**）：
     * `Fate/BridgeB3.lean`：`induce A : DAG V`（同顶点类型口径）；
     * `Fate/BridgeB1Final.lean`：`subDAG G A : DAG ↥A`（子类型口径）。

  **故本轮的处置**：在本文件 **§7 新增** `inducedEdge` / `inducedSubgraph`
  （**同顶点类型 `DAG V`** 口径，与 §6 的 `mass B p : (A → α) → ℝ` 讨论口径一致），
  并给出**真正用到 `G.edge` 与 `A`** 的关系引理（§7 全部零缺口）。

  **⚠ 诚实边界（不声称「诱导子图已实现」到超出下面的范围）**：
  * ✅ 已做：`inducedSubgraph G A : DAG V` 的**定义**、无环性、边子集、
    父集刻画、祖先关系保持、全集退化、空集无边的**非平凡性**（§7）。
  * ❌ **未做**：`§6` 里「`mass B p` 在 `G[A]` 上满足 `LMGc`」这个**命题本身**
    **仍未陈述、更未证明**——§6 已证明其文字版为**假**（explaining-away），
    所以它**不该**被写成任何 `Prop` 占位。本轮的 `inducedSubgraph` 只**消除
    「缺定义」这一登记项**，**不**表示 §6 的继承目标已可达。
  * ❌ **未做**：`↥A` 子类型口径的版本（本文件不提供；`BridgeB1Final.subDAG` 已有）。

  ---

  ## §0 ⚠ 本路**必须**先报告的两个坏消息（均机器验证）

  第 4 路分配到的任务是「证 `LMG` 在祖先闭包上继承（子图仍因子分解）」。
  在动手之前先检查了 `Fate/FactorRecursionRouteB.lean` 的 `Factorizes` / `LMG`
  两个定义，**发现两者都不是它们名字所说的东西**：

  1. **`Factorizes` 的读集少了 `v` 自己。** 定义要求
     `∀ v, φ v` 只读 `pa G v`，即 `φ_v` **不读 `x_v`**。标准因子分解要求
     `φ_v` 读 `{v} ∪ pa(v)`。后果：`Factorizes` 在**只有一个顶点的图**上就
     只能表达**常值** `p`（见 §2 的推论 A5、A7 的机制）。
  2. **`LMG` 的乘性条件独立写错了。** 正确的乘性形式是
     `mass({v}∪pa) · mass(nd∪pa) = mass(pa) · mass({v}∪nd∪pa)`
     （即 `p_{v|pa} · p_{nd|pa} = p_{v,nd|pa}`）。文件里写的是
     `p x · mass(nd∪pa) = mass({v}∪nd∪pa) · mass(nd∪pa)`，
     它在 `mass(nd∪pa) ≠ 0` 时**等价于**「`p` 对 `v` 的后代取边缘后不变」
     （A4），而不是局部 Markov 性。

  **机器检证的反例（A5 + A6）**：常值 `p ≡ 2` 在 `chainDAG`（`Fin 3` 三元链）
  上**满足** `Factorizes`，却**不满足** `LMG`。于是路线乙登记的
  `Factorizes_implies_LMG_Gap`（`Factorizes ⟹ LMG`）**是假命题**（A7）。

  ⟹ **段 1（`Factorizes ⟹ LMG`）与段 2（`LMG ⟹ GM`）在现有定义下都不可能证完**，
  必须先把两个定义改成 §3 的 `FactorizesC` / `LMGc`。本文件余下部分给出
  **修正后**的继承（§4 的 B2 是可证的；§5/§6 说明为什么**完整**继承仍然不能靠
  「边际化」得到）。

  ⚠ 本文件**不修改** `Fate/FactorRecursionRouteB.lean`（那是 1/2/3 路的资产），
  只在**本文件**内定义修正版并标注二者的关系。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace AncestralInheritanceRouteB

set_option linter.unusedSectionVars false

open Finset FateV2.Predict.DAGFactorization FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 ⭐ 两个基础引理（零缺口）
  =========================================================================== -/

/-- ⭐⭐ **A1**：若 `p` 只读 `S` 内的坐标，则 `mass S p x = |α|^(|V|-|S|) · p x`。

纤维 `{w : w|_S = x|_S}` 上 `p` 恒等于 `p x`，求和只是「个数 × 值」，
个数由 `card_fiber` 给出。**零缺口。** -/
lemma mass_of_reads (S : Finset V) (p : (V → α) → ℝ)
    (hp : ∀ x y, (∀ u ∈ S, x u = y u) → p x = p y) (x : V → α) :
    mass S p x = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * p x := by
  classical
  unfold mass
  have hterm : ∀ w : V → α, (if (∀ u ∈ S, w u = x u) then p w else 0)
      = if (∀ u ∈ S, w u = x u) then p x else 0 := by
    intro w
    by_cases h : ∀ u ∈ S, w u = x u
    · rw [if_pos h, if_pos h, hp w x h]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl (fun w _ => hterm w)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    FactorRecursionRouteB.card_fiber, Nat.cast_pow]

/-- ⭐ **A2**：常函数的 `mass`。A1 的特例。 -/
lemma mass_const (S : Finset V) (c : ℝ) (x : V → α) :
    mass S (fun _ => c) x = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * c :=
  mass_of_reads S (fun _ => c) (fun _ _ _ => rfl) x

/-! ===========================================================================
  §2 ⭐⭐⭐ 对既有 `LMG` 的审计（全部机器验证）

  ### 2.1 `LMG` 在汇点处恒真

  `LMG` 在 `v` 处的等式里，集合是 `nd(v) ∪ pa(v)` 与 `insert v (nd(v) ∪ pa(v))`。
  由于 `descendants(v)` 之外的一切都在 `nd(v) ∪ pa(v) ∪ {v}` 里，两个集合相等的
  充要条件是 `v` 没有后代。此时等式两边同形，**恒真**。

  ⟹ `LMG` 只在**非汇点**上有内容；这与局部 Markov 性（每个点都有内容）不同。 -/

/-- `v` 的父集是 `v` 的非后代、且 `v ∉ pa v`：故 `nd ∪ pa` 不含 `v`。 -/
lemma not_mem_nd_union_pa (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    v ∉ G.nonDescendants v ∪ pa G v := by
  intro h
  rw [mem_union] at h
  rcases h with h | h
  · exact (mem_filter.mp h).2.2 rfl
  · exact not_mem_pa_self G v h

/-- **汇点刻画**：`insert v (nd v ∪ pa v) = univ` ⟺ `v` 无后代。

（⟸ 方向：`nd(v)` 含所有既非 `v` 亦非 `v` 后代的点，`pa(v)` 含其余… 严格说，
`nd(v) ∪ pa(v) ∪ {v}` = 全体「非 `v` 后代」的点，故当 `v` 无后代时它就是 `univ`。） -/
lemma insert_nd_pa_eq_univ_iff (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    insert v (G.nonDescendants v ∪ pa G v) = univ
      ↔ ∀ w : V, ¬ G.isAncestor v w := by
  constructor
  · intro h w hw
    have hmem : w ∈ insert v (G.nonDescendants v ∪ pa G v) := by rw [h]; exact mem_univ w
    rw [mem_insert, mem_union] at hmem
    rcases hmem with rfl | h' | h'
    · exact G.isAncestor_irrefl w hw
    · exact (mem_filter.mp h').2.1 hw
    · -- `w ∈ pa v` 即 `edge w v`，则 `w → v ⇝ w`，成环
      have hwv : G.edge w v := mem_pa.mp h'
      exact G.isAncestor_irrefl w (G.isAncestor_trans (FateV2.Modeling.Graph.DAG.isAncestor.edge hwv) hw)
  · intro h
    refine Finset.eq_univ_iff_forall.mpr (fun w => ?_)
    by_cases hw : w = v
    · subst hw; exact mem_insert_self _ _
    · rw [mem_insert, mem_union]
      exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ w, h w, hw⟩))

/-- ⭐⭐ **A3**：`LMG` 在**无后代**的点上恒真（无任何内容）。

**这正是 `LMG` 与局部 Markov 性的关键区别**：局部 Markov 性对每个点都有内容
（`v ⊥ nd(v) | pa(v)` 对汇点也说的是「`v` 与所有非父点条件独立」，非平凡），
而这里的 `LMG` 在汇点退化成 `x = x`。 -/
theorem lmg_at_sink_trivial (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) {v : V}
    (h : ∀ w : V, ¬ G.isAncestor v w) :
    ∀ x, p x * mass (G.nonDescendants v ∪ pa G v) p x
       = mass (insert v (G.nonDescendants v ∪ pa G v)) p x
         * mass (G.nonDescendants v ∪ pa G v) p x := by
  intro x
  have hins := (insert_nd_pa_eq_univ_iff G v).mpr h
  rw [hins, mass_univ]

/-- ⭐⭐⭐ **A4：`LMG` 退化的精确形式。**

`LMG` 在 `v` 处的等式两边含公因子 `mass (nd∪pa) p x`；若它非零，则
`p x = mass (insert v (nd∪pa)) p x`，即 **`p` 在 `v` 的后代上取边缘后不变**。

这不是局部 Markov 性，而是「`p` 不依赖后代」——对几乎一切真实分布为假。
（`LMG` 的等式本身只是这个等式两边同乘 `mass (nd∪pa)`。） -/
theorem lmg_forces_desc_marginal (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) (v : V)
    (hlmg : ∀ x, p x * mass (G.nonDescendants v ∪ pa G v) p x
       = mass (insert v (G.nonDescendants v ∪ pa G v)) p x
         * mass (G.nonDescendants v ∪ pa G v) p x)
    {x : V → α} (hne : mass (G.nonDescendants v ∪ pa G v) p x ≠ 0) :
    p x = mass (insert v (G.nonDescendants v ∪ pa G v)) p x := by
  have h := hlmg x
  exact mul_right_cancel₀ hne h

/-- ⭐⭐ **A4'**：反过来，A4 的等式也推出 `LMG` 在该点的等式（两边乘同一个数）。 -/
theorem desc_marginal_implies_lmg (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) (v : V)
    (h : ∀ x, p x = mass (insert v (G.nonDescendants v ∪ pa G v)) p x) :
    ∀ x, p x * mass (G.nonDescendants v ∪ pa G v) p x
       = mass (insert v (G.nonDescendants v ∪ pa G v)) p x
         * mass (G.nonDescendants v ∪ pa G v) p x := by
  intro x; rw [h x]

/-! ### 2.2 ⭐⭐⭐ 反例：`Factorizes` 成立而 `LMG` 不成立

取 `α = Bool`、`V = Fin 3`、`G = chainDAG`（`0 → 1 → 2`）、`p ≡ 2`。

* `Factorizes p G`：取 `φ_0 ≡ 2, φ_1 ≡ 1, φ_2 ≡ 1`（都只读 `pa`，因为常值），
  `∏ φ = 2 = p`。 ✅（A5）
* `¬ LMG p G`：在 `v = 1` 处 `nd(1) = {0} = pa(1)`，等式变成
  `2 · mass{0} p x = mass{0,1} p x · mass{0} p x`，即 `2·8 = 4·8`，即 `16 = 32`。 ❌（A6） -/

/-- `chainDAG` 在 `v = 1` 处的非后代集与父集（`decide` 算出）。 -/
lemma chain3_nd_pa_one :
    FateV2.Modeling.Graph.DAG.nonDescendants chainDAG (1 : Fin 3) = {0} ∧
      pa chainDAG (1 : Fin 3) = {0} := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⭐ **A5**：常值 `p ≡ 2` 在 `chainDAG` 上满足（既有的，读集偏小的）`Factorizes`。 -/
theorem chain3_const_factorizes :
    FactorRecursionRouteB.Factorizes (α := Bool) (fun _ : Fin 3 → Bool => (2 : ℝ))
      chainDAG := by
  refine ⟨fun v _ => if v = (0 : Fin 3) then 2 else 1, ?_, ?_⟩
  · intro v x y _; rfl
  · intro x
    rw [Fin.prod_univ_three]
    norm_num [Fin.ext_iff]

/-- ⭐⭐⭐ **A6**：同一个 `p ≡ 2` **不满足** `LMG`（`v = 1` 处 `16 ≠ 32`）。 -/
theorem chain3_const_not_lmg :
    ¬ FactorRecursionRouteB.LMG (α := Bool) (fun _ : Fin 3 → Bool => (2 : ℝ)) chainDAG := by
  intro h
  obtain ⟨hnd, hpa⟩ := chain3_nd_pa_one
  have h1 := h 1 (fun _ => true)
  simp only [hnd, hpa] at h1
  have e1 : mass ({(0 : Fin 3)} ∪ {(0 : Fin 3)}) (fun _ : Fin 3 → Bool => (2 : ℝ))
      (fun _ => true) = 8 := by
    rw [mass_const]; norm_num [Finset.card_singleton]
  have e2 : mass (insert (1 : Fin 3) ({(0 : Fin 3)} ∪ {(0 : Fin 3)}))
      (fun _ : Fin 3 → Bool => (2 : ℝ)) (fun _ => true) = 4 := by
    rw [mass_const]
    have hcard : (insert (1 : Fin 3) ({(0 : Fin 3)} ∪ {(0 : Fin 3)}) : Finset (Fin 3)).card = 2 := by
      decide
    rw [hcard]; norm_num
  rw [e1, e2] at h1
  norm_num at h1

/-- ⭐⭐⭐⭐ **A7：路线乙登记的段 1 缺口是假命题。**

`Factorizes_implies_LMG_Gap p G` 的定义就是 `Factorizes p G → LMG p G`
（`factorizes_implies_LMG_gap_unfold`）。但 A5 + A6 给出一个反例，
故该 `Prop` **不可证**（它是假的）。

**⟹ 段 1（`Factorizes ⟹ LMG`）在现有定义下不可达；必须先修定义（§3）。** -/
theorem routeB_gap_segment1_is_false :
    ¬ FactorRecursionRouteB.Factorizes_implies_LMG_Gap
        (α := Bool) (fun _ : Fin 3 → Bool => (2 : ℝ)) chainDAG := by
  rw [FactorRecursionRouteB.factorizes_implies_LMG_gap_unfold]
  intro h
  exact chain3_const_not_lmg (h chain3_const_factorizes)


/-- ⭐⭐ 单点图（无边），用于演示既有 `Factorizes` 的读集缺陷。 -/
def singleDAG : FateV2.Modeling.Graph.DAG (Fin 1) where
  edge := fun _ _ => False
  decEdge := fun _ _ => inferInstanceAs (Decidable False)
  acyclic := by
    intro v h
    have key : ∀ {a b : Fin 1}, Relation.TransGen (fun _ _ : Fin 1 => False) a b → False := by
      intro a b htr
      induction htr with
      | single hab => exact hab
      | tail _ hbc _ => exact hbc
    exact key h

/-- 单点图上 `pa` 为空（`decode`）。 -/
lemma pa_single (v : Fin 1) : pa singleDAG v = ∅ := by
  ext u; simp [pa, singleDAG]

/-- ⭐ **A8：既有 `Factorizes` 在单点图上只能表达常值。**

因为 `φ_0` 只被要求读 `pa(0) = ∅`，它根本**不读 `x_0`**，
于是 `p = φ_0` 与 `x` 无关。

**这直接说明 `Factorizes` 不是因子分解**：标准因子分解 `φ_v(x_v|x_{pa(v)})`
在单点图上可表达**任何**分布。 -/
theorem factorizes_single_const {p : (Fin 1 → Bool) → ℝ}
    (h : FactorRecursionRouteB.Factorizes p singleDAG) : ∀ x y, p x = p y := by
  obtain ⟨φ, hφ, hp⟩ := h
  intro x y
  have hc : ∀ v : Fin 1, φ v x = φ v y := by
    intro v
    refine hφ v x y (fun u hu => ?_)
    rw [pa_single] at hu
    exact absurd hu (by simp)
  rw [hp x, hp y]
  simp only [Fin.prod_univ_one]
  exact hc 0

/-- ⭐⭐ **A9：非常值分布在单点图上**不可**因子分解**（既有定义）。 -/
theorem not_factorizes_single (p : (Fin 1 → Bool) → ℝ) (hnc : ∃ x y, p x ≠ p y) :
    ¬ FactorRecursionRouteB.Factorizes p singleDAG := by
  intro h
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (factorizes_single_const h x y)

/-! ===========================================================================
  §3 ⭐⭐ 修正版定义：`FactorizesC` / `LMGc`

  与 `Fate/FactorRecursionRouteB.lean` 的差别只有两处，都是**加回**标准内容：

  * `FactorizesC`：`φ v` 读 **`{v} ∪ pa(v)`**（stdlib 因子 `φ_v(x_v|x_{pa(v)})`）；
  * `LMGc`：乘性条件独立用**正确的四个边缘**：
    $$p_{v\mid pa} \cdot p_{nd\mid pa} = p_{v,nd\mid pa}
      \iff \mathrm{mass}_{\{v\}\cup pa}\cdot\mathrm{mass}_{nd\cup pa}
        = \mathrm{mass}_{pa}\cdot\mathrm{mass}_{\{v\}\cup nd\cup pa}.$$
  =========================================================================== -/

/-- ⭐⭐⭐ **因子分解（修正版）**：`φ v` 只读 `{v} ∪ pa G v`。 -/
def FactorizesC (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  ∃ (φ : V → (V → α) → ℝ),
    (∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y) ∧
    ∀ x, p x = ∏ v, φ v x

/-- ⭐⭐⭐ **局部 Markov（修正版，乘性条件独立）**：`v ⊥ nd(v) | pa(v)`。 -/
def LMGc (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  ∀ v : V, ∀ x : V → α,
    mass (insert v (pa G v)) p x * mass (G.nonDescendants v ∪ pa G v) p x
      = mass (pa G v) p x * mass (insert v (G.nonDescendants v ∪ pa G v)) p x

/-- **修正版之间的蕴含目标**（段 1 的正确陈述）。**登记为 `Prop`，不进下游。** -/
def FactorizesC_implies_LMGc_Gap (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  FactorizesC p G → LMGc p G

/-- 自反检查：该 `Prop` 就是字面蕴含。 -/
theorem factorizesC_implies_LMGc_gap_unfold (p : (V → α) → ℝ)
    (G : FateV2.Modeling.Graph.DAG V) :
    FactorizesC_implies_LMGc_Gap p G = (FactorizesC p G → LMGc p G) := rfl

/-! **为什么 `FactorizesC ⟹ LMGc` 是（真且可证的）**（论文级证明，代码中未落地）：

设 `p = ∏_w φ_w`，`φ_w` 读 `{w} ∪ pa(w)`。固定 `v`，记
`D = descendants(v)`、`nd = nd(v)`、`pa' = pa(v)`。由 DAG 的图论事实
`V = {v} ⊔ D ⊔ nd ⊔ pa'`（`nonDescendants` 的定义 + `v ∉ pa v`），且

* `w ∈ nd ∪ pa'` 时 `{w} ∪ pa(w) ⊆ nd ∪ pa'`（若 `pa(w)` 含 `v` 或 `D` 中的点，
  则 `w` 是 `v` 的后代，矛盾）；
* `w ∈ {v} ∪ D` 时 `{w} ∪ pa(w) ⊆ {v} ∪ D ∪ pa' = V \ nd`（祖先链不过 `nd`）。

于是 `p = F(x_{v∪D∪pa'}) · G(x_{nd∪pa'})`，其中 `G = ∏_{w∈nd∪pa'} φ_w`、
`F = ∏_{w∈{v}∪D} φ_w`。令
`μ(x_{pa'}) = Σ_{x_{v∪D}} F`、`ν(x_{pa'}) = Σ_{x_{nd}} G`、`F̃(x_v,x_{pa'}) = Σ_{x_D} F`，
四个 `mass` 分别是

| `mass` | 值 |
|---|---|
| `mass (nd∪pa')` | `μ · G` |
| `mass pa'` | `μ · ν` |
| `mass ({v}∪pa')` | `F̃ · ν` |
| `mass ({v}∪nd∪pa')` | `G · F̃` |

交叉相乘两边都等于 `F̃ · ν · μ · G`。 ∎

卡在哪：需要 `mass` 的**乘积分离**（`mass_mul` 已有，但要求因子读集 ⊆ 求和集）
与上述四个集合的**分割记账**；文本量约 4 个 `mass` 展开 + 若干 `Finset` 子集引理。
本轮**未落地**，故登记为 `_Gap`。 -/

/-! ===========================================================================
  §4 ⭐⭐⭐ 继承的**可证一半**：祖先闭集上的分块分解

  「`LMG` 在祖先闭包上继承」的正确数学内容分两步：
  **(i)** 把 `p` 沿「祖先闭集 / 其余部分」**分块**成两个因子（本节，可证）；
  **(ii)** 由分块推出乘性 CI（§5，登记为缺口，并说明为什么**不能**由此得到
  完整的「子图仍因子分解」——§6 反例）。

  ### 4.1 祖先闭集

  注意：这里用 **`pa`-封闭** 而不用 `CausDAG.ancestralSet`（后者是 `isAncestor`
  的口径，见 `CausDAG.ancestralSet`）；对 DAG 而言两者等价（`pa`-封闭 ⟹ 祖先封闭
  沿路径归纳），本文件只用 `pa` 口径，因为因子只读 `pa`。 -/

/-- ⭐ **B1**：`A` 对 `pa` 封闭（= 祖先闭集）。 -/
def AncestorClosed (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) : Prop :=
  ∀ v ∈ A, pa G v ⊆ A

/-- `B` 的父集（作为集合）。 -/
def paSet (G : FateV2.Modeling.Graph.DAG V) (B : Finset V) : Finset V :=
  B.biUnion (fun v => pa G v)

/-- 分块所需的「边界」：`C = pa(B) \ B`（在 `A` 内，故 `C ⊆ A`）。 -/
def boundary (G : FateV2.Modeling.Graph.DAG V) (B : Finset V) : Finset V :=
  paSet G B \ B

/-- 分块引理：`A` 祖先闭时，`A` 内每个因子只读 `A`。 -/
lemma factor_reads_within_ancestorClosed {G : FateV2.Modeling.Graph.DAG V}
    {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y)
    {A : Finset V} (hA : AncestorClosed G A) :
    ∀ x y, (∀ u ∈ A, x u = y u) → (∏ v ∈ A, φ v x) = ∏ v ∈ A, φ v y := by
  intro x y hxy
  refine Finset.prod_congr rfl (fun v hv => ?_)
  exact hφ v x y (fun u hu => hxy u (by
    rw [mem_insert] at hu
    rcases hu with rfl | hu
    · exact hv
    · exact hA v hv hu))

/-- 分块引理：`B` 内每个因子只读 `B ∪ boundary`。 -/
lemma factor_reads_within_block {G : FateV2.Modeling.Graph.DAG V}
    {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y)
    {B : Finset V} :
    ∀ x y, (∀ u ∈ B ∪ boundary G B, x u = y u) → (∏ v ∈ B, φ v x) = ∏ v ∈ B, φ v y := by
  intro x y hxy
  refine Finset.prod_congr rfl (fun v hv => ?_)
  refine hφ v x y (fun u hu => hxy u ?_)
  rw [mem_insert] at hu
  rcases hu with rfl | hu
  · exact mem_union_left _ hv
  · rw [mem_union]
    by_cases huB : u ∈ B
    · exact Or.inl huB
    · refine Or.inr ?_
      rw [boundary, mem_sdiff]
      exact ⟨Finset.mem_biUnion.mpr ⟨v, hv, hu⟩, huB⟩

/-- ⭐⭐⭐ **B2（分块分解）：祖先闭集上的因子分解仍然「分块」。**

设 `FactorizesC p G`、`A` 对 `pa` 封闭、`B = Aᶜ`。则存在两个因子 `f h`：

* `f` 只读 `A` 内的坐标；
* `h` 只读 `B ∪ boundary G B` 内的坐标；
* `p x = f x * h x`。

**这是「限制到祖先闭集」的可证一半**（纯乘积分离，无需任何 `mass` 运算）。
`f` 只读 `A` 说明：**把 `A` 之外的坐标全改掉，`p` 的 `A` 部分不动**；
这正是 §5 推出乘性 CI 的起点。 -/
theorem factorizesC_block_split {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : FactorizesC p G) {A : Finset V} (hA : AncestorClosed G A) :
    ∃ (f h' : (V → α) → ℝ),
      (∀ x y, (∀ u ∈ A, x u = y u) → f x = f y) ∧
      (∀ x y, (∀ u ∈ Aᶜ ∪ boundary G Aᶜ, x u = y u) → h' x = h' y) ∧
      (∀ x, p x = f x * h' x) := by
  classical
  obtain ⟨φ, hφ, hp⟩ := h
  refine ⟨fun x => ∏ v ∈ A, φ v x, fun x => ∏ v ∈ Aᶜ, φ v x, ?_, ?_, ?_⟩
  · exact factor_reads_within_ancestorClosed hφ hA
  · exact factor_reads_within_block (B := Aᶜ) hφ
  · intro x
    rw [hp x, ← Finset.prod_mul_prod_compl (A) (fun v => φ v x)]

/-! ===========================================================================
  §5 ⚠ 继承的**另一半**（登记为缺口）：由 B2 推出乘性 CI

  由 B2 的 `p = f · h`（`f` 只读 `A`，`h` 只读 `B ∪ C`，`C = boundary G B`），
  标准论证给出（记 `p_S = mass S p`）：

  * `p_{A} = f · ĥ`（`ĥ(x_C) = Σ_{x_B} h`）；
  * `p_{C} = ĥ · Φ`（`Φ(x_C) = Σ_{x_{A\C}} f`）；
  * `p_{B∪C} = h · Φ`；
  * `p_{A∪B} = p = f · h`。

  于是 `p · p_C = p_A · p_{B∪C}`，即
  $$(A \setminus C) \perp B \mid C .$$
  这就是「祖先闭集上的继承」的真实内容：**`B` 只通过边界 `C` 与 `A` 交互**。

  **未落地原因**：需要 `mass` 与「分块乘积」的交换（`mass (B∪C) (f·h)` 型
  4 次，每次都要 `mass_mul` + 「`f` 只读 `A`」的纤维不变性）。与 §3 的
  `FactorizesC ⟹ LMGc` 共用同一套记账，本轮未实现。 -/

/-- ⚠ **B3（缺口，显式 `Prop`，不进下游）**：B2 的乘性 CI 推论。

`p · mass C p = mass A p · mass (B ∪ C) p`，其中 `B = Aᶜ`、`C = boundary G B`。
（形式写作一般 `A B`，便于下游按需实例化。） -/
def BlockCI_Gap (p : (V → α) → ℝ) (_G : FateV2.Modeling.Graph.DAG V) (A B C : Finset V) : Prop :=
  ∀ x, p x * mass C p x = mass A p x * mass (B ∪ C) p x

/-! ⚠ **B4（缺口，文字登记，无 `Prop` 占位，不进下游）**：段 2 想要的「继承」文字版。

**⚠ 这是「`LMG` 在祖先闭集上继承」的直白形式，但见 §6：它在正确的 `LMGc`
下是假的**（collider 的 explaining-away）。故此处**只登记文字**。

（陈述：若 `p` 在 `G` 上满足 `LMGc`，且 `A` 对 `pa` 封闭、`B = Aᶜ`，
则 `mass B p`（作为 `A` 上的函数）在**诱导子图**上满足 `LMGc`。
「诱导子图」此处只能以 `G` 本身描述，因为 `CausDAG` 没有诱导子图构造。）

**【第 6 条子代理审计 P0-3：删除原 `:- True` 占位】**

原内容：
```
def AncestralInheritance_Gap (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  LMGc p G → True   -- 占位
```
**问题**：结论是 `True` ⟹ 本 `Prop` **恒真**，下游可当「已证前提」使用。

**为何删而不修**：
* `grep -rn "AncestralInheritance_Gap" Fate/` ⟹ **仅本文件第 23 行（文件头表格）
  与第 465 行（定义处）命中**，**无任何下游引用**，删除不影响编译链。
* 去掉 `→ True` 后只剩 `LMGc p G`，这不是缺口而是前件本身（空内容）。
* 且 §6 已**证明本命题的文字版是假的**（collider explaining-away 反例），保留
  任何 `Prop` 形式都是误导。
-/

/-! ===========================================================================
  §6 ⚠⚠ **为什么完整的「继承」不可能**：collider 的 explaining-away

  §5 的 B3 已经是能从分块分解得到的**最强**结论。想再进一步得到「边际分布
  在子图上仍因子分解 / 仍满足局部 Markov」是**假的**：

  **反例（三元 collider + 一个后代，`explaining-away`）**

  顶点 `0, 1, 2`，边 `0 → 2`、`1 → 2`（collider）。取 `A = {0,1}`（对 `pa` 封闭，
  因为 `pa(0) = pa(1) = ∅`），`B = {2}`，`C = pa({2}) \ {2} = {0,1}`。

  * 任取 `φ_0(x_0) = 1`、`φ_1(x_1) = 1`、`φ_2(x_2,x_0,x_1) = [x_2 = x_0 ∧ x_1]`，
    `p = φ_0 φ_1 φ_2 = φ_2`，则 `FactorizesC p G` 成立（读集 `{2} ⊔ {0,1}` ✅）。
  * 边际 `p_A(x_0,x_1) = Σ_{x_2} p = 1`（对每个 `(x_0,x_1)` 恰有一个 `x_2`）——
    这个例子里 `p_A` 是常数，看不出依赖。改取
    `φ_2(x_2,x_0,x_1) = [x_2 = x_0 ∧ x_1] · w(x_0,x_1)`（`w` 任意非乘积函数），
    则 `p_A = w`，**`0` 与 `1` 在 `p_A` 上不独立**（`x_0, x_1` 一旦相关，
    「`x_2` 的边缘化」就是 explaining-away）。
  * 但 `G[A]` 上 `0,1` 之间**没有边**，`LMGc` 在 `G[A]` 处要求
    `mass{0} p_A · mass{1} p_A = mass ∅ p_A · mass{0,1} p_A`，即 `0 ⊥ 1 | ∅`，
    对非乘积的 `w` **不成立**。

  ⟹ **`LMGc p G` 不蕴含「边际在诱导子图上满足 `LMGc`」**（这里 `p` 在 `G` 上的
  `LMGc` 由 `FactorizesC ⟹ LMGc`（§3 的论文级证明）给出）。`Factorizes` 的
  「子图仍因子分解」同样**不成立**，因为 collider 的道德边 `0 – 1` 不在 `G[A]` 里。

  **⟹ 段 2 的正确路线**（给第 5 路）：不要边际化。改用
  * (i) §4 的**分块**：`p = f(x_A) · h(x_B, x_C)`，`B` 只通过 `C` 影响 `A`；
  * (ii) 沿**拓扑序**从 sink 剥点：剥点用的是 `mass_insert_sum`（**不是**塔性质），
        每剥一个 sink `ℓ`，`LMGc` 在 `ℓ` 处给 `ℓ ⊥ nd(ℓ) | pa(ℓ)`；
  * (iii) 与 `dSep` 的**顶点剥离刻画**对接（`dSep` 在 `insert ℓ ∅` 上的等价形式）。
  也就是说：全局 Markov 要走「**逐点剥离 + 图侧 d-分离同步剥离**」，
  而**不是**「限制到祖先闭子图」。
  =========================================================================== -/


/-! ===========================================================================
  §7 ⭐⭐ **诱导子图 `G[A]`：登记项「缺 `InducedSubgraph`」的落地**

  ### 口径说明（为什么是 `DAG V` 而不是 `DAG ↥A`）

  `Causalean.Graph.DAG V` 的字段是 `edge / decEdge / acyclic`，**顶点集不是字段**
  （由类型参数 `V` 给定）。因此在一张**固定的** `DAG V` 上谈「限制到 `A`」，
  最自然且与 §6 的 `mass B p : (A → α) → ℝ` 讨论口径一致的做法是：
  **保留顶点类型 `V`，把边关系过滤成「两端都在 `A` 内」**。
  这样 `inducedSubgraph G A : DAG V`，原有 `pa` / `nonDescendants` / `mass`
  等一切以 `V` 为索引的工具**可继续使用**，无需子类型搬运。

  （子类型口径 `DAG ↥A` 已由 `Fate/BridgeB1Final.subDAG` 提供，本文件不重复、
  也不修改该模块。）

  ### 本节结论（全部零缺口，且**均非平凡**——真用到 `G.edge` 与 `A`）

  | 编号 | 名称 | 内容 |
  |---|---|---|
  | B5 | `inducedEdge` / `inducedSubgraph` | 诱导子图的边关系与图对象 `DAG V` |
  | B6.1 | `inducedSubgraph_edge_iff` | 边 ⟺ 两端在 `A` 内且是原图边 |
  | B6.2 | `inducedSubgraph_sub` | 诱导子图的边 ⊆ 原图的边 |
  | B6.3 | `inducedEmpty_edge` | **非平凡性**：`A = ∅` 时**没有任何边** |
  | B6.4 | `mem_pa_inducedSubgraph` | 父集刻画（需 `v ∈ A` 才可能成为父）|
  | B6.5 | `pa_inducedSubgraph_subset` | `pa_{G[A]}(v) ⊆ pa_G(v)` |
  | B6.6 | `inducedSubgraph_transGen` | 子图可达 ⟹ 原图可达 |
  | B6.7 | `inducedSubgraph_univ` | `G[univ] = G`（边关系相同）|
  | B6.8 | `inducedSubgraph_edge_of_mem` | 两端在 `A` 内的原图边在 `G[A]` 中保留 |

  **⚠ 本节不陈述、也不证明 §6 的「边际在诱导子图上满足 `LMGc`」**——
  §6 已证明其文字版为**假**（collider explaining-away）。本节只补上
  **缺失的定义**，使那个（假的）目标至少**可写**。
  =========================================================================== -/

/-- ⭐ **B5（边关系）**：`G` 限制到 `A` 上的诱导子图的边——两端都在 `A` 内。 -/
def inducedEdge (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) (u v : V) : Prop :=
  u ∈ A ∧ v ∈ A ∧ G.edge u v

instance inducedEdgeDec (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) :
    DecidableRel (inducedEdge G A) := fun u v =>
  inferInstanceAs (Decidable (u ∈ A ∧ v ∈ A ∧ G.edge u v))

/-- **B5 的辅助**：诱导子图无环——每条子图边搬回 `G`。

⚠ 这里 `G.acyclic` 被**真正使用**：不是 `True` 占位。 -/
theorem inducedEdge_acyclic (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) :
    ∀ v : V, ¬ Relation.TransGen (inducedEdge G A) v v := by
  have key : ∀ {a b : V}, Relation.TransGen (inducedEdge G A) a b →
      Relation.TransGen G.edge a b := by
    intro a b h
    induction h with
    | single hab => exact Relation.TransGen.single hab.2.2
    | tail _ hbc ih => exact ih.tail hbc.2.2
  intro v hv
  exact G.acyclic v (key hv)

/-- ⭐⭐ **B5：诱导子图 `G[A]`**（**同顶点类型 `DAG V`** 口径）。 -/
def inducedSubgraph (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) :
    FateV2.Modeling.Graph.DAG V where
  edge := inducedEdge G A
  decEdge := inducedEdgeDec G A
  acyclic := inducedEdge_acyclic G A

/-- **B6.1**：诱导子图的边 ⟺ 两端在 `A` 内且是 `G` 的边。 -/
theorem inducedSubgraph_edge_iff {G : FateV2.Modeling.Graph.DAG V} {A : Finset V} {u v : V} :
    (inducedSubgraph G A).edge u v ↔ u ∈ A ∧ v ∈ A ∧ G.edge u v := Iff.rfl

/-- **B6.2**：诱导子图的边 ⊆ 原图的边。 -/
theorem inducedSubgraph_sub {G : FateV2.Modeling.Graph.DAG V} (A : Finset V) :
    ∀ ⦃u v⦄, (inducedSubgraph G A).edge u v → G.edge u v :=
  fun ⦃_ _⦄ h => h.2.2

/-- **B6.3（非平凡性见证）**：`A = ∅` 时诱导子图**没有任何边**。

⚠ 这条排除了「`inducedEdge` 恒真」的可能：若定义退化成 `True`，本条不可能成立。 -/
theorem inducedEmpty_edge (G : FateV2.Modeling.Graph.DAG V) (u v : V) :
    ¬ inducedEdge G ∅ u v := by
  intro h
  exact absurd h.1 (by simp)

/-- **B6.4**：父集刻画：`v ∈ A` 时，`u` 是 `G[A]` 中 `v` 的父 ⟺ `u ∈ A` 且 `u` 是 `G` 中 `v` 的父。 -/
theorem mem_pa_inducedSubgraph {G : FateV2.Modeling.Graph.DAG V} {A : Finset V} {u v : V}
    (hu : u ∈ A) (hv : v ∈ A) :
    u ∈ pa (inducedSubgraph G A) v ↔ u ∈ pa G v := by
  rw [mem_pa, mem_pa, inducedSubgraph_edge_iff]
  constructor
  · intro h; exact h.2.2
  · intro h; exact ⟨hu, hv, h⟩

/-- **B6.5**：诱导子图的父集 ⊆ 原图的父集（**子图不新增父**）。 -/
theorem pa_inducedSubgraph_subset {G : FateV2.Modeling.Graph.DAG V} {A : Finset V} {v : V} :
    pa (inducedSubgraph G A) v ⊆ pa G v := by
  intro u hu
  rw [mem_pa] at hu ⊢
  exact hu.2.2

/-- **B6.6**：诱导子图里的可达 ⟹ 原图里的可达（子图不新增路径）。 -/
theorem inducedSubgraph_transGen {G : FateV2.Modeling.Graph.DAG V} {A : Finset V} {a b : V}
    (h : Relation.TransGen (inducedSubgraph G A).edge a b) :
    Relation.TransGen G.edge a b := by
  induction h with
  | single hab => exact Relation.TransGen.single hab.2.2
  | tail _ hbc ih => exact ih.tail hbc.2.2

/-- **B6.7**：`G[univ]` 与 `G` 的边关系相同。 -/
theorem inducedSubgraph_univ (G : FateV2.Modeling.Graph.DAG V) :
    ∀ u v, (inducedSubgraph G univ).edge u v ↔ G.edge u v := by
  intro u v
  rw [inducedSubgraph_edge_iff]
  simp

/-- **B6.8**：两端都在 `A` 内的原图边，在 `G[A]` 中保留。 -/
theorem inducedSubgraph_edge_of_mem {G : FateV2.Modeling.Graph.DAG V} {A : Finset V} {u v : V}
    (hu : u ∈ A) (hv : v ∈ A) (h : G.edge u v) : (inducedSubgraph G A).edge u v :=
  ⟨hu, hv, h⟩

end AncestralInheritanceRouteB
end FateV2.Predict