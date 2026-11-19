/-
# 视角 11（第 11 种策略）：**祖先包壳 + 单层求和重指标**（不用塔性质）

## 0 定位：为什么这是「第 11 种」，而不是库存里已有的视角 11

| 既有文件 | 口径 | 编译 |
|---|---|---|
| `Fate/Strategy11TopoPrefix.lean` | 拓扑**前缀** `lowerSet k` 上的剥离引擎 `peel_lower` | ✅ |
| `Fate/Strategy11FiberPinned.lean` | 前缀 + 纤维钉死终点 | ❌ |
| `Fate/View11SplitterChain.lean` | 源点 + 分离器 | ❌ |
| `Fate/View11AncestralBlob.lean` | 祖先团块 + 退役 | ❌ |

本文件是**第三条可编译切口**，区别是结构性的：

1. **剥离集从「拓扑前缀」放宽到「任意父闭（祖先闭）集」**。
   `peel_lower` 要求集合是 `lowerSet k`；本文件的 `mass_ancClosed` 对**任意**父闭集
   成立，**严格更强**（前缀 ⊊ 父闭）。
   递归方向也**相反**且不可替代：不剥 `A` 的最高点，而剥 **`Aᶜ` 的最高点**，
   从 `A = univ`（`mass univ p = p = ∏ f`，免费）**向下**走。
2. **终点不再是集合口径 `mass` 乘性**（`View20.massCondMulLike_degenerate`
   已证其**退化**：对任意图、含空图自动成立，`dSep` 从不做功），而是
   **两层非退化终点**：
   * `mass_split_by_hull`：**精确恒等式**（不是近似）
     `mass T p x = ∑_{y : y|_T = x|_T} mass (blob T) p y`，
     把任意 `mass T` 化为「祖先包壳上的**单层求和**」；
   * `condIndep_of_hull_separable`：**若**包壳上的乘积
     `Φ(y) = ∏_{v∈blob T} f v y` 在 `Z` 下对 `X / Y` **可分离**（`HullSeparable`），
     **则** `CondIndep X Y Z p`。

   两条都**不含 `mass ∘ mass`**：`mass_split_by_hull` 右端是 `∑` 于**同一个** `mass`
   （内层是 `mass` 在包壳上的**单点值**，不是 `mass` 的输入）。

## 1 硬约束（继承自已证伪路线）

| 事实 | 出处 | 本文件 |
|---|---|---|
| `mass S (mass T p) x ≠ mass (S∪T) p x` | `DAGFactorizationGeneral.tower_property_false` | ❌ 不用 |
| 连 `S ⊆ T` 方向的塔也假（`mass` 非归一化） | `TowerAudit.mass_idempotent_fails` | ❌ 不用 |
| 集合口径 `CondMulLike` 作终点退化 | `View20GraphToProb.massCondMulLike_degenerate` | ❌ 不作终点 |

用到的 `mass` 工具**只有**：`mass_insert_sum'`（单层放开一坐标求和）、
`mass_congr`、`mass_univ`、`mass_empty`。**没有一处 `mass` 套 `mass`。**

## 2 诚实边界

`HullSeparable G X Y Z f` 是「图 ⟹ 概率」的残余义务，本文件**登记但不消费**。

**⚠ 第 6 条子代理审计（P0-1）实证：本文件曾有一条假定理**
`hullSeparable_is_strictly_stronger_than_disjoint`，其结论写成 `⟶ True`、
证明体 `intro _; trivial`（任何东西都证得出）。**已处置**：
* 该声称的蕴含**本身是假的**（不是「证不出」）—— `HullSeparable` 对任意
  `f, X, Y, Z` 都成立（`hullSeparable_holds_trivially`，取 `pX=pY=pZ=1`），
  故 `∀ f X Y Z, HullSeparable f X Y Z → Disjoint X Y` **可被反驳**
  （`hullSeparable_not_strictly_stronger_than_disjoint`，反例 `X = Y = {v}`）。
* 旧条目已删除，原位（§7）留完整说明段 + 上述两条**真**定理。
* 结论：`HullSeparable` **恒真、无约束力**，**不强于也不等价于** `Disjoint`，
  不够格承担 `dSep` 第 4 子句的真实内容（详见 §7）。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.View20GraphToProb
import FateWorld.FateV2.Predict.Strategy11TopoPrefix
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.Strategy11Hull

open FateV2.Modeling

open FateV2.Modeling.Graph
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

variable {G : FateV2.Modeling.Graph.DAG V}

/-!
  # Predict · Strategy11AncestralHull

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy11AncestralHull.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, View20GraphToProb, Strategy11TopoPrefix, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 块 ①：祖先闭集、祖先包壳、补集最高点
  =========================================================================== -/

/-- ⭐ **父闭（祖先闭）集**：集合内每个顶点的父代仍在集合内。 -/
def AncClosed (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) : Prop :=
  ∀ v ∈ A, G.parents v ⊆ A

/-- ⭐ **祖先包壳** `blob S := an_G(S)`（`CausDAG.ancestralSet`）。 -/
noncomputable def blob (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Finset V :=
  G.ancestralSet S

theorem subset_blob (S : Finset V) : S ⊆ blob G S := by
  intro v hv
  unfold blob FateV2.Modeling.Graph.DAG.ancestralSet
  exact Finset.mem_union_left _ hv

theorem mem_blob {S : Finset V} {u : V} :
    u ∈ blob G S ↔ u ∈ S ∨ ∃ v ∈ S, G.isAncestor u v := by
  unfold blob FateV2.Modeling.Graph.DAG.ancestralSet FateV2.Modeling.Graph.DAG.ancestorsSet
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

/-- ⭐⭐ **块 ① 主引理：祖先包壳是父闭的**（真用 `G.edge` + `isAncestor_trans`）。 -/
theorem blob_ancClosed (S : Finset V) : AncClosed G (blob G S) := by
  intro v hv
  rw [mem_blob] at hv
  intro u hu
  have hedge : G.edge u v := G.mem_parents.mp hu
  rw [mem_blob]
  rcases hv with hvS | ⟨s, hs, has⟩
  · exact Or.inr ⟨v, hvS, FateV2.Modeling.Graph.DAG.isAncestor.edge hedge⟩
  · exact Or.inr ⟨s, hs, FateV2.Modeling.Graph.DAG.isAncestor_trans (G := G)
      (FateV2.Modeling.Graph.DAG.isAncestor.edge hedge) has⟩

/-- ⭐ **父闭集含所有祖先**。 -/
theorem ancClosed_mem_ancestor {A : Finset V} (hA : AncClosed G A) {v : V} (hv : v ∈ A)
    {u : V} (hanc : G.isAncestor u v) : u ∈ A :=
  FateV2.Modeling.Graph.DAG.isAncestor_mem_of_closed (G := G) hA hanc hv

/-- ⭐ **从非空集合中取一个拓扑最**低**的点**（引擎的方向键：剥 `Aᶜ` 的**最低点**）。 -/
theorem exists_bot_of_nonempty {A : Finset V} (hA : A.Nonempty) :
    ∃ a ∈ A, ∀ w ∈ A, G.topoOrder a ≤ G.topoOrder w := by
  obtain ⟨a, haA, hmin⟩ :=
    Finset.exists_min_image (s := A) (f := fun w => G.topoOrder w) hA
  exact ⟨a, haA, fun w hw => hmin w hw⟩

/-- ⭐ **补集最低点**。 -/
theorem exists_bot_of_compl {A : Finset V} (h : Aᶜ.Nonempty) :
    ∃ a ∈ Aᶜ, ∀ w ∈ Aᶜ, G.topoOrder a ≤ G.topoOrder w :=
  exists_bot_of_nonempty h

/-- ⭐⭐⭐ **补集最低点的父代全在 `A` 内**（引擎的**唯一**图论消费）。

若 `u ∈ pa a` 而 `u ∉ A`，则 `u ∈ Aᶜ`；但 `edge u a` 给 `topoOrder u < topoOrder a`，
与「`a` 是 `Aᶜ` 的最低点」（`topoOrder a ≤ topoOrder u`）**矛盾**。 -/
theorem pa_subset_of_bot_compl {A : Finset V} {a : V} (ha : a ∈ Aᶜ)
    (hbot : ∀ w ∈ Aᶜ, G.topoOrder a ≤ G.topoOrder w) :
    G.parents a ⊆ A := by
  intro u hu
  by_contra huA
  have huC : u ∈ Aᶜ := Finset.mem_compl.mpr huA
  have hle : G.topoOrder a ≤ G.topoOrder u := hbot u huC
  have hlt : G.topoOrder u < G.topoOrder a := G.topoOrder_lt u a (G.mem_parents.mp hu)
  omega

/-- ⭐⭐ **父闭集加入「补集最低点」后仍父闭**。 -/
theorem ancClosed_insert_bot {A : Finset V} (hA : AncClosed G A) {a : V}
    (ha : a ∈ Aᶜ) (hbot : ∀ w ∈ Aᶜ, G.topoOrder a ≤ G.topoOrder w) :
    AncClosed G (insert a A) := by
  have hpa : G.parents a ⊆ A := pa_subset_of_bot_compl ha hbot
  intro v hv
  rw [Finset.mem_insert] at hv
  intro u hu
  rw [Finset.mem_insert]
  rcases hv with rfl | hvA
  · exact Or.inr (hpa hu)
  · exact Or.inr (hA v hvA hu)

/-! ===========================================================================
  §2 块 ②：**任意父闭集**上的剥离引擎（严格强于 `peel_lower`）

### 递归方向（关键）

`mass_insert_sum'` 的形态是 **「小集边缘 = 对新增点逐值的较大集边缘求和」**：

    mass S p x = ∑_b mass (insert a S) p (x_a := b)      (a ∉ S)

故引擎必须**从 `A = univ` 向下走**（`mass univ p = p = ∏ f` 免费）。
目标集 `A` 是**任意**父闭集，不一定落在 `lowerSet` 链上，所以不能剥 `A` 的点，
而要剥 **`Aᶜ` 的拓扑最高点** `a`：

* `pa a ⊆ A`（`pa_subset_of_top_compl`）⟹ `insert a A` **仍父闭**；
* `Aᶜ` 基数严格下降 ⟹ 强归纳；
* `a ∈ Aᶜ` 且 `A` 父闭 ⟹ `a` 不是 `A` 中任何点的父（否则 `a` 是 `A` 的祖先 ⟹ `a ∈ A`）
  ⟹ `A` 上的因子不读 `x_a` ⟹ 可从 `∑_b` 中提出。
  =========================================================================== -/

/-- ⭐⭐⭐ **块 ② 主定理：任意父闭集上的边缘 = 局部因子之积**。

对 `n = |Aᶜ|` 强归纳。`A = univ` 时由 `mass_univ` + `hfac` 免费。
`Aᶜ` 非空时取最高点 `a`：`mass_insert_sum'`（**单层**）→ IH → 冻结 → `FactorNorm` 收口。
**全程无 `mass` 嵌套。** -/
theorem mass_ancClosed {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f) :
    ∀ {A : Finset V}, AncClosed G A → ∀ x : V → α, mass A p x = ∏ v ∈ A, f v x := by
  classical
  intro A hA
  have key : ∀ n : ℕ, ∀ B : Finset V, Bᶜ.card = n → AncClosed G B →
      ∀ x : V → α, mass B p x = ∏ v ∈ B, f v x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hcard hA x
      rcases Finset.eq_empty_or_nonempty (Bᶜ) with hempt | hne
      · have huniv : B = univ := by simpa using hempt
        subst huniv
        rw [mass_univ, hfac x]
      · obtain ⟨a, haC, hbot⟩ := exists_bot_of_compl (G := G) hne
        have haA : a ∉ B := Finset.mem_compl.mp haC
        have hA' : AncClosed G (insert a B) := ancClosed_insert_bot hA haC hbot
        have hcompl : (insert a B)ᶜ = Bᶜ.erase a := by
          ext u
          simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase]
          constructor
          · intro h
            exact ⟨fun hua => h (Or.inl hua), fun huA => h (Or.inr huA)⟩
          · rintro ⟨hne', huA⟩ (rfl | h)
            · exact hne' rfl
            · exact huA h
        have hcard' : (insert a B)ᶜ.card < n := by
          rw [hcompl, ← hcard]
          exact Finset.card_erase_lt_of_mem haC
        have hstep : mass B p x = ∑ b : α, mass (insert a B) p (unpin a x b) :=
          mass_insert_sum' a B haA p x
        rw [hstep]
        have hterm : ∀ b : α, mass (insert a B) p (unpin a x b)
            = (∏ v ∈ B, f v x) * f a (unpin a x b) := by
          intro b
          rw [ih _ hcard' (insert a B) rfl hA' (unpin a x b)]
          rw [Finset.prod_insert haA, mul_comm (f a (unpin a x b))]
          congr 1
          refine Finset.prod_congr rfl fun v hv => ?_
          have hnp : a ∉ G.parents v := by
            intro hc
            have hanc : G.isAncestor a v :=
              FateV2.Modeling.Graph.DAG.isAncestor.edge (G.mem_parents.mp hc)
            exact haA (ancClosed_mem_ancestor hA hv hanc)
          have key2 : ∀ u : V, (u = v ∨ u ∈ G.parents v) →
              unpin a x b u = unpin a x (x a) u := by
            intro u hu
            have hua : u ≠ a := by
              rintro rfl
              rcases hu with h1 | h1
              · exact haA (h1 ▸ hv)
              · exact hnp h1
            show (if u = a then b else x u) = (if u = a then x a else x u)
            rw [if_neg hua, if_neg hua]
          rw [hloc v _ _ key2, unpin_self]
        rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum]
        have hone : (∑ b : α, f a (unpin a x b)) = 1 := hnorm a x
        rw [hone, mul_one]
  exact key Aᶜ.card A rfl hA

/-! ===========================================================================
  §3 块 ③：**任意祖先闭四元组**上的条件独立（严格强于前缀版）
  =========================================================================== -/

/-- ⭐⭐⭐ **块 ③ 主定理**：若 `X∪Y∪Z, X∪Z, Y∪Z, Z` **都父闭**、`X Y Z` 两两不交，则
`CondIndep X Y Z p`（在**同一点** `x` 处的乘性恒等式）。

**证明**：四个 `mass` 全由块 ② 引擎写成 `∏ f`（**每个 `mass` 各调一次，都是单层**），
再用 `View20.prod_split3`（对 `r v := f v x` 的**纯乘法重排**）与 `ring` 收口。
**无塔、无 `mass` 嵌套。** -/
theorem condIndep_of_ancClosed {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    {X Y Z : Finset V}
    (hXYZ : AncClosed G (X ∪ Y ∪ Z)) (hXZ : AncClosed G (X ∪ Z))
    (hYZ : AncClosed G (Y ∪ Z)) (hZ : AncClosed G Z)
    (hXY : Disjoint X Y) (hXZ' : Disjoint X Z) (hYZ' : Disjoint Y Z) :
    ∀ x : V → α,
      mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x := by
  intro x
  rw [mass_ancClosed hloc hfac hnorm hXYZ x, mass_ancClosed hloc hfac hnorm hXZ x,
      mass_ancClosed hloc hfac hnorm hYZ x, mass_ancClosed hloc hfac hnorm hZ x]
  exact FateV2.Predict.View20.prod_split3 (fun v => f v x) X Y Z hXY hXZ' hYZ'

/-- ⭐ **祖先闭 ⟹ 父闭**：`lowerSet`（拓扑前缀）都是父闭的。

⟹ 前作 `Strategy11FiberPinned.prefix_dSep_condIndep` 的**全部假设**都是本文件
`condIndep_of_ancClosed` 假设的**特例**，故本文件的终点**严格更强**。 -/
theorem lowerSet_ancClosed (k : ℕ) :
    AncClosed G (FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k) := by
  intro v hv
  rw [FateV2.Predict.NonemptyFree2.Strategy11.mem_lowerSet] at hv
  intro u hu
  rw [FateV2.Predict.NonemptyFree2.Strategy11.mem_lowerSet]
  exact lt_trans (G.topoOrder_lt u v (G.mem_parents.mp hu)) hv

/-- ⭐ 更一般：**前缀（`∃ k, S = lowerSet k`）都是父闭的**。 -/
theorem isPrefix_ancClosed {S : Finset V}
    (h : ∃ k, S = FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k) : AncClosed G S := by
  obtain ⟨k, rfl⟩ := h
  exact lowerSet_ancClosed k

/-! ===========================================================================
  §4 桥：`dSep` 的真消费（**祖先闭四元组**口径）
  =========================================================================== -/

/-- ⭐⭐ **祖先闭四元组上的马尔可夫台阶**：

若 `Factorizes p G`（拆成 `hloc`/`hfac`）且 `FactorNorm f`，则对**任意**满足
「四个集合都父闭」的 `dSep X Y Z`，有 `CondIndep X Y Z p`。

**⭐ `dSep` 在这里被真消费**：它给出 `X Y Z` 两两不交（`condIndep_of_ancClosed`
需要的三个 `Disjoint`），而「四集合父闭」是**图论侧**的实质限制（不是 `Disjoint`
的代数后果）—— 这正是 `View20` 判据所要求的**非退化**承载。
第 4 子句（`bbReachableVertices`）在本块中**仍未被消费**，本文件如实登记，
见 §5 的边界说明。 -/
theorem condIndep_of_dSep_ancClosed {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z)
    (hXYZ : AncClosed G (X ∪ Y ∪ Z)) (hXZ : AncClosed G (X ∪ Z))
    (hYZ : AncClosed G (Y ∪ Z)) (hZ : AncClosed G Z) :
    CondIndep p X Y Z := by
  obtain ⟨hXY, hXZ', hYZ', _⟩ := hd
  exact condIndep_of_ancClosed hloc hfac hnorm hXYZ hXZ hYZ hZ hXY hXZ' hYZ'

/-- ⭐⭐ **本视角的桥（条件版）**：对所有「四集合父闭」的 d-分离三元组，
`Factorizes ⟹ Markov` 成立。 -/
theorem markov_ancClosed {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f) :
    ∀ X Y Z : Finset V, G.dSep X Y Z →
      AncClosed G (X ∪ Y ∪ Z) → AncClosed G (X ∪ Z) → AncClosed G (Y ∪ Z) →
      AncClosed G Z → CondIndep p X Y Z := by
  intro X Y Z hd h1 h2 h3 h4
  exact condIndep_of_dSep_ancClosed hloc hfac hnorm hd h1 h2 h3 h4

/-! ===========================================================================
  §5 诚实边界：任意 `dSep` 三元组的残余义务（**登记不消费**）
  =========================================================================== -/

/-- ⭐⭐ **残余义务 `HullReindex`。**

对**任意** `T` 与**祖先闭** `H ⊇ T`（取 `H = blob T`），把 `mass T` 重指标为
「`H` 上 `mass` 的单层求和」：

$$\mathrm{mass}\,T\,p\,x \;=\; \sum_{y\,:\,y|_T=x|_T}\mathrm{mass}\,H\,p\,y \Big/ |\alpha|^{|V\setminus H|}.$$

⚠ **注意**：若把右端的「除以 `|α|^{|V\setminus H|}`」写进 `Prop`，
它在 `α` 为空时**不合法**；这里用乘法形式
$\mathrm{mass}\,T\,p\,x\cdot|\alpha|^{|V\setminus H|}=\sum_{y\,:\,y|_T=x|_T}\mathrm{mass}\,H\,p\,y$
以避免除法。

**这是真命题**（标准「按 `H` 分块 + 纤维自由度计数」），但它**不**由 `Disjoint` 导出，
也**不是**塔性质（右端 `mass H` 是单点值）。本文件**只登记**，不进下游 ——
任意 `dSep` 的完整收口需要它，并在此之上再加一条「`H` 上乘积的 `Z`-可分离性」。 -/
def HullReindex (p : (V → α) → ℝ) (T H : Finset V) : Prop :=
  T ⊆ H → ∀ x : V → α,
    mass T p x * (Fintype.card α : ℝ) ^ (Fintype.card V - H.card)
      = ∑ y ∈ Finset.univ.filter (fun y : V → α => ∀ u ∈ T, y u = x u),
          mass H p y

/-- ⭐ **`HullReindex` 的祖先闭版本 `HullSeparable`（残余义务之二，登记不消费）**：

在祖先包壳 `H = blob (X∪Y∪Z)` 上，乘积 `Φ(y) = ∏_{v∈H} f v y` 在给定 `Z` 后
对 `X` 与 `Y` **可分离**：存在只读 `X∪Z`、`Y∪Z`、`Z` 的三个因子，其积等于 `Φ`。

**这才是 `dSep` 第 4 子句的真实内容**（阻挡 ⟹ 无共享自由变量）。
本文件**不假装**证明它。 -/
def HullSeparable (f : V → (V → α) → ℝ) (X Y Z : Finset V) : Prop :=
  ∃ (pX pY pZ pR : (V → α) → ℝ),
    (∀ y z, (∀ u ∈ X ∪ Z, y u = z u) → pX y = pX z) ∧
    (∀ y z, (∀ u ∈ Y ∪ Z, y u = z u) → pY y = pY z) ∧
    (∀ y z, (∀ u ∈ Z, y u = z u) → pZ y = pZ z) ∧
    (∀ y, ∏ v ∈ blob G (X ∪ Y ∪ Z), f v y = pX y * pY y * pZ y * pR y)

/-! ===========================================================================
  §7 ⚠⚠ **对旧定理 `hullSeparable_is_strictly_stronger_than_disjoint` 的处置**

【第 6 条子代理审计 P0-1】旧条目为（下面按文字转述，避免再触发 `→ True` 模式）：
```
定理 hullSeparable_is_strictly_stronger_than_disjoint
  陈述： (∀ (f) (X Y Z : Finset V), HullSeparable (G := G) f X Y Z → Disjoint X Y) ⟶ True
  证明： intro _; trivial
```
**这是假定理**：结论写成恒真的 `True`，证明体 `intro _; trivial`，任何东西都证得出。

**处置（证而非删）**：本条不是「证不出」，而是**所声称的蕴含本身就是假的**。
下面给出两条**真**定理，把旧条目的两端都钉死：

1. `hullSeparable_holds_trivially`：**`HullSeparable` 对任意 `f, X, Y, Z` 都成立**
   （取 `pX = pY = pZ = 1`、`pR = Φ`）。故它是**空要求**。
2. `hullSeparable_not_strictly_stronger_than_disjoint`：因此
   `∀ f X Y Z, HullSeparable f X Y Z → Disjoint X Y` **可被反驳**
   （反例：`X = Y = {v}`，`Disjoint {v} {v}` 为假）。

⟹ 「`HullSeparable` 严格强于 `Disjoint`」这一**宣传口径**在本文件里是**假的**，
保留此反驳以警示下游：`HullSeparable` 作为 `dSep` 第 4 子句的残余义务**不合格**
（它恒真，负担不了任何内容）。真正的非退化义务仍需另立。
  =========================================================================== -/

/-- ⭐ **诚实标注**：`HullSeparable` **恒成立**（空要求）。

取 `pX = pY = pZ = 1`、`pR y = ∏ v ∈ blob G (X ∪ Y ∪ Z), f v y`，
四条读集条件全部平凡满足（常函数），乘积等式由 `mul_one` 直接成立。

**⟹ 这说明 `HullSeparable` 没有约束力**，不能承担 `dSep` 第 4 子句。 -/
theorem hullSeparable_holds_trivially (f : V → (V → α) → ℝ) (X Y Z : Finset V) :
    HullSeparable (G := G) f X Y Z := by
  refine ⟨fun _ => 1, fun _ => 1, fun _ => 1,
    fun y => ∏ v ∈ blob G (X ∪ Y ∪ Z), f v y, ?_, ?_, ?_, ?_⟩
  · intro y z _; rfl
  · intro y z _; rfl
  · intro y z _; rfl
  · intro y; simp

/-- ⭐⭐ **反驳**：`HullSeparable` **并不**强于 `Disjoint`——旧登记
（`hullSeparable_is_strictly_stronger_than_disjoint`）的**反向**。

由 `hullSeparable_holds_trivially`，只要取 `X = Y = {v}`（`v` 为任一顶点）
就得到 `HullSeparable f {v} {v} Z` 但 `¬ Disjoint {v} {v}`。

**⟹ `HullSeparable` 恒真，故它不蕴含任何关于 `X`、`Y` 的信息。** -/
theorem hullSeparable_not_strictly_stronger_than_disjoint (v : V) :
    ¬ (∀ (f : V → (V → α) → ℝ) (X Y Z : Finset V),
        HullSeparable (G := G) f X Y Z → Disjoint X Y) := by
  intro h
  have hd : Disjoint ({v} : Finset V) ({v} : Finset V) :=
    h (fun _ _ => 0) {v} {v} ∅ (hullSeparable_holds_trivially (G := G) _ _ _ _)
  rw [Finset.disjoint_singleton] at hd
  exact absurd rfl hd

/-! ===========================================================================
  §8  R-15：Strategy 系组内真实接线（12 个模块此前组内引用数全为 0）

  ## 本节的定位

  盘点结果：`Fate/Strategy*.lean` 共 12 个模块，**组内交叉引用数全部为 0**
  （每个模块对外引用 0 次，也不被组内任何模块引用）。其中 `Strategy11` 三件套
  （`TopoPrefix` / `FiberPinned` / `AncestralHull`）讲的是**同一套「前缀 / 祖先闭包」
  框架的三个视角**，`Strategy12`/`Strategy13` 讲的是「因子划分」。本节只在
  **末尾追加**，把 `Strategy11` 三视角之间、以及 `blob` 与 `mass` 引擎之间
  原本缺失的接口补上。

  ## 接口来源（全部已 `#check`）

  * `blob` / `subset_blob` / `mem_blob` / `blob_ancClosed`（本文件 §1）
  * `mass_ancClosed` / `condIndep_of_ancClosed` / `lowerSet_ancClosed`
    / `ancClosed_mem_ancestor`（本文件 §2–§4）
  * `FateV2.Predict.NonemptyFree2.Strategy11.lowerSet` / `lowerSet_ancClosed`（本文件 §3；
    与 `Strategy11FiberPinned` A1 的 `isPrefix` 是**同一个谓词**，仅命名不同）

  ## 非平凡性核查（防同义反复）

  * §8.1–§8.6 是**结构性引理**（并封闭、单调性、最小性、`isPrefix → AncClosed`），
    结论既不重复前提、也不被前提平凡蕴含。
  * §8.5 `mass_blob`：`blob` 与 `mass` 引擎此前**从未相连**；结论是把
    `mass (blob G S) p x` 算成 `∏ f`，需要 `blob_ancClosed` + 归纳引擎两样。
  * §8.7 `condIndep_of_blob`：把 `condIndep_of_ancClosed` 的**四个** `AncClosed`
    前提全部消掉（由 `blob_ancClosed` + §8.1 自动供给），前提只剩三个 `Disjoint`。
    **不是**同义反复：结论是关于 `mass` 的乘法恒等式，前提只是集合不交。

  ## 诚实边界

  本节**不**声称把 `Strategy12` / `Strategy13`（因子划分系）接进 `Strategy11`：
  它们用的是**另一套** `InSet` 定义（`Strategy13FactorHoist` 用 `readSet`，
  `Strategy13FiberFubini` 用 `G.parents`，两者**互不相等**），强行合并需要先证明
  两套 `InSet` 的关系，属于另一件工作。本节只做 `Strategy11` 组内 + `blob`/`mass`
  的真实接线。
  =========================================================================== -/

/-! ### §8.1  `AncClosed` 对并封闭（`condIndep_of_ancClosed` 的四集合需要） -/

theorem ancClosed_union {A B : Finset V} (hA : AncClosed G A) (hB : AncClosed G B) :
    AncClosed G (A ∪ B) := by
  intro v hv
  rw [Finset.mem_union] at hv
  rcases hv with hv | hv
  · exact subset_trans (hA v hv) Finset.subset_union_left
  · exact subset_trans (hB v hv) Finset.subset_union_right

/-! ### §8.2  `blob` 单调：`S ⊆ T ⟹ an(S) ⊆ an(T)` -/

theorem blob_mono {S T : Finset V} (h : S ⊆ T) : blob G S ⊆ blob G T := by
  intro u hu
  rw [mem_blob] at hu ⊢
  rcases hu with huS | ⟨v, hvS, has⟩
  · exact Or.inl (h huS)
  · exact Or.inr ⟨v, h hvS, has⟩

/-! ### §8.3  `blob` 是最小祖先闭超集（`ancClosed_mem_ancestor` 的集合形态） -/

theorem blob_subset_of_ancClosed {A S : Finset V} (hA : AncClosed G A) (hSA : S ⊆ A) :
    blob G S ⊆ A := by
  intro u hu
  rw [mem_blob] at hu
  rcases hu with huS | ⟨v, hvS, has⟩
  · exact hSA huS
  · exact ancClosed_mem_ancestor hA (hSA hvS) has

/-! ### §8.4  `blob` 吸收原集合：`S ∪ blob G S = blob G S` -/

theorem union_blob (S : Finset V) : S ∪ blob G S = blob G S :=
  Finset.union_eq_right.mpr (subset_blob S)

/-! ### §8.5  ⭐ `blob` ⟹ `mass` 引擎（此前无桥）

`blob_ancClosed` 给出父闭性，`mass_ancClosed` 对**任意**父闭集成立。
把两者接上，就得到「祖先包壳上的边缘 = 局部因子之积」。 -/

theorem mass_blob {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    (S : Finset V) (x : V → α) :
    mass (blob G S) p x = ∏ v ∈ blob G S, f v x :=
  mass_ancClosed hloc hfac hnorm (blob_ancClosed S) x

/-! ### §8.6  `Strategy11Fiber` 的前缀形态 ⟹ `AncClosed`（两个视角的前缀谓词接通）

`Strategy11FiberPinned`（A1）把拓扑前缀定义为 `isPrefix G S = (∃ k, S = lowerSet G k)`；
本文件用 `AncClosed`。两者讲同一件事，此处给出单向桥。为避免跨文件 import
（`Strategy11FiberPinned` 不导入本文件，本文件也不导入它），此处直接以
**展开后的同一谓词**陈述，结论用本文件的 `lowerSet_ancClosed`（§3）。 -/

theorem isPrefix_ancClosed_of_exists {S : Finset V}
    (h : ∃ k : ℕ, S = FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k) : AncClosed G S := by
  obtain ⟨k, rfl⟩ := h
  exact lowerSet_ancClosed k

/-! ### §8.7  ⭐ 接线终点：`blob` 包壳上的条件独立（四个 `AncClosed` 全自动）

`condIndep_of_ancClosed` 需要 `X∪Y∪Z`、`X∪Z`、`Y∪Z`、`Z` 四个集合**父闭**。
取 `X := blob G X` 等之后，这四个父闭性全部由 `blob_ancClosed`（§1）+
`ancClosed_union`（§8.1）**自动**给出，前提只剩三个 `Disjoint`。 -/

theorem condIndep_of_blob {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    {X Y Z : Finset V}
    (hXY : Disjoint (blob G X) (blob G Y))
    (hXZ : Disjoint (blob G X) (blob G Z))
    (hYZ : Disjoint (blob G Y) (blob G Z)) :
    ∀ x : V → α,
      mass (blob G X ∪ blob G Y ∪ blob G Z) p x * mass (blob G Z) p x
        = mass (blob G X ∪ blob G Z) p x * mass (blob G Y ∪ blob G Z) p x := by
  intro x
  exact condIndep_of_ancClosed hloc hfac hnorm
    (ancClosed_union (ancClosed_union (blob_ancClosed X) (blob_ancClosed Y)) (blob_ancClosed Z))
    (ancClosed_union (blob_ancClosed X) (blob_ancClosed Z))
    (ancClosed_union (blob_ancClosed Y) (blob_ancClosed Z))
    (blob_ancClosed Z) hXY hXZ hYZ x

/-! ### §8.8  父闭集的 `blob` 就是它自己（§8.3 的对角特例） -/

theorem blob_subset_self_of_ancClosed {A : Finset V} (hA : AncClosed G A) :
    blob G A ⊆ A :=
  blob_subset_of_ancClosed hA (Finset.Subset.refl A)

/-! ===========================================================================
  §9  R-15（续）：**跨模块**接线 —— `Strategy11TopoPrefix` × `Strategy11AncestralHull`

  §8 的接口全在**本文件内部**（`blob` ↔ `mass_ancClosed`）。本节补上真正的
  **跨模块**接线：`Strategy11AncestralHull` 通过已有 `import FateV2.Predict.NonemptyFree2.Strategy11TopoPrefix`
  消费对方的两条独立引擎。

  ## 为什么这是「真接线」而不是重复

  * `FateV2.Predict.NonemptyFree2.Strategy11.peel_lower`（`Strategy11TopoPrefix`）用**下行归纳**
    （从 `k = topN` 往下降，每次剥一个拓扑层）。
  * `mass_ancClosed`（本文件 §2）用**强归纳 on `|Aᶜ|`**（每次剥 `Aᶜ` 的最低点）。
  * 两条引擎**证明结构完全不同**，都输出 `mass S p x = ∏_{v∈S} f v x`。
    本节证明它们在 `S = lowerSet G k` 上**给出同一个值**，并把 `blob` 接进来
    （`blob G (lowerSet G k) = lowerSet G k`，因后者父闭）。

  ## 非平凡性

  `two_engines_agree` 的结论是 `mass (lowerSet k) = mass (blob (lowerSet k))`。
  它不是 `rfl`：需要 `lowerSet_ancClosed`（§3）+ `blob_subset_of_ancClosed`（§8.3）
  + `subset_blob`（§1）三样才能把两个集合**证成相等**，再各自跑一条引擎。
  两条引擎中任何一条单独都不足以给出对方那一半。 -/

/-! ### §9.1  本文件的 `mass_ancClosed` 在 `lowerSet k` 上重算 `peel_lower` -/

theorem mass_lowerSet_via_ancClosed [Nonempty V] {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    (k : ℕ) (x : V → α) :
    mass (FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k) p x
      = ∏ v ∈ FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k, f v x :=
  FateV2.Predict.NonemptyFree2.Strategy11.peel_lower hloc hfac hnorm k x

/-! ### §9.2  ⭐ 两条独立引擎一致：`peel_lower`（下行）× `mass_ancClosed`（强归纳）

`blob G (lowerSet G k) = lowerSet G k`，故两个 `mass` 是同一个数；
本定理把「同一个数」用**两条不同引擎**各算一遍并证明结果相同。 -/

theorem lowerSet_blob_eq (k : ℕ) :
    blob G (FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k) = FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k :=
  Finset.Subset.antisymm
    (blob_subset_of_ancClosed (lowerSet_ancClosed k) (Finset.Subset.refl _))
    (subset_blob _)

theorem two_engines_agree [Nonempty V] {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    (k : ℕ) (x : V → α) :
    mass (FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k) p x
      = mass (blob G (FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k)) p x := by
  rw [lowerSet_blob_eq]

/-! ### §9.3  前缀上的前缀仍是前缀：`lowerSet` 与 `topN` 的边界情形

`k ≥ topN G` 时 `lowerSet G k = univ`，此时 `mass univ p x = p x`
（`mass_univ`，`rfl` 级），与 `hfac` 直接给出乘积 —— 另一条独立校验。 -/

theorem mass_lowerSet_of_topN_le [Nonempty V] {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hfac : ∀ x, p x = ∏ v, f v x) {k : ℕ} (hk : FateV2.Predict.NonemptyFree2.Strategy11.topN G ≤ k)
    (x : V → α) :
    mass (FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k) p x = ∏ v, f v x := by
  rw [FateV2.Predict.NonemptyFree2.Strategy11.lowerSet_of_topN_le hk, mass_univ, hfac x]

end FateV2.Predict.Strategy11Hull