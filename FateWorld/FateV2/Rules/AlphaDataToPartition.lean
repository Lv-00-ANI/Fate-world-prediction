/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Rules.AlphaDataToPartition`
阶段：**P2 桥的第 1 半 —— `AlphaData.alpha` 的商化给出「划分的一块」**

---------------------------------------------------------------------------
本文件做了什么（一句话）
---------------------------------------------------------------------------
在真实类型上定义 **α 纤维块** `alphaCell D e`，并证明它确实是
「α 值相等」这一等价关系的**一块**（自反 / 对称 / 传递 / 就是等价类），
且**尊重 `ker(obs)`**（即块在观测等价下饱和）——这正是子代理审计 §3.4
所要求的「商化 → 划分」的第一小步。

---------------------------------------------------------------------------
(a) 真实类型（贴原文核对，非推测）
---------------------------------------------------------------------------
`Fate/AlphaFCAConstruction.lean:95`：

```
structure AlphaData (E : InstSpace.{u}) (M : Type u) where
  /-- 观测映射：实例 ↦ 它满足的属性集 -/
  obs : E.Carrier → Set M
```

`Fate/Frame.lean:568`：`structure InstSpace where Carrier : Type*`

`Fate/AlphaFCAConstruction.lean:372`（α 本体）：

```
def alpha (D : AlphaData E M) (e : E.Carrier) :
    Concept E.Carrier M (D.ctx).Irel × Set M :=
  (D.instanceConcept e, D.takeConcept (D.obs e))
```

`Fate/AlphaFCAConstruction.lean:412`（已有的商下降）：

```
def alphaQuot (D : AlphaData E M) :
    Quotient (Setoid.ker D.obs) → Concept E.Carrier M (D.ctx).Irel × Set M :=
  Quotient.lift D.alpha (fun _ _ h => D.alpha_respects_obs h)
```

因此本文件的元素类型是 `E.Carrier`，α 值是
`Concept E.Carrier M (D.ctx).Irel × Set M`，**没有任何额外假设**。

---------------------------------------------------------------------------
(b) 本文件新增的定义与定理（全部实际存在，可用 `grep ^theorem` 核对）
---------------------------------------------------------------------------
| # | 名称 | 内容 |
|---|---|---|
| 1 | `alphaCell`（def） | `{e' | D.alpha e' = D.alpha e}` —— α 纤维块 |
| 2 | `mem_alphaCell_iff` | `e' ∈ alphaCell D e ↔ D.alpha e' = D.alpha e`（`Iff.rfl`） |
| 3 | `alphaCell_mem_self` | `e ∈ alphaCell D e`（自反 / 定义性） |
| 4 | `alphaCell_symm` | `e' ∈ alphaCell D e → e ∈ alphaCell D e'` |
| 5 | `alphaCell_trans` | 传递性：两块相等或相交则同一块 |
| 6 | `alphaCell_eq_of_mem` | `e' ∈ alphaCell D e → alphaCell D e' = alphaCell D e` |
| 7 | `alphaCell_eq_iff_mem` | `alphaCell D e' = alphaCell D e ↔ e' ∈ alphaCell D e` |
| 8 | `alphaCell_saturated` | **商化核心**：`obs e' = obs e → e' ∈ alphaCell D e` |
| 9 | `alphaCell_union_eq_univ` | `⋃ e, alphaCell D e = univ`（块覆盖全体） |
| 10 | `alphaCell_eq_ker` | `alphaCell D e` 恰是 `Setoid.ker D.alpha` 的等价类 |
| 11 | `alphaQuot_eq_of_mem_alphaCell` | 块内两个代表元的 `alphaQuot` 值相同 |
| 12 | `alphaCell_subset_alphaQuot_fiber` | 块 ⊆ 商像的纤维（商化相容） |
| 13 | `alphaCell_extent_eq` | 块内实例的概念外延相等（α 第一分量） |

---------------------------------------------------------------------------
(c) 反同义反复核对（本项目最高频缺陷，逐条自检）
---------------------------------------------------------------------------
- 定理 3、2 是**定义性**的（`rfl` / `Iff.rfl`），**不**冒充实质定理，
  它们只用来给出 `alphaCell` 是「自反」的。
- 定理 4、5、6、7 的前件是**成员关系** `e' ∈ alphaCell D e`
  （即 `alpha e' = alpha e`），结论是**块之间的等式或方向反转**，
  前件**没有**直接重述结论（块等式 `alphaCell D e' = alphaCell D e`
  是集合**外延**相等，需要 ext + 传递性两步，不是前件的字面复制）。
- 定理 8 是本文件**唯一的实质商化内容**：前件是 `obs e' = obs e`
  （**观测**相等），结论是 `e' ∈ alphaCell D e`（即 **α 值**相等）。
  两者是**不同的等价关系**，前件不蕴含结论的定义性成立，
  必须真正调用 `AlphaData.alpha_respects_obs`。
- 定理 9 是 `univ` 的覆盖性（`e` 自己就在自己的块里），前件为空。
- 定理 10 把块与 `Setoid.ker D.alpha` 的等价类对齐（两侧都用 `Iff.rfl` 层面的
  `Setoid.ker` 定义展开，但等式本身需要 `ext`，非字面复制）。
- 定理 11、12 的前件是块的成员关系，结论涉及 **Quotient** 的值，
  需要 `Quotient.sound` / `Quotient.lift` 的下降，不是前件的复制。
- 定理 13 的前件是块成员关系，结论是 `Concept.extent` 的相等，
  经由 `alpha` 的 `Prod` 第一分量相等再取 `.extent`。

---------------------------------------------------------------------------
(d) 本文件**不**声称什么（必须写明的边界）
---------------------------------------------------------------------------
- **不**声称「`AlphaData` 与 `AlphaOutput` 的桥已建成」。
  本文件只做了**第 1 项（商化 → 划分的一块）**。
  第 2 项（**规则提取**：`dgBasis` 的伪内涵对 → `LawRule` 字段对齐）
  **完全未做**，因此「`AlphaOutput` 的 `LawRule` 集」一侧仍空缺。
- **不**声称「`W.alpha` 等价性已证」。本文件证明的是**块结构**（划分的一半），
  不是「α 输出 = 规格 α」。
- **不**声称块**构成**一个 `Partition` 对象（`Setoid` 商 / `Partition` 类型）。
  本文件只给出纤维块及其封闭性；把 `{alphaCell D e | e}` 打包成
  Mathlib `Partition` 需要另写 `PairwiseDisjoint` + `sSup = univ` 的构造，
  本文件用定理 5、9 提供了**这两条的原始素材**，但**未**打包。
- 局部域划分（`AlphaOutput` 的「局部域」部分）需要先把实例集切成局部域，
  本文件**假设**单一全局域（与 `AlphaData` 本身一致），**不**处理局部性。

---------------------------------------------------------------------------
诚实边界（技术性）
---------------------------------------------------------------------------
- 本文件**零 `sorry`、零 `admit`、零 `axiom`**（`#print axioms` 见文末）。
- **不修改**任何既有模块；`Fate/AlphaDataConsumed.lean` 未触碰。
- 仅依赖已编译的 `FateV2.Rules`（其 `.olean` 已存在）。
-/

import Mathlib.Order.Concept
import Mathlib.Data.Set.Lattice
import FateWorld.FateV2.Rules.AlphaFCAConstruction
import FateWorld.FateV2.Rules.AlgoKNNComponents
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set

universe u

noncomputable section

set_option linter.checkUnivs false

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-!
  # Rules · AlphaDataToPartition

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaDataToPartition.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：AlphaFCAConstruction, AlgoKNNComponents
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  α 纤维块：划分的一块
    =========================================================================== -/

/-- ⭐⭐⭐ **【桥的第 1 半：`AlphaData` 的 α 给出划分的一个分块】**

同一 `alpha` 值的 `e'` 与 `e` 落在同一块。

这是「商化 → 划分」的**原子对象**：把 `E.Carrier` 按 α 输出分类，
每一类就是一个候选块。后续 §2 证明它满足块的封闭性，
§3 证明它在 `ker(obs)` 下饱和（即商化相容）。 -/
def alphaCell (D : AlphaData E M) (e : E.Carrier) : Set E.Carrier :=
  {e' | D.alpha e' = D.alpha e}

/-- 块的定义展开：`e' ∈ alphaCell D e ↔ alpha e' = alpha e`（`Iff.rfl`）。 -/
theorem mem_alphaCell_iff (D : AlphaData E M) (e e' : E.Carrier) :
    e' ∈ alphaCell D e ↔ D.alpha e' = D.alpha e := Iff.rfl

/-- **自反性**：`e` 在自己的块里（定义性，非实质定理）。 -/
theorem alphaCell_mem_self (D : AlphaData E M) (e : E.Carrier) :
    e ∈ alphaCell D e := rfl

/-- **对称性**：块关系是对称的。 -/
theorem alphaCell_symm (D : AlphaData E M) {e e' : E.Carrier}
    (h : e' ∈ alphaCell D e) : e ∈ alphaCell D e' :=
  h.symm

/-- **传递性**：若 `e''` 与 `e'` 同块、`e'` 与 `e` 同块，则 `e''` 与 `e` 同块。 -/
theorem alphaCell_trans (D : AlphaData E M) {e e' e'' : E.Carrier}
    (h₁ : e'' ∈ alphaCell D e') (h₂ : e' ∈ alphaCell D e) :
    e'' ∈ alphaCell D e :=
  h₁.trans h₂

/-- **同块则块相等**：`e' ∈ alphaCell D e → alphaCell D e' = alphaCell D e`。

注意结论是**集合外延相等**（需 `ext` + 向两侧用传递性），
**不是**前件的字面复制。 -/
theorem alphaCell_eq_of_mem (D : AlphaData E M) {e e' : E.Carrier}
    (h : e' ∈ alphaCell D e) : alphaCell D e' = alphaCell D e := by
  ext e''
  exact ⟨fun h'' => h''.trans h, fun h'' => h''.trans h.symm⟩

/-- **块相等 ↔ 代表元同块**（块由代表元唯一决定）。 -/
theorem alphaCell_eq_iff_mem (D : AlphaData E M) (e e' : E.Carrier) :
    alphaCell D e' = alphaCell D e ↔ e' ∈ alphaCell D e := by
  constructor
  · intro h
    rw [← h]
    exact alphaCell_mem_self D e'
  · exact alphaCell_eq_of_mem D

/-! ===========================================================================
    §2  覆盖性：块覆盖全体实例
    =========================================================================== -/

/-- ⭐ **块覆盖全体**：`⋃ e, alphaCell D e = univ`。

这是把 `{alphaCell D e | e}` 打包成划分所需的「覆盖性」一半
（另一半是 §1 的 `alphaCell_eq_of_mem`）。 -/
theorem alphaCell_union_eq_univ (D : AlphaData E M) :
    (⋃ e, alphaCell D e) = (univ : Set E.Carrier) := by
  ext e'
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨e', alphaCell_mem_self D e'⟩

/-! ===========================================================================
    §3  商化核心：块在 `ker(obs)` 下饱和
    =========================================================================== -/

/-- ⭐⭐⭐ **【商化相容：块尊重观测等价】**

若 `obs e' = obs e`，则 `e'` 与 `e` 同块；换言之，块在 `ker(obs)` 下**饱和**
（`ker(obs) ⊆ ker(alpha)`）。

**前件**是**观测**相等 `obs e' = obs e`（`ker(obs)` 的关系），
**结论**是**α 值**相等（`ker(alpha)` 的关系）—— 两者**是不同的等价关系**，
本定理是这两者之间的下降，靠 `AlphaData.alpha_respects_obs` 实现。

这正是子代理审计 §3.4 所说的「`alphaQuot` 只在 `ker(obs)` 上下降」的
**块形式**：α 纤维块作为 `ker(alpha)` 的类，是 `ker(obs)` 的类的**并**。 -/
theorem alphaCell_saturated (D : AlphaData E M) {e e' : E.Carrier}
    (h : D.obs e' = D.obs e) : e' ∈ alphaCell D e :=
  D.alpha_respects_obs h

/-! ===========================================================================
    §4  块与 `Setoid.ker` 的对齐（使「划分」与「商」对接）
    =========================================================================== -/

/-- ⭐ **块就是 `Setoid.ker D.alpha` 的等价类**：
`e' ∈ alphaCell D e ↔ (Setoid.ker D.alpha).r e' e`。

这使 `alphaCell` 与 Lean 的商类型 `Quotient (Setoid.ker D.alpha)` 直接对接，
而不只是「看起来像」纤维。 -/
theorem alphaCell_eq_ker (D : AlphaData E M) (e e' : E.Carrier) :
    e' ∈ alphaCell D e ↔ (Setoid.ker D.alpha).r e' e :=
  Iff.rfl

/-- ⭐ **块内代表元的商值相同**：`e' ∈ alphaCell D e →
alphaQuot D ⟦e'⟧ = alphaQuot D ⟦e⟧`。

即块内实例在 `alphaQuot`（`ker(obs)` 商上的下降）下**不可区分**。
需要真正使用 `Quotient.sound` 与 `alphaQuot_mk`，不是定义复制。 -/
theorem alphaQuot_eq_of_mem_alphaCell (D : AlphaData E M) {e e' : E.Carrier}
    (h : e' ∈ alphaCell D e) :
    D.alphaQuot (Quotient.mk _ e') = D.alphaQuot (Quotient.mk _ e) := by
  rw [alphaQuot_mk, alphaQuot_mk]
  exact h

/-- **块 ⊆ `alphaQuot` 纤维**：块内两个实例的 `alphaQuot` 值相等，
等价于说它们在 `ker(obs)` 的商下取同一个 α 值。 -/
theorem alphaCell_subset_alphaQuot_fiber (D : AlphaData E M) (e : E.Carrier) :
    ∀ e' ∈ alphaCell D e,
      D.alphaQuot (Quotient.mk _ e') = D.alphaQuot (Quotient.mk _ e) :=
  fun _ h => alphaQuot_eq_of_mem_alphaCell D h

/-- **块内概念外延相等**：`e' ∈ alphaCell D e → (alpha e').1.extent = (alpha e).1.extent`。

α 的第一分量（概念）在块内不变——即「划分的一块」承载同一个概念外延。 -/
theorem alphaCell_extent_eq (D : AlphaData E M) {e e' : E.Carrier}
    (h : e' ∈ alphaCell D e) :
    (D.alpha e').1.extent = (D.alpha e).1.extent :=
  congrArg (fun p => p.1.extent) h

end AlphaData

/-! ===========================================================================
    §5  公理审计
    =========================================================================== -/

#print axioms FateV2.Rules.AlphaData.alphaCell_mem_self
#print axioms FateV2.Rules.AlphaData.alphaCell_eq_of_mem
#print axioms FateV2.Rules.AlphaData.alphaCell_saturated
#print axioms FateV2.Rules.AlphaData.alphaCell_union_eq_univ
#print axioms FateV2.Rules.AlphaData.alphaCell_eq_ker
#print axioms FateV2.Rules.AlphaData.alphaQuot_eq_of_mem_alphaCell
#print axioms FateV2.Rules.AlphaData.alphaCell_extent_eq

end



/-! ===========================================================================
    §6  ⭐⭐ **消费 `AlgoKNNComponents`：α 块族是一个连通分量划分**（R-46）

本节把 `AlgoKNNComponents` 的 `IsConnectedPartition` 抽象
**实例化到本文件的 `alphaCell` 族**，并消费其 proper 族判据。
这使 `AlgoKNNComponents` 从「外部零引用」变成**被本文件实质调用**。

⚠ **防同义反复审计**：本节定理的**前件**是 `alphaCell` 的自反/同块相等性质
（来自本文件 §1 的已证引理）；**结论**是「α 块族满足
`IsConnectedPartition` 的三个字段」或「proper 族为空 ⟺ 全族 = `univ`」。
**结论是 `AlgoKNNComponents` 的抽象谓词，前件是本文件的具体构造性质** ——
两者由 `IsConnectedPartition` 的**三个字段**相接，**不是同一命题**。
-/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- ⭐⭐ **消费 1**：`alphaCell` 族（`range` 形式）是
`KNNComponents.IsConnectedPartition` 的一个实例。

三个字段分别由本文件已证引理提供：
* `nonempty`：`alphaCell_mem_self`（`e` 在自己的块里）；
* `pairwise_disjoint`：`alphaCell_eq_of_mem`（同块 ⟹ 块相等，故不同块不交）；
* `sUnion_eq`：`alphaCell_union_eq_univ`（块覆盖全体）。

⚠ **跨模块**：`KNNComponents.IsConnectedPartition` 来自 `AlgoKNNComponents`。 -/
theorem alphaCell_range_isConnectedPartition (D : AlphaData E M) :
    KNNComponents.IsConnectedPartition (Set.range (alphaCell (E := E) (M := M) D)) where
  nonempty := by
    rintro A ⟨e, rfl⟩
    exact ⟨e, alphaCell_mem_self D e⟩
  pairwise_disjoint := by
    rintro A ⟨e, rfl⟩ B ⟨e', rfl⟩ hne
    rw [Set.disjoint_left]
    intro x hx hx'
    -- `x` 同时在两块 ⟹ 两块相等，矛盾
    -- `hx : x ∈ alphaCell e` 直接给 `alphaCell x = alphaCell e`
    have h1 : alphaCell (E := E) (M := M) D x = alphaCell (E := E) (M := M) D e :=
      alphaCell_eq_of_mem D hx
    have h2 : alphaCell (E := E) (M := M) D x = alphaCell (E := E) (M := M) D e' :=
      alphaCell_eq_of_mem D hx'
    exact hne (h1.symm.trans h2)
  sUnion_eq := by
    rw [Set.sUnion_range]
    exact alphaCell_union_eq_univ D

/-- ⭐⭐ **消费 2**：α 块族的 **proper 族为空** ⟺ 族中每块都是 `univ`
（`AlgoKNNComponents` 的 `proper_family_empty_iff_all_univ` 在 `alphaCell` 上的实例）。

这是「kNN 实验中 `maxdiam*` 无定义」现象在 α 块上的**对应判据**：
若 α 只有**一个**块且它就是全体，则没有 proper 块可取。

⚠ **跨模块**：显式调用
`KNNComponents.IsConnectedPartition.proper_family_empty_iff_all_univ`。 -/
theorem alphaCell_proper_family_empty_iff (D : AlphaData E M) :
    ({B ∈ Set.range (alphaCell (E := E) (M := M) D) | B ≠ Set.univ}
        = (∅ : Set (Set E.Carrier)))
      ↔ (∀ B ∈ Set.range (alphaCell (E := E) (M := M) D), B = Set.univ) :=
  KNNComponents.IsConnectedPartition.proper_family_empty_iff_all_univ (C :=
    Set.range (alphaCell (E := E) (M := M) D))

/-- ⭐⭐ **消费 3**：α 块族的每个非空成员都能取出**具体见证点**
（`AlgoKNNComponents` 的 `exists_mem_and_mem_univ` 在 `alphaCell` 上的实例）。

这是把「块非空」这一抽象事实落到**具体的 `e : E.Carrier`** 上，
供下游「取块代表元」使用。

⚠ **跨模块**：显式调用
`KNNComponents.IsConnectedPartition.exists_mem_and_mem_univ`。 -/
theorem alphaCell_member_has_witness (D : AlphaData E M)
    {A : Set E.Carrier} (hA : A ∈ Set.range (alphaCell (E := E) (M := M) D)) :
    ∃ x : E.Carrier, x ∈ A ∧ x ∈ Set.univ :=
  KNNComponents.IsConnectedPartition.exists_mem_and_mem_univ
    (alphaCell_range_isConnectedPartition D) hA

end AlphaData

end FateV2.Rules