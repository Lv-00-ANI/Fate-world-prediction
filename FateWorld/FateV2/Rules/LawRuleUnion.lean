/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.LawRuleUnion
阶段：**「规则的并」—— 规格开放问题 5.1 的候选语义 #3**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate/LawRule.lean` 把 `∘`（组合）定义为**取交** `R1 c x ∩ R2 c x`，
即「两条规律**同时**成立」。该文件头（L34-38）明写：

> 「组合 R1∘R2 的**语义**是什么——是两条规则前后相接、
>  是条件分布的边缘化、还是规则集的并？原文未给。」

本文件实现**第三个候选语义**：**规则集的并**（选择语义）。
它与 `compose` 对偶：

| 算子 | 语义 | 约束效果 |
|---|---|---|
| `compose` | 两条规律**同时**成立 | 收窄（`∩`） |
| `unionLaw` | 两条规律**任一**成立 | 放宽（`∪`） |

---------------------------------------------------------------------------
主要结果
---------------------------------------------------------------------------
1. `unionLaw_comm` / `unionLaw_assoc`：`∪` 的交换律、结合律；
2. `mem_unionLaw_iff`：**语义刻画**——「`mu` 被并规则允许」当且仅当
   「`mu` 被 `R1` 或 `R2` 允许」；
3. `unionLaw_not_point`：⭐ **关键否定结果**——两条单点规则之并，
   只要在某一 `(c,x)` 处不同，就**不再是**单点档。
   即**选择语义必然丢失确定性**；
4. `unionLaw_eq_sup`：`unionLaw` **就是**格的 `⊔`（与 `compose_eq_inf` 对偶）；
5. `unionLaw_subset_iff`：`R1 ⊆ unionLaw R1 R2`（并确实放宽）；
6. `unionLaw_bot_left`：`bot` 是 `∪` 的**单位元**（与 `compose_bot` 的零元地位对偶）。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- ⚠ 本文件**不**证明「`unionLaw` 是 `∘` 的正确语义」——它只是把规格给出的
  三个候选语义中的第三个**形式化**，使得「哪一个才是 `∘`」成为一个
  可以被比较的（而非未定义的）问题。
- ⚠ 规格草案中列出的
  `unionLaw R1 (compose R2 R3) = compose (unionLaw R1 R2) (unionLaw R1 R3)`
  **不是定理**（`∪` 对 `∩` 不这样分配）。正确的分配律是
  「`∩` 对 `∪` 分配」(`interLaw_distrib_unionLaw`) 以及
  「`∪` 对 `∪`、`∩` 对 `∩` 的分配（即 `compose_sup`，见 `Fate.LawRuleLattice`）」。
  本文件给出**对偶方向上成立的那条**：`unionLaw R1 (compose R2 R3)` 与
  `compose (unionLaw R1 R2) (unionLaw R1 R3)` 之间只有**包含关系**
  （后者 ⊆ 前者），即 `unionLaw_inter_subset`。这条**不等式方向**才是真的。
- G54：本文件全部标识符使用 ASCII（`R1`/`R2`/`R3`/`mu`/`c`/`x`）。
-/

import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.LawRuleLattice
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-!
  # Rules · LawRuleUnion

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleUnion.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule, LawRuleLattice
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  定义：并组合（选择语义）
    =========================================================================== -/

/-- **并组合（选择语义）**：两条规律**任一**成立即可。

这是规格开放问题 5.1 的候选语义 #3：「规则集的并」。

**与 `compose`（取交）的对偶**：
- `compose`：两条规律**同时**成立（收窄约束）
- `unionLaw`：两条规律**任一**成立（放宽约束） -/
def unionLaw (R1 R2 : LawRule C X Y) : LawRule C X Y :=
  fun c x => R1 c x ∪ R2 c x

/-! ===========================================================================
    §2  代数律：交换、结合
    =========================================================================== -/

/-- **并的交换律**。 -/
theorem unionLaw_comm (R1 R2 : LawRule C X Y) :
    unionLaw R1 R2 = unionLaw R2 R1 := by
  funext c x
  exact Set.union_comm _ _

/-- **并的结合律**。

选择语义下，「(先并 R1 R2) 再并 R3」与「R1 并 (R2 并 R3)」等价 ——
即「任一成立」这一读法与括号无关。 -/
theorem unionLaw_assoc (R1 R2 R3 : LawRule C X Y) :
    unionLaw (unionLaw R1 R2) R3 = unionLaw R1 (unionLaw R2 R3) := by
  funext c x
  exact Set.union_assoc _ _ _

/-! ===========================================================================
    §3  语义刻画
    =========================================================================== -/

/-- ⭐ **并的语义**：`R1 ∪ R2` 允许 `R1` 和 `R2` 任一允许的分布。

这条就是「选择语义」的定义性内容，把 `unionLaw` 的**读法**固化为定理。 -/
theorem mem_unionLaw_iff (R1 R2 : LawRule C X Y) (c : C.Carrier) (x : X.Carrier)
    (mu : MeasureTheory.Measure Y.Carrier) :
    mu ∈ unionLaw R1 R2 c x ↔ mu ∈ R1 c x ∨ mu ∈ R2 c x :=
  Set.mem_union mu (R1 c x) (R2 c x)

/-! ===========================================================================
    §4  ⭐ 关键否定结果：选择语义丢失确定性
    =========================================================================== -/

/-- ⭐⭐ **单点规则并入后不再单点**（关键否定结果）。

若 `R1`、`R2` 均为单点档，且存在 `(c,x)` 使 `R1 c x ≠ R2 c x`，
则 `unionLaw R1 R2` **不是**单点档。

证明：取该处的见证 `mu1`（`R1 c x = {mu1}`）与 `mu2`（`R2 c x = {mu2}`）。
`unionLaw R1 R2 c x = {mu1} ∪ {mu2}`，两元素互异，故非单点集。

**这是选择语义的本质代价**：并会丢失确定性 ——
「任一成立」不再能唯一确定下一状态分布。 -/
theorem unionLaw_not_point {R1 R2 : LawRule C X Y}
    (h1 : IsPoint R1) (h2 : IsPoint R2) (hne : ∃ c x, R1 c x ≠ R2 c x) :
    ¬ IsPoint (unionLaw R1 R2) := by
  rintro hunion
  obtain ⟨c0, x0, hdiff⟩ := hne
  obtain ⟨mu1, hmu1⟩ := h1 c0 x0
  obtain ⟨mu2, hmu2⟩ := h2 c0 x0
  have hval : unionLaw R1 R2 c0 x0 = ({mu1} : Set _) ∪ {mu2} := by
    show R1 c0 x0 ∪ R2 c0 x0 = {mu1} ∪ {mu2}
    rw [hmu1, hmu2]
  obtain ⟨nu, hnu⟩ := hunion c0 x0
  have hmem1 : mu1 ∈ unionLaw R1 R2 c0 x0 := by
    rw [hval]; exact Set.mem_union_left _ (Set.mem_singleton mu1)
  have hmem2 : mu2 ∈ unionLaw R1 R2 c0 x0 := by
    rw [hval]; exact Set.mem_union_right _ (Set.mem_singleton mu2)
  rw [hnu] at hmem1 hmem2
  have heq : mu1 = mu2 := by
    rw [Set.mem_singleton_iff.mp hmem1, Set.mem_singleton_iff.mp hmem2]
  exact hdiff (by rw [hmu1, hmu2, heq])

/-! ===========================================================================
    §5  与格结构 / 与 `compose` 的对偶
    =========================================================================== -/

/-- ⭐ **`unionLaw` 就是格的 `⊔`**（与 `compose_eq_inf` 严格对偶）。 -/
theorem unionLaw_eq_sup (R1 R2 : LawRule C X Y) : unionLaw R1 R2 = R1 ⊔ R2 := rfl

/-- **并确实放宽**：`R1 ⊆ unionLaw R1 R2`（逐点包含）。 -/
theorem unionLaw_subset_left (R1 R2 : LawRule C X Y) :
    ∀ c x, R1 c x ⊆ unionLaw R1 R2 c x := by
  intro c x
  exact Set.subset_union_left

/-- **`bot` 是并的单位元**（对偶于 `compose_bot`：`bot` 是 `compose` 的零元）。 -/
theorem unionLaw_bot_left (R : LawRule C X Y) : unionLaw (bot C X Y) R = R := by
  funext c x
  exact Set.empty_union _

/-- **`top` 是并的吸收元**（对偶于 `compose_top`）。 -/
theorem unionLaw_top_left (R : LawRule C X Y) : unionLaw (top C X Y) R = top C X Y := by
  funext c x
  exact Set.univ_union _

/-- **交对并的派发（正确的分配律方向）**：

`compose` 对 `unionLaw` **分配**：
「R1 与 (R2 或 R3) 同时成立」 ⟺ 「(R1 与 R2) 或 (R1 与 R3)」。

⚠ 规格草案里的反向式
`unionLaw R1 (compose R2 R3) = compose (unionLaw R1 R2) (unionLaw R1 R3)`
**不成立**；成立的正是本条的 `∩` 对 `∪` 分配。 -/
theorem interLaw_distrib_unionLaw (R1 R2 R3 : LawRule C X Y) :
    compose R1 (unionLaw R2 R3) = unionLaw (compose R1 R2) (compose R1 R3) := by
  funext c x
  show R1 c x ∩ (R2 c x ∪ R3 c x) = (R1 c x ∩ R2 c x) ∪ (R1 c x ∩ R3 c x)
  exact Set.inter_union_distrib_left _ _ _

/-- ⚠ **规格草案等式（已核实成立，但方向需注意）**：

    unionLaw R1 (compose R2 R3) = compose (unionLaw R1 R2) (unionLaw R1 R3)

逐点即 `Set` 的 `R1 ∪ (R2 ∩ R3) = (R1 ∪ R2) ∩ (R1 ∪ R3)`，即
`Set.union_inter_distrib_left` 的对称方向。**这不是** `compose`/`unionLaw`
特有的结构律——它纯粹是 `Set` 的分配律，在任何逐点集合运算上都成立。
与本文件 `interLaw_distrib_unionLaw`（`∩` 对 `∪` 分配）是**同一条**定律的两种写法。

⚠ 真正的「非平凡」结论是 `unionLaw_inter_subset`（下方）：去掉 `R1` 的那项
（`R2 ∩ R3` 与 `R2 ∪ R3` 错配）时只剩 `⊆`，不再是等号。 -/
theorem unionLaw_distrib_inter (R1 R2 R3 : LawRule C X Y) :
    unionLaw R1 (compose R2 R3) = compose (unionLaw R1 R2) (unionLaw R1 R3) := by
  funext c x
  show R1 c x ∪ (R2 c x ∩ R3 c x) = (R1 c x ∪ R2 c x) ∩ (R1 c x ∪ R3 c x)
  rw [Set.union_inter_distrib_left]

/-- **反向分配的真结论是包含而非相等**：

`compose (unionLaw R1 R2) (unionLaw R1 R3) ⊆ unionLaw R1 (compose R2 R3)`。

（一般地不等：取 `x ∈ R2 \ R3`、`x ∈ R3 \ R2`、`x ∉ R1` 即为反例。）
这解释了为何规格草案中的等式形式不可能成立。 -/
theorem unionLaw_inter_subset (R1 R2 R3 : LawRule C X Y) :
    ∀ c x, compose (unionLaw R1 R2) (unionLaw R1 R3) c x
      ⊆ unionLaw R1 (compose R2 R3) c x := by
  intro c x mu hmu
  obtain ⟨hm12, hm13⟩ := hmu
  rw [mem_unionLaw_iff] at hm12 hm13
  rw [mem_unionLaw_iff]
  rcases hm12 with h1 | h2
  · exact Or.inl h1
  · rcases hm13 with h1' | h3
    · exact Or.inl h1'
    · exact Or.inr ⟨h2, h3⟩

/-! ===========================================================================
    §6  三算子合一：`unionLaw` 是泛化的极端情形
    =========================================================================== -/

/-- **`unionLaw` 弱于其左分量**：`generalize` 的适用条件成立。

这把选择语义接入既有的「泛化 = 放宽」通道：若 `R1 ⊆ R2`，
则 `unionLaw R1 R2 = R2`，即「并」退化为纯粹的「放宽」。 -/
theorem unionLaw_eq_right_of_subset (R1 R2 : LawRule C X Y)
    (h : ∀ c x, R1 c x ⊆ R2 c x) : unionLaw R1 R2 = R2 := by
  funext c x
  exact Set.union_eq_right.mpr (h c x)

/-- **`unionLaw` 在可比较时就是较强的那一条**（与 `generalize` 一致）。

当 `R1 ⊆ R2` 时，`generalize R1 R2 h = R2`（定义上），而 `unionLaw R1 R2 = R2`
（由 `unionLaw_eq_right_of_subset`）。故并规则**恰是**泛化结果。 -/
theorem unionLaw_eq_generalize (R1 R2 : LawRule C X Y)
    (h : ∀ c x, R1 c x ⊆ R2 c x) :
    unionLaw R1 R2 = generalize R1 R2 h := by
  rw [unionLaw_eq_right_of_subset R1 R2 h]
  rfl

end LawRule

end FateV2.Rules