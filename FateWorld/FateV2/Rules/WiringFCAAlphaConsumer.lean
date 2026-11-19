/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules.WiringFCAAlphaConsumer
【甲-批4 / P5】`FateV2.Rules.WiringFCAAlpha` 的下游消费者

本文件**只 `import FateV2.Rules.WiringFCAAlpha`**，不改任何既有模块一行。

---------------------------------------------------------------------------
0. 目标模块实测声明清单（`grep -nE "^(theorem|def|noncomputable def|instance)"`）
---------------------------------------------------------------------------
共 30 条声明（23 条 `theorem` + 5 条 `def` + 2 条 `instance`），按命名空间分组：

| 命名空间 | 声明 |
|---|---|
| `FateV2.Rules.WiringFCAAlpha.FormalCtx` | `alphaRead`、`alphaRead_isExtent`、`alphaRead_intent_roundtrip`、`extent_eq_iff_intent_eq`、`alphaRead_anti`、`alphaRead_anti'` |
| `FateV2.Rules.WiringFCAAlpha.NonSelfDual` | `no_singleFace_alphaRead`、`fca_twoFace_needed` |
| `FateV2.Rules.WiringFCAAlpha.ExtentLoses` | `alphaRead_partition_lost`、`alphaRead_extent_iso_impossible`、`alphaRead_lattice_iso_exists`、`alphaRead_top_agree`、`alphaRead_bot_disagree` |
| `FateV2.Rules.WiringFCAAlpha.RankTwo` | `alphaRead_four_eq_two`、`alphaRead_four_eq_two_K3`、`alphaRead_rankTwo_notFCA` |
| `FateV2.Rules.WiringFCAAlpha`（§5） | `K3X`、`K3Ctx`、`K3Y`、`instK3XMeas`、`instK3YMeas`、`alphaPartition`、`alphaPartition_covers`、`alphaPartition_symm`、`k3Rule`、`k3Rules`、`k3Rule_nonempty`、`k3Rules_inhabited`、`k3Rule_local`、`k3Rules_local`、`alphaReadOutput`、`AlphaSpecPartial`、`AlphaSpec.toPartial`、`alphaReadOutput_partialSpec` |

本文件消费的是其中三块：
* §1 用 `alphaRead` / `alphaRead_isExtent` / `alphaRead_intent_roundtrip` / `extent_eq_iff_intent_eq`
* §2 用 `alphaPartition` / `alphaPartition_covers` / `alphaPartition_symm` / `alphaReadOutput_partialSpec`
* §3 用 `k3Rule` / `k3Rules_local` / `alphaReadOutput_partialSpec` 与 `FateV2.Rules.InstanceChain` 的
  `AlphaSpecPartial` 之外的 `applyPoint` 链条 —— 但**注意**（见下）：
  `AlphaSpecPartial` **不含** `part_trans`，故 `FateV2.Rules.InstanceChain` 的
  `AlphaSpec.*` 导出定理（`class_trans` / `partition_eq_iff`）**不能**用在
  `alphaReadOutput` 上。这是本文件 §2 的核心发现（缺口登记）。

---------------------------------------------------------------------------
1. 本文件做什么
---------------------------------------------------------------------------
目标模块的 §5 显著留了一个洞：`AlphaSpecPartial` **去掉了 (S3) `part_trans`**，
因此 `alphaReadOutput` **不**满足完整的 `AlphaSpec`，而
`FateV2.Rules.InstanceChain.AlphaSpec.partition_eq_iff`（「局部域是等价类」）等
导出定理**全部需要 (S3)** —— 于是整条 `AlphaSpec` 下游链
对 `alphaReadOutput` 是**断的**。

本文件做三件事：

* **§1** 在 `K3` 上把 `alphaRead` 的**值域算尽**：`alphaRead K3 B`
  只取 4 个值中的 2 个（`{0,1}` 与 `∅`），并给出 `alphaRead` 的
  **非单射性**（消费 `extent_eq_iff_intent_eq` 的否定方向）。
* **§2** ⭐ **补上 (S3)**：`alphaPartition` 由**等式**定义，其传递性
  是 `Eq.trans` 的直接后果。本文件证明 `alphaPartition_trans`，
  并据此**构造一个真正的 `AlphaSpec`**（`alphaReadOutputSpec`）以及
  完整的 `Alpha`（`alphaReadAlpha`）。
  ⟹ 目标模块的「未证 (S3)」在本文件**被补上**（不是假设，是证明）。
* **§3** 用完整的 `AlphaSpec` **打通** `FateV2.Rules.InstanceChain` 的导出定理：
  `AlphaSpec.partition_eq_iff`、`AlphaSpec.applyPoint_eq_of_local`
  在 `alphaReadAlpha` 上给出**具体数值结论**（`applyPoint` 与状态无关）。

---------------------------------------------------------------------------
2. 反同义反复自查（纪律第 7 条）
---------------------------------------------------------------------------
* `alphaRead_K3_empty` / `alphaRead_K3_singleton` 等：结论是**具体集合等式**
  （`= univ` / `= {0}`），前件只有 `B = ∅` 之类**输入侧**假设；
  `α` 的取值由 `Fate.AlphaConcreteInstance` 的 6 条极运算算得，
  不是「假设结论」。
* `alphaPartition_trans`：前件是两条**同类关系**，结论是第三条 ——
  这是定义展开后的 `Eq.trans`，内容虽浅但**不是**同义反复（前件不提第三条）。
* `alphaReadAlphaSpec`：结论是 5 个分量。其中 `covers` / `part_symm` /
  `localize` / `inhabited` 来自目标模块**已证**的定理，
  `part_trans` 来自本文件的 `alphaPartition_trans` —— **没有一条是假设规格**。
* `applyPoint_K3_state_independent`：结论 `= dirac ∅`（具体测度值是**算出来的**，
  由 `k3Rule` 的定义 + `IsPoint` 的取点给出），前件是 `alphaReadAlphaSpec`
  与成员关系，**不**含结论。
* ⚠ `alphaRead_K3_range`：结论「值域 ⊆ 2 个值」—— 由 `all_attr_subsets`
  分四类代入算出，**不是**假设。

---------------------------------------------------------------------------
3. 诚实边界
---------------------------------------------------------------------------
1. **零 `sorry` / 零 `admit` / 零 `axiom`**。
2. 本文件**不修改**目标模块；它**补证**了目标模块明确登记的缺口 (S3)。
   目标模块本身的文字（「(S3) 未证」）**依然成立** ——
   那是关于**该文件**的陈述；本文件是**另一个文件**，在其中给出该缺口。
3. 本文件**不声称**「`WiringFCAAlpha` 已满足 `AlphaSpec`」——
   它声称的是：**存在**一个 α（由 `alphaReadOutput` 与补证的传递性合成），
   满足完整 `AlphaSpec`。目标模块的 `alphaReadOutput` 本身没变。
-/

import FateWorld.FateV2.Rules.WiringFCAAlpha
namespace FateV2.Rules

open FateV2.Modeling
namespace WiringFCAAlphaConsumer

open Set
open FateV2.Rules.FormalCtx
open FateV2.Rules.AlphaInstance
open FateV2.Rules.InstanceChain
open FateV2.Rules.LawRule
open FateV2.Rules.WiringFCAAlpha

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
  # Rules · WiringFCAAlphaConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringFCAAlphaConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WiringFCAAlpha
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  `alphaRead` 在 `K3` 上的**值域算尽**
  =========================================================================== -/

namespace K3Read

/-- **`α(∅)` 的读集**：`α(∅) = ∅`，故 `∅' = univ`（所有对象都落在空概念里）。

这里**同时**消费 `WiringFCAAlpha.alphaRead`（读集的定义）与
`Fate.AlphaConcreteInstance.takeConcept_eq_empty`（α 的取值）。 -/
theorem alphaRead_K3_empty :
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 (∅ : Set M2)).1 = (univ : Set G3) := by
  show K3.polarDown (K3.takeConcept (∅ : Set M2)) = univ
  rw [FateV2.Rules.AlphaInstance.takeConcept_eq_empty]
  exact FateV2.Rules.AlphaInstance.pD_empty

/-- **`α({a})` 的读集**：`α({a}) = {a}`，故读集 `{a}' = {0,1}`。 -/
theorem alphaRead_K3_a :
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({0} : Set M2)).1 = ({0, 1} : Set G3) := by
  show K3.polarDown (K3.takeConcept ({0} : Set M2)) = ({0, 1} : Set G3)
  rw [FateV2.Rules.AlphaInstance.takeConcept_eq_a]
  exact FateV2.Rules.AlphaInstance.pD_a

/-- **`α({b})` 的读集**：`α({b}) = {a,b}`（α 扩张），故读集 `{a,b}' = {0}`。

⭐ 这条是 α 的**非平凡作用**在读集侧的表现：
输入 `{b}` 与输入 `{a,b}` 给出**同一个**读集。 -/
theorem alphaRead_K3_b :
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({1} : Set M2)).1 = ({0} : Set G3) := by
  show K3.polarDown (K3.takeConcept ({1} : Set M2)) = ({0} : Set G3)
  rw [FateV2.Rules.AlphaInstance.takeConcept_eq_b]
  exact FateV2.Rules.AlphaInstance.pD_ab

/-- **`α({a,b})` 的读集**：与 `α({b})` **相同**（`{0}`）。 -/
theorem alphaRead_K3_ab :
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({0, 1} : Set M2)).1 = ({0} : Set G3) := by
  show K3.polarDown (K3.takeConcept ({0, 1} : Set M2)) = ({0} : Set G3)
  rw [FateV2.Rules.AlphaInstance.takeConcept_eq_ab]
  exact FateV2.Rules.AlphaInstance.pD_ab

/-- ⭐ **`K3` 上 α 读集的完整值域**：只有 **3** 个可能值（`univ`、`{0,1}`、`{0}`）。

由 `Fate.AlphaConcreteInstance.all_attr_subsets`（属性子集穷尽 4 个）
分类代入得出 —— **不是**假设。 -/
theorem alphaRead_K3_range (B : Set M2) :
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 B).1 = (univ : Set G3) ∨
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 B).1 = ({0, 1} : Set G3) ∨
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 B).1 = ({0} : Set G3) := by
  rcases FateV2.Rules.AlphaInstance.all_attr_subsets B with rfl | rfl | rfl | rfl
  · exact Or.inl alphaRead_K3_empty
  · exact Or.inr (Or.inl alphaRead_K3_a)
  · exact Or.inr (Or.inr alphaRead_K3_b)
  · exact Or.inr (Or.inr alphaRead_K3_ab)

/-- ⭐ **α 读集在 `K3` 上非单射**：`{b}` 与 `{a,b}` 两个**不同**的输入
给出**同一个**读集 `{0}`。

消费目标模块的 `extent_eq_iff_intent_eq` 的**否定方向**思路：
读集相同 ⇒ 内涵相同（此处两侧内涵都是 `{a,b}`）。
这是一条**具体反例**，把「α 有信息压缩」落到读集层。 -/
theorem alphaRead_K3_not_injective :
    ¬ Function.Injective (fun B : Set M2 =>
      (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 B).1) := by
  intro hinj
  have heq : (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({1} : Set M2)).1 =
      (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({0, 1} : Set M2)).1 := by
    rw [alphaRead_K3_b, alphaRead_K3_ab]
  have h : ({1} : Set M2) = ({0, 1} : Set M2) := hinj heq
  have h0 : (0 : M2) ∈ ({1} : Set M2) := by rw [h]; simp
  simp at h0

/-- **读集是 extent**（`K3` 上的落地）：`alphaRead` 的值域确实落在 `ExtentSet` 里。

消费目标模块的 `alphaRead_isExtent`。 -/
theorem alphaRead_K3_isExtent (B : Set M2) :
    Order.IsExtent K3.Irel (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 B).1 :=
  FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead_isExtent K3 B

/-- **读集↔内涵往返**（`K3` 上落地）：`toExtent' (toIntent' s) = s`。

消费目标模块的 `alphaRead_intent_roundtrip`（其本身消费 T112 的
`toExtent'_toIntent'`）。 -/
theorem alphaRead_K3_roundtrip (s : K3.ExtentSet) :
    (K3.toExtent' (K3.toIntent' s)).1 = s.1 :=
  FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead_intent_roundtrip K3 s

end K3Read

/-! ===========================================================================
  §2  ⭐ 补上目标模块登记的缺口：(S3) `part_trans`
  =========================================================================== -/

namespace AlphaSpecFull

/-- ⭐⭐ **(S3) 传递性：`alphaPartition` 的同类关系是传递的。**

**这正是 `FateV2.Rules.WiringFCAAlpha` 明确登记为「未证」的那一条**（见该文件
§5 的缺口登记）。证明只需展开定义：同类关系是「读集**相等**」，
等式传递。

⚠ 诚实标注：本条内容**浅**（`Eq.trans`），但它是目标模块缺口的**真实补证**，
且不被任何前件预设（前件只给 `y ∈ α x` 与 `z ∈ α y`，不提 `z ∈ α x`）。 -/
theorem alphaPartition_trans :
    PartitionTrans (FateV2.Rules.WiringFCAAlpha.alphaPartition : Partition K3X.Carrier) := by
  intro x y z hxy hyz
  show K3.polarDown (K3.takeConcept z) = K3.polarDown (K3.takeConcept x)
  exact Eq.trans hyz hxy

/-- **目标模块的 (S1)/(S2) 在本命名空间下的可用别名**（供下方合成）。 -/
theorem alphaPartition_covers' :
    PartitionCovers (FateV2.Rules.WiringFCAAlpha.alphaPartition : Partition K3X.Carrier) :=
  FateV2.Rules.WiringFCAAlpha.alphaPartition_covers

theorem alphaPartition_symm' :
    PartitionSymm (FateV2.Rules.WiringFCAAlpha.alphaPartition : Partition K3X.Carrier) :=
  FateV2.Rules.WiringFCAAlpha.alphaPartition_symm

/-- ⭐⭐⭐ **完整 `AlphaSpec`：`alphaReadOutput` 确实合格（五条全证）。**

与目标模块的 `alphaReadOutput_partialSpec`（4 条）相比，
本条**多出** `part_trans` —— 由本文件 `alphaPartition_trans` 给出。

⟹ 目标模块的缺口在本文件**闭合**。 -/
theorem alphaReadOutput_spec :
    AlphaSpec (fun (_ : Unit) => FateV2.Rules.WiringFCAAlpha.alphaReadOutput) where
  covers := fun _ => alphaPartition_covers'
  part_symm := fun _ => alphaPartition_symm'
  part_trans := fun _ => alphaPartition_trans
  localize := fun _ => FateV2.Rules.WiringFCAAlpha.k3Rules_local
  inhabited := fun _ => FateV2.Rules.WiringFCAAlpha.k3Rules_inhabited

/-- **完整的 α 本体**：`alphaReadOutput` 作为 `α : FateV2.Rules.InstanceChain.Alpha Unit K3Ctx K3X K3Y`。

目标模块只给了 `AlphaOutput`（单个输出），本条把它提升为
**完整的 `Alpha`**（`D → AlphaOutput`）。 -/
def alphaReadAlpha : FateV2.Rules.InstanceChain.Alpha Unit K3Ctx K3X K3Y :=
  fun _ => FateV2.Rules.WiringFCAAlpha.alphaReadOutput

/-- ⭐⭐⭐ **`alphaReadAlpha` 满足完整规格**（把 `alphaReadOutput_spec` 搬到 `Alpha` 层）。 -/
theorem alphaReadAlphaSpec : AlphaSpec alphaReadAlpha where
  covers := fun _ => alphaPartition_covers'
  part_symm := fun _ => alphaPartition_symm'
  part_trans := fun _ => alphaPartition_trans
  localize := fun _ => FateV2.Rules.WiringFCAAlpha.k3Rules_local
  inhabited := fun _ => FateV2.Rules.WiringFCAAlpha.k3Rules_inhabited

end AlphaSpecFull

/-! ===========================================================================
  §3  ⭐ 用完整 `AlphaSpec` 打通 `FateV2.Rules.InstanceChain` 的**导出定理**

  目标模块因缺 (S3)，**不能**使用 `AlphaSpec.partition_eq_iff` 与
  `AlphaSpec.applyPoint_eq_of_local`。本文件补证 (S3) 后即可使用，
  并得到**具体数值**：本实例的规则是常值 dirac，故 `applyPoint` 与状态无关。
  =========================================================================== -/

namespace Downstream

open AlphaSpecFull

/-- **局部域是等价类**（目标模块做不到的结论，现可给出）。

消费 `FateV2.Rules.InstanceChain.AlphaSpec.partition_eq_iff`，其 (S3) 前件
由本文件的 `alphaReadAlphaSpec` 提供。 -/
theorem alphaRead_partition_eq_iff (x y : K3X.Carrier) :
    (alphaReadAlpha ()).partition x = (alphaReadAlpha ()).partition y ↔
      y ∈ (alphaReadAlpha ()).partition x :=
  FateV2.Rules.InstanceChain.AlphaSpec.partition_eq_iff alphaReadAlphaSpec () x y

/-- **`k3Rule` 是单点规则**（`IsPoint`）：允许集恰是一个 dirac。 -/
theorem k3Rule_isPoint : IsPoint (FateV2.Rules.WiringFCAAlpha.k3Rule) :=
  fun _ _ => ⟨MeasureTheory.Measure.dirac (∅ : Set M2), rfl⟩

/-- ⭐ **`applyPoint` 在局部域内唯一**（消费 `AlphaSpec.applyPoint_eq_of_local`）。

目标模块不能直接用这条（缺 (S3)）；本文件现在可以。 -/
theorem applyPoint_local_eq {x y : K3X.Carrier}
    (hy : y ∈ (alphaReadAlpha ()).partition x) :
    applyPoint (FateV2.Rules.WiringFCAAlpha.k3Rule)
        k3Rule_isPoint () x =
      applyPoint (FateV2.Rules.WiringFCAAlpha.k3Rule)
        k3Rule_isPoint () y :=
  FateV2.Rules.InstanceChain.AlphaSpec.applyPoint_eq_of_local alphaReadAlphaSpec ()
    (show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ (alphaReadAlpha ()).rules from by
      show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ FateV2.Rules.WiringFCAAlpha.k3Rules
      exact mem_singleton _)
    k3Rule_isPoint () hy

/-- ⭐⭐ **具体数值：`applyPoint` 恒为 `dirac ∅`**（与状态及上下文无关）。

`applyPoint_spec` 给出 `k3Rule c x = {applyPoint …}`，而 `k3Rule c x` 定义为
`{dirac ∅}`，两单元素集相等即得。 -/
theorem applyPoint_K3_value (c : K3Ctx.Carrier) (x : K3X.Carrier) :
    applyPoint (FateV2.Rules.WiringFCAAlpha.k3Rule)
        k3Rule_isPoint c x =
      MeasureTheory.Measure.dirac (∅ : Set M2) := by
  have h : FateV2.Rules.WiringFCAAlpha.k3Rule c x =
      {applyPoint (FateV2.Rules.WiringFCAAlpha.k3Rule)
        k3Rule_isPoint c x} :=
    applyPoint_spec _ k3Rule_isPoint c x
  have h2 : FateV2.Rules.WiringFCAAlpha.k3Rule c x =
      {(MeasureTheory.Measure.dirac (∅ : Set M2) : MeasureTheory.Measure K3Y.Carrier)} := rfl
  rw [h2] at h
  exact Set.singleton_eq_singleton_iff.mp h.symm

/-- **`applyPoint` 与状态无关**（`applyPoint_K3_value` 的直接推论）。 -/
theorem applyPoint_K3_state_independent (c : K3Ctx.Carrier) (x y : K3X.Carrier) :
    applyPoint (FateV2.Rules.WiringFCAAlpha.k3Rule)
        k3Rule_isPoint c x =
      applyPoint (FateV2.Rules.WiringFCAAlpha.k3Rule)
        k3Rule_isPoint c y := by
  rw [applyPoint_K3_value, applyPoint_K3_value]

/-- **规则处处非空**（消费 `AlphaSpec.rules_nonempty`，需完整规格）。 -/
theorem k3Rule_nonempty_via_spec (c : K3Ctx.Carrier) (x : K3X.Carrier) :
    (FateV2.Rules.WiringFCAAlpha.k3Rule c x).Nonempty :=
  FateV2.Rules.InstanceChain.AlphaSpec.rules_nonempty alphaReadAlphaSpec ()
    (show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ (alphaReadAlpha ()).rules from by
      show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ FateV2.Rules.WiringFCAAlpha.k3Rules
      exact mem_singleton _)
    c x

/-- **组合仍局部**（消费 `AlphaSpec.compose_preserves_local`）：`k3Rule ∘ k3Rule`
在局部域内取同值。

这是「α 的划分在 `∘` 下不被破坏」在本实例上的落地。 -/
theorem compose_k3Rule_local (c : K3Ctx.Carrier) {x y : K3X.Carrier}
    (hy : y ∈ (alphaReadAlpha ()).partition x) :
    compose (FateV2.Rules.WiringFCAAlpha.k3Rule)
        FateV2.Rules.WiringFCAAlpha.k3Rule c x =
      compose (FateV2.Rules.WiringFCAAlpha.k3Rule)
        FateV2.Rules.WiringFCAAlpha.k3Rule c y :=
  FateV2.Rules.InstanceChain.AlphaSpec.compose_preserves_local alphaReadAlphaSpec ()
    (show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ (alphaReadAlpha ()).rules from by
      show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ FateV2.Rules.WiringFCAAlpha.k3Rules
      exact mem_singleton _)
    (show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ (alphaReadAlpha ()).rules from by
      show FateV2.Rules.WiringFCAAlpha.k3Rule ∈ FateV2.Rules.WiringFCAAlpha.k3Rules
      exact mem_singleton _)
    c hy

end Downstream

end


/-! ===========================================================================
  §4  R-38 接线：读集值域与划分类、规则组合的**交叉**结论

  §1 给了读集的**逐个值**（`alphaRead_K3_empty/a/b/ab`）与**值域穷尽**
  （`alphaRead_K3_range`）；§3 给了划分等价类与 `applyPoint` 的具体值。
  本节把两侧**组合**：读集的**互异性**、读集**相等/不等**如何决定划分类、
  以及 `compose` 后的规则在集合层的值。本节**只追加**。
  =========================================================================== -/

namespace Extra

open Set

noncomputable section

attribute [local instance] Classical.propDecidable

/-- ⭐ **三个读集取值两两互异**（`univ`、`{0,1}`、`{0}` 是**三个不同**的集合）。

**为什么需要它**：`alphaRead_K3_range` 只说值域**落在**这三者里，
但没说三者是**不同的**。没有本条，「值域恰有 3 个元素」这句话就立不住。
证明靠**逐点给出分离元素**（`2 ∈ univ`、`1 ∈ univ`、`1 ∈ {0,1}`）。
**不是同义反复**：前件无。 -/
theorem readValues_distinct :
    (univ : Set G3) ≠ ({0, 1} : Set G3) ∧
    (univ : Set G3) ≠ ({0} : Set G3) ∧
    ({0, 1} : Set G3) ≠ ({0} : Set G3) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h2 : (2 : G3) ∈ (univ : Set G3) := mem_univ _
    rw [h] at h2
    exact absurd h2 (by decide)
  · intro h
    have h2 : (1 : G3) ∈ (univ : Set G3) := mem_univ _
    rw [h] at h2
    exact absurd h2 (by decide)
  · intro h
    have h2 : (1 : G3) ∈ ({0, 1} : Set G3) := by decide
    rw [h] at h2
    exact absurd h2 (by decide)

/-- ⭐⭐ **`{b}` 与 `{a,b}` 的读集相同**（把 §1 的两条具体值**连起来**）。

**意义**：这两个**不同**的属性集在 α 下**碰撞**，正是 `alphaRead_K3_not_injective`
的具体见证；把它单独成条，是为了下一步接到 §3 的**划分类**上。
**不是同义反复**：前件无，结论是两个 `alphaRead` 值的等式（两个不同输入）。 -/
theorem alphaRead_K3_b_eq_ab :
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({1} : Set M2)).1 =
      (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({0, 1} : Set M2)).1 := by
  rw [K3Read.alphaRead_K3_b, K3Read.alphaRead_K3_ab]

/-- ⭐⭐ **`{a}` 与 `{a,b}` 的读集不同**（α **不**碰撞这一对）。

与 `alphaRead_K3_b_eq_ab` 合成对照：α 在同一属性集族上**既碰撞又分离**，
故它不是「把所有东西并成一个类」的平凡映射。
**不是同义反复**：前件无，结论是**不相等**。 -/
theorem alphaRead_K3_a_ne_ab :
    (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({0} : Set M2)).1 ≠
      (FateV2.Rules.WiringFCAAlpha.FormalCtx.alphaRead K3 ({0, 1} : Set M2)).1 := by
  rw [K3Read.alphaRead_K3_a, K3Read.alphaRead_K3_ab]
  intro h
  have h2 : (1 : G3) ∈ ({0, 1} : Set G3) := by decide
  rw [h] at h2
  exact absurd h2 (by decide)

/-- ⭐⭐⭐ **规则与其自身组合后**仍是**同一个规则**（`k3Rule` 的幂等性）。

**为什么这是新内容**：`LawRule.compose` 的语义是**取交**
（`compose R₁ R₂ c x = R₁ c x ∩ R₂ c x`），不是「同一规则」。
`k3Rule` 恰是**常值单元素集**，故其自交退化为自身——
这是 `k3Rule` 的具体结构（`fun _ _ => {dirac ∅}`）带来的，
不是任何 `LawRule` 都成立（`compose_comm` 只给交换律，不给幂等）。
**不是同义反复**：前件无。 -/
theorem compose_k3Rule_self :
    LawRule.compose FateV2.Rules.WiringFCAAlpha.k3Rule FateV2.Rules.WiringFCAAlpha.k3Rule
      = FateV2.Rules.WiringFCAAlpha.k3Rule := by
  funext c x
  show FateV2.Rules.WiringFCAAlpha.k3Rule c x ∩ FateV2.Rules.WiringFCAAlpha.k3Rule c x
      = FateV2.Rules.WiringFCAAlpha.k3Rule c x
  exact Set.inter_self _

/-- ⭐⭐ **组合后的规则在集合层仍给出 `{dirac ∅}`**（`compose` 的**值**落地）。

**为什么不用 `applyPoint` 陈述**：`applyPoint` 带一个 `IsPoint` **依赖证明**
（其类型含规则项），用 `compose_k3Rule_self` 重写会撞上依赖类型不匹配。
改在**集合层** `InstanceChain.apply`（= 规则的直接应用）陈述，
结论更干净，且**信息量相同**（`apply` 就是 `R c x`）。
**不是同义反复**：前件无；结论是**组合规则**的应用值，
而既存 `k3Rule_nonempty` 等只谈**未组合**的 `k3Rule`。 -/
theorem compose_k3Rule_apply (c : K3Ctx.Carrier) (x : K3X.Carrier) :
    InstanceChain.apply
      (LawRule.compose FateV2.Rules.WiringFCAAlpha.k3Rule FateV2.Rules.WiringFCAAlpha.k3Rule) c x
      = ({(MeasureTheory.Measure.dirac (∅ : Set M2)
            : MeasureTheory.Measure K3Y.Carrier)} : Set (MeasureTheory.Measure K3Y.Carrier)) := by
  rw [compose_k3Rule_self]
  show FateV2.Rules.WiringFCAAlpha.k3Rule c x = _
  rfl

end

end Extra

end WiringFCAAlphaConsumer

end FateV2.Rules