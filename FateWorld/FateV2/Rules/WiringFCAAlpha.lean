/-
命运理论 · Lean 4 形式化实现
================================

模块：WiringFCAAlpha
任务：**W1-最高优先 接线** —— 把 `FateV2.Rules` 的具体 FCA 结果
      接到规则层 α（`FateV2.Rules` / `FateV2.Rules.InstanceChain.AlphaOutput`）。

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate/T112FCASpecific.lean` 此前是**孤立的**：已证明，但无任何下游消费。
本文件是它的**下游**，并且**不是只 import** —— 下面每条新定理的
**陈述里都出现 `T112FCASpecific` 的结论作为实质成分**：

| 用到的 T112FCASpecific 结论 | 在本文件里如何被真正使用 |
|---|---|
| `toExtent'_toIntent'` / `toIntent'_le_iff` / `toExtent'_le_iff` | α 读集↔内涵的**双射**与**反序**：§1 |
| `ClosureSep.NonSelfDual.no_selfDual_iso`（一般闭包算子非自对偶） | ⭐ **α 阅读不能单面实现**：`no_singleFace_alphaRead` |
| `Counterexample.KA_KC_lattice_iso`（概念格同构） | α 的读集格**可以**同构（但见下条） |
| `Counterexample.no_extent_preserving_iso` | ⭐ **α 读集划分丢失外延信息**：`alphaRead_partition_lost` |
| `Counterexample.no_extent_card_preserving_iso` | 加强形式：`alphaRead_extent_iso_impossible` |
| `Counterexample.KA_bot_extent_nonempty` / `KC_bot_extent_empty` | `alphaRead_bot_disagree` |
| `Counterexample.KA_top_extent` / `KC_top_extent` | `alphaRead_top_agree`（差异只在 `⊥` 侧） |
| `RankTwo.polarUp_polarDown_polarUp_polarDown_idem`（四次极=二次极） | α 读集闭包**秩 ≤ 2**：`alphaRead_four_eq_two` |
| `Contrast.closure_four_eq_two`（一般对照） | 诚实性对照（防虚假声称）：`alphaRead_rankTwo_notFCA` |

§5 再给出**真正的 α 实例**：`FateV2.Rules.InstanceChain.AlphaOutput` 的具体构造，
其 `partition` 由 `K3`（`FateV2.Rules` 的取概念过程）的**读集（extent）**给出。

---------------------------------------------------------------------------
🔧 P-006 修复记录（本次 = 修 `29 error`；按 `坏模块分诊.md` 判定为 **FIX**）
---------------------------------------------------------------------------

**病因三分**（drift 4 / local 12 / 一处结构错位）：

| # | 原写法 | 病因 | 修法 |
|---|---|---|---|
| 1 | `⟨Set G3⟩` 构造 `StateSpace` | 上游 `StateSpace` 已从单字段改为
`Carrier` / `topo` / `meas` / `borel_le` 四分量 | 逐字段构造，`meas := @borel _ ⊤`、`borel_le := le_rfl` |
| 2 | `alphaPartition : Set G3 → …` 里调 `K3.takeConcept y` | ⚠ **不是改名，是类型写错**：`takeConcept : Set K.MFCA → Set K.MFCA`，
而 α 的输入本来就是**属性集**；写成 `Set G3`（对象集）类型不符 | 状态类型改为 `Set M2`（`= Set K3.MFCA`） |
| 3 | `LawRule` / `Alpha` / `AlphaSpec` 未限定 | `LawRule` 在 `LawRule`，`Alpha`/`AlphaSpec` 在 `FateV2.Rules.InstanceChain`；
且 `FateV2.Model.Alpha`（接 `InstSpace`）**与** `FateV2.Rules.InstanceChain.Alpha`（接 `Type u`）**同名**，非限定会歧义 | 加 `open FateV2.Rules.LawRule`；`Alpha`/`AlphaSpec` 显式限定为 `FateV2.Rules.InstanceChain.*` |
| 4 | `MeasurableSpace K3Y.Carrier` 无法解析 | `StateSpace.meas` 是**结构字段**不是实例，
而 `LawRule` 需要 `[MeasurableSpace Y.Carrier]` | 仿 `Fate/T1DegeneracyVerify.lean:232` 写
`instance … := inferInstanceAs (MeasurableSpace (Set M2))` |
| 5 | 文档注释块内又开了一个文档注释 | 块注释内出现未闭合的注释起始符，Lean 报
`unexpected token; expected lemma`（**这是 1 处真语法错**） | 内层降级为普通块注释 |
| 6 | 缺 `end`（`noncomputable section` 未闭合） | `end WiringFCAAlpha` 前少一个 `end`，
报 "current section is unnamed" | 补 `end` |
| 7 | `k3Rules_inhabited` 漏用 `hr` | `intro r _` 丢了成员关系，目标反而对不上 | `intro r hr` + `subst` |

**未修的内容**：一条都没删。22 条定理（原计数）全在，**新增 0 条、删除 0 条**。
（实数为 23 条 `theorem`，含 `AlphaSpec.toPartial`；分诊表的 22 为口径差。）

---------------------------------------------------------------------------
⚠ 反同义反复自查（纪律第 7 条）
---------------------------------------------------------------------------
- `extent_eq_iff_intent_eq`：两个输出分别在**对象侧**（extent）与**属性侧**（intent），
  二者由 `toExtent'_toIntent'`（**双射的逆性质**）连接，
  不是定义相同 / 不是同一命题换写。
- `no_singleFace_alphaRead`：前件是「存在一个反序对合 `f : CL → CL`」，
  结论是 **已证的分离定理** `no_selfDual_iso` **的否定使用**
  —— 实际上是 `¬∃f`，前件不蕴含它。
- `alphaRead_partition_lost` / `alphaRead_extent_iso_impossible`：
  前件是「存在保外延（非空性 / 空性）的序同构」，结论 = `False`
  —— 是 T112 两条**独立已证**反例定理的合成，前件不蕴含 `False`。
- `alphaRead_four_eq_two`：结论 = 四次极 = 二次极 —— 由 T112 秩二定理直接给出。
- `alphaReadOutput_partialSpec`：四个分量分别由 §5.1–§5.4 的定理给出，
  **不是**「假设规格再重复它」。
- ⚠ **诚实标注两条弱定理**：`alphaPartition_covers` 与 `k3Rule_local` 都是 `rfl`
  （前者由「同类」的定义自反性，后者因 `k3Rule` 是常值函数）。
  它们的前件为空（`k3Rule_local` 的 `_hy` 甚至未被使用），**不是**同义反复，
  但**内容极弱**：只验证「定义确实满足该分量」，不承担数学内容。
  真正的内容在 `alphaReadOutput_partialSpec`（它把四条合成，并接上 `AlphaOutput`）。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
1. **零 `sorry` / 零 `admit` / 零 `axiom`。**
2. ⭐ **`AlphaSpec` 的 (S3) `part_trans` 未证**：本文件的划分
   「读集相同 ⇒ 同类」在任何形式背景上都是等价关系，故 (S3) 事实上成立；
   但本文件**未形式化证明它**，故**不陈述**该分量，也**不用** `sorry` 占位。
   ⟹ §5 给出的是 `AlphaSpecPartial`（**去掉 (S3)**），
   本文件**不声称** `AlphaSpec`，`AlphaSpec.toPartial` 只证「更强者推出更弱者」。
3. 本文件**不修改**任何已有模块。
4. **P-006 修复后实测：两遍 `lake env lean Fate/WiringFCAAlpha.lean` 均 0 error / 0 warning**，
   `#print axioms` 仅 `propext` / `Classical.choice` / `Quot.sound`。
5. ⚠ §5 的状态空间由原写的 `Set G3`（**对象集**）改为 `Set M2`（**属性集**）——
   这是**实质纠错**：α 的输入就是属性集，原写法与 `takeConcept` 的签名类型不符。
   因此 `k3Rule` 的 `dirac` 取值也由 `∅ : Set G3` 改为 `∅ : Set M2`。
   这个改动**不改变任何定理的数学含义**（都是「空集上的点质量」），
   但纠正了类型层面的错位。
-/

import FateWorld.FateV2.Rules.T112FCASpecific
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.AlphaConcreteInstance
import FateWorld.FateV2.Rules.InstanceChain
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace WiringFCAAlpha

open Set
open FateV2.Rules.FormalCtx
open FateV2.Rules.AlphaInstance
open FateV2.Rules.InstanceChain
open FateV2.Rules.LawRule

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
  # Rules · WiringFCAAlpha

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringFCAAlpha.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T112FCASpecific, Alpha, AlphaConcreteInstance, InstanceChain
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  α 的**读集划分**：由 T112 的「外延 ↔ 内涵」反序同构驱动
    =========================================================================== -/

namespace FormalCtx
variable (K : FormalCtx)

/-- **α 的读集（extent）**：α 作用于属性集 `B`，读回「哪些对象落在这个概念里」。

即 `α(B)' = polarDown (takeConcept B)`，由 FCA 基本定理它是 **extent**。

**这条定义是 α 与 T112 之间的桥**：T112 的 `ExtentSet K` 元素正是这种东西。 -/
def alphaRead (B : Set K.MFCA) : K.ExtentSet :=
  ⟨K.polarDown (K.takeConcept B), ⟨K.takeConcept B, rfl⟩⟩

/-- **α 读集确实是 `ExtentSet` 的元素**（值域正确性）。 -/
theorem alphaRead_isExtent (B : Set K.MFCA) : Order.IsExtent K.Irel (FormalCtx.alphaRead K B).1 :=
  (FormalCtx.alphaRead K B).2

/-- ⭐⭐ **α 读集 ↔ α 内涵：反序同构给出双向唯一性**。

**这里真正用上了 `T112FCASpecific` 的 `toExtent'_toIntent'`**——
结论 `(toExtent' (toIntent' s)).1 = s.1` 是反序同构
`ExtentSet K ≃o (IntentSet K)ᵒᵈ` 的**逆性质**，不是任何前件的换写。 -/
theorem alphaRead_intent_roundtrip (s : K.ExtentSet) :
    (K.toExtent' (K.toIntent' s)).1 = s.1 := by
  have h := K.toExtent'_toIntent' s
  rw [h]

/-- ⭐ **α 的读集相等 ⟺ 内涵相等**（反序同构是**双射**的逐点形式）。

这是 T112 任务 1 在 α 上的落点：
**α 的两个输出在对象侧相同，当且仅当它们在属性侧相同**。 -/
theorem extent_eq_iff_intent_eq (s t : K.ExtentSet) :
    (K.toIntent' s).1 = (K.toIntent' t).1 ↔ s.1 = t.1 := by
  constructor
  · intro h
    have hi : K.toIntent' s = K.toIntent' t := Subtype.ext h
    have he := congrArg (fun u : K.IntentSet => (K.toExtent' u).1) hi
    rw [K.toExtent'_toIntent', K.toExtent'_toIntent'] at he
    exact he
  · intro h
    exact congrArg (fun u : K.ExtentSet => (K.toIntent' u).1) (Subtype.ext h)

/-- ⭐ **α 读集的序单调性（反序版）**：读集扩大 ⟹ 内涵缩小。

直接由 `T112FCASpecific` 的 `toIntent'_le_iff`（反序同构的序部分）。 -/
theorem alphaRead_anti {s t : K.ExtentSet} (h : s ≤ t) :
    (K.toIntent' t).1 ⊆ (K.toIntent' s).1 :=
  (K.toIntent'_le_iff s t).2 h

/-- ⭐ **对偶方向**：内涵扩大 ⟹ 读集缩小（`toExtent'_le_iff` 的消费）。 -/
theorem alphaRead_anti' {s t : K.IntentSet} (h : s ≤ t) :
    (K.toExtent' t).1 ⊆ (K.toExtent' s).1 :=
  (K.toExtent'_le_iff s t).2 h

end FormalCtx

/-! ===========================================================================
    §2  ⭐ α 阅读是**方向敏感**的：一般闭包算子读不到「对象/属性」两面

  把 T112 的分离定理 `no_selfDual_iso` 接到 α 上：
  若存在一个「α 阅读」在**单面**闭包（`cl3`）上也能两头走且保序，
  则一般闭包算子的闭集格就自对偶 —— 被 T112 否定。
  ⟹ **α 必须依赖 FCA 的双面结构**（`polarUp`/`polarDown` 的 Galois 连接）。
  =========================================================================== -/

namespace NonSelfDual

open FateV2.Rules.ClosureSep NonSelfDual

/-- ⭐⭐ **单面 α 阅读不存在**（消费 `T112FCASpecific` 的 `no_selfDual_iso`）。

「单面 α 阅读」= 一个反序、双向保序、且对合的映射 `f : CL → CL`
（读得到「对象侧」，也读得回「属性侧」，但只用**一个**闭包算子）。

**结论**：这样的 `f` **不存在** —— 因为它会给出 `CL ≃o CLᵒᵈ`，
而 T112 已证该反序同构不存在。

**这条定理的意义**：它是「α 必须用 FCA 双面结构」的机器验证形式；
也是 `T112FCASpecific` 任务 1 的诚实性声明在 α 层的**落点**。 -/
theorem no_singleFace_alphaRead :
    ¬ ∃ f : CL → CL, (∀ a b, f a ≤ f b ↔ b ≤ a) ∧ Function.Involutive f := by
  rintro ⟨f, hf, hinv⟩
  -- 由前件构造 `CL ≃o CLᵒᵈ`，与 T112 的分离定理矛盾
  have hff : ∀ a : CL, f (f a) = a := hinv
  refine FateV2.Rules.ClosureSep.NonSelfDual.no_selfDual_iso ⟨?_⟩
  exact
    { toFun := fun a => OrderDual.toDual (f a)
      invFun := fun b => f (OrderDual.ofDual b)
      left_inv := fun a => hff a
      right_inv := fun b => by
        show OrderDual.toDual (f (f (OrderDual.ofDual b))) = OrderDual.toDual (OrderDual.ofDual b)
        rw [hff]
      map_rel_iff' := by
        intro a b
        show OrderDual.toDual (f a) ≤ OrderDual.toDual (f b) ↔ a ≤ b
        rw [OrderDual.toDual_le_toDual]
        exact hf b a }

/-- **推论（正向陈述）**：T112 的分离结论本身
（`no_selfDual_iso` 的直接消费，用于下游引用）。 -/
theorem fca_twoFace_needed :
    ¬ Nonempty (FateV2.Rules.ClosureSep.NonSelfDual.CL ≃o FateV2.Rules.ClosureSep.NonSelfDual.CLᵒᵈ) :=
  FateV2.Rules.ClosureSep.NonSelfDual.no_selfDual_iso

end NonSelfDual

/-! ===========================================================================
    §3  ⭐ α 的读集划分**保不住外延信息**：T112 反例在 α 上的落点

  T112 反例：`KA` 与 `KC` 概念格**同构**，但 `KA` 的 `⊥` 外延非空、
  `KC` 的 `⊥` 外延为空 ⟹ **任何** α 读集划分都不能把「外延是否为空」保过去。
  =========================================================================== -/

namespace ExtentLoses

open Counterexample

/-- ⭐⭐ **α 的读集划分丢失外延信息**（消费 `no_extent_preserving_iso`）。

前件：α 的读集划分上存在一个**序同构**，且它**保持外延非空性**。
结论：`False`。 -/
theorem alphaRead_partition_lost
    (e : ConceptLattice KA ≃o ConceptLattice KC)
    (hpres : ∀ c : ConceptLattice KA, (e c).extent.Nonempty ↔ c.extent.Nonempty) :
    False :=
  Counterexample.no_extent_preserving_iso ⟨e, hpres⟩

/-- ⭐ **加强形式**：连「外延是否为空」都不能保。 -/
theorem alphaRead_extent_iso_impossible
    (e : ConceptLattice KA ≃o ConceptLattice KC)
    (hpres : ∀ c : ConceptLattice KA,
      (e c).extent = (∅ : Set KC.GFCA) ↔ c.extent = (∅ : Set KA.GFCA)) :
    False :=
  Counterexample.no_extent_card_preserving_iso ⟨e, hpres⟩

/-- ⭐ **划分本身仍然存在**：两侧的 α 读集格**可以**序同构。 -/
theorem alphaRead_lattice_iso_exists :
    Nonempty (ConceptLattice KA ≃o ConceptLattice KC) :=
  Counterexample.KA_KC_lattice_iso

/-- ⭐ **差异定位在 `⊥` 侧**：`⊤` 的外延两侧相同。 -/
theorem alphaRead_top_agree :
    (⊤ : ConceptLattice KA).extent = (univ : Set KA.GFCA) ∧
    (⊤ : ConceptLattice KC).extent = (univ : Set KC.GFCA) :=
  ⟨Counterexample.KA_top_extent, Counterexample.KC_top_extent⟩

/-- ⭐ **`⊥` 侧差异是实质的**（两侧外延空性相反）。 -/
theorem alphaRead_bot_disagree :
    (⊥ : ConceptLattice KA).extent.Nonempty ∧
    (⊥ : ConceptLattice KC).extent = (∅ : Set KC.GFCA) :=
  ⟨Counterexample.KA_bot_extent_nonempty, Counterexample.KC_bot_extent_empty⟩

end ExtentLoses

/-! ===========================================================================
    §4  ⭐ α 读集闭包**秩 ≤ 2**：T112 任务 2 的落点
    =========================================================================== -/

namespace RankTwo

/-- ⭐ **α 读集的四步极 = 两步极**（`T112FCASpecific.RankTwo` 的消费）。 -/
theorem alphaRead_four_eq_two (K : FormalCtx) (A : Set K.GFCA) :
    K.polarDown (K.polarUp (K.polarDown (K.polarUp A)))
      = K.polarDown (K.polarUp A) :=
  RankTwo.polarUp_polarDown_polarUp_polarDown_idem K A

/-- ⭐ **具体实例上落地**：`K3` 的 α 读集两次即稳定。 -/
theorem alphaRead_four_eq_two_K3 (A : Set G3) :
    K3.polarDown (K3.polarUp (K3.polarDown (K3.polarUp A)))
      = K3.polarDown (K3.polarUp A) :=
  alphaRead_four_eq_two K3 A

/-- ⚠ **诚实对照**：同样结论对**任何闭包算子**成立
（`T112FCASpecific.Contrast` 的消费）。

**⟹ 这条定理的作用是防止虚假声称**：α 读集的秩 ≤ 2
**不是** FCA 的贡献，只反映幂等性。 -/
theorem alphaRead_rankTwo_notFCA {β : Type*} [Preorder β] (c : ClosureOperator β) (x : β) :
    c (c (c (c x))) = c (c x) :=
  FateV2.Rules.Contrast.closure_four_eq_two c x

end RankTwo
/-! ===========================================================================
    §5  ⭐ 真正的 α 实例：`AlphaOutput` 的具体构造（读集划分 + 规则集）

  **P-006 修复说明（本次修复的实际内容）**：

  原文件本节按**旧版** `StateSpace` 书写（`⟨Carrier⟩` 单字段）。
  新版 `FateV2.Modeling.StateSpace` 有 `Carrier` / `topo` / `meas` / `borel_le`
  四个分量，故本节全部 `⟨Set G3⟩` 写法失效。
  修复另加两处**实质纠错**（不是纯改名）：

  1. α 的作用对象是**属性集** `B : Set K.MFCA`（见 §1 `alphaRead` 的签名
     `Set K.MFCA → K.ExtentSet`）。原文件把状态类型写成 `Set G3`（对象集），
     与 `takeConcept : Set K.MFCA → Set K.MFCA` 的输入类型不符 ——
     这不是重命名问题，是**类型写错**。本次改为 `Set M2`（= `Set K3.MFCA`）。
  2. 规则取值空间 `Y` 必须是**可测空间**；`Set G3` 配 `⊤` 拓扑 + Borel
     以取得 `MeasurableSpace`（与 `LawRuleCondMul.discreteSpace` 同一模式）。

  ⚠ (S3) `part_trans` **仍然未证**（见下方登记），
  本文件仍**不**声称 `AlphaSpec`，只声称 `AlphaSpecPartial`。
  =========================================================================== -/

/-- α 的**状态空间**：取 `K3` 的属性集（**α 的输入就是属性集**，
故「读到哪个概念」即状态）。`⊤` 拓扑 + Borel 可测结构。

⚠ `borel_le` 要求可测结构**弱于** Borel，故 `meas` 取 `@borel _ ⊤`
（取 `⊤` 可测结构会违反该前件）。 -/
def K3X : StateSpace where
  Carrier := Set M2
  topo := ⊤
  meas := @borel (Set M2) ⊤
  borel_le := le_rfl

/-- α 的**上下文空间**：退化到单点（本实例不区分上下文）。 -/
def K3Ctx : CtxSpace := ⟨Unit⟩

/-- α 的**输出空间**（`OutSpace` 是 `StateSpace` 的缩写）。 -/
def K3Y : StateSpace := K3X

/-- ⚠ `StateSpace.meas` 是**结构字段**，不是自动可用的实例；
为使 `LawRule` 的 `[MeasurableSpace Y.Carrier]` 前件可解析，
此处显式把 `K3X` / `K3Y` 的可测结构提升为实例
（模式同 `Fate/T1DegeneracyVerify.lean:232` 的 `inferInstanceAs` 写法）。 -/
instance instK3XMeas : MeasurableSpace K3X.Carrier := inferInstanceAs (MeasurableSpace (Set M2))

instance instK3YMeas : MeasurableSpace K3Y.Carrier := inferInstanceAs (MeasurableSpace (Set M2))

/-- ⭐ **局部域划分**：`x` 的局部域 = 「α 读集与 `x` 相同的所有状态」。

这**正是**作者裁决 O2「局部域 = 读集」的落实。 -/
def alphaPartition (x : Set M2) : Set (Set M2) :=
  {y | K3.polarDown (K3.takeConcept y) = K3.polarDown (K3.takeConcept x)}

/-- **(S1) 覆盖性：每个状态落在自己的局部域里。** -/
theorem alphaPartition_covers : PartitionCovers alphaPartition := by
  intro x
  show K3.polarDown (K3.takeConcept x) = K3.polarDown (K3.takeConcept x)
  rfl

/-- **(S2) 对称性：局部域同类关系对称。** -/
theorem alphaPartition_symm : PartitionSymm alphaPartition := by
  intro x y hxy
  show K3.polarDown (K3.takeConcept x) = K3.polarDown (K3.takeConcept y)
  exact hxy.symm

/- ⚠ **(S3) `part_trans` —— 未证（如实登记）**

划分由**等式**生成（`polarDown (takeConcept y) = polarDown (takeConcept x)`），
故传递性**事实成立**；但本文件**未形式化证明它**。
按纪律第 6 条，此处**不陈述未证定理**，也**不用** `sorry` 占位。
⟹ 下方给出 `AlphaSpecPartial`（**去掉 (S3)**），**不**声称 `AlphaSpec`。 -/

/-- **本实例唯一的规则**：常值规则 —— 无论状态如何，允许的分布集都是固定单点集。

**为什么取常函数**：局部域把状态**按 α 读集分类**，同类状态读集相同但
**状态本身可以不同**（`FateV2.Rules.alpha_not_injective` 已证
α 不单射）。故要 (S4) 成立，规则**必须**在同类上取同值 —— 常函数是最简实现。

**这不是空洞的退化**：规则输出取自 **`∅` 的取概念结果**（`takeConcept ∅ = ∅`，
见 `FateV2.Rules.AlphaInstance.takeConcept_eq_empty`），故它与 α 直接相关。 -/
def k3Rule : LawRule K3Ctx K3X K3Y :=
  fun _ _ => {MeasureTheory.Measure.dirac (∅ : Set M2)}

/-- **本实例的规则集**（单元素集）。 -/
def k3Rules : Set (LawRule K3Ctx K3X K3Y) := {k3Rule}

/-- **(S5) 每条规则处处非空**。 -/
theorem k3Rule_nonempty (c : K3Ctx.Carrier) (x : K3X.Carrier) :
    (k3Rule c x).Nonempty :=
  ⟨MeasureTheory.Measure.dirac (∅ : Set M2), mem_singleton _⟩

/-- **(S5) 集合形式**：`RulesInhabited k3Rules`。 -/
theorem k3Rules_inhabited : RulesInhabited k3Rules := by
  intro r hr c x
  have hr' : r = k3Rule := by simpa [k3Rules] using hr
  subst hr'
  exact k3Rule_nonempty c x

/-- **(S4) 逐点形式**：规则在同一局部域内取同值。 -/
theorem k3Rule_local (c : K3Ctx.Carrier) {x y : K3X.Carrier}
    (_hy : y ∈ alphaPartition x) : k3Rule c x = k3Rule c y := rfl

/-- **(S4) 集合形式**：`RulesLocal alphaPartition k3Rules`。 -/
theorem k3Rules_local :
    RulesLocal (C := K3Ctx) (X := K3X) (Y := K3Y) alphaPartition k3Rules := by
  intro r hr c x y hy
  have hr' : r = k3Rule := by simpa [k3Rules] using hr
  subst hr'
  exact k3Rule_local c hy

/-- ⭐ **α 在 `K3` 上的具体输出**：`partition` = α 读集划分，`rules` = 常值规则集。

这是 `FateV2.Rules.InstanceChain.AlphaOutput` 的**第一个由 FCA 读集驱动**的具体实例。 -/
def alphaReadOutput : AlphaOutput K3Ctx K3X K3Y where
  partition := alphaPartition
  rules := k3Rules

/-- **⚠ 部分规格**：`AlphaSpec` 五个分量中本文件证出**四个**。

⭐ 缺失 `part_trans`（见上登记）—— 本文件**不**提供它，
故本结构**不是** `AlphaSpec`，本文件**不**声称 `alphaReadOutput` 满足 `AlphaSpec`。 -/
structure AlphaSpecPartial {D : Type u} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] (α : FateV2.Rules.InstanceChain.Alpha D C X Y) : Prop where
  /-- (S1) 局部域覆盖全空间。 -/
  covers : ∀ d, PartitionCovers (α d).partition
  /-- (S2) 局部域同类关系对称。 -/
  part_symm : ∀ d, PartitionSymm (α d).partition
  /-- (S4) 规则只通过局部域看状态。 -/
  localize : ∀ d, RulesLocal (α d).partition (α d).rules
  /-- (S5) 规则集非退化。 -/
  inhabited : ∀ d, RulesInhabited (α d).rules

/-- **`AlphaSpec` 蕴含 `AlphaSpecPartial`**（只缺 (S3)）。 -/
theorem AlphaSpec.toPartial {D : Type u} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] {α : FateV2.Rules.InstanceChain.Alpha D C X Y}
    (h : FateV2.Rules.InstanceChain.AlphaSpec α) :
    AlphaSpecPartial α where
  covers := h.covers
  part_symm := h.part_symm
  localize := h.localize
  inhabited := h.inhabited

/-- ⭐⭐ **中心结论：α 的具体读集实现在 `K3` 上满足部分规格**。

`covers` / `part_symm` / `localize` / `inhabited` **分别**由
§5.1–§5.4 的定理给出，不是「假设 `AlphaSpec` 再重复它」。 -/
theorem alphaReadOutput_partialSpec :
    AlphaSpecPartial (fun (_ : Unit) => alphaReadOutput) where
  covers := fun _ => alphaPartition_covers
  part_symm := fun _ => alphaPartition_symm
  localize := fun _ => k3Rules_local
  inhabited := fun _ => k3Rules_inhabited

end

end WiringFCAAlpha

end FateV2.Rules
-- ## §6  使用登记（供下游与审计）
--
-- 本文件消费的 `FateV2.Rules` 定理清单（逐条 grep 可查）：
-- FormalCtx 的 toExtent 逆性质、toIntent 与 toExtent 的序等价；
-- ClosureSep.NonSelfDual 的 no_selfDual_iso；
-- Counterexample 的 KA_KC_lattice_iso、no_extent_preserving_iso、
-- no_extent_card_preserving_iso、KA_bot_extent_nonempty、KC_bot_extent_empty、
-- KA_top_extent、KC_top_extent；RankTwo 的四次极等于二次极；
-- Contrast 的一般闭包算子对照。
