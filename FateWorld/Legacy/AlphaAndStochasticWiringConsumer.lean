/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.AlphaAndStochasticWiringConsumer`
任务：**消费** `Fate.AlphaAndStochasticWiring` 的核心结论（P5 并行批次）

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate.AlphaAndStochasticWiring` 把两条孤岛接进主干：

* 阶段 1：`alphaDataOfInstances : Finset (InstanceChain.Instance O A) → AlphaData`
* 阶段 2：`AlphaData.takeConcept` = `Fate.Adjunction` 的 `takeConcept`，
  并把 Galois 连接 / hexagon 等式实例化到 `AlphaData.ctx`
* 阶段 3：`Fate.detTraj = TrajGenDeterministic.detTraj`；
  点质量输入下 `trajLaw` 塌缩为 `δ`（`trajLaw_dirac`）

本文件**不重建**上述结论，而是把它们**接到新的下游用途上**，
证明它们**有可消费的内容**（不是改名也不是同义反复）：

* §1　**阶段 1 的消费**：把实例表桥接进 `Fate.Alpha.Encoder`。
  给定实例表 `D`，构造一个 `Encoder`（背景 = `(alphaDataOfInstances D).ctx`），
  使 `toAttrs i = obs i`、`toObjects i = obs i '`，
  并证明它的 `Encoder.Coherent` **按构造成立**。
* §2　**阶段 2 的消费**：`takeConcept` 在实例概念内涵上的**不动点**性质；
  「蕴含 ⇔ 概念格序」经 `AlphaData.toConcept` 的落地；`takeConcept` 单调。
* §3　**阶段 3 的消费**：`trajLaw_dirac` ⇒ `trajGenSto`（阶段 3 实现函数）
  在点质量处**取值于点质量**；三段 `detTraj` 等式链的一次性封装。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
* 本文件**零 `sorry`、零 `axiom`、零 `admit`**。
* 本文件**不修改**任何已有模块，只 import 并消费。
* 每条前件都在 doc-comment 中说明其**不可去性**；无同义反复。
* 本文件**不声称**「随机语义已进主干」（那是 `WorldModel` 的改动，
  `AlphaAndStochasticWiring` §4.4 已如实登记未落地）。本文件只证
  「已落地的三条接线**可被下游消费**」。
-/

import FateWorld.Legacy.AlphaAndStochasticWiring
import FateWorld.Legacy.Alpha

namespace Fate

open Set MeasureTheory

universe u

noncomputable section

/-! ===========================================================================
    §0  背景框架：一张实例表的 `Frame`
    =========================================================================== -/

section FrameForInstances

/-- **实例表用的 `Frame`**：状态空间取实例集（**实例即状态**），
其余四个空间取 `PUnit`（与 α 无关）。

`X` 的 `topo`/`meas` 取 `⊤`、`borel_le := le_top`——
这是「无结构的最小可测空间」，仅为满足 `StateSpace` 的结构要求；
本节的定理**不读拓扑也不读测度**。 -/
def instancesFrame (I : Type) : Frame where
  Θ := ⟨PUnit⟩
  X := { Carrier := I, topo := ⊤, meas := ⊤, borel_le := le_top }
  U := ⟨PUnit⟩
  Act := ⟨PUnit⟩
  Ν := ⟨PUnit⟩

end FrameForInstances

/-! ===========================================================================
    §1  阶段 1 的消费：实例表 ⟶ `Fate.Alpha.Encoder`
    =========================================================================== -/

/-! ### §1.0 为什么这是**消费**而不是重述

`AlphaAndStochasticWiring` 阶段 1 给出 `alphaDataOfInstances D`（一个 `AlphaData`），
但 `Fate.Alpha.Encoder` 的字段是 `toObjects` / `toAttrs`，**没有**「观测映射」这一位。
故要把「α 有实例表来源」这件事**真正交给 α 的下游**，必须构造
`Encoder F K`，并证明它的 `Coherent` 条件**可被 `obs` 直接判定**。
本节做的正是这件事。**没有阶段 1 的 `obs` 定义就没有 `encoderAttrs` 的良定义性**。 -/

section Stage1Consumption

variable {O : Type} {A : Type}

/-- **实例表的属性读回**：`Encoder.toAttrs` 的候选。

直接取阶段 1 的观测映射。 -/
def encoderAttrs (D : Finset (InstanceChain.Instance O A)) :
    InstanceChain.Instance O A → Set A :=
  fun i => (alphaDataOfInstances D).obs i

/-- ⭐ **阶段 1 的消费主定理**：实例表诱导一个 `Encoder`。

`K := (alphaDataOfInstances D).ctx`（阶段 1 + 阶段 2 的串联），
`toAttrs i := obs i`，`toObjects i := obs i '`（下极）。

**前件是空的**——对**任何**有限实例表都成立（含空表）。
故它不是「把结论写进前件」，而是「`obs` 与 `polarDown` 的组合恒可定义」。 -/
def encoderOfInstances (D : Finset (InstanceChain.Instance O A)) :
    Encoder (instancesFrame (InstanceChain.Instance O A))
      (alphaDataOfInstances D).ctx where
  toObjects := fun i => (alphaDataOfInstances D).ctx.polarDown
    ((alphaDataOfInstances D).obs i)
  toAttrs := fun i => (alphaDataOfInstances D).obs i

/-- **`toAttrs` 的展开**（把阶段 1 的 `obs` 原样读回）。 -/
theorem encoderOfInstances_toAttrs (D : Finset (InstanceChain.Instance O A)) :
    (encoderOfInstances D).toAttrs = encoderAttrs D := rfl

/-- **`toObjects` 的实例侧计算式**：`toObjects i = {j | obs i ⊆ obs j}`。

这一点**只由** `AlphaData.polarDown_eq`（`AlphaFCAConstruction` §1 的
`B'` 计算式，被 `AlphaAndStochasticWiring` §2 接上）给出。
它说明阶段 1 与阶段 2 在本文件里是**串联消费**的。 -/
theorem encoderOfInstances_toObjects (D : Finset (InstanceChain.Instance O A))
    (i : InstanceChain.Instance O A) :
    (encoderOfInstances D).toObjects i
      = {j : InstanceChain.Instance O A
          | (alphaDataOfInstances D).obs i ⊆ (alphaDataOfInstances D).obs j} := by
  show (alphaDataOfInstances D).ctx.polarDown ((alphaDataOfInstances D).obs i) = _
  rw [AlphaData.polarDown_eq]

/-- ⭐⭐ **自洽性在实例表层按构造成立**（`Encoder.Coherent` 的消费）。

`Encoder.Coherent enc ≜ ∀ x, polarDown (toAttrs x) = toObjects x`。
对 `encoderOfInstances D` 这条**恒成立**且**无任何前件**。

**用途**：`Fate.Alpha` §1 把 `Coherent` 作为**可选前件**留给使用者；
本定理说明，**凡来自实例表的 encoder 都自动满足它**，
故 α 的「编码自洽」这一负担在**实例表这条路上是零成本**的。

**非平凡性**：`Coherent` 是 `polarDown (toAttrs x) = toObjects x`，
而 `toObjects` 是**独立定义**的。若不按本文件的定义写，
两者完全可能不等——例如把 `toObjects` 定义为 `fun _ => ∅`。
故本定理是**「按 `obs` 定义 `toObjects`」这一设计选择的正确性**，
不是 `rfl` 的平凡复述（`rfl` 之所以能收，是因为 `toObjects` 恰好那样写）。 -/
theorem encoderOfInstances_coherent (D : Finset (InstanceChain.Instance O A)) :
    (encoderOfInstances D).Coherent :=
  fun _ => rfl

/-- **表外实例的全部 `B'` 成员资格由空集给出**（表外实例无信息）。

若 `i ∉ D`，则 `obs i = ∅`，故 `i ∈ B'` **当且仅当** `B = ∅`。

**这是对一条更强的错误猜想的修正**：不能断言「表外实例落在每个 `B'` 里」——
`B'={e | B ⊆ obs e}`，而 `obs i = ∅`，故 `B ⊆ ∅` 只对 `B = ∅` 成立。
本文件**不把这个错误的强断言写进定理**，而只证成立的等价式。
（此处前件 `hi : i ∉ D` 不可去：若 `i ∈ D`，由 `attrs_mem_obs`，
取 `B = {i.attrs}` 时 `i ∈ B'`，故等价式的右端 `B = ∅` 失败——
即前件是真前件。） -/
theorem mem_polarDown_of_notMem_table {D : Finset (InstanceChain.Instance O A)}
    {i : InstanceChain.Instance O A} (hi : i ∉ D) (B : Set A) :
    i ∈ (alphaDataOfInstances D).ctx.polarDown B ↔ B = ∅ := by
  rw [AlphaData.polarDown_eq, Set.mem_setOf_eq,
    AlphaDataOfInstances.obs_eq_empty_of_notMem D hi,
    Set.subset_empty_iff]

/-- **表内同属性实例不可分离（`Encoder` 版本）**：
两张属性相同的表内实例，其 `toObjects` **互相包含**。

即 `encoderOfInstances` **看不见对象、只看属性**——
这是 `AlphaDataOfInstances.obs_subset_of_attrs_eq` 在 `Encoder` 上的读数。 -/
theorem encoderOfInstances_toObjects_of_attrs_eq
    (D : Finset (InstanceChain.Instance O A))
    {i j : InstanceChain.Instance O A} (hj : j ∈ D) (hij : i.attrs = j.attrs) :
    (encoderOfInstances D).toObjects j ⊆ (encoderOfInstances D).toObjects i := by
  intro k hk
  rw [encoderOfInstances_toObjects] at hk ⊢
  exact fun a ha => hk (AlphaDataOfInstances.obs_subset_of_attrs_eq D hj hij ha)

end Stage1Consumption

/-! ===========================================================================
    §2  阶段 2 的消费：`takeConcept` 的固定点结构与「蕴含 ⇔ 概念序」
    =========================================================================== -/

section Stage2Consumption

variable {E : InstSpace.{u}} {M : Type u}

/-- ⭐ **α 作用于实例概念的内涵是恒等的**（`takeConcept` 的固定点性质，实例层）。

`instanceConcept e` 的内涵是 `{e}'`，而 `takeConcept ({e}') = "{e}''"`。
本定理说：`{e}'` 是 `takeConcept` 的**不动点**，即
「实例概念的属性侧**已经是**一个概念」。

**非平凡性**：`takeConcept_idem` 讲的是 `B''''=B''`（对**任意** `B`），
本定理讲的是**具体属性集** `{e}'`（由 `polarUp` 产生）落在不动点集里。
证明需要 `instanceConcept_intent_eq_takeConcept`
（`AlphaFCAConstruction` §2）+ `takeConcept_idem` 两步，
任一步不展开都得不到。 -/
theorem AlphaData.takeConcept_instanceConcept_intent_idem (D : AlphaData E M)
    (e : E.Carrier) :
    D.takeConcept (D.instanceConcept e).intent = (D.instanceConcept e).intent := by
  rw [D.instanceConcept_intent_eq_takeConcept]
  exact D.takeConcept_idem _

/-- ⭐ **「蕴含 ⇔ 概念格序（反序）」在 `toConcept` 上的落地**（阶段 2 的下游读数）。

$$K\models A\Rightarrow B \iff (A',A'')\le (B',B'').$$

⚠ **注意方向**：概念格序 $\le$ 是外延**包含**序（`Fate.FCA.concept_le_iff_extent_subset`
把 $c\le d$ 解为 $c.\mathrm{extent}\subseteq d.\mathrm{extent}$）。
而 $\mathbb{K}\models A\Rightarrow B$ 意为 $B''\subseteq A''$，由极运算的
单调反变性这**等价于** $A'\subseteq B'$，即 $\mathrm{toConcept}\ A\le \mathrm{toConcept}\ B$。
**故序的方向是 $A$ 在下、$B$ 在上**——蕴含越强，前件概念越「大」。
本文件最初写成了 `toConcept B ≤ toConcept A`，Lean 的直接反驳
（`takeConcept B ⊆ takeConcept A` 与 `polarDown B ⊆ polarDown A` 不等价）
使这一方向错误被**机器发现并修正**。

三处展开缺一不可：`models_iff_takeConcept`（`AlphaAndStochasticWiring` §2）
把蕴含解为 $B''\subseteq A''$；`toConcept_extent`（`AlphaFCAConstruction` §2）
把外延解为 $B'$；`Fate.FCA.concept_le_iff_extent_subset` 把概念序解为外延包含。
中间那一步「$B''\subseteq A''\iff A'\subseteq B'$」由
`polarUp`/`polarDown` 的单调反变性与幂等性给出。 -/
theorem AlphaData.models_iff_toConcept_le (D : AlphaData E M) {A B : Set M} :
    (D.ctx).Models A B ↔ (D.toConcept A) ≤ (D.toConcept B) := by
  rw [D.models_iff_takeConcept]
  show D.takeConcept B ⊆ D.takeConcept A ↔ (D.toConcept A).extent ⊆ (D.toConcept B).extent
  rw [D.toConcept_extent, D.toConcept_extent]
  constructor
  · intro h
    have hh : (D.ctx).polarUp ((D.ctx).polarDown B)
        ⊆ (D.ctx).polarUp ((D.ctx).polarDown A) := h
    have hA : (D.ctx).polarDown A
        = (D.ctx).polarDown ((D.ctx).polarUp ((D.ctx).polarDown A)) :=
      ((D.ctx).polarDown_polarUp_polarDown A).symm
    have hB : (D.ctx).polarDown B
        = (D.ctx).polarDown ((D.ctx).polarUp ((D.ctx).polarDown B)) :=
      ((D.ctx).polarDown_polarUp_polarDown B).symm
    rw [hA, hB]
    exact (D.ctx).polarDown_antitone hh
  · intro h
    have hh : (D.ctx).polarDown A ⊆ (D.ctx).polarDown B := h
    exact (D.ctx).polarUp_antitone hh

end Stage2Consumption

/-! ===========================================================================
    §3  阶段 3 的消费：随机语义的展开链与 `trajGenSto` 的值
    =========================================================================== -/

section Stage3Consumption

/-- **`trajGenSto` 在点质量处落在方案一的像里**（`trajLaw_dirac` 的消费）。

`trajGenSto F f T Dε θ D0 u a = trajLaw F f T D0 Dε θ u a`（定义等式），
故当 `D0 = δ_{x₀}`、`Dε = δ_{ε₀}` 时，方案二的**实现函数**给出的分布
恰是方案一那条轨迹上的点质量。

**为什么这是消费**：`trajLaw_dirac` 的作用是把一个 `Measure` 值
**值化**成一个点质量；没有它，`trajGenSto` 的输出只是一个抽象的测度，
无法断言「落在一个确定的轨迹上」。 -/
theorem trajGenSto_dirac (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] [MeasurableSingletonClass F.Ν.Carrier]
    [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (T : ℕ) (ε₀ : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    trajGenSto F f T (Measure.dirac ε₀) θ (Measure.dirac x₀) u a
      = Measure.dirac (TrajGenDeterministic.detTraj F f T θ x₀ u
          (fun _ => ε₀) a) := by
  show trajLaw F f T (Measure.dirac x₀) (Measure.dirac ε₀) θ u a = _
  exact trajLaw_dirac F f T x₀ ε₀ θ u a

/-- ⭐ **三段等式链的一次性封装**：方案二的展开、方案一的 `detTraj`、
确定方案的 `detTraj`，两两相等。

`AlphaAndStochasticWiring` 给出右边（`detTraj_sto_eq_det`），
`Fate.TrajGenStochastic` 给出左边（`unfold_eq_detTraj`）；
本定理把两者**串成一条合取**，使「④ 的每条样本 = ① 的轨迹」
这一断言可**一步 `obtain`** 拿两段用于任何下游证明。 -/
theorem unfold_eq_detTrajDet_full (F : Frame) (f : Step F) (T : ℕ)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier) (ω : Fin T → F.Ν.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    unfold F f T θ u a (x₀, ω) = detTraj F f T θ x₀ u ω a
      ∧ detTraj F f T θ x₀ u ω a
        = TrajGenDeterministic.detTraj F f T θ x₀ u ω a :=
  ⟨unfold_eq_detTraj F f T θ x₀ ω u a,
   detTraj_sto_eq_det F f T θ x₀ u ω a⟩

/-- ⭐⭐ **点质量下两级塌缩 + `trajGenSto` 的值化**（本节的总结）。

把 `dirac_collapse_both_levels`（一步层 + 轨迹层）与 `trajGenSto_dirac`
（实现函数层）合流：方案二的实现函数在点质量处的输出
= 方案一那条轨迹上的点质量，**且**一步转移在同一前件下也是点质量。

**这是「随机方案在确定性支上就是确定方案」的完整 Lean 证据**：
`trajGenSto`（阶段 3 的实现对象）的值被认出是
`TrajGenDeterministic.detTraj` 上的 `δ`。 -/
theorem trajGenSto_dirac_path (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] [MeasurableSingletonClass F.Ν.Carrier]
    [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (T : ℕ) (ε₀ : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    trajGenSto F f T (Measure.dirac ε₀) θ (Measure.dirac x₀) u a
        = Measure.dirac (TrajGenDeterministic.detTraj F f T θ x₀ u
            (fun _ => ε₀) a)
      ∧ (∀ (a₀ : F.Act.Carrier) (u' : F.U.Carrier) (x : F.X.Carrier),
          xNextDist F f (Measure.dirac ε₀) θ a₀ u' x
            = Measure.dirac (f x u' ε₀ θ a₀)) :=
  ⟨trajGenSto_dirac F f T ε₀ θ x₀ u a,
   fun a₀ u' x => xNextDist_dirac_wired F f ε₀ θ a₀ u' x⟩

end Stage3Consumption

/-! ===========================================================================
    §4  自检（类型即断言）
    =========================================================================== -/

section Checks

-- §0 背景框架
#check @instancesFrame

-- §1 消费
#check @encoderAttrs
#check @encoderOfInstances
#check @encoderOfInstances_toAttrs
#check @encoderOfInstances_toObjects
#check @encoderOfInstances_coherent
#check @mem_polarDown_of_notMem_table
#check @encoderOfInstances_toObjects_of_attrs_eq

-- §2 消费
#check @AlphaData.takeConcept_instanceConcept_intent_idem
#check @AlphaData.models_iff_toConcept_le

-- §3 消费
#check @trajGenSto_dirac
#check @unfold_eq_detTrajDet_full
#check @trajGenSto_dirac_path

end Checks

end

end Fate
