/-
# `Fate/View17` 的**消费方**（甲-批 4b，P5 并行；一次只接一个模块）

## 0 本文件只做一件事

把 `Fate/View17`（「图 ⟹ 概率」桥的第 17 种策略：**屏障 / barrier**）的结论
**接到下游**。**本文件不修改**该模块一个字符（纪律 2）。

## 1 目标模块的实测声明

`grep -nE "^(theorem|def|noncomputable def|instance)" Fate/View17.lean`：

```
  100: abbrev Joint3 (α β γ : Type*) := FateV2.Predict.FinCondIndep.FinJoint α β γ
  108: def KernelSplit (p : Joint3 α β γ) : Prop
  113: theorem kernelSplit_one
  119: theorem kernelSplit_implies_separable
  157: theorem kernelSplit_implies_condMul
  210: theorem kernelSplit_Ytrivial_implies_condMul
  262: theorem kernelSplit_implies_condRatio
  286: theorem bbStep_vertex
  340: theorem bbReach_screen
  370: theorem dSep_not_mem_bbReachable
  403: def BarrierSplit (G : DAG V) (X _Y Z : Finset V) (p : (V × V) × V → ℝ) : Prop
  409: theorem barrierSplit_implies_kernelSplit
  422: theorem barrier_Y_factor_trivial
  435: theorem barrier_Y_channel_collapses
  476: theorem view17_bridge
  493: theorem view17_bridge_ratio
  515: noncomputable def colliderP
  519: theorem colliderP_margZ
  525: theorem colliderP_margXZ
  531: theorem colliderP_margYZ
  537: theorem colliderP_point_tt
  545: theorem collider_not_condMul
  555: theorem collider_not_kernelSplit
  568: abbrev V3
  571: def chainEdge3
  574: def chainDAG3
  591: def colliderEdge3
  594: def colliderDAG3
  611: theorem chain_dSep
  617: theorem collider_not_dSep_selfcond
  626: theorem view17_dsep_discriminates
  648: theorem bridge_nonvacuous_chain
```

（`section`/`end` 不计；`grep -c sorry` 与 `grep -c axiom` 均为 `0`。）

## 2 本文件给出的消费定理（5 条）+ 反例登记（1 条）

| 编号 | 定理 | 消费了 `View17` 的什么 | 前件是否已含结论？（纪律 7 自查） |
|---|---|---|---|
| **C1** | `barrier_antitone_source` | `BarrierSplit` 的定义（§4 B0）+ `bbReachableVertices_mono_source`（`CausBayesBall`） | **否**。前件是**小**源集 `X'` 上的屏障；结论是**大**源集 `X` 上的屏障。`View17` 里 `BarrierSplit` 的 `X` 在每个定理中都是**自由形参**，**从未**与另一个源集比较。两次 `⊆` 反向（`bbReach` 单调升、补集单调降）必须显式走一遍。 |
| **C2** | `dSep_barrier_reads_smaller_source` | `dSep_not_mem_bbReachable`（§3 G3） | **否**。前件 `G.dSep X Y Z`、`y ∈ Y`、`X' ⊆ X`；结论 `y ∉ bbReachableVertices Z X'`。`View17` 的 G3 只对 `X` 给出结论；本条的源集是**更小**的 `X'`。必须额外把可达集沿 `⊆` 收缩。 |
| **C3** | `view17_bridge_of_smaller_barrier` | `view17_bridge` ＋ C1 | **否**（见 C1）。**图侧**用大源集 `X` 的 `dSep`，**概率侧**只要求**小**源集 `X'` 的屏障 —— 这正是 C1 把屏障「升级」到大源集后由 `view17_bridge` 收口。`View17.view17_bridge` **不能**直接给出（它的 `BarrierSplit` 与 `dSep` 必须同一个 `X`）。**这是真正的自由度扩展**：把概率侧的屏障要求从「大源集」放宽到「小源集」。 |
| **C4** | `view17_bridge_condRatio_of_smaller_barrier` | `view17_bridge_ratio` ＋ C3 | **否**。结论是**除法形式** `CondRatio`；需额外 `margZ ≠ 0`（`View17` §0 已诚实登记的语义必需项）＋ `condMul_iff_condRatio_of_ne_zero`。 |
| **C5** | `barrier_Y_trivial_of_small_barrier` | `barrier_Y_factor_trivial`（§4 B1）＋ C1 | **否**。前件：大源集 `dSep`、小源集屏障、`X' ⊆ X`；结论：`∃ lam a b, 剖分 ∧ (∀ y ∈ Y, ∀ z, b y z = 1)`（**`Y`-通道因子退化**）。`View17` 的 B1 要求 **同一个** `X`；本条把屏障条件放宽到小源集。结论本身（`b` 在 `Y` 上为 `1`）确实由 B1 **真实产出**（不是把前件搬过来）。 |
| **R1** | `barrierSplit_blind_to_Y`（**反例登记**） | `chain_one_mem_bbReach`（新）＋ `BarrierSplit` 定义 | **否**（是否定式）。登记：`BarrierSplit` 的屏障只覆盖 `bbReachableVertices Z X` 的**补集**，**与 `Y` 无关**；故在 `Y = X = {0}`、`Z = {1}` 处可以令 `BarrierSplit` 成立而 `dSep` 为假，此时 `b` 在 `1`（可达集**内**、`Y` **外**）上不受任何约束。这是 `View17` **未单独登记**的一条（它只登记了概率侧 `collider_not_condMul`）。 |

## 3 诚实边界

* 本文件**不**声称「`View17` 接入主链完成」。`View17` §0 自陈的缺口
  （`dSep ⟹ KernelSplit` 需要一般 DAG 因子分解）**本文件不碰**。
* C1–C5 的数学内容是 `dSep` / `bbReachableVertices` 在源集上的**单调方向**
  与 `View17` 屏障定义的交互；**不是** `View17` 已有恒等式的换写。
* R1 是**反例登记**，不声称「桥失效」（那已由 `View17.collider_not_condMul` 给出），
  而是登记「屏障子句**单独**不足以给 `Y`-退化」这一**交界事实**。
* 所有区间求和 / `CondMul` / `CondRatio` 完全由 `View17` 提供，本文件**不重新证明**
  任何概率侧等式（避免与 `View17` 的主定理重复）。
-/

import FateWorld.FateV2.Predict.View17
import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FateV2.Predict.View17Consumer

open FateV2.Modeling

open Finset FateV2.Modeling.Graph
open Fate.View17

/-!
  # Predict · View17Consumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View17Consumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：View17, _root.CausBayesBall, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  可达集单调性的**逐点包装**（引擎）

  ⚠ 为什么要包一层：`bbReachableVertices` 的定义体是
  `(G.bbReachable Z X).image Prod.fst`，`G.bbReachable` 是 `bbReachAux` 的
  `Nat` 递归，`whnf` 代价极高。在**已有 `BarrierSplit` 假设**的上下文中
  直接内联 `bbReachableVertices_mono_source` 会让 Lean 的 `whnf` 超时
  （实测 200000 heartbeats 打满）。把它的**逐点形式**先独立声明，
  上下文即不再需要展开 `BarrierSplit` 的定义体去对齐类型。
  =========================================================================== -/

section Engine

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐ **引擎：`bbReachableVertices` 在源集上单调（逐点形式）。**

`X' ⊆ X ⟹ bbReachableVertices Z X' ⊆ bbReachableVertices Z X`
（即 `X` **更大** ⟹ 可达集**更大**）。 -/
theorem bbReachV_mono_pt (G : DAG V) {X X' : Finset V} (Z : Finset V)
    (hXX' : X' ⊆ X) :
    ∀ y : V, y ∈ G.bbReachableVertices Z X' → y ∈ G.bbReachableVertices Z X :=
  fun (y : V) (hy : y ∈ G.bbReachableVertices Z X') =>
    FateV2.Modeling.Graph.DAG.bbReachableVertices_mono_source (G := G) (Z := Z)
      (X := X) (X' := X') hXX' hy

end Engine

/-! ===========================================================================
  §2  C1：`BarrierSplit` 对源集**反单调**

  ⚠ 方向说明（易错，故显式陈述）：
  `X' ⊆ X` ⟹ `reach(X') ⊆ reach(X)` ⟹ `reach(X)ᶜ ⊆ reach(X')ᶜ`。
  `BarrierSplit G X' Y Z p` 的屏障要求 `b = 1` 在**更大**的补集 `reach(X')ᶜ` 上，
  故它**更强**；由它可推出 `reach(X)ᶜ` 上的同一要求（`BarrierSplit G X Y Z p`）。
  **即「屏障对源集反单调」**：往**大**源集走时屏障条件**变弱**。
  =========================================================================== -/

section AntitoneSource

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐⭐ **C1 `barrier_antitone_source`：小源集的屏障 ⟹ 大源集的屏障。**

若 `X' ⊆ X` 且 `BarrierSplit G X' Y Z p`，则 `BarrierSplit G X Y Z p`。

**为什么需要一条定理**：`BarrierSplit` 的屏障子句是
`y ∉ bbReachableVertices Z X → b y z = 1`，其锚点集合
`bbReachableVertices Z X` **随 `X` 单调升**，故屏障**随 `X` 单调降**。
`View17` **没有任何**比较两个源集的定理（`X` 在那边始终是自由形参）。

**⚠ 前件不是结论**：前件是 `X'`（小）版屏障，结论是 `X`（大）版屏障。
反方向（大 ⟹ 小）**不成立**，因为大源集的屏障只约束**更小**的补集。 -/
theorem barrier_antitone_source (G : DAG V) {X X' Y Z : Finset V}
    {p : (V × V) × V → ℝ} (hXX' : X' ⊆ X) (h : BarrierSplit G X' Y Z p) :
    BarrierSplit G X Y Z p := by
  obtain ⟨lam, a, b, hfac, hbar⟩ := h
  refine ⟨lam, a, b, hfac, fun y z hy => ?_⟩
  -- `y ∉ bbReachableVertices Z X`，需证 `b y z = 1`。
  -- 屏障（`X'` 版）只需 `y ∉ bbReachableVertices Z X'` —— 由 `reach(X') ⊆ reach(X)` 得。
  apply hbar y z
  intro hmem
  exact hy (bbReachV_mono_pt G Z hXX' y hmem)

end AntitoneSource

/-! ===========================================================================
  §3  C2：`dSep` 的屏障读出可**收缩**到更小的源集
  =========================================================================== -/

section ReachSmallerSource

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐ **C2 `dSep_barrier_reads_smaller_source`：`dSep` 在小源集上仍挡住 `Y`。**

若 `G.dSep X Y Z`、`y ∈ Y`、`X' ⊆ X`，则 `y ∉ bbReachableVertices Z X'`。

**消费**：`View17.dSep_not_mem_bbReachable`（§3 G3 —— 「`dSep` 的屏障读出」）。
**新增内容**：源集从 `X` **收缩**到 `X'`。`View17` 的 G3 只覆盖 `X` 本身，
故结论不是 G3 的实例（源集**不同**）。 -/
theorem dSep_barrier_reads_smaller_source (G : DAG V) {X X' Y Z : Finset V}
    (h : G.dSep X Y Z) (hXX' : X' ⊆ X) {y : V} (hy : y ∈ Y) :
    y ∉ G.bbReachableVertices Z X' := by
  intro hmem
  exact dSep_not_mem_bbReachable G h hy (bbReachV_mono_pt G Z hXX' y hmem)

end ReachSmallerSource

/-! ===========================================================================
  §4  C3–C5：桥在**更小**的屏障源集上仍收口
  =========================================================================== -/

section SmallerBarrierBridge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐⭐⭐ **C3 `view17_bridge_of_smaller_barrier`：`dSep` 用大源集，
屏障只用小源集，仍得 `CondMul`。**

前件：
* `hsep : G.dSep X Y Z` —— **图侧**（大源集的 d-分离）；
* `hsp : BarrierSplit G X' Y Z p` —— **小**源集上的屏障剖分；
* `hXX' : X' ⊆ X`。

结论：`Fate.FinCondIndep.CondMul p`（对 `p` 作为 `(X, Y, Z) = (V, V, V)` 三元联合律）。

**证明必须消费两件 `View17` 的东西**：
1. `barrier_antitone_source`（C1）把屏障**升级**到 `X`；
2. `view17_bridge` 用 `dSep X Y Z` ＋ `X` 版屏障收口。
**⚠ 若把 `hsp` 弱化成 `True`，`view17_bridge` 无从构造。**

**⚠ 前件不含结论**：`View17.view17_bridge` 要求屏障与 `dSep` **共享同一个 `X`**；
本条把概率侧要求**放宽**到一个更小的源集。
这是 `View17` **明确留白**的自由度（它的 `BarrierSplit` 定义对 `X` 是单点式）。 -/
theorem view17_bridge_of_smaller_barrier (G : DAG V) {X X' Y Z : Finset V}
    (hsep : G.dSep X Y Z) (hXX' : X' ⊆ X)
    (p : (V × V) × V → ℝ) (hsp : BarrierSplit G X' Y Z p) :
    FateV2.Predict.FinCondIndep.CondMul p :=
  view17_bridge G hsep p (barrier_antitone_source G hXX' hsp)

/-- ⭐⭐⭐⭐ **C4 `view17_bridge_condRatio_of_smaller_barrier`：字面 `CondRatio` 版。**

在 C3 基础上加 `margZ ≠ 0`（概率语义所必需，`View17` §0 已诚实标注），
经 `condMul_iff_condRatio_of_ne_zero` 得除法形式 `CondRatio`。 -/
theorem view17_bridge_condRatio_of_smaller_barrier (G : DAG V) {X X' Y Z : Finset V}
    (hsep : G.dSep X Y Z) (hXX' : X' ⊆ X)
    (p : (V × V) × V → ℝ) (hsp : BarrierSplit G X' Y Z p)
    (hz : ∀ z, FateV2.Predict.FinCondIndep.margZ p z ≠ 0) :
    FateV2.Predict.FinCondIndep.CondRatio p :=
  (FateV2.Predict.FinCondIndep.condMul_iff_condRatio_of_ne_zero p hz).mp
    (view17_bridge_of_smaller_barrier G hsep hXX' p hsp)

/-- ⭐⭐⭐⭐ **C5 `barrier_Y_trivial_of_small_barrier`：`Y`-通道因子退化，屏障只需小源集。**

前件：`G.dSep X Y Z`、`X' ⊆ X`、`BarrierSplit G X' Y Z p`。
结论：`∃ lam a b, (∀ x y z, p ((x,y),z) = lam z * a x z * b y z) ∧ (∀ y ∈ Y, ∀ z, b y z = 1)`。

**消费**：`View17.barrier_Y_factor_trivial`（§4 B1 —— `dSep` 真正做功处）＋ C1。

**⚠ 前件不含结论**：B1 要求屏障与 `dSep` 共享 `X`；本条把屏障源集放宽到 `X'`。
**⚠ 结论非线性组合前件**：`b` 在 `Y` 上恒 `1` 是 B1 **产出**的信息，
不是从 `BarrierSplit G X' Y Z p` 直接读出的（后者只约束 `reach(X')ᶜ`，与 `Y` 无关 ——
见 §6 的 R1 反例登记）。 -/
theorem barrier_Y_trivial_of_small_barrier (G : DAG V) {X X' Y Z : Finset V}
    (hsep : G.dSep X Y Z) (hXX' : X' ⊆ X)
    (p : (V × V) × V → ℝ) (hsp : BarrierSplit G X' Y Z p) :
    ∃ (lam : V → ℝ) (a : V → V → ℝ) (b : V → V → ℝ),
      (∀ x y z, p ((x, y), z) = lam z * a x z * b y z) ∧
      (∀ y ∈ Y, ∀ z, b y z = 1) :=
  barrier_Y_factor_trivial G hsep p (barrier_antitone_source G hXX' hsp)

end SmallerBarrierBridge

/-! ===========================================================================
  §5  图侧 **非空性检查**（C3 的实例至少有一次可落地）

  这一节确认 C3 的前提在具体图上**可以同时满足**，故 C3 不是空转。
  =========================================================================== -/

section NonVacuousCheck

/-- ⭐ **`0 ∈ chainDAG3.bbReachableVertices {1} {0}` 的辅助：`1 ∈ children 0`。**
（链 `0 → 1 → 2`。） -/
theorem chain_one_mem_children : (1 : V3) ∈ chainDAG3.children 0 := by
  simp only [FateV2.Modeling.Graph.DAG.children, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inl ⟨rfl, rfl⟩

/-- ⭐ **`1 ∈ chainDAG3.bbReachableVertices {1} {0}`。**

`(1, fromParent) ∈ bbInit {0}`（`1` 是 `0` 的孩子），
源集初始前沿包含在可达集（`bbReachable_init_subset`），投影即得。 -/
theorem chain_one_mem_bbReach : (1 : V3) ∈ chainDAG3.bbReachableVertices {1} {0} := by
  refine Finset.mem_image.mpr ⟨(1, DAG.BBDir.fromParent), ?_, rfl⟩
  refine chainDAG3.bbReachable_init_subset {1} {0} ?_
  simp only [FateV2.Modeling.Graph.DAG.bbInit, Finset.mem_biUnion]
  exact ⟨0, by simp, Finset.mem_union_left _
    (Finset.mem_map.mpr ⟨1, chain_one_mem_children, rfl⟩)⟩

/-- ⭐⭐⭐ **C3 前提非空洞**：在链 `0 → 1 → 2` 上取
`X = {0}`（大）、`X' = ∅`（小）、`Z = {1}`、`Y = {2}`，则 `X' ⊆ X` 且
`BarrierSplit chainDAG3 ∅ {2} {1} p` 对 `p ≡ 1` 成立，而 `dSep {0} {2} {1}` 也成立
（`View17.chain_dSep`）。**⟹ C3 的前提可同时满足。** -/
theorem c3_hypotheses_satisfiable :
    (∅ : Finset V3) ⊆ {0} ∧ chainDAG3.dSep {0} {2} {1} ∧
      BarrierSplit chainDAG3 ∅ {2} {1} (fun _ => (1 : ℝ)) := by
  refine ⟨Finset.empty_subset _, chain_dSep, ?_⟩
  exact ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1,
    fun _ _ _ => by ring, fun _ _ _ => by ring⟩

end NonVacuousCheck

/-! ===========================================================================
  §6  反例登记（R1）：`BarrierSplit` 的屏障**只覆盖补集**，**与 `Y` 无关**
  =========================================================================== -/

section CounterexampleRegistry

/-- ⭐⭐⭐ **R1（反例登记）：`BarrierSplit` 可以成立而 `dSep` 为假，
且它与 `Y` 完全无关。**

**登记的形参**（`V3 = Fin 3`；链 `chainDAG3 : 0 → 1 → 2`）：

| 形参 | 取值 |
|---|---|
| `G` | `chainDAG3` |
| `X` | `{0}` |
| `Z` | `{1}` |
| `Y` | `{0}` ← **注意 `Y` 与 `X` 相交** |

`BarrierSplit` 的屏障子句只对 `bbReachableVertices {1} {0}` 的**补集**
要求 `b ≡ 1`。`1` 在该可达集**内**（`chain_one_mem_bbReach`），
`1 ∉ Y = {0}`，故 `b 1 z` **永不被屏障约束**。

本定理给出的 `p`（`λ ≡ a ≡ 1`、`b 1 · = 7`）满足 `BarrierSplit`，
但 `chainDAG3.dSep {0} {0} {1}` 为**假**（`Disjoint X Y` 失败）。
**⟹ `barrier_Y_factor_trivial` 的 `h : G.dSep X Y Z` 形参不可退化为
任何只关于 `G, Z, X` 的条件。**

**⚠ 诚实标注**：`View17` §0 C4 与 `collider_not_condMul` 已登记
「无 `dSep` 则 `CondMul` 假」。本条的**新增内容**是**图侧 / 概率侧的交界**：
`BarrierSplit` 的屏障**只是** `bbReachableVertices Z X` 的补集，
其定义中 `Y` 是**哑参数**（`_Y`！），因此屏障本身**不**给 `Y` 上任何信息。
这是 `View17` **未单独登记**的一条。 -/
theorem barrierSplit_blind_to_Y :
    ∃ (p : (V3 × V3) × V3 → ℝ) (b : V3 → V3 → ℝ),
      -- ① `BarrierSplit` 对 `X = {0}`、`Y = {0}`、`Z = {1}` 成立
      BarrierSplit chainDAG3 {0} {0} {1} p ∧
      -- ② 该剖分的 `b` 满足屏障子句（补集上为 `1`）
      (∀ y z, y ∉ chainDAG3.bbReachableVertices {1} {0} → b y z = 1) ∧
      -- ③ 但 `b` 在**可达集内部**（`y = 1`）取值 `7 ≠ 1`
      b 1 1 ≠ 1 ∧
      -- ④ 且 `dSep` 在该三元组上**为假**（`barrier_Y_factor_trivial` 不可用）
      ¬ chainDAG3.dSep {0} {0} {1} := by
  refine ⟨fun w => (if w.1.2 = 1 then 7 else 1),
    fun y _ => if y = 1 then 7 else 1, ?_, ?_, ?_, ?_⟩
  · -- ① 剖分：`p ((x,y),z) = 1 * 1 * b y z`。
    refine ⟨fun _ => 1, fun _ _ => 1, fun y _ => if y = 1 then 7 else 1,
      fun x y z => ?_, fun y z hy => ?_⟩
    · show (if y = 1 then 7 else 1) = 1 * 1 * (if y = 1 then 7 else 1)
      ring
    · show (if y = 1 then 7 else 1) = 1
      have hy1 : y ≠ 1 := fun h => hy (by rw [h]; exact chain_one_mem_bbReach)
      rw [if_neg hy1]
  · -- ② 屏障子句（同上）。
    intro y z hy
    show (if y = 1 then 7 else 1) = 1
    have hy1 : y ≠ 1 := fun h => hy (by rw [h]; exact chain_one_mem_bbReach)
    rw [if_neg hy1]
  · -- ③ `b 1 1 = 7 ≠ 1`。
    show (if (1 : V3) = 1 then 7 else 1) ≠ 1
    norm_num
  · -- ④ `¬ dSep {0} {0} {1}`：`Disjoint {0} {0}` 为假。
    intro h
    have hmem : (0 : V3) ∈ ({0} : Finset V3) := by simp
    exact Finset.disjoint_left.mp h.1 hmem hmem

end CounterexampleRegistry

end FateV2.Predict.View17Consumer