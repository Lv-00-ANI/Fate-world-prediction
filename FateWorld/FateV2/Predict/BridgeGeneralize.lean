import FateWorld.FateV2.Predict.SplitFromDAG
import FateWorld.FateV2.Predict.BridgeIntegrated
import FateWorld.FateV2.Predict.ThreeNodeFactorizes
/-!
  # Predict · BridgeGeneralize

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeGeneralize.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SplitFromDAG, BridgeIntegrated, ThreeNodeFactorizes
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeGeneralize` —— **任务 B：因果缺口从 3 节点推广到一般 DAG**

  ## 0 任务与结论一览

  | # | 名称 | 陈述 | 状态 |
  |---|---|---|---|
  | **B1.0** | `FrozenOn` | 「`f` 只读 `S` 上坐标」的谓词 | 定义 |
  | **B1.1** | `frozen_mono` | `S ⊆ T` 且 `f` 冻结于 `S` ⟹ 冻结于 `T` | ✅ |
  | **B2.1** | `factorizes_split_twoBlock` | ⭐⭐ **一般引擎**：`Factorizes p G` + `Split R X Y Z` ⟹ **两块可分离形式** `p = f·g`，`f` 只读 `X∪Z`、`g` 只读 `Y∪Z` | ✅ |
  | **B2.2** | `dSep_forces_split` | ⭐⭐ `dSep X Y Z` + 覆盖 ⟹ `Split R X Y Z`（**真消费 `dSep`**，经 `SplitFromDAG.split_of_dSep`） | ✅ |
  | **B3.1** | `dSep_factorizes_separable_general` | ⭐⭐⭐ **主定理（一般 DAG）**：`dSep` + `Factorizes` + 覆盖 ⟹ 两块可分离 | ✅ |
  | **B3.2** | `condIndep_of_factorizes_dSep_generalZ` | ⭐⭐⭐ **一般 `Z` 全链**：`Factorizes` + `dSep X Y Z` + 覆盖 ⟹ `CondIndep p X Y Z` | ✅ |
  | **B4.1** | `threeNode_condMul_of_general` | ⭐⭐⭐ **回代**：把 B3.1 在 `Fin 3`、`X={0},Y={2},Z={1}` 上落地，得 `CondMul (jointXZ p)` ——**即 `BridgeThreeNode` 主定理由一般引擎重新导出** | ✅ |
  | **B4.2** | `chain_dSep_split` | 链图上主定理的 `Split` 前件确实可满足（非空洞性） | ✅ |
  | **B5.1** | `collider_not_dSep_general` | 撞子图在一般口径下**不**满足 `dSep {0}{2}{1}`（与 `BridgeThreeNode` C1.5 同一命题） | ✅ |
  | **B5.2** | `collider_not_split_general` | 撞子图上 `Split` **也**不成立 ⟹ B3.1 的链条在撞子处确实断开 | ✅ |

  （另有两个辅助引理：`frozen01` / `frozen12`，把 `FrozenOn {0,1}` / `{1,2}`
  翻译成向量形式 `![x,z,y] = ![x,z,d]` / `![d,z,y]`，与 `BridgeThreeNode.reads01` /
  `reads12` 同一命题。）

  **零 `sorry` / `admit` / `axiom`。不修改任何既有模块。**

  ---

  ## 1 三节点证明（`Fate/BridgeThreeNode.lean`）到底用了什么

  `BridgeThreeNode.factorizes_condMul_of_dSep` 的证明分三段：

  ```
  dSep {0}{2}{1}  ──C1.2──▶  ∀ v, pa v ⊆ {0,1} ∨ pa v ⊆ {1,2}
                  ──C1.1──▶  ∃ f g, jointXZ p = f·g（f 只读 x₀x₁，g 只读 x₁x₂）
                  ──代数─▶  CondMul
  ```

  逐条剥出**真正的性质**：

  * **(P1) 「因子不横跨 `X` 与 `Y`」**。C1.2 的结论
    `pa v ⊆ {0,1} ∨ pa v ⊆ {1,2}`，在**读集**口径下就是
    `{v} ∪ pa v ⊆ {0,1} ∪ {1} ∨ {v} ∪ pa v ⊆ {2,1} ∪ {1}`
    —— 即 `BridgeGeneralize` 的 `Split`（`R v ⊆ X∪Z ∨ R v ⊆ Y∪Z`）。
    **`dSep` 在这一步被消费**，且只消费它的第 4 项
    `Disjoint (bbReachableVertices Z X) Y`（Bayes-ball 不可达）。
    ⟹ **完全可推广**：`SplitFromDAG.split_of_dSep` 已在**任意 `V`** 上把
    `dSep X Y Z` + 覆盖 `X∪Y∪Z = univ` 翻成 `Split`。

  * **(P2) 「乘积可拆成两块」**。C1.1 的证明只做了一件事：把顶点集按
    `pa v ⊆ {0,1}` 二分成 `A`/`B`，用**因子只读 `pa v`**把 `φ v` 在
    `![x,z,y]` 与 `![x,z,d]`（或 `![d,z,y]`）之间换值，然后
    `∏ = ∏A · ∏B`。**证明里没有任何一处用到「顶点数 = 3」**：
    `Finset.prod_filter_mul_prod_filter_not` 对任意 `V` 成立，
    「只读 ⟹ 在父集外可换值」对任意 `V` 成立。
    ⟹ **完全可推广**：这就是本文件的 **B2.1**。

  * **(P3) `CondMul` 的收尾**。`separable_implies_condMul` 是纯代数，
    但它**只对 `FinJoint α β γ`（即 `(α×β)×γ`）陈述** ——
    因为 `CondMul` 是**三个标量块**的乘性等式。
    在一般 `V` 上若强行取 `X,Y,Z` 为「块」并配 `mass`，得到的正是
    `FactorMarkov.CondIndep p X Y Z`（集合口径），而它**不是** `CondMul` 的
    推广形态，二者是**不同粒度**的命题：
    `CondMul` 是 `CondIndep` 在 `V = Fin 3`、`X/Y/Z` 各单点、且用
    三块联合（而非边缘）质量时的**特化**。

  ## 2 哪些能推广、哪些不能

  **能（本文件已证）**：
  * (P1)：`dSep ⟹ Split`（任意 `V`，`dSep` 真消费）——B2.2；
  * (P2)：`Factorizes + Split ⟹ 两块可分离`（任意 `V`）——B2.1；
  * 合起来：`dSep + Factorizes + 覆盖 ⟹ 两块可分离`（任意 `V`）——B3.1；
  * 再接 `BridgeIntegrated.condIndep_of_factorizes_general`：
    `dSep + Factorizes + 覆盖 ⟹ CondIndep`（任意 `V`，任意 `Z`）——B3.2；
  * 回代 `Fin 3` 得 `CondMul`——B4.1，**说明三节点主定理是一般引擎的实例**。

  **不能（诚实登记）**：
  * 「一般 DAG 上的 `Factorizes ⟹ CondMul`」**不是**正确的推广形态：
    `CondMul` 的定义域就是 `FinJoint α β γ`，一般 `V` 上无对应物；
    正确的推广终点是 `CondIndep p X Y Z`（B3.2）。
  * **覆盖条件不可去**：`SplitFromDAG.dSep_not_implies_split` 给出机检反例
    （`Fin 3` collider，`X={0},Y={1},Z=∅`，顶点 `2` 不在覆盖内）。
    三节点证明里 `dSep {0}{2}{1}` **自动**带覆盖 `{0}∪{2}∪{1} = univ`，
    故该障碍在 `V = Fin 3` 时**被隐藏**了 —— 这是「3 节点情形看起来更强」
    的全部原因。**一般情形的唯一额外前提就是覆盖。**
  * **`mass` 塔性质**完全未使用（亦不需要）。

  ## 3 依赖

  * `Fate.SplitFromDAG.split_of_dSep`（`dSep + 覆盖 ⟹ Split`，零 `sorry`）
  * `Fate.BridgeIntegrated.condIndep_of_factorizes_general`（`Factorizes + Split ⟹ CondIndep`）
  * `Fate.FactorizesToHyper.readSetOf` / `localTo_iff_readSet`
  * `Fate.PearlCondIndepBridge.separable_implies_condMul`（纯代数收尾）
  * `Fate.ThreeNodeFactorizes.jointXZ` / `CondMul`
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeGeneralize

open Finset

set_option linter.unusedSectionVars false

universe u w

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 「只读」谓词（对应三节点证明里 `hφ` / `reads01` / `reads12` 的一般形态）
  =========================================================================== -/

/-- **B1.0**：`f` 在 `S` 外**冻结** —— 只读 `S` 上的坐标。

这是三节点证明里 `reads01` / `reads12` 的前提的一般形态
（那里 `S` 分别取 `{0,1}`、`{1,2}`）。

**⚠ 两个宇宙参数独立**（`V : Type u`、`α : Type w`）：三节点回代时
`V = Fin 3 : Type 0` 而 `α` 可在任意宇宙，故不能共用一个宇宙。 -/
def FrozenOn {V : Type u} {α : Type w} (S : Finset V) (f : (V → α) → ℝ) : Prop :=
  ∀ x y : V → α, (∀ u ∈ S, x u = y u) → f x = f y

/-- **B1.1**：`S ⊆ T` 且 `f` 冻结于 `S` ⟹ `f` 冻结于 `T`。

三节点证明里「`φ v` 只读 `pa v` ⟹ 只读 `{0,1}`」正是这条
（`pa v ⊆ S` 且 `φ v` 只读 `pa v`）。 -/
theorem frozen_mono {S T : Finset V} {f : (V → α) → ℝ} (h : FrozenOn S f)
    (hST : S ⊆ T) : FrozenOn T f :=
  fun x y hxy => h x y (fun u hu => hxy u (hST hu))

/-! ===========================================================================
  §2 ⭐⭐ **一般引擎：`Factorizes + Split ⟹ 两块可分离`**

  这是 `BridgeThreeNode.separable_of_reads`（C1.1）在**任意 `V`** 上的推广。
  原证明的核心两步（`prod_filter_mul_prod_filter_not` + 因子换值）
  **逐字复用**，只是把 `{0,1}` / `{1,2}` 换成 `X ∪ Z` / `Y ∪ Z`。
  =========================================================================== -/

/-- ⭐⭐ **B2.1（两块可分离，任意 DAG）**：

设 `p` 因子分解于 `G`，且读集 `R v = {v} ∪ pa_G(v)` **不横跨** `X` 与 `Y`
（即 `Split R X Y Z`）。则 `p` 可写成两块之积：
$$p\,w = f\,w \cdot g\,w,\qquad
  f \text{ 只读 } X\cup Z,\quad g \text{ 只读 } Y\cup Z.$$

**证明结构**（与三节点 C1.1 同构）：
1. 取因子见证 `φ`。把顶点集二分成
   `A = {v | R v ⊆ X∪Z}` 与 `B = {v | ¬ R v ⊆ X∪Z}`；
   `Split` 保证 `v ∈ B` 时 `R v ⊆ Y∪Z`。
2. `f := ∏_{v∈A} φ v`，`g := ∏_{v∈B} φ v`，`∏ = f · g`
   由 `Finset.prod_filter_mul_prod_filter_not`。
3. `f` 冻结于 `X∪Z`：每个 `v ∈ A` 的 `φ v` 只读 `R v ⊆ X∪Z`（`frozen_mono`）。
   同理 `g` 冻结于 `Y∪Z`。

**⚠ `hfac` 与 `hsplit` 均被真使用**：`hfac` 提供 `φ` 与只读约束
（没有它 `p` 可任意，乘积结构无从谈起）；`hsplit` 提供 `B` 侧的 `Y∪Z` 归属
（没有它 `g` 不冻结于 `Y∪Z`）。 -/
theorem factorizes_split_twoBlock (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V)
    (hfac : Fate.FactorMarkov.Factorizes p G) (X Y Z : Finset V)
    (hsplit : Fate.View19.Split (Fate.FactorizesToHyper.readSetOf G) X Y Z) :
    ∃ f g : (V → α) → ℝ,
      (∀ w, p w = f w * g w) ∧ FrozenOn (X ∪ Z) f ∧ FrozenOn (Y ∪ Z) g := by
  classical
  obtain ⟨φ, hloc, hprod⟩ := hfac
  have hread : Fate.View19.ReadSet φ (Fate.FactorizesToHyper.readSetOf G) :=
    Fate.FactorizesToHyper.readSet_of_localTo hloc
  set R : V → Finset V := Fate.FactorizesToHyper.readSetOf G with hR
  set A : Finset V := univ.filter (fun v => R v ⊆ X ∪ Z) with hA
  set B : Finset V := univ.filter (fun v => ¬ R v ⊆ X ∪ Z) with hB
  refine ⟨fun w => ∏ v ∈ A, φ v w, fun w => ∏ v ∈ B, φ v w, ?_, ?_, ?_⟩
  · -- `p = f * g`
    intro w
    rw [hprod w]
    rw [← Finset.prod_filter_mul_prod_filter_not (univ : Finset V)
          (fun v => R v ⊆ X ∪ Z)]
  · -- `f` 冻结于 `X ∪ Z`
    intro w w' hww'
    show (∏ v ∈ A, φ v w) = (∏ v ∈ A, φ v w')
    refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : R v ⊆ X ∪ Z := (Finset.mem_filter.mp hv).2
    exact hread v w w' (fun u hu => hww' u (hv' hu))
  · -- `g` 冻结于 `Y ∪ Z`
    intro w w' hww'
    show (∏ v ∈ B, φ v w) = (∏ v ∈ B, φ v w')
    refine Finset.prod_congr rfl fun v hv => ?_
    have hnot : ¬ R v ⊆ X ∪ Z := (Finset.mem_filter.mp hv).2
    have hv' : R v ⊆ Y ∪ Z := by
      rcases hsplit v with h | h
      · exact absurd h hnot
      · exact h
    exact hread v w w' (fun u hu => hww' u (hv' hu))

/-! ===========================================================================
  §3 ⭐⭐ **`dSep` 真的推出 `Split`（一般 `V`；`dSep` 在此被消费）**

  三节点的 `dSep_forces_reads`（C1.2）在任意 `V` 上的**精确对应物**
  就是 `SplitFromDAG.split_of_dSep`（该定理在 `Fate/` 中，零 `sorry`）。
  这里**不重复证明**，只把它包成与本文件 §2 可直接对接的形式，并显式
  登记「`dSep` 的哪一项被消费」。
  =========================================================================== -/

/-- ⭐⭐ **B2.2（`dSep ⟹ Split`，任意 `V`）**。

消费 `dSep` 的**第 4 个合取项** `Disjoint (bbReachableVertices Z X) Y`
（Bayes-ball 不可达），经 `SplitFromDAG` 的三条「禁边」引理
（`not_edge_of_dSep_left` / `not_edge_of_dSep_right` / `no_collider_in_Z`）
翻成读集不横跨。

**⚠ 覆盖条件 `X ∪ Y ∪ Z = univ` 不可去**：反例见
`Fate.SplitFromDAG.dSep_not_implies_split`（`Fin 3` collider）。
三节点情形 (`V = Fin 3`, `X={0},Y={2},Z={1}`) 该覆盖**自动成立**
（`{0}∪{2}∪{1} = univ`），故在那里它被隐藏了。 -/
theorem dSep_forces_split (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ) :
    Fate.View19.Split (Fate.FactorizesToHyper.readSetOf G) X Y Z :=
  Fate.SplitFromDAG.split_of_dSep G X Y Z hdsep hcover

/-! ===========================================================================
  §4 ⭐⭐⭐ **主定理（一般 DAG）：`dSep` + `Factorizes` + 覆盖 ⟹ 两块可分离**
  =========================================================================== -/

/-- ⭐⭐⭐ **B3.1（主定理，一般 DAG）**：

$$\underbrace{G.\texttt{dSep}\ X\, Y\, Z}_{hdsep}
  \;\wedge\; \underbrace{\texttt{Factorizes}\ p\ G}_{hfac}
  \;\wedge\; \underbrace{X\cup Y\cup Z = V}_{hcover}
  \;\Longrightarrow\;
  \exists f\,g,\ p = f\cdot g,\ f \text{ 只读 } X\cup Z,\ g \text{ 只读 } Y\cup Z.$$

这是 `BridgeThreeNode.factorizes_condMul_of_dSep` 的**去 `Fin 3` 化**版本：
把「`X = x₀`、`Y = x₂`、`Z = x₁`」换成**任意三块 `X, Y, Z`**，
把「`pa v ⊆ {0,1} ∨ pa v ⊆ {1,2}`」换成 `Split`。

**前件分工**（与三节点文件逐条对应）：
* `hdsep` + `hcover` ⟹ `Split`（B2.2，即 C1.2）；
* `hfac` + `Split` ⟹ 两块可分离（B2.1，即 C1.1）。
⟹ 三节点证明的**两个关键性质 (P1)(P2) 全部一般化**，无一处依赖 `|V| = 3`。 -/
theorem dSep_factorizes_separable_general (p : (V → α) → ℝ)
    (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ)
    (hfac : Fate.FactorMarkov.Factorizes p G) :
    ∃ f g : (V → α) → ℝ,
      (∀ w, p w = f w * g w) ∧ FrozenOn (X ∪ Z) f ∧ FrozenOn (Y ∪ Z) g :=
  factorizes_split_twoBlock p G hfac X Y Z (dSep_forces_split G X Y Z hdsep hcover)

/-- ⭐⭐⭐ **B3.2（一般 `Z` 全链）**：DAG 因子分解 + `dSep X Y Z` + 覆盖
⟹ 集合口径的条件独立 `CondIndep p X Y Z`。

比 B3.1 更进一步：把两块可分离**喂给** `BridgeIntegrated.condIndep_of_factorizes_general`
（该定理内部用 `mass` 的三块拆分完成代数收尾，**不用塔**）。

**⟹ 这是三节点 `CondMul` 在一般 `V` 上的正确推广终点**：
`CondMul` 只能在 `FinJoint α β γ` 上陈述，一般 `V` 上的对应命题就是 `CondIndep`。 -/
theorem condIndep_of_factorizes_dSep_generalZ [Nonempty α]
    (p : Fate.FactorMarkov.Joint V α) (G : FateV2.Modeling.Graph.DAG V)
    (hfac : Fate.FactorMarkov.Factorizes p G) {X Y Z : Finset V}
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = univ) :
    Fate.FactorMarkov.CondIndep p X Y Z := by
  have hsplit := dSep_forces_split G X Y Z hdsep hcover
  obtain ⟨hXY, hXZ, hYZ, _⟩ := hdsep
  exact Fate.BridgeIntegrated.condIndep_of_factorizes_general p G hfac
    hsplit hXY hXZ hYZ hcover

/-! ===========================================================================
  §5 ⭐⭐⭐ **回代三节点：`CondMul` 由一般引擎重新导出**

  本节证明：`BridgeThreeNode` 的主定理 **不是** `Fin 3` 的巧合，
  而是一般引擎 B2.1 + `Split` 在 `V = Fin 3` 上的**实例**。
  =========================================================================== -/

section ThreeNode

/- 三节点部分把 `α` 落在 `Type 0`：`Fate.ThreeNodeFactorizes.jointXZ` 与
`Fate.FactorMarkov.Factorizes` 在此处的宇宙参数一致（`V = Fin 3 : Type`）。 -/
variable {β : Type} [Fintype β] [DecidableEq β] [Nonempty β]

/-- **B4.0**：`FrozenOn {0,1}` 的向量形式 —— 与 `BridgeThreeNode.reads01` 同一命题，
但这里从**一般**的 `FrozenOn` 得到。 -/
theorem frozen01 {f : (Fate.ThreeNodeFactorizes.N → β) → ℝ}
    (hf : FrozenOn ({0, 1} : Finset Fate.ThreeNodeFactorizes.N) f)
    (x y z d : β) : f ![x, z, y] = f ![x, z, d] := by
  refine hf _ _ ?_
  intro u hu
  fin_cases u <;> simp_all

/-- **B4.0′**：`FrozenOn {1,2}` 的向量形式 —— 与 `BridgeThreeNode.reads12` 同一命题。 -/
theorem frozen12 {f : (Fate.ThreeNodeFactorizes.N → β) → ℝ}
    (hf : FrozenOn ({1, 2} : Finset Fate.ThreeNodeFactorizes.N) f)
    (x y z d : β) : f ![x, z, y] = f ![d, z, y] := by
  refine hf _ _ ?_
  intro u hu
  fin_cases u <;> simp_all

/-- ⭐⭐⭐ **B4.1（回代：三节点 `CondMul` 是一般引擎的实例）**：

对 `V = Fin 3`、`X = {0}`、`Y = {2}`、`Z = {1}`，一般主定理 B3.1 给出
`p = f·g` 且 `f` 只读 `{0,1}`、`g` 只读 `{1,2}`；再用
`separable_implies_condMul`（纯代数）收尾，得到 `CondMul (jointXZ p)`
—— **与 `BridgeThreeNode.factorizes_condMul_of_dSep` 同一结论**，
但走的是**完全一般**的路线（`Split` 由 `dSep` 给出，不再逐点 `fin_cases` 分析）。

**⚠ 这里唯一的 `Fin 3` 专属步骤是「向量重排」**（`frozen01` / `frozen12`：
把 `FrozenOn {0,1}` 翻译成 `![x,z,y] = ![x,z,d]`），
它是 `FinJoint` 坐标约定的产物，**与图论内容无关**。 -/
theorem threeNode_condMul_of_general {p : (Fate.ThreeNodeFactorizes.N → β) → ℝ}
    (G : FateV2.Modeling.Graph.DAG Fate.ThreeNodeFactorizes.N)
    (hdsep : G.dSep ({0} : Finset Fate.ThreeNodeFactorizes.N)
      ({2} : Finset Fate.ThreeNodeFactorizes.N)
      ({1} : Finset Fate.ThreeNodeFactorizes.N))
    (hfac : Fate.FactorMarkov.Factorizes p G) :
    FateV2.Predict.FinCondIndep.CondMul (Fate.ThreeNodeFactorizes.jointXZ p) := by
  have hsub01 : ({0, 1} : Finset Fate.ThreeNodeFactorizes.N) =
      ({0} : Finset Fate.ThreeNodeFactorizes.N) ∪ ({1} : Finset Fate.ThreeNodeFactorizes.N) := rfl
  have hsub12 : ({1, 2} : Finset Fate.ThreeNodeFactorizes.N) =
      ({2} : Finset Fate.ThreeNodeFactorizes.N) ∪ ({1} : Finset Fate.ThreeNodeFactorizes.N) :=
    Finset.ext (fun u => by fin_cases u <;> simp)
  obtain ⟨f, g, hpg, hf, hg⟩ :=
    dSep_factorizes_separable_general p G
      ({0} : Finset Fate.ThreeNodeFactorizes.N)
      ({2} : Finset Fate.ThreeNodeFactorizes.N)
      ({1} : Finset Fate.ThreeNodeFactorizes.N) hdsep (by decide) hfac
  rw [← hsub01] at hf
  rw [← hsub12] at hg
  obtain ⟨d⟩ := ‹Nonempty β›
  refine FateV2.Predict.PearlCondIndepBridge.separable_implies_condMul
    (Fate.ThreeNodeFactorizes.jointXZ p)
    (fun x z => f ![x, z, d]) (fun y z => g ![d, z, y]) ?_
  intro x y z
  rw [Fate.ThreeNodeFactorizes.jointXZ_apply, hpg, frozen01 hf x y z d,
    frozen12 hg x y z d]

/-- ⭐⭐ **B4.2（连通性检查）**：主定理 B3.1 的**假设确实可满足**（链图）。
若把 `hdsep` 换成撞子图，`Split` 不成立（见 B5.1），链条在此断开 ——
说明 B4.1 的前件**非空洞**。 -/
theorem chain_dSep_split :
    Fate.View19.Split
      (Fate.FactorizesToHyper.readSetOf Fate.ThreeNodeFactorizes.chainDAG)
      ({0} : Finset Fate.ThreeNodeFactorizes.N)
      ({2} : Finset Fate.ThreeNodeFactorizes.N)
      ({1} : Finset Fate.ThreeNodeFactorizes.N) :=
  dSep_forces_split Fate.ThreeNodeFactorizes.chainDAG _ _ _
    (by decide) (by decide)

end ThreeNode

/-! ===========================================================================
  §6 ⭐⭐ **非空洞性：撞子在一般口径下同样被 `dSep` 排除**

  三节点文件的 C1.5 用 `decide` 证 `colliderDAG` 不满足 `dSep {0}{2}{1}`。
  这里给出**一般 `V` 上的对应事实**：`dSep` 的不成立**等价于**
  「存在 `X → z ← Y` 型被激活的撞子或直边」，故 `Split` 的失败点
  只在覆盖缺失处（见 `SplitFromDAG.dSep_not_implies_split`）。
  下面只机检与三节点一致的那一条，作为对三节点 C1.5 的一般化交叉核对。
  =========================================================================== -/

/-- **B5.1**：撞子图 `0 → 2 ← 1` 不满足 `dSep {0}{2}{1}`（一般口径下的交叉核对；
与 `BridgeThreeNode.collider_not_dSep_cond` 同一命题）。 -/
theorem collider_not_dSep_general :
    ¬ Fate.ThreeNodeFactorizes.colliderDAG.dSep
        ({0} : Finset Fate.ThreeNodeFactorizes.N)
        ({2} : Finset Fate.ThreeNodeFactorizes.N)
        ({1} : Finset Fate.ThreeNodeFactorizes.N) := by
  decide

/-- **B5.2**：撞子图上 `Split R {0} {2} {1}` **也**不成立 ——
这从**读集侧**独立确认「主定理的 `dSep` 前件不可去」：
`Split` 假 ⟹ `dSep` 假（B2.2 的逆否），故 B3.1 的链条确实断开，
而不是绕过了撞子。 -/
theorem collider_not_split_general :
    ¬ Fate.View19.Split
        (Fate.FactorizesToHyper.readSetOf Fate.ThreeNodeFactorizes.colliderDAG)
        ({0} : Finset Fate.ThreeNodeFactorizes.N)
        ({2} : Finset Fate.ThreeNodeFactorizes.N)
        ({1} : Finset Fate.ThreeNodeFactorizes.N) := by
  unfold Fate.View19.Split Fate.FactorizesToHyper.readSetOf
  decide

/-! ===========================================================================
  §7 ⚠ **诚实登记（边界）**

  | 项 | 状态 |
  |---|---|
  | (P1) `dSep ⟹ Split`，任意 `V` | ✅ 已证（B2.2），经 `SplitFromDAG.split_of_dSep`，零 `sorry` |
  | (P2) `Factorizes + Split ⟹ 两块可分离`，任意 `V` | ✅ **本文件新证**（B2.1）|
  | 主定理 `dSep + Factorizes + 覆盖 ⟹ 两块可分离`，任意 `V` | ✅ 已证（B3.1）|
  | 一般 `Z` 全链 ⟹ `CondIndep p X Y Z` | ✅ 已证（B3.2）|
  | 三节点 `CondMul` 由一般引擎导出 | ✅ 已证（B4.1）|
  | 撞子被排除（一般口径） | ✅ 已证（B5.1、B5.2）|
  | 覆盖条件不可去 | ✅ **已证实为必需**（外部 `SplitFromDAG.dSep_not_implies_split` 机检反例）|
  | 「一般 DAG 的 `Factorizes ⟹ CondMul`」 | ❌ **不是正确的推广形态**：`CondMul` 的定义域为 `FinJoint α β γ`，一般 `V` 无对应 |
  | `mass` 塔性质 | 完全未使用 |

  **本文件边界的准确陈述**：B3.1/B3.2 对**任意有限 `V`**、**任意三块
  `X, Y, Z`** 成立，唯一额外前提是覆盖 `X∪Y∪Z = univ`。
  故三节点证明的关键性质 (P1)(P2) **全部一般化且无障碍**；
  唯一的「障碍」是覆盖条件 —— 而它在 `V = Fin 3`、`X,Y,Z` 各取单点时
  **自动成立**，这正是 3 节点情形看不到该障碍的原因。
  =========================================================================== -/

end BridgeGeneralize

end FateV2.Predict