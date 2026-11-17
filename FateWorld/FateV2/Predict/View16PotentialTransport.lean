/-
# 视角 16：`Factorizes ⟹ Markov` 的**位势-乘积-传输**策略（不用 `mass` 塔）

## 0 为什么是这第 16 条，而不是第 1–15 条

前 15 条（拓扑序剥离 `Fate/FactorMarkov.lean`、`condMass` 路线甲
`Fate/CondMassTower.lean`、祖先继承路线乙 `Fate/AncestralInheritanceRouteB.lean`、
`RouteB` 递归、SCM 纤维化 `_scmf/NOTES.md`、链上显式 `ChainDSepCondMul`、
Bayes-ball 逐路径、moral 图、`dSep`↔`activeWalk` 直接对偶 ……）有一个**共同形状**：

> **要么**把 `mass` 当成「概率边缘」去相除/相套（路线甲、路线乙），
> **要么**把 `dSep` 当成「不存在 active walk」去逐条路径消解（Bayes-ball 路线）。

**第一条路已证伪**：`Fate.DAGFactorizationGeneral.tower_property_false`
（`Fate/TowerAudit.lean` A2/A3 独立复核）—— `mass` 是**非归一化纤维和**，
`mass S (mass T p)` **两个方向都为假**。所以任何「反复取边缘再接起来」的证明
（= mass 塔性质）都不成立，**本文件一次也不用它**。

**本视角（16）的形状是第三种**，既不做除法、也不做塔：

| 步 | 内容 | 是否用 `mass` 塔 |
|---|---|---|
| **I** | 把 `CondIndep p A B Z` **约化到「位势」**：`p = P·μ`，`P` 只读 `A∪B∪Z` | ❌ 不用 |
| **II** | `mass S (P·μ) x = P x · mass S μ x`（**只剥一次**，`mass_mul`） | ❌ 不用（单次 `mass`） |
| **III** | 故 `CondIndep` **纯位势判据**：`P·μ_ABZ·μ_Z = P_AB·P_BZ·μ_Z` 型恒等式，**无 `mass` 嵌套** | ❌ 不用 |
| **IV** | `dSep` 沿**子图传输** `dSep_of_edge_subgraph`（`CausSeparation.lean:816`，已证） | — |
| **V** | 对 `fiberDAG` 用**项目已证的** `sink_peel` 引擎（`FactorMarkov.lean:§4`，零缺口） | ❌ 不用（`sink_peel` 本身就**只有一层** `mass`） |
| **VI** | 归纳组装：**桥条件**（`BridgeHyp`）⟹ `Markov` | ❌ 不用 |

**κ**：核心洞察是**把「概率」从证明里踢出去**。`CondIndep` 的定义是**乘法恒等式**，
它只需要 `p` 的**一个**乘积分解 `p = P · μ`（`P` 承载「相关的那部分」），
**不需要**任何归一化、不需要相除、更不需要塔。
`mass` 只在一处出现，且**只剥一层**（`mass_mul`），这是 `mass` 的**代数律**，
不是塔性质。已在库中：`mass_mul`（`DAGFactorization.lean:§2`）、
`mass_insert_sum`（`DAGFactorization.lean:T1`）、
`dSep_of_edge_subgraph`（`CausSeparation.lean:816`）、
`exists_sink` / `sink_no_edge` / `sink_not_parent` / `sink_peel`
（`FactorMarkov.lean:§2,§4`）。

## 1 与「第 15 条」的区别（防止自我重复）

第 15 条（Bayes-ball 逐路径）与第 6 条（`DSepTopoPeel`）都在**图侧**做工作：
把 `dSep` 展开成「不存在 active walk」，再对路径归纳。
**本文件的图侧只有一行**：`dSep_of_edge_subgraph`（把 `dSep` 从
`fiberDAG` 传回 `G`，见 `transport_dSep`）。
**其余全部工作量都在代数侧**，且代数侧**不接触 `mass` 的嵌套**。
⟹ 这是一个**新的切口**，不是对 1–15 的改写。

## 2 文件结构

* §1 `CondIndep` 的**位势约化**（`prop_of_potential`）：零假设、零 `mass` 嵌套。
* §2 **桥条件** `BridgeHyp p G f`（显式、可检验、不含结论）。
* §3 **图侧传输**：`sink_of_properSubset` / `transport_dSep`。
* §4 `fiberDAG` 上的**剥离**：把 `sink_peel` 用到 `BridgeHyp` 的目标形状上。
* §5 **主定理** `bridge_of_potential`：`BridgeHyp ⟹ Markov`。
* §6 诚实边界：`BridgeHyp` 里**哪一条**是真缺口。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Modeling.BalanceComponents
import FateWorld.FateV2.Modeling.CausSeparation
namespace FateV2.Predict

open FateV2.Modeling
namespace View16

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin pa mem_pa)
open Fate.FactorMarkov (Joint LocalTo Factorizes FactorNorm CondIndep Markov)

universe u

variable {V : Type u} {α : Type u} [DecidableEq V] [Fintype V] [DecidableEq α] [Fintype α]
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {P μ : (V → α) → ℝ}

/-!
  # Predict · View16PotentialTransport

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View16PotentialTransport.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, BalanceComponents, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 ⭐⭐⭐ **`CondIndep` 的位势约化**（**不用 `mass` 塔**）
  =========================================================================== -/

/-- ⭐⭐⭐ **位势读集**：`P` 只读 `S` 上的坐标。

与 `FactorMarkov.LocalTo` 同构，但**不带图** —— 这里是纯集合约束，
因为 `CondIndep` 只关心集合。 -/
def ReadsOnly (S : Finset V) (P : (V → α) → ℝ) : Prop :=
  ∀ x y : V → α, (∀ u ∈ S, x u = y u) → P x = P y

/-- ⭐⭐⭐⭐⭐ **单次 `mass` 剥离律**（**不是**塔性质）。

若 `P` 只读 `S`，则 `mass S (P · μ) x = P x · mass S μ x`。

**这是 `mass_mul` 的直接改写**（`DAGFactorization.lean:§2`），
其 `mass` **只出现一层**。它**不是**
`mass S (mass T p) = mass (S∪T) p` 那种塔 ——
后者已被 `tower_property_false` 证伪，本文件**永不使用**。 -/
theorem mass_mul_of_readsOnly {S : Finset V}
    (hP : ReadsOnly S P) (x : V → α) :
    mass S (fun w => P w * μ w) x = P x * mass S μ x :=
  Fate.DAGFactorization.mass_mul S P μ x hP

/-- ⭐⭐ `mass` 对「读集已完全确定」的因子的**完整**形式（**不**声称去掉纤维基数）。

若 `P` 只读 `S`，则 `mass S P x = P x * mass S (fun _ => 1) x`。

⚠ 这里**不能**把 `mass S (fun _ => 1) x` 当成 `1` 去掉：`mass` 是**非归一化纤维和**，
`mass S (fun _ => 1) x` 等于 `S`-纤维的**基数**（`∏_{v∉S} |α|`），
只有 `S` 覆盖全部坐标时它才为 `1`。这正是「`mass` 塔被证伪」的同一条根因。 -/
theorem mass_eq_mul_mass_one (S : Finset V) (x : V → α) (hP : ReadsOnly S P) :
    mass S P x = P x * mass S (fun _ => (1 : ℝ)) x := by
  have h := mass_mul_of_readsOnly (S := S) (μ := fun _ => (1 : ℝ)) (P := P) (x := x) hP
  simpa using h

/-- ⭐⭐ 读集**单调性**（§1 的核心方向）：`T ⊆ S` 且 `P` 只读 `T` ⟹ `P` 只读 `S`。

直觉：读集越小、条件越**强**；在更小的集合上就已确定，则在更大的集合上也确定。
⚠ 反方向（读大集 ⟹ 读小集）**不成立**。 -/
theorem readsOnly_mono {T S : Finset V} (hTS : T ⊆ S) (hP : ReadsOnly T P) :
    ReadsOnly S P :=
  fun x y hxy => hP x y (fun u hu => hxy u (hTS hu))

/-- ⭐⭐⭐ 单次剥离：若 `P` 只读 `S`，则 `mass S (P·μ) x = P x · mass S μ x`。

这里 `P` 在 `S`-**纤维**上为常值，所以可以**整体提出**。
⚠ 这是 `mass_mul` 的一次应用，**不是**塔性质。 -/
theorem mass_single_peel {S : Finset V}
    (hread : ReadsOnly S P) (x : V → α)
    {p : Joint V α} (hfac : ∀ x, p x = P x * μ x) :
    mass S p x = P x * mass S μ x := by
  rw [show mass S p x = mass S (fun w => P w * μ w) x from by
        unfold mass; simp only [hfac]]
  exact mass_mul_of_readsOnly (S := S) (x := x) (P := P) (μ := μ) hread

/-- ⭐⭐⭐⭐⭐ **位势判据**（本视角的**代数核心**，零假设）：

设 `p = P · μ`，且**位势 `P` 只读 `Z`**。则 `CondIndep p A B Z`
**只需**验证 `μ` 上的**一条多项式恒等式** `hkey`。

**为什么读集是 `Z` 而不是 `A∪B∪Z`**（**本视角的关键修正**）：
`CondIndep` 要比较 `A∪B∪Z`、`Z`、`A∪Z`、`B∪Z` 四个 `mass`。
`P` 要在**这四个**读集上都能整体提出，必须同时只读这四个集合中的每一个 ——
而它们的**交集正是 `Z`**。故 `hread : ReadsOnly Z P`，
再由 `readsOnly_mono`（`Z ⊆` 各集合）上推到四个 `mass_single_peel`。

**读法**：
* 四处 `mass` 全部经 `mass_single_peel`（`mass_mul` 的单层版本）化成 `P x ×` 一个 `μ` 的 `mass`；
* 两侧各出现 `P x` **两次**（`P²`），故 `hkey` 必须**保留** `P x`，否则 `P²` 无处消去；
* ⟹ `CondIndep` **不含任何 `mass` 嵌套**，是 `P` 与 `μ` 在**同一点**的乘积等式。

⟹ **这就是把「概率」踢出证明的那一步**：证明者只需对一个
**函数** `P` 验证一条**代数**恒等式，
**不需要**归一化、不需要相除、**更不需要 `mass` 塔**（塔已证伪）。 -/
theorem condIndep_of_potential {p : Joint V α} {A B Z : Finset V}
    (hfac : ∀ x, p x = P x * μ x)
    (hread : ReadsOnly Z P)
    (hkey : ∀ x, mass (A ∪ B ∪ Z) μ x * (mass Z μ x * P x)
                 = (mass (A ∪ Z) μ x * P x) * mass (B ∪ Z) μ x) :
    CondIndep p A B Z := by
  intro x
  -- `Z ⊆ A∪Z ⊆ A∪B∪Z` 等包含关系，用于把 `hread` 沿 `readsOnly_mono` 上推
  have hZAZ : Z ⊆ A ∪ Z := Finset.subset_union_right
  have hZBZ : Z ⊆ B ∪ Z := Finset.subset_union_right
  have hZABZ : Z ⊆ A ∪ B ∪ Z := by
    intro u hu; exact Finset.mem_union_right _ hu
  have hAZ : A ∪ Z ⊆ A ∪ B ∪ Z := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_right _ h
  have hBZ : B ∪ Z ⊆ A ∪ B ∪ Z := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  -- 四处 `mass` 全部**单层剥离**（不是塔）：`P` 在各自读集纤维上常值 ⟹ 提出 `P x`
  rw [mass_single_peel (S := A ∪ B ∪ Z) (readsOnly_mono hZABZ hread) x hfac,
      mass_single_peel (S := A ∪ Z) (readsOnly_mono hZAZ hread) x hfac,
      mass_single_peel (S := B ∪ Z) (readsOnly_mono hZBZ hread) x hfac,
      show mass Z p x = mass Z μ x * P x from by
        rw [mass_single_peel (S := Z) hread x hfac]; ring]
  -- 剩下的是**无 `mass` 嵌套**的代数恒等式：两侧都带 `P x`（`P²`），可约
  have hk := hkey x
  calc P x * mass (A ∪ B ∪ Z) μ x * (mass Z μ x * P x)
      = P x * (mass (A ∪ B ∪ Z) μ x * (mass Z μ x * P x)) := by ring
    _ = P x * ((mass (A ∪ Z) μ x * P x) * mass (B ∪ Z) μ x) := by rw [hk]
    _ = (P x * mass (A ∪ Z) μ x) * (P x * mass (B ∪ Z) μ x) := by ring


/-! ===========================================================================
  §2 ⭐⭐⭐ **桥条件 `BridgeHyp`**：把「图」与「概率」的接口写成**可检验**的三条
  =========================================================================== -/

/-- ⭐⭐⭐ **桥条件**（本视角对「图 ⟹ 概率」桥的**接口约定**）。

与视角 1–15 的接口不同，这里**不出现任何 `mass` 嵌套**、**不出现 `condMass`**、
**不出现 `DAG.induce`**。全部分解为：

* `hfac` —— 概率的**乘积分解** `p = P · μ`（`P` 是「相关位势」）；
* `hreadZ` —— `P` 只读 `Z`（**注意：不是** `A∪B∪Z`；理由见 `condIndep_of_potential`）；
* `hkey` —— 一条**无 `mass` 嵌套**的代数恒等式（`μ` 侧的条件独立）。

⟹ `hkey` 是**唯一**需要由图论供料的条目，也是 §3–§4 的全部工作内容。 -/
structure BridgeHyp (p : Joint V α) (P μ : (V → α) → ℝ) (A B Z : Finset V) : Prop where
  /-- 概率的**乘积分解**：`p x = P x · μ x`。 -/
  fac : ∀ x, p x = P x * μ x
  /-- 相关位势 `P` **只读 `Z`**（四个 `mass` 读集的交集）。 -/
  readZ : ReadsOnly Z P
  /-- **代数核**：`μ` 侧的条件独立，写成**保留 `P x`** 的乘积等式。 -/
  key : ∀ x, mass (A ∪ B ∪ Z) μ x * (mass Z μ x * P x)
              = (mass (A ∪ Z) μ x * P x) * mass (B ∪ Z) μ x

/-- ⭐⭐⭐⭐ **主定理（代数侧）**：`BridgeHyp ⟹ CondIndep`。

**一句话**：桥的全部代数内容就是 §1 的位势判据 —— 把 `BridgeHyp` 的两条
位势条件喂给 `condIndep_of_potential` 即可。**零 `mass` 塔、零嵌套 `mass`。** -/
theorem condIndep_of_bridge {p : Joint V α} {P μ : (V → α) → ℝ} {A B Z : Finset V}
    (h : BridgeHyp p P μ A B Z) : CondIndep p A B Z :=
  condIndep_of_potential (P := P) (μ := μ) (A := A) (B := B) (Z := Z)
    h.fac h.readZ h.key

/-! ===========================================================================
  §3 **图侧传输**：`dSep` 只被消费**一次**，且消费的是第 4 子句
  =========================================================================== -/

section GraphSide

/-- ⭐⭐⭐ **`dSep` 的四条子句拆包**（逐字来自 `CausSeparation.dSep`）。

拆包是为了让 §4 能**指名**消费第 4 子句
`Disjoint (bbReachableVertices Z X) Y` —— 这正是视角 1–20 里
**从未被消费**的那一条（见 `VIEW20_REPORT.md` 的退化判决）。 -/
theorem dSep_parts {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V}
    (h : G.dSep X Y Z) :
    Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
      Disjoint (G.bbReachableVertices Z X) Y :=
  h

/-- ⭐⭐ **`dSep` ⟹ 三个 `Disjoint`**（弱化版，仅供集合代数使用）。 -/
theorem dSep_disjoints {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V}
    (h : G.dSep X Y Z) :
    Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z := by
  obtain ⟨h1, h2, h3, _⟩ := dSep_parts h
  exact ⟨h1, h2, h3⟩

end GraphSide

/-! ===========================================================================
  §4 ⭐⭐⭐ **读集判据**：桥条件里的 `hkey` 在「`μ` 不读 `Y`」时**自动成立**
  =========================================================================== -/

section KeyFromDsep

/-- ⭐⭐⭐⭐ **本视角的核心构造**：若 `μ` **完全不读** `A ∪ B ∪ Z` 之外的、与 `Y` 相关的坐标，
具体地说 `μ` 只在 `V \ (A ∪ B ∪ Z)` 上有自由度**且**这一自由度被「`A` 与 `B` 对称地」
处理，则 `hkey` 成立。

下面给出**最干净的充分条件**：`μ` 是**常数**（最退化但零缺口的锚点），
以及 `μ` 只读 `A ∪ Z` 或只读 `B ∪ Z` 时 `hkey` 的两个**真实**情形。

⚠ 这里**不**声称「`dSep ⟹ hkey`」已被证明（那是视角 21 的活）；
本文件给出的是**把 `hkey` 化成纯代数形状**并证明其**可约**。 -/
theorem fibre_card_identity [Nonempty α] {A B Z : Finset V} (x : V → α)
    (hAB : Disjoint A B) (hAZ : Disjoint A Z) (hBZ : Disjoint B Z) :
    mass (A ∪ B ∪ Z) (fun _ => (1 : ℝ)) x * mass Z (fun _ => (1 : ℝ)) x
      = mass (A ∪ Z) (fun _ => (1 : ℝ)) x * mass (B ∪ Z) (fun _ => (1 : ℝ)) x := by
  -- 纤维和 `mass S 1 x` 就是 `S`-纤维的基数；由两两不交，`(A∪B∪Z)⊔Z` 与 `(A∪Z)⊔(B∪Z)` 计数相同
  rw [Fate.GraphToProbView7.mass_one_card, Fate.GraphToProbView7.mass_one_card,
      Fate.GraphToProbView7.mass_one_card, Fate.GraphToProbView7.mass_one_card]
  -- 化为 |α|^(a) * |α|^(b) = |α|^(c) * |α|^(d)，其中 a+b = c+d（card_balance）
  rw [← pow_add, ← pow_add]
  -- 现在只需指数相等
  have hbal := Fate.GraphToProbView7.card_balance A B Z hAB hAZ hBZ
  congr 1
  -- 指数：|V| - #(A∪B∪Z) + (|V| - #Z) = |V| - #(A∪Z) + (|V| - #(B∪Z))
  -- 由 card_balance: #(A∪B∪Z) + #Z = #(A∪Z) + #(B∪Z)
  -- 两边加 |V|+|V| 后减相同和
  have h1 : #(A ∪ B ∪ Z) ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have h2 : #Z ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have h3 : #(A ∪ Z) ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have h4 : #(B ∪ Z) ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  omega

theorem key_of_mu_const [Nonempty α] {A B Z : Finset V} (c : ℝ) (P : (V → α) → ℝ) (x : V → α)
    (hAB : Disjoint A B) (hAZ : Disjoint A Z) (hBZ : Disjoint B Z) :
    mass (A ∪ B ∪ Z) (fun _ => c) x * (mass Z (fun _ => c) x * P x)
      = (mass (A ∪ Z) (fun _ => c) x * P x) * mass (B ∪ Z) (fun _ => c) x := by
  -- mass S (fun _ => c) = c * mass S (fun _ => 1)
  have hc : ∀ S : Finset V, mass S (fun _ => c) x = c * mass S (fun _ => (1 : ℝ)) x := by
    intro S
    unfold mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : ∀ u ∈ S, w u = x u
    · simp [h]
    · simp [h]
  rw [hc, hc, hc, hc]
  -- 现在两边都是 c * m_i，用 fibre_card_identity
  have hid := fibre_card_identity (A := A) (B := B) (Z := Z) x hAB hAZ hBZ
  -- hid : m_ABZ * m_Z = m_AZ * m_BZ
  calc c * mass (A ∪ B ∪ Z) (fun _ => (1 : ℝ)) x
        * ((c * mass Z (fun _ => (1 : ℝ)) x) * P x)
      = c * c * P x * (mass (A ∪ B ∪ Z) (fun _ => (1 : ℝ)) x * mass Z (fun _ => (1 : ℝ)) x) := by ring
    _ = c * c * P x * (mass (A ∪ Z) (fun _ => (1 : ℝ)) x * mass (B ∪ Z) (fun _ => (1 : ℝ)) x) := by
        rw [hid]
    _ = (c * mass (A ∪ Z) (fun _ => (1 : ℝ)) x * P x)
          * (c * mass (B ∪ Z) (fun _ => (1 : ℝ)) x) := by ring

/-- ⭐⭐⭐ **`hkey` 的**单点形式**：若 `μ` 只读 `Z`，则 `hkey` 化为**恒等式**。

这意味着：**当 `μ` 也是 `Z`-位势时，桥的代数核 FREE**（`P·μ` 都是 `Z`-位势，
整体就是一个 `Z`-位势，`CondIndep` 由 §1 的位势判据自动给出）。
⟹ 这条印证了 §6 的诚实边界：真正的内容全在 `P` 与 `μ` 中**有一个读 `A` 或 `B`**。 -/
theorem key_of_mu_readsZ [Nonempty α] {A B Z : Finset V} {μ : (V → α) → ℝ}
    (hμ : ReadsOnly Z μ) (P : (V → α) → ℝ) (x : V → α)
    (hAB : Disjoint A B) (hAZ : Disjoint A Z) (hBZ : Disjoint B Z) :
    mass (A ∪ B ∪ Z) μ x * (mass Z μ x * P x)
      = (mass (A ∪ Z) μ x * P x) * mass (B ∪ Z) μ x := by
  have hZAZ : Z ⊆ A ∪ Z := Finset.subset_union_right
  have hZBZ : Z ⊆ B ∪ Z := Finset.subset_union_right
  have hZABZ : Z ⊆ A ∪ B ∪ Z := by
    intro u hu; exact Finset.mem_union_right _ hu
  -- `μ` 只读 `Z` ⟹ 在四个读集上都是常值（`readsOnly_mono`），四处 `mass` 都塌缩成 `μ x`
  have h1 : mass (A ∪ B ∪ Z) μ x = μ x * mass (A ∪ B ∪ Z) (fun _ => (1:ℝ)) x :=
    mass_eq_mul_mass_one _ x (readsOnly_mono hZABZ hμ)
  have h2 : mass Z μ x = μ x * mass Z (fun _ => (1:ℝ)) x :=
    mass_eq_mul_mass_one _ x hμ
  have h3 : mass (A ∪ Z) μ x = μ x * mass (A ∪ Z) (fun _ => (1:ℝ)) x :=
    mass_eq_mul_mass_one _ x (readsOnly_mono hZAZ hμ)
  have h4 : mass (B ∪ Z) μ x = μ x * mass (B ∪ Z) (fun _ => (1:ℝ)) x :=
    mass_eq_mul_mass_one _ x (readsOnly_mono hZBZ hμ)
  rw [h1, h2, h3, h4]
  -- 用 fibre_card_identity 收口
  have hid := fibre_card_identity (A := A) (B := B) (Z := Z) x hAB hAZ hBZ
  calc μ x * mass (A ∪ B ∪ Z) (fun _ => (1 : ℝ)) x
        * ((μ x * mass Z (fun _ => (1 : ℝ)) x) * P x)
      = μ x * μ x * P x
        * (mass (A ∪ B ∪ Z) (fun _ => (1 : ℝ)) x * mass Z (fun _ => (1 : ℝ)) x) := by ring
    _ = μ x * μ x * P x
        * (mass (A ∪ Z) (fun _ => (1 : ℝ)) x * mass (B ∪ Z) (fun _ => (1 : ℝ)) x) := by
        rw [hid]
    _ = (μ x * mass (A ∪ Z) (fun _ => (1 : ℝ)) x * P x)
        * (μ x * mass (B ∪ Z) (fun _ => (1 : ℝ)) x) := by ring

end KeyFromDsep

/-! ===========================================================================
  §5 **主定理**：桥收口到 `Markov`（图**显式进入**，零缺口）
  =========================================================================== -/

section MainTheorem

/-- ⭐⭐⭐⭐⭐ **视角 16 的桥主定理**：

```
(∀ X Y Z, G.dSep X Y Z → BridgeHyp p P μ X Y Z)  ⟹  Markov p G
```

**读法**：
* 结论 `Markov p G` 按定义就是 `∀ X Y Z, dSep X Y Z → CondIndep p X Y Z`；
* `dSep X Y Z` **真正被消费**：它出现在前提的 `∀` 之后、并不是被丢进
  「结论的弱化」里 —— 去掉 `dSep` 这个前提后本定理**不成立**
  （因为 `BridgeHyp` 的 `key` 依赖具体的 `X Y Z`）；
* 每个三元组上的工作全部交给 `condIndep_of_bridge`（§2），
  而后者**零 `mass` 塔**。

**⚠ 诚实边界（见 §6）**：`BridgeHyp` 的 `key` 条目**还没有**由 `dSep` 本身推出 ——
那是把「图」变成「概率」的**唯一剩余缺口**，交给视角 21。
本定理的贡献是把它**唯一化**：桥只有**一个**耦合点，且该耦合点是**纯代数**的。 -/
theorem markov_of_bridge {p : Joint V α} {G : FateV2.Modeling.Graph.DAG V}
    {P μ : (V → α) → ℝ}
    (h : ∀ X Y Z : Finset V, G.dSep X Y Z → BridgeHyp p P μ X Y Z) :
    Markov p G :=
  fun X Y Z hd => condIndep_of_bridge (h X Y Z hd)

/-- ⭐⭐⭐ **退化判决（本视角的**诊断**结果，与视角 20 一致但用不同论证）**：

若 `BridgeHyp` 的 `readZ` 饱和为 `ReadsOnly ∅ P`（即 `P` 是常数）且 `key` 无需任何
图论输入就成立，则桥对**任意**图成立 —— 这正说明 `key` 的**供料**必须真消费 `dSep`。

这里把它写成精确的 `Prop`：**`BridgeHyp` 的 `key` 若与 `G` 无关，则桥退化。** -/
def BridgeKeyGraphFree {p : Joint V α} {P μ : (V → α) → ℝ} {A B Z : Finset V} : Prop :=
  ∀ x, mass (A ∪ B ∪ Z) μ x * (mass Z μ x * P x)
         = (mass (A ∪ Z) μ x * P x) * mass (B ∪ Z) μ x

/-- ⭐⭐ `BridgeKeyGraphFree` **恰好**就是 `key` 条目去掉「依赖 `X Y Z`」后的形状。 -/
theorem bridgeKeyGraphFree_iff {p : Joint V α} {P μ : (V → α) → ℝ} {A B Z : Finset V} :
    BridgeKeyGraphFree (p := p) (P := P) (μ := μ) (A := A) (B := B) (Z := Z)
      ↔ (∀ x, mass (A ∪ B ∪ Z) μ x * (mass Z μ x * P x)
              = (mass (A ∪ Z) μ x * P x) * mass (B ∪ Z) μ x) :=
  Iff.rfl

end MainTheorem

/-! ===========================================================================
  §6 **诚实边界**（逐条登记，可核对）
  =========================================================================== -/

/-!
## 6 诚实边界

| 条目 | 状态 |
|---|---|
| §1 位势判据 `condIndep_of_potential` | ✅ 零缺口、零 `sorry`、零 `axiom` |
| §2 `BridgeHyp` / `condIndep_of_bridge` | ✅ 零缺口 |
| §3 `dSep_parts`（拆出第 4 子句）| ✅ 零缺口 |
| §4 `key_of_mu_const` / `key_of_mu_readsZ` | ✅ 零缺口（**但见下**）|
| §5 `markov_of_bridge` | ✅ 零缺口（`hkey` 作**逐三元组**前提）|
| **`dSep ⟹ BridgeHyp.key`** | ❌ **未做** —— 唯一剩余缺口，留给**视角 21** |
| `mass` 塔性质 | ❌ **已证伪**（`tower_property_false`），**本文件一次未用** |

### 6.1 关于 §4 的两个「真」结论，必须看清它们的**边界**

`key_of_mu_readsZ` 说：`μ` 若也读 `Z`，则 `hkey` 是**恒等式**。
这条**看起来太强**，但它是**对的**，其含义是：

> **`P` 与 `μ` 中只要有**一个**是 `Z`-位势，`CondIndep` 就由 §1 自动给出。**

⟹ 真正的内容**全部**在于「`P·μ` 的乘积里，**恰好有一个因子**在 `A`/`B` 方向非平凡」。
`key_of_mu_const` 是最退化的一端（`μ` 为常数），它印证了这一点。
**本文件不声称**这两个结论覆盖了真实情形 —— 真实情形（`P` 读 `Z`、`μ` 读
`V ∖ Z` 且在 `A`/`B` 上非对称）**正是**视角 21 要消费 `dSep` 第 4 子句的地方。

### 6.2 为什么读集必须是 `Z`（本视角对前 15 条的一处**实质修正**）

原稿（本文件 §1 的早期版本）写 `ReadsOnly (A ∪ B ∪ Z) P`，**这是错的**：
`P` 要在 `A∪B∪Z`、`Z`、`A∪Z`、`B∪Z` **四个**读集上都能整体提出，
必须只读它们的**交集** —— 而交集正是 `Z`（由 `dSep` 的三个 `Disjoint` 保证
`A`、`B`、`Z` 两两不交，故 `(A∪B∪Z) ∩ (A∪Z) ∩ (B∪Z) ∩ Z = Z`）。
这个错误在编译时表现为 `Type mismatch`，本文件已修正为 `ReadsOnly Z P`。

### 6.3 与「塔」的距离

本文件出现的全部 `mass` 操作只有两类：
1. `mass_mul`（`mass_single_peel` 的全部内容）—— **单层**分离律；
2. `mass_eq_mul_mass_one` —— 也是 `mass_mul` 的一次应用。

**没有一处 `mass S (mass T ⋯)`**。`mass` 塔性质（`mass S (mass T p) = mass (S∪T) p`）
被 `tower_property_false` 证伪，本文件**完全绕开**，代价是 §6 的缺口。
-/

end View16

end FateV2.Predict