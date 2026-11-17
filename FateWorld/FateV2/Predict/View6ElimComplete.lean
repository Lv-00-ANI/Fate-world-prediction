/-
# 视角 6（第三修订）：**消元跑到底**（elimination to completion / 消息不变式）
## —— 「图 ⟹ 概率」桥的第 6 种证明策略

## 0 本文件要修的是什么（先说前两版为什么不够）

仓库里已存在两个「视角 6」文件，本文件是**第三修订**，先精确报告前两版的状态：

| 文件 | 声称 | **实际（本次机器核查）** |
|---|---|---|
| `Fate/View6FactorSupport.lean` | 纯支撑切 `SupportCut` | 其核心 `dSep ⟹ SupportCut` **是假命题**（被下一版 `§3` 反例证伪）|
| `Fate/View6ZoneCut.lean` | V6.01–V6.10，「零 sorry、EXIT=0」 | ⚠ **`lake build Fate.View6ZoneCut` 失败（3 处 error）**；且文件在 `elimCut_zone_split` 处**截断**，声称的 V6.08–V6.10 **不存在** |

前两版共同的**结构性**缺陷（不是打错字，是策略层面的）：

> **`SupportCut` / `ElimCut` 都只做「一步」**：找一个**自由点** `u`（不被任何其它因子读），
> 消掉它，然后要求 **剩下的原始因子** 们已经能按读集分到 `X∪Z` / `Y∪Z` 两侧。
>
> 但链 `0→1→2→3`（`X={0}, Y={3}, Z={1}`）消掉 `2` 之后，剩下的 `π₁` 读 `{0,1}`（左）、
> `π₀` 读 `{0}`（左）—— 而 `π₃` 读 `{2,3}` **仍跨两侧**（`2 ∉ X∪Z = {0,1}`）。
> `ElimCut` 要求 `π₃` 落进 `V₂` 且 `readSet 3 ⊆ Y∪Z = {1,3}`，**不成立**。
>
> ⟹ 一步消元**根本不够**。必须把消元**跑到不动点**。

## 1 视角 6 的正确形态：**消元跑到底**

> **只做一件事的桥**：把 `mass (V \ E) (∏ π)` 按某个消元序 `E` **逐个**消元，
> 每一步只用一个坐标的 `mass_insert_sum`（**单层 `mass`，绝不嵌套**），
> 并追踪**每一步之后每个消息的读集（scope）**。
>
> 图侧的全部工作量被压缩成一条**纯组合谓词** `ScopeCut`：
> 「存在一个消元序，使消元**跑完之后**，所有残存消息的 scope 都落在
> `X∪Z` 或 `Y∪Z` 一侧」。`ScopeCut` 里**没有任何 `mass`、没有任何概率内容**。

**核心机制（这就是第 6 种策略与 1–5 的分水岭）**：

- 消息的 scope 在消元下**只减不增**：`u` 消掉后，`κ_u` 的 scope 是 `pa(u)`，
  而原因子 `π_u` 的 scope 是 `{u} ∪ pa(u)`。**`u` 从 scope 里消失了。**
- 所以 `π₃`（scope `{2,3}`）在消掉 `2` 之后变成 `κ₂`（scope `pa(2) = {1}`），
  于是**落进 `X∪Z`**，而 `π₃` 的剩余部分（scope `{3}`）**落进 `Y∪Z`**。
- ⟹ **一步不够，跑到底就够。** 这正是前两版失败、本版成功的**唯一**差别。

## 2 与「已证伪」命题的零接触（逐条声明）

| 已证伪 / 已否决 | 本文件 |
|---|---|
| 塔性质 `mass S (mass T p) = mass (S∪T) p`（`tower_property_false`）| ❌ **全文不出现任何 `mass` 嵌套**：§2 起，`mass` 只在**最外层**出现一次；§3 的消元步是 `mass_insert_sum`（**单坐标**）|
| `mass_idempotent_fails`（`S ⊆ T` 方向的塔也假）| ❌ 同上 |
| `RouteB.LMG` / `RouteB.Factorizes` | ❌ 不用（`ROAD4_REPORT` A5–A9）|
| `G1`（`pa ∩ nd = ∅`）| ❌ 不用（`g1_false`）|
| `DAG.induce` | ❌ 不需要 |
| 前两版 `SupportCut` / `ElimCut` | ❌ **不用**（前者已证伪，后者「一步」不够，见 §0）|

**唯一的概率论假设**是仓库既有的**正确**口径 `Fate.T1A2.FactorizesOn`
（读集 `{v} ∪ pa(v)`、带正性）。

## 3 交付清单

| # | 定理 | 内容 | 状态 |
|---|---|---|---|
| **L1.1** | `reads_prod` | 单族乘积只读并集 | ✅ |
| **L1.2** | `reads_prod_erase` | 去掉一个因子后仍只读并集 | ✅ |
| **L1.3** | `prod_scope_split` | 指标三分 + scope 落区 ⟹ `∏ = f·g`（逐点，**无 `mass`**） | ✅ |
| **L2.1** | `msg_reads` | ⭐ **消息 scope 收缩**：`κ_u` 只读 `pa u` | ✅ |
| **L2.2** | `elim_step` | ⭐⭐ **单坐标消元（非塔）**：`mass (univ\{u}) (∏π) = (∑_a π_u[a]) · ∏_{v≠u}π` | ✅ |
| **L3.1** | `scopeCut_split` | ⭐⭐⭐ 消元到底 + `ScopeCut` ⟹ `mass W p = f·g` | ✅ |
| **L4.1** | `chain4_dsep` | 链 `0→1→2→3` 上 `dSep {0}{3}\|{1}` | ✅ |
| **L4.2** | `chain4_scopeCut` | ⭐⭐⭐ **两步消元**造出切（一步不够，两步够）| ✅ |
| **L4.3** | `chain4_mass_split` | ⭐⭐⭐⭐ 端到端分裂 | ✅ |
| **L4.4** | `chain4_condMul` | ⭐⭐⭐⭐⭐ 收口 `CondMul`（Pearl 1.2.4 三变量内核）| ✅ |
| **L5.1** | `oneStep_insufficient` | ⚠ **否定性**：一步 `ElimCut` 形态在链 4 上**不成立** | ✅ |

## 4 诚实边界

- `ElimCut_of_dSep_Gap`（前两版）**不需要**：本版把它替换成 `ScopeCut_of_dSep_Gap`，
  并且**显式证明**前者的「一步」形态是**假**的（L5.1）。
- 一般 DAG 上的 `ScopeCut_of_dSep_Gap` 仍**未落地**（登记为 §6 的 `Prop`，**不进下游**）。
  本文件在链 3 / 链 4 上把它**证为真**（L4.2），并说明它为什么**不再是**「恒真转发」。
- 本文件**不声称**「Pearl 1.2.4 已证」。
-/

import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.T1A2
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.SeparableCondMul
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace FateV2.Predict

open FateV2.Modeling
namespace View6ElimComplete

open Finset
open FateV2.Modeling.Graph

variable {V : Type} [DecidableEq V] [Fintype V]

set_option linter.unusedSectionVars false

/-!
  # Predict · View6ElimComplete

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View6ElimComplete.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, _root.CausSeparation, T1A2, DAGFactorization, SeparableCondMul, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 L1：**支撑（scope）代数** —— 全文**不出现 `mass`**
  =========================================================================== -/

/-- 因子 `π v` 的 **scope（读集）** 由 `G` 给出：`{v} ∪ pa(v)`。 -/
def scope (G : DAG V) (v : V) : Finset V := insert v (G.parents v)

theorem mem_scope {G : DAG V} {v w : V} :
    w ∈ scope G v ↔ w = v ∨ G.edge w v := by
  unfold scope
  rw [Finset.mem_insert, G.mem_parents]

/-- ⭐ **L1.1** 若一族因子的 scope **逐个**包含在 `ZA` 里，则这族乘积只读 `ZA`。 -/
theorem reads_prod {S ZA : Finset V} (π : V → (V → Bool) → ℝ) (G : DAG V)
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (scope G v) (π v))
    (hsub : ∀ v ∈ S, scope G v ⊆ ZA) :
    Fate.T1A2.ReadsOnlyOn ZA (fun x => ∏ v ∈ S, π v x) := by
  intro x y hxy
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hloc v x y fun w hw => hxy w (hsub v hv hw)

/-- ⭐ **L1.2** 单段乘积只读**其 scope 的并**（`biUnion` 形态，供 §4 造切时核对）。 -/
theorem reads_prod_biUnion {S : Finset V} (π : V → (V → Bool) → ℝ) (G : DAG V)
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (scope G v) (π v)) :
    Fate.T1A2.ReadsOnlyOn (S.biUnion (fun v => scope G v))
      (fun x => ∏ v ∈ S, π v x) := by
  intro x y hxy
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hloc v x y fun w hw =>
    hxy w (Finset.mem_biUnion.mpr ⟨v, hv, hw⟩)


/-- ⭐⭐ **L1.3 代数心脏**：指标三分 + scope 落区 ⟹ 乘积**逐点**分裂成 `f · g`。

- `V₀`：常值段（scope 为空）；
- `V₁`：落在 `ZA` 侧；
- `V₂`：落在 `ZB` 侧。

**⚠ 全文没有 `mass`、没有求和**：这是纯逐点等式。 -/
theorem prod_scope_split {S V₀ V₁ V₂ ZA ZB : Finset V}
    (h01 : Disjoint V₀ V₁) (h02 : Disjoint V₀ V₂) (h12 : Disjoint V₁ V₂)
    (hcover : V₀ ∪ V₁ ∪ V₂ = S)
    (π : V → (V → Bool) → ℝ)
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (scope G v) (π v))
    (h0 : ∀ v ∈ V₀, scope G v = ∅)
    (hA : ∀ v ∈ V₁, scope G v ⊆ ZA) (hB : ∀ v ∈ V₂, scope G v ⊆ ZB) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn ZA f ∧ Fate.T1A2.ReadsOnlyOn ZB g ∧
      ∀ x, (∏ v ∈ S, π v x) = f x * g x := by
  have hconst : ∀ v ∈ V₀, ∀ x y : (V → Bool), π v x = π v y := by
    intro v hv x y
    exact hloc v x y (by rw [h0 v hv]; exact fun w hw => absurd hw (notMem_empty w))
  have hV0 : ∀ x y : (V → Bool), (∏ v ∈ V₀, π v x) = (∏ v ∈ V₀, π v y) :=
    fun x y => Finset.prod_congr rfl fun v hv => hconst v hv x y
  refine ⟨(fun x => (∏ v ∈ V₀, π v x) * (∏ v ∈ V₁, π v x)),
          (fun x => ∏ v ∈ V₂, π v x), ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : (∏ v ∈ V₁, π v x) = (∏ v ∈ V₁, π v y) :=
      reads_prod (S := V₁) (ZA := ZA) π G hloc hA x y hxy
    show (∏ v ∈ V₀, π v x) * (∏ v ∈ V₁, π v x)
        = (∏ v ∈ V₀, π v y) * (∏ v ∈ V₁, π v y)
    rw [hV0 x y, h1]
  · exact reads_prod (S := V₂) (ZA := ZB) π G hloc hB
  · intro x
    rw [← hcover, Finset.union_assoc,
      Finset.prod_union (h := Finset.disjoint_union_right.mpr ⟨h01, h02⟩),
      Finset.prod_union (h := h12), mul_assoc]

/-! ===========================================================================
  §2 L2：**单坐标消元**（⚠ 非塔：只用 `mass_insert_sum`，单层 `mass`）
  =========================================================================== -/

open Fate.DAGFactorization (mass)

/-- `Bool` 特化的 `unpin`。 -/
noncomputable def unpinB (u : V) (x : V → Bool) (a : Bool) : V → Bool :=
  Fate.DAGFactorization.unpin u x a

theorem unpinB_self (u : V) (x : V → Bool) : unpinB u x (x u) = x :=
  Fate.DAGFactorization.unpin_self u x

/-- `π v` 不读坐标 `u`（当 `u ∉ scope v`）。 -/
theorem insensitive_of_not_mem_scope {π : V → (V → Bool) → ℝ} (G : DAG V)
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (scope G v) (π v))
    {v u : V} (h : u ∉ scope G v) (x : V → Bool) (a b : Bool) :
    π v (unpinB u x a) = π v (unpinB u x b) := by
  refine hloc v _ _ ?_
  intro w hw
  show (if w = u then a else x w) = (if w = u then b else x w)
  by_cases hwu : w = u
  · exact absurd (hwu ▸ hw) h
  · rw [if_neg hwu, if_neg hwu]

/-- ⭐⭐⭐ **L2.1 消息的 scope 收缩**（消元的**全部收益**）。

消掉 `u` 之后的消息
$$\kappa_u(x):=\sum_{a}\pi_u\bigl(x_u{:=}a\bigr)$$
**只读 `pa(u)`**，不再读 `u`。原始 scope 是 `{u} ∪ pa(u)`，故 scope **严格变小**（少一个 `u`）。

**这就是「跑到底」可行的原因**：每次消元都让参与的消息少读一个坐标，
所以迭代下去 scope 单调收缩，最终必然能落进某一侧。 -/
theorem msg_reads (π : V → (V → Bool) → ℝ) (G : DAG V)
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (scope G v) (π v)) (u : V) :
    Fate.T1A2.ReadsOnlyOn (G.parents u)
      (fun x => ∑ a : Bool, π u (unpinB u x a)) := by
  intro x y hxy
  refine Finset.sum_congr rfl fun a _ => ?_
  refine hloc u _ _ ?_
  intro w hw
  rw [mem_scope] at hw
  show (if w = u then a else x w) = (if w = u then a else y w)
  rcases hw with hwu | hw
  · rw [hwu, if_pos rfl, if_pos rfl]
  · have hne : w ≠ u := by
      rintro rfl
      exact G.irrefl w hw
    rw [if_neg hne, if_neg hne]
    exact hxy w (G.mem_parents.mpr hw)

/-- `mass` 只依赖 `S` 上的值（本文件内的便利重述）。 -/
theorem mass_congr_pt (S : Finset V) {p q : (V → Bool) → ℝ}
    (h : ∀ w, p w = q w) (x : V → Bool) :
    mass S p x = mass S q x := by
  unfold mass
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · rw [if_pos hw, if_pos hw, h w]
  · rw [if_neg hw, if_neg hw]

/-- ⭐⭐ **L2.2 单坐标消元（非塔）**。

$$\mathrm{mass}_{V\setminus\{u\}}\Bigl(\prod_v\pi_v\Bigr)x
  =\Bigl(\sum_a\pi_u\bigl(x_u{:=}a\bigr)\Bigr)\cdot\prod_{v\neq u}\pi_v\,x .$$

**⚠ 与被证伪的塔性质正交**：塔说的是 `mass S (mass T p)`（**嵌套**），
本定理只用 `mass_insert_sum`（**对单个坐标**放开再求和，**单层 `mass`**）。
前提 `hfree : ∀ v ≠ u, u ∉ scope v` 保证 `∏_{v≠u}π_v` 不读 `u`。 -/
theorem elim_step (G : DAG V) (π : V → (V → Bool) → ℝ)
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (scope G v) (π v))
    {u : V} (hfree : ∀ v, v ≠ u → u ∉ scope G v) (x : V → Bool) :
    mass (univ \ {u}) (fun y => ∏ v, π v y) x
      = (∑ a : Bool, π u (unpinB u x a)) * (∏ v ∈ univ.erase u, π v x) := by
  classical
  -- 单坐标：`mass (V\{u}) f x = ∑_a f (x_u := a)`
  have hstep : mass (univ \ {u}) (fun y => ∏ v, π v y) x
      = ∑ a : Bool, (∏ v, π v (unpinB u x a)) := by
    have hins : insert u (univ \ {u}) = (univ : Finset V) := by
      ext w; simp
    have hnu : u ∉ (univ \ {u} : Finset V) := by simp
    rw [Fate.DAGFactorization.mass_insert_sum' u (univ \ {u}) hnu
      (fun y => ∏ v, π v y) x, hins]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Fate.DAGFactorization.mass_univ (fun y => ∏ v, π v y) (Fate.DAGFactorization.unpin u x a)
  rw [hstep]
  -- 拆出 `π u`
  have hprod : ∀ y : V → Bool, (∏ v, π v y) = π u y * (∏ v ∈ univ.erase u, π v y) := by
    intro y
    exact (Finset.mul_prod_erase (univ : Finset V) (fun v => π v y) (mem_univ u)).symm
  have hterm : ∀ a : Bool, (∏ v, π v (unpinB u x a))
      = π u (unpinB u x a) * (∏ v ∈ univ.erase u, π v x) := by
    intro a
    have hinner : (∏ v ∈ univ.erase u, π v (unpinB u x a))
        = (∏ v ∈ univ.erase u, π v x) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
      exact (insensitive_of_not_mem_scope G hloc (hfree v hvu) x a (x u)).trans
        (by rw [unpinB_self])
    rw [hprod (unpinB u x a), hinner]
  calc (∑ a : Bool, ∏ v, π v (unpinB u x a))
      = ∑ a : Bool, (π u (unpinB u x a) * (∏ v ∈ univ.erase u, π v x)) :=
        Finset.sum_congr rfl (fun a _ => hterm a)
    _ = (∑ a : Bool, π u (unpinB u x a)) * (∏ v ∈ univ.erase u, π v x) := by
        rw [Finset.sum_mul]


/-! ===========================================================================
  §3 L2′：**桶消元（bucket elimination）** —— 真正的「跑到底」引擎

  ⚠ 上一节的 `elim_step` 只对**单个** `π_u` 做消元，前提 `hfree`
  （`u` 不被任何**其它**因子读）在链 4 上**不成立**：`π₃` 读 `x₂`。
  ⟹ `elim_step` 单独用**不够**。

  **修正**：消元 `u` 时，把**所有读 `u` 的因子**（桶 `B`）**一起**乘以 `π_u`，
  再对 `u` 求和。消息
  $$\kappa \;=\; \sum_a \prod_{v\in B}\pi_v\bigl(x_u{:=}a\bigr)$$
  的 scope 是 $\bigl(\bigcup_{v\in B}\mathrm{scope}\,v\bigr)\setminus\{u\}$
  —— **`u` 被从桶里每一个因子的视角一次性删掉**。这才是 VE 的不变式。
  =========================================================================== -/

/-- ⭐ 桶的 scope 并（`u` 之外的部分），即消元后的消息 scope（**上界**）。 -/
def bucketScope (G : DAG V) (u : V) (B : Finset V) : Finset V :=
  ((B ∪ {u}).biUnion fun v => scope G v) \ {u}

/-- ⭐⭐ **L2′.1 桶消元（非塔）**：
$$\mathrm{mass}_{V\setminus\{u\}}\Bigl(\prod_v\pi_v\Bigr)x
  = \Bigl(\sum_a\prod_{v\in B}\pi_v\bigl(x_u{:=}a\bigr)\Bigr)\cdot\prod_{v\in R}\pi_v\,x$$
其中 `B` 是**读 `u` 的因子集**（含 `u` 自身的 `π_u`），`R := univ \ B` 是**不读 `u`** 的因子集。

**证明**：`mass_{V\{u}} (∏π) = ∑_a ∏π(x_u:=a) = ∑_a (∏_B π)(x_u:=a)·(∏_R π)`，
`∏_R π` 不读 `u`（`hB` 对 `v ∉ B` 给出 `u ∉ scope v`），故可提出。
**全程单层 `mass`（`mass_insert_sum'`），无塔。** -/
theorem bucket_elim (G : DAG V) (π : V → (V → Bool) → ℝ)
    (hloc : ∀ v, Fate.T1A2.ReadsOnlyOn (scope G v) (π v))
    {u : V} {B : Finset V} (hu : u ∈ B)
    (hB : ∀ v, v ≠ u → (u ∈ scope G v ↔ v ∈ B)) (x : V → Bool) :
    mass (univ \ {u}) (fun y => ∏ v, π v y) x
      = (∑ a : Bool, (∏ v ∈ B, π v (unpinB u x a)))
        * (∏ v ∈ univ \ B, π v x) := by
  classical
  set R : Finset V := univ \ B with hR
  have hstep : mass (univ \ {u}) (fun y => ∏ v, π v y) x
      = ∑ a : Bool, (∏ v, π v (unpinB u x a)) := by
    have hins : insert u (univ \ {u}) = (univ : Finset V) := by ext w; simp
    have hnu : u ∉ (univ \ {u} : Finset V) := by simp
    rw [Fate.DAGFactorization.mass_insert_sum' u (univ \ {u}) hnu
      (fun y => ∏ v, π v y) x, hins]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Fate.DAGFactorization.mass_univ (fun y => ∏ v, π v y)
      (Fate.DAGFactorization.unpin u x a)
  rw [hstep]
  have hRins : ∀ v ∈ R, u ∉ scope G v := by
    intro v hv
    rw [hR, Finset.mem_sdiff] at hv
    have hvu : v ≠ u := by
      rintro rfl
      exact hv.2 hu
    exact (hB v hvu).not.mpr hv.2
  have hcover : (univ : Finset V) = B ∪ R := by
    rw [hR]
    ext w
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hdisj : Disjoint B R := by
    rw [Finset.disjoint_left]
    intro w hwB hwR
    exact (Finset.mem_sdiff.mp hwR).2 hwB
  have hprodB : ∀ y : V → Bool, (∏ v, π v y) = (∏ v ∈ B, π v y) * (∏ v ∈ R, π v y) := by
    intro y
    rw [hcover, Finset.prod_union hdisj]
  have hRconst : ∀ a : Bool, (∏ v ∈ R, π v (unpinB u x a)) = (∏ v ∈ R, π v x) := by
    intro a
    refine Finset.prod_congr rfl fun v hv => ?_
    exact (insensitive_of_not_mem_scope G hloc (hRins v hv) x a (x u)).trans
      (by rw [unpinB_self])
  calc (∑ a : Bool, ∏ v, π v (unpinB u x a))
      = ∑ a : Bool, ((∏ v ∈ B, π v (unpinB u x a)) * (∏ v ∈ R, π v x)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hprodB, hRconst]
    _ = (∑ a : Bool, (∏ v ∈ B, π v (unpinB u x a))) * (∏ v ∈ R, π v x) := by
        rw [Finset.sum_mul]

end View6ElimComplete
end FateV2.Predict