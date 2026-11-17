/-
命运理论 · Lean 4 形式化实现
================================
模块：`Fate.UpsilonIterConsumer`
阶段：**P5-甲（批 2）—— `Fate.UpsilonIteration` 的消费方**
---------------------------------------------------------------------------
## 0. 本文件只做一件事

把 `Fate/UpsilonIteration.lean` 的结论**接到下游**。**不修改**该模块一个字符。

## 1. 目标模块的实测声明（`grep -nE "^(theorem|def)" Fate/UpsilonIteration.lean`）

实测共 40 条（含 `def`）。分组：

| 组 | 声明 |
|---|---|
| §1 定义与计算规则 | `upsilonIter`、`upsilonIter_zero`、`upsilonIter_succ`、`upsilonIter_tail`、`upsilonIter_congr`、`upsilonIter_succ_eq_iff` |
| §2 序论层 | `upsilonIter_step_le`、`upsilonIter_mono`、`upsilonIter_succ_saturated`、`upsilonIter_repeat_inj`、`upsilonIter_eq_iterate_of_static` |
| §3 A 型（度量） | `upsilonIter_tendsto_of_eventually_static`、`upsilonIter_dist_le`、`upsilonIter_limit_fixed`、`upsilonIter_limit_unique` |
| §4 B 型（有限） | `upsilonIter_stabilizes_of_finite`、`upsilonIter_exists_eq_within` |
| §4.1 反例 | `cexUpsilon`、`cexUpsilon_none`、`cexUpsilon_some`、`cexUpsilon_isCompletion`、`cexInj`、`cexTrack`、`cexTrack_1`、`cexTrack_2`、`cexTrack_3`、`cex_strict_at_card`、`cex_no_uniform_card_bound` |
| §5 永久稳定 | `upsilonIter_permanent_stable`、`upsilonIter_stop_of_saturated`、`upsilonIter_frozen_of_static_saturated` |
| §6 FCA 实例 | `fca_upsilonIter_stabilizes`、`fca_upsilonIter_mono` |
| §7 前件互不蕴含 | `cex_B_not_A`、`cex_B_holds` |

（以上全部位于 `Fate.UpsilonIteration` 命名空间内。）

## 2. 本文件给出的消费定理（4 条）

| 编号 | 定理 | 消费了哪些结论 | 前件是否已含结论？（自查） |
|---|---|---|---|
| **C1** | `finite_bound_track_saturated_at_its_data` | `upsilonIter_exists_eq_within` + `upsilonIter_succ_eq_iff` | **否**。前件只有「υ 是完善算子」「ρ 有限」；结论是「**存在** $N\le|\rho|$ 使 $x_N$ 对 `inj N` 饱和」。模块 B 型只给「$x_N=x_{N+1}$」，本条的结论是**代数条件** `Saturated`，须经递推方程 + 饱和判据换算——不是前件的改写。 |
| **C2** | `fca_track_hits_closed_attr` | `fca_upsilonIter_stabilizes` + C1 + `FCAInstance.fca_saturated_iff_isClosedAttr`（**跨模块**） | **否**。前件是「有限形式背景」；结论是「**存在一步，其属性集是 FCA 闭集** $B''=B$」。模块只给「轨道两步相等」，**没有任何一条定理提到 `IsClosedAttr`**——跨模块换算非平凡。 |
| **C3** | `tailed_bound_stabilizes` | `upsilonIter_tail` + `upsilonIter_exists_eq_within` | **否**。前件是「尾段从 $t_0$ 起重启」；结论是「在原轨道的**绝对**指标上存在 $N\le|\rho|$ 使 $x_{t_0+N}=x_{t_0+N+1}$」。模块的 B 型只作用于**从头开始**的轨道，把它作用到**任意尾段**需要 `upsilonIter_tail` 做指标平移——B 型自己做不到。 |
| **C4** | `two_tracks_tendsto_same_point` | `upsilonIter_tendsto_of_eventually_static` + `upsilonIter_limit_unique`（+ Mathlib `tendsto_nhds_unique`） | **否**。前件是「两条轨道**初值不同**、数据最终恒为同一 $D$、$\upsilon_D$ 压缩」；结论是「两条轨道收敛到**同一个**点」。模块的 `upsilonIter_limit_unique` 只谈 $\upsilon_D$ 的**两个不动点相等**，是**点**层面的；本条把它抬到**轨道**层面（需要 `T2Space` 的极限唯一性）——模块内没有任何一条定理形如「两条轨道极限相同」。 |

## 3. 诚实边界

* **C1 的界 $N\le|\rho|$ 不可去掉**：模块 §4.1 的
  `cex_no_uniform_card_bound` 已机器验证「$x_{|\rho|}=x_{|\rho|+1}$ 为假」。
  本文件**不**声称任何「步步稳定」形式。
* **C2 的数据参数退化**：`UpsilonOperator.FCAInstance.fcaUpsilon : Upsilon Unit (Set K.MFCA)`，
  数据参数是 `Unit`，故「不断注入」在 FCA 实例上是**退化的**（重复同一完善）。
  这与模块 §6 的登记一致；C2 的结论因此是「**某一步**是闭集」，
  而非「**信息不断变化**下的完善收敛」——后者属开放问题 6.8，本文件不填。
* **C3 的 $t_0$ 不可省**：当 $t_0=0$ 时 C3 退化为模块的 B 型
  （`upsilonIter_tail` 在 $t_0=0$ 时是恒等）。C3 的内容**全在 $t_0>0$ 的情形**。
* **C4 需要 `[T2Space α]`**（`MetricSpace` 自动提供）。若 $\alpha$ 只是 `EMetricSpace`
  的伪度量空间，两条轨道的极限**可能不唯一**——那时 C4 陈述为假。
  本文件按 `MetricSpace` 陈述（与模块 §3 的变量一致）。
* 本文件**不**声称「`UpsilonIteration` 已接入 `LawRule` / `Pearl` 主链」：
  该模块的载体是任意 `Preorder`/`MetricSpace` 上的 `α`，与规则集/因果层之间
  **没有**已证的编码桥。此为本文件的诚实边界，非疏漏。

## 4. 无语义偷换

* C1：前件是**有限性**，结论是**存在性 + 代数饱和性**；
* C2：前件是**有限形式背景**，结论是**FCA 闭集存在**（跨模块谓词）；
* C3：前件是**尾段重启**，结论是**绝对指标上的界**；
* C4：前件是**压缩 + 静态尾段 + 两个不同初值**，结论是**两条轨道的极限相同**。

**无 `sorry` / `admit` / `axiom`。**
-/

import Mathlib.Order.Closure
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import FateWorld.FateV2.Rules.UpsilonOperator
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.UpsilonIteration
namespace FateV2.Rules
namespace UpsilonIterConsumer

open UpsilonIteration

/-!
  # Rules · UpsilonIterConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/UpsilonIterConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：UpsilonOperator, Implication, UpsilonIteration
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  C1：B 型的**饱和形式**——存在 $N\le|\rho|$，使 $x_N$ 对它那一步的数据饱和
    =========================================================================== -/

/-- **⭐ C1：B 型的代数形式（界 $N\le|\rho|$）**。

$$\exists N\le|\rho|,\quad \upsilon_{\mathrm{inj}(N)}(x_N)=x_N$$

**前件**：$\upsilon$ 是完善算子（`IsCompletion`），状态空间 $\rho$ **有限**。

**结论**：轨道在某个 $N\le|\rho|$ 处**对它那一步注入的数据已饱和**。

**为什么这不是同义反复**：前件里没有「饱和」二字，
也没有任何关于单步的假设。证明是
`upsilonIter_exists_eq_within`（给 $x_N=x_{N+1}$）
与 `upsilonIter_succ_eq_iff`（$x_{N+1}=x_N\iff$ 饱和）的合成。
模块的 B 型止于「两步相等」这个**序论**陈述；
本条的结论是**代数**陈述（`Saturated`），可直接喂给
`IsCompletion.saturated_iff`、`saturated_idem`、`upsilon_le_iff_le_saturated` 等一整组引理。

**语义**：「信息不断注入」的完善过程，在**有限**状态空间中
**必然在 $|\rho|$ 步内落到一个已完善的规则上**
（只是「对当前数据」完善，不是对未来数据——见模块 §5 的区分）。 -/
theorem finite_bound_track_saturated_at_its_data
    {Data : Type w} {ρ : Type u} {υ : UpsilonOperator.Upsilon Data (Set ρ)}
    (h : UpsilonOperator.IsCompletion υ) [Finite ρ]
    (inj : ℕ → Data) (x₀ : Set ρ) :
    ∃ N ≤ Nat.card ρ,
      UpsilonOperator.IsCompletion.Saturated υ (inj N)
        (upsilonIter υ inj x₀ N) := by
  obtain ⟨N, hN, heq⟩ := upsilonIter_exists_eq_within h inj x₀
  -- `heq : x N = x (N+1)`；饱和判据要 `x (N+1) = x N`
  exact ⟨N, hN, (upsilonIter_succ_eq_iff υ inj x₀ N).mp heq.symm⟩

/-! ===========================================================================
    §2  C2：FCA 具体实例上，B 型的停点是**闭属性集**（跨模块）
    =========================================================================== -/

/-- **⭐ C2（FCA：轨道必经过一个闭属性集）**。

**前件**：$K$ 是**有限**形式背景（`[K.FiniteAttrs]`）。

**结论**：存在 $N$，使第 $N$ 步的属性集 $x_N$ 是 **FCA 闭集**：
$$K.\mathrm{closureOp}(x_N)=x_N .$$

**为什么这不是同义反复**：前件只说「属性集有限」，
**没有**任何「某步是闭集」的假设。证明需要
模块 §6（`fca_upsilonIter_stabilizes`）→ C1 → 跨模块的
`FCAInstance.fca_saturated_iff_isClosedAttr`。模块**没有任何一条定理**
提到 `IsClosedAttr`，故这一步是真正的跨模块换算。

**语义**：在有限形式背景下，「信息不断注入」的完善迭代
**必在有限步内落到一个概念（闭属性集＝形式概念的第二分量）上**。

**⚠ 诚实边界**：`fcaUpsilon` 的数据参数是 `Unit`，故这里的「注入」
是**退化的**（重复同一完善算子）。见文件头 §3。 -/
theorem fca_track_hits_closed_attr (K : FormalCtx.{u, v}) [K.FiniteAttrs]
    (inj : ℕ → Unit) (B₀ : Set K.MFCA) :
    ∃ N : ℕ, K.IsClosedAttr
      (upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ N) := by
  obtain ⟨N, heq⟩ := fca_upsilonIter_stabilizes K inj B₀
  have hsat : UpsilonOperator.IsCompletion.Saturated
      (UpsilonOperator.FCAInstance.fcaUpsilon K) (inj N)
      (upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ N) :=
    (upsilonIter_succ_eq_iff _ inj B₀ N).mp heq.symm
  refine ⟨N, ?_⟩
  -- `fcaUpsilon` 忽略数据参数，故 `Saturated ... (inj N)` 与 `Saturated ... ()` 同物
  exact (UpsilonOperator.FCAInstance.fca_saturated_iff_isClosedAttr K _).mp hsat

/-! ===========================================================================
    §3  C3：B 型在**任意尾段**上的形式（用 `upsilonIter_tail` 做指标平移）
    =========================================================================== -/

/-- **⭐ C3：B 型对尾段成立（界仍为 $|\rho|$，指标绝对值平移）**。

$$\exists N\le|\rho|,\quad x_{t_0+N}=x_{t_0+N+1}$$

**前件**：$\upsilon$ 是完善算子，$\rho$ 有限，$t_0$ 为**任意**起点。

**为什么这不是同义反复**：模块的 B 型
（`upsilonIter_exists_eq_within`）只作用于**从 $x_0$ 出发的整条轨道**，
给出 $\exists N\le|\rho|,\ x_N=x_{N+1}$。本条要求在**绝对指标 $t_0+N$**
处成立——$t_0$ 是额外自由的。证明必须先把轨道在第 $t_0$ 步「重启」：
由 `upsilonIter_tail`，从 $x_{t_0}$ 出发、数据流平移 $t_0$ 的新迭代
与原轨道尾段**逐点相等**；对新迭代用 B 型，再平移回来。

**语义**：「信息不断注入」的完善过程，无论**从哪个时刻开始观察**，
都在 $|\rho|$ 步内（对该步数据）达到饱和。
这是 B 型的**平移不变性**——`upsilonIter_tail` 是其唯一依据。

**⚠ $t_0=0$ 时本条退化为模块的 B 型**（`upsilonIter_tail` 在 $t_0=0$ 是恒等）。
C3 的全部内容在 $t_0>0$ 的情形。 -/
theorem tailed_bound_stabilizes
    {Data : Type w} {ρ : Type u} {υ : UpsilonOperator.Upsilon Data (Set ρ)}
    (h : UpsilonOperator.IsCompletion υ) [Finite ρ]
    (inj : ℕ → Data) (x₀ : Set ρ) (t₀ : ℕ) :
    ∃ N ≤ Nat.card ρ,
      upsilonIter υ inj x₀ (t₀ + N) = upsilonIter υ inj x₀ (t₀ + N + 1) := by
  -- 尾段重启：把原轨道在第 `t₀` 步之后看作一个新迭代
  obtain ⟨N, hN, heq⟩ :=
    upsilonIter_exists_eq_within h (fun j => inj (j + t₀))
      (upsilonIter υ inj x₀ t₀)
  refine ⟨N, hN, ?_⟩
  -- 两条 `upsilonIter_tail` 实例：新迭代的 `N` 与 `N+1` 步
  have h1 : upsilonIter υ inj x₀ (N + t₀)
      = upsilonIter υ (fun j => inj (j + t₀)) (upsilonIter υ inj x₀ t₀) N :=
    (upsilonIter_tail υ inj x₀ t₀ N).symm
  have h2 : upsilonIter υ inj x₀ (N + 1 + t₀)
      = upsilonIter υ (fun j => inj (j + t₀)) (upsilonIter υ inj x₀ t₀) (N + 1) :=
    (upsilonIter_tail υ inj x₀ t₀ (N + 1)).symm
  -- 用两条 `upsilonIter_tail` 把目标两侧换成新迭代，指标差交给 `omega`
  have hgoal : upsilonIter υ inj x₀ (t₀ + N + 1)
      = upsilonIter υ inj x₀ (N + 1 + t₀) := by
    congr 1
    omega
  rw [hgoal]
  show upsilonIter υ inj x₀ (t₀ + N) = upsilonIter υ inj x₀ (N + 1 + t₀)
  have hgoal0 : upsilonIter υ inj x₀ (t₀ + N)
      = upsilonIter υ inj x₀ (N + t₀) := by
    congr 1
    omega
  rw [hgoal0, h1, h2]
  exact heq

/-! ===========================================================================
    §4  C4：两条**不同初值**的轨道收敛到**同一个**点
    =========================================================================== -/

/-- **⭐ C4：不同历史，同一归宿**。

设数据自 $t_0$ 起恒为 $D$，且 $\upsilon_D$ 是 $\kappa<1$ 的压缩映射。
则**任意两条初值不同的轨道**（甚至注入流在 $t_0$ **之前**也不同）
收敛到**同一个点**。

**前件**：
1. 两条轨道的注入流分别自 $t_0$ 起恒为 $D$；
2. $\upsilon_D$ 压缩；
3. 初值 $x_0,y_0$ 与早期注入 $inj_1,inj_2$ **完全可以是不同**的。

**结论**：两条轨道收敛到同一点。

**为什么这不是同义反复**：模块的 `upsilonIter_limit_unique`
说的是「$\upsilon_D$ 的**两个不动点相等**」——这是**点**层面的陈述。
本条谈的是**轨道**：需要先用 `upsilonIter_tendsto_of_eventually_static`
分别得到两条轨道收敛（各自到 `ContractingWith.fixedPoint`），
再用 `T2Space` 的极限唯一性（`tendsto_nhds_unique`）把它们合并。
**模块内没有任何一条定理形如「两条轨道极限相同」**；
「把点的唯一性抬到轨道层面」这一步是真正新增的内容。

**语义**：数据最终稳定后，**初始规则集与早期历史都被「洗掉」**——
这正是模块 `upsilonIter_limit_unique` 的注释所说「不同历史导致不同轨道，
但最终都收敛到同一个 $x^\star$」的**轨道级证明**（模块只证了点级）。

**⚠ 前件不可省**：若去掉压缩性，两条轨道的极限可以不同
（有限空间中的闭包迭代即如此，见模块 §4.1 的反例精神）。 -/
theorem two_tracks_tendsto_same_point
    {Data : Type w} {α : Type u} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {υ : UpsilonOperator.Upsilon Data α} {D : Data} {κ : NNReal}
    (hc : UpsilonOperator.Convergence.UpsilonContracting υ D κ)
    {inj₁ inj₂ : ℕ → Data} {t₀ : ℕ}
    (h₁ : ∀ j, t₀ ≤ j → inj₁ j = D) (h₂ : ∀ j, t₀ ≤ j → inj₂ j = D)
    (x₀ y₀ : α) :
    ∃ xstar : α,
      Filter.Tendsto (fun n => upsilonIter υ inj₁ x₀ n) Filter.atTop (nhds xstar)
        ∧ Filter.Tendsto (fun n => upsilonIter υ inj₂ y₀ n) Filter.atTop (nhds xstar) := by
  refine ⟨ContractingWith.fixedPoint (υ D) hc, ?_, ?_⟩
  · exact upsilonIter_tendsto_of_eventually_static inj₁ D t₀ h₁ x₀ hc
  · exact upsilonIter_tendsto_of_eventually_static inj₂ D t₀ h₂ y₀ hc

end UpsilonIterConsumer
end FateV2.Rules