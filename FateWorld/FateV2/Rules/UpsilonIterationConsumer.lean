/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.UpsilonIterationConsumer`
阶段：**P5-甲（批 1）—— `Fate.UpsilonIteration` 的消费方**

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
`Fate.UpsilonIteration` 给出了「信息不断注入」下的 υ 迭代
$x_{t+1}=\upsilon_{\mathrm{inj}(t)}(x_t)$，以及两条**互不替代**的收敛定理：

* **A 型**（度量 + 压缩 + 数据最终恒定）⟹ 收敛到唯一不动点，带几何速率；
* **B 型**（只要状态空间有限高度）⟹ 有限步无增益，无度量、无压缩、无数据规律。

本文件**不修改**该模块一个字符，只把它的结论**接到下游**：
把 A 型、B 型与「饱和判据」「永久稳定」「FCA 闭属性集」**组合**，
得到 4 条该模块中**不存在**的定理。

---------------------------------------------------------------------------
目标模块的实测声明（`grep -nE "^(theorem|def)" Fate/UpsilonIteration.lean`）
---------------------------------------------------------------------------
| 类别 | 声明 |
|---|---|
| 定义 | `upsilonIter` |
| §1 计算 | `upsilonIter_zero` `upsilonIter_succ` `upsilonIter_tail` `upsilonIter_congr` `upsilonIter_succ_eq_iff` |
| §2 序论 | `upsilonIter_step_le` `upsilonIter_mono` `upsilonIter_succ_saturated` `upsilonIter_repeat_inj` |
| §3 A 型 | `upsilonIter_eq_iterate_of_static` `upsilonIter_tendsto_of_eventually_static` `upsilonIter_dist_le` `upsilonIter_limit_fixed` `upsilonIter_limit_unique` |
| §4 B 型 | `upsilonIter_stabilizes_of_finite` `upsilonIter_exists_eq_within` |
| §4.1 反例 | `cexUpsilon` `cexUpsilon_none` `cexUpsilon_some` `cexUpsilon_isCompletion` `cexInj` `cexTrack` `cexTrack_1` `cexTrack_2` `cexTrack_3` `cex_strict_at_card` `cex_no_uniform_card_bound` |
| §5 稳定 | `upsilonIter_permanent_stable` `upsilonIter_stop_of_saturated` `upsilonIter_frozen_of_static_saturated` |
| §6 FCA | `fca_upsilonIter_stabilizes` `fca_upsilonIter_mono` |
| §7 分离 | `cex_B_not_A` `cex_B_holds` |

（以上全部位于 `Fate.UpsilonIteration` 命名空间内；`cexUpsilon` 等经
`open Fate.UpsilonIteration` 后可直接引用。）

---------------------------------------------------------------------------
⚠⚠ 同义反复自检（纪律 7：逐条核对「前件是否已把结论包进去」）
---------------------------------------------------------------------------
| # | 定理 | 前件 | 结论 | 判定 |
|---|---|---|---|---|
| **C1** | `finite_track_hits_saturated_at_its_data` | `IsCompletion υ` + `[Finite ρ]` | `∃ N ≤ Nat.card ρ, Saturated υ (inj N) (x_N)` | **否**。前件**完全不提「饱和」**；结论是「**某一步**的状态对它**该步**的数据饱和」。需 B 型（只给 $x_N=x_{N+1}$）与饱和判据**两次独立调用**、再取逆。模块里**没有**这条：模块只给 $\exists N,\ x_N=x_{N+1}$ 这个**相等**，从未换写成 `Saturated`。 |
| **C2** | `fca_track_stabilizes_at_closed_attr` | `[K.FiniteAttrs]` | `∃ N, K.IsClosedAttr (x_N)` | **否**。前件只有「属性集有限」；结论是「**存在某一步的属性集是 FCA 闭集**」。需 §6 B 型 + 饱和判据 + **跨模块**的 `fca_saturated_iff_isClosedAttr` 三步。模块的 `fca_upsilonIter_stabilizes` 只给相等，**不**给闭集判定。 |
| **C3** | `tracks_close_under_contracting` | 压缩性 + 数据自 $t_0$ 起恒定 | 两条**不同初值**轨道的距离 $\le$ 两个「启动距离」各乘 $\kappa^k/(1-\kappa)$ 之和 | **否**。`upsilonIter_dist_le` 只给**单条**轨道到不动点的界；本条用**三角不等式**把**两条**轨道各自的界拼起来，是模块中**没有的双轨道**陈述；前件不含任何「两轨道接近」的内容。 |
| **C4** | `finite_static_tail_eventually_frozen` | `IsCompletion υ` + `[Finite ρ]` + **数据自 $t_0$ 起恒定** | `∃ N ≤ Nat.card ρ, ∀ k, x_{(t_0+N)+k} = x_{t_0+N}` | **否**。这是把 **B 型（有限高度）** 与 **§5 永久稳定** 真正接起来：模块头表明写 B 型**不保证永久稳定**，本条用「数据恒定」补上缺口得**永久冻结**。前件的「有限」与「恒定」是**两个独立**假设，结论（对**一切** $k$ 冻结）严格多于任一支。 |

**结论**：4 条**无一条**把结论塞进前件。

---------------------------------------------------------------------------
诚实边界（如实登记）
---------------------------------------------------------------------------
1. **零 `sorry` / 零 `admit` / 零 `axiom`**。
2. 本文件**不**声称证明了任何**新**的收敛定理——收敛定理全部来自目标模块。
   本文件的贡献**仅在于组合与换写**，且组合的每一步都在上表中标出。
3. **C4 的前件「数据自 $t_0$ 起恒定」不可省**：模块 §4 头表明确说 B 型单独
   **不保证永久稳定**（第 $N+1$ 步若注入不同数据仍可撑大状态）。C4 **不**主张
   「有限高度 ⟹ 永久稳定」，只主张「有限高度 + 常尾 ⟹ 永久稳定」。
4. **C2 的 `inj : ℕ → Unit` 是退化的**（`fcaUpsilon` 的数据参数是 `Unit`），
   这与模块 §6 的诚实边界一致：真正「数据在变」的 FCA 情形属开放问题 6.8，本文件不填。
5. 本文件**不**声称「`UpsilonIteration` 已接入 `LawRule` / `Pearl` 主链」——
   `UpsilonIteration` 是**迭代层**的一般结论，其载体是任意的 `Preorder`/`MetricSpace` 上的 `α`，
   与 `LawRule` 的概率核载体**不同类型**，故**不存在**可写的直连定理；
   本文件据实选择**不**伪造这样的连接。
-/

import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Linarith
import FateWorld.FateV2.Rules.UpsilonIteration
import FateWorld.FateV2.Rules.UpsilonOperator
import FateWorld.FateV2.Rules.Implication
namespace FateV2.Rules
namespace UpsilonIterationConsumer

open UpsilonIteration Filter

/-!
  # Rules · UpsilonIterationConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/UpsilonIterationConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：UpsilonIteration, UpsilonOperator, Implication
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  C1：B 型（有限高度）**换写**为「某一步的状态对该步数据饱和」
    ===========================================================================

B 型定理 `upsilonIter_exists_eq_within` 只断言
$$\exists N\le|\rho|,\quad x_N=x_{N+1}.$$
而 `upsilonIter_succ_eq_iff` 说
$$x_{N+1}=x_N\iff \text{Saturated}\ \upsilon_{\mathrm{inj}(N)}\ x_N .$$
把两者合成，得到 B 型的**饱和形式**——这是模块里**没有**的表述，
且正是「何时可以停」的判据在 B 型前件下的落点。 -/

/-- **⭐ C1（B 型 ⟹ 某一步已饱和）**。

**前件**：υ 是完善的（`IsCompletion`）+ 状态空间**有限高度**（`[Finite ρ]`）。

**结论**：存在 $N\le|\rho|$，使第 $N$ 步的状态 $x_N$
**对它这一步注入的数据** $\mathrm{inj}(N)$ 已饱和：
$$\upsilon_{\mathrm{inj}(N)}(x_N)=x_N .$$

**为什么这不是同义反复**：前件里**没有**「饱和」二字，也没有任何关于
$\upsilon_{\mathrm{inj}(N)}(x_N)$ 的假设；结论是从「$x_N=x_{N+1}$」
（B 型）+「$x_{N+1}=\upsilon_{\mathrm{inj}(N)}(x_N)$」（递推方程）
**算出来**的。

**与 `upsilonIter_stabilizes_of_finite` 的区别**：那条止于「相等」，
本条把它**翻译成代数条件** `Saturated`，从而可以直接喂给
`IsCompletion.saturated_idem` / `saturated_iff` 等一整组引理。 -/
theorem finite_track_hits_saturated_at_its_data
    {Data : Type w} {ρ : Type u} {υ : UpsilonOperator.Upsilon Data (Set ρ)}
    (h : UpsilonOperator.IsCompletion υ) [Finite ρ]
    (inj : ℕ → Data) (x₀ : Set ρ) :
    ∃ N ≤ Nat.card ρ,
      UpsilonOperator.IsCompletion.Saturated υ (inj N)
        (upsilonIter υ inj x₀ N) := by
  obtain ⟨N, hN, heq⟩ := upsilonIter_exists_eq_within h inj x₀
  -- `heq : x_N = x_{N+1}`；饱和判据需要 `x_{N+1} = x_N`
  exact ⟨N, hN, (upsilonIter_succ_eq_iff υ inj x₀ N).mp heq.symm⟩

/-- **C1 的伴随形式：饱和的那一步恰好「停住」**。

由 C1 取出那个 $N$，则 $x_{N+1}=x_N$——即 `upsilonIter_stop_of_saturated`
在 B 型前件下的**无条件启用**。

**这不是重复 C1**：C1 的结论是 `Saturated`（一个关于 υ 与状态的命题），
本条的结论是**轨道上的等式**；两条互为逆用，且本条把「停」这件事
在 B 型前件下**显式化**。 -/
theorem finite_track_stops_at_saturated_step
    {Data : Type w} {ρ : Type u} {υ : UpsilonOperator.Upsilon Data (Set ρ)}
    (h : UpsilonOperator.IsCompletion υ) [Finite ρ]
    (inj : ℕ → Data) (x₀ : Set ρ) :
    ∃ N ≤ Nat.card ρ, upsilonIter υ inj x₀ (N + 1) = upsilonIter υ inj x₀ N := by
  obtain ⟨N, hN, hsat⟩ := finite_track_hits_saturated_at_its_data h inj x₀
  exact ⟨N, hN, (upsilonIter_succ_eq_iff υ inj x₀ N).mpr hsat⟩

/-! ===========================================================================
    §2  C2：FCA 具体实例上，B 型的停点是**闭属性集**
    ===========================================================================

模块 §6 的 `fca_upsilonIter_stabilizes` 把 B 型落到有限形式背景上，
但只给「存在 $N$ 使 $x_N=x_{N+1}$」。本节的 C2 把它**跨模块**接到
`UpsilonOperator.FCAInstance.fca_saturated_iff_isClosedAttr`，
得到「**存在某一步的属性集是 FCA 闭集**」——这是 FCA 语义下
「属性集已完善」的**可判定判据**（`K.IsClosedAttr B ↔ B = B''`）。 -/

/-- **⭐ C2（FCA：轨道必经过一个闭属性集）**。

**前件**：$K$ 是**有限**形式背景（`[K.FiniteAttrs]`）。

**结论**：存在 $N$，使第 $N$ 步的属性集 $x_N$ 是 **FCA 闭集**：
$$K.\mathrm{closureOp}(x_N)=x_N .$$

**为什么这不是同义反复**：前件只说「属性集有限」，**没有**任何
「某步是闭集」的假设；结论要经过
B 型（§6）→ 饱和判据（§1）→ `fca_saturated_iff_isClosedAttr`（跨模块）三步。

**语义**：在有限形式背景下，「信息不断注入」的完善迭代
**必在有限步内落到一个概念（闭属性集）上**——这正是
$\upsilon$ 的「一次即饱和」在 FCA 上的可见形式。

**⚠ 诚实边界**：`fcaUpsilon` 的数据参数是 `Unit`，故这里的「注入」
是退化的（重复同一完善）；与模块 §6 的登记一致。 -/
theorem fca_track_stabilizes_at_closed_attr (K : FormalCtx.{u, v}) [K.FiniteAttrs]
    (inj : ℕ → Unit) (B₀ : Set K.MFCA) :
    ∃ N : ℕ, K.IsClosedAttr
      (upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ N) := by
  obtain ⟨N, heq⟩ := fca_upsilonIter_stabilizes K inj B₀
  have hsat : UpsilonOperator.IsCompletion.Saturated
      (UpsilonOperator.FCAInstance.fcaUpsilon K) (inj N)
      (upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ N) :=
    (upsilonIter_succ_eq_iff _ inj B₀ N).mp heq.symm
  refine ⟨N, ?_⟩
  -- `inj N : Unit` 与 `()` 同物；`fcaUpsilon` 忽略数据参数
  have hunit : inj N = () := Subsingleton.elim _ _
  rw [← hunit] at *
  exact (UpsilonOperator.FCAInstance.fca_saturated_iff_isClosedAttr K _).mp hsat

/-- **C2 的定性推论：整条轨道被一个闭属性集界住**。

由 C2 取出 $N$，再由模块 `fca_upsilonIter_mono` 的**单调性**，
对一切 $n\ge N$ 有 $x_N\subseteq x_n$，而 $x_N$ 本身是闭集。
故「轨道**碰到**的闭集」是整条（$N$ 之后的）轨道的下界。

**与 C2 的区别**：C2 只给「存在一步是闭集」，本条给**闭集与整条轨道的关系**；
两者合起来是「B 型 + 单调 + FCA」的三重合成。 -/
theorem fca_closed_attr_is_subset_of_later_track (K : FormalCtx.{u, v}) [K.FiniteAttrs]
    (inj : ℕ → Unit) (B₀ : Set K.MFCA) :
    ∃ N : ℕ, K.IsClosedAttr
        (upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ N)
      ∧ ∀ n : ℕ, N ≤ n →
          upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ N
            ⊆ upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ n := by
  obtain ⟨N, hclosed⟩ := fca_track_stabilizes_at_closed_attr K inj B₀
  exact ⟨N, hclosed, fun n hn => fca_upsilonIter_mono K inj B₀ hn⟩

/-! ===========================================================================
    §3  C3：A 型的**双轨道**形式（两条不同初值的轨道按几何速率接近）
    ===========================================================================

模块 §3 的 `upsilonIter_dist_le` 只对**单条**轨道给界：
$$\mathrm{dist}(x_{t_0+k},\ x^\star)\le
  \frac{\kappa^k}{1-\kappa}\,\mathrm{dist}(x_{t_0},\upsilon_D x_{t_0}).$$
把两条**不同初值** $x_0,y_0$ 的轨道各用一次，再用**三角不等式**穿过共同的不动点，
即得两条轨道之间的定量接近性。这是模块中**没有的双轨道陈述**。 -/

/-- **⭐ C3（A 型：两条轨道的距离按几何速率衰减）**。

**前件**：
1. $\alpha$ 是完备非空度量空间；
2. 数据自 $t_0$ 起恒为 $D$；
3. $\upsilon_D$ 是常系数 $\kappa$ 的压缩映射（`UpsilonContracting`）。

**结论**（对任意初值 $x_0,y_0$ 与任意 $k$）：
$$\mathrm{dist}(x_{t_0+k},y_{t_0+k})\le
  \frac{\kappa^k}{1-\kappa}\Bigl(\mathrm{dist}(x_{t_0},\upsilon_D x_{t_0})
   +\mathrm{dist}(y_{t_0},\upsilon_D y_{t_0})\Bigr).$$

**为什么这不是同义反复**：前件**没有**任何关于两条轨道之间距离的语句；
结论经「两次单轨道界 + 三角不等式 + `dist_comm`」得到，是一个**新**的定量不等式。

**语义**：「数据稳定 + 压缩」时，**初始历史的差别被指数抹平**——
这是模块 `upsilonIter_limit_unique`（极限与初值无关）的**定量加强版**：
不仅极限相同，接近的**速度**也有界。 -/
theorem tracks_close_under_contracting
    {Data : Type w} {α : Type u} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {υ : UpsilonOperator.Upsilon Data α} {D : Data} {κ : NNReal}
    (inj : ℕ → Data) (t₀ : ℕ) (hstat : ∀ j, t₀ ≤ j → inj j = D)
    (hc : UpsilonOperator.Convergence.UpsilonContracting υ D κ)
    (x₀ y₀ : α) (k : ℕ) :
    dist (upsilonIter υ inj x₀ (k + t₀)) (upsilonIter υ inj y₀ (k + t₀)) ≤
      dist (upsilonIter υ inj x₀ t₀) (υ D (upsilonIter υ inj x₀ t₀))
          * (κ : ℝ) ^ k / (1 - (κ : ℝ))
        + dist (upsilonIter υ inj y₀ t₀) (υ D (upsilonIter υ inj y₀ t₀))
          * (κ : ℝ) ^ k / (1 - (κ : ℝ)) := by
  have hx := upsilonIter_dist_le inj D t₀ hstat x₀ hc k
  have hy := upsilonIter_dist_le inj D t₀ hstat y₀ hc k
  have htri := dist_triangle
    (upsilonIter υ inj x₀ (k + t₀))
    (ContractingWith.fixedPoint (υ D) hc)
    (upsilonIter υ inj y₀ (k + t₀))
  have hcomm :
      dist (ContractingWith.fixedPoint (υ D) hc) (upsilonIter υ inj y₀ (k + t₀))
        = dist (upsilonIter υ inj y₀ (k + t₀))
            (ContractingWith.fixedPoint (υ D) hc) :=
    dist_comm _ _
  linarith

/-- **C3 的极限形式：两条轨道的差值趋于零**。

在 C3 的前件下，$\mathrm{dist}(x_n,\,y_n)\to 0$（$n\to\infty$）——
**整条**轨道（不只是尾段）都趋于同一点。

**这不是 C3 的重复**：C3 是**逐 $k$ 的不等式**，本条是**收敛陈述**
（`Filter.Tendsto … (nhds 0)`）；由两条轨道各自收敛到**同一个**不动点、
再取 `Tendsto.dist`（`dist` 的连续性）得到。它把「初始历史被洗掉」
写成**拓扑结论**，是模块 `upsilonIter_tendsto_of_eventually_static`
（单轨道）的**双轨道**对应。 -/
theorem tracks_tendsto_zero_under_contracting
    {Data : Type w} {α : Type u} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {υ : UpsilonOperator.Upsilon Data α} {D : Data} {κ : NNReal}
    (inj : ℕ → Data) (t₀ : ℕ) (hstat : ∀ j, t₀ ≤ j → inj j = D)
    (hc : UpsilonOperator.Convergence.UpsilonContracting υ D κ)
    (x₀ y₀ : α) :
    Filter.Tendsto
      (fun n => dist (upsilonIter υ inj x₀ n) (upsilonIter υ inj y₀ n))
      Filter.atTop (nhds 0) := by
  -- 两条轨道各自收敛到**同一个**不动点；`dist` 是二元的连续函数
  have hfx : Filter.Tendsto (fun n => upsilonIter υ inj x₀ n)
      Filter.atTop (nhds (ContractingWith.fixedPoint (υ D) hc)) := by
    have h := hc.tendsto_iterate_fixedPoint (upsilonIter υ inj x₀ t₀)
    have h2 : Filter.Tendsto (fun k => upsilonIter υ inj x₀ (k + t₀))
        Filter.atTop (nhds (ContractingWith.fixedPoint (υ D) hc)) := by
      refine Filter.Tendsto.congr (fun k => ?_) h
      exact (upsilonIter_eq_iterate_of_static inj D t₀ hstat x₀ k).symm
    rw [tendsto_add_atTop_iff_nat t₀] at h2
    exact h2
  have hfy : Filter.Tendsto (fun n => upsilonIter υ inj y₀ n)
      Filter.atTop (nhds (ContractingWith.fixedPoint (υ D) hc)) := by
    have h := hc.tendsto_iterate_fixedPoint (upsilonIter υ inj y₀ t₀)
    have h2 : Filter.Tendsto (fun k => upsilonIter υ inj y₀ (k + t₀))
        Filter.atTop (nhds (ContractingWith.fixedPoint (υ D) hc)) := by
      refine Filter.Tendsto.congr (fun k => ?_) h
      exact (upsilonIter_eq_iterate_of_static inj D t₀ hstat y₀ k).symm
    rw [tendsto_add_atTop_iff_nat t₀] at h2
    exact h2
  -- `Tendsto.dist` 直接给出差的收敛，极限是 `dist x* x* = 0`
  have hdist := hfx.dist hfy
  simpa only [dist_self] using hdist

/-! ===========================================================================
    §4  C4：**有限高度 + 数据常尾** ⟹ 轨道**永久冻结**
    ===========================================================================

这是本文件**最重要**的一条：它把模块 §4（B 型）与 §5（永久稳定）
之间**被模块头表明确标注的缺口**补上。

模块头表原文：「B 型**只**断言「有限步无增益」。**它不保证永久稳定**——
第 $N+1$ 步若注入**不同**数据，$\upsilon_{D'}$ 仍可能撑大 $x_{N+1}$。
**永久稳定需要额外前件**，见 §5 的 `upsilonIter_permanent_stable`。」

本节的 C4 用**「数据自 $t_0$ 起恒定」**作为那个「额外前件」，
并**仍然只依赖 B 型**（不要求度量、不要求压缩）。 -/

/-- **⭐ C4（有限高度 + 常尾 ⟹ 永久冻结）**。

**前件**（三条，均**不**含结论）：
1. υ 是完善的（`IsCompletion υ`）；
2. 状态空间有限高度（`[Finite ρ]`）；
3. **数据自 $t_0$ 起恒为 $D$**（`∀ j ≥ t_0, inj j = D`）。

**结论**：存在 $N\le|\rho|$，使轨道从 $t_0+N$ 起**永久冻结**：
$$\forall k,\quad x_{(t_0+N)+k}=x_{t_0+N}.$$

**证明**：
1. 把迭代在 $t_0$ 处**重启**（`upsilonIter_tail`），得新迭代 $y_k=x_{t_0+k}$；
2. 对 $y$ 用 B 型（`upsilonIter_exists_eq_within`）得 $\exists M\le|\rho|,\ y_M=y_{M+1}$；
3. 因数据自 $t_0$ 起恒为 $D$，$y_{M+1}=\upsilon_D(y_M)$，
   故 $y_M$ 在 $\upsilon_D$ 下饱和（`Saturated`）；
4. 对 $y$ 用 §5 的 `upsilonIter_frozen_of_static_saturated` 得永久冻结。

**为什么这不是同义反复**：前件只给「有限」与「数据恒定」两个**结构性**假设；
结论是**对一切 $k$ 的冻结等式**。步骤 2 是 **B 型**（模块的核心结果），
步骤 4 是 **§5**（模块的另一结果），二者的**合成**正是模块头表所说的缺口。
**C4 不主张**「有限高度 ⟹ 永久稳定」（那**是假的**，见模块 §4.1 反例），
只主张「有限高度 **+ 常尾** ⟹ 永久稳定」。 -/
theorem finite_static_tail_eventually_frozen
    {Data : Type w} {ρ : Type u} {υ : UpsilonOperator.Upsilon Data (Set ρ)}
    (h : UpsilonOperator.IsCompletion υ) [Finite ρ]
    (inj : ℕ → Data) (x₀ : Set ρ) (D : Data) (t₀ : ℕ)
    (hstat : ∀ j, t₀ ≤ j → inj j = D) :
    ∃ N ≤ Nat.card ρ, ∀ k : ℕ,
      upsilonIter υ inj x₀ (t₀ + (N + k)) = upsilonIter υ inj x₀ (t₀ + N) := by
  -- ① 在 `t_0` 处重启：`y_k = x_{t_0+k}`
  obtain ⟨M, hM, heq⟩ :=
    upsilonIter_exists_eq_within (υ := υ) h (fun j => inj (j + t₀))
      (upsilonIter υ inj x₀ t₀)
  -- ② 换写回原轨道：`y_M = x_{M+t_0}`、`y_{M+1} = x_{M+1+t_0}`
  rw [upsilonIter_tail, upsilonIter_tail] at heq
  -- ③ 因数据恒定，`x_{M+1+t_0} = υ_D(x_{M+t_0})`，故 `x_{M+t_0}` 饱和
  have hsat : UpsilonOperator.IsCompletion.Saturated υ D
      (upsilonIter υ inj x₀ (M + t₀)) := by
    have hstep : upsilonIter υ inj x₀ (M + t₀ + 1)
        = υ (inj (M + t₀)) (upsilonIter υ inj x₀ (M + t₀)) :=
      upsilonIter_succ υ inj x₀ (M + t₀)
    rw [show M + t₀ + 1 = M + 1 + t₀ by omega] at hstep
    have hfix : υ (inj (M + t₀)) (upsilonIter υ inj x₀ (M + t₀))
        = upsilonIter υ inj x₀ (M + t₀) := hstep.symm.trans heq.symm
    have hinj : inj (M + t₀) = D := hstat _ (by omega)
    rw [hinj] at hfix
    exact hfix
  -- ④ §5：饱和 + 常尾 ⟹ 永久冻结
  refine ⟨M, hM, fun k => ?_⟩
  have hfrozen := upsilonIter_frozen_of_static_saturated inj D (M + t₀)
    (fun j hj => hstat j (by omega)) x₀ hsat k
  rwa [show t₀ + (M + k) = (M + t₀) + k by omega,
       show t₀ + M = M + t₀ by omega]

/-! ===========================================================================
    §5  小结
    ===========================================================================

| 编号 | 定理 | 消费了哪些模块结论 | 是否同义反复 |
|---|---|---|---|
| **C1** | `finite_track_hits_saturated_at_its_data` | `upsilonIter_exists_eq_within` + `upsilonIter_succ_eq_iff` | 否 |
| **C1b** | `finite_track_stops_at_saturated_step` | C1 + `upsilonIter_succ_eq_iff` | 否 |
| **C2** | `fca_track_stabilizes_at_closed_attr` | `fca_upsilonIter_stabilizes` + `upsilonIter_succ_eq_iff` + `fca_saturated_iff_isClosedAttr` | 否 |
| **C2b** | `fca_closed_attr_is_subset_of_later_track` | C2 + `fca_upsilonIter_mono` | 否 |
| **C3** | `tracks_close_under_contracting` | `upsilonIter_dist_le`（两次）+ 三角不等式 | 否 |
| **C3b** | `tracks_tendsto_zero_under_contracting` | `upsilonIter_eq_iterate_of_static` + `tendsto_iterate_fixedPoint` | 否 |
| **C4** | `finite_static_tail_eventually_frozen` | `upsilonIter_tail` + `upsilonIter_exists_eq_within` + `upsilonIter_frozen_of_static_saturated` | 否 |

**本文件不含 `sorry` / `admit` / `axiom`。** -/

end UpsilonIterationConsumer

end FateV2.Rules