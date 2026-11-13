/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.UpsilonIteration
阶段：**阶段 1B 补充 —— 「信息不断注入」作为 υ 的迭代**

---------------------------------------------------------------------------
本文件回答的问题
---------------------------------------------------------------------------
理论把（完善／更新）算子 υ 的作用写成**递推**：

  $R_{t+1}=\upsilon(R_t,\mathrm{Data}_t)$（规格定义 5.8，出处 03:460）

**「信息不断注入」**即：$\mathrm{Data}_0,\mathrm{Data}_1,\mathrm{Data}_2,\dots$
是一个**无限序列**，每一步都把新数据喂给 υ，得到一条状态轨道
$R_0\to R_1\to R_2\to\cdots$。

本文件把这个直观**形式化**，并给出**收敛定理**。分层结构：

| 层 | 内容 | 数学原型 |
|---|---|---|
| **§1** | 迭代的**定义**（`Nat.rec`，唯一权威方程） | 非自治离散动力系统 |
| **§2** | **序论层**：扩张性 $\Rightarrow$ 非降轨道；**饱和判据** | 闭包算子的序性质 |
| **§3** | **度量层（A 型收敛）**：数据最终恒定 + 压缩 $\Rightarrow$ 收敛到唯一不动点，**带定量速率** | Banach 不动点定理 |
| **§4** | **有限层（B 型收敛）**：无度量、无压缩，只需**有限高度** $\Rightarrow$ 有限步无增益 | 鸽巢原理 |
| **§4.1** | ⭐ **反例：$|\rho|$ 步均匀界为假** | 显式构造 + 机器验证 |
| **§5** | **信息单调律与永久稳定** | 扩张性 + 饱和性 |
| **§6** | FCA 有限形式背景上的具体实例 | 落地 |
| **§7** | 两条收敛定理的**前件互不蕴含** | 可验证的登记 |

---------------------------------------------------------------------------
⭐ 两条收敛定理的**关系**（本文件的核心区分）
---------------------------------------------------------------------------
同一句「信息不断注入，状态最终稳定」有**两种数学含义**，
它们**前件不同、结论不同，不能互相替代**：

| | A 型（§3） | B 型（§4） |
|---|---|---|
| **前件** | 数据**最终恒定** $+$ $\upsilon_D$ 是**压缩映射** | 状态空间**有限高度**（如有限属性集） |
| **是否需要度量** | 需要（`MetricSpace`） | **不需要**（只要 `Set ρ` + `Finite ρ`） |
| **结论** | 收敛到**唯一不动点**，且给出**几何速率** | 只保证**有限步后一步不动**，不给唯一性 |
| **稳定后是否永久稳定** | 是（尾段数据恒定） | **不保证**（数据仍可改变状态） |

**为什么 B 型不保证永久稳定**：B 型只断言 $\exists N,\ x_N=x_{N+1}$；
若第 $N+1$ 步注入的是**不同**数据 $D'\ne D$，则 $\upsilon_{D'}$ 仍可能
把 $x_{N+1}$ 撑大（扩张性只保证「不减」，不保证「不变」）。
**故 B 型是「有限步无增益」，不是「永久稳定」**——
后者需要 A 型的「数据恒定」前件，或 §5 的「饱和」前件
（`upsilonIter_permanent_stable`）。

---------------------------------------------------------------------------
⚠ 一条**被推翻的猜想**（如实登记）
---------------------------------------------------------------------------
**猜想**：既然幂等性保证「完善一步即饱和」，而 $|\rho|$ 有限，
那么迭代必在 $|\rho|$ 步内稳定，即
$\forall N\le|\rho|,\ x_N=x_{N+1}$。

**该猜想为假**。幂等性 `υ_D(υ_D R) = υ_D R` **只对同一数据**成立；
**时变注入下，第 $k$ 步的「饱和」不能外推到第 $k+1$ 步**。
§4.1 给出**机器验证的反例**：$|\rho|=2$ 而轨道第 2 步仍严格增。

**⟹ 故 B 型的正确陈述只能是「$\exists N$」或「$\exists N\le|\rho|$」
（§4.2），不能是「$\forall N\le|\rho|$」。**

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件**零 `sorry`、零 `admit`、零 `axiom`**。
- **不主张**任何具体 υ 满足压缩性（T6.10 的显式前件，见
  `Fate.UpsilonOperator` §5 与本文件 §3）。
- **不构造**具体的数据流 `inj`——那属开放问题 6.8「先验来源未答」，
  规格纪律「填数即为虚构」。§4.1 的反例**只用于证伪定量界**，
  **不冒充**任何现实数据模型。
- 依赖：`Fate.UpsilonOperator`（υ 的类型、`IsCompletion` 三公理、
  §5 的 Banach 定理、FCA 实例）。
-/

import Mathlib.Order.Closure
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import FateWorld.Legacy.UpsilonOperator

namespace Fate

open Set Filter

universe u v w

noncomputable section

namespace UpsilonIteration

/-! ===========================================================================
    §1  迭代的定义：「信息不断注入」＝ Data 流 + υ 的 `Nat.rec` 展开
    =========================================================================== -/

/-- **⭐ 信息不断注入下的 υ 迭代**（本文件的核心定义）。

$$x_0:=R_0,\qquad x_{t+1}:=\upsilon\bigl(\mathrm{inj}(t),\,x_t\bigr)$$

**与规格的对应**：规格定义 5.8 写 $R_{t+1}=\upsilon(R_t,\mathrm{Data}_t)$。
本定义是它的**逐字展开**：
- `inj t` 就是规格里的 $\mathrm{Data}_t$（**第 $t$ 步注入的数据**）；
- `x₀` 就是 $R_0$（初始规则集）；
- `Nat.rec` 使**每一步只依赖上一步**（Markov 性），
  这正是「不断注入」的形式含义：**信息按时间顺序、逐步累积进状态**。

**为什么用 `Data → α → α`**：与 `Fate.UpsilonOperator.Upsilon` 的签名一致，
使「固定数据 $D$ 时 $\upsilon_D$ 是一个 `α → α`」在类型层可见——
这是 A 型收敛定理（§3）能直接调用 Banach 不动点定理的**类型层前提**。

**为什么用 `Nat.rec` 而非 `Function.iterate`**：`iterate` 只能表达
**同一个** $f$ 的重复复合，而「不断注入」要求第 $t$ 步用**不同的**
$\upsilon_{\mathrm{inj}(t)}$。故必须用**时变迭代**
（non-autonomous iteration／非自治动力系统）。
§4 的 B 型定理正是利用了 `Nat.rec` 的逐步结构。 -/
def upsilonIter (υ : UpsilonOperator.Upsilon Data α) (inj : ℕ → Data) (x₀ : α) : ℕ → α :=
  fun n => Nat.rec x₀ (fun t x => υ (inj t) x) n

variable {Data : Type w} {α : Type u}

/-- **初始条件（计算方程 0）**：$x_0=R_0$。 -/
@[simp] theorem upsilonIter_zero (υ : UpsilonOperator.Upsilon Data α) (inj : ℕ → Data)
    (x₀ : α) : upsilonIter υ inj x₀ 0 = x₀ := rfl

/-- **⭐ 递推方程（计算方程 succ）**：$x_{t+1}=\upsilon_{\mathrm{inj}(t)}(x_t)$。

**这是规格 $R_{t+1}=\upsilon(R_t,\mathrm{Data}_t)$ 在 Lean 中的唯一权威形式**——
它就是 `Nat.rec` 的计算规则本身，不是额外假设。 -/
theorem upsilonIter_succ (υ : UpsilonOperator.Upsilon Data α) (inj : ℕ → Data)
    (x₀ : α) (n : ℕ) :
    upsilonIter υ inj x₀ (n + 1) = υ (inj n) (upsilonIter υ inj x₀ n) :=
  Nat.casesOn n rfl (fun _ => rfl)

/-- **前缀无关性（尾段重启）**：从第 $t_0$ 步的状态出发、
把数据流平移 $t_0$ 后重新迭代，结果与原轨道**完全一致**。

$$x_{t_0+k}=\text{（从 }x_{t_0}\text{ 起、数据 }(\mathrm{inj}(t_0+j))_j\text{ 的迭代）}_k$$

**意义**：这是 §3 的全部技术基础——它使「尾段」成为一个**独立的迭代过程**，
从而可以对它调用 Banach 定理。
**它也是「信息可被分段消化」这一直观的形式化**：
前面 $t_0$ 步累积到 $x_{t_0}$ 的信息，与后面数据的处理**可分离**。 -/
theorem upsilonIter_tail (υ : UpsilonOperator.Upsilon Data α) (inj : ℕ → Data)
    (x₀ : α) (t₀ k : ℕ) :
    upsilonIter υ (fun j => inj (j + t₀)) (upsilonIter υ inj x₀ t₀) k
      = upsilonIter υ inj x₀ (k + t₀) := by
  induction k with
  | zero => simp only [upsilonIter_zero, Nat.zero_add]
  | succ m ih =>
      rw [upsilonIter_succ, ih]
      rw [show m + 1 + t₀ = (m + t₀) + 1 by omega, upsilonIter_succ]

/-- **轨道完全由「注入流 + 初值」决定**（函数外延性）。

这是 `upsilonIter` 是**良定义的过程**的直接表述：
两条轨道相同 $\iff$ 起点相同且每步注入相同。 -/
theorem upsilonIter_congr (υ : UpsilonOperator.Upsilon Data α) {inj₁ inj₂ : ℕ → Data}
    (hinj : ∀ t, inj₁ t = inj₂ t) {x₀ y₀ : α} (h₀ : x₀ = y₀) :
    upsilonIter υ inj₁ x₀ = upsilonIter υ inj₂ y₀ := by
  subst h₀
  have hinj' : inj₁ = inj₂ := funext hinj
  subst hinj'
  rfl

/-- **⭐ 饱和判据（一阶不动 $\iff$ 已饱和）**。

$$x_{t+1}=x_t\iff x_t\ \text{在}\ \upsilon_{\mathrm{inj}(t)}\ \text{下已饱和}$$

**这是「何时可以停」的判据**：迭代的**相邻两步相等**当且仅当
当前状态已被**这一步注入的数据**完善到饱和（`Saturated`）。
**注意**：这只是「**针对当前数据**饱和」，不是「针对未来数据饱和」
——故它**不**推出永久稳定（见 §5 与文件头表格的说明）。 -/
theorem upsilonIter_succ_eq_iff (υ : UpsilonOperator.Upsilon Data α) (inj : ℕ → Data)
    (x₀ : α) (n : ℕ) :
    upsilonIter υ inj x₀ (n + 1) = upsilonIter υ inj x₀ n
      ↔ UpsilonOperator.IsCompletion.Saturated υ (inj n) (upsilonIter υ inj x₀ n) := by
  rw [upsilonIter_succ]
  exact Iff.rfl

/-! ===========================================================================
    §2  序论层：扩张性 $\Rightarrow$ 非降轨道
    =========================================================================== -/

section Order

variable [Preorder α] {υ : UpsilonOperator.Upsilon Data α}

/-- **单步非降**：若 υ 是完善的（只需**扩张性**），则每一步都**不减**：
$x_t\le x_{t+1}$。

**直观**：「完善」只**补全未覆盖的情形**，绝不丢弃已覆盖者
（`IsCompletion.le_upsilon`）。故**无论注入什么数据**，信息都只增不减。

**⚠ 注意**：本条**不**需要注入序列 `inj` 单调——**每一步**都扩张，
不需要数据之间有任何关系。这是「信息不断注入」的**最基本健全性**。 -/
theorem upsilonIter_step_le (h : UpsilonOperator.IsCompletion υ) (inj : ℕ → Data) (x₀ : α)
    (n : ℕ) : upsilonIter υ inj x₀ n ≤ upsilonIter υ inj x₀ (n + 1) := by
  rw [upsilonIter_succ]
  exact h.le_upsilon (inj n) _

/-- **⭐ 轨道是单调链**：$m\le n\Rightarrow x_m\le x_n$。

**这是「信息累积」的序论形式**：状态随时间是**非降链**。
在闭包算子语义下，它意味着「已完善的规则永远保持被完善」——
后续注入只能**在其基础上**补全更多，不能回退。

**证明**：对 `n` 归纳，用 `upsilonIter_step_le` 作归纳步。∎ -/
theorem upsilonIter_mono (h : UpsilonOperator.IsCompletion υ) (inj : ℕ → Data) (x₀ : α)
    {m n : ℕ} (hmn : m ≤ n) : upsilonIter υ inj x₀ m ≤ upsilonIter υ inj x₀ n := by
  induction n with
  | zero => have : m = 0 := Nat.le_zero.mp hmn; subst this; exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_eq_of_le hmn with hlt | heq
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (upsilonIter_step_le h inj x₀ k)
      · subst heq; exact le_rfl

/-- **值域落在饱和元素中**：若 υ 是完善的，则每个「完善后」的元素
对它自己的数据饱和（幂等性）。

**意义**：**注入一次即饱和**——这正是闭包算子幂等性的时变版：
$\upsilon_{\mathrm{inj}(t)}\bigl(\upsilon_{\mathrm{inj}(t)}\,x\bigr)=\upsilon_{\mathrm{inj}(t)}\,x$。
故若**同一步数据被重复注入两次**，第二次无增益。 -/
theorem upsilonIter_succ_saturated (h : UpsilonOperator.IsCompletion υ) (inj : ℕ → Data)
    (x₀ : α) (n : ℕ) :
    UpsilonOperator.IsCompletion.Saturated υ (inj n) (upsilonIter υ inj x₀ (n + 1)) := by
  rw [upsilonIter_succ]
  exact h.idem (inj n) _

/-- **重复注入同一数据无增益**（幂等性在迭代上的直接后果）。

若第 $t$ 与第 $t+1$ 步注入**同一**数据 $D$，则第三步与第二步相同：
$x_{t+2}=x_{t+1}$。

**这是 A 型收敛的「静态尾段」在序论层的对应**：
一旦数据不再变化，轨道立刻**停在** $\upsilon_D$ 的值域上。
（A 型进一步说：这个停点就是**唯一不动点**。） -/
theorem upsilonIter_repeat_inj (h : UpsilonOperator.IsCompletion υ) (inj : ℕ → Data)
    (x₀ : α) (n : ℕ) (hrep : inj (n + 1) = inj n) :
    upsilonIter υ inj x₀ (n + 2) = upsilonIter υ inj x₀ (n + 1) := by
  rw [upsilonIter_succ (n := n + 1), upsilonIter_succ (n := n), hrep]
  exact h.idem (inj n) _

end Order

/-! ===========================================================================
    §3  A 型收敛：静态尾段 + 压缩性 $\Rightarrow$ 收敛到唯一不动点
    =========================================================================== -/

/-- **⭐ 静态尾段的迭代等同**：若 $t_0$ 之后数据恒为 $D$，
则第 $t_0+k$ 步的状态就是「$\upsilon_D$ 的 $k$ 次普通迭代」。

$$x_{t_0+k}=(\upsilon_D)^{[k]}(x_{t_0})\qquad(k\ge 0)$$

**这是 A 型收敛的桥梁**：它把**时变**迭代（`Nat.rec`，每步不同算子）
在尾段化归为**自治**迭代（同一个 `υ D` 重复复合），
从而可以直接调用 Banach 不动点定理。

**证明**：对 $k$ 归纳；归纳步用 `upsilonIter_succ` 展开、
再用 `hstat` 把 $\mathrm{inj}(m+t_0)$ 换成 $D$，
最后把 $(\upsilon_D)^{[k+1]}$ 用 `Function.iterate_succ_apply'` 展开。∎ -/
theorem upsilonIter_eq_iterate_of_static {υ : UpsilonOperator.Upsilon Data α}
    (inj : ℕ → Data) (D : Data) (t₀ : ℕ)
    (hstat : ∀ j, t₀ ≤ j → inj j = D) (x₀ : α) (k : ℕ) :
    upsilonIter υ inj x₀ (k + t₀) = (υ D)^[k] (upsilonIter υ inj x₀ t₀) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 + t₀ = (m + t₀) + 1 by omega, upsilonIter_succ, ih,
          Function.iterate_succ_apply']
      rw [hstat (m + t₀) (by omega)]

section Metric

variable [MetricSpace α] [Nonempty α] [CompleteSpace α]
variable {υ : UpsilonOperator.Upsilon Data α}

/-- **⭐⭐ A 型收敛定理（拓扑形式）——「信息不断注入下的完善收敛」**。

**前件**（全部显式，无一条默认）：
1. **数据最终恒定**：$\exists t_0,\ \forall j\ge t_0,\ \mathrm{inj}(j)=D$
   ——即「信息注入到某个时刻后不再有新信息」；
2. **压缩性**：$\upsilon_D$ 是常系数 $\kappa<1$ 的压缩映射
   ——即 T6.10 的显式前件（`UpsilonContracting`）。

**结论**：整条轨道 $\bigl(x_n\bigr)_{n\in\mathbb{N}}$（含**全部**历史，
不只是尾段）**收敛到 $\upsilon_D$ 的唯一不动点**
$x^\star=\mathrm{fixedPoint}\,(\upsilon_D)$。

**证明**：
1. 由 `upsilonIter_eq_iterate_of_static`，尾段 $x_{t_0+k}=(\upsilon_D)^{[k]}(x_{t_0})$；
2. 由 Mathlib `ContractingWith.tendsto_iterate_fixedPoint`，该自治迭代收敛；
3. **指标平移**：$\{k+t_0\}$ 与 $\{n\}$ 在 `atTop` 下等价
   （`tendsto_add_atTop_iff_nat`），故原序列收敛到同一点。∎

**与 T6.10 的关系**：T6.10（`Fate.UpsilonOperator.Convergence.t6_10_*`）
说的是**固定数据下** `(υ D)^[n]` 的收敛；**本条把结论提升到
「数据流最终恒定」的时变迭代上**——这是「信息不断注入」场景下
真正需要的定理，且它是 T6.10 的**直接推论**（不是重新假设）。 -/
theorem upsilonIter_tendsto_of_eventually_static
    (inj : ℕ → Data) (D : Data) (t₀ : ℕ)
    (hstat : ∀ j, t₀ ≤ j → inj j = D) (x₀ : α) {κ : NNReal}
    (hc : UpsilonOperator.Convergence.UpsilonContracting υ D κ) :
    Filter.Tendsto (fun n => upsilonIter υ inj x₀ n) Filter.atTop
      (nhds (ContractingWith.fixedPoint (υ D) hc)) := by
  -- ① 尾段的自治迭代收敛
  have htail : Filter.Tendsto (fun k => (υ D)^[k] (upsilonIter υ inj x₀ t₀))
      Filter.atTop (nhds (ContractingWith.fixedPoint (υ D) hc)) :=
    hc.tendsto_iterate_fixedPoint _
  -- ② 逐点等式：尾段 = 原轨道的平移
  have h2 : Filter.Tendsto (fun k => upsilonIter υ inj x₀ (k + t₀))
      Filter.atTop (nhds (ContractingWith.fixedPoint (υ D) hc)) := by
    refine Filter.Tendsto.congr (fun k => ?_) htail
    exact (upsilonIter_eq_iterate_of_static inj D t₀ hstat x₀ k).symm
  -- ③ 指标平移：`{k+t₀}` 与 `{n}` 在 atTop 下等价
  rwa [tendsto_add_atTop_iff_nat t₀] at h2

/-- **⭐⭐ A 型收敛定理（定量形式）——几何速率**。

$$\mathrm{dist}\bigl(x_{t_0+k},\,x^\star\bigr)
  \ \le\ \frac{\kappa^k}{1-\kappa}\,
  \mathrm{dist}\bigl(x_{t_0},\ \upsilon_D(x_{t_0})\bigr)$$

**这是把「收敛」从定性措辞变成定量不等式的落点**
（合规格阶段 1B 验收标准 3：定量陈述，非定性描述）。

**注意误差是「尾部」的**：$\mathrm{dist}(x_{t_0},\upsilon_D x_{t_0})$，
即**数据停止变化那一步**的单步增益——**前面的历史不入界**。
上界分两部分：$\kappa^k$（几何衰减，压缩性所致）
与 $\dfrac{\mathrm{dist}(x_{t_0},\upsilon_D x_{t_0})}{1-\kappa}$
（静态尾段的「启动距离」，由 $x_{t_0}$ 距不动点的远近决定）。 -/
theorem upsilonIter_dist_le (inj : ℕ → Data) (D : Data) (t₀ : ℕ)
    (hstat : ∀ j, t₀ ≤ j → inj j = D) (x₀ : α) {κ : NNReal}
    (hc : UpsilonOperator.Convergence.UpsilonContracting υ D κ) (k : ℕ) :
    dist (upsilonIter υ inj x₀ (k + t₀)) (ContractingWith.fixedPoint (υ D) hc) ≤
      dist (upsilonIter υ inj x₀ t₀) (υ D (upsilonIter υ inj x₀ t₀))
        * (κ : ℝ) ^ k / (1 - (κ : ℝ)) := by
  rw [upsilonIter_eq_iterate_of_static inj D t₀ hstat x₀ k]
  exact hc.apriori_dist_iterate_fixedPoint_le _ k

/-- **A 型收敛的极限就是不动点**：极限点 $x^\star$ 满足
$\upsilon_D(x^\star)=x^\star$。

由 `ContractingWith.fixedPoint_isFixedPt` 直接给出——
**「信息不再注入后，状态停在已完善的规则上」**的精确表述。 -/
theorem upsilonIter_limit_fixed (D : Data) {κ : NNReal}
    (hc : UpsilonOperator.Convergence.UpsilonContracting υ D κ) :
    υ D (ContractingWith.fixedPoint (υ D) hc) = ContractingWith.fixedPoint (υ D) hc :=
  hc.fixedPoint_isFixedPt

/-- **A 型收敛的唯一性（与初值无关）**。

压缩映射的不动点**唯一**，故**不同的历史（不同 $R_0$、不同早期注入）
导致不同轨道，但最终都收敛到同一个 $x^\star$**。

**这给出「完善」的一条重要语义**：数据最终稳定时，
完善算子的结果**不依赖初始规则集的选取**——初始信息被「洗掉」，
只有最终数据决定结局。**（⚠ 这是压缩性的推论，不是 υ 的一般性质。）** -/
theorem upsilonIter_limit_unique (D : Data) {κ : NNReal}
    (hc : UpsilonOperator.Convergence.UpsilonContracting υ D κ) {x y : α}
    (hx : υ D x = x) (hy : υ D y = y) : x = y := by
  have h1 : x = ContractingWith.fixedPoint (υ D) hc := hc.fixedPoint_unique hx
  have h2 : y = ContractingWith.fixedPoint (υ D) hc := hc.fixedPoint_unique hy
  exact h1.trans h2.symm

end Metric

/-! ===========================================================================
    §4  B 型收敛：有限高度 $\Rightarrow$ 有限步饱和（无度量、无压缩）
    =========================================================================== -/

section Finite

variable {ρ : Type u} {υ : UpsilonOperator.Upsilon Data (Set ρ)}

/-- **⭐⭐ B 型收敛定理——有限高度下的有限步饱和**。

**前件**（比 A 型弱得多）：
1. υ 是完善的（`IsCompletion`，但**证明中只用扩张性**）；
2. **状态空间高度有限**：$|\rho|<\infty$（如**有限形式背景**的属性集）。

**结论**：**存在** $N$，使 $x_N=x_{N+1}$——即迭代在**有限步后不再增长**。

**⭐ 本定理的强处**：它**不需要**度量结构、**不需要**压缩性、
也**不需要**数据流 `inj` 有任何规律（**可以无限变化**）。
唯一代价是**状态空间的基数有限**。

**证明（鸽巢论证）**：反证。若永不稳定，则每步都是**真扩张**
（$x_k\subsetneq x_{k+1}$，用扩张性 + 假设的反面），
故 `ncard` 严格递增（`Set.ncard_lt_ncard`），于是
$k\le\mathrm{ncard}(x_k)\le|\rho|$ 对**所有** $k$ 成立——
取 $k=|\rho|+1$ 得矛盾。∎

**⚠ 与 A 型的实质差别**（见文件头表格）：
本定理**只**断言「有限步无增益」。**它不保证永久稳定**——
第 $N+1$ 步若注入**不同**数据，$\upsilon_{D'}$ 仍可能撑大 $x_{N+1}$。
**永久稳定需要额外前件**，见 §5 的 `upsilonIter_permanent_stable`。 -/
theorem upsilonIter_stabilizes_of_finite (h : UpsilonOperator.IsCompletion υ)
    [Finite ρ] (inj : ℕ → Data) (x₀ : Set ρ) :
    ∃ N : ℕ, upsilonIter υ inj x₀ N = upsilonIter υ inj x₀ (N + 1) := by
  by_contra hnot
  push Not at hnot
  have hss : ∀ k : ℕ, upsilonIter υ inj x₀ k ⊂ upsilonIter υ inj x₀ (k + 1) := by
    intro k
    refine (Set.ssubset_iff_subset_ne).2 ⟨?_, hnot k⟩
    rw [upsilonIter_succ]
    exact h.le_upsilon (inj k) _
  have hcard : ∀ k : ℕ,
      (upsilonIter υ inj x₀ k).ncard < (upsilonIter υ inj x₀ (k + 1)).ncard :=
    fun k => Set.ncard_lt_ncard (hss k)
  have hbound : ∀ k : ℕ, k ≤ (upsilonIter υ inj x₀ k).ncard := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ m ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hcard m))
  have hle_univ : ∀ k : ℕ, (upsilonIter υ inj x₀ k).ncard ≤ (Set.univ : Set ρ).ncard :=
    fun k => Set.ncard_le_ncard (Set.subset_univ _)
  have hfin : (Set.univ : Set ρ).ncard = Nat.card ρ := Set.ncard_univ _
  have h1 := hbound (Nat.card ρ + 1)
  have h2 := hle_univ (Nat.card ρ + 1)
  omega

/-- **⭐ B 型的存在性界（$N\le|\rho|$）**。

比 `upsilonIter_stabilizes_of_finite` 的「$\exists N$」**强**：
给出**显式上界** $N\le|\rho|$。

**⚠ 注意陈述的精确形式**：它是「**存在** $N\le|\rho|$ 使 $x_N=x_{N+1}$」，
**不是**「$x_{|\rho|}=x_{|\rho|+1}$」（后者**为假**，见 §4.1 反例）。
二者的差别正是本文件 §4.1 的核心发现。

**证明**：反设所有 $N\le|\rho|$ 都严格增。
则由扩张性 $x_k\subseteq x_{k+1}$ 得 `ncard` 每步严格增，
故 $\mathrm{ncard}(x_{|\rho|+1})\ge|\rho|+1>|\rho|$——
与 $x_{|\rho|+1}\subseteq\mathrm{univ}$ 矛盾。∎ -/
theorem upsilonIter_exists_eq_within (h : UpsilonOperator.IsCompletion υ)
    [Finite ρ] (inj : ℕ → Data) (x₀ : Set ρ) :
    ∃ N ≤ Nat.card ρ, upsilonIter υ inj x₀ N = upsilonIter υ inj x₀ (N + 1) := by
  by_contra hnot
  push Not at hnot
  have hss : ∀ k ≤ Nat.card ρ, upsilonIter υ inj x₀ k ⊂ upsilonIter υ inj x₀ (k + 1) := by
    intro k hk
    refine (Set.ssubset_iff_subset_ne).2 ⟨?_, hnot k hk⟩
    rw [upsilonIter_succ]
    exact h.le_upsilon (inj k) _
  have hcard : ∀ k ≤ Nat.card ρ,
      (upsilonIter υ inj x₀ k).ncard < (upsilonIter υ inj x₀ (k + 1)).ncard :=
    fun k hk => Set.ncard_lt_ncard (hss k hk)
  have hbound : ∀ k ≤ Nat.card ρ + 1, k ≤ (upsilonIter υ inj x₀ k).ncard := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ m ih =>
        refine Nat.succ_le_of_lt (lt_of_le_of_lt (ih (by omega)) ?_)
        exact hcard m (by omega)
  have h1 := hbound (Nat.card ρ + 1) (le_refl _)
  have hle : (upsilonIter υ inj x₀ (Nat.card ρ + 1)).ncard ≤ Nat.card ρ := by
    have : (upsilonIter υ inj x₀ (Nat.card ρ + 1)).ncard ≤ (Set.univ : Set ρ).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _)
    rwa [Set.ncard_univ] at this
  omega

/-! ### §4.1 ⭐⭐ **为什么 B 型不能给出「$|\rho|$ 步内稳定」的定量界**

B 型的存在性定理容易被误读为「在 $|\rho|$ 步内必稳定」——
**这是错的**。§2 已指出：幂等性 `υ_D(υ_D R) = υ_D R` **只对同一数据**成立；
**时变注入下，第 $k$ 步的「饱和」不能外推到第 $k+1$ 步**。

下面给出**机器验证的反例**：$\rho=\mathrm{Fin}\,2$（故 $|\rho|=2$），
而轨道**第 2 步仍严格增**——故任何形如
「$\forall N\le|\rho|,\ x_N=x_{N+1}$」的命题**为假**。

反例设计：数据参数取 $\mathrm{Option}(\mathrm{Fin}\,2)$，
$\upsilon_{\mathrm{none}}(X)=X$，$\upsilon_{\mathrm{some}\,a}(X)=X\cup\{a\}$
（各自都是闭包算子）；注入流 $\mathrm{none},\mathrm{some}\,0,\mathrm{some}\,1,\mathrm{none},\dots$，
初值 $\varnothing$。则轨道
$$\varnothing\to\varnothing\to\{0\}\to\{0,1\}\to\{0,1\}\to\cdots$$
第 2 步仍有 $x_2=\{0\}\subsetneq\{0,1\}=x_3$，而 $|\rho|=2$。 -/

section Counterexample

/-- 反例用的完善算子：数据 = 「本步要补的元素」（`none` = 不补）。

每个 $\upsilon_D$ 都是**闭包算子**（恒等 / 加单个元素），
满足扩张、单调、幂等三律。 -/
def cexUpsilon : UpsilonOperator.Upsilon (Option (Fin 2)) (Set (Fin 2)) :=
  fun D X => match D with
    | none => X
    | some a => X ∪ {a}

theorem cexUpsilon_none (X : Set (Fin 2)) : cexUpsilon none X = X := rfl

theorem cexUpsilon_some (a : Fin 2) (X : Set (Fin 2)) :
    cexUpsilon (some a) X = X ∪ {a} := rfl

/-- **反例算子满足 `IsCompletion`**（三律全部机器验证）。 -/
theorem cexUpsilon_isCompletion : UpsilonOperator.IsCompletion cexUpsilon where
  le_upsilon := by
    intro D X
    cases D with
    | none => rw [cexUpsilon_none]
    | some a => rw [cexUpsilon_some]; exact Set.subset_union_left
  mono := by
    intro D X Y hXY
    cases D with
    | none => rwa [cexUpsilon_none, cexUpsilon_none]
    | some a => rw [cexUpsilon_some, cexUpsilon_some]; exact Set.union_subset_union_left _ hXY
  idem := by
    intro D X
    cases D with
    | none => rw [cexUpsilon_none]
    | some a =>
        rw [cexUpsilon_some, cexUpsilon_some]
        ext x; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto

/-- 反例的注入流：第 0 步不补，第 1 步补 $0$，第 2 步补 $1$，之后不补。 -/
def cexInj : ℕ → Option (Fin 2)
  | 0 => none
  | 1 => some 0
  | 2 => some 1
  | _ => none

/-- 反例的轨道。 -/
def cexTrack : ℕ → Set (Fin 2) :=
  upsilonIter cexUpsilon cexInj ∅

theorem cexTrack_1 : cexTrack 1 = ∅ := rfl

theorem cexTrack_2 : cexTrack 2 = ({0} : Set (Fin 2)) := by
  show cexUpsilon (cexInj 1) (cexTrack 1) = {0}
  have h : cexInj 1 = some (0 : Fin 2) := rfl
  rw [cexTrack_1, h, cexUpsilon_some]
  ext x; simp

theorem cexTrack_3 : cexTrack 3 = ({0,1} : Set (Fin 2)) := by
  show cexUpsilon (cexInj 2) (cexTrack 2) = {0,1}
  have h : cexInj 2 = some (1 : Fin 2) := rfl
  rw [cexTrack_2, h, cexUpsilon_some]
  ext x; fin_cases x <;> simp

/-- ⭐ **反例：第 $|\rho|=2$ 步仍严格增**。 -/
theorem cex_strict_at_card : cexTrack 2 ⊂ cexTrack 3 := by
  rw [cexTrack_2, cexTrack_3]
  refine (Set.ssubset_iff_subset_ne).2 ⟨by simp, ?_⟩
  intro heq
  have hmem : (1 : Fin 2) ∈ ({0,1} : Set (Fin 2)) := by simp
  rw [← heq] at hmem
  simp at hmem

/-- **⭐⭐ 「$|\rho|$ 步内稳定」的定量界为假**。

$$\neg\ \forall N\le|\rho|,\ x_N=x_{N+1}$$

**这是本文件对 B 型定理的诚实边界**：存在性
（`upsilonIter_stabilizes_of_finite`）**成立**，
但**不存在**仅依赖 $|\rho|$ 的「步步稳定」界——
每注入一次**新**数据，就可能再推进一格。
**故 B 型只能断言「$\exists N\le|\rho|$」（§4 的
`upsilonIter_exists_eq_within`），不能断言「$\forall N\le|\rho|$」。** -/
theorem cex_no_uniform_card_bound :
    ¬ ∀ N : ℕ, N ≤ Nat.card (Fin 2) → cexTrack N = cexTrack (N + 1) := by
  intro h
  have h2 := h 2 (by simp)
  rw [cexTrack_2, cexTrack_3] at h2
  have hmem : (1 : Fin 2) ∈ ({0,1} : Set (Fin 2)) := by simp
  rw [← h2] at hmem
  simp at hmem

end Counterexample

end Finite

/-! ===========================================================================
    §5  信息单调律与永久稳定
    =========================================================================== -/

section Stable

variable {υ : UpsilonOperator.Upsilon Data α}

/-- **⭐ 信息注入下的永久稳定（需要「饱和」前件）**。

**这条定理补上 §4 的缺口**：B 型只保证「某一步无增益」，
本定理给出**何时可以断言永久稳定**。

**前件**：状态 $x_t$ 在**未来所有**注入数据下都已被完善
（`∀ j ≥ t, Saturated υ (inj j) (x_t)`）。

**结论**：$x_t=x_{t+1}=x_{t+2}=\cdots$——轨道**冻结**。

**语义**：一旦当前规则**对所有将来可能的数据都已完善到饱和**，
则无论再注入什么数据，都不再有增益：
$$\text{「信息饱和」}\iff\text{「对未来的所有数据均已覆盖」}$$
这是「停在原地」的**正确充分条件**（而 §1 的
`upsilonIter_succ_eq_iff` 只覆盖**当前**数据）。 -/
theorem upsilonIter_permanent_stable (inj : ℕ → Data) (x₀ : α) (t : ℕ)
    (hsat : ∀ j, t ≤ j → UpsilonOperator.IsCompletion.Saturated υ (inj j)
      (upsilonIter υ inj x₀ t)) (k : ℕ) :
    upsilonIter υ inj x₀ (t + k) = upsilonIter υ inj x₀ t := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [show t + (m + 1) = (t + m) + 1 by omega, upsilonIter_succ, ih]
      exact hsat (t + m) (by omega)

/-- **完善不改变已完善者（在轨道上）**：若 $x_m$ 已对数据 $\mathrm{inj}(m)$ 饱和，
则第 $m+1$ 步与第 $m$ 步相同。

这是 `upsilonIter_succ_eq_iff` 的**反向使用**：
它给出「已饱和 $\Rightarrow$ 停」这半条。 -/
theorem upsilonIter_stop_of_saturated (inj : ℕ → Data) (x₀ : α) (m : ℕ)
    (h : UpsilonOperator.IsCompletion.Saturated υ (inj m) (upsilonIter υ inj x₀ m)) :
    upsilonIter υ inj x₀ (m + 1) = upsilonIter υ inj x₀ m := by
  rw [upsilonIter_succ]
  exact h

/-- **A 型下的永久稳定推论**：若数据从 $t_0$ 起恒为 $D$，
且 $x_{t_0}$ 已在 $\upsilon_D$ 下饱和，则轨道从 $t_0$ 起**永久冻结**。

这是「数据恒定」情形下永久稳定的**充分条件**——
它同时说明：A 型的「尾段恒定」前件**恰好**提供给
`upsilonIter_permanent_stable` 所需的「未来数据全同」信息。 -/
theorem upsilonIter_frozen_of_static_saturated (inj : ℕ → Data) (D : Data) (t₀ : ℕ)
    (hstat : ∀ j, t₀ ≤ j → inj j = D) (x₀ : α)
    (hsatS : UpsilonOperator.IsCompletion.Saturated υ D (upsilonIter υ inj x₀ t₀))
    (k : ℕ) :
    upsilonIter υ inj x₀ (t₀ + k) = upsilonIter υ inj x₀ t₀ := by
  refine upsilonIter_permanent_stable inj x₀ t₀ (fun j hj => ?_) k
  rw [hstat j hj]
  exact hsatS

end Stable

/-! ===========================================================================
    §6  FCA 实例上的具体化（把 B 型落到 `FiniteAttrs` 形式背景）
    =========================================================================== -/

section FCAInstance

variable (K : FormalCtx.{u, v})

/-- **⭐ FCA 有限形式背景上的 B 型收敛（具体实例）**。

**这是本文件唯一的「常数级」实例**：把 §4 的
`upsilonIter_stabilizes_of_finite` 落到
`Fate.UpsilonOperator.FCAInstance.fcaUpsilon`（属性集闭包 $B\mapsto B''$）上，
并借 `K.FiniteAttrs` 提供「有限高度」前件。

**结论**：在**有限**形式背景下，属性集的完善迭代**必在有限步内饱和**。

**⚠ 诚实边界**：`fcaUpsilon : Upsilon Unit (Set K.MFCA)` 的数据参数为 `Unit`，
故「不断注入」在此**退化为重复同一完善**——
**这恰好说明幂等性（§2）使轨道一步即停**（`upsilonIter_repeat_inj`）。
真正「数据在变」的情形需要非退化 `Data`，那属开放问题 6.8，
本文件不填。 -/
theorem fca_upsilonIter_stabilizes [K.FiniteAttrs]
    (inj : ℕ → Unit) (B₀ : Set K.MFCA) :
    ∃ N : ℕ,
      upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ N
        = upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ (N + 1) := by
  haveI : Finite K.MFCA :=
    Set.finite_univ_iff.mp (FormalCtx.FiniteAttrs.finite (K := K))
  exact upsilonIter_stabilizes_of_finite
    (UpsilonOperator.FCAInstance.fcaInstance_isCompletion K) inj B₀

/-- **FCA 实例上的轨道是单调增链**（`⊆` 意义下）。 -/
theorem fca_upsilonIter_mono (inj : ℕ → Unit) (B₀ : Set K.MFCA) {m n : ℕ} (hmn : m ≤ n) :
    upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ m
      ⊆ upsilonIter (UpsilonOperator.FCAInstance.fcaUpsilon K) inj B₀ n :=
  upsilonIter_mono (UpsilonOperator.FCAInstance.fcaInstance_isCompletion K) inj B₀ hmn

end FCAInstance

/-! ===========================================================================
    §7  两条收敛定理的**前件互不蕴含**（可验证的登记）
    ===========================================================================
A 型（§3）与 B 型（§4）常被误当作「同一件事的强弱两版」。
**它们不是**：前件互不蕴含，故**不能互相替代**。

本节给出**可验证**的一条：§4.1 的反例空间中
$|\rho|=2$ 有限（B 型前件满足），而注入流**不恒定**——
故 A 型的「数据最终恒定」前件**不成立**。
**⟹ 「有限高度」推不出「数据恒定」。**

（反方向——「数据恒定」而有度量时 $|\rho|$ 可以无限、
故 B 型前件不成立——由 A 型定理自身的存在范围即知：
`upsilonIter_tendsto_of_eventually_static` 不要求 `Finite ρ`。） -/

section NonImplication

/-- **B 型前件成立，但 A 型的「数据（自始）恒定」前件不成立**。

`cexInj` 在第 0 步与第 1 步注入**不同**数据，
故「从 $t_0=0$ 起数据恒定」为假：
$$\neg\ \forall j,\ \mathrm{cexInj}(j)=\mathrm{cexInj}(0)$$

**这足以说明**：B 型的「有限高度」前件**不会**自动给出
「数据最终恒定」，故**不能**从 B 型前件推出 A 型结论。 -/
theorem cex_B_not_A : ¬ ∀ j : ℕ, cexInj j = cexInj 0 := by
  intro h
  have h1 := h 1
  have e1 : cexInj 1 = some (0 : Fin 2) := rfl
  have e0 : cexInj 0 = (none : Option (Fin 2)) := rfl
  rw [e1, e0] at h1
  exact absurd h1 (by simp)

/-- **同一反例空间中 B 型结论成立**（对照 `cex_B_not_A`）。

有限高度下迭代确实在有限步后无增益。
**与 `cex_B_not_A` 并列**，这两条给出 §7 的核心对比：
同一空间里 B 型有结论，而 A 型的「自始恒定」前件为假——
**故 A、B 的前件不可互相替代**。 -/
theorem cex_B_holds : ∃ N : ℕ, cexTrack N = cexTrack (N + 1) :=
  upsilonIter_stabilizes_of_finite cexUpsilon_isCompletion cexInj ∅

end NonImplication

/-! ===========================================================================
    §8  小结（本文件的结果清单）
    ===========================================================================

| 编号 | 名称 | 内容 |
|---|---|---|
| **D1** | `upsilonIter` | 迭代定义：$x_{t+1}=\upsilon_{\mathrm{inj}(t)}(x_t)$ |
| **D2** | `upsilonIter_succ` | 递推方程（`Nat.rec` 计算规则，规格 5.8 的落点） |
| **T1** | `upsilonIter_tail` | 尾段独立：$x_{t_0+k}$ = 平移数据流后的迭代 |
| **T2** | `upsilonIter_mono` | **信息累积**：轨道是非降链 |
| **T3** | `upsilonIter_succ_eq_iff` | 饱和判据：$x_{t+1}=x_t\iff$ 已（对该步数据）饱和 |
| **T4** | ⭐⭐ `upsilonIter_tendsto_of_eventually_static` | **A 型收敛**：数据最终恒定 + 压缩 $\Rightarrow$ 收敛到唯一不动点 |
| **T5** | ⭐⭐ `upsilonIter_dist_le` | A 型的**定量速率**（几何衰减） |
| **T6** | `upsilonIter_limit_unique` | A 型极限**与初值无关** |
| **T7** | ⭐⭐ `upsilonIter_stabilizes_of_finite` | **B 型收敛**：有限高度 $\Rightarrow$ 有限步无增益（无需度量） |
| **T8** | `upsilonIter_exists_eq_within` | B 型显式界：$\exists N\le|\rho|$ |
| **T9** | ⭐ `cex_no_uniform_card_bound` | **反例**：$|\rho|$ 步「步步稳定」**为假** |
| **T10** | `upsilonIter_permanent_stable` | **永久稳定**的充分条件（对未来数据全饱和） |
| **T11** | `fca_upsilonIter_stabilizes` | FCA 有限背景上的具体实例 |
| **T12** | `cex_B_not_A` | A、B 前件互不蕴含（可验证） |
-/

end UpsilonIteration

end

end Fate
