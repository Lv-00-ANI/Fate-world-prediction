import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.SetNotation

/-!
  # Meta · ICPCoverage

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ICPCoverage.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Meta`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §19  ⭐⭐ **ICP 覆盖保证的群体层**：一条**被论文隐藏的前件**

  **来源**：探针 `probes/_probe_q33.lean`（**不在构建内**）。

  ## 问题

  ICP（Invariant Causal Prediction, Peters–Bühlmann–Meinshausen 2016）的
  **有限样本保证**（Thm 1）能否形式化到「**群体层 + 显式样本复杂度前件**」？

  ## ⭐ 答案：能 —— 且**分解暴露一条被论文隐藏的前件**

  ### 核心观察

  ICP Thm 1 的**全部数学内容**是「一族有效检验 + 集合论取交」的**纯概率/组合**论断，
  **与样本量 $n$ 无关** —— $n$ 只以「每个检验在 $n$ 下 level-$\alpha$ 有效」
  这一**前件**身份出现。

  故可分解为：

  | 部分 | 内容 |
  |---|---|
  | **(P) 群体层** | 抽象拒绝事件、概率、原假设为真 —— **不依赖 $n$、不依赖分布** |
  | **(C) 样本复杂度前件** | 「检验 level-$\alpha$ 有效」写成显式前件 `ValidAt` |

  ### ⭐⭐ 隐藏前件（本节的主要发现）

  论文 Thm 1 的证明写
  $$\Pr[\hat S \subseteq S^*] \ge \Pr[S^* \text{ 未被拒}] \ge 1-\alpha$$
  **第二步隐含「补集可加性」**（$\Pr[A] + \Pr[A^c] = \Pr[\Omega]$）。

  **若概率接口只有单调性 + 归一，第二步不成立。**

  **⟹ 故本节把「有限可加」**显式**列入前件**（`Prob.compl_add`），
  使 `icp_coverage` 在**真正最小**的前件集下成立。

  ## ⚠ 诚实边界

  **本节不证明 `ValidAt` 本身** —— 那需要具体检验构造（Levene / KS / 矩条件）
  与分布假设，属**统计学**，**不是 ICP Thm 1 的内容**。

  **⟹ 本节把它显式化为前件，把「可形式化的」与「须外部证明的」彻底分离。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Meta
namespace ICPCoverage

universe u v

variable {S : Type u} {ι : Type v} {Ω : Type u}

/-! ### §19.1 群体层接口 -/

/-- ⭐ **抽象有限可加概率**：**单调性 + 归一 + 非负 + 补集可加**。

**⚠ `compl_add` 是 Thm 1 的**隐藏前件**** ——
论文未明写，但证明的第二步依赖它（见文件头）。

**这是「群体层」的精确含义**：任何满足此接口的 `pr` 都适用，
**不涉及样本量、不涉及分布族、不涉及 σ-代数细节**。 -/
structure Prob (Ω : Type u) where
  /-- 概率函数。 -/
  toFun : Set Ω → ℝ
  /-- 单调性。 -/
  mono : ∀ {A B : Set Ω}, A ⊆ B → toFun A ≤ toFun B
  /-- 归一。 -/
  prob_univ : toFun Set.univ = 1
  /-- 非负。 -/
  nonneg : ∀ A, 0 ≤ toFun A
  /-- ⭐ **补集可加**：`pr A + pr Aᶜ = pr univ`。**这是 Thm 1 的隐藏前件。** -/
  compl_add : ∀ A, toFun A + toFun Aᶜ = toFun Set.univ

instance : CoeFun (Prob Ω) (fun _ => Set Ω → ℝ) := ⟨Prob.toFun⟩

/-- **算法输出 $\hat S$**：**未被拒绝者之**交****。

$$\hat S(\omega) := \bigcap_{i\ :\ \omega \notin \mathrm{reject}\,i} F\,i$$ -/
def hatS (F : ι → Set S) (reject : ι → Set Ω) (ω : Ω) : Set S :=
  ⋂ i ∈ {i | ω ∉ reject i}, F i

/-- ⭐ **「有效检验」前件**（level-$\alpha$）：
$H_{0,Fi}$ 真时拒绝概率 $\le \alpha$。

**⚠ 样本量 $n$ 只通过 `Ω` 的结构携带，本定理不依赖它。** -/
def ValidAt (pr : Prob Ω) (reject : ι → Set Ω) (α : ℝ) (trueH : Set ι) : Prop :=
  ∀ i ∈ trueH, pr (reject i) ≤ α

/-! ### §19.2 ⭐⭐ 主定理：ICP 覆盖保证（群体层） -/

/-- ⭐⭐ **定理 19.1（ICP Thm 1，群体层形式）**。

设索引 $i^*$（代表 $S^* = \mathrm{PA}(Y)$）满足
$i^* \in \mathrm{trueH}$（**真父集索引**）**且** `ValidAt pr reject α trueH`
（每个真原假设的检验 level-$\alpha$ 有效）。
**则无论 $n$、无论分布**，
$$\Pr[\hat S \subseteq S^*] \ \ge\ 1 - \alpha.$$

**★ 证明的关键两步**：
1. 事件「$i^*$ 未被拒绝」$\subseteq$「$\hat S \subseteq F\,i^*$」（因 $\hat S$ 是交）
2. $\Pr[(\mathrm{reject}\,i^*)^c] = 1 - \Pr[\mathrm{reject}\,i^*]$ —— **这一步用到隐藏前件** -/
theorem icp_coverage
    (pr : Prob Ω) (F : ι → Set S) (reject : ι → Set Ω) (α : ℝ)
    (trueH : Set ι) (istar : ι)
    (hstar : istar ∈ trueH)
    (hvalid : ValidAt pr reject α trueH) :
    1 - α ≤ pr {ω | hatS F reject ω ⊆ F istar} := by
  -- 事件「istar 未被拒绝」含于「hatS ⊆ F istar」
  have hsub : (reject istar)ᶜ ⊆ {ω | hatS F reject ω ⊆ F istar} := by
    intro ω hω x hx
    simp only [hatS, Set.mem_iInter, Set.mem_setOf_eq] at hx
    exact hx istar hω
  have hle : pr (reject istar) ≤ α := hvalid istar hstar
  -- ⭐ 隐藏前件的使用处
  have hcompl : pr (reject istar)ᶜ = 1 - pr (reject istar) := by
    have h := pr.compl_add (reject istar)
    rw [pr.prob_univ] at h
    linarith
  calc 1 - α ≤ pr (reject istar)ᶜ := by rw [hcompl]; linarith
    _ ≤ pr {ω | hatS F reject ω ⊆ F istar} := pr.mono hsub

/-! ### §19.3 前件的层次分解 -/

/-- ⭐ **定理 19.2（覆盖方向即「不误纳」）**。

若 $i^*$ 未被拒绝，则 $\hat S \subseteq F\,i^*$。

**⟹ 这刻画了 ICP 保证的**保守性**：它**不误纳**，但**可能给空集**。 -/
theorem hatS_subset_of_mem (F : ι → Set S) (reject : ι → Set Ω) (ω : Ω)
    (istar : ι) (hω : ω ∉ reject istar) :
    hatS F reject ω ⊆ F istar := by
  intro x hx
  simp only [hatS, Set.mem_iInter, Set.mem_setOf_eq] at hx
  exact hx istar hω

/-- ⭐ **定理 19.3（空集诊断）**。

$$\hat S = \varnothing \iff \forall s,\ \exists i,\ \omega \notin \mathrm{reject}\,i \wedge s \notin F\,i$$

**⟹ 即**：**空集 = 每个变量都被某个存活的候选排除** ——
这正是 ICP「空集」的集合论刻画。 -/
theorem hatS_empty_iff (F : ι → Set S) (reject : ι → Set Ω) (ω : Ω) :
    hatS F reject ω = ∅ ↔ ∀ s, ∃ i, ω ∉ reject i ∧ s ∉ F i := by
  rw [hatS, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h s
    by_contra hc
    push Not at hc
    exact h s (by simp only [Set.mem_iInter, Set.mem_setOf_eq]; exact hc)
  · intro h s hs
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hs
    obtain ⟨i, hi, hsi⟩ := h s
    exact hsi (hs i hi)

/-- ⭐ **单调性下的覆盖下界**（把 `icp_coverage` 的证明结构显式化）。

若某事件 $A$ 的概率 $\ge 1-\alpha$ 且 $A \subseteq B$，则 $\Pr[B] \ge 1-\alpha$。

**⟹ 这是 `icp_coverage` 的**抽象骨架**** ——
它说明该定理的实质是「**单调性 + 补集可加**」，与 ICP 的具体构造无关。 -/
theorem coverage_of_subset (pr : Prob Ω) {A B : Set Ω} {α : ℝ}
    (hA : 1 - α ≤ pr A) (hAB : A ⊆ B) : 1 - α ≤ pr B :=
  le_trans hA (pr.mono hAB)

end ICPCoverage

end FateV2.Meta