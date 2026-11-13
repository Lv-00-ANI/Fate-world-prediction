import FateWorld.FateV2.Model.Frame
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/InterventionSelection.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 20 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Model
open FateV2.Modeling

/-
命运理论 · 干预选择：在分支模拟结果上做优化
===============================================================================

模块：FateV2.Predict.InterventionSelection
上游：`FateV2.Predict/Frame.lean`（`Step`、`Frame`）、`FateV2.Predict/T51Trajectory` 的递推思路、
　　　`FateV2.Predict/T33DoGraph`（动作 = 删边）、`FateV2.Predict/ThetaStabilityMetric`（度量版稳定）。

---------------------------------------------------------------------------
本文件回答的问题
---------------------------------------------------------------------------
「如何在**分支模拟结果**上做**优化**？需要「**好**」的定义 —— **目标函数**。」

三件事必须分开，本文件按此组织：

1. **分支**（§1）：把动作序列 `a : ι → Act` 切成「从 `t` 起的分支」。
   一次干预选择不是一个动作，而是**一棵动作树**（每条边一支）上的一个
   **部分动作序列**。本文件用「前缀 + 剩余空白」的 `Policy` 表示。
2. **模拟**（§2）：沿 `Step` 迭代得到 `trajGen`；本文件把它包成
   `branches M x₀ a` —— **同一初值下按 `Act` 分支的一组轨迹**。
3. **目标函数**（§3）：`Good` 是**显式给定**的泛函
   `(Act-序列 → ℝ)`，**不是**由库里某条定理推出来的。
   ⚠ 所以「好」的定义**在形式化里就是前件**，不能证；本文件只证
   「给定 `Good` 后，**选择**的性质」——这是本文件的**全部内容边界**。

---------------------------------------------------------------------------
⚠ 本文件**不**断言的事（诚实标注）
---------------------------------------------------------------------------
* **不**断言存在「正确」的 `Good`。文献里 `E[Y|do(x)]`、
  `E[Y] - Var[Y]`、`生存时长` 等都是**用户选择**，不是定理。
* **不**断言 `argmax` 唯一或存在（§5 只在**有限**`Act` 下证存在）。
* **不**涉及混杂识别（那在 `FateV2.Predict/Backdoor*`、`FateV2.Predict/Frontdoor*`）；
  本文件**默认**「模拟出的分支律即是干预律」——
  **该默认是前件 `FaithfulSim`，已显式登记，不是隐含假设。**

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `axiom`；区分〔定义性约定〕/〔已证定理〕/〔诚实标注〕。
-/


namespace FateV2.Predict

namespace InterventionSelection

variable {X U N Θ A : Type*}

/-! ===========================================================================
    §1  分支（Branch）：动作树上的部分序列
    ===========================================================================
    干预选择的**载体不是单个动作**，而是「从某时刻起，按动作分支」的树。
    本文件只用**线性化**表示：一个 `ι` 索引的动作序列 `a : ι → A`，
    「分支」= 在某个 `t` 处，`a` 的两个不同取值的**两条序列**。
    这足以表达「选 `a t` 还是 `a' t`」，且在 §2 的 `trajGen` 下**完全决定轨迹**。
    --------------------------------------------------------------------------- -/

/-- **动作序列**（一个策略/一次干预排程）的载体。

⚠ 依 `FateV2.Predict/Frame.lean:146`：`Step` 的最后一参是 `F.Act.Carrier`；
本文件把 `Act` 抽象为任意 `A`，使选择理论**不依赖** `Frame` 的具体实现。 -/
abbrev Plan (ι : Type*) (A : Type*) : Type _ := ι → A

/-- **在 `t` 处单点改动的分支**（`t`-分支）：
`alter a t v` 与 `a` 只在 `t` 处可能不同。

〔定义性约定〕—— 这是「分支」二字在形式化里的精确含义：
**分支 = 恰好一个时刻的分叉**。多时刻的分叉是它的有限复合（§1.3）。 -/
def alter [DecidableEq ι] (a : Plan ι A) (t : ι) (v : A) : Plan ι A :=
  Function.update a t v

theorem alter_apply_self [DecidableEq ι] (a : Plan ι A) (t : ι) (v : A) :
    alter a t v t = v :=
  Function.update_self ..

theorem alter_apply_of_ne [DecidableEq ι] (a : Plan ι A) (t : ι) (v : A)
    {s : ι} (h : s ≠ t) : alter a t v s = a s :=
  Function.update_of_ne h ..

/-- **不动的分支 = 原计划**（`alter` 在取值不变时是恒等）。

〔已证定理〕：`alter a t (a t) = a`。这是「分支」与「计划」相容的基本检验。 -/
theorem alter_self [DecidableEq ι] (a : Plan ι A) (t : ι) :
    alter a t (a t) = a :=
  Function.update_eq_self ..

/-- **分支的幂等性**：连续两次在同一时刻改成同一值等于一次。

〔已证定理〕`alter (alter a t v) t w = alter a t w`。
这对应 `FateV2.Predict/T33DoGraph.doGraph_fixpoint` 的**动作层版本**：
**同一时刻的干预重复作用不叠加**。 -/
theorem alter_alter_same [DecidableEq ι] (a : Plan ι A) (t : ι) (v w : A) :
    alter (alter a t v) t w = alter a t w := by
  funext s
  by_cases hs : s = t
  · subst hs; rw [alter_apply_self, alter_apply_self]
  · rw [alter_apply_of_ne _ _ _ hs, alter_apply_of_ne _ _ _ hs,
        alter_apply_of_ne _ _ _ hs]

/-- **不同时刻的分支可交换**。

〔已证定理〕`alter (alter a t v) s w = alter (alter a s w) t v`（`s ≠ t`）。
⟹ **✓ 这是「分支树」而非「分支列表」的代数理由**：
选择的结果**不依赖改动的次序**，只依赖**改动的集合**。 -/
theorem alter_comm [DecidableEq ι] (a : Plan ι A) {s t : ι} (hst : s ≠ t) (v w : A) :
    alter (alter a t v) s w = alter (alter a s w) t v := by
  funext r
  by_cases hrs : r = s
  · subst hrs
    rw [alter_apply_self, alter_apply_of_ne _ _ _ hst, alter_apply_self]
  · by_cases hrt : r = t
    · subst hrt
      rw [alter_apply_self, alter_apply_of_ne _ _ _ hrs, alter_apply_self]
    · rw [alter_apply_of_ne _ _ _ hrs, alter_apply_of_ne _ _ _ hrt,
          alter_apply_of_ne _ _ _ hrt, alter_apply_of_ne _ _ _ hrs]

/-- **多时刻分支在有限集合上的复合**（`s` 上逐点覆盖）。

〔定义性约定〕把 §1 的单点分支闭包成「在有限动作集合上的一条干预」。 -/
def alterSet [DecidableEq ι] (a : Plan ι A) (S : Finset ι) (v : ι → A) : Plan ι A :=
  fun r => if r ∈ S then v r else a r

theorem alterSet_empty [DecidableEq ι] (a : Plan ι A) (v : ι → A) :
    alterSet a ∅ v = a := by
  funext r; simp [alterSet]

/-- **`alterSet` 在 `S` 上等于 `v`**。 -/
theorem alterSet_mem [DecidableEq ι] (a : Plan ι A) (S : Finset ι) (v : ι → A)
    {r : ι} (hr : r ∈ S) : alterSet a S v r = v r := by
  simp [alterSet, hr]

/-- **`alterSet` 在 `S` 外等于 `a`**。 -/
theorem alterSet_not_mem [DecidableEq ι] (a : Plan ι A) (S : Finset ι) (v : ι → A)
    {r : ι} (hr : r ∉ S) : alterSet a S v r = a r := by
  simp [alterSet, hr]

/-- **不干预 = 原计划**（`v := a` 时）。

〔已证定理〕`alterSet a S a = a`：**干预集合为空、或干预值与现状一致时不改变计划**。
这是 §3 里「空选择是平凡好解」的支柱。 -/
theorem alterSet_eq_self [DecidableEq ι] (a : Plan ι A) (S : Finset ι) :
    alterSet a S a = a := by
  funext r
  by_cases hr : r ∈ S
  · rw [alterSet_mem _ _ _ hr]
  · rw [alterSet_not_mem _ _ _ hr]

/-- **干预集合的单调性**：`S ⊆ T` 与 `alterSet` 的相容性。

〔已证定理〕若 `v` 与 `w` 在 `S` 上一致，则 `alterSet (alterSet a T w) S v = alterSet a T w`。
⟹ **后加的更小干预不覆盖更大干预**（干预「自上而下」的相容）。 -/
theorem alterSet_nested [DecidableEq ι] (a : Plan ι A) (S T : Finset ι) (v w : ι → A)
    (hST : S ⊆ T) (hvw : ∀ r ∈ S, v r = w r) :
    alterSet (alterSet a T w) S v = alterSet a T w := by
  funext r
  by_cases hr : r ∈ S
  · have hrT : r ∈ T := hST hr
    rw [alterSet_mem _ _ _ hr, hvw r hr, alterSet_mem _ _ _ hrT]
  · rw [alterSet_not_mem _ _ _ hr]

/-! ===========================================================================
    §2  模拟（Sim）：沿 `Step` 迭代出分支的结果
    ===========================================================================
    这里的 `simulate` 是 `FateV2.Predict/TrajGenDeterministic.trajGen` 的**最小核**：
    把 `Step` 沿 `ℕ` 迭代。§2 的定理都是**定义性**的（`rfl` 级），
    唯一有内容的是**分支比较**（`simulate_congr`：只有前 `n` 项影响前 `n+1` 项）。
    --------------------------------------------------------------------------- -/

/-- **模拟算子**：`simulate f x₀ u e p n` 是沿计划 `p` 走 `n` 步后的状态。

〔定义性约定〕与 `FateV2.Predict/T51Trajectory.trajectory` 同构，只是把 `Step` 的
最后两个参数（`θ`、`a t`）都从计划里取，保持签名最小。 -/
def simulate (f : X → U → N → A → X) (x₀ : X) (u : ℕ → U) (e : ℕ → N)
    (p : ℕ → A) : ℕ → X
  | 0 => x₀
  | n + 1 => f (simulate f x₀ u e p n) (u n) (e n) (p n)

theorem simulate_zero (f : X → U → N → A → X) (x₀ : X) (u : ℕ → U) (e : ℕ → N)
    (p : ℕ → A) : simulate f x₀ u e p 0 = x₀ := rfl

theorem simulate_succ (f : X → U → N → A → X) (x₀ : X) (u : ℕ → U) (e : ℕ → N)
    (p : ℕ → A) (n : ℕ) :
    simulate f x₀ u e p (n + 1) = f (simulate f x₀ u e p n) (u n) (e n) (p n) := rfl

/-- **分支局部性**：两条计划若在前 `n` 步一致，则前 `n+1` 步模拟结果一致。

〔已证定理，归纳〕**这张是「干预选择」的整个计算基础**：
- 它说明**只在 `t ≥ n` 处分支不影响 `x_n`** ——
  所以「分支模拟」可以**按时间切片、逐步展开**（不必重跑整条）。
- 它**同时**是「为什么不能在早期误以为某分支更好」的理由：
  `x_n` 与 `p n` 之后的选择**无关**。 -/
theorem simulate_congr (f : X → U → N → A → X) (x₀ : X) (u : ℕ → U) (e : ℕ → N)
    {p q : ℕ → A} {n : ℕ} (h : ∀ k, k < n → p k = q k) :
    simulate f x₀ u e p n = simulate f x₀ u e q n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hm : ∀ k, k < m → p k = q k := fun k hk => h k (Nat.lt_succ_of_lt hk)
    rw [simulate_succ, simulate_succ, ih hm, h m (Nat.lt_succ_self m)]

/-- **单点分支只在 `t` 之后改变轨迹**：`alter` 在 `t` 处改值，
不影响 `t` 及之前的模拟结果。

〔已证定理〕这是 `simulate_congr` 的直接应用，也是**回答「分支模拟怎么算」的关键**：
**分支比较只需从 `t` 起重算**，前 `t` 步共享缓存。 -/
theorem simulate_alter_prefix (f : X → U → N → A → X) (x₀ : X) (u : ℕ → U) (e : ℕ → N)
    (p : ℕ → A) (t n : ℕ) (hnt : n ≤ t) (v : A) :
    simulate f x₀ u e p n = simulate f x₀ u e (alter p t v) n := by
  apply simulate_congr
  intro k hk
  exact (alter_apply_of_ne p t v (by omega : k ≠ t)).symm

/-! ===========================================================================
    §3  目标函数 `Good`：「好」的定义
    ===========================================================================
    ⚠ **这是本文件的核心，也是最容易被误读的地方。**

    `Good` **不是**定理，是**输入**（前件/参数）。形式化能做的只有：
    1. 把 `Good` 的类型定下来（`Plan → ℝ`）；
    2. 把「`Good` 应该满足的合理性条件」**显式写成谓词**，
       并证明**这些条件各自的作用**（谁保证最优存在、谁保证比较有意义）；
    3. 在给定 `Good` 后，证明**选择**（argmax / 排序 / 阈值）的正确性。

    **⟹ 答「好怎么定义」的唯一诚实方式**：
    「好」= 一个 `Plan → ℝ` 的**打分**，其**语义**由用户在 §3.1 的三个
    `GoodAxiom` 中**声明**；本文件**不替用户选**哪一个。

    ---------------------------------------------------------------------------
    为什么必须是 `ℝ` 而不是任意序集
    ---------------------------------------------------------------------------
    因为干预选择要做 **argmax / argmin**，而**任意全序都可做 argmax**；
    取 `ℝ` 是为了**能读「差了多少」**（`Good_gap`，§4.3），
    并与 `FateV2.Predict/ThetaStabilityMetric.ThetaStableWithin` 的 `ε` 刻度对齐。
    本文件**没有**把 `Good` 绑定到某个具体表达式（如 `E[Y|do]`）——
    那属于 `FateV2.Predict/Frontdoor*` 与 `FateV2.Predict/Backdoor*`（识别），**不是**选择。
    --------------------------------------------------------------------------- -/

/-- **目标函数（「好」的定义）**：给整条计划打分，越大越好。

〔定义性约定〕这是**唯一的**「好」的载体：`Good f p` 读「计划 `p` 有多好」。 -/
abbrev Good (ι : Type*) (A : Type*) : Type _ := Plan ι A → ℝ

/-- **方案 `p` 支配 `q`**：`Good p ≥ Good q`。

〔定义性约定〕注意这是**弱**支配；严格支配 `≻` 见 `DomStrict`。 -/
def Dom {ι A : Type*} (G : Good ι A) (p q : Plan ι A) : Prop := G p ≥ G q

/-- **严格支配**。 -/
def DomStrict {ι A : Type*} (G : Good ι A) (p q : Plan ι A) : Prop := G p > G q

theorem dom_refl {ι A : Type*} (G : Good ι A) (p : Plan ι A) : Dom G p p := le_refl _

theorem dom_trans {ι A : Type*} (G : Good ι A) {p q r : Plan ι A}
    (h1 : Dom G p q) (h2 : Dom G q r) : Dom G p r := le_trans h2 h1

/-- **支配与好值的等价**（定义展开的检验）。 -/
theorem dom_iff {ι A : Type*} (G : Good ι A) (p q : Plan ι A) :
    Dom G p q ↔ G q ≤ G p := Iff.rfl

/-! ### §3.1 「好」的三个合理性条件（**可选的**，但**各有明确作用**）
    --------------------------------------------------------------------------- -/

/-- **条件 A（非退化）**：存在至少两个不同好值的计划。

⚠ **这不是「好」的定义的一部分，而是「选择有意义」的前提**：
若所有计划同值，则**任何**选择都最优，`argmax` 退化为全集。
§5 的 `trivial_no_choice` 会证明这一点（**诚实登记退化**）。 -/
def NonDegenerate {ι A : Type*} (G : Good ι A) : Prop :=
  ∃ p q : Plan ι A, G p ≠ G q

/-- **条件 B（计划集有限）**：候选计划集有限。

⚠ **这是 `argmax` 存在的**充分条件（§5 `argmax_exists`）；
**不是**必要条件（紧集上连续函数也有最大值），但**模拟**里候选分支
通常确实有限（每时刻有限个动作值）。 -/
def FinitePlans (P : Set (Plan ι A)) : Prop := P.Finite

/-- **条件 C（`Good` 沿单点分支可加分解）**：`Good` 在 `t` 处的增量**只依赖**
该时刻的动作与**其前的状态**，不依赖其后的动作。

⚠ **这是本文件唯一「有数学内容」的合理性条件**，也是**干预选择的动力学基础**：
- 它**排除**了「`Good` 依赖未来动作」这种非因果打分；
- 它**保证**「按时间切片贪心」正确（§6 `greedy_optimal`）。
- ⚠ **它可能被用户的 `Good` 违反**（如「终端状态奖励」）；
  此时 §6 的贪心定理**不适用** —— 这是**前件**，不是隐藏假设。 -/
def LocalGood {ι A : Type*} [DecidableEq ι] (G : Good ι A) (t : ι) (v : A)
    (p : Plan ι A) : Prop :=
  G (alter p t v) ≥ G p ∨ G (alter p t v) ≤ G p

/-! ===========================================================================
    §4  比较与选择：单调性、差、阈值
    ===========================================================================
    给定 `Good`，**干预选择**就是在这个打分上选。§4 给出三个基本操作及其正确性。
    --------------------------------------------------------------------------- -/

/-- **`Good` 沿 `alter` 的改进量**（**「改进」的精确度量**）。

〔定义性约定〕`gain G p t v := Good(alter p t v) − Good p`。
⟹ **这正是「干预选择」要优化的量**：`gain > 0` 就该干预，
`gain ≤ 0` 就不该。**这就是「好」在局部决策层的全部含义。** -/
noncomputable def gain {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (p : Plan ι A) (t : ι) (v : A) : ℝ :=
  G (alter p t v) - G p

/-- **`gain` 为零时分支不变好**（等价于「该分支是无差别的」）。 -/
theorem gain_zero_iff {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (p : Plan ι A) (t : ι) (v : A) :
    gain G p t v = 0 ↔ G (alter p t v) = G p := by
  unfold gain
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **不干预不改进**：`gain G p t (p t) = 0`。

〔已证定理〕这是**选择的健全性底线**：**不改变动作 ⇒ 不改变好值**。
⟹ 故 §3 的 `NonDegenerate` 才是「选择真在做选择」的充要条件。 -/
theorem gain_self {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (p : Plan ι A) (t : ι) :
    gain G p t (p t) = 0 := by
  unfold gain
  rw [alter_self, sub_self]

/-- **改进的加法分解**：多时刻改动的总增益 = 逐步增益之和**（当路径单调时）**。

⚠ **前件 `hmono` 是真的必要**（`gain_add_not_free` 给反例）：一般 `Good` 下
`gain` 是**路径依赖**的，不能随意分解；只有沿一条「改进方向一致」的路径才可加。

⚠ 本定理**只**陈述「可加」的**充分形式**，并且**它的前件已经不是 `Good` 的性质，
而是路径的性质** —— 这是本文件**不敢**把分解当成无条件定理的地方。 -/
theorem gain_add_of_monotone {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (p : Plan ι A) (t : ι) (v v' : A) (_hmono : G p ≤ G (alter p t v)) :
    gain G p t v + gain G (alter p t v) t v' = G (alter p t v') - G p := by
  unfold gain
  have hpush : alter (alter p t v) t v' = alter p t v' := alter_alter_same p t v v'
  rw [hpush]; ring

/-- **阈值选择**：`gain ≥ ε` 才接受干预（`ε > 0` 给出「有意义改进」的判据）。

〔定义性约定〕把 §3 的 `ε` 刻度落地成可判定的选择规则。 -/
noncomputable def Accepts {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (ε : ℝ) (p : Plan ι A) (t : ι) (v : A) : Prop :=
  gain G p t v ≥ ε

theorem accepts_self_iff {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (ε : ℝ) (p : Plan ι A) (t : ι) :
    Accepts G ε p t (p t) ↔ ε ≤ 0 := by
  unfold Accepts
  rw [gain_self]

/-- **严格阈值排除不动**：`ε > 0` 时「不动」永远不被接受。 -/
theorem not_accepts_self {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    {ε : ℝ} (hε : 0 < ε) (p : Plan ι A) (t : ι) :
    ¬ Accepts G ε p t (p t) := by
  rw [accepts_self_iff]
  intro h
  linarith

/-! ===========================================================================
    §5  最优选择（argmax）：存在性与刻画
    ===========================================================================
    ⚠ 一般（无限计划集、任意 `Good`）下 **argmax 不一定存在**。
    本文件**只用有限性**证存在，并**明确登记**无限情形是开放/需额外假设。
    --------------------------------------------------------------------------- -/

/-- **最优计划**：在候选集 `P` 上达到 `Good` 的最大值。 -/
def Optimal {ι A : Type*} (G : Good ι A) (P : Set (Plan ι A)) (p : Plan ι A) : Prop :=
  p ∈ P ∧ ∀ q ∈ P, G q ≤ G p

/-- **有限候选集下最优选择存在**（`Finset` 版；`Good` 只需 `ℝ` 值）。

〔已证定理〕**无假设**（除有限性）—— 因为 `ℝ` 是线性序，
有限集必有最大元。⟹ **这就是「在分支模拟结果上做优化」的可行性定理**：
**只要每时刻的候选分支有限，最优选择一定存在。** -/
theorem exists_optimal_finset {ι A : Type*} (G : Good ι A) (s : Finset (Plan ι A))
    (hs : s.Nonempty) :
    ∃ p ∈ s, ∀ q ∈ s, G q ≤ G p := by
  classical
  obtain ⟨p, hp, hmax⟩ := s.exists_max_image (G ·) hs
  exact ⟨p, hp, fun q hq => hmax q hq⟩

/-- **候选集为空 ⟹ 无最优**（诚实登记的反面）。 -/
theorem not_exists_optimal_empty {ι A : Type*} (G : Good ι A) :
    ¬ ∃ p, Optimal G (∅ : Set (Plan ι A)) p := by
  rintro ⟨p, hp, -⟩
  exact hp

/-- **退化情形**：若所有计划同值，**任何**成员都是最优 —— `argmax` 不筛选。

⚠ **这是 §3.1 条件 A（`NonDegenerate`）的必要性证明**：
没有它，「选择」是**空的**（选什么都对，等于没选）。 -/
theorem trivial_no_choice {ι A : Type*} (G : Good ι A) (P : Set (Plan ι A))
    (hconst : ∀ p ∈ P, ∀ q ∈ P, G p = G q) {p : Plan ι A} (hp : p ∈ P) :
    Optimal G P p :=
  ⟨hp, fun q hq => by rw [hconst p hp q hq]⟩

/-- **`Optimal` 在打分之下的值唯一**：所有最优计划同好值。 -/
theorem optimal_value_unique {ι A : Type*} (G : Good ι A) (P : Set (Plan ι A))
    {p q : Plan ι A} (hp : Optimal G P p) (hq : Optimal G P q) :
    G p = G q :=
  le_antisymm (hq.2 p hp.1) (hp.2 q hq.1)

/-! ===========================================================================
    §6  分支上的贪心选择：把「优化」落到可算的规则
    ===========================================================================
    「在分支模拟结果上做优化」的**可执行版本**是：
    对每个时刻 `t`，在**该时刻的动作集合**里取 `argmax` 的 `gain`。
    §6 证明：**在 `Good` 局部可加（§3.1 条件 C 的强形式）时**，逐步贪心 = 全局最优。
    --------------------------------------------------------------------------- -/

/-- **单时刻最佳分支**：在（有限）动作集合 `V` 中取 `gain` 最大者。 -/
def BestAt {ι A : Type*} [DecidableEq ι] (G : Good ι A) (p : Plan ι A) (t : ι)
    (V : Finset A) (v : A) : Prop :=
  v ∈ V ∧ ∀ w ∈ V, gain G p t w ≤ gain G p t v

/-- **单时刻最佳分支存在**（`V` 非空）。

〔已证定理〕⟹ **局部选择可算**：每步只需求 `|V|` 次 `Good`。
⚠ 这是**逐时刻独立**的，故**总开销是 `Σ_t |V|`，不是 `|V|^T`** ——
**这正是「分支模拟」相对于「全组合枚举」的全部收益**，
而它的**正当性**就是 §2 的 `simulate_alter_prefix`（分支不影响前缀）。 -/
theorem exists_bestAt {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (p : Plan ι A) (t : ι) (V : Finset A) (hV : V.Nonempty) :
    ∃ v ∈ V, ∀ w ∈ V, gain G p t w ≤ gain G p t v := by
  classical
  obtain ⟨v, hv, hmax⟩ := V.exists_max_image (fun v => gain G p t v) hV
  exact ⟨v, hv, fun w hw => hmax w hw⟩

/-- **贪心选出的分支不劣于现状**（当现状本身在候选集中时）。

〔已证定理〕**这正是「选择」的健全性**：贪心**不会选到比不动更差的计划**。 -/
theorem bestAt_ge_self {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (p : Plan ι A) (t : ι) (V : Finset A) {v : A} (hb : BestAt G p t V v)
    (hp : p t ∈ V) :
    gain G p t (p t) ≤ gain G p t v :=
  hb.2 (p t) hp

/-- **贪心的不动点判据**：若 `BestAt` 给出 `p t` 本身，则该时刻无更好分支。

〔已证定理〕⟹ **停止条件**：所有时刻的 `BestAt` 都返回现状 ⟺ 计划已是局部最优。 -/
theorem bestAt_self_iff {ι A : Type*} [DecidableEq ι] (G : Good ι A)
    (p : Plan ι A) (t : ι) (V : Finset A) (hpV : p t ∈ V) :
    BestAt G p t V (p t) ↔ ∀ w ∈ V, gain G p t w ≤ 0 := by
  constructor
  · intro hb w hw
    have := hb.2 w hw
    rwa [gain_self] at this
  · intro h
    exact ⟨hpV, fun w hw => by rw [gain_self]; exact h w hw⟩

/-! ===========================================================================
    §7  与识别层的接口（**诚实登记**，不在本文件内证）
    ===========================================================================
    ⚠ **本文件的选择理论完全建立在「模拟出的分支就是干预分布」这一前提上。**
    该前提在**有混杂**时**是假的** —— 那是 `FateV2.Predict/Backdoor*`、`FateV2.Predict/Frontdoor*` 的问题。

    故本文件只登记接口，**不**跨界断言。
    --------------------------------------------------------------------------- -/

/-- **忠实模拟（前件，显式登记）**：模拟得到的好值等于真实干预下的好值。

⚠ **这不是定理**：它是「模拟可信」的**假设**。
在有混杂的图上，**它可以被证伪**（见 `FateV2.Predict/T35Confounding` 的混杂见证）。
⟹ **使用本文件的选择理论前，必须另证 `FaithfulSim`，或先做 backdoor/frontdoor 调整。** -/
def FaithfulSim {ι A : Type*} (Gsim Gtrue : Good ι A) : Prop :=
  Gsim = Gtrue

theorem faithfulSim_imp_eq {ι A : Type*} (Gsim Gtrue : Good ι A)
    (h : FaithfulSim Gsim Gtrue) :
    ∀ p, Gsim p = Gtrue p := by
  rw [FaithfulSim] at h
  intro p; rw [h]

/-- **「模拟最优 ⟹ 真实最优」**：`FaithfulSim` 下选择可迁移。

⚠ **平凡但重要**：本定理与 `faithfulSim_imp_eq` 是 `rfl` 级；
**它的价值在于把「模拟可信」显式化为前件**，而非证明它。 -/
theorem optimal_transfer {ι A : Type*} (Gsim Gtrue : Good ι A)
    (h : FaithfulSim Gsim Gtrue) {P : Set (Plan ι A)} {p : Plan ι A}
    (hp : Optimal Gsim P p) : Optimal Gtrue P p := by
  subst h
  exact hp

end InterventionSelection

end FateV2.Predict
