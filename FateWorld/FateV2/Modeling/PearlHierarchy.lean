import FateWorld.FateV2.Predict.Counterfactual
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/PearlHierarchy.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-007 D-008 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Modeling（正文 4 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict

/-
=============================================================================
  Pearl 三层级（因果层级）在 Lean 中的形式化 —— 以 **第三层（反事实）** 为重点
=============================================================================

本文件是一份**可编译的骨架**：每个定义与定理都无 `sorry`/`admit`/`axiom`。

## Pearl (2009, *Causality* §1.3 / §7.1) 的三层级

| 层 | 名称 | 典型问句 | 本项目对象 |
|---|---|---|---|
| **L1** | 关联 (association) | 「看到 X，Y 是多少？」 | 观测分布 `P(X,Y)` |
| **L2** | 干预 (intervention) | 「若令 X:=x，Y 是多少？」 | 每个 `do(x)` 下 `Y` 的律 |
| **L3** | 反事实 (counterfactual) | 「已知 X=x、Y=y，若当初 X:=x′ 呢？」 | 逐个体响应族 `{Y_{x′}(u)}` |

## 形式化口径（**本文件为准**）

**⚠ 关于与探针文件的关系（修正一处不可核验的声称）**：

本节口径**与**（不在构建内的）探索性文件 `_probe_q15.lean` **同源**，
但**本文件是权威版本**。

**为何改措辞**：此前本节写作「与 `_probe_q15.lean` **逐字一致**」——
但该探针**不在 `lakefile.toml` 的 `roots` 里，也不被任何文件 import**，
故「逐字一致」**无法被编译期保证**，属**不可核验的声称**。
**依本项目对「注释里的话须可核验」的纪律，改为：本文件为准，探针仅供参考。**

一个**结构性有限 SCM** `⟨U, pU, sg⟩`，其中 `sg : U → X × (X → Y)`：
`sg u = (x, h)` 读作「外生实现 `u` 下，事实 `X = x`，结构方程 `Y := h(X)`」。

* **L1**：观测分布 `P(X,Y) = ev_# L3`，`ev (x,h) = (x, h x)`（求值映射）。
* **L2**：对 `X := x′` 的干预分布 = 外生律沿 `u ↦ h_u(x′)` 的推前。
* **L3**：**反事实系统** = 外生律沿 `u ↦ (x, h_u)` 的推前，落在 `X × (X → Y)`；
  第二分量即逐个体响应函数。

## 本文件证了什么（全部可编译，零 sorry）

1. `L3_determines_L2` / `L3_determines_L1`：**L3 ⟹ L2 ⟹ L1**（层间蕴含）。
2. `L3_not_determined_by_L1_and_L2`：**L3 ⊋ (L1 与 L2 的联合)**。
   存在两个机制，在**全部观测**与**全部干预**下不可区分，
   却在**反事实**上不同——因为 L3 额外读到「同一个体在不同干预下的**联合**响应」
   （`(Y_{x′})_{x′}` 的相关性），而 L1、L2 只读到它的**边缘**。
   这正是 Pearl「L3 不可由 L1+L2 还原」的最小见证。
3. `L3_cf_not_injective`：**L3 读出非单射**（`= ⊊ ~cf`）：外生空间细化给出
   「不同 SCM、同一反事实系统」。

## 诚实边界

* 本文件**不**形式化 do-calculus 的三条代数规则（`FateV2.Modeling.Stage1A` 登记 `T1A.5 = ❌ 未实现`）。
* 一般 SCM 的 `~cf` 商**基数**无闭式；本文件只给存在性，不越界。
-/


namespace FateV2.Modeling

namespace PearlHierarchy

set_option autoImplicit false

/-! ===========================================================================
    §1  结构性 SCM（与 `_probe_q15.lean` 同口径的最小载体）
    =========================================================================== -/

/-- 一个**结构性有限 SCM**（单结果变量口径，足以承载全部三层）。

`sg u = (x, h)`：外生实现 `u` 下事实 `X = x`，结构方程 `Y := h X`。 -/
structure SCM (X Y : Type*) where
  /-- 外生空间（有限、可判定相等）。 -/
  U : Type
  [instFintype : Fintype U]
  [instDecEq : DecidableEq U]
  /-- 外生律。 -/
  pU : U → ℝ
  /-- 结构映射：事实 `X` 的取值 × 结构方程 `X → Y`。 -/
  sg : U → X × (X → Y)

attribute [instance] SCM.instFintype SCM.instDecEq

/-! ## 有限推前（自足版本） -/

/-- 有限律 `p : U → ℝ` 沿 `g : U → W` 的**推前**。 -/
noncomputable def push {U W : Type*} [Fintype U] [DecidableEq W]
    (p : U → ℝ) (g : U → W) : W → ℝ :=
  fun w => ∑ u, p u * (if g u = w then (1 : ℝ) else 0)

/-- **推前复合律**：`h_#(g_#p) = (h ∘ g)_#p`。 -/
theorem push_push {U W Z : Type*} [Fintype U] [Fintype W]
    [DecidableEq W] [DecidableEq Z]
    (p : U → ℝ) (g : U → W) (h : W → Z) :
    push (push p g) h = push p (fun u => h (g u)) := by
  funext z
  simp only [push]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [Finset.sum_eq_single (g u)]
  · simp
  · intro w _ hw
    have hne : ¬ (g u = w) := fun hc => hw hc.symm
    simp [hne]
  · intro hw; exact absurd (Finset.mem_univ _) hw

variable {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]

/-! ===========================================================================
    §2  三层读出：L1 / L2 / L3
    =========================================================================== -/

namespace SCM

variable (M : SCM X Y)

/-- **L1 · 观测分布** `P(X,Y)`：外生律沿 `u ↦ (x, h x)` 的推前。 -/
noncomputable def L1_obs : X × Y → ℝ :=
  push M.pU (fun u => ((M.sg u).1, (M.sg u).2 (M.sg u).1))

/-- **L2 · 干预分布** `P(Y | do(X := x′))`：外生律沿 `u ↦ h u x′` 的推前。 -/
noncomputable def L2_do (x' : X) : Y → ℝ :=
  push M.pU (fun u => (M.sg u).2 x')

/-- **L2 · 全部干预的读出**（一次读遍所有 `do(x′)`）。 -/
noncomputable def L2_family : (X → Y → ℝ) := fun x' => M.L2_do x'

/-- **L3 · 反事实系统**：外生律沿 `u ↦ (事实 X, 逐个体响应函数 x′ ↦ Y_{x′}(u))`
的推前，落在 `X × (X → Y)`。

这是 Pearl 第三层的**全部输出**：每个个体 `u` 的响应函数 `x′ ↦ Y_{x′}(u)`。 -/
noncomputable def L3_cf [DecidableEq (X → Y)] : X × (X → Y) → ℝ :=
  push M.pU (fun u => ((M.sg u).1, (M.sg u).2))

/-! ### **SCM 在可观测三元组上的诱导联合律**（**第 119 轮从 `_pending` 移入**）

⚠ **为何移入**：本定义原先只存在于 `_pending/FinMarkov.lean`（**不在构建图内**），
而**下游定理**（如「边缘 = 乘积」的一致性引理）**引用了它** ——
⟹ **那些引用在正式构建里**全部悬空****（`simp only [.. jointLaw3 ..]` 无从展开）。

**本定义**不依赖任何**私有符号****（只用 `push`）——
**故它是**可以立即入库**的。 -/

/-- **诱导联合律** `P(A,B,C)`：外生律沿轨道映射
$$u \mapsto \bigl((\mathrm{sg}\,u).1,\;(\mathrm{sg}\,u).2\,(\mathrm{sg}\,u).1\bigr) \in X \times Y$$
的**推前**（当 `Y = B × C` 时，落点即 `A × B × C`）。

**⚠ 与 `L1_obs` 的关系**：`L1_obs` 是 `X × Y` 上的观测律；
`jointLaw3` 是**同一映射**在 `Y` 被**显式视为乘积** `B × C` 时的形式 ——
**故二者在 `Y = B × C` 时**是同一个东西****（`jointLaw3 = L1_obs`，定义上）。
**此处保留 `jointLaw3` 这个名字是因为下游定理沿用它。** -/
noncomputable def jointLaw3 {B C : Type*} [DecidableEq B] [DecidableEq C]
    (M : SCM X (B × C)) : X × B × C → ℝ :=
  push M.pU (fun u => ((M.sg u).1, (M.sg u).2 (M.sg u).1))

end SCM

/-! ===========================================================================
    §3  L3 ⟹ L2 ⟹ L1：层级的细化链（Pearl 层级的层间蕴含）
    =========================================================================== -/

/-- **L3 ⟹ L2**：反事实系统决定一切干预分布。

证明：`do(x′)` 分布是反事实系统沿「读数映射」`(x, h) ↦ h x′` 的推前。 -/
theorem L3_determines_L2 {M₁ M₂ : SCM X Y}
    [DecidableEq (X → Y)]
    (h : M₁.L3_cf = M₂.L3_cf) :
    M₁.L2_family = M₂.L2_family := by
  have key : ∀ M : SCM X Y,
      M.L2_family = fun x' => push M.L3_cf (fun p : X × (X → Y) => p.2 x') := by
    intro M
    funext x' y
    rw [SCM.L2_family, SCM.L2_do, SCM.L3_cf]
    exact (congrFun (push_push M.pU (fun u => ((M.sg u).1, (M.sg u).2))
        (fun p : X × (X → Y) => p.2 x')) y).symm
  rw [key M₁, key M₂, h]

/-- **L3 ⟹ L1**：反事实系统决定观测分布（第 15 问引理 2.2）。 -/
theorem L3_determines_L1 {M₁ M₂ : SCM X Y}
    [DecidableEq (X → Y)]
    (h : M₁.L3_cf = M₂.L3_cf) : M₁.L1_obs = M₂.L1_obs := by
  have key : ∀ M : SCM X Y,
      M.L1_obs = push M.L3_cf (fun p : X × (X → Y) => (p.1, p.2 p.1)) := by
    intro M
    rw [SCM.L1_obs, SCM.L3_cf]
    exact (push_push M.pU (fun u => ((M.sg u).1, (M.sg u).2))
        (fun p : X × (X → Y) => (p.1, p.2 p.1))).symm
  rw [key M₁, key M₂, h]

/-! ===========================================================================
    §4  L3 严格细于 L1+L2：反事实读到「联合响应」，L1/L2 只读到边缘
    ===========================================================================

    为使见证**完全可判定**（避免函数外延性的不可判定比较），
    本节的 L3 载体取「逐个体的响应**对** `(Y_{x′})_{x′∈X}`」的显式形式
    （`X = Bool` 时即 `(Y_{false}, Y_{true}) ∈ Bool × Bool`）。
    这与 `SCM.L3_cf`（响应**函数**）等价——把函数表为值对即可。

    两个机制的 `L3` 联合律不同（一个 `Y_1 = ¬Y_0`、一个 `Y_1 = Y_0`），
    但它们的 L1 与 L2 边缘律完全相同。
    =========================================================================== -/

/-- 外生空间 `U = Bool × Bool`（4 点，均匀 1/4）。 -/
abbrev U4 := Bool × Bool

/-- L3 的坐标：`(X, Y_false, Y_true)`——事实变量 + 逐个体响应对。 -/
abbrev L3coord := Bool × (Bool × Bool)

/-- **机制 1** 的 `L3` 联合：`(X, Y_0, Y_1)` 取值
`(0,0,1),(0,1,0),(1,0,1),(1,1,0)`（`Y_1 = ¬Y_0`，反相关）。 -/
def sel1 : U4 → L3coord
  | (false, false) => (false, false, true)
  | (false, true)  => (false, true, false)
  | (true, false)  => (true, false, true)
  | (true, true)   => (true, true, false)

/-- **机制 2** 的 `L3` 联合：`(X, Y_0, Y_1)` 取值
`(0,0,0),(0,1,1),(1,0,0),(1,1,1)`（`Y_1 = Y_0`，正相关）。 -/
def sel2 : U4 → L3coord
  | (false, false) => (false, false, false)
  | (false, true)  => (false, true, true)
  | (true, false)  => (true, false, false)
  | (true, true)   => (true, true, true)

/-- 机制 1 的 **L3 联合律**。 -/
noncomputable def L3_1 : L3coord → ℝ :=
  push (fun _ : U4 => (1 : ℝ) / 4) sel1

/-- 机制 2 的 **L3 联合律**。 -/
noncomputable def L3_2 : L3coord → ℝ :=
  push (fun _ : U4 => (1 : ℝ) / 4) sel2

/-- 机制 1 的 **L1 观测律** `(X, Y_X)`。 -/
noncomputable def L1_1 : Bool × Bool → ℝ :=
  push (fun _ : U4 => (1 : ℝ) / 4)
    (fun i => let c := sel1 i; (c.1, if c.1 then c.2.2 else c.2.1))

/-- 机制 2 的 **L1 观测律**。 -/
noncomputable def L1_2 : Bool × Bool → ℝ :=
  push (fun _ : U4 => (1 : ℝ) / 4)
    (fun i => let c := sel2 i; (c.1, if c.1 then c.2.2 else c.2.1))

/-- 机制 1 的 **L2 干预律族** `{P(Y | do(x′))}`。 -/
noncomputable def L2_1 : Bool → Bool → ℝ := fun x' =>
  push (fun _ : U4 => (1 : ℝ) / 4)
    (fun i => let c := sel1 i; if x' then c.2.2 else c.2.1)

/-- 机制 2 的 **L2 干预律族**。 -/
noncomputable def L2_2 : Bool → Bool → ℝ := fun x' =>
  push (fun _ : U4 => (1 : ℝ) / 4)
    (fun i => let c := sel2 i; if x' then c.2.2 else c.2.1)

/-- **L1 相同**：两机制的观测分布一致。 -/
theorem L1_1_eq_L1_2 : L1_1 = L1_2 := by
  funext w
  fin_cases w <;>
    simp [L1_1, L1_2, push, sel1, sel2, Fintype.sum_prod_type]

/-- **L2 相同**：两机制在**每个** `do(x′)` 下的分布一致。 -/
theorem L2_1_eq_L2_2 : L2_1 = L2_2 := by
  funext x' y
  fin_cases x' <;> fin_cases y <;>
    simp [L2_1, L2_2, push, sel1, sel2, Fintype.sum_prod_type]

/-- **L3 不同**：两机制的**联合响应律**不同（反相关 vs 正相关）。 -/
theorem L3_1_ne_L3_2 : L3_1 ≠ L3_2 := by
  intro h
  have h0 := congrFun h ((false, false, false) : L3coord)
  simp [L3_1, L3_2, push, sel1, sel2, Fintype.sum_prod_type] at h0

/-- **核心定理（Pearl 第 7.1 节）**：L1 与 L2 相同 **不蕴含** L3 相同。

即存在一对机制，其**联合** `(L1, L2)` 读出相同，而反事实联合律不同——
**L3 携带 L1+L2 无法还原的信息**（逐个体跨干预的相关性）。 -/
theorem L3_not_determined_by_L1_and_L2 :
    L1_1 = L1_2 ∧ L2_1 = L2_2 ∧ L3_1 ≠ L3_2 :=
  ⟨L1_1_eq_L1_2, L2_1_eq_L2_2, L3_1_ne_L3_2⟩

/-! ===========================================================================
    §5  L3 读出非单射：`= ⊊ ~cf`（外生空间细化见证）
    =========================================================================== -/

/-- 模型 **C**：外生空间 `Bool`，`sg u = (u, id)`。 -/
noncomputable def modelC : SCM Bool Bool where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1 / 2
  sg := fun u => (u, id)

/-- 模型 **D**：外生空间 `Bool × Bool`，`sg (i, _) = (i, id)`
（第二外生坐标被机制忽略）。**与 C 是不同的 SCM**（外生空间基数不同）。 -/
noncomputable def modelD : SCM Bool Bool where
  U := Bool × Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1 / 4
  sg := fun u => (u.1, id)

/-- **L3 读出非单射**：存在不同 SCM 具有**相同**反事实系统
（`= ⊊ ~cf`，Pearl 层级第三层的「中间地带」非空）。 -/
theorem L3_cf_not_injective :
    ∃ M₁ M₂ : SCM Bool Bool, M₁ ≠ M₂ ∧ M₁.L3_cf = M₂.L3_cf := by
  refine ⟨modelC, modelD, ?_, ?_⟩
  · -- 外生空间基数不同 ⟹ 模型不等
    intro h
    have hU : modelC.U = modelD.U := congrArg SCM.U h
    have hc : Fintype.card modelC.U = Fintype.card modelD.U :=
      Fintype.card_congr (Equiv.cast hU)
    have hc2 : Fintype.card modelC.U = 2 := by
      change Fintype.card Bool = 2
      rw [Fintype.card_bool]
    rw [hc2] at hc
    change 2 = Fintype.card (Bool × Bool) at hc
    rw [Fintype.card_prod, Fintype.card_bool] at hc
    norm_num at hc
  · -- 反事实系统相同：均为 (0,id),(1,id) 各 1/2
    funext w
    simp only [SCM.L3_cf, modelC, modelD, push]
    change (∑ u : Bool, (1 : ℝ) / 2 * (if (u, id) = w then 1 else 0)) =
      (∑ u : Bool × Bool, (1 : ℝ) / 4 * (if (u.1, id) = w then 1 else 0))
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    ring

end PearlHierarchy

end FateV2.Modeling
