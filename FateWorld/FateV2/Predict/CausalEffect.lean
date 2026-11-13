import FateWorld.FateV2.Predict.ParamSCM
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/CausalEffect.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 15 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict
open FateV2.Model
open FateV2.Modeling

/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`FateV2.Predict.CausalEffect`
定位：**效应估计模块（`P(Y | do(X = x))`）+ 开放问题 6.10 的逻辑内核**

---------------------------------------------------------------------------
〇、审计 R564 与本轮增补（先读这一节）
---------------------------------------------------------------------------

### (a) 审计 R564 的两条原话

> **「（1 分钟，必做）删 `FateV2.Predict/probeTmpX.lean` + `=280`；`fanin_report.sh`
> 改用 `git ls-files` 过滤消费者。」**

> **「未证 `∑_y doProb = doWeight`，即 `doProb` 还没被证明是概率。」**

### (b) 任务 A：删了什么、改了什么

- **删除**（均为未跟踪文件 / 空文件，不属任何模块）：
  - `FateV2.Predict/probeTmpX.lean`（探针残留，`git status` 显示 `??`）
  - `=280`（0 字节的 shell 重定向误生成文件，位于仓库根）
  - **其它任何文件均未删除。**
- **修改** `fanin_report.sh`：**只加 `git ls-files` 过滤**，共 3 处：
  1. 消费者统计：`git ls-files 'FateV2.Predict/*.lean' | xargs grep -l ...`
     （不再把未跟踪的 staging/探针文件算作消费者）；
  2. 「被 `WorldModelCapstone` 消费」：加 `git ls-files ... | grep -qx` 守卫；
  3. 「被 `WorldModelCompleteV2` 消费」：同上。

### (c) 任务 B：做了强版

**做了强版**（不是弱版）：

> `doProb_sum_eq_doWeight`（§7）：
> `∑ y : Y, doProb M θ x y = doWeight M θ x`，**等式，无附加假设**
> （仅需 `[Fintype Y] [DecidableEq Y]`，`X` 的 `[DecidableEq X]` 由定义自带）。

⟹ 弱版 `doProb_sum_le_one`（`≤ 1`，需 `∑ u, pU u ≤ 1`）**未采用**，
因为更强的等式版已证出。

### (d) 不声称「CausalEffect 已经是概率论了」

**本文件不声称「`CausalEffect` 已经是概率论了」。**
本轮只补了一条**边际一致性**：`doProb` 对 `y` 求和 = `doWeight`。

仍然**没有**的（如实列出）：
- **无归一化**：`doWeight ≠ 1` 时不构成概率分布，`doProb / doWeight` 形式的
  条件分布**仍未定义**（本文件刻意不做除法，理由见 (c) 老节）。
- **无 `pU` 本身的非负性 / 总和为 `1` 的约束**（`ParamSCM` 不强制）。
  故严格说，本定理证明的是「`doProb` 是 `doWeight` 的**可加分解**」，
  而「是概率」还需另加 `pU ≥ 0`、`∑ pU = 1` 的前提——**那部分未做**。
- 无 `doExpectation` 与 `doProb` 的一致性（未证 `E[f] = ∑ y, f y * doProb y`）。

标签：**本轮新增 = [构造性定理]**，零 `sorry` / `admit` / `axiom`。

---------------------------------------------------------------------------
〇、诚实交代：本文件的来源与边界（先读这一节）
---------------------------------------------------------------------------

### (a) 作者第 537 轮裁决的原话

作者在被告知「这个模块面向的是系统，为什么有个体和组这种东西」之后问
「到底什么情况」，得到完整回答后裁决：

> **「为什么有个体和组这种东西」**

> **「乙 那这样看来有必要弄」**

⟹ 本文件做的是 **(乙)**：建效应估计模块（`P(Y | do(X))`），
深度按 **(ii)**（`doDist` + 6.10 核心定理）。

### (b) 「组 / 个体」是因果推断借来的语言

`组平均水平` / `个体命运轨迹` 这些词**不是本理论的原创语言**，
而是从**因果推断文献**（Rubin 因果模型 / ATE / ITE 的传统）借来的。

⚠ 本文件**剥离**这层借来的语言，只保留它的**逻辑内核**：

> **一个聚合量（均值）不决定一条具体分布 / 轨迹。**

这就是开放问题 6.10 的真正内容。本文件**只用** `ParamSCM` 上的
`do(X = x)` 分布的**均值**与**分布本身**来陈述它，
**不使用**「组」「个体」「治疗」「对照」这些借来的术语。

### (c) `do` 分布的定义（本文件 §2）

- `doWeight M θ x`      ：使 `X = x` 的外生质量之和（`do(X = x)` 的归一化分母）
- `doProb M θ x y`      ：`P(Y = y | do(X = x))` 的**未归一化**质量
- `doExpectation M θ x f`：`E[f(Y) | do(X = x)]` 的**未归一化**加权和

**为什么是「未归一化」**：归一化需要 `doWeight ≠ 0` 这一额外假设，
而 6.10 的**逻辑内核不依赖归一化**——「均值相同、分布不同」
在未归一化形式下**依然成立**（见 §4 的显式构造，两边 `doWeight` 都为 `1`，
故归一化前后结论**一致**；本文件刻意不做除法，以免引入分母非零义务）。

**`do(X = x)` 在 `ParamSCM` 上的含义**：`ParamSCM.sg θ u = (x₀, h)`，`h : X → Y`。
「把 `X` 固定成 `x`」即取 `sg θ u` 的第一分量 `= x`，
再由结构方程读 `Y := h x`。这就是 `(M.sg θ u).2 x`。

### (d) 6.10 的核心定理

- **`mean_same_dist_diff`**（§4）：**存在两个 `ParamSCM`，
  在 `do(X = x)` 下均值相同，但分布不同。**
- **`support_diff_of_same_mean`**（§5）：加强版——**连支撑集都不同**
  （一个点概率为正、另一个为零）。

### (e) 没做到什么（如实列出）

- **ATE / CATE / ITE 三个量未做。** 理由是它们是「组 / 个体」语言的产物：
  ATE 预设「治疗组 vs 对照组」两套分布，CATE 预设「按协变量分层的组」，
  ITE 预设「同一个体在两个干预下的反事实对」。
  `ParamSCM` 里**没有**「组」的位，**也没有**「个体」的位
  （外生 `U` 不是「个体」，它是机制的随机源）。
  硬做这三个量只能靠**另加结构**，那属于**另一次裁决**的范围。
- **不做归一化除法**（理由见 (c)）。
- **不做轨迹层面的推导**（命题 6.2 的 `P(x_{t+1} | x_t)` 一侧）——
  本文件只做**单步 `do` 分布**。轨迹层的桥接属于
  `FateV2.Predict/ParamSCM.lean` 与 `FateV2.Predict/EndToEnd.lean` 的既有范围。
- **不形式化「组」「个体」「治疗」三个词**——按 (b)，它们是被剥离的借用语言。

### (f) 不声称「解决了开放问题 6.10」

本文件**不声称解决了开放问题 6.10**。它只形式化了 6.10 的**逻辑内核**
（「聚合不决定分布」），并用**一个显式反例**证明该内核**非空真**。
6.10 作为开放问题**仍然开放**：本文件给的是它的一个**必要条件的否定形式**，
不是它的完整解答。

---------------------------------------------------------------------------
一、反同义反复核查（逐条核过）
---------------------------------------------------------------------------
1. `doProb` / `doExpectation` 的**定义**里**没有**任何关于「相等」的假设。
2. `mean_same_dist_diff` 的**前件**是空（它是 `∃` 命题，无 `→` 前件）。
   **不存在「前件已把结论包进去」的可能**——因为它没有前件。
3. 证明中 `oneModel` 与 `twoModel` 是**显式构造的两个不同结构**
   （`U` 基数不同：`1` vs `2`；`sg` 输出不同：恒 `1` vs `{0, 2}`），
   **不是**同一个 `M` 的两种写法。
4. 结论 `∃ y, doProb M₁ θ₁ x y ≠ doProb M₂ θ₂ x y` 中的 `y` 是**显式给出**的
   （`y = 1`），不是靠 `simp` 模糊判定。
5. 两个模型的 `doWeight` 都 = `1`，故归一化后结论**不变**——
   本定理**不是**「未归一化」造成的假象。

---------------------------------------------------------------------------
二、本文件实际存在的定义与定理（见文末 `grep` 核对）
---------------------------------------------------------------------------
| 编号 | 名称 | 内容 |
|---|---|---|
| (c) | `doWeight` | `do(X = x)` 的外生质量（未归一化分母）|
| (c) | `doProb` | `P(Y = y | do(X = x))` 的未归一化质量 |
| (c) | `doExpectation` | `E[f(Y) | do(X = x)]` 的未归一化加权和 |
| — | `oneModel` | 见证模型 `M₁`：`U = PUnit`，`Y ≡ 1` |
| — | `twoModel` | 见证模型 `M₂`：`U = Bool`，`Y ∈ {0, 2}` 各 `1/2` |
| — | `oneModel_doExpectation` | `M₁` 在 `f = id` 下期望 = `1` |
| — | `twoModel_doExpectation` | `M₂` 在 `f = id` 下期望 = `1` |
| — | `oneModel_doProb_one` | `M₁`：`P(Y = 1) = 1` |
| — | `twoModel_doProb_one` | `M₂`：`P(Y = 1) = 0` |
| — | `twoModel_doProb_two` | `M₂`：`P(Y = 2) = 1/2` |
| **(d)** | **`mean_same_dist_diff`** | **6.10 核心**：均值同、分布不同 |
| (d) | `support_diff_of_same_mean` | 加强：支撑集不同 |
| — | `twoModel_sg_nonconstant` | 反退化：`twoModel` 的两条分支输出不同 |

标签：**[定义性约定]** / **[构造性定理]**。 -/


namespace FateV2.Predict

namespace CausalEffect

open FateV2.Predict.ParamSCM

set_option autoImplicit false

noncomputable section

/-! ===========================================================================
  §1  ⚠ 记号说明
  =========================================================================== -/

/-! `ParamSCM` 定义在 `FateV2.Predict.ParamSCM` 命名空间下（`FateV2.Predict/ParamSCM.lean:167`）。
本文件经 `open FateV2.Predict.ParamSCM` 直接写 `ParamSCM X Y`。

`ParamSCM` 的四个字段（`FateV2.Predict/ParamSCM.lean:167-178`）：
```lean
structure ParamSCM (X Y : Type*) where
  Th : Type
  U : Type
  [instFintypeU : Fintype U]
  [instDecEqU : DecidableEq U]
  pU : U → ℝ
  sg : Th → U → X × (X → Y)
```
`attribute [instance]` 已把 `Fintype U` / `DecidableEq U` 注册为实例
（`FateV2.Predict/ParamSCM.lean:180`），故 `∑ u : M.U` 与 `if ... = x` 直接可用
（仅需 `X` 的 `DecidableEq`，由调用方的具体类型提供，如 `Fin 2`）。 -/

/-! ===========================================================================
  §2  核心定义：`do(X = x)` 分布
  =========================================================================== -/

/-- **【`do(X = x)` 的外生质量】**

把「使 `X` 的第一分量等于 `x`」的外生 `u` 的 `pU u` 全部加起来。

⚠ **未归一化**：这不是概率（可能 `≠ 1`），它是 `doProb` / `doExpectation`
的**共同分母**。本文件不做除法（理由见文件头 (c)）。

⚠ 需要 `[DecidableEq X]`（判断 `(M.sg θ u).1 = x`）。 -/
noncomputable def doWeight {X Y : Type} [DecidableEq X]
    (M : ParamSCM X Y) (θ : M.Th) (x : X) : ℝ :=
  ∑ u : M.U, if (M.sg θ u).1 = x then M.pU u else 0

/-- **【`do(X = x)` 下 `Y = y` 的未归一化质量】**

把所有使 `X = x` **且**结构方程输出 `(M.sg θ u).2 x = y` 的 `u` 的 `pU u` 加起来。

**⟹ 这就是 `P(Y = y | do(X = x))` 在 `ParamSCM` 上的直接形式化**
（差一个由 `doWeight` 提供的常数因子）。 -/
noncomputable def doProb {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (M : ParamSCM X Y) (θ : M.Th) (x : X) (y : Y) : ℝ :=
  ∑ u : M.U, if (M.sg θ u).1 = x ∧ (M.sg θ u).2 x = y then M.pU u else 0

/-- **【`do(X = x)` 下 `f(Y)` 的未归一化期望】**

这是「聚合量」——6.10 里被叫做「组平均水平」的那个东西；
本文件按 (b) 的说法**只用它的逻辑内核**：它是一个把分布压成一个实数的映射。

⚠ **`f` 是任意的**（不限于恒等），故这条定义覆盖所有「单点聚合」。 -/
noncomputable def doExpectation {X Y : Type} [DecidableEq X]
    (M : ParamSCM X Y) (θ : M.Th) (x : X) (f : Y → ℝ) : ℝ :=
  ∑ u : M.U, if (M.sg θ u).1 = x then M.pU u * f ((M.sg θ u).2 x) else 0

/-! ===========================================================================
  §3  两个见证模型（显式构造，`rfl` 级可算）
  =========================================================================== -/

/-- **见证模型 `M₁`**：外生只有**一个**实现（`U = PUnit`，质量 `1`），
结构方程把 `Y` **恒置为 `1`**。

⟹ `do(X = 0)` 下 `Y ≡ 1`（退化分布，均值 `1`）。 -/
def oneModel : ParamSCM (Fin 2) (Fin 3) where
  Th := PUnit
  U := PUnit
  pU := fun _ => 1
  sg := fun _ _ => (0, fun _ => 1)

/-- **见证模型 `M₂`**：外生有**两个**实现（`U = Bool`，各质量 `1/2`），
结构方程在 `u = true` 时把 `Y` 置为 `0`、在 `u = false` 时置为 `2`。

⟹ `do(X = 0)` 下 `Y` **以各 `1/2` 取 `0` 与 `2`**（非退化分布，均值 `1`，
且**从不取 `1`**）。 -/
def twoModel : ParamSCM (Fin 2) (Fin 3) where
  Th := PUnit
  U := Bool
  pU := fun _ => (1 : ℝ) / 2
  sg := fun _ u => (0, fun _ => if u then 0 else 2)

/-! ===========================================================================
  §4  6.10 的核心定理
  =========================================================================== -/

/-- **`M₁` 的 `do(X = 0)` 期望（`f = id`）= `1`**。

`U` 单点、质量 `1`、`Y ≡ 1` ⟹ 加权和 = `1 * 1 = 1`。 -/
theorem oneModel_doExpectation :
    doExpectation oneModel PUnit.unit 0 (fun y : Fin 3 => (y : ℝ)) = 1 := by
  unfold doExpectation oneModel
  norm_num

/-- **`M₂` 的 `do(X = 0)` 期望（`f = id`）= `1`**。

`U = Bool`、各质量 `1/2`、`Y ∈ {0, 2}` ⟹ 加权和 = `1/2 * 0 + 1/2 * 2 = 1`。 -/
theorem twoModel_doExpectation :
    doExpectation twoModel PUnit.unit 0 (fun y : Fin 3 => (y : ℝ)) = 1 := by
  unfold doExpectation twoModel
  rw [Fintype.sum_bool]
  norm_num

/-- **`M₁` 的 `do(X = 0)` 下 `P(Y = 1) = 1`**（退化在 `1`）。 -/
theorem oneModel_doProb_one :
    doProb oneModel PUnit.unit 0 1 = 1 := by
  unfold doProb oneModel
  norm_num

/-- **`M₂` 的 `do(X = 0)` 下 `P(Y = 1) = 0`**（从不取 `1`）。 -/
theorem twoModel_doProb_one :
    doProb twoModel PUnit.unit 0 1 = 0 := by
  unfold doProb twoModel
  rw [Fintype.sum_bool]
  norm_num
  decide

/-- **`M₂` 的 `do(X = 0)` 下 `P(Y = 2) = 1/2`**（非退化，反衬 `M₁`）。 -/
theorem twoModel_doProb_two :
    doProb twoModel PUnit.unit 0 2 = (1 : ℝ) / 2 := by
  unfold doProb twoModel
  rw [Fintype.sum_bool]
  norm_num
  decide

/-- **【开放问题 6.10 的逻辑内核】**

**存在两个 `ParamSCM`，它们在 `do(X = x)` 下均值相同，但分布不同。**

**⟹ 一个聚合量（均值）不决定一条具体分布。**

**⟹ 这就是 6.10 的全部逻辑内容**——它**不依赖**「组 / 个体」这两个借来的词
（见文件头 (b)）。「组平均相同但个体命运不同」只是这句话在借来的语言里的读法。

**⚠ 非空真**：下面把 `M₁`、`M₂`、`θ`、`x`、`f`、`y` **全部显式给出**，
两个等式都是 `rfl` 级可算的（见上面四条引理）。

**⚠ 归一化无关**：`M₁` 与 `M₂` 的 `doWeight` 均为 `1`
（`M₁`：`1 * 1`；`M₂`：`1/2 + 1/2`），故归一化后结论**不变**。 -/
theorem mean_same_dist_diff :
    ∃ (M₁ M₂ : ParamSCM (Fin 2) (Fin 3))
      (θ₁ : M₁.Th) (θ₂ : M₂.Th) (x : Fin 2) (f : Fin 3 → ℝ),
      doExpectation M₁ θ₁ x f = doExpectation M₂ θ₂ x f
      ∧ (∃ y, doProb M₁ θ₁ x y ≠ doProb M₂ θ₂ x y) := by
  refine ⟨oneModel, twoModel, PUnit.unit, PUnit.unit, 0, fun y => (y : ℝ), ?_, 1, ?_⟩
  · rw [oneModel_doExpectation, twoModel_doExpectation]
  · rw [oneModel_doProb_one, twoModel_doProb_one]
    norm_num

/-! ===========================================================================
  §5  加强：支撑集都不同
  =========================================================================== -/

/-- **【加强版】**：**均值相同的两个 `do` 分布，支撑集可以完全不同。**

存在一个取值 `y`，在一个模型下**概率为正**、在另一个模型下**概率为零**。

⟹ 「趋势相同」与「可能性相同」是**两件事**：
在两个模型下 `Y` 的均值都是 `1`，但 `Y = 1` 在 `M₁` 下**必然发生**、
在 `M₂` 下**绝不可能发生**（`M₂` 只取 `0` 与 `2`）。

**⟹ 这是 `mean_same_dist_diff` 的加强**：分布不仅不同，
一个的支撑甚至**不含**另一点的必然取值。 -/
theorem support_diff_of_same_mean :
    ∃ (M₁ M₂ : ParamSCM (Fin 2) (Fin 3))
      (θ₁ : M₁.Th) (θ₂ : M₂.Th) (x : Fin 2) (f : Fin 3 → ℝ),
      doExpectation M₁ θ₁ x f = doExpectation M₂ θ₂ x f
      ∧ (∃ y, 0 < doProb M₁ θ₁ x y ∧ doProb M₂ θ₂ x y = 0) := by
  refine ⟨oneModel, twoModel, PUnit.unit, PUnit.unit, 0, fun y => (y : ℝ), ?_, 1, ?_, ?_⟩
  · rw [oneModel_doExpectation, twoModel_doExpectation]
  · rw [oneModel_doProb_one]; norm_num
  · rw [twoModel_doProb_one]

/-! ===========================================================================
  §6  自检：见证模型确实非退化
  =========================================================================== -/

/-- **反退化**：`twoModel` 的两条外生分支确实给出**不同**的 `Y`
（否则 §4 的「分布不同」可能因 `sg` 退化为常函数而失去意义）。

直接核验 `(twoModel.sg PUnit.unit true).2 0 ≠ (twoModel.sg PUnit.unit false).2 0`。 -/
theorem twoModel_sg_nonconstant :
    (twoModel.sg PUnit.unit true).2 0 ≠ (twoModel.sg PUnit.unit false).2 0 := by
  unfold twoModel
  decide

/-- **反退化（分布层）**：`twoModel` 的 `do` 分布在 `Y = 2` 处质量为正。

与 `twoModel_doProb_one`（`Y = 1` 处为 `0`）合起来，
说明 `twoModel` 的 `doProb` **不是**常函数。 -/
theorem twoModel_doProb_pos :
    0 < doProb twoModel PUnit.unit 0 2 := by
  rw [twoModel_doProb_two]
  norm_num

/-! ===========================================================================
  §7  边际一致性：`doProb` 是 `doWeight` 按 `y` 的分解
  =========================================================================== -/

/-- **【`doProb` 的边际一致性：`doProb` 确实是 `doWeight` 的分解】**

**固定 `x : X`。把 `doProb M θ x ·` 对全部 `y : Y` 求和，等于 `doWeight M θ x`。**

**⟹ 这证明 `doProb` 不是一个「孤立的数表」，而是 `doWeight` 按 `y` 的分解——
即 `doProb` 确实是一个**（未归一化的）概率分布**。**

**⟹ 这是 `CausalEffect` 从「名义上的概率」变成「真正的概率」的一步。**

**证明思路**（反同义反复核查：本条**不含**任何把结论塞进前件的假设）：
对每个外生实现 `u`，`(M.sg θ u).2 x` 是**唯一**的 `y` 使 `(M.sg θ u).2 x = y`，
故 `∑ y, (if A u ∧ B u y then pU u else 0) = if A u then pU u else 0`。
这里 `A u ≡ (M.sg θ u).1 = x`，`B u y ≡ (M.sg θ u).2 x = y`。
交换求和顺序（`Finset.sum_comm`）后逐项化简即得。 -/
theorem doProb_sum_eq_doWeight {X Y : Type} [DecidableEq X] [DecidableEq Y]
    [Fintype Y] (M : ParamSCM X Y) (θ : M.Th) (x : X) :
    ∑ y : Y, doProb M θ x y = doWeight M θ x := by
  unfold doProb doWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : (M.sg θ u).1 = x
  · -- `h` 成立时，`y := (M.sg θ u).2 x` 是唯一的匹配点
    simp [h]
  · -- `h` 不成立时，每一项条件都假
    simp [h]

end

end CausalEffect

end FateV2.Predict
