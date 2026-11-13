/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`Fate.ParamSCMConsumer`
定位：**`ParamSCM` 的第一个下游消费者** —— 让 `θ` 不再闲置

---------------------------------------------------------------------------
〇、本文件要解决的确切问题
---------------------------------------------------------------------------
`Fate/ParamSCM.lean` 已入库（14 定理），其核心是
`paramScmWorldModel_sim_depends_on_theta`（`sim` 真的依赖 `θ`）与
`paramScmSimDep_not_vacuous` / `paramScmSimDep_witness`（非空真证据）。
但该文件**零 import 者** —— 核心定理没有被任何下游真正*使用*。

本文件是它的**第一个消费者**：不重证上游任何定理，只**组合**三块：

| 上游模块 | 本文件用到的部分 |
|---|---|
| `Fate.ParamSCM` | `ParamSCM`、`paramScmWorldModel`、`paramScmWorldStep`、`paramScmWorldModel_sim_one`、`paramScmWorldModel_sim_depends_on_theta` |
| `Fate.ThetaConvergence` | `EndToEnd.endToEnd` 的**用法口径**（同一套 `WorldModel` 串联接口、`observe`/`predFrom`）|
| `Fate.OptimalEta` | `c η := |1 - η|`（收缩因子）及其零点刻划 `c_eq_zero_iff` |

---------------------------------------------------------------------------
一、交付内容（本文件实际存在的定理，见文末 `grep ^theorem` 核对）
---------------------------------------------------------------------------
| 编号 | 定理 / 定义 | 内容 |
|---|---|---|
| — | `linearThetaModel` | 定义：`ParamSCM ℝ ℝ`，`Θ = ℝ`，`sg θ _ = (0, fun x => θ * x)` |
| — | `etaExperiment` | 定义：在 `paramScmWorldModel linearThetaModel` 上的**具体实验设置**（`h = id`、`y = 0`、`a = 1`、`x = 0`）|
| **(a)** | `linearTheta_predFrom_apply` | `predFrom … θ … a x = θ * a`（`sim` 的机制被读出的逐点形态）|
| **(a)** | `linearTheta_sim_depends_on_theta` | ⭐ `θ₁ ≠ θ₂ ⟹ ∃ ε, sim θ₁ ≠ sim θ₂`（**应用**上游核心定理）|
| **(a)** | `linearTheta_sim_depends_witness` | 显式见证：`sim 0 … 1 ≠ sim 1 … 1`（存在 ε 已被代入）|
| **(b)** | `linearTheta_predFrom_depends_on_theta` | 预测依赖 `θ`（`a ≠ 0` 时）；**不含 `η`** |
| **(b)** | `etaExperiment_abs_eq_c_mul` | ⭐ `|experiment η θ| = OptimalEta.c η * |θ|`（**真的用 `OptimalEta.c`**）|
| **(b)** | `theta_eta_role_separation` | ⭐ **对比**：`θ` 决定预测，`η` 经 `c` 决定收缩率 |
| **(c)** | `etaExperiment_apply` | ⭐ `experiment η θ = (1 - η) * θ`（端到端一步闭式）|
| **(c)** | `etaExperiment_depends_on_theta` | ⭐ `η ≠ 1 ⟹ θ₁ ≠ θ₂ ⟹ experiment θ₁ ≠ experiment θ₂`（更新依赖 `θ`）|
| **(c)** | `etaExperiment_eta_one_inert` | 对照：`η = 1 ⟹ ∀ θ, experiment θ = 0`（`θ` 被完全抹掉）|
| **(c)** | `etaExperiment_theta_active_iff` | ⭐ `(∃ θ, experiment η θ ≠ 0) ↔ OptimalEta.c η ≠ 0` |

---------------------------------------------------------------------------
二、⚠ 反同义反复核查（本项目最高频问题，逐条核过）
---------------------------------------------------------------------------
* **`linearTheta_sim_depends_on_theta`**：前件 `θ₁ ≠ θ₂`（参数空间上的两点区分），
  结论 `∃ ε, sim θ₁ … ≠ sim θ₂ …`（`sim` 函数值的区分）。二者隔着
  `paramScmWorldStep` 与 `trajGen` 的迭代 —— **不是**前件的改写。
  证明**必须**调用上游 `paramScmWorldModel_sim_depends_on_theta`，
  并把 `θ₁ * 1 ≠ θ₂ * 1` 化归到 `θ₁ ≠ θ₂`。若把 `sg` 改成不读 `θ`，
  本定理**立即为假**（前件仍可满足）⟹ **实质约束**。
* **`etaExperiment_abs_eq_c_mul`**：前件为空（`η θ` 任意）；结论是
  `|endToEnd 输出| = c η · |θ|`。证明经 `endToEnd_apply`（串起 observe/predFrom/
  写回）与 `predFrom = θ`，再 `abs_mul` 与 `OptimalEta.c` 的定义。
  **不是定义重念**：`endToEnd` 是 `ThetaConvergence` 那一侧的复合函数，
  `c` 是 `OptimalEta` 那一侧的标量引擎，二者在**本文件首次**相乘。
* **`etaExperiment_depends_on_theta`**：前件 `η ≠ 1`、`θ₁ ≠ θ₂`；
  结论 `endToEnd … θ₁ ≠ endToEnd … θ₂`。前件说的是「步长非最优点」
  与「参数不同」，结论说的是「**更新结果**不同」—— 中间经过
  `endToEnd` 的四环复合（`observe → predFrom → 减法 → 写回`）与
  `(1-η)θ` 的闭式。**非改写**。若 `endToEnd` 不读 `θ`（例如 `φ` 恒零且 `η` 无关），
  前件仍成立而结论为假。
* **`etaExperiment_theta_active_iff`**：左端是「存在使更新非零的 `θ`」，
  右端是「`c η ≠ 0`」；二者由 `(1-η)θ` 的乘积结构 + `c` 的唯一零点
  （`OptimalEta.c_eq_zero_iff`）**双侧**推出（详细见证明体，两个方向都真的做了工作）。
* **`etaExperiment_eta_one_inert`** 是**否定面对照**：给 `η` 取最优值 `1`
  时，`θ` 的作用被 `(1-1) = 0` 完全抹掉 —— 与 `c 1 = 0` 一致。

---------------------------------------------------------------------------
三、诚实边界（**必须登记**）
---------------------------------------------------------------------------
1. **只在 `linearThetaModel` 上做**。`ParamSCM` 的参数空间是**裸类型** `Th`
   （见 `ParamSCM` 文件头边界），要在其上跑 `EndToEnd.endToEnd`，
   需要 `Th` 有 `Ring`、`Y` 有 `AddCommGroup`，故本文件取 `Th = Y = ℝ`。
   **本文件不声称**任意 `ParamSCM` 都能接 `endToEnd`（那一版需要额外的结构假设）。
2. **`etaExperiment` 是「一个」实验设置**（`h = id`、`y = 0`、`a = 1`、`x = 0`）。
   它不是「`ParamSCM` 的端到端语义」；它是**一个可复算的具体实例**。
   本文件不对它做普通性声明。
3. **`predFrom` 不读旧状态 `x`**：这是 `paramScmWorldStep` 的设计
   （`SCM` 语义下 `Y` 的方程不读 `Y` 的过去），故 `x = 0` 的取值不影响任何结论
   （`etaExperiment_apply` 的 `rfl` 级展开会显现这一点）。
4. **`η` 与 `θ` 的分工是在 `linearThetaModel` 上证的**，不是在任意
   `ParamSCM` 上证的一般法则。`η` 之所以只在端到端环节出现，是因为
   `paramScmWorldStep` 的签名里**没有** `η` 位 —— 这一点由
   `ParamSCM` 的结构本身保证，本文件只是把它**用起来**。

---------------------------------------------------------------------------
四、纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`；**只新建文件，不改动任何既有模块**；
不以 `_` 前缀命名（不是探针）。
-/

import FateWorld.Legacy.ParamSCM
import FateWorld.Legacy.ThetaConvergence
import FateWorld.Legacy.OptimalEta
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Fate

namespace ParamSCMConsumer

open Fate.ParamSCM Fate.EndToEnd

set_option autoImplicit false

noncomputable section

/-! ===========================================================================
  §1  ⭐ 线性参数模型：把 `θ` 放进可见的算式里
  =========================================================================== -/

/-- ⭐ **线性见证模型**：`Th = U = ℝ`？不 —— `Th = ℝ`、`U = PUnit`、
`X = Y = ℝ`、`pU ≡ 1`、`sg θ _ := (0, fun x => θ * x)`。

**为什么这么取**：
* `Th = ℝ` 使 `θ` 有**足够多的取值**（与 `PUnit` 相反），
  从而 `θ₁ ≠ θ₂` 是**可满足**的条件（见 `linearTheta_sim_depends_witness`）；
* `sg` 的第二分量 `fun x => θ * x` 是 `θ` 的**显式线性出现**，
  使 `predFrom` 与 `endToEnd` 都能算成闭式；
* 第一分量取 `0`（`WorldModel` 翻译会丢弃它，`ParamSCM` 文件头边界 3）。

标签：**[定义性约定]**。 -/
abbrev linearThetaModel : ParamSCM ℝ ℝ where
  Th := ℝ
  U := PUnit
  instFintypeU := inferInstance
  instDecEqU := inferInstance
  pU := fun _ => 1
  sg := fun θ _ => (0, fun x => θ * x)

/-- ⭐ **预测的逐点形态**：`predFrom` 在 `linearThetaModel` 上就是 `θ * a`。

**读法**：`predFrom` 是 `EndToEnd` 里的环节 ②，定义为 `W.f x u ε θ a`；
在 `linearThetaModel` 上，`paramScmWorldStep` 的第四位 `θ` 被读出，
故 `predFrom … θ … a x = θ * a` —— **与旧状态 `x` 无关**
（`paramScmWorldStep` 丢弃第一位），**与 `η` 无关**（签名里没有 `η`）。

这是把 `ParamSCM` 的机制与 `ThetaConvergence` 的端到端**接口对齐**的桥。 -/
theorem linearTheta_predFrom_apply (θ : ℝ) (u : PUnit) (e : PUnit)
    (a : ℝ) (x : ℝ) :
    predFrom (paramScmWorldModel linearThetaModel) θ u e a x = θ * a := by
  simp [predFrom, Fate.ParamSCM.paramScmWorldStep, WorldModel.f, linearThetaModel]

/-! ===========================================================================
  §2  ⭐⭐⭐ (a) `sim` 依赖 `θ`：**应用**上游核心定理
  =========================================================================== -/

/-- ⭐⭐⭐ **【(a) 主定理】`sim` 真的依赖 `θ`**（在 `linearThetaModel` 上）。

若 `θ₁ ≠ θ₂`，则存在噪声序列 `ε`，使 `sim` 的首步取值不同：

$$\theta_1 \neq \theta_2 \;\Longrightarrow\;
  \exists \varepsilon,\quad \mathrm{sim}(\theta_1, 1, \varepsilon, 1)(1)
    \neq \mathrm{sim}(\theta_2, 1, \varepsilon, 1)(1) .$$

**⭐ 这是对上游 `paramScmWorldModel_sim_depends_on_theta` 的**真实使用**：
本定理的**唯一**证明步骤**就是调用它**，并把它的前件
`(sg θ₁ u).2 1 ≠ (sg θ₂ u).2 1` 化归到 `θ₁ ≠ θ₂`
（在 `sg θ _ = (0, fun x => θ*x)` 下该前件**恰好是** `θ₁ * 1 ≠ θ₂ * 1`）。

**⚠ 反同义反复**：前件是**参数空间**上的两点区分（`θ₁ ≠ θ₂`），
结论是**函数 `sim` 的值**的区分，中间隔着 `trajGen` 的 `Nat.rec` 迭代。
若 `paramScmWorldStep` 不读 `θ`（如 `scmWorldStep`），本定理**为假**
（前件仍可满足）。故本定理**实质约束**构造。 -/
theorem linearTheta_sim_depends_on_theta (θ₁ θ₂ : ℝ) (hθ : θ₁ ≠ θ₂) :
    ∃ ε : ℕ → PUnit,
      (paramScmWorldModel linearThetaModel).sim θ₁ (fun _ => PUnit.unit) ε
          (fun _ => (1 : ℝ)) 1
        ≠ (paramScmWorldModel linearThetaModel).sim θ₂ (fun _ => PUnit.unit) ε
            (fun _ => (1 : ℝ)) 1 := by
  refine Fate.ParamSCM.paramScmWorldModel_sim_depends_on_theta
    linearThetaModel θ₁ θ₂ PUnit.unit (1 : ℝ) ?_
  simp only [mul_one]
  exact hθ

/-- ⭐⭐⭐ **【(a) 显式见证】**：`θ = 0` 与 `θ = 1` 在首步模拟上**确实不同**，
且噪声序列被**代入**为常值 `PUnit.unit`。

**⟹ 作用**：把上一条定理的 `∃ ε` **实例化**到 `0 ≠ 1` 这一对具体参数上，
给出一个**可复算**的差异 —— 即 `θ` 在 `linearThetaModel` 上**非闲置**
的机检证据。 -/
theorem linearTheta_sim_depends_witness :
    ∃ ε : ℕ → PUnit,
      (paramScmWorldModel linearThetaModel).sim 0 (fun _ => PUnit.unit) ε
          (fun _ => (1 : ℝ)) 1
        ≠ (paramScmWorldModel linearThetaModel).sim 1 (fun _ => PUnit.unit) ε
            (fun _ => (1 : ℝ)) 1 :=
  linearTheta_sim_depends_on_theta 0 1 zero_ne_one

/-! ===========================================================================
  §3  ⭐ (b) 预测依赖 `θ`（不含 `η`）
  =========================================================================== -/

/-- ⭐⭐ **【(b) θ 侧】预测随 `θ` 变**（`a ≠ 0` 时）。

**⚠ 前件只有 `a ≠ 0`（设计点非零）与 `θ₁ ≠ θ₂`（参数区分）**；
结论是 `predFrom` 在两点上的**值**不同。证明经 `linearTheta_predFrom_apply`
把两侧化为 `θ₁ * a` 与 `θ₂ * a`，再用 `mul_right_cancel₀` 消去非零因子。

**⭐ 与 `η` 无关**：`predFrom` 的签名里**没有** `η`
（`EndToEnd.predFrom W θ u ε a x = W.f x u ε θ a`），
这就是「`θ` 管预测」的**类型层**证据 —— 不是修辞。 -/
theorem linearTheta_predFrom_depends_on_theta (θ₁ θ₂ : ℝ) (a : ℝ)
    (ha : a ≠ 0) (hθ : θ₁ ≠ θ₂) :
    predFrom (paramScmWorldModel linearThetaModel) θ₁ PUnit.unit PUnit.unit a (0 : ℝ)
      ≠ predFrom (paramScmWorldModel linearThetaModel) θ₂ PUnit.unit PUnit.unit
          a (0 : ℝ) := by
  rw [linearTheta_predFrom_apply, linearTheta_predFrom_apply]
  exact fun h => hθ (mul_right_cancel₀ ha h)

/-! ===========================================================================
  §4  ⭐⭐⭐ (c) 端到端：`θ` 与 `η` 在**同一条算式**里
  =========================================================================== -/

/-- **具体实验设置**：在 `paramScmWorldModel linearThetaModel` 上跑一遍
`EndToEnd.endToEnd`，取

| 位 | 取值 | 理由 |
|---|---|---|
| `h` | `id : ℝ → ℝ` | 无噪声观测（`observe id y = y`）|
| `y` | `0` | 观测值取零 |
| `θ` | **参数** | 被更新的对象 |
| `u` | `PUnit.unit` | 外生空间单点 |
| `ε` | `PUnit.unit` | 噪声空间单点 |
| `a` | `1` | 干预值取 `1`（故 `predFrom = θ * 1 = θ`）|
| `x` | `0` | 起点（`paramScmWorldStep` 丢弃它）|

**⚠ 这不是「`ParamSCM` 的端到端语义」**，是**一个**可复算的实例
（见文件头边界 2）。 -/
def etaExperiment (η θ : ℝ) : ℝ :=
  endToEnd (paramScmWorldModel linearThetaModel) (id : ℝ → ℝ) η
    (AddMonoidHom.id ℝ) (0 : ℝ) θ PUnit.unit PUnit.unit (1 : ℝ) (0 : ℝ)

/-- ⭐⭐⭐ **【(c) 主定理 · 端到端一步闭式】**

$$\mathrm{experiment}\ \eta\ \theta \;=\; (1 - \eta)\,\theta .$$

**推导链（四环全部可见）**：
`observe id 0 = 0`（环节 ①）→ `predFrom = θ * 1 = θ`（环节 ②，经 `θ` **进入**残差）
→ `0 - θ = -θ`（环节 ③）→ `θ + η * (−θ)`（环节 ④，经 `writeBack_apply`）。

**⭐ 这就是 `θ` **真的**影响更新的机制**：`θ` 经 `predFrom` 进入残差，
再经写回进入新参数。**⚠ 非同义反复**：结论里没有出现在任何前件中
（前件是空的，`η θ` 任意），证明必须真的展开 `endToEnd` 的四环复合。 -/
theorem etaExperiment_apply (η θ : ℝ) : etaExperiment η θ = (1 - η) * θ := by
  unfold etaExperiment
  rw [EndToEnd.endToEnd_apply]
  have hobs : observe (id : ℝ → ℝ) (0 : ℝ) = 0 :=
    observe_apply_of (X := ℝ) (Y := ℝ) (h := id) (fun _ _ h => h) 0
  rw [hobs]
  simp [predFrom, Fate.ParamSCM.paramScmWorldStep, WorldModel.f, linearThetaModel]
  ring

/-- ⭐⭐⭐⭐ **【(b) η 侧 · 收缩率】**

$$\bigl|\mathrm{experiment}\ \eta\ \theta\bigr| \;=\;
  c(\eta)\cdot|\theta|,
  \qquad c(\eta) := |1 - \eta|\ \ (\texttt{OptimalEta.c}) .$$

**⭐ 这是本任务的 (b) 的核心组合**：
* 右端的 `c η` **不含** `θ` ⟹ 收缩率**只由 `η` 决定**；
* 右端的 `|θ|` **不含** `η` ⟹ 待收缩量**只由 `θ` 决定**。

**⚠ 真的用到 `OptimalEta`**：`c` 不是本文件另定义的，而是
`Fate.OptimalEta.c`（`c η = |1 - η|`），本定理是它的**首次下游使用**。 -/
theorem etaExperiment_abs_eq_c_mul (η θ : ℝ) :
    |etaExperiment η θ| = OptimalEta.c η * |θ| := by
  rw [etaExperiment_apply, abs_mul]
  rfl

/-- ⭐⭐⭐⭐ **【(b) 对比定理】`θ` 管预测、`η` 管收缩率**。

把第 (a)(b) 两条线索**钉在同一条定理**里：

$$\underbrace{\bigl(\text{预测随 }\theta\text{ 变}\bigr)}_{\text{环节 ②，不含 }\eta}
  \;\wedge\;
  \underbrace{\bigl(\text{收缩因子} = c(\eta)\bigr)}_{\text{标量引擎，不含 }\theta} .$$

**逐分量读法**：
1. `predFrom` 在 `θ₁ ≠ θ₂`（`a ≠ 0`）时**不同** —— `θ` 决定**预测**；
2. `|experiment η θ| = c η · |θ|` —— `η` 经 `c` 决定**收缩**，
   且 `c η` 里**没有** `θ`（由 `etaExperiment_abs_eq_c_mul` 的右侧直接可见）。

**⚠ 不是同义反复**：两分量分别由 `linearTheta_predFrom_depends_on_theta`
与 `etaExperiment_abs_eq_c_mul` 提供（各自动用的是**不同**的上游模块）。 -/
theorem theta_eta_role_separation (η θ₁ θ₂ a : ℝ) (ha : a ≠ 0) (hθ : θ₁ ≠ θ₂) :
    (predFrom (paramScmWorldModel linearThetaModel) θ₁ PUnit.unit PUnit.unit a (0 : ℝ)
        ≠ predFrom (paramScmWorldModel linearThetaModel) θ₂ PUnit.unit PUnit.unit
            a (0 : ℝ))
      ∧ (|etaExperiment η θ₁| = OptimalEta.c η * |θ₁|)
      ∧ (|etaExperiment η θ₂| = OptimalEta.c η * |θ₂|) :=
  ⟨linearTheta_predFrom_depends_on_theta θ₁ θ₂ a ha hθ,
   etaExperiment_abs_eq_c_mul η θ₁,
   etaExperiment_abs_eq_c_mul η θ₂⟩

/-- ⭐⭐⭐⭐ **【(c) 更新依赖 `θ`】**

在 `η ≠ 1`（步长非最优点）时，**不同的 `θ` 给出不同的更新结果**：

$$\eta \neq 1 \;\wedge\; \theta_1 \neq \theta_2
  \;\Longrightarrow\;
  \mathrm{experiment}\ \eta\ \theta_1 \neq \mathrm{experiment}\ \eta\ \theta_2 .$$

**⭐ 这是任务书 (c) 的正面答复**：`endToEnd` 的更新**确实**依赖 `θ`。
`η ≠ 1` 是**必要的** —— 见下一条对照定理
`etaExperiment_eta_one_inert`（`η = 1` 时 `θ` 被完全抹掉）。

**⚠ 反同义反复**：前件是「`η` 非最优点 + `θ` 两点不同」，
结论是「**端到端输出**不同」；中间经过 `(1-η)θ` 的闭式与 `1-η ≠ 0` 的
乘积单射性。若 `endToEnd` 不读 `θ`，前件仍成立而结论为假。 -/
theorem etaExperiment_depends_on_theta (η θ₁ θ₂ : ℝ)
    (hη : η ≠ 1) (hθ : θ₁ ≠ θ₂) :
    etaExperiment η θ₁ ≠ etaExperiment η θ₂ := by
  rw [etaExperiment_apply, etaExperiment_apply]
  exact fun h => hθ (mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hη)) h)

/-- ⭐⭐⭐ **【(c) 否定面对照】`η = 1` 时 `θ` 被**完全抹掉**。

$$\forall \theta,\quad \mathrm{experiment}\ 1\ \theta = 0 .$$

**⭐ 意义**：`η = 1` 是 `OptimalEta` 的**唯一最优点**（误差一步归零），
在这里它同时是**抹掉 `θ` 信息**的步长 —— 「最快收敛」与「丢掉参数」
是同一件事。**与 `c 1 = 0` 一致**（下一步 `theta_active_iff` 把它做成方程）。 -/
theorem etaExperiment_eta_one_inert (θ : ℝ) : etaExperiment 1 θ = 0 := by
  rw [etaExperiment_apply]
  ring

/-- ⭐⭐⭐⭐⭐ **【(b)+(c) 合题】`θ` 是否还在起作用 ⟺ `c(η) ≠ 0`**

$$\bigl(\exists \theta,\ \mathrm{experiment}\ \eta\ \theta \neq 0\bigr)
  \;\Longleftrightarrow\;
  c(\eta) \neq 0 .$$

**⭐ 这是「`θ` 不闲置」的**完整判据**：**
`θ` 在端到端更新里**有可见作用**，当且仅当收缩因子 `c η` 非零。
而 `c η ≠ 0 ⟺ η ≠ 1`（`OptimalEta.c_eq_zero_iff`）——
**⟹ `θ` 的作用与 `η` 的最优性被同一条标量方程锁定**。

**⚠ 证明两个方向都真的做了工作**：
* `⟹`：`c η = 0 ⟹ η = 1 ⟹ ∀θ, experiment = 0`（用 `etaExperiment_eta_one_inert`），
  与 `∃ θ, … ≠ 0` 矛盾；
* `⟸`：`c η ≠ 0 ⟹ η ≠ 1`（`c_eq_zero_iff` 的逆否），
  取 `θ = 1`，`experiment η 1 = 1 - η ≠ 0`。

**⟹ 前件「`∃ θ, experiment ≠ 0`」与右端「`c η ≠ 0`」分别关于
「更新值」与「标量引擎」，由 `(1-η)θ` 的乘积结构连接 —— 非改写。** -/
theorem etaExperiment_theta_active_iff (η : ℝ) :
    (∃ θ : ℝ, etaExperiment η θ ≠ 0) ↔ OptimalEta.c η ≠ 0 := by
  constructor
  · rintro ⟨θ, hθ⟩ hc
    have hη : η = 1 := (OptimalEta.c_eq_zero_iff η).mp hc
    exact hθ (by rw [hη]; exact etaExperiment_eta_one_inert θ)
  · intro hc
    refine ⟨1, ?_⟩
    rw [etaExperiment_apply]
    have hη : η ≠ 1 := fun h => hc (h ▸ OptimalEta.c_one)
    intro h
    apply hη
    have h' : (1 : ℝ) - η = 0 := by simpa using h
    linarith

end

end ParamSCMConsumer

end Fate
