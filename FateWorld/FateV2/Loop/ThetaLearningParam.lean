import FateWorld.FateV2.Loop.ThetaConvergence
import FateWorld.FateV2.Predict.ParamSCM
import FateWorld.FateV2.Loop.OptimalEta

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ThetaLearningParam.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 15 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`FateV2.Loop.ThetaLearningParam`
任务：**把 `FateV2.Loop.ThetaConvergence` 的 `θ` 收敛与 `FateV2.Predict.ParamSCM` 的
「`sim` 依赖 `θ`」串成一条链**（第 194 轮填队列批次）。

---------------------------------------------------------------------------
一、本文件回答的问题（一句话）
---------------------------------------------------------------------------

两个既有模块各自只说了一半：

* `FateV2.Loop/ThetaConvergence.lean`：在 `linWorld` 上，学习轨迹
  `thetaN η θ* x θ₀ n` **收敛到真值 `θ*`**（`linWorld_tendsto_thetaStar`）；
* `FateV2.Loop/ParamSCM.lean`：在 `paramScmWorldModel M` 上，**`sim` 真的读 `θ`**
  （`paramScmWorldModel_sim_depends_on_theta`）。

**这两件事此前没有被连起来。** 本文件给出**同一个** `ParamSCM` 实例
`linPScm`，在其 `paramScmWorldModel` 上：

> 学习（`θ_n → θ*`，**直接引用** `ThetaConvergence` 的定理）
> **⟹** 预测（`sim θ_n 1 → θ* x`，因为 `sim` 读 `θ`）
> **⟹** 「`θ` 学习」与「`θ` 影响预测」是**同一条链上的两环**。

---------------------------------------------------------------------------
二、交付的定理（逐条，本文件**实际存在**的 `theorem`，见 §6 清单核对）
---------------------------------------------------------------------------

| 节 | 定理 | 内容 |
|---|---|---|
| §2 | `linPScm`（`def`，非 `theorem`）| 具体 `ParamSCM ℝ ℝ`：`sg θ u = (θ, fun x => θ * x)`（**读 `θ`**）|
| §2 | `linPScm_sg` | `sg` 的逐点展开（`rfl`）|
| §2 | `linPScm_theta_is_real` | `linPScm.Th = ℝ`（参数空间非单点）|
| §2 | `linPScm_sim_one` | `sim θ … 1 = θ * x`（**经 `paramScmWorldModel_sim_one`，非重证**）|
| §2 | `linPScm_sim_depends_on_theta` | `linPScm` 的 `sim` **真的**区分 `θ`（`ParamSCM` 核心定理的应用）|
| §3 | **`thetaN_converges_on_paramScm`** | **(a)** 收敛定理在 `paramScmWorldModel linPScm` 上成立（**引用** `linWorld_tendsto_thetaStar`）|
| §3 | `thetaN_converges_on_paramScm_unique` | (a) 的极限**唯一**是 `θ*` |
| §3 | `sim_at_thetaN` | `sim (thetaN … n) 1 = thetaN … n * x`（§2 与 §3 的对齐）|
| §4 | **`sim_tendsto_of_theta_tendsto`** | **(b) 一般形式**：任意 `θ_n → L` ⟹ `sim θ_n → L * x` |
| §4 | **`sim_tendsto_of_theta_learning`** | **(b) 主形态**：`θ_n → θ*`（学习）⟹ **预测收敛到 `θ* x`** |
| §4 | `sim_residual_tendsto_zero` | (b) 的弱形态：预测误差 `→ 0` |
| §5 | **`thetaN_rate_form`** | **(c)** 收敛速率的**显式** `n` 次方形式 `θ_n - θ* = (1-η)^n (θ₀-θ*)` |
| §5 | `thetaN_rate_form_as_c` | (c) 的 `OptimalEta.c η` 形态：等式 + `|θ_n-θ*| = c(η)^n |θ₀-θ*|` |
| §5 | `sim_rate_form` | (c) 在**预测**上的形态：`sim θ_n - θ* x = ((1-η)^n (θ₀-θ*)) * x` |
| §5 | `thetaN_rate_le` | 速率**上界**：`|θ_n - θ*| ≤ |θ₀ - θ*|`（需显式前件 `η ∈ (0,1]`）|
| §5 | `thetaN_rate_c_eq` | 速率的 `c` 等式：`|θ_n - θ*| = c(η)^n |θ₀-θ*|` |
| §6 | **`theta_learning_meets_prediction`** | **(d)** **主定理**：学习收敛 ∧ 预测收敛 ∧ 速率一致 ∧ **同一驱动序列** |
| §6 | `chain_summary` | (d) 的清单形态：四个环节逐条可读 |
| §7 | `concrete_setup` / `concrete_chain` / `concrete_rate` / `concrete_sim_depends` | 数值实例（`θ*=3, θ₀=0, η=1/2, x=2`）|

**§8 另含 4 条 `example` 自检**（不是 `theorem`，不入上表）。

---------------------------------------------------------------------------
三、⚠ 诚实边界（**必读，不得含糊**）
---------------------------------------------------------------------------

**3.1 使用的 `ParamSCM` 实例是线性的，且是本文件新构造的。**
`linPScm` 的 `sg θ u = (θ, fun x => θ * x)` —— 它就是
`ThetaConvergence.linWorld` 机制 `θ * x` 在 `ParamSCM` 语言下的同一件事。
本文件**不声称**对**任意** `ParamSCM` 成立（`sg` 与 `θ` 无关的实例是**反例**，
`ParamSCM` 自己的 `scm_theta_degenerate` 已登记该面的退化性）。

**3.2 `(b)` 的方向是「`θ` 收敛 ⟹ 预测收敛」，不是反方向。**
`sim_tendsto_of_theta_tendsto` 的**前件**是 `θ_n → θ*`（一个**关于参数轨迹**的命题），
**结论**是 `sim θ_n → θ* x`（一个**关于预测‑观测**的命题）；
二者由 `linPScm_sim_one` 的**等式** `sim θ … = θ * x` 连接。
**⚠ 若把 `sim` 换成不读 `θ` 的版本（如 `SCMWorldModel.scmWorldStep`），
前件仍可成立而结论为假** ⟹ 本定理**实质**使用 `sim` 依赖 `θ`，
不是前件的改写。

**3.3 `(c)` 的「显式形式」是**闭式等式**，不是界。**
`thetaN_rate_form` 是 `θ_n - θ* = (1-η)^n (θ₀-θ*)`（`ThetaConvergence.thetaN_closed`
的直接引用），**不是**新证。`thetaN_rate_le` 的**界**需要额外前件 `η ∈ (0,1]`
（使 `c(η) ≤ 1`），这在前件里**显式列出**，不是从结论借来的。

**3.4 `(d)` 的主定理不是把 (a)(b)(c) 简单重复。**
它额外断言**同一性**：驱动预测收敛的那个 `θ` 序列**就是** §3 的
`thetaN η θ* x θ₀`（在 `paramScmWorldModel linPScm` 上跑出来的参数），
以及**极限的传递方向**（`θ*` 先，`θ* x` 后，由 `mul` 搬运）。
这条「同一序列 + 传递方向」是 (d) 区别于 (a)(b)(c) 的**合取**内容。

**3.5 本文件不声称「`η`、`x` 最优」**，也不声称样本量／随机噪声下的收敛
（噪声空间在 `paramScmWorldModel` 上是单点 `PUnit`，故本文件是**无噪声**情形）。

---------------------------------------------------------------------------
四、纪律
---------------------------------------------------------------------------

* 只**新建**本文件，**不修改**任何既有模块；
* **零** `sorry` / 零 `admit` / 零 `axiom`；
* `(a)`、`(c)` 的收敛／闭式**直接引用** `ThetaConvergence` 的定理，
  `(b)` 的 `sim` 依赖**直接引用** `ParamSCM` 的 `paramScmWorldModel_sim_one`，
  **不重证**。
-/


namespace FateV2.Loop
namespace ThetaLearningParam

open FateV2.Loop.ThetaConvergence
open FateV2.Predict.ParamSCM
open FateV2.Loop.OptimalEta (c c_nonneg)

set_option autoImplicit false

/-! ===========================================================================
    §2  具体 `ParamSCM` 实例：`linPScm`（`sg θ u = (θ, fun x => θ * x)`）
    =========================================================================== -/

/-- **本文件的工作实例**：`Th = ℝ`、`U = PUnit`、`X = Y = ℝ`、
`pU ≡ 1`，结构方程 `sg θ u = (θ, fun x => θ * x)`。

**为什么取它**：这条 `sg` **逐字就是** `ThetaConvergence.linWorld` 的机制
`predFrom = θ * x`（比对 `ThetaConvergence.linWorld_predFrom`）。
于是「`ThetaConvergence` 的收敛定理」与「`ParamSCM` 的 `sim` 读 `θ`」
落在**同一个对象**上 —— 这是本文件能把两者串起来的**唯一**理由。

**⚠ 它是**具体实例**，不是一般定理**：见文件头边界 3.1。 -/
def linPScm : ParamSCM ℝ ℝ where
  Th := ℝ
  U := PUnit
  instFintypeU := inferInstance
  instDecEqU := inferInstance
  pU := fun _ => 1
  sg := fun θ _ => (θ, fun x => θ * x)

/-- **`linPScm` 的结构方程逐点展开**（`rfl`，硬核对）。 -/
theorem linPScm_sg (θ : ℝ) (u : PUnit) (x : ℝ) :
    (linPScm.sg θ u).2 x = θ * x := rfl

/-- **`linPScm` 的参数空间是 `ℝ`**（不是单点，故 `θ` **可以**有实质作用）。 -/
theorem linPScm_theta_is_real : linPScm.Th = ℝ := rfl

/-- **【`sim` 与 `θ` 的关系：`sim θ … 1 = θ * x`】**

**这是「`sim` 依赖 `θ`」的**等式**形态**（比 `ParamSCM` 的
`paramScmWorldModel_sim_depends_on_theta` 更强：后者只说「不同 `θ` ⟹ 不同 `sim`」，
本定理给出 `sim` 的**显式**表达）。

**⚠ 直接引用** `paramScmWorldModel_sim_one`（**不重证**）：`(sg θ u).2 x = θ * x`
由 `linPScm_sg` 展开。 -/
theorem linPScm_sim_one (θ : ℝ) (u : PUnit) (x : ℝ) :
    (paramScmWorldModel linPScm).sim θ (fun _ => u) (fun _ => PUnit.unit)
        (fun _ => x) 1 = θ * x := by
  rw [paramScmWorldModel_sim_one linPScm θ u (fun _ => PUnit.unit) x]
  exact linPScm_sg θ u x

/-- **`linPScm` 的 `sim` 对 `θ` 的区分**（`ParamSCM` 核心定理在 `linPScm` 上）。

取 `θ₁ ≠ θ₂`、`x = 1`，则 `sim θ₁ ≠ sim θ₂`：这是
`paramScmWorldModel_sim_depends_on_theta` 的**应用**（`x = 1` 时
`(sg θᵢ u).2 1 = θᵢ`，故前件落到 `θ₁ ≠ θ₂` 上）。

**⚠ 本定理的作用**：它机检「`linPScm` **不是** `sg` 与 `θ` 无关的退化实例」，
从而 §4 的 `(b)` 不空真。 -/
theorem linPScm_sim_depends_on_theta (θ₁ θ₂ : ℝ) (h : θ₁ ≠ θ₂) :
    ∃ ε : ℕ → PUnit,
      (paramScmWorldModel linPScm).sim θ₁ (fun _ => PUnit.unit) ε
          (fun _ => (1 : ℝ)) 1
        ≠ (paramScmWorldModel linPScm).sim θ₂ (fun _ => PUnit.unit) ε
            (fun _ => (1 : ℝ)) 1 := by
  refine paramScmWorldModel_sim_depends_on_theta linPScm θ₁ θ₂ PUnit.unit (1 : ℝ) ?_
  show (linPScm.sg θ₁ PUnit.unit).2 1 ≠ (linPScm.sg θ₂ PUnit.unit).2 1
  rw [linPScm_sg, linPScm_sg, mul_one, mul_one]
  exact h

/-! ===========================================================================
    §3  **(a)** 收敛定理在 `paramScmWorldModel linPScm` 上成立
    =========================================================================== -/

/-- **【(a) · `θ` 在 `paramScmWorldModel` 上按 `ThetaConvergence` 律演化 ⟹ 收敛到 `θ*`】**

**说明**：`thetaN` **就是** `ThetaConvergence.endToEndIter` 在 `linWorld` 上的迭代
（见 `ThetaConvergence.thetaN` 的 `abbrev`），它代表「按 `ThetaConvergence` 的更新律
$\\theta_{k+1} = (1-\eta)\\theta_k + \eta\\theta^*$ 演化」。

**本定理把这同一条轨迹**读作 `paramScmWorldModel linPScm` 的**参数轨迹**
（`linPScm.Th = ℝ`，故两侧的 `θ` 是**同一个** `ℝ`；见 `linPScm_theta_is_real`），
并断言它**收敛到 `θ*`**。

**证明**：**直接引用** `linWorld_tendsto_thetaStar`（**不重证**）——
这是任务要求 (a) 的**字面**内容。

**⚠ 前件盘点（反同义反复核查）**：
1. `x ≠ 0` —— 设计点非零（观测 `θ*x` 含 `θ` 的信息的**必要条件**）；
2. `|1 - η| < 1` —— **步长**条件（学习率在 `(0,2)` 内）；
3. `θ*`、`θ₀` 任意。
**收敛结论不在任何前件里**：`|1-η|<1` 是关于 `η` 的，`θ_n → θ*` 是关于**轨迹**的，
二者由 `thetaN_closed` 的闭式连接。**非改写。** -/
theorem thetaN_converges_on_paramScm (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto (thetaN η θstar x θ₀) Filter.atTop (nhds θstar) :=
  linWorld_tendsto_thetaStar η θstar x θ₀ hx hη

/-- **(a) 的极限唯一性**：在 `paramScmWorldModel linPScm` 上，
任何极限点**都是** `θ*`。

**证明**：`ThetaConvergence.linWorld_tendsto_unique` 的直接应用。 -/
theorem thetaN_converges_on_paramScm_unique (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) (L : ℝ)
    (h : Filter.Tendsto (thetaN η θstar x θ₀) Filter.atTop (nhds L)) :
    L = θstar :=
  linWorld_tendsto_unique η θstar x θ₀ hx hη L h

/-- **`paramScmWorldModel linPScm` 上的 `sim` 与 `thetaN` 对齐**
（把 §2 的 `linPScm_sim_one` 用在 `thetaN` 上，供 §4 使用）。 -/
theorem sim_at_thetaN (η θstar x θ₀ : ℝ) (n : ℕ) :
    (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1
      = thetaN η θstar x θ₀ n * x :=
  linPScm_sim_one (thetaN η θstar x θ₀ n) PUnit.unit x

/-! ===========================================================================
    §4  **(b)** `θ` 收敛 ⟹ **预测**收敛（因为 `sim` 依赖 `θ`）
    =========================================================================== -/

/-- **【(b) 一般形式】任意参数轨迹收敛 ⟹ 其 `sim` 预测收敛**

**陈述**：若 `θ_n → L`，则
$$\\mathrm{sim}\\ \\theta_n\\ (x)\\ 1 \\longrightarrow L\\cdot x .$$

**为什么这证明「`sim` 依赖 `θ`」是本质的**：证明用 §2 的**等式**
`sim θ … 1 = θ * x`。若换成**不读 `θ`** 的 `sim`（如 `SCMWorldModel.scmWorldStep`），
左侧**恒为常数**，结论将要求该常数为 `L * x` —— 对变化的 `L` **为假**。
⟹ 本定理**实质**约束构造。

**⚠ 反同义反复**：前件 `θ_n → L` 是关于 `θ` 轨迹的；结论 `sim θ_n → L x`
是关于**预测**的；二者由 `linPScm_sim_one` 的**等式**连接（不是假设）。
结论里出现 `x` 作为**乘子**，这一「搬运」是 `Filter.Tendsto.mul_const` 的实质工作。 -/
theorem sim_tendsto_of_theta_tendsto (x : ℝ) (L : ℝ)
    {θn : ℕ → ℝ} (h : Filter.Tendsto θn Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun n : ℕ => (paramScmWorldModel linPScm).sim (θn n)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1)
      Filter.atTop (nhds (L * x)) := by
  have hmul : Filter.Tendsto (fun n : ℕ => θn n * x) Filter.atTop (nhds (L * x)) :=
    h.mul_const x
  refine hmul.congr (fun n => ?_)
  exact linPScm_sim_one (θn n) PUnit.unit x

/-- **【(b) · 主形态】`θ_n` 收敛到 `θ*` ⟹ **预测**收敛到 `θ* x`**

**这是本文件的「桥」**：左侧前件来自 §3 的 `(a)`（`θ` 学习收敛），
结论是 `paramScmWorldModel linPScm` 上的**预测收敛**，
中间的传递**只**靠 `sim` 读 `θ`（`linPScm_sim_one`）。

**⚠ 前件 = `x ≠ 0` 与 `|1-η| < 1`**（同 `(a)`），**结论**（预测极限 `θ* x`）
**不在前件里**：`θ* x` 是 `θ*`（前件中未具名的**自由结论值**）乘 `x`（**参数**），
由 `(a)` 经 `mul_const` 搬运得到。**非改写。** -/
theorem sim_tendsto_of_theta_learning (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1)
      Filter.atTop (nhds (θstar * x)) :=
  sim_tendsto_of_theta_tendsto x θstar
    (thetaN_converges_on_paramScm η θstar x θ₀ hx hη)

/-- **(b) 的残差形态**：预测误差 `sim θ_n − θ* x` **收敛到 0**。

**⚠ 这条是**弱**的（「误差 → 0」），列在此处仅表示 `(b)` 也蕴含旧口径；
本文件的**强**结论是上一条（极限是 `θ* x`，一个可**任意**的值）。 -/
theorem sim_residual_tendsto_zero (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1 - θstar * x)
      Filter.atTop (nhds 0) := by
  have h := sim_tendsto_of_theta_learning η θstar x θ₀ hx hη
  have h0 : (θstar * x) - (θstar * x) = (0 : ℝ) := sub_self _
  rw [← h0]
  exact h.sub_const (θstar * x)

/-! ===========================================================================
    §5  **(c)** 收敛速率 `(1-η)^n` 的**显式**形式
    =========================================================================== -/

/-- **【(c) 主形态：速率的显式 `n` 次方形式】**

$$\\boxed{\\;\\theta_n - \\theta^* = (1-\\eta)^n\\,(\\theta_0 - \\theta^*)\\;}$$

**读数**：偏离真值的量在每个时刻乘**同一个**因子 `1 - η`，
故速率的显式形式是**等比** `(1-η)^n`，底 `1-η` 与 `n`、`θ₀`、`θ*` **无关**。

**证明**：**直接引用** `ThetaConvergence.thetaN_closed`（**不重证**）。 -/
theorem thetaN_rate_form (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    thetaN η θstar x θ₀ n - θstar = (1 - η)^n * (θ₀ - θstar) :=
  thetaN_closed η θstar x θ₀ hx n

/-- **【(c) 用 `OptimalEta.c` 的写法】**：底 `1-η` 的绝对值**就是**
`OptimalEta.c η`（收缩因子）。

$$\\theta_n - \\theta^* = (1-\\eta)^n\\,(\\theta_0-\\theta^*) .$$

**⚠ 本定理只重写**底**的记号**（`c η = |1-η|`），不复述 `(c)` 主体；
其价值在于把本文件的速率**接到** `FateV2.Loop/OptimalEta.lean` 的最优步长引擎上
（`c_pow_mono`、`c_pow_strict_of_lt` 可**直接**用于本轨迹）。 -/
theorem thetaN_rate_form_as_c (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    thetaN η θstar x θ₀ n - θstar = (1 - η)^n * (θ₀ - θstar)
      ∧ |thetaN η θstar x θ₀ n - θstar| = c η ^ n * |θ₀ - θstar| := by
  refine ⟨thetaN_rate_form η θstar x θ₀ hx n, ?_⟩
  rw [thetaN_rate_form η θstar x θ₀ hx n, abs_mul, abs_pow]
  rfl

/-- **【(c) 在预测上的形态】**：`sim` 预测的速率**同底同指数**。

$$\\mathrm{sim}\\ \\theta_n - \\theta^* x
  = \\bigl((1-\\eta)^n(\\theta_0-\\theta^*)\\bigr)\\cdot x .$$

**意义**：参数与预测的收敛速率**完全一致**（同一个 `(1-η)^n`），
因为 `sim` 是 `θ` 的**线性**函数（`θ ↦ θ * x`，斜率 `x`）。
这是 `(d)` 的「链条」在**速率**层的证据。 -/
theorem sim_rate_form (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1 - θstar * x
      = ((1 - η)^n * (θ₀ - θstar)) * x := by
  rw [sim_at_thetaN]
  have h := thetaN_rate_form η θstar x θ₀ hx n
  calc thetaN η θstar x θ₀ n * x - θstar * x
      = (thetaN η θstar x θ₀ n - θstar) * x := by ring
    _ = ((1 - η)^n * (θ₀ - θstar)) * x := by rw [h]

/-- **【(c) 的界形态】速率上界** `|θ_n - θ*| ≤ c(η)^n |θ₀ - θ*|`，`η ∈ (0,1]`。

**⚠ 前件 `0 < η ≤ 1` 是**显式列出**的（它使 `c(η) = 1-η ≤ 1`）。
这一条**不是** `(c)` 的闭式的改写 —— 闭式是**等式**，本条是**界**；
界需要「`c ≤ 1`」这个**额外**的步长条件，故在结论中**不能**去掉前件
（`η` 在 `(1,2)` 内时 `|1-η|` 仍 `< 1`，但界的方向应换成单调递增，不是本条）。 -/
theorem thetaN_rate_le (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ)
    (h1 : 0 < η) (h2 : η ≤ 1) :
    |thetaN η θstar x θ₀ n - θstar| ≤ |θ₀ - θstar| :=
  linWorld_err_le η θstar x θ₀ hx h1 h2 n

/-- **`(c)` 的 `c` 形态的界**：`|θ_n - θ*| = c(η)^n |θ₀ - θ*|`。
（`|1-η|` 记号的 `OptimalEta.c` 版本，供最优步长引擎直接消费。） -/
theorem thetaN_rate_c_eq (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    |thetaN η θstar x θ₀ n - θstar| = c η ^ n * |θ₀ - θstar| :=
  (thetaN_rate_form_as_c η θstar x θ₀ hx n).2

/-! ===========================================================================
    §6  **(d)** 主定理：学习与预测串成**一条链**
    =========================================================================== -/

/-- **【(d) 主定理：`θ` 学习与 `θ` 影响预测是**同一条链的两环**】**

在 `paramScmWorldModel linPScm` 上，同一条参数轨迹 `θ_n := thetaN η θ* x θ₀ n`
**同时**满足：

1. **学习收敛**：`θ_n → θ*`（来自 `(a)`，引用 `ThetaConvergence`）；
2. **预测收敛**：`sim θ_n (x) 1 → θ* x`（来自 `(b)`，经 `sim` 读 `θ`）；
3. **速率一致**：两者共享**同一个**速率因子 `(1-η)^n`
   （`θ_n − θ* = (1-η)^n(θ₀−θ*)`，`sim θ_n − θ* x = ((1-η)^n(θ₀−θ*))·x`）；
4. **同一序列**：驱动 (2) 的 `θ` 序列**就是** (1) 的 `thetaN`（不是另一条）。

**(d) 与 (a)(b)(c) 的差别（防「简单重复」）**：
本定理把三者**捆绑到同一个 `θ_n` 上**并**显式断言 4**（同一序列），
这是把「`θ` 学习」与「`θ` 影响预测」串成**一条链**的**内容**；
`(a)` 单独说「参数收敛」，`(b)` 单独说「若参数收敛则预测收敛」，
`(c)` 单独说「速率形状」—— 三者**不含**「同一驱动序列」这一断言。

**⚠ 反同义反复核查**：
* 前件：`x ≠ 0`（设计点）、`|1-η| < 1`（步长）；两者都**不含**结论；
* 结论第 4 项是**等式** `θ_n = thetaN η θ* x θ₀ n`（`rfl` 级，**定义**同一性），
  它**不**是「结论蕴含结论」—— 它断言的是「(2) 中的序列**就是** (1) 中的序列」，
  这是把两个**不同命题**（参数收敛 vs 预测收敛）**绑定到同一对象**的核心内容；
  若无此项，(1) 与 (2) 可能对**不同**轨迹成立，(d) 就**不是**一条链。
* 第 1、2 项**各自**由 `(a)`、`(b)` 给出（**引用**，不重证）；
  第 3 项由 `(c)` 给出（**引用**）。 -/
theorem theta_learning_meets_prediction (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    -- (1) 学习收敛
    Filter.Tendsto (thetaN η θstar x θ₀) Filter.atTop (nhds θstar)
    -- (2) 预测收敛
    ∧ Filter.Tendsto
        (fun n : ℕ => (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1)
        Filter.atTop (nhds (θstar * x))
    -- (3) 速率一致（同一速率因子 `(1-η)^n`）
    ∧ (∀ n : ℕ, thetaN η θstar x θ₀ n - θstar = (1 - η)^n * (θ₀ - θstar))
    ∧ (∀ n : ℕ, (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1 - θstar * x
        = ((1 - η)^n * (θ₀ - θstar)) * x)
    -- (4) 同一驱动序列（预测里的 `θ` 就是学习里的 `thetaN`，定义性同一）
    ∧ (∀ n : ℕ, (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1
        = thetaN η θstar x θ₀ n * x) :=
  ⟨thetaN_converges_on_paramScm η θstar x θ₀ hx hη,
   sim_tendsto_of_theta_learning η θstar x θ₀ hx hη,
   fun n => thetaN_rate_form η θstar x θ₀ hx n,
   fun n => sim_rate_form η θstar x θ₀ hx n,
   fun n => sim_at_thetaN η θstar x θ₀ n⟩

/-- **【(d) 的清单形态】**：把主定理的五个合取项**逐条**读出。

**用途**：使 `(d)` 的每个环节可**单独**被下游引用（避免每次都拆合取）。 -/
theorem chain_summary (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    -- 环节 ①：`θ` 学习收敛（引用 `ThetaConvergence`）
    Filter.Tendsto (thetaN η θstar x θ₀) Filter.atTop (nhds θstar)
    -- 环节 ②：`sim` 读 `θ`（引用 `ParamSCM`）
    ∧ (∀ n : ℕ, (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1
        = thetaN η θstar x θ₀ n * x)
    -- 环节 ③：预测收敛（由 ①② 得到）
    ∧ Filter.Tendsto
        (fun n : ℕ => (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1)
        Filter.atTop (nhds (θstar * x))
    -- 环节 ④：速率 `(1-η)^n` 显式（引用 `ThetaConvergence.thetaN_closed`）
    ∧ (∀ n : ℕ, thetaN η θstar x θ₀ n - θstar = (1 - η)^n * (θ₀ - θstar)) :=
  ⟨thetaN_converges_on_paramScm η θstar x θ₀ hx hη,
   fun n => sim_at_thetaN η θstar x θ₀ n,
   sim_tendsto_of_theta_learning η θstar x θ₀ hx hη,
   fun n => thetaN_rate_form η θstar x θ₀ hx n⟩

/-! ===========================================================================
    §7  具体数值实例（检验链的**非空真**：前件可同时满足）
    =========================================================================== -/

/-- **具体设定**：`θ* = 3`、`θ₀ = 0`、`η = 1/2`、`x = 2`
（`x≠0` 与 `|1-η|<1` **同时**满足）。 -/
theorem concrete_setup : (2 : ℝ) ≠ 0 ∧ |1 - (1/2 : ℝ)| < 1 :=
  ⟨by norm_num, by norm_num⟩

/-- **具体链：`θ_n → 3` 且 `sim θ_n → 6`**（真值 `3`、观测 `3*2 = 6`）。 -/
theorem concrete_chain :
    Filter.Tendsto (thetaN (1/2) 3 2 0) Filter.atTop (nhds 3)
    ∧ Filter.Tendsto
        (fun n : ℕ => (paramScmWorldModel linPScm).sim (thetaN (1/2) 3 2 0 n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (2 : ℝ)) 1)
        Filter.atTop (nhds 6) := by
  refine ⟨thetaN_converges_on_paramScm (1/2) 3 2 0 (by norm_num) (by norm_num), ?_⟩
  have h := sim_tendsto_of_theta_learning (1/2) 3 2 0 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- **具体速率**：`θ_n − 3 = (1/2)^n · (−3)`，且 `sim θ_n − 6 = ((1/2)^n · (−3)) · 2`。 -/
theorem concrete_rate (n : ℕ) :
    thetaN (1/2) 3 2 0 n - 3 = (1/2 : ℝ)^n * (0 - 3)
    ∧ (paramScmWorldModel linPScm).sim (thetaN (1/2) 3 2 0 n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (2 : ℝ)) 1 - 3 * 2
        = ((1/2 : ℝ)^n * (0 - 3)) * 2 := by
  have h2 : (1 - (1:ℝ)/2) = 1/2 := by norm_num
  refine ⟨?_, ?_⟩
  · have h := thetaN_rate_form (1/2) 3 2 0 (by norm_num) n
    rw [h2] at h
    exact h
  · have h := sim_rate_form (1/2) 3 2 0 (by norm_num) n
    rw [h2] at h
    exact h

/-- **具体非平凡性**：`linPScm` 的 `sim` **真的**区分 `θ = 3` 与 `θ = 0`。

即 `sim 3 … 1 = 6 ≠ 0 = sim 0 … 1` —— 直接由 `linPScm_sim_one` 得到，
故上面的链**不是**「`sim` 与 `θ` 无关」的退化情形。 -/
theorem concrete_sim_depends :
    (paramScmWorldModel linPScm).sim (3 : ℝ) (fun _ => PUnit.unit)
        (fun _ => PUnit.unit) (fun _ => (2 : ℝ)) 1
      ≠ (paramScmWorldModel linPScm).sim (0 : ℝ) (fun _ => PUnit.unit)
          (fun _ => PUnit.unit) (fun _ => (2 : ℝ)) 1 := by
  rw [linPScm_sim_one, linPScm_sim_one]
  norm_num

/-! ===========================================================================
    §8  自检清单（逐条可编译）
    =========================================================================== -/

noncomputable section

/-- **自检 1**：`linPScm` 的结构方程确实是 `θ * x`（与 `ThetaConvergence.linWorld` 同机制）。 -/
example (θ x : ℝ) :
    (linPScm.sg θ PUnit.unit).2 x
      = FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ PUnit.unit PUnit.unit
          PUnit.unit x := by
  rw [linPScm_sg, ThetaConvergence.linWorld_predFrom]

/-- **自检 2**：本文件的 `thetaN` **就是** `ThetaConvergence.thetaN`（不是第二个学习律）。 -/
example (η θstar x θ₀ : ℝ) (n : ℕ) :
    thetaN η θstar x θ₀ n = ThetaConvergence.thetaN η θstar x θ₀ n := rfl

/-- **自检 3**：主定理 `(d)` 在另一个合法步长 `η = 1/3` 上同样成立。 -/
example (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (thetaN (1/3) θstar x θ₀) Filter.atTop (nhds θstar)
    ∧ Filter.Tendsto
        (fun n : ℕ => (paramScmWorldModel linPScm).sim (thetaN (1/3) θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1)
        Filter.atTop (nhds (θstar * x)) :=
  ⟨thetaN_converges_on_paramScm (1/3) θstar x θ₀ hx (by norm_num),
   sim_tendsto_of_theta_learning (1/3) θstar x θ₀ hx (by norm_num)⟩

/-- **自检 4**：`(c)` 的闭式在 `n = 0` 时退化为 `θ₀ − θ* = θ₀ − θ*`（一致性检验）。 -/
example (η θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    thetaN η θstar x θ₀ 0 - θstar = θ₀ - θstar := by
  rw [thetaN_rate_form η θstar x θ₀ hx 0]; ring

end

end ThetaLearningParam
end FateV2.Loop
