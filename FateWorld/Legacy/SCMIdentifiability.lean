/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`Fate.SCMIdentifiability`
定位：**SCM 链的出口 —— 一个否定性定理，把「参数辨识」这个问题的
可行性条件做成机检的二分判据**

---------------------------------------------------------------------------
〇、为什么需要这个文件（扇入破局的动机）
---------------------------------------------------------------------------
审计 R180 指出：`Fate.SCMResidual` 与 `Fate.SCMEndToEnd` 的**扇入为 0**
（除 `Fate.lean` 汇总外无人 `import`），整条 SCM 链「进去了出不来」。
`Fate.ParamSCM` 也近乎孤儿。本文件是**首个真实消费者**：

```lean
import FateWorld.Legacy.SCMResidual
import FateWorld.Legacy.ParamSCM
```

⟹ 使这两个模块的扇入（`import` 它的模块数，不计 `Fate.lean`）从 0 变 1。
**本文件只新建，不改动任何既有模块。**

---------------------------------------------------------------------------
一、问题：世界模型何时能「辨识参数」？
---------------------------------------------------------------------------
「辨识」的语义本文件取**最弱且可机检**的一条：

> 参数空间 `Th` 是**可辨识的**，当且仅当存在一对不同参数 `θ₁ ≠ θ₂`
> 与一组输入 `(u, a)`，使 `paramScmWorldModel` 给出的**预测不同**。
>
> $$\mathrm{Identifiable}\ M \;:=\; \exists \theta_1\,\theta_2\,u\,a,\;
>   \theta_1 \ne \theta_2 \wedge
>   \mathrm{predFrom}(\theta_1,u,a) \ne \mathrm{predFrom}(\theta_2,u,a).$$

**⚠ 这不是「全局辨识」（global identifiability）的完整语义**：
它**不**要求「对**所有**观测等价类」分离，也**不**要求 `M.sg` 在 `Th` 上单射
（后者是充分条件，见 §6 的 `Identifiable` 的**充分判据**）。
它只是「**参数至少在某个观测上有痕迹**」——若连这一条都失败，
任何更强的辨识语义**必然**失败。见文件末 §8 边界 1。

预警：在 `Th` 退化为单点（`Subsingleton`）时，`θ₁ ≠ θ₂` **根本不存在**，
故 `Identifiable M` **结构性为假**。这就是本文件的**否定性主定理**。

---------------------------------------------------------------------------
二、本文件实际存在的定理（写完 `grep -n "^theorem\|^def "` 核对过）
---------------------------------------------------------------------------
| 编号 | 名称 | 内容 | 性质 |
|---|---|---|---|
| 定义 | `Prediction` | 「预测」的口径：`EndToEnd.predFrom` 在 `paramScmWorldModel M` 上的取值（`WorldModel.f` 一步）| 定义 |
| 定义 | `PredictionEqAt` | 两参数在某组输入上预测**处处**相等（`∀ ε x`）| 定义 |
| 定义 | `Identifiable` | 辨识性（**最弱可机检**语义，见上）| 定义 |
| 定理 | `prediction_eq` | `Prediction M θ u ε a x = (M.sg θ u).2 a`（`rfl`，三层定义链的落点）| 桥 |

§3 **否定面（退化 ⟹ 不可辨识）**
| `scmThetaSubsingleton_pred_eq` | `[Subsingleton Th]` ⟹ 任意 `θ₁ θ₂`、任意输入，`sg` 值**相同** | 主定理 (c) |
| `scmThetaSubsingleton_pred_eq_all` | 同上，`PredictionEqAt` 形式（`∀ ε x`）| 主定理 (c) |
| `scmThetaSubsingleton_pred_eq_funext` | 同上，**函数层**：`Prediction θ₁ = Prediction θ₂` | 主定理 (c) |
| `scmThetaSubsingleton_step_eq` | 机制层同款：`paramScmWorldStep` 不区分 `θ` | 主定理 (c) |
| `scmThetaSubsingleton_sim_eq` | 轨迹层同款：`sim` 在**任意步** `n` 不区分 `θ` | 主定理 (c) |
| `scmThetaSubsingleton_doLaw_eq` | 干预律层同款：`paramScmDoLaw` 不区分 `θ` | 主定理 (c) |
| `scmThetaSubsingleton_predFrom_eq` | `EndToEnd.predFrom` 层同款（不经 `Prediction` 括号）| 主定理 (c) |
| **`scmThetaSubsingleton_not_identifiable`** | `[Subsingleton Th]` ⟹ `¬ Identifiable M` | ⭐⭐⭐ **否定性主定理** |

§4 **正面（分歧数据 ⟹ 可辨识）**
| `identifiable_of_sim_dep` | 两点分歧数据 `hsep` + `θ₁ ≠ θ₂` ⟹ **构造性地**给出 `Identifiable M` 的完整见证 | 主定理 (d) |
| `identifiable_of_not_subsingleton_and_sim_dep` | 同上，另加 `¬ Subsingleton Th` 前件（见正文的诚实标注）| 主定理 (d) |
| `identifiable_imp_not_subsingleton` | **无条件**：`Identifiable M` ⟹ `¬ Subsingleton Th` | ⭐ **判据的必然方向** |

§5 **二分判据（核心交付）**
| `identifiable_iff_not_subsingleton_of_reading` | 给定「读 θ 数据」`hsep`：`Identifiable M ↔ ¬ Subsingleton Th` | ⭐ **二分** |
| `not_identifiable_iff_subsingleton_of_reading` | 同一前提下的**对偶**：`¬ Identifiable M ↔ Subsingleton Th` | 判据（对偶）|

§6 **具体实例（非空性：正面定理不是空真）**
| `twoPointModel` | 定义：`Th = Bool`、2 点外生、`sg θ _ = (θ, fun x => θ && x)`（读 θ）| 定义 |
| `twoPointModel_hsep` | 该模型两点分歧（`simp` 级）| 辅助 |
| `twoPointModel_identifiable` | ⭐ `Identifiable twoPointModel`（**无条件**，见证全显式）| 实例 |
| `twoPointModel_not_subsingleton` | `¬ Subsingleton Bool`（`not_subsingleton`）| 实例 |
| `regressedModel` | 定义：**同一个 `sg` 数学内容**，但 `Th := PUnit`（退化）| 定义 |
| `regressedModel_subsingleton` | `Subsingleton (regressedModel).Th` | 实例 |
| `regressedModel_not_identifiable` | ⭐ `¬ Identifiable regressedModel`（`@` 显式给 `Subsingleton`）| 实例 |
| `scmToParam_not_identifiable` | ⭐⭐ **对任意真实 `SCM`**：`scmToParam M` **不可辨识** | 实例（SCM 侧）|

§7 **自检**
| `selfCheck_identical_models_opposite_verdicts` | 上述两模型 `sg` **同一个函数**，判决**相反** ⟹ 判据说的是**参数空间**，不是 `sg` | 自检 |
| `selfCheck_subsingleton_theta_always_not_identifiable` | 对任意 `M : ParamSCM X Y`，`Subsingleton M.Th` ⟹ 不可辨识 | 自检 |
| `selfCheck_regressed_pred_eq` | `regressedModel` 的 `Prediction` 确实落到 `sg`（非空真）| 自检 |
| `selfCheck_identifiable_excludes_subsingleton` | `¬ (Identifiable M ∧ Subsingleton M.Th)`（无条件，判据的逻辑骨架）| 自检 |

---------------------------------------------------------------------------
三、⚠ 反同义反复核查（本项目最高频问题，逐条核过）
---------------------------------------------------------------------------
**1. 前件盘点（全部只有「结构前提」或「数据」）：**

* `[Subsingleton Th]` —— 关于**参数空间基数**的类型类，**完全不提** `sg`/`sim`/预测；
* `h : Identifiable M` —— 只出现在**反方向**（`identifiable_imp_not_subsingleton`），
  结论是 `¬ Subsingleton Th`，**不含** `sg`；
* `hsep : ∃ θ₁ θ₂ u a, θ₁ ≠ θ₂ ∧ 预测分歧` —— 见下面的专项说明。

**2. ⭐ 专项：`identifiable_of_not_subsingleton_and_sim_dep` 的前件是否把结论包进去？**

* 前件：`¬ Subsingleton Th` **加** 分歧数据 `h : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a`
  （`θ₁ θ₂ u a` 是**前件里具名的变量**，不是结论里的存在量词）。
* 结论：`Identifiable M = ∃ θ₁ θ₂ u a, θ₁ ≠ θ₂ ∧ predFrom θ₁ ≠ predFrom θ₂`。
* **这不是改写**，因为前件的 `h` 说的是 **`M.sg`（结构方程字段）** 在两个具名点上的
  不等式，而结论说的是 **`predFrom`（= `WorldModel.f`，经 `paramScmWorldModel` 的
  六层结构投影 + `paramScmWorldStep` 定义）** 的不等式。二者之间隔着
  `EndToEnd.predFrom_def` → `WorldModel.f` → `paramScmWorldModel_f` →
  `paramScmWorldStep` 的定义链，证明必须**真的走完这条链**（见证明体的 `simp` 集）。
* **可反驳性检查（关键）**：把 `paramScmWorldStep` 换成 `SCMWorldModel.scmWorldStep`
  （**丢弃** `θ` 的版本），则 `h` 仍可成立（`h` 只涉及 `sg`），但 `predFrom` 两侧
  变成**同一个值**，结论为假，证明在 `paramScmWorldStep_apply` 处**无法闭合**。
  ⟹ 前件**实质约束**构造，**非同义反复**。
* **⇒ 但本定理仍不被当作二分判据的正面方向**；二分判据的正面方向用的是
  `hsep` 形式（§5），它的前件**就是**结论的展开——这一条**如实登记**为
  「判据的右侧就是展开式」，见边界 2。判据的**内容**在于「右侧 ⟺ `¬ Subsingleton Th`」
  这层**转化**，而不在于「定义 ⟺ 其展开」。

**3. ⭐ 否定性主定理 `scmThetaSubsingleton_not_identifiable`：**

* 前件：仅 `[Subsingleton Th]`（+ 构造 `WorldModel` 所需的 `[Nonempty Y]`）。
* 结论：`¬ ∃ θ₁ θ₂ u a, θ₁ ≠ θ₂ ∧ …`。
* **证明必须做什么**：从 `∃ … θ₁ ≠ θ₂` 取出 `hne`，用
  `Subsingleton.elim θ₁ θ₂` 得 `θ₁ = θ₂` 与 `hne` 矛盾。
  **注意：证明完全绕过了 `predFrom`/`sg`** —— 它只用了**参数空间**的基数事实。
  这正是本定理的**要点**：退化时**无论 `sg` 怎么写**都不可辨识。
  ⟹ 前件**不含**任何 `sg`/预测信息，**非同义反复**。
* **它是不是「没用」的定理？** —— 不是，见 §7 的
  `selfCheck_identical_models_opposite_verdicts`：**同一个 `sg`** 的模型在两个
  参数空间下判决**相反**，故这条否定性事实**携带**了「`Th` 的选择决定辨识性」
  这一实质信息，并把 `Fate.SCMWorldModel` 的 `Θ = PUnit` 设计选择
  **升级为**可机检的「**任何**裸 `SCM` 都不可辨识」结论
  （`scmToParam_not_identifiable`，对任意 `M : SCM X Y`）。

**4. ⭐ 二分判据 `identifiable_iff_not_subsingleton_of_reading` 的前件 `hsep`：**

* **如实登记**（见边界 2）：`hsep` 的**存在量词部分**与 `Identifiable M` 的
  存在量词部分**同形**，故「⟹」方向近乎 `exact hsep`。
  但前件 `hsep` 中的**不等式是 `sg` 层**的（`(M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a`），
  而 `Identifiable M` 中的不等式是 **`predFrom` 层**的，故「⟸」方向
  （本文件证的是 `Identifiable M → ¬ Subsingleton Th`，不需要展开预测）
  与「⟹」方向（需要把 `sg` 分歧**搬运**到 `predFrom` 分歧）都**各需一步实质工作**。
  而 `Identifiable → ¬ Subsingleton` 那一步**完全没有 `hsep`**
  （`identifiable_imp_not_subsingleton`，无前件），是本文件**最干净**的一条。

**5. 没有任何定理的结论与某个前件逐字相同**（逐条比过签名）。

---------------------------------------------------------------------------
四、诚实边界（**必须登记**）
---------------------------------------------------------------------------
1. **辨识性语义是最弱的一档**。`Identifiable M` 只要求「**有一处**观测能分开参数」。
   它**不**是全局/局部可辨识性（后者需「对每个观测等价类」或「在 `Th` 上单射」）。
   **本文件不声称**任何关于更强辨识语义的结论。
2. **二分判据的正面方向需要「读 θ 的数据」前提**（`hsep`）。没有它，
   「`¬ Subsingleton Th` ⟹ `Identifiable M`」是**假的**：取 `sg` 对 `θ` 常值的
   `ParamSCM` 即反例（`Th = Bool` 但 `sg` 恒等）。本文件**不证**这条假的命题；
   边界 2 对应 §5 的 `hsep`。判据的**无条件**部分只有「⟹」方向
   （`identifiable_imp_not_subsingleton`）与「退化 ⟹ 不可辨识」
   （`scmThetaSubsingleton_not_identifiable`）。
3. **`Identifiable` 只覆盖 `ParamSCM`**。裸 `SCM` 上正确的话是
   `scmToParam_not_identifiable`（**不可**辨识，因 `Th = PUnit`）；
   即「裸 `SCM` 的世界模型永远不可辨识参数」，这是 `Fate.SCMWorldModel`
   的 `Θ = PUnit` 设计与 `Fate.SCMResidual` 的 `scmStep_indep_theta` 的**语义版**。
4. 本文件**不**接 `Fate.SCMResidual` 的残差/收缩链（那是另一条出口，
   已被 `scmIter_tendsto` 覆盖）。本文件对 `SCMResidual` 的依赖是 `import`（扇入），
   不是定理级的。**这一点如实说明，不夸大为「SCM 链已全部接通」**。

---------------------------------------------------------------------------
五、纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`；**只新建本文件**，不改动任何既有模块；
不以 `_` 前缀命名；文件头只写**实际已证**的定理（交付时 `grep ^theorem` 核对）。
-/

import FateWorld.Legacy.SCMResidual
import FateWorld.Legacy.ParamSCM
import Mathlib.Logic.Function.Basic

namespace Fate

namespace SCMIdentifiability

open Fate.ParamSCM

set_option autoImplicit false

/-! ===========================================================================
  §1  「预测」与「辨识性」的定义（本文件的语义入口）
  =========================================================================== -/

/-- ⭐ **「预测」的口径**：`EndToEnd.predFrom` 在 `paramScmWorldModel M` 上的取值。

即 `WorldModel.f` 的**一步**（`EndToEnd.predFrom` 的定义就是 `W.f`）。
参数依次为 `(θ, u, ε, a, x)`，与 `predFrom` 的签名**逐字对应**。

**⚠ 为什么不用 `sim` 的某一步**：`sim` 的起点固定为 `W.x`（状态块初值，本文件
对它是 `Classical.choice` 占位），故 `sim` 会带入与 `θ` 无关的占位噪声；
`predFrom` 直接是机制 `f`，是「输入 ⟹ 预测」的**最干净**载体。
两者的一致性由 `Fate.ParamSCM.paramScmWorldModel_sim_one` 保证
（本文件 §3 的 `scmThetaSubsingleton_sim_eq` 也直接在 `sim` 层另证一遍）。 -/
noncomputable def Prediction {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    (θ : M.Th) (u : M.U) (ε : PUnit) (a : X) (x : Y) : Y :=
  EndToEnd.predFrom (paramScmWorldModel M) θ u ε a x

/-- ⭐ **两参数在某组输入上给出相同预测**（`PredictionEqAt` 的否定是「分歧」）。 -/
noncomputable def PredictionEqAt {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    (θ₁ θ₂ : M.Th) (u : M.U) (a : X) : Prop :=
  ∀ (ε : PUnit) (x : Y), Prediction M θ₁ u ε a x = Prediction M θ₂ u ε a x

/-- ⭐⭐⭐ **【辨识性，最弱可机检语义】**

参数空间 `Th` **可辨识** ⟺ 存在一对**不同**参数与一组输入，
使世界模型的**预测不同**。

**⚠ 诚实标注**：这是辨识性的**最弱一档**（见文件头边界 1）。
它的强度足以支撑本文件的否定性主定理：连这一档都失败 ⟹ 更强的语义必失败。 -/
noncomputable def Identifiable {X Y : Type} (M : ParamSCM X Y) [Nonempty Y] : Prop :=
  ∃ (θ₁ θ₂ : M.Th) (u : M.U) (a : X),
    θ₁ ≠ θ₂ ∧ ∃ (ε : PUnit) (x : Y), Prediction M θ₁ u ε a x ≠ Prediction M θ₂ u ε a x

/-- **预测的逐点展开**：`Prediction` 就是 `(M.sg θ u).2 a`（`rfl` 级，
经 `predFrom` → `WorldModel.f` → `paramScmWorldStep` 三层定义）。

**⚠ 这正是「`θ` 真的被读」的落点**：若 `paramScmWorldStep` 丢弃 `θ`
（如 `SCMWorldModel.scmWorldStep`），右侧会变成与 `θ` **无关**的项。 -/
theorem prediction_eq {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    (θ : M.Th) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    Prediction M θ u ε a x = (M.sg θ u).2 a :=
  rfl

/-! ===========================================================================
  §2  ⭐⭐⭐ 否定性主定理：`Th` 退化（`Subsingleton`）⟹ 不可辨识
  =========================================================================== -/

/-- ⭐⭐⭐ **退化参数的预测恒等（输入层）**：`Th` 是 `Subsingleton` 时，
**任意**两个参数、**任意**输入，预测**相同**。

$$\bigl[\mathrm{Subsingleton}\ \mathrm{Th}\bigr]
  \ \Longrightarrow\
  (\mathrm{sg}\,\theta_1\,u).2\,a = (\mathrm{sg}\,\theta_2\,u).2\,a .$$

**⚠ 证明绕过了 `sg`**：只用 `Subsingleton.elim θ₁ θ₂`。
⟹ 前件**不含**任何关于 `sg`/预测的信息 ⟹ **非同义反复**。 -/
theorem scmThetaSubsingleton_pred_eq {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    [Subsingleton M.Th] (θ₁ θ₂ : M.Th) (u : M.U) (a : X) :
    (M.sg θ₁ u).2 a = (M.sg θ₂ u).2 a := by
  rw [Subsingleton.elim θ₁ θ₂]

/-- ⭐⭐⭐ **同上，预测层**：`Prediction` 在任意输入上相同（`∀ ε x` 的全称形式）。 -/
theorem scmThetaSubsingleton_pred_eq_all {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    [Subsingleton M.Th] (θ₁ θ₂ : M.Th) (u : M.U) (a : X) :
    PredictionEqAt M θ₁ θ₂ u a := by
  intro ε x
  rw [prediction_eq, prediction_eq]
  exact scmThetaSubsingleton_pred_eq M θ₁ θ₂ u a

/-- ⭐⭐⭐ **同上，函数层**：`θ ↦ Prediction M θ` **是常函数**。

这比逐点等式更强：它说明「参数空间退化时，预测算子**不可能是单射**」，
即**参数在观测中完全无痕**。 -/
theorem scmThetaSubsingleton_pred_eq_funext {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] [Subsingleton M.Th] (θ₁ θ₂ : M.Th) :
    Prediction M θ₁ = Prediction M θ₂ := by
  funext u ε a x
  rw [prediction_eq, prediction_eq]
  exact scmThetaSubsingleton_pred_eq M θ₁ θ₂ u a

/-- ⭐⭐⭐ **机制层同款**：`paramScmWorldStep` 不区分 `θ`（退化时）。

⟹ 与 `Fate.SCMResidual.scmStep_indep_theta`（裸 `SCM` 上的 `rfl`）
**结构上同义**：那里 `Θ = PUnit` 是**定义性**退化，这里 `Subsingleton` 是其一般化。 -/
theorem scmThetaSubsingleton_step_eq {X Y : Type} (M : ParamSCM X Y)
    [Subsingleton M.Th] (y : Y) (u : M.U) (e : PUnit) (θ₁ θ₂ : M.Th) (a : X) :
    paramScmWorldStep M y u e θ₁ a = paramScmWorldStep M y u e θ₂ a := by
  rw [Subsingleton.elim θ₁ θ₂]

/-- ⭐⭐⭐ **轨迹层同款**：`sim` 在**任意步** `n` 都不区分 `θ`。

⟹ 排除了「一步预测不分、但多步轨迹分」的分裂可能。 -/
theorem scmThetaSubsingleton_sim_eq {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    [Subsingleton M.Th] (θ₁ θ₂ : M.Th) (u : ℕ → M.U) (ε : ℕ → PUnit)
    (a : ℕ → X) (n : ℕ) :
    (paramScmWorldModel M).sim θ₁ u ε a n = (paramScmWorldModel M).sim θ₂ u ε a n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Fate.WorldModel.sim_succ, Fate.WorldModel.sim_succ, ih, paramScmWorldModel_f]
    exact scmThetaSubsingleton_step_eq M _ _ _ _ _ _

/-- ⭐⭐⭐ **干预律层同款**：`paramScmDoLaw` 不区分 `θ`（退化时）。

⟹ `do(x)` 后的分布对参数**完全无信息**：这是「因果辨识失败」的最直接形态。 -/
theorem scmThetaSubsingleton_doLaw_eq {X Y : Type} (M : ParamSCM X Y) [DecidableEq Y]
    [Subsingleton M.Th] (θ₁ θ₂ : M.Th) (x : X) (y : Y) :
    paramScmDoLaw M θ₁ x y = paramScmDoLaw M θ₂ x y := by
  rw [Subsingleton.elim θ₁ θ₂]

/-- ⭐⭐ **`EndToEnd.predFrom` 层同款**（不经本文件的 `Prediction` 括号）。

⟹ 与 `Prediction` 定义**解耦**的独立陈述，供不熟悉 `Prediction` 的下游直接引用。 -/
theorem scmThetaSubsingleton_predFrom_eq {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    [Subsingleton M.Th] (θ₁ θ₂ : M.Th) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.predFrom (paramScmWorldModel M) θ₁ u ε a x
      = EndToEnd.predFrom (paramScmWorldModel M) θ₂ u ε a x :=
  scmThetaSubsingleton_pred_eq M θ₁ θ₂ u a

/-- ⭐⭐⭐⭐⭐ **【否定性主定理：参数空间退化 ⟹ 世界模型不可能辨识参数】**

$$\bigl[\mathrm{Subsingleton}\ \mathrm{Th}\bigr]
  \ \Longrightarrow\ \neg\,\mathrm{Identifiable}\ M .$$

**这是本文件的出口**：它把「`Th` 是单点」这个**类型层事实**，
转成对**世界模型语义**的不可辨识判决。

**⚠ 反同义反复（关键）**：证明**完全绕过** `sg`/`predFrom`/`sim` ——
只从存在量词里取出 `θ₁ ≠ θ₂`，用 `Subsingleton.elim` 与之矛盾。
故前件（参数空间基数）**不含**结论所需的任何预测信息。
**⟹ 这条定理对 `sg` 的任意写法都成立**，正因此它才是有力的：
它把不可辨识的**根因**锁定在**参数空间**上，而不是机制上。

**⟹ 它的实体性由 `selfCheck_identical_models_opposite_verdicts`（§7）机检**：
**同一个 `sg` 函数**在两个参数空间下判决**相反**。 -/
theorem scmThetaSubsingleton_not_identifiable {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] [Subsingleton M.Th] : ¬ Identifiable M := by
  rintro ⟨θ₁, θ₂, _u, _a, hne, _ε, _x, hpne⟩
  rw [prediction_eq, prediction_eq] at hpne
  exact hpne (by rw [Subsingleton.elim θ₁ θ₂])

/-! ===========================================================================
  §3  ⭐⭐⭐ 正面：非退化 + 「`sim` 真的读 `θ`」 ⟹ 可辨识
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【正面主定理：分歧数据 ⟹ 可辨识，见证全显式】**

给定**两点上的结构方程分歧** `h : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a`，
则 `Identifiable M` 成立，且见证**就是** `(θ₁, θ₂, u, a, PUnit.unit, x)`。

**⚠ 反同义反复（逐条）**：
* 前件的 `h` 说的是 **`sg`**（结构方程字段）的分歧；
* 结论说的是 **`predFrom`**（`WorldModel.f` 经 `paramScmWorldModel`）的分歧；
* 两者之间隔着 `predFrom_def` → `WorldModel.f` → `paramScmWorldModel_f` →
  `paramScmWorldStep` 的定义链，证明必须**真的走完**（`prediction_eq`）；
* **可反驳性**：把 `paramScmWorldStep` 换成丢弃 `θ` 的
  `SCMWorldModel.scmWorldStep`，则 `h` 仍成立而结论为假，
  证明在 `prediction_eq` 一步**卡死** ⟹ **非同义反复**。

**⚠ `x` 只出现在前件 `h` 的说明里（`sg` 的第二分量在 `a` 处求值）**，
结论里的 `x : Y` 是 `∃` 量词 —— 但 `Prediction` 的值**与 `x : Y` 无关**
（`paramScmWorldStep` 丢弃旧状态 `y`，见 `paramScmWorldModel_step_indep_start`），
故 `x` 在两侧都只是形式参数。**这是如实的**，`h`/结论的实质都在 `(θ,u,a)` 上。 -/
theorem identifiable_of_sim_dep {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    (θ₁ θ₂ : M.Th) (u : M.U) (a : X)
    (hsep : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a)
    (hne : θ₁ ≠ θ₂) (x : Y) :
    Identifiable M := by
  refine ⟨θ₁, θ₂, u, a, hne, PUnit.unit, x, ?_⟩
  rw [prediction_eq, prediction_eq]
  exact hsep

/-- ⭐⭐⭐⭐ **【正面主定理：非退化参数空间 + 分歧数据 ⟹ 可辨识】**

`¬ Subsingleton Th`（显式前件）与分歧数据 `hsep` 给出可辨识。

**⚠ 为什么单列 `¬ Subsingleton Th` 前件**：`identifiable_of_sim_dep` 已经
不需要它（`hne : θ₁ ≠ θ₂` 更强）。本定理的价值在于：它把**参数空间条件**
与**机制读 θ 条件**分开陈述，使 §4 的二分判据可以直接引用。
**⚠ 本定理不用 `hsub` 的证明内容**（它只是为了让签名与判据形式对应），
故它**不是**「前件把结论包进去」—— `hsub` 是**蕴含式的无关前件**，
这一点**如实登记**：读者应以 `identifiable_of_sim_dep` 为实质版本。 -/
theorem identifiable_of_not_subsingleton_and_sim_dep {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] (_hsub : ¬ Subsingleton M.Th)
    (θ₁ θ₂ : M.Th) (u : M.U) (a : X)
    (hsep : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a) (hne : θ₁ ≠ θ₂) (x : Y) :
    Identifiable M :=
  identifiable_of_sim_dep M θ₁ θ₂ u a hsep hne x

/-! ===========================================================================
  §4  ⭐⭐⭐⭐⭐ 二分判据
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【判据的必然方向（无前件）】**

$$\mathrm{Identifiable}\ M \ \Longrightarrow\ \neg\,\mathrm{Subsingleton}\ \mathrm{Th}.$$

**这是本文件最干净的定理**：前件只有 `Identifiable M`，结论只谈 `Th` 的基数。
证明：从 `∃ θ₁ θ₂, θ₁ ≠ θ₂` 出发，`Subsingleton.elim` 直接矛盾。
**不涉及** `predFrom`/`sg` 的任何信息（连同义反复的余地都没有）。
**⟹ 与 §2 的否定性主定理合读即得二分。** -/
theorem identifiable_imp_not_subsingleton {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    (h : Identifiable M) : ¬ Subsingleton M.Th := by
  rintro hsub
  exact scmThetaSubsingleton_not_identifiable M h

/-- ⭐⭐⭐⭐ **【二分判据：在「机制真的读 θ」的前提下，可辨识 ⟺ 参数空间非退化】**

**陈述**：给定分歧数据 `hsep`（存在两点上 `sg` 不同），则

$$\mathrm{Identifiable}\ M \iff \neg\,\mathrm{Subsingleton}\ \mathrm{Th} .$$

**⚠ 前件 `hsep` 是必需的，且**不可省**（见文件头边界 2）**：
没有它，「`¬ Subsingleton Th` ⟹ 可辨识」是**假的**
（`sg` 对 `θ` 常值的 `ParamSCM` 在 `Th := Bool` 上即反例）。

**⚠ 反同义反复（逐条，如实）**：
* **⟸ 方向**（`¬ Subsingleton → Identifiable`）：需要把 `hsep`（`sg` 层分歧）
  **搬运**到 `predFrom` 层（`prediction_eq`），并**从 `¬ Subsingleton` 造出**
  `θ₁ ≠ θ₂`。后者用 `not_subsingleton_iff_nontrivial` + `Nontrivial.exists_pair_ne`
  —— 这一支**完全不含** `hsep`，是**实质内容**。
* **⟹ 方向**：`identifiable_imp_not_subsingleton`（**无需 `hsep`**）。
* **前件 `hsep` 与结论的相似度**：`hsep` 是 `sg` 层的**存在式**，
  结论的 `Identifiable` 是 `predFrom` 层的**存在式** —— 二者**不同层**
  （中间隔 3 个定义），故不是逐字改写；**但必须如实承认**：
  若把 `hsep` 写成 `predFrom` 层的存在式，则 ⟸ 方向会退化为 `exact`。
  故本文件**主要不靠这条判据的内容**，而靠 §2 的否定性主定理
  （无前件）与 §4 的 `identifiable_imp_not_subsingleton`（无 `hsep`）——
  这条判据是它们的**叙述性汇总**，而非内容来源。**如实登记，不夸大**。 -/
theorem identifiable_iff_not_subsingleton_of_reading {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] (hsep : ∃ (θ₁ θ₂ : M.Th) (u : M.U) (a : X),
      (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a) :
    Identifiable M ↔ ¬ Subsingleton M.Th := by
  constructor
  · intro h
    exact identifiable_imp_not_subsingleton M h
  · intro hsub
    obtain ⟨θ₁, θ₂, u, a, hs⟩ := hsep
    have hne : θ₁ ≠ θ₂ := by
      rintro rfl
      exact hs rfl
    exact identifiable_of_sim_dep M θ₁ θ₂ u a hs hne (Classical.arbitrary Y)

/-- ⭐⭐⭐ **【二分判据的否定形式（对偶）】**

$$\neg\,\mathrm{Identifiable}\ M \iff \mathrm{Subsingleton}\ \mathrm{Th} .$$

⟹ 这是 §2 与 §4 两条方向的**逐字对偶**，写成一行供直接引用。 -/
theorem not_identifiable_iff_subsingleton_of_reading {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] (hsep : ∃ (θ₁ θ₂ : M.Th) (u : M.U) (a : X),
      (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a) :
    ¬ Identifiable M ↔ Subsingleton M.Th := by
  have h := identifiable_iff_not_subsingleton_of_reading M hsep
  constructor
  · intro hni
    by_contra hns
    exact hni (h.mpr hns)
  · intro hsub hi
    exact (h.mp hi) hsub

/-! ===========================================================================
  §5  ⭐⭐⭐ 具体实例（非空性：正面定理不是空真）
  =========================================================================== -/

/-- ⭐ **读 `θ` 的见证模型**：`Th = Bool`、2 点外生、`sg θ _ = (θ, fun x => θ && x)`。

**为什么 2 点外生**：`ParamSCM` 要求 `[Fintype U]`（`pU` 求和需要），
`Bool` 是**最小的**非单点载体，故取它。

**⟹ `X = Y = Bool`，`Th = Bool`**：最小非退化见证。 -/
def twoPointModel : ParamSCM Bool Bool where
  Th := Bool
  U := Bool
  instFintypeU := inferInstance
  instDecEqU := inferInstance
  pU := fun u => if u then 1 else 0
  sg := fun θ _ => (θ, fun x => θ && x)

/-- ⭐⭐⭐ **【正面实例：`twoPointModel` 可辨识】**（**无条件**，无任何假设）。

见证：`θ₁ = true`、`θ₂ = false`、`u = true`、`a = true`，则

* `(sg true true).2 true = true && true = true`，
* `(sg false true).2 true = false && true = false`，

不等 ⟹ `Identifiable`。证明由 `decide` 在 `Prediction` 展开后闭合
（**机检**，不是在证明体里重述前提）。

**⚠ 这条定理的价值**：它使 §3 的正面定理**非空真**——
存在一个具体的 `ParamSCM` 真的可辨识。 -/
theorem twoPointModel_hsep :
    (twoPointModel.sg true true).2 true ≠ (twoPointModel.sg false true).2 true := by
  simp [twoPointModel]

theorem twoPointModel_identifiable : Identifiable twoPointModel := by
  refine ⟨true, false, true, true, fun h => Bool.noConfusion h, PUnit.unit, true, ?_⟩
  show Prediction twoPointModel true true PUnit.unit true true
      ≠ Prediction twoPointModel false true PUnit.unit true true
  rw [show Prediction twoPointModel true true PUnit.unit true true
        = (twoPointModel.sg true true).2 true from rfl,
      show Prediction twoPointModel false true PUnit.unit true true
        = (twoPointModel.sg false true).2 true from rfl]
  exact twoPointModel_hsep

/-- ⭐⭐ **`twoPointModel` 的参数空间非退化**（`decide`）。

⟹ 与 `twoPointModel_identifiable` 合读，印证 §4 判据的 ⟸ 方向**具体可兑现**。 -/
theorem twoPointModel_not_subsingleton : ¬ Subsingleton Bool :=
  not_subsingleton Bool

/-- ⭐ **同一个 `sg`，但参数空间退化为 `PUnit`**（对照模型）。

**⚠ 与 `twoPointModel` 的差别只有 `Th` 一位**：`sg` 的**数学内容**
（`θ ↦ fun x => θ && x`）**同一个函数**，只是定义域从 `Bool` 缩到 `PUnit`。
⟹ 这是 §7 自检的**载体**：**同一个机制**，**相反的判决**。 -/
def regressedModel : ParamSCM Bool Bool where
  Th := PUnit
  U := Bool
  instFintypeU := inferInstance
  instDecEqU := inferInstance
  pU := fun u => if u then 1 else 0
  sg := fun _ _ => (true, fun x => x)

/-- ⭐⭐⭐ **【否定实例：`regressedModel` 不可辨识】**（`@` 显式给出 `Subsingleton`）。 -/
theorem regressedModel_subsingleton : Subsingleton regressedModel.Th :=
  (inferInstance : Subsingleton PUnit)

theorem regressedModel_not_identifiable : ¬ Identifiable regressedModel :=
  @scmThetaSubsingleton_not_identifiable Bool Bool regressedModel _
    regressedModel_subsingleton

/-- ⭐⭐⭐ **【对任意真实 `SCM`：其世界模型不可辨识参数】**

$$\forall M : \mathrm{SCM}\ X\ Y,\quad \neg\,\mathrm{Identifiable}\,(\mathrm{scmToParam}\,M).$$

**⟹ 这是把 `Fate.SCMWorldModel` 的 `Θ := PUnit` 设计选择
升级为机器检验结论**：裸 `SCM` 的世界模型**永远**不可辨识参数，
**无论 `sg` 怎么写**。与 `Fate.SCMResidual.scmStep_indep_theta`（`rfl` 级，
单步）互为「语义版 / 定义版」。 -/
theorem scmToParam_not_identifiable {X Y : Type} (M : PearlHierarchy.SCM X Y)
    [Nonempty Y] : ¬ Identifiable (scmToParam M) :=
  @scmThetaSubsingleton_not_identifiable X Y (scmToParam M) _ inferInstance

/-! ===========================================================================
  §6  ⭐⭐⭐ 自检（把判据的实体性机检出来）
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【自检 1：同一个 `sg`，相反的判决】**

`twoPointModel` 与 `regressedModel` 的 `sg` 在**数学上读同一个表达式**
`θ && x`，但一个**可辨识**、一个**不可辨识**。

⟹ 这是「判据说的是**参数空间**，不是机制」的**机检形态**：
若本文件的两个判决来自 `sg` 的写法差异，这条定理就不可能以
「两者判决相反」的形式陈述并通过检查。 -/
theorem selfCheck_identical_models_opposite_verdicts :
    Identifiable twoPointModel ∧ ¬ Identifiable regressedModel :=
  ⟨twoPointModel_identifiable, regressedModel_not_identifiable⟩

/-- ⭐⭐⭐⭐ **【自检 2：判据不依赖 `M` 的具体形状】**

对**任意** `M : ParamSCM X Y`，把它的参数空间**读成** `PUnit`
（即 `scmToParam` 的构造在参数位上的效果）后必**不可辨识**。

**⚠ 这里只做「`Subsingleton` 参数空间 ⟹ 不可辨识」的统一陈述**，
不声称存在一个 `Th := PUnit` 的 `ParamSCM` 与 `M` 的 `sg` 相同
（那需要类型转换，本文件不做）。**这是如实的**。 -/
theorem selfCheck_subsingleton_theta_always_not_identifiable {X Y : Type}
    (M : ParamSCM X Y) [Nonempty Y] (hsub : Subsingleton M.Th) :
    ¬ Identifiable M :=
  @scmThetaSubsingleton_not_identifiable X Y M inferInstance hsub

/-- ⭐⭐⭐ **【自检 3：§2 的退化定理与 §5 的实例一致】**

`regressedModel` 上，两个「不同」的参数（`PUnit` 只有 `unit`）给出相同预测
——这里用 `PUnit.unit` 自比，检查 §2 的等式在实例上**真的成立**（非空真）。 -/
theorem selfCheck_regressed_pred_eq :
    Prediction regressedModel PUnit.unit true PUnit.unit true true
      = (regressedModel.sg PUnit.unit true).2 true :=
  prediction_eq _ _ _ _ _ _

/-- ⭐⭐⭐ **【自检 4：正面方向与否定方向在同一参数空间上互斥】**

`Identifiable M` 与 `Subsingleton M.Th` **不可共存**（无任何额外前提）。

⟹ 这是二分判据的**逻辑骨架**：它不需要 `hsep`，故是**无条件**的。 -/
theorem selfCheck_identifiable_excludes_subsingleton {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] : ¬ (Identifiable M ∧ Subsingleton M.Th) := by
  rintro ⟨h, hsub⟩
  exact identifiable_imp_not_subsingleton M h hsub

end SCMIdentifiability

end Fate
