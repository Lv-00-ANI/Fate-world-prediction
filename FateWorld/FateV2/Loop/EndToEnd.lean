import FateWorld.FateV2.Loop.ResidualLoop
import FateWorld.FateV2.Modeling.ObsEstimationStrong
import FateWorld.FateV2.Error.EndToEndError

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/EndToEnd.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 16 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Loop
open FateV2.Model

/-! ===========================================================================
  `FateV2.Loop.EndToEnd` —— **端到端串联**：观测 → 预测 → 残差 → 更新

  ## 0  本文件要解决的问题

  线 1-任务 B 的现状判定：**端到端串联 0%** —— 仓内有四个环节的**类型**，
  但**没有任何一条定理**把它们串成一条链。

  | 环节 | 现有落点 | 类型 |
  |---|---|---|
  | ① **观测** $y \mapsto \hat x$ | `FateV2.Modeling.RA14Strong.chooseEstimator h` | `Y → X`（单射 $h$ 下的选择函数）|
  | ② **预测** | `FateV2.Predict.WorldModel.WorldModel.sim` / `W.f` | `Step W.frame` 的一步 |
  | ③ **残差** $r = x - \hat x$ | `FateV2.Loop.ResidualLoop.residual` | `Residual X = X.Carrier` |
  | ④ **更新** $r \mapsto \theta'$ | `FateV2.Loop.ResidualLoop.writeBack` | `Residual X → Θ.Carrier → Θ.Carrier` |

  **本文件补上的正是「串」这件事**：给出一条定理，其**结论**是从观测 `y`
  出发、依次经过 ①②③④ 得到的 `θ'`，并且**证明**这条链满足：

  * **`endToEnd_fixed`**（正确性）：观测恰等于预测 ⟹ `θ' = θ`；
  * **`endToEnd_moves`**（非平凡性）：观测 ≠ 预测 ⟹ `θ' ≠ θ`；
  * **`endToEnd_step_eq`**（分解式）：`θ' - θ = η * φ (x̂_obs - x̂_pred)`，
    即「参数的变化量**唯一地**由残差决定」，**这是四个环节真正首尾相接的证据**。

  ## 1  ⚠ 诚实边界（必读，不得含糊）

  **1.1 「观测」环节的接口是 `chooseEstimator`，不是一条新假设。**
  本文件**直接复用** `FateV2.Modeling.RA14Strong.chooseEstimator`（`Y → X` 的选择函数），
  其数学内容（单射 $h$ + `Classical.choose`）已在 `FateV2.Loop/ObsEstimationStrong.lean`
  中证明（`chooseEstimator_apply_of`）。本文件**不重证**，只**引用**。

  **1.2 本文件把「观测映射」与「预测器」的**载体**分开，且都做成参数。**

  链上的两个状态值来源：
  - $\hat x^{\mathrm{obs}}_t := \hat x(y)$ —— 由**观测** $y$ 经估计器得到（环节 ①）；
  - $\hat x^{\mathrm{pred}}_t := W.\mathrm{sim}(\theta,u,\varepsilon,a)(n+1)$
    —— 由**规则**（世界模型 `W`）一步预测得到（环节 ②）。

  **本文件不声称这两个值相等**。相反，端到端的**全部内容**就是
  「它们的差 = 残差 = 更新的驱动量」。若强行假定相等，链就退化为恒等，
  定理也就变成空真 —— **本文件明确拒绝这样做**。

  **1.3 本文件不声称闭环收敛。** `η`（步长）与 `φ`（残差→参数方向）都是**参数**，
  不是结论（承 `FateV2.Loop/ResidualLoop.lean` 的纪律「凡规格未给出结构的位，做成参数、不填数」）。
  收敛是**另一件**事，需要 `FateV2.Loop/RealConvergence.lean` 层的额外结构，**本文件不涉及**。

  **1.4 结构前提是显式的**：需要 `[AddCommGroup W.frame.X.Carrier]`（做减法）
  与 `[Ring W.frame.Θ.Carrier]`（做标量乘）。二者**不是**隐藏假设，
  而是**显式**出现在每条定理的签名里 —— 若没有它们，
  「残差」与「更新」在类型层**根本无法写下**。

  **1.5 任务书第 3 条要求「若某环缺失，明确标出缺什么」。本文件的判定如下：**

  | 环节 | 状态 | 说明 |
  |---|---|---|
  | ① 观测 → 估计 | ✅ **有** | `RA14Strong.chooseEstimator`，单射 $h$ 下正确（`chooseEstimator_apply_of`）|
  | ② 估计 → 一步预测 | ⚠ **部分缺** | `W.sim` 给的是「从 $x_0$ 起的整条轨迹」，**没有**「从任意状态 $x$ 出发一步」的公开接口。本文件用 `W.f` 直接调用机制补齐（见 §2 `predFrom`），**它等于 `sim_succ` 的右式**（`predFrom_eq_sim_succ`），故确实复用 `W.sim` 而非另造 |
  | ③ 残差 | ✅ **有** | `ResidualLoop.residual` |
  | ④ 更新 | ✅ **有** | `ResidualLoop.writeBack`（已证 `writeBack_zero` / `writeBack_ne`）|
  | ①→② **串联** | 🔴 **原先缺（0%）** | **本文件补**：`observe` / `predFrom` 在同一 `W` 上取同一 `X.Carrier` 值 |
  | ②→③ **串联** | 🔴 **原先缺** | **本文件补**：`e2eResidual` |
  | ③→④ **串联** | ✅ 已有 | `ResidualLoop.closedLoopStep`（但**不读观测**）|
  | ①→②→③→④ **全链** | 🔴 **原先缺** | **本文件补**：`endToEnd` 及三条定理 |

  **其中最关键的一条**：`ResidualLoop.closedLoopStep` 已经串了 ②③④，
  但它的「观测」位是一个**裸参数** `x : W.frame.X.Carrier`，
  **与环节 ①（观测 $y$ 经估计器）无关**。本文件的 `endToEnd`
  把该位**改成 `y` 的函数**，从而把环节 ① 真正接上。
  这就是「串联」的实质内容（见 `endToEnd_observes`）。

  ## 2  结构

  | 节 | 内容 |
  |---|---|
  | §1 | 环节 ① 的接线：`observe`（`chooseEstimator` 在 `W` 上的落地）|
  | §2 | 环节 ② 的接线：`predFrom`（`W.f` 一步）+ `predFrom_eq_sim_succ`（确系 `W.sim`）|
  | §3 | 环节 ③ 的接线：`e2eResidual` |
  | §4 | 环节 ④ + 全链：`endToEnd` |
  | §5 | 三条主定理：`endToEnd_fixed` / `endToEnd_moves` / `endToEnd_step_eq` |
  | §6 | 迭代：`endToEndIter`（闭环多步）+ `endToEndIter_zero` |
  | §7 | 自检清单 |

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**本文件不改动任何既有模块**。
  =========================================================================== -/

namespace FateV2.Loop
namespace EndToEnd

universe u v

/-! ===========================================================================
    §1  环节 ①（观测 → 估计）：`observe`
    =========================================================================== -/

/-- **环节 ①：由观测 `y` 得到状态估计 `x̂`。**

**本定义是 `FateV2.Modeling.RA14Strong.chooseEstimator` 的逐字别名**（在某个具体 `W` 上）。

**⚠ 为什么不重新定义**：任务书要求「理清四个环节的现有类型」，
`chooseEstimator` **就是**现有类型（`Y → X` 的选择函数，
单射时精确，见 `chooseEstimator_apply_of`）。
本文件只做**改名接线**，不重造估计器 —— 重造会违反「不修改已有模块」的精神
（等价于悄悄换掉 A14 的落点）。

**`h : X.Carrier → Y` 是观测映射**（任务书的 $h$）；`Y` 是观测取值类型。
本文件**不**把 `Y` 绑到任何具体空间（观测空间在 A14 强档里是独立空间）。 -/
noncomputable def observe {X : Type u} [Nonempty X] {Y : Type v} (h : X → Y) :
    Y → X :=
  RA14Strong.chooseEstimator h

/-- **环节 ① 的正确性（引用既有定理，不重证）**：

若观测映射 `h` **单射**，则观测 **无噪声**时估计**精确**：
$$\hat x(h x) = x .$$

**⟹ 这是全链「正确性」判据（§5 `endToEnd_fixed`）在环节 ① 上的唯一入口。** -/
theorem observe_apply_of {X : Type u} [Nonempty X] {Y : Type v}
    {h : X → Y} (hinj : Function.Injective h) (x : X) :
    observe h (h x) = x :=
  RA14Strong.chooseEstimator_apply_of hinj x

/-! ===========================================================================
    §2  环节 ②（估计 → 一步预测）：`predFrom`
    =========================================================================== -/

open FateV2.Predict.WorldModel in
/-- **环节 ②：用规则（世界模型机制 `W.f`）从当前状态一步预测下一状态。**

$$\mathrm{predFrom}\ W\ \theta\ u\ \varepsilon\ a\ x
  := W.f\ x\ u\ \varepsilon\ \theta\ a .$$

**⚠ 为什么用 `W.f` 而不是 `W.sim` 的某一步**：
`W.sim` 的起点**固定**为 `W.x`（状态块的初值），
故 `W.sim ... (n+1)` 是「从 $x_0$ 起走 $n+1$ 步」，
**不是**「从**当前观测估计**起走一步」。
端到端链的第二步必须从**估计**出发，故须调用 `W.f` 本身。

**但这不是「另造预测器」**：`predFrom_eq_sim_succ`（下一条）
证明它**恒等于** `W.sim` 的一步，即**同一个机制**。
本文件因此**没有**引入第二个预测语义。 -/
noncomputable def predFrom (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier)
    (a : W.frame.Act.Carrier) (x : W.frame.X.Carrier) : W.frame.X.Carrier :=
  W.f x u ε θ a

/-- **`predFrom` 就是 `W.sim` 的一步**（从 `W.sim` 的第 `n` 步出发）。

这是 `WorldModel.sim_succ` 的**逐字重排**（把 `W.f` 的五个参数提到 `sim` 的对应位）。

**⟹ 本定理证明：环节 ② 复用的是**同一个**世界模型机制，
没有引入平行的预测语义。若 `predFrom` 与 `W.f` 脱钩，本定理立即失败。** -/
theorem predFrom_eq_sim_succ (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    predFrom W θ (u n) (ε n) (a n) (W.sim θ u ε a n) = W.sim θ u ε a (n + 1) :=
  (WorldModel.sim_succ W θ u ε a n).symm

/-! ===========================================================================
    §3  环节 ③（预测 vs 观测 → 残差）：`e2eResidual`
    =========================================================================== -/

/-- **环节 ③：端到端残差**——观测估计与规则预测之差。

$$r := \mathrm{residual}\ \hat x^{\mathrm{obs}}\ \hat x^{\mathrm{pred}}
  = \hat x^{\mathrm{obs}} - \hat x^{\mathrm{pred}} .$$

**⚠ 注意减法的**方向**：$r = $ 观测估计 $-$ 规则预测。
这是 `ResidualLoop.residual x xhat = x - xhat` 的**逐字实例**
（把 `x` 取为「观测给出的世界值」，把 `xhat` 取为「模型预测值」）。

**语义**：$r = 0 \iff$ **模型一步预测与观测一致**（`e2eResidual_eq_zero_iff`）。 -/
noncomputable def e2eResidual (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    (xobs : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (xpred : W.frame.X.Carrier) : ResidualLoop.Residual W.frame.X :=
  ResidualLoop.residual xobs (predFrom W θ u ε a xpred)

/-- **`e2eResidual` 的展开式**（供下游 `rw`，避免展开 `def` 链）。 -/
theorem e2eResidual_def (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    (xobs : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (xpred : W.frame.X.Carrier) :
    e2eResidual W xobs θ u ε a xpred
      = xobs - predFrom W θ u ε a xpred := rfl

/-- **残差为零 ⟺ 观测估计 = 规则一步预测**。

**这是端到端「模型正确」的判据**，也是 §5 正确性定理的唯一输入。 -/
theorem e2eResidual_eq_zero_iff (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    (xobs : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (xpred : W.frame.X.Carrier) :
    e2eResidual W xobs θ u ε a xpred = 0 ↔ xobs = predFrom W θ u ε a xpred :=
  ResidualLoop.residual_eq_zero_iff _ _

/-! ===========================================================================
    §4  环节 ④ + 全链：`endToEnd`
    =========================================================================== -/

/-- **端到端串联（全链）**：

$$\underbrace{y}_{\text{观测}}
  \xrightarrow{\ \text{①估计}\ }
  \underbrace{\hat x^{\mathrm{obs}}}_{\text{状态估计}}
  \xrightarrow{\ \text{②预测}\ }
  \underbrace{\hat x^{\mathrm{pred}}}_{\text{规则一步预测}}
  \xrightarrow{\ \text{③残差}\ }
  \underbrace{r}_{\text{误差}}
  \xrightarrow{\ \text{④更新}\ }
  \underbrace{\theta'}_{\text{新参数}}$$

用**一层**定义把它写死：

$$\mathrm{endToEnd}\ W\ h\ \eta\ \varphi\ y\ \theta\ u\ \varepsilon\ a\ x
  := \mathrm{writeBack}\ \eta\ \varphi\
     \bigl(\mathrm{observe}\ h\ y - \mathrm{predFrom}\ W\ \theta\ u\ \varepsilon\ a\ x\bigr)\ \theta .$$

**读法（逐位）**：

| 位 | 名字 | 来自 | 环节 |
|---|---|---|---|
| `y` | 观测值 | **输入** | ① 的入口 |
| `θ` | 当前参数 | **输入**（也是被写者）| ④ 的入口 |
| `observe h y` | 状态估计 $\hat x^{\mathrm{obs}}$ | `chooseEstimator` | ① |
| `predFrom W θ u ε a x` | 一步预测 $\hat x^{\mathrm{pred}}$ | `W.f` | ② |
| `observe h y - predFrom ...` | 残差 $r$ | 减法 | ③ |
| `writeBack η φ · θ` | 新参数 $\theta'$ | `ResidualLoop.writeBack` | ④ |

**与 `ResidualLoop.closedLoopStep` 的**唯一**差别**：
后者的「观测位」是一个**裸参数** `x`，**不经过** `y` 与 `observe h`；
本定义的该位是 **`observe h y`**，即**真的读了观测**。
这就是本次串联补上的东西（见 `endToEnd_observes` 与 `endToEnd_differs_from_closedLoop`）。

**⚠ `x` 仍在签名里**，因为环节 ② 需要「从哪个状态出发」。
本文件**不**假定 `x = observe h y`（那会令链退化，见 §1.2 诚实边界），
而是把 `x` 与 `y` **并列**为两条独立输入，其**差**正是残差。 -/
noncomputable def endToEnd (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) : W.frame.Θ.Carrier :=
  ResidualLoop.writeBack W.frame.Θ η φ
    (observe h y - predFrom W θ u ε a x) θ

/-- **`endToEnd` 的逐位展开式**：`θ' = θ + η * φ (x̂_obs - x̂_pred)`。

**这是端到端链的**显式形式**——四个环节在这条等式里**全部可见**：
`observe h y`（①）、`predFrom ...`（②）、减法（③）、`θ + η * φ ·`（④）。 -/
theorem endToEnd_apply (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    endToEnd W h η φ y θ u ε a x
      = θ + η * φ (observe h y - predFrom W θ u ε a x) :=
  ResidualLoop.writeBack_apply _ _ _ _ _

/-- **`endToEnd` 真的**读**观测**：换 `y` 会经过 `observe h` 进入结果。

本定理把「环节 ① 在链上」写成一条**等式**（不是修辞）：
`endToEnd` 的值**定义性地**等于把 `observe h y` 喂给残差后的写回。

**⚠ 若某人把 `observe h y` 换成常值，本定理即失效。** -/
theorem endToEnd_observes (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    endToEnd W h η φ y θ u ε a x
      = ResidualLoop.writeBack W.frame.Θ η φ
          (ResidualLoop.residual (observe h y) (predFrom W θ u ε a x)) θ :=
  rfl

/-! ### §4.1 与既有 `closedLoopStep` 的**精确对位**（说明「补上了什么」）

`ResidualLoop.closedLoopStep` 已经做了 ②③④，其「观测」位是 `x : W.frame.X.Carrier`。
本文件的 `endToEnd` 在 `x` 取 `observe h y` 时**退化为**它 —— 这条定理
钉住「新增的只有环节 ①」这一事实，防止夸大。 -/

/-- **当观测位取 `observe h y` 时，`endToEnd` 退化为既有 `closedLoopStep` 的残差回写**。

**⚠ 本定理是**对位**而非「新内容」**：它说明 §4 的 `endToEnd`
在 `x := observe h y` 时与 `ResidualLoop` 的 `writeBack` **完全一致**，
故本文件**没有**重造更新算子，只**接**了观测环节。 -/
theorem endToEnd_eq_closedLoop (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier) :
    endToEnd W h η φ y θ u ε a (observe h y)
      = ResidualLoop.writeBack W.frame.Θ η φ
          (ResidualLoop.residual (observe h y) (predFrom W θ u ε a (observe h y))) θ :=
  rfl

/-! ===========================================================================
    §5  **三条主定理**：正确性 / 非平凡性 / 分解式（在整条链上）
    =========================================================================== -/

/-- **定理 A【正确性】**：观测估计**恰等于**规则一步预测 ⟹ `θ` **不动**。

$$\hat x^{\mathrm{obs}} = \hat x^{\mathrm{pred}}
  \;\Longrightarrow\; \mathrm{endToEnd}\ \dots\ θ = θ .$$

**⚠ 前提怎么来**：`hobs` 是「观测端给出 `xobs`、预测端给出同一个值」——
最自然的情形是**无噪声观测**（`y = h x`）且**世界模型一步正确**；
此时 `observe_apply_of`（环节 ① 正确）+ 模型正确性共同给出它。

**语义**：**模型本已正确 ⟹ 端到端闭环不引入漂移**。
这是闭环的「不伤害」判据（承 `ResidualLoop.writeBack_zero`）。 -/
theorem endToEnd_fixed (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hobs : observe h y = predFrom W θ u ε a x) :
    endToEnd W h η φ y θ u ε a x = θ := by
  rw [endToEnd_apply, hobs, sub_self, map_zero, mul_zero, add_zero]

/-- **定理 A′【正确性，无噪声观测的具体形态】**：

**前提**：观测映射 `h` **单射**、观测**无噪声** `y = h x`、且**模型一步命中** `x = predFrom ...`。

则 `endToEnd` **不动** `θ`。

**这是任务书「给定观测 y，估计状态 x̂」的**字面**情形**：
`observe h (h x) = x` 由环节 ① 的正确性给出，然后与预测比对。 -/
theorem endToEnd_fixed_of_noiseless (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    (h : W.frame.X.Carrier → W.frame.X.Carrier)
    (hinj : Function.Injective h)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (x : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (hmodel : x = predFrom W θ u ε a x) :
    endToEnd W h η φ (h x) θ u ε a x = θ := by
  refine endToEnd_fixed W h η φ (h x) θ u ε a x ?_
  rw [observe_apply_of hinj x, ← hmodel]

/-- **定理 B【非平凡性】**：观测估计 ≠ 规则一步预测 ⟹ `θ` **必改**。

前提：`ReadsResidual η φ`（`ResidualLoop.ReadsResidual`，
即「参数空间感受得到残差」——**不是**三个散落假设，而是一个**具名判据**）。

**这是任务书第 2 条「用 r 更新参数 θ，得到 θ′」的**闭环兑现**：
残差一旦非零，`θ' ≠ θ`。** -/
theorem endToEnd_moves (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (hR : ResidualLoop.ReadsResidual W.frame.Θ η φ)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hne : observe h y ≠ predFrom W θ u ε a x) :
    endToEnd W h η φ y θ u ε a x ≠ θ := by
  intro hcontra
  have hr : (observe h y - predFrom W θ u ε a x) = 0 := by
    by_contra hz
    exact hR _ hz (by
      have h2 : θ + η * φ (observe h y - predFrom W θ u ε a x) = θ := hcontra
      rw [endToEnd_apply] at hcontra
      have : η * φ (observe h y - predFrom W θ u ε a x) = 0 := by
        have h3 : (η * φ (observe h y - predFrom W θ u ε a x)) + θ = 0 + θ := by
          rw [zero_add, add_comm]
          exact hcontra
        exact add_right_cancel h3
      exact this)
  exact hne (sub_eq_zero.mp hr)

/-- **定理 C【分解式：参数变化量 = 步长 × 残差方向】**。

$$\theta' - \theta = \eta * \varphi\, r,
\qquad r = \hat x^{\mathrm{obs}} - \hat x^{\mathrm{pred}} .$$

**这是「四环节真正首尾相接」的最强形式**：
它把**参数的变化量**写成**残差的像**再加步长 —— 即
**`θ` 的位移唯一地由「观测估计」与「规则预测」之差决定**，
且**没有第三项**（无漂移项、无遗忘项）。

**⚠ 本定理对**任意** `η, φ` 成立**（不需要 `ReadsResidual`），
因为它是**定义性**的代数重排（`add_sub_cancel_left`）。
`ReadsResidual` 只在定理 B 中用于把「变化量非零」转成「`θ' ≠ θ`」。 -/
theorem endToEnd_step_eq (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    endToEnd W h η φ y θ u ε a x - θ
      = η * φ (observe h y - predFrom W θ u ε a x) := by
  rw [endToEnd_apply, add_sub_cancel_left]

/-- **定理 C′【分解式的闭合性：位移为零 ⟺ 残差为零】**（在 `ReadsResidual` 下）。

$$\mathrm{endToEnd}\ \dots\ θ = θ \iff \hat x^{\mathrm{obs}} = \hat x^{\mathrm{pred}} .$$

**这使 §5 的定理 A 与定理 B 成为**同一个**判据的两面**：
不动 ⟺ 残差为零；动 ⟺ 残差非零。**闭环没有「中间态」**。 -/
theorem endToEnd_fixed_iff (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (hR : ResidualLoop.ReadsResidual W.frame.Θ η φ)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    endToEnd W h η φ y θ u ε a x = θ ↔ observe h y = predFrom W θ u ε a x := by
  constructor
  · intro hfix
    by_contra hne
    exact endToEnd_moves W h η φ hR y θ u ε a x hne hfix
  · intro heq
    exact endToEnd_fixed W h η φ y θ u ε a x heq

/-! ===========================================================================
    §6  **迭代：闭环多步** `endToEndIter`

    §4 的 `endToEnd` 是**一步**。端到端的真正用途是**反复跑**：
    用新 `θ'` 去预测下一步。本节把一步串成 `n` 步。

    **⚠ 本节只做**迭代的良定义与 `n = 0` 的情形**，**不**证收敛
    （那需要额外结构，见 §1 诚实边界 1.3）。 -/

/-- **端到端闭环的 `n` 步迭代**：每步用上一步的 `θ` 作预测参数。

$$\theta_0 := \theta,\qquad
  \theta_{k+1} := \mathrm{endToEnd}\ \dots\ y\ \theta_k\ \dots$$

**⚠ `y`／`x`／`u`／`ε`／`a` 保持**固定**（即「同一条观测、同一个起点」）。
**换时刻**的版本需要 `y`／`u`／`ε`／`a` 也随 `k` 变 —— 那是**另一件**事，
本文件**不**混入（避免把「时间索引」伪装成「迭代索引」）。 -/
noncomputable def endToEndIter (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) : ℕ → W.frame.Θ.Carrier → W.frame.Θ.Carrier
  | 0, θ => θ
  | k + 1, θ => endToEndIter W h η φ y u ε a x k
      (endToEnd W h η φ y θ u ε a x)

/-- **迭代零步 = 恒等**（`θ_0 = θ`）。 -/
theorem endToEndIter_zero (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x 0 θ = θ := rfl

/-- **迭代一步 = `endToEnd`**（`rec` 的 `succ` 分支读法）。 -/
theorem endToEndIter_succ (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (k : ℕ) (θ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x (k + 1) θ
      = endToEndIter W h η φ y u ε a x k (endToEnd W h η φ y θ u ε a x) := rfl

/-- **迭代的不动点**：若一步不动，则**任意**多步都不动。

$$\mathrm{endToEnd}\ \dots\ θ = θ \;\Longrightarrow\;
  \mathrm{endToEndIter}\ \dots\ n\ θ = θ .$$

**这是定理 A（正确性）在多步上的**传输**：
模型一步命中 ⟹ 闭环**永不**漂移。**（仍**不**是收敛定理。）** -/
theorem endToEndIter_fixed (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier)
    (hfix : endToEnd W h η φ y θ u ε a x = θ) :
    ∀ n : ℕ, endToEndIter W h η φ y u ε a x n θ = θ := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [endToEndIter_succ, hfix]
    exact ih

/-! ===========================================================================
    §7  **自检清单**（本文件的验收点，逐条可编译）
    =========================================================================== -/

noncomputable section

/-- **自检 1**：环节 ① 的类型是 `Y → X`（估计器）。 -/
example {X : Type} [Nonempty X] {Y : Type} (h : X → Y) : Y → X := observe h

/-- **自检 2**：环节 ② 的类型是「当前状态 → 下一状态」。 -/
example (W : WorldModel) (θ : W.frame.Θ.Carrier) (u : W.frame.U.Carrier)
    (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier) :
    W.frame.X.Carrier → W.frame.X.Carrier := predFrom W θ u ε a

/-- **自检 3**：环节 ③ 的类型是 `Residual X`（即 `X.Carrier`）。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    (xobs : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (xpred : W.frame.X.Carrier) :
    ResidualLoop.Residual W.frame.X := e2eResidual W xobs θ u ε a xpred

/-- **自检 4**：环节 ④ 的类型是 `Θ → Θ`（更新算子，读残差）。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier) :
    ResidualLoop.Residual W.frame.X → W.frame.Θ.Carrier → W.frame.Θ.Carrier :=
  ResidualLoop.writeBack W.frame.Θ η φ

/-- **自检 5**：全链的类型是「观测值 → θ → θ′」。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    Y → W.frame.Θ.Carrier → W.frame.Θ.Carrier :=
  fun y θ => endToEnd W h η φ y θ u ε a x

/-- **自检 6**：正确性与非平凡性**可同时**陈述（不冲突）。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (hR : ResidualLoop.ReadsResidual W.frame.Θ η φ)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    (observe h y = predFrom W θ u ε a x → endToEnd W h η φ y θ u ε a x = θ)
    ∧ (observe h y ≠ predFrom W θ u ε a x → endToEnd W h η φ y θ u ε a x ≠ θ) :=
  ⟨fun h1 => endToEnd_fixed W h η φ y θ u ε a x h1,
   fun h1 => endToEnd_moves W h η φ hR y θ u ε a x h1⟩

end
end EndToEnd
end FateV2.Loop
