import FateWorld.FateV2.Loop.EndToEnd
/-!
  # Predict · KK1NoiseAsymmetry

  ## 迁移登记
  - 来源：`FateWorld/Legacy/KK1NoiseAsymmetry.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd
  - 补充 open 域：FateV2.Loop, FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `KK1NoiseAsymmetry` —— **噪声不对称的核实与后果**（KK1）

  ## 0  被核实的判断

  主控的偏移自查提出如下结构不对称：

  * `ResidualLoop.predicted`（约 495–506 行）取
    `ε : ℕ → W.frame.Ν.Carrier`，**在第 `n` 步用的是 `ε n`**（噪声随时间变化）；
  * `EndToEnd.endToEnd`（约 240–249 行）与 `endToEndIter`（约 445–453 行）
    取 `ε : W.frame.Ν.Carrier`，**只是一个单点值**（噪声不随时间变化）。

  本文件**逐条核实**该判断，并在具体世界模型上展示其后果。

  ## 1  核实结论（先说结论）

  **不对称属实，且比描述的还强一层。**

  | 事实 | 出处 | 结论 |
  |---|---|---|
  | A1 | `ResidualLoop.predicted` 的签名 `ε : ℕ → Ν.Carrier` | 是**序列** |
  | A2 | `ResidualLoop.predicted_eq`：`= W.f (W.sim ... n) (u n) (ε n) θ (a n)` | 真用 **`ε n`** |
  | B1 | `EndToEnd.endToEnd` 的签名 `ε : W.frame.Ν.Carrier` | 是**单点** |
  | B2 | `EndToEnd.endToEndIter` 的签名 `ε : W.frame.Ν.Carrier` | 是**单点**，且**每步复用同一个** |
  | B3 | `EndToEnd.endToEndIter_succ`（`rfl`）：递归里 `ε` 原样传递 | 迭代中**无任何量携带噪声的时间索引** |

  **强于描述的那一层**：`endToEnd` / `endToEndIter` 不只把噪声当常数，
  它们**根本没有位置**安放 `ε n` —— 签名里没有 `n`。
  故「模型内部认为噪声是常数」是准确的，而且「模型无法表达噪声的时间变化」
  是类型层的事实，不是语义层的近似。

  ## 2  后果（具体世界模型）

  本文件构造一个具体世界模型 `demoW`（状态/参数/噪声都取 `ℤ`），机制
  $$f(x,u,\varepsilon;\theta,a) = x + \varepsilon + \theta$$
  （**状态累加、噪声可加**，即噪声在每一步都真实进入状态）。

  在该模型上证明：

  | 定理 | 内容 |
  |---|---|
  | `demoW_sim_one/two` | 真实轨迹：`sim 1 = ε 0 + θ`，`sim 2 = (ε 1 + θ) + (ε 0 + θ)` |
  | `demoW_predicted_uses_eps_succ` | `predicted` 在 `n=2` 处用到 `ε 2`、`ε 1`、`ε 0`（事实 A2 的落地）|
  | `no_constant_noise_matches` | **不存在** 任何常数噪声 `c` 使模型轨迹与真实轨迹在 `t=1` 与 `t=2` **同时**吻合 |
  | `endToEnd_correct_fixed` | 用**当前**噪声 `ε = 1`：`endToEnd` **不动** `θ`（残差为 `0`）|
  | `endToEnd_false_move` | 用**陈旧/固定**噪声 `ε = 0`：`endToEnd` 把 `θ` 从 `0` 推到 `1`（**臆造出一个不存在的残差**）|
  | `endToEndIter_wrong_at_step1` | 于是 `endToEndIter ... 1 θ` 给出 `1`，而真实系统在该时刻残差为 `0` |

  ⭐ **读法**：同一个观测 `y = 1`、同一个起点 `x = 0`、同一组参数 `θ = 0`，
  仅因「用哪一步的噪声」不同，`θ` 的更新结果从 `0` 变成 `1`。
  这就是「模型内部把噪声当常数」的可观测后果：**θ 被错误地驱动**。

  ## 3  ⚠ 诚实边界（必须写清）

  1. **`EndToEnd` 的 §6 已明文声明**「`y`／`x`／`u`／`ε`／`a` 保持固定……
     换时刻的版本需要它们也随 `k` 变 —— 那是**另一件事**，本文件**不**混入」。
     故本文件**不指控** `EndToEnd` 违反了它自己的承诺；
     本文件核实的是**两个模块放在一起时**产生的结构落差：
     `predicted` 有 `n`，`endToEndIter` 没有 `n`。
     这个落差**正是** `y/u/ε/a` 被固定的后果，且**只在噪声一项上**是致命的
     —— 因为 `u`／`a` 的固定可以是设计选择，而 `ε` 的固定**违反噪声的定义**
     （噪声按规格是每步独立的 $\varepsilon_t \sim \mathcal{D}_\varepsilon$）。
  2. 本文件**不**声称 `endToEndIter` 应如何改写（那属于修改既有模块，
     依纪律本文件**不做**）。本文件只**核实与展示后果**。
  3. 本文件**不**证任何收敛/发散定理；`no_constant_noise_matches` 是
     **两点不吻合**的有限陈述，不是渐近发散。
  4. 具体模型的 `f` 故意取最简单形式 `x + ε + θ`：它使「噪声真进入状态」
     成为可计算事实。该模型**不**声称是任何真实系统的代表。
  5. 各具体世界模型分量用 `abbrev` 而非 `def`，**仅为让类型类合成能看见载体 `ℤ`**；
     这是技术需要，不改变任何数学内容。

  ## 4  结构

  | 节 | 内容 |
  |---|---|
  | §1 | 不对称的**类型层**事实（A1/A2/B1/B3）|
  | §2 | 具体世界模型 `demoW` |
  | §3 | 真实轨迹的两步计算 |
  | §4 | 无常数噪声可同时吻合两步 |
  | §5 | `endToEnd` 的后果：陈旧噪声 ⟹ 臆造残差 ⟹ `θ` 被错误驱动 |
  | §6 | `endToEndIter` 的后果 |
  | §7 | 自检清单 |

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**本文件不改动任何既有模块**。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Loop
open FateV2.Model
open FateV2.Modeling
namespace KK1NoiseAsymmetry

universe u v

/-! ===========================================================================
    §1  不对称的**类型层**事实

    这一节不做具体计算，只把「谁的 `ε` 是什么类型」钉成可引用的事实。
    不对称在类型层就已经确定。
    =========================================================================== -/

/-- **事实 A（对照用）**：`ResidualLoop.predicted` 的噪声参数是**序列**，
且第 `n` 步读的是 `ε n`（`predicted_eq` 的逐字内容）。 -/
theorem fact_A_predicted_reads_sequence (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    FateV2.Loop.ResidualLoop.predicted W θ u ε a n
      = W.f (W.sim θ u ε a n) (u n) (ε n) θ (a n) :=
  FateV2.Loop.ResidualLoop.predicted_eq W θ u ε a n

/-- **事实 B1**：`EndToEnd.endToEnd` 的噪声参数是**单点** `Ν.Carrier`。

本定理以「一个具体调用」把签名钉死：右式的 `ε` 位**不接受序列**，
故 `endToEnd` **无法**在图内表达 `ε n`。 -/
theorem fact_B1_endToEnd_single_noise (W : WorldModel)
    [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    FateV2.Loop.EndToEnd.endToEnd W h η φ y θ u ε a x
      = θ + η * φ (FateV2.Loop.EndToEnd.observe h y
          - FateV2.Loop.EndToEnd.predFrom W θ u ε a x) :=
  FateV2.Loop.EndToEnd.endToEnd_apply W h η φ y θ u ε a x

/-- **事实 B3**：`endToEndIter` 的递归把**同一个** `ε` 原样传给下一步
（`endToEndIter_succ` 的逐字内容）。

⟹ 迭代中**没有任何量**携带「这一步该用哪个 `ε n`」。
这是不对称的**机制性**说明：不是「忘了传」，而是**签名里没有可传的位**。 -/
theorem fact_B3_iter_reuses_same_noise (W : WorldModel)
    [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (k : ℕ) (θ : W.frame.Θ.Carrier) :
    FateV2.Loop.EndToEnd.endToEndIter W h η φ y u ε a x (k + 1) θ
      = FateV2.Loop.EndToEnd.endToEndIter W h η φ y u ε a x k
          (FateV2.Loop.EndToEnd.endToEnd W h η φ y θ u ε a x) :=
  FateV2.Loop.EndToEnd.endToEndIter_succ W h η φ y u ε a x k θ

/-! ===========================================================================
    §2  具体世界模型 `demoW`

    状态 `X`、参数 `Θ`、噪声 `Ν` 全部取 `ℤ`；输入 `U`、动作 `Act` 取 `Unit`。
    机制：`f x u ε θ a = x + ε + θ`。

    **为什么取 `ℤ`**：残差需要加法群（`ResidualLoop` 的既有要求）、
    写回需要环，`ℤ` 两者都给，且所有计算可被 `omega`/`norm_num` 终结。
    =========================================================================== -/

/-- 具体状态空间：`ℤ`（离散拓扑 / 离散可测）。 -/
abbrev demoStateSpace : StateSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 具体参数空间：`ℤ`。 -/
abbrev demoThetaSpace : ThetaSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤

/-- 具体输入空间：`Unit`。 -/
abbrev demoInputSpace : InputSpace where
  Carrier := Unit
  topo := ⊤
  meas := ⊤

/-- 具体动作空间：`Unit`。 -/
abbrev demoActionSpace : ActionSpace where
  Carrier := Unit
  topo := ⊤
  meas := ⊤

/-- 具体噪声空间：`ℤ`。 -/
abbrev demoNoiseSpace : NoiseSpace where
  Carrier := ℤ
  meas := ⊤

/-- 具体上下文空间：`Unit`。 -/
abbrev demoCtx : CtxSpace where
  Carrier := Unit

/-- 具体框架。 -/
abbrev demoFrame : Frame where
  Θ := demoThetaSpace
  X := demoStateSpace
  U := demoInputSpace
  Act := demoActionSpace
  Ν := demoNoiseSpace

/-- 具体规则（任意核，本文件不使用其语义；只为满足 `WorldModel` 的非空约束）。 -/
abbrev demoRule : Rule demoCtx demoStateSpace demoStateSpace where
  kernel := fun _ _ => 0

/-- **具体机制**：`f x u ε θ a = x + ε + θ`（噪声可加、状态累加）。 -/
abbrev demoF : Step demoFrame := fun x _u ε θ _a => x + ε + θ

/-- 具体模拟器。 -/
abbrev demoSimulator : WorldSimulator demoFrame where
  step := demoF
  horizon := 2

/-- 具体选择器（任意，本文件不用）。 -/
abbrev demoSelector : Selector demoCtx demoStateSpace demoStateSpace where
  select := fun _ _ _ => (demoRule, 0)
  criterion := fun _ _ _ => 0

/-- 具体规则集块（非空性由 `demoRule` 提供）。 -/
abbrev demoRules : WorldRules demoCtx demoStateSpace demoStateSpace where
  rules := {demoRule}
  nonempty := ⟨demoRule, rfl⟩

/-- **具体世界模型**：初值 `x₀ = 0`，机制 `x + ε + θ`。 -/
abbrev demoW : WorldModel where
  frame := demoFrame
  ctx := demoCtx
  state :=
    { space := demoStateSpace
      cur := 0
      initial := { val := 0, isRandom := false } }
  rules := demoRules
  simulator := demoSimulator
  selector := demoSelector
  state_consistent := rfl

/-- `demoW` 的状态载体确实是 `ℤ`（供下游使用）。 -/
theorem demoW_X_carrier : demoW.frame.X.Carrier = ℤ := rfl

/-- `demoW` 的初值确实是 `0`。 -/
theorem demoW_initial : demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => (0 : ℤ)) (fun _ => ()) 0
    = 0 :=
  WorldModel.sim_zero demoW _ _ _ _

/-! ===========================================================================
    §3  真实轨迹的两步计算

    `sim 0 = 0`（初值），`sim (n+1) = sim n + ε n + θ`。
    故 `sim 1 = ε 0 + θ`，`sim 2 = (ε 1 + θ) + (ε 0 + θ)`。
    =========================================================================== -/

/-- 真实轨迹第 `n+1` 步的转移式（机制展开）。 -/
theorem demoW_sim_succ (θ : ℤ) (u : ℕ → Unit) (ε : ℕ → ℤ) (a : ℕ → Unit) (n : ℕ) :
    demoW.sim θ u ε a (n + 1) = demoW.sim θ u ε a n + ε n + θ :=
  WorldModel.sim_succ demoW θ u ε a n

/-- 真实轨迹起点：`sim 0 = 0`（`demoW` 的初值）。 -/
theorem demoW_sim_zero (θ : ℤ) (u : ℕ → Unit) (ε : ℕ → ℤ) (a : ℕ → Unit) :
    demoW.sim θ u ε a 0 = 0 :=
  WorldModel.sim_zero demoW θ u ε a

/-- **第一步**：`sim 1 = ε 0 + θ`。 -/
theorem demoW_sim_one (θ : ℤ) (u : ℕ → Unit) (ε : ℕ → ℤ) (a : ℕ → Unit) :
    demoW.sim θ u ε a 1 = ε 0 + θ := by
  have h := demoW_sim_succ θ u ε a 0
  rw [demoW_sim_zero] at h
  simpa using h

/-- **第二步**：`sim 2 = (ε 1 + θ) + (ε 0 + θ)`。 -/
theorem demoW_sim_two (θ : ℤ) (u : ℕ → Unit) (ε : ℕ → ℤ) (a : ℕ → Unit) :
    demoW.sim θ u ε a 2 = (ε 1 + θ) + (ε 0 + θ) := by
  have h := demoW_sim_succ θ u ε a 1
  rw [demoW_sim_one] at h
  show demoW.sim θ u ε a 2 = (ε 1 + θ) + (ε 0 + θ)
  rw [h]
  ring

/-- **噪声真的进入了 `predicted`**：`predicted` 在 `n = 2` 处用到 `ε 2`、`ε 1`、`ε 0`
（体现事实 A2）。

**⚠ 本定理不是同义反复**：右式是把 `predicted` 展开到 `demoW` 的两步转移之后
的**计算结果**，其中 `ε 2`／`ε 1`／`ε 0` 各自出现。 -/
theorem demoW_predicted_uses_eps_succ (θ : ℤ) (u : ℕ → Unit) (ε : ℕ → ℤ) (a : ℕ → Unit) :
    FateV2.Loop.ResidualLoop.predicted demoW θ u ε a 2
      = (ε 2 + θ) + (ε 1 + θ) + (ε 0 + θ) := by
  have h := demoW_sim_succ θ u ε a 2
  rw [demoW_sim_two] at h
  show demoW.sim θ u ε a (2 + 1) = (ε 2 + θ) + (ε 1 + θ) + (ε 0 + θ)
  rw [h]
  ring

/-! ===========================================================================
    §4  **无常数噪声可同时吻合两步**（不对称的量化后果）

    取噪声序列 `εT`：`εT 0 = 0`、`εT 1 = 1`。
    真实轨迹（`θ = 0`）：`sim 1 = 0`、`sim 2 = 1`。

    若模型用**常数**噪声 `fun _ => c`，则 `sim 1 = c`、`sim 2 = c + c = 2c`。
    要同时吻合须 `c = 0` 且 `2c = 1` —— **无解**。

    ⟹ **一个以常数为噪声的模型在类型上就不可能复现这条真实轨迹。**
    =========================================================================== -/

/-- 一条**变化的**噪声序列：`εT 1 = 1`、其余 `0`。 -/
abbrev epsT : ℕ → ℤ := fun n => if n = 1 then 1 else 0

/-- `epsT 0 = 0`。 -/
theorem epsT_zero : epsT 0 = 0 := by
  simp [epsT]

/-- `epsT 1 = 1`。 -/
theorem epsT_one : epsT 1 = 1 := by
  simp [epsT]

/-- 真实轨迹（`θ = 0`、噪声 `epsT`）在 `t = 1` 的值：`0`。 -/
theorem true_traj_at_one :
    demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 1 = 0 := by
  rw [demoW_sim_one, epsT_zero]
  ring

/-- 真实轨迹（`θ = 0`、噪声 `epsT`）在 `t = 2` 的值：`1`。 -/
theorem true_traj_at_two :
    demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2 = 1 := by
  rw [demoW_sim_two, epsT_one, epsT_zero]
  ring

/-- **主定理（不对称的后果）**：给定 `epsT`（真实噪声变化），
**不存在**常数噪声 `c` 使模型轨迹与真实轨迹在 `t = 1` 及 `t = 2` **同时**吻合。

$$\neg\ \exists c,\ \mathrm{sim}\ (c,c,c,\dots)\ 1 = \mathrm{sim}\ \varepsilon_T\ 1
\ \wedge\ \mathrm{sim}\ (c,c,c,\dots)\ 2 = \mathrm{sim}\ \varepsilon_T\ 2 .$$

**⚠ 本定理不是同义反复**：它把两边的 `sim` 都**算成了具体整数**
（`c`、`2c` 与 `0`、`1`），再用 `omega` 排除。前件里没有任何一个直接说出结论。 -/
theorem no_constant_noise_matches :
    ¬ ∃ c : ℤ,
        demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 1
          = demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 1
        ∧ demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 2
          = demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2 := by
  rintro ⟨c, h1, h2⟩
  rw [true_traj_at_one] at h1
  rw [true_traj_at_two] at h2
  rw [demoW_sim_one] at h1
  rw [demoW_sim_two] at h2
  simp only at h1 h2
  omega

/-! ===========================================================================
    §5  `endToEnd` 的后果：**陈旧噪声 ⟹ 臆造残差 ⟹ `θ` 被错误驱动**

    设定：观测 `y = 1` 是真实下一状态（真实噪声 `epsT 1 = 1`，`θ = 0`，起点 `0`）。
    用 `h := id`（单射），故 `observe id 1 = 1`。

    * **用当前噪声** `ε = 1`：`predFrom = 0 + 1 + 0 = 1 = 观测` ⟹ 残差 `0` ⟹ `θ` 不动；
    * **用陈旧噪声** `ε = 0`：`predFrom = 0 + 0 + 0 = 0 ≠ 1` ⟹ 残差 `1` ⟹ `θ` 被推到 `1`。
    =========================================================================== -/

/-- 观测映射 `id : ℤ → ℤ` 是单射。 -/
theorem id_injective : Function.Injective (id : ℤ → ℤ) := fun _ _ h => h

/-- `observe id (id 1) = 1`（环节 ① 的正确性在 `id` 上的实例）。 -/
theorem observe_id_one : FateV2.Loop.EndToEnd.observe (id : ℤ → ℤ) (id (1 : ℤ)) = 1 :=
  FateV2.Loop.EndToEnd.observe_apply_of id_injective 1

/-- **用当前噪声 `ε = 1`：`endToEnd` 不动 `θ`（残差为 `0`）**。 -/
theorem endToEnd_correct_fixed :
    FateV2.Loop.EndToEnd.endToEnd demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
      (id (1 : ℤ)) (0 : ℤ) () (1 : ℤ) () (0 : ℤ) = 0 := by
  rw [FateV2.Loop.EndToEnd.endToEnd_apply, observe_id_one]
  show (0 : ℤ) + 1 * ((1 : ℤ) - (0 + 1 + 0)) = 0
  ring

/-- **用陈旧/固定噪声 `ε = 0`：`endToEnd` 把 `θ` 推到 `1`（臆造残差）**。

**⚠ 这不是同义反复**：结论 `= 1` 与 `θ` 的输入 `0` 不同，
且右端是 `writeBack` 展开后的算术结果。 -/
theorem endToEnd_false_move :
    FateV2.Loop.EndToEnd.endToEnd demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
      (id (1 : ℤ)) (0 : ℤ) () (0 : ℤ) () (0 : ℤ) = 1 := by
  rw [FateV2.Loop.EndToEnd.endToEnd_apply, observe_id_one]
  show (0 : ℤ) + 1 * ((1 : ℤ) - (0 + 0 + 0)) = 1
  ring

/-- **对照**：同一个数据、只差噪声一项，`θ'` 从 `1` 变成 `0`（不等）。

即：两个 `endToEnd` 调用**只在噪声参数上不同**，结果不同。
这把「用哪一步的噪声」变成可观测的 `θ` 差异。 -/
theorem endToEnd_noise_sensitivity :
    FateV2.Loop.EndToEnd.endToEnd demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
        (id (1 : ℤ)) (0 : ℤ) () (0 : ℤ) () (0 : ℤ)
      ≠ FateV2.Loop.EndToEnd.endToEnd demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
        (id (1 : ℤ)) (0 : ℤ) () (1 : ℤ) () (0 : ℤ) := by
  rw [endToEnd_false_move, endToEnd_correct_fixed]
  norm_num

/-! ===========================================================================
    §6  `endToEndIter` 的后果

    `endToEndIter` 用**一个** `ε` 跑全部步。用 §5 的陈旧噪声 `ε = 0`，
    第一步就把 `θ` 从 `0` 变成 `1`；而真实系统在该步（噪声 `1`）残差为 `0`，
    `θ` 应保持 `0`。⟹ 迭代结果与真实结果**在该步即偏离**。
    =========================================================================== -/

/-- **迭代一步即偏离**：`endToEndIter ... 1 0 = 1`。 -/
theorem endToEndIter_wrong_at_step1 :
    FateV2.Loop.EndToEnd.endToEndIter demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
      (id (1 : ℤ)) () (0 : ℤ) () (0 : ℤ) 1 (0 : ℤ) = 1 := by
  rw [FateV2.Loop.EndToEnd.endToEndIter_succ, FateV2.Loop.EndToEnd.endToEndIter_zero]
  exact endToEnd_false_move

/-- **对照**：正确的 `θ` 应为 `0`（真实残差为 `0`，`θ` 不动），
而固定噪声迭代给出 `1`。⟹ 迭代结果与真实结果**不等**。 -/
theorem endToEndIter_diverges_from_truth :
    FateV2.Loop.EndToEnd.endToEndIter demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
        (id (1 : ℤ)) () (0 : ℤ) () (0 : ℤ) 1 (0 : ℤ)
      ≠ 0 := by
  rw [endToEndIter_wrong_at_step1]
  norm_num

/-! ===========================================================================
    §7  自检清单（本文件的验收点，逐条可编译）
    =========================================================================== -/

/-- **自检 1**：`predicted` 的噪声位是序列（事实 A1）。 -/
example (θ : ℤ) (u : ℕ → Unit) (ε : ℕ → ℤ) (a : ℕ → Unit) (n : ℕ) :
    FateV2.Loop.ResidualLoop.predicted demoW θ u ε a n = demoW.sim θ u ε a (n + 1) := rfl

/-- **自检 2**：`endToEnd` 的噪声位是单点（事实 B1）—— 类型陈述。 -/
noncomputable example :
    (ℤ → ℤ) → ℤ → (ℤ →+ ℤ) → ℤ → ℤ → Unit → ℤ → Unit → ℤ → ℤ :=
  fun h η φ y θ u ε a x =>
    FateV2.Loop.EndToEnd.endToEnd demoW (h := h) η φ y θ u ε a x

/-- **自检 3**：真实轨迹两步不同（`0 ≠ 1`）—— 不对称的**素材**。 -/
example : demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 1
    ≠ demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2 := by
  rw [true_traj_at_one, true_traj_at_two]
  norm_num

/-- **自检 4**：常数噪声下两步相同的前提会逼出 `c = 0`，佐证 `no_constant_noise_matches`。 -/
example (c : ℤ) :
    demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 1
        = demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 2
      → c = 0 := by
  intro h
  rw [demoW_sim_one, demoW_sim_two] at h
  simp only at h
  omega

end KK1NoiseAsymmetry
end FateV2.Predict