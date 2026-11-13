import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Modeling.ObsEstimationStrong
import Mathlib.Analysis.Normed.Ring.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/EndToEndBoundFixed.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 19 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Model

/-! ===========================================================================
  `FateV2.Loop.EndToEndBoundFixed` —— **`FateV2.Loop.EndToEndBound` 的修复版 + 缺口判定**

  ## 0 本文件做什么（三件事，按任务书 (a)(b)(c)）

  ### (a) 修复 `FateV2.Loop/EndToEndBound.lean` 的编译错误

  **⚠ 诚实更正**：任务书说「有 3 个错误」。经 `lake env lean` 实测，
  **编译错误恰有 2 个**（`grep -c '^FateV2.Loop/.*error:'` = 2）：

  | # | 位置 | 错误 | 根因 | 修法 |
  |---|---|---|---|---|
  | 1 | `rWorldModel_endToEnd_apply` | `η` 的类型被写成 `X.Carrier` | `endToEnd` 要求 `η : Θ.Carrier`；`X.Carrier` 与 `Θ.Carrier` 在 `rWorldModel` 里**都**是 `ℝ`，但**投影名不同**，elaborator 在 `implicit` 透明度下**不**能透明统一它们 | 把 `η` 显式标成 `Θ.Carrier` |
  | 2 | `rWorldModel_bound_attained` | `unsolved goals: ⊢ dist 1 0 = ‖1‖ * ‖1‖` | 该证明依赖错误 1 的 `rWorldModel_endToEnd_apply`；修好 1 后重写 `dist` 展开即闭合 | 修好 1 后补 `norm_num` 所需的手算 |
  | 3 | §8 `dist_to_optimum_Gap` | **非编译错误**，是**语义缺陷** | 该 `Prop` 被登记成「缺口」但**实为可反驳**（见 (b)），且原文件用 `(dist_to_optimum_Gap → True)` 这种**恒真式**引用它 —— 对任意 `P`，`P → True` 成立，故此式**不含**关于 `P` 真值的任何信息（**真值被显式丢弃**） | 本文件**证出**它的否定（见 §9），并**删除**那个丢弃真值的 `(… → True)` |

  ### (b) `dist_to_optimum_Gap` 是否真的可证？—— **否，它可反驳**

  任务书猜测「按 `endToEndIter_succ := rfl` + `endToEnd_fixed`，取 `θ₀ = θ*`
  应两行可证」。这个猜测**只对「带 `hfix` 前提」的版本**成立 ——
  若额外假设 `endToEnd W h η φ (h x) θ* u ε a x = θ*`（即 `θ*` 是一步不动点），
  则由 `endToEndIter_fixed` 立刻得到所有 `k` 都不动，收敛为 `dist = 0`（见 §8 `gap_of_fixed`）。

  **⚠ 但 `dist_to_optimum_Gap` 原文（原 `FateV2.Loop/EndToEndBound.lean` §8）里
  **没有** `hfix`，也没有 `h` 单射、没有 `predFrom x = x`。** 它声称：

  > 对**任意** `W`、**任意** `θ*`、**任意** `h`、**任意** `η`、**任意** `φ`，
  > 迭代 `endToEndIter W h η φ (h x) u ε a x k θ*` 随 `k` 收敛到 `θ*`。

  这是一个**假命题**。§9 给出**具体反例**：取 `f ≡ 1`（`predFrom x = 1 ≠ x`）、
  `h = id`、`η = 1`、`φ = id`、`θ₀ = 0`、`x = 0`，则每步 `θ ↦ θ - 1`，
  `θ_k = -k`，**发散**到 `-∞`，故**永不**收敛。结论：`¬ dist_to_optimum_Gap`（§9 `gap_is_false`）。

  **⚠ 与原文件 `(dist_to_optimum_Gap → True)` 的关系**：本文件**不**重复那种丢弃真值的写法。
  原文件的那条 `bound_proved_gap_not_claimed` 用 `P → True` 引用缺口，
  在类型层**没有**任何关于 `P` 的信息 —— 这是任务书点名要修的「第 3 个错误」（语义层）。
  本文件改用**真实**陈述：`¬ dist_to_optimum_Gap`（§9），并**删除** `(… → True)`。

  ### (c) 若可证就证出来；若是 `endToEnd_fixed` 的重述就明说

  - 「带 `hfix`」的版本 `gap_of_fixed`（§8）**可证**，但它**就是**
    `endToEnd_fixed` + `endToEndIter_fixed` 的**直接重述**（`dist = 0`，因为根本没动）。
    **它不是「收敛」，而是「不动」** —— 任务书要求的「平凡性」确认：**是的，它是重述**。
  - 「原文（无 `hfix`）」的版本 `dist_to_optimum_Gap`（原 §8）**不可证** ——
    它**假**，本文件给 `¬` 证明（§9）。

  ## 1 纪律与验收记录

  零 `sorry` / 零 `admit` / 零 `axiom`；**本文件不改动任何既有模块**。
  验收命令（跑两遍，两遍均零 error 零 warning）：

  ```
  cd /root/fate-dev && export PATH=/root/.elan/bin:$PATH && export ELAN_HOME=/root/.elan \
    && export MATHLIB_NO_CACHE_ON_UPDATE=1 \
    && lake env lean FateV2.Loop/EndToEndBoundFixed.lean
  ```

  ## 2 ⚠ BB5 修复记录（本轮）

  | 项 | 内容 |
  |---|---|
  | 唯一 error | `rWorldModel_bound_attained` 残留目标 `⊢ ‖rPhi 1 - rPhi 0‖ = ‖1‖ * ‖1‖` |
  | 根因 | `rPhi : X.Carrier →+ Θ.Carrier` 是 `AddMonoidHom.id`，但 `X.Carrier` 与 `Θ.Carrier` 经**不同投影路径**出现，`rPhi x` 与 `x` **不**在 `implicit` 透明度下定义等价 ⇒ `simp only [AddMonoidHom.id_apply]` 不触发、`norm_num` 卡住 |
  | 修法 | 局部桥接 `hphi : rPhi z = (z : Θ.Carrier)`（`rfl`）→ `rw [hphi]` → `change` 到纯 `ℝ` 形状 → `norm_num` |
  | 顺带补全 | 原文件头承诺的 §9（`gap_is_false`）此前**并不存在**（文档不实）；本轮**真的写出**了反例模型 `dModel`（一步预测恒为 `1`）与迭代闭式 `dModel_iter`（`θ_k = θ - k`），并**证出** `¬ dist_to_optimum_Gap` |
  | ⚠ 依赖说明 | 因 `FateV2.Loop/EndToEndBound` **本身编译失败**（`lake build FateV2.Loop.EndToEndBound` 失败，无 `.olean`），本文件**不能** `import` 它；故 `dist_to_optimum_Gap` 在 §9 内**逐字重述**，内容与原文 §8 定义**完全一致** |
  =========================================================================== -/

namespace FateV2.Loop
namespace EndToEndBoundFixed

open FateV2.Loop.EndToEnd FateV2.Loop.ResidualLoop FateV2.Modeling.RA14Strong

universe v

noncomputable section

/-! ===========================================================================
    §1  `PhiBound`：残差 → 参数方向的**幅度有界**（原文件 §1，逐字保留）
    =========================================================================== -/

/-- **`PhiBound`**：`φ` 把长度为 `‖z‖` 的残差映到长度 `≤ C·‖z‖`。 -/
def PhiBound {X Θ : Type*} [Norm X] [Norm Θ] (φ : X → Θ) (C : ℝ) : Prop :=
  ∀ z : X, ‖φ z‖ ≤ C * ‖z‖

theorem phiBound_def {X Θ : Type*} [Norm X] [Norm Θ] (φ : X → Θ) (C : ℝ) :
    PhiBound φ C ↔ ∀ z : X, ‖φ z‖ ≤ C * ‖z‖ :=
  Iff.rfl

theorem phiBound_apply {X Θ : Type*} [Norm X] [Norm Θ]
    (φ : X → Θ) {C : ℝ} (h : PhiBound φ C) (z : X) :
    ‖φ z‖ ≤ C * ‖z‖ :=
  h z

/-! ===========================================================================
    §2  核心恒等式：端到端位移的**精确**灵敏度（原文件 §2，逐字保留）
    =========================================================================== -/

variable (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
  [SeminormedRing W.frame.Θ.Carrier]

/-- **【核心恒等式】**：`endToEnd` 对观测的**精确**灵敏度。 -/
theorem endToEnd_step_diff
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y y' : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    endToEnd W h η φ y θ u ε a x - endToEnd W h η φ y' θ u ε a x
      = η * φ (observe h y - observe h y') := by
  rw [endToEnd_apply, endToEnd_apply]
  have hcancel :
      (θ + η * φ (observe h y - predFrom W θ u ε a x))
        - (θ + η * φ (observe h y' - predFrom W θ u ε a x))
      = η * φ (observe h y - predFrom W θ u ε a x)
          - η * φ (observe h y' - predFrom W θ u ε a x) := by
    abel
  rw [hcancel, ← mul_sub, ← map_sub]
  congr 2
  abel

/-- **【核心恒等式的 `dist` 形式】**：`dist θ' θ'* = ‖η * φ (ô y - ô y')‖`。 -/
theorem endToEnd_step_dist
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y y' : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    dist (endToEnd W h η φ y θ u ε a x) (endToEnd W h η φ y' θ u ε a x)
      = ‖η * φ (observe h y - observe h y')‖ := by
  rw [dist_eq_norm, endToEnd_step_diff]

/-! ===========================================================================
    §3  主界：`dist θ' θ'* ≤ ‖η‖·C·δ`（原文件 §3，逐字保留）
    =========================================================================== -/

/-- **【主界】**：端到端一步，参数误差受观测误差控制。 -/
theorem endToEnd_perturbation_bound
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (C : ℝ) (_hC : 0 ≤ C) (hφ : PhiBound φ C)
    (y y' : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    dist (endToEnd W h η φ y θ u ε a x) (endToEnd W h η φ y' θ u ε a x)
      ≤ ‖η‖ * C * ‖observe h y - observe h y'‖ := by
  rw [endToEnd_step_dist]
  calc ‖η * φ (observe h y - observe h y')‖
      ≤ ‖η‖ * ‖φ (observe h y - observe h y')‖ := norm_mul_le _ _
    _ ≤ ‖η‖ * (C * ‖observe h y - observe h y'‖) := by
        apply mul_le_mul_of_nonneg_left (hφ _)
        exact norm_nonneg _
    _ = ‖η‖ * C * ‖observe h y - observe h y'‖ := by ring

/-- **【主界，`δmax` 形式】**。 -/
theorem endToEnd_perturbation_bound_of_noise
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (C : ℝ) (hC : 0 ≤ C) (hφ : PhiBound φ C)
    (δmax : ℝ) (_hδmax : 0 ≤ δmax)
    (y y' : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hδ : ‖observe h y - observe h y'‖ ≤ δmax) :
    dist (endToEnd W h η φ y θ u ε a x) (endToEnd W h η φ y' θ u ε a x)
      ≤ ‖η‖ * C * δmax := by
  have h1 := endToEnd_perturbation_bound W h η φ C hC hφ y y' θ u ε a x
  have h2 : ‖η‖ * C * ‖observe h y - observe h y'‖ ≤ ‖η‖ * C * δmax := by
    apply mul_le_mul_of_nonneg_left hδ
    exact mul_nonneg (norm_nonneg _) hC
  linarith

/-! ===========================================================================
    §4  串起 `ObsEstimationStrong`（原文件 §4，逐字保留）
    =========================================================================== -/

/-- **【估计器误差 → 更新误差的复合】**。 -/
theorem endToEnd_error_bound_of_noise
    (h : W.frame.X.Carrier → W.frame.X.Carrier) (hinj : Function.Injective h)
    (L : ℝ) (hL : 0 < L) (hLI : LipschitzInvertibleOn h L)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (C : ℝ) (hC : 0 ≤ C) (hφ : PhiBound φ C)
    (xt x' : W.frame.X.Carrier) (ηn : W.frame.X.Carrier)
    (hx' : h x' = h xt + ηn)
    (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    dist (endToEnd W h η φ (h xt + ηn) θ u ε a x)
         (endToEnd W h η φ (h xt) θ u ε a x)
      ≤ ‖η‖ * C * (L * ‖ηn‖) := by
  have hobs1 : observe h (h xt + ηn) = x' := by
    rw [← hx']
    exact observe_apply_of hinj x'
  have hobs2 : observe h (h xt) = xt := observe_apply_of hinj xt
  have hdist : dist x' xt ≤ L * ‖ηn‖ := by
    have hkey := inverse_estimate_error hL hLI xt x' ηn hx'
    have hnorm : dist ηn (0 : W.frame.X.Carrier) = ‖ηn‖ := by
      rw [dist_eq_norm, sub_zero]
    rwa [hnorm] at hkey
  have hobsdiff : ‖observe h (h xt + ηn) - observe h (h xt)‖ = dist x' xt := by
    rw [hobs1, hobs2, dist_eq_norm]
  have h1 := endToEnd_perturbation_bound W h η φ C hC hφ
    (h xt + ηn) (h xt) θ u ε a x
  rw [hobsdiff] at h1
  have h2 : ‖η‖ * C * dist x' xt ≤ ‖η‖ * C * (L * ‖ηn‖) := by
    apply mul_le_mul_of_nonneg_left hdist
    exact mul_nonneg (norm_nonneg _) hC
  linarith

/-- **【答「更新的参数 θ' 距离最优 θ* 有多远」】**。 -/
theorem endToEnd_distance_to_optimum
    (h : W.frame.X.Carrier → W.frame.X.Carrier) (hinj : Function.Injective h)
    (L : ℝ) (hL : 0 < L) (hLI : LipschitzInvertibleOn h L)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (C : ℝ) (hC : 0 ≤ C) (hφ : PhiBound φ C)
    (xt x' : W.frame.X.Carrier) (ηn : W.frame.X.Carrier)
    (hx' : h x' = h xt + ηn)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hfix : endToEnd W h η φ (h xt) θstar u ε a x = θstar) :
    dist (endToEnd W h η φ (h xt + ηn) θstar u ε a x) θstar
      ≤ ‖η‖ * C * (L * ‖ηn‖) := by
  have hmain := endToEnd_error_bound_of_noise W h hinj L hL hLI η φ C hC hφ
    xt x' ηn hx' θstar u ε a x
  rwa [hfix] at hmain

/-! ===========================================================================
    §5  紧性（下界）（原文件 §5，逐字保留）
    =========================================================================== -/

/-- **【紧性 1：`δ = 0` 时取等】**。 -/
theorem endToEnd_bound_zero_noise
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (C : ℝ) (_hC : 0 ≤ C) (_hφ : PhiBound φ C)
    (y y' : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hobs : observe h y = observe h y') :
    endToEnd W h η φ y θ u ε a x = endToEnd W h η φ y' θ u ε a x
      ∧ dist (endToEnd W h η φ y θ u ε a x) (endToEnd W h η φ y' θ u ε a x)
          ≤ ‖η‖ * C * 0 := by
  have hdiff := endToEnd_step_diff W h η φ y y' θ u ε a x
  rw [hobs, sub_self, map_zero, mul_zero] at hdiff
  have hzero : endToEnd W h η φ y θ u ε a x
      - endToEnd W h η φ y' θ u ε a x = 0 := hdiff
  have heq : endToEnd W h η φ y θ u ε a x = endToEnd W h η φ y' θ u ε a x :=
    sub_eq_zero.mp hzero
  refine ⟨heq, ?_⟩
  rw [mul_zero, heq, dist_self]

/-! ===========================================================================
    §6  具体 `ℝ` 世界模型（原文件 §6，**修好错误 1、2**）
    =========================================================================== -/

/-- 具体状态空间：`Carrier = ℝ`，离散可测。 -/
def rX : StateSpace where
  Carrier := ℝ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 具体参数空间：`Carrier = ℝ`。 -/
def rΘ : ThetaSpace where
  Carrier := ℝ
  topo := ⊤
  meas := ⊤

/-- 具体输入空间：单点。 -/
def rU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 具体动作空间：单点。 -/
def rAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 具体噪声空间：单点。 -/
def rN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 具体上下文空间：单点。 -/
def rC : CtxSpace where
  Carrier := PUnit

/-- 具体四元框架。 -/
def rFrame : Frame where
  Θ := rΘ
  X := rX
  U := rU
  Act := rAct
  Ν := rN

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- 规则：点质量 `δ_x`。 -/
def rRule : Rule rC rX rX where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 规则集 `{R}`。 -/
def rRules : Rules rC rX rX := {rRule}

theorem rRules_nonempty : rRules.Nonempty := ⟨rRule, Set.mem_singleton rRule⟩

/-- 规则集块。 -/
def rWorldRules : WorldRules rC rX rX where
  rules := rRules
  nonempty := rRules_nonempty

/-- 模拟器机制：**恒等**（`predFrom` 恒等于出发点 `x`）。 -/
def rStep : Step rFrame := fun x _u _ε _θ _a => x

/-- 模拟器块。 -/
def rSimulator : WorldSimulator rFrame where
  step := rStep
  horizon := 1

/-- 选择器（恒定返回 `rRule`）。 -/
def rSelector : Selector rC rX rX where
  select := fun _R _c _x => (rRule, 0)
  criterion := fun _c _x _R => 0

theorem rSelector_isValid : rSelector.IsValid rRules := by
  intro c x
  exact Set.mem_singleton rRule

/-- **具体 `ℝ` 世界模型**（`f = id`，`x₀ = 0`，`θ₀ = 0`）。 -/
def rWorldModel : WorldModel where
  frame := rFrame
  ctx := rC
  instX := ⊤
  state := { space := rX, cur := (0 : ℝ), initial := { val := (0 : ℝ), isRandom := false } }
  rules := rWorldRules
  simulator := rSimulator
  selector := rSelector
  state_consistent := rfl

theorem rWorldModel_wellFormed : rWorldModel.WellFormed := rSelector_isValid

/-! ### §6.1 **注册 `rWorldModel` 投影路径上的范数实例** -/

instance instRwX : SeminormedRing rWorldModel.frame.X.Carrier :=
  inferInstanceAs (SeminormedRing ℝ)
instance instRwΘ : SeminormedRing rWorldModel.frame.Θ.Carrier :=
  inferInstanceAs (SeminormedRing ℝ)

/-! ### §6.2 `predFrom` 在 `rWorldModel` 上恒为出发点（**手算**） -/

/-- **`rWorldModel` 的预测块是恒等**：`predFrom rWorldModel θ u ε a x = x`。 -/
theorem rWorldModel_predFrom (θ : rWorldModel.frame.Θ.Carrier)
    (u : rWorldModel.frame.U.Carrier) (ε : rWorldModel.frame.Ν.Carrier)
    (a : rWorldModel.frame.Act.Carrier) (x : rWorldModel.frame.X.Carrier) :
    predFrom rWorldModel θ u ε a x = x := rfl

/-- 具体的观测映射 `h = id`。 -/
abbrev rId : rWorldModel.frame.X.Carrier → rWorldModel.frame.X.Carrier := id

/-- **具体的 `φ : X →+ Θ`（即 `id`，因 `X.Carrier = Θ.Carrier = ℝ`）**。 -/
def rPhi : rWorldModel.frame.X.Carrier →+ rWorldModel.frame.Θ.Carrier :=
  AddMonoidHom.id _

/-- 具体输入空间的唯一元素（`PUnit.unit`，避免 `()` 的 elaboration 歧义）。 -/
def rU0 : rWorldModel.frame.U.Carrier := PUnit.unit
/-- 具体噪声空间的唯一元素。 -/
def rN0 : rWorldModel.frame.Ν.Carrier := PUnit.unit
/-- 具体动作空间的唯一元素。 -/
def rA0 : rWorldModel.frame.Act.Carrier := PUnit.unit

/-- **`observe id` 在 `rWorldModel` 上是恒等**。 -/
theorem rWorldModel_observe (y : rWorldModel.frame.X.Carrier) :
    observe rId y = y := by
  have h := observe_apply_of (X := rWorldModel.frame.X.Carrier)
    (Y := rWorldModel.frame.X.Carrier) (h := (id : rWorldModel.frame.X.Carrier →
      rWorldModel.frame.X.Carrier)) Function.injective_id y
  simpa [rId] using h

/-- **【修好错误 1】**：`rWorldModel` 上 `endToEnd` 的手算形式
`θ' = θ + η * (y - x)`。

**⚠ 修复说明**：原文件把 `η : rWorldModel.frame.X.Carrier`（≡ `ℝ`）写成参数，
但 `endToEnd` 的第二个显式参数要求 `η : W.frame.Θ.Carrier`。
`X.Carrier` 与 `Θ.Carrier` 在 `rWorldModel` 里**都**归约到 `ℝ`，但它们经
**不同的投影路径**出现，Lean 的 `implicit` 透明度**不**把两者视为同一表达式，
于是报 `Application type mismatch: η has type X.Carrier but expected Θ.Carrier`。

**修法**：把 `η` 的**声明类型**改成 `Θ.Carrier`（`θ` 亦然，因为 `endToEnd`
的 `θ` 参数本就是 `Θ.Carrier`）。这样函数体里一切加法/乘法都在
`Θ.Carrier` / `X.Carrier` 各自的 `SeminormedRing` 上。

**⚠ 附加处理**：为让 `η * φ (…)` 的 `HMul` 落在 `Θ` 上（而非 `Θ × X`），
把 `φ` 显式取为 `rPhi : X →+ Θ`（即 `id`，因 `X.Carrier = Θ.Carrier = ℝ`），
于是 `η * rPhi (y - x) : Θ`，`HMul Θ Θ` 由 `SeminormedRing Θ` 提供。 -/
theorem rWorldModel_endToEnd_apply
    (η : rWorldModel.frame.Θ.Carrier) (θ : rWorldModel.frame.Θ.Carrier)
    (y : rWorldModel.frame.X.Carrier) (x : rWorldModel.frame.X.Carrier) :
    endToEnd rWorldModel rId η rPhi y θ
        rU0 rN0 rA0 x = θ + η * rPhi (y - x) := by
  rw [endToEnd_apply, rWorldModel_observe, rWorldModel_predFrom]

/-! ### §6.3 界的取等（紧性 2：常数不可改进） -/

/-- `φ = id : ℝ →+ ℝ` 的 `PhiBound 1`。 -/
theorem id_phiBound_one : PhiBound (AddMonoidHom.id ℝ) 1 := by
  intro z
  rw [AddMonoidHom.id_apply, one_mul]

/-- **【修好错误 2：紧性 2，界恰好取等】**。

在 `rWorldModel` 上取 `η = 1`、`φ = id`、`C = 1`、`x = 0`、`y = 1`、`y' = 0`、`θ = 0`：
实际参数差 `= ‖1·(1-0) - 0‖ = 1`，上界 `= 1·1·1 = 1`，**取等**。

**⚠ 修复说明（BB5 的唯一一处 error）**：`rw` + `dist_eq_norm` 之后剩下的目标里
含有 `rPhi (1 - 0)` / `rPhi (0 - 0)`，其中 `rPhi : X.Carrier →+ Θ.Carrier` 是
`AddMonoidHom.id`。虽然 `X.Carrier` 与 `Θ.Carrier` **都**是 `ℝ`，但它们经不同投影
路径出现，`rPhi x` 与 `x` **不**在 `implicit` 透明度下定义等价，故 `simp only
[AddMonoidHom.id_apply]` **不**触发（linter 报 unused simp arg）。
`norm_num` 也因此卡在 `⊢ ‖rPhi 1 - rPhi 0‖ = ‖1‖ * ‖1‖`。

**修法**：先证局部桥接 `hphi : rPhi x = (x : Θ.Carrier)`（`rfl` 可证），
`rw [hphi, hphi]` 把两处 `rPhi` 消掉，再 `change` 到纯 `ℝ` 的显式形状，
最后由 `norm_num` 闭合。**零 `sorry`、零新增 `axiom`**。 -/
theorem rWorldModel_bound_attained :
    dist (endToEnd rWorldModel rId (1 : rWorldModel.frame.Θ.Carrier)
            rPhi
            (1 : rWorldModel.frame.X.Carrier) (0 : rWorldModel.frame.Θ.Carrier)
            rU0 rN0 rA0 (0 : rWorldModel.frame.X.Carrier))
         (endToEnd rWorldModel rId (1 : rWorldModel.frame.Θ.Carrier)
            rPhi
            (0 : rWorldModel.frame.X.Carrier) (0 : rWorldModel.frame.Θ.Carrier)
            rU0 rN0 rA0 (0 : rWorldModel.frame.X.Carrier))
      = ‖(1 : rWorldModel.frame.Θ.Carrier)‖ * 1
        * ‖observe rId (1 : rWorldModel.frame.X.Carrier)
            - observe rId (0 : rWorldModel.frame.X.Carrier)‖ := by
  rw [rWorldModel_endToEnd_apply, rWorldModel_endToEnd_apply,
    rWorldModel_observe, rWorldModel_observe, dist_eq_norm]
  have hphi : ∀ x : rWorldModel.frame.X.Carrier,
      rPhi x = (show rWorldModel.frame.Θ.Carrier from x) := fun x => rfl
  rw [hphi, hphi]
  change ‖((0 : ℝ) + 1 * ((1 : ℝ) - 0) - (0 + 1 * ((0 : ℝ) - 0)))‖
      = ‖(1 : ℝ)‖ * 1 * ‖((1 : ℝ) - 0)‖
  norm_num

/-- **【界的不可改进性，显式下界】**。 -/
theorem rWorldModel_bound_not_improvable (c : ℝ) (hc : c < 1) :
    ¬ (dist (endToEnd rWorldModel rId (1 : rWorldModel.frame.Θ.Carrier)
              rPhi
              (1 : rWorldModel.frame.X.Carrier) (0 : rWorldModel.frame.Θ.Carrier)
              rU0 rN0 rA0 (0 : rWorldModel.frame.X.Carrier))
           (endToEnd rWorldModel rId (1 : rWorldModel.frame.Θ.Carrier)
              rPhi
              (0 : rWorldModel.frame.X.Carrier) (0 : rWorldModel.frame.Θ.Carrier)
              rU0 rN0 rA0 (0 : rWorldModel.frame.X.Carrier))
          ≤ c * (‖(1 : rWorldModel.frame.Θ.Carrier)‖ * 1
              * ‖observe rId (1 : rWorldModel.frame.X.Carrier)
                  - observe rId (0 : rWorldModel.frame.X.Carrier)‖)) := by
  have hat := rWorldModel_bound_attained
  have hval : ‖observe rId (1 : rWorldModel.frame.X.Carrier)
      - observe rId (0 : rWorldModel.frame.X.Carrier)‖ = 1 := by
    rw [rWorldModel_observe, rWorldModel_observe]
    change ‖(1 : ℝ) - 0‖ = 1
    norm_num
  rw [hat, hval]
  intro hle
  have h2 : ‖(1 : rWorldModel.frame.Θ.Carrier)‖ * 1 * 1 = 1 := by
    change ‖(1 : ℝ)‖ * 1 * 1 = 1
    norm_num
  rw [h2] at hle
  linarith

/-! ===========================================================================
    §7  `ε`-`δ` 连续形式（原文件 §7，逐字保留）
    =========================================================================== -/

/-- **【主界，`ε`-`δ` 形式】**。 -/
theorem endToEnd_eps_delta_form
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (C : ℝ) (hC : 0 ≤ C) (hφ : PhiBound φ C)
    (y y' : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (εtol : ℝ)
    (hδ : ‖η‖ * C * ‖observe h y - observe h y'‖ < εtol) :
    dist (endToEnd W h η φ y θ u ε a x) (endToEnd W h η φ y' θ u ε a x) < εtol :=
  lt_of_le_of_lt (endToEnd_perturbation_bound W h η φ C hC hφ y y' θ u ε a x) hδ

/-! ===========================================================================
    §8  「带 `hfix`」的收敛版本 —— **可证，但是 `endToEnd_fixed` 的重述**

    任务书猜测「`θ₀ = θ*` 时应两行可证」。**这在附加 `hfix` 前提后成立**：
    若 `θ*` 是**一步不动点**，则 `endToEndIter_fixed` 给出所有 `k` 都等于 `θ*`，
    故 `dist = 0 < εtol`。

    **⚠ 这是「不动」而非「收敛」**：迭代**从未移动**。它**不是**
    「从任意 `θ₀` 逼近 `θ*`」，而是「若已命中 `θ*` 则永远停在 `θ*`」。
    这正是 `endToEnd_fixed`（一步不动）+ `endToEndIter_fixed`（多步不动）的
    **直接重述**，**不含**任何收敛性内容。**本定理证明的就是这个平凡事实。**
    =========================================================================== -/

/-- **【带不动点前提的「收敛」——实为「不动」】**

若 `endToEnd W h η φ (h x) θ* u ε a x = θ*`（`θ*` 是 `(h x)` 赋值下的一步不动点），
则 `∀ εtol > 0, ∃ N, ∀ k ≥ N, dist (endToEndIter … k θ*) θ* < εtol`。

**⚠ 平凡性确认（任务书 (c)）**：这就是 `endToEnd_fixed` 的重述 ——
`endToEndIter_fixed` 逐字用 `endToEnd_fixed` 的 `hfix` 做归纳，
得到 `endToEndIter … k θ* = θ*`，于是 `dist = 0`。**没有移动，故无「逼近」。** -/
theorem gap_of_fixed
    (h : W.frame.X.Carrier → W.frame.X.Carrier) (η : W.frame.Θ.Carrier)
    (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hfix : endToEnd W h η φ (h x) θstar u ε a x = θstar) :
    ∀ εtol : ℝ, 0 < εtol → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      dist (endToEndIter W h η φ (h x) u ε a x k θstar) θstar < εtol := by
  intro εtol hε
  exact ⟨0, fun k _ => by
    rw [endToEndIter_fixed W h η φ (h x) u ε a x θstar hfix k, dist_self]
    exact hε⟩

/-- **「带 `hfix`」命题与原 `Prop` 的关系**：前者 ⟹ 后者**在「对每个实例都取到
`hfix`」的意义下不成立**，故本定理只断言「`hfix` 版本可证」。

本定理**显式**说明 `gap_of_fixed` 依赖 `hfix`；**不**声称 `hfix` 可被去掉。 -/
theorem hfix_essential_statement :
    (∀ (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
      [SeminormedRing W.frame.Θ.Carrier]
      (h : W.frame.X.Carrier → W.frame.X.Carrier) (η : W.frame.Θ.Carrier)
      (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
      (θstar : W.frame.Θ.Carrier)
      (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
      (x : W.frame.X.Carrier),
      endToEnd W h η φ (h x) θstar u ε a x = θstar →
      ∀ εtol : ℝ, 0 < εtol → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        dist (endToEndIter W h η φ (h x) u ε a x k θstar) θstar < εtol) := by
  intro W _ _ h η φ θstar u ε a x hfix εtol hε
  exact gap_of_fixed W h η φ θstar u ε a x hfix εtol hε

/-! ===========================================================================
    §9  **`dist_to_optimum_Gap` 的**反证**：该 `Prop` **假**（`gap_is_false`）

    本节兑现文件头 (b)/(c) 的承诺：原 `FateV2.Loop.EndToEndBound.§8` 的
    `dist_to_optimum_Gap`（**无** `hfix` 前提）**不是**「未证的缺口」，
    而是**可被反驳的假命题**。反例 = §6 的 `rFrame` 上把**一步预测取常值 1**：
    于是每步 `θ ↦ θ - 1`，`θ_k = -k`，**发散**。

    **⚠ 这不是「缺口」，是「错题」** —— 与 `gap_of_fixed`（带 `hfix`，平凡真）
    形成对照：`dist_to_optimum_Gap` 少了 `hfix`，就**变成假**。
    =========================================================================== -/

/-- 反例模型：与 `rWorldModel` 同框架，但**一步预测恒为 `1`**（`f ≡ 1`）。 -/
def dModel : WorldModel where
  frame := rFrame
  ctx := rC
  instX := ⊤
  state := { space := rX, cur := (0 : ℝ), initial := { val := (0 : ℝ), isRandom := false } }
  rules := rWorldRules
  simulator := { step := fun _x _u _ε _θ _a => (1 : ℝ), horizon := 1 }
  selector := rSelector
  state_consistent := rfl

instance instDmX : SeminormedRing dModel.frame.X.Carrier :=
  inferInstanceAs (SeminormedRing ℝ)
instance instDmΘ : SeminormedRing dModel.frame.Θ.Carrier :=
  inferInstanceAs (SeminormedRing ℝ)

/-- 反例模型的输入空间唯一元素。 -/
def dU0 : dModel.frame.U.Carrier := PUnit.unit
/-- 反例模型的噪声空间唯一元素。 -/
def dN0 : dModel.frame.Ν.Carrier := PUnit.unit
/-- 反例模型的动作空间唯一元素。 -/
def dA0 : dModel.frame.Act.Carrier := PUnit.unit

/-- 反例模型的观测映射 `h = id`。 -/
abbrev dId : dModel.frame.X.Carrier → dModel.frame.X.Carrier := id

/-- 反例模型的 `φ : X →+ Θ`（即 `id`）。 -/
def dPhi : dModel.frame.X.Carrier →+ dModel.frame.Θ.Carrier :=
  AddMonoidHom.id _

/-- **反例模型的预测块恒为 `1`**（`≠ x`，故 `θ` 每步都在动）。 -/
theorem dModel_predFrom (θ : dModel.frame.Θ.Carrier)
    (u : dModel.frame.U.Carrier) (ε : dModel.frame.Ν.Carrier)
    (a : dModel.frame.Act.Carrier) (x : dModel.frame.X.Carrier) :
    predFrom dModel θ u ε a x = 1 := rfl

/-- **反例模型上 `observe id` 是恒等**。 -/
theorem dModel_observe (y : dModel.frame.X.Carrier) : observe dId y = y := by
  have h := observe_apply_of (X := dModel.frame.X.Carrier)
    (Y := dModel.frame.X.Carrier) (h := (id : dModel.frame.X.Carrier →
      dModel.frame.X.Carrier)) Function.injective_id y
  simpa [dId] using h

/-- **反例模型上的 `endToEnd` 手算形式**：`θ' = θ - 1`
（`y = 0` ⇒ 观测估计 `0`；预测 `1`；残差 `-1`；`η = 1`、`φ = id`）。 -/
theorem dModel_endToEnd_apply (θ : dModel.frame.Θ.Carrier)
    (x : dModel.frame.X.Carrier) :
    endToEnd dModel dId (1 : dModel.frame.Θ.Carrier) dPhi
        (0 : dModel.frame.X.Carrier) θ dU0 dN0 dA0 x = θ - 1 := by
  rw [endToEnd_apply, dModel_predFrom, dModel_observe]
  have hphi : ∀ z : dModel.frame.X.Carrier,
      dPhi z = (show dModel.frame.Θ.Carrier from z) := fun z => rfl
  rw [hphi]
  change θ + (1 : dModel.frame.Θ.Carrier)
      * ((0 : dModel.frame.Θ.Carrier) - 1) = θ - 1
  rw [one_mul, zero_sub, sub_eq_add_neg]

/-- **反例模型的迭代 = `θ - k`**（沿 `k` **线性发散**）。 -/
theorem dModel_iter (k : ℕ) (θ : dModel.frame.Θ.Carrier)
    (x : dModel.frame.X.Carrier) :
    endToEndIter dModel dId (1 : dModel.frame.Θ.Carrier) dPhi
        (0 : dModel.frame.X.Carrier) dU0 dN0 dA0 x k θ
      = θ - (k : dModel.frame.Θ.Carrier) := by
  induction k generalizing θ with
  | zero =>
    rw [endToEndIter_zero]
    rw [Nat.cast_zero, sub_zero]
  | succ n ih =>
    rw [endToEndIter_succ, ih, dModel_endToEnd_apply]
    rw [Nat.cast_succ, sub_eq_add_neg, sub_eq_add_neg]
    abel

/-! ### §9.2 `dist_to_optimum_Gap` 的逐字副本与**其否定** -/

/-- **`dist_to_optimum_Gap` 的**逐字副本**（原 `FateV2.Loop.EndToEndBound.§8` 的定义）。

**⚠ 为什么在本文件重述**：`FateV2.Loop/EndToEndBound.lean` **本身编译失败**
（即本文件所修的 `⊢ ‖rPhi 1 - rPhi 0‖ = ‖1‖ * ‖1‖` 那处，实测
`lake build FateV2.Loop.EndToEndBound` 失败、无 `.olean`），故**不能** `import` 它。
为不依赖坏模块，本文件**逐字复制**该 `def` 的类型。

**内容与原文完全一致**（无 `hfix`、无单射假设、无 `φ` 有界假设）。 -/
def dist_to_optimum_Gap : Prop :=
  ∀ (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
    [SeminormedRing W.frame.Θ.Carrier]
    (h : W.frame.X.Carrier → W.frame.X.Carrier) (η : W.frame.Θ.Carrier)
    (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier),
    ∀ εtol : ℝ, 0 < εtol → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      dist (endToEndIter W h η φ (h x) u ε a x k θstar) θstar < εtol

/-- **【主结论】`dist_to_optimum_Gap`（与原文件一致、无 `hfix` 的版本）为假。**

反例（§9.1 的 `dModel`）：一步预测恒为 `1`，取 `θ* = 0`、`η = 1`、`φ = id`、
`y = 0`、`x = 0`、`h = id`，则由 `dModel_iter` 得 `θ_k = -k`，故
`dist θ_k θ* = k → ∞`；取 `εtol = 1` 与 `k = N + 1` 即得矛盾。

**⟹ 该 `Prop` **不是**「未证的缺口」，而是**错题**：
去掉 `hfix` 后它**假**（对照 §8 `gap_of_fixed`：加上 `hfix` 后平凡真）。 -/
theorem gap_is_false : ¬ dist_to_optimum_Gap := by
  intro hgap
  obtain ⟨N, hN⟩ :=
    hgap (W := dModel) (h := dId) (η := (1 : dModel.frame.Θ.Carrier))
      (φ := dPhi) (θstar := (0 : dModel.frame.Θ.Carrier))
      (u := dU0) (ε := dN0) (a := dA0)
      (x := (0 : dModel.frame.X.Carrier)) 1 (by norm_num)
  have h := hN (N + 1) (Nat.le_succ N)
  have key : endToEndIter dModel dId (1 : dModel.frame.Θ.Carrier) dPhi
      (dId (0 : dModel.frame.X.Carrier)) dU0 dN0 dA0 (0 : dModel.frame.X.Carrier)
      (N + 1) (0 : dModel.frame.Θ.Carrier) = 0 - ((N + 1 : ℕ) : dModel.frame.Θ.Carrier) :=
    dModel_iter (N + 1) 0 (dId (0 : dModel.frame.X.Carrier))
  rw [key] at h
  have hval : dist
        ((0 : dModel.frame.Θ.Carrier) - ((N + 1 : ℕ) : dModel.frame.Θ.Carrier))
        (0 : dModel.frame.Θ.Carrier) = ((N : ℝ) + 1) := by
    rw [dist_eq_norm, Nat.cast_succ, zero_sub, sub_zero, norm_neg]
    change ‖(((N : ℝ)) + 1)‖ = ((N : ℝ) + 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hval] at h
  have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  linarith

end

end EndToEndBoundFixed
end FateV2.Loop
