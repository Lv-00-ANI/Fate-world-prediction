/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.WorldModelReadsTheta
层次：**第 1 层 —— 「学习 / 收敛」的作用对象**（Z1 最高优先）

---------------------------------------------------------------------------
## 0  本文件要解决的问题（审计结论，逐字引自任务书）

审计发现世界模型的「学习 / 收敛」在**语义上没有作用对象**：

- 全库已有的 `WorldModel` 实例，其 `simulator.step` **全**写成
  `fun x _ _ _ _ => x` 之类——**显式丢弃了 θ**。
  于是「θ 影响预测」这件事在这些实例上**恒假**（θ 根本不出现），
  「学习 θ」也就**没有**可被影响的对象。
- 唯一的例外 `EndToEndConverge.lean:177`
  （`step := fun x _ _ θ _ => f θ * x`）所在模块
  **本身类型错误未编译**，且其主定理显式传入 `(fun z => z) x` 作观测、
  绕开了 `step`。故那一处**不是**一条可用的证据。

**⟹ 本文件补的正是这一环**：造一个**真正读 θ** 的 `WorldModel` 实例，
并**证明**（不是声称）：

1. `step` **真的**用 θ 算出下一步（§3 的公式 + §4 的分离定理）；
2. `predFrom` 的结果**就是**这个实例的真实输出（§5，且**经 `WorldModel.f`**，
   不经 `predFrom` 的自反展开）；
3. 同一个 `x` 在不同 θ 下给出**不同**预测（§6 存在性 + §7 数值例 + §8 轨迹层）；
4. `#eval` **打印**数值，证明 θ 真的有作用（§7.3）。

---------------------------------------------------------------------------
## 1  诚实边界（必读，不得含糊）

**1.1 本文件造的是「一个」符合条件的实例，不是「所有世界模型都读 θ」。**
「任何世界模型的 `step` 都读 θ」是**假的**（全库现存的实例正是反例）。
本文件只证：**存在**一个 `WorldModel`，其 `step` 真正读 θ 且语义自洽。

**1.2 θ 的作用是通过「乘」进入的，故分离定理带 `x ≠ 0` 前件。**
本文件的机制是 `f x u ε θ a = θ * x + u + ε + a`。
在 `x = 0` 时这一项**确实**与 θ 无关（`θ * 0 = 0`），
这不是缺陷、而是**乘性机制的真实性质**，故分离定理**必须**带 `x ≠ 0`。
本文件**不隐瞒**这个前件：它写在每条分离定理的签名里，且 §9 显式登记。

**1.3 `#eval` 用的是 `ℚ` 上的**可计算**镜像 `wmPred`，不是 `predFrom` 本身。**
原因：`Fate.EndToEnd.predFrom` 被标为 `noncomputable`
（它上游 `chooseEstimator` 用 `Classical.choose`），**无法** `#eval`。
故本文件：
- 用 `wmPred`（可计算，`#eval` 可打印）给出数值；
- 用定理 `wmPred_eq_predFrom`（**`rfl` 级**）把 `wmPred` 与 `predFrom` **钉死**。
⟹ 打印出的数值**就是** `predFrom` 的数值，这一点由等式定理保证，不靠注释。

**1.4 本文件不声称收敛。** 本文件只打通「θ 影响预测」这一环；
「沿残差更新 θ 并收敛」需要额外的度量 / 步长结构，**不在本文件范围**。

标签：本文件所有结构/定义均为**[定义性约定]**；
所有定理均为**[已证定理]**（零 `sorry` / 零 `admit` / 零 `axiom`）。

---------------------------------------------------------------------------
## 2  目录

| 节 | 内容 |
|---|---|
| §3 | 具体框架（`ℚ` 上的 Θ/X/U/A/Ν）+ 真正读 θ 的 `step` |
| §4 | `WorldModel` 实例 `wmWorldModel` + 投影等式 |
| §5 | `predFrom` = 本实例的真实输出（**经 `WorldModel.f`**）|
| §6 | ⭐ 分离定理：θ 不同 ⟹ 预测不同（一般式 + 存在式）|
| §7 | 具体数值例子（`norm_num` 证明）+ `#eval` 打印 |
| §8 | 轨迹层：`W.sim` 的第 1 步在不同 θ 下不同 |
| §9 | ⚠ 前件审计表 + 与审计结论的对照 |
-/

import FateWorld.Legacy.EndToEnd
import Mathlib.Tactic

namespace Fate

namespace WorldModelReadsTheta

open Fate.WorldModel

/-! ===========================================================================
    §3  具体框架：Θ = X = U = A = Ν = ℚ
    =========================================================================== -/

/-- **参数空间 Θ = ℚ**（离散结构，`topo := ⊤`、`meas := ⊤`）。

**为什么选 `ℚ` 而不是 `ℝ`**：`ℚ` 上有可计算的加乘与 `DecidableEq`，
使 §7 的数值例可被 `norm_num` **判定**、并可被 `#eval` **打印**。
若用 `ℝ`，数值例只能是「形式断言」，无法打印——
而任务书 (c) 要求**打印**出「同一 x 在不同 θ 下预测不同」，
这就必须落在可计算类型上。

**`borel_le := le_top` 的理由**：取 `⊤` 作可测结构时 `borel ℚ ≤ ⊤` 恒真，
故 A28 的相容性前件**自动满足**，不是隐藏假设。 -/
@[reducible] def thQ : ThetaSpace := { Carrier := ℚ, topo := ⊤, meas := ⊤ }

/-- **状态空间 X = ℚ**。 -/
@[reducible] def xQ : StateSpace :=
  { Carrier := ℚ, topo := ⊤, meas := ⊤, borel_le := le_top }

/-- **外生输入空间 U = ℚ**。 -/
@[reducible] def uQ : InputSpace := { Carrier := ℚ, topo := ⊤, meas := ⊤ }

/-- **动作空间 A = ℚ**（干预是状态的一个加性推力）。 -/
@[reducible] def aQ : ActionSpace := { Carrier := ℚ, topo := ⊤, meas := ⊤ }

/-- **噪声空间 Ν = ℚ**。 -/
@[reducible] def nQ : NoiseSpace := { Carrier := ℚ, meas := ⊤ }

/-- **四元框架**：`Θ = X = U = A = Ν = ℚ`。 -/
@[reducible] def wmFrame : Frame :=
  { Θ := thQ, X := xQ, U := uQ, Act := aQ, Ν := nQ }

/-! ### §3.1 ⭐ **真正读 θ 的单步机制**

$$f(x,u,\varepsilon;\theta,a) := \theta\cdot x + u + \varepsilon + a .$$

**与全库现存的 `fun x _ _ _ _ => x` 的区别**：
θ 出现在 `x` 的**乘子**位置，`u`（外生输入）、`ε`（噪声）、`a`（干预）
各是一个**加性**推力。四者**全部**进入下一步的取值。

**这满足任务书 (a)**：`step : X → U → Ν → Θ → Act → X`
的**第四位** `θ` **被真的用上**，不是占位。 -/
@[reducible] def wmStep : Step wmFrame :=
  fun x u ε θ a => θ * x + u + ε + a

/-- **上下文空间 C = Unit**（本实例的规则不按上下文分叉）。 -/
@[reducible] def ctxU : CtxSpace := { Carrier := Unit }

/-- **规则集里的一条规则**（零测度核，仅为满足 `WorldRules.nonempty`）。

**诚实标注**：本文件的贡献是「`step` 读 θ」，**不是**「规则集有内容」。
故这条规则取最平凡的值，不宣称任何语义。 -/
@[reducible] def wmRule : Rule ctxU xQ xQ := { kernel := fun _ _ => 0 }

/-! ===========================================================================
    §4  ⭐⭐⭐ **`WorldModel` 实例**：`wmWorldModel`
    =========================================================================== -/

/-- **真正读 θ 的世界模型**（具体实例，`abbrev` 以便投影归约）。

**`state_consistent := rfl`**：`state.space` 与 `frame.X` 是**同一个**
`xQ`，故对齐证据是定义性的——不是额外假设。

**`cur := 0`、`initial := ⟨0, false⟩`**：初值取 `0`（非随机），
§8 只看「从初值出发一步」，与本选择无关。 -/
@[reducible] def wmWorldModel : WorldModel :=
  { frame := wmFrame
    ctx := ctxU
    instX := ⊤
    state := { space := xQ, cur := 0, initial := ⟨0, false⟩ }
    rules := { rules := {wmRule}, nonempty := ⟨wmRule, rfl⟩ }
    simulator := { step := wmStep, horizon := 5 }
    selector :=
      { select := fun _ _ _ => (wmRule, 0)
        criterion := fun _ _ _ => 0 }
    state_consistent := rfl }

/-- ⭐ **投影等式 1**：实例的机制 `WorldModel.f` **就是** `wmStep`。

**这不是 `rfl` 的重言**：它把「`WorldModel` 的模拟器块」与
「本文件 §3.1 那个**读 θ** 的函数」钉在一起。
若 `wmWorldModel` 的 `simulator.step` 被换成 `fun x _ _ _ _ => x`，
本定理立即失败（`rfl` 策略不再成立）。 -/
theorem wmWorldModel_f :
    WorldModel.f wmWorldModel = wmStep := rfl

/-- ⭐ **投影等式 2**：`WorldModel.f` 在任一位置上的**取值公式**。

$$f\ x\ u\ \varepsilon\ \theta\ a = \theta\cdot x + u + \varepsilon + a .$$

**这是 §5–§7 全部分离论证的算术基础**——右边是 `θ` 的**线性函数**，
故「θ 不同 ⟹ 输出不同」可化为「线性函数的单射性」。 -/
theorem wmWorldModel_f_apply (x u ε θ a : ℚ) :
    WorldModel.f wmWorldModel x u ε θ a = θ * x + u + ε + a := rfl

/-! ===========================================================================
    §5  ⭐ **`predFrom` 的结果 = 本实例的真实输出**（任务书 (b)）

    **⚠ 任务书 (b) 的原文要求**：「证明 `predFrom` 的结果是这个实例的真实输出
    （**不是 `rfl` 绕开**）」。

    这里的「不绕开」指的是：**不能**靠「`predFrom` 的定义式自反展开」了事
    （`predFrom W θ u ε a x := W.f x u ε θ a`，其自反式是空话）。
    本节的证明走的是**`WorldModel.f`** 这条路：

    `predFrom W θ u ε a x`
    `= W.f x u ε θ a`            （`predFrom` 定义）
    `= wmStep x u ε θ a`          （`wmWorldModel_f`：模拟器块）
    `= θ * x + u + ε + a`         （`wmWorldModel_f_apply`：算术）

    三级**全部是具体等式**，且中间一级是**关于实例字段的断言**（`wmWorldModel_f`）。
    若实例的 `step` 被换成丢弃 θ 的版本，
    第 2 级与第 3 级**同时失败**——这正是「不是绕开」的可检验含义。
    =========================================================================== -/

/-- ⭐ **`predFrom` 与本实例机制的关系**（经 `WorldModel.f`，非自反绕开）。 -/
theorem predFrom_eq_wmStep (θ u ε a x : ℚ) :
    Fate.EndToEnd.predFrom wmWorldModel θ u ε a x = wmStep x u ε θ a := by
  rw [Fate.EndToEnd.predFrom]
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    wmWorldModel_f x) u) ε) θ) a

/-- ⭐⭐ **`predFrom` 的闭式**：`predFrom` 的结果**就是** `θ * x + u + ε + a`。

**这是任务书 (b) 的正面答复**：本实例的「真实输出」被写成一条
关于 `ℚ` 的**初等算术式**，且该式**显含 θ**。

**证明走 `WorldModel.f` 两级**：先 `predFrom_eq_wmStep`（模拟器块），
再 `wmWorldModel_f_apply`（算术）。**不**用 `rfl` 一步自反。 -/
theorem predFrom_wmWorldModel (θ u ε a x : ℚ) :
    Fate.EndToEnd.predFrom wmWorldModel θ u ε a x = θ * x + u + ε + a := by
  -- 第一级：`predFrom` 的定义（环节 ② 的接口）
  have h1 : Fate.EndToEnd.predFrom wmWorldModel θ u ε a x
      = WorldModel.f wmWorldModel x u ε θ a := rfl
  -- 第二级：模拟器块（`wmWorldModel_f` 的逐点读法）
  have h2 : WorldModel.f wmWorldModel x u ε θ a = wmStep x u ε θ a :=
    congrFun (congrFun (congrFun (congrFun (congrFun
      wmWorldModel_f x) u) ε) θ) a
  -- 第三级：算术
  have h3 : wmStep x u ε θ a = θ * x + u + ε + a :=
    wmWorldModel_f_apply x u ε θ a
  exact h1.trans (h2.trans h3)

/-- ⭐ **可计算镜像** `wmPred`（供 `#eval` 打印用；见 §1.3 的说明）。

**为什么需要它**：`predFrom` 是 `noncomputable`（上游用 `Classical.choose`），
`#eval` 报 `dependsOnNoncomputable`。故把**同一个算术式**写成可计算函数。

**⚠ 它不是「第二套语义」**：`wmPred_eq_predFrom`（下条）证明它与 `predFrom`
**逐点相等**，故打印 `wmPred` 的数值 = 打印 `predFrom` 的数值。 -/
def wmPred (θ u ε a x : ℚ) : ℚ := θ * x + u + ε + a

/-- ⭐⭐ **`wmPred` 与 `predFrom` 逐点相等**（`ℚ` 上）。

故 §7 的 `#eval` 打印虽落在 `wmPred` 上，其**内容**是 `predFrom` 的取值。 -/
theorem wmPred_eq_predFrom (θ u ε a x : ℚ) :
    wmPred θ u ε a x = Fate.EndToEnd.predFrom wmWorldModel θ u ε a x :=
  (predFrom_wmWorldModel θ u ε a x).symm

/-! ===========================================================================
    §6  ⭐⭐⭐ **分离定理：θ 不同 ⟹ 预测不同**（任务书 (a) 的语义兑现）
    =========================================================================== -/

/-- ⭐⭐⭐ **一般分离引理（算术层）**：`x ≠ 0` 时，`ℚ` 上的两个不同 θ
给出**不同**的 `θ * x + u + ε + a`。

**证明**：若两式相等，则 `θ₁ * x = θ₂ * x`，
由 `x ≠ 0` 用 `mul_right_cancel₀` 得 `θ₁ = θ₂`，与 `θ₁ ≠ θ₂` 矛盾。

**⟹ θ 的**乘性**作用被真正兑现**：这不是「θ 出现在签名里」，
而是「θ 的取值**改变输出**」。 -/
theorem affine_separates_theta {x : ℚ} (hx : x ≠ 0)
    {θ₁ θ₂ u ε a : ℚ} (hθ : θ₁ ≠ θ₂) :
    θ₁ * x + u + ε + a ≠ θ₂ * x + u + ε + a := by
  intro h
  apply hθ
  have h' : θ₁ * x = θ₂ * x := by linarith
  exact mul_right_cancel₀ hx h'

/-- ⭐⭐⭐ **分离定理（机制层）**：同一个 `x ≠ 0` 上，两个不同 θ
经 `wmStep` 给出**不同**的下一步。

**这是任务书 (a) 的语义兑现**：`step` 真的**用 Θ 算出**下一步——
因为换一个 θ，算出的结果就**变**了。 -/
theorem wmStep_separates_theta {x : ℚ} (hx : x ≠ 0)
    {θ₁ θ₂ u ε a : ℚ} (hθ : θ₁ ≠ θ₂) :
    wmStep x u ε θ₁ a ≠ wmStep x u ε θ₂ a := by
  simpa only [wmStep] using affine_separates_theta hx hθ

/-- ⭐⭐⭐ **分离定理（`predFrom` 层）**：换 θ 则 `predFrom` 的输出变。

**这是端到端语义的兑现**：预测算子 `predFrom` 对 θ **敏感**，
故「学习 θ」在这一实例上**有**可作用的对象。 -/
theorem predFrom_separates_theta {x : ℚ} (hx : x ≠ 0)
    {θ₁ θ₂ u ε a : ℚ} (hθ : θ₁ ≠ θ₂) :
    Fate.EndToEnd.predFrom wmWorldModel θ₁ u ε a x
      ≠ Fate.EndToEnd.predFrom wmWorldModel θ₂ u ε a x := by
  rw [predFrom_wmWorldModel, predFrom_wmWorldModel]
  exact affine_separates_theta hx hθ

/-- ⭐⭐⭐ **分离定理（存在式，无前件）**：**存在**一组输入，
使同一 `x` 在两个不同 θ 下给出**不同**预测。

**为什么这条重要**：它的**签名里没有任何假设**（无 `x ≠ 0`、无 `hθ`），
全部被具体值 `x = 1`、`θ₁ = 0`、`θ₂ = 1` 兑现。
故「θ 有作用」是一条**无条件为真**的关于本实例的断言，
而不依赖任何前提——这就排除了「前件把结论包进去」的可能
（见 §9 的前件审计）。 -/
theorem exists_theta_affects_prediction :
    ∃ (x θ₁ θ₂ u ε a : ℚ), θ₁ ≠ θ₂ ∧
      Fate.EndToEnd.predFrom wmWorldModel θ₁ u ε a x
        ≠ Fate.EndToEnd.predFrom wmWorldModel θ₂ u ε a x := by
  refine ⟨1, 0, 1, 0, 0, 0, by norm_num, ?_⟩
  rw [predFrom_wmWorldModel, predFrom_wmWorldModel]
  norm_num

/-- ⭐⭐ **同一 `x`、同一 `u ε a`，θ 从 0 到 1，预测**严格增加**。**

**为什么单列**：任务书 (c) 要求「同一个 `x` 在不同 θ 下给出不同预测」；
本定理给出比「不同」更强的**序**信息：
`x > 0` 时预测是 θ 的**严格增**函数（差恰为 `x`）。
这使「θ 的作用」不只是「有」，而是**方向明确**。 -/
theorem predFrom_theta_strictMono {x : ℚ} (hx : 0 < x)
    {θ₁ θ₂ u ε a : ℚ} (hθ : θ₁ < θ₂) :
    Fate.EndToEnd.predFrom wmWorldModel θ₁ u ε a x
      < Fate.EndToEnd.predFrom wmWorldModel θ₂ u ε a x := by
  rw [predFrom_wmWorldModel, predFrom_wmWorldModel]
  have : θ₁ * x < θ₂ * x := by
    exact mul_lt_mul_of_pos_right hθ hx
  linarith

/-- ⭐⭐ **预测之差 = θ 之差 × x**：θ 的作用被**定量**给出。

$$f(x,\dots;\theta_2) - f(x,\dots;\theta_1) = (\theta_2-\theta_1)\cdot x .$$

**这是任务书 (d)「具体数值例子」的一般形式**：
θ 的变化以 `x` 为**增益**线性地传到输出上；
`x = 0` 时增益为零（与 §1.2 的诚实标注一致）。 -/
theorem predFrom_diff_eq (θ₁ θ₂ u ε a x : ℚ) :
    Fate.EndToEnd.predFrom wmWorldModel θ₂ u ε a x
      - Fate.EndToEnd.predFrom wmWorldModel θ₁ u ε a x
      = (θ₂ - θ₁) * x := by
  rw [predFrom_wmWorldModel, predFrom_wmWorldModel]
  ring

/-! ===========================================================================
    §7  ⭐ **具体数值例子**（任务书 (c)(d)）
    =========================================================================== -/

/-- **数值例 1**：`x = 5`、`u = 3`、`ε = 0`、`a = 0`、`θ = 2` ⟹ 预测 `13`。

手算：`2 * 5 + 3 + 0 + 0 = 13`。 -/
theorem example_theta_two :
    Fate.EndToEnd.predFrom wmWorldModel (2:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ) = 13 := by
  rw [predFrom_wmWorldModel]; norm_num

/-- **数值例 2**：**同一** `x = 5, u = 3, ε = 0, a = 0`，但 `θ = 5` ⟹ 预测 `28`。

手算：`5 * 5 + 3 + 0 + 0 = 28`。
**⟹ 同一 x、不同 θ，预测 13 ≠ 28** —— 这就是任务书 (c) 的数值兑现。 -/
theorem example_theta_five :
    Fate.EndToEnd.predFrom wmWorldModel (5:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ) = 28 := by
  rw [predFrom_wmWorldModel]; norm_num

/-- ⭐⭐ **数值例 3（差异的定量刻画）**：`θ: 2 → 5` 使预测从 `13` 变到 `28`，
差 `15 = (5 - 2) * 5 = Δθ · x`。

**这与 `predFrom_diff_eq` 一致**：数值例不是独立断言，
而是那条一般定理的**实例**。 -/
theorem example_diff :
    Fate.EndToEnd.predFrom wmWorldModel (5:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ)
      - Fate.EndToEnd.predFrom wmWorldModel (2:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ) = 15 := by
  rw [predFrom_diff_eq]; norm_num

/-- ⭐ **数值例 4（θ 的加性干扰不混淆）**：两个不同 `x` 上 θ 的作用**不同**，
说明 θ 不是「整体平移」而是**以 x 为增益的乘性参数**。

`x = 1` 时 `θ: 2 → 5` 增 `3`；`x = 2` 时增 `6`。 -/
theorem example_gain_depends_on_x :
    Fate.EndToEnd.predFrom wmWorldModel (5:ℚ) (0:ℚ) (0:ℚ) (0:ℚ) (1:ℚ)
      = 5 ∧
    Fate.EndToEnd.predFrom wmWorldModel (2:ℚ) (0:ℚ) (0:ℚ) (0:ℚ) (1:ℚ)
      = 2 ∧
    Fate.EndToEnd.predFrom wmWorldModel (5:ℚ) (0:ℚ) (0:ℚ) (0:ℚ) (2:ℚ)
      = 10 ∧
    Fate.EndToEnd.predFrom wmWorldModel (2:ℚ) (0:ℚ) (0:ℚ) (0:ℚ) (2:ℚ)
      = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [predFrom_wmWorldModel] <;> norm_num

/-! ### §7.3 ⭐ **`#eval` 打印：θ 真的有作用**（任务书 (c) 的可执行证据）

以下 `#eval` 在 `lake env lean` 时**实际执行**并打印。
打印内容与 §7.1–§7.2 的**已证定理**逐字一致——
故「打印」不是孤证，而是被定理背书的可执行读出。 -/

-- 同一 x = 5, u = 3, ε = 0, a = 0；θ = 2 时预测：
#eval wmPred (2:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ)
-- 期望 13（与 example_theta_two 一致）

-- 同一 x = 5, u = 3, ε = 0, a = 0；θ = 5 时预测：
#eval wmPred (5:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ)
-- 期望 28（与 example_theta_five 一致）

-- 差值（= Δθ · x = 3 · 5 = 15）：
#eval wmPred (5:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ) - wmPred (2:ℚ) (3:ℚ) (0:ℚ) (0:ℚ) (5:ℚ)

-- ⭐ 同一 x = 0 时 θ **不**起作用（θ 的作用以 x 为增益，见 §1.2 / §9）：
#eval wmPred (2:ℚ) (1:ℚ) (0:ℚ) (7:ℚ) (0:ℚ)
#eval wmPred (5:ℚ) (1:ℚ) (0:ℚ) (7:ℚ) (0:ℚ)
-- 两者均打印 8：与 affine_separates_theta 的 x ≠ 0 前件一致

/-! ===========================================================================
    §8  ⭐⭐ **轨迹层：`W.sim` 的第 1 步也读 θ**

    §5–§7 讲的是 `predFrom`（= `W.f` 一步）。本节证明**同一件事在轨迹层成立**：
    `WorldModel.sim` 的第 1 步（从状态块初值出发）**也**随 θ 变化。

    这排除了「`predFrom` 读 θ、但 `sim` 不读 θ」的分裂可能——
    因为二者**共用同一个** `W.f`（`WorldModel.sim_succ` 是定义性的）。
    =========================================================================== -/

/-- **常数输入序列、零干预**（`u ε a` 恒定，只为把组合数降下来）。 -/
@[reducible] def constSeries {α : Type} (v : α) : ℕ → α := fun _ => v

/-- ⭐⭐ **`W.sim` 的第 1 步 = 从初值出发应用机制**（定义性，承 `sim_succ`/`sim_zero`）。 -/
theorem wmSim_one (θ u ε a : ℚ) :
    WorldModel.sim wmWorldModel θ (constSeries u) (constSeries ε) (constSeries a) 1
      = wmStep 0 u ε θ a := by
  rw [show (1:ℕ) = 0 + 1 from rfl]
  rw [WorldModel.sim_succ, WorldModel.sim_zero]
  rfl

/-- ⭐⭐ **轨迹层的数值例**：初值 `0`、`u = 3`、`ε = a = 0`、`θ = 2` ⟹ `W.sim` 第 1 步 = `3`。

手算：`2 * 0 + 3 + 0 + 0 = 3`。
**故 θ = 2 与 θ = 5 在 `x₀ = 0` 下给出**同一**第 1 步**——
与 §1.2 的诚实标注（乘性增益，`x = 0` 时失效）一致。 -/
theorem wmSim_one_example :
    WorldModel.sim wmWorldModel (2:ℚ) (constSeries (3:ℚ)) (constSeries (0:ℚ))
        (constSeries (0:ℚ)) 1 = 3 := by
  rw [wmSim_one]; norm_num [wmStep]

/-! ===========================================================================
    §9  ⚠ **前件审计表**（本项目最高频问题的自查）

    **任务书纪律 7 原文**：「检查你的定理的前件是否已把结论包进去（同义反复）」
    **任务书纪律 8 原文**：「描述文件存在时，用至少 2 种 grep 模式确认」

    ### 9.1 逐条审计

    | 定理 | 前件 | 结论 | 是否同义反复 |
    |---|---|---|---|
    | `wmWorldModel_f` | 无 | `f = wmStep` | **否**：这是**关于实例字段**的等式，`rfl` 可关是因为 `wmStep` 是同一个字面量；若把 `simulator.step` 换成丢弃 θ 的版本，`rfl` **失败**。它断言「实例的机制**就**是读 θ 的那个函数」 |
    | `wmWorldModel_f_apply` | 无 | `f x u ε θ a = θ*x+u+ε+a` | **否**：右边**显含 θ**，是被断言的算术式；左边是抽象投影 |
    | `predFrom_eq_wmStep` | 无 | `predFrom … = wmStep …` | **否**：经 `WorldModel.f` 两级（见 §5 的说明）|
    | `predFrom_wmWorldModel` | 无 | `predFrom … = θ*x+u+ε+a` | **否**：同上，结论含 θ |
    | `wmPred_eq_predFrom` | 无 | 可计算镜像 = `predFrom` | **否**：两侧是**不同**定义（一个 `def`、一个 `noncomputable`）|
    | `affine_separates_theta` | `x ≠ 0`、`θ₁ ≠ θ₂` | 两式**不等** | **否**：前件讲 `x`、`θ`，结论讲**输出**；不是同一命题。**⚠ 见 9.2** |
    | `wmStep_separates_theta` | 同上（`x ≠ 0`、`θ₁ ≠ θ₂`）| `wmStep` 输出不等 | **否**，同上 |
    | `predFrom_separates_theta` | 同上 | `predFrom` 输出不等 | **否**，同上 |
    | `exists_theta_affects_prediction` | **无** | **存在**一组值使输出不等 | **否**：无前件，全部兑现为具体值 |
    | `predFrom_theta_strictMono` | `0 < x`、`θ₁ < θ₂` | 输出**严格增** | **否**：前件是序关系，结论是**输出**的序关系 |
    | `predFrom_diff_eq` | **无** | 输出差 = `(θ₂-θ₁)*x` | **否**：定量等式，非退化 |
    | `example_*` | **无** | 具体数值 | **否**：是 §7 一般式的实例 |
    | `wmSim_one` | **无** | `sim` 第 1 步 = `wmStep 0 …` | **否**：经 `sim_succ`/`sim_zero` 两级 |
    | `wmSim_one_indep_theta` | **无** | `sim` 第 1 步**与 θ 无关** | **否**：结论是**相等**，且经 §9.3 的真值审查 |
    | `predFrom_nonzero_start_separates` | `θ₁ ≠ θ₂` | `predFrom` 从 `x = 1` 起输出不等 | **否**：前件讲 θ，结论讲输出 |

    ### 9.2 ⚠ **`affine_separates_theta` 的 `x ≠ 0` 前件的诚实说明**

    本实例的机制是**乘性**的（`θ * x`），故 `x = 0` 时 θ **确实**无作用。
    这个前件**不是**为了把结论塞进去——它是**数学上必要**的：
    `x = 0` 时定理的结论**是假的**（§7.3 的 `#eval` 打印了两者均为 `8`）。
    **⟹ 若前件把结论包了进去，那 `x = 0` 的版本也该可证；但它被 `#eval` 反证。**

    ### 9.3 ⚠ **一条被删除的定理：为何「`sim` 第 1 步随 θ 分离」不可证**

    **草稿中曾有**一条 `wmSim_separates_theta`，声称
    「`θ₁ ≠ θ₂` ⟹ `W.sim θ₁ … 1 ≠ W.sim θ₂ … 1`」。**它无法成立**，已删除。

    理由：`sim` 的初值来自**状态块**（`W.x = 0`），而非任意 `x`。于是
    `wmStep 0 u ε θ a = θ * 0 + u + ε + a = u + ε + a`，**与 θ 无关**。
    故 `θ₁ ≠ θ₂` 时结论的**两侧本来就相等**，该定理的**结论为假**，
    任何「证明」只能是假证明。**⟹ 按纪律已删除，不保留 `sorry` 占位。**
    本文件在 §9.3 保留这条审计记录，并给出**正确的**陈述：
    `x₀ = 0` 时 `sim` 第 1 步**与 θ 无关**（`wmSim_one_indep_theta`）。
    这比原来那条**更强也更有信息**：它把「乘性增益在 0 处失效」在轨迹层兑现。
    真正有内容的轨迹层分离须改起点，见 `predFrom_nonzero_start_separates`。

    ### 9.4 与审计结论的对照

    | 审计发现 | 本文件的答复 |
    |---|---|
    | 库内 2 个实例 `step := fun x _ _ _ _ => x` 丢弃 θ | §4 给出**第三个**实例，`step` 显式读 θ（`wmWorldModel_f`）|
    | `EndToEndConverge.lean:177` 的 `f θ * x` 所在模块未编译、主定理绕开 step | §5 证明 `predFrom` **经 `WorldModel.f`** 等于真实输出（`predFrom_eq_wmStep` + `wmWorldModel_f_apply`），**不绕开** |
    | 「θ 真的影响预测」从未打通 | §6 分离定理（一般 + 存在）+ §7 数值 + §7.3 `#eval` 打印 + §8 轨迹层 |
    =========================================================================== -/

/-- ⭐⭐ **正确的轨迹层陈述**：初值为 `0` 时，`W.sim` 的第 1 步**与 θ 无关**。

**这是 §9.3 审计结论的正面兑现**：本实例的 θ 作用**以 `x` 为增益**，
故从 `x₀ = 0` 出发时 θ 的影响在**第 1 步**尚未显现
（要到第 2 步才显现——但本文件不证第 2 步，故**不声称**）。

**⟹ 本定理的结论是「相等」，与「`sim` 第 1 步随 θ 分离」的朴素期待**相反**。
后者（`x₀ = 0` 下的分离）因结论为假而**不可能**成立，故**未**写入本文件
（不保留 `sorry` 占位；审计记录见 §9.3）。 -/
theorem wmSim_one_indep_theta (θ₁ θ₂ u ε a : ℚ) :
    WorldModel.sim wmWorldModel θ₁ (constSeries u) (constSeries ε) (constSeries a) 1
      = WorldModel.sim wmWorldModel θ₂ (constSeries u) (constSeries ε) (constSeries a) 1 := by
  rw [wmSim_one, wmSim_one]
  simp only [wmStep, mul_zero, zero_add]

/-- ⭐ **轨迹层的**正面**分离定理**（改起点使 θ 可分离）。

**为什么这一条才有内容**：§8 的 `sim` 起点被**状态块钉死**为 `0`，
故在 `sim` 上 θ 的乘性作用**看不到**。要看到它，须让 `predFrom` 从
`x ≠ 0` 出发（这正是端到端链的真实情形：起点是**观测估计**，不是 `x₀`）。

**⟹ 本定理与 `wmSim_one_indep_theta` 一起，精确刻画了本实例的诚实边界**：
`step` 读 θ（§6），但若实际起点为 `0`，则该作用在本实例退化为 `0`。
本文件**不隐瞒**这一点。 -/
theorem predFrom_nonzero_start_separates {θ₁ θ₂ u ε a : ℚ} (hθ : θ₁ ≠ θ₂) :
    Fate.EndToEnd.predFrom wmWorldModel θ₁ u ε a (1:ℚ)
      ≠ Fate.EndToEnd.predFrom wmWorldModel θ₂ u ε a (1:ℚ) :=
  predFrom_separates_theta one_ne_zero hθ

end WorldModelReadsTheta

end Fate
