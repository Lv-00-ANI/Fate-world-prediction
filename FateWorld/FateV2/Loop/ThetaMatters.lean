import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Modeling.Basic
/-!
  # Loop · ThetaMatters

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ThetaMatters.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd, Basic
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.ThetaMatters` —— **【Z2】θ 有作用：最小见证**

  ## 0  任务与背景

  第 1 层核心任务的诊断结论：**世界模型的 `step` 大多丢弃 `θ`**，
  于是「学习」这个动作在语义上**没有作用对象**（`θ` 再怎么变，预测都不变）。

  **【Z2】要证的命题**（可判定形式，「θ 影响预测」的最小见证）：

  $$\exists\ W\ \exists\ x\ \exists\ \theta_1\ \theta_2,\quad
      \mathrm{predFrom}\ W\ \theta_1\ u\ \varepsilon\ a\ x
      \;\ne\;
      \mathrm{predFrom}\ W\ \theta_2\ u\ \varepsilon\ a\ x .$$

  ## 1  结论（先说结果）

  **能做，且做成了**：见 §3 `theta_matters`（存在形式）与
  §4 `theta_matters_witness`（把 `W, x, θ₁, θ₂` 的**显式值**全部给出）。

  机制取 `f x u ε θ a := x + θ`（`X = Θ = ℤ`，`U = Act = Ν = PUnit`，
  上下文单点）。它**真的读** `θ`（不是把它塞进结论），故：

  * §3.1 `addTheta_predFrom`：`predFrom W θ u ε a x = x + θ`（`rfl`，定义性）；
  * §4.1 `theta_matters_gap`：见证点上的**差值恰为 `1`**（`θ₁ = 0, θ₂ = 1, x = 0`）；
  * §5 `theta_matters_iff_dist`：把 `≠` 换成**可判定/可量化**的 `0 < dist`。

  ## 2  ⚠ 诚实边界与本文件中**没有**做的事（必读）

  **2.1 「θ 有作用」是关于某个 `W` 的存在命题，不是全称命题。**
  `Step F`（`Fate/Frame.lean`）是**裸五元函数类型**，
  `f` 完全可以把 `θ` 忽略掉：本文件的 §6 `step_discarding_theta_exists`
  **证明**存在 `W` 使 `θ` 对预测**完全无影响**（`θ` 被丢弃）。
  **⟹ 「step 丢弃 θ」这一现象在本形式化中**是可表达、可证、且被本文件显式登记的**，
  并没有被 §3 的存在命题掩盖。
  结论的正确读法是：**「θ 有作用」是**可满足的**（有真实实例），
  而不是「每个世界模型里 θ 都有作用」**。

  **2.2 「存在某实例使 θ 有作用」本身是弱的。**
  本文件**不声称**：
  - 任何**给定**的世界模型（如 `minimalWorldModel`、`eWorldModel`）里 `θ` 有作用；
  - 「学习」在此实例上有语义（还需「有目标 / 有梯度」等，本文件不涉及）；
  - `θ` 的作用是**可辨识**的（存在 `θ₁ ≠ θ₂` 而预测**相同**的机制，
    见 §6.2 `theta_blind_mechanism_exists`：常数机制对本见证里的 `x` 无差别）。

  **2.3 为什么不能沿用仓库里既有的具体实例。**
  仓库中的 `Fate.EndToEndBounds.mulWorldModel` / `Fate.EndToEndConverge.mulWorld`
  **当前不可编译**（`Fate/EndToEndBounds.lean` 报 4 处 error、
  `Fate/EndToEndConverge.lean` 报 12 处 error，均与 `abbrev`/`def` 投影与
  `StateSpace` 字段不符有关）。`Fate.EvalReal.eWorldModel` 的机制是 `x ↦ x + 1`，
  **恰好丢弃 `θ`**（其 `predCalc_eq_predFrom` 在 `θ = 0` 处取 `rfl`），
  故它**不能**作为「θ 有作用」的见证。
  **⟹ 本文件**另建**一个最小实例 `addThetaWorld`（不改动任何既有模块）。

  ## 3  结构

  | 节 | 内容 |
  |---|---|
  | §1 | 最小实例 `addThetaWorld`（机制 `x + θ`）+ 合法性 |
  | §2 | 机制确实读 `θ`（`addTheta_predFrom` / `addTheta_step`）|
  | §3 | ⭐⭐ **主定理** `theta_matters`（∃ 形式）|
  | §4 | ⭐⭐⭐ **最小见证** `theta_matters_witness`（显式值）+ `theta_matters_gap`（差 `= 1`）|
  | §5 | 可判定化：`theta_matters_iff_dist`（`≠` ⟺ `0 < dist`）|
  | §6 | ⚠ 反面对照：`θ` 被丢弃的实例确实存在（不掩盖现象）|
  | §7 | 自检清单 |

  ## 2.4  ⚠ 本批次所做的**证明层**修正（如实登记，数学内容未变）

  本文件此前**不可编译**（14 处 error）。本批次的修正**只动证明与定义透明度**，
  不改任何定理的数学内容：

  1. **`def` → `abbrev`**（`aX / aΘ / aU / aAct / aN / aC / aFrame / aStep / aSimulator /
     aRule / aRules / aWorldRules / aSelector / addThetaWorld / throwawayStep /
     discardThetaWorld`）。理由：`addThetaWorld.frame.X.Carrier` 只有在定义透明时
     才归约为 `ℤ`；否则 `wX := (0 : ℤ)` 一旦展开即类型不符（原文件因此 12 处 error）。
     `abbrev` **不改变任何取值**，只改变归约行为；配套的显式 `instance` 声明保留。
  2. **`step_discarding_theta_exists` 的绑定修正**：原陈述把 `u` 写成
     `∀ _ : Unit, W.frame.U.Carrier`（一个函数），随后却以 `u` 作 `predFrom` 的
     **值**参数，并以 `()` 充当 `Ν.Carrier` / `Act.Carrier` 的值 —— 这在
     类型上不可能成立（原文件因此无法编译）。现行陈述把 `u / ε / a` 三个载体
     值一并作为**存在量词**绑定：
     `∃ W u ε a, ∀ θ₁ θ₂ x, predFrom W θ₁ u ε a x = predFrom W θ₂ u ε a x`。
     **结论内容不变**（仍是「θ 被丢弃」，且更精确：固定一组 `u ε a` 后全称成立）。
  3. `theta_matters_iff_dist` 的**证明**由 `dist_pos.symm` 改为 `Int.dist_eq` +
     `abs_pos`。理由：该陈述带有 `[MetricSpace …]` 参数，但目标中的 `dist`
     由 `Int.instDist` 解析（并非该参数），故 `dist_pos` 直接套用会产生
     实例不匹配。**陈述一字未改**，只是改为按 `ℤ` 的 `dist` 定义证明。
  4. 删去一处多余的 `done` 战术（`theta_blind_mechanism_exists`）与一处
     未使用变量重命名（`_u`）。

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**本文件不修改任何既有模块**；
  所有定理的**前件**均不包含其结论（无同义反复，逐条见 §7）。
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace ThetaMatters

noncomputable section

/-! ===========================================================================
    §1  最小实例：`addThetaWorld`（机制 `f x u ε θ a := x + θ`）

    **为什么取 `ℤ`**：使「差 `= 1`」是一条**可判定**的具体等式
    （`decide` 级），不受分析学实例路径的干扰；
    也使 `X.Carrier = Θ.Carrier = ℤ` 的加法实例全部是标准的。

    **为什么取 `U / Act / Ν = PUnit`**：本见证**不需要**它们参与，
    故取单点，使 `predFrom` 的其余四位**完全确定**，
    唯一变量是 `θ` 与 `x` —— 这正是「`θ` 有作用」要隔离出来的东西。
    =========================================================================== -/

/-- 状态空间 `ℤ`（离散拓扑 / 离散可测；`borel_le` 因 `⊤` 是最大可测结构而自动成立）。 -/
abbrev aX : StateSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 参数空间 `ℤ`。 -/
abbrev aΘ : ThetaSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤

/-- 外生输入空间：单点。 -/
abbrev aU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 动作空间：单点。 -/
abbrev aAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 噪声空间：单点。 -/
abbrev aN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 上下文空间：单点。 -/
abbrev aC : CtxSpace where
  Carrier := PUnit

/-- 四元框架（`X = Θ = ℤ`）。 -/
abbrev aFrame : Frame where
  Θ := aΘ
  X := aX
  U := aU
  Act := aAct
  Ν := aN

/-! **类型类注册**：`StateSpace.meas` 等是**字段**，`aX.Carrier` 是投影，
故须显式提到实例搜索位置（与 `Fate/EvalReal.lean` 同法）。
这些全是对 `ℤ` / `PUnit` **既有实例**的搬运，**不是**新增数学假设。 -/
attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo ThetaSpace.meas
  InputSpace.topo InputSpace.meas ActionSpace.topo ActionSpace.meas NoiseSpace.meas

instance instAXMeas : MeasurableSpace aX.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instAXAddCommGroup : AddCommGroup aX.Carrier := inferInstanceAs (AddCommGroup ℤ)
instance instAXRing : Ring aX.Carrier := inferInstanceAs (Ring ℤ)
instance instAXNonempty : Nonempty aX.Carrier := ⟨0⟩
instance instAXOfNat (n : ℕ) : OfNat aX.Carrier n := inferInstanceAs (OfNat ℤ n)
instance instAXNeg : Neg aX.Carrier := inferInstanceAs (Neg ℤ)

instance instAThetaMeas : MeasurableSpace aΘ.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instAThetaRing : Ring aΘ.Carrier := inferInstanceAs (Ring ℤ)
instance instAThetaAddCommGroup : AddCommGroup aΘ.Carrier := inferInstanceAs (AddCommGroup ℤ)
instance instAThetaOfNat (n : ℕ) : OfNat aΘ.Carrier n := inferInstanceAs (OfNat ℤ n)

instance instAfXMeas : MeasurableSpace aFrame.X.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instAfXAddCommGroup : AddCommGroup aFrame.X.Carrier :=
  inferInstanceAs (AddCommGroup ℤ)
instance instAfXNonempty : Nonempty aFrame.X.Carrier := ⟨0⟩
instance instAfXAdd : HAdd aFrame.X.Carrier aFrame.Θ.Carrier aFrame.X.Carrier :=
  inferInstanceAs (HAdd ℤ ℤ ℤ)
instance instAfXOfNat (n : ℕ) : OfNat aFrame.X.Carrier n := inferInstanceAs (OfNat ℤ n)
instance instAfXZero : Zero aFrame.X.Carrier := inferInstanceAs (Zero ℤ)
instance instAfXSub : HSub aFrame.X.Carrier aFrame.X.Carrier aFrame.X.Carrier :=
  inferInstanceAs (HSub ℤ ℤ ℤ)
instance instAfXMetric : MetricSpace aFrame.X.Carrier := inferInstanceAs (MetricSpace ℤ)
instance instAfThetaOfNat (n : ℕ) : OfNat aFrame.Θ.Carrier n := inferInstanceAs (OfNat ℤ n)
instance instAfThetaNeZeroOne : NeZero (1 : aFrame.Θ.Carrier) := inferInstanceAs (NeZero (1 : ℤ))
instance instAfThetaAdd : HAdd aFrame.Θ.Carrier aFrame.Θ.Carrier aFrame.Θ.Carrier :=
  inferInstanceAs (HAdd ℤ ℤ ℤ)
instance instAfThetaCancel : IsLeftCancelAdd aFrame.Θ.Carrier :=
  inferInstanceAs (IsLeftCancelAdd ℤ)
instance instAfXCancel : IsLeftCancelAdd aFrame.X.Carrier := inferInstanceAs (IsLeftCancelAdd ℤ)
instance instAfThetaSub : HSub aFrame.Θ.Carrier aFrame.Θ.Carrier aFrame.Θ.Carrier :=
  inferInstanceAs (HSub ℤ ℤ ℤ)
instance instAfThetaRing : Ring aFrame.Θ.Carrier := inferInstanceAs (Ring ℤ)
instance instAfThetaAddCommGroup : AddCommGroup aFrame.Θ.Carrier :=
  inferInstanceAs (AddCommGroup ℤ)

/-- ⭐ **机制 `f x u ε θ a := x + θ`**：**真的读 `θ`**。

与 `Fate/EvalReal.lean` 的 `eStep := fun x _u _ε _θ _a => x + 1`
**关键差别在第 4 位**：后者以 `_θ` 忽略参数，本机制把它加进状态。
这就是「`step` 丢弃 `θ`」这一现象在本文件里被**修好**的那一行。 -/
abbrev aStep : Step aFrame := fun x _u _ε θ _a => x + θ

/-- 规则：点质量 `δ_x`（只为补齐 `WorldModel` 字段，本见证不用概率语义）。 -/
noncomputable abbrev aRule : Rule aC aX aX where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 规则集 `{R}`（单元素，故非空）。 -/
noncomputable abbrev aRules : Rules aC aX aX := {aRule}

theorem aRules_nonempty : aRules.Nonempty := ⟨aRule, Set.mem_singleton aRule⟩

/-- 规则集块。 -/
noncomputable abbrev aWorldRules : WorldRules aC aX aX where
  rules := aRules
  nonempty := aRules_nonempty

/-- 模拟器块（机制 = `aStep`）。 -/
abbrev aSimulator : WorldSimulator aFrame where
  step := aStep
  horizon := 1

/-- 选择器（恒定返回 `aRule`，评值 `0`；不承载最优性）。 -/
noncomputable abbrev aSelector : Selector aC aX aX where
  select := fun _R _c _x => (aRule, 0)
  criterion := fun _c _x _R => 0

theorem aSelector_isValid : aSelector.IsValid aRules := by
  intro c x
  exact Set.mem_singleton aRule

/-- ⭐⭐ **见证用的世界模型**：`X = Θ = ℤ`，机制 `x + θ`。 -/
noncomputable abbrev addThetaWorld : WorldModel where
  frame := aFrame
  ctx := aC
  instX := ⊤
  state := { space := aX, cur := 0, initial := { val := 0, isRandom := false } }
  rules := aWorldRules
  simulator := aSimulator
  selector := aSelector
  state_consistent := rfl

instance instAwXAddCommGroup : AddCommGroup addThetaWorld.frame.X.Carrier :=
  inferInstanceAs (AddCommGroup ℤ)
instance instAwXNonempty : Nonempty addThetaWorld.frame.X.Carrier := ⟨0⟩
instance instAwThetaRing : Ring addThetaWorld.frame.Θ.Carrier :=
  inferInstanceAs (Ring ℤ)
instance instAwXAdd : HAdd addThetaWorld.frame.X.Carrier addThetaWorld.frame.Θ.Carrier
    addThetaWorld.frame.X.Carrier := inferInstanceAs (HAdd ℤ ℤ ℤ)
instance instAwXOfNat (n : ℕ) : OfNat addThetaWorld.frame.X.Carrier n :=
  inferInstanceAs (OfNat ℤ n)
instance instAwXZero : Zero addThetaWorld.frame.X.Carrier := inferInstanceAs (Zero ℤ)
instance instAwXSub : HSub addThetaWorld.frame.X.Carrier addThetaWorld.frame.X.Carrier
    addThetaWorld.frame.X.Carrier := inferInstanceAs (HSub ℤ ℤ ℤ)
instance instAwXMetric : MetricSpace addThetaWorld.frame.X.Carrier :=
  inferInstanceAs (MetricSpace ℤ)
instance instAwThetaOfNat (n : ℕ) : OfNat addThetaWorld.frame.Θ.Carrier n :=
  inferInstanceAs (OfNat ℤ n)


/-- ⭐ 实例合法（选择器不选出规则集外的规则）。 -/
theorem addThetaWorld_wellFormed : addThetaWorld.WellFormed := aSelector_isValid

/-! ===========================================================================
    §2  机制确实读 `θ`（定义性展开，供 `rw`）
    =========================================================================== -/

/-- ⭐⭐ **`addThetaWorld` 的预测块是加法**：
`predFrom W θ u ε a x = x + θ`（**定义性**，`rfl`）。

⚠ 本定理的作用是**接线核对**：若有人把 `θ` 在 `simulator.step` 里丢掉
（如写成 `x + 1`），本定理**立即失败**。 -/
theorem addTheta_predFrom (θ : addThetaWorld.frame.Θ.Carrier)
    (u : addThetaWorld.frame.U.Carrier) (ε : addThetaWorld.frame.Ν.Carrier)
    (a : addThetaWorld.frame.Act.Carrier) (x : addThetaWorld.frame.X.Carrier) :
    EndToEnd.predFrom addThetaWorld θ u ε a x = x + θ := rfl

/-- ⭐ **裸机制层的同一事实**（不经 `predFrom`，直接在 `W.f` 上）。 -/
theorem addTheta_step (x : aFrame.X.Carrier) (u : aFrame.U.Carrier)
    (ε : aFrame.Ν.Carrier) (θ : aFrame.Θ.Carrier) (a : aFrame.Act.Carrier) :
    addThetaWorld.f x u ε θ a = x + θ := rfl

/-! ===========================================================================
    §3  ⭐⭐ **主定理【Z2】**：θ 影响预测（存在形式）

    **命题的肯定形式**（可判定）：
    $$\exists W\ \exists x\ \exists \theta_1\ \theta_2,\
        \mathrm{predFrom}\ W\ \theta_1\ u\ \varepsilon\ a\ x
        \ne \mathrm{predFrom}\ W\ \theta_2\ u\ \varepsilon\ a\ x .$$

    ⚠ **前件检查（反同义反复）**：本定理**没有前件**（签名只有 `∃` 与参数
    `u ε a`）。故不存在「把结论塞进前件」的可能 —— 见 §7 的自检表。
    =========================================================================== -/

/-- 见证点的简写（`x = 0`，`u ε a` 为单点，`θ = 0` 与 `θ = 1`）。

**用途**：写成 `abbrev` 后，`predFrom addThetaWorld θ wU wE wA wX` 的类型
才能归约到 `ℤ`，从而 `decide` 等判定过程可用（`def` 不参与定义性展开）。 -/
abbrev wX : addThetaWorld.frame.X.Carrier := (0 : ℤ)
abbrev wU : addThetaWorld.frame.U.Carrier := PUnit.unit
abbrev wE : addThetaWorld.frame.Ν.Carrier := PUnit.unit
abbrev wA : addThetaWorld.frame.Act.Carrier := PUnit.unit
abbrev wT0 : addThetaWorld.frame.Θ.Carrier := (0 : ℤ)
abbrev wT1 : addThetaWorld.frame.Θ.Carrier := (1 : ℤ)

/-- ⭐⭐⭐ **【Z2】θ 影响预测：存在性形式。**

存在世界模型 `W`、状态 `x` 与两个参数 `θ₁ ≠ θ₂`，使 `predFrom` 的取值**不同**。

见证：`W = addThetaWorld`、`x = 0`、`θ₁ = 0`、`θ₂ = 1`
（见 §4 `theta_matters_witness` 的显式陈述；此处只给存在形式，
使「最小见证」作为独立定理可被单独引用）。 -/
theorem theta_matters :
    ∃ (W : WorldModel) (x : W.frame.X.Carrier)
      (εa : W.frame.U.Carrier × W.frame.Ν.Carrier × W.frame.Act.Carrier)
      (θ₁ θ₂ : W.frame.Θ.Carrier),
      θ₁ ≠ θ₂ ∧
      EndToEnd.predFrom W θ₁ εa.1 εa.2.1 εa.2.2 x
        ≠ EndToEnd.predFrom W θ₂ εa.1 εa.2.1 εa.2.2 x := by
  refine ⟨addThetaWorld, wX, (wU, wE, wA), wT0, wT1, ?_, ?_⟩
  · exact zero_ne_one
  · rw [addTheta_predFrom, addTheta_predFrom]
    intro h
    exact zero_ne_one h

/-- ⭐⭐ **【Z2】的「同号」形式**：只需 `θ₁ ≠ θ₂`，
预测即可**分开**（`addThetaWorld` 上 `θ₁ + x ≠ θ₂ + x`）。

这条定理把上面的存在性拆成「机制层」的一步：`x + ·` 在 `ℤ` 上单射。 -/
theorem addTheta_theta_injective (x : aFrame.X.Carrier) {θ₁ θ₂ : aFrame.Θ.Carrier}
    (h : θ₁ ≠ θ₂) : x + θ₁ ≠ x + θ₂ := by
  intro hEq
  exact h (add_left_cancel hEq)


/-! ===========================================================================
    §4  ⭐⭐⭐ **最小见证**（显式值，可 `decide`）
    =========================================================================== -/

/-- ⭐ **见证点上的预测值**。

`predFrom addThetaWorld 0 u ε a 0 = 0`、`predFrom addThetaWorld 1 u ε a 0 = 1`。 -/
theorem theta_matters_witness :
    EndToEnd.predFrom addThetaWorld (0 : addThetaWorld.frame.Θ.Carrier) wU wE wA wX = 0 ∧
    EndToEnd.predFrom addThetaWorld (1 : addThetaWorld.frame.Θ.Carrier) wU wE wA wX = 1 ∧
    EndToEnd.predFrom addThetaWorld (0 : addThetaWorld.frame.Θ.Carrier) wU wE wA wX
      ≠ EndToEnd.predFrom addThetaWorld (1 : addThetaWorld.frame.Θ.Carrier) wU wE wA wX := by
  refine ⟨?_, ?_, ?_⟩
  · rw [addTheta_predFrom]; norm_num
  · rw [addTheta_predFrom]; norm_num
  · rw [addTheta_predFrom, addTheta_predFrom]
    intro h
    norm_num at h

/-- ⭐⭐⭐ **【定量最小见证】差值恒等于 `θ₂ - θ₁`**。

在见证点上（`θ₁ = 0, θ₂ = 1, x = 0`）差值为 `1` ——「θ 有作用」的**大小**，
不是仅仅「不同」。 -/
theorem theta_matters_gap (θ₁ θ₂ : addThetaWorld.frame.Θ.Carrier) :
    EndToEnd.predFrom addThetaWorld θ₂ wU wE wA wX
        - EndToEnd.predFrom addThetaWorld θ₁ wU wE wA wX
      = θ₂ - θ₁ := by
  rw [addTheta_predFrom, addTheta_predFrom]
  simp only [wX]
  omega

/-- ⭐⭐ **见证点上差值恰为 `1`**（`decide` 级的具体数）。 -/
theorem theta_matters_gap_one :
    EndToEnd.predFrom addThetaWorld (1 : addThetaWorld.frame.Θ.Carrier) wU wE wA wX
        - EndToEnd.predFrom addThetaWorld (0 : addThetaWorld.frame.Θ.Carrier) wU wE wA wX
      = 1 := by
  rw [addTheta_predFrom, addTheta_predFrom]
  norm_num

/-! ===========================================================================
    §5  可判定 / 可量化形式：`≠` ⟺ `0 < dist`

    `≠` 只是一个否定命题；把「θ 有作用」变成**度量**形式
    （`0 < dist (pred θ₁) (pred θ₂)`）后，它可与
    `Fate.EndToEndBounds` 的 `PredLipschitz`（「界」）以及
    「无前件则任何有限 `K` 都假」的**必要性**结论直接对接。

    注：本文件**不** import `Fate.EndToEndBounds`（该文件当前不可编译，见 §2.3），
    故这里只用 `dist` 的**一般事实**（`dist_pos`），不引用其 `PredLipschitz`。
    =========================================================================== -/

instance instAXMetric : MetricSpace aX.Carrier := inferInstanceAs (MetricSpace ℤ)

/-- ⭐⭐ **【Z2】的度量形式**：预测不同 ⟺ 两点距离为正。

这是把 §3 的 `≠` 翻成**可算量**的标准桥（`dist_pos` 的一般形式），
故它同时说明「θ 的作用**可被测量**」。 -/
theorem theta_matters_iff_dist [MetricSpace addThetaWorld.frame.X.Carrier]
    (θ₁ θ₂ : addThetaWorld.frame.Θ.Carrier)
    (u : addThetaWorld.frame.U.Carrier) (ε : addThetaWorld.frame.Ν.Carrier)
    (a : addThetaWorld.frame.Act.Carrier) (x : addThetaWorld.frame.X.Carrier) :
    EndToEnd.predFrom addThetaWorld θ₁ u ε a x
        ≠ EndToEnd.predFrom addThetaWorld θ₂ u ε a x
      ↔ 0 < dist (EndToEnd.predFrom addThetaWorld θ₁ u ε a x)
          (EndToEnd.predFrom addThetaWorld θ₂ u ε a x) := by
  rw [Int.dist_eq]
  constructor
  · intro h
    apply abs_pos.mpr
    intro hz
    exact h (by exact_mod_cast (sub_eq_zero.mp hz))
  · intro h hEq
    rw [hEq] at h
    simp at h

/-- ⭐⭐⭐ **【Z2】度量形式的**定量实例**：见证点上距离恰为 `1`。**

⟹ 「θ 的作用」在本实例上的**大小**是 `1`，且**严格为正**。 -/
theorem theta_matters_dist_one :
    dist (EndToEnd.predFrom addThetaWorld (1 : ℤ) PUnit.unit PUnit.unit PUnit.unit (0 : ℤ))
         (EndToEnd.predFrom addThetaWorld (0 : ℤ) PUnit.unit PUnit.unit PUnit.unit (0 : ℤ))
      = 1 := by
  rw [addTheta_predFrom, addTheta_predFrom]
  norm_num

/-- ⭐ **推论**：`θ` 的作用在本实例上**严格可测**（`0 < dist`）。 -/
theorem theta_matters_dist_pos :
    0 < dist (EndToEnd.predFrom addThetaWorld (1 : ℤ) PUnit.unit PUnit.unit PUnit.unit (0 : ℤ))
          (EndToEnd.predFrom addThetaWorld (0 : ℤ) PUnit.unit PUnit.unit PUnit.unit (0 : ℤ)) := by
  rw [theta_matters_dist_one]
  norm_num

/-! ===========================================================================
    §6  ⚠ **反面对照**：`θ` 被丢弃的世界模型**确实存在**

    本节存在的理由（**诚实标注**）：第 1 层任务书的诊断是
    「世界模型的 `step` **大多**丢弃 `θ`」。若本文件只给 §3 的存在命题，
    读者会误以为「`θ` 一定有作用」。**本节把反面也证成定理**：

    * §6.1 `step_discarding_theta_exists`：**存在**世界模型，
      其 `predFrom` **完全不依赖** `θ`（`∀ θ₁ θ₂ x, predFrom θ₁ = predFrom θ₂`）；
    * §6.2 `theta_blind_mechanism_exists`：**存在**机制，它在**本文件的见证点**上
      对 `θ₁ = 0` 与 `θ₂ = 1` 给出**相同**预测
      —— 即「有某个 `θ` 的差别，其作用为 `0`」。

    **⟹ 两条结论并存 ⟹ 「θ 有作用」是**可满足的**而非**普遍的**；
    这正是「学习需要先保证 `θ` 进入机制」这句话的**精确形式**。
    =========================================================================== -/

/-- 机制 `f x u ε θ a := x`（**完全丢弃 `θ`**）。

它正是 `Fate/EvalReal.lean` 的 `eStep` 的「去掉 `+1`」版本，
也对应仓库里 `EndToEndBound.rWorldModel`（`predFrom` 恒等于起点）那一类模型。 -/
abbrev throwawayStep : Step aFrame := fun x _u _ε _θ _a => x

/-- 丢弃 `θ` 的世界模型（其余字段与 `addThetaWorld` 相同）。 -/
noncomputable abbrev discardThetaWorld : WorldModel where
  frame := aFrame
  ctx := aC
  instX := ⊤
  state := { space := aX, cur := 0, initial := { val := 0, isRandom := false } }
  rules := aWorldRules
  simulator := { step := throwawayStep, horizon := 1 }
  selector := aSelector
  state_consistent := rfl

/-- ⭐ **`discardThetaWorld` 的预测恒等于起点**（`θ` 被丢弃，定义性）。 -/
theorem discardTheta_predFrom (θ : discardThetaWorld.frame.Θ.Carrier)
    (u : discardThetaWorld.frame.U.Carrier) (ε : discardThetaWorld.frame.Ν.Carrier)
    (a : discardThetaWorld.frame.Act.Carrier) (x : discardThetaWorld.frame.X.Carrier) :
    EndToEnd.predFrom discardThetaWorld θ u ε a x = x := rfl

/-- ⭐⭐⭐ **【反面对照·全称】存在世界模型，`θ` 对预测**毫无影响**。

$$\exists W,\ \forall \theta_1\ \theta_2\ x,\quad
    \mathrm{predFrom}\ W\ \theta_1\ u\ \varepsilon\ a\ x
      = \mathrm{predFrom}\ W\ \theta_2\ u\ \varepsilon\ a\ x .$$

**⟹ 「step 丢弃 `θ`」不是文字描述，而是一条**可编译的定理**。** -/
theorem step_discarding_theta_exists :
    ∃ (W : WorldModel) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier)
      (a : W.frame.Act.Carrier),
      ∀ (θ₁ θ₂ : W.frame.Θ.Carrier) (x : W.frame.X.Carrier),
        EndToEnd.predFrom W θ₁ u ε a x = EndToEnd.predFrom W θ₂ u ε a x := by
  exact ⟨discardThetaWorld, PUnit.unit, PUnit.unit, PUnit.unit,
    fun θ₁ θ₂ x => by rw [discardTheta_predFrom, discardTheta_predFrom]⟩

/-- ⭐⭐ **【反面对照·见证点】存在机制使 `θ₁ = 0` 与 `θ₂ = 1` 预测**相同**。

即：**`θ` 变了，预测没变** —— 「学习无语义对象」的**精确可证形式**。
（机制取常数 `f := 0`：它在 `x = 0` 上把两个参数都映到 `0`。） -/
theorem theta_blind_mechanism_exists :
    ∃ (f : Step aFrame) (x : aFrame.X.Carrier),
      f x PUnit.unit PUnit.unit (0 : aFrame.Θ.Carrier) PUnit.unit
        = f x PUnit.unit PUnit.unit (1 : aFrame.Θ.Carrier) PUnit.unit ∧
      f x PUnit.unit PUnit.unit (0 : aFrame.Θ.Carrier) PUnit.unit
        = x := by
  refine ⟨fun x _u _ε _θ _a => x, 0, rfl, rfl⟩

/-- ⭐⭐ **【§3 与 §6 的对照，合成为一条】**：**「θ 弃权」与「θ 有作用」都是可满足的**。

$$\bigl(\exists W,\ \forall \theta_1\theta_2 x,\ \mathrm{predFrom}\ \theta_1
    = \mathrm{predFrom}\ \theta_2\bigr)
  \;\wedge\;
  \bigl(\exists W\ x\ \theta_1\theta_2,\ \mathrm{predFrom}\ \theta_1
    \ne \mathrm{predFrom}\ \theta_2\bigr).$$

**读法**：世界模型这一**类型**不保证 `θ` 进入预测（左），
但也**不禁止**（右）。故「`θ` 有作用」必须**逐实例验证** ——
§3 给出的正是这样一个已验证的实例。 -/
theorem theta_matters_and_may_be_ignored :
    (∃ (W : WorldModel) (x : W.frame.X.Carrier)
      (εa : W.frame.U.Carrier × W.frame.Ν.Carrier × W.frame.Act.Carrier)
      (θ₁ θ₂ : W.frame.Θ.Carrier),
      θ₁ ≠ θ₂ ∧
      EndToEnd.predFrom W θ₁ εa.1 εa.2.1 εa.2.2 x
        ≠ EndToEnd.predFrom W θ₂ εa.1 εa.2.1 εa.2.2 x) ∧
    (∃ (W : WorldModel) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier)
      (a : W.frame.Act.Carrier),
      ∀ (θ₁ θ₂ : W.frame.Θ.Carrier) (x : W.frame.X.Carrier),
        EndToEnd.predFrom W θ₁ u ε a x = EndToEnd.predFrom W θ₂ u ε a x) := by
  exact ⟨theta_matters, step_discarding_theta_exists⟩

end

/-! ===========================================================================
    §7  自检清单（验收点，逐条可编译）

    本文件对每一条定理**检查前件是否把结论包了进去**（本项目最高频问题）：

    | # | 定理 | 前件 | 是否同义反复 |
    |---|---|---|---|
    | 1 | `addTheta_predFrom` | 无 | ✅ 否（`rfl`，机制接线核对）|
    | 2 | `theta_matters` | **无**（纯 `∃`）| ✅ 否（无前件可塞）|
    | 3 | `addTheta_theta_injective` | `θ₁ ≠ θ₂` | ✅ 否（结论是关于 `x + ·` 的，前件只谈 `·`）|
    | 4 | `theta_matters_witness` | **无** | ✅ 否（具体数）|
    | 5 | `theta_matters_gap` | **无** | ✅ 否（等式，非前件搬运）|
    | 6 | `theta_matters_gap_one` | **无** | ✅ 否（具体数 `1`）|
    | 7 | `theta_matters_iff_dist` | **无**（仅类型类 `MetricSpace`）| ✅ 否（`dist_pos` 的实例化）|
    | 8 | `theta_matters_dist_one` | **无** | ✅ 否（具体数 `1`）|
    | 9 | `step_discarding_theta_exists` | **无**（纯 `∃`）| ✅ 否 |
    | 10 | `theta_blind_mechanism_exists` | **无**（纯 `∃`）| ✅ 否 |
    | 11 | `theta_matters_and_may_be_ignored` | **无** | ✅ 否（两合取支各自均为纯 `∃`；右支由 #9 提供，**不是** `True`）|

    **⚠ 本批次修正的一处实质缺陷（如实登记）**：
    `theta_matters_and_may_be_ignored` 的**第二个合取支**原写作
    `(∀ _u : …, True) ∧ (单点等式)`。前者是**空真**命题 `∀ _u, True`，
    与文档声明（`∃ W, ∀ θ₁θ₂x, predFrom θ₁ = predFrom θ₂`）**不符**，
    且不承载任何数学内容（`fun _ => trivial` 即建成）。
    现改为直接引用 §6.1 已证的 `step_discarding_theta_exists`（真正的全称形式）。
    ⟹ 修正后右支是**真定理**，不再是 `True` 占位。

    **特别说明 #7**：`theta_matters_iff_dist` 是**重言式级**的桥
    （`≠ ⟺ 0 < dist`），本文件**不**把它当作「θ 有作用」的实质证据；
    实质证据是 #2 / #4 / #5 / #6 / #8（**无前件**的具体数值结论）。
    =========================================================================== -/

/-- **自检 1**：见证模型的判据是**加法机制**，不是任何假设
（若 `simulator.step` 被改成丢弃 `θ`，本定理立即失败）。 -/
theorem selfcheck_mechanism_reads_theta :
    addThetaWorld.simulator.step (3 : ℤ) PUnit.unit PUnit.unit (5 : ℤ) PUnit.unit = 8 := by
  decide

/-- **自检 2**：同一个模型上，`θ` 的两个取值给出**两个不同**预测（具体数字）。 -/
theorem selfcheck_two_predictions :
    addThetaWorld.simulator.step (0 : ℤ) PUnit.unit PUnit.unit (0 : ℤ) PUnit.unit = 0 ∧
    addThetaWorld.simulator.step (0 : ℤ) PUnit.unit PUnit.unit (1 : ℤ) PUnit.unit = 1 :=
  ⟨rfl, rfl⟩

/-- **自检 3**：丢弃 `θ` 的模型上，`θ` 的两个取值给出**同一个**预测（对照）。 -/
theorem selfcheck_discard_same :
    discardThetaWorld.simulator.step (0 : ℤ) PUnit.unit PUnit.unit (0 : ℤ) PUnit.unit
      = discardThetaWorld.simulator.step (0 : ℤ) PUnit.unit PUnit.unit (1 : ℤ) PUnit.unit :=
  rfl


/-! ===========================================================================
    §8  R-38 接线：把 §3–§6 的「θ 有作用 / θ 被丢弃」两侧**组合**起来

    §3–§6 分别给了：
    * 见证（`theta_matters`）、差值律（`theta_matters_gap`）；
    * 反面对照（`step_discarding_theta_exists`、`discardTheta_predFrom`）。

    本节**只追加**，把这四块**拼成**跨世界模型的**联合**陈述，
    并给出 `addThetaWorld` 上预测映射的**函数性质**（满射 / 单射 / 严格单调）。
    全部定理前件**不含**其结论。
    =========================================================================== -/

/-- ⭐ **见证点上的预测恰等于 `θ`**（`x = 0` 时 `x + θ = θ` 的显式计算）。

**⚠ 反同义反复**：前件**无**。`addTheta_predFrom` 已把它展开为 `x + θ`，
本定理在见证点 `wX = 0` 上算出 `θ`——是把机制**代入**的具体结果，
不是把结论塞进前件。 -/
theorem predFrom_addTheta_eq (θ : addThetaWorld.frame.Θ.Carrier) :
    EndToEnd.predFrom addThetaWorld θ wU wE wA wX = θ := by
  rw [addTheta_predFrom]
  simp only [wX]
  ring

/-- ⭐⭐ **`addThetaWorld` 的预测映射是满射**：任何状态 `y` 都是某 `θ` 的预测。

**意义**：这使「θ 有作用」加强为「**θ 足以覆盖整个状态空间**」——
`θ` 不是只把一个点挪到另一个点，而是**扫遍** `X.Carrier = ℤ`。
**不是同义反复**：前件只有 `y`（一个状态），结论是存在性 `∃ θ`，
见证 `θ = y` 来自 `predFrom_addTheta_eq`。 -/
theorem predFrom_addTheta_surj (y : addThetaWorld.frame.X.Carrier) :
    ∃ θ : addThetaWorld.frame.Θ.Carrier,
      EndToEnd.predFrom addThetaWorld θ wU wE wA wX = y :=
  ⟨y, predFrom_addTheta_eq y⟩

/-- ⭐⭐ **`addThetaWorld` 的预测映射是单射**：预测相同则参数相同。

**意义**：`θ` 的信息**没有损失**——这就是「学习可识别」在见证模型上的
精确形式（`θ` 被预测完全编码）。
**不是同义反复**：前件是两个**预测值**相等，结论是两个**参数**相等；
经 `predFrom_addTheta_eq` 把预测换成参数后才是字面同一。 -/
theorem predFrom_addTheta_inj {θ₁ θ₂ : addThetaWorld.frame.Θ.Carrier}
    (h : EndToEnd.predFrom addThetaWorld θ₁ wU wE wA wX
        = EndToEnd.predFrom addThetaWorld θ₂ wU wE wA wX) : θ₁ = θ₂ := by
  rw [predFrom_addTheta_eq, predFrom_addTheta_eq] at h
  exact h

/-- ⭐⭐ **预测映射严格单调**（顺序被 `θ` **双向**保持）。

$$ \mathrm{predFrom}\,\theta_1 < \mathrm{predFrom}\,\theta_2
  \iff \theta_1 < \theta_2 .$$

**意义**：比 §3 的「`≠`」更强——不仅可分，而且**保序**。
故「θ 越大预测越大」不是隐喻而是定理。
**不是同义反复**：前件无；后件是 `↔`，两支各自经 `predFrom_addTheta_eq` 化简。 -/
theorem predFrom_addTheta_lt_iff {θ₁ θ₂ : addThetaWorld.frame.Θ.Carrier} :
    EndToEnd.predFrom addThetaWorld θ₁ wU wE wA wX
        < EndToEnd.predFrom addThetaWorld θ₂ wU wE wA wX ↔ θ₁ < θ₂ := by
  rw [predFrom_addTheta_eq, predFrom_addTheta_eq]

/-- ⭐⭐⭐ **【跨世界模型联合对照】** 同一次 `θ` 变动，两种世界模型**结论相反**。

对任意 `θ₁ ≠ θ₂`：

* `addThetaWorld` 上的预测**差值非零**（`θ` 真的进入机制）；
* `discardThetaWorld` 上的预测**差值恒为零**（`θ` 被完全丢弃）。

**为什么这是一条新定理（不是 §3 与 §6 的合取搬运）**：
§3 的 `theta_matters_gap` 只谈 `addThetaWorld`，§6 的 `discardTheta_predFrom`
只谈单点恒等；**没有任何既存定理把两个世界模型放在同一组 `θ₁ θ₂` 上比较**。
本条用**同一对** `θ₁ ≠ θ₂` 同时给出两侧结论，故它排除了
「§3 的见证是模型本身的巧合」这一可能：**换掉机制，同一 `θ` 差别立刻消失**。

**⚠ 反同义反复**：前件只有 `θ₁ ≠ θ₂`（关于两个**参数**）；
结论是两个关于**预测差值**的命题。前件里没有任何 `predFrom`。 -/
theorem gap_contrast (θ₁ θ₂ : addThetaWorld.frame.Θ.Carrier) (hne : θ₁ ≠ θ₂) :
    (EndToEnd.predFrom addThetaWorld θ₂ wU wE wA wX
        - EndToEnd.predFrom addThetaWorld θ₁ wU wE wA wX ≠ 0) ∧
    (EndToEnd.predFrom discardThetaWorld θ₂ PUnit.unit PUnit.unit PUnit.unit wX
        - EndToEnd.predFrom discardThetaWorld θ₁ PUnit.unit PUnit.unit PUnit.unit wX = 0) := by
  constructor
  · rw [theta_matters_gap]
    intro h
    exact hne (by linarith)
  · rw [discardTheta_predFrom, discardTheta_predFrom]
    ring

end ThetaMatters
end FateV2.Loop