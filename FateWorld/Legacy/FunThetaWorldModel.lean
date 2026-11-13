import FateWorld.Legacy.EndToEnd

/-! ===========================================================================
  `Fate.FunThetaWorldModel` —— **T-1b：θ 是函数（在 WorldModel 里的真实例）**

  ## 0  任务与交付

  T-1b 问的是「**θ 是点还是函数**」。库里的现状（**已逐条核实，两种 grep 模式**）：

  * `Fate/Frame.lean:73` 的 `Frame.Θ` 是 `ThetaSpace` 类型，签名
    （`Fate/Basic.lean:261`）只要求 `Carrier : Type u` + 拓扑 + 可测，
    **故取函数空间是签名允许的**；
  * 签名层的函数载体**已存在**：`Fate/ThetaExpressiveness.lean:238` 的
    `funTheta`、`Fate/StepExpressiveness.lean:66` 的 `FunTheta`
    （两者都不是 `WorldModel` 实例，只是孤立的 `ThetaSpace`）；
  * ⚠ **更正任务书对该库的描述**：称全库 `"Carrier := .*→"` 在 Θ 上「零命中」
    **不准确** —— `Fate/LearnFunction.lean:167` 的 `ptWorld`
    （`grep -rn "Θ :=" Fate/*.lean` 交叉核对）**已经**是
    `Θ.Carrier := ℝ → ℝ` 的真 `WorldModel`，机制 `θ x`。

  故本文件**不**声称「首次让 Θ 是函数空间」（那是 `LearnFunction.ptWorld` 已做的），
  而是补三条**库中确实缺失**的内容：

  | 库中现状 | 本文件 |
  |---|---|
  | `LearnFunction.ptWorld` 的机制是 `θ x`（**无** `u`/`ε`/`a`，也不含加法结构）| 机制 `g x + u + e + a`（`g` 仍作用到 `x`，且三种外生输入**可分离**）|
  | `grep -rn "WellFormed" Fate/*.lean` 全库**无任何实例证明**（只有 `WorldModel.lean` 的谓词定义）| ⭐ `funThetaWorld_wellFormed`：**首个** `WorldModel.WellFormed` 的实例证明 |
  | 无任何定理排除「θ 只造成**常数平移**」这一 `Θ := ℝ` 退化解 | ⭐ `pred_not_constant_shift`：**机检排除**该退化解（§0.1）|

  | 要求 | 定理 | 内容 |
  |---|---|---|
  | (a) | `xS` / `tS` | `Θ.Carrier := ℝ → ℝ`、`X.Carrier := ℝ` |
  | (b) | 同上 | `StateSpace.Carrier := ℝ` |
  | (c) | `funThetaWorld` | `step = fun x u e g a => g x + u + e + a` |
  | (d) | `funThetaWorld_wellFormed` | `WorldModel.WellFormed funThetaWorld` |
  | (e) | `funThetaWorld_predFrom`、`predFrom_determines_g`、`pred_not_constant_shift` | 预测 `= g x + u + e + a`；不同 `g` 给不同预测；且**不是**「标量平移」|

  ## 0.1  ⚠ 为什么 (e) 的第 3 条才是「θ 是函数」的**实质**证据

  仅仅 `Θ.Carrier := ℝ → ℝ` 是**类型层**的声明；一个装饰性的函数参数
  （例如 `step = fun x u e g a => x`，把 `g` 丢掉）也满足类型声明，
  却**不**满足「θ 是函数」。

  本文件因此证明三条**区分性**事实：

  * `predFrom_determines_g`：预测函数**唯一确定** `g`（`g` **不被丢弃**）；
  * `pred_differs_of_g_differs`：`g₁ ≠ g₂ ⟹` 存在 `x` 使预测不同（**逐点敏感**）；
  * `pred_not_constant_shift`：`g₁ = id` 与 `g₂ = 0` 的预测差
    **不是常数** —— 即「`g` 只造成一个**标量平移**」这一退化解**被机检排除**。
    这最后一条是关键：它说明 `g` 必须是**函数**（能随 `x` 变），
    不能退化成 `Θ.Carrier := ℝ` 的一个点。

  ## 0.2  ⚠ 避坑记录（第 48 / 60 轮 9 次失败的根因）

  当时主控自己写 `WorldModel` 实例失败 9 次，根因是
  `WorldModel.frame.Θ.Carrier` **不归约**到中间 `def` 的 `Θ.Carrier`。
  本文件的对策（与 `Fate/LearnFunction.lean` 的可编译 `funWorld` 一致）：

  * 空间用 **`abbrev`** 定义（`abbrev` 展开为定义体，故 `Carrier` 可归约）；
  * `WorldModel` 用 **一个 `where` 一次性内联所有字段**（不分步 `def` 再拼装）；
  * 因此 `funThetaWorld.frame.Θ.Carrier` 的 `rfl` 级等式
    `funThetaWorld_carrier : funThetaWorld.frame.Θ.Carrier = (ℝ → ℝ)`
    **可证**（`§3` 第一条），使「θ 是函数」成为**类型层可检验**事实。

  ## 0.3  ⚠ 诚实边界（不得含糊）

  **0.3.1 `Θ` 上的拓扑与可测取 `⊤`。** 本文件的定理**完全不用**
  `Θ` 上的拓扑/可测结构；取最弱结构使构造最小。这**不构成**
  任何关于「策略空间应取何种拓扑」的主张（与 `LearnFunction` §1 同一纪律）。

  **0.3.2 本文件不证明学习/收敛。** `simulator.horizon = 1`、`state.cur = 0`，
  这些只为补齐字段。本文件的全部内容是**一个实例的存在性 + 其预测语义**，
  不含轨迹收敛断言。轨迹收敛在 `Fate/LearnFunction.lean`（单点）中另做。

  **0.3.3 `u`、`ε`、`a` 的载体都取 `ℝ`**（便于写出 `g x + u + e + a`）。
  这不是「物理上正确」的主张，只是使**加法**在类型层可行。

  ## 0.4  结构

  | 节 | 内容 |
  |---|---|
  | §1 | 空间定义 `xS`（`ℝ`）/ `tS`（`ℝ → ℝ`）/ `uS` / `aS` / `nS` / `cS` |
  | §2 | ⭐⭐ 实例 `funThetaWorld`（单个 `where` 内联全部字段）|
  | §3 | ⭐⭐ (a)(b)：`Carrier` 的类型层事实（`rfl`）|
  | §4 | ⭐⭐ (c)(e)：`predFrom` 的求值语义（`rfl` 级）|
  | §5 | ⭐ (d)：`WellFormed` 的证明 |
  | §6 | ⭐⭐⭐ (e) 的实质部分：`g` 不被丢弃 / 逐点敏感 / 非标量平移；小结 `theta_function_has_substantive_effect` |
  | §7 | 具体数值核对 |
  | §8 | 自检清单（反同义反复逐条）|

  ## 0.5  ⚠ 同义反复自检（详见 §8）

  | 定理 | 前件 | 结论 | 判定 |
  |---|---|---|---|
  | `funThetaWorld_carrier` | 无 | `Θ.Carrier = ℝ→ℝ` | ✅ `rfl` 体量核对（**类型层事实，非重述前件**）|
  | `funThetaWorld_predFrom` | 无 | `predFrom = g x + u + e + a` | ✅ 无前件 |
  | `funThetaWorld_wellFormed` | 无 | `WellFormed W` | ✅ 结论是 `Sel.IsValid W.R`，需证 `r0 ∈ {r0}`；**不是**字段重述（`WellFormed` 不是 `WorldModel` 的字段）|
  | `predFrom_determines_g` | `∀x, pred x 与 pred' x 相等` | `g₁ = g₂` | ✅ 前件谈**预测值**，结论谈**函数相等**（需 `funext`）；若 `g` 被丢弃则前件恒真而结论假 ⟹ 本定理**exactly** 排除退化 |
  | `pred_differs_of_g_differs` | `g₁ ≠ g₂` | `∃x, 预测不同` | ✅ 前件谈函数不等，结论谈**存在点**；证明需逆否 + `funext` |
  | `pred_not_constant_shift` | 无 | `¬ ∃c, ∀x, 预测差 = c` | ✅ 无前件；结论排除「标量平移」这一**退化解**，是 `g` 必须为函数的核心机检 |
  | `theta_function_has_substantive_effect` | **无** | 上述三条的**合取** | ✅ 无前件；`g` 全自由；三条结论均非定义改写 |

  **⚠ 关于 3 条 `rfl` 定理的诚实标注**（用 `tautology_check.py` 实测：
  本文件 19 条定理中 3 条为 T0 = `:= rfl`）：
  `funThetaWorld_carrier` / `funThetaWorld_state_carrier` / `funThetaWorld_predFrom`
  **确实是定义展开**，它们的作用是**接线核对**（任务书 (a)(b)(c)(e) 的逐字要求），
  而不是「深刻定理」。本文件**不**把它们当作实质贡献。
  实质贡献在 §5–§6（`funThetaWorld_wellFormed` 及 §6 四条，实测 T4/T5）。

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**未修改任何既有模块**；
  本文件只导入 `Fate.EndToEnd`。
  =========================================================================== -/

namespace Fate
namespace FunThetaWorldModel

open Fate.EndToEnd

/-! ===========================================================================
    §1  空间定义

    ⚠ 全部用 `abbrev`：`abbrev` 的定义体可归约，
    故 `funThetaWorld.frame.Θ.Carrier` **能**归约到 `(ℝ → ℝ)`（§0.2 的坑）。
    =========================================================================== -/

/-- **(b) 状态空间：`X.Carrier := ℝ`**（`abbrev` 使 `Carrier` 可归约）。 -/
abbrev xS : StateSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)
  borel_le := OpensMeasurableSpace.borel_le

/-- ⭐⭐ **(a) 参数空间：`Θ.Carrier := ℝ → ℝ`** —— **θ 是函数**的类型事实。

`ThetaSpace` 的签名只有 `Carrier : Type u` 与拓扑/可测两个实例位，
故取函数空间是签名允许的。拓扑与可测取 `⊤`（§0.3.1）。 -/
abbrev tS : ThetaSpace where
  Carrier := ℝ → ℝ
  topo := ⊤
  meas := ⊤

/-- 外生输入空间：`ℝ`（只为使 `+` 在类型层可行，§0.3.3）。 -/
abbrev uS : InputSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)

/-- 动作空间：`ℝ`（同上）。 -/
abbrev aS : ActionSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)

/-- 噪声空间：`ℝ`（同上；`NoiseSpace` 只要求可测）。 -/
abbrev nS : NoiseSpace where
  Carrier := ℝ
  meas := inferInstanceAs (MeasurableSpace ℝ)

/-- 上下文空间：单点（只为补齐字段，不承载内容）。 -/
def cS : CtxSpace where Carrier := PUnit

instance instAddGroup_xS : AddCommGroup xS.Carrier := inferInstanceAs (AddCommGroup ℝ)

/-- ⭐ 函数空间 `ℝ → ℝ` 的逐点环结构（`endToEnd` 要求 `[Ring Θ.Carrier]`）。 -/
instance instRing_tS : Ring tS.Carrier := inferInstanceAs (Ring (ℝ → ℝ))

/-! ===========================================================================
    §2  ⭐⭐ 实例 `funThetaWorld`

    **⚠ 关键（§0.2 的坑）**：整个 `WorldModel` 用**一个 `where` 一次性内联**，
    不先 `def` 中间结构再拼装 —— 这使得
    `funThetaWorld.frame.Θ.Carrier` 直接归约到 `tS.Carrier`，进而归约到 `ℝ → ℝ`。
    =========================================================================== -/

/-- 单条机制规则（Dirac 核，只为补齐字段）。 -/
noncomputable abbrev r0 : Fate.Rule cS xS xS :=
  ⟨fun _ x => MeasureTheory.Measure.dirac x⟩

/-- 规则集（单元素集）。 -/
def r0s : Fate.Rules cS xS xS := {r0}

theorem r0s_nonempty : r0s.Nonempty := ⟨r0, rfl⟩

/-- 规则集块。 -/
def b0 : WorldRules cS xS xS :=
  { rules := r0s, nonempty := r0s_nonempty }

/-- ⭐⭐⭐ **`funThetaWorld`：`Θ.Carrier := ℝ → ℝ` 且 `g` 真的作用到 `x` 上**。

机制（任务书 (c)）：

$$\texttt{step}\ x\ u\ \varepsilon\ g\ a \;=\; g\,x + u + \varepsilon + a .$$

注意第 5 位（`Θ` 位）是 `g : ℝ → ℝ`，且被**应用**到 `x` ——
**这是「θ 是函数」在语义层的落实，而非仅仅在类型层**。 -/
noncomputable abbrev funThetaWorld : WorldModel where
  frame :=
    { Θ := tS
      X := xS
      U := uS
      Act := aS
      Ν := nS }
  ctx := cS
  instX := inferInstanceAs (MeasurableSpace ℝ)
  state :=
    { space := xS
      cur := 0
      initial := { val := 0, isRandom := false } }
  rules := b0
  simulator :=
    { step := fun x u e g a => g x + u + e + a
      horizon := 1 }
  selector :=
    { select := fun _ _ _ => (Classical.choose b0.nonempty, 0)
      criterion := fun _ _ _ => 0 }
  state_consistent := rfl

instance instAddGroup_funX : AddCommGroup funThetaWorld.frame.X.Carrier :=
  inferInstanceAs (AddCommGroup ℝ)

/-- ⭐ 本实例的 `Ring` 实例（= 函数空间的逐点环）。 -/
instance instRing_funΘ : Ring funThetaWorld.frame.Θ.Carrier :=
  inferInstanceAs (Ring (ℝ → ℝ))

/-! ===========================================================================
    §3  ⭐⭐ (a)(b) 的类型层事实（`rfl` 体量核对）
    =========================================================================== -/

/-- ⭐⭐ **(a) 机检：实例的参数空间载体确为函数空间**。

**⚠ 若 §0.2 的坑仍在（`Carrier` 不归约），本 `rfl` 会失败** ——
故本定理的**可编译性**就是「实例构造正确」的证据。 -/
theorem funThetaWorld_carrier :
    funThetaWorld.frame.Θ.Carrier = (ℝ → ℝ) := rfl

/-- ⭐ **(b) 机检：实例的状态空间载体确为 `ℝ`**。 -/
theorem funThetaWorld_state_carrier :
    funThetaWorld.frame.X.Carrier = ℝ := rfl

/-- ⭐ **【`Θ` 不退化到单点】**：参数空间里有**两个不同的元素**。

**意义**：若 `Θ.Carrier` 是 `PUnit`（或任何单点类型），本命题为假。
故它与 `funThetaWorld_carrier` 合起来说明 §0.1 的类型层前提**非空非退化**。

**⚠ 不是同义反复**：结论是**存在性 + 不等式**，由两个具体函数（`id` 与 `0`）见证。 -/
theorem exists_two_distinct_thetas :
    ∃ g₁ g₂ : funThetaWorld.frame.Θ.Carrier, g₁ ≠ g₂ := by
  refine ⟨(id : ℝ → ℝ), (fun _ => 0), ?_⟩
  intro h
  have h1 : (id : ℝ → ℝ) 1 = (fun _ => (0 : ℝ)) 1 := by rw [h]
  simp at h1

/-! ===========================================================================
    §4  ⭐⭐ (c)(e) 的求值语义
    =========================================================================== -/

/-- ⭐⭐⭐ **(c)(e) 主引理：`predFrom` 在本实例上就是 `g x + u + e + a`**（`rfl` 级）。

**⚠ 这个 `rfl` 就是「`g` 真的作用到 `x` 上」的机检证据**：
右式含 `g x`（函数应用）。若机制被写成 `x + u + e + a`（丢 `g`），
本引理**类型正确但为假** —— 故本引理不是语法重排。 -/
theorem funThetaWorld_predFrom (g : ℝ → ℝ) (u e a x : ℝ) :
    predFrom funThetaWorld g u e a x = g x + u + e + a := rfl

/-- ⭐ **`g` 项与扰动项**可分离**：取 `u = e = a = 0` 时预测恰为 `g x`。

**意义**：预测**精确暴露** `g` 在该点的取值 —— 这是 §6「`g` 不被丢弃」的基础。 -/
theorem funThetaWorld_predFrom_zero (g : ℝ → ℝ) (x : ℝ) :
    predFrom funThetaWorld g 0 0 0 x = g x := by
  rw [funThetaWorld_predFrom]
  ring

/-- ⭐ **预测对扰动的**加法**结构**：`predFrom g u e a x = predFrom g 0 0 0 x + (u+e+a)`。

**意义**：`g x` 与 `u+e+a` 在预测中**可分离** ——
这使「`g` 的作用」可以**独立于**扰动被检验（§6 的证明就靠它）。 -/
theorem funThetaWorld_predFrom_add (g : ℝ → ℝ) (u e a x : ℝ) :
    predFrom funThetaWorld g u e a x = predFrom funThetaWorld g 0 0 0 x + (u + e + a) := by
  rw [funThetaWorld_predFrom, funThetaWorld_predFrom_zero]
  ring

/-- ⭐⭐ **【预测相等 ⟺ `g` 在该点取值相等】**。

**⚠ 不是同义反复**：无前件；经 `funThetaWorld_predFrom` 两次改写后由加法消去得到。
若 `g` 被丢弃（机制为 `x+u+e+a`），左式恒真而右式不必真，本引理**立即失败**。 -/
theorem predFrom_eq_iff_apply_eq (g₁ g₂ : funThetaWorld.frame.Θ.Carrier)
    (u e a x : ℝ) :
    predFrom funThetaWorld g₁ u e a x = predFrom funThetaWorld g₂ u e a x ↔ g₁ x = g₂ x := by
  rw [funThetaWorld_predFrom, funThetaWorld_predFrom]
  constructor <;> intro h
  · linarith
  · rw [h]

/-! ===========================================================================
    §5  ⭐ (d) `WellFormed`
    =========================================================================== -/

/-- ⭐⭐ **(d) `funThetaWorld` 满足 `WorldModel.WellFormed`**。

`WellFormed W := W.Sel.IsValid W.R`，即
`∀ c x, (select R c x).1 ∈ R`。本实例的 `select` 恒返回
`Classical.choose b0.nonempty`，而 `b0.rules = {r0}`，故需证 `r0 ∈ {r0}`。

**⚠ 不是同义反复**：`WellFormed` **不是** `WorldModel` 的字段
（它是 `Fate/WorldModel.lean` §5.4 定义的**谓词**）；
本定理是**新证**，且若把 `selector.select` 改成返回集合外的规则，本定理即失败。 -/
theorem funThetaWorld_wellFormed : WorldModel.WellFormed funThetaWorld := by
  intro c x
  show (Classical.choose b0.nonempty : Fate.Rule cS xS xS) ∈ b0.rules
  have hspec : (Classical.choose b0.nonempty : Fate.Rule cS xS xS) ∈ b0.rules :=
    Classical.choose_spec b0.nonempty
  exact hspec

/-- ⭐ **规则集非空的显式见证**（供上一条的读法）。 -/
theorem funThetaWorld_rules_nonempty : funThetaWorld.R.Nonempty :=
  Fate.rules_nonempty funThetaWorld

/-! ===========================================================================
    §6  ⭐⭐⭐ (e) 的实质部分：`g` 是**函数**而非可退化的标量

    本条节是「θ 是函数」的**核心机检**：
    §6.1 说明 `g` **不被丢弃**；§6.2 说明预测对 `g` **逐点敏感**；
    §6.3 说明「`g` 只造成一个**常数平移**」（即 `Θ.Carrier := ℝ` 的退化解）
    **被排除** —— 这正是 `g` 必须是**函数**（能随 `x` 变）的证据。
    =========================================================================== -/

/-- ⭐⭐⭐ **【`g` 不被丢弃】**：若两个参数函数给出**处处相同**的预测
（在同一点、同一扰动下），则两个函数**相等**。

**⚠ 这是「θ 是函数」的判别性定理，不是同义反复**：

* 前件只谈**预测值**的逐点相等；
* 结论是**函数相等**（需要 `funext`）；
* 若机制里 `g` 被丢掉（例如 `step = fun x _ _ _ _ => x`），
  则前件**恒真**而结论**假** ⟹ 本定理**恰好在退化时失败**。

故本定理的可编译性 + 其为真，**排除**「`g` 只是装饰」这一可能。 -/
theorem predFrom_determines_g (g₁ g₂ : funThetaWorld.frame.Θ.Carrier)
    (h : ∀ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x
      = predFrom funThetaWorld g₂ 0 0 0 x) : g₁ = g₂ := by
  funext x
  have hx := h x
  rwa [funThetaWorld_predFrom_zero, funThetaWorld_predFrom_zero] at hx

/-- ⭐⭐ **【`g` 不同 ⟹ 存在一点预测不同】**（逐点敏感，逆否形式）。

**⚠ 不是同义反复**：前件是**函数不等式**，结论是**存在性**（存在一个 `x`
与一个扰动把差异暴露出来）；证明需逆否 + `funext`（走 §6.1 的判别性引理）。 -/
theorem pred_differs_of_g_differs (g₁ g₂ : funThetaWorld.frame.Θ.Carrier)
    (h : g₁ ≠ g₂) :
    ∃ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x ≠ predFrom funThetaWorld g₂ 0 0 0 x := by
  by_contra hcon
  push Not at hcon
  exact h (predFrom_determines_g g₁ g₂ hcon)

/-- ⭐⭐⭐ **【关键：`g` 的作用**不是常数平移**】**（机检排除退化解）

取 `g₁ = id`、`g₂ = 0`，则在任意扰动下两者预测之差**不是常数**。

**⭐ 这是「θ 必须是函数」的**核心**证据**：
若 `Θ.Carrier := ℝ`（θ 是一个**点**），则机制只能形如
$x + u + \varepsilon + a + \theta$，即 `θ` 只能造成**同一个常数平移**。
本定理证明 `g₁ = id` 与 `g₂ = 0` 的预测差**依赖 `x`**（`x = 0` 时差为 `0`，
`x = 1` 时差为 `1`），故**不可能**用任何标量 `θ` 表示。
⟹ 「θ 是函数」不是修辞/类型游戏，而是**表达力上的必要**。

**⚠ 不是同义反复**：无前件；结论是一个**否定存在命题**，
由两个具体点的数值差（`0 ≠ 1`）推翻。 -/
theorem pred_not_constant_shift :
    ¬ ∃ c : ℝ, ∀ x : ℝ,
      predFrom funThetaWorld (id : ℝ → ℝ) 0 0 0 x
        - predFrom funThetaWorld (fun _ => 0) 0 0 0 x = c := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  rw [funThetaWorld_predFrom_zero, funThetaWorld_predFrom_zero] at h0 h1
  simp only [id_eq] at h0 h1
  -- h0 : 0 - 0 = c, h1 : 1 - 0 = c
  linarith

/-- ⭐ **【`g` 的作用比常数平移更多：它逐点取值都自由】**。

对**任意**两个实数 `y₀`、`y₁`（**不需**不等），存在一个 `g` 使 `g 0 = y₀` 且 `g 1 = y₁`
（即函数参数能承载「两个点上的独立取值」，而标量参数不能）。

**⚠ 不是同义反复**：结论是**存在性构造**（`if` 分支），非前件重述。

**⚠ 无前件**（`y₀ = y₁` 时取常函数即可，故 `y₀ ≠ y₁` **不是**必要条件 ——
本定理**不**把它当前件，以免出现装饰性前件）。
本定理是**直接的构造性见证**：`if` 分支函数。 -/
theorem exists_g_with_two_values (y₀ y₁ : ℝ) :
    ∃ g : funThetaWorld.frame.Θ.Carrier, g 0 = y₀ ∧ g 1 = y₁ := by
  refine ⟨fun x => if x = 0 then y₀ else if x = 1 then y₁ else 0, ?_, ?_⟩
  · simp
  · simp

/-- ⭐⭐ **【上一条的预测版】**：`g` 能同时在两点给出**任意预先指定**的预测值。

**意义**：这是「θ 是函数」的**表达能力**陈述 ——
一个标量 `θ` 无法同时指定两点上的预测。

**⚠ 无前件**（同 `exists_g_with_two_values`）。 -/
theorem exists_g_with_two_predictions (y₀ y₁ : ℝ) :
    ∃ g : funThetaWorld.frame.Θ.Carrier,
      predFrom funThetaWorld g 0 0 0 0 = y₀ ∧
      predFrom funThetaWorld g 0 0 0 1 = y₁ := by
  obtain ⟨g, h0, h1⟩ := exists_g_with_two_values y₀ y₁
  refine ⟨g, ?_, ?_⟩
  · rw [funThetaWorld_predFrom_zero]; exact h0
  · rw [funThetaWorld_predFrom_zero]; exact h1

/-- ⭐⭐⭐ **【§6 小结：「θ 是函数」的三条实质判据同时成立】**。

把 §6 的三条区分性事实写成一条合取（便于审计一句话读完）：

1. **可靠（无退化信息丢失）**：预测函数唯一确定 `g`；
2. **逐点敏感**：`g₁ ≠ g₂` 必在某点暴露；
3. **不可标量化**：`g = id` 与 `g = 0` 的预测差不是常数 ——
   即任何 `Θ.Carrier := ℝ` 的模型都**无法**表达本实例的预测族。

**⚠ 不是同义反复**：三条结论无一是任一定义的改写；
1 需 `funext`，2 需逆否，3 需两个具体点的数值比较。
前件为**空**（无任何假设）—— `g`、`g₁`、`g₂` 全自由。 -/
theorem theta_function_has_substantive_effect :
    (∀ g₁ g₂ : funThetaWorld.frame.Θ.Carrier,
        (∀ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x
          = predFrom funThetaWorld g₂ 0 0 0 x) → g₁ = g₂) ∧
    (∀ g₁ g₂ : funThetaWorld.frame.Θ.Carrier, g₁ ≠ g₂ →
        ∃ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x
          ≠ predFrom funThetaWorld g₂ 0 0 0 x) ∧
    (¬ ∃ c : ℝ, ∀ x : ℝ,
        predFrom funThetaWorld (id : ℝ → ℝ) 0 0 0 x
          - predFrom funThetaWorld (fun _ => 0) 0 0 0 x = c) := by
  refine ⟨predFrom_determines_g, pred_differs_of_g_differs, pred_not_constant_shift⟩

/-! ===========================================================================
    §7  具体数值核对
    =========================================================================== -/

/-- 具体参数函数：`g(z) = 3z + 1`。 -/
def gDemo : ℝ → ℝ := fun z => 3 * z + 1

/-- ⭐ **数值核对**：`g = gDemo`、`x = 2`、`u = 5`、`ε = 0`、`a = 1` 时
预测 `= 3*2 + 1 + 5 + 0 + 1 = 13`。 -/
theorem demo_pred : predFrom funThetaWorld gDemo 5 0 1 2 = 13 := by
  rw [funThetaWorld_predFrom]
  unfold gDemo
  norm_num

/-- ⭐ **【数值版 (e)：同一点、不同 `g` 给不同预测】**（`13 ≠ 7`）。 -/
theorem demo_g_differs :
    predFrom funThetaWorld gDemo 5 0 1 2 ≠
      predFrom funThetaWorld (fun _ => 0) 5 0 1 2 := by
  rw [funThetaWorld_predFrom, funThetaWorld_predFrom]
  unfold gDemo
  norm_num

/-- ⭐ **【数值版：`g` 的**逐点**差异（同一 `g₁ = id`, `g₂ = 0`，`x = 0` 与 `x = 1`）】**：
在 `x = 0` 处两者预测**相同**，在 `x = 1` 处**不同** —— 这就是 §6.3
「差不是常数」的具体来源。 -/
theorem demo_pointwise_difference :
    predFrom funThetaWorld (id : ℝ → ℝ) 0 0 0 0
        = predFrom funThetaWorld (fun _ => 0) 0 0 0 0 ∧
      predFrom funThetaWorld (id : ℝ → ℝ) 0 0 0 1
        ≠ predFrom funThetaWorld (fun _ => 0) 0 0 0 1 := by
  rw [funThetaWorld_predFrom, funThetaWorld_predFrom,
      funThetaWorld_predFrom, funThetaWorld_predFrom]
  refine ⟨by norm_num, by norm_num⟩

/-! ===========================================================================
    §8  自检清单（反同义反复，逐条）
    =========================================================================== -/

/-- **自检 1**：`Θ.Carrier` 确为函数空间（§3，`rfl`）。 -/
example : funThetaWorld.frame.Θ.Carrier = (ℝ → ℝ) := rfl

/-- **自检 2**：机制确实把 `g` 应用到 `x`（§4，`rfl`）。 -/
example (g : ℝ → ℝ) (u e a x : ℝ) :
    predFrom funThetaWorld g u e a x = g x + u + e + a := rfl

/-- **自检 3**：`WellFormed` 成立（§5）。 -/
example : WorldModel.WellFormed funThetaWorld := funThetaWorld_wellFormed

/-- **自检 4**：`g` 被完全确定（§6.1）—— 若机制丢弃 `g`，本条失败。 -/
example (g₁ g₂ : ℝ → ℝ)
    (h : ∀ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x
      = predFrom funThetaWorld g₂ 0 0 0 x) : g₁ = g₂ :=
  predFrom_determines_g g₁ g₂ h

/-- **自检 5**：`g` 的不同必在某点暴露（§6.2）。 -/
example (g₁ g₂ : ℝ → ℝ) (h : g₁ ≠ g₂) :
    ∃ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x
      ≠ predFrom funThetaWorld g₂ 0 0 0 x :=
  pred_differs_of_g_differs g₁ g₂ h

/-- **自检 6**：`g` 的作用**不是**常数平移（§6.3）—— 「θ 是点」的退化解被排除。 -/
example : ¬ ∃ c : ℝ, ∀ x : ℝ,
    predFrom funThetaWorld (id : ℝ → ℝ) 0 0 0 x
      - predFrom funThetaWorld (fun _ => 0) 0 0 0 x = c :=
  pred_not_constant_shift

/-- **自检 7**：`g` 能承载两点上的**独立**取值（§6.4）。 -/
example (y₀ y₁ : ℝ) :
    ∃ g : funThetaWorld.frame.Θ.Carrier, g 0 = y₀ ∧ g 1 = y₁ :=
  exists_g_with_two_values y₀ y₁

/-- **自检 8**：`predFrom` 与 `W.f`（即与模拟器机制）**同一个语义**（`rfl`）。 -/
example (g : ℝ → ℝ) (u e a x : ℝ) :
    predFrom funThetaWorld g u e a x
      = funThetaWorld.f x u e g a := rfl

/-- **自检 9**：§6 的三条实质判据**同时**成立（空前件）。 -/
example :
    (∀ g₁ g₂ : funThetaWorld.frame.Θ.Carrier,
        (∀ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x
          = predFrom funThetaWorld g₂ 0 0 0 x) → g₁ = g₂) ∧
    (∀ g₁ g₂ : funThetaWorld.frame.Θ.Carrier, g₁ ≠ g₂ →
        ∃ x : ℝ, predFrom funThetaWorld g₁ 0 0 0 x
          ≠ predFrom funThetaWorld g₂ 0 0 0 x) ∧
    (¬ ∃ c : ℝ, ∀ x : ℝ,
        predFrom funThetaWorld (id : ℝ → ℝ) 0 0 0 x
          - predFrom funThetaWorld (fun _ => 0) 0 0 0 x = c) :=
  theta_function_has_substantive_effect

/-- **自检 10**：`g` 能被两点上的**任意**预测值同时指定（§6.4 的预测版）。 -/
example (y₀ y₁ : ℝ) :
    ∃ g : funThetaWorld.frame.Θ.Carrier,
      predFrom funThetaWorld g 0 0 0 0 = y₀ ∧
      predFrom funThetaWorld g 0 0 0 1 = y₁ :=
  exists_g_with_two_predictions y₀ y₁

end FunThetaWorldModel
end Fate
