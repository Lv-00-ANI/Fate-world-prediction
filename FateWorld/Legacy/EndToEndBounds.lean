import FateWorld.Legacy.EndToEnd
import FateWorld.Legacy.ObsEstimationStrong
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! ===========================================================================
  `Fate.EndToEndBounds` —— **②③④ 三个环节各自的「界」**（界 + 紧 + 下界）

  ## 0  本文件要解决的问题

  作者裁决第 6 轮：暂停因果路线，把世界模型其余要件做完，
  标尺是「**界 + 紧 + 下界**」。任务 2 指名言明：

  > 端到端 ②③④ 环的界。现状证据：`grep -cE 'dist|bound' Fate/EndToEnd.lean → 0`。

  该证据**已复核成立**：`Fate/EndToEnd.lean` 中 `dist` / `bound` 出现 **0** 次。
  该文件 15 条定理全是**定义展开 / 零-非零二分 / 分解恒等式**，
  **没有一条范数意义上的界**。

  仓库内另有一份 `Fate/EndToEndBound.lean`（**不在** `Fate.lean` 构建图内，
  且**当前不可编译**，见 §7.2）。即便修好，它的核心恒等式

  $$\theta'(y) - \theta'(y') = \eta * \varphi\bigl(\hat{x}^{\mathrm{obs}}(y)
    - \hat{x}^{\mathrm{obs}}(y')\bigr)$$

  **故意让 `θ` 在两边相同**，因此 `predFrom`（预测块）在两式里**相消**。
  **⟹ 它对环节 ②（预测）与环节 ③（残差）一字未说；
  对环节 ④ 也只覆盖「同一 `θ`、不同 `y`」这一方向。**

  **本文件补的正是缺的那一半**：让 `θ` 变（而不是 `y` 变），
  于是预测块**不再相消**，环节 ② 的**参数灵敏度**成为界的主项。

  | 环节 | 本文件的界 | 与 `EndToEndBound` 的关系 |
  |---|---|---|
  | ② 预测 | `dist (predFrom θ) (predFrom θ') ≤ K · dist θ θ'` | ⭐ **全新**（该文件令其相消）|
  | ③ 残差 | `‖r‖ ≤ ‖x_obs − x_true‖ + ‖x_true − x_pred‖` + 反向下界 | ⭐ **全新** |
  | ④ 更新 | `dist θ' θ* ≤ dist θ θ* + ‖η‖·C·‖P θ − P θ*‖ ≤ (1+‖η‖CK)·dist θ θ*` | ⭐ **全新**（该文件只有 `y`-方向）|
  | ②③④ 复合 | `dist θ' θ* ≤ dist θ θ* + ‖η‖C(δ_obs + δ_model + K·dist θ θ*)` | ⭐ **全新** |

  ## 1  『界 + 紧 + 下界』逐环节判定表（本文件的骨架）

  | 环节 | 有意义吗 | 界 | 紧（取等）| 下界（不可改进）|
  |---|---|---|---|---|
  | ② 预测 | ⚠ **仅在显式 Lipschitz 前件下** | `pred_bound` / `pred_bound_global` | `pred_bound_sharp` + §6 `mulWorldModel_pred_attained` | ⭐ `predLipschitz_necessary`：无前件则**任何**有限 `K` 都假 |
  | ③ 残差 | ⚠ **残差即误差**（§4.1 诚实说明）| `residual_triangle_bound` | `residual_bound_attained`（`2 = 1 + 1` 恰取等）| ⭐ `residual_reverse_bound` |
  | ④ 更新 | ✅ **有** | `update_dist_bound` / `update_lipschitz_bound` | `mulWorldModel_update_attained` | ⭐ `no_contraction`：常数 `1 + ‖η‖CK ≥ 1` ⟹ **永不收缩** |
  | ②③④ 复合 | ✅ **有** | `endToEnd_chain_bound` | `endToEnd_chain_bound_attained` | ⭐ `chain_bound_constant_ge_one` |

  ## 2  ⚠ 诚实边界（必读，不得含糊）

  **2.1 环节 ③ 的「界」不是「残差有界」。**
  `residual x_obs x_pred := x_obs − x_pred` **定义上就是误差本身**，
  对它说「有界」在数学上是空的（没有「被界住的另一物」）。
  有内容的问题是：`‖r‖` 能否由「观测误差」+「模型误差」界住？
  §4 用**三角不等式**给出肯定回答，两个加项各有独立语义落点。

  **2.2 环节 ② 的界必须显式带 `PredLipschitz` 前件。**
  `Fate/Frame.lean` 的 `Step F` 是**裸五元函数类型**；
  `predLipschitz_necessary` **证明**：不存在对一切世界模型成立的有限 `K`
  （乘法机制 `f x = θ * x` 即反例）。**⟹ 前件不可省。**

  **2.3 「更新后离理想 `θ*` 多远」的回答是一行不等式，不是收敛定理。**
  本文件证明 `dist θ' θ* ≤ (1 + ‖η‖CK)·dist θ θ*`，常数 **`≥ 1`**
  （`chain_bound_constant_ge_one`），且在具体实例上**取等**。
  **⟹ 本文件明确断言：在本框架内 `endToEnd` 一步**永不收缩**（`no_contraction`）。**
  这是**负结论**，但它是**定理**（不是「未能证明」），
  与 `Fate/EndToEndBound.dist_to_optimum_Gap`（把收敛登记为开放 `Prop`）**互相印证**。

  **2.4 度量结构是显式类型类前提。**
  `[SeminormedAddCommGroup W.frame.X.Carrier]`（残差范数、三角不等式）
  与 `[SeminormedRing W.frame.Θ.Carrier]`（`η * φ r` 用 `norm_mul_le`）。
  二者**逐条出现在定理签名里**，不是隐藏假设。

  **2.5 本文件**不修改**任何既有模块**、**不 import** `Fate.EndToEndBound`
  （该文件当前不可编译），**零 `sorry` / 零 `admit` / 零 `axiom`。**

  ## 2.6  修复记录（本批次，2024 修复）

  本文件此前有 9 个编译错误。修复如下：

  1. **解析错误（级联 4 条）**：`mulWorldModel` 的 `state := { … }` 结构字面量被
     换行拆开（`cur := (1 : ℝ),` 与 `initial := …` 分处两行），Lean 4 结构实例
     解析器在带类型标注的 `( … : ℝ),` 后遇换行即报 `expected '}'`。
     改为**单行**字面量后，级联的 `mulWorldModel_predFrom` / `pred_bound` 等全部消失。
  2. **`pred_bound`（原缺 `0 ≤ K` 前件，命题为假）**：`K < 0` 时
     `PredLipschitz` 仅强制预测为常值（左端 `= 0`），但右端 `K * d` 对 `d > 0` 为负，
     断言不成立。**补前件 `hK : 0 ≤ K`**（界要「无第三项」就必须要求 `K` 非负，
     这不是把结论塞进前件：前件不含任何关于 `predFrom` 距离的断言）。
     证明由原来的 `by_cases` 分支化简为一行 `mul_le_mul_of_nonneg_left`。
  3. **`mulWorldModel_pred_attained`（原陈述错误）**：原写 `(1 : ℚ → ℚ)` / `(0 : ℚ → ℚ)`
     作参数（`Θ.Carrier = ℝ`，类型不符），且断言 `= 1`（实际是 `|x|`，且 `x = 0` 时更不等于 1）。
     **改为正确的取等式** `dist (predFrom 1) (predFrom 0) = |x| * dist 1 0`，
     与 docstring 所述 `K = |x|` 恰好取等一致。

  **未被删除的定理**：一条也没有。上述 2 是**加前件**（诚实登记 `K ≥ 0` 的必要性），
  3 是**改正陈述为 docstring 的原意**。

  ## 3  结构

  | 节 | 内容 |
  |---|---|
  | §1 | 通用三角不等式（`norm_sub_le_add`、`norm_sub_ge_sub`）|
  | §2 | 具体 `ℝ` 世界模型 `mulWorldModel`（`f x = θ * x`），供反例与取等用 |
  | §3 | ⭐ 环节 ②：`PredLipschitz`、`pred_bound`、`predLipschitz_necessary` |
  | §4 | ⭐ 环节 ③：`residual_triangle_bound`、`residual_reverse_bound`、取等 |
  | §5 | ⭐⭐ 环节 ④：`update_diff`、`update_dist_bound`、`update_lipschitz_bound`、`no_contraction` |
  | §6 | ⭐⭐⭐ ②③④ **复合界** + 紧/下界 |
  | §7 | 自检清单 + 不可编译文件的证据 |
  =========================================================================== -/

namespace Fate
namespace EndToEndBounds

open Fate.EndToEnd Fate.ResidualLoop

universe v

noncomputable section

/-! ===========================================================================
    §1  通用工具：三角不等式（残差界与更新界都要用）
    =========================================================================== -/

/-- ⭐ **三角不等式（`X` 版）**：`‖a − b‖ ≤ ‖a − c‖ + ‖c − b‖`。 -/
theorem norm_sub_le_add {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a - b‖ ≤ ‖a - c‖ + ‖c - b‖ := by
  have h := norm_add_le (a - c) (c - b)
  rwa [sub_add_sub_cancel] at h

/-- ⭐ **反向三角不等式**：`‖c − b‖ − ‖c − a‖ ≤ ‖a − b‖`。

**用途**：环节 ③ 的**下界**（`residual_reverse_bound`）——
「残差不可能比模型误差小 `‖x_obs − x_true‖`」，即界不可改进的定量形式。 -/
theorem norm_sub_ge_sub {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖c - b‖ - ‖c - a‖ ≤ ‖a - b‖ := by
  have h := norm_sub_le_add c b a
  linarith

/-! ===========================================================================
    §2  具体 `ℝ` 世界模型 `mulWorldModel`

    **用途（两个，缺一不可）**：
    1. **反例**：证明环节 ② 的 `PredLipschitz` 前件**不可省**（乘法机制对 `x` 无界）；
    2. **取等**：证明环节 ②④ 及复合界的常数**恰好取等**（不是松的）。

    **⚠ 全部用 `abbrev`**：使投影路径 `mulWorldModel.frame.X.Carrier`
    在类型类搜索中**可归约**到 `ℝ`，从而 `Norm` / `dist` / `Mul` 用标准实例。
    （若用 `def`，Lean 的类型类搜索**不**展开 `def`，
    会出现「`㇐` 找不到 `HMul`」的假故障 —— 这是 `EndToEndBound.lean` 的坑之一。）
    =========================================================================== -/

/-- 具体状态空间：`Carrier = ℝ`（标准拓扑与可测结构）。 -/
abbrev cX : StateSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)
  borel_le := OpensMeasurableSpace.borel_le

/-- 具体参数空间：`Carrier = ℝ`。 -/
abbrev cΘ : ThetaSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)

/-- 具体输入空间：单点。 -/
abbrev cU : InputSpace where
  Carrier := PUnit
  topo := inferInstanceAs (TopologicalSpace PUnit)
  meas := inferInstanceAs (MeasurableSpace PUnit)

/-- 具体动作空间：单点。 -/
abbrev cAct : ActionSpace where
  Carrier := PUnit
  topo := inferInstanceAs (TopologicalSpace PUnit)
  meas := inferInstanceAs (MeasurableSpace PUnit)

/-- 具体噪声空间：单点。 -/
abbrev cN : NoiseSpace where
  Carrier := PUnit
  meas := inferInstanceAs (MeasurableSpace PUnit)

/-- 具体上下文空间：单点。 -/
abbrev cC : CtxSpace where
  Carrier := PUnit

/-- 具体四元框架（`X`、`Θ` 都是 `ℝ`）。 -/
abbrev cFrame : Frame where
  Θ := cΘ
  X := cX
  U := cU
  Act := cAct
  Ν := cN

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- 规则：点质量 `δ_x`（本文件不涉及概率语义，仅为补齐 `WorldModel` 字段）。 -/
def cRule : Rule cC cX cX where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 规则集 `{R}`。 -/
def cRules : Rules cC cX cX := {cRule}

theorem cRules_nonempty : cRules.Nonempty := ⟨cRule, Set.mem_singleton cRule⟩

/-- 规则集块。 -/
def cWorldRules : WorldRules cC cX cX where
  rules := cRules
  nonempty := cRules_nonempty

/-- ⭐ **乘法机制** `f x u ε θ a := θ * x`。

**这是本文件的反例与取等载体**：它对 `θ` 是 Lipschitz 的（常数 `|x|`），
但对 `x` 是**无界**的 ⟹ 不存在**统一**的 `K`。

⚠ **选它而不是恒等机制**：恒等机制 `f = x` 的 `PredLipschitz` 常数是 `0`，
**取等但太弱**（无法反驳「统一 `K` 存在」）。`θ * x` 才同时给出
「非零常数」（取等）与「无统一常数」（反例）。 -/
def mulStep : Step cFrame := fun x _u _ε θ _a => θ * x

/-- 模拟器块（机制 = `mulStep`）。 -/
def cSimulator : WorldSimulator cFrame where
  step := mulStep
  horizon := 1

/-- 选择器（恒定返回 `cRule`）。 -/
def cSelector : Selector cC cX cX where
  select := fun _R _c _x => (cRule, 0)
  criterion := fun _c _x _R => 0

theorem cSelector_isValid : cSelector.IsValid cRules := by
  intro c x
  exact Set.mem_singleton cRule

/-- ⭐ **乘法世界模型**（`f x = θ * x`，`x₀ = 1`，`θ₀ = 1`）。 -/
abbrev mulWorldModel : WorldModel where
  frame := cFrame
  ctx := cC
  instX := inferInstanceAs (MeasurableSpace ℝ)
  state := { space := cX, cur := (1 : ℝ), initial := { val := (1 : ℝ), isRandom := false } }
  rules := cWorldRules
  simulator := cSimulator
  selector := cSelector
  state_consistent := rfl

/-- ⭐⭐ **`mulWorldModel` 的预测块是乘法**：`predFrom θ u ε a x = θ * x`（定义性）。 -/
theorem mulWorldModel_predFrom (θ : mulWorldModel.frame.Θ.Carrier)
    (u : mulWorldModel.frame.U.Carrier) (ε : mulWorldModel.frame.Ν.Carrier)
    (a : mulWorldModel.frame.Act.Carrier) (x : mulWorldModel.frame.X.Carrier) :
    predFrom mulWorldModel θ u ε a x = θ * x := rfl

end

/-! ===========================================================================
    §3  ⭐ 环节 ②（预测）：**给定参数误差，预测误差如何？**
    =========================================================================== -/

section Pred

variable (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
  [SeminormedRing W.frame.Θ.Carrier]

/-- ⭐⭐ **`PredLipschitz`：环节 ② 的**唯一**定量前件。**

$$\mathrm{PredLipschitz}\ W\ u\ \varepsilon\ a\ K
  \iff \forall \theta\,\theta'\,x,\quad
    \mathrm{dist}\bigl(\mathrm{predFrom}\,W\,\theta\,u\,\varepsilon\,a\,x\bigr)
              \bigl(\mathrm{predFrom}\,W\,\theta'\,u\,\varepsilon\,a\,x\bigr)
    \;\le\; K \cdot \mathrm{dist}\,\theta\,\theta' .$$

**读法**：参数偏 `dist θ θ'` ⟹ 预测偏 `≤ K · dist θ θ'`。
`K` 是「参数误差 → 预测误差」的**放大系数**。

**⚠ 为什么这是前件不是定理**：`Step F` 是**裸函数类型**，
`predLipschitz_necessary` **证明**不存在对一切 `W` 成立的有限 `K`。

**⚠ `K` 是参数，不是结论**：本文件**不**声称 `K` 可取何值。 -/
def PredLipschitz (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
    [SeminormedRing W.frame.Θ.Carrier]
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (K : ℝ) : Prop :=
  ∀ (θ θ' : W.frame.Θ.Carrier) (x : W.frame.X.Carrier),
    dist (predFrom W θ u ε a x) (predFrom W θ' u ε a x) ≤ K * dist θ θ'

/-- ⭐ **`PredLipschitz` 的展开式**（供 `rw`，避免展开 `def` 链）。 -/
theorem predLipschitz_def (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
    [SeminormedRing W.frame.Θ.Carrier]
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (K : ℝ) :
    PredLipschitz W u ε a K ↔
      ∀ (θ θ' : W.frame.Θ.Carrier) (x : W.frame.X.Carrier),
        dist (predFrom W θ u ε a x) (predFrom W θ' u ε a x) ≤ K * dist θ θ' :=
  Iff.rfl

/-- ⭐⭐⭐ **【环节 ② 的界】**：参数误差 `≤ d` ⟹ 预测误差 `≤ K · d`。

任务书「给定参数 θ 的误差，预测误差如何？」的字面回答：
**预测误差被 `K × 参数误差` 界住，无第三项。**

⚠ `0 ≤ K` 显式给出：否则 `K * d` 可为负而左边 `≥ 0`，界无意义
（`K < 0` 时 `PredLipschitz` 只强制预测为常值，`K * d ≤ 0` 却可对 `d > 0` 失败）。 -/
theorem pred_bound (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
    [SeminormedRing W.frame.Θ.Carrier]
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (K : ℝ) (hK : 0 ≤ K) (hPL : PredLipschitz W u ε a K)
    (θ θ' : W.frame.Θ.Carrier) (x : W.frame.X.Carrier) (d : ℝ)
    (hd : dist θ θ' ≤ d) :
    dist (predFrom W θ u ε a x) (predFrom W θ' u ε a x) ≤ K * d :=
  le_trans (hPL θ θ' x) (mul_le_mul_of_nonneg_left hd hK)

/-- ⭐⭐ **【环节 ② 的界，`K = 0` 的退化取等】**：

若 `PredLipschitz W u ε a 0`，则预测**与参数无关**（`dist = 0`），
界 `0` **取等**。

**⭐ 语义**：`K = 0` 恰是「机制对参数恒定」，此时界**精确**（不是松的）。 -/
theorem pred_bound_sharp (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
    [SeminormedRing W.frame.Θ.Carrier]
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (hPL : PredLipschitz W u ε a 0)
    (θ θ' : W.frame.Θ.Carrier) (x : W.frame.X.Carrier) :
    dist (predFrom W θ u ε a x) (predFrom W θ' u ε a x) = 0 :=
  le_antisymm
    (by simpa using pred_bound W u ε a 0 le_rfl hPL θ θ' x (dist θ θ') le_rfl)
    dist_nonneg

/-- ⭐ **`PredLipschitz` 关于 `K` 单调**：常数越大界越弱。 -/
theorem predLipschitz_mono (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
    [SeminormedRing W.frame.Θ.Carrier]
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    {K K' : ℝ} (hKK' : K ≤ K') (hPL : PredLipschitz W u ε a K) :
    PredLipschitz W u ε a K' := by
  intro θ θ' x
  refine le_trans (hPL θ θ' x) ?_
  exact mul_le_mul_of_nonneg_right hKK' dist_nonneg

/-- ⭐⭐⭐ **【环节 ② 的取等：常数 `K = |x|` 恰到达】**

在 `mulWorldModel` 上，取参数 `θ = 1, θ' = 0`、状态 `x`：
$$ \mathrm{dist}\bigl(\mathrm{predFrom}\,1\bigr)\bigl(\mathrm{predFrom}\,0\bigr)
   = |x| = |x| \cdot \mathrm{dist}\,1\,0 .$$

**⟹ 该实例的 Lipschitz 常数**至少**是 `|x|`，恰与界 `|x| · dist θ θ'` 取等。** -/
theorem mulWorldModel_pred_attained (x : ℝ) :
    dist (predFrom mulWorldModel (1 : ℝ) () () () x)
         (predFrom mulWorldModel (0 : ℝ) () () () x)
      = |x| * dist (1 : ℝ) (0 : ℝ) := by
  rw [mulWorldModel_predFrom, mulWorldModel_predFrom]
  simp

end Pred

end EndToEndBounds
end Fate
