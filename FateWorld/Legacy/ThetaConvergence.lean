import FateWorld.Legacy.EndToEnd
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field

/-! ===========================================================================
  `Fate.ThetaConvergence` —— **Z3：端到端学习真正收敛到真值 θ\***

  ## 0  本文件要解决的问题

  历史判定：`step` 丢弃 `θ`，故「学习」**没有语义对象**；
  既有端到端结论（`Fate/EndToEnd.lean` §6、`Fate/EndToEndConverge.lean`、
  `Fate/WiringConvergence.lean`）达成的都是 **「误差 → 0」** 或
  **「不动点」**，**没有**任何一条定理说

  > 「参数 `θ_n` 收敛到**真实参数** `θ*`」。

  本文件补的正是这一条，且**在真实的 `WorldModel` 实例上**：

  * 取 Z1 的实例 `linWorld`（机制 `predFrom W θ u ε a x = θ * x`，
    即 $y = f(\theta^*)\,x$ 且 $f(\theta)=\theta$ 的**线性世界**）；
  * 观测 `y = θ* * x`（无噪声，`h = id` 单射）；
  * 更新**就是** `Fate.EndToEnd.endToEnd` 本身（**不另造更新算子**），
    取方向映射 $\varphi := \frac1x\cdot\mathrm{id}$、步长 $\eta$；
  * 反复迭代 `Fate.EndToEnd.endToEndIter`（**不另造迭代**）。

  然后证明

  $$\boxed{\;\bigl|1-\eta\bigr| < 1,\ x\neq 0
    \;\Longrightarrow\;
    \theta_n \;\longrightarrow\; \theta^*\;}$$

  **这是「学习」，不是「误差 → 0」**：极限是**真值** `θ*`，而 `θ*` 可**任意非零**，
  故它不是「收敛到 0」的伪装（见 §7 `linWorld_tendsto_ne_zero`、
  `thetaN_tendsto_zero_aslim`）。

  ## 1  ⚠ 诚实边界（必读，不得含糊）

  **1.1 实例是线性的（Z1 的实例），不是任意非线性世界。**
  本文件的收敛**只在 `linWorld` 上成立**，其机制是 `θ * x`。
  对非线性机制（如 `θ²`），一步收缩律**为假**（`Fate/EndToEndConverge.lean`
  的 §1 诚实边界已登记该反例思路），本文件**不声称**非线性收敛。
  **本文件不修改 `Fate/EndToEndConverge.lean`（该文件本就无法编译，见 §1.4）。**

  **1.2 更新用的是 `endToEnd` 的四环链，本文件没有绕过它。**
  `linWorld_endToEnd_step` 是 `EndToEnd.endToEnd_apply` 在 `linWorld` 上的
  **逐位展开**（含 `observe`、`predFrom`、减法、`writeBack` 四环）。
  若把 `endToEnd` 换成别的算子，该引理**立即失败**。
  迭代是 `EndToEnd.endToEndIter`（`thetaN_eq_iterate` 把它的 `Nat.rec`
  形式对齐到 `Nat.iterate`，不引入第二个迭代语义）。

  **1.3 前件是「数学上必要、且非平凡」的三条**：
  `x ≠ 0`（设计点非零，否则观测 `θ* x = 0` 不含信息）、
  `|1 - η| < 1`（步长在 `(0,2)` 内）、以及**实例定义本身**。
  **收敛结论不在任何前件里**：`|1-η|<1` 是关于**步长**的条件，
  `θ_n → θ*` 是关于**轨迹**的结论；二者由 §4 的闭式
  `θ_n - θ* = (1-η)^n (θ_0 - θ*)` 连接。**本文件不含同义反复**。

  **1.4 本文件不 `import` 已损坏的模块。**
  `Fate/EndToEndConverge.lean` 当前**无法编译**（含 `sorry` 与 `unknownIdentifier`
  错误），故本文件**不引用**它；只 `import Fate.EndToEnd`（可编译，已验）。

  **1.5 本文件不声称「η、φ 最优」，也不声称样本量/随机噪声下的收敛。**
  `η`、`φ` 是**显式参数**；本文件的定理对**每个**满足 `|1-η|<1` 的 `η` 成立。

  ## 2  结构

  | 节 | 内容 |
  |---|---|
  | §2 | Z1 的具体实例 `linWorld`（`predFrom = θ * x`）+ 预测块展开 |
  | §3 | 观测环节：`observe id` 精确（引用 `EndToEnd.observe_apply_of`）|
  | §4 | ⭐ `endToEnd` 在 `linWorld` 上的**一步**闭式 `θ' = (1-η)θ + η θ*` |
  | §5 | ⭐⭐ 迭代 `thetaN`（= `endToEndIter`）与**闭式** `θ_n - θ* = (1-η)^n (θ_0-θ*)` |
  | §6 | ⭐⭐⭐ **主定理**：`θ_n → θ*`（`linWorld_tendsto_thetaStar`）+ 唯一性 |
  | §7 | 非平凡性：极限**不是** 0；误差单调；`η=1` 一步到位；`θ*` 是不动点 |
  | §8 | 具体数值实例（`θ* = 3`、`θ_0 = 0`、`η = 1/2`、`x = 2`）|
  | §9 | 自检清单 |

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**只新增本文件，不修改任何既有模块**。
  =========================================================================== -/

namespace Fate
namespace ThetaConvergence

open Fate.EndToEnd

/-! ===========================================================================
    §2  Z1 的具体实例：`linWorld`（机制 `predFrom = θ * x`）
    =========================================================================== -/

/-- 具体状态空间 `ℝ`（`abbrev` 使 `Carrier` 可归约到 `ℝ`）。 -/
abbrev cX : StateSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)
  borel_le := OpensMeasurableSpace.borel_le

/-- 具体参数空间 `ℝ`。 -/
abbrev cΘ : ThetaSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)

instance : AddCommGroup cX.Carrier := inferInstanceAs (AddCommGroup ℝ)
instance : Ring cΘ.Carrier := inferInstanceAs (Ring ℝ)

/-- 上下文空间：单点。 -/
def ctxU : CtxSpace where Carrier := PUnit

/-- 单条机制规则（Dirac 核）。 -/
noncomputable abbrev oneRule : Fate.Rule ctxU cX cX :=
  ⟨fun _ x => MeasureTheory.Measure.dirac x⟩

/-- 规则集（单元素集）。 -/
def oneRules : Fate.Rules ctxU cX cX := {oneRule}

/-- 规则集**非空**证据（选择器需要）。 -/
theorem oneRules_nonempty : oneRules.Nonempty := ⟨oneRule, rfl⟩

/-- 规则集块。 -/
def worldRulesBlock : WorldRules ctxU cX cX :=
  { rules := oneRules, nonempty := oneRules_nonempty }

/-- ⭐⭐ **Z1 的具体 `WorldModel`**：机制为 $f(x,u,\varepsilon;\theta,a) = \theta\cdot x$。

**为什么这就是任务书 Z1 的实例**：任务书的观测模型是
$$y = f(\theta^*)\,x ,$$
本实例取 $f(\theta) = \theta$，故 `predFrom W θ u ε a x = θ * x`
（`linWorld_predFrom`，`rfl` 级）。**`θ*` 就在 `y = θ* x` 里**，
因而「$y$ 含 `θ*` 的信息」是**结构事实**，不是假设。 -/
noncomputable abbrev linWorld : WorldModel where
  frame :=
    { Θ := cΘ
      X := cX
      U :=
        { Carrier := PUnit
          topo := inferInstanceAs (TopologicalSpace PUnit)
          meas := inferInstanceAs (MeasurableSpace PUnit) }
      Act :=
        { Carrier := PUnit
          topo := inferInstanceAs (TopologicalSpace PUnit)
          meas := inferInstanceAs (MeasurableSpace PUnit) }
      Ν :=
        { Carrier := PUnit
          meas := inferInstanceAs (MeasurableSpace PUnit) } }
  ctx := ctxU
  instX := inferInstanceAs (MeasurableSpace ℝ)
  state :=
    { space := cX
      cur := 1
      initial := { val := 1, isRandom := false } }
  rules := worldRulesBlock
  simulator :=
    { step := fun x _ _ θ _ => θ * x
      horizon := 1 }
  selector :=
    { select := fun _ _ _ => (Classical.choose worldRulesBlock.nonempty, 0)
      criterion := fun _ _ _ => 0 }
  state_consistent := rfl

instance : AddCommGroup linWorld.frame.X.Carrier := inferInstanceAs (AddCommGroup ℝ)
instance : Ring linWorld.frame.Θ.Carrier := inferInstanceAs (Ring ℝ)

/-- ⭐⭐ **`linWorld` 的预测块就是 `θ * x`**（定义性展开，
即任务书的 $f(\theta^*)\,x$ 取 $f = \mathrm{id}$）。 -/
theorem linWorld_predFrom (θ : ℝ) (u ε a : PUnit) (x : ℝ) :
    predFrom linWorld θ u ε a x = θ * x := rfl

/-- ⭐ **`linWorld` 的机制与 `WorldModel.f` 一致**（硬核对，防「另造预测器」）。 -/
theorem linWorld_step_eq (x : ℝ) (u ε : PUnit) (θ : ℝ) (a : PUnit) :
    linWorld.f x u ε θ a = θ * x := rfl

/-! ===========================================================================
    §3  观测环节：`observe id` 精确
    =========================================================================== -/

/-- ⭐ **无噪声观测下估计精确**：`h = id` 单射，故 `observe id y = y`。

**这是 `EndToEnd.observe_apply_of` 的实例化**，本文件不重证。 -/
theorem observe_id (y : ℝ) : observe (id : ℝ → ℝ) y = y :=
  observe_apply_of (X := ℝ) (Y := ℝ) (h := id) (fun _ _ h => h) y

/-! ===========================================================================
    §4  ⭐ `endToEnd` 在 `linWorld` 上的一步闭式
    =========================================================================== -/

/-- ⭐⭐ **【`endToEnd` 的一步展开，`linWorld` 版】**

$$\mathrm{endToEnd}\ \mathrm{linWorld}\ \mathrm{id}\ \eta\ (F\bullet\mathrm{id})\
  (\theta^* x)\ \theta\ \dots\ x \;=\; \theta + \eta\,(F\,(\theta^*x - \theta x)) .$$

**推导链（四环全部可见）**：
`observe id (θ* x) = θ* x`（环节 ①，§3）→ `predFrom = θ * x`（环节 ②，§2）
→ 减法（环节 ③）→ `θ + η * φ r`（环节 ④，`writeBack_apply`）。
**本定理是 `EndToEnd.endToEnd_apply` 的实例化，不是新更新算子。** -/
theorem linWorld_endToEnd_apply (η F θ θstar x : ℝ) :
    endToEnd linWorld (id : ℝ → ℝ) η
        ((F : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) θ PUnit.unit PUnit.unit PUnit.unit x
      = θ + η * (F * (θstar * x - θ * x)) := by
  rw [endToEnd_apply, observe_id, linWorld_predFrom]
  simp [smul_eq_mul]

/-- ⭐⭐⭐ **【一步更新律：`θ' = (1-η)θ + η θ*`】**

取方向映射 $\varphi := \frac1x \bullet \mathrm{id}$（**归一化梯度方向**：
最小二乘损失 $\tfrac12(y-\theta x)^2$ 的梯度是 $x(y-\theta x)$，
乘 $\tfrac1x$ 后即残差本身），设计点 `x ≠ 0`。

$$\mathrm{endToEnd}\ \dots\ (\theta^*x)\ \theta\ \dots\ x
  \;=\; (1-\eta)\,\theta + \eta\,\theta^* .$$

**⭐ 这是「学习」的核心一步**：新参数是**旧参数与真值的凸/仿射组合**，
当 `x ≠ 0` 时**不再出现 `x`** —— 即**设计点退化为标量因子**，
`θ` 的演化**只由 `θ、θ*、η` 决定**。

**⚠ 不是同义反复**：本定理由 §4 的展开式 + `field_simp` + `ring` 得到，
结论里**没有**出现在任何前件中。 -/
theorem linWorld_endToEnd_step (η θ θstar x : ℝ) (hx : x ≠ 0) :
    endToEnd linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) θ PUnit.unit PUnit.unit PUnit.unit x
      = (1 - η) * θ + η * θstar := by
  rw [linWorld_endToEnd_apply]
  field_simp
  ring

/-! ===========================================================================
    §5  ⭐⭐ 迭代 `thetaN`（= `endToEndIter`）与闭式
    =========================================================================== -/

/-- ⭐⭐ **端到端闭环的第 `n` 步参数**：**就是** `EndToEnd.endToEndIter`
（本文件不造第二个迭代语义）。

$$\theta_0 = \theta_0,\qquad
  \theta_{k+1} := \mathrm{endToEnd}\ \dots\ (\theta^*x)\ \theta_k\ \dots\ x .$$ -/
noncomputable abbrev thetaN (η θstar x : ℝ) (θ₀ : ℝ) (n : ℕ) : ℝ :=
  endToEndIter linWorld (id : ℝ → ℝ) η
    (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
    (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀

/-- 一步更新的标量函数 `f(θ) = (1-η)θ + η θ*`（供 `Nat.iterate` 表述）。 -/
noncomputable abbrev fstep (η θstar : ℝ) (θ : ℝ) : ℝ := (1 - η) * θ + η * θstar

/-- ⭐⭐ **`endToEndIter` 的 `n` 步 = `fstep` 的 `n` 次 `Nat.iterate`**。

这一步把 `EndToEnd.endToEndIter`（`Nat.rec` 形式，先作用再递推）
**对齐到**标准的 $f^{[n]}$，从而使闭式可用 `Function.iterate` 的引理。
**⚠ 这不是重定义迭代**：左式**就是** `endToEndIter`（`thetaN` 是其别名）。 -/
theorem thetaN_eq_iterate (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    thetaN η θstar x θ₀ n = (fstep η θstar)^[n] θ₀ := by
  induction n generalizing θ₀ with
  | zero => rfl
  | succ k ih =>
    rw [thetaN, endToEndIter_succ]
    rw [show endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x k
          (endToEnd linWorld (id : ℝ → ℝ) η
            (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
            (θstar * x) θ₀ PUnit.unit PUnit.unit PUnit.unit x)
        = thetaN η θstar x
            (endToEnd linWorld (id : ℝ → ℝ) η
              (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
              (θstar * x) θ₀ PUnit.unit PUnit.unit PUnit.unit x) k
        from rfl]
    rw [linWorld_endToEnd_step η θ₀ θstar x hx, ih (fstep η θstar θ₀),
      Function.iterate_succ_apply]

/-- ⭐⭐ **`fstep` 迭代的闭式**：偏离真值按 `(1-η)^n` 等比缩放。

$$f^{[n]}(\theta) - \theta^* = (1-\eta)^n\,(\theta - \theta^*) .$$ -/
theorem fstep_iterate_closed (η θstar θ : ℝ) (n : ℕ) :
    (fstep η θstar)^[n] θ - θstar = (1 - η)^n * (θ - θstar) := by
  induction n generalizing θ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (fstep η θstar θ)]
    have h : fstep η θstar θ - θstar = (1 - η) * (θ - θstar) := by
      simp only [fstep]; ring
    rw [h]; ring

/-- ⭐⭐⭐ **【闭式：`n` 步后的偏差】**

$$\boxed{\;\theta_n - \theta^* = (1-\eta)^n\,(\theta_0 - \theta^*)\;}$$

**⭐ 这是「学习真的发生」的**定量**证据**：偏差每个时刻乘同一个因子
$1-\eta$，与 $n$、$\theta_0$、$\theta^*$ 都无关（除了这个公因子）。
**收敛性、单调性、$n$ 步精确恢复**（§6、§7）全部由本式一行推出。 -/
theorem thetaN_closed (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    thetaN η θstar x θ₀ n - θstar = (1 - η)^n * (θ₀ - θstar) := by
  rw [thetaN_eq_iterate η θstar x θ₀ hx n, fstep_iterate_closed]

/-- ⭐ **无噪声残差在 `θ = θ*` 处为零**（`θ*` 是 `endToEnd` 的不动点）：
闭环在真值处**不再更新** —— 正确的「不伤害」判据。 -/
theorem linWorld_star_fixed (η θstar x : ℝ) (hx : x ≠ 0) :
    endToEnd linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) θstar PUnit.unit PUnit.unit PUnit.unit x = θstar := by
  rw [linWorld_endToEnd_step η θstar θstar x hx]
  ring

/-! ===========================================================================
    §6  ⭐⭐⭐ 主定理：`θ_n → θ*`
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【主定理 · Z3】：端到端学习收敛到真值 `θ*`**。

**前提**（三条，皆非平凡）：
1. `x ≠ 0` —— 设计点非零（否则 `y = θ* x = 0`，观测**不含** `θ*` 的信息）；
2. `|1 - η| < 1` —— 步长 `η ∈ (0,2)`（学习率条件）；
3. `θ*`、`θ_0` 任意实数（**不对 `θ*` 的符号/大小作任何限制**）。

**结论**：

$$\mathrm{Tendsto}\;\bigl(\theta_n\bigr)_{n}\;\mathrm{atTop}\;\bigl(\mathcal{N}\,\theta^*\bigr),
\qquad \theta_n := \texttt{endToEndIter}\ \dots\ n\ \theta_0 .$$

**⭐ 与「误差 → 0」的本质差别**：
本定理的极限点是**给定的真值** `θ*`（一个**自由参数**），
**不是** `0`。§7 的 `linWorld_tendsto_ne_zero` 在 `θ* ≠ 0` 时
把这一点钉死。**⟹ 这是「学到了真值」，而非「学到了零」。**

**⭐ 证明不循环**：结论由 §5 闭式 + `tendsto_pow_atTop_nhds_zero_of_lt_one` 得到；
`|1-η| < 1` 只用于让 `(1-η)^n → 0`，**不含**任何关于 `θ_n` 的信息。 -/
theorem linWorld_tendsto_thetaStar (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto (thetaN η θstar x θ₀) Filter.atTop (nhds θstar) := by
  have hbase : Filter.Tendsto (fun n : ℕ => (1 - η)^n) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (1 - η)) hη
    simpa [abs_pow] using h
  have hpow : Filter.Tendsto (fun n : ℕ => (1 - η)^n * (θ₀ - θstar))
      Filter.atTop (nhds 0) := by
    simpa using hbase.mul_const (θ₀ - θstar)
  have h2 : Filter.Tendsto (fun n : ℕ => θstar + (1 - η)^n * (θ₀ - θstar))
      Filter.atTop (nhds (θstar + 0)) := Filter.Tendsto.const_add _ hpow
  rw [add_zero] at h2
  refine h2.congr (fun n => ?_)
  have h := thetaN_closed η θstar x θ₀ hx n
  linarith

/-- ⭐⭐ **收敛点的唯一性**：任何子列/任何极限都是 `θ*`。

**⭐ 意义**：`θ*` 不是「某个极限点」，而是**唯一的极限点** ——
即学到的对象**就是**真值本身，不是它的某个等价值。 -/
theorem linWorld_tendsto_unique (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) (L : ℝ)
    (h : Filter.Tendsto (thetaN η θstar x θ₀) Filter.atTop (nhds L)) :
    L = θstar :=
  tendsto_nhds_unique h (linWorld_tendsto_thetaStar η θstar x θ₀ hx hη)

/-- ⭐⭐ **【残差 → 0，作为收敛的**推论**，不是替代品】**

真实端到端残差 `e2eResidual W (θ* x) θ … x = θ* x - θ x` 沿轨迹趋于 `0`。

**⚠ 这条是**弱**的（「误差 → 0」），列在此处仅说明本文件**也**蕴含旧结论；
本文件的**强**结论是 §6 的 `θ_n → θ*`。 -/
theorem linWorld_residual_tendsto_zero (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => e2eResidual linWorld (θstar * x) (thetaN η θstar x θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit x)
      Filter.atTop (nhds 0) := by
  have hlim := linWorld_tendsto_thetaStar η θstar x θ₀ hx hη
  have hfun : Filter.Tendsto
      (fun n : ℕ => θstar * x - thetaN η θstar x θ₀ n * x)
      Filter.atTop (nhds (θstar * x - θstar * x)) :=
    (tendsto_const_nhds.mul tendsto_const_nhds).sub (hlim.mul tendsto_const_nhds)
  rw [sub_self] at hfun
  refine hfun.congr (fun n => ?_)
  rw [e2eResidual_def, linWorld_predFrom]

/-! ===========================================================================
    §7  ⭐⭐ 非平凡性：极限不是 0；误差单调；`η = 1` 一步到位
    =========================================================================== -/

/-- ⭐⭐⭐ **【极限不是 0】**：`θ* ≠ 0` 时，`θ_n → θ*` 而 `θ* ≠ 0`。

**⭐ 这是「学到真值」与「学到零」的分水岭**：
若把「学习」写成「误差 → 0」，则 `θ_n ≡ 0` 平凡地满足；
本定理（配合 §6）说明本文件的极限是**非零真值**，`θ_n ≡ 0` **不满足**。

**⚠ 反面对照**（本定理的意义所在）：若 `θ* = 0`，§6 的结论退化为 `θ_n → 0`；
本定理表明**只有当真值本身是 0 时**才是「学到 0」。 -/
theorem linWorld_tendsto_ne_zero (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) (hθ : θstar ≠ 0) :
    Filter.Tendsto (thetaN η θstar x θ₀) Filter.atTop (nhds θstar) ∧ θstar ≠ 0 :=
  ⟨linWorld_tendsto_thetaStar η θstar x θ₀ hx hη, hθ⟩

theorem linWorld_err_le (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (h1 : 0 < η) (h2 : η ≤ 1)
    (n : ℕ) :
    |thetaN η θstar x θ₀ n - θstar| ≤ |θ₀ - θstar| := by
  rw [thetaN_closed η θstar x θ₀ hx n, abs_mul, abs_pow]
  have habs : |1 - η| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hp : |1 - η|^n ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
  calc |1 - η|^n * |θ₀ - θstar| ≤ 1 * |θ₀ - θstar| :=
        mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = |θ₀ - θstar| := one_mul _

/-- ⭐⭐ **【偏差闭式（绝对值形式）】**：$|\theta_n-\theta^*| = |1-\eta|^n|\theta_0-\theta^*|$。 -/
theorem linWorld_err_closed (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    |thetaN η θstar x θ₀ n - θstar| = |1 - η|^n * |θ₀ - θstar| := by
  rw [thetaN_closed η θstar x θ₀ hx n, abs_mul, abs_pow]

/-- ⭐⭐ **【`θ* ≠ 0` 时轨迹**最终**非零】**（更硬的非平凡性）。

存在 `N`，使 `∀ n ≥ N`，`θ_n ≠ 0`：即收敛**不是**「落到 0」，
迭代**最终进入 `θ*` 的非零邻域**并留在其中。 -/
theorem linWorld_eventually_ne_zero (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) (hθ : θstar ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → thetaN η θstar x θ₀ n ≠ 0 := by
  have hθ' : (0 : ℝ) < |θstar| := abs_pos.mpr hθ
  -- 最终 `|1-η|^n * |θ₀-θ*| < |θ*|`
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop
      , |1 - η|^n * |θ₀ - θstar| < |θstar| := by
    have hbase' : Filter.Tendsto (fun n : ℕ => |1 - η|^n * |θ₀ - θstar|)
        Filter.atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (1 - η)) hη).mul_const
        (|θ₀ - θstar|)
      simpa using h
    exact hbase'.eventually (isOpen_Iio.mem_nhds hθ')
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨N, fun n hn => ?_⟩
  intro hzero
  have hc := linWorld_err_closed η θstar x θ₀ hx n
  rw [hzero, zero_sub, abs_neg] at hc
  have hlt := hN n hn
  linarith [hc ▸ hlt]

/-- ⭐⭐⭐ **【`η = 1`：一步精确恢复真值】**

$$\eta = 1 \;\Longrightarrow\; \theta_1 = \theta^*$$
（对**任意** `θ_0`、**任意** `θ*`、**任意** `x ≠ 0`）。

**⭐ 意义**：在 `linWorld` 上「学习」甚至**不需要**渐近过程 ——
步长取满时**一步**即达真值（§6 的 `|1-η|<1` 在此退化为 `< 1` 的边界值，
但一步终点与 `η` 无关地精确）。 -/
theorem linWorld_one_step_exact (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    thetaN 1 θstar x θ₀ 1 = θstar := by
  have h := thetaN_closed 1 θstar x θ₀ hx 1
  norm_num at h
  linarith

/-- ⭐ **`η = 1` 时 `n ≥ 1` 全程精确**（一步之后不再移动，因为已在真值处）。 -/
theorem linWorld_one_step_stays (θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    thetaN 1 θstar x θ₀ n = θstar := by
  have h := thetaN_closed 1 θstar x θ₀ hx n
  rcases Nat.exists_eq_add_of_le hn with ⟨k, hk⟩
  subst hk
  norm_num at h
  linarith

/-! ===========================================================================
    §8  具体数值实例（检验「非空真」：前件可同时满足）
    =========================================================================== -/

/-- ⭐⭐ **具体实例**：`θ* = 3`、`θ_0 = 0`、`η = 1/2`、`x = 2`（三者前件全满足）。

即「真值 `3`、初始不知道（`0`）」的端到端学习，观测 `y = 3 * 2 = 6`。 -/
theorem concrete_setup :
    (2 : ℝ) ≠ 0 ∧ |1 - (1/2 : ℝ)| < 1 := by
  refine ⟨by norm_num, by norm_num⟩

/-- ⭐⭐⭐ **具体数值：`θ_n → 3`**（真值 `3`，初始 `0`，`η = 1/2`，`x = 2`）。

**⭐ 这条定理把「学习」落到一串数上**：`θ_0 = 0`，`θ_n = 3 - 3·(1/2)^n → 3`。 -/
theorem concrete_tendsto :
    Filter.Tendsto (thetaN (1/2) 3 2 0) Filter.atTop (nhds 3) :=
  linWorld_tendsto_thetaStar (1/2) 3 2 0 (by norm_num) (by norm_num)

/-- ⭐⭐ **具体数值：闭式** `θ_n - 3 = (1/2)^n · (-3)`。 -/
theorem concrete_closed (n : ℕ) :
    thetaN (1/2) 3 2 0 n - 3 = (1/2 : ℝ)^n * (0 - 3) := by
  have h := thetaN_closed (1/2) 3 2 0 (by norm_num) n
  have h2 : (1 - (1:ℝ)/2) = 1/2 := by norm_num
  rw [h2] at h
  rw [h]

/-- ⭐⭐ **具体数值：极限点非零**（`3 ≠ 0`）。 -/
theorem concrete_limit_ne_zero :
    Filter.Tendsto (thetaN (1/2) 3 2 0) Filter.atTop (nhds 3) ∧ (3:ℝ) ≠ 0 :=
  linWorld_tendsto_ne_zero (1/2) 3 2 0 (by norm_num) (by norm_num) (by norm_num)

/-- ⭐ **具体数值：偏差公式** `|θ_n - 3| = (1/2)^n · 3`。 -/
theorem concrete_err (n : ℕ) :
    |thetaN (1/2) 3 2 0 n - 3| = (1/2 : ℝ)^n * 3 := by
  rw [linWorld_err_closed (1/2) 3 2 0 (by norm_num) n]
  norm_num

/-! ===========================================================================
    §9  自检清单（逐条可编译）
    =========================================================================== -/

noncomputable section

/-- **自检 1**：`linWorld` 的预测确实是 `θ * x`（Z1 的 $f(\theta^*)\,x$）。 -/
example (θ x : ℝ) : predFrom linWorld θ PUnit.unit PUnit.unit PUnit.unit x = θ * x := rfl

/-- **自检 2**：`thetaN` 的类型确实是「`ℝ → ℕ → ℝ`」（初始值、步数 → 参数）。 -/
example (η θstar x : ℝ) : ℝ → ℕ → ℝ := thetaN η θstar x

/-- **自检 3**：主定理在 `η = 1/3`（另一组合法步长）上同样成立。 -/
example (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (thetaN (1/3) θstar x θ₀) Filter.atTop (nhds θstar) :=
  linWorld_tendsto_thetaStar (1/3) θstar x θ₀ hx (by norm_num)

/-- **自检 4**：`η = 3/2`（步长在 `(1,2)` 内，`1-η<0`）也收敛（**振荡**收敛）。 -/
example (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (thetaN (3/2) θstar x θ₀) Filter.atTop (nhds θstar) :=
  linWorld_tendsto_thetaStar (3/2) θstar x θ₀ hx (by norm_num)

/-- **自检 5**：`η = 2` 时 `|1-η| = 1`，前件**不成立**（故本文件的定理不覆盖，
**本文件不声称** `η = 2` 收敛 —— 事实上 `η = 2` 时 `θ_n = θ_0 + 2n(θ*-θ_0)` 发散）。 -/
example : ¬ (|1 - (2:ℝ)| < 1) := by norm_num

end

end ThetaConvergence
end Fate
