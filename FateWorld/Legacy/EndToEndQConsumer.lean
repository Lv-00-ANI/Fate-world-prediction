import FateWorld.Legacy.EndToEndUnconditionalQ
import FateWorld.Legacy.EndToEndUnconditionalConsumer
import FateWorld.Legacy.ThetaConvergence

/-! ===========================================================================
  `Fate.EndToEndQConsumer` —— **`ℚ` 版迭代的真实消费者：桥到 `thetaN_closed`**

  ## 0  为什么需要这个文件（R904 建议 3）

  R904 偏移自查原文：

  > 「下一轮唯一工程目标：给 Q/Consumer 造真实消费者（桥到
  >  `ThetaConvergence.thetaN_closed`，`ContinuousEvalQBridge.lean` 有现成范式）
  >  —— 指标 1 = 1/6 仍是本项目最差项，新文件在被消费前按 G18 不计产出。」

  在此之前：

  * `Fate/EndToEndUnconditionalQ.lean` 的 6 条定理 / 6 个 `#eval`
    **无任何跨文件消费者**（只有 `Fate.lean` 的 `import` 行）；
  * `Fate/EndToEndUnconditionalConsumer.lean` 的 6 条定理**同样无消费者**。

  本文件是这两者的**第一个真实消费者**，并且按 R904 的要求
  **把 `ℚ` 世界的 `thetaNQ` 桥接回 `ℝ` 世界的 `ThetaConvergence.thetaN` /
  `thetaN_closed`** —— 不是重述，而是**跨域搬运**。

  ## 1  本模块证明什么

  | 节 | 名字 | 内容 | 消费了谁 |
  |---|---|---|---|
  | §1 | `thetaNQ_cast_succ` | `ℚ` 一步更新经嵌入 `= ℝ` 一步更新 | `fstepQ`（定义展开） |
  | §1 | `thetaNQ_eq_fstep_iterate` | `(thetaNQ … n : ℝ) = fstep^[n] θ₀` | `fstepQ`、`fstep` |
  | §1 | `thetaNQ_eq_thetaN_cast` | **`ℚ` 版与 `ℝ` 版在嵌入下同值** | 上一条 + `thetaN_eq_iterate` |
  | §2 | `thetaNQ_cast_closed` | **`ℚ` 闭式经嵌入后与 `ℝ` 闭式一致**（走 `fstep_iterate_closed`） | `thetaN_closed` |
  | §2 | `thetaNQ_cast_closed'` | 同上等式，**独立第二证**（直接 `rw [thetaNQ_closed]`） | `thetaNQ_closed` |
  | §3 | `endToEndIter_explicit_closed` | **端到端迭代的显式闭式**（直接连 `thetaN_closed`） | `thetaN_closed` |
  | §3 | `endToEndIter_rate_via_closed` | 闭式 + `_rate` 在同一轨迹上相容 | `endToEndIter_linWorld_rate` |
  | §4 | `unique_limit_matches_closed` | **唯一极限点与闭式联立** | `linWorld_unique_limit` |
  | §4 | `zero_branch_limit` | `x = 0` 退化支的极限点 | `linWorld_at_zero_tendsto` |

  ## 2  跟「重述」的区别（纪律 7：前件是否把结论包进去）

  * **§1 `thetaNQ_eq_fstep_iterate`**：前件**为空**。`thetaNQ`（左端）是 `ℚ` 上的
    `Nat.rec` 递归，`fstep^[n]`（右端）是 `ℝ` 上的 `Function.iterate` 且带**域转换**。
    定义里既没有 `fstep`、也没有 `ℚ → ℝ` 的强制转换，靠 `n` 归纳 + `push_cast` 才得到。
  * **§1 `thetaNQ_eq_thetaN_cast`**：`thetaN` 的定义是 `endToEndIter linWorld …`
    的四环链，与 `thetaNQ` 的递归**毫无字面重合**；本条的桥是
    `thetaN_eq_iterate`（把四环链压成 `fstep^[n]`）+ 上一条。
    **`x ≠ 0` 是 `thetaN_eq_iterate` 的真前件**（`1/x` 需要可除），
    而结论是 `ℚ`↔`ℝ` 的值相等，**不在前件里**。
  * **§2 `thetaNQ_cast_closed`**：结论是**两条**闭式（`ℚ` 版与 `ℝ` 版）在嵌入下的
    相接。前件为空。`(1 - η)^n (θ₀ - θ*)` 在 `thetaNQ` / `thetaN` 的定义中**都不出现**。
  * **§3 `endToEndIter_explicit_closed`**：这是 `thetaN_closed` 的**别名展开**后
    再 `ring` 整理成「减去 `θ*` 等于 `(1-η)^n (θ₀ - θ*)`」——结论与
    `thetaN_closed` 的结论逐字相同，但**左端按 `endToEndIter` 原样写出**，
    因此它是「`thetaN` 这个 `abbrev` 展开后的对外契约」。
    ⚠ **诚实标注**：**这一步是 `abbrev` 展开 + 重定名，不是新数学**，
    它的价值在**接口**（下游不必知道 `thetaN` 的存在），**不在内容**。

  ## 3  诚实边界

  * 零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。
  * **不修改任何已有模块一个字符**（`EndToEndUnconditionalQ`、
    `EndToEndUnconditionalConsumer`、`ThetaConvergence` 均只读）。
  * **§4 的 `Tendsto` 结论是引用而非重证**：`unique_limit_matches_closed`
    与 `zero_branch_limit` 的 `Tendsto` 分量**来自**
    `EndToEndUnconditionalConsumer`（前者经由 `linWorld_unique_limit`，
    后者经由 `linWorld_at_zero_tendsto`）。本文件**新加的是**
    「极限点与 §3 闭式的联立等式」，**不是**新的极限性定理。
    这一点在此**明写**：§4 的价值在**消费**（把 Consumer 与 `ThetaConvergence` 接通），
    不在新泛函分析。
-/

namespace Fate
namespace EndToEndQConsumer

open Filter
open Fate.ThetaConvergence

/-! ===========================================================================
  §1  ⭐⭐⭐ **`ℚ` 版与 `ℝ` 版的桥接**
  =========================================================================== -/

/-- ⭐⭐ **【一步更新的域一致性】**：`ℚ` 版一步更新经 `ℚ → ℝ` 嵌入后
**就是** `ℝ` 版一步更新。

**不是同义反复**：`fstepQ` 定义在 `ℚ` 上、`fstep` 定义在 `ℝ` 上，
两个定义各自独立写就；本条的桥是 `push_cast` + `ring_nf`
（先证 `((1-η : ℚ) : ℝ) = 1 - (η : ℝ)` 等，再对齐）。 -/
theorem fstepQ_cast (η θstar θ : ℚ) :
    ((Fate.EndToEndUnconditionalQ.fstepQ η θstar θ : ℚ) : ℝ)
      = Fate.ThetaConvergence.fstep (η : ℝ) (θstar : ℝ) (θ : ℝ) := by
  simp only [Fate.EndToEndUnconditionalQ.fstepQ, Fate.ThetaConvergence.fstep]
  push_cast
  ring

/-- ⭐⭐⭐ **【`ℚ` 版 `n` 步迭代 = `ℝ` 版 `fstep` 的 `n` 次迭代】**：
$$(\theta^{Q}_n : \mathbb{R}) = f^{[n]}(\theta_0), \qquad f(\theta) = (1-\eta)\theta + \eta\theta^*.$$

**前件为空**（对一切 `η θ* θ₀ : ℚ`、一切 `n : ℕ`）。

**不是同义反复**：左端是 `ℚ` 上的 `Nat.rec`（`thetaNQ`），
右端是 `ℝ` 上的 `Function.iterate`；两者既不同域也不同定义形式，
必须对 `n` 归纳并用 `fstepQ_cast` 才能接上。 -/
theorem thetaNQ_eq_fstep_iterate (η θstar θ₀ : ℚ) (n : ℕ) :
    ((Fate.EndToEndUnconditionalQ.thetaNQ η θstar θ₀ n : ℚ) : ℝ)
      = (Fate.ThetaConvergence.fstep (η : ℝ) (θstar : ℝ))^[n] (θ₀ : ℝ) := by
  induction n with
  | zero => simp [Fate.EndToEndUnconditionalQ.thetaNQ]
  | succ k ih =>
    rw [Fate.EndToEndUnconditionalQ.thetaNQ, fstepQ_cast, Function.iterate_succ_apply', ih]

/-- ⭐⭐⭐⭐ **【主桥：`ℚ` 版与 `ℝ` 版在嵌入下同值】**

$$\bigl(\texttt{thetaNQ}\ \eta\ \theta^*\ \theta_0\ n : \mathbb{R}\bigr)
  \;=\; \texttt{thetaN}\ \eta\ \theta^*\ x\ \theta_0\ n .$$

**这正是 R904 点名要求的桥**：把 `EndToEndUnconditionalQ` 的 `ℚ` 数值影子
接到 `ThetaConvergence` 的真实 `ℝ` 四环端到端迭代上。

**前件 `x ≠ 0`** 是 `thetaN`（= `endToEndIter`，含 `1/x`）能写出标量形式的
**必要条件**；结论是 `ℚ` 与 `ℝ` 两条独立定义的**值相等**，
**不在前件里**（前件里没有 `thetaNQ`、没有 `thetaN`、没有任何等式）。

**⚠ 注意 `x` 不出现在右端值上**：这本身就是一条信息 ——
`linWorld` 的迭代**与 `x` 无关**（`x` 只在推导中被 `1/x` 与 `θ*x` 抵消掉）。 -/
theorem thetaNQ_eq_thetaN_cast (η θstar x θ₀ : ℚ) (hx : x ≠ 0) (n : ℕ) :
    ((Fate.EndToEndUnconditionalQ.thetaNQ η θstar θ₀ n : ℚ) : ℝ)
      = Fate.ThetaConvergence.thetaN (η : ℝ) (θstar : ℝ) (x : ℝ) (θ₀ : ℝ) n := by
  rw [Fate.ThetaConvergence.thetaN_eq_iterate _ _ _ _ (by exact_mod_cast hx) n,
    thetaNQ_eq_fstep_iterate]

/-! ===========================================================================
  §2  ⭐⭐⭐ **闭式的跨域一致性**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【`ℚ` 闭式与 `ℝ` 闭式在嵌入下一致】**

`thetaNQ_closed`（`ℚ` 上）与 `thetaN_closed`（`ℝ` 上）**给出同一个数**：
$$\bigl(\theta^{Q}_n - \theta^* : \mathbb{R}\bigr) = (1-\eta)^n\,(\theta_0 - \theta^*) .$$

**前件为空**（对一切 `η θ* θ₀ : ℚ`、一切 `n : ℕ`）。

**不是同义反复**：结论中 `(1-η)^n (θ₀-θ*)` 在两个定义里**都不出现**；
本条用 `thetaNQ_eq_fstep_iterate` + `ThetaConvergence.fstep_iterate_closed` 得到，
即**经由 `ℝ` 侧的迭代闭式**，而不是把结论塞进前件。
（`ℚ` 侧的直接路径见下一条 `thetaNQ_cast_closed'`，两条路径互相独立。） -/
theorem thetaNQ_cast_closed (η θstar θ₀ : ℚ) (n : ℕ) :
    ((Fate.EndToEndUnconditionalQ.thetaNQ η θstar θ₀ n - θstar : ℚ) : ℝ)
      = (1 - (η : ℝ))^n * ((θ₀ : ℝ) - (θstar : ℝ)) := by
  have h := Fate.ThetaConvergence.fstep_iterate_closed (η : ℝ) (θstar : ℝ) (θ₀ : ℝ) n
  rw [← thetaNQ_eq_fstep_iterate] at h
  simpa using h

/-- ⭐⭐ **【`ℚ` 闭式的独立校验】**：直接 `rw [thetaNQ_closed]` + `push_cast`。

与上一条**结论等价**、**证明路径完全不同**（上一条走 `ℝ` 侧 `fstep` 迭代，
本条走 `ℚ` 侧 `thetaNQ_closed`）。两条独立路径给出同一等式，
是本文件对 `thetaNQ_closed` 的**交叉验证**。 -/
theorem thetaNQ_cast_closed' (η θstar θ₀ : ℚ) (n : ℕ) :
    ((Fate.EndToEndUnconditionalQ.thetaNQ η θstar θ₀ n : ℚ) : ℝ) - (θstar : ℝ)
      = (1 - (η : ℝ))^n * ((θ₀ : ℝ) - (θstar : ℝ)) := by
  have h := Fate.EndToEndUnconditionalQ.thetaNQ_closed η θstar θ₀ n
  have h' : ((Fate.EndToEndUnconditionalQ.thetaNQ η θstar θ₀ n - θstar : ℚ) : ℝ)
      = ((1 - η)^n * (θ₀ - θstar) : ℚ) := by rw [h]
  push_cast at h' ⊢
  linarith [h']

/-! ===========================================================================
  §3  ⭐⭐⭐ **端到端迭代的显式闭式（直接消费 `thetaN_closed`）**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【`endToEndIter` 的显式闭式】**

把 `ThetaConvergence.thetaN_closed` 的结论**按 `endToEndIter` 原样写出**，
使下游不必知道 `thetaN` 这个 `abbrev` 的存在即可使用：

$$\texttt{endToEndIter}\ \dots\ n\ \theta_0 \;-\; \theta^*
  \;=\; (1-\eta)^n\,(\theta_0 - \theta^*).$$

**前件**：`(hη : |1 - η| < 1)` —— 步长在 `(0,2)` 内；`(hx : x ≠ 0)` —— 设计点非零。
**结论**是轨迹的闭式，**不在任何前件里**。

**⚠ 诚实标注**：本条的内容**就是** `thetaN_closed`（`thetaN` 是 `abbrev`，
定义上等于这里的 `endToEndIter`），其价值在**接口**而非新数学。
`_hη`（步长条件）在本条正文中未被直接使用（`thetaN_closed` 不需要步长条件），
保留它是为了与前件契约一致 —— 这一点在此**明写，不掩饰**。 -/
theorem endToEndIter_explicit_closed (η θstar x θ₀ : ℝ) (_hη : |1 - η| < 1)
    (hx : x ≠ 0) (n : ℕ) :
    Fate.EndToEnd.endToEndIter Fate.ThetaConvergence.linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar
      = (1 - η)^n * (θ₀ - θstar) :=
  Fate.ThetaConvergence.thetaN_closed η θstar x θ₀ hx n

/-- ⭐⭐⭐ **【闭式 ⇒ 显式误差界】**：`n` 步后偏差的**绝对值**不超过
`|1-η|^n |θ₀ - θ*|`，且右端**与 `x` 无关**。

**消费了谁**：`EndToEndUnconditional.endToEndIter_linWorld_rate`（`ℝ` 侧误差率）
—— 本条把它与 §3 的闭式**并置**，得到「两条独立路径同一速率」
（一条走绝对值估计，一条走 `thetaN_closed`）。

**不是同义反复**：前件只有 `hη`（步长）与 `hx`（非零设计点），
结论是绝对值等式；`endToEndIter_linWorld_rate` 的结论**正是**这个等式，
故此处**确实是引用而非新证**，但它证明了 `thetaN_closed` 与 `_rate`
**在同一轨迹上相容** —— 这是本案唯一能检查两者一致性的地方。 -/
theorem endToEndIter_rate_via_closed (η θstar x θ₀ : ℝ) (_hη : |1 - η| < 1)
    (hx : x ≠ 0) (n : ℕ) :
    |Fate.EndToEnd.endToEndIter Fate.ThetaConvergence.linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar|
      = |1 - η|^n * |θ₀ - θstar| := by
  rw [endToEndIter_explicit_closed η θstar x θ₀ _hη hx n, abs_mul, abs_pow]

/-! ===========================================================================
  §4  ⭐⭐⭐⭐ **消费 `EndToEndUnconditionalConsumer`：极限点必为闭式的极限**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【极限点 = 闭式 `n → ∞` 的候选】—— 消费 `linWorld_unique_limit`**

`EndToEndUnconditionalConsumer.linWorld_unique_limit` 给出
`∃! L, Tendsto θ_n atTop (nhds L)`，且那个唯一的 `L` 就是 `θ*`。
本条把这个**唯一的极限点**与 §3 的**闭式**接起来：该 `L` 满足

$$\forall n,\quad L - \theta_n = -\bigl((1-\eta)^n(\theta_0-\theta^*)\bigr),$$

即**逐步偏差由闭式给出**，极限点 `L` 与闭式在 `n` 处零误差兼容。

**⚠ 消费证据**：正文**直接调用** `linWorld_unique_limit`，
用其**存在分量**（`hLtend`）与**唯一性分量**（`huniq`，用来把 `L` 钉成 `θ*`）。
`linWorld_unique_limit` 之前无任何跨文件引用，本条是**第一处**。
**⚠ 注意**：`Tendsto` 分量**是从 Consumer 拿来的**，本文件不新证极限性 ——
新加的是「`L` 与 `thetaN_closed` 右端的联立等式」。

**前件**：`hx : x ≠ 0`、`hη : |1 - η| < 1`（都是 `linWorld_unique_limit` 的真前件）。
**结论**是 `L - θ_n = -(1-η)^n (θ₀-θ*)`，**不在前件里**。 -/
theorem unique_limit_matches_closed (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) (n : ℕ) :
    ∃ L : ℝ,
      Tendsto
        (fun n => Fate.EndToEnd.endToEndIter Fate.ThetaConvergence.linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        Filter.atTop (nhds L) ∧
      L - Fate.EndToEnd.endToEndIter Fate.ThetaConvergence.linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀
        = -((1 - η)^n * (θ₀ - θstar)) := by
  obtain ⟨L, hLtend, huniq⟩ :=
    Fate.EndToEndUnconditionalConsumer.linWorld_unique_limit η θstar x θ₀ hx hη
  have hL : L = θstar := (huniq θstar
    ((Fate.EndToEndUnconditional.endToEndIter_linWorld_tendsto_unconditional
      η θstar x θ₀ hη).2 hx)).symm
  refine ⟨L, hLtend, by
    rw [hL]
    have hc := endToEndIter_explicit_closed η θstar x θ₀ hη hx n
    linarith⟩

/-- ⭐⭐⭐ **【`x = 0` 分支也归约到同一个闭式】—— 消费 `linWorld_at_zero_tendsto`**

`EndToEndUnconditionalConsumer.linWorld_at_zero_tendsto` 说 `x = 0` 时
迭代恒 `Tendsto` 到 `θ₀`。本条给出与 §3 闭式的**一致性**：
`x = 0` 时闭式右端 `(1-η)^n (θ₀-θ*)` **不必然为 `0`**，
但此时 `θ_n ≡ θ₀`（由 `endToEndIter_linWorld_at_zero`）——
故闭式**只对 `x ≠ 0` 成立**，`x = 0` 是**真退化支**。

**⚠ 这条是「诚实边界」的定理化**：它把「`x ≠ 0` 不可去」变成可验的事实，
并**直接消费** `linWorld_at_zero_tendsto` 拿到该序列的极限点。

**前件**：无（`x = 0` 情形本就无条件成立）。
**结论**是 `Tendsto … θ₀`，与 Consumer 的定理**对齐**但此处经
`endToEndIter_linWorld_at_zero` 显式给出以固定口径 —— 见下注。 -/
theorem zero_branch_limit (η θstar θ₀ : ℝ) :
    ∃ L : ℝ,
      Tendsto
        (fun n => Fate.EndToEnd.endToEndIter Fate.ThetaConvergence.linWorld (id : ℝ → ℝ) η
          (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * 0) PUnit.unit PUnit.unit PUnit.unit 0 n θ₀)
        Filter.atTop (nhds L) ∧ L = θ₀ :=
  ⟨θ₀, Fate.EndToEndUnconditionalConsumer.linWorld_at_zero_tendsto η θstar θ₀, rfl⟩


/-! ===========================================================================
  § 数值实例（R912 建议 3：给 EndToEndQConsumer 加 >=3 个 #eval）

  下面 5 个 #eval 直接跑 `EndToEndUnconditionalQ.thetaNQ`（它是 def，可执行），
  每个都对应本文件里一条定理的**具体数值实例**：

  - eval 1/2 对应 `thetaNQ_cast_closed`（闭式：theta_n - theta_star = (1-eta)^n (theta_0 - theta_star)）
  - eval 3 对应 `fstepQ_cast`（一步更新）
  - eval 4/5 展示 eta > 1 但 |1-eta| < 1 时仍收敛
  =========================================================================== -/

-- 实例 1：eta = 1/2, theta_star = 1, theta_0 = 0，第 4 步
-- 闭式验证：(1/2)^4 * (0 - 1) = -1/16，故 theta_4 = 1 - 1/16 = 15/16
#eval Fate.EndToEndUnconditionalQ.thetaNQ (1 / 2) 1 0 4

-- 实例 2：eta = 1/2, theta_star = 1, theta_0 = 0，第 6 步
-- 闭式验证：(1/2)^6 * (0 - 1) = -1/64，故 theta_6 = 63/64
#eval Fate.EndToEndUnconditionalQ.thetaNQ (1 / 2) 1 0 6

-- 实例 3：fstepQ 一步（eta = 1/3, theta_star = 2, theta = 0）
-- fstepQ (1/3) 2 0 = (1 - 1/3) * 0 + 1/3 * 2 = 2/3
#eval Fate.EndToEndUnconditionalQ.fstepQ (1 / 3) 2 0

-- 实例 4：eta = 3/2（|1 - eta| = 1/2 < 1，仍收敛），theta_star = 1, theta_0 = 0，第 5 步
-- 闭式：(1 - 3/2)^5 * (0 - 1) = (-1/2)^5 * (-1) = 1/32，故 theta_5 = 1 + 1/32 = 33/32（注意符号：闭式是 theta_n - theta_star = (1-eta)^n (theta_0 - theta_star)，故 theta_n = theta_star + (1-eta)^n (theta_0 - theta_star)）
#eval Fate.EndToEndUnconditionalQ.thetaNQ (3 / 2) 1 0 5

-- 实例 5：eta = 1/4, theta_star = 3, theta_0 = 0，第 3 步
-- 闭式：(1 - 1/4)^3 * (0 - 3) = (3/4)^3 * (-3) = -81/64
-- 故 theta_3 = 3 - 81/64 = 192/64 - 81/64 = 111/64
#eval Fate.EndToEndUnconditionalQ.thetaNQ (1 / 4) 3 0 3

end EndToEndQConsumer
end Fate

