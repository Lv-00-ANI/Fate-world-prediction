import FateWorld.FateV2.Loop.EndToEndPipelineTendsto
import FateWorld.FateV2.Loop.ThetaConvergence
/-!
  # Loop · EndToEndUnconditional

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndUnconditional.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEndPipelineTendsto, ThetaConvergence
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.EndToEndUnconditional` —— **拆退化分支：`x = 0` 时不声称收敛到 `θ*`**

  ## 0  本文件补的到底是哪一条缺口

  已入库 `Fate/EndToEndPipelineTendsto.lean:225` 的主定理

  ```
  endToEndIter_linWorld_tendsto (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
      Tendsto (fun n => endToEndIter linWorld … x n θ₀) atTop (nhds θstar)
  ```

  带**数据前件** `hx : x ≠ 0`。R891 建议 3 要求把 `hx` 拆成退化/非退化两支。

  ## 1  ⚠ 关键技术真相（本文件的核心诚实边界）

  **「无前件 `Tendsto … θstar`」是不可能证的 —— 它在 `x = 0` 时是假的。**

  `linWorld`（`Fate/ThetaConvergence.lean:130`）的单步写入是 `θ ↦ θ * x`；
  在 `x = 0` 时（`Fate/ThetaConvergence.lean` 的 `linWorld_predFrom`）：

  ```
  predFrom linWorld θ u ε a 0 = θ * 0 = 0
  观测            y = θstar * 0 = 0
  残差            observe id y - predFrom = 0 - 0 = 0
  写回            θ + η * φ 0 = θ + η * 0 = θ        （φ : ℝ →+ ℝ，map_zero）
  ```

  即 **`x = 0` 时端到端迭代恒等于 `θ₀`**（`endToEndIter_linWorld_at_zero`），
  极限是 `θ₀` 而**不是** `θstar`（除非 `θ₀ = θstar`）。

  **⟹ 正确的「无数据前件」形式是 case-split：`x = 0 → θ₀`，`x ≠ 0 → θstar`。**
  这就是本文件的 §1 与 §2。**本文件绝不声称无前件的 `Tendsto … θstar`。**

  ## 2  本文件的三条定理

  | 节 | 定理 | 前件 | 结论 |
  |---|---|---|---|
  | §1 | `endToEndIter_linWorld_at_zero` | 无 | `x = 0` 时 `n` 步恒等于 `θ₀` |
  | §2 | `endToEndIter_linWorld_tendsto_unconditional` | 只有 `|1-η| < 1` | `x = 0 → Tendsto … θ₀` ∧ `x ≠ 0 → Tendsto … θstar` |
  | §3 | `endToEndIter_linWorld_converges_some` | 只有 `|1-η| < 1` | `∃ L, Tendsto … L`（对**任意** `x`，零数据前件）|

  ## 3  ⚠ 自查（纪律 7：「前件是否把结论包进去」）

  * §1：**无前件**，纯等式（对一切 `η θstar θ₀ n`）。
  * §2：前件只有 `hη : |1 - η| < 1`（**关于步长**的标量条件），
    结论是**两个蕴含**：`x = 0 → Tendsto … θ₀` 与 `x ≠ 0 → Tendsto … θstar`。
    前件里**不出现**任何 `Tendsto`、**不出现** `endToEndIter`，
    也**不出现** `x` 的任何假设 —— 数据 `x` 完全自由。
  * §3：前件同样只有 `hη`。结论是**存在极限** `∃ L, Tendsto … L`；
    `L` 未被前件指定，`θ₀`／`θstar` 只是**见证**，不是假设。
    `x = 0 ∨ x ≠ 0` 是 `em`（排中律），**不是**数学假设。

  **⚠ 唯一保留的前件 `|1 - η| < 1` 是数学必需**：`η = 0` 时迭代完全不动
  （`θ_n ≡ θ₀`），`|1-η| ≥ 1` 时 `x ≠ 0` 支发散 —— 故它不是同义反复，
  而是**步长在 `(0,2)` 内**这一算法参数条件。
-/

namespace FateV2.Loop

open FateV2.Modeling
namespace EndToEndUnconditional

open Filter
open FateV2.Loop.ThetaConvergence

/-! ===========================================================================
  §1  ⭐⭐ `x = 0` 时迭代恒等
  =========================================================================== -/

/-- ⭐⭐⭐ **【`x = 0` 时端到端迭代恒等】**

$$\forall n,\quad \texttt{endToEndIter}\ \mathrm{linWorld}\ \mathrm{id}\ \eta\
  (\tfrac10 \bullet \mathrm{id})\ (\theta^* \cdot 0)\ 0\ n\ \theta_0 \;=\; \theta_0 .$$

**证明**：`x = 0` 时一步不动（`linWorld_endToEnd_apply` 展开后
`predFrom = θ * 0 = 0`、观测 `θstar * 0 = 0`，残差 `0 - 0 = 0`，
`φ 0 = 0` 故 `θ + η * 0 = θ`），再用已入库 `EndToEnd.endToEndIter_fixed`
（不动点 ⟹ 任意步数不动）。

**⚠ 不是同义反复**：**无前件**；结论是对**一切** `η θstar θ₀ n` 的等式。
`n` 在结论里出现但在前件里不出现。

**⚠ 注意 `Lean` 中 `1 / 0 = 0`**（`div_zero`），故 `x = 0` 时方向映射
`(1/0) • id` 就是零映射 —— 但上面的推导**不依赖**这一点：
`φ : ℝ →+ ℝ` 满足 `map_zero`，故 `φ 0 = 0` 对**任何**方向映射都成立。 -/
theorem endToEndIter_linWorld_at_zero (η θstar θ₀ : ℝ) (n : ℕ) :
    FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
      (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
      (θstar * 0) PUnit.unit PUnit.unit PUnit.unit 0 n θ₀ = θ₀ := by
  have hfix : FateV2.Loop.EndToEnd.endToEnd linWorld (id : ℝ → ℝ) η
      (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
      (θstar * 0) θ₀ PUnit.unit PUnit.unit PUnit.unit 0 = θ₀ := by
    rw [linWorld_endToEnd_apply]
    simp
  exact FateV2.Loop.EndToEnd.endToEndIter_fixed linWorld (id : ℝ → ℝ) η
    (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
    (θstar * 0) PUnit.unit PUnit.unit PUnit.unit 0 θ₀ hfix n

/-! ===========================================================================
  §2  ⭐⭐⭐ **无数据前件主定理：case-split 形式的 `Tendsto`**
  =========================================================================== -/

/-- ⭐⭐⭐ **【无数据前件主定理：case-split 形式】**

对**任意** `η θstar x θ₀`（`x` 是数据，**无任何假设**），只要步长满足 `|1 - η| < 1`：

* `x = 0` ⟹ 迭代 `Tendsto` 到 **`θ₀`**（不动）；
* `x ≠ 0` ⟹ 迭代 `Tendsto` 到 **`θstar`**（收敛到真值）。

**⚠ 这比 `EndToEndPipelineTendsto:225` 强在哪里**：该定理把 `hx : x ≠ 0`
当**前件**（数据条件），在 `x = 0` 时**不适用**；本条把 `x = 0` 与 `x ≠ 0`
放进**结论**的两个分支，故对**一切** `x` 都给出确定的极限。

**⚠ 为什么不能更强**（即不能写成无前件 `Tendsto … θstar`）：
`x = 0` 时极限**真的是** `θ₀` 而**不是** `θstar`（见 §1），故那样写是**假命题**。
本文件的 §0 记录了这条技术真相。

**⚠ 不是同义反复**：前件只含 `hη : |1 - η| < 1`（**步长**条件，不含 `x`、
不含 `Tendsto`、不含 `endToEndIter`）。`x = 0` 支用 §1 + 常数序列的 `Tendsto`；
`x ≠ 0` 支用已入库 `endToEndIter_linWorld_tendsto`（其中 `hx` 由本支的假设提供）。 -/
theorem endToEndIter_linWorld_tendsto_unconditional
    (η θstar x θ₀ : ℝ) (hη : |1 - η| < 1) :
    (x = 0 → Tendsto
        (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        atTop (nhds θ₀)) ∧
    (x ≠ 0 → Tendsto
        (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        atTop (nhds θstar)) := by
  constructor
  · intro hx0
    subst hx0
    have hconst : (fun n : ℕ => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * 0) PUnit.unit PUnit.unit PUnit.unit 0 n θ₀)
        = fun _ => θ₀ := by
      funext n
      exact endToEndIter_linWorld_at_zero η θstar θ₀ n
    rw [hconst]
    exact tendsto_const_nhds
  · intro hx
    exact Fate.EndToEndPipelineTendsto.endToEndIter_linWorld_tendsto
      η θstar x θ₀ hx hη

/-! ===========================================================================
  §3  ⭐⭐⭐⭐ **完全无数据前件的收敛性：两个可能极限的析取**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【完全无数据前件的收敛性：存在极限】**

对**任意** `η θstar x θ₀`（**`x` 完全自由，零数据假设**），
若步长满足 `|1 - η| < 1`，则端到端迭代**必收敛于某个 `L`**。

**⚠ 这条是本文件对 R891 建议 3 的**真正**落实**：
`x` 是数据，前件里**没有**任何关于 `x` 的假设。
唯一前件 `|1 - η| < 1` 是**关于步长**（算法参数）的，数学必需。

**⚠ 极限 `L` 是谁**不在此定理的结论里（那需要 `x = 0` 与否，
见 §2 的 case-split）；本条只声称**存在性**，
正如「一个序列必收敛」这句话本身不需要知道它的极限。

**⚠ 不是同义反复**：前件不含 `∃ L`、不含 `Tendsto`、不含 `x` 的条件。
`x = 0 ∨ x ≠ 0` 由 `em`（排中律）给出，是逻辑恒真，**不是**数学假设。

**⚠ 诚实说明**：第二条合取项 `x = 0 ∨ x ≠ 0` 是 `em x 0`，
按任务书原文保留（作「数据分支穷尽」的显式见证）；
它**不**携带数学内容，但也**不**削弱第一条 —— 第一条的 `∃ L` 才是主结论。 -/
theorem endToEndIter_linWorld_converges_some
    (η θstar x θ₀ : ℝ) (hη : |1 - η| < 1) :
    (∃ L : ℝ, Tendsto
        (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        atTop (nhds L)) ∧
    (x = 0 ∨ x ≠ 0) := by
  have h := endToEndIter_linWorld_tendsto_unconditional η θstar x θ₀ hη
  have hex : x = 0 ∨ x ≠ 0 := Classical.em (x = 0)
  refine ⟨?_, hex⟩
  by_cases hx : x = 0
  · exact ⟨θ₀, h.1 hx⟩
  · exact ⟨θstar, h.2 hx⟩

/-! ===========================================================================
  §A  速率：误差按 `|1-η|^n` 几何衰减
  =========================================================================== -/

/-- ⭐⭐⭐ **【收敛速率：误差几何衰减】**

$$\bigl|\theta_n - \theta^*\bigr|
  = \bigl|1-\eta\bigr|^{\,n}\cdot\bigl|\theta_0 - \theta^*\bigr| .$$

其中 `θ_n` **就是** `endToEndIter linWorld … n θ₀`（端到端四环闭环的迭代）。

**⚠ 为什么不是同义反复**：前件 `hx : x ≠ 0` 只保证 `1/x` 存在
（`linWorld` 的方向映射是 `(1/x) • id`，`x = 0` 时方向退化）；
结论是**关于 `n` 的定量闭式**。`n` 在前件里**不出现**，
指数律 `⟹` 几何衰减这一内容不在前件里。

**⚠ 与已入库 `ThetaConvergence.linWorld_err_closed` 的关系**：
后者是关于 `thetaN`（= `endToEndIter` 的别名）的同一命题；
本条把它**逐字落到 `endToEndIter` 的完整参数列表**上
（`EndToEndIter` 的 `W hyd h φ xobs u ε a x n θ₀` 十一位全显式），
以保证「速率定理说的是端到端迭代，不是别的算子」。 -/
theorem endToEndIter_linWorld_rate (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    |FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar|
      = |1 - η|^n * |θ₀ - θstar| :=
  linWorld_err_closed η θstar x θ₀ hx n

/-! ===========================================================================
  §B  显式误差带：给定 `ε` 存在 `N`
  =========================================================================== -/

/-- ⭐⭐⭐ **【显式误差带：`∃ N, ∀ n ≥ N, |θ_n - θ*| < ε`】**

对任意精度 `ε > 0`，存在 `N`，使**一切** `n ≥ N` 都有
`|endToEndIter linWorld … n θ₀ - θ*| < ε`。

**⚠ 为什么不是同义反复**：
- 前件是 `hx`（数据非零）、`hη : |1-η| < 1`（**步长**条件）、
  `hε : 0 < ε`（精度）、`hθ₀ : θ₀ ≠ θ*`（非退化初值）。
- 结论里的 `N` 是**前件完全未指定**的**存在量词见证**；
  前件里**没有**任何 `∀ n ≥ N` 形式的词、没有 `Tendsto`、没有 `endToEndIter` 的取值假设。
- `N` 的构造来自 `|1-η|^n → 0` 与 `ε / |θ₀-θ*| > 0`：
  `exists_pow_lt_of_lt_one` 给出 `N` 使 `|1-η|^N < ε / |θ₀-θ*|`，
  再乘以 `|θ₀-θ*|`（**正是**这个乘法需要 `θ₀ ≠ θ*`，否则 `ε/0` 无意义）。 -/
theorem endToEndIter_linWorld_explicit_N (η θstar x θ₀ : ℝ)
    (hx : x ≠ 0) (hη : |1 - η| < 1) (hθ₀ : θ₀ ≠ θstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      |FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar| < ε := by
  have hd : (0 : ℝ) < |θ₀ - θstar| := abs_pos.mpr (sub_ne_zero.mpr hθ₀)
  have hq : (0 : ℝ) < ε / |θ₀ - θstar| := div_pos hε hd
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hq hη
  have hmono : ∀ n : ℕ, N ≤ n → |1 - η|^n ≤ |1 - η|^N :=
    fun n hn => pow_le_pow_of_le_one (abs_nonneg (1 - η)) (le_of_lt hη) hn
  have hbound : |1 - η|^N * |θ₀ - θstar| < ε := by
    have h2 : (ε / |θ₀ - θstar|) * |θ₀ - θstar| = ε := div_mul_cancel₀ ε (ne_of_gt hd)
    calc |1 - η|^N * |θ₀ - θstar|
        < (ε / |θ₀ - θstar|) * |θ₀ - θstar| := mul_lt_mul_of_pos_right hN hd
      _ = ε := h2
  refine ⟨N, fun n hn => ?_⟩
  rw [endToEndIter_linWorld_rate η θstar x θ₀ hx n]
  have hle := mul_le_mul_of_nonneg_right (hmono n hn) (le_of_lt hd)
  exact lt_of_le_of_lt hle hbound

/-! ===========================================================================
  §C  严格单调性：`|1-η| < 1` 且 `θ₀ ≠ θ*` 时误差严格递减
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【误差严格单调递减】**

```
|θ_{n+1} - θ*|  <  |θ_n - θ*|        （对一切 n）
```

**⚠ 三条前件都是数学必需的（逐条给出为什么，见 §C 的文件头笔记）**：

1. `hx : x ≠ 0` —— `linWorld` 的方向映射是 `(1/x) • id`，`x = 0` 时退化。
2. `hη : |1 - η| < 1` —— 步长在 `(0,2)` 内。
3. ⚠ **`hη0 : 0 < |1 - η|`** —— **这条最容易漏，且不可省**：
   在 `η = 1` 时 `|1-η| = 0`，由 §A 的闭式误差**恒为 `0`**，
   「严格 `<`」退化为 `0 < 0`，**命题为假**
   （已入库 `ThetaConvergence.linWorld_one_step_exact` 说明 `η = 1` 一步精确到位）。
   故 `hη0` 是**必要**的，不是冗余假设。
4. `hθ₀ : θ₀ ≠ θ*` —— 若 `θ₀ = θ*` 则误差恒为 `0`，同样使严格不等式为假。

**⚠ 为什么不是同义反复**：结论是**对一切 `n` 的严格不等式**；
由 §A 的闭式它等价于 `|1-η|^{n+1}|θ₀-θ*| < |1-η|^n|θ₀-θ*|`，
两边约去 `|1-η|^n |θ₀-θ*| > 0`（**这正是 `hη0` 与 `hθ₀` 在此处的用武之地**）
得 `|1-η| < 1`，即 `hη`。
`n` 在结论里出现但**前件里不出现**；前件里**没有**任何关于 `n` 的不等式，
也**没有**任何 `endToEndIter` 的取值假设。 -/
theorem endToEndIter_linWorld_monotone (η θstar x θ₀ : ℝ)
    (hx : x ≠ 0) (hη : |1 - η| < 1) (hη0 : 0 < |1 - η|) (hθ₀ : θ₀ ≠ θstar) (n : ℕ) :
    |FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x (n + 1) θ₀ - θstar|
      < |FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar| := by
  rw [endToEndIter_linWorld_rate η θstar x θ₀ hx (n + 1),
    endToEndIter_linWorld_rate η θstar x θ₀ hx n, pow_succ]
  have hd : (0 : ℝ) < |θ₀ - θstar| := abs_pos.mpr (sub_ne_zero.mpr hθ₀)
  have hpow : (0 : ℝ) < |1 - η|^n := pow_pos hη0 n
  calc |1 - η|^n * |1 - η| * |θ₀ - θstar|
      = (|1 - η|^n * |θ₀ - θstar|) * |1 - η| := by ring
    _ < (|1 - η|^n * |θ₀ - θstar|) * 1 :=
        mul_lt_mul_of_pos_left hη (mul_pos hpow hd)
    _ = |1 - η|^n * |θ₀ - θstar| := mul_one _


end EndToEndUnconditional
end FateV2.Loop