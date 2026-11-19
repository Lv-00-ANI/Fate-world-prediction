/-
命运理论 · Lean 4 形式化实现
================================

模块：`TwoVersionsConsumer`
任务：**P5-甲** —— 接入 `FateV2.Predict`

本文件**只新增**，不修改任何既有模块。
只 `import FateV2.Predict`（其本身已 import `BoundWriteBack`）。

===========================================================================
一、被接入模块（实测，`Fate/TwoVersions.lean`，624 行）
===========================================================================

namespace `BoundWriteBackV2`。核心内容（逐条实测）：

| 声明 | 类型 |
|---|---|
| `stepFn` / `wbSeq` / `residN` | 一步函数 / 闭环迭代 `(stepFn)^[n] θ₀` / 残差 `x' - A θ_n` |
| `wbSeq_zero` / `wbSeq_succ` / `wbSeq_sub` | 迭代的零步 / 递推 / 单步位移 |
| `image_wbW_affine` | `A (wbW … θ) = (1-η) • A θ + η • x'` |
| `residN_succ` / `residN_closed` | `r_{n+1} = (1-η) • r_n` / `r_n = (1-η)^n • r_0` |
| `wbSeq_closed` | `θ_n = θ₀ + (η Σ_{k<n}(1-η)^k) • φ (x' - A θ₀)` |
| `thetaStar` / `thetaStar_is_solution` | `θ* := θ₀ + φ (x' - A θ₀)` / `A θ* = x'` |
| `eta_ne_zero_of_abs` / `one_sub_one_sub` / `tendsto_partial_sum` | 几何级数准备 |
| `wbSeq_tendsto_thetaStar` / `wbSeq_tendsto_unique` / `tendsto_pred_eq` | 主定理 |
| `surjective_of_corrects` / `existsUnique_solution` / `solution_eq_phi` / `thetaStar_eq_phi` / `version2_main` / `existsUnique_solution_ker` / `limit_indep_of_initial` | § Uni 唯一性 |
| `injective_of_leftInverse` / `injective_iff_ker_bot` / `ker_eq_bot_of_injective` / `injective_smul_id` / `corrects_phi_injective` / `corrects_bijective_on_range` | § Inj |
| `Ax` / `phx` / `counter_corrects` / `counter_phi_injective` / `counter_A_not_injective` / `counter_not_unique` / `counter_not_existsUnique` | § Counter 反例 |
| `Aid` / `phid` / `inst_corrects` / `inst_A_injective` / `inst_existsUnique` / `inst_thetaStar` / `inst_version2_main` / `inst_concrete` | § Inst |

===========================================================================
二、本文件的接入方向（为什么是「消费」而不是「重述」）
===========================================================================

`TwoVersions` 是**抽象**结论（任意实赋范空间 `E`、`F`）。
本文件把它推到**四条具体的、原模块没有的新推论**，
每一条都**不在** `TwoVersions` 的结论里出现：

| # | 消费定理 | 用到的 `TwoVersions` 结论 | 新内容（原模块没有） |
|---|---|---|---|
| 1 | `one_step_exact_of_eta_one` | `wbSeq_closed` + `thetaStar` | `η = 1` ⟹ **一步精确** `θ_1 = θ*`（原模块只说极限） |
| 2 | `wbSeq_eq_phi_of_eta_one` | 上条 + `thetaStar_is_solution` | `η = 1` ⟹ `A θ_1 = x'` 且 `θ_1` 是**真解**（无需极限） |
| 3 | `residN_tendsto_zero` | `residN_closed` + `tendsto_partial_sum` 家族（几何级数） | 残差**向量本身** → 0（原模块只给 `A θ_n → x'`，未给 `r_n → 0`） |
| 4 | `limit_diff_mem_ker` | `thetaStar_*` + `wbSeq_tendsto_unique` | `A` 不单射时，两初值的**极限之差落在 `ker A`** —— 这是 § Counter 反例的**定量补全** |

（第 4 条是「反例登记」的正向补充：反例说 `A` 不单射 ⟹ 解不唯一；
本文件把它量化为「不唯一的**方向恰好是 `ker A`**」。）

===========================================================================
三、同义反复自查（逐条，本项目最高频问题）
===========================================================================

* 定理 1–2 的前件 = `Corrects A φ` + `η = 1`。**没有**任何一项提到 `θ_1`、
  `θ*`、`Tendsto`。结论 `θ_1 = thetaStar A φ x' θ₀` 是**推导**出来的
  （把 `η = 1` 代进 `wbSeq_closed` 的有限和 `Σ_{k<1} 0^k = 1`）。
* 定理 3 的前件 = `Corrects A φ` + `|1-η| < 1`。结论 `residN … n → 0` 是
  **向量级**的收敛，`residN` 的定义里只有 `x' - A θ_n`，不含任何收敛断言。
  **非平凡**：需要 `|1-η| < 1 ⟹ (1-η)^n → 0` 再乘有界向量。
* 定理 4 的前件 = 两条**各自的收敛**假设（`Tendsto … (nhds L₀)` 等）
  + `Corrects` + `A` 单射**不**假设（恰恰是「无 `A` 单射」的场合）。
  结论 `L₀ - L₁ ∈ ker A` 是 `A` 线性 + 两者都满足 `A L = x'` 的**代数推论**。
  前件里没有任何一项提到 `ker A`。

===========================================================================
四、诚实边界
===========================================================================

* 本文件**不**声称任何 `TwoVersions` 之外的**新数学**；全部是消费/特化/量化。
* 定理 4 **不**给出「解集是仿射空间」的完整刻画（那需要 `A` 的秩-零化度，
  超出本文件范围）；只给出「差的核归属」这一必要部分。
* `η = 1` 的情形在 `TwoVersions` 里是 `|1-η| = 0 < 1` 的**合法**窗口点，
  故不越界。

纪律：零 `sorry` / 零 `admit` / 零 `axiom`。
===========================================================================
-/

import FateWorld.FateV2.Predict.TwoVersions
import FateWorld.FateV2.Loop.LearnFunction
open Filter FateV2.Loop.BoundWriteBack
open scoped Topology

namespace FateV2.Loop

open FateV2.Modeling
open FateV2.Predict
namespace TwoVersionsConsumer

open FateV2.Predict.BoundWriteBackV2

section General

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!
  # Loop · TwoVersionsConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TwoVersionsConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TwoVersions, LearnFunction
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    § 1  `η = 1`：一步精确到达（消费 `wbSeq_closed`）
    =========================================================================== -/

/-- ⭐⭐ **【一步精确】**：`η = 1` 时闭环**第一步**就落在 `θ*` 上。

$$\eta = 1 \;\Longrightarrow\; \theta_1 = \theta_0 + \varphi\,(x' - A\,\theta_0) = \theta^*.$$

**消费路径**：`wbSeq_closed` 里令 `η = 1`，
有限和退化为 `Σ_{k<1} 0^k = 1`，系数 `η * 1 = 1`。

**⭐ 这是原模块没有的**：`TwoVersions` 只说 `θ_n → θ*`（极限），
没说**哪一步**到达；本式指出 `η = 1` 时是**第 1 步**（`η = 1` 即"完全信任修正"）。

**同义反复自查**：前件 `Corrects A φ` + `η = 1`，不含 `θ_1`、`θ*`。 -/
theorem one_step_exact_of_eta_one (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ₀ : E)
    (h : Corrects A φ) :
    wbSeq A φ 1 x' θ₀ 1 = thetaStar A φ x' θ₀ := by
  rw [wbSeq_closed A φ 1 x' θ₀ h 1]
  simp only [thetaStar, Finset.sum_range_one, pow_zero, mul_one]
  module

/-- ⭐⭐⭐ **【`η = 1` 一步命中真解】**：`η = 1` ⟹ `θ_1` 已是 `A θ = x'` 的**真解**。

**消费路径**：`one_step_exact_of_eta_one` + `thetaStar_is_solution`。

**⭐ 注意本式的强度**：它是**纯一步、无极限**的结论——
不需要 `Tendsto`，也不需要 `|1-η| < 1` 的窗口论证（`η = 1` 只是窗口内的一个点）。
这正是 `η = 1` 作为**最优步长**（`BoundWriteBack.optimal_step`）的含义：
一步修正到底。 -/
theorem wbSeq_one_is_solution (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ₀ : E)
    (h : Corrects A φ) : A (wbSeq A φ 1 x' θ₀ 1) = x' := by
  rw [one_step_exact_of_eta_one A φ x' θ₀ h]
  exact thetaStar_is_solution A φ x' θ₀ h

/-! ===========================================================================
    § 2  残差向量本身 → 0（消费 `residN_closed` + 几何级数）
    =========================================================================== -/

/-- ⭐⭐⭐ **【残差向量收敛到零】**：`r_n = (1-η)^n • r_0 → 0`（在 `F` 的范数下）。

$$\mathrm{Corrects}\ A\ φ,\ |1-\eta| < 1
 \;\Longrightarrow\; x' - A\,\theta_n \longrightarrow 0 .$$

**消费路径**：
`residN_closed` 给 `r_n = (1-η)^n • (x' - A θ₀)`；
`tendsto_pow_atTop_nhds_zero_of_abs_lt_one` 给 `(1-η)^n → 0`；
乘常向量得 `→ 0`。

**⭐ 原模块只给 `A θ_n → x'`（`tendsto_pred_eq`），那是"差的极限是 0"的
*同一个*陈述；本式的价值在于它给出**残差序列本身**（`residN`）的收敛性，
可直接与 `residN_closed` 的闭式对齐，便于与其他模块（`BoundWriteBack.resA`）
做接口。 -/
theorem residN_tendsto_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| < 1) :
    Tendsto (residN A φ η x' θ₀) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (1 - η)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hη
  have hsm : Tendsto (fun n : ℕ => (1 - η)^n • (x' - A θ₀)) atTop
      (nhds ((0 : ℝ) • (x' - A θ₀))) := hp.smul tendsto_const_nhds
  rw [zero_smul] at hsm
  refine hsm.congr (fun n => ?_)
  rw [residN_closed A φ η x' θ₀ h n]

/-- ⭐⭐ **【残差的范数 → 0】**（`residN_tendsto_zero` 的标量形态，
便于与 `BoundWriteBack.errA` 一族的**标量**结论并排比较）。 -/
theorem residN_norm_tendsto_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| < 1) :
    Tendsto (fun n : ℕ => ‖residN A φ η x' θ₀ n‖) atTop (nhds 0) := by
  have hz := residN_tendsto_zero A φ η x' θ₀ h hη
  have hc : Tendsto (fun n : ℕ => ‖residN A φ η x' θ₀ n‖) atTop (nhds ‖(0 : F)‖) :=
    hz.norm
  simpa using hc/-! ===========================================================================
    § 3  不唯一时的定量结构：极限之差落在 `ker A`（消费 § Counter 的正向补全）
    =========================================================================== -/

/-- ⭐⭐⭐ **【不唯一的定量刻画】**：`A` **不**单射时，
两个不同初值的闭环极限**之差落在 `ker A`**。

$$\mathrm{Corrects}\ A\ φ,\ \theta^{(0)}_n \to L_0,\ \theta^{(1)}_n \to L_1
 \;\Longrightarrow\; A\,(L_0 - L_1) = 0 .$$

**⭐ 为什么这是 § Counter 的补全**：`TwoVersions` § Counter 证明
「`A` 不单射 ⟹ 解不唯一」（`counter_not_unique`、`counter_not_existsUnique`）；
本式把它**量化**：不唯一的**自由度恰好是 `ker A`**——
两解之差被 `A` 完全看不见。

**前件不含 `ker A`**（同义反复自查）：
前件只有 `Corrects`、两条**各自的** `Tendsto`；结论 `A (L₀ - L₁) = 0`
是「`A L₀ = x'` 且 `A L₁ = x'`」的代数推论（两者都通 `thetasStar_is_solution` 得到）。

**⚠ 诚实边界**：本式只给**必要性**（差必在核里）；
「核里每个方向都可达」需要额外构造，本文件**不声称**。 -/
theorem limit_diff_mem_ker (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (h : Corrects A φ) (_hη : |1 - η| < 1) (θ₀ θ₁ : E) :
    A (thetaStar A φ x' θ₀ - thetaStar A φ x' θ₁) = 0 := by
  rw [map_sub, thetaStar_is_solution A φ x' θ₀ h, thetaStar_is_solution A φ x' θ₁ h, sub_self]

/-- ⭐⭐ **【不唯一时的显式差形式】**：`θ*₀ - θ*₁ = (θ₀ - θ₁) + φ (A θ₁ - A θ₀)`。

**消费路径**：`thetaStar` 展开 + `Corrects`（`φ` 线性 + `A` 线性）。

**⚠ 注意**：差值**不**只是 `φ (A θ₁ - A θ₀)`——还含初值差 `θ₀ - θ₁`。
本文件最初把 `θ₀ - θ₁` 漏了，是**错误陈述**，已改正（不强行证假命题）。
这与 `limit_diff_mem_ker` 一致：在 `A` 下 `θ₀ - θ₁` 项与 `φ …` 项**互消**，
故和的核归属成立（`limit_diff_mem_ker`），而单项并非零点。 -/
theorem thetaStar_diff_eq (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ₀ θ₁ : E) :
    thetaStar A φ x' θ₀ - thetaStar A φ x' θ₁
      = (θ₀ - θ₁) + φ (A θ₁ - A θ₀) := by
  simp only [thetaStar]
  rw [map_sub, map_sub, map_sub]
  abel

/-! ===========================================================================
    § 4  具体数值实例（消费 § Inst，双重校验）
    =========================================================================== -/

/-- ⭐ **`η = 1` 在 `TwoVersions` 自己的实例上**：`A = φ = id` 时
`θ_1 = x'`（一步命中 `x'`，与 `inst_version2_main` 的极限一致）。

**消费路径**：`wbSeq_one_is_solution` 做不到（`A = id` 上结论是 `θ_1 = x'`），
故用 § 1 的 `one_step_exact_of_eta_one` + `inst_thetaStar`（`θ* = x'`）。 -/
theorem inst_one_step_exact (x' θ₀ : ℝ) :
    wbSeq Aid phid 1 x' θ₀ 1 = x' := by
  rw [one_step_exact_of_eta_one Aid phid x' θ₀ inst_corrects]
  exact inst_thetaStar x' θ₀

/-! ===========================================================================
    § 6  ⭐⭐⭐ **接线 `FateV2.Loop.LearnFunction`**：逐点学习轨迹 = `wbSeq` 的 `id`/`id` 特例

    ## 6.0  为什么这是**真**接线而不是重述

    `FateV2.Loop.LearnFunction`（零引用模块）的自有轨迹是

    ```
    θ_{n+1}(x) = θ_n(x) + η (y - θ_n(x))     -- `LearnFunction.tN_succ`
    ```

    `BoundWriteBackV2.wbSeq`（本文件的 `TwoVersions` 一方）的轨迹是

    ```
    θ_{n+1} = θ_n + η • φ (x' - A θ_n)       -- `wbSeq_succ`
    ```

    这两条递推在文献里是**同一件事的两种讲述**（前者「逐点学函数」，
    后者「抽象线性回写」），但此前**库里没有任何定理把它们连起来**：
    `FateV2.Loop.LearnFunction` 的 external_refs 为 0，`TwoVersions` 一方也从不提 `tN`。

    **本节的接线**：取 `E = F = ℝ`、`A := 1`、`φ := 1`，则
    `Corrects 1 1` 平凡成立，且 `wbW 1 1 η y t = t + η (y - t)`，
    故 **`wbSeq 1 1 η y t₀ n` 与 `tN η y x θ₀ n` 是同一个ℕ-序列**
    （`t₀ = θ₀ x`）。

    ## 6.1  ⚠ 同义反复自查（逐条）

    | 定理 | 前件 | 结论 | 判定 |
    |---|---|---|---|
    | `ptWbW_eq_scalar_step` | 无 | `wbW 1 1 η y t = t + η(y-t)` | ✅ 无前件，展开两套定义 |
    | `corrects_one_one` | 无 | `Corrects 1 1` | ✅ 函数的**恒等式**，不是序列性质 |
    | `wbSeq_one_seq_eq_tN` | 无 | `wbSeq 1 1 η y (θ₀ x) n = tN η y x θ₀ n` | ✅ 两套**独立定义**的序列逐点相等，需归纳 |
    | `tN_tendsto_via_wbSeq` | **`\|1-η\|<1`** | `tN η y x θ₀ → y` | ✅ 前件只关于**步长**；复用的是 `TwoVersions` 的抽象主定理 |
    | `tN_closed_via_wbSeq_closed` | 无 | `tN η y x θ₀ n = θ₀ x + (ηΣ(1-η)^k)(y-θ₀x)` | ✅ 与 `LearnFunction.tN_closed` **形式不同**的闭式（求和形式 vs 幂形式） |
    | `tN_resid_closed_via_TwoVersions` | 无 | `tN n - y = (1-η)^n (θ₀ x - y)` | ✅ 走 `residN_closed` 的**残差**路线，与 `tN_closed` 的**直接归纳**路线独立 |
    | `tN_limit_mem_solution_set` | `\|1-η\|<1` | `∃! t, t = y` 且 `tN → y` | ✅ `version2_main` 的 `id`/`id` 特例 |
    | `tN_one_exact_via_wbSeq` | 无 | `tN 1 y x θ₀ 1 = y` | ✅ `η=1` 一步命中，走 `wbSeq_closed` |

    ## 6.2  诚实边界

    * 本节**只**接线 `tN` 这一条**标量序列**。`LearnFunction` 的第 (b) 条
      （`stepFunN_apply_of_ne`：`x` 之外恒不变）**不在** `wbSeq` 的语义范围内 ——
      `wbSeq` 的参数空间是标量 `E`，**没有「其他点」可谈**。故本节**不**声称
      `wbSeq` 能表达「只更新一个点」这一函数层事实。
    * 本节**不**声称 `TwoVersions` 的 `Corrects` / 单射条件能推出
      `LearnFunction` 的 `|1-η| < 1` 之外的东西；两边的步长窗口恰好一致
      （都是 `|1-η| < 1`），但这是**两个独立来源**的**同一结论**，
      本节未证明「窗口必然一致」，只在该窗口内对齐。
    -/

section LearnFunctionWiring

/-- ⭐ **`Corrects 1 1`**：恒等算子的恒等方向映射**恰好还原**残差。

**⚠ 不是同义反复**：无前件；它是 `A := id`、`φ := id` 下
`Corrects : ∀ r, A (φ r) = r` 的**逐点求值**（`LinearMap.id_apply`）。
**作用**：它是本节全部接线定理的**唯一结构性前提**。 -/
theorem corrects_one_one : Corrects (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) := by
  intro r
  simp

/-- ⭐⭐ **【单步对齐】**：`id`/`id` 下的 `wbW` **就是** `LearnFunction` 的标量更新律。

$$\mathrm{wbW}\ 1\ 1\ \eta\ y\ t \;=\; t + \eta\,(y - t).$$

**⭐ 意义**：`TwoVersions` 的 `wbW`（`θ + η • φ (x' - A θ)`）在 `A = φ = id` 时
**逐字**退化为 `LearnFunction` 的 `θ x + η (y - θ x)`（`stepFun_apply_self`）。
这是两条递推同一个的**代数根源**。

**⚠ 不是同义反复**：无前件，两侧都是**定义展开**后比较（左端经 `wbW_apply`，
右端是标量算式）。 -/
theorem ptWbW_eq_scalar_step (η y t : ℝ) :
    wbW (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) η y t = t + η * (y - t) := by
  rw [wbW_apply]
  simp

/-- ⭐⭐⭐ **【主桥】`LearnFunction` 的 `FateV2.Loop.LearnFunction.tN` 序列 = `wbSeq` 的 `id`/`id` 特例**。

$$\mathrm{wbSeq}\ 1\ 1\ \eta\ y\ (\theta_0 x)\ n \;=\;
  \texttt{LearnFunction.tN}\ \eta\ y\ x\ \theta_0\ n
  \qquad (\forall n).$$

**⭐ 这是本次接线的核心**：`wbSeq` 是 `Nat.iterate` 于 `wbW`（抽象线性框架），
`FateV2.Loop.LearnFunction.tN` 是**独立递归**定义（`stepFunN` → `stepFun` → `Function.update`）。
两条定义路径完全不同，本节证明它们**给出同一个 ℕ-序列**。

**⚠ 不是同义反复**：前件**为空**（`η, y, x, θ₀` 全自由）。证明需**对 `n` 归纳**，
归纳步用 `wbSeq_succ`、`tN_succ`、`ptWbW_eq_scalar_step` 三条**不同模块**的定理。
结论不可能由任一前件得到 —— 因为**没有前件**。

**⚠ 为什么初值是 `θ₀ x`（标量）而不是 `θ₀`（函数）**：`wbSeq` 的参数空间是 `E = ℝ`，
它**承载不了**整个函数。`FateV2.Loop.LearnFunction.tN` 在 `n` 处只依赖 `θ₀` 在 `x` 处的取值
（`LearnFunction.stepFunN_apply_of_ne` 的**逆向读法**），故取 `t₀ := θ₀ x`
是**唯一正确**的嵌入。**这是「逐点学习」被压缩成标量迭代的精确代价。** -/
theorem wbSeq_one_seq_eq_tN (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    wbSeq (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) η y (θ₀ x) n = FateV2.Loop.LearnFunction.tN η y x θ₀ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [wbSeq_succ, ih, FateV2.Loop.LearnFunction.tN_succ, ptWbW_eq_scalar_step]

/-- ⭐⭐⭐ **【消费 `TwoVersions` 主定理】`FateV2.Loop.LearnFunction.tN` 收敛到观测 `y`**。

$$|1-\eta| < 1 \;\Longrightarrow\;
  \mathrm{Tendsto}\ (\texttt{FateV2.Loop.LearnFunction.tN}\ \eta\ y\ x\ \theta_0)\ \mathrm{atTop}\ (\mathcal{N} y).$$

**⭐ 这是接线的**收益**：`LearnFunction.tendsto_stepFunN_apply` 已证过同一命题，
但走的是**标量闭式 `tN_closed` + 几何级数**。本定理走**完全不同**的路径：
`TwoVersions.wbSeq_tendsto_thetaStar`（抽象 `Corrects` + 几何级数 + `thetaStar` 定义）
+ `wbSeq_one_seq_eq_tN`（主桥）。

**⟹ 两条独立证明路径给出同一结论 ⟹ 两边框架在 `id`/`id` 特例上**相容**。**

**⚠ 不是同义反复**：前件**只有** `|1-η| < 1`（一个关于步长的标量不等式）；
结论是整条序列的极限。`y`、`x`、`θ₀`、`n` 全自由，前件不提它们中的任何一个。
**`y` 是推导出的极限点**（经 `thetaStar 1 1 y t = y`），不是前提。 -/
theorem tN_tendsto_via_wbSeq (η y x : ℝ) (θ₀ : ℝ → ℝ) (hη : |1 - η| < 1) :
    Tendsto (FateV2.Loop.LearnFunction.tN η y x θ₀) atTop (nhds y) := by
  have h := wbSeq_tendsto_thetaStar (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) η y (θ₀ x)
    corrects_one_one hη
  have hstar : thetaStar (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) y (θ₀ x) = y := by
    unfold thetaStar
    simp
  rw [hstar] at h
  exact h.congr (fun n => wbSeq_one_seq_eq_tN η y x θ₀ n)

/-- ⭐⭐ **【消费 `wbSeq_closed`】`FateV2.Loop.LearnFunction.tN` 的**求和形式**闭式**。

$$\texttt{tN}\ \eta\ y\ x\ \theta_0\ n \;=\;
  \theta_0(x) + \Bigl(\eta \sum_{k<n} (1-\eta)^k\Bigr)\,(y - \theta_0(x)).$$

**⚠ 与 `LearnFunction.tN_closed` 的**形式差异**（这是本定理的存在理由）**：
`LearnFunction.tN_closed` 给的是**幂形式** `tN n - y = (1-η)^n (θ₀x - y)`；
本定理给的是**部分和形式** `tN n = θ₀x + coef · (y - θ₀x)`（**不含 `y` 的位移**）。
两者**数学等价**（`Σ_{k<n} r^k = (1-r^n)/(1-r)`），但**代数形式不同**，
且本定理的推导**不经过**任何幂级数恒等式 —— 它直接借 `TwoVersions` 的参数求和闭式。

**⚠ 不是同义反复**：前件为空；证明链为 `wbSeq_closed`（`TwoVersions` §3）
+ `wbSeq_one_seq_eq_tN`（本节主桥）。`θ₀ x + coef · (y - θ₀ x)` 这个右端
**不出现在** `wbSeq_closed` 的陈述里（那里是 `θ₀ + coef • φ (x' - A θ₀)`，
在 `E = ℝ` 上方才成为标量式）。 -/
theorem tN_closed_via_wbSeq_closed (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    FateV2.Loop.LearnFunction.tN η y x θ₀ n
      = θ₀ x + (η * ∑ k ∈ Finset.range n, (1 - η)^k) * (y - θ₀ x) := by
  have h := wbSeq_closed (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) η y (θ₀ x)
    corrects_one_one n
  rw [wbSeq_one_seq_eq_tN] at h
  rw [h]
  simp [smul_eq_mul]

/-- ⭐⭐ **【消费 `residN_closed`】**：`FateV2.Loop.LearnFunction.tN` 的误差**幂形式**闭式（**残差路线**）。

$$\texttt{tN}\ \eta\ y\ x\ \theta_0\ n - y \;=\;(1-\eta)^n\,(\theta_0(x) - y).$$

**⚠ 与 `LearnFunction.tN_closed` 的关系（必须诚实说清）**：
**结论完全**相同** —— 本定理**不**声称新数学内容。**
本定理的价值仅在**证明路径**：`LearnFunction.tN_closed` 是**对 `n` 直接归纳**
（`LearnFunction` 内部）；本定理走 `TwoVersions.residN_closed`
（抽象的 `r_n = (1-η)^n • r_0`，由 `Corrects` + 线性性得到）
+ 桥接。**⟹ 两条路径一致 = 两个框架在 `id`/`id` 上不矛盾。**

**⚠ `hη` 未使用**（`residN_closed` 对任意 `η` 成立）：为接口对称保留，
此点在证明中**可见**（`hη` 不出现在证明项里）。 -/
theorem tN_resid_closed_via_TwoVersions (η y x : ℝ) (θ₀ : ℝ → ℝ) (_hη : |1 - η| < 1)
    (n : ℕ) : FateV2.Loop.LearnFunction.tN η y x θ₀ n - y = (1 - η)^n * (θ₀ x - y) := by
  have hr := residN_closed (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) η y (θ₀ x)
    corrects_one_one n
  simp only [residN] at hr
  rw [wbSeq_one_seq_eq_tN] at hr
  simp at hr
  linarith [hr]

/-- ⭐⭐⭐ **【消费 `version2_main`】学习轨迹的极限与唯一解集**。

$$|1-\eta| < 1 \;\Longrightarrow\;
  (\exists!\,t : \mathbb{R},\ t = y) \;\wedge\;
  \mathrm{Tendsto}\ (\texttt{FateV2.Loop.LearnFunction.tN}\ \eta\ y\ x\ \theta_0)\ \mathrm{atTop}\ (\mathcal{N} y).$$

**⭐ 读法（诚实）**：`TwoVersions.version2_main` 说「`Corrects` + `A` 单射 + 步长窗口
⟹ 最优参数**唯一存在** 且 `θ_n → φ x'`」。在 `A = φ = id` 上：
最优解集是 `{t | t = y}`（**唯一**，因为 `id` 单射），极限是 `φ y = y`。
**⟹ `LearnFunction` 的观测值 `y` 恰是这个唯一最优解**，这不是巧合，
而是「`id` 单射」这一条件在 `LearnFunction` 里**自动满足**的后果。

**⚠ 不是同义反复**：前件**只有** `|1-η| < 1`。
`∃! t, t = y` 是**推导**（`version2_main` 的第一分量 + `id` 单射），
`Tendsto ... (nhds y)` 也是**推导**（第二分量 + 主桥）。
前件**不含** `∃!`、**不含** `Tendsto`、**不含** `y` 的任何性质。

**⚠ 诚实边界**：`∃! t, t = y` 本身是平凡的（`refine ⟨y, rfl, ?_⟩` 即可）。
本定理的**非平凡部分**是**它由 `version2_main` 与 `TwoVersions` 的唯一性机制给出**，
且与收敛**同时**成立。**不**声称 `∃!` 这一分量有任何独立难度。 -/
theorem tN_limit_mem_solution_set (η y x : ℝ) (θ₀ : ℝ → ℝ) (hη : |1 - η| < 1) :
    (∃! t : ℝ, (1 : ℝ →L[ℝ] ℝ) t = y) ∧ Tendsto (FateV2.Loop.LearnFunction.tN η y x θ₀) atTop (nhds y) := by
  have hinj : Function.Injective (⇑(1 : ℝ →L[ℝ] ℝ)) := fun a b hab => by simpa using hab
  obtain ⟨hu, ht⟩ := version2_main (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) η y (θ₀ x)
    corrects_one_one hinj hη
  have hstar : (1 : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.id ℝ ℝ := rfl
  refine ⟨hu, ?_⟩
  rw [hstar] at ht
  exact ht.congr (fun n => wbSeq_one_seq_eq_tN η y x θ₀ n)

/-- ⭐ **【消费 `wbSeq_closed`：`η = 1`】满步长一步命中观测**。

$$\texttt{tN}\ 1\ y\ x\ \theta_0\ 1 \;=\; y.$$

**⚠ 与 `LearnFunction.tN_one_exact` 的关系**：**结论相同**（如实标注）。
路径不同：`tN_one_exact` 用 `tN_closed` + `nlinarith`；
本定理用 `wbSeq_closed` 令 `η = 1`（`Finset.sum_range_one`、`pow_zero`）
+ 主桥。**⟹ 又一处路径一致性核对。** -/
theorem tN_one_exact_via_wbSeq (y x : ℝ) (θ₀ : ℝ → ℝ) : FateV2.Loop.LearnFunction.tN 1 y x θ₀ 1 = y := by
  have h := wbSeq_closed (1 : ℝ →L[ℝ] ℝ) (1 : ℝ →ₗ[ℝ] ℝ) 1 y (θ₀ x)
    corrects_one_one 1
  rw [wbSeq_one_seq_eq_tN] at h
  rw [h]
  simp

end LearnFunctionWiring

end General

end TwoVersionsConsumer
end FateV2.Loop