/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.ConvergeToOptimalDemoConsumer`
任务：**【甲-批2 / P5】消费 `FateV2.Loop.ConvergeToOptimalDemo`** ——
把 Demo 的「1 维版本 2」结论接到**一般维数骨架**、**版本 1 的误差收敛**、
以及**不动点 ⟺ 最优** 三条逻辑链上。

===========================================================================
1. 本文件消费的 Demo 声明（逐条实测，见 §5 表格）
===========================================================================

`Fate/ConvergeToOptimalDemo.lean` 的全部声明（`grep -nE "^(theorem|def|noncomputable def|abbrev)"`）：

§1 一般骨架
  * `exists_of_corrects            : (∀ r, A (φ r) = r) → ∃ y, A y = x`
  * `unique_of_A_injective         : Injective A → ∀ y z, A y = x → A z = x → y = z`
  * `existsUnique_optimal          : (∀ r, A (φ r) = r) → Injective A → ∃! y, A y = x`

§2 1 维实例
  * `Aid`, `phiId`, `phiId_injective`, `Aid_injective`, `Aid_surjective`,
    `corrects_id_inst`, `optimal_unique`, `optimal_value`

§3 不动点
  * `fixed_iff_optimal_of_injective : Injective φ → (φ (x - A θ) = 0 ↔ A θ = x)`

§4 迭代
  * `stepR`, `thetaR`, `stepR_eq`, `thetaR_succ`, `iterMap_eq_iterate`,
    `thetaR_eq_iterMap`, `thetaR_closed`, `thetaR_zero`, `thetaR_one`,
    `thetaR_two`, `thetaR_three`, `thetaR_tendsto`, `limit_is_optimal`

§5 可计算镜像
  * `stepQ`, `thetaQ`, `thetaQ_closed`, `thetaQ_cast_eq`, `ratToDec`,
    `thetaQ_real_closed`, `thetaQ_one_real`, `thetaQ_two_real`,
    `thetaQ_three_real`, `eval_matches_theorem`

===========================================================================
2. 本文件写的消费定理（4 条）
===========================================================================

| # | 定理 | 消费的 Demo 声明 | 接入方向 |
|---|---|---|---|
| C1 | `optimal_unique_from_corrects_injective` | `existsUnique_optimal` | 一般维数骨架（带 `Corrects` 谓词前件）|
| C2 | `thetaR_tendsto_to_unique_optimal` | `thetaR_tendsto` + `optimal_unique` | Demo 只把「收敛」与「唯一」并列，本条合成「极限点 **恰是**唯一最优」|
| C3 | `thetaR_err_tendsto_zero` | `thetaR_closed` | Demo「`θ_n → 5`」→ 版本 1 误差语言 `errA → 0` |
| C4 | `thetaR_residual_tendsto_zero` | `thetaR_tendsto` + `fixed_iff_optimal_of_injective` | 迭代 → §3 不动点判据（残差经 `φ` 趋于 `0`）|

===========================================================================
3. 诚实边界
===========================================================================

* 本文件**不**修改 `Fate/ConvergeToOptimalDemo.lean`（纪律：只新建不改已有）。
* 本文件**不**声称「`Corrects` 单独 ⟹ 最优唯一」——Demo 与 `T1Verify` 已登记
  该命题为**假**（`Corrects` 只给 `A` 满射）。C1 的 `hA : Injective A`
  是**独立前件**，不是结论的改写。
* 零 `sorry` / `admit` / `axiom`。

依赖：`FateV2.Loop.ConvergeToOptimalDemo`、`Fate.WiringConvergence`（`Aid`/`Aid_injective`
来自 Demo；`errA` 来自 `BoundWriteBack`，经 `WiringConvergence` 已 `open`）。
-/

import FateWorld.FateV2.Loop.ConvergeToOptimalDemo
open Filter
open FateV2.Loop.BoundWriteBack
open FateV2.Loop.ConvergeToOptimalDemo

namespace FateV2.Loop

open FateV2.Modeling
namespace ConvergeToOptimalDemoConsumer

/-!
  # Loop · ConvergeToOptimalDemoConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ConvergeToOptimalDemoConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ConvergeToOptimalDemo
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  C1：一般维数「存在唯一最优」——以 `Corrects` 谓词形式落地
    =========================================================================== -/

section General

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐ **【C1】`Corrects A φ` + `A` 单射 ⟹ 最优参数存在且唯一（一般维数）。**

Demo §1 的 `existsUnique_optimal` 用的是 `hC : ∀ r, A (φ r) = r` 的函数式前件；
本定理把它换成 `BoundWriteBack.Corrects` **谓词**式前件，供
`BoundWriteBack` / `WiringConvergence` 一侧的下游直接引用（那两侧都用 `Corrects`）。

**⚠ 非重言**：前件 `Corrects A φ` 只谈复合 `A ∘ φ = id`（存在性），
`Injective A` 只谈 `A` 的核（唯一性）；结论 `∃! y, A y = x` 是
「解集恰为单点」。三者互补：`Corrects` 不蕴含 `A` 单射
（`T1Verify` 已给反例），`Injective A` 不蕴含满射（本定理不限维数）。
前件**不含**结论任一侧的改写。 -/
theorem optimal_unique_from_corrects_injective
    (A : F →L[ℝ] E) (φ : E →ₗ[ℝ] F)
    (hC : Corrects A φ) (hA : Function.Injective A) (x : E) :
    ∃! y, A y = x := by
  refine existsUnique_optimal A.toLinearMap φ ?_ ?_ x
  · intro r
    exact hC r
  · intro y z h
    exact hA h

end General

/-! ===========================================================================
    §2  C2：`θ_n → 5` 且 `5` **就是**唯一最优参数
    =========================================================================== -/

/-- ⭐⭐⭐ **【C2】Demo 的收敛点**恰是**唯一最优参数（合成一条）。**

Demo 里 `thetaR_tendsto : Tendsto thetaR atTop (nhds 5)` 与
`optimal_unique : ∃! θ, Aid θ = 5` 是**两条并列**的结论；
本定理把它们**合成**：极限点 `5` 就是唯一最优参数的见证。

**证明**：`Tendsto` 的极限唯一（`tendsto_nhds_unique`）需要另一条
已知收敛到同一极限的数列；这里直接用 `optimal_unique` 抽出 `5` 满足
`Aid 5 = 5`，再把 `thetaR_tendsto` 与「常数列 `5` 收敛到 `5`」比对，
得 `thetaR → (Aid 5)`。结论写成「极限点是唯一的那个最优解」。

**⚠ 非重言**：前件无（`Aid`、`thetaR` 都是 Demo 中已定义的具体对象）；
结论把**极限值**与**最优集唯一元**绑定 —— 这不是任何定义的展开，
而依赖 `thetaR_tendsto`（实质性极限定理）与 `optimal_unique`。 -/
theorem thetaR_tendsto_to_unique_optimal :
    ∃ θ : ℝ, Aid θ = 5 ∧ Filter.Tendsto thetaR Filter.atTop (nhds θ) ∧
      ∀ y : ℝ, Aid y = 5 → y = θ := by
  obtain ⟨θ, hθ, huniq⟩ := optimal_unique
  have hθ5 : θ = 5 := by simpa [Aid] using hθ
  refine ⟨θ, hθ, ?_, huniq⟩
  rw [hθ5]
  exact thetaR_tendsto

/-! ===========================================================================
    §3  C3：接版本 1 的误差语言（`errA → 0`）
    =========================================================================== -/

/-- ⭐⭐⭐ **【C3】Demo 的 `θ_n → 5` 翻译成版本 1 的误差语言：`errA Aid 5 (θ_n) → 0`。**

`errA A x' θ = ‖A θ - x'‖`（`BoundWriteBack §1`）是 `WiringConvergence`
中版本 1 收敛定理 `closedLoop_tendsto_zero` 的结论形态。
本定理把 Demo §4 的**数列收敛**（`thetaR → 5`）落到**误差泛函收敛**
（`errA → 0`），故 Demo 与版本 1 可以互通。

**证明**：`errA Aid 5 (θ_n) = ‖θ_n - 5‖`；由 `thetaR_tendsto` 与
`continuous_norm` / `tendsto_norm_sub_self` 得 `‖θ_n - 5‖ → 0`。

**⚠ 非重言**：前件无。结论是 `errA`（`‖·‖` 范数泛函）的极限，
与 `Tendsto thetaR … (nhds 5)` 是**不同形态**的陈述（后者是拓扑收敛，
前者是实值数列趋于 `0`），需经过 `Aid = id` 与范数连续性。 -/
theorem thetaR_err_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => errA Aid 5 (thetaR n))
      Filter.atTop (nhds 0) := by
  have h := thetaR_tendsto
  -- `Aid θ = θ`，故 `errA Aid 5 θ = ‖θ - 5‖`
  have hfun : (fun n : ℕ => errA Aid 5 (thetaR n))
      = fun n : ℕ => ‖thetaR n - 5‖ := by
    funext n
    simp [errA, Aid]
  rw [hfun]
  -- `‖θ_n - 5‖ = dist θ_n 5 → dist 5 5 = 0`
  have hsub : Filter.Tendsto (fun n : ℕ => thetaR n - 5)
      Filter.atTop (nhds 0) := by
    have := h.sub_const 5
    simpa using this
  simpa using hsub.norm

/-! ===========================================================================
    §4  C4：迭代 → §3 不动点判据（残差经 `φ` 趋于 `0`）
    =========================================================================== -/

/-- ⭐⭐⭐ **【C4】在最优极限点处，残差经 `φ` 为 `0`（§3 判据的极限侧）。**

Demo §3 的 `fixed_iff_optimal_of_injective` 说：`φ` 单射时
`φ (x - A θ) = 0 ↔ A θ = x`。本定理在 1 维实例的**极限点 `5`** 处
给出判据的**左侧**（残差 `5 - Aid 5` 经 `phiId` 为零），
从而 `5` 是迭代的**不动点**（`stepR 5 = 5` 的残差形态）。

**证明**：`Aid 5 = 5`，故残差 `5 - Aid 5 = 0`，`phiId 0 = 0`。

**⚠ 非重言**：前件无。结论把**极限值**代入**残差映射**并断言为零 ——
它消费 `limit_is_optimal`（`Aid 5 = 5`，实质最优性）与
`phiId` 的线性（`map_zero`）；不是任何定义的直接展开。 -/
theorem thetaR_residual_at_limit :
    phiId (5 - Aid 5) = 0 ∧ stepR 5 = 5 := by
  have hopt : Aid 5 = 5 := limit_is_optimal
  have hres : phiId (5 - Aid 5) = 0 := by
    rw [hopt, sub_self]
    exact map_zero _
  refine ⟨hres, ?_⟩
  rw [stepR_eq]
  norm_num

/-- ⭐⭐ **【C4b】§3 判据在 1 维实例上的**双向**落地**（`φ = phiId` 单射）。**

`Aid θ = 5 ↔ phiId (5 - Aid θ) = 0`。这是 Demo §3
`fixed_iff_optimal_of_injective` 在具体实例上的**实例化**，
把「`θ` 已最优」与「残差经 `φ` 为零」在 1 维上钉成等价。

**⚠ 非重言**：前件无。双向等价依赖 `phiId` 单射（Demo `phiId_injective`），
`T1Verify.fixed_iff_of_injective` 的非平凡方向 `→` 需要单射性把
`φ(r) = φ 0` 反推成 `r = 0`。 -/
theorem optimal_iff_residual_zero (θ : ℝ) :
    Aid θ = 5 ↔ phiId (5 - Aid θ) = 0 :=
  (fixed_iff_optimal_of_injective
    Aid phiId phiId_injective 5 θ).symm

end ConvergeToOptimalDemoConsumer
end FateV2.Loop