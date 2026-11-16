/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ConvergeToOptimalStrong`
任务：**【EE1】强化版本 2：去掉 `hφ : Function.Injective φ` 前件**

===========================================================================
背景与动机
===========================================================================

`Fate/ConvergeToOptimalV2.lean` 的版本 2 主定理需要**两个**额外假设：

  `h : Corrects A φ`  **和**  `hφ : Function.Injective φ`。

但 `Fate/ConvergeToOptimalCounterexample.lean` 已证（无任何额外假设）：

  `corrects_injective : Corrects A φ ⟹ Function.Injective φ`
  `corrects_ker_eq_bot  : Corrects A φ ⟹ LinearMap.ker φ = ⊥`

⟹ **`hφ` 是冗余前件**。按作者「一切按照最优最强的来 / 可以推广的推广」，
本文件把两个主定理的 `hφ` 前件**删除**，得到严格更强的版本：

| 定理 | `ConvergeToOptimalV2` 前件 | 本文件前件 |
|---|---|---|
| `fixed_iff_optimal_strong` | `η ≠ 0`, `Corrects A φ`, **`φ` 单射** | `η ≠ 0`, `Corrects A φ` |
| `existsUnique_optimal_and_fixed_strong` | `η ≠ 0`, `Corrects A φ`, **`φ` 单射**, `A` 单射, `A` 满射 | `η ≠ 0`, `Corrects A φ`, `A` 单射, `A` 满射 |

**⭐ 后件与原版逐字相同** ⟹ 是**严格强化**（前件减少、后件不变），
**不是**同义反复：结论 `wbW … = θ ↔ IsOptimal …` 与
`∃! θ, IsOptimal … ∧ wbW … = θ` 均**不**出现在前件中。

===========================================================================
证明策略（全部用已有模块，零 sorry）
===========================================================================

* `fixed_iff_optimal_strong`：
  由 `wbW_sub` 把不动点化为 `η • φ (x' - Aθ) = 0`，
  再由 `η ≠ 0` 化为 `φ (x' - Aθ) = 0`；
  最后用 `ConvergeToOptimalCounterexample.corrects_injective` **导出**
  单射性，套 `T1Verify.fixed_iff_of_injective`。

* `existsUnique_optimal_and_fixed_strong`：
  由 `optimal_existsUnique` 得最优参数唯一存在，
  再用强化后的 `fixed_iff_optimal_strong` 把「不动点」等价替换掉。

===========================================================================
纪律声明
===========================================================================

* **零 `sorry` / `admit` / `axiom`**。
* 只新建，不修改任何已有模块（本文件仅 `import`）。
* 全部定理在 `lake env lean` 下零 error（已跑两遍）。
* 未跑全量 `lake build`（纪律 §5）。
-/

import FateWorld.FateV2.Loop.BoundWriteBack
import FateWorld.FateV2.Loop.T1Verify
import FateWorld.FateV2.Loop.ConvergeToOptimalV2
import FateWorld.FateV2.Loop.ConvergeToOptimalCounterexample
namespace FateV2.Loop

open FateV2.Modeling
namespace ConvergeToOptimalStrong

open FateV2.Loop.BoundWriteBack

variable {E F : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!
  # Loop · ConvergeToOptimalStrong

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ConvergeToOptimalStrong.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BoundWriteBack, T1Verify, ConvergeToOptimalV2, ConvergeToOptimalCounterexample
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  强化主定理 2：`fixed_iff_optimal` **去掉** `hφ`
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【EE1-a 强化主定理】`Corrects` 单独 ⟹ `wbW` 不动点 ⟺ 最优参数。**

**与原版 `ConvergeToOptimalV2.fixed_iff_optimal` 的唯一区别**：
删除了前件 `hφ : Function.Injective φ`。

**为何可以删除**：`h : Corrects A φ` 已**蕴含** `φ` 单射
（`ConvergeToOptimalCounterexample.corrects_injective`，无额外假设）。
故 `hφ` 冗余，本定理严格更强。

**非循环性检查**：前件 `{η ≠ 0, Corrects A φ}` 中**不含**
`wbW A φ η x' θ = θ` 也**不含** `IsOptimal A x' θ`；
结论是二者的等价 —— 这是真内容，不是同义反复。 -/
theorem fixed_iff_optimal_strong (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (hη : η ≠ 0)
    (h : Corrects A φ) (x' : F) (θ : E) :
    (BoundWriteBack.wbW A φ η x' θ : E) = θ ↔ FateV2.Loop.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ := by
  -- 单射性由 `Corrects` 直接导出（核心：`hφ` 前件冗余）
  have hφ : Function.Injective φ :=
    Fate.ConvergeToOptimalCounterexample.corrects_injective A φ h
  have hstep : (BoundWriteBack.wbW A φ η x' θ : E) = θ ↔ φ (x' - A θ) = 0 := by
    rw [← sub_eq_zero (a := (BoundWriteBack.wbW A φ η x' θ : E)) (b := θ),
      FateV2.Loop.ConvergeToOptimalV2.wbW_sub]
    constructor
    · intro heq
      rcases smul_eq_zero.mp heq with h0 | h0
      · exact absurd h0 hη
      · exact h0
    · intro h0
      rw [h0, smul_zero]
  rw [hstep]
  exact FateV2.Loop.T1Verify.fixed_iff_of_injective (A : E →ₗ[ℝ] F) φ hφ x' θ

/-! ===========================================================================
    §2  强化主定理 3：`existsUnique_optimal_and_fixed` **去掉** `hφ`
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【EE1-b 强化主定理】`A` 双射 + `Corrects`（无需 `φ` 单射）
⟹ 最优参数**恰有一个**，且它恰是 `wbW` 的不动点。**

**与原版 `ConvergeToOptimalV2.existsUnique_optimal_and_fixed` 的唯一区别**：
删除了前件 `hφ : Function.Injective φ`，其余前件（`hη`、`h`、`hAinj`、`hAsurj`）相同。

**含义**：版本 2 所声称的「收敛到唯一最优」**完全不需要**显式的 `φ` 单射假设
—— `Corrects` 已把它免费送上。这是可达到的最强形式。

**非循环性检查**：结论 `∃! θ, IsOptimal A x' θ ∧ wbW A φ η x' θ = θ`
不出现于前件 `{η ≠ 0, Corrects A φ, Injective A, Surjective A, x' : F}` 中。 -/
theorem existsUnique_optimal_and_fixed_strong (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (hη : η ≠ 0) (h : Corrects A φ)
    (hAinj : Function.Injective A) (hAsurj : Function.Surjective A) (x' : F) :
    ∃! θ, FateV2.Loop.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ ∧ (BoundWriteBack.wbW A φ η x' θ : E) = θ := by
  obtain ⟨θ₀, hθ₀, huniq⟩ :=
    FateV2.Loop.ConvergeToOptimalV2.optimal_existsUnique (A : E →ₗ[ℝ] F) hAinj hAsurj x'
  refine ⟨θ₀, ⟨hθ₀, ?_⟩, ?_⟩
  · exact (fixed_iff_optimal_strong A φ η hη h x' θ₀).mpr hθ₀
  · intro θ' h'
    exact huniq θ' h'.1

/-! ===========================================================================
    §3  推论：不动点集 = 最优参数集（等式形式，最强陈述）
    =========================================================================== -/

/-- ⭐⭐ **【推论：不动点集与最优参数集相等】**

强化版的集合形式：在 `Corrects`（无 `φ` 单射假设）下，
`wbW` 的不动点集**恰等于**最优参数集。

**用途**：把「收敛到最优」直接改写为「收敛到不动点」，
且**无需**任何关于 `φ` 的额外假设。 -/
theorem fixed_set_eq_optimal_set (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (hη : η ≠ 0)
    (h : Corrects A φ) (x' : F) :
    {θ : E | (BoundWriteBack.wbW A φ η x' θ : E) = θ}
      = {θ : E | FateV2.Loop.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ} := by
  ext θ
  exact fixed_iff_optimal_strong A φ η hη h x' θ

/-- ⭐⭐ **【推论：单射性由 `Corrects` 免费获得】**

把「`Corrects` ⟹ `φ` 单射」在**本强化语境下**再登记一次，
作为 §1/§2 前件删除的**正当性依据**（可独立调用，便于后续模块引用）。 -/
theorem corrects_gives_injective (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) : Function.Injective φ :=
  Fate.ConvergeToOptimalCounterexample.corrects_injective A φ h

/-! ===========================================================================
    §4  降级一致性：强化版**蕴含**原版（证明未削弱任何结论）
    =========================================================================== -/

/-- ⭐ **【一致性检验】强化版 `⟹` 原版 `fixed_iff_optimal`（逐字前件）。**

这条定理证明本文件**没有**削弱原版：凡原版能用的场合，强化版照样能用。
（说明 `hφ` 是纯冗余前件，删除是**严格加强**。） -/
theorem fixed_iff_optimal_of_old (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (hη : η ≠ 0)
    (h : Corrects A φ) (_hφ : Function.Injective φ) (x' : F) (θ : E) :
    (BoundWriteBack.wbW A φ η x' θ : E) = θ ↔ FateV2.Loop.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ :=
  fixed_iff_optimal_strong A φ η hη h x' θ

/-- ⭐ **【一致性检验】强化版 `⟹` 原版 `existsUnique_optimal_and_fixed`（逐字前件）。** -/
theorem existsUnique_of_old (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (hη : η ≠ 0) (h : Corrects A φ) (_hφ : Function.Injective φ)
    (hAinj : Function.Injective A) (hAsurj : Function.Surjective A) (x' : F) :
    ∃! θ, FateV2.Loop.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ ∧ (BoundWriteBack.wbW A φ η x' θ : E) = θ :=
  existsUnique_optimal_and_fixed_strong A φ η hη h hAinj hAsurj x'

end ConvergeToOptimalStrong

end FateV2.Loop