/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.T1VerifyStrong`
任务：**【EE2】强化 T1Verify** —— 把 `Fate/T1Verify.lean` 的
`fixed_iff_of_injective` 的**前提 `hφ : Function.Injective φ`**
替换成**更强的形式** `h : Corrects A φ`。

===========================================================================
1. 目标陈述
===========================================================================

`Fate/T1Verify.lean` 证的是：

    fixed_iff_of_injective (hφ : Function.Injective φ) :
      φ (x' - A θ) = 0 ↔ A θ = x'

即「**先假设** `φ` 单射，才有不动点 ⟺ 最优」。

本文件证它的**强化形式**：

    fixed_iff_of_corrects (h : Corrects A φ) :
      φ (x' - A θ) = 0 ↔ A θ = x'

**⚠ 方向说明（重要，避免误读）**：
`Corrects A φ` 在 `φ : F →ₗ[ℝ] E`、`A : E →L[ℝ] F` 的设定下
（见 `Fate/ConvergeToOptimalCounterexample.lean` 的 `corrects_injective`）
**本身就蕴含** `φ` 单射。因此本定理的**前提严格弱于**（= 蕴含强于）
`Function.Injective φ`：调用者不必再单独提供单射性，
`Corrects` 一个假设就够。这正是「更强的形式」的确切含义。

===========================================================================
2. 证明结构
===========================================================================

1. **`corrects_injective_here`**：`Corrects A φ ⟹ φ` 单射。
   （本文件自足地重证一遍，避免额外 import 带来的耦合；
    证明与原版一致：`Corrects` 在 `v` 处给 `A (φ v) = v`，
    故 `φ v = 0 ⟹ v = 0`，即 `ker φ = ⊥`，再由线性得单射。）

2. **`fixed_iff_of_corrects`**：把 1 喂给 `φ (x' - A θ) = 0 ↔ A θ = x'` 的
   标准论证：
   * `→`：`φ (x' - A θ) = 0 = φ 0`，单射给 `x' - A θ = 0`，故 `A θ = x'`。
   * `←`：`A θ = x' ⟹ x' - A θ = 0 ⟹ φ 0 = 0`。

3. **`fixed_iff_of_corrects'`**：`A θ - x'` 的对称写法（避免调用者先做
   符号整理），以及 **`wbW_fixed_iff_of_corrects`**：直接落到
   `Fate/BoundWriteBack.lean` 的 `wbW` 不动点形态。

===========================================================================
3. 诚实边界（不夸大）
===========================================================================

* 本文件**不**声称 `Corrects` 是**必要**条件 —— 它只是把前提从
  「单射」换成了「`Corrects`」。**是否存在既不 `Corrects` 又非单射
  却满足等价式的实例不在本文件讨论范围**。
* 本文件的定理都是 **`↔`**，**不是**同义反复：等价式左侧说的是
  「残差经 `φ` 后为零」，右侧说的是「`θ` 恰是真值原像」，
  桥接它们的是 `Corrects ⟹ φ` 单射这一**非平凡**事实。
  前件 `Corrects A φ` **不包含**结论中的任何一侧（`Corrects` 只谈
  `A ∘ φ`，结论谈 `φ (x' - A θ)` 与 `A θ = x'`，两者不同）。
* 零 `sorry` / `admit` / `axiom`。

依赖：`Fate.T1Verify`（原定理）、`Fate.BoundWriteBack`（`Corrects`、`wbW`）。
-/

import FateWorld.FateV2.Loop.T1Verify
import FateWorld.FateV2.Loop.BoundWriteBack
open FateV2.Loop.BoundWriteBack

namespace FateV2.Loop
namespace T1VerifyStrong

/-!
  # Loop · T1VerifyStrong

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1VerifyStrong.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1Verify, BoundWriteBack
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  载体（与 `Fate.BoundWriteBack` 的 `Corrects` 签名一致）
    =========================================================================== -/

section Basic

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### §1.1 `Corrects ⟹ φ` 单射（本文件自足重证） -/

/-- ⭐⭐ **`Corrects A φ` ⟹ `φ` 单射。**

证明：若 `φ v = 0`，则 `v = A (φ v) = A 0 = 0`（第一条等号用 `Corrects`）。
故 `ker φ = ⊥`；线性映射 `ker = ⊥` 即单射。 -/
theorem corrects_injective_here (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) : Function.Injective φ := by
  intro v w hvw
  have hsub : φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hv : v - w = 0 := by
    calc v - w = A (φ (v - w)) := (h (v - w)).symm
      _ = A 0 := by rw [hsub]
      _ = 0 := map_zero A
  exact sub_eq_zero.mp hv

/-! ===========================================================================
    §2  ⭐⭐⭐⭐ 主定理：`Corrects` 版本的「不动点 ⟺ 最优」
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【EE2 主定理】`Corrects A φ` 下：`φ (x' - A θ) = 0 ↔ A θ = x'`。**

这是 `Fate/FateV2.Loop.T1Verify.fixed_iff_of_injective` 的**强化形式**：
前提从 `Function.Injective φ` 弱化为 `Corrects A φ`（后者蕴含前者）。 -/
theorem fixed_iff_of_corrects (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) (x' : F) (θ : E) :
    φ (x' - A θ) = 0 ↔ A θ = x' := by
  have hinj : Function.Injective φ := corrects_injective_here A φ h
  constructor
  · intro hz
    have h0 : φ (x' - A θ) = φ 0 := by simpa using hz
    have hsub : x' - A θ = 0 := hinj h0
    exact (sub_eq_zero.mp hsub).symm
  · intro hAx
    rw [hAx, sub_self, map_zero]

/-- ⭐⭐ **对称写法**：`A θ - x'` 形式的等价式（省去调用者的符号整理）。 -/
theorem fixed_iff_of_corrects' (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) (x' : F) (θ : E) :
    φ (A θ - x') = 0 ↔ A θ = x' := by
  have hinj : Function.Injective φ := corrects_injective_here A φ h
  constructor
  · intro hz
    have h0 : φ (A θ - x') = φ 0 := by simpa using hz
    have hsub : A θ - x' = 0 := hinj h0
    exact sub_eq_zero.mp hsub
  · intro hAx
    rw [hAx, sub_self, map_zero]

/-! ===========================================================================
    §3  ⭐⭐⭐ 落到 `wbW`（写回算子）的不动点形态
    =========================================================================== -/

/-- ⭐⭐⭐ **`wbW` 不动点 ⟺ `A θ = x'`（`Corrects` 下）。**

`wbW A φ η x' θ = θ + η • φ (x' - A θ)`（见 `Fate.BoundWriteBack`），
当 `η ≠ 0` 时它不动 **当且仅当** `φ (x' - A θ) = 0`，
再由 `fixed_iff_of_corrects` 换成 `A θ = x'`。 -/
theorem wbW_fixed_iff_of_corrects (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) (η : ℝ) (hη : η ≠ 0) (x' : F) (θ : E) :
    wbW A φ η x' θ = θ ↔ A θ = x' := by
  have hiff : φ (x' - A θ) = 0 ↔ A θ = x' := fixed_iff_of_corrects A φ h x' θ
  rw [wbW_apply]
  constructor
  · intro heq
    have hz : η • φ (x' - A θ) = 0 := by
      have : θ + η • φ (x' - A θ) = θ + 0 := by rw [heq, add_zero]
      exact add_left_cancel this
    rcases smul_eq_zero.mp hz with h1 | h1
    · exact absurd h1 hη
    · exact hiff.mp h1
  · intro hAx
    rw [hiff.mpr hAx, smul_zero, add_zero]

/-! ===========================================================================
    §4  与 `FateV2.Loop.T1Verify.fixed_iff_of_injective` 的一致性
    =========================================================================== -/

/-- ⭐ **一致性检查**：由 `Corrects` 得到的单射性喂回 `T1Verify` 的原定理，
得到**同一个**结论 —— 说明本文件确实是原定理的强化而非改写。 -/
theorem fixed_iff_of_corrects_via_T1Verify (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) (x' : F) (θ : E) :
    φ (x' - A θ) = 0 ↔ A θ = x' :=
  FateV2.Loop.T1Verify.fixed_iff_of_injective A φ (corrects_injective_here A φ h) x' θ

end Basic

end T1VerifyStrong
end FateV2.Loop