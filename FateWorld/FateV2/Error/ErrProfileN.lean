import FateWorld.FateV2.Export.Export
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · ErrProfileN —— 离散误差剖面 `E_W(γ) = b(γ) + v(γ)`

  ## 迁移登记
  - 来源：新写（**不重定义** `Error/FitBoundary.lean` 里已有的 `ErrProfileWeak`）
  - 动作：C 重写
  - 对应环节：F7-02（误差剖面）、F7-11（误差判据）
  - 依赖裁决：**裁决 K**、**D-008**（σ 由建模层给出）、
              **D-020**（双界只作数学界）、**D-022**（反空泛）
  - 改动：新文件。原 `Error/ErrProfile.lean` 是骨架；本文件把它落成
          **离散分辨率**版（`γ : Nat`），与 demo 的离散数据一致。
  - 状态：已验证

  ## 与既有 `ErrProfileWeak` 的关系

  `Error/FitBoundary.lean`（B 类迁移，连续 `γ : Real`）已有
  `ErrProfileWeak : bias + var，两分量非负`。
  本文件的 `ErrProfileN` 是它在**离散索引**上的同型实例。

  ⚠ **降级**：本批**没有**证明「离散 → 连续」的嵌入（那需要 `Real` 上的
  稠密性/插值），两者是**平行**的两套，不是一条链。

  ## 超出定义之处
  * `err_nonneg`：两分量非负 ⟹ 误差非负。定义是两字段 + 一个和式，
    定义本身没说这个和是非负的。
  * `err_sq_nonneg`：误差平方非负（由 `err_nonneg` 推）。
-/

namespace FateV2.ErrorN

open FateV2.Modeling

/-! ===========================================================================
  §1  离散误差剖面
  =========================================================================== -/

/-- **离散误差剖面**：分辨率 `γ : Nat` 上的 `b + v`。

  两分量**非负**是领域公理（距离/范数类量），不是估计。 -/
structure ErrProfileN where
  /-- 逼近误差 `b(γ)`：分辨率不足导致偏离真结构 -/
  bias : Nat → Real
  /-- 估计误差 `v(γ)`：自由度多导致拟合噪声 -/
  var : Nat → Real
  /-- 两分量非负（度量公理） -/
  bias_nonneg : ∀ γ, 0 ≤ bias γ
  /-- 两分量非负（度量公理） -/
  var_nonneg : ∀ γ, 0 ≤ var γ

namespace ErrProfileN

/-- **误差** `E_W(γ) = b(γ) + v(γ)`。 -/
def err (W : ErrProfileN) (γ : Nat) : Real := W.bias γ + W.var γ

/-- **误差非负**（两非负分量之和）。

  **超出定义之处**：`err` 是一个和式，两个非负性分列在字段里；
  本定理把三者**合起来**得到「误差恒非负」——
  这是 `E_W` 能当「尺度」用的前提，也是后面「σ 是下界且 σ ≥ 0」的基石。 -/
theorem err_nonneg (W : ErrProfileN) (γ : Nat) : 0 ≤ W.err γ :=
  add_nonneg (W.bias_nonneg γ) (W.var_nonneg γ)

/-- **误差平方非负**（由 `err_nonneg` 推）。 -/
theorem err_sq_nonneg (W : ErrProfileN) (γ : Nat) : 0 ≤ W.err γ * W.err γ :=
  mul_nonneg (W.err_nonneg γ) (W.err_nonneg γ)

/-- **只看偏差的剖面**（`v ≡ 0`）。 -/
def biasOnly (b : Nat → Real) (hb : ∀ γ, 0 ≤ b γ) : ErrProfileN where
  bias := b
  var := fun _ => 0
  bias_nonneg := hb
  var_nonneg := fun _ => le_refl 0

/-- **纯偏差剖面的误差恰是偏差本身**。 -/
theorem biasOnly_err (b : Nat → Real) (hb : ∀ γ, 0 ≤ b γ) (γ : Nat) :
    (biasOnly b hb).err γ = b γ := by
  show b γ + 0 = b γ
  rw [add_zero]

end ErrProfileN

end FateV2.ErrorN
