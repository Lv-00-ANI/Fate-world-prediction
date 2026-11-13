/-
# P4 实例：`d ≥ 2` 且 `A` 非恒等 的**存在性**见证

本文件**只**证明一件事：在二维载体 `V2 := Fin 2 → ℝ` 上存在一个
**非恒等**的 `ℝ`-线性算子。这是 P4 实例（维数 `d ≥ 2`、线性写回算子 `A`
非恒等）可被满足的最低限度证据。

目标定理：`swap2_ne_id : swap2 ≠ LinearMap.id`。

- 零 `sorry` / `admit` / `axiom`。
- 仅 import `Fate.ScratchAssemblyLearns`（提供 `Fate` 环境与 `ℝ` 线性代数）；
  本文件不依赖其任何具体定理，`swap2` 独立定义。
-/
import FateWorld.Legacy.ScratchAssemblyLearns

namespace Fate
namespace WorldModelInstance2D

/-- 二维实向量空间载体。 -/
abbrev V2 : Type := Fin 2 → ℝ

/-- 交换两个坐标的**非恒等**线性算子 `(v₀, v₁) ↦ (v₁, v₀)`。 -/
noncomputable def swap2 : V2 →ₗ[ℝ] V2 where
  toFun v := fun i => v (i + 1)
  map_add' := by
    intro x y
    ext i
    simp [Pi.add_apply]
  map_smul' := by
    intro c x
    ext i
    simp [Pi.smul_apply]

/-- `swap2` 在第一个基向量上的作用：`e₀ ↦ e₁`（坐标交换）。 -/
theorem swap2_apply_zero (v : V2) : swap2 v 0 = v 1 := by
  simp [swap2]

/-- ⭐⭐ **【关键性质：`swap2` 非恒等】** -/
theorem swap2_ne_id : swap2 ≠ LinearMap.id := by
  intro h
  -- 取第一个基向量 e₀ = (1, 0)
  have hv := congrArg (fun (L : V2 →ₗ[ℝ] V2) => (L (fun i => if i = 0 then (1 : ℝ) else 0)) 0) h
  -- 展开两边的实际取值：左边 = e₀ 在坐标 1 处的值 = 0，右边 = e₀ 在坐标 0 处的值 = 1
  have hleft : swap2 (fun i => if i = 0 then (1 : ℝ) else 0) 0 = 0 := by
    simp [swap2]
  have hright : (LinearMap.id : V2 →ₗ[ℝ] V2) (fun i => if i = 0 then (1 : ℝ) else 0) 0 = 1 := by
    show ((fun i => if i = 0 then (1 : ℝ) else 0) : V2) 0 = 1
    simp
  rw [hleft, hright] at hv
  exact zero_ne_one hv

end WorldModelInstance2D
end Fate
