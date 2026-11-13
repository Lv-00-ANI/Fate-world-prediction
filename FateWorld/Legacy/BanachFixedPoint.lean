import Mathlib.Topology.MetricSpace.Contracting

/-!
# 第 8 层：从赋范空间到度量空间 —— Banach 不动点定理

## 为什么这是推广

前 7 层（①-⑦）都在 `NormedAddCommGroup E`（需要线性结构 + 范数）上做。
本文件只需要 `MetricSpace X` + `CompleteSpace X`，**不需要线性结构**。

## 主定理

若 `F : X → X` 满足 `dist (F x) (F y) ≤ c * dist x y`（`c < 1`），
且 `X` 完备，则 `F` 有唯一不动点，且任意初值迭代收敛，且有几何收敛速度。

## 证明策略

把 `c : ℝ`（`0 ≤ c < 1`）转成 `NNReal`，构造 `ContractingWith ⟨c, hc0⟩ F`，
再调用 Mathlib 的 `ContractingWith.fixedPoint`、`.fixedPoint_isFixedPt`、
`.fixedPoint_unique`、`.tendsto_iterate_fixedPoint`、`.toLipschitzWith.iterate`。

## 非平凡性检查（前件是否含结论）

- `banach_existsUnique_fixedPoint`：前件只说"压缩 + 完备 + 非空"，结论是"存在唯一不动点"，
  这是实打实的内容（完备性是本质条件，缺了不成立）。
- `banach_iterate_tendsto`：前件给任意初值 `x0`，结论断言该初值迭代收敛。
- `banach_distance_bound`：前件给一个不动点 `xstar`，结论给第 n 步的显式几何误差界
  `dist (...) xstar ≤ c^n * dist x0 xstar`，这是定量结论，不是前件的重述。
-/

namespace Fate
namespace BanachFixedPoint

open Filter

/-- 把实数压缩因子 `c`（`0 ≤ c < 1`）提升为 `NNReal` 并证明其 `< 1`。 -/
theorem nnreal_coe_lt_one {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (NNReal.mk c hc0 : NNReal) < 1 := by
  rw [← NNReal.coe_lt_coe]
  simpa using hc1

/-- 由 `dist (F x) (F y) ≤ c * dist x y` 构造 `LipschitzWith ⟨c, hc0⟩ F`。 -/
theorem lipschitzWith_of_dist_le {X : Type*} [MetricSpace X]
    (F : X → X) (c : ℝ) (hc0 : 0 ≤ c)
    (hcont : ∀ x y : X, dist (F x) (F y) ≤ c * dist x y) :
    LipschitzWith (NNReal.mk c hc0) F := by
  intro x y
  rw [edist_dist, edist_dist]
  have h : ((NNReal.mk c hc0) : ENNReal) = ENNReal.ofReal c := by
    rw [ENNReal.coe_nnreal_eq]; simp
  rw [h, ← ENNReal.ofReal_mul hc0]
  exact ENNReal.ofReal_le_ofReal (hcont x y)

/-- 由压缩条件构造 `ContractingWith ⟨c, hc0⟩ F`。 -/
theorem contractingWith_of_dist_le {X : Type*} [MetricSpace X]
    (F : X → X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcont : ∀ x y : X, dist (F x) (F y) ≤ c * dist x y) :
    ContractingWith (NNReal.mk c hc0) F :=
  ⟨nnreal_coe_lt_one hc0 hc1, lipschitzWith_of_dist_le F c hc0 hcont⟩

/-- ⭐⭐⭐⭐⭐ **【Banach 不动点定理：存在唯一】**

若 `F : X → X` 是压缩映射（`dist (F x) (F y) ≤ c * dist x y`，`c < 1`），
且 `X` 是**完备**度量空间，则 `F` 有**唯一**不动点。

这是从「赋范空间」到「度量空间」的推广 —— **不需要线性结构**。 -/
theorem banach_existsUnique_fixedPoint
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : X → X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcont : ∀ x y : X, dist (F x) (F y) ≤ c * dist x y) :
    ∃! xstar : X, F xstar = xstar := by
  have hcw : ContractingWith (NNReal.mk c hc0) F :=
    contractingWith_of_dist_le F c hc0 hc1 hcont
  have hfix : F (hcw.fixedPoint F) = hcw.fixedPoint F := hcw.fixedPoint_isFixedPt
  exact ⟨hcw.fixedPoint F, hfix, fun y hy => hcw.fixedPoint_unique hy⟩

/-- ⭐⭐⭐⭐ **【任意初值迭代收敛到不动点】**

任意 `x0`，迭代 `x_{n+1} = F x_n` 收敛到 `F` 的唯一不动点。
这里迭代序列用函数迭代 `F^[n] x0` 表示。 -/
theorem banach_iterate_tendsto
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : X → X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcont : ∀ x y : X, dist (F x) (F y) ≤ c * dist x y)
    (x0 : X) :
    ∃ xstar : X, F xstar = xstar ∧
      Tendsto (fun n : ℕ => F^[n] x0) atTop (nhds xstar) := by
  have hcw : ContractingWith (NNReal.mk c hc0) F :=
    contractingWith_of_dist_le F c hc0 hc1 hcont
  exact ⟨hcw.fixedPoint F, hcw.fixedPoint_isFixedPt,
    hcw.tendsto_iterate_fixedPoint x0⟩

/-- ⭐⭐⭐ **【收敛速度（先验误差界）】**

若 `xstar` 是 `F` 的不动点，则第 `n` 步迭代与 `xstar` 的距离满足
`dist (F^[n] x0) xstar ≤ c^n * dist x0 xstar`。 -/
theorem banach_distance_bound
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : X → X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcont : ∀ x y : X, dist (F x) (F y) ≤ c * dist x y)
    (x0 xstar : X) (hfix : F xstar = xstar) (n : ℕ) :
    dist (F^[n] x0) xstar ≤ c ^ n * dist x0 xstar := by
  have hcw : ContractingWith (NNReal.mk c hc0) F :=
    contractingWith_of_dist_le F c hc0 hc1 hcont
  have hlip := hcw.toLipschitzWith.iterate n
  have h1 : dist (F^[n] x0) (F^[n] xstar) ≤ ((NNReal.mk c hc0 : NNReal) ^ n : NNReal) * dist x0 xstar :=
    hlip.dist_le_mul x0 xstar
  have h2 : F^[n] xstar = xstar := Function.iterate_fixed hfix n
  rw [h2] at h1
  have h3 : (((NNReal.mk c hc0 : NNReal) ^ n : NNReal) : ℝ) = c ^ n := by
    rw [NNReal.coe_pow]; rfl
  rwa [h3] at h1

end BanachFixedPoint
end Fate
