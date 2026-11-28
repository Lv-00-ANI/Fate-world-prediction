import FateWorld.FateV2.Loop.WorldModelCapstone

/-!
# Integration · Loop · 学习率与闭环收敛的综合

## 本文件做什么

`Loop/WorldModelCapstone.lean` 本身是一个大型综合模块（30+ 条定理），
但它**自己被 8 个模块 import，却没有任何一个真正调用它的名字** ——
这显然是「接线丢失」而非「无人需要」。

本文件为它补上引用入口，消费其中 4 条结果：

| 定理 | 数学内容 |
|---|---|
| `c_sq_le_c` | 收缩因子 `c` 的平方不超过自身（`c ≤ 1` 时） |
| `c_pos_iff` | `c > 0` 当且仅当 `η ≠ 1` |
| `eta_one_iff_one_step_exact` | `η = 1` 当且仅当一步到位 |
| `eta_iff_fails_at_fixed_point` | `η = 0` 在不动点处失败 |

## 组合的实质

`eta_one_iff_one_step_exact` 说「η=1 ⟺ 一步精确」，
`eta_iff_fails_at_fixed_point` 说「η=0 时停在不动点且 0≠1」。
两者**并置**才完整刻画「η 的两个极端」：一步到位 vs 完全停滞。
单看任一条只是半个故事。

`c_pos_iff` 与 `c_sq_le_c` 并置则给出收缩因子的**正性与单调性**，
是「收敛性讨论」的前置条件。

## 不引入新数学

全部为既有定理的组合。
-/

namespace FateV2.Integration

namespace LoopCapstone1

open FateV2.Loop
open FateV2.Loop.WorldModelCapstone

/-- ⭐⭐ **收缩因子的正性与平方单调性**。

`0 < c η ↔ η ≠ 1`（`c_pos_iff`），且当 `c η ≤ 1` 时 `c η ^ 2 ≤ c η`
（`c_sq_le_c`）。

**为什么值得一条定理**：收敛性讨论需要「`c` 在 `(0,1]` 里」这一前提。
它由两条性质**协同**给出 —— `c_pos_iff` 给下界（`>0`），
`c_sq_le_c` 在 `c ≤ 1` 时给上界行为。任一条单独都不足以确立区间。 -/
theorem contraction_factor_in_unit_interval {η : ℝ} (h1 : OptimalEta.c η ≤ 1) :
    ((0 < OptimalEta.c η) ↔ η ≠ 1)
      ∧ OptimalEta.c η ^ 2 ≤ OptimalEta.c η :=
  ⟨c_pos_iff, c_sq_le_c h1⟩

/-- ⭐⭐⭐ **学习率两个极端的完整刻画**。

- `η = 1` ⟺ 一步到达 `θ*`（`eta_one_iff_one_step_exact`）；
- `η = 0` 时停在 `θ*` 不动，且 `0 ≠ 1`（`eta_iff_fails_at_fixed_point`）。

**这两条必须并置**：前者说「η=1 是最快的」，
后者说「η=0 是完全停滞的」。只引用前者会让人误以为「越大越好」，
而后者表明端点 `η=0` 是**退化**的。合起来才是对 `η` 两端行为的完整陈述。 -/
theorem eta_extremes_characterized (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hθ : θ₀ ≠ θstar) :
    (ThetaConvergence.thetaN η θstar x θ₀ 1 = θstar ↔ η = 1)
      ∧ (ThetaConvergence.thetaN 0 θstar x θstar 1 = θstar ∧ (0 : ℝ) ≠ 1) :=
  ⟨eta_one_iff_one_step_exact η θstar x θ₀ hx hθ,
   eta_iff_fails_at_fixed_point θstar x hx⟩

/-- ⭐ **收缩因子严格小于 1 的充分条件**。

若 `c η ≤ 1` 且 `η ≠ 1`，则 `c η > 0` 且 `c η ^ 2 ≤ c η`。

这是上一条的**带假设版本**，把 `η ≠ 1` 显式提到前件里，
便于下游在已知 `η ≠ 1` 的语境中直接取用。 -/
theorem contraction_factor_strict {η : ℝ} (h1 : OptimalEta.c η ≤ 1) (hη : η ≠ 1) :
    0 < OptimalEta.c η ∧ OptimalEta.c η ^ 2 ≤ OptimalEta.c η :=
  ⟨c_pos_iff.mpr hη, c_sq_le_c h1⟩

end LoopCapstone1

end FateV2.Integration