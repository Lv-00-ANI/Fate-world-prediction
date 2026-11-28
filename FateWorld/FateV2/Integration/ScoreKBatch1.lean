import FateWorld.FateV2.Error.ScoreK
import FateWorld.FateV2.Modeling.NaryAlgebra

/-!
# Integration · Error/Modeling · 带损失与 N 元条件独立的综合

## 本文件做什么

修复两条接线丢失：

| 源模块 | 被 import 次数 |
|---|---:|
| `Modeling.NaryAlgebra` | **9** |
| `Error.ScoreK` | **8** |

## 消费的定理

`Error.ScoreK`（namespace `FateV2.Error.ScoreK`）：
- `bandLoss_eq_zero`       带内 ⟹ 损失为零
- `bandLoss_eq_zero_iff`   损失为零 ⟺ 带内（完整刻画）
- `bandLoss_pos_of_lt`     低于下界 ⟹ 损失正
- `bandLoss_pos_of_gt`     高于上界 ⟹ 损失正

`Modeling.NaryAlgebra`（namespace `FateV2.Modeling.GenC3`）：
- `condIndepN_sum_factorize`  N 元条件独立的和因子化

## 组合的实质

`bandLoss_eq_zero_iff` 是**完整刻画**（双向），而
`bandLoss_pos_of_lt` / `_of_gt` 是它的**两个负向特例**。
三者并置才说明「带损失恰在带外为正」——单引 `_iff` 只知道等价，
不知道两个方向各自的具体条件。

`condIndepN_sum_factorize` 则把 N 元条件独立落到「和可因子化」这一
可计算形式，是 `Modeling` 侧进入数值论证的唯一入口。
-/

namespace FateV2.Integration

namespace ScoreKBatch1

/-! ---------------------------------------------------------------------------
  §1  带损失的完整刻画
  --------------------------------------------------------------------------- -/

namespace BandLossNS

open FateV2.Error.ScoreK

/-- ⭐⭐⭐ **带损失的完整刻画：零 ⟺ 带内，带外必正**。

同时给出：
1. `bandLoss σ ε = 0 ↔ σ/2 ≤ ε ∧ ε ≤ 2σ`（双向，`bandLoss_eq_zero_iff`）；
2. `ε < σ/2 → 0 < bandLoss σ ε`（下界外为正）；
3. `2σ < ε → 0 < bandLoss σ ε`（上界外为正）。

**为什么值得一条定理**：`bandLoss_eq_zero_iff` 只给出等价，
但下游做「分情形」论证时需要**两个方向的具体条件**
（低于下界 / 高于上界各自蕴含正损失）。三条并置后，
下游一次引用即可覆盖全部三种情形，不必再展开 `max`。 -/
theorem bandLoss_complete_characterization {σ : ℝ} (hσ : 0 < σ) {ε : ℝ} :
    (bandLoss σ ε = 0 ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ)
      ∧ (ε < σ / 2 → 0 < bandLoss σ ε)
      ∧ (2 * σ < ε → 0 < bandLoss σ ε) :=
  ⟨bandLoss_eq_zero_iff hσ, fun h => bandLoss_pos_of_lt h, fun h => bandLoss_pos_of_gt h⟩

/-- ⭐⭐ **带内 ⟹ 损失为零，且此时损失非负（自动）**。

`bandLoss σ ε = 0` 当 `ε` 落在 `[σ/2, 2σ]`；
同时 `0 ≤ bandLoss σ ε` 恒成立（由 `max 0` 的结构给出）。

第二条虽平凡，但下游做 `linarith` 时需要一个**命名的**下界，
否则每次都要 `unfold bandLoss; exact le_max_left _ _`。 -/
theorem bandLoss_zero_and_nonneg {σ ε : ℝ} (h1 : σ / 2 ≤ ε) (h2 : ε ≤ 2 * σ) :
    bandLoss σ ε = 0 ∧ 0 ≤ bandLoss σ ε := by
  refine ⟨bandLoss_eq_zero h1 h2, ?_⟩
  unfold bandLoss
  exact le_max_left _ _

end BandLossNS

/-! ---------------------------------------------------------------------------
  §2  N 元条件独立的和因子化
  --------------------------------------------------------------------------- -/

namespace NaryNS

open FateV2.Modeling.GenC3

/-- ⭐⭐⭐ **N 元条件独立 ⟹ 和可因子化（可直接引用的形式）**。

本体即 `condIndepN_sum_factorize`；单列是因为这是 `Modeling` 侧
进入**数值论证**的唯一入口 —— 下游若要真做求和计算，
必须先拿到「和可因子化」这一形式，而不是 `CondIndepN` 的抽象定义。 -/
theorem condIndepN_factorize_form {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] {γ : Type*}
    (p : NJoint (ι := ι) α γ) (h : CondIndepN p)
    (S : ∀ i, Set (α i)) [∀ i, DecidablePred (· ∈ S i)] (z : γ) :
    (∑ xs : (∀ i, α i), (if ∀ i, xs i ∈ S i then p xs z else 0))
        * (NMass p z) ^ (Fintype.card ι - 1)
      = ∏ i, ∑ a : α i, (if a ∈ S i then marg p i a z else 0) :=
  condIndepN_sum_factorize p h S z

end NaryNS

end ScoreKBatch1

end FateV2.Integration
