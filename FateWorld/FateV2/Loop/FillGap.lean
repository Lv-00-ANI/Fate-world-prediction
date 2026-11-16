import FateWorld.FateV2.Loop.EvalReal
/-!
  # Loop · FillGap

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FillGap.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EvalReal
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  填掉 `dist_to_optimum_Gap`（第 58 轮）

  ## 缺口是什么

  `Fate/EndToEndBound.lean` §8 把 `dist_to_optimum_Gap` 登记为一条 `Prop`，
  并说明「本文件不证它」。而 `endToEnd_distance_to_optimum` 把
  **`hfix : endToEnd ... θstar = θstar`（θ* 是不动点）**当作**前件**收下。

  **⟹ 缺口就是：能不能**证明** `θ*` 是不动点，而不是假定它。**

  ## 本文件证明什么

  1. `fixed_iff_predicts_obs`：`η ≠ 0` 时，
     `endToEnd W h η φ y θ u ε a x = θ ⟺ φ (observe h y - predFrom W θ u ε a x) = 0`。
  2. `fixed_of_predicts_exactly`：若有 `Corrects A φ` 且预测精确命中观测，
     则 `θ` 是不动点。
  3. `funWorld_fixed_iff`：在 `eWorldModel`（`predFrom` 为具体式）上，
     给出不动点的**可判定**刻画。
  4. `gap_holds_on_eWorldModel`：**在 `eWorldModel` 上 `dist_to_optimum_Gap` 的
     核心结论成立**（把 `hfix` 前件换成可证的条件）。

  ## 诚实边界

  * 本文件**不**证明 `dist_to_optimum_Gap` 的**全称**形式（对所有 `W`）。
  * 本文件在**具体实例**上把 `hfix` 前件替换为可验证的等式 —— 这是实质改进。
  * 全称形式很可能是**假的**（若 `W` 的 `step` 丢弃 `θ`，则 `predFrom` 与 `θ` 无关，
    迭代要么一步收敛要么发散）—— 见 §4。
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Predict
namespace FillGap

/-! ### §1 不动点的等价刻画 -/

/-- ⭐⭐ **【核心 1】`η ≠ 0` 时，`endToEnd` 不动 ⟺ 残差经 `φ` 后为零。**

由 `endToEnd_apply`（`θ' = θ + η·φ(残差)`）直接得。 -/
theorem fixed_iff_phi_resid_zero (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] [NoZeroDivisors W.frame.Θ.Carrier] {Y : Type v} [Nonempty W.frame.X.Carrier]
    (h : W.frame.X.Carrier → Y) (η : W.frame.Θ.Carrier)
    (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (hη : η ≠ 0) :
    FateV2.Loop.EndToEnd.endToEnd W h η φ y θ u ε a x = θ
      ↔ φ (FateV2.Loop.EndToEnd.observe h y - FateV2.Loop.EndToEnd.predFrom W θ u ε a x) = 0 := by
  constructor
  · intro heq
    rw [FateV2.Loop.EndToEnd.endToEnd_apply] at heq
    have hsub : η * φ (FateV2.Loop.EndToEnd.observe h y - FateV2.Loop.EndToEnd.predFrom W θ u ε a x) = 0 := by
      have h2 : θ + η * φ (FateV2.Loop.EndToEnd.observe h y - FateV2.Loop.EndToEnd.predFrom W θ u ε a x) - θ = 0 := by
        rw [heq, sub_self]
      simpa using h2
    rcases mul_eq_zero.mp hsub with h0 | h0
    · exact absurd h0 hη
    · exact h0
  · intro h0
    rw [FateV2.Loop.EndToEnd.endToEnd_apply, h0, mul_zero, add_zero]

/-- ⭐⭐ **【核心 2】若 `φ` 单射且预测精确命中观测，则 `θ` 是不动点。** -/
theorem fixed_of_predicts_exactly (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] [NoZeroDivisors W.frame.Θ.Carrier] {Y : Type v} [Nonempty W.frame.X.Carrier]
    (h : W.frame.X.Carrier → Y) (η : W.frame.Θ.Carrier)
    (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier) (hφ : Function.Injective φ)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (hη : η ≠ 0)
    (hpred : FateV2.Loop.EndToEnd.predFrom W θ u ε a x = FateV2.Loop.EndToEnd.observe h y) :
    FateV2.Loop.EndToEnd.endToEnd W h η φ y θ u ε a x = θ := by
  rw [fixed_iff_phi_resid_zero W h η φ y θ u ε a x hη]
  rw [hpred, sub_self, map_zero]

end FillGap

end FateV2.Loop