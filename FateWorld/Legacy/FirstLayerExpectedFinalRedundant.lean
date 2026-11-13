import FateWorld.Legacy.FirstLayerExpectedGeneral
import FateWorld.Legacy.FirstLayerExpectedFinal

/-! ===========================================================================
  `Fate/FirstLayerExpectedFinalRedundant` —— **验证 `Final` 是否被 `General` 覆盖**
  ===========================================================================

  ## 目的

  主控第 351 轮曾判断 `FirstLayerExpectedFinal` 被 `FirstLayerExpectedGeneral` 完全取代，
  打算归档。第 355 轮发现同一批判断里 `ContinuousEval` 那个判错了（只看了定理数量，
  没看内容——`ContinuousEval` 有 `continuous_sim_values_via_worldmodel` 是独有的）。

  所以对 `Final` 不能用「看着像特例就归档」，必须**证明 `Final` 的三条都能从 `General` 推出**。

  `Final` 的三条都是 `xhat = 1` 的形式：
  * `e2e_eta_one_zero`（`μ * 1`、`thetaN 1 μ 1 θ₀ n`）
  * `e2e_expand`（`μ * 1`）
  * `first_layer_bound_expected_final`（`(∫ y, y ∂P) * 1`）

  `General` 的对应三条接受任意 `xhat ≠ 0`，取 `xhat = 1` 时应给出同样结论。
  本文件把这三条**用 `General` 重证一遍**，确认它们确实是推论。
-/

namespace Fate
namespace FirstLayerExpectedFinalRedundant

open MeasureTheory

/-- ⭐ **`Final.e2e_expand` 可以从 `General.e2e_expand_general` 推出**（取 `xhat = 1`）。

`hx : (1 : ℝ) ≠ 0` 是 `one_ne_zero`。

注意：`Final.e2e_expand` 的 `μ * 1` 与 `General` 的 `μ * xhat` 在 `xhat = 1` 时相同。 -/
theorem e2e_expand_from_general (η μ θ₀ : ℝ) (n : ℕ) :
    |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (μ * 1)
        (ThetaConvergence.thetaN η μ 1 θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit 1|
      = |1 - η| ^ n * |θ₀ - μ| := by
  rw [FirstLayerExpectedGeneral.e2e_expand_general η μ θ₀ 1 one_ne_zero n]
  simp

/-- ⭐ **`Final.e2e_eta_one_zero` 可以从 `General.e2e_expand_general` 推出**（`η = 1`、`xhat = 1`）。 -/
theorem e2e_eta_one_zero_from_general (μ θ₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (μ * 1)
        (ThetaConvergence.thetaN 1 μ 1 θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit 1| = 0 := by
  rw [e2e_expand_from_general 1 μ θ₀ n]
  simp [hn.ne']

/-- ⭐⭐ **`Final.first_layer_bound_expected_final` 可以从
`General.first_layer_bound_expected_general` 推出**（取 `xhat = 1`）。

这是「`Final` 被 `General` 覆盖」的**决定性证据**：主定理也是推论。 -/
theorem first_layer_bound_expected_final_from_general
    {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (η : ℝ) (n : ℕ) (hn : 0 < n) :
    ∫ ω : Fin n → ℝ,
        |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (((∫ y, y ∂P)) * 1)
          (ThetaConvergence.thetaN η ((∫ y, y ∂P)) 1
            (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
          PUnit.unit PUnit.unit PUnit.unit 1|
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ |1 - η| ^ n * 1 * ChainBudgetBound.sigmaEst P n := by
  have h := FirstLayerExpectedGeneral.first_layer_bound_expected_general
    hP η n hn 1 one_ne_zero
  simpa using h

/-! ===========================================================================
  §3  结论
  =========================================================================== -/

/-!
### ⚠ 本文件证明了什么

`FirstLayerExpectedFinal` 的三条定理（`e2e_eta_one_zero`、`e2e_expand`、
`first_layer_bound_expected_final`）**全部可以从 `FirstLayerExpectedGeneral` 推出**
（取 `xhat = 1`）。

**所以 `Final` 确实被 `General` 覆盖，可以归档。**

### ⚠ 但归档前必须回答一个问题

`Final` **先入库**（第 312 轮），`General` **后入库**（第 314 轮）。
`Final` 里面还带着 `e2e_eta_one_zero` 的**独立证明**（不依赖 `General`）。

**若 `General` 将来被修改或删除，`Final` 是备份。**

**⟹ 这是「保留 vs 归档」的真正权衡点，不是「谁覆盖谁」的技术问题。**

**⟹ 主控的判断：可以归档（因为 `General` 更一般，且两条都在 git 历史里）。**

**⟹ 但这属于**冗余清理**，不是数学进展。**
-/

end FirstLayerExpectedFinalRedundant
end Fate
