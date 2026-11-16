import FateWorld.FateV2.Loop.PipelineAdaptiveEta
/-!
  # Loop · PipelineAdaptiveEtaNormed

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PipelineAdaptiveEtaNormed.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PipelineAdaptiveEta
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.PipelineAdaptiveEtaNormed` —— **变步长收敛从 ℝ 推广到赋范空间**

  ## 0  本文件补什么

  `Fate/PipelineAdaptiveEta.lean` 中的 `thetaN_adaptive_tendsto` 只处理**标量 `ℝ`**：

      θ_{n+1} = θ_n + η_n (θ* - θ_n),   θ_n - θ* = (∏_{k<n}(1-η_k)) (θ₀ - θ*).

  本文件把同一定理搬到**任意实赋范空间 `E`**（`[NormedAddCommGroup E] [NormedSpace ℝ E]`）：

      θ_{n+1} = θ_n + η_n • (θ* - θ_n),   θ_n - θ* = (∏_{k<n}(1-η_k)) • (θ₀ - θ*)

  于是**标量情形是 `E = ℝ` 的特例**，并且立刻覆盖：
  * **多维参数** `E = ℝ^d`（尤其 `ℝ × ℝ`，见 §3 的推论）；
  * **函数空间** `E = C[0,1]`；
  * **算子空间** `E = L(H)`。

  ## 1  主结果

  * `adaptive_closed_normed` —— 赋范空间上的 `n` 步**闭式**（乘积形式）；
  * ⭐⭐⭐⭐ `adaptive_tendsto_normed` —— 一致收缩步长 `⟹` `θ_n → θ*`（**主定理**）；
  * ⭐⭐⭐ `adaptive_tendsto_pair` —— `E = ℝ × ℝ` 的多维特例（直接 `apply` 主定理）。

  ## 2  ⚠ 诚实边界

  **2.1 前件不含结论。** `adaptive_tendsto_normed` 的前件只涉及
  **步长序列 `η : ℕ → ℝ`** 与常数 `c`（`0 ≤ c < 1` 且 `∀ k, |1-η_k| ≤ c`），
  `θstar`、`θ₀` 是**任意**给定点；结论是关于**轨迹**的收敛。
  二者由 `adaptive_closed_normed` 的闭式连接，**不是同义反复**。
  （若前件写成「`θ_n → θ*`」则为同义反复；本文件没有这样写。）

  **2.2 不需要完备性。** 与任务描述里的 `[NormedAddCommGroup E]` 一致：
  收敛的**极限点 `θ*` 是显式给定的**，故只用到 `nhds` 的拓扑性质，
  **不必**假设 `E` 完备（`CompleteSpace E`）。这是本文件比「完备性版本」更弱的假设。

  **2.3 本文件不声称完整调和判据。** 无穷乘积 `→ 0` 的一般判据
  （`Σ η_k = ∞ ∧ η_k → 0`）**不在本文件中**；这里只有一致收缩假设下的通用定理。
  标量调和特例见 `PipelineAdaptiveEta.thetaN_harmonic_tendsto`。

  **2.4 不修改任何已有模块。**
-/

namespace FateV2.Loop

open FateV2.Modeling
namespace PipelineAdaptiveEtaNormed

open Filter
open scoped Topology

/-! ## §1  赋范空间上的变步长迭代 -/

/-- **【赋范空间上的一步更新】**：`θ ↦ (1 - η_n) • θ + η_n • θ*`，
写作 `θ + η_n • (θ* - θ)`（沿残差方向走一步）。 -/
noncomputable def fstepV {E : Type*} [AddCommGroup E] [Module ℝ E]
    (η : ℕ → ℝ) (θstar : E) (n : ℕ) (θ : E) : E :=
  θ + η n • (θstar - θ)

/-- ⭐ **【一步更新的偏差形式】**：`fstepV η θ* n θ - θ* = (1 - η_n) • (θ - θ*)`。 -/
theorem fstepV_sub {E : Type*} [AddCommGroup E] [Module ℝ E]
    (η : ℕ → ℝ) (θstar : E) (n : ℕ) (θ : E) :
    fstepV η θstar n θ - θstar = (1 - η n) • (θ - θstar) := by
  simp only [fstepV, sub_smul, one_smul, smul_sub]
  abel

/-- ⭐ **【闭式的归纳辅助】**：`θ_n - θ* = (∏_{k<n}(1-η_k)) • (θ₀ - θ*)`。 -/
theorem adaptive_closed_aux {E : Type*} [AddCommGroup E] [Module ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) :
    ∀ n : ℕ, (Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n) - θstar
      = ((Finset.range n).prod (fun k => (1 - η k))) • (θ₀ - θstar)
  | 0 => by simp
  | n + 1 => by
    have ih := adaptive_closed_aux η θstar θ₀ n
    rw [show Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) (n + 1)
          = fstepV η θstar n (Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n) from rfl,
      fstepV_sub, ih, Finset.prod_range_succ, mul_smul, smul_comm]

/-- ⭐⭐⭐ **【赋范空间上的变步长 `n` 步闭式】**

$$\boxed{\;\theta_n - \theta^* = \Bigl(\prod_{k<n} (1-\eta_k)\Bigr)\bullet(\theta_0-\theta^*)\;}$$

这是标量版 `thetaN_adaptive_closed` 到任意 `ℝ`-模的推广
（标量情形即 `E = ℝ` 时 `•` 退化为 `*`）。 -/
theorem adaptive_closed_normed {E : Type*} [AddCommGroup E] [Module ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (n : ℕ) :
    (Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n) - θstar
      = ((Finset.range n).prod (fun k => (1 - η k))) • (θ₀ - θstar) :=
  adaptive_closed_aux η θstar θ₀ n

/-- ⭐ **【范数形式的偏差上界】**：`‖θ_n - θ*‖ ≤ c^n * ‖θ₀ - θ*‖`。 -/
theorem adaptive_norm_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c : ℝ) (_hc0 : 0 ≤ c)
    (hη : ∀ k, |1 - η k| ≤ c) (n : ℕ) :
    ‖(Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n) - θstar‖
      ≤ c ^ n * ‖θ₀ - θstar‖ := by
  rw [adaptive_closed_normed, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (Fate.PipelineAdaptiveEta.prod_abs_le_pow η c hη n) (norm_nonneg _)

/-! ## §2  主定理：赋范空间上的变步长收敛 -/

/-- ⭐⭐⭐⭐ **【赋范空间上的变步长收敛】**

若 `E` 是实赋范空间，`η : ℕ → ℝ` 满足一致收缩 `∀ k, |1 - η_k| ≤ c < 1`，
则迭代 `θ_{n+1} = θ_n + η_n • (θ* - θ_n)` 收敛到 `θ*`：

$$\lim_{n\to\infty} \left\| \theta_n - \theta^* \right\| = 0.$$

这是 `Fate.PipelineAdaptiveEta.thetaN_adaptive_tendsto` 从 `ℝ` 到**任意赋范空间**的推广
（取 `E = ℝ`、`• = *` 即退化回标量定理）。

**证明**：闭式 + `|∏(1-η_k)| ≤ c^n` + `c^n → 0` + 乘常数 + 范数刻画收敛。 -/
theorem adaptive_tendsto_normed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (hη : ∀ k, |1 - η k| ≤ c) :
    Tendsto (fun n => Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n)
      atTop (nhds θstar) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc
  have hbound : Tendsto (fun n : ℕ => c ^ n * ‖θ₀ - θstar‖) atTop (nhds 0) := by
    simpa using hpow.mul_const ‖θ₀ - θstar‖
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => adaptive_norm_le η θstar θ₀ c hc0 hη n) hbound

/-! ## §3  `ℝ × ℝ` 特例（多维参数） -/

/-- ⭐⭐⭐ **【多维情形：`ℝ × ℝ` 上的变步长收敛】**

`ℝ × ℝ` 是 `NormedAddCommGroup` 与 `NormedSpace ℝ` 的实例（`Prod.normedAddCommGroup`、
`Prod.normedSpace`），故直接由 `adaptive_tendsto_normed` 得到。
适用于**二维参数**；一般 `ℝ^d`（`Fin d → ℝ`）同理。 -/
theorem adaptive_tendsto_pair (η : ℕ → ℝ) (θstar θ₀ : ℝ × ℝ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1) (hη : ∀ k, |1 - η k| ≤ c) :
    Tendsto (fun n => Nat.rec θ₀ (fun k ih => ih + η k • (θstar - ih)) n)
      atTop (nhds θstar) :=
  adaptive_tendsto_normed η θstar θ₀ c hc0 hc hη

end PipelineAdaptiveEtaNormed
end FateV2.Loop