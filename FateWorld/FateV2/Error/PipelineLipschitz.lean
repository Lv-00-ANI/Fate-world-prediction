/-
  `Fate.PipelineLipschitz`
  ========================================================================

  ## 目的
  `Fate.PipelineTendstoGen.pipeline_tendsto_gen` 证明了「**线性**仿射收缩」
  `gstep η θstar θ = (1-η) • θ + η • θstar` 的迭代收敛到 `θstar`。
  本文件提供它的 **非线性对应物** 所需的**唯一分析核心**：
  「`K`-Lipschitz 收缩（`K < 1`）的迭代，相邻两项距离按 `K^n` 几何衰减」。

  ## 为什么不用 `Mathlib.Topology.MetricSpace.Contraction`
  实测该模块的 `olean` **不存在**（未编译），无法 `import`。故本文件
  只用已验证可加载的
    * `Mathlib.Topology.MetricSpace.Lipschitz`（`olean` 实测存在）
    * `Mathlib.Analysis.SpecificLimits.Normed`（`olean` 实测存在）
  且**主定理（§1）完全不依赖 Lipschitz 模块**，只用 `NormedAddCommGroup` 的
  范数公理 + 归纳（方案 2「纯推导」）。§2 才用 Lipschitz 模块做**交叉核对**。

  ## 前件是否已把结论包进去？（本项目最高频问题，逐条自查）
  * §1 前件：`0 ≤ K`、`K < 1`、`∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖`。
    结论：`∀ n, ‖(f^[n+1]) x - (f^[n]) x‖ ≤ K^n * ‖f x - x‖`。
    **前件谈的是 `f` 的一致压缩性（一对点之间的距离），结论谈的是单个轨道上
    相邻两项的偏差上界**。结论中出现 `f^[n]`、`x`、`‖f x - x‖` 这些前件
    完全没有的量；且 `n` 上是非平凡归纳（每步用一次压缩不等式）。**非同义反复。**
  * §2 前件：`LipschitzWith K f`。结论：同形状的 `dist` 不等式。
    这里确实是 Mathlib 现成引理的**直接转述**（`K : ℝ≥0` 版），
    文件内**如实标注** `iterates dist bound` 为 `↔ 引用`，不作为新成果。
  * §3 前件：`η`、`θstar`、`hη : |1-η| < 1`。结论：`gstep η θstar`
    是 `|1-η|`-Lipschitz。**前件只谈标量，结论谈映射**，非同义反复。
  -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Lipschitz

namespace FateV2.Error
namespace PipelineLipschitz

/-!
  # Error · PipelineLipschitz

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PipelineLipschitz.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Error`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐⭐⭐ 方案 2（纯推导）：范数版 Lipschitz 收缩的迭代几何界

  **完全不用 `LipschitzWith`**，直接在 `NormedAddCommGroup` 上用归纳证明。
  这是本文件的主结果（最稳，依赖最少）。
  =========================================================================== -/

/-- ⭐⭐⭐ **【范数版：`K`-收缩迭代的相邻项偏差 ≤ `K^n · ‖f x - x‖`】**

若 `f : V → V` 满足 `‖f x - f y‖ ≤ K * ‖x - y‖`（`0 ≤ K`、`K < 1`），
则第 `n` 步与第 `n+1` 步之间：

$$\bigl\|f^{n+1}(x) - f^{n}(x)\bigr\| \;\le\; K^n \cdot \|f(x) - x\| .$$

**这是 `pipeline_tendsto_gen` 的非线性对应物的分析核心**：
把「线性算子 `(1-η)•· + η•θstar`」换成任意 `K`-Lipschitz 映射。

**⚠ 非同义反复**：前件是关于 `f` 的一致压缩性，结论是关于单条轨道
`x, f x, f² x, …` 相邻两项的偏差界，且 `n` 上做非平凡归纳。
**⚠ 注意**：`hK1 : K < 1` 在**本定理中并未用到**（界对任意 `K` 成立）；
保留它只是为了与「收缩」语境一致，并让 §1.2 的可和性推论可直接使用。
故本定理实际上比「收缩」情形更强。** -/
theorem norm_iterate_geometric
    {V : Type*} [NormedAddCommGroup V]
    (f : V → V) {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x y : V, ‖f x - f y‖ ≤ K * ‖x - y‖)
    (x : V) (n : ℕ) :
    ‖(f^[n+1]) x - (f^[n]) x‖ ≤ K ^ n * ‖f x - x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ‖(f^[n+2]) x - (f^[n+1]) x‖
        = ‖f ((f^[n+1]) x) - f ((f^[n]) x)‖ := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [hstep]
    calc ‖f ((f^[n+1]) x) - f ((f^[n]) x)‖
        ≤ K * ‖(f^[n+1]) x - (f^[n]) x‖ := hf _ _
      _ ≤ K * (K ^ n * ‖f x - x‖) := by
          have := norm_nonneg ((f^[n+1]) x - (f^[n]) x)
          nlinarith
      _ = K ^ (n+1) * ‖f x - x‖ := by ring

/-- ⭐⭐ **【`n = 0` 的边界情形】**：首步偏差就是 `‖f x - x‖`（界 `K^0 · ‖f x - x‖` 取等）。

单列是为了让使用者在 `n = 0` 处不必展开 `pow_zero` / `one_mul`。 -/
theorem norm_iterate_geometric_zero
    {V : Type*} [NormedAddCommGroup V] (f : V → V) (x : V) :
    ‖(f^[1]) x - (f^[0]) x‖ = ‖f x - x‖ := by
  simp

/-- ⭐⭐ **【相邻项偏差之和被 `1/(1-K)` 控制 —— 收缩的直接推论】**

对 `K < 1`，几何级数 `∑ K^n` 收敛到 `1/(1-K)`，故相邻项偏差之和
`∑_n ‖f^{n+1} x - f^n x‖ ≤ ‖f x - x‖ / (1 - K)`。

**这解释了「迭代为什么是 Cauchy 列，从而收敛」的定量机制**
（本文件不证收敛本身 —— 那需要 `CompleteSpace`，且已在
`PipelineTendstoGen.pipeline_tendsto_gen` 的线性情形中给出）。

**⚠ 非同义反复**：前件是压缩性 + `K < 1`，结论是一个**级数和的定量上界**。 -/
theorem sum_iterate_le
    {V : Type*} [NormedAddCommGroup V]
    (f : V → V) {K : ℝ} (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hf : ∀ x y : V, ‖f x - f y‖ ≤ K * ‖x - y‖)
    (x : V) :
    ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖(f^[n+1]) x - (f^[n]) x‖
      ≤ ‖f x - x‖ * (1 - K ^ N) / (1 - K) := by
  intro N
  have hN : ∑ n ∈ Finset.range N, K ^ n = (1 - K ^ N) / (1 - K) := by
    rw [geom_sum_eq (by linarith : K ≠ 1)]
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  calc ∑ n ∈ Finset.range N, ‖(f^[n+1]) x - (f^[n]) x‖
      ≤ ∑ n ∈ Finset.range N, K ^ n * ‖f x - x‖ := by
        apply Finset.sum_le_sum
        intro n _
        exact norm_iterate_geometric f hK0 hf x n
    _ = (∑ n ∈ Finset.range N, K ^ n) * ‖f x - x‖ := by
        rw [Finset.sum_mul]
    _ = ‖f x - x‖ * (1 - K ^ N) / (1 - K) := by
        rw [hN]; ring

/-! ===========================================================================
  §2  ⭐⭐ 方案 1（交叉核对）：`ℝ≥0` 系数版，用 Mathlib 现成 `LipschitzWith`

  **如实说明**：本节的定理是 Mathlib 引理
  `LipschitzWith.dist_iterate_succ_le_geometric` 的**直接转述**
  （只把右端因子的书写顺序换成与 §1 一致）。列在此处的唯一作用是
  **交叉核对 §1 的纯推导与 Mathlib 的实现给出同一个界**，
  并让依赖 `LipschitzWith` 风格（`K : ℝ≥0`）的下游代码可直接引用本文件名。
  **本节不宣称任何新数学内容。**
  =========================================================================== -/

/-- ⭐⭐ **【`LipschitzWith` 版：与 §1 同一界（Mathlib 的直接转述）】**

`LipschitzWith K f`（`K : ℝ≥0`）时，`dist (f^[n] x) (f^[n+1] x) ≤ K^n * dist x (f x)`。

**⚠ 本定理是 Mathlib `LipschitzWith.dist_iterate_succ_le_geometric` 的直接转述，
不是本文件的新成果**；列出的目的仅为与 §1 的纯推导交叉核对，并把
`dist` 语言与 `norm` 语言对齐到同一份文件里。 -/
theorem lipschitz_iterate_dist_geometric
    {α : Type*} [MetricSpace α]
    (f : α → α) {K : NNReal} (hf : LipschitzWith K f) (x : α) (n : ℕ) :
    dist ((f^[n]) x) ((f^[n+1]) x) ≤ (K : ℝ) ^ n * dist x (f x) := by
  have h := LipschitzWith.dist_iterate_succ_le_geometric hf x n
  rwa [mul_comm] at h

/-! ===========================================================================
  §3  ⭐⭐⭐ 方案 3（接线）：`gstep` 是 `|1-η|`-Lipschitz

  这一节把 §1 的抽象结果与 `PipelineTendstoGen` 的具体管线接上：
  管线的单步映射 `gstep η θstar` **确实是**一个 `K`-收缩（只是它是**仿射**的）。
  **注意：本节只证明「线性情形满足 Lipschitz 前件」，从而说明 §1 的框架
  覆盖线性情形；它不声称管线的非线性推广已被证明。**
  =========================================================================== -/

/-- 管线单步（与 `Fate.PipelineTendstoGen.gstep` 逐字同一定义；
此处独立复述以避免引入 `PipelineTendstoGen` 的重依赖，便于单独审计）。 -/
noncomputable def gstep {V : Type*} [AddCommGroup V] [Module ℝ V]
    (η : ℝ) (θstar : V) (θ : V) : V := (1 - η) • θ + η • θstar

/-- ⭐⭐⭐ **【管线单步是 Lipschitz 收缩，常数 `|1 - η|`】**

$$\| \mathrm{gstep}\,\eta\,\theta^*\,x - \mathrm{gstep}\,\eta\,\theta^*\,y \|
   \;=\; |1-\eta|\cdot\|x - y\| .$$

因此 `gstep η θstar` 是 `|1-η|`-Lipschitz；当 `|1-η| < 1`（即
`pipeline_tendsto_gen` 的 `hη`）时它是**严格收缩**，
§1 的 `norm_iterate_geometric` 适用于它。

**⚠ 非同义反复**：前件只有 `η`、`θstar` 与（隐含的）`V` 的结构；
结论是关于 `gstep` 的一对点的距离**等式**（因而是 Lipschitz 性）。
两边定义不同，需真正计算（`sub_smul`、`smul_sub`、`norm_smul`）。 -/
theorem gstep_dist_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (θstar x y : V) :
    ‖gstep η θstar x - gstep η θstar y‖ = |1 - η| * ‖x - y‖ := by
  have h : gstep η θstar x - gstep η θstar y = (1 - η) • (x - y) := by
    simp only [gstep, smul_sub]
    abel
  rw [h, norm_smul, Real.norm_eq_abs]

/-- ⭐⭐⭐ **【`gstep` 满足 §1 的前件：`|1-η|` 为 Lipschitz 常数】**

由 `gstep_dist_eq` 直接得 `∀ x y, ‖gstep x - gstep y‖ ≤ K * ‖x - y‖`，
取 `K := |1 - η|`。

**这条把 `PipelineTendstoGen` 的线性管线正式接入 §1 的抽象框架。** -/
theorem gstep_lipschitz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (θstar : V) :
    ∀ x y : V, ‖gstep η θstar x - gstep η θstar y‖ ≤ |1 - η| * ‖x - y‖ := by
  intro x y
  rw [gstep_dist_eq]

/-- ⭐⭐ **【`LipschitzWith` 形式的 `gstep`】**

`gstep η θstar` 是 `|1-η|` 的 `NNReal` 化常数下的 `LipschitzWith` 映射。
与 §2 的 `lipschitz_iterate_dist_geometric` 配合即可得管线版的几何界。 -/
theorem gstep_lipschitzWith {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (θstar : V) :
    LipschitzWith (|1 - η|).toNNReal (gstep η θstar) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have h := gstep_lipschitz η θstar x y
  refine le_trans h ?_
  rw [Real.coe_toNNReal _ (abs_nonneg _)]

/-- ⭐⭐⭐ **【管线版几何界：直接代入 §1】**

`PipelineTendstoGen` 的迭代轨迹相邻两项偏差按 `|1-η|^n` 几何衰减：

$$\bigl\|\theta_{n+1} - \theta_{n}\bigr\| \;\le\; |1-\eta|^n \cdot \| \eta • (\theta^* - \theta_0)\|$$

其中 `θ_n := (gstep η θstar)^[n] θ₀`。

**⚠ 非同义反复**：前件是 `|1-η|` 的压缩性（`gstep_lipschitz`），
结论是轨道偏差的 `n` 次幂界，`n` 上非平凡归纳（由 §1 提供）。 -/
theorem gstep_iterate_geometric {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (θstar θ₀ : V) (n : ℕ) :
    ‖((gstep η θstar)^[n+1]) θ₀ - ((gstep η θstar)^[n]) θ₀‖
      ≤ |1 - η| ^ n * ‖gstep η θstar θ₀ - θ₀‖ :=
  norm_iterate_geometric (gstep η θstar) (abs_nonneg _) (gstep_lipschitz η θstar) θ₀ n

end PipelineLipschitz
end FateV2.Error