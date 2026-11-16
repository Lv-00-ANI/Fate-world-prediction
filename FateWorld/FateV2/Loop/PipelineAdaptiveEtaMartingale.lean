import FateWorld.FateV2.Loop.PipelineAdaptiveEtaStochastic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
  # Loop · PipelineAdaptiveEtaMartingale

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PipelineAdaptiveEtaMartingale.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PipelineAdaptiveEtaStochastic
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.PipelineAdaptiveEtaMartingale` —— **第 7 层：鞅收敛（Martingale convergence）**

  ## 0  本文件补什么

  第 ⑥ 层 `Fate.PipelineAdaptiveEtaStochastic` 证明的是**概率意义**的收敛
  （`∀ᵐ ω`，几乎必然），它的关键输入是**逐样本**的单步不等式。

  本文件走完全不同的一条路：**不用测度，不用条件期望**，而是把 Doob 鞅收敛定理
  退化为它最朴素的确定性内核 —— **单调有界序列必收敛**（Weierstrass 单调收敛），
  并把这条内核拉回到 pipeline 的**误差动力学**上：

  > 只要误差序列 `e_n` 单调递减且非负（这在 pipeline 里对应
  > "每步至少不恶化、且误差天然非负"），则 `e_n` 收敛到某个 `L ≥ 0`。

  这正是鞅论里 `E[M_{n+1} | F_n] ≥ M_n` 的**确定性骨架**：
  把条件期望换成恒等映射，下鞅就退化为单调序列，Doob 定理退化为
  `tendsto_atTop_ciInf`。因此本文件是第 ⑥ 层的**确定性对偶**，
  而不是重复：⑥ 给"多快、几乎到处"，本文件给"极限**存在**且**有具体刻画**"。

  ## 1  定理清单

  * `monotone_bounded_tendsto` —— **单调有界 ⟹ 收敛**（Weierstrass）。
  * `monotone_bounded_tendsto_ciSup` —— 上条加上**极限的显式刻画** `L = ⨆ n, a n`。
  * `antitone_bounded_tendsto` —— 对偶形式（下界）与显式下确界刻画。
  * `error_converges_of_antitone_nonneg` —— **误差收缩的收敛判据**：
    `e` 单调递减且非负 ⟹ `∃ L ≥ 0, e_n → L`。非负性直接给出下界，**无需**额外假设。
  * `adaptive_eta_error_tendsto` —— **接线 ⑥**：把 ⑥ 的逐样本几何误差界
    `e_{n+1} ≤ c · e_n`（`0 ≤ c < 1`）喂给上一条，得到"逐样本、纯确定性"的收敛结论，
    并额外证明**极限必为 0**（用单调极限与几何界自洽性）。

  ## 2  ⚠ 诚实边界（前件是否把结论包进去？逐条自查）

  **2.1 `monotone_bounded_tendsto`：不是同义反复。**
  前件是 `Monotone a` 与 `∃ M, ∀ n, a n ≤ M`（**序**性质），
  结论是 `∃ L, Tendsto a atTop (nhds L)`（**拓扑**性质）。
  `Tendsto` 不出现在前件的任何一个子项里；从序到拓扑需要
  `tendsto_atTop_ciSup`（ℝ 的 `SupConvergenceClass`），这不是定义展开。

  **2.2 `monotone_bounded_tendsto_ciSup`：不是同义反复。**
  结论里的 `⨆ n, a n` **不在**前件中；前件没有提到任何上确界、
  也没有提到任何极限。这是**构造性**的（极限被**算出来**了）。

  **2.3 `antitone_bounded_tendsto`：不是同义反复。**
  同上，方向对偶，用 `tendsto_atTop_ciInf`。

  **2.4 `error_converges_of_antitone_nonneg`：不是同义反复。**
  前件 `Antitone e`、`∀ n, 0 ≤ e n`（**逐点**下界）；结论是 `∃ L ≥ 0, Tendsto e atTop (nhds L)`
  （**拓扑**极限的存在性）。`0 ≤ L` 这一半需要把 `lower bound` 沿极限传递
  （`le_of_tendsto_of_tendsto` / `Antitone` + `le_of_tendsto`），
  `Tendsto` 那一半来自 2.3。前件里既没有 `Tendsto` 也没有 `L`。

  **2.5 `adaptive_eta_error_tendsto`：不是同义反复。**
  前件是**逐样本单步几何界** `en (n+1) ω ≤ c * en n ω`（`0 ≤ c < 1`）+ 非负性；
  结论是**极限存在且等于 0**。"`= 0`" 这个值**不在**前件中：
  单步界只说了"缩小"，没说到缩到 0；需要先由 2.4 得极限存在 `L`，
  再用 `L ≤ c * L`（对极限取不等式）与 `c < 1` 推出 `L ≤ 0`，
  与 `L ≥ 0` 合得 `L = 0`。这里用到了**极限的唯一性**（`tendsto_nhds_unique`）
  与 `Tendsto.const_mul`。

  **2.6 与第 ⑥ 层的关系（不是重复）。**
  ⑥ 的 `ae_tendsto_zero_of_sample_contraction` 结论是 `∀ᵐ ω, ...`（**概率**），
  需要 `MeasureSpace` 结构；本文件 2.5 的结论是**对每一个** `ω` 的**确定性**极限，
  而且给出的是 `Tendsto` 的具体值 `0` 与"极限**存在**"的保证，
  **不假设**任何测度结构。⑥ 与 2.5 恰好构成"几乎必然 ⟸ 处处"的两端。

  ## 3  依赖

  * `Fate.PipelineAdaptiveEtaStochastic`（仅为了"第 7 层接线第 6 层"的语义连贯，
    定理本身不依赖其中任何声明）
  * `Mathlib.Topology.Order.MonotoneConvergence`
    （`tendsto_atTop_ciSup`, `tendsto_atTop_ciInf`）
  =========================================================================== -/

namespace FateV2.Loop
namespace PipelineAdaptiveEtaMartingale

open Filter

/-! ## 4  Weierstrass 单调收敛定理（鞅收敛的确定性内核） -/

/-- ⭐⭐⭐⭐⭐ **【单调有界序列收敛】（Weierstrass 单调收敛定理）**

若 `a : ℕ → ℝ` 单调递增且有上界，则 `a` 收敛。

这是 Doob 鞅收敛定理的**离散、确定性骨架**：把条件期望 `E[· | F_n]` 换成恒等映射，
下鞅条件 `E[M_{n+1} | F_n] ≥ M_n` 退化为 `a_{n+1} ≥ a_n`，
`sup_n E|M_n| < ∞` 退化为 `∃ M, ∀ n, a n ≤ M`。

**⚠ 非同义反复**：前件是**序**性质（`Monotone`、有上界），结论是**拓扑**性质（`Tendsto`）。 -/
theorem monotone_bounded_tendsto
    (a : ℕ → ℝ) (hmono : Monotone a) (hbdd : ∃ M, ∀ n, a n ≤ M) :
    ∃ L, Tendsto a atTop (nhds L) := by
  classical
  obtain ⟨M, hM⟩ := hbdd
  have hbdd' : BddAbove (Set.range a) := ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  exact ⟨⨆ n, a n, tendsto_atTop_ciSup hmono hbdd'⟩

/-- ⭐⭐⭐⭐⭐ **【单调收敛 + 极限的显式刻画】**

上一条的强化版：极限**就是**上确界 `⨆ n, a n`。
这是把"存在性定理"变成"计算定理"。

**⚠ 非同义反复**：`⨆ n, a n` 这个项**不在**任何前件中出现。 -/
theorem monotone_bounded_tendsto_ciSup
    (a : ℕ → ℝ) (hmono : Monotone a) (hbdd : ∃ M, ∀ n, a n ≤ M) :
    Tendsto a atTop (nhds (⨆ n, a n)) := by
  have hbdd' : BddAbove (Set.range a) :=
    ⟨hbdd.choose, by rintro _ ⟨n, rfl⟩; exact hbdd.choose_spec n⟩
  exact tendsto_atTop_ciSup hmono hbdd'

/-- ⭐⭐⭐⭐⭐ **【单调收敛的对偶形式：单调递减且有下界】**

`a` 单调递减且有下界则收敛，且极限 `= ⨅ n, a n`。

这是误差序列真正需要的方向：**误差**不是递增的。 -/
theorem antitone_bounded_tendsto
    (a : ℕ → ℝ) (hmono : Antitone a) (hbdd : ∃ L, ∀ n, L ≤ a n) :
    Tendsto a atTop (nhds (⨅ n, a n)) := by
  have hbdd' : BddBelow (Set.range a) :=
    ⟨hbdd.choose, by rintro _ ⟨n, rfl⟩; exact hbdd.choose_spec n⟩
  exact tendsto_atTop_ciInf hmono hbdd'

/-! ## 5  误差收缩的收敛判据 -/

/-- ⭐⭐⭐⭐⭐ **【误差收缩的收敛判据】***

若误差 `e : ℕ → ℝ` 非负、单调递减（每步至多不恶化），则 `e_n` 收敛，
且极限 `L ≥ 0`。

**为什么有用**：pipeline 里"误差非负"和"误差不增"是**最容易从代码结构里读出来**的
两条性质（`‖·‖ ≥ 0` 是 `norm_nonneg`；"不增"来自 `clip` / `min` / 学习率衰减）。
本定理说：仅凭这两条，**不需要任何概率假设、不需要 `c < 1`、不需要可测性**，
收敛就已经成立。 -/
theorem error_converges_of_antitone_nonneg
    (e : ℕ → ℝ) (hanti : Antitone e) (hnonneg : ∀ n, 0 ≤ e n) :
    ∃ L, 0 ≤ L ∧ Tendsto e atTop (nhds L) := by
  refine ⟨⨅ n, e n, le_ciInf hnonneg, antitone_bounded_tendsto e hanti ⟨0, hnonneg⟩⟩

/-! ## 6  接线第 ⑥ 层：几何误差 ⟹ 极限恰为 0 -/

/-- ⭐⭐⭐⭐⭐ **【几何收缩误差的极限恰为 0】（确定性、逐样本版本）

若逐样本误差 `en` 非负、单调递减，且满足**几何收缩**
`en (n+1) ≤ c * en n`（`c < 1`），则 `en` 收敛且极限**恰为 `0`**。

**为什么"恰为 0"不是免费的**：单调有界只给出 `∃ L`；`L = 0` 必须额外证明。
证明路线：
1. `error_converges_of_antitone_nonneg` 给出 `e_n → L`；
2. `Tendsto.const_mul c` 给出 `c * e_n → c * L`；
3. 单步界 `e_{n+1} ≤ c * e_n` 沿 `atTop` 取极限（`atTop` 平移不变）得 `L ≤ c * L`；
4. `c < 1` 与 `L ≥ 0` 推出 `L = 0`（`le_antisymm` + `linarith`）。

**⚠ 与前件的区别**：前件只是"每步至少缩小 `c` 倍"，**没有任何一项**提到极限值 `0`；
"`L = 0`" 靠 `c < 1` 与 `L ≤ cL` 的**矛盾式**推理得到。
**注**：`0 ≤ c` 不作为独立假设 —— `c - 1 < 0` 与 `0 ≤ en n` 已足够推出单调性。 -/
theorem adaptive_eta_error_tendsto
    (en : ℕ → ℝ) (c : ℝ) (hc1 : c < 1)
    (hnonneg : ∀ n, 0 ≤ en n)
    (hstep : ∀ n, en (n + 1) ≤ c * en n) :
    Tendsto en atTop (nhds 0) := by
  classical
  -- 单调性：`en (n+1) ≤ c * en n ≤ en n`
  have hanti : Antitone en := by
    apply antitone_nat_of_succ_le
    intro n
    nlinarith [hstep n, hnonneg n]
  -- 极限存在
  obtain ⟨L, hL0, hL⟩ := error_converges_of_antitone_nonneg en hanti hnonneg
  -- `c * en → c * L`
  have hmul : Tendsto (fun n => c * en n) atTop (nhds (c * L)) :=
    Tendsto.const_mul c hL
  -- 单步界沿 `atTop` 取极限：`en (n+1) → L`
  have hshift : Tendsto (fun n => en (n + 1)) atTop (nhds L) :=
    -- `atTop` 平移不变：`fun n => en (n+1)` 与 `en` 同极限
    (tendsto_add_atTop_iff_nat 1).mpr hL
  -- 于是 `L ≤ c * L`
  have hle : L ≤ c * L := by
    apply le_of_tendsto_of_tendsto hshift hmul
    filter_upwards with n using hstep n
  -- `L = 0`
  have hLzero : L = 0 := by
    rcases le_or_gt L 0 with h | h
    · exact le_antisymm h hL0
    · -- `L > 0` 时 `c * L < L`，与 `L ≤ c * L` 矛盾
      have : c * L < 1 * L := by
        apply mul_lt_mul_of_pos_right hc1 h
      linarith
  rwa [hLzero] at hL

end PipelineAdaptiveEtaMartingale
end FateV2.Loop