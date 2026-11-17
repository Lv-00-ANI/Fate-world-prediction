/-
命运理论 · 开放问题 1.1（路径空间的测度）· 有限视窗情形
============================================================

净版原文（`10-命运理论-净版.md:127`）：
> **[开放问题] 开放问题 1.1（路径空间的测度）**
> 当 `T = ℝ≥0` 且状态为随机变量时，「随机过程的样本路径」这一说法要求先给定一个函数空间
> 及其上的 σ-代数与概率测度，否则「轨迹的分布」无定义。原素材**从未给出该路径空间与其上的测度**。
> 本问题阻塞**第 4 章**对「随机轨迹」的全部陈述。

---------------------------------------------------------------------------
本文件做到了什么
---------------------------------------------------------------------------
`Fate/TrajGenStochastic.lean:201` 已给出**有限视窗** `Fin T` 上的轨迹测度
    `trajLaw F f T D0 Dε θ u a : Measure (Traj (Fin T) F.X)`
    （其定义为 `unfold_# (D0 ⊗ Dε^{⊗T})`）。
本文件证明：**当 `D0`、`Dε` 都是概率测度、且单步 `f` 在 (状态, 噪声) 上联合可测时，
`trajLaw` 本身是一个概率测度**（`IsProbabilityMeasure`）。

即：轨迹空间 `Traj (Fin T) F.X` 上确有一个**概率测度**，
从而「（有限视窗内的）轨迹的分布」——作为该概率测度——**有定义**。

定理：`isProbabilityMeasure_trajLaw`。

---------------------------------------------------------------------------
前件说明（务必阅读：这不是同义反复）
---------------------------------------------------------------------------
- `[IsProbabilityMeasure D0]`、`[IsProbabilityMeasure Dε]`：
  这两条是**输入分布**的概率性。`InitDist`/`Dist` 只是 `Measure` 的别名，
  **类型层不保证**它们是概率测度；若 `D0` 或 `Dε` 是零测度或无穷测度，
  `trajLaw` 只是**非零测度/无穷测度/零测度**，而不是概率测度。
  故此两条是**实质性前件**，结论（`trajLaw` 是概率测度）**不蕴含**它们。
- `hstep : ∀ n, Measurable (fun p : X × Ν => f p.1 (u n) p.2 θ (a n))`：
  这是「单步随机转移可测」这一**正则性假设**，标准马尔可夫核理论本就要求。
  `Step F` 只是裸函数类型 `X → U → Ν → Θ → Act → X`（`Fate/Frame.lean:146`），
  **不含任何可测性**，故须显式携带；否则 `unfold` 不可测，推前测度不可定义。
  在本文件中，由 `hstep` **推出** `unfold` 的可测性（见证明中的 `hstate`），
  而非把「`unfold` 可测」直接当作同义反复式前提。

---------------------------------------------------------------------------
本文件没做到什么
---------------------------------------------------------------------------
- **连续时间 `T = ℝ≥0` 完全未做。** 净版 1.1 的原问题正是关于 `T = ℝ≥0` 的
  「随机过程的样本路径」；本文件仅覆盖 `TrajGenStochastic` 已实现的**有限视窗** `Fin T`。
  连续时间/无穷索引需 Kolmogorov 扩张定理（`TrajGenStochastic` §7 已登记为外部假设），本文件不涉及。
- 不证明 `trajLaw` 与任何「路径空间上的正则测度」（如 Wiener 测度）的关系。

---------------------------------------------------------------------------
不声称
---------------------------------------------------------------------------
**本文件不声称「开放问题 1.1 已解决」。** 只声称：
「有限视窗 `Fin T` 情形下，`trajLaw` 是一条概率测度（故有概率测度可用）」。
对 `T = ℝ≥0` 该问题仍未解。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 全程无未完成证明项、无外部公设（无需引入额外公理）。
- 只 import 既有入链模块，不修改任何既有文件。
-/

import FateWorld.FateV2.Model.TrajGenStochastic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace FateV2.Model
namespace TrajLawIsProb

open MeasureTheory

noncomputable section

/-!
  # Model · TrajLawIsProb

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TrajLawIsProb.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TrajGenStochastic
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## 辅助：`hstep` ⟹ `unfold` 可测

`unfold` 由 `stateAt` 沿 `f` 逐点递推定义；`stateAt` 关于 `(x₀, ω)` 的可测性
可由 `hstep` 对时间 `n` 归纳得到，进而 `unfold` 作为 `Π i, X` 中一元可测。 -/

private theorem measurable_unfold_of_hstep
    (F : Frame) [MeasurableSpace F.Ν.Carrier] [MeasurableSpace F.X.Carrier]
    (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier)
    (hstep : ∀ n : Fin T, Measurable (fun p : F.X.Carrier × F.Ν.Carrier =>
      f p.1 (u n) p.2 θ (a n))) :
    Measurable (unfold F f T θ u a) := by
  have hstate : ∀ n : ℕ, ∀ (hn : n ≤ T),
      Measurable (fun p : F.X.Carrier × (Fin T → F.Ν.Carrier) =>
        stateAt F f T θ u a p.2 p.1 n hn) := by
    intro m
    induction m with
    | zero => intro _; exact measurable_fst
    | succ k ih =>
        intro hn
        have hk : k ≤ T := Nat.le_of_succ_le hn
        have hklt : k < T := hn
        have hprev := ih hk
        have hstepk := hstep ⟨k, hklt⟩
        have hproj : Measurable (fun p : F.X.Carrier × (Fin T → F.Ν.Carrier) =>
            p.2 (⟨k, hklt⟩ : Fin T)) :=
          (measurable_pi_apply (⟨k, hklt⟩ : Fin T)).comp measurable_snd
        have hmm : Measurable (fun p : F.X.Carrier × (Fin T → F.Ν.Carrier) =>
            (stateAt F f T θ u a p.2 p.1 k hk, p.2 (⟨k, hklt⟩ : Fin T))) :=
          hprev.prodMk hproj
        exact hstepk.comp hmm
  rw [measurable_pi_iff]
  intro n
  change Measurable (fun p : F.X.Carrier × (Fin T → F.Ν.Carrier) =>
    stateAt F f T θ u a p.2 p.1 n.val (Nat.le_of_lt n.isLt))
  exact hstate n.val (Nat.le_of_lt n.isLt)

/-! ## 主定理 -/

/-- ⭐⭐ **【开放问题 1.1 · 有限视窗情形】**：`trajLaw` 是一个概率测度。

**意义**：给出「轨迹空间 `Traj (Fin T) F.X` 上的概率测度」的存在性，
从而「（有限视窗内）轨迹的分布」**有定义**——正是净版 1.1 所要求的
「先给定函数空间及其上的 σ-代数与概率测度」在有限时间离散视窗下的落实。

**证明**：`trajLaw = unfold_# (D0 ⊗ Dε^{⊗T})`。由 `D0`、`Dε` 为概率测度，
`Measure.pi` 与 `Measure.prod` 的概率性自动给出乘积测度是概率测度；
再由 `hstep` 得 `unfold` 可测，故推前测度仍为概率测度
（`Measure.isProbabilityMeasure_map`）。

⚠ **只对有限视窗 `Fin T` 成立**；`T = ℝ≥0`（连续时间）的情形**本文件不做**。 -/
theorem isProbabilityMeasure_trajLaw
    (F : Frame) [MeasurableSpace F.Ν.Carrier] [MeasurableSpace F.X.Carrier]
    (f : Step F) (T : ℕ) (D0 : InitDist F) (Dε : Dist F.Ν)
    (θ : F.Θ.Carrier) (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier)
    [IsProbabilityMeasure D0] [IsProbabilityMeasure Dε]
    (hstep : ∀ n : Fin T, Measurable (fun p : F.X.Carrier × F.Ν.Carrier =>
      f p.1 (u n) p.2 θ (a n))) :
    IsProbabilityMeasure (trajLaw F f T D0 Dε θ u a) := by
  unfold trajLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_unfold_of_hstep F f T θ u a hstep).aemeasurable

end

end TrajLawIsProb
end FateV2.Model