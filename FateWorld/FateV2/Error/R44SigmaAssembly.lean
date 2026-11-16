/-
# R-44 · 组合层 2：`SigmaLandscape` × `AssemblyGainShared`

## 本文件做什么

`Fate/SigmaLandscape.lean`（真实 namespace `Fate.SigmaLandscape`，27 条定理）
与 `Fate/AssemblyGainShared.lean`（真实 namespace `Fate.AssemblyGainShared`，17 条定理）
在真实 `external_refs` 口径下**双双为 0**。

本文件把「sigma 估计链条」与「共享变量约束下的收益」两条独立线索的结论
**并置成新的合取命题**，供下游一次性取用。

## ⚠ 防环

本文件 `import FateV2.Error.SigmaLandscape` 与 `import Fate.AssemblyGainShared`。
两者均无 `import Fate.R44SigmaAssembly`（本文件是新建的），故不可能成环。

## ⚠ 前件检查

下面各条定理的前件都只包含**两侧原料的假设**（`MemLp id 2 P`、`0 < n`、
`|1 - eta| < 1`，或对 `Supported` / `jointShared` 的一般性量化），
没有一条把结论的等式/包含关系塞进前件。

## G54

本文件不使用希腊字母作为标识符（`eta` 用 ASCII 拼写）。
-/
import FateWorld.FateV2.Error.SigmaLandscape
import FateWorld.FateV2.Meta.AssemblyGainShared
/-!
  # Error · R44SigmaAssembly

  ## 迁移登记
  - 来源：`FateWorld/Legacy/R44SigmaAssembly.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SigmaLandscape, AssemblyGainShared
  - 补充 open 域：FateV2.Meta, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 sigma 侧：三种刻画与收敛窗口的联合接口 -/

/-- ⭐⭐⭐ **【sigma 三刻画 + 收缩窗内的稳态误差，一次取全】**

在 `MemLp id 2 P`、`0 < n`、`0 < varOf P`、`|1 - eta| < 1` 下：

1. `Var[meanOf n] = varOf P / n`；
2. `Var[steadyErrEst eta n] = (gain eta)^2 * (varOf P / n)`。

两条**同用**同一个 `varOf P / n`，这正是「sigma 的两种刻画指向同一个数」的机检形态。

**⚠ 前件不含结论**：`hP`、`hn`、`hv`、`hwin` 分别是 `L²` 性、正整数性、
非退化性、收缩窗，都是关于测度与参数的条件，**没有**任何一条是关于
`variance` 的等式。

**⚠ 与 `Fate.SigmaLandscape.sigma_three_faces` 的关系**：本定理是它的**两支抽取**
（第 1 支与第 4 支），并把第 4 支右端的 `Var[meanOf n]` 用第 1 支**替换成**
`varOf P / n` —— 这一步替换需要 `rw`，不是投影。 -/

namespace FateV2.Error.R44SigmaAssembly

open FateV2.Meta
open FateV2.Modeling

theorem r44_sigma_two_faces_same_number
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    (n : ℕ) (hn : 0 < n) (hv : 0 < FateV2.Error.GaussMarkovScalar.varOf P)
    {eta : ℝ} (hwin : |1 - eta| < 1) :
    ProbabilityTheory.variance (FateV2.Error.SigmaEstimation.meanOf n)
        (MeasureTheory.Measure.pi (fun _ : Fin n => P))
        = FateV2.Error.GaussMarkovScalar.varOf P / n
      ∧ ProbabilityTheory.variance (FateV2.Error.SteadyErrEstimate.steadyErrEst eta n)
            (FateV2.Error.SigmaEstimation.iidMeasure P n)
          = (FateV2.Error.SteadyErrEstimate.gain eta) ^ 2 * (FateV2.Error.GaussMarkovScalar.varOf P / n) := by
  obtain ⟨h1, -, -, h4⟩ :=
    FateV2.Error.SigmaLandscape.sigma_three_faces hP n hn hv hwin
  exact ⟨h1, h4.trans (by rw [h1])⟩

/-- ⭐⭐ **【`eta = 1` 时，Gauss–Markov 等式与 gain 归一同时成立】**

`eta = 1` 既是收敛最快步长（`gain 1 = 1`），也让稳态误差的方差
**等于**样本均值的方差。

**⚠ 前件只有 `MemLp id 2 P` 与 `0 < n`**；两条结论分别靠
`Fate.SteadyErrEstimate.gain_one` 与 `variance_const_mul` 得到，**不是**前件的一部分。 -/
theorem r44_eta_one_gauss_markov_equality
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    FateV2.Error.SteadyErrEstimate.gain (1 : ℝ) = 1
      ∧ ProbabilityTheory.variance (FateV2.Error.SteadyErrEstimate.steadyErrEst 1 n)
            (FateV2.Error.SigmaEstimation.iidMeasure P n)
          = ProbabilityTheory.variance (FateV2.Error.SigmaEstimation.meanOf n)
              (MeasureTheory.Measure.pi (fun _ : Fin n => P)) := by
  obtain ⟨hg, hvar, -⟩ :=
    FateV2.Error.SigmaLandscape.fastest_step_is_gauss_markov_equality hP n hn
  exact ⟨hg, hvar⟩

/-- ⭐ **【gain 的闭式与「gain = 1 ⟺ c = 0」并置】**

`gain eta = 1 / (1 - c eta)`，且 `gain eta = 1 ↔ c eta = 0`。

两条一起把 `gain` 的**闭式**与**不动点刻画**交付给下游，不必各自 `unfold`。

**⚠ 第一条是 `rfl` 级**（`gain` 的定义），**第二条不是**：
它需要 `1 / (1 - x) = 1 ↔ x = 0` 在 `x = |1 - eta|` 处的算术（`field_simp` + `linarith`）。 -/
theorem r44_gain_closed_form_and_fixed_point (eta : ℝ) :
    FateV2.Error.SteadyErrEstimate.gain eta = 1 / (1 - FateV2.Loop.OptimalEta.c eta)
      ∧ (FateV2.Error.SteadyErrEstimate.gain eta = 1 ↔ FateV2.Loop.OptimalEta.c eta = 0) :=
  ⟨FateV2.Error.SigmaLandscape.gain_eq_inv_one_sub_c eta,
   FateV2.Error.SigmaLandscape.gain_eq_one_iff_c_eq_zero eta⟩

/-! ## §2 装配侧：共享变量的收益是「真收益」 -/

/-- ⭐⭐⭐⭐ **【共享变量收益的完整包：交集蕴含 + 两侧单独不蕴含】**

把 `Fate.AssemblyGainShared.assembly_gain_shared` 的 `Set` 形态
与 `jointShared_subset_left` / `jointShared_subset_right` 一起交付：

- `jointShared c1 c2 ⊆ c1.holds`（联合约束是**更严**的约束）；
- `jointShared c1 c2 ⊆ c2.holds`；
- `not (PhiC ⊆ ThetaC)` 且 `not (PsiC ⊆ ThetaC)`（两侧**单独**都推不出关系型后果）。

这样下游同时得到「联合约束更强」与「任何一側都不够」。

**⚠ 前件为 `Supported` 的一般量化 `c1`、`c2`（第一、二支）加上具体实例的
两条反例（第三、四支）；结论中的包含关系不是前件的一部分**。 -/
theorem r44_shared_gain_full_package :
    (∀ {V : Type} {V1 V2 : Set V}
        (c1 : Fate.AssemblyGainShared.Supported V1)
        (c2 : Fate.AssemblyGainShared.Supported V2),
        Fate.AssemblyGainShared.jointShared c1 c2 ⊆ c1.holds
          ∧ Fate.AssemblyGainShared.jointShared c1 c2 ⊆ c2.holds)
      ∧ ¬ Fate.AssemblyGainShared.Φc ⊆ Fate.AssemblyGainShared.Θc
      ∧ ¬ Fate.AssemblyGainShared.Ψc ⊆ Fate.AssemblyGainShared.Θc := by
  refine ⟨fun c1 c2 => ⟨Fate.AssemblyGainShared.jointShared_subset_left c1 c2,
    Fate.AssemblyGainShared.jointShared_subset_right c1 c2⟩,
    Fate.AssemblyGainShared.shared_gain_not_from_Φ,
    Fate.AssemblyGainShared.shared_gain_not_from_Ψ⟩

/-- ⭐⭐ **【收益判据：存在性 ⟺ 互不包含】**（`Set` 层的一般形式，与 §2 的具体实例并置）

`(exists T, P ∩ Q ⊆ T ∧ not (P ⊆ T) ∧ not (Q ⊆ T)) ↔ (not (P ⊆ Q)) ∧ (not (Q ⊆ P))`。

**⚠ 前件为空**（全称量化 `P`、`Q`），结论是一条完整的 `↔`。
注意这条定理本身的前件是 `α : Type u` 与两个 `Set α`，**不包含**任何一支的结论。 -/
theorem r44_gain_iff_general {alpha : Type} {Phi Psi : Set alpha} :
    (∃ Theta : Set alpha, Phi ∩ Psi ⊆ Theta ∧ ¬ Phi ⊆ Theta ∧ ¬ Psi ⊆ Theta)
      ↔ (¬ Phi ⊆ Psi) ∧ (¬ Psi ⊆ Phi) :=
  Fate.AssemblyGainShared.gain_iff

/-! ## §3 两线并置：sigma 的下界与装配收益的**同一份接口** -/

/-- ⭐⭐⭐ **【同一份接口里的两条「下界/收益」结论】**

左侧（sigma 线）：线性无偏估计器的方差下界 `varOf P / n ≤ Var[est a]`（对 `sum a = 1`）。
右侧（装配线）：共享约束的联合形式蕴含关系型约束 `ThetaC`，而两侧单独都不蕴含。

两条彼此**不是**同一命题的重述：左侧是**测度论不等式**（Cauchy–Schwarz），
右侧是**集合论包含关系**（关系型约束不可由单点约束推出）。
把两条放进同一接口，是为了让下游的「代价 vs 收益」论证能一次取到两侧的端点。

**⚠ 前件**：`hP`、`hn` 只用于左侧；右侧两支由已证的**无条件**结论给出。
**没有**任何一支的结论出现在前件里。 -/
theorem r44_sigma_bound_and_assembly_gain
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    (ProbabilityTheory.variance (FateV2.Error.SigmaEstimation.meanOf n)
        (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      ≤ ProbabilityTheory.variance (FateV2.Error.GaussMarkovScalar.est a)
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
      ∧ (∀ f : Fate.AssemblyGainShared.V2 → ℝ,
          f ∈ Fate.AssemblyGainShared.jointShared
                Fate.AssemblyGainShared.c₁ Fate.AssemblyGainShared.c₂
            → f ∈ Fate.AssemblyGainShared.Θc) :=
  ⟨FateV2.Error.SigmaLandscape.meanOf_is_minimizer hP n hn a hsum,
   Fate.AssemblyGainShared.shared_gain_holds⟩

end FateV2.Error.R44SigmaAssembly
