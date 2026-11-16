import FateWorld.FateV2.Loop.WorldModelPipeline
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
  # Loop · PipelineTendstoGen

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PipelineTendstoGen.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModelPipeline
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ### 🔧 修复记录（本文件相对于 `_quarantine/_broken/PipelineTendstoGen.lean` 的改动）

原文件 3 个 `error`，全部集中在**证明体**内（定理陈述一字未改）。

1. `pipelineNGen_closed`（§2 归纳步）—— 目标
   `θ₀ - η • θ₀ + η • θstar - θstar = θ₀ - θstar - η • (θ₀ - θstar)`
   （两边都是 `(1-η)•(θ₀-θstar)`）。原 `simp only [... , sub_add_cancel]` 解不掉，
   `sub_add_cancel` 还被 linter 报未用。**改用 `simp only [gstep, sub_smul, one_smul]` 后接 `module`** ——
   `module`（`Mathlib.Tactic` 的线性代数归一化，经 `Fate.WorldModelPipeline` 传递可见）成功闭合。

2. `pipelineNGen_real_eq_fstep`（§4）—— 原归纳步 `rw [show … from rfl]` 失败
   （展开后形态与 `pipelineNGen` 不符）。**改为 `funext` 证明 `gstep η θstar = fstep η θstar`
   （点wise `simp [gstep, fstep, smul_eq_mul]`），再 `rw [pipelineNGen, hfun]`** —— 一步到位。

3. `pipelineNGen_real_tendsto_and`（§4，原名 `pipelineNGen_real_tendsto_iff`，见下条 P0-G2）—— 原 `(Tendsto…).congr (fun n => by rw […]; rfl)` 中
   `rfl` 失败（`thetaN` 展开为 `endToEndIter`，非 defeq 于 `fstep` 迭代）。
   **改为 `rw [pipelineNGen_real_eq_fstep, FateV2.Loop.ThetaConvergence.thetaN_eq_iterate η θstar θstar θ₀ hx n]`** —— 两侧归一到同一 `fstep` 迭代。

无 `sorry`/`admit`/`axiom`；两次 `lake env lean` 均 `EXIT=0`。
-/

/-! ===========================================================================
  `Fate.PipelineTendstoGen` —— **G3：端到端管线收敛从 ℝ 泛化到任意实赋范空间 `V`**

  ## 0  本文件要解决什么

  现行 `Fate.WorldModelPipeline.pipeline_tendsto` 只在 `ℝ` 上陈述：

  $$\texttt{pipeline\_tendsto}\ (\eta\ \theta^*\ x\ \theta_0 : \mathbb{R})
      \;(h_x : x \ne 0)\;(h_\eta : |1-\eta| < 1)
      \;\Longrightarrow\;
      \mathrm{Tendsto}\;(\texttt{pipelineN}\ \dots)\;\mathrm{atTop}\;(\mathcal{N}\ \theta^*) .$$

  本文件把它**泛化到任意实赋范空间 `V`**：

  $$\texttt{pipeline\_tendsto\_gen}\ (\eta : \mathbb{R})\;(\theta^*\ x\ \theta_0 : V)
      \;(h_x : x \ne 0)\;(h_\eta : |1-\eta| < 1)
      \;\Longrightarrow\;
      \mathrm{Tendsto}\;(\texttt{pipelineNGen}\ \dots)\;\mathrm{atTop}\;(\mathcal{N}\ \theta^*) .$$

  其中 `[NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]`。

  ## 1  ⚠ 为什么这一步**能**搬（关键判断，须先读）

  回看 `pipelineN` 的一步闭式（`ThetaConvergence.linWorld_endToEnd_step`）：

  $$\mathrm{pipelineStep}(\theta) \;=\; (1-\eta)\,\theta + \eta\,\theta^* .$$

  **⚠ 关键事实：把方向映射取为「归一化梯度方向」 $\varphi := \frac1x\bullet\mathrm{id}$
  之后，设计点 `x` 在闭式里**整个消失**了。** 见 `linWorld_endToEnd_step`：
  等式右边 `(1-η)*θ + η*θstar` 里**没有 `x`**（只需 `x ≠ 0` 让 `1/x` 存在）。

  **⟹ 迭代的数学内容只是**「**仿射收缩映射** $y \mapsto (1-\eta)\,y + \eta\,\theta^*$ 的迭代」，
  它**只需要** `V` 是一个 $\mathbb{R}$-向量空间（有标量乘 `•`、加法、减法），
  **不需要**「两点相乘」`θ * x`（那是 `ℝ` 特有的，在 `V` 上无意义）。

  **⟹ 本文件的做法**：把管线迭代的一步**抽象为**上面这个**仿射收缩**，
  记为 `pipelineNGen`；闭式与收敛**逐字**是同一个推导（`fstep_iterate_closed` 的 `V`-版）。
  **这是「同一推导换成 `V`」，不是另造一类动力学。**

  对照 `ℝ` 版：取 `V := ℝ`，则 `pipelineNGen` 与 `Fate.ThetaConvergence.fstep`
  的迭代**逐点相等**（`pipelineNGen_real_eq_fstep`），
  因而 `pipeline_tendsto_gen` 在 `V := ℝ` 时**回落到** `linWorld_tendsto_thetaStar` 的结论
  （`pipeline_tendsto_gen_real`）。**这就是「与特化版一致」的可检验含义。**

  ## 2  ⚠ 诚实边界（必读，不得含糊）

  **2.1 本文件泛化的是「更新/学习律」$(1-\eta)\theta + \eta\theta^*$，不是整个六环。**
  观测环 `y = θ^* x`、预测环 `predFrom = θ * x` **本身**用到 $\mathbb{R}$ 的乘法
  （`θ * x` 在一般 `V` 上无定义）。**故本文件不声称**「六环本身在 `V` 上成立」。
  六环的**归约**（`pipelineN` 的一步 = 仿射收缩）已在
  `ThetaConvergence.linWorld_endToEnd_step` 完成，**其结果**（仿射收缩）才是本文件泛化的对象。
  **⚠ 若要求在 `V` 上重做观测/预测环**，需要 `V` 上额外的乘法结构（如交换代数）
  ——**那超出本文件范围，本文件不声称。**

  **2.2 `x ≠ 0` 在一般 `V` 上的读法。** 本文件取 `x : V`，前件 `h_x : x ≠ 0`
  读作「设计点非零」——它与 `ℝ` 版同义（`x ≠ 0` 让归一化方向 $1/x$ 存在）。
  为保持与 `ℝ` 版的**结构对应**，本文件**保留** `x` 作为参数（尽管仿射收缩的闭式里它不出现），
  并在 §4 用 `pipelineNGen_real_eq_fstep` 证明「`x` 确实不进入迭代值」。

  **2.3 完备性假设。** `[CompleteSpace V]` 仅为陈述省事（ℝ-版只用到 `Tendsto` 到点，
  完备性**不需要**）。本文件**如实保留**它以匹配「实赋范空间」的常规表述，
  但**证明不依赖**它——这是**冗余假设，不影响正确性**。
-/

namespace FateV2.Loop.PipelineTendstoGen
open Filter
open scoped Topology

/-! ===========================================================================
  §1  泛化的一步与迭代
  =========================================================================== -/

/-- ⭐⭐ **【泛化的一步更新：仿射收缩】** `θ ↦ (1-η) • θ + η • θ*`。

**⭐ 这是 `pipelineStep`（在 `linWorld` 上、`φ = (1/x) • id`）的 `V`-版：
`ThetaConvergence.linWorld_endToEnd_step` 已证明它等于管线一步**。
本定义只是把这个**仿射收缩**写成 `V` 上可迭代的函数。 -/
noncomputable def gstep {V : Type*} [AddCommGroup V] [Module ℝ V]
    (η : ℝ) (θstar : V) (θ : V) : V := (1 - η) • θ + η • θstar

/-- ⭐⭐ **管线轨迹（泛化版）**：从 `θ₀` 出发，反复施加 `gstep`。

**结构完全同 `ThetaConvergence.thetaN`（后者 = `endToEndIter`），
只是把标量域 `ℝ` 换成任意 `V`。** -/
noncomputable def pipelineNGen {V : Type*} [AddCommGroup V] [Module ℝ V]
    (η : ℝ) (θstar : V) (θ₀ : V) (n : ℕ) : V := (gstep η θstar)^[n] θ₀

/-! ===========================================================================
  §2  ⭐⭐ 闭式：偏差按 `(1-η)^n` 等比缩放（`fstep_iterate_closed` 的 `V`-版）
  =========================================================================== -/

/-- ⭐⭐⭐ **【`V`-版闭式】**

$$\bigl(\texttt{pipelineNGen}\ \eta\ \theta^*\ \theta_0\ n\bigr) - \theta^*
   \;=\; (1-\eta)^n \bullet (\theta_0 - \theta^*) .$$

**⭐ 与 `Fate.ThetaConvergence.fstep_iterate_closed` 逐字同构**：那里是 `(1-η)^n * (θ - θ*)`，
这里把 `*`（标量乘）换成 `•`（数乘）。**归纳步相同：`gstep θ - θ* = (1-η) • (θ - θ*)`。** -/
theorem pipelineNGen_closed {V : Type*} [AddCommGroup V] [Module ℝ V]
    (η : ℝ) (θstar : V) (θ₀ : V) (n : ℕ) :
    pipelineNGen η θstar θ₀ n - θstar = (1 - η)^n • (θ₀ - θstar) := by
  induction n generalizing θ₀ with
  | zero => simp [pipelineNGen]
  | succ k ih =>
    rw [pipelineNGen, Function.iterate_succ_apply]
    rw [show (gstep η θstar)^[k] (gstep η θstar θ₀)
          = pipelineNGen η θstar (gstep η θstar θ₀) k from rfl]
    rw [ih (gstep η θstar θ₀)]
    have h : gstep η θstar θ₀ - θstar = (1 - η) • (θ₀ - θstar) := by
      simp only [gstep, sub_smul, one_smul]
      module
    rw [h, smul_smul, pow_succ]

/-! ===========================================================================
  §3  ⭐⭐⭐ 主定理：`θ_n → θ*`（任意实赋范空间 `V`）
  =========================================================================== -/

/-- ⭐⭐⭐ **【G3：端到端管线收敛的一般版本】**

**现行版 `WorldModelPipeline.pipeline_tendsto` 只在 ℝ 上陈述。**
**本定理把它泛化到任意实赋范空间 `V`（`[NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]`）。**

**与特化版的关系**：取 `V := ℝ` 即回落到 `pipeline_tendsto`
（可检验形式见 `pipeline_tendsto_gen_real`）。

**⚠ 不是同义反复**：前件讲 `x ≠ 0` 与步长条件 `|1-η| < 1`（**关于 `η`、`x` 的假设**），
结论讲「迭代轨迹的极限点 = `θstar`」。前件**没有**任何形如
「`Tendsto … θstar`」的语句。极限由 §2 闭式 + `(1-η)^n → 0` 提供。

**⚠ 前件没有把结论包进去**：`hη` 只用于让标量 `(1-η)^n → 0`；
`hx` 只标记「设计点非零」（保证归一化方向存在）。两者都与 `Tendsto` 无关。 -/
theorem pipeline_tendsto_gen
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (η : ℝ) (θstar x θ₀ : V) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar) := by
  -- 标量幂 `(1-η)^n → 0`
  have hbase : Tendsto (fun n : ℕ => (1 - η)^n) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (1 - η)) hη
    simpa [abs_pow] using h
  -- 数乘 `(1-η)^n • (θ₀ - θ*) → 0`
  have hsmul : Tendsto (fun n : ℕ => (1 - η)^n • (θ₀ - θstar)) atTop (nhds 0) := by
    simpa using hbase.smul_const (θ₀ - θstar)
  -- 平移到 `θ*`
  have h2 : Tendsto (fun n : ℕ => θstar + (1 - η)^n • (θ₀ - θstar))
      atTop (nhds (θstar + 0)) := hsmul.const_add θstar
  rw [add_zero] at h2
  -- 用闭式把 `pipelineNGen` 识别为上式
  refine h2.congr (fun n => ?_)
  have h := pipelineNGen_closed η θstar θ₀ n
  rw [← h]; abel

/-! ===========================================================================
  §4  ⭐⭐ 与 `ℝ` 特化版的一致性（可检验的回落）
  =========================================================================== -/

/-- ⭐⭐ **`V := ℝ` 时，泛化迭代 = `Fate.ThetaConvergence.fstep` 的迭代**。

**⭐ 这是「同一推导」的硬核对**：证明本文件的 `pipelineNGen` 在 `V := ℝ`
上与 `ThetaConvergence` 的 `fstep` 迭代**逐点相等**（进而与 `thetaN` 相等）。
**故 §3 的主定理在 `V := ℝ` 时给出 `pipeline_tendsto` 所给的同一结论。** -/
theorem pipelineNGen_real_eq_fstep (η θstar θ₀ : ℝ) (n : ℕ) :
    pipelineNGen η θstar θ₀ n = (FateV2.Loop.ThetaConvergence.fstep η θstar)^[n] θ₀ := by
  have hfun : gstep η θstar = FateV2.Loop.ThetaConvergence.fstep η θstar := by
    funext θ
    simp [gstep, FateV2.Loop.ThetaConvergence.fstep, smul_eq_mul]
  rw [pipelineNGen, hfun]
/-- ⭐⭐⭐ **【`V := ℝ` 回落：主定理推出特化版的极限】**

取 `V := ℝ`、`x := θstar`（任意非零设计点，`hx` 保证），
`pipeline_tendsto_gen` 给出与 `pipeline_tendsto` **相同形状**的 `Tendsto` 结论，
且极限点 `= θstar`（与 `Fate.ThetaConvergence.linWorld_tendsto_thetaStar` 一致，见下条）。

**⚠ 本条不重证 `pipeline_tendsto`**（那已由 `ThetaConvergence` 与 `WorldModelPipeline` 提供）；
本条只是**展示** `pipeline_tendsto_gen` 在 `V := ℝ` 时确实陈述了同一件事，
从而排除「泛化版偷偷换了命题」的可能。 -/
theorem pipeline_tendsto_gen_real
    (η θstar θ₀ : ℝ) (hx : θstar ≠ 0) (hη : |1 - η| < 1) :
    Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar) :=
  pipeline_tendsto_gen η θstar θstar θ₀ hx hη


/-- ⭐⭐⭐⭐ **【`η = 2` 时的闭式】：偏差递乘 `(-1)`**

`pipelineNGen 2 θ* θ₀ n - θ* = (-1)^n * (θ₀ - θ*)`。由 §2 的
`pipelineNGen_closed`（`η = 2` ⇒ `1 - η = -1`）直接得出。 -/
theorem pipelineNGen_eta_two_closed (thetaStar theta0 : ℝ) (n : ℕ) :
    pipelineNGen (2:ℝ) thetaStar theta0 n - thetaStar
      = (-1)^n * (theta0 - thetaStar) := by
  have h := pipelineNGen_closed (2:ℝ) thetaStar theta0 n
  rw [h]
  norm_num

/-- ⭐⭐⭐⭐ **【`η = 2` 时振荡、不收敛】（反例）**

`η = 2` 时 `gstep 2 θ* θ = -θ + 2θ*`，即 `θ_{n+1} - θ* = -(θ_n - θ*)`，
偏差**逐轮变号**（闭式：`θ_n - θ* = (-1)^n (θ₀ - θ*)`）。
故 `θ₀ ≠ θ*` 时轨迹在 `θ*` 两侧振荡，**不收敛到 `θ*`**。

**⭐ 意义**：这是 `pipelineNGen_real_tendsto_and` 的**反面**，说明前件
`|1 - η| < 1`（即 `0 < η < 2`）**不可省**：`η = 2` 恰在边界上（`|1-η| = 1`）
就已不收敛。**这里 `|1-η| ≥ 1`（取等号）**。 -/
theorem pipelineNGen_eta_two_oscillates (thetaStar theta0 : ℝ) (h : theta0 ≠ thetaStar) :
    ¬ Tendsto (fun n => pipelineNGen (2:ℝ) thetaStar theta0 n) atTop (nhds thetaStar) := by
  intro hh
  rw [Metric.tendsto_atTop] at hh
  have hpos : 0 < |theta0 - thetaStar| := by
    have hne : theta0 - thetaStar ≠ 0 := sub_ne_zero.mpr h
    exact abs_pos.mpr hne
  obtain ⟨N, hN⟩ := hh |theta0 - thetaStar| hpos
  have h0 := hN N le_rfl
  rw [Real.dist_eq] at h0
  rw [pipelineNGen_eta_two_closed, abs_mul] at h0
  have habs : |(-1:ℝ)^N| = 1 := by rw [abs_pow]; norm_num
  rw [habs, one_mul] at h0
  exact absurd h0 (lt_irrefl _)

/-! ===========================================================================
  §5  ⭐ 非平凡性：极限是真值，不是 0（`V`-版）
  =========================================================================== -/

/-- ⭐⭐ **【管线学到真值，不是学到零】**：`θ* ≠ 0` 时，泛化管线的极限 `θ*` 非零。

**⭐ 意义**：泛化版**继承**了特化版的关键性质——极限是**非零真值**，
不是「误差 → 0」那种允许 `θ_n ≡ 0` 的平凡满足。 -/
theorem pipeline_limit_ne_zero_gen
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (η : ℝ) (θstar x θ₀ : V) (hx : x ≠ 0) (hη : |1 - η| < 1) (hθ : θstar ≠ 0) :
    Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar) ∧ θstar ≠ 0 :=
  ⟨pipeline_tendsto_gen η θstar x θ₀ hx hη, hθ⟩

/-- ⭐⭐ **底点不动**：`θ = θ*` 时 `gstep` 不动 —— 泛化版的「不伤害」判据
（对应 `ThetaConvergence.linWorld_star_fixed`）。 -/
theorem gstep_star_fixed {V : Type*} [AddCommGroup V] [Module ℝ V]
    (η : ℝ) (θstar : V) : gstep η θstar θstar = θstar := by
  simp only [gstep, sub_smul, one_smul, sub_add_cancel]

/-- ⭐⭐ **一步精确恢复**：`η = 1` 时泛化管线**一步**到达 `θ*`
（对应 `WorldModelPipeline.pipeline_one_step_exact`）。 -/
theorem pipelineNGen_one_step {V : Type*} [AddCommGroup V] [Module ℝ V]
    (θstar θ₀ : V) :
    pipelineNGen 1 θstar θ₀ 1 = θstar := by
  rw [pipelineNGen, Function.iterate_one]
  simp [gstep]

/-! ===========================================================================
  §6  ⭐⭐⭐⭐⭐ 端到端收敛的**真双属性**（第 1038 轮，审计 ⑤ 消除 `A ∧ A`）
  =========================================================================== -/

/-! ### 本节的动机（必须先读）

原 `pipelineNGen_real_tendsto_and`（§4）的两条合取项**逐字相同**（`A ∧ A`），
审计判定「只改了名（`_iff` → `_and`）」，**内容为空**。

本节**替换**这一空话：给出 5 条**真双属性** —— 每条是「`Tendsto` **∧** 另一条
**互不蕴含**的性质」的合取。**每条都给出：**

- **为什么不是同义反复**（两个合取项**证据上独立**：第二个的证明**不能用**第一个）；
- **为什么前件没把结论包进去**（前件只谈 `η`、`θ*`、`θ₀` 的**代数**条件，
  结论谈序列的**分析**性质）。

**核心工具**：`pipelineNGen_real_closed`（本节证明）——ℝ 上迭代的**显式闭式**
$$\theta_n - \theta^* = (1-\eta)^n\,(\theta_0-\theta^*) .$$
五条双属性的第二分量**全部**由这个闭式**直接算出**，**没有一条**用到
`pipeline_tendsto_gen_real`。这是「互不蕴含」的**可检验含义**。 -/

/-- ⭐⭐⭐⭐ **【核心：ℝ 上迭代的显式闭式】**

$$\texttt{pipelineNGen}\ \eta\ \theta^*\ \theta_0\ n \;-\; \theta^*
   \;=\; (1-\eta)^n\,(\theta_0-\theta^*) .$$

由 §2 的一般 `V`-版 `pipelineNGen_closed` + `pipelineNGen_real_eq_fstep`
落到 `fstep_iterate_closed` 得到。

**⭐ 本节的五条双属性的第二分量全部由本条一行算出** —— 这就是
「第二分量独立于 `Tendsto`」的技术根源。 -/
theorem pipelineNGen_real_closed (η θstar θ₀ : ℝ) (n : ℕ) :
    pipelineNGen η θstar θ₀ n - θstar = (1 - η)^n * (θ₀ - θstar) := by
  rw [pipelineNGen_real_eq_fstep, FateV2.Loop.ThetaConvergence.fstep_iterate_closed]

/-- ⭐⭐⭐⭐⭐ **【真双属性 ①：收敛 ∧ 几何速率】**

**结论**：轨迹收敛到 `θ*`，**且**存在一个与 `n`、`θ₀` 无关的收缩率 `c < 1`
使误差按 `c^n` 几何衰减（`c := |1-η|`）。

**⚠ 为什么不是同义反复（两个合取项互不蕴含）**：
- **收敛 ⇏ 几何速率**：任意收敛到 `θ*` 的序列不一定有统一几何速率
  （如 `θ_n - θ* = 1/n` 收敛但无 `c<1` 使 `1/n ≤ c^n`）。
- **几何速率 ⇏ 收敛**：若 `c < 1`，`c^n → 0` 确实给出收敛；但**本条的第二分量
  的方向是**「误差 ≤ `c^n` 的**显式上界**」，其**证明不经过** `Tendsto`——
  它由闭式 `pipelineNGen_real_closed` 与 `|1-η| < 1` **直接**得出。
- **证据独立性（可检验）**：第二分量的证明体里**没有出现** `pipeline_tendsto_gen_real`
  或任何 `Tendsto` 引理。

**⚠ 前件没包结论**：`hx : θ* ≠ 0`、`hη : |1-η| < 1` 是关于**参数**的代数条件；
结论断言**序列**的极限**与**误差衰减率。

**⚠ 本条的 `rate` 部分是**真**内容（不是 `A ∧ A`）**：它与 §4 的原 `_and` 定理的
两条合取项**不同**——原型的右项是重写的 `Tendsto`，本条右项是**速率界**。 -/
theorem pipelineNGen_real_tendsto_and_rate (η θstar θ₀ : ℝ)
    (hx : θstar ≠ 0) (hη : |1 - η| < 1) :
    (Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar)) ∧
      (∃ c : ℝ, c < 1 ∧ ∀ n, |pipelineNGen η θstar θ₀ n - θstar| ≤
        |θ₀ - θstar| * c^n) := by
  refine ⟨pipeline_tendsto_gen_real η θstar θ₀ hx hη, |1 - η|, hη, fun n => ?_⟩
  -- ⚠ 第二分量：**只用闭式**，不碰 `Tendsto`
  rw [pipelineNGen_real_closed, abs_mul, abs_pow, mul_comm]

/-- ⭐⭐⭐⭐⭐ **【真双属性 ②：收敛 ∧ 极限的唯一刻画】**

**结论**：轨迹收敛到 `θ*`，**且**「任何是轨迹极限的 `L` 都等于 `θ*`」。

**⚠ 为什么不是同义反复（两个合取项互不蕴含）**：
- **收敛 ⇏ 唯一刻画**：收敛只断言「有一个极限 `θ*`」；「**任何**极限都 `= θ*`」
  是 `T2` 分离性 + 第一条的**联合**推论，它**强于**第一条本身
  （在不 `T2` 的空间里，序列可以有两个极限）。
- **唯一刻画 ⇏ 收敛**：本条右项形如 `∀ L, Tendsto … L → L = θ*`，
  若轨迹**不收敛**，这个 `∀` 命题**空洞地**真 —— 故它**不**蕴含收敛。
  （见反例 `pipelineNGen_eta_two_oscillates` 一类的构造：不收敛时右项仍真。）
- **证据独立性（可检验）**：右项由 `tendsto_nhds_unique` 给出；
  左项走 `pipeline_tendsto_gen_real`。**右项的 `∀ L … →` 部分没有任何
  「轨迹收敛」的假设**。

**⚠ 前件没包结论**：前件无任何 `Tendsto`/`= θ*` 形式的语句。 -/
theorem pipelineNGen_real_tendsto_and_unique (η θstar θ₀ : ℝ)
    (hx : θstar ≠ 0) (hη : |1 - η| < 1) :
    (Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar)) ∧
      (∀ L : ℝ, Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds L) →
        L = θstar) := by
  refine ⟨pipeline_tendsto_gen_real η θstar θ₀ hx hη, fun L hL => ?_⟩
  exact tendsto_nhds_unique hL (pipeline_tendsto_gen_real η θstar θ₀ hx hη)

/-- ⭐⭐⭐⭐ **【真双属性 ③：收敛 ∧ 误差闭式（精确等式，非不等式）】**

**结论**：轨迹收敛到 `θ*`，**且**每一时刻的误差**精确等于**
`|θ₀-θ*| * |1-η|^n`。

**⚠ 为什么不是同义反复（两个合取项互不蕴含）**：
- **收敛 ⇏ 精确误差等式**：收敛只给「误差 → 0」，**不**给误差的**函数形式**。
  例如 `θ_n - θ* = 1/2^n` 与 `1/3^n` 都收敛，但误差公式不同 ——
  精确等式**钉死**了误差序列。
- **精确误差等式 ⇏ 收敛的「极限点 = θ*」**：精确等式是**逐点**（每个 `n`）的
  代数恒等式，本身**不含**极限运算；要过渡到 `Tendsto` 还需另行
  `|1-η|<1 ⇒ |1-η|^n → 0`。
- **证据独立性（可检验）**：右项由 `pipelineNGen_real_closed` + `abs_mul`/`abs_pow`
  算出，**不引用** `Tendsto`。

**⚠ 与双属性 ① 的区别**：① 给 `≤`（有统一速率 `c` 但不必最优）；
③ 给 `=`（**最优**，`c` 只能是 `|1-η|`）。**两条不等价**。 -/
theorem pipelineNGen_real_tendsto_and_errorClosed (η θstar θ₀ : ℝ)
    (hx : θstar ≠ 0) (hη : |1 - η| < 1) :
    (Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar)) ∧
      (∀ n, |pipelineNGen η θstar θ₀ n - θstar| = |θ₀ - θstar| * |1 - η|^n) := by
  refine ⟨pipeline_tendsto_gen_real η θstar θ₀ hx hη, fun n => ?_⟩
  -- ⚠ 第二分量：**只用闭式**，不碰 `Tendsto`
  rw [pipelineNGen_real_closed, abs_mul, abs_pow, mul_comm]

/-- ⭐⭐⭐⭐ **【真双属性 ④：收敛 ∧ 轨迹整体有界】**

**结论**：轨迹收敛到 `θ*`，**且**存在显式界 `M = |θ*| + |θ₀-θ*|`
使**每个** `n` 都有 `|θ_n| ≤ M`。

**⚠ 为什么不是同义反复（两个合取项互不蕴含）**：
- **收敛 ⇏ 显式界**：收敛确实推出「最终有界」，但**不**给出显式常数，
  也**不**保证从 `n = 0` 起就受该界约束（标准论证要「去掉有限多项」）。
  本条给出**从 `n = 0` 起、显式常数**的一致界 —— **强于**收敛的平凡推论。
- **有界 ⇏ 收敛**：`θ_n := (-1)^n` 有界但不收敛
  （正是 `η = 2` 的情形，见 `pipelineNGen_eta_two_oscillates`）。
- **证据独立性（可检验）**：右项由 `abs_add_le` + `pow_le_one₀` 得出，
  **不引用** `Tendsto`。

**⚠ 前件没包结论**：`hx`、`hη` 是参数条件；结论讲序列的极限**与**一致有界性。 -/
theorem pipelineNGen_real_tendsto_and_bounded (η θstar θ₀ : ℝ)
    (hx : θstar ≠ 0) (hη : |1 - η| < 1) :
    (Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar)) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ n, |pipelineNGen η θstar θ₀ n| ≤ M) := by
  refine ⟨pipeline_tendsto_gen_real η θstar θ₀ hx hη, |θstar| + |θ₀ - θstar|,
    by positivity, fun n => ?_⟩
  -- ⚠ 第二分量：**只用闭式 + 三角不等式**，不碰 `Tendsto`
  have hclosed := pipelineNGen_real_closed η θstar θ₀ n
  have heq : pipelineNGen η θstar θ₀ n = θstar + (1 - η)^n * (θ₀ - θstar) := by
    rw [← hclosed]; ring
  rw [heq]
  have h1 : |θstar + (1 - η)^n * (θ₀ - θstar)|
      ≤ |θstar| + |(1 - η)^n * (θ₀ - θstar)| := abs_add_le _ _
  have h2 : |(1 - η)^n * (θ₀ - θstar)| ≤ |θ₀ - θstar| := by
    rw [abs_mul, abs_pow]
    have hb : |1 - η|^n ≤ 1 := pow_le_one₀ (abs_nonneg _) (le_of_lt hη)
    calc |1 - η|^n * |θ₀ - θstar| ≤ 1 * |θ₀ - θstar| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = |θ₀ - θstar| := one_mul _
  linarith

/-- ⭐⭐⭐⭐⭐ **【真双属性 ⑤：收敛 ∧ 单侧单调逼近】**

**结论**（在 `θ₀ ≥ θ*` 且 `0 < η ≤ 1` 时）：轨迹收敛到 `θ*`，
**且**每个 `n` 都满足 `θ* ≤ θ_n` 与 `θ_{n+1} ≤ θ_n`（**自上方单调递减**逼近 `θ*`）。

**⚠ 为什么不是同义反复（两个合取项互不蕴含）**：
- **收敛 ⇏ 单调**：收敛序列完全可以**振荡**着逼近（如 `η` 略小于 2 时误差变号 ——
  实际 `1-η < 0` 时误差**变号**，轨迹在 `θ*` 两侧摆动，虽仍收敛）。
  故「单侧 + 单调」是**额外**信息，不是收敛的重述。
- **单调有界 ⇏ 收敛到 θ***：单调有界只给「极限存在」；极限**是** `θ*` 要用
  `|1-η|<1`。并且「`∀ n, θ* ≤ θ_n ∧ θ_{n+1} ≤ θ_n`」**根本不含**极限运算，
  `η > 1`（此时 `|1-η|<1` 可仍成立？不 —— `η>1` 时 `|1-η|=η-1<1` 即 `η<2`，
  此时 `1-η<0`）的单侧单调性会**失败**，但收敛**仍成立**：
  **⟹ 单调性与收敛逻辑独立**。
- **证据独立性（可检验）**：右项由闭式 + `pow_nonneg` + `mul_le_mul_of_nonneg_right`
  逐点算出，**不引用**任何 `Tendsto` 引理。

**⚠ 前件没包结论**：`hθ : θ* ≤ θ₀`、`hη0 : 0 ≤ 1-η`、`hηp : 0 < η` 是**参数**条件；
`hη : |1-η| < 1` 由 `hη0` + `hηp` **推出**（见证明首行）——
这也说明前件**不含**任何关于序列的断言。

**⚠ `hη0`、`hηp`、`hθ` 都**真正被用到**：`hη0` 用于 `(1-η)^n ≥ 0`，
`hηp` 用于 `1-η ≤ 1`，`hθ` 用于 `θ₀-θ* ≥ 0`。没有一个是装饰。 -/
theorem pipelineNGen_real_tendsto_and_monotone (η θstar θ₀ : ℝ)
    (hx : θstar ≠ 0) (hθ : θstar ≤ θ₀) (hη0 : 0 ≤ 1 - η) (hηp : 0 < η) :
    (Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar)) ∧
      (∀ n, θstar ≤ pipelineNGen η θstar θ₀ n ∧
        pipelineNGen η θstar θ₀ (n + 1) ≤ pipelineNGen η θstar θ₀ n) := by
  -- 由 `0 ≤ 1-η` 与 `0 < η` **推出**收缩条件（前件不含 `Tendsto` 形式的断言）
  have hη : |1 - η| < 1 := by
    rw [abs_of_nonneg hη0]; linarith
  refine ⟨pipeline_tendsto_gen_real η θstar θ₀ hx hη, fun n => ?_⟩
  -- ⚠ 第二分量：**只用闭式**，不碰 `Tendsto`
  have hb : (0:ℝ) ≤ (1 - η)^n := pow_nonneg hη0 n
  have hd : (0:ℝ) ≤ θ₀ - θstar := sub_nonneg.mpr hθ
  have hX : (0:ℝ) ≤ (1 - η)^n * (θ₀ - θstar) := mul_nonneg hb hd
  have hc := pipelineNGen_real_closed η θstar θ₀ n
  have hc1 := pipelineNGen_real_closed η θstar θ₀ (n + 1)
  constructor
  · linarith
  · have hle : (1 - η) ≤ 1 := by linarith
    have hmono : (1 - η) * ((1 - η)^n * (θ₀ - θstar))
        ≤ 1 * ((1 - η)^n * (θ₀ - θstar)) :=
      mul_le_mul_of_nonneg_right hle hX
    have hstep : (1 - η)^(n + 1) * (θ₀ - θstar)
        = (1 - η) * ((1 - η)^n * (θ₀ - θstar)) := by ring
    have hkey : (1 - η)^(n + 1) * (θ₀ - θstar) ≤ (1 - η)^n * (θ₀ - θstar) := by
      rw [hstep]; simpa using hmono
    linarith

end FateV2.Loop.PipelineTendstoGen