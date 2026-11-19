/-
命运理论 · 开放问题 1.2：`F_traj`（`trajGen`）的可测性 —— 条件性结果
=====================================================================

模块：FateV2.Model.TrajGenMeasurable
上游：`FateV2.Model.TrajGenDeterministic`（`trajGen`、`trajGen_zero`、`trajGen_succ`）、
　　　`Fate.Frame`（`Frame`、`Step`）、`Fate.Basic`（`Traj` 及各 Space 的 `meas` 字段）。

---------------------------------------------------------------------------
(a) 净版开放问题 1.2 原文（`10-命运理论-净版.md:158`）
---------------------------------------------------------------------------
> **[开放问题] 开放问题 1.2（`F_traj` 的定义域与值域）**
> `F_traj` 的定义域含序列 `{u_t}`、`{ε_t}`、`{a_t}`，其值域是轨迹空间。
> **该定义域上的 σ-代数、值域上的可测结构、以及 `F_traj` 的可测性，本章均未给出。**

---------------------------------------------------------------------------
(b) 本文件做到了什么（**条件性**可达）
---------------------------------------------------------------------------
在下列**显式前件**下，本文件证明 `trajGen` 的可测性：

  * `H_space`（实例前件，5 条）：`F.X.Carrier`、`F.U.Carrier`、`F.Ν.Carrier`、
    `F.Act.Carrier`、`F.Θ.Carrier` 上各取定一个 `MeasurableSpace`。
    （`Fate.Basic` 的 `StateSpace` / `InputSpace` / `NoiseSpace` / `ActionSpace` /
      `ThetaSpace` **已经各自带 `meas : MeasurableSpace Carrier` 字段**，
      但 Lean 的 instance 搜索**不会**自动把 `F.X.meas` 当作
      `MeasurableSpace F.X.Carrier` 的实例（实测 `synthInstanceFailed`），
      故本文件把 5 个实例作为 `variable` 前件显式列出、
      **不修改 `Frame` 或任何已入链模块**。可用 `letI := F.X.meas` 等
      在本文件的定理**之外**把它们实例化。）

  * `H_f`（机制前件，1 条）：单步机制 `f : Step F` 关于
      `F.X.Carrier × F.U.Carrier × F.Ν.Carrier × F.Θ.Carrier × F.Act.Carrier`
      （乘积可测空间）到 `F.X.Carrier` **联合可测**。

已证的**两条定理**：

  1. **`trajGen_measurable_at`（逐点 / 弱版，对应任务阶段 2 的「(甲)」）**
     对每个 `n : ℕ`，
     `w ↦ trajGen F f θ x₀ w.1 w.2.1 w.2.2 n` 关于
     `(ℕ → F.U.Carrier) × (ℕ → F.Ν.Carrier) × (ℕ → F.Act.Carrier)`
     （三个序列空间各配 Pi 可测结构，再取乘积）**可测**。
     证明：对 `n` 归纳 —— `n = 0` 时取值恒为 `x₀`（`measurable_const`）；
     `n = k+1` 时由 `trajGen_succ` 得
     `f (traj_k) (u k) (ε k) θ (a k)`，用 `H_f.comp` 与
     `u ↦ u k`、`ε ↦ ε k`、`a ↦ a k` 的 `measurable_pi_apply` 组装。

  2. **`trajGen_measurable`（整条轨迹，对应任务阶段 2 的「(乙)」）**
     `w ↦ trajGen F f θ x₀ w.1 w.2.1 w.2.2` 作为
     `(ℕ → F.U.Carrier) × (ℕ → F.Ν.Carrier) × (ℕ → F.Act.Carrier)`
     → `Traj ℕ F.X`（`= ℕ → F.X.Carrier`，配 Pi 可测空间）**可测**。
     证明：`rw [measurable_pi_iff]` 后逐 `n` 用定理 1。
     **本文件把「`Traj` 上的 σ-代数」取为 `ℕ → F.X.Carrier` 上的 Pi 可测空间**
     —— 这是一条**显式的建模选择**，不是从净版推导出来的。

另附**非空性见证**两条（`const_jointMeasurable`、`fst_jointMeasurable`），
说明前件 `H_f` **可被满足**（`f` 为常函数、或 `f` 只依赖 `x`），
故上述两定理**不是空真**。

---------------------------------------------------------------------------
(c) 本文件**没有**做到什么（诚实标注）
---------------------------------------------------------------------------
  1. **没有**把 `Frame` 的 `meas` 字段变成 instance —— 那**需要改已入链的
     `Fate.Basic`**，本文件不做。故 5 条 `MeasurableSpace` 前件是**显式变量**，
     下游用户若想免去它们，必须自己在 `letI` 处补（本文件 §4 已给出
     `letI` 可用性的说明，但**不提供** `instance` 声明，以免污染全局实例）。
  2. **没有**证明 `H_f` 可由任何 `Frame` 的内生数据推出 —— `Step F` 是
     **任意函数**，可测性**不由 `Frame` 保证**，必须作为假设。
  3. **没有**解决「定义域上的 σ-代数」的**唯一性 / 正确性**问题：本文件只是
     **选定**了三个序列空间的**乘积 Pi 可测结构**作为定义域 σ-代数。
     净版开放问题 1.2 问的是「该取什么」，本文件**回答是「取这个能证」**，
     而**不是**论证它是对的那个。
  4. **没有**处理 `θ`、`x₀` 也作为**变量**时的可测性（本文件中它们固定为常数；
     若要把它们也纳入定义域，需再加两条 `MeasurableSpace` 前件，
     且 `trajGen` 关于 `θ` 的可测性**不能**由本文件的方法直接得到 ——
     `Nat.rec` 每一步都把 `θ` 原样传入，但**归纳假设须含 `θ`**，本文件未做）。
  5. **没有**声称「开放问题 1.2 已解决」。

---------------------------------------------------------------------------
(d) 准确的声称
---------------------------------------------------------------------------
本文件只声称：

> **在「5 个载体各带可测结构」且「单步机制 `f` 联合可测」的假设下，
> `trajGen` 关于三个输入序列 `{u_t}`、`{ε_t}`、`{a_t}`（配乘积 Pi 可测结构）
> 逐点可测，且整条轨迹可测。**

**不**声称「开放问题 1.2 已解决」。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 全程零 `sorry` / 零 `admit` / 零 `axiom`；本文件不修改任何已存在模块。
- `universe u`；`Traj` 用 `Fate.Basic` 的定义（本文件不改）。
- 警示性块注释用普通块注释写法，不用 doc 注释（三斜杠）前缀。
-/

import FateWorld.FateV2.Model.TrajGenDeterministic
import Mathlib.MeasureTheory.Constructions.Pi

namespace FateV2.Model.TrajGenMeasurable

open MeasureTheory

/-!
  # Model · TrajGenMeasurable

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TrajGenMeasurable.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TrajGenDeterministic
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  记号与显式前件
    =========================================================================== -/

/-- **定义域**：三个输入序列的乘积空间（本文件选定的定义域对象）。 -/
abbrev InputSeq (F : Frame) : Type _ :=
  (ℕ → F.U.Carrier) × (ℕ → F.Ν.Carrier) × (ℕ → F.Act.Carrier)

section Instances

variable (F : Frame)

/- 显式前件 `H_space`：5 个载体上的可测结构（**不**改 `Frame`，只作变量）。 -/
variable [MeasurableSpace F.X.Carrier]
variable [MeasurableSpace F.U.Carrier]
variable [MeasurableSpace F.Ν.Carrier]
variable [MeasurableSpace F.Act.Carrier]
variable [MeasurableSpace F.Θ.Carrier]

variable {f : Step F}

/-! ===========================================================================
    §1  逐点可测（弱版）
    =========================================================================== -/

/-- ⭐ **定理 1（逐点可测）**：每个时间点 `n` 的状态关于三输入序列联合可测。

**前件**：`H_f` —— 单步机制 `f` 在 5 元乘积上**联合可测**。

**结论**：`w ↦ trajGen F f θ x₀ w.1 w.2.1 w.2.2 n` 可测。

**注意**：前件说的是 `f` 的可测性（单步），结论说的是**第 `n` 步状态**的可测性。
`n` 步递推需要 `n` 次复合，`f` 的可测性**不**平凡地给出结论 ——
本定理的实质内容是 `Nat.rec` 的归纳，不是前件的重述。 -/
theorem trajGen_measurable_at
    (hf : Measurable (fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier) (n : ℕ) :
    Measurable (fun w : InputSeq F =>
      TrajGenDeterministic.trajGen F f θ x₀ w.1 w.2.1 w.2.2 n) := by
  induction n with
  | zero =>
    simp only [TrajGenDeterministic.trajGen_zero]
    exact measurable_const
  | succ k ih =>
    simp only [TrajGenDeterministic.trajGen_succ]
    change Measurable ((fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
      fun (w : InputSeq F) =>
        (TrajGenDeterministic.trajGen F f θ x₀ w.1 w.2.1 w.2.2 k,
         w.1 k, w.2.1 k, θ, w.2.2 k))
    refine hf.comp ?_
    have hu : Measurable (fun w : InputSeq F => w.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have he : Measurable (fun w : InputSeq F => w.2.1 k) :=
      (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)
    have ha : Measurable (fun w : InputSeq F => w.2.2 k) :=
      (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
    have h4 : Measurable (fun w : InputSeq F => (w.1 k, w.2.1 k, θ, w.2.2 k)) :=
      hu.prodMk (he.prodMk (measurable_const.prodMk ha))
    exact ih.prodMk h4

/-! ===========================================================================
    §2  整条轨迹可测（强版）
    =========================================================================== -/

/-- ⭐ **定理 2（整条轨迹可测）**：`trajGen` 全体作为
`InputSeq F → Traj ℕ F.X` 可测。

**值域上的可测结构**：本文件**选定** `Traj ℕ F.X = ℕ → F.X.Carrier` 上的
**Pi 可测空间**（`instMeasurableSpaceForall`，由 `Mathlib.MeasureTheory.Constructions.Pi`
提供）。这是一条**建模选择**，本文件不主张它是唯一正确的选择。

**证明**：`measurable_pi_iff` 把目标化为「对每个 `n` 逐点可测」，
即定理 1。 -/
theorem trajGen_measurable
    (hf : Measurable (fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier) :
    Measurable (fun w : InputSeq F =>
      TrajGenDeterministic.trajGen F f θ x₀ w.1 w.2.1 w.2.2) := by
  rw [measurable_pi_iff]
  intro n
  exact trajGen_measurable_at F hf θ x₀ n

/-! ===========================================================================
    §3  非空性见证：前件 `H_f` 确实可被满足
    =========================================================================== -/

/-- **见证 1**：常机制（`f ≡ c`）联合可测 ⟹ `H_f` 非空。 -/
theorem const_jointMeasurable (c : F.X.Carrier) :
    Measurable (fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      (fun (_x : F.X.Carrier) (_u : F.U.Carrier) (_e : F.Ν.Carrier)
        (_θ : F.Θ.Carrier) (_a : F.Act.Carrier) => c)
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  measurable_const

/-- **见证 2**：只依赖 `x` 的机制（`f x _ _ _ _ = x`）联合可测 ⟹ `H_f` 非空，
且这是**非常值**的机制，说明前件不平凡。 -/
theorem fst_jointMeasurable :
    Measurable (fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      (fun (x : F.X.Carrier) (_u : F.U.Carrier) (_e : F.Ν.Carrier)
        (_θ : F.Θ.Carrier) (_a : F.Act.Carrier) => x)
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have h : (fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      (fun (x : F.X.Carrier) (_u : F.U.Carrier) (_e : F.Ν.Carrier)
        (_θ : F.Θ.Carrier) (_a : F.Act.Carrier) => x)
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) = fun p => p.1 := rfl
  rw [h]
  exact measurable_fst

/-! ===========================================================================
    §4  `letI` 使用说明（**不**声明 instance，避免全局实例污染）
    =========================================================================== -/

/- 下游若要免除 5 条 `variable` 前件，可在**自己的文件**里写

      letI := F.X.meas
      letI := F.U.meas
      letI := F.Ν.meas
      letI := F.Act.meas
      letI := F.Θ.meas

   本文件**不**这么做，理由：`Frame` 的 `meas` 字段随 `F` 变化，
   把它们提升为全局 instance 会让实例搜索产生歧义，
   且会改动（尽管是隐式的）已入链模块的实例环境。 -/

end Instances

end FateV2.Model.TrajGenMeasurable
