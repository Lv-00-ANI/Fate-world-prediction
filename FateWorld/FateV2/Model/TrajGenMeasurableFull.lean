/-
命运理论 · 开放问题 1.2 的剩余缺口：`θ` 与 `x₀` 也作为变量时的可测性
=====================================================================

模块：FateV2.Model.TrajGenMeasurableFull
上游：`FateV2.Model.TrajGenMeasurable`（`trajGen_measurable_at`、`trajGen_measurable`）、
　　　`FateV2.Model.TrajGenDeterministic`（`trajGen`、`trajGen_zero`、`trajGen_succ`）、
　　　`Fate.Frame`（`Frame`、`Step`）。

---------------------------------------------------------------------------
(a) 净版开放问题 1.2 原文（`10-命运理论-净版.md:158`）
---------------------------------------------------------------------------
> **[开放问题] 开放问题 1.2（`F_traj` 的定义域与值域）**
> `F_traj` 的定义域含序列 `{u_t}`、`{ε_t}`、`{a_t}`，其值域是轨迹空间。
> **该定义域上的 σ-代数、值域上的可测结构、以及 `F_traj` 的可测性，本章均未给出。**

`Fate/TrajGenMeasurable.lean:72-75` 的缺口自述（原文）：

> 「**没有**处理 `θ`、`x₀` 也作为**变量**时的可测性（本文件中它们固定为常数；
> 若要把它们也纳入定义域，需再加两条 `MeasurableSpace` 前件，
> 且 `trajGen` 关于 `θ` 的可测性**不能**由本文件的方法直接得到 ——
> `Nat.rec` 每一步都把 `θ` 原样传入，但**归纳假设须含 `θ`**，本文件未做）。」

---------------------------------------------------------------------------
(b) 本文件做到了什么
---------------------------------------------------------------------------
**一条定理**，`trajGen_measurable_full`：把 `trajGen` 的**全部五个变量**
（`u`、`ε`、`a`、`θ`、`x₀`）都作为 `w` 的分量，证明

        w ↦ trajGen F f w.2.2.2.1 w.2.2.2.2 (fun _ => w.1) (fun _ => w.2.1) (fun _ => w.2.2.1) n

关于乘积空间
`F.U.Carrier × F.Ν.Carrier × F.Act.Carrier × F.Θ.Carrier × F.X.Carrier`
（每个因子各配一个 `MeasurableSpace` 实例，再取 `Prod` 乘积可测结构）**可测**。

**技术要点（正是 `TrajGenMeasurable:72-75` 指出的缺口）**：
归纳假设**含 `θ` 与 `x₀`** —— 即对 `n` 作归纳时，被证命题是
「对**所有** `θ`、`x₀` 的联合可测」，而不是固定它们的某一个取值。
`succ` 情形因此可以直接用归纳假设 `ih`（它已对任意 `θ`、`x₀` 成立）
来组合 `f` 的第五个参数 `θ = w.2.2.2.1`，无需再对 `θ` 单独做参数化论证。

与已入链模块的**区别**：
  * `TrajGenMeasurable.trajGen_measurable_at`：`θ`、`x₀` 为**固定常数**，`w` 只含三个序列；
  * `TrajGenMeasurable.trajGen_measurable`：同上，取整条轨迹；
  * **本文件**：`θ`、`x₀` 是**单步取值**（不是序列），也是 `w` 的分量。
    而 `u`、`ε`、`a` 在 `trajGen` 的签名里必须是**序列**，故此处把
    `w` 的单步取值提升为**常序列** `fun _ => w.1` 等；结论是「第 `n` 步状态」
    关于五个**单步取值** `(u_n, ε_n, a_n, θ, x₀)` 联合可测 ——
    这相对于 `trajGen_measurable_at` 新增了 `θ`、`x₀` 两个变维度。

---------------------------------------------------------------------------
(c) 本文件**没有**做到什么（诚实标注）
---------------------------------------------------------------------------
  1. **没有**证明「定义域上的 σ-代数」的**唯一性 / 正确性**：本文件与
     `TrajGenMeasurable` 一样，**选定**乘积可测结构作为定义域 σ-代数。
     净版开放问题 1.2 问的是「该取什么」，本文件**回答是「取这个能证」**，
     **不是**论证它是对的那个。
  2. **没有**把 `Frame` 的 `meas` 字段提升为 instance（那需改已入链的
     `Fate.Basic`）；5 条 `MeasurableSpace` 前件仍是**显式变量**。
  3. **没有**证明前件 `H_f`（`f` 在 5 元乘积上联合可测）可由任何 `Frame`
     的内生数据推出 —— `Step F` 是任意函数，可测性必须作为假设。
  4. **没有**处理 `u`、`ε`、`a` 作为**序列**（`ℕ → ·`）时的联合情形 ——
     本文件里它们是**单步取值**（提升为常序列，配合 `n` 固定）。序列版见
     `TrajGenMeasurable.trajGen_measurable`（但那里 `θ`、`x₀` 是常数）。
     「三个序列 + `θ` + `x₀` 全部为变量」的**组合**，本文件**没有**做。
  5. **没有**声称「开放问题 1.2 已解决」。

---------------------------------------------------------------------------
(d) 准确的声称
---------------------------------------------------------------------------
本文件只声称：

> **在「5 个载体各带可测结构」且「单步机制 `f` 联合可测」的假设下，
> `trajGen` 的第 `n` 步取值关于 `(u_n, ε_n, a_n, θ, x₀)` 五元组
> （配乘积可测结构）联合可测。**

**不**声称「开放问题 1.2 已解决」。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 全程无占位证明（不用 `sorry` / `admit` / `axiom`）；本文件不修改任何已存在模块。
- 警示性块注释用普通块注释写法（斜杠加星号），不用 doc 注释前缀。
-/

import FateWorld.FateV2.Model.TrajGenMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace FateV2.Model.TrajGenMeasurableFull

open MeasureTheory

/-!
  # Model · TrajGenMeasurableFull

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TrajGenMeasurableFull.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TrajGenMeasurable
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  定义域对象
    =========================================================================== -/

/-- **完备定义域**：单步输入 `u_n`、噪声 `ε_n`、动作 `a_n`，
连同参数 `θ` 与初值 `x₀`，共 5 个因子。

（与 `FateV2.Model.TrajGenMeasurable.InputSeq` 不同：那里 `u`、`ε`、`a` 是**序列**，
`θ`、`x₀` 固定；这里 5 个都是**单步取值**，全部可变。） -/
abbrev FullInput (F : Frame) : Type _ :=
  F.U.Carrier × F.Ν.Carrier × F.Act.Carrier × F.Θ.Carrier × F.X.Carrier

section Full

variable (F : Frame)

/- 显式前件 `H_space`：5 个载体上的可测结构（**不**改 `Frame`，只作变量）。 -/
variable [MeasurableSpace F.X.Carrier]
variable [MeasurableSpace F.U.Carrier]
variable [MeasurableSpace F.Ν.Carrier]
variable [MeasurableSpace F.Θ.Carrier]
variable [MeasurableSpace F.Act.Carrier]

variable {f : Step F}

/-! ===========================================================================
    §1  主定理：关于全部 5 个变量联合可测
    =========================================================================== -/

/-- ⭐⭐ **【开放问题 1.2 的剩余部分】**：`trajGen` 关于
`(u, ε, a, θ, x₀)` **全部五个**变量都可测。

**与 `TrajGenMeasurable.trajGen_measurable_at` 的区别**：
那里 `θ`、`x₀` 是固定常数；**这里它们也是 `w` 的分量**。

**关于 `u` / `ε` / `a` 的形态**：`trajGen` 的这三个参数在
`FateV2.Model.TrajGenDeterministic` 里是**序列**（`ℕ → ·`）。本文件取
`w` 的单步取值提升为**常序列**（`fun _ => w.1` 等），故结论是
「第 `n` 步状态」关于 `(u_n, ε_n, a_n, θ, x₀)` 五个**单步取值**可测。
（序列 + `θ` + `x₀` 全变量的组合本文件未做，见文件头 (c.4)。）

**证明结构**：对 `n` 归纳，**归纳假设含 `θ` 与 `x₀`**（即 `ih` 对
任意 `θ`、`x₀` 成立，产物是 `(θ, x₀, ...)` 的联合可测性）。
  * `n = 0`：由 `trajGen_zero`，目标是 `w ↦ w.2.2.2.2` 可测
    （`x₀` 是 `w` 的第 5 个分量），由投影可测性直接得（`fun_prop`）；
  * `n = k+1`：由 `trajGen_succ`，目标是
    `f (trajGen ... k) w.1 w.2.1 w.2.2.2.1 w.2.2.1`
    （`f` 的实参顺序是 `x u ε θ a`，而 `w` 的因子顺序是 `u ε a θ x`）。
    用 `hf.comp` 归约为五元组的联合可测性：
    第 1 分量用 `ih`（**此处 `θ`、`x₀` 仍作变量传入**，正是本文件的关键），
    第 2–5 分量分别是 `w.1`（`u`）、`w.2.1`（`ε`）、
    `w.2.2.2.1`（`θ`）、`w.2.2.1`（`a`）的投影。

**不**声称「开放问题 1.2 已解决」；见文件头 (c)(d)。 -/
theorem trajGen_measurable_full
    (hf : Measurable (fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (n : ℕ) :
    Measurable (fun w : FullInput F =>
      TrajGenDeterministic.trajGen F f w.2.2.2.1 w.2.2.2.2
        (fun _ => w.1) (fun _ => w.2.1) (fun _ => w.2.2.1) n) := by
  induction n with
  | zero =>
    simp only [TrajGenDeterministic.trajGen_zero]
    fun_prop
  | succ k ih =>
    simp only [TrajGenDeterministic.trajGen_succ]
    change Measurable ((fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
      fun (w : FullInput F) =>
        (TrajGenDeterministic.trajGen F f w.2.2.2.1 w.2.2.2.2
           (fun _ => w.1) (fun _ => w.2.1) (fun _ => w.2.2.1) k,
         w.1, w.2.1, w.2.2.2.1, w.2.2.1))
    refine hf.comp ?_
    have hu : Measurable (fun w : FullInput F => w.1) := measurable_fst
    have he : Measurable (fun w : FullInput F => w.2.1) :=
      measurable_fst.comp measurable_snd
    have ha : Measurable (fun w : FullInput F => w.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hθ : Measurable (fun w : FullInput F => w.2.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    exact ih.prodMk (hu.prodMk (he.prodMk (hθ.prodMk ha)))

/-! ===========================================================================
    §2  前件 `H_f` 非空性的见证（防止空真）
    =========================================================================== -/

/-- **见证**：常机制满足 `H_f`，故主定理的前件**可被满足**，非空真。 -/
theorem const_jointMeasurable (c : F.X.Carrier) :
    Measurable (fun p : F.X.Carrier × F.U.Carrier × F.Ν.Carrier
        × F.Θ.Carrier × F.Act.Carrier =>
      (fun (_x : F.X.Carrier) (_u : F.U.Carrier) (_e : F.Ν.Carrier)
        (_θ : F.Θ.Carrier) (_a : F.Act.Carrier) => c)
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  measurable_const

end Full

end FateV2.Model.TrajGenMeasurableFull
