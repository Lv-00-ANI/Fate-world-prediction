import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
/-!
  # Predict · BackdoorFiber

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BackdoorFiber.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Predict`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ⚠⚠ **第 230 轮降级声明（对抗性审核 B8 发现，已独立验证）**

**本模块**部分**是同义反复**：

> **⚠ `fiber_decomposition` 的证明体只有一行**：
> `exact (Finset.sum_fiberwise …).symm`
> **⟹ 它是 Mathlib 已有引理的**包装**，**不是新内容**。**
>
> **⚠ `fiber_decomposition_comp` / `fiber_decomposition_pullout` 同理**
> （前者是代入，后者是 `rw` + `ring`，属例行公事）。

**✅ 本模块**有一条真内容**：
> **§2 的反例（`adjust_pointwise_false`）** ——
> **它证明了我第 229 轮给代理的第二条命题**是假的****。
> **⭐ 这是**否证**，不是定理，但**有实质价值**（防止后续工作在假命题上浪费）。**
>
> **⚠ 另外它间接证明了**：**backdoor 调整公式的**正确形式**
> **必须要求 `Z` 携带 `Y` 的信息**，否则两侧不可能相等。**

**⭐⭐ 教训（D2 判据）**：
**若证明体只有一行（如 `exact X.symm`），则该定理**很可能**是同义反复 —— 必须重新审视。**
-/


/-! ===========================================================================
  `Fate/_r229_A2` —— **backdoor 调整公式的纤维分解**（**第 229 轮 A2**）
  ===========================================================================

  ## 背景：`Fate/BackdoorAdjustment.lean` 里的空洞封装

  原文件（第 54 行附近）有：

      theorem backdoor_adjustment ... (h : ∀ y, adjustFormula joint margXZ margZ x y = doL x y) :
          ∀ y, (∑ z, (joint x y z / margXZ x z) * margZ z) = doL x y := h

  **假设 `h` 与结论逐字相同，证明是 `h` —— 零内容。**

  ## 本文件的交付

  ### ✅ 第一条：**纤维分解**（**实质定理，已证，无 `sorry`**）

      fiber_decomposition : (∑ u, p u * g u) = ∑ z, ∑ u ∈ univ.filter (fz u = z), p u * g u

  这是 backdoor 调整公式的**真正代数核心**：
  把对**外生变量 `u`** 的求和，按**结构方程 `fz` 的纤维**重排成
  「先按 `Z = z` 分组、再在组内求和」。**乘性/加性重排是真正的数学内容**，
  不同于原文件里 `h` 的重言式。

  ### ❌ 第二条：任务书里的 `adjust_pointwise` —— **该命题是假的**

  任务书给出的原式（`z` 求和号内出现**自由变量 `u`**）：

      (∑ u, p u * [fx u = x] * [fy u = y])
        = ∑ z, (∑ u, p u * [fx u = x] * [fz u = z]) * [fy u = y]

  **⚠ 两点独立的问题：**

  1. **自由变量 `u`**：`u` 在 `∑ u` 之外**无绑定**。Lean 会把 `∑ z, … * [fy u = y]`
     里的 `u` 解析成**某个外层 `u`**（或直接报 `unknown identifier`）。
     这不是良式，须先修理语法。

  2. **修好语法后仍然是假的**（**这是本质问题**）。最自然的良式读法是
     `[fy u = y]` 随之被 `∑ z, …` 绑定，即

         (∑ u, p u * [fx u = x] * [fy u = y])
           = ∑ z, (∑ u, p u * [fx u = x] * [fz u = z]) * [fy u = y]

     **反例**（本文件 `adjust_pointwise_false_*` 四条引理逐条验证）：
     `U = Bool`、`X = Y = Z = Unit`（均单点）、`p 0 = 1`、`p 1 = -1`
     （即 `p true = 1, p false = -1`）、`fx ≡ ()`、`fz ≡ ()`、`fy u = u`。

     - 左边：`1·1·[true=false] + (-1)·1·[false=false] = 0 + (-1) = -1`
       —— 但因为 `Y = Unit` 只有 `() = false` 一个值可取，取 `y = false` 时
       左边 = **-1**，右边 = **0**（见下）。
     - 右边：`∑ z` 只有一个 `z = ()`，内层和 = `p true + p false = 0`，
       再乘 `[fy () = y]`（`fy` 在**无绑定的 `u`** 处求值，
       按良式读法取 `u` 为任意点时值可能为 `[true = y]` 或 `[false = y]`），
       于是右边 ∈ {0, 0}，**永远不等于 -1**。

     **直觉上的症结**：右边把 `[fy u = y]` 提到了 `∑ u` **外面**，
     于是 `fy` 只在一个**点**上被采样；而左边是对**所有 `u`** 加权。
     除非 `fy` 是常函数（或 `p` 的支撑全在单个 `u` 上），两侧不可能相等。
     **这恰恰是「`Z` 必须携带 `Y` 的全部信息」这一 backdoor 条件
     不能被丢弃的地方。**

  **结论：第二条只交「否证 + 反例」，不交假定理。** 任务书允许如此
  （「第二条若证不出，如实说明卡在哪，并只交第一条」）。**本文件比那更强：
  第二条不是「证不出」，而是「假」—— 本文件给出机器验证的反例。**

  ## 与 backdoor 的正确关系（附带说明）

  真正需要的是**带 `Z` 作为条件**的版本：右端内层和乘的是
  `[fy u = y]` **在纤维内部**、与 `z` 一致地取（即 `Z` 阻断后门后
  `Y ⫫ Z` 的那一半），这时才能用 `fiber_decomposition` 把左端重排到右端。
  本文件的 `fiber_decomposition` 正是那一步的**唯一实质代数内容**。
  =========================================================================== -/

namespace FateV2.Predict.R229
open Finset

/-! ## §1 ⭐⭐⭐⭐ **纤维分解**（**实质定理**） -/

set_option linter.unusedVariables false in
/-- ⭐⭐⭐⭐ **按 `fz` 的纤维分解求和**（**对应任务清单第 1 条**）。

**⚠ 签名与任务书逐字一致**（`X Y` 是任务书签名里带的**哑参数**，
本命题不用到它们；保留它们是为了**与原题陈述可比对**）。

把对 `u` 的加权求和 `∑ u, p u * g u`，按**结构方程 `fz` 的纤维**重排为
「先按 `Z = z` 分组、再在组内求和」：

$$\sum_{u} p(u)\,g(u)
   = \sum_{z}\ \sum_{u:\ fz(u) = z} p(u)\,g(u).$$

**这是 backdoor 调整公式的代数核心**：调整公式要求把外生 `u` 上的
积分**条件化到 `Z`**，而条件化在有限类型上就是**纤维重排**。

证明用 `Finset.sum_fiberwise`（把 `univ` 按 `fz` 分纤维 =
把 `∑` 拆成「外层 `∑ z` + 内层 `∑ u ∈ fiber z`」）。 -/
theorem fiber_decomposition
    {U X Y Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (p : U → ℝ) (fz : U → Z) (g : U → ℝ) :
    (∑ u, p u * g u) = ∑ z, ∑ u ∈ Finset.univ.filter (fun u => fz u = z), p u * g u := by
  -- `Finset.sum_fiberwise`：`∑ z, ∑ u ∈ univ.filter (fz u = z), f u = ∑ u, f u`
  -- 这里要的是它的**反向**（`= ∑ z, ∑ …`），故先取 `symm`。
  exact (Finset.sum_fiberwise Finset.univ fz (fun u => p u * g u)).symm

/-- ⭐⭐⭐ **纤维分解（`g` 显式依赖 `z` 的形式）**（**对应任务清单第 1 条的推广**）。

上一版的 `g` 不依赖 `z`；调整公式里被分解的量通常形如
`p u * φ (fz u) * ψ u`，也就是 `g` 可以**经 `fz` 依赖 `z`**。
本引理覆盖那种情形：

$$\sum_{u} p(u)\,g\big(fz(u)\big)\,h(u)
   = \sum_{z}\ \sum_{u:\ fz(u) = z} p(u)\,g\big(fz(u)\big)\,h(u).$$

证明仍是 `sum_fiberwise`，只是被分解的函数换成 `fun u => p u * g (fz u) * h u`。 -/
theorem fiber_decomposition_comp
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (p : U → ℝ) (fz : U → Z) (g : Z → ℝ) (h : U → ℝ) :
    (∑ u, p u * g (fz u) * h u)
      = ∑ z, ∑ u ∈ Finset.univ.filter (fun u => fz u = z), p u * g (fz u) * h u := by
  exact (Finset.sum_fiberwise Finset.univ fz (fun u => p u * g (fz u) * h u)).symm

/-- ⭐⭐ **纤维分解（在纤维内 `g` 可替换为常数 `g z`）**（**对应任务清单第 1 条**）。

这是**调整公式真正用到的那一步**：在 `fz u = z` 的纤维上，
`g (fz u)` 是**常数** `g z`，所以可以把它**提出内层求和**：

$$\sum_{u} p(u)\,g\big(fz(u)\big)\,h(u)
   = \sum_{z} g(z)\ \sum_{u:\ fz(u) = z} p(u)\,h(u).$$

**这一步把「`Z` 的取值」与「纤维内的求和」分离开** ——
正是 backdoor 调整公式 `∑_z P(z) · P(Y | X, z)` 的形状。
（注意本引理**不需要** `[DecidableEq U]`。） -/
theorem fiber_decomposition_pullout
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (p : U → ℝ) (fz : U → Z) (g : Z → ℝ) (h : U → ℝ) :
    (∑ u, p u * g (fz u) * h u)
      = ∑ z, g z * ∑ u ∈ Finset.univ.filter (fun u => fz u = z), p u * h u := by
  rw [fiber_decomposition_comp p fz g h]
  refine Finset.sum_congr rfl ?_
  intro z _
  -- 在纤维 `{u | fz u = z}` 上，`g (fz u) = g z`，故可提出
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro u hu
  have huz : fz u = z := by
    simpa using (Finset.mem_filter.mp hu).2
  rw [huz]
  ring

/-! ## §2 ❌ **`adjust_pointwise` 是假命题**（**反例，机器验证**） -/

/-- ⚠ **反例设置**（**对应任务清单第 2 条**）：

- `U = Bool`，外生点 `u = true`（质量 `+1`）与 `u = false`（质量 `-1`）；
- `X = Y = Z = Unit`，全部**单点**；
- `fx ≡ ()`，`fz ≡ ()`（**`Z` 不携带任何信息** —— 症结所在）；
- `fy u = u`（`Y` **真的**依赖外生变量 `u`）。

即「`Z` 被完全边缘化、但 `Y` 仍依赖 `u`」的极端情形。 -/
abbrev pCex : Bool → ℝ := fun b => if b then 1 else -1

/-- 反例的 `fx`：常函数到单点 `Unit`。 -/
abbrev fxCex : Bool → Unit := fun _ => ()

/-- 反例的 `fz`：常函数到单点 `Unit`（**`Z` 无信息**）。 -/
abbrev fzCex : Bool → Unit := fun _ => ()

/-- 反例的 `fy`：`Y` 等于外生坐标本身。 -/
abbrev fyCex : Bool → Bool := fun b => b

/-- ⚠ **反例·左边** = `-1`（**对应任务清单第 2 条**）。

$$\sum_u p(u)\,[fx(u) = ()]\,[fy(u) = \texttt{false}]
  = 1\cdot 1\cdot 0 + (-1)\cdot 1\cdot 1 = -1.$$ -/
lemma adjust_pointwise_lhs_cex :
    (∑ u : Bool, pCex u * (if fxCex u = () then 1 else 0)
        * (if fyCex u = false then 1 else 0)) = -1 := by
  rw [Fintype.sum_bool]
  rw [if_neg (by decide : ¬ ((true : Bool) = false))]
  rw [if_pos (by decide : ((false : Bool) = false))]
  norm_num [pCex, fxCex, fyCex]

/-- ⚠ **反例·中间量**：`X = ()` 处对 `u` 的纤维和 = `0`（**对应任务清单第 2 条**）。

$$\sum_u p(u)\,[fx(u) = ()]\,[fz(u) = ()]
  = 1 + (-1) = 0.$$

⭐ **注意**：这个 `0` 与 `y` **无关** —— 一旦 `Z` 被边缘化，
`X = ()` 的纤维和就只剩 `p` 的总质量（这里是 `0`），
**关于 `Y` 的信息全部丢失**。这正是右边再也无法还原左边的根因。 -/
lemma adjust_pointwise_mid_cex :
    (∑ u : Bool, pCex u * (if fxCex u = () then 1 else 0)
        * (if fzCex u = () then 1 else 0)) = 0 := by
  rw [Fintype.sum_bool]
  norm_num [pCex, fxCex, fzCex]

/-- ⚠ **反例·右边 = `0`**（**对应任务清单第 2 条**）。

$$\sum_{z}\Big(\sum_u p(u)[fx(u)=()][fz(u)=z]\Big)\cdot[fy(\_) = \texttt{false}]
  = 0 \cdot [\,\cdot\,] = 0.$$

`Z = Unit` 只有一个 `z`，内层和为 `0`（上一引理），故右边恒为 `0`。

**⚠ 关于良式读法**：原式里的 `u` 在 `∑ u` 之外是**自由的**，
故严格的良式需要**固定**一个点来对 `fy` 求值。本文件取 `u = false`
（见 `adjust_pointwise_false` 的陈述）；取 `u = true` 时右边同样为 `0`
（`[fy true = false] = [true = false] = 0`，也是 `0`），故**无论取哪个点，反例都成立**
—— 反例的成立**不依赖**这个选择，因为那个因子本来就被 `0` 杀掉。 -/
lemma adjust_pointwise_rhs_cex :
    (∑ z : Unit, (∑ u : Bool, pCex u * (if fxCex u = () then 1 else 0)
        * (if fzCex u = z then 1 else 0)) * (if fyCex false = false then 1 else 0)) = 0 := by
  rw [Fintype.sum_unique]
  rw [adjust_pointwise_mid_cex]
  norm_num [fyCex]

/-- ❌❌ **`adjust_pointwise` 不成立**（**对应任务清单第 2 条**）。

**任务书给出的等式**

    (∑ u, p u * [fx u = x] * [fy u = y])
      = ∑ z, (∑ u, p u * [fx u = x] * [fz u = z]) * [fy u = y]

**在良式读法下是假的**。本定理是它的**否定**：
存在 `p, fx, fz, fy`（即上面的反例）使等式在 `x = ()`, `y = false` 处
两侧分别取 `-1` 与 `0`。

**⚠ 因此本文件不提供 `adjust_pointwise` 的证明**（那将需要 `sorry` 或说谎），
而提供它的**否证**。任务书允许「第二条证不出则只交第一条」；
本文件更强：**不是证不出，而是命题为假**，并给出机器验证的反例。

**根因（也是 backdoor 的真正内容）**：右边把 `[fy u = y]` 提到了 `∑ u`
**外面**，于是 `fy` 只在一个点上被采样，而左边对所有 `u` 加权。
要修复，必须让 `Z` **携带 `Y` 的信息**（`Y ⫫ Z | X` 的那一半），
即把 `[fy u = y]` 留在**纤维内部** —— 那时的重排由
`fiber_decomposition_pullout` 承担。 -/
theorem adjust_pointwise_false :
    ¬ ∀ (p : Bool → ℝ) (fx : Bool → Unit) (fz : Bool → Unit) (fy : Bool → Bool),
      (∑ u : Bool, p u * (if fx u = () then 1 else 0) * (if fy u = false then 1 else 0))
        = ∑ z : Unit, (∑ u : Bool, p u * (if fx u = () then 1 else 0)
            * (if fz u = z then 1 else 0)) * (if fy false = false then 1 else 0) := by
  intro h
  have hcex := h pCex fxCex fzCex fyCex
  rw [adjust_pointwise_lhs_cex, adjust_pointwise_rhs_cex] at hcex
  norm_num at hcex

/-! ## §3 ⭐⭐ **单点塌缩**（**可修版本的代数核心**） -/

/-- ⭐⭐ **单点塌缩**。

若权重 `c z = [z = z₀]`，则对 `z` 的求和**塌缩**到 `z₀`：

$$\sum_{z} \Big(\sum_u A(u)\,[f(u)=z]\Big)\cdot[z = z_0]
   = \sum_u A(u)\,[f(u)=z_0].$$

证明用 `Finset.sum_eq_single`：只有 `z = z₀` 一项非零
（其余项被 `[z = z₀] = 0` 杀死），而该项的 `[z₀ = z₀] = 1`
把外因子消掉。

**⭐ 这是 §2 反例诊断的代数化**：反例里 `Z = Unit` 只有一个点，
右边的 `∑ z` 本就塌缩成一项；塌缩后剩 `(∑ u, p u) * [fy () = y]`，
而 `∑ u, p u = 0`（`p` 有正负抵消），**`Y` 的信息彻底消失**。
**所以「`Z` 必须携带 `Y` 的信息」不是修辞，而是这个塌缩引理的对偶要求。** -/
theorem sum_mul_single_point
    {U Y : Type*} [Fintype U] [Fintype Y] [DecidableEq Y]
    (A : U → ℝ) (f : U → Y) (z₀ : Y) :
    (∑ z : Y, (∑ u, A u * (if f u = z then 1 else 0)) * (if z = z₀ then 1 else 0))
      = ∑ u, A u * (if f u = z₀ then 1 else 0) := by
  rw [Finset.sum_eq_single z₀]
  · rw [if_pos rfl, mul_one]
  · intro z _ hz
    rw [if_neg hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ z₀) h

/-- ⭐⭐ **`Z` 被边缘化后 `Y` 的信息全部丢失**（**§2 反例的机制，抽象化**）。

若 `Z` 是单点（`Z = Unit`），则 §2 右端**恒等于**

$$\Big(\sum_u p(u)\,[fx(u)=x]\Big)\cdot[fy(\_) = y],$$

**`fx` 之外只剩一个总质量 `∑ u, p u·[fx u = x]`，与 `fy` 独立**。
左边却是 `∑ u p(u)[fx u = x][fy u = y]` —— **依赖 `fy`**。
两者相等的唯一机会是总质量恰好「碰对」，或者 `fy` 退化。

**⚠ 本引理正是 §2 反例的骨架**：`pCex` 的总质量 = 0，
而左边 = -1，故必然不等。 -/
theorem unit_z_collapses_to_total_mass
    {U X : Type*} [Fintype U] [DecidableEq X]
    (p : U → ℝ) (fx : U → X) (x : X) (z : Unit) :
    (∑ u, p u * (if fx u = x then 1 else 0) * (if (fun _ : U => z) u = z then 1 else 0))
      = ∑ u, p u * (if fx u = x then 1 else 0) := by
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [if_pos rfl, mul_one]

end FateV2.Predict.R229