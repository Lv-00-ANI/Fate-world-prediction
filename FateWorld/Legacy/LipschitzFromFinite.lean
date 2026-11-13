/-
  命运理论 · **裁决 1：(乙) 有限分离空间上 L 的存在性**

  ============================================================================
  ⚠ 本文件的定位（**诚实声明，须先读**）
  ============================================================================

  ## (a) 作者第 577 轮裁决原话

  > 「裁决1 试一下乙  如果实在不行  甲」
  > 「然后做不出来一般是需要给别的东西加东西才能做而不是单纯的要证明的对象才能解决」

  ## (b) 为什么 (乙) 在**一般**度量空间上是【假】的

  (乙) 的原命题是：

  > `f : X → Y` 单射且连续 ⟹ `∃ L > 0, LipschitzInvertibleOn f L`。

  **⟹ 这在一般（伪）度量空间上不成立。** 反例：

  `f : ℝ → ℝ`，`f x = x ^ 3`。它**单射**且**连续**。但
  `dist (f ε) (f 0) = ε ^ 3`，而 `LipschitzInvertibleOn f L` 要求
  `ε ^ 3 ≥ ε / L`，即 `L ≥ 1 / ε ^ 2`；当 `ε → 0` 时右端 `→ ∞`，
  **不存在有限的 `L`**。故 (乙) 在原形式下**是假的**。

  ## (c) 加的结构：`FiniteSeparatedSpace`

  按作者第 577 轮的方法论（「给别的东西加东西」），本文件
  **不是**去证更强的命题，而是**给空间加结构**：

  * `fintype : Fintype X` —— 空间**有限**；
  * `sep : ∀ x₁ x₂, x₁ ≠ x₂ → 0 < dist x₁ x₂` —— 空间**分离**
    （伪度量下有限空间自动分离，但显式写出便于使用）；
  * `DecidableEq` —— 由 `Fintype` + `Classical` 提供，供 `Finset` 使用。

  **⚠ 关于值域 `Y` 的分离性**：本文件用的是 `PseudoMetricSpace`
  （与 `LipschitzInvertibleOn` 的定义一致）。在**伪**度量空间中
  `dist a b = 0` **不**推出 `a = b`，所以仅凭 `h` 单射**不能**推出
  `0 < dist (h x₁) (h x₂)`。故本文件把「值域分离」也作为一个
  **显式前件** `hsep : ∀ y₁ y₂ : Y, y₁ ≠ y₂ → 0 < dist y₁ y₂` 写出。
  这是「给别的东西加东西」的第二步 —— 若把 `Y` 换成 `MetricSpace`，
  `hsep` 可由 `dist_pos` 自动得到。

  在「有限 + 分离（含值域分离）」下，不同点对的距离比只有**有限多个**，
  取**最小值** `m > 0`（由单射 + 双向分离保证），令 `L := 1 / m`
  即得 `LipschitzInvertibleOn h L`。

  **⚠ 注意方向**：目标是 `dist (h x₁) (h x₂) ≥ dist x₁ x₂ / L`，
  等价于「比值 `dist_h / dist_x` 有**正下界**」，所以必须取比值的
  **最小值**（不是最大值）—— 取最大值会得到**反向**的不等式。

  ## (d) 本定理的实质

  **它是「加结构后」的定理，不是「原命题」的定理。**
  原命题（一般度量空间上单射 + 连续 ⟹ `∃ L`）是**假的**（见 (b)）。
  本文件只声称：

  > **在有限分离空间上（且值域分离），单射 ⟹ 存在 `L`。**

  ## (e) 不声称的事

  本文件**不声称**「`L` 可以完全从数据算出」——
  只声称「在有限分离空间上，单射 ⟹ **存在** `L`」。
  本文件也**不**触碰 `LipschitzInvertibleOn` 定义本身
  （定义在 `Fate/ObsEstimationStrong.lean`，命名空间 `Fate.RA14Strong`）。
  ============================================================================ -/

import FateWorld.Legacy.ObsEstimationStrong
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Sort

set_option warn.classDefReducibility false

namespace Fate

namespace LipschitzFromFinite

open Fate.RA14Strong (LipschitzInvertibleOn)

/-! ## 一、新结构：有限且分离的度量空间 -/

/-- ⭐⭐ **【新结构：有限且分离的度量空间】**

**为什么需要它**：在一般度量空间上，「`h` 单射且连续」**不足以**推出
`∃ L, LipschitzInvertibleOn h L` —— 反例 `h(x) = x ^ 3` 在 `ℝ` 上：
`dist (h ε) (h 0) = ε ^ 3`，需 `ε ^ 3 ≥ ε / L`，`ε → 0` 时无有限 `L` 满足。

**⟹ 所以按作者第 577 轮的方法论（「给别的东西加东西」）**：
**加两个结构条件** —— **有限**（`Fintype`）与**分离**
（`∀ x ≠ y, 0 < dist x y`）。在这两个条件下，「单射」即足以给出有限 `L`。 -/
class FiniteSeparatedSpace (X : Type*) [PseudoMetricSpace X] where
  /-- 空间有限。 -/
  fintype : Fintype X
  /-- 任意两个不同点的距离有正下界（有限 + 分离即自动成立，但显式写出便于使用）。 -/
  sep : ∀ x₁ x₂ : X, x₁ ≠ x₂ → 0 < dist x₁ x₂

attribute [instance] FiniteSeparatedSpace.fintype

/-! ## 二、辅助定义与引理 -/

/-- 不同点对的「距离比」函数。 -/
noncomputable def ratio {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : X → Y) (p : X × X) : ℝ :=
  dist (h p.1) (h p.2) / dist p.1 p.2

/-- 不同点对的集合（作为 `Finset (X × X)`）。 -/
noncomputable def distinctPairs (X : Type*) [PseudoMetricSpace X] [Fintype X]
    [DecidableEq X] : Finset (X × X) :=
  Finset.univ.filter (fun p : X × X => p.1 ≠ p.2)

/-- 若 `X` 中**不存在**不同点对，则 `X` 的任意两点相等。 -/
theorem eq_of_no_distinct_pair {X : Type*} [PseudoMetricSpace X] [Fintype X]
    [DecidableEq X] (hempty : distinctPairs X = ∅) : ∀ x₁ x₂ : X, x₁ = x₂ := by
  intro x₁ x₂
  by_contra hne
  have hmem : (x₁, x₂) ∈ distinctPairs X := by
    simp only [distinctPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hne
  rw [hempty] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- 单射 + 双向分离 ⟹ 每个不同点对的「距离比」为**正**。 -/
theorem ratio_pos {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {h : X → Y} (hinj : Function.Injective h)
    (FX : FiniteSeparatedSpace X)
    (hsep : ∀ y₁ y₂ : Y, y₁ ≠ y₂ → 0 < dist y₁ y₂)
    {p : X × X} (hp : p.1 ≠ p.2) :
    0 < ratio h p := by
  unfold ratio
  have hd : 0 < dist p.1 p.2 := FX.sep p.1 p.2 hp
  have hh : 0 < dist (h p.1) (h p.2) := hsep (h p.1) (h p.2) (fun he => hp (hinj he))
  exact div_pos hh hd

/-! ## 三、主定理：(乙) 在有限分离空间上的版本 -/

/-- ⭐⭐⭐ **【裁决 1 的 (乙)：L 的存在性】**

**在【有限分离空间】上（且值域分离），若 `h` 是单射，则存在 `L` 使
`LipschitzInvertibleOn h L`。**

**见证**：设所有不同点对的距离比的**最小值**为 `m`（若不存在不同点对，
即 `X` 至多一个点，则取 `L := 1`，条件空真），令 `L := 1 / m`。

* `m > 0`：由 `h` 单射（`dist (h x₁) (h x₂) > 0`，用 `hsep`）与 `FX.sep`
  （`dist x₁ x₂ > 0`），比值正。
* 对任意 `x₁ ≠ x₂`，比值 `≥ m = 1 / L`，
  即 `dist (h x₁) (h x₂) / dist x₁ x₂ ≥ 1 / L = m`，
  两边乘 `dist x₁ x₂ > 0` 得 `dist (h x₁) (h x₂) ≥ m * dist x₁ x₂`，
  而 `m * dist x₁ x₂ = dist x₁ x₂ / (1 / m)`。
* 对 `x₁ = x₂`，两边皆 `0`。

**⟹ 这是「给别的东西加东西」后才可证的**：在一般度量空间上它是假的
（`x ^ 3` 反例，见文件头 (b)）。 -/
theorem exists_lipschitzInvertibleOn_of_finite_separated
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (FX : FiniteSeparatedSpace X)
    (hsep : ∀ y₁ y₂ : Y, y₁ ≠ y₂ → 0 < dist y₁ y₂)
    (h : X → Y) (hinj : Function.Injective h) :
    ∃ L : ℝ, 0 < L ∧ ∀ x₁ x₂ : X, dist (h x₁) (h x₂) ≥ dist x₁ x₂ / L := by
  classical
  haveI : DecidableEq X := Classical.decEq X
  by_cases hempty : distinctPairs X = ∅
  · -- 情形 1：无不同点对 ⟹ 任意两点相等 ⟹ 结论对 L = 1 空真成立
    have hall : ∀ x₁ x₂ : X, x₁ = x₂ := eq_of_no_distinct_pair hempty
    refine ⟨1, one_pos, ?_⟩
    intro x₁ x₂
    rw [hall x₁ x₂]
    simp
  · -- 情形 2：存在不同点对，取比值集合 {ratio h p | p ∈ distinctPairs} 的最小值 m
    have hne : (distinctPairs X).Nonempty := Finset.nonempty_of_ne_empty hempty
    have hne' : ((distinctPairs X).image (fun p => ratio h p)).Nonempty :=
      hne.image _
    set m : ℝ := ((distinctPairs X).image (fun p => ratio h p)).min' hne' with hm
    -- m 是某个不同点对的比值，故 m > 0
    obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne')
    have hp' : p.1 ≠ p.2 := by
      simpa only [distinctPairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    have hmpos : 0 < m := by rw [hm, ← hpm]; exact ratio_pos hinj FX hsep hp'
    refine ⟨1 / m, by positivity, ?_⟩
    intro x₁ x₂
    by_cases hne2 : x₁ = x₂
    · subst hne2; simp
    · -- m ≤ ratio h (x₁, x₂)
      have hlower : m ≤ ratio h (x₁, x₂) := by
        rw [hm]
        exact Finset.min'_le _ _
          (Finset.mem_image.mpr
            ⟨(x₁, x₂), by
              simp only [distinctPairs, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hne2, rfl⟩)
      have hd : 0 < dist x₁ x₂ := FX.sep x₁ x₂ hne2
      -- 目标：dist (h x₁) (h x₂) ≥ dist x₁ x₂ / (1 / m)，即 m * dist x₁ x₂ ≤ dist (h x₁) (h x₂)
      have hone : dist x₁ x₂ / (1 / m) = m * dist x₁ x₂ := by
        field_simp
      rw [hone]
      unfold ratio at hlower
      have key : m * dist x₁ x₂ ≤ dist (h x₁) (h x₂) := by
        rw [le_div_iff₀ hd] at hlower
        simpa using hlower
      calc m * dist x₁ x₂ ≤ dist (h x₁) (h x₂) := key

end LipschitzFromFinite

end Fate
