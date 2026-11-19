import FateWorld.FateV2.Predict.T1A2
import Mathlib.Tactic

/-!
  # Predict · T1A2CI

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2CI.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/T1A2CI` —— `T1A.2` 的代数核心

## 内容

本文件交付 `T1A.2`（图因子分解 ⟹ 条件独立）所需的**代数核心**：
从 `FactorizesOn` 提取出**显式的乘积分量**，并证明**可分离性**。

## 为什么这几条重要

`FactorizesOn` 的定义里 `π` 是**存在量化**的，下游无法直接 `rw`。
本文件把它**提取成显式函数**，并提供代数性质（正性、非零性、可分离性）。

**可分离性**是「给定 `S` 后，`S` 内与 `S` 外独立」的**代数形式**，
正是 `T1A.2` 的最终结论（条件独立）的入口。
-/

namespace FateV2.Predict.T1A2CI

open FateV2.Modeling

open Finset
open FateV2.Predict.T1A2

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## §1 分量提取 -/

/-- ⭐⭐⭐ **从 `FactorizesOn` 提取分量**：

存在 `π` 使得 `p x = ∏ v, π v x`，且每个 `π v` 只读 `{v} ∪ pa(v)`、且恒正。

**⚠ 这是 `FactorizesOn` 的直接展开**（`:= h`），
但它的价值在于**把存在量化变成显式函数**，供下游 `rw`。 -/
theorem factorizesOn_components
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) :
    ∃ π : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      ∀ x, p x = ∏ v, π v x :=
  h

/-! ## §2 正性与非零性 -/

/-- ⭐⭐ **正性**：若 `p` 因子分解，则 `p x > 0`。

**证明**：`p x = ∏ v, π v x`，每个因子 `> 0`，故乘积 `> 0`。
（`Finset.prod_pos` 需要每个因子都正，而 `FactorizesOn` 正好要求 `0 < π v x`。） -/
theorem factorizesOn_pos
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) (x : V → Bool) : 0 < p x := by
  obtain ⟨π, _, hpos, hfac⟩ := h
  rw [hfac x]
  exact Finset.prod_pos (fun v _ => hpos v x)

/-- ⭐⭐ **非零性**：若 `p` 因子分解，则 `p x ≠ 0`。 -/
theorem factorizesOn_ne_zero
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) (x : V → Bool) : p x ≠ 0 :=
  ne_of_gt (factorizesOn_pos h x)

/-! ## §3 ⭐⭐⭐ 可分离性（核心） -/

/-- ⭐⭐⭐⭐ **乘积的可分离性**：

若 `p` 因子分解，则对**任意** `S : Finset V`，

$$p(x) = \left(\prod_{v \in S} \pi_v(x)\right) \cdot \left(\prod_{v \notin S} \pi_v(x)\right).$$

**⚠ 这是「给定 `S` 后，`S` 内与 `S` 外独立」的**代数形式**。**

**证明**：`p x = ∏ v, π v x`（`hfac`），
再用 `Finset.prod_mul_prod_compl` 把全集乘积拆成 `S` 与 `Sᶜ` 两半。 -/
theorem factorizesOn_separable
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) (x : V → Bool) :
    ∃ π : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      ∀ S : Finset V,
        p x = (∏ v ∈ S, π v x) * (∏ v ∈ Sᶜ, π v x) := by
  obtain ⟨π, hreads, hpos, hfac⟩ := h
  refine ⟨π, hreads, hpos, fun S => ?_⟩
  rw [hfac x]
  exact (Finset.prod_mul_prod_compl S (fun v => π v x)).symm

/-! ## §4 公理审计 -/

#print axioms factorizesOn_components
#print axioms factorizesOn_pos
#print axioms factorizesOn_ne_zero
#print axioms factorizesOn_separable

end FateV2.Predict.T1A2CI