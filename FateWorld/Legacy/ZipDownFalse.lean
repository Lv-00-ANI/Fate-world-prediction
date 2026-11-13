/-
# `ZipDownFalseFixed` —— **桥的反例**：`¬ ZipDown`（**零 `sorry`**）

## 0 结论

**主定理** ⭐⭐ `zipDown_false`：

```
¬ ZipDown PjointB {0} {1},  即
¬ ∀ Z Z', Z ⊆ Z' → CondIndep p {0} {1} Z' → CondIndep p {0} {1} Z.
```

见证：`Z = ∅`、`Z' = {2}`（`∅ ⊆ {2}` 成立）。

* ✅ `condIndepB`：`CondIndep PjointB {0} {1} {2}`（**大条件集成立**）；
* ✅ `not_condIndepB`：`¬ CondIndep PjointB {0} {1} ∅`（**小条件集失败**）；
* ⟹ `ZipDown` 对条件集**不单调**，machine-checked。

**⟹ 这否证的是「先用更大的 `Z'` 拿到 `CondIndep`、再压回 `Z`」这一策略**，
不否证 `Z' = Z` 版的桥（`BridgeFull.markov_of_gap`，其前件是 `Z' = Z`）。

### 0.1 ⚠ 对 `Fate/BridgeZipDown.lean` 的两处更正（均已 machine-checked）

1. 该文件 §0.1 声称 `Pjoint w = 1/4·[w₂ = (w₀ = w₁)]` 满足
   `CondIndep Pjoint {0} {1} {2}`。**这是错的**：`x₂` 记录 `x₀ = x₁` 使
   **给定 `x₂` 后 `(x₀,x₁)` 完全相关**，方向与「给定 `x₂` 后独立」相反。
   本文件 §3 的 `Pjoint_not_condIndep` 给出机器验证的否定
   （在 `x₂ = (x₀ = x₁)` 的点上 `mass{0,1,2}·mass{2} = 2k·4k = 8k²` 而
   `mass{0,2}·mass{1,2} = 2k·2k = 4k²`，`k = 1/4 ≠ 0`）。
2. 该文件的 `mass_empty_P` **仍是 `sorry`**，且其结论 `mass ∅ Pjoint = 2`
   与其联合律相配的**正确**值不符（见上）。本文件**不消费**该定理。

### 0.2 本文件的反例联合律 `PjointB`（**混合模型 / Simpson 型**）

`V = Fin 4`、`α = Bool`，图无关（本反例是**纯概率**现象）：

$$p(w) = \begin{cases}1/8 & w_2\\ 1/2 & \neg w_2 \wedge w_0 \wedge w_1\\ 0 & \text{else}\end{cases}$$

`x₂` 是「选择子族」的隐变量，**两支各半权、各自内部 `(x₀,x₁)` 独立**，
但**合并（混合）后** `x₀` 与 `x₁` 相关。坐标 `3` 完全自由。
总质量 `2`（**不归一**）—— `CondIndep` 是**齐次乘性恒等式**，对标量不变，
故不归一不影响任何结论（⚠ 因此本反例**不对 `FactorNorm` 成立的归一分布**作断言）。

**数值台账**（全部 machine-checked，§2）：

| 集合 `S` | `mass S PjointB x` |
|---|---|
| `{0,1,2}` | `x₂ = ⊤ ⟹ 1/4`；否则 `x₀∧x₁ ⟹ 1`，否则 `0` |
| `{2}` | `1` |
| `{0,2}` | `x₂ = ⊤ ⟹ 1/2`；否则 `x₀ ⟹ 1`，否则 `0` |
| `{1,2}` | `x₂ = ⊤ ⟹ 1/2`；否则 `x₁ ⟹ 1`，否则 `0` |
| `{0,1}` | `x₀∧x₁ ⟹ 5/4`，否则 `1/4` |
| `{0}` | `x₀ ⟹ 3/2`，否则 `1/2` |
| `{1}` | `x₁ ⟹ 3/2`，否则 `1/2` |
| `∅` | `2` |

* `Z' = {2}`：`(1/4)·1 = 1/4 = (1/2)·(1/2)` ✅；`x₂ = ⊥` 且 `x₀∧x₁`：`1·1 = 1·1` ✅；
  其余点左端 `mass{0,1,2} = 0`、右端某因子为 `0` ✅ ⟹ `CondIndep … {2}`。
* `Z = ∅` 在 `x = (⊤,⊤,…)`：`(5/4)·2 = 5/2 ≠ 9/4 = (3/2)·(3/2)` ⟹ 失败。

### 0.3 ⭐ 工程要点（**这就是「不要全量展开」的正确做法**）

`mass` 的定义是**对全部 `x : V → α` 求和**（`Fin 4 → Bool` 有 `16` 个原子，
朴素展开即 `whnf` 超时）。本文件的全部计算只用**两条**已有引理，**从不让 `mass` 展开**：

* `mass_compl_eq_sum`（`univ \ {v}` 上的 `mass` = 对 `v` 位的二项和）；
* `mass_insert_sum`（**T1**）—— 本文件把它包装成 **`mass_erase_eq_sum`**：

$$\texttt{mass }(S\setminus\{h\})\,p\,x=\sum_{a∈\texttt{Bool}}\texttt{mass }S\,p\,[x_h{:=}a].$$

即「**从小集合往大集合加一个坐标**」的剥离方向（`erase` 侧求和，而不是把 `mass`
展开成 16 项）。于是每个 `mass` 值的计算只有 `2`–`4` 个 `p` 的**显式取点**值，
关键是**依次向上剥离**：`∅ → {0} → {0,1} → {0,1,2}`（或 `{2} → {0,2} → {0,1,2}`）。

**⟹ 峰值只有 `∥` `∑_{a:Bool} mass {0,1,2} …` `∥` 这样的 2 项和，从不出现 16 项展开。**

### 0.4 纪律核对

* ✅ 只**新增**本文件（`Fate_agent_staging/`）；**未改** `Fate/`、**未改** `Fate.lean`、
  **未改**任何既有模块；
* ✅ `ZipDown`/`CondIndep`/`mass` 全部 **import 既有定义**，未重定义；
* ✅ 零 `sorry` / `admit` / `axiom`；
* ✅ 单文件验证：`lake env lean Fate_agent_staging/ZipDownFalseFixed.lean` 零错误。
================================================================================ -/

import FateWorld.Legacy.BridgeZipDown
import Mathlib.Tactic

open Finset
namespace Fate.ZipDownFalseFixed

open Fate.DAGFactorization
open Fate.FactorMarkov
open Fate.BridgeZipDown (ZipDown zipDown_def)

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-! ===========================================================================
  §1 反例联合律 `PjointB`（混合模型 / Simpson 型）
  =========================================================================== -/

/-- ⭐ **反例联合律 `PjointB`**。

* `w₂ = ⊤`：`(w₀,w₁)` **独立**均匀（4 组合），`w₃` 自由，权重 `1/8` ⟹ 该支总质量 `1`；
* `w₂ = ⊥`：`w₀ = w₁ = ⊤`，`w₃` 自由，权重 `1/2` ⟹ 该支总质量 `1`。

⟹ 总质量 `2`（不归一）；**给定 `x₂` 后 `(x₀,x₁)` 独立**，**不给定则相关**。 -/
noncomputable def PjointB (w : Fin 4 → Bool) : ℝ :=
  if w 2 then (1 / 8 : ℝ) else (if (w 0 && w 1) then (1 / 2 : ℝ) else 0)

/-! ===========================================================================
  §2 `mass` 的剥离工具（**从不让 `mass` 全量展开**）
  =========================================================================== -/

section Peel

/-- `unpin` 在**自己**的坐标上取新值。 -/
theorem unpin_same (v : Fin 4) (x : Fin 4 → Bool) (a : Bool) : unpin v x a v = a := by
  simp [unpin]

/-- `unpin` 在**别的**坐标上不动。 -/
theorem unpin_other {v j : Fin 4} (hj : j ≠ v) (x : Fin 4 → Bool) (a : Bool) :
    unpin v x a j = x j := by
  simp [unpin, hj]

/-- ⭐⭐⭐ **剥离主引理**：把 `mass` 从 `S ∖ {h}` **升到** `S`（`h ∈ S`）：

$$\texttt{mass }(S\setminus\{h\})\,p\,x=\sum_{a∈\texttt{Bool}}\texttt{mass }S\,p\,[x_h{:=}a].$$

**证明**：`mass_insert_sum`（T1）取 `S := S ∖ {h}` 与 `insert h (S∖{h}) = S`（`h ∈ S`）。

**⚠ 方向是关键**：等式右端是**小规模**的 2 项和，左端才是我们要求的量 ——
所以用它**向上**剥离（`∅ → {0} → {0,1} → {0,1,2}`），
绝不把 `mass` 展开成 `Fin 4 → Bool` 的 16 项求和。 -/
theorem mass_erase_eq_sum (h : Fin 4) (S : Finset (Fin 4)) (hh : h ∈ S)
    (p : (Fin 4 → Bool) → ℝ) (x : Fin 4 → Bool) :
    mass (S.erase h) p x = ∑ a : Bool, mass S p (unpin h x a) := by
  have hnot : h ∉ S.erase h := by simp
  have hins : insert h (S.erase h) = S := Finset.insert_erase hh
  have := mass_insert_sum h (S.erase h) hnot p x
  rw [hins] at this
  exact this.symm

/-- ⭐ `mass {0,1,2}`（`= univ ∖ {3}`）的**二项**展开。 -/
theorem m012_unfold (x : Fin 4 → Bool) :
    mass ({0,1,2} : Finset (Fin 4)) PjointB x = ∑ a : Bool, PjointB (unpin 3 x a) := by
  have h : ({0,1,2} : Finset (Fin 4)) = univ \ {3} := by decide
  rw [h]
  exact mass_compl_eq_sum PjointB 3 x

end Peel

/-! ===========================================================================
  §3 七个 `mass` 值（**全部机器验证**，§0.2 的台账）
  =========================================================================== -/

/-- ⭐ `mass {0,1,2}`：`x₂ = ⊤` ⟹ `1/4`；否则 `x₀ ∧ x₁` ⟹ `1`，否则 `0`。 -/
theorem m012_val (x : Fin 4 → Bool) :
    mass ({0,1,2} : Finset (Fin 4)) PjointB x
      = (if x 2 = true then (1/4 : ℝ) else (if (x 0 = true ∧ x 1 = true) then 1 else 0)) := by
  rw [m012_unfold, Fintype.sum_bool]
  simp only [PjointB]
  by_cases h2 : x 2 = true <;> by_cases h0 : x 0 = true <;> by_cases h1 : x 1 = true <;>
    simp [unpin, h2, h0, h1] <;> norm_num

/-- ⭐ `mass {0,2}`：`x₂ = ⊤` ⟹ `1/2`；否则 `x₀` ⟹ `1`，否则 `0`。 -/
theorem m02_val (x : Fin 4 → Bool) :
    mass ({0,2} : Finset (Fin 4)) PjointB x
      = (if x 2 = true then (1/2 : ℝ) else (if x 0 = true then 1 else 0)) := by
  have h := mass_erase_eq_sum 1 {0,1,2} (by decide) PjointB x
  have e : ({0,1,2} : Finset (Fin 4)).erase 1 = {0,2} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, m012_val, m012_val]
  by_cases h2 : x 2 = true <;> by_cases h0 : x 0 = true <;>
    simp [unpin, h2, h0] <;> norm_num

/-- ⭐ `mass {2} = 1`。 -/
theorem m2_val (x : Fin 4 → Bool) : mass ({2} : Finset (Fin 4)) PjointB x = 1 := by
  have h := mass_erase_eq_sum 0 {0,2} (by decide) PjointB x
  have e : ({0,2} : Finset (Fin 4)).erase 0 = {2} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, m02_val, m02_val]
  by_cases h2 : x 2 = true <;> simp [unpin, h2] <;> norm_num

/-- ⭐ `mass {1,2}`（与 `m02_val` 对称）。 -/
theorem m12_val (x : Fin 4 → Bool) :
    mass ({1,2} : Finset (Fin 4)) PjointB x
      = (if x 2 = true then (1/2 : ℝ) else (if x 1 = true then 1 else 0)) := by
  have h := mass_erase_eq_sum 0 {0,1,2} (by decide) PjointB x
  have e : ({0,1,2} : Finset (Fin 4)).erase 0 = {1,2} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, m012_val, m012_val]
  by_cases h2 : x 2 = true <;> by_cases h1 : x 1 = true <;>
    simp [unpin, h2, h1] <;> norm_num

/-- ⭐ `mass {0,1}`：`x₀ ∧ x₁` ⟹ `5/4`，否则 `1/4`。 -/
theorem m01_val (x : Fin 4 → Bool) :
    mass ({0,1} : Finset (Fin 4)) PjointB x
      = (if (x 0 = true ∧ x 1 = true) then (5/4 : ℝ) else 1/4) := by
  have h := mass_erase_eq_sum 2 {0,1,2} (by decide) PjointB x
  have e : ({0,1,2} : Finset (Fin 4)).erase 2 = {0,1} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, m012_val, m012_val]
  by_cases h0 : x 0 = true <;> by_cases h1 : x 1 = true <;>
    simp [unpin, h0, h1] <;> norm_num

/-- ⭐ `mass {0}`：`x₀` ⟹ `3/2`，否则 `1/2`。 -/
theorem m0_val (x : Fin 4 → Bool) :
    mass ({0} : Finset (Fin 4)) PjointB x
      = (if x 0 = true then (3/2 : ℝ) else 1/2) := by
  have h := mass_erase_eq_sum 1 {0,1} (by decide) PjointB x
  have e : ({0,1} : Finset (Fin 4)).erase 1 = {0} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, m01_val, m01_val]
  by_cases h0 : x 0 = true <;> simp [unpin, h0] <;> norm_num

/-- ⭐ `mass {1}`（与 `m0_val` 对称）。 -/
theorem m1_val (x : Fin 4 → Bool) :
    mass ({1} : Finset (Fin 4)) PjointB x
      = (if x 1 = true then (3/2 : ℝ) else 1/2) := by
  have h := mass_erase_eq_sum 0 {0,1} (by decide) PjointB x
  have e : ({0,1} : Finset (Fin 4)).erase 0 = {1} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, m01_val, m01_val]
  by_cases h1 : x 1 = true <;> simp [unpin, h1] <;> norm_num

/-- ⭐ `mass ∅ = 2`（总质量；两支各 `1`）。

**⚠** 这里**不**用 `mass_empty`（那会展开 `Fin 4 → Bool` 的 16 项求和），
而是继续用剥离链 `∅ ← {0}`，把 16 项摊成 8 次「2 项和」。 -/
theorem mEmpty_val (x : Fin 4 → Bool) : mass (∅ : Finset (Fin 4)) PjointB x = 2 := by
  have h := mass_erase_eq_sum 0 {0} (by decide) PjointB x
  have e : ({0} : Finset (Fin 4)).erase 0 = (∅ : Finset (Fin 4)) := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, m0_val, m0_val]
  by_cases h0 : x 0 = true <;> simp [unpin, h0] <;> norm_num

/-! ===========================================================================
  §4 三块拼图：`CondIndep` 在 `Z' = {2}` 成立、在 `Z = ∅` 失败 ⟹ `¬ ZipDown`
  =========================================================================== -/

/-- ⭐⭐ **`CondIndep PjointB {0} {1} {2}`**（大条件集 `Z' = {2}` 成立）。

逐点 `x`：
* `x₂ = ⊤`：`(1/4)·1 = 1/4 = (1/2)·(1/2)`；
* `x₂ = ⊥ ∧ x₀ ∧ x₁`：`(1)·1 = 1 = (1)·(1)`；
* 其余：`mass {0,1,2} = 0`，且 `x₂ = ⊥` 时 `x₀ ∨ ¬x₀`、`x₁ ∨ ¬x₁` 保证
  `mass {0,2} = 0` 或 `mass {1,2} = 0`，右端为 `0`。 -/
theorem condIndepB : CondIndep PjointB ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) {2} := by
  intro x
  have e1 : (({0} : Finset (Fin 4)) ∪ {1} ∪ ({2} : Finset (Fin 4))) = {0,1,2} := by decide
  have e2 : (({0} : Finset (Fin 4)) ∪ {2}) = {0,2} := by decide
  have e3 : (({1} : Finset (Fin 4)) ∪ {2}) = {1,2} := by decide
  show mass ({0} ∪ {1} ∪ {2}) PjointB x * mass ({2} : Finset (Fin 4)) PjointB x
      = mass ({0} ∪ {2}) PjointB x * mass ({1} ∪ {2}) PjointB x
  rw [e1, e2, e3, m012_val, m2_val, m02_val, m12_val]
  by_cases h2 : x 2 = true
  · simp [h2]
    norm_num
  · have h2' : x 2 = false := by simpa using h2
    rw [h2']
    by_cases h0 : x 0 = true <;> by_cases h1 : x 1 = true <;>
      (simp [h0, h1]; try norm_num)

/-- ⭐⭐ **`¬ CondIndep PjointB {0} {1} ∅`**（小条件集 `Z = ∅` **失败**）。

在 `x ≡ ⊤` 处：`mass {0,1} · mass ∅ = (5/4)·2 = 5/2`，
而 `mass {0} · mass {1} = (3/2)·(3/2) = 9/4`，且 `5/2 ≠ 9/4`。 -/
theorem not_condIndepB :
    ¬ CondIndep PjointB ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) ∅ := by
  intro hci
  have h := hci (fun _ => true)
  have e1 : (({0} : Finset (Fin 4)) ∪ {1} ∪ (∅ : Finset (Fin 4))) = {0,1} := by decide
  have e2 : (({0} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) = {0} := by decide
  have e3 : (({1} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) = {1} := by decide
  rw [e1, e2, e3, m01_val, mEmpty_val, m0_val, m1_val] at h
  simp at h
  norm_num at h

/-- ⭐⭐⭐⭐⭐ **主定理：`¬ ZipDown PjointB {0} {1}`**。

见证 `Z = ∅`、`Z' = {2}`：`∅ ⊆ {2}`（`hsub`），
`CondIndep … {2}`（`condIndepB`），但 `CondIndep … ∅` **不成立**
（`not_condIndepB`）。

**⟹ `CondIndep` 对条件集不单调：`Z ⊆ Z'` 且 `Z'` 处成立，推不出 `Z` 处成立。** -/
theorem zipDown_false : ¬ ZipDown PjointB ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) := by
  intro hzd
  have hsub : (∅ : Finset (Fin 4)) ⊆ {2} := by decide
  exact not_condIndepB (hzd ∅ {2} hsub condIndepB)


/-! ===========================================================================
  §5 ⚠ 更正：`Fate/BridgeZipDown.lean` §0.1 的 `Pjoint` **不是**反例
  =========================================================================== -/

section Correction

/-- `Fate/BridgeZipDown` 的联合律（**原样复写**，未改原文件）：

`p w = 1/4 · [w₂ = (w₀ = w₁)]`。 -/
noncomputable def PjointOrig (w : Fin 4 → Bool) : ℝ :=
  if w 2 = (w 0 = w 1) then (1 / 4 : ℝ) else 0

/-- `mass {0,1,2} PjointOrig x`：约束成立 ⟹ `1/2`（`w₃` 两个值各 `1/4`），否则 `0`。 -/
theorem porig_012 (x : Fin 4 → Bool) :
    mass ({0,1,2} : Finset (Fin 4)) PjointOrig x
      = (if x 2 = (x 0 = x 1) then (1/2 : ℝ) else 0) := by
  have h : ({0,1,2} : Finset (Fin 4)) = univ \ {3} := by decide
  rw [h, mass_compl_eq_sum, Fintype.sum_bool]
  unfold PjointOrig unpin
  by_cases h0 : x 0 = true <;> by_cases h1 : x 1 = true <;> by_cases h2 : x 2 = true <;>
    simp [h0, h1, h2] <;> norm_num

/-- `mass {0,2} PjointOrig x = 1/2`（与 `x` 无关：对 `w₁` 只有一个取值使约束成立）。 -/
theorem porig_02 (x : Fin 4 → Bool) :
    mass ({0,2} : Finset (Fin 4)) PjointOrig x = 1 / 2 := by
  have h := mass_erase_eq_sum 1 {0,1,2} (by decide) PjointOrig x
  have e : ({0,1,2} : Finset (Fin 4)).erase 1 = {0,2} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, porig_012, porig_012]
  unfold unpin
  by_cases h0 : x 0 = true <;> by_cases h2 : x 2 = true <;>
    (simp [h0, h2]; try norm_num)

/-- `mass {1,2} PjointOrig x = 1/2`（与 `porig_02` 对称）。 -/
theorem porig_12 (x : Fin 4 → Bool) :
    mass ({1,2} : Finset (Fin 4)) PjointOrig x = 1 / 2 := by
  have h := mass_erase_eq_sum 0 {0,1,2} (by decide) PjointOrig x
  have e : ({0,1,2} : Finset (Fin 4)).erase 0 = {1,2} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, porig_012, porig_012]
  unfold unpin
  by_cases h1 : x 1 = true <;> by_cases h2 : x 2 = true <;>
    (simp [h1, h2]; try norm_num)

/-- `mass {2} PjointOrig x = 1`（与 `x` 无关）。 -/
theorem porig_2 (x : Fin 4 → Bool) : mass ({2} : Finset (Fin 4)) PjointOrig x = 1 := by
  have h := mass_erase_eq_sum 0 {0,2} (by decide) PjointOrig x
  have e : ({0,2} : Finset (Fin 4)).erase 0 = {2} := by decide
  rw [e] at h
  rw [h, Fintype.sum_bool, porig_02, porig_02]
  norm_num

/-- ⭐⭐ **`¬ CondIndep PjointOrig {0} {1} {2}`**

**⟹ `Fate/BridgeZipDown.lean` §0.1 的断言「`Pjoint` 满足
`CondIndep Pjoint {0}{1}{2}`」是错的**（本定理机器验证其否定）。

取 `x ≡ ⊤`（约束 `⊤ = (⊤ = ⊤)` 成立）：
`mass{0,1,2}·mass{2} = (1/2)·1 = 1/2`，
而 `mass{0,2}·mass{1,2} = (1/2)·(1/2) = 1/4`，两者不等。

**直觉**：`x₂` 记录 `x₀ = x₁` 使**给定 `x₂` 后 `(x₀,x₁)` 完全相关** ——
方向与「给定 `x₂` 后独立」**相反**。 -/
theorem pOriginal_not_condIndep :
    ¬ CondIndep PjointOrig ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) {2} := by
  intro hci
  have h := hci (fun _ => true)
  have e1 : (({0} : Finset (Fin 4)) ∪ {1} ∪ ({2} : Finset (Fin 4))) = {0,1,2} := by decide
  have e2 : (({0} : Finset (Fin 4)) ∪ {2}) = {0,2} := by decide
  have e3 : (({1} : Finset (Fin 4)) ∪ {2}) = {1,2} := by decide
  rw [e1, e2, e3, porig_012, porig_2, porig_02, porig_12] at h
  simp only [Finset.sum_apply, Pi.zero_apply, Finset.mem_univ, Finset.sum_const_zero] at h
  norm_num at h

end Correction

end Fate.ZipDownFalseFixed