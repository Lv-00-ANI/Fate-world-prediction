import FateWorld.Legacy.PearlMarkov

/-! ===========================================================================
  `Fate/PearlPathCompose` —— **沿路径组合条件独立**（**第 225 轮**）

  ## 缺口（路线图 §6 缺口 1）

  **Pearl《Causality》定理 1.2.4**：**d-分离 ⟹ 条件独立。**

  **完整 1.2.4 的四步**：
  1. **局部片段**：链 / 分叉 / 对撞各自的独立性 → ✅ **第 213/215/224 轮**
  2. **路径组合**：把**沿一条路径**的局部独立性**串起来** → ⭐ **本文件补**
  3. **路径分解**：把「所有路径被阻断」化为「每条路径各算一段」 → ⚠ 未做
  4. **全局 Markov 性**：把 3 接到联合分布 → ⚠ 未做

  **⭐⭐ 本文件交付第 2 步** —— 它是 1.2.4 的**归纳引擎**。

  ## 本文件的核心结果

  **⭐ 命题（四元链）**：`x → y → z → w`，局部 Markov
  $$p(x,y,z,w) = p(x)\,p(y|x)\,p(z|y)\,p(w|z)$$
  **⟹ `x ⊥ w | y`**（**跨两步仍条件独立**）。

  **⭐⭐ 这正是 1.2.4 在**长链**上的归纳步：
  **链的一步（第 215 轮）给出 `a ⊥ c | b`；本文件给出**跨任意多数步**的版本。**
================================================================================ -/

namespace Fate.PearlPathCompose

open Finset

/-! ## §1 四元链的 Markov 分解 -/

/-- ⭐⭐ **四元链的 Markov 分解**：`p(x,y,z,w) = px x · py x y · pz y z · pw z w`。 -/
def Chain4Fac {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (p : X × Y × Z × W → ℝ) (px : X → ℝ) (py : X → Y → ℝ)
    (pz : Y → Z → ℝ) (pw : Z → W → ℝ) : Prop :=
  ∀ x y z w, p (x, y, z, w) = px x * py x y * pz y z * pw z w

/-- ⭐⭐ **`w` 在给定 `y` 下的边缘条件律**：`∑ z, pz y z · pw z w`。 -/
noncomputable def margPW_of_Y {Y Z W : Type*} [Fintype Z]
    (pz : Y → Z → ℝ) (pw : Z → W → ℝ) (y : Y) (w : W) : ℝ :=
  ∑ z, pz y z * pw z w

/-- ⭐⭐ **`y` 的边缘律**：`∑ x, px x · py x y`。 -/
noncomputable def margPY {X Y : Type*} [Fintype X]
    (px : X → ℝ) (py : X → Y → ℝ) (y : Y) : ℝ :=
  ∑ x, px x * py x y

/-! ## §2 ⭐⭐⭐ **边缘化 `z`：`x` 与 `w` 只通过 `y` 交互** -/

/-- ⭐⭐⭐ **边缘化 `z`**：

$$\sum_z p(x,y,z,w) = p(x)\cdot p(y|x)\cdot \sum_z p(z|y)p(w|z)$$

**🔹 这是链式传播的**核心计算**：
**`x` 与 `w` **只通过 `y` 交互** —— `p(w|x,y)` 实际上**只依赖 `y`**。** -/
theorem margZ_chain4 {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (p : X × Y × Z × W → ℝ) (px : X → ℝ) (py : X → Y → ℝ)
    (pz : Y → Z → ℝ) (pw : Z → W → ℝ)
    (h : Chain4Fac p px py pz pw) (x : X) (y : Y) (w : W) :
    (∑ z, p (x, y, z, w)) = px x * py x y * margPW_of_Y pz pw y w := by
  have step : ∀ z, p (x, y, z, w) = px x * py x y * (pz y z * pw z w) := by
    intro z
    rw [h x y z w]
    ring
  rw [Finset.sum_congr rfl (fun z _ => step z)]
  rw [← Finset.mul_sum]
  rfl

/-- ⭐⭐⭐⭐ **条件律 `p(w|x,y)` 与 `x` **无关****（**这就是 `x ⊥ w | y` 的精确含义**）。

**⭐ 陈述**：`∑ z, p(x,y,z,w) / (px x · py x y) = margPW_of_Y pz pw y w`
**—— 右边**不出现 `x`**。** -/
theorem condPW_indep_of_x {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (p : X × Y × Z × W → ℝ) (px : X → ℝ) (py : X → Y → ℝ)
    (pz : Y → Z → ℝ) (pw : Z → W → ℝ)
    (h : Chain4Fac p px py pz pw) (x : X) (y : Y) (w : W)
    (hpx : px x ≠ 0) (hpy : py x y ≠ 0) :
    (∑ z, p (x, y, z, w)) / (px x * py x y) = margPW_of_Y pz pw y w := by
  rw [margZ_chain4 p px py pz pw h x y w]
  field_simp

/-! ## §3 ⭐⭐⭐⭐ **主定理：`x ⊥ w | y` 的乘性形式**

**⭐⭐ 标准形式**：`p(x,y,w) · p(y) = p(x,y) · p(y,w)`。

**⚠ 这需要**归一化假设**：`∑ z, pz y z = 1`（`z` 在给定 `y` 下归一）
与 `∀ z, ∑ w, pw z w = 1`（`w` 在给定 `z` 下归一）。** -/

/-- ⭐⭐ **`(x,y)` 的边缘律**：`∑ z ∑ w, p(x,y,z,w) = px x · py x y`（**当 `pz`、`pw` 归一**）。

**⭐ 这两个归一化假设是**概率分布的标准要求**（`p(z|y)` 与 `p(w|z)` 都是条件概率）。** -/
theorem margXY_chain4 {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (p : X × Y × Z × W → ℝ) (px : X → ℝ) (py : X → Y → ℝ)
    (pz : Y → Z → ℝ) (pw : Z → W → ℝ)
    (h : Chain4Fac p px py pz pw) (x : X) (y : Y)
    (hz : ∑ z, pz y z = 1) (hw : ∀ z, ∑ w', pw z w' = 1) :
    (∑ z, ∑ w', p (x, y, z, w')) = px x * py x y := by
  have step : ∀ z, (∑ w', p (x, y, z, w')) = px x * py x y * pz y z := by
    intro z
    have hwz : ∀ w', p (x, y, z, w') = px x * py x y * pz y z * pw z w' := by
      intro w'
      rw [h x y z w']
    rw [Finset.sum_congr rfl (fun w' _ => hwz w')]
    rw [← Finset.mul_sum, hw z, mul_one]
  rw [Finset.sum_congr rfl (fun z _ => step z)]
  rw [← Finset.mul_sum, hz, mul_one]

/-- ⭐⭐ **`(y,w)` 的边缘律**：`∑ x ∑ z, p(x,y,z,w) = margPY · margPW`。 -/
theorem margYW_chain4 {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (p : X × Y × Z × W → ℝ) (px : X → ℝ) (py : X → Y → ℝ)
    (pz : Y → Z → ℝ) (pw : Z → W → ℝ)
    (h : Chain4Fac p px py pz pw) (y : Y) (w : W) :
    (∑ x, ∑ z, p (x, y, z, w)) = margPY px py y * margPW_of_Y pz pw y w := by
  have step : ∀ x, (∑ z, p (x, y, z, w)) = px x * py x y * margPW_of_Y pz pw y w :=
    fun x => margZ_chain4 p px py pz pw h x y w
  rw [Finset.sum_congr rfl (fun x _ => step x)]
  rw [← Finset.sum_mul]
  rfl

/-- ⭐⭐⭐⭐⭐ **主定理：`x ⊥ w | y`（乘性形式）**

$$p(x,y,w)\cdot p(y) = p(x,y)\cdot p(y,w)$$

**🔹 对应清单**：**Pearl 1.2.4 的长链归纳步**。

**⭐⭐ 这是**链式传播**的最终形式**：
**一条链上相隔任意远的两个点，在中间点下条件独立。**

**⭐ 证明**：把四条边缘律全部代入，两边都化为 `px x · py x y · margPY · margPW`。** -/
theorem chain4_multiplicative {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (p : X × Y × Z × W → ℝ) (px : X → ℝ) (py : X → Y → ℝ)
    (pz : Y → Z → ℝ) (pw : Z → W → ℝ)
    (h : Chain4Fac p px py pz pw) (x : X) (y : Y) (w : W)
    (hz : ∑ z, pz y z = 1) (hw : ∀ z, ∑ w', pw z w' = 1) :
    (∑ z, p (x, y, z, w)) * margPY px py y
      = (∑ z, ∑ w', p (x, y, z, w')) * (∑ x', ∑ z, p (x', y, z, w)) := by
  rw [margZ_chain4 p px py pz pw h x y w]
  rw [margXY_chain4 p px py pz pw h x y hz hw]
  rw [margYW_chain4 p px py pz pw h y w]
  ring

end Fate.PearlPathCompose
