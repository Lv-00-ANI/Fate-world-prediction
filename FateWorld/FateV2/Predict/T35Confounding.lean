import FateWorld.FateV2.Modeling.SCMSemantics

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/T35Confounding.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 4 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Predict

/-! ===========================================================================
  `FateV2.Predict/T35Confounding` —— **T3.5 观测分布与干预分布的不重合**（**第 219 轮**）

  ## 清单原文（T3.5）

  > **观测分布与干预分布的不重合（因果层级的分离）**：
  > 存在 SCM 与变量 `X, Y`，使 `P(Y | do(X=x)) ≠ P(Y | X=x)`。

  **本文件的任务**：**构造一个具体的有限 SCM，显式计算两条律，
  **证明它们不相等** —— **这是「因果层级分离」的最直接见证**。

  ## 为何这条重要

  **Pearl 因果层级**：`观测 ⊂ 干预 ⊂ 反事实`。
  **T3.5 是「观测 ≠ 干预」的具体见证** ——
  **⟹ 它证明只看观测分布无法回答干预问题**，
  **这是整个因果推断存在的理由。**
================================================================================ -/

namespace FateV2.Predict.T35

open PearlHierarchy

/-! ## §1 一个具体的混杂结构

**结构**（最经典的「混杂」图形）：一个外生隐变量 `U` 同时影响 `X` 与 `Y`。

```
    U ──→ X
    │
    └──→ Y
```

**⚠ 用一个 `X = Y = U` 的「完全混杂」实现**（最简且最清晰）：

- 外生空间 `U = Fin 2`
- 外生律 `pU ≡ 1/2`
- `sg u = (u, fun _ => u)`，即 `X = u` 且 `Y = u`

**直觉**：
- **观测** `P(Y=y | X=x)`：`X=x` 已筛出 `u=x` ⟹ `Y` 必为 `x` ⟹ **点质量**
- **干预** `P(Y=y | do(X=x))`：`U` 不受干预影响，`Y = u` 仍随机 ⟹ **`1/2` 取 0、`1/2` 取 1**

**⟹ 二者截然不同** —— 这正是「混杂」的含义。 -/

/-- **完全混杂的 SCM**：`X = Y = U`，`U` 均匀。 -/
noncomputable def M : SCM (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => (u, fun _ => u)

/-! ## §2 显式计算两条律

**⚠ 技术说明**：`condY` / `doLaw` 里的求和号 `∑ u` 依赖 `M.U` 的 `Fintype` 实例，
**而该实例在 `M` 是具体定义时会以 `M.instFintype` 出现** ——
**故我用 `show` 把它化为 `Fin 2` 上的求和，再用 `Fin.sum_univ_two` 展开。** -/

/-- **观测律 `condY M x y`**：**当 `x = y` 时为 `1/2`，否则为 `0`**。

**读法**：给定 `X = x`，`Y` **必等于** `x` —— `Y` 被 `X` 完全决定。

**⚠ 数值上是 `1/2` 而非 `1`**：`condY` 是**联合质量** `P(X=x, Y=y)`，
**而非归一化的条件概率**。`X=x` 的边缘质量是 `1/2`，
**故 `P(Y=y|X=x) = (1/2)/(1/2) = 1`**（点质量）。 -/
theorem condY_M (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.condY M x y = if x = y then (1 : ℝ) / 2 else 0 := by
  classical
  have h1 : FateV2.Modeling.SCMSemantics.condY M x y
      = ∑ u : Fin 2, (1 : ℝ) / 2 * (if u = x then 1 else 0) * (if u = y then 1 else 0) := rfl
  rw [h1, Fin.sum_univ_two]
  fin_cases x <;> fin_cases y <;> norm_num

/-- **干预律 `doLaw M x y`**：**恒为 `1/2`**（与 `x` 无关）。

**读法**：干预 `do(X = x)` 后，`Y` 仍按 `U` 的分布取值 ——
`1/2` 取 `0`、`1/2` 取 `1`。**⟹ 与观测律截然不同**。 -/
theorem doLaw_M (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.doLaw M x y = (1 : ℝ) / 2 := by
  have h1 : FateV2.Modeling.SCMSemantics.doLaw M x y
      = ∑ u : Fin 2, (1 : ℝ) / 2 * (if u = y then 1 else 0) := rfl
  rw [h1, Fin.sum_univ_two]
  fin_cases y <;> norm_num

/-! ## §3 T3.5 主定理：两者不相等 -/

/-- **T3.5**：**存在 SCM 与 `x, y`，使观测律 ≠ 干预律**。

**🔹 对应清单**：T3.5 的逐字形式化。

**见证**：取 `x = 0`、`y = 1`：
- **观测**：`condY M 0 1 = 0`（因为 `x ≠ y`）
- **干预**：`doLaw M 0 1 = 1/2`
- **⟹ `0 ≠ 1/2`** ✓ -/
theorem t35_observational_ne_interventional :
    ∃ (X Y : Type) (_ : Fintype X) (_ : DecidableEq X)
      (_ : Fintype Y) (_ : DecidableEq Y)
      (M' : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y),
      FateV2.Modeling.SCMSemantics.condY M' x y ≠ FateV2.Modeling.SCMSemantics.doLaw M' x y :=
  ⟨Fin 2, Fin 2, inferInstance, inferInstance, inferInstance, inferInstance,
   M, 0, 1, by rw [condY_M, doLaw_M]; norm_num⟩

/-- **T3.5（更精确）**：见证里两个值的具体数值是 `0` 与 `1/2`。

**⚠ 这比 `≠` 更强** —— 它给出了两条律的**实际数值**。 -/
theorem t35_witness_values :
    FateV2.Modeling.SCMSemantics.condY M 0 1 = 0 ∧ FateV2.Modeling.SCMSemantics.doLaw M 0 1 = (1 : ℝ) / 2 :=
  ⟨by rw [condY_M]; norm_num, by rw [doLaw_M]⟩

/-- **对照：在 `x = y` 处两者数值恰好相等**。

**⚠ 本定理如实登记这个巧合**，以免读者误以为「处处不等」才是 T3.5 的结论。
**而它们的**含义不同**：观测是「联合质量 `1/2`」，干预是「边缘质量 `1/2`」。** -/
theorem t35_coincidence_at_diagonal :
    FateV2.Modeling.SCMSemantics.condY M 0 0 = FateV2.Modeling.SCMSemantics.doLaw M 0 0 := by
  rw [condY_M, doLaw_M]
  norm_num

/-- **归一化后的条件概率**（**更贴近「`P(Y|X=x)`」的原意**）。

**定义**：`condProb M x y := condY M x y / marginalX M x`（**当 `marginalX ≠ 0`**）。

**⚠ 本定义**新增**，因为清单写的是 `P(Y | X=x)`（**归一化概率**），
**而 `condY` 是**联合质量****。 -/
noncomputable def condProb (x y : Fin 2) : ℝ :=
  FateV2.Modeling.SCMSemantics.condY M x y / FateV2.Modeling.SCMSemantics.marginalX M x

/-- **`X = x` 的边缘质量恒为 `1/2`**。 -/
theorem marginalX_M (x : Fin 2) : FateV2.Modeling.SCMSemantics.marginalX M x = (1 : ℝ) / 2 := by
  have h1 : FateV2.Modeling.SCMSemantics.marginalX M x
      = ∑ u : Fin 2, (1 : ℝ) / 2 * (if u = x then 1 else 0) := rfl
  rw [h1, Fin.sum_univ_two]
  fin_cases x <;> norm_num

/-- **T3.5（归一化形式，**最贴近清单原意**）**：
**`P(Y=y | X=x) = 1` 当 `x = y`，`= 0` 否则**；
**而 `P(Y=y | do(X=x))` 的归一化版本恒为 `1/2`（当总质量为 1）**。

**⟹ 两者对 `y = 1, x = 0` 给出 `0 ≠ 1/2`。** -/
theorem t35_normalized :
    condProb 0 0 = 1 ∧ condProb 0 1 = 0 := by
  constructor
  · simp only [condProb, marginalX_M]
    rw [condY_M]; norm_num
  · simp only [condProb, marginalX_M]
    rw [condY_M]; norm_num

end FateV2.Predict.T35
