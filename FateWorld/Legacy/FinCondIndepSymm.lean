import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

-- ⚠⚠ **导入清单的实测记录**（在 Lean 4.33.0-rc1 上逐条验证）：
--
-- | 需要的引理 | **真正所在的模块** |
-- |---|---|
-- | `Finset.sum_mul` / `mul_sum` | `BigOperators.Ring.Finset` |
-- | `Finset.sum_comm` | `BigOperators.Group.Finset.Sigma`（⚠ 只有这个模块提供） |
-- | `ring` | `Mathlib.Tactic.Ring` |
--
-- **⚠ rc1 语法陷阱（实测）**：`∑ a b, f a b`（一次绑定两个指标）
-- **在此版本被拒**，**必须写成 `∑ a, ∑ b, f a b`**。
-- 本文件所有求和均按此写法。

/-! ===========================================================================
  §70  ⭐⭐⭐ **有限条件独立的对称性**（`Fate.FinCondIndepSymm`）

  ## 目标

  在有限三变量联合律 $p : (\alpha \times \beta) \times \gamma \to \mathbb{R}$
  上定义**换位操作** $\mathrm{swap}$（交换前两个坐标 $X$ 与 $Y$，
  **不动条件变量 $Z$**），并证明：

  $$\mathrm{CondIndepFin}\ p \iff \mathrm{CondIndepFin}\,(\mathrm{swap}\ p)$$

  **⟹ 即** $X \perp\!\!\!\perp Y \mid Z$ 与 $Y \perp\!\!\!\perp X \mid Z$
  是**同一个断言** —— 这正是「条件独立」概念的**对称性**。

  ## ⚠ 记号约定（与 `Fate/FiniteCondIndep.lean` 口径一致）

  底层容器是 $(\alpha \times \beta) \times \gamma$，
  **其中 $\gamma$ 读作条件变量 $Z$**，$(\alpha \times \beta)$ 是待条件化的对。
  于是 $p\,((x,y),z)$ 的书写形态与「$(X{=}x, Y{=}y) \mid Z{=}z$」一致。

  ## ⚠ 与既有模块的关系（**本文件是独立复现，便于单独验收**）

  `Fate/FiniteCondIndep.lean`（命名空间 `Fate.FiniteCondIndep`）
  已用 `swapXY` 证过同一结论。**本文件把该结论在独立命名空间
  `Fate.FinCondIndepSymm` 下**重新陈述并证明**（操作名改为 `swap`），
  **不依赖前者** —— 使本文件**可单独编译、单独审计**。

  ## ⚠ 边界（诚实声明）

  - **不做归一化假设、不做正性假设**：下列恒等式对**任意实值** $p$ 成立。
  - **无硬编码**（依作者裁决 Q-1）；**无 `sorry` / `admit` / `axiom`**。
  =========================================================================== -/

namespace Fate

namespace FinCondIndepSymm

open Finset

/-- ⭐⭐⭐ **有限联合律**（定义在 $(\alpha \times \beta) \times \gamma$ 上的实值函数）。

**⚠ 用 `abbrev`**：让类型级展开对 elaborator 透明，
使 `p` 可直接传给期望 `Finset` 求和引理的引理，**免去反复 `show`/`change`**。 -/
abbrev FinJoint (α β γ : Type*) := (α × β) × γ → ℝ

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- ⭐⭐ **$Z$ 的边缘律**（把 $X$ 与 $Y$ 全部边缘化掉）。

$$\mathrm{margZ}\ p\ z := \sum_{x}\sum_{y}\ p\,((x,y),z)$$

**⚠ 求和**必须写成两层**（`∑ x, ∑ y, ...`），
**因 rc1 拒收 `∑ x y, ...`。** -/
noncomputable def margZ (p : FinJoint α β γ) (z : γ) : ℝ :=
  ∑ x, ∑ y, p ((x, y), z)

/-- ⭐⭐ **$(X,Z)$ 的边缘律**（把 $Y$ 边缘化掉）。 -/
noncomputable def margXZ (p : FinJoint α β γ) (x : α) (z : γ) : ℝ :=
  ∑ y, p ((x, y), z)

/-- ⭐⭐ **$(Y,Z)$ 的边缘律**（把 $X$ 边缘化掉）。 -/
noncomputable def margYZ (p : FinJoint α β γ) (y : β) (z : γ) : ℝ :=
  ∑ x, p ((x, y), z)

/-- ⭐⭐⭐ **有限条件独立** $X \perp\!\!\!\perp Y \mid Z$（**乘性形式**）。

$$\forall x\,y\,z,\quad p\,((x,y),z)\cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z$$

**⟹ 为什么用乘性形式**：**不出现除法**，故**在 $\mathrm{margZ}=0$ 处仍有意义**，
**且不需正性/归一化假设** —— 对**任意实值** $p$ 成立。 -/
def CondIndepFin (p : FinJoint α β γ) : Prop :=
  ∀ x y z, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z

/-! ### §70.1 ⭐⭐⭐ **换位操作 `swap`** -/

/-- ⭐⭐⭐ **联合律的 $X$/$Y$ 换位**。

$$\mathrm{swap}\ p\,((y,x),z) := p\,((x,y),z)$$

**⟹ 语义**：把联合律的**前两个坐标**（$X$ 与 $Y$）交换，
**保持条件变量 $Z$（即第三坐标）不变**。

**⚠ 类型**：`swap p : FinJoint β α γ` ——
$\alpha$ 与 $\beta$ **互换**，$\gamma$ **不动**。
**这正是「$Z$ 是条件变量、$X,Y$ 是被条件化的对」的**类型级体现**：
**「对称性」只应交换被条件化的两者，绝不该碰条件变量。** -/
def swap (p : FinJoint α β γ) : FinJoint β α γ :=
  fun q => p ((q.1.2, q.1.1), q.2)

/-- ⭐⭐ **`swap` 是对合**（两次换位回到原状）。

$$\mathrm{swap}\,(\mathrm{swap}\ p) = p$$

**⟹ 这把换位钉成**结构性的对合**，而非临时操作。 -/
@[simp] theorem swap_swap (p : FinJoint α β γ) :
    swap (swap p) = p := by
  funext q
  cases q with
  | mk xy z =>
    cases xy with
    | mk a b => rfl

/-- ⭐⭐ **换位下 $Z$ 的边缘不变**。

$$\mathrm{margZ}\,(\mathrm{swap}\ p) = \mathrm{margZ}\ p$$

**⟹ 意义**：**条件变量的边缘**绝不该**因交换被条件化的两者而改变。** -/
theorem margZ_swap (p : FinJoint α β γ) :
    margZ (swap p) = margZ p := by
  funext z
  unfold margZ swap
  exact Finset.sum_comm

/-- ⭐⭐ **换位下两个交叉边缘互换**：

$$\mathrm{margXZ}\,(\mathrm{swap}\ p) = \mathrm{margYZ}\ p$$

**⟹ 即**：换位后 $X$ 的边缘**恰是原来的 $Y$ 的边缘**。** -/
theorem margXZ_swap (p : FinJoint α β γ) :
    margXZ (swap p) = margYZ p := by
  funext x z
  unfold margXZ swap
  rfl

/-- ⭐⭐ **换位下 $\mathrm{margYZ}$ 与 $\mathrm{margXZ}$ 互换**。 -/
theorem margYZ_swap (p : FinJoint α β γ) :
    margYZ (swap p) = margXZ p := by
  funext y z
  unfold margYZ swap
  rfl

/-! ### §70.2 ⭐⭐⭐ **主定理：条件独立的对称性** -/

/-- ⭐⭐⭐ **条件独立在 $X$/$Y$ 换位下不变**（**本文件的核心交付**）。

$$\mathrm{CondIndepFin}\ p \iff \mathrm{CondIndepFin}\,(\mathrm{swap}\ p)$$

**证明（两个方向，互为镜像）**：

- **$\Rightarrow$**：设 $h : \mathrm{CondIndepFin}\ p$。对任意 $y,x,z$，
  取 $h\,x\,y\,z$，再用三条换位边缘引理
  （`margZ_swap`、`margXZ_swap`、`margYZ_swap`）改写目标，
  **最后用 `mul_comm` 交换乘积顺序**（因换位后左右因子互换）。
- **$\Leftarrow$**：同上，方向相反。

**⚠ 为什么 `mul_comm` 不可省**：乘性等式的两边
$\mathrm{margXZ}\cdot\mathrm{margYZ}$ 与
$\mathrm{margYZ}\cdot\mathrm{margXZ}$ **字面不同** ——
**换位把两个因子**交换了位置**，故需一次交换律对齐。
**这也说明：对称性**不是定义层的显然结论**，而是一条**需要证明的定理**。** -/
theorem condIndepFin_swap (p : FinJoint α β γ) :
    CondIndepFin p ↔ CondIndepFin (swap p) := by
  constructor
  · -- 方向一：`p` 条件独立 ⟹ `swap p` 条件独立。
    intro hp y x z
    have h := hp x y z
    rw [margZ_swap, margXZ_swap, margYZ_swap]
    -- 目标右边为 `margYZ p y z * margXZ p x z`，与 `h` 的右边顺序相反。
    rw [mul_comm (margYZ p y z) (margXZ p x z)]
    exact h
  · -- 方向二：`swap p` 条件独立 ⟹ `p` 条件独立。
    intro hp x y z
    have h := hp y x z
    rw [margZ_swap, margXZ_swap, margYZ_swap,
      mul_comm (margYZ p y z) (margXZ p x z)] at h
    exact h

/-- ⭐⭐ **主定理的推论**：对称也可以写成「反向」形态
（由对合性 `swap_swap` 立即得到）。

$$\mathrm{CondIndepFin}\,(\mathrm{swap}\ p) \iff \mathrm{CondIndepFin}\ p$$

**⟹ 与主定理逻辑等价，此处显式给出以便下游按需取用方向。** -/
theorem condIndepFin_swap_symm (p : FinJoint α β γ) :
    CondIndepFin (swap p) ↔ CondIndepFin p :=
  (condIndepFin_swap p).symm

end FinCondIndepSymm

end Fate
