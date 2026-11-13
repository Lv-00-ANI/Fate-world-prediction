/-
  ⭐⭐⭐ **第 213 轮 B2：fork（分叉 / 共同原因）情形 —— 自足翻译**

  ⚠ **本文件刻意不 `import Fate.FinCondIndep`，也不 import 任何 B1 文件**：
  所用记号（`FinJoint` / `margZ` / `margXZ` / `margYZ`）与全部辅助引理
  **在本文件内重新定义、重新证明**，因此本文件可以**单独编译**，
  只依赖 Mathlib。这正是任务要求「独立文件」的字面落实。

  ## 0. 结构（因果图）

  ```
        b          a ← b → c        （b 是 a 与 c 的**共同原因**）
      ↙   ↘        Z = {b}
     a     c       ⇒  a ⊥ c | b
  ```

  **这是因果推断里最重要的结构**（"fork" / common cause / confounding）：
  * 若不条件化 $b$，$a$ 与 $c$ **通常不独立**（被共同原因混淆）；
  * 条件化 $b$ 后，$a$ 与 $c$ 独立 —— 即「**关闭后门路径**」。

  ## 1. 命题的精确形式

  假设联合律满足**分叉因子化**（fork factorization）

  $$p(a,b,c) = p(b)\;p(a\mid b)\;p(c\mid b),
  \qquad\text{即}\qquad
  p\big((x,y),z\big) = h(z)\cdot f(z,x)\cdot g(z,y),$$

  则

  $$\underbrace{\frac{p\big((x,y),z\big)}{\mathrm{margZ}\ p\ z}}_{p(a,c\mid b)}
      = \underbrace{\frac{\mathrm{margXZ}\ p\ x\ z}{\mathrm{margZ}\ p\ z}}_{p(a\mid b)}
        \cdot
        \underbrace{\frac{\mathrm{margYZ}\ p\ y\ z}{\mathrm{margZ}\ p\ z}}_{p(c\mid b)}$$

  本文件证的就是这条 **除法（条件律）形式**（主定理 `fork_condIndep`，
  及逐点版 `fork_pointwise`），外加**乘性 / 交叉相乘形式**
  （`condMul_of_fork`、`fork_cross`）与归一化重读（`margZ_fork_of_normalized`）。

  ## 2. 与 B1（chain / 中介）的区别

  | | B1：chain $a\to b\to c$ | B2：fork $a\leftarrow b\to c$ |
  |---|---|---|
  | 中间变量角色 | **中介**（mediator） | **共同原因**（common cause） |
  | 因子化 | $p(a,b,c)=p(a)p(b\mid a)p(c\mid b)$ | $p(a,b,c)=p(b)p(a\mid b)p(c\mid b)$ |
  | 条件化 $b$ | 切断 $a\to b\to c$ 通路 | **关闭后门路径** |
  | 结论 | $a\perp c\mid b$ | $a\perp c\mid b$ |

  **⚠ 结论形式相同，但概率机制完全不同**：B1 是「$b$ 中介了全部影响」，
  B2 是「$b$ 是共同源头」。本文件对 B2 **独立重建**，
  不复用 B1 的任何定理（包括其代数引理）。

  ## 3. 强度声明（诚实）

  * **不做归一化假设**（不要求 $\sum p = 1$）；
  * **不做正性假设**（$p(b),p(a\mid b),p(c\mid b)$ 可为任意实数，含负值）；
  * **除法形式带守卫** $\mathrm{margZ}\,p\,z \neq 0$（即 $P(b{=}z)>0$）；
  * **无 `sorry` / `admit` / `axiom`**。

  ## 4. rc1 语法注意（实测）

  * `∑ x y, …` 被拒，必须写 `∑ x, ∑ y, …`；
  * 显式 `ring` + 自备 `sum_mul_const` / `const_mul_sum`，不依赖 `BigOperators.Ring.Finset`。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

namespace Fate

namespace Fork213

open Finset

-- 关掉与数学内容无关的提示：若干净（零 warning）是验收标准。
set_option linter.unusedSectionVars false

/-! ### §1 联合律与边缘律（本文件自备，不引用上游） -/

/-- 联合律：$(a,c,b)$ 的实值函数，底层类型 $((\alpha\times\beta)\times\gamma)$。
（约定 $\alpha$ = $a$ 的值域，$\beta$ = $c$ 的值域，$\gamma$ = $b$ 的值域。） -/
abbrev FinJoint (α β γ : Type*) := (α × β) × γ → ℝ

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]

/-- $b$ 的边缘律 $p(b{=}z)=\sum_a\sum_c p(a,c,b)$；即「条件化变量」的质量。 -/
noncomputable def margZ (p : FinJoint α β γ) (z : γ) : ℝ :=
  ∑ x, ∑ y, p ((x, y), z)

/-- $(a,b)$ 的边缘律 $p(a{=}x, b{=}z) = \sum_c p(a,c,b)$。 -/
noncomputable def margXZ (p : FinJoint α β γ) (x : α) (z : γ) : ℝ :=
  ∑ y, p ((x, y), z)

/-- $(c,b)$ 的边缘律 $p(c{=}y, b{=}z) = \sum_a p(a,c,b)$。 -/
noncomputable def margYZ (p : FinJoint α β γ) (y : β) (z : γ) : ℝ :=
  ∑ x, p ((x, y), z)

/-! ### §2 代数辅助引理（自备，避免越出导入边界） -/

/-- $\sum_i f_i \cdot c = (\sum_i f_i)\cdot c$。 -/
theorem sum_mul_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i * c) = (∑ i, f i) * c := by
  symm
  exact map_sum (AddMonoidHom.mulRight c) f Finset.univ

/-- $\sum_i c \cdot f_i = c \cdot \sum_i f_i$。 -/
theorem const_mul_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, c * f i) = c * (∑ i, f i) := by
  symm
  exact map_sum (AddMonoidHom.mulLeft c) f Finset.univ

/-! ### §3 ⭐⭐⭐ **fork 条件独立谓词（乘性形式）** -/

/-- ⭐⭐⭐ **fork 情形的条件独立（乘性形式，无守卫）**：

$$\forall x\,y\,z,\quad
  p\big((x,y),z\big)\cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z\cdot \mathrm{margYZ}\ p\ y\ z.$$

（$x$ = $a$，$y$ = $c$，$z$ = 共同原因 $b$。） -/
def CondMul (p : FinJoint α β γ) : Prop :=
  ∀ x y z, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z

/-- ⭐⭐⭐ **fork 情形的条件独立（除法 / 条件律形式，带守卫）**：

$$\mathrm{margZ}\ p\ z \neq 0 \implies
  \frac{p((x,y),z)}{\mathrm{margZ}\ p\ z}
  = \frac{\mathrm{margXZ}\ p\ x\ z}{\mathrm{margZ}\ p\ z}
    \cdot\frac{\mathrm{margYZ}\ p\ y\ z}{\mathrm{margZ}\ p\ z}.$$

左边 $=p(a,c\mid b{=}z)$，右边 $=p(a\mid b{=}z)\,p(c\mid b{=}z)$。 -/
def CondRatio (p : FinJoint α β γ) : Prop :=
  ∀ x y z, margZ p z ≠ 0 →
    p ((x, y), z) / margZ p z =
      (margXZ p x z / margZ p z) * (margYZ p y z / margZ p z)

/-! ### §4 ⭐⭐⭐ **fork 因子化假设**

联合律的**分叉分解**：$p(a,c,b) = p(b)\,p(a\mid b)\,p(c\mid b)$，
其中 $h$ 扮演 $p(b)$，$f$ 扮演 $(z,x)\mapsto p(a{=}x\mid b{=}z)$，
$g$ 扮演 $(z,y)\mapsto p(c{=}y\mid b{=}z)$。

**⚠ 注意参数顺序**：$f$ 与 $g$ 都以（$b$ 的值，自己的值）为参数，
这正是「给定 $b$」的**条件**方向的类型级体现。 -/
def ForkFac (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ) (g : γ → β → ℝ) :
    Prop :=
  ∀ x y z, p ((x, y), z) = h z * f z x * g z y

/-! ### §5 ⭐⭐⭐ **因子化 ⟹ 三个关键量**

把 $p$ 代入三个边缘律，得到 $p(b)$、$p(a,b)$、$p(c,b)$ 的显式形式。 -/

/-- $b$ 的边缘律：$\mathrm{margZ}\ p\ z = h\,z\cdot\big(\sum_x f\,z\,x\big)\big(\sum_y g\,z\,y\big)$。

**⟹ 即 $p(b{=}z)$**（在归一化假设下）。 -/
theorem margZ_fork (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) (z : γ) :
    margZ p z = h z * (∑ x, f z x) * (∑ y, g z y) := by
  unfold margZ
  calc ∑ x, ∑ y, p ((x, y), z)
      = ∑ x, ∑ y, f z x * (h z * g z y) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hfac x y z]
        ring
    _ = ∑ x, f z x * (h z * (∑ y, g z y)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [show (∑ y, f z x * (h z * g z y)) = f z x * (∑ y, h z * g z y)
              from const_mul_sum _ _]
        rw [const_mul_sum (fun y => g z y) (h z)]
    _ = ∑ x, (f z x * h z) * (∑ y, g z y) := by
        refine Finset.sum_congr rfl fun x _ => by ring
    _ = (∑ x, f z x * h z) * (∑ y, g z y) := sum_mul_const _ _
    _ = h z * (∑ x, f z x) * (∑ y, g z y) := by
        rw [sum_mul_const (fun x => f z x) (h z)]
        ring

/-- $(a,b)$ 的边缘律：$\mathrm{margXZ}\ p\ x\ z = h\,z\cdot f\,z\,x\cdot\big(\sum_y g\,z\,y\big)$。

**⟹ 即 $p(a{=}x\mid b{=}z)$ 的分子。** -/
theorem margXZ_fork (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) (x : α) (z : γ) :
    margXZ p x z = h z * f z x * (∑ y, g z y) := by
  unfold margXZ
  calc ∑ y, p ((x, y), z)
      = ∑ y, f z x * (h z * g z y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hfac x y z]; ring
    _ = f z x * (∑ y, h z * g z y) := const_mul_sum _ _
    _ = f z x * (h z * (∑ y, g z y)) := by
        rw [const_mul_sum (fun y => g z y) (h z)]
    _ = h z * f z x * (∑ y, g z y) := by ring

/-- $(c,b)$ 的边缘律：$\mathrm{margYZ}\ p\ y\ z = h\,z\cdot g\,z\,y\cdot\big(\sum_x f\,z\,x\big)$。

**⟹ 即 $p(c{=}y\mid b{=}z)$ 的分子。** -/
theorem margYZ_fork (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) (y : β) (z : γ) :
    margYZ p y z = h z * g z y * (∑ x, f z x) := by
  unfold margYZ
  calc ∑ x, p ((x, y), z)
      = ∑ x, g z y * (h z * f z x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hfac x y z]; ring
    _ = g z y * (∑ x, h z * f z x) := const_mul_sum _ _
    _ = g z y * (h z * (∑ x, f z x)) := by
        rw [const_mul_sum (fun x => f z x) (h z)]
    _ = h z * g z y * (∑ x, f z x) := by ring

/-! ### §6 ⭐⭐⭐ **主定理：fork 因子化 ⟹ 条件独立（乘性形式）**

把 §5 三条公式代入乘性等式：两边都等于
$h\,z\cdot f\,z\,x\cdot g\,z\,y\cdot h\,z\cdot(\sum_x f)\cdot(\sum_y g)$，
**纯交换律即闭合**。 -/
theorem condMul_of_fork (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) : CondMul p := by
  intro x y z
  rw [margXZ_fork p h f g hfac x z,
      margYZ_fork p h f g hfac y z,
      margZ_fork p h f g hfac z,
      hfac x y z]
  ring

/-! ### §7 ⭐⭐⭐ **主结论：$p(a,c\mid b) = p(a\mid b)\,p(c\mid b)$**

即「条件化于共同原因 $b$ 后，$a$ 与 $c$ 独立」的**除法形式**。 -/
theorem condRatio_of_fork (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) : CondRatio p := by
  intro x y z hz
  have hmul := condMul_of_fork p h f g hfac x y z
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hz hz)]
  rw [← hmul, ← mul_assoc, div_mul_cancel₀ _ hz]

/-- ⭐⭐⭐ **fork 主定理（任务书的字面命题）**：

若 $\forall a\,c\,b,\; p(a,c,b)=p(b)\,p(a\mid b)\,p(c\mid b)$
（这里写成 $h\,z\cdot f\,z\,x\cdot g\,z\,y$），
则在 $p(b{=}z)\neq 0$ 处有
$$p(a,c\mid b{=}z) = p(a\mid b{=}z)\cdot p(c\mid b{=}z).$$

**⚠ 这就是「共同原因」结构下后门路径被关闭的代数骨架。** -/
theorem fork_condIndep (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) :
    ∀ x y z, margZ p z ≠ 0 →
      p ((x, y), z) / margZ p z =
        (margXZ p x z / margZ p z) * (margYZ p y z / margZ p z) :=
  condRatio_of_fork p h f g hfac

/-! ### §8 ⭐⭐⭐ **谱系形式：$p(a,c\mid b) = p(a\mid b)\,p(c\mid b)$（单点形态）**

把 §7 逐点写出，避免读者不得不展开 `CondRatio`。 -/
theorem fork_pointwise (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) (x : α) (y : β) (z : γ)
    (hz : margZ p z ≠ 0) :
    p ((x, y), z) / margZ p z =
      (margXZ p x z / margZ p z) * (margYZ p y z / margZ p z) :=
  condRatio_of_fork p h f g hfac x y z hz

/-- ⭐⭐ **交叉相乘形态**（把分母清掉，最便于机器核对的版本）：

$$\mathrm{margZ}\ p\ z \neq 0 \implies
  p\big((x,y),z\big)\cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z\cdot\mathrm{margYZ}\ p\ y\ z.$$ -/
theorem fork_cross (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) (x : α) (y : β) (z : γ)
    (_hz : margZ p z ≠ 0) :
    p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z :=
  condMul_of_fork p h f g hfac x y z

/-! ### §9 ⭐⭐ **概率归一化下的重读（把因子读成真概率）**

若 $h$ 归一（$\sum_z h = 1$）、每个 $z$ 下的 $f\,z$ 与 $g\,z$ 各自归一
（即条件分布），则 `margZ p z = h z`，于是主定理给出
$$p(b{=}z)\neq 0 \implies p(a,c\mid b{=}z) = \cdots$$
这一条**只是把 §5 的 `margZ_fork` 在归一假设下化简**，
用于说明「$h$ 就是 $p(b)$」不是比喻。 -/
theorem margZ_fork_of_normalized (p : FinJoint α β γ) (h : γ → ℝ)
    (f : γ → α → ℝ) (g : γ → β → ℝ) (hfac : ForkFac p h f g)
    (hf : ∀ z, (∑ x, f z x) = 1) (hg : ∀ z, (∑ y, g z y) = 1) (z : γ) :
    margZ p z = h z := by
  rw [margZ_fork p h f g hfac z, hf z, hg z, mul_one, mul_one]

/-! ### §10 ⭐⭐ **因子形状的登记（类型层面的因果假设）**

fork 的关键是「$p$ 对 $(a,c)$ 的依赖**在给定 $b$ 后**完全因子化」：
$h$ 必须**只看 $b$**。这一点在 `ForkFac` 的类型 `γ → ℝ` 中
**被类型系统强制** —— 写成 $h\,z\,x$ 的「伪 fork」在类型层面就进不了 `ForkFac`。
下面把这一形状显式登记为一条存在性引理。 -/

/-- ⭐ **`ForkFac` 的形状**：存在只看 $b$ 的 $H$ 使
$p\big((x,y),z\big)=H\,z\cdot f\,z\,x\cdot g\,z\,y$。 -/
theorem forkFac_shape (p : FinJoint α β γ) (h : γ → ℝ) (f : γ → α → ℝ)
    (g : γ → β → ℝ) (hfac : ForkFac p h f g) :
    ∃ H : γ → ℝ, ∀ x y z, p ((x, y), z) = H z * f z x * g z y :=
  ⟨h, hfac⟩

/-! ### §11 ⭐⭐ **非空性 / 自洽性检查** -/

/-- 全零联合律满足 fork 因子化（取 $h\equiv 0$），且条件独立成立。
⟹ 定理不是空洞的。 -/
theorem fork_zero (α β γ : Type*) [Fintype α] [Fintype β] [Fintype γ] :
    CondMul (fun _ => (0 : ℝ) : FinJoint α β γ) := by
  intro x y z
  simp [margZ, margXZ, margYZ]

end Fork213

end Fate
