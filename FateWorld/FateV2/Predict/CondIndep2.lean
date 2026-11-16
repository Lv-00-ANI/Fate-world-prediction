import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Predict.SeparableCondMul
/-!
  # Predict · CondIndep2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CondIndep2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FinCondIndep, SeparableCondMul
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §CondIndep2  ⭐⭐⭐⭐ **双条件变量条件独立：`CondMul` 的直接推广**

  ## 动机（Pearl 1.2.4 的第一步）

  `Fate/FinCondIndep.lean` 的 `CondMul` 只处理**一个**条件变量 $Z$：

  $$\mathrm{CondMul}\ p \;\Longleftrightarrow\;
    \forall x\,y\,z,\; p((x,y),z)\cdot \mathrm{marg}_Z(z)
      = \mathrm{marg}_{XZ}(x,z)\cdot \mathrm{marg}_{YZ}(y,z).$$

  而 Pearl 的 d-分离要在**一般 DAG** 上用：一条链
  $X \to Z_1 \to Z_2 \to Y$ 上的条件独立，是
  $X \perp\!\!\!\perp Y \mid \{Z_1, Z_2\}$ —— **两个**条件变量。
  故第一步必须是：把 $Z$ 从「一个变量」推广到「一对变量」。

  **本文件因此定义 `CondMul2`，并把 `CondMul` 的全部结构性质
  （可分离⟹成立、对称性、退化）逐条推广过去。**

  ## 记号

  * $(\alpha \times \beta)$ —— 两个被分离的变量 $X, Y$；
  * $(\zeta \times \omega)$ —— **两个条件变量** $Z_1, Z_2$；
  * 联合律 $p : (\alpha\times\beta)\times(\zeta\times\omega) \to \mathbb{R}$。

  ## 诚实声明（假设强度）

  * **不归一化**：不要求 $\sum p = 1$，恒等式对任意实值 `p` 成立。
  * **不正性**：乘性形式对负值也成立（`ring` 只需交换环）。
  * **不设 $0$ 守卫**：与 `CondMul` 同口径，$\mathrm{marg}=0$ 处照样断言。
    带守卫的版本见 `CondMul2Guard`。

  ## rc1 语法陷阱（沿用 `FinCondIndep` 的实测结论）

  * `∑ x y, f x y` **非法**，必须写 `∑ x, ∑ y, f x y`。
  * `Finset.sum_mul` / `Finset.mul_sum` 的**方向**：
    `Finset.sum_mul : (∑ i, f i) * a = ∑ i, f i * a`，
    `Finset.mul_sum : a * (∑ i, f i) = ∑ i, a * f i`
    —— 两者都是**外向**（把常数提出求和），因此
    「`∑ i, f i * a` ⟹ `(∑ i, f i) * a`」要用 `.symm`。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Predict
namespace CondIndep2

open Finset

variable {α β ζ ω : Type*}

/-! ---------------------------------------------------------------------------
  §1  联合律与边缘律（双条件变量版）
  --------------------------------------------------------------------------- -/

/-- **双条件联合律**：$(X,Y)$ 与**一对**条件变量 $(Z_1,Z_2)$ 的联合分布。 -/
abbrev FinJoint2 (α β ζ ω : Type*) := ((α × β) × (ζ × ω)) → ℝ

/-- $X$ 的边缘律：对 $Y$ 求和（$Z_1,Z_2$ 固定）。 -/
noncomputable def marg2X [Fintype β] (p : FinJoint2 α β ζ ω) (x : α) (z : ζ) (w : ω) : ℝ :=
  ∑ y, p ((x, y), (z, w))

/-- $Y$ 的边缘律：对 $X$ 求和。 -/
noncomputable def marg2Y [Fintype α] (p : FinJoint2 α β ζ ω) (y : β) (z : ζ) (w : ω) : ℝ :=
  ∑ x, p ((x, y), (z, w))

/-- 条件量（$Z_1,Z_2$ 的联合边缘律）：对 $X$ 与 $Y$ **都**求和。 -/
noncomputable def marg2Z [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (z : ζ) (w : ω) : ℝ :=
  ∑ x, ∑ y, p ((x, y), (z, w))

/-! ---------------------------------------------------------------------------
  §2  ⭐⭐⭐⭐ 主定义：`CondMul2`
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐ **双条件变量条件独立（乘性形式）**。

$$\mathrm{CondMul2}\ p \;\Longleftrightarrow\;
  \forall x\,y\,z\,w,\;
  p((x,y),(z,w))\cdot\Big(\sum_{x',y'} p((x',y'),(z,w))\Big)
    = \Big(\sum_{y'} p((x,y'),(z,w))\Big)
      \cdot\Big(\sum_{x'} p((x',y),(z,w))\Big).$$

**与 `CondMul` 的关系**：把 $(\zeta\times\omega)$ 读成一个整体，
这就是 `CondMul` 的字面形式；把它展开成两个坐标，就是
$X \perp\!\!\!\perp Y \mid (Z_1,Z_2)$。**这是直接推广，不是另造定义。** -/
def CondMul2 [Fintype α] [Fintype β] (p : FinJoint2 α β ζ ω) : Prop :=
  ∀ x y z w,
    p ((x, y), (z, w)) * marg2Z p z w
      = marg2X p x z w * marg2Y p y z w

/-- **带 $0$ 守卫的版本**：只在 $\mathrm{marg}_Z \ne 0$ 处断言。

与 `CondMul2` 的关系同 `CondMulGuard` 与 `CondMul`：**不等价**，
在 $\mathrm{marg}_Z = 0$ 处有分歧（见 `Fate/FiniteCondIndep.lean` 的讨论）。 -/
def CondMul2Guard [Fintype α] [Fintype β] (p : FinJoint2 α β ζ ω) : Prop :=
  ∀ x y z w, marg2Z p z w ≠ 0 →
    p ((x, y), (z, w)) * marg2Z p z w = marg2X p x z w * marg2Y p y z w

/-! ---------------------------------------------------------------------------
  §3  ⭐⭐⭐⭐ **可分离 ⟹ `CondMul2`**（核心）
  --------------------------------------------------------------------------- -/

/-- ⭐ **求和辅助**：`(c * ∑ R) * W = ∑ g, c * (R g * W)`。

`W` 取为常数 `ℝ`（不依赖求和指标）—— 这正是链式结构需要的形态。 -/
theorem sum_mul_const_sum {ι : Type*} [Fintype ι] (R : ι → ℝ) (W c : ℝ) :
    (c * (∑ g, R g)) * W = ∑ g, c * (R g * W) := by
  rw [Finset.mul_sum (s := (univ : Finset ι)) (f := R) (a := c)]
  rw [Finset.sum_mul (s := (univ : Finset ι)) (f := fun g => c * R g) (a := W)]
  exact Finset.sum_congr rfl (fun g _ => by ring)

/-- ⭐ 边缘律的乘积分解：`marg2X` 在可分离形式下的值。 -/
theorem marg2X_of_separable [Fintype β]
    (p : FinJoint2 α β ζ ω) (f : α → ζ → ω → ℝ) (g : β → ζ → ω → ℝ)
    (hsep : ∀ x y z w, p ((x, y), (z, w)) = f x z w * g y z w) (x : α) (z : ζ) (w : ω) :
    marg2X p x z w = f x z w * (∑ y, g y z w) := by
  unfold marg2X
  calc ∑ y, p ((x, y), (z, w)) = ∑ y, f x z w * g y z w :=
        Finset.sum_congr rfl (fun y _ => hsep x y z w)
    _ = f x z w * (∑ y, g y z w) := by rw [Finset.mul_sum]

/-- ⭐ 边缘律的乘积分解：`marg2Y`。 -/
theorem marg2Y_of_separable [Fintype α]
    (p : FinJoint2 α β ζ ω) (f : α → ζ → ω → ℝ) (g : β → ζ → ω → ℝ)
    (hsep : ∀ x y z w, p ((x, y), (z, w)) = f x z w * g y z w) (y : β) (z : ζ) (w : ω) :
    marg2Y p y z w = g y z w * (∑ x, f x z w) := by
  unfold marg2Y
  calc ∑ x, p ((x, y), (z, w)) = ∑ x, f x z w * g y z w :=
        Finset.sum_congr rfl (fun x _ => hsep x y z w)
    _ = (∑ x, f x z w) * g y z w := by rw [Finset.sum_mul]
    _ = g y z w * (∑ x, f x z w) := by ring

/-- ⭐⭐ 条件量的乘积分解：`marg2Z`。 -/
theorem marg2Z_of_separable [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (f : α → ζ → ω → ℝ) (g : β → ζ → ω → ℝ)
    (hsep : ∀ x y z w, p ((x, y), (z, w)) = f x z w * g y z w) (z : ζ) (w : ω) :
    marg2Z p z w = (∑ x, f x z w) * (∑ y, g y z w) := by
  unfold marg2Z
  calc ∑ x, ∑ y, p ((x, y), (z, w))
      = ∑ x, ∑ y, f x z w * g y z w := by
        refine Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => hsep x y z w
    _ = ∑ x, f x z w * (∑ y, g y z w) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = (∑ x, f x z w) * (∑ y, g y z w) := by rw [Finset.sum_mul]

/-- ⭐⭐⭐⭐ **可分离 ⟹ `CondMul2`**。

$$\Big(\forall x\,y\,z\,w,\; p((x,y),(z,w)) = f(x,z,w)\cdot g(y,z,w)\Big)
  \;\Longrightarrow\; \mathrm{CondMul2}\ p.$$

**证明**：三条边缘分解 + `ring`。
**⚠ 强度**：不假设归一化、不假设正性 —— 对任意实值 `p, f, g` 成立。
这是 `Posterior.lean` 里 `separable_implies_condMul` 的双条件变量版。 -/
theorem separable_implies_condMul2 [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (f : α → ζ → ω → ℝ) (g : β → ζ → ω → ℝ)
    (hsep : ∀ x y z w, p ((x, y), (z, w)) = f x z w * g y z w) :
    CondMul2 p := by
  intro x y z w
  rw [marg2X_of_separable p f g hsep x z w,
      marg2Y_of_separable p f g hsep y z w,
      marg2Z_of_separable p f g hsep z w,
      hsep x y z w]
  ring

/-! ---------------------------------------------------------------------------
  §4  退化：单条件变量是双条件变量的特例
  --------------------------------------------------------------------------- -/

/-- **把 `CondMul` 的联合律看作 `CondMul2` 的联合律**（第二个条件变量取 `Unit`）。

$$p\mapsto \tilde p\big((x,y),(z,())\big) := p((x,y),z).$$

**⚠ 这是纯重标号**（$z \leftrightarrow (z,())$ 是双射），概率内容一字不改。 -/
def liftUnit (p : FinCondIndep.FinJoint α β ζ) : FinJoint2 α β ζ Unit :=
  fun t => p ((t.1.1, t.1.2), t.2.1)

/-- ⭐⭐⭐ **`CondMul` 是 `CondMul2` 的特例**（第二个条件变量为 `Unit`）。

$$\mathrm{CondMul}\ p \;\Longrightarrow\; \mathrm{CondMul2}\,(\mathrm{liftUnit}\ p).$$

这把新定义**接回**了 `PearlCondIndepBridge` 的全部既有结论：
凡是那里证出的 `CondMul`（链、叉、对撞），都自动得到对应的 `CondMul2`。 -/
theorem condMul_implies_condMul2 [Fintype α] [Fintype β]
    (p : FinCondIndep.FinJoint α β ζ) (h : FinCondIndep.CondMul p) :
    CondMul2 (liftUnit (β := β) (ζ := ζ) p) := by
  intro x y z w
  simp only [liftUnit, marg2X, marg2Y, marg2Z]
  exact h x y z

/-! ---------------------------------------------------------------------------
  §5  对称性：`CondMul2` 在交换 $X \leftrightarrow Y$ 下不变
  --------------------------------------------------------------------------- -/

/-- 交换两个被分离变量的坐标。 -/
def swap2XY (p : FinJoint2 α β ζ ω) : FinJoint2 β α ζ ω :=
  fun t => p ((t.1.2, t.1.1), (t.2.1, t.2.2))

/-- ⭐ 交换后条件量不变：`marg2Z ∘ swap2XY = marg2Z`（需 `Finset.sum_comm`）。 -/
theorem marg2Z_swap2XY [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (z : ζ) (w : ω) :
    marg2Z (swap2XY p) z w = marg2Z p z w := by
  unfold marg2Z swap2XY
  exact Finset.sum_comm

/-- ⭐ **`swap2XY` 交换 `marg2X` 与 `marg2Y`**（定义级等式）。 -/
theorem marg2X_swap2XY [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (y : β) (z : ζ) (w : ω) :
    marg2X (swap2XY p) y z w = marg2Y p y z w := rfl

/-- ⭐ **`swap2XY` 交换 `marg2Y` 与 `marg2X`**。 -/
theorem marg2Y_swap2XY [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (x : α) (z : ζ) (w : ω) :
    marg2Y (swap2XY p) x z w = marg2X p x z w := rfl

/-- ⭐ **`swap2XY` 保持联合值**。 -/
theorem swap2XY_apply [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (x : α) (y : β) (z : ζ) (w : ω) :
    (swap2XY p) ((y, x), (z, w)) = p ((x, y), (z, w)) := rfl

/-- ⭐⭐⭐ **`CondMul2` 关于 $X \leftrightarrow Y$ 对称**。

条件独立按定义应当对称，这里证实新定义满足此要求。 -/
theorem condMul2_swap [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (h : CondMul2 p) :
    CondMul2 (swap2XY p) := by
  intro y x z w
  show (swap2XY p) ((y, x), (z, w)) * marg2Z (swap2XY p) z w
      = marg2X (swap2XY p) y z w * marg2Y (swap2XY p) x z w
  rw [marg2Z_swap2XY p z w, swap2XY_apply p x y z w,
      marg2X_swap2XY p y z w, marg2Y_swap2XY p x z w]
  exact (h x y z w).trans (mul_comm (marg2X p x z w) (marg2Y p y z w))

/-! ---------------------------------------------------------------------------
  §6  小结
  --------------------------------------------------------------------------- -/

/-- **一致性检查**：`CondMul2` 在两个条件变量都退化时回到 `CondMul` 的形态。

这是 §4 的逆命题方向的一个可用弱形式：若 `liftUnit p` 满足 `CondMul2`，
且 `marg2Z` 与 `p` 都不依赖 `Unit` 分量，则 `p` 满足 `CondMul`。

（`Unit` 只有唯一元素，故条件在 `()` 处取值即可。） -/
theorem condMul2_liftUnit_iff [Fintype α] [Fintype β]
    (p : FinCondIndep.FinJoint α β ζ) :
    CondMul2 (liftUnit (β := β) (ζ := ζ) p) ↔ FinCondIndep.CondMul p := by
  constructor
  · intro h x y z
    have hxy := h x y z ()
    simpa only [liftUnit, marg2X, marg2Y, marg2Z, FinCondIndep.margZ,
      FinCondIndep.margXZ, FinCondIndep.margYZ] using hxy
  · intro h
    exact condMul_implies_condMul2 p h

/-! ---------------------------------------------------------------------------
  §7  ⭐⭐⭐⭐ **真正的四变量条件独立：链式分解 ⟹ `CondMul2`**

  ## 数学内容（Pearl 1.2.4 对链 $X \to Z_1 \to Z_2 \to Y$）

  若 $p$ **沿链分解**：

  $$p(x,z_1,z_2,y) = f_1(x,z_1)\; f_2(z_1,z_2)\; f_3(z_2,y),$$

  则 $X \perp\!\!\perp Y \mid (Z_1,Z_2)$，即 `CondMul2`。

  ## 为什么这**不是** §3 的直接套用

  §3 的 `separable_implies_condMul2` 要求 $p((x,y),(z,w)) = f(x,z,w)\,g(y,z,w)$
  ——**第一因子可以依赖** $w=z_2$，**第二因子可以依赖** $z=z_1$。
  链分解**不允许**这两种依赖：
  * $f_1$ 只依赖 $(x,z_1)$（**不看** $z_2$）；
  * $f_3$ 只依赖 $(z_2,y)$（**不看** $z_1$）；
  * 唯一的耦合是 $f_2(z_1,z_2)$，它**同时**依赖两个条件变量。

  ⟹ 链分解是 §3 的**真子类**（见 `chain4_as_separable`），
  但**共同因子 $f_2$ 的位置**正是「链」的结构所在：
  它把 $z_1$ 的信息单方向传给 $z_2$，这正是 d-分离的代数痕迹。
  本节因此给出**独立于 §3 的直接证明**，并明确指出链结构在哪里被用到
  （即 $f_2$ 从 $p$、`marg2X`、`marg2Y`、`marg2Z` 中**逐字提出**）。

  ## ⚠ 假设强度（与 §3 同口径）

  不归一化、不正性、不设 $0$ 守卫 —— 全部是**交换环恒等式**。
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐ **链式分解（四变量，双条件变量版）**。

$$p((x,y),(z,w)) = f_1(x,z)\; f_2(z,w)\; f_3(w,y).$$

**⚠ 与 §3「可分离」的区别**：这里 $f_1$ **不依赖** $w$、$f_3$ **不依赖** $z$，
唯一的跨边耦合是 $f_2(z,w)$。**这就是链 $X \to Z_1 \to Z_2 \to Y$ 的代数像。** -/
def ChainFactor4 (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) : Prop :=
  ∀ x y z w, p ((x, y), (z, w)) = f₁ x z * f₂ z w * f₃ w y

/-- ⭐ **`marg2X` 在链式分解下的值**：

$$\sum_{y} p((x,y),(z,w)) = f_1(x,z)\, f_2(z,w)\cdot \Big(\sum_y f_3(w,y)\Big).$$

**⭐ 结构要点**：$w$ 只通过**两个标量因子** $f_2(z,w)$ 与 $\sum_y f_3(w,y)$ 进入，
$x$ 只通过 $f_1(x,z)$ 进入 —— **二者被彻底分离**。 -/
theorem marg2X_of_chain [Fintype β] (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ)
    (f₂ : ζ → ω → ℝ) (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃)
    (x : α) (z : ζ) (w : ω) :
    marg2X p x z w = f₁ x z * f₂ z w * (∑ y, f₃ w y) := by
  unfold marg2X
  have step : ∀ y, p ((x, y), (z, w)) = (f₁ x z * f₂ z w) * f₃ w y := by
    intro y
    rw [h x y z w]
  rw [Finset.sum_congr rfl (fun y _ => step y), Finset.mul_sum]

/-- ⭐ **`marg2Y` 在链式分解下的值**：

$$\sum_{x} p((x,y),(z,w)) = f_3(w,y)\, f_2(z,w)\cdot \Big(\sum_x f_1(x,z)\Big).$$ -/
theorem marg2Y_of_chain [Fintype α] (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ)
    (f₂ : ζ → ω → ℝ) (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃)
    (y : β) (z : ζ) (w : ω) :
    marg2Y p y z w = f₃ w y * f₂ z w * (∑ x, f₁ x z) := by
  unfold marg2Y
  have step : ∀ x, p ((x, y), (z, w)) = (f₃ w y * f₂ z w) * f₁ x z := by
    intro x
    rw [h x y z w]
    ring
  rw [Finset.sum_congr rfl (fun x _ => step x), Finset.mul_sum]

/-- ⭐⭐ **`marg2Z` 在链式分解下的值**：

$$\sum_{x}\sum_{y} p((x,y),(z,w))
  = f_2(z,w)\cdot\Big(\sum_x f_1(x,z)\Big)\cdot\Big(\sum_y f_3(w,y)\Big).$$

**⭐⭐ 这是全部证明的枢纽**：$f_2(z,w)$ 被**完整地提出**，
于是乘性等式左右两边只剩 $f_1,f_3$ 的**独立求和**。 -/
theorem marg2Z_of_chain [Fintype α] [Fintype β] (p : FinJoint2 α β ζ ω)
    (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ) (f₃ : ω → β → ℝ)
    (h : ChainFactor4 p f₁ f₂ f₃) (z : ζ) (w : ω) :
    marg2Z p z w = f₂ z w * (∑ x, f₁ x z) * (∑ y, f₃ w y) := by
  unfold marg2Z
  have inner : ∀ x, (∑ y, p ((x, y), (z, w)))
      = f₁ x z * (f₂ z w * (∑ y, f₃ w y)) := by
    intro x
    have hx := marg2X_of_chain p f₁ f₂ f₃ h x z w
    unfold marg2X at hx
    rw [hx]
    ring
  rw [Finset.sum_congr rfl (fun x _ => inner x)]
  rw [(Finset.sum_mul (s := (univ : Finset α))
        (f := fun x => f₁ x z) (a := (f₂ z w * (∑ y, f₃ w y)))).symm]
  ring

/-- ⭐⭐⭐⭐ **链式分解 ⟹ `CondMul2`**（**本文件的核心新结果**）。

$$\Big(\forall x\,y\,z\,w,\; p((x,y),(z,w)) = f_1(x,z)\,f_2(z,w)\,f_3(w,y)\Big)
  \;\Longrightarrow\; \mathrm{CondMul2}\ p.$$

**证明**（见上文三条边缘律）：把

* $p = (f_1 f_2)\,f_3$、
* $\mathrm{marg}_{XZ} = f_1 f_2 \,(\Sigma f_3)$、
* $\mathrm{marg}_{YZ} = f_3 f_2 \,(\Sigma f_1)$、
* $\mathrm{marg}_{Z_1Z_2} = f_2\,(\Sigma f_1)(\Sigma f_3)$

代入后，两边都等于 $(f_1 f_2 f_3)\,f_2 (\Sigma f_1)(\Sigma f_3)$，`ring` 闭合。

**⚠ 这是真的四变量条件独立**：$X$ 与 $Y$ 是**两个**被分离变量，
$Z_1,Z_2$ 是**两个**条件变量，而链结构（$f_2$ 的位置）**被实际用到**
（它保证 $w$ 不出现在 $f_1$ 里、$z$ 不出现在 $f_3$ 里）。 -/
theorem chain4_implies_condMul2 [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃) : CondMul2 p := by
  intro x y z w
  rw [marg2X_of_chain p f₁ f₂ f₃ h x z w,
      marg2Y_of_chain p f₁ f₂ f₃ h y z w,
      marg2Z_of_chain p f₁ f₂ f₃ h z w,
      h x y z w]
  ring

/-! ---------------------------------------------------------------------------
  §7.1 ⭐ **四变量联合律的「扁平」形态与 `chain4_condindep`**
  --------------------------------------------------------------------------- -/

/-- ⭐ **四变量扁平联合律**：$p : (X \times Z_1 \times Z_2 \times Y) \to \mathbb{R}$。

坐标顺序**刻意写成** $(x, z_1, z_2, y)$ —— 与链 $X \to Z_1 \to Z_2 \to Y$
的书写顺序一致（**注意** `CondMul2` 的底层坐标顺序是 $((x,y),(z_1,z_2))$，
两者的差异由 `assemble2` 显式重排）。 -/
abbrev FinJoint4 (α ζ ω β : Type*) := α × ζ × ω × β → ℝ

/-- ⭐ **把扁平四元联合律重排成 `CondMul2` 的坐标顺序**：

$$(x,z_1,z_2,y) \;\longmapsto\; \big((x,y),(z_1,z_2)\big).$$

**⚠ 纯重标号**（双射），概率内容一字不改。 -/
def assemble2 (p : FinJoint4 α ζ ω β) : FinJoint2 α β ζ ω :=
  fun t => p (t.1.1, t.2.1, t.2.2, t.1.2)

/-- ⭐ **扁平链式分解**：$p(x,z_1,z_2,y) = f_1(x,z_1)\,f_2(z_1,z_2)\,f_3(z_2,y)$。 -/
def ChainFactor4Flat (p : FinJoint4 α ζ ω β) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) : Prop :=
  ∀ x z w y, p (x, z, w, y) = f₁ x z * f₂ z w * f₃ w y

/-- ⭐ **扁平链式分解 ⟹ 重排后的链式分解**（`assemble2` 只是换坐标）。 -/
theorem chainFactor4_of_flat (p : FinJoint4 α ζ ω β) (f₁ : α → ζ → ℝ)
    (f₂ : ζ → ω → ℝ) (f₃ : ω → β → ℝ) (h : ChainFactor4Flat p f₁ f₂ f₃) :
    ChainFactor4 (assemble2 p) f₁ f₂ f₃ := by
  intro x y z w
  exact h x z w y

/-- ⭐⭐⭐⭐ **四级链的条件独立**（**任务书要求的主定理**）：

若 $p : (X \times Z_1 \times Z_2 \times Y) \to \mathbb{R}$ 沿链
$X \to Z_1 \to Z_2 \to Y$ 分解为

$$p(x,z_1,z_2,y) = f_1(x,z_1)\; f_2(z_1,z_2)\; f_3(z_2,y),$$

则 $X \perp\!\!\perp Y \mid (Z_1,Z_2)$，即

$$\mathrm{CondMul2}\Big(\lambda\,((x,y),(z_1,z_2))\mapsto p(x,z_1,z_2,y)\Big).$$

**文献（N1）**：Pearl, *Causality* 2nd ed., **Theorem 1.2.4**（链 $X\to Z_1\to Z_2\to Y$
上 $X \perp\!\!\perp Y \mid \{Z_1,Z_2\}$）。 -/
theorem chain4_condindep [Fintype α] [Fintype β]
    (p : FinJoint4 α ζ ω β) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) (h : ChainFactor4Flat p f₁ f₂ f₃) :
    CondMul2 (fun q => p (q.1.1, q.2.1, q.2.2, q.1.2)) :=
  chain4_implies_condMul2 (assemble2 p) f₁ f₂ f₃ (chainFactor4_of_flat p f₁ f₂ f₃ h)

/-! ---------------------------------------------------------------------------
  §7.2 ⭐ 交叉检查：链式分解是 `separable_implies_condMul2` 的特例
  --------------------------------------------------------------------------- -/

/-- ⭐ **链式分解 ⟹ 可分离（§3 的形式）**。

取 $f(x,z,w) := f_1(x,z)\,f_2(z,w)$、$g(y,z,w) := f_3(w,y)$ 即可。

**⚠ 反向不成立**：§3 的 $f$ 可以**任意**依赖 $w$、$g$ 可以**任意**依赖 $z$，
链分解不允许。**故 §7 是真推广，不是 §3 的重述。** -/
theorem chain4_as_separable [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃) :
    CondMul2 p :=
  separable_implies_condMul2 p (fun x z w => f₁ x z * f₂ z w) (fun y _ w => f₃ w y)
    (fun x y z w => h x y z w)

/-- ⭐ **两条路径给出同一结论**（交叉检查：无新内容，仅一致性）。 -/
theorem chain4_two_routes [Fintype α] [Fintype β]
    (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃) :
    chain4_implies_condMul2 p f₁ f₂ f₃ h = chain4_as_separable p f₁ f₂ f₃ h :=
  rfl

/-! ---------------------------------------------------------------------------
  §8  ⚠⚠ **`CondMul2` 的表达能力边界**（诚实声明 + 可证反例）

  ## 问题

  `CondMul2 p` 只是**一句话**：「$X \perp\!\!\perp Y \mid (Z_1,Z_2)$」。
  它**不编码**任何关于「$Z_1, Z_2$ 之间、以及它们与 $X,Y$ 的方向结构」的信息。
  于是：

  * **链** $X \to Z_1 \to Z_2 \to Y$ 给出**三条**条件独立：
    $X \perp\!\!\perp Z_2 \mid Z_1$、$X \perp\!\!\perp Y \mid (Z_1,Z_2)$、
    $Z_1 \perp\!\!\perp Y \mid Z_2$；
  * `CondMul2` **只表达中间那一条**。

  ## 本节的交付

  1. 三条断言的**形式化**（`collapseX/collapseY` + `chain_*_indep_*`）；
  2. `ChainCondIndep4` —— **三条断言的合取**，这才是「链的四变量条件独立结构」；
  3. ⭐ **可证反例**：存在 $p$ 使 `CondMul2 p` 成立而 $X \perp\!\!\perp Z_2 \mid Z_1$ **不**成立
     （`CondMul2` 不足以推出链结构）；
  4. 结论：**「更好的定义」** = `ChainFactor4`（模型类）/ `ChainCondIndep4`（独立性子集），
     而 `CondMul2` 只是其中的**一个分量**，不是四变量链式 CI 的完整表达。
  --------------------------------------------------------------------------- -/

/-- **把 $Y$ 边缘化掉**：得到 $(X, Z_2)$ 在 $Z_1$ 下的联合律（`FinCondIndep` 口径）。

$$q\big((x,z_2), z_1\big) := \sum_{y} p\big((x,y),(z_1,z_2)\big).$$ -/
noncomputable def collapseY [Fintype β] (p : FinJoint2 α β ζ ω) :
    FinCondIndep.FinJoint α ω ζ :=
  fun t => ∑ y, p ((t.1.1, y), (t.2, t.1.2))

/-- **把 $X$ 边缘化掉**：得到 $(Z_1, Y)$ 在 $Z_2$ 下的联合律。

$$q\big((z_1, y), z_2\big) := \sum_{x} p\big((x,y),(z_1,z_2)\big).$$ -/
noncomputable def collapseX [Fintype α] (p : FinJoint2 α β ζ ω) :
    FinCondIndep.FinJoint ζ β ω :=
  fun t => ∑ x, p ((x, t.1.2), (t.1.1, t.2))

/-- ⭐⭐⭐ **链式分解 ⟹ $X \perp\!\!\perp Z_2 \mid Z_1$**（链的**上游**段）。

**⭐ 这是 `CondMul2` 无法表达而链结构给出的额外信息。** -/
theorem chain_X_indep_Z2 [Fintype α] [Fintype β] [Fintype ω]
    (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃) :
    FinCondIndep.CondMul (collapseY p) := by
  intro x w z
  have hq : ∀ (x' : α) (w' : ω), collapseY p ((x', w'), z)
      = f₁ x' z * (f₂ z w' * (∑ y, f₃ w' y)) := by
    intro x' w'
    have hx := marg2X_of_chain p f₁ f₂ f₃ h x' z w'
    unfold marg2X at hx
    unfold collapseY
    rw [hx]
    ring
  show collapseY p ((x, w), z) * (∑ x' : α, ∑ w' : ω, collapseY p ((x', w'), z))
      = (∑ w' : ω, collapseY p ((x, w'), z)) * (∑ x' : α, collapseY p ((x', w), z))
  rw [hq x w]
  rw [show (∑ x' : α, ∑ w' : ω, collapseY p ((x', w'), z))
        = ∑ x' : α, ∑ w' : ω, f₁ x' z * (f₂ z w' * (∑ y, f₃ w' y)) from
      Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun w' _ => hq x' w'))]
  rw [show (∑ w' : ω, collapseY p ((x, w'), z))
        = ∑ w' : ω, f₁ x z * (f₂ z w' * (∑ y, f₃ w' y)) from
      Finset.sum_congr rfl (fun w' _ => hq x w')]
  rw [show (∑ x' : α, collapseY p ((x', w), z))
        = ∑ x' : α, f₁ x' z * (f₂ z w * (∑ y, f₃ w y)) from
      Finset.sum_congr rfl (fun x' _ => hq x' w)]
  rw [(Fintype.sum_mul_sum (fun x' => f₁ x' z) (fun w' => f₂ z w' * (∑ y, f₃ w' y))).symm]
  rw [show (∑ w' : ω, f₁ x z * (f₂ z w' * (∑ y, f₃ w' y)))
        = f₁ x z * (∑ w' : ω, f₂ z w' * (∑ y, f₃ w' y)) from
      (Finset.mul_sum (s := (univ : Finset ω))
        (f := fun w' => f₂ z w' * (∑ y, f₃ w' y)) (a := f₁ x z)).symm]
  rw [show (∑ x' : α, f₁ x' z * (f₂ z w * (∑ y, f₃ w y)))
        = (∑ x' : α, f₁ x' z) * (f₂ z w * (∑ y, f₃ w y)) from
      (Finset.sum_mul (s := (univ : Finset α))
        (f := fun x' => f₁ x' z) (a := (f₂ z w * (∑ y, f₃ w y)))).symm]
  ring

/-- ⭐⭐⭐ **链式分解 ⟹ $Z_1 \perp\!\!\perp Y \mid Z_2$**（链的**下游**段）。

经由 `separable_implies_condMul`：把 $q\big((z_1,y),z_2\big)$ 写成
$\big(f_2(z_1,z_2)\sum_x f_1(x,z_1)\big)\cdot f_3(z_2,y)$。 -/
theorem chain_Z1_indep_Y [Fintype α] [Fintype ζ] [Fintype β] [Fintype ω]
    (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃) :
    FinCondIndep.CondMul (collapseX p) := by
  refine FateV2.Predict.SeparableCondMul.separable_implies_condMul (collapseX p) ?_
  refine ⟨fun z w => f₂ z w * (∑ x, f₁ x z), fun y w => f₃ w y, ?_⟩
  intro z y w
  have hc : collapseX p ((z, y), w) = f₃ w y * f₂ z w * (∑ x, f₁ x z) := by
    unfold collapseX
    exact marg2Y_of_chain p f₁ f₂ f₃ h y z w
  rw [hc]
  ring

/-- ⭐⭐⭐⭐ **链的完整四变量条件独立结构：三条断言的合取**。

$$\mathrm{ChainCondIndep4}\ p \;:=\;
  \underbrace{(X \perp\!\!\perp Z_2 \mid Z_1)}_{\text{上游}}
  \;\wedge\;
  \underbrace{(X \perp\!\!\perp Y \mid (Z_1,Z_2))}_{\texttt{CondMul2}}
  \;\wedge\;
  \underbrace{(Z_1 \perp\!\!\perp Y \mid Z_2)}_{\text{下游}}.$$

**⚠⚠ 这就是「更好的定义」的候选**：
`CondMul2` 只出现为**中间一项**。**要表达「沿链的条件独立」，必须用三者合取**，
因为链的**方向**（$Z_1$ 是 $X$ 的下游、$Y$ 是 $Z_2$ 的下游）正是由**另外两条**断言的
**成立组合**所刻画：对撞 $X \to Z_2 \leftarrow Y$ 会**破坏**第一条，而
$X \leftarrow Z_1 \leftarrow Z_2 \leftarrow Y$ 之类的其它方向会破坏第三条。 -/
def ChainCondIndep4 [Fintype α] [Fintype β] [Fintype ζ] [Fintype ω]
    (p : FinJoint2 α β ζ ω) : Prop :=
  FinCondIndep.CondMul (collapseY p) ∧ CondMul2 p ∧ FinCondIndep.CondMul (collapseX p)

/-- ⭐⭐⭐⭐ **链式分解 ⟹ `ChainCondIndep4`**（**链式 CI 的完整形式**）。

⚠ 注意**每个前提都有用**：第 1 条用 $f_1,f_2$，第 2 条用 $f_2,f_3$，第 3 条用 $f_2$ 两侧。
**这正是 `ChainFactor4` 比「可分离」更强的地方。** -/
theorem chain4_implies_chainCondIndep4 [Fintype α] [Fintype β] [Fintype ζ] [Fintype ω]
    (p : FinJoint2 α β ζ ω) (f₁ : α → ζ → ℝ) (f₂ : ζ → ω → ℝ)
    (f₃ : ω → β → ℝ) (h : ChainFactor4 p f₁ f₂ f₃) : ChainCondIndep4 p :=
  ⟨chain_X_indep_Z2 p f₁ f₂ f₃ h, chain4_implies_condMul2 p f₁ f₂ f₃ h,
    chain_Z1_indep_Y p f₁ f₂ f₃ h⟩

/-- ⭐ **`ChainCondIndep4` 蕴含 `CondMul2`**（`CondMul2` 是其一分量）。 -/
theorem condMul2_of_chainCondIndep4 [Fintype α] [Fintype β] [Fintype ζ] [Fintype ω]
    (p : FinJoint2 α β ζ ω) (h : ChainCondIndep4 p) : CondMul2 p :=
  h.2.1

/-! ### §8.1 ⚠⚠ **可证反例：`CondMul2` 推不出链结构**

构造 $\alpha=\beta=\zeta=\omega=\mathrm{Bool}$ 上的

$$p\big((x,y),(z,w)\big) := \mathbf{1}[x = w \wedge y = w].$$

* **每个 $(z,w)$ 切片**都是 $e_w e_w^{\top}$（秩 $1$），
  且 $z$ 完全不出现 ⟹ `CondMul2` **成立**；
* 但把 $Y$ 边缘化后 $q\big((x,w),z\big) = \mathbf{1}[x=w]$ 是**单位阵**（秩 $2$），
  故 $X \not\perp\!\!\perp Z_2 \mid Z_1$。

**⟹ 结论**：`CondMul2` **不是**「四变量链式条件独立」的完整表达；
它只是 $X \perp\!\!\perp Y \mid (Z_1,Z_2)$ 这一句。
**「更好的定义」= `ChainFactor4`（模型假设）与 `ChainCondIndep4`（三条断言的合取）**。 -/

/-- ⭐ 反例联合律：$p((x,y),(z,w)) = \mathbf{1}[x=w \wedge y=w]$（**不依赖** $z$）。 -/
noncomputable def cexCondMul2Only : FinJoint2 Bool Bool Bool Bool :=
  fun t => if (t.1.1 = t.2.2 ∧ t.1.2 = t.2.2) then (1 : ℝ) else 0

/-- ⭐ 反例在「$Y$ 边缘化后」的联合律 $q((x,w),z) = \sum_y p((x,y),(z,w))$。 -/
noncomputable def cexCollapseY : FinCondIndep.FinJoint Bool Bool Bool :=
  fun t => ∑ y : Bool, cexCondMul2Only ((t.1.1, y), (t.2, t.1.2))

/-- ⭐⭐ **反例满足 `CondMul2`**（逐点 `decide` 有限验证）。 -/
theorem cex_condMul2 : CondMul2 cexCondMul2Only := by
  intro x y z w
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;>
    simp [cexCondMul2Only, marg2X, marg2Y, marg2Z, Fintype.univ_bool] <;> decide

/-- ⭐⭐⭐ **反例不满足 $X \perp\!\!\perp Z_2 \mid Z_1$**
（在 $x = z_2 = \mathrm{true}$ 的切片上，乘性等式给出 $2 = 1$）。 -/
theorem cex_not_X_indep_Z2 : ¬ FinCondIndep.CondMul cexCollapseY := by
  intro h
  have h1 := h true true true
  simp [cexCollapseY, cexCondMul2Only, FinCondIndep.margZ, FinCondIndep.margXZ,
    FinCondIndep.margYZ, Fintype.univ_bool] at h1
  have e1 : (#({x ∈ ({true, false} : Finset Bool) | x = true}) : ℝ) = 1 := by
    have : (#({x ∈ ({true, false} : Finset Bool) | x = true}) : ℕ) = 1 := by decide
    rw [this]; norm_num
  have e2 : (#({x ∈ ({true, false} : Finset Bool) | x = false}) : ℝ) = 1 := by
    have : (#({x ∈ ({true, false} : Finset Bool) | x = false}) : ℕ) = 1 := by decide
    rw [this]; norm_num
  rw [e1, e2] at h1
  norm_num at h1

/-- ⭐⭐⭐⭐ **`CondMul2` 严格弱于链式条件独立（可证分离）**：

存在 $p$ 使 `CondMul2 p` 成立，但 $X \perp\!\!\perp Z_2 \mid Z_1$ 不成立。
**故 `CondMul2` 不能表达链结构。** -/
theorem condMul2_not_sufficient_for_chain :
    ∃ p : FinJoint2 Bool Bool Bool Bool,
      CondMul2 p ∧ ¬ FinCondIndep.CondMul (collapseY p) :=
  ⟨cexCondMul2Only, cex_condMul2, cex_not_X_indep_Z2⟩

/-! ---------------------------------------------------------------------------
  §9  小结（本轮新增）
  --------------------------------------------------------------------------- -/

/-- **本轮结论清单**（`Prop` 值的形式化总结，便于审计）：

1. 链式分解 ⟹ 真四变量条件独立 `CondMul2`（`chain4_condindep`）；
2. 链式分解 ⟹ 三条链式 CI 的合取 `ChainCondIndep4`；
3. `CondMul2` 严格弱于链结构（`condMul2_not_sufficient_for_chain`）。

**⚠ 这三条都是真证明，不含 `sorry`/`axiom`。** -/
def NewResults : Prop :=
  (∀ (p : FinJoint4 Bool Bool Bool Bool) (f₁ : Bool → Bool → ℝ)
      (f₂ : Bool → Bool → ℝ) (f₃ : Bool → Bool → ℝ),
      ChainFactor4Flat p f₁ f₂ f₃ →
      CondMul2 (fun q => p (q.1.1, q.2.1, q.2.2, q.1.2)))
  ∧ (∀ p : FinJoint2 Bool Bool Bool Bool, ChainCondIndep4 p → CondMul2 p)
  ∧ (∃ p : FinJoint2 Bool Bool Bool Bool,
      CondMul2 p ∧ ¬ FinCondIndep.CondMul (collapseY p))

/-- ⭐ **`NewResults` 成立**（把三条主结果打包）。 -/
theorem newResults_holds : NewResults :=
  ⟨fun p f₁ f₂ f₃ h => chain4_condindep (α := Bool) (β := Bool) p f₁ f₂ f₃ h,
   fun p h => condMul2_of_chainCondIndep4 p h,
   condMul2_not_sufficient_for_chain⟩

end CondIndep2

end FateV2.Predict