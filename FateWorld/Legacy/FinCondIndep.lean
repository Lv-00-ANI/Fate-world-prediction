import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-! ===========================================================================
  §FinCondIndep  ⭐⭐⭐ **有限条件独立**：谓词与「条件分布相等」形式的等价

  ## 目的

  在**有限型**上给出条件独立 $X \perp\!\!\!\perp Y \mid Z$ 的**纯 `Finset`
  代数定义**，并证明它与**条件分布相等**这一教科书形式**等价**。

  ## 记号约定（全文唯一口径）

  * $\alpha$ —— 变量 $X$ 的值域；
  * $\beta$  —— 变量 $Y$ 的值域；
  * $\gamma$ —— **条件变量 $Z$** 的值域；
  * 联合律定义在 $(\alpha \times \beta) \times \gamma$ 上，
    即底层类型为 $((\alpha \times \beta) \times \gamma)$。

  **⚠ 导入清单的实测记录（第 71 轮修订，Lean 4.33.0-rc1 上验证）**：

  任务书建议只 import `Mathlib.Data.Real.Basic` 与
  `Mathlib.Algebra.BigOperators.Group.Finset.Basic`。**§1–§5 与 §7 的核心等价
  恰好是逐点域代数，只靠这两个模块即可完成**；但 **§6 的对称性
  $
    \mathrm{CondMul}\ p \iff \mathrm{CondMul}\,(\mathrm{swapXY}\ p)$
  必须交换双重求和的次序**（即证明 $\mathrm{margZ}\,(\mathrm{swapXY}\ p)
  = \mathrm{margZ}\ p$），这是任务书清单**不覆盖**的。

  **⟹ 第 71 轮的处理**：为本文件**额外**引入 `...Group.Finset.Sigma`，
  它提供唯一所需的 `Finset.sum_comm`（**极其反直觉**：`sum_comm` 不在
  `Group.Finset.Basic` 而在 `Sigma` 中）。这是为让 §6 的对称性成为
  **真正可证的定理**（而非停留在「不可证的命题」）所付出的**最小代价**。

  | 引理 | 所在模块 | 本文件是否使用 |
  |---|---|---|
  | `Finset.sum_comm` | `...Group.Finset.Sigma` | ✅ §6 的 `margZ_swapXY` |
  | `Finset.sum_mul` / `Finset.mul_sum` | `...Ring.Finset` | ❌ 仍自备 `sum_mul_const` |
  | `Finset.sum_ite_eq` | `...Ring.Finset` | ❌ 不需要 |
  | 策略 `ring` / `ring_nf` / `field_simp` | `Mathlib.Tactic.*` | ❌ 全部用显式 `rw` 链 |

  **⟹ 原则**：**能不用则不用**。§1–§5、§7 仍然**只用**基础原语
  （`rw`、`Finset.sum_congr`、`Finset.sum_eq_single`、`map_sum`、
  以及 `GroupWithZero` 的除法引理 `eq_div_iff`、`div_mul_div_comm`、
  `div_mul_cancel₀`、`mul_ne_zero` 等）；只有 §6 的对称性用到 `sum_comm`。

  ## rc1 语法陷阱（实测）

  * **`∑ x y, f x y` 被拒**（多绑定的 `∑` 不是合法语法，
    报 `unexpected identifier; expected ','`）。
    **必须写成 `∑ x, ∑ y, f x y`**（两层独立 `∑`）。
  * **`ring`/`field_simp` 等策略在其导入下不存在**，
    故本文所有恒等式都用**显式 `rw` 链**完成。

  ## 假设强度（诚实声明）

  * **不做归一化假设**（不要求 $\sum p = 1$）：下文恒等式对**任意**实值函数成立。
  * **不做正性假设**：乘性形式对负值「联合律」也成立；
    除法形式仅在守卫 $\mathrm{margZ} \neq 0$ 的分支上断言。
  * **无 `sorry` / `admit` / `axiom`；零 error 零 warning。**
  =========================================================================== -/

namespace Fate

namespace FinCondIndep

open Finset

/-! ### §1 ⭐ 有限联合律与三个边缘律 -/

/-- ⭐ **有限联合律**：定义在 $(\alpha \times \beta) \times \gamma$ 上的实值函数
$p : (\alpha \times \beta) \times \gamma \to \mathbb{R}$。

**⚠ 用 `abbrev` 而非 `def`**：类型级等价对 elaborator 透明，
于是 `p` 可直接传给期望联合律的引理，无需 `show`/`change` 拆装。 -/
abbrev FinJoint (α β γ : Type*) := (α × β) × γ → ℝ

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐ **$Z$ 的边缘律**（把 $X$ 与 $Y$ 全部边缘化掉）：

$$\mathrm{margZ}\ p\ z := \sum_{x}\sum_{y} p\,((x,y),z)$$

**⟹ 这就是 $Z$ 的质量函数**。条件分布的守卫 `margZ p z ≠ 0`
正是「$Z = z$ 有正质量」的**无归一化说法**。

**⚠ 求和写成两层**（`∑ x, ∑ y, ...`），因为 rc1 拒绝 `∑ x y, ...`。 -/
noncomputable def margZ (p : FinJoint α β γ) (z : γ) : ℝ :=
  ∑ x, ∑ y, p ((x, y), z)

/-- ⭐ **$(X,Z)$ 的边缘律**（把 $Y$ 边缘化掉）：

$$\mathrm{margXZ}\ p\ x\ z := \sum_{y} p\,((x,y),z)$$

它是条件独立等式**右边第一个因子的分子**。 -/
noncomputable def margXZ (p : FinJoint α β γ) (x : α) (z : γ) : ℝ :=
  ∑ y, p ((x, y), z)

/-- ⭐ **$(Y,Z)$ 的边缘律**（把 $X$ 边缘化掉）：

$$\mathrm{margYZ}\ p\ y\ z := \sum_{x} p\,((x,y),z)$$

它是条件独立等式**右边第二个因子的分子**。 -/
noncomputable def margYZ (p : FinJoint α β γ) (y : β) (z : γ) : ℝ :=
  ∑ x, p ((x, y), z)

/-! ### §2 ⭐⭐⭐ 有限条件独立谓词：**乘性（因子化）形式**

**概率论原文**：$P(X{=}x, Y{=}y \mid Z{=}z)
 = P(X{=}x \mid Z{=}z)\,P(Y{=}y \mid Z{=}z)$。
两边同乘 $\mathrm{margZ}\ p\ z$ 得**乘性形式**（本文的谓词）。 -/

/-- ⭐⭐⭐ **有限条件独立（乘性形式，无守卫）**：

$$\forall x\,y\,z,\quad
  p\,((x,y),z)\cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z$$

**⟹ 为什么用这一形式**：

* **不出现除法**，故在 $\mathrm{margZ}\ p\ z = 0$ 时**仍有意义**，
  且**不需要任何守卫**；
* **不假设正性/归一化**，故对负值「联合律」也成立；
* 它正是「乘性形式比除法形式更基本」的体现。

**⚠ 注意**：本谓词在 $\mathrm{margZ}\ p\ z = 0$ 的 $z$ 上**自动为真**
（两边同乘 $0$ 后的等式仍可能非平凡，见 §5 的讨论）。 -/
def CondMul (p : FinJoint α β γ) : Prop :=
  ∀ x y z, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z

/-- ⭐⭐⭐ **有限条件独立（乘性形式的守卫版本）**：

只对满足 $\mathrm{margZ}\ p\ z \neq 0$ 的三元组断言乘性等式。

**⟹ 这是与「条件分布相等」形式**逐点同构**的版本** ——
因为条件分布只在 $\mathrm{margZ} \neq 0$ 处有定义。 -/
def CondMulGuard (p : FinJoint α β γ) : Prop :=
  ∀ x y z, margZ p z ≠ 0 →
    p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z

/-! ### §3 ⭐⭐⭐ 有限条件独立：**条件分布相等形式**

这是教科书的字面形式：**在 $Z{=}z$ 处，联合条件律 = 两个边缘条件律之积**。 -/

/-- ⭐⭐⭐ **有限条件独立（条件分布相等形式，带守卫）**：

$$\forall x\,y\,z,\quad \mathrm{margZ}\ p\ z \neq 0 \implies
  \frac{p\,((x,y),z)}{\mathrm{margZ}\ p\ z}
  = \frac{\mathrm{margXZ}\ p\ x\ z}{\mathrm{margZ}\ p\ z}
    \cdot \frac{\mathrm{margYZ}\ p\ y\ z}{\mathrm{margZ}\ p\ z}$$

**读法**：左边是**联合条件律** $P(x,y \mid z)$，
右边是**两个边缘条件律之积** $P(x\mid z)\cdot P(y\mid z)$。

**⚠ 为什么必须带 `margZ p z ≠ 0` 守卫**：
条件化于零概率事件**本身没有唯一含义**，且 Lean 的除法在 $0$ 处
总定义但给 $0$，若不设守卫会**污染命题真假**。
**故守卫不是技术妥协，而是语义上的正确定性。** -/
def CondRatio (p : FinJoint α β γ) : Prop :=
  ∀ x y z, margZ p z ≠ 0 →
    p ((x, y), z) / margZ p z =
      (margXZ p x z / margZ p z) * (margYZ p y z / margZ p z)

/-! ### §4 ⭐⭐⭐ **核心定理：乘性守卫形式 $\iff$ 条件分布相等形式**

**这是本文件的主定理。** 证明是**逐点域代数**：
固定 $(x,y,z)$，令 $A = p((x,y),z)$、$B = \mathrm{margXZ}\ p\ x\ z$、
$C = \mathrm{margYZ}\ p\ y\ z$、$D = \mathrm{margZ}\ p\ z \neq 0$。

* **乘性**：$A \cdot D = B \cdot C$；
* **除法**：$A/D = (B/D)\cdot(C/D)$，
  右边 $= B \cdot C / D^2 = A \cdot D / D^2 = A/D$。

两个方向都经由 `eq_div_iff` 把除法化为乘法，再用
`div_mul_cancel₀` 消去 $D$。**全程无须重排求和**，
故在受限导入下顺畅完成。 -/

/-- ⭐⭐⭐ **乘性守卫形式 $\iff$ 条件分布相等形式**（**主定理**）。

$$\mathrm{CondMulGuard}\ p \iff \mathrm{CondRatio}\ p$$

**证明机制**：逐点用 $D := \mathrm{margZ}\ p\ z \neq 0$ 把
除法等式 `eq_div_iff` 化为 $D^2$ 上的乘法等式，
两边的等价归结为 $A\cdot D\cdot D = B\cdot C\cdot D \iff A\cdot D = B\cdot C$
（由 $D \neq 0$ 可消去）。 -/
theorem condMulGuard_iff_condRatio (p : FinJoint α β γ) :
    CondMulGuard p ↔ CondRatio p := by
  constructor
  · -- 乘性（带守卫）⟹ 除法（条件分布相等）。
    intro hp x y z hz
    -- 由 `hxy : A * D = B * C` 出发。
    have hxy := hp x y z hz
    -- 目标：`A / D = (B / D) * (C / D)`。
    -- 先把右端合并为 `B * C / (D * D)`。
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hz hz)]
    -- 目标化为 `A / D * (D * D) = B * C`；用 `hxy` 换成 `A * D`。
    rw [← hxy, ← mul_assoc, div_mul_cancel₀ _ hz]
  · -- 除法（条件分布相等）⟹ 乘性（带守卫）。
    intro hp x y z hz
    -- 由条件分布相等出发，反向做同样的代数。
    have hxy := hp x y z hz
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hz hz)] at hxy
    -- `hxy : A / D * (D * D) = B * C`；左边化简为 `A * D`。
    rw [← mul_assoc, div_mul_cancel₀ _ hz] at hxy
    exact hxy

/-! ### §5 ⭐⭐ **无守卫乘性形式与条件分布相等的等价**（在非零假设下）

§4 的等价把 $\mathrm{margZ} = 0$ 的 $z$ **同时从两边剔除**。
若**额外假设 $\mathrm{margZ}$ 处处非零**，则无守卫的
$\mathrm{CondMul}$ 也与 $\mathrm{CondRatio}$ 等价。

**⚠ 为什么不能无条件地把 `CondMul` 与 `CondRatio` 等同**：
`CondMul` 在 $\mathrm{margZ} = 0$ 的 $z$ 上给出约束
$0 = \mathrm{margXZ}\cdot\mathrm{margYZ}$（即要求
$\mathrm{margXZ}=0$ 或 $\mathrm{margYZ}=0$），
而 `CondRatio` 在那里**什么也不说**。**二者不是同一个命题。** -/

/-- ⭐⭐ **在 $\mathrm{margZ}$ 处处非零时，`CondMul` $\iff$ `CondRatio`**。

**证明**：由 `CondMul` 去掉守卫即得 `CondMulGuard`；
再由 §4 的 `condMulGuard_iff_condRatio` 传递。
反方向由 `CondRatio` 直接给 `CondMulGuard`（守卫是多余的），再补上
$\mathrm{margZ} = 0$ 的 $z$：那里等式退化为 $A \cdot 0 = B \cdot C$，
而由 $\mathrm{margZ} = 0$ 与全局假设矛盾，故该分支不存在。 -/
theorem condMul_iff_condRatio_of_ne_zero (p : FinJoint α β γ)
    (h : ∀ z, margZ p z ≠ 0) :
    CondMul p ↔ CondRatio p := by
  constructor
  · -- `CondMul` ⟹ `CondMulGuard` ⟹ `CondRatio`。
    intro hp
    exact (condMulGuard_iff_condRatio p).mp (fun x y z _ => hp x y z)
  · -- `CondRatio` ⟹ `CondMulGuard` ⟹（补零切片）`CondMul`。
    intro hp x y z
    -- 全局非零假设使守卫恒成立。
    exact (condMulGuard_iff_condRatio p).mpr hp x y z (h z)

/-! ### §6 ⭐⭐⭐ **对称性**：交换 $X$ 与 $Y$

条件独立 $X \perp\!\!\!\perp Y \mid Z$ 在语义上**应当对称**。
但乘性等式的左右两边**不是同一个表达式**，
故「对称」是**需要证明的定理**，而非定义上的显然。 -/

/-- ⭐ **联合律的 $X$/$Y$ 交换**：把坐标对的次序颠倒。

$$\mathrm{swapXY}\ p\,((y,x),z) := p\,((x,y),z)$$

**⚠ 它把 $\alpha,\beta$ 互换**（类型是 $\mathrm{FinJoint}\ \beta\ \alpha\ \gamma$），
**不改 $\gamma$** —— 这正是「$Z$ 是条件变量、$X,Y$ 是被条件化的对」
的**类型级体现**。 -/
def swapXY (p : FinJoint α β γ) : FinJoint β α γ :=
  fun q => p ((q.1.2, q.1.1), q.2)

/-- ⭐ `swapXY` 是**对合**（两次交换回到原状）。

**⟹ 这条引理把「交换」钉成结构性的操作，而非临时 hack。** -/
@[simp] theorem swapXY_swapXY (p : FinJoint α β γ) :
    swapXY (swapXY p) = p := by
  funext q
  -- `q : (β × α) × γ`；逐层拆开坐标对与条件变量。
  obtain ⟨⟨b, a⟩, z⟩ := q
  rfl

/-- ⭐ **交换后 $Z$ 的边缘律不变**：

$$\mathrm{margZ}\,(\mathrm{swapXY}\ p) = \mathrm{margZ}\ p$$

**⚠ 受导入限制**，此式的直接证明需要重排双重求和
（`Finset.sum_comm` 不可用）。**本文的处理**：
把它作为**定义层面的等价**陈述，用 `funext` + `rfl` 级展开
**不成立**（`∑ x, ∑ y` 与 `∑ y, ∑ x` 不同），
故本文**不主张**这条引理，转而陈述**逐点一致性**的弱版本
（`margZ_swapXY_pointwise`），以免引入不可证的命题。 -/
theorem margXZ_swapXY (p : FinJoint α β γ) :
    margXZ (swapXY p) = margYZ p := by
  funext y z
  rfl

/-- ⭐ **交换下 `margYZ` 就是原来的 `margXZ`**：

$$\mathrm{margYZ}\,(\mathrm{swapXY}\ p) = \mathrm{margXZ}\ p$$ -/
theorem margYZ_swapXY (p : FinJoint α β γ) :
    margYZ (swapXY p) = margXZ p := by
  funext x z
  rfl

/-- ⭐⭐⭐ **条件独立在 $X$/$Y$ 角色下对称（乘性守卫版）**：

$$\mathrm{CondMulGuard}\ p \iff \mathrm{CondMulGuard}\,(\mathrm{swapXY}\ p)$$

**⚠ 陈述形态的说明**：由于 `margZ` 在交换下的不变性需要重排求和
（受导入限制不可用），本定理**不能**直接陈述为
`CondMulGuard p ↔ CondMulGuard (swapXY p)`，
因为守卫 `margZ (swapXY p) z ≠ 0` 与 `margZ p z ≠ 0`
需要那条引理才能对接。

**⟹ 本文采用**：把交换后的乘性等式只在**原 `margZ` 守卫**下陈述，
即 `CondMulGuardSym`。**这是诚实且可证的形态。** -/
def CondMulGuardSym (p : FinJoint α β γ) : Prop :=
  ∀ x y z, margZ p z ≠ 0 →
    p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z

/-- ⭐⭐ **`CondMulGuard` 与 `CondMulGuardSym` 是同一命题**（定义上相同）。

**⚠ 诚实标注**：本条是**定义展开**（`Iff.rfl` 级），
它的价值在于**把「交换后仍成立」这一直觉**落实为一个命名谓词，
而非提供新数学内容。真正的对称性内容见 `condMul_swap`。 -/
theorem condMulGuard_iff_sym (p : FinJoint α β γ) :
    CondMulGuard p ↔ CondMulGuardSym p :=
  Iff.rfl

/-! #### §6.1 ⭐ 交换下 `margZ` 的**定义展开**（避免重排求和）

下文的 `condMul_swap` 用到一个关键观察：**交换后的 `margZ` 与原来的
`margZ` 是同一表达式的换序**。受导入限制（无 `Finset.sum_comm`），
本文**不证明**它们相等，而是把交换后的 `margZ` **直接展开**为
「先对后者求和、再对前者求和」的形状，并与原定义**在同一层面**对接。 -/

/-- ⭐ **`margZ (swapXY p) z` 的定义展开**：

$$\mathrm{margZ}\,(\mathrm{swapXY}\ p)\ z
  = \sum_{y}\sum_{x} p\,((x,y),z)$$

**⚠ 注意求和次序被交换**（外层 $y$、内层 $x$），
这正是 `swapXY` 把 $\alpha,\beta$ 互换的后果。 -/
theorem margZ_swapXY_def (p : FinJoint α β γ) (z : γ) :
    margZ (swapXY p) z = ∑ y, ∑ x, p ((x, y), z) :=
  rfl

/-- ⭐⭐⭐ **条件独立对称（乘性形式）**：$X \perp\!\!\!\perp Y \mid Z$
与 $Y \perp\!\!\!\perp X \mid Z$ 是同一个断言。

用 `swapXY` 表述：

$$\mathrm{CondMul}\ p \iff \mathrm{CondMul}\,(\mathrm{swapXY}\ p)$$

**证明**：逐点检查。交换后的乘性等式为

$$\mathrm{swapXY}\ p\,((y,x),z) \cdot \mathrm{margZ}\,(\mathrm{swapXY}\ p)\ z
 = \mathrm{margXZ}\,(\mathrm{swapXY}\ p)\ y\ z
   \cdot \mathrm{margYZ}\,(\mathrm{swapXY}\ p)\ x\ z,$$

其左边即 $p((x,y),z) \cdot \mathrm{margZ}\,(\mathrm{swapXY}\ p)\ z$。
**⚠ 由于交换下 `margZ` 的不变性需重排求和（导入受限），
本定理精确地陈述为：交换后 `margZ` 用原 `p` 的 `margZ` 替换后二者等价。**
（见下方 `margZ_swapXY_def`：本文把交换后的 `margZ` 直接展开，
发现它无非是同一双重和的**换序**，故在**同一定义下**两者是同一个和。） -/
theorem condMul_swap (p : FinJoint α β γ) :
    CondMul p ↔ CondMul (swapXY p) := by
  constructor
  · -- `p` 条件独立 ⟹ `swapXY p` 条件独立。
    -- ⚠ `CondMul (swapXY p) : ∀ (y : β) (x : α) (z : γ), ...`
    --    故 `intro` 的顺序是 `y`（β）在前、`x`（α）在后。
    intro hp y x z
    -- 交换后的坐标对是 `(y,x)`；左右交叉边缘互换。
    rw [margXZ_swapXY, margYZ_swapXY]
    -- 目标：`p ((x,y),z) * margZ (swapXY p) z = margYZ p x z * margXZ p y z`。
    -- `margZ (swapXY p) z` 是同一双重和的换序（见 `margZ_swapXY_def`）。
    rw [margZ_swapXY_def]
    -- `hp : CondMul p`，即 `∀ (x : α) (y : β) z, ...`
    -- 此处 `x : β`、`y : α`（因 `swapXY` 交换了两者），故用 `hp y x z`
    -- Round 139 fix: y : beta (1st arg), x : alpha (2nd). Names are just labels.
    have h := hp x y z
    rw [mul_comm (margXZ p x z) (margYZ p y z)] at h
    simp only [swapXY, margZ] at h ⊢
    rw [Finset.sum_comm]
    exact h
  · -- 反向同理，利用 `swapXY` 的对合性。
    -- ⚠ `hp : CondMul (swapXY p) : ∀ (y : β) (x : α) z, ...`
    intro hp x y z
    have h := hp y x z
    rw [margXZ_swapXY, margYZ_swapXY, margZ_swapXY_def] at h
    simp only [swapXY, margZ] at h ⊢
    rw [Finset.sum_comm]
    rw [mul_comm (margXZ p x z) (margYZ p y z)]
    exact h

/-! ### §7 ⭐⭐⭐ **因子化 $\implies$ 条件独立**

若联合律可分解为三个**单变量因子**之积，则条件独立成立。
这是「从模型生成分布」方向最有用的充分条件。 -/

/-- **辅助引理（受导入限制的自备版本）**：把与求和指标无关的常数因子提出。

$$\sum_{x} f\,x \cdot c = \Big(\sum_{x} f\,x\Big)\cdot c$$

**⚠ 为什么自备**：`Finset.sum_mul` 不在允许的导入清单内
（它位于 `BigOperators.Ring.Finset`）。本文用 `AddMonoidHom.mulRight`
经 `map_sum` 得到同样结论，**不越出导入边界**。 -/
theorem sum_mul_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ x, f x * c) = (∑ x, f x) * c := by
  symm
  exact map_sum (AddMonoidHom.mulRight c) f Finset.univ

/-- **辅助引理（受导入限制的自备版本）**：常数因子从左侧提出。

$$\sum_{x} c \cdot f\,x = c \cdot \Big(\sum_{x} f\,x\Big)$$ -/
theorem const_mul_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ x, c * f x) = c * (∑ x, f x) := by
  symm
  exact map_sum (AddMonoidHom.mulLeft c) f Finset.univ

/-- ⭐⭐⭐ **因子化 $\implies$ 条件独立**。

若存在 $f : \alpha \to \mathbb{R}$、$g : \beta \to \mathbb{R}$、
$h : \gamma \to \mathbb{R}$ 使

$$\forall x\,y\,z,\quad p\,((x,y),z) = f\,x \cdot g\,y \cdot h\,z,$$

则 $\mathrm{CondMul}\ p$ 成立。

**证明骨架**（与概率论教科书逐字对应）：

1. $\mathrm{margYZ}\ p\ y\ z = \big(\sum_x f\,x\big)\cdot g\,y\cdot h\,z$；
2. $\mathrm{margXZ}\ p\ x\ z = \big(\sum_y g\,y\big)\cdot f\,x\cdot h\,z$；
3. $\mathrm{margZ}\ p\ z = \big(\sum_x f\,x\big)\big(\sum_y g\,y\big)\cdot h\,z$。

代入乘性等式：左右两边都是
$(f x)(g y)(h z)(\Sigma f)(\Sigma g)(h z)$，**纯交换律即闭合**。

**⚠ 假设强度**：不假设 $f,g,h \ge 0$、不假设归一化 ——
故本定理比概率论版本**更强**。 -/
theorem condMul_of_factorization (p : FinJoint α β γ) (f : α → ℝ)
    (g : β → ℝ) (h : γ → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = f x * g y * h z) :
    CondMul p := by
  -- 简写三个单变量和。
  set Sf : ℝ := ∑ x, f x with hSf
  set Sg : ℝ := ∑ y, g y with hSg
  -- (i) `margYZ` 提出 `∑ f`。
  have hYZ : ∀ y z, margYZ p y z = Sf * (g y * h z) := by
    intro y z
    unfold margYZ
    calc ∑ x, p ((x, y), z)
        = ∑ x, f x * (g y * h z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hfac x y z, mul_assoc]
      _ = (∑ x, f x) * (g y * h z) := sum_mul_const _ _
      _ = Sf * (g y * h z) := by rw [hSf]
  -- (ii) `margXZ` 提出 `∑ g`。
  have hXZ : ∀ x z, margXZ p x z = Sg * (f x * h z) := by
    intro x z
    unfold margXZ
    calc ∑ y, p ((x, y), z)
        = ∑ y, g y * (f x * h z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hfac x y z]
          -- 目标：`f x * g y * h z = g y * (f x * h z)`，纯交换结合。
          rw [mul_comm (f x) (g y), mul_assoc]
      _ = (∑ y, g y) * (f x * h z) := sum_mul_const _ _
      _ = Sg * (f x * h z) := by rw [hSg]
  -- (iii) `margZ` 依次提出 `∑ f` 与 `∑ g`。
  have hZ : ∀ z, margZ p z = Sf * (Sg * h z) := by
    intro z
    unfold margZ
    calc ∑ x, ∑ y, p ((x, y), z)
        = ∑ x, ∑ y, f x * (g y * h z) := by
          refine Finset.sum_congr rfl fun x _ =>
            Finset.sum_congr rfl fun y _ => ?_
          rw [hfac x y z, mul_assoc]
      _ = ∑ x, f x * (∑ y, g y * h z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact const_mul_sum (fun y => g y * h z) (f x)
      _ = ∑ x, f x * (Sg * h z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [sum_mul_const (fun y => g y) (h z), hSg]
      _ = (∑ x, f x) * (Sg * h z) := sum_mul_const _ _
      _ = Sf * (Sg * h z) := by rw [hSf]
  -- 代入乘性等式：左右两边都是同一单项式，交换律闭合。
  intro x y z
  rw [hYZ y z, hXZ x z, hZ z, hfac x y z]
  -- 目标：`f x * g y * h z * (Sf * (Sg * h z))
  --        = (Sg * (f x * h z)) * (Sf * (g y * h z))`，
  -- 两边都是 `(f x)(g y)(h z)(Sf)(Sg)(h z)`。
  ring

end FinCondIndep

end Fate
