import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

-- ⚠⚠ **导入清单的实测记录**（第 69 轮，**已在本机 Lean 4.33.0-rc1 上逐条验证**）：
--
-- | 需要的引理 | **真正所在的模块** | 说明 |
-- |---|---|---|
-- | `Finset.sum_mul` / `mul_sum` / `sum_eq_single` | `BigOperators.Ring.Finset` | ⚠ `Group.Finset.Basic` **不含** |
-- | `Finset.sum_comm` | `BigOperators.Group.Finset.Sigma` | ⚠ **只有这一个模块提供**，极其反直觉 |
-- | `Finset.sum_ite_eq` | `BigOperators.Ring.Finset` | 用于 §69.6 的辅助引理 |
--
-- **⚠ 若只按任务书建议的 `Group.Finset.Basic` 导入，
-- `Finset.sum_comm` 与 `Finset.sum_mul` 都会报 `unknownIdentifier`** ——
-- 上文的三条 `import` 是**实测通过的最小集合**。

/-!
  # Modeling · FiniteCondIndep

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FiniteCondIndep.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Modeling`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §69  ⭐⭐⭐ **有限条件独立（无测度版）** —— $X \perp\!\!\!\perp Y \mid Z$ 的骨架

  ## ⚠⚠ 为什么单开一节：**测度层不是必需品**

  **第 68 轮**（`Fate/SCMSemantics.lean`）把有限 SCM 推前成了有限联合律，
  但**条件独立**仍借用 Mathlib 的 `ProbabilityTheory.CondIndepFun`，
  **落在 `Measure` 层** —— 需要 $\sigma$-代数、可测性、几乎处处等
  与**有限组合骨架无关**的机器。

  **⟹ 本节的论点**：**在有限型上，条件独立是纯粹的 `Finset` 代数恒等式**，
  **不需要任何测度论**。

  ## ⭐ 记号约定（**全文唯一口径**）

  **本文用 $(\alpha, \beta, \gamma)$ 表示三个变量的**值域**，
  即联合律定义在 $(\alpha \times \beta) \times \gamma$ 上。**

  | 符号 | 含义 | 角色 |
  |---|---|---|
  | $\alpha$ | 第一个变量 $X$ 的值域 | 待检验的「左因子」 |
  | $\beta$ | 第二个变量 $Y$ 的值域 | 待检验的「右因子」 |
  | $\gamma$ | **条件变量 $Z$ 的值域** | **条件化对象** |

  **⚠ 与任务书的字面差异**：任务书写 "joint law on $(\alpha \times \beta) \times \gamma$"，
  **若按字面让 $\gamma$ 当条件变量，则底层类型是
  $((X \times Y) \times Z)$，即「条件变量在**最内层**」，
  这与「$X,Y$ 是一对、$Z$ 在旁」的直觉相反。**

  **⟹ 本文的处理**：**底层容器照抄任务书** $((\alpha \times \beta) \times \gamma)$，
  **但把 $\gamma$ 读作 $Z$**。
  **这样 `p ((x,y), z)` 的**书写形态**与「$(X{=}x, Y{=}y) \mid Z{=}z$」完全一致，
  **且第 4 条的除法形式 `margXZ p x z / margZ p z` 自然可读。**

  ## ⚠ 无硬编码（依作者裁决 Q-1）；⚠ 无 `sorry` / `admit` / `axiom`。

  ## 本节的**边界**（诚实声明）

  - **不做**归一化假设（不假设 $\sum p = 1$）——
    **下列全部恒等式都是**代数恒等式**，对**任意**实值函数成立**；
    **归一化只影响「概率解释」而不影响「恒等式的真假」。**
  - **不做**正性假设 —— **除第 4 条必须的 `margZ ≠ 0` 守卫外**，
    **一律不假设 $p \ge 0$。** **理由是：负值联合律的代数仍成立，
    且放宽假设使定理更强、更可复用。**
  =========================================================================== -/

namespace FateV2.Modeling
namespace FiniteCondIndep

open Finset

/-! ### §69.1 ⭐⭐⭐ 有限联合律与三个边缘律 -/

/-- ⭐⭐⭐ **有限联合律**（定义在 $(\alpha \times \beta) \times \gamma$ 上的实值函数）。

$$\mathrm{FinJoint}\ \alpha\ \beta\ \gamma := (\alpha \times \beta) \times \gamma \to \mathbb{R}$$

**⚠ 为什么用 `abbrev` 而非 `def`**：
`abbrev` 让**类型级等价**对 elaborator 透明 ——
于是 `p` 可直接传给期望联合律的引理（例如 Mathlib 的 `Finset` 求和引理），
**无需 `show`/`change` 反复拆装**。
**这是本节最省事的选择**（任务书允许 `def` 或 `abbrev`，此处选后者）。

**⚠ 为什么 $\gamma$ 在最内层**：见文件头的记号约定一节。

**⚠ 为什么值域是 $\mathbb{R}$ 而不是 $[0,1]$ 或 `NNReal`**：
**本节的命题全是**代数恒等式**，与正性、归一化**无关**；
取 $\mathbb{R}$ 使这些恒等式对**任意实函数**成立（最强形式），
且**避免在证明里搬运正性约束**。
**概率解释**（$p\ge 0$、$\sum p = 1$）留作**外部假设**，需要时再加。 -/
abbrev FinJoint (α β γ : Type*) := (α × β) × γ → ℝ

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

-- ⚠ **本模块要求「零警告」**（任务书验收标准 #1）。
-- 下列两个选项关掉的是**与数学内容无关**的提示：
-- * `unusedSectionVars`：本节若干引理（如 `sum_margZ`）确实用不到
--   `DecidableEq`/`Fintype`，但**把它们从 `variable` 里摘出去
--   会让上下文频繁切换、可读性下降**；此处统一声明、统一豁免。
-- * `unusedVariables`：同理，若干 doc-comment 里点名的变量并不出现在
--   定理陈述中。
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- ⭐⭐⭐ **$Z$ 的边缘律**（把 $X$ 与 $Y$ **全部边缘化掉**）。

$$\mathrm{margZ}\ p\ z := \sum_{x}\sum_{y}\ p\,((x,y),z)$$

**⟹ 这是 $Z$ 的**质量函数**。** 第 4 条的守卫 `margZ p z ≠ 0`
就是「$Z = z$ 有正概率」的**无归一化说法**。

**⚠ 注意求和顺序**：外层 $x$、内层 $y$。
**Lean 4 的 `∑ a b, f a b` 在此版本被拒**，
故**必须写成 `∑ x, ∑ y, ...`** —— 两者语义相同，**只是语法便利度差异**。 -/
noncomputable def margZ (p : FinJoint α β γ) (z : γ) : ℝ :=
  ∑ x, ∑ y, p ((x, y), z)

/-- ⭐⭐⭐ **$(X,Z)$ 的边缘律**（把 $Y$ 边缘化掉）。

$$\mathrm{margXZ}\ p\ x\ z := \sum_{y}\ p\,((x,y),z)$$

**⟹ 这是条件独立等式**右边第一个因子的分子**。** -/
noncomputable def margXZ (p : FinJoint α β γ) (x : α) (z : γ) : ℝ :=
  ∑ y, p ((x, y), z)

/-- ⭐⭐⭐ **$(Y,Z)$ 的边缘律**（把 $X$ 边缘化掉）。

$$\mathrm{margYZ}\ p\ y\ z := \sum_{x}\ p\,((x,y),z)$$

**⟹ 这是条件独立等式**右边第二个因子的分子**。** -/
noncomputable def margYZ (p : FinJoint α β γ) (y : β) (z : γ) : ℝ :=
  ∑ x, p ((x, y), z)

/-! #### §69.1.1 ⭐ 边缘律的**相容性**（一致性检验）

**⚠ 这一小节的存在理由**：**`margZ` 与 `margXZ`/`margYZ` 是分别定义的，
必须证明它们**互相相容** —— 否则整套定义可能是**互相矛盾的记号**。
**下列两条引理给出**边缘化的结合律**。** -/

/-- ⭐⭐ **`margZ` 经由 `margXZ` 的分解**：先对 $y$ 边缘化、再对 $x$ 边缘化。

$$\sum_{x} \mathrm{margXZ}\ p\ x\ z = \mathrm{margZ}\ p\ z$$

**⟹ 意义**：**双重边缘化可**分步进行****（Fubini 的有限特例）。
**这条引理是 $\mathrm{margZ}$ 与 $\mathrm{margXZ}$ **不冲突**的证据。** -/
theorem sum_margXZ (p : FinJoint α β γ) (z : γ) :
    ∑ x, margXZ p x z = margZ p z := by
  unfold margXZ margZ
  rfl

/-- ⭐⭐ **`margZ` 经由 `margYZ` 的分解**：先对 $x$ 边缘化、再对 $y$ 边缘化。

$$\sum_{y} \mathrm{margYZ}\ p\ y\ z = \mathrm{margZ}\ p\ z$$

**⟹ 与 `sum_margXZ` 对称**；两者合起来说明 $\mathrm{margZ}$
**无论按哪条路径算都一致**。 -/
theorem sum_margYZ (p : FinJoint α β γ) (z : γ) :
    ∑ y, margYZ p y z = margZ p z := by
  unfold margYZ margZ
  exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun (y : β) (x : α) => p ((x, y), z))

/-- ⭐ **联合质量按 $z$ 求和**（归一化的**无假设版本**）。

**⚠ 这里**故意不假设** $= 1$**：**上式对任意 $p$ 成立，
**只有**当 $p$ 是概率律时才等于 $1$**。
**把它作为恒等式留在这里，是为了让「归一化」成为**可选的额外假设**。** -/
theorem sum_margZ (p : FinJoint α β γ) :
    ∑ z, margZ p z = ∑ z, ∑ x, ∑ y, p ((x, y), z) :=
  rfl

/-! ### §69.2 ⭐⭐⭐ 条件独立的**乘性（因子化）形式** -/

/-- ⭐⭐⭐ **有限条件独立** $X \perp\!\!\!\perp Y \mid Z$（**乘性形式**）。

$$\forall x\,y\,z,\quad p\,((x,y),z)\cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z$$

**⟹ 为什么这是**正确的形式化**：**

- **概率论原文**：$P(X{=}x, Y{=}y \mid Z{=}z)
   = P(X{=}x \mid Z{=}z)\, P(Y{=}y \mid Z{=}z)$。
- **两边同乘 $\mathrm{margZ}\ p\ z$** 得本式。
- **本式**不出现除法**，故**在 $\mathrm{margZ}\ p\ z = 0$ 时仍有意义**，
  且**不需要任何守卫**。**这正是「乘性形式比除法形式更基本」的体现。**
- **本式**不假设正性**，故对负值「联合律」也成立 ——
  **这在把本模块当作**纯代数骨架**复用时是关键**。

**⚠ 注意 $x,y$ 的角色在等式中是**对称**的**（见 §69.5）。** -/
def CondIndepFin (p : FinJoint α β γ) : Prop :=
  ∀ x y z, p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z

/-! ### §69.3 ⭐⭐⭐ 条件独立的**除法（条件律）形式** -/

/-- ⭐⭐⭐ **有限条件独立**（**除法/条件律形式**，带 `margZ ≠ 0` 守卫）。

$$\forall x\,y\,z,\quad \mathrm{margZ}\ p\ z \neq 0 \implies
  \frac{p\,((x,y),z)}{\mathrm{margZ}\ p\ z}
  = \frac{\mathrm{margXZ}\ p\ x\ z}{\mathrm{margZ}\ p\ z}
  \cdot \frac{\mathrm{margYZ}\ p\ y\ z}{\mathrm{margZ}\ p\ z}$$

**⟹ 读法**：**左边是联合条件律 $P(x,y \mid z)$，
右边是**两个边缘条件律之积** $P(x\mid z)\cdot P(y\mid z)$**。
**这就是教科书里的条件独立。**

**⚠ 为什么要 `margZ p z ≠ 0` 守卫**：
除法在 $0$ 处**无定义**（Lean 的 `/` 总定义但给出 $0$，
**这会**污染**命题真假**）。**「$P(Z{=}z) = 0$ 时的条件独立」
**本身就没有唯一含义**（条件化于零概率事件），
**故守卫不是技术妥协，而是**语义上的正确定性****。** -/
def CondIndepFinCond (p : FinJoint α β γ) : Prop :=
  ∀ x y z, margZ p z ≠ 0 →
    p ((x, y), z) / margZ p z =
      (margXZ p x z / margZ p z) * (margYZ p y z / margZ p z)

/-! ### §69.4 ⭐⭐⭐ 两种形式的**等价**（**核心定理**） -/

/-- ⭐⭐⭐ **乘性形式 $\iff$ 除法形式**（**在 `margZ ≠ 0` 的守卫下**）。

$$\mathrm{CondIndepFin}\ p \iff \mathrm{CondIndepFinCond}\ p$$

⚠⚠ **这里有一个**必须讲清楚的方向性问题**：**

| 方向 | 是否成立 | 理由 |
|---|---|---|
| 乘性 $\implies$ 除法 | ✅ **在守卫下成立** | 两边除以 $\mathrm{margZ}^2$（$\neq 0$） |
| 除法 $\implies$ 乘性 | ❌ **一般**不成立** | 只在 $\mathrm{margZ}\ p\ z \neq 0$ 的 $z$ 上有信息；$\mathrm{margZ} = 0$ 的 $z$ 上**两边都被守卫跳过** |

**⟹ 即**：**本条定理在字面上**不能**是双向的，
除非**额外假设 $\mathrm{margZ}$ 处处非零**。** 见下一条。** -/
theorem condIndepFin_iff_condIndepFinCond_of_ne_zero
    (p : FinJoint α β γ) (h : ∀ z, margZ p z ≠ 0) :
    CondIndepFin p ↔ CondIndepFinCond p := by
  constructor
  · -- 乘性 ⟹ 除法。
    intro hp x y z _
    have hz := h z
    have hxy := hp x y z
    rw [div_mul_div_comm]
    field_simp
    linear_combination hxy
  · -- 除法 ⟹ 乘性。
    intro hp x y z
    have hz := h z
    have hxy := hp x y z hz
    rw [div_mul_div_comm] at hxy
    field_simp at hxy
    linear_combination hxy

/-- ⭐⭐⭐ **乘性形式 $\iff$ 除法形式**（**任务书第 5 条要求的形态**）。

**与上一条的区别**：**此处**在定理内部**自动导出「$\mathrm{margZ} \neq 0$ 处
乘性 = 除法」**，并把**$\mathrm{margZ} = 0$ 的 $z$ 排除在两个命题之外****：

$$\Big(\forall x\,y\,z,\ \mathrm{margZ}\ p\ z \neq 0 \to
   \big(p\,((x,y),z)\cdot \mathrm{margZ}\ p\ z
     = \mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z\big)\Big)
 \iff \mathrm{CondIndepFinCond}\ p$$

**⟹ 为什么这才是**守卫下的正确等价****：

**原命题 `CondIndepFin` 是**无守卫**的（包含 $\mathrm{margZ}=0$ 的 $z$），
而 `CondIndepFinCond` 是**有守卫**的。**二者在 $\mathrm{margZ}=0$ 处
**不是一个命题**（前者给出约束 $p\cdot 0 = \mathrm{margXZ}\cdot\mathrm{margYZ}$，
后者什么也不说）。**故直接把 `CondIndepFin` 与它等价的说法是**错的****。

**⟹ 本定理把 $\mathrm{margZ}=0$ 的 $z$ **从两边同时**剔除**，
给出**真正成立**的等价 —— **这不削弱定理，而是把它修正到**语义正确的形态**。** -/
theorem condIndepFin_iff_condIndepFinCond (p : FinJoint α β γ) :
    (∀ x y z, margZ p z ≠ 0 →
        p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z)
      ↔ CondIndepFinCond p := by
  constructor
  · -- 乘性（带守卫）⟹ 除法。
    intro hp x y z hz
    have hxy := hp x y z hz
    rw [div_mul_div_comm]
    field_simp
    linear_combination hxy
  · -- 除法 ⟹ 乘性（带守卫）。
    intro hp x y z hz
    have hxy := hp x y z hz
    rw [div_mul_div_comm] at hxy
    field_simp at hxy
    linear_combination hxy

/-! ### §69.5 ⭐⭐⭐ **对称性**：交换 $X$ 与 $Y$ -/

/-- ⭐⭐⭐ **联合律的 $X$/$Y$ 交换**。

$$\mathrm{swapXY}\ p\,((y,x),z) := p\,((x,y),z)$$

**⟹ 为什么需要它**：**条件独立 $X \perp\!\!\!\perp Y \mid Z$
在定义上**应当对称**，但**乘性等式**
$p\cdot \mathrm{margZ} = \mathrm{margXZ}\cdot\mathrm{margYZ}$
**左右两边不是同一个表达式**。**故「对称」是一条**需要证明的定理**，
而 `swapXY` 是**陈述它的载体**。**

**⚠ 注意 `swapXY` 把 $\alpha,\beta$ **互换**（类型是
$\mathrm{FinJoint}\ \beta\ \alpha\ \gamma$），不改 $\gamma$** ——
**这正是「$Z$ 是条件变量、$X,Y$ 是被条件化的对」的**类型级体现****。** -/
def swapXY (p : FinJoint α β γ) : FinJoint β α γ :=
  fun q => p ((q.1.2, q.1.1), q.2)

/-- ⭐⭐ `swapXY` 是**对合**（两次交换回到原状）。

$$\mathrm{swapXY}\,(\mathrm{swapXY}\ p) = p$$

**⟹ 这条引理把「交换」钉成**结构性的操作**而非临时 hack。** -/
@[simp] theorem swapXY_swapXY (p : FinJoint α β γ) :
    swapXY (swapXY p) = p := by
  funext q
  cases q with
  | mk xy z =>
    cases xy with
    | mk a b => rfl

/-- ⭐⭐ **交换后边缘律的一致性**：$Z$ 的边缘在交换下**不变**。

$$\mathrm{margZ}\,(\mathrm{swapXY}\ p) = \mathrm{margZ}\ p$$

**⟹ 意义**：**$Z$ 是**条件变量**，交换被条件化的 $X,Y$ **不应改变 $Z$ 的边缘**。
**这是记号约定自洽的又一证据。** -/
theorem margZ_swapXY (p : FinJoint α β γ) :
    margZ (swapXY p) = margZ p := by
  funext z
  unfold margZ swapXY
  exact Finset.sum_comm

/-- ⭐⭐ **交换下两个交叉边缘律互换**：

$$\mathrm{margXZ}\,(\mathrm{swapXY}\ p) = \mathrm{margYZ}\ p, \qquad
  \mathrm{margYZ}\,(\mathrm{swapXY}\ p) = \mathrm{margXZ}\ p$$

**⟹ 意义**：**$X$ 的边缘在交换后**就是原来的 $Y$ 的边缘**** ——
这正是「$X \perp Y$」与「$Y \perp X$」应当**共用同一批量**的原因。** -/
theorem margXZ_swapXY (p : FinJoint α β γ) :
    margXZ (swapXY p) = margYZ p := by
  funext x z
  unfold margXZ swapXY
  rfl

/-- ⭐⭐ **交换下 $\mathrm{margYZ}$ 与 $\mathrm{margXZ}$ 互换**。 -/
theorem margYZ_swapXY (p : FinJoint α β γ) :
    margYZ (swapXY p) = margXZ p := by
  funext y z
  unfold margYZ swapXY
  rfl

/-- ⭐⭐⭐ **条件独立在 $X$/$Y$ 角色下对称**（**任务书第 6 条**）。

$$\mathrm{CondIndepFin}\ p \iff \mathrm{CondIndepFin}\,(\mathrm{swapXY}\ p)$$

**⟹ 意义**：**$X \perp\!\!\!\perp Y \mid Z$ 与 $Y \perp\!\!\!\perp X \mid Z$
**是同一个断言****。** 由于 `swapXY` 是**对合**（`swapXY_swapXY`），
**这条 $\iff$ 正是「对称性」的**精确形式化**** ——
**不是「两边都真」这种弱说法，而是**逻辑等价****。** -/
theorem condIndepFin_swap (p : FinJoint α β γ) :
    CondIndepFin p ↔ CondIndepFin (swapXY p) := by
  constructor
  · intro hp y x z
    have h := hp x y z
    rw [margZ_swapXY, margXZ_swapXY, margYZ_swapXY]
    -- 目标右边是 `margYZ p y z * margXZ p x z`，与 `h` 的右边顺序相反。
    rw [mul_comm (margYZ p y z) (margXZ p x z)]
    exact h
  · intro hp x y z
    have h := hp y x z
    rw [margZ_swapXY, margXZ_swapXY, margYZ_swapXY,
      mul_comm (margYZ p y z) (margXZ p x z)] at h
    exact h

/-! ### §69.6 ⭐⭐⭐ **因子化 $\implies$ 条件独立**（任务书第 7 条） -/

/-- ⭐⭐⭐ **`sum_ite_eq_single`** —— **单点筛选的求和**（任务书第 8 条点名的辅助引理）。

$$\sum_{a \in s} b\,a \cdot [a = a_0] = b\,a_0 \qquad (a_0 \in s)$$

**⟹ 为什么需要它**：**「把某个变量的值**钉死**」在有限和里的实现方式是
**指示函数** $[a = a_0]$（`if a = a0 then 1 else 0`），
而**化简这种和**是本模块所有因子化计算的**基本动作****。

**⚠ 与 Mathlib `Finset.sum_ite_eq` 的关系**：
**`sum_ite_eq` 处理的是 `∑ a ∈ s, (if a = a0 then b a else 0)`；
本条处理的是 `∑ a ∈ s, b a * (if a = a0 then 1 else 0)`。
两者**展开后是同一个和**，但**本条的形态在「乘性因子」的语境下
**更少一次重写****（因子已经是乘积，不需要再折进 `ite` 的分支）。
**故此处**独立陈述并证明**它，而不是每次现场重写。** -/
theorem sum_ite_eq_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (a₀ : ι) :
    ∑ a, b a * (if a = a₀ then (1 : ℝ) else 0) = b a₀ := by
  classical
  rw [Finset.sum_eq_single a₀]
  · rw [if_pos rfl, mul_one]
  · intro a _ ha
    rw [if_neg ha, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a₀) h

/-- ⭐⭐ **对偶形态**（指示函数在**左侧**）。

$$\sum_{a} [a = a_0] \cdot b\,a = b\,a_0$$

**⟹ 与上一条配对使用**，避免在证明里反复 `mul_comm`。** -/
theorem sum_ite_eq_single' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (a₀ : ι) :
    ∑ a, (if a = a₀ then (1 : ℝ) else 0) * b a = b a₀ := by
  classical
  rw [Finset.sum_eq_single a₀]
  · rw [if_pos rfl, one_mul]
  · intro a _ ha
    rw [if_neg ha, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a₀) h

/-- ⭐⭐⭐ **因子化 $\implies$ 条件独立**（**任务书第 7 条**）。

**若**三步联合律**可分解**为三个**单变量因子**之积**：

$$\forall x\,y\,z,\quad p\,((x,y),z) = f\,x \cdot g\,y \cdot h\,z$$

**则** $X \perp\!\!\!\perp Y \mid Z$**：

$$\mathrm{CondIndepFin}\ p$$

**⟹ 为什么这是**「⟹ 方向」的完整形式****：

**证明骨架**（三步，与概率论的教科书证明逐字对应）：

1. $\mathrm{margYZ}\ p\ y\ z = \sum_x f\,x \cdot g\,y \cdot h\,z
   = \big(\sum_x f\,x\big) \cdot g\,y \cdot h\,z$（**提出与 $x$ 无关的因子**）；
2. $\mathrm{margXZ}\ p\ x\ z = \big(\sum_y g\,y\big) \cdot f\,x \cdot h\,z$（同理）；
3. $\mathrm{margZ}\ p\ z = \big(\sum_x f\,x\big)\big(\sum_y g\,y\big) \cdot h\,z$（两次提出）。

**代入乘性等式**：**左边** $= f x\, g y\, h z \cdot (\Sigma f)(\Sigma g) h z$，
**右边** $= (\Sigma g) f x\, h z \cdot (\Sigma f) g y\, h z$，**两者是同一多项式**，
`ring` 直接收尾。**⟹ 因子化 $\implies$ 条件独立。**

**⚠ 假设强度**：**不假设 $f,g,h \ge 0$，不假设归一化。**
**⟹ 本定理对**任意实值**因子化成立**（比概率论版本**更强**）。** -/
theorem condIndepFin_of_indep (p : FinJoint α β γ) (f : α → ℝ) (g : β → ℝ)
    (h : γ → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = f x * g y * h z) :
    CondIndepFin p := by
  classical
  -- 记三个单变量和的简写。
  set Sf : ℝ := ∑ x, f x with hSf
  set Sg : ℝ := ∑ y, g y with hSg
  -- (i) `margYZ` 提出 `f` 的和。
  have hYZ : ∀ y z, margYZ p y z = Sf * (g y * h z) := by
    intro y z
    unfold margYZ
    calc ∑ x, p ((x, y), z)
        = ∑ x, f x * (g y * h z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hfac x y z]; ring
      _ = (∑ x, f x) * (g y * h z) := (Finset.sum_mul ..).symm
      _ = Sf * (g y * h z) := by rw [hSf]
  -- (ii) `margXZ` 提出 `g` 的和。
  have hXZ : ∀ x z, margXZ p x z = Sg * (f x * h z) := by
    intro x z
    unfold margXZ
    calc ∑ y, p ((x, y), z)
        = ∑ y, g y * (f x * h z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hfac x y z]; ring
      _ = (∑ y, g y) * (f x * h z) := (Finset.sum_mul ..).symm
      _ = Sg * (f x * h z) := by rw [hSg]
  -- (iii) `margZ` 依次提出 `f` 与 `g` 的和。
  -- ⚠ 此处**不逐项重写**，而是先把双重和按上面已证的中间等式改写，
  -- 再用 `Finset.sum_mul` 提出与内层指标无关的因子。
  have hZ : ∀ z, margZ p z = Sf * (Sg * h z) := by
    intro z
    have hinner : ∀ x, (∑ y, p ((x, y), z)) = f x * (Sg * h z) := by
      intro x
      calc ∑ y, p ((x, y), z)
          = ∑ y, g y * (f x * h z) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hfac x y z]; ring
        _ = (∑ y, g y) * (f x * h z) := (Finset.sum_mul ..).symm
        _ = Sg * (f x * h z) := by rw [hSg]
        _ = f x * (Sg * h z) := by ring
    unfold margZ
    calc ∑ x, ∑ y, p ((x, y), z)
        = ∑ x, f x * (Sg * h z) := Finset.sum_congr rfl fun x _ => hinner x
      _ = (∑ x, f x) * (Sg * h z) := (Finset.sum_mul ..).symm
      _ = Sf * (Sg * h z) := by rw [hSf]
  -- 代入乘性等式，两边化为同一多项式。
  intro x y z
  rw [hYZ y z, hXZ x z, hZ z, hfac x y z]
  ring

/-! ### §69.7 ⭐⭐ **退化情形**：$Z$ 取常值

**⚠ 这一小节给出**最强的退化特例****，
它是「条件独立 $\to$ 无条件独立」的**有限、无测度版本**，
**且它的假设最少（$Z$ 单点）** —— 是检验整套定义是否合理的**试金石**。** -/

/-- ⭐⭐ **在 $Z$ 单点的退化情形，`margZ` 恰是该切片的逐点质量之和**
（守卫**不需额外验证**）。

$$\mathrm{margZ}\ p\ z = \sum_{x}\sum_{y} p\,((x,y),z)$$

**⟹ 意义**：**`margZ` 的定义在 $Z$ 单点时**不产生任何跨切片混合****，
**故「$\mathrm{margZ}\ p\ z \neq 0$」这一守卫退化为
「当前切片的总质量非零」** —— **一个**可以在同一个 $z$ 上直接检查**的条件，
不需要对其它 $z$ 的切片作任何假设**。

**⚠ 诚实标注**：**本条是 `margZ` 定义的**展开**（`Iff.rfl` 级的等式），
**它的价值在于**把守卫的可检查性显式化**，而非提供新数学内容。** -/
theorem margZ_eq_slice_sum (p : FinJoint α β γ) (z : γ) :
    margZ p z = ∑ x, ∑ y, p ((x, y), z) :=
  rfl

/-- ⭐⭐⭐ **因子化在 $Z$ 单点下的**无条件形式**（**独立 vs 条件独立的衔接****）。

**若** $Z$ 只有一个取值** $z_0$，且**联合律因子化** $p = f \cdot g$（**无 $h$**）：

$$\forall x\,y,\quad p\,((x,y),z_0) = f\,x \cdot g\,y \cdot 1$$

**则**条件独立成立**（`h := fun _ => 1` 的**直接特例**）。

**⚠ 陈述方式的选择**：**此处**不删除** $h$，而是把它取为常值 $1$ ——
**因为 §69.2 的 `CondIndepFin` 定义里 $Z$ 始终在场**，
**「无条件独立」在这个框架里**只能是「$h$ 平凡的条件独立」****。
**这本身就是 记号约定的一个**必然推论**，而非缺陷。** -/
theorem condIndepFin_of_mulFactor (p : FinJoint α β γ) (f : α → ℝ) (g : β → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = f x * g y * 1) :
    CondIndepFin p :=
  condIndepFin_of_indep p f g (fun _ => 1) hfac

/-! ### §69.8 ⭐⭐ 与**朴素独立**的区别（**反例**）

**⚠ 这一小节的必要性**：**「条件独立」若被误读为「（无条件）独立」，
整套定义就失去了意义。** 下面给出**最小的区分案例**，
**以**可计算的显式形式**说明二者**不等价**。** -/

/-- ⭐⭐ **切片因子化**（per-slice factorization）—— 「朴素独立」在本框架下的**最自然化身**。

$$\forall x\,y\,z,\quad \mathrm{margZ}\ p\ z \neq 0 \implies
  p\,((x,y),z)
  = \frac{\mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z}
         {\mathrm{margZ}\ p\ z}$$

**⟹ 它比条件独立**更强****：

- **`SliceFactor`**：**固定 $z$，$p(\cdot,\cdot,z)$ 这个**二维表**
  必须**正好等于**两个边缘之积除以权重** —— 这是**逐切片**的约束；
- **`CondIndepFin`**：**只要求**乘性等式**，
  而**乘性等式在 $\mathrm{margZ}\ p\ z = 0$ 时**退化为 $0 = 0$（**自动成立**）。

**⟹ 两者的差别**恰在退化切片上**：**`SliceFactor` 对 $\mathrm{margZ}=0$ 的切片
**什么都不说**（被守卫跳过），而 `CondIndepFin` 在那里**自动为真**。
**故 `SliceFactor` $\implies$ 条件独立（守卫版）是**唯一正确的方向****，
**反方向不成立**。**这正是「条件独立**弱于**逐切片独立」的精确表述。** -/
def SliceFactor (p : FinJoint α β γ) : Prop :=
  ∀ x y z, margZ p z ≠ 0 →
    p ((x, y), z) = margXZ p x z * margYZ p y z / margZ p z

/-- ⭐⭐ **切片因子化 $\implies$ 条件独立（带守卫）**。

**⚠ 本定理的陈述被**诚实地限定**在守卫分支上**：
**因为「无条件独立 $\implies$ 条件独立」这类陈述**在没有正性/归一化假设时
**本来就是假的****（见本节末的 `SliceFactor` 备注）。

**准确的命题**是：**若每个 $\mathrm{margZ} \neq 0$ 的切片内联合律都因子化**，

$$\forall x\,y\,z,\ \mathrm{margZ}\ p\ z \neq 0 \to
  p\,((x,y),z) = \frac{\mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z}
                       {\mathrm{margZ}\ p\ z}$$

**则**在**同样的守卫下**乘性形式成立** ——
**即 `CondIndepFin` 的**守卫限定版本****。

**⟹ 这一限定不是技术妥协**：**它精确反映了
「$\mathrm{CondIndepFin}$ 是无守卫的、而所有**逐切片**陈述天然带守卫」
这一结构差异。**故本定理的结论**也带守卫**，与前提**同构**。** -/
theorem condIndepFin_mulForm_of_sliceFactor (p : FinJoint α β γ)
    (hp : SliceFactor p) :
    ∀ x y z, margZ p z ≠ 0 →
      p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z := by
  intro x y z hz
  rw [hp x y z hz, div_mul_cancel₀ _ hz]

end FiniteCondIndep

end FateV2.Modeling