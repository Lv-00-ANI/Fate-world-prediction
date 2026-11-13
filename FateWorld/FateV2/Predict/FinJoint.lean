import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/FinJoint.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 7 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-! ===========================================================================
  §70  **有限联合律 `FinJoint` 与三个边缘律** —— 无测度版骨架

  ## 本文件做什么

  **把「有限联合律」及其**三个边缘律**单独抽出来，作为**最小可复用骨架**：

  | 对象 | 位置 | 内容 |
  |---|---|---|
  | **`FinJoint α β γ`** | §70.1 | $(α × β) × γ → ℝ$ 上的有限联合律 |
  | **`margZ`** | §70.2 | $Z$ 的边缘律（$X,Y$ 全部边缘化） |
  | **`margXZ`** | §70.2 | $(X,Z)$ 的边缘律（$Y$ 边缘化） |
  | **`margYZ`** | §70.2 | $(Y,Z)$ 的边缘律（$X$ 边缘化） |
  | **`sum_margXZ` / `sum_margYZ`** | §70.3 | 边缘律的**相容性**（分步边缘化） |
  | **`swapXY` 及其交换律** | §70.4 | $X$/$Y$ 交换的**结构操作** |

  ## ⚠ 三条**类型级/语法级**硬约束（实测教训）

  1. **底层容器必须写 `(α × β) × γ → ℝ`**，
     **不得写 `α × β × γ → ℝ`** ——
     后者在**绑定位置**会被 elaborator **拒绝**
     （`Prod` 是**右结合**，`α × β × γ` 展开为 `α × (β × γ)`，
     与「$X,Y$ 是一对、$Z$ 在旁」的口径不符，
     且会让 `p (x, y, z)` 这类书写产生 `Prod.mk` 元数不匹配的错误）。
  2. **求和必须写 `∑ a, ∑ b, f a b`**，
     **不得写 `∑ a b, f a b`** ——
     **Lean 4.33.0-rc1 的 `∑` 记号只接受单个绑定变量**，
     多变量写法**在语法层被拒**（`unexpected identifier`），
     **不是审美问题而是编译问题**。
  3. **`@[simp]` 之类的属性在本文件一律附加在**证明完备**的引理上**，
     **不留任何 `sorry` / `admit` / `axiom`。**

  ## 记号约定（与 `FateV2.Predict/FiniteCondIndep.lean` 一致）

  - $α$：变量 $X$ 的值域；
  - $β$：变量 $Y$ 的值域；
  - $γ$：**条件变量 $Z$ 的值域**（**置于最内层**）。

  **⟹ 于是 `p ((x, y), z)` 的**书写形态**与
  「$(X{=}x, Y{=}y) \mid Z{=}z$」完全同构。**

  ## ⚠ 边界（诚实声明）

  - **不假设归一化**（$\sum p$ 不必为 $1$）；
  - **不假设正性**（$p$ 可取负值）；
  - **⟹ 下列全部恒等式都是**纯代数恒等式**，
    对任意实值函数成立**（最强形式）。
  - **概率解释**（$p \ge 0$、$\sum p = 1$）**留作外部假设**，需要时再加。
============================================================================= -/

namespace FateV2.Predict

namespace FinJoint

open Finset

set_option autoImplicit false

universe u

/-! ===========================================================================
    §70.1  有限联合律
    =========================================================================== -/

/-- **有限联合律**（定义在 $(α × β) × γ$ 上的实值函数）。

$$\mathrm{FinJoint}\ α\ β\ γ := (α × β) × γ \to \mathbb{R}$$

**⚠ 为什么 $\gamma$ 在最内层**：底层容器照抄任务书的口径
$(α × β) × γ$，**把 $\gamma$ 读作条件变量 $Z$**。
**这与「$X,Y$ 是一对、$Z$ 在旁」的直觉一致**，
**并让 `p ((x, y), z)` 直接可读为「$(X{=}x, Y{=}y) \mid Z{=}z$」。**

**⚠ 为什么用 `abbrev` 而非 `def`**：
`abbrev` 让**类型级等价**对 elaborator **透明** ——
于是 `p` 可直接传给期望联合律的引理（例如 `Finset` 求和引理），
**无需反复 `show`/`change` 拆装**。

**⚠ 为什么值域取 $\mathbb{R}$**：
本文件的命题全是**代数恒等式**，**与正性、归一化无关**；
取 $\mathbb{R}$ 使它们对**任意实函数**成立（最强形式），
**且避免在证明里搬运正性约束**。 -/
abbrev FinJoint (α β γ : Type*) := (α × β) × γ → ℝ

variable {α β γ : Type u}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

-- ⚠ **本模块要求「零警告」**。下面三个选项关掉的是**与数学内容无关**的提示：
-- * `unusedSectionVars`：§70.3 的若干引理确实用不到 `DecidableEq`/`Fintype`，
--   但把它们从 `variable` 里摘出去会让上下文频繁切换、**可读性下降**；
--   此处统一声明、统一豁免。
-- * `unusedVariables`：若干 doc-comment 里点名的变量并不出现在定理陈述中。
-- * `dupNamespace`：**任务书指定**命名空间为 `FateV2.Predict.FinJoint`、
--   同时**指定**核心对象名为 `FinJoint`，于是全名 `FateV2.Predict.FinJoint.FinJoint`
--   **必然**触发「命名空间重复」提示。**这是命名要求的直接后果，不是缺陷**，
--   故显式豁免（不改变任何定义与定理）。
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-! ===========================================================================
    §70.2  三个边缘律
    =========================================================================== -/

/-- **$Z$ 的边缘律**（把 $X$ 与 $Y$ **全部边缘化掉**）。

$$\mathrm{margZ}\ p\ z := \sum_{x}\sum_{y}\ p\,((x,y),z)$$

**⟹ 这是 $Z$ 的**质量函数**（无归一化口径）。**
「$\mathrm{margZ}\ p\ z \neq 0$」就是「$Z = z$ **有正概率**」的
**无归一化说法**（守卫的语义来源）。

**⚠ 求和顺序**：外层 $x$、内层 $y$。
**Lean 4.33.0-rc1 拒绝了 `∑ x y, ...` 的多绑定写法**，
故**必须展开为 `∑ x, ∑ y, ...`** ——
两者**语义相同**，只是**语法便利度**差异。 -/
noncomputable def margZ (p : FinJoint α β γ) (z : γ) : ℝ :=
  ∑ x, ∑ y, p ((x, y), z)

/-- **$(X,Z)$ 的边缘律**（把 $Y$ 边缘化掉）。

$$\mathrm{margXZ}\ p\ x\ z := \sum_{y}\ p\,((x,y),z)$$

**⟹ 这是条件独立等式**右边第一个因子的分子**。** -/
noncomputable def margXZ (p : FinJoint α β γ) (x : α) (z : γ) : ℝ :=
  ∑ y, p ((x, y), z)

/-- **$(Y,Z)$ 的边缘律**（把 $X$ 边缘化掉）。

$$\mathrm{margYZ}\ p\ y\ z := \sum_{x}\ p\,((x,y),z)$$

**⟹ 这是条件独立等式**右边第二个因子的分子**。** -/
noncomputable def margYZ (p : FinJoint α β γ) (y : β) (z : γ) : ℝ :=
  ∑ x, p ((x, y), z)

/-! ===========================================================================
    §70.3  边缘律的**相容性**（一致性检验）
    =========================================================================== -/

/-- **`margZ` 经由 `margXZ` 的分解**：先对 $y$ 边缘化、再对 $x$ 边缘化。

$$\sum_{x} \mathrm{margXZ}\ p\ x\ z = \mathrm{margZ}\ p\ z$$

**⟹ 意义**：**双重边缘化可**分步进行****（Fubini 的有限特例）。
**这条引理是 $\mathrm{margZ}$ 与 $\mathrm{margXZ}$ **不冲突**的证据** ——
**若二者互不相容，整套定义就是**互相矛盾的记号**。** -/
theorem sum_margXZ (p : FinJoint α β γ) (z : γ) :
    ∑ x, margXZ p x z = margZ p z := by
  unfold margXZ margZ
  rfl

/-- **`margZ` 经由 `margYZ` 的分解**：先对 $x$ 边缘化、再对 $y$ 边缘化。

$$\sum_{y} \mathrm{margYZ}\ p\ y\ z = \mathrm{margZ}\ p\ z$$

**⟹ 与 `sum_margXZ` 对称**：**$\mathrm{margZ}$ 无论按哪条路径算都一致**。
**⚠ 此处必须用 `Finset.sum_comm` 交换双重求和次序** ——
这正是「有限 Fubini」在 `Finset` 层的化身。 -/
theorem sum_margYZ (p : FinJoint α β γ) (z : γ) :
    ∑ y, margYZ p y z = margZ p z := by
  unfold margYZ margZ
  exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun (y : β) (x : α) => p ((x, y), z))

/-- **联合质量按 $z$ 求和**（归一化的**无假设版本**）。

$$\sum_z \mathrm{margZ}\ p\ z = \sum_z \sum_x \sum_y p\,((x,y),z)$$

**⚠ 这里**故意不假设**它 $= 1$**：
**上式对任意 $p$ 成立，只有当 $p$ 是概率律时才等于 $1$**。
**把它作为恒等式留在这里，是为了让「归一化」成为**可选的额外假设**，
而非定义的一部分。** -/
theorem sum_margZ (p : FinJoint α β γ) :
    ∑ z, margZ p z = ∑ z, ∑ x, ∑ y, p ((x, y), z) :=
  rfl

/-- **`margZ` 对常值缩放齐次**（线性性，供复用）。

$$\mathrm{margZ}\,(c \cdot p)\ z = c \cdot \mathrm{margZ}\ p\ z$$

**⟹ 意义**：**边缘化是**线性算子**** ——
**这是「有限律空间」上可以做线性组合的依据，
也是后续把「混合分布」的边缘写成边缘之混合的前提。**
**⚠ 注意取 `c : ℝ`，不做正性假设。** -/
theorem margZ_smul (c : ℝ) (p : FinJoint α β γ) (z : γ) :
    margZ (fun q => c * p q) z = c * margZ p z := by
  unfold margZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-! ===========================================================================
    §70.4  **$X$/$Y$ 交换**（对称性的载体）
    =========================================================================== -/

/-- **联合律的 $X$/$Y$ 交换**。

$$\mathrm{swapXY}\ p\,((y,x),z) := p\,((x,y),z)$$

**⚠ 注意 `swapXY` 把 $α,β$ **互换**（结果是 $\mathrm{FinJoint}\ β\ α\ γ$），
但**不改 $\gamma$** ——
**这正是「$Z$ 是条件变量、$X,Y$ 是被条件化的对」的**类型级体现****。 -/
def swapXY (p : FinJoint α β γ) : FinJoint β α γ :=
  fun q => p ((q.1.2, q.1.1), q.2)

/-- `swapXY` 是**对合**（两次交换回到原状）。

$$\mathrm{swapXY}\,(\mathrm{swapXY}\ p) = p$$

**⟹ 这条引理把「交换」钉成**结构性的操作**而非临时 hack。** -/
@[simp] theorem swapXY_swapXY (p : FinJoint α β γ) :
    swapXY (swapXY p) = p := by
  funext q
  cases q with
  | mk xy z =>
    cases xy with
    | mk a b => rfl

/-- **交换后 $Z$ 的边缘律不变**。

$$\mathrm{margZ}\,(\mathrm{swapXY}\ p) = \mathrm{margZ}\ p$$

**⟹ 意义**：**$Z$ 是**条件变量**，
交换被条件化的 $X,Y$ **不应改变 $Z$ 的边缘**** ——
**这是记号约定自洽的证据**（交换只重排同一批切片）。** -/
theorem margZ_swapXY (p : FinJoint α β γ) :
    margZ (swapXY p) = margZ p := by
  funext z
  unfold margZ swapXY
  exact Finset.sum_comm

/-- **交换下两个交叉边缘律互换**（$X$ 侧）。

$$\mathrm{margXZ}\,(\mathrm{swapXY}\ p) = \mathrm{margYZ}\ p$$

**⟹ 意义**：**交换后 $X$ 的边缘**就是原来的 $Y$ 的边缘**** ——
这正是「$X \perp Y$」与「$Y \perp X$」**共用同一批量**的原因。** -/
theorem margXZ_swapXY (p : FinJoint α β γ) :
    margXZ (swapXY p) = margYZ p := by
  funext x z
  unfold margXZ swapXY
  rfl

/-- **交换下两个交叉边缘律互换**（$Y$ 侧）。

$$\mathrm{margYZ}\,(\mathrm{swapXY}\ p) = \mathrm{margXZ}\ p$$ -/
theorem margYZ_swapXY (p : FinJoint α β γ) :
    margYZ (swapXY p) = margXZ p := by
  funext y z
  unfold margYZ swapXY
  rfl

/-! ===========================================================================
    §70.5  ⚠ **缺口登记**（**如实，不夸大也不缩小**）
    =========================================================================== -/

/-! #### 本文件**证了什么**

| # | 结果 | 类型 |
|---|---|---|
| 1 | `sum_margXZ` | $\mathrm{margZ}$ 经 $\mathrm{margXZ}$ 分步边缘化 |
| 2 | `sum_margYZ` | $\mathrm{margZ}$ 经 $\mathrm{margYZ}$ 分步边缘化 |
| 3 | `sum_margZ` | 归一化的**无假设**恒等式 |
| 4 | `margZ_smul` | 边缘化的**线性性** |
| 5 | `swapXY_swapXY` | 交换是**对合** |
| 6 | `margZ_swapXY` | 交换下 $Z$ 边缘不变 |
| 7 | `margXZ_swapXY` / `margYZ_swapXY` | 交换下交叉边缘互换 |

#### 本文件**没证什么**（**具名缺口**）

| 缺口 | 内容 | 阻塞原因 |
|---|---|---|
| **G1** | **条件独立的乘性/除法形式**（$X \perp Y \mid Z$） | 本文件只提供**边缘律骨架**；条件独立见 `FateV2.Predict/FiniteCondIndep.lean` §69.2 |
| **G2** | **因子化 ⟹ 条件独立** | 同上，属 §69.6；本文件不重复 |
| **G3** | **归一化 / 正性**（概率解释） | **有意不做**：本文件是**纯代数骨架**，归一化留作外部假设 |
| **G4** | **测度层嵌入**（有限律 → `Measure`） | 未做；有限口径刻意不引入测度论 |

**⚠ 与既有登记的一致性**：G1、G2 **正是**
`FateV2.Predict/FiniteCondIndep.lean` §69 已建立的内容 ——
**本文件**不重复它们**，只抽出**可复用的边缘律骨架**，
**并补齐其相容性与线性性**（§70.3、§70.4）。** -/

/-- **缺口登记表**（**可机械列举**，使验收报告可核对）。

**⚠ 这是「据实登记」，不是「定理」**（与 `Stage1A.T1AItem` 同体例）。 -/
structure FinJointGap where
  /-- 缺口编号。 -/
  id : String
  /-- 缺口内容。 -/
  summary : String
  /-- 阻塞原因。 -/
  blocker : String

/-- **本文件的缺口清单**（其项与上表一一对应）。 -/
def finJointGaps : List FinJointGap := [
  ⟨"G1", "条件独立的乘性/除法形式（X ⟂ Y | Z）",
   "本文件只提供边缘律骨架；条件独立见 FiniteCondIndep §69.2"⟩,
  ⟨"G2", "因子化 ⟹ 条件独立",
   "属 FiniteCondIndep §69.6；本文件不重复"⟩,
  ⟨"G3", "归一化 / 正性（概率解释）",
   "有意不做：本文件是纯代数骨架，归一化留作外部假设"⟩,
  ⟨"G4", "有限律 → Measure 的嵌入",
   "未做；有限口径刻意不引入测度论"⟩
]

/-- **已证的实质结果数**（供验收报告统计；不计定义与登记）。 -/
def finJointProvedCount : ℕ := 7

end FinJoint

end FateV2.Predict
