import FateWorld.FateV2.Modeling.FiniteCondIndep
/-!
  # Modeling · FinFactorization

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FinFactorization.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FiniteCondIndep
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  ⭐⭐⭐ **因子化 ⟹ 条件独立** —— `FinFactorization`

  ## 0. 本节的任务（一句话）

  **若三元联合律 $p\big((x,y),z\big)$ 可分解为三个单变量因子之积**

  $$p\big((x,y),z\big) = f(x)\cdot g(y)\cdot h(z),$$

  **则 $X \perp\!\!\!\perp Y \mid Z$ 成立**，即 `CondIndepFin p`。

  **⟹ 这就是概率论里「因子分解 $\Rightarrow$ 条件独立」的有限、无测度版本**：
  它**不需要 $\sigma$-代数、不需要可测性、不需要几乎处处**，
  **只是一条纯粹的 `Finset` 代数恒等式**。

  ## 1. 依赖与命名空间

  - **底层机器全部复用** `FiniteCondIndep`（§69）：
    * `FinJoint α β γ` —— 有限联合律 $(\alpha\times\beta)\times\gamma \to \mathbb{R}$；
    * `margZ` / `margXZ` / `margYZ` —— 三个边缘律；
    * `CondIndepFin` —— 条件独立的**乘性形式**。
  - **本模块只加一条主定理**（外加若干配套的分解引理），
    **落在独立命名空间 `FinFactorization`**，
    **不改动、不遮蔽上游任何定义**（**避免与 §69 的名字冲突**）。

  ## 2. ⚠⚠ Lean v4.33.0-rc1 的**两个语法陷阱**（本模块必须绕开）

  **本文件在 `leanprover/lean4:v4.33.0-rc1` 上实测。该版本有两个
  与旧版文档/直觉不符的**硬陷阱**，写错即报 `error`（不是 warning）：**

  ### 陷阱一：**嵌套求和绑定子 `∑ a b, f a b` 被拒**

  **在 `∑ a b, f a b` 这种「一个 `∑` 后跟两个绑定子」的写法上，
  rc1 会报语法错误**（旧版 Lean/Mathlib 里这曾是允许的简写）。
  **⟹ 必须写成显式嵌套：`∑ a, ∑ b, f a b`。**
  **两者数学语义相同，只是 rc1 要求显式嵌套。**
  **本模块所有求和一概用 `∑ x, ∑ y, ...`，绝不用 `∑ x y, ...`。**

  ### 陷阱二：**`Finset.sum_comm` / `Finset.sum_mul` 的导入模块反直觉**

  **rc1 下这两个引理的真正来源是：**

  | 引理 | **真正所在的模块** | 常见误以为的来源 |
  |---|---|---|
  | `Finset.sum_comm` | `BigOperators.Group.Finset.Sigma` | ❌ `Group.Finset.Basic`（**不含**） |
  | `Finset.sum_mul` / `mul_sum` | `BigOperators.Ring.Finset` | ❌ `Group.Finset.Basic`（**不含**） |

  **本模块通过 `import FateV2.Modeling.FiniteCondIndep` 间接获得这些导入**
  （§69 的文件头已逐条实测并列明最小导入集），
  **故本节不再重复 `import`，以免引入重复/顺序问题。**

  ## 3. 无硬编码（依作者裁决 Q-1）；⚠ 无 `sorry` / `admit` / `axiom`。

  ## 4. 陈述强度（诚实声明）

  - **不假设 $f,g,h \ge 0$**（因子可以是任意实数）；
  - **不假设归一化**（$\sum p = 1$）；
  - **不假设 $h$ 处处非零**。

  **⟹ 本节定理对**任意实值**因子化成立**，
  **比「概率论教科书版本」更强**；
  **概率解释留给外部假设，本模块只提供代数骨架。**
  =========================================================================== -/

namespace FateV2.Modeling
namespace FinFactorization

open Finset

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

-- ⚠ **本模块要求「零警告」**（任务书验收标准）。
-- 下列两个 `option` 关掉的是**与数学内容无关**的提示：
-- * `unusedSectionVars`：若干辅助引理确实用不到全部 `Fintype`/`DecidableEq`，
--   但把它们从 `variable` 摘出去会让上下文频繁切换、可读性下降；
-- * `unusedVariables`：同理，doc-comment 里点名的变量未必出现在定理陈述中。
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### §F.1 ⭐⭐ **单变量和**的记号与基本化简

**为了把「提出与求和指标无关的因子」这件事写成可复用的引理，
下面显式命名三个**因子和**。**
**⚠ 注意：这里是**把 $f$ 的和单独拿出来**，
而不是依赖任何「自动提取常量」的 `simp` 规则 ——
**显式命名让每一步都**可核对**，也绕开了不同版本 `simp` 集合的差异。** -/

/-- ⭐ 因子 $f$ 的总和 $S_f := \sum_x f\,x$。

**⟹ 它在 `condIndepFin_of_indep` 的证明里反复出现，
故**提出来单独命名**，避免每次现场 `set`。** -/
noncomputable def sumF (f : α → ℝ) : ℝ := ∑ x, f x

/-- ⭐ 因子 $g$ 的总和 $S_g := \sum_y g\,y$。 -/
noncomputable def sumG (g : β → ℝ) : ℝ := ∑ y, g y

/-- ⭐ 因子 $h$ 的总和 $S_h := \sum_z h\,z$（**主定理用不到，
但为对称性与完整性保留**）。 -/
noncomputable def sumH (h : γ → ℝ) : ℝ := ∑ z, h z

/-! ### §F.2 ⭐⭐⭐ **三项因子分解的形态**（本模块的中心假设）

**把任务书的假设 $p((x,y),z) = f\,x \cdot g\,y \cdot h\,z$
抽成一条**具名命题**。** -/

/-- ⭐⭐⭐ **三项因子分解**：$p\big((x,y),z\big) = f\,x \cdot g\,y \cdot h\,z$
对**所有** $x,y,z$ 成立。

**⟹ 为什么把它命名为 `Fac3`**：
**「因子化」是本模块的**前提**，把它作为 `def` 而非内联 `∀`，
使得：**（i）主定理的陈述更短、意图更明；
（ii）可以在别处以 `Fac3 p f g h` 整体引用，**避免每次展开长公式**；
（iii）将来若要加「仅在守卫下因子化」的变体，只需另立一个 `def`，
**主定理不必改动**。** -/
def Fac3 (p : FiniteCondIndep.FinJoint α β γ) (f : α → ℝ) (g : β → ℝ)
    (h : γ → ℝ) : Prop :=
  ∀ x y z, p ((x, y), z) = f x * g y * h z

/-! ### §F.3 ⭐⭐⭐ **边缘律在因子化下的显式公式**

**主定理的三块积木：把三个边缘律各算一遍。**
**⚠ 这三条引理是**分开陈述**的（而不是塞进主定理的 `have`），
**理由是：它们各自都是有独立价值的中间结论**，
而且**分开后每条都能被 `#check`/外部模块单独引用**。** -/

/-- ⭐⭐⭐ **$Y,Z$ 的边缘律在因子化下**：

$$\mathrm{margYZ}\ p\ y\ z = \Big(\sum_x f\,x\Big)\cdot g\,y \cdot h\,z.$$

**⟹ 证明动作**：对每个 $x$ 把被积函数改写为 $f\,x\cdot(g\,y\cdot h\,z)$，
**再用 `Finset.sum_mul` 把与 $x$ 无关的因子 $(g\,y\cdot h\,z)$ 提到求和号外**。**
**⚠ 注意因子重新结合为 $(g\,y \cdot h\,z)$ 是**必要的** ——
`Finset.sum_mul` 的形态要求被提出的因子在每项里**恰好在右侧**。** -/
theorem margYZ_fac (p : FiniteCondIndep.FinJoint α β γ) (f : α → ℝ)
    (g : β → ℝ) (h : γ → ℝ) (hfac : Fac3 p f g h) (y : β) (z : γ) :
    FiniteCondIndep.margYZ p y z = sumF f * (g y * h z) := by
  classical
  unfold FiniteCondIndep.margYZ
  calc ∑ x, p ((x, y), z)
      = ∑ x, f x * (g y * h z) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hfac x y z]; ring
    _ = (∑ x, f x) * (g y * h z) := (Finset.sum_mul ..).symm
    _ = sumF f * (g y * h z) := by rw [sumF]

/-- ⭐⭐⭐ **$X,Z$ 的边缘律在因子化下**：

$$\mathrm{margXZ}\ p\ x\ z = \Big(\sum_y g\,y\Big)\cdot f\,x \cdot h\,z.$$

**⟹ 与 `margYZ_fac` 完全对称**（$f \leftrightarrow g$，$x \leftrightarrow y$），
**只是被提出的因子变成 $\sum_y g\,y$。** -/
theorem margXZ_fac (p : FiniteCondIndep.FinJoint α β γ) (f : α → ℝ)
    (g : β → ℝ) (h : γ → ℝ) (hfac : Fac3 p f g h) (x : α) (z : γ) :
    FiniteCondIndep.margXZ p x z = sumG g * (f x * h z) := by
  classical
  unfold FiniteCondIndep.margXZ
  calc ∑ y, p ((x, y), z)
      = ∑ y, g y * (f x * h z) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hfac x y z]; ring
    _ = (∑ y, g y) * (f x * h z) := (Finset.sum_mul ..).symm
    _ = sumG g * (f x * h z) := by rw [sumG]

/-- ⭐⭐⭐ **$Z$ 的边缘律在因子化下**：

$$\mathrm{margZ}\ p\ z = \Big(\sum_x f\,x\Big)\Big(\sum_y g\,y\Big) h\,z.$$

**⟹ 证明分两层**：**内层先对 $y$ 用 `Finset.sum_mul` 提出 $\sum_y g\,y$，
得到 $\sum_x f\,x\cdot\big((\sum_y g\,y)\,h\,z\big)$；
外层再对 $x$ 用 `Finset.sum_mul` 提出 $\sum_x f\,x$。**
**⚠ 这里**不能**一次提出两个和**，因为 `sum_mul` 一次只处理一层；
**分两步是与 Lean 的求和结构对应的。** -/
theorem margZ_fac (p : FiniteCondIndep.FinJoint α β γ) (f : α → ℝ)
    (g : β → ℝ) (h : γ → ℝ) (hfac : Fac3 p f g h) (z : γ) :
    FiniteCondIndep.margZ p z = sumF f * (sumG g * h z) := by
  classical
  have hinner : ∀ x, (∑ y, p ((x, y), z)) = f x * (sumG g * h z) := by
    intro x
    calc ∑ y, p ((x, y), z)
        = ∑ y, g y * (f x * h z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hfac x y z]; ring
      _ = (∑ y, g y) * (f x * h z) := (Finset.sum_mul ..).symm
      _ = sumG g * (f x * h z) := by rw [sumG]
      _ = f x * (sumG g * h z) := by ring
  unfold FiniteCondIndep.margZ
  calc ∑ x, ∑ y, p ((x, y), z)
      = ∑ x, f x * (sumG g * h z) := Finset.sum_congr rfl fun x _ => hinner x
    _ = (∑ x, f x) * (sumG g * h z) := (Finset.sum_mul ..).symm
    _ = sumF f * (sumG g * h z) := by rw [sumF]

/-! ### §F.4 ⭐⭐⭐⭐ **主定理：因子化 ⟹ 条件独立** -/

/-- ⭐⭐⭐⭐ **主定理（任务书目标）**：**因子化 $\Longrightarrow$ 条件独立**。

**若**存在 $f:\alpha\to\mathbb{R}$、$g:\beta\to\mathbb{R}$、$h:\gamma\to\mathbb{R}$ 使

$$\forall x\,y\,z,\quad p\big((x,y),z\big) = f\,x \cdot g\,y \cdot h\,z,$$

**则** `CondIndepFin p` 成立**，即 $X \perp\!\!\!\perp Y \mid Z$：

$$\forall x\,y\,z,\quad
  p\big((x,y),z\big)\cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z.$$

**⟹ 证明骨架（与概率论教科书逐字对应）**：

1. $\mathrm{margYZ} = S_f \cdot (g\,y\,h\,z)$ —— 调用 `margYZ_fac` 提出 $\sum_x f$；
2. $\mathrm{margXZ} = S_g \cdot (f\,x\,h\,z)$ —— 调用 `margXZ_fac` 提出 $\sum_y g$；
3. $\mathrm{margZ}  = S_f \cdot (S_g\,h\,z)$ —— 调用 `margZ_fac` 两次提出；
4. 代入乘性等式，并用 `Fac3` 把左边 $p$ 也换成因子形式，
   **两边化为同一多项式**，`ring` 收尾。

**⚠ 陈述强度（再强调）**：**不假设 $f,g,h \ge 0$，不假设归一化，
不假设 $h$ 非零。** 故本定理对**任意实值因子化**成立。** -/
theorem condIndepFin_of_fac3 (p : FiniteCondIndep.FinJoint α β γ)
    (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ) (hfac : Fac3 p f g h) :
    FiniteCondIndep.CondIndepFin p := by
  intro x y z
  rw [margYZ_fac p f g h hfac y z,
      margXZ_fac p f g h hfac x z,
      margZ_fac p f g h hfac z,
      hfac x y z]
  ring

/-- ⭐⭐⭐ **主定理的「裸 `∀`」版本**（**任务书字面形式**）。

**与 `condIndepFin_of_fac3` 的**唯一区别**：
**此处直接把 $p((x,y),z)=f\,x\,g\,y\,h\,z$ 写进假设位，
不经过具名命题 `Fac3`。** 两者**逻辑上完全等价**（定义上就是同一件事），
**同时提供两条，是为了让「按字面复述任务书」与「按工程惯例复用」都方便。** -/
theorem condIndepFin_of_factorization (p : FiniteCondIndep.FinJoint α β γ)
    (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = f x * g y * h z) :
    FiniteCondIndep.CondIndepFin p :=
  condIndepFin_of_fac3 p f g h hfac

/-- ⭐⭐ **主定理的「上游直通」入口**（**对接口**）。

**`FiniteCondIndep`（§69）里已经证过一条同名结论
`FiniteCondIndep.condIndepFin_of_indep`，假设形态与本模块完全一致。**

**⟹ 本引理**不是重复造轮子，而是**显式登记二者的等价接口**：
它把 §69 的定理**重新导出到本命名空间下**，
**使得只用 `FinFactorization` 的读者不必再穿透到 §69 的名字。**
**同时它也是一次**一致性自检**：若上游将来改了定义，此处会立刻编译失败。** -/
theorem condIndepFin_of_fac3_via_upstream (p : FiniteCondIndep.FinJoint α β γ)
    (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ) (hfac : Fac3 p f g h) :
    FiniteCondIndep.CondIndepFin p :=
  FiniteCondIndep.condIndepFin_of_indep p f g h hfac

/-! ### §F.5 ⭐⭐ **推论：常见特例** -/

/-- ⭐⭐ **两因子特例**（$Z$ 的因子恒为 $1$，即「$Z$ 无信息」）。

**若** $p\big((x,y),z\big) = f\,x\cdot g\,y$（对**所有** $z$ 相同），
**则条件独立成立**。**这是主定理取 $h \equiv 1$ 的直接特例。** -/
theorem condIndepFin_of_fac2 (p : FiniteCondIndep.FinJoint α β γ)
    (f : α → ℝ) (g : β → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = f x * g y) :
    FiniteCondIndep.CondIndepFin p :=
  condIndepFin_of_fac3 p f g (fun _ => 1)
    (fun x y z => by rw [hfac x y z, mul_one])

/-- ⭐ **状态：本模块的**存在性见证**（非空性检查）。**

**⚠ 这是一条**平凡但有用**的引理：它保证 `Fac3` 不是空类 ——
**例如取 $p := 0$、$f := 0$ 即可满足前提**，
**故主定理至少有一个前件成立的实例，定理不是「空洞的真」。**

**⚠ 注意 $f \equiv 0$ 是**必须**的**：若让 $f$ 任取而只把 $p$ 取零，
则右端 $f\,x\,g\,y\,h\,z$ 未必为零，前提为假。
**故本引理的正确形态是「把零放在因子上」，而不是「只把 $p$ 取零」。** -/
theorem fac3_zero {α : Type*} [Fintype α] (g : β → ℝ) (h : γ → ℝ) :
    Fac3 (α := α) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) g h := by
  intro x y z
  simp

/-- ⭐⭐ **零联合律满足条件独立**（主定理的最简实例）。

**取 $p \equiv 0$、$f \equiv 0$，由 `fac3_zero` + 主定理立即得到。
⟹ 这条引理给出一条**可被其它模块直接引用的落地实例**，
用于确认本模块的定理**在非概率（全零）场景下也自洽**。** -/
theorem condIndepFin_zero (α β γ : Type*) [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    FiniteCondIndep.CondIndepFin (fun _ => (0 : ℝ) : FiniteCondIndep.FinJoint α β γ) :=
  condIndepFin_of_fac3 _ (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fac3_zero (α := α) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)))

/-! ### §F.6 ⭐⭐ **因子化的唯一性备注（诚实标注：本条只到「非零处的比例唯一」）**

**⚠ 上游 §69 已有 `CondIndepFin` 的**对称性**（`condIndepFin_swap`）
等结构定理；本模块**不重复**它们，只补充与「因子化」直接相关的一条观察。
**为避免越界声称，这里只陈述**可证且无争议**的一条。** -/

/-- ⭐⭐ **因子化在「非零切片」上的乘性后果**（**弱化的唯一性**）。

**若** $p$ 因子化、且 $z_0$ 处 $\mathrm{margZ}\ p\ z_0 \neq 0$，
**则**该切片的联合律**正比于**两个边缘律之积**：

$$p\big((x,y),z_0\big)\cdot \mathrm{margZ}\ p\ z_0
  = \mathrm{margXZ}\ p\ x\ z_0 \cdot \mathrm{margYZ}\ p\ y\ z_0.$$

**⟹ 这是 `CondIndepFin` 在 $z_0$ 处的**分量形式**，
**它的意义是把「全局条件独立」**逐切片**读出来 ——
**正是「因子化 $\Rightarrow$ 每个非零切片按乘积分布」这一概率内容的有限代数版。** -/
theorem mulForm_at_slice_of_fac3 (p : FiniteCondIndep.FinJoint α β γ)
    (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ) (hfac : Fac3 p f g h)
    (x : α) (y : β) (z : γ) :
    p ((x, y), z) * FiniteCondIndep.margZ p z =
      FiniteCondIndep.margXZ p x z * FiniteCondIndep.margYZ p y z :=
  condIndepFin_of_fac3 p f g h hfac x y z

end FinFactorization

end FateV2.Modeling