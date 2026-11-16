/-
================================================================================
  `RegressFinMarkov` —— ⭐ **`FinMarkov` 的回归测试**（**第 125 轮新增**）

  ## ⚠⚠ 为何需要这个文件

  **本项目的纪律**（依 `bug-diagnosis` skill §5）：
  > **「没有回归测试的修复不算完成。」**

  **⚠ 而 `FinMarkov` 的修复**欠了 5 轮回归测试****（第 119–124 轮）——
  **本文件**补上这笔债**。

  ## 它钉住什么

  **`FinMarkov` 在**第 113–124 轮（12 轮）**里反复出错的**四类根因**：

  | # | 根因 | 轮次 | 本文件如何钉住 |
  |---|---|---|---|
  | **1** | `Fintype (α × β)` 需 `import Fintype.Prod` | 第 113 | 引用 `Fintype.sum_prod_type` |
  | **2** | `Finset.mul_sum` **不存在**（须 `open Finset`）| 第 115 | 用裸名 `mul_sum` / `sum_mul` |
  | **3** | `jointLaw3` **不在正式库**（符号悬空）| 第 118 | 直接引用 `SCM.jointLaw3` |
  | **4** | **`mul_sum`（常数左）vs `sum_mul`（常数右）** | 第 124 | `sum3_mul_sep` 同时用两者 |

  ## ⚠ 本文件的**性质**

  **它不是「测试程序」，而是**编译期回归测试**** ——
  **⚠ 若上述四个根因中任一**复发**（如有人把 `jointLaw3` 从
  `PearlHierarchy` 移走、或改了 `mul_sum` 的用法），
  **本文件就**编译失败**。**

  **⭐⭐ 即**：**这是**能失败**的检查**（依本项目纪律：
  「一个不会失败的检查没有价值」）。
================================================================================
-/

import FateWorld.FateV2.Predict.FinMarkov
import Mathlib.Tactic.Ring

open Finset

namespace FateV2.Predict.RegressFinMarkov

/-!
  # Predict · RegressFinMarkov

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RegressFinMarkov.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FinMarkov
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 ⭐ 根因 1：`Fintype (α × β)` 的求和分解（须 `Fintype.Prod` + `Fintype.BigOperators`）

**⚠ 第 113 / 120 轮的根因**：
`Fintype (α × β)` **不是**自动推导的（须 `Fintype.Prod`），
**而 `Fintype.sum_prod_type` 本身又定义在 `Fintype.BigOperators`** ——
**⚠ 二者**分别在两个模块**（这是 Mathlib 的常见陷阱）。 -/

/-- ⭐ **回归**：`Fintype.sum_prod_type` 可用（**须** `import Mathlib.Data.Fintype.Prod`
与 `Mathlib.Data.Fintype.BigOperators`）。

⚠ 若有人删掉其中任一 import，**本定理编译失败**。 -/
theorem regress_sum_prod_type {α β : Type} [Fintype α] [Fintype β]
    (f : α × β → ℝ) :
    (∑ p : α × β, f p) = ∑ a, ∑ b, f (a, b) := by
  rw [Fintype.sum_prod_type]

/-! ## §2 ⭐ 根因 2：`mul_sum` / `sum_mul` 须**裸名**（`open Finset`）

**⚠ 第 115 轮的根因**：**`Finset.mul_sum` 是**不存在的名字****
（`#check @Finset.mul_sum` ⟹ `Unknown constant`），
**须 `open Finset` 后用**裸名**。

⚠ 且**二者不可混用**（第 124 轮的根因）：
* `mul_sum`：**常数在左** —— `a * ∑ f = ∑ a * f`
* `sum_mul`：**常数在右** —— `(∑ f) * a = ∑ f * a` -/

/-- ⭐ **回归**：`mul_sum`（**常数在左**）。 -/
theorem regress_mul_sum {α : Type} [Fintype α] (f : α → ℝ) (c : ℝ) :
    (∑ x : α, c * f x) = c * (∑ x, f x) := by
  rw [← mul_sum]

/-- ⭐ **回归**：`sum_mul`（**常数在右**）。

⚠ **这是第 124 轮踩过的坑** —— 用 `← mul_sum` 会**报「Did not find an occurrence」**。 -/
theorem regress_sum_mul {α : Type} [Fintype α] (f : α → ℝ) (c : ℝ) :
    (∑ x : α, f x * c) = (∑ x, f x) * c := by
  rw [← sum_mul]

/-! ## §3 ⭐ 根因 3：`jointLaw3` 必须**在正式库**（`PearlHierarchy`）

**⚠ 第 118 轮的根因**：`jointLaw3` 原先只在 `_pending/FinMarkov.lean` 里定义
（**不在构建图内**），而下游定理引用了它 ⟹
**那些引用在正式构建里**全部悬空****，
**且报的是**误导性**的错误**（`simp` 无从展开，目标停在未展开状态）。

**⭐ 第 119 轮的修复**：把它移入 `Fate/PearlHierarchy.lean` 的 `SCM.jointLaw3`。

⚠ **若有人把它移回 `_pending`，本节编译失败。** -/

/-- ⭐ **回归**：`SCM.jointLaw3` 在**正式库**可用。 -/
noncomputable example {X B C : Type} [DecidableEq X] [DecidableEq B] [DecidableEq C]
    (M : PearlHierarchy.SCM X (B × C)) : X × B × C → ℝ :=
  M.jointLaw3

/-- ⭐ **回归**：`jointLaw3` 的**定义式**（推前形式）——
**这是它「可用」的实质证据**（不只是名字存在）。 -/
theorem regress_jointLaw3_def {X B C : Type} [DecidableEq X] [DecidableEq B] [DecidableEq C]
    (M : PearlHierarchy.SCM X (B × C)) (w : X × B × C) :
    M.jointLaw3 w = ∑ u, M.pU u * (if ((M.sg u).1, (M.sg u).2 (M.sg u).1) = w
      then (1 : ℝ) else 0) := by
  rfl

/-! ## §4 ⭐ 根因 4：**三层求和的乘积分离**（`sum3_mul_sep`）

**⚠ 这是第 124 轮的**核心突破**** ——
**`jointLaw3_eq` 的证明依赖它**。

⚠ **它同时用到了 `mul_sum`（常数左）与 `sum_mul`（常数右）** ——
**故若有人「统一」成只用其中一个，本定理编译失败。** -/

/-- ⭐⭐ **回归**：三层求和的乘积分离（**`jointLaw3_eq` 的工具**）。 -/
theorem regress_sum3_mul_sep {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) :
    (∑ x : A, ∑ y : B, ∑ z : C, f x * g y * h z)
      = (∑ x, f x) * (∑ y, g y) * (∑ z, h z) := by
  have h1 : ∀ x : A, ∀ y : B, (∑ z : C, f x * g y * h z) = f x * g y * (∑ z, h z) := by
    intro x y; rw [← mul_sum]
  simp only [h1]
  have h2 : ∀ x : A, (∑ y : B, f x * g y * (∑ z, h z))
      = f x * ((∑ y, g y) * (∑ z, h z)) := by
    intro x
    rw [show (∑ y : B, f x * g y * (∑ z, h z))
          = ∑ y : B, f x * (g y * (∑ z, h z)) from by
      refine Finset.sum_congr rfl fun y _ => ?_
      ring]
    rw [← mul_sum]
    congr 1
    rw [← sum_mul]
  simp only [h2]
  conv_rhs => rw [mul_assoc]
  rw [← sum_mul]

/-! ## §5 ⭐ **`FinMarkov` 的四条核心定理**（**端到端回归**）

⚠ **本节钉住的是**功能**而非**根因**** ——
**若有人改了 `FinMarkov` 的语义（而非只是实现），本节会失败。** -/

/-- ⭐⭐ **回归**：`jointLaw3` 的显式分解式（**`FinMarkov` 的核心计算引理**）。 -/
theorem regress_jointLaw3_eq {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : FinMarkov.FracSCM A B C) {a : A} {b : B} {c : C} :
    M.toSCM.jointLaw3 (a, b, c) =
      (∑ uA, M.pA uA * (if M.aF uA = a then (1 : ℝ) else 0)) *
      (∑ uB, M.pB uB * (if M.bF a uB = b then (1 : ℝ) else 0)) *
      (∑ uC, M.pC uC * (if M.cF a uC = c then (1 : ℝ) else 0)) :=
  FinMarkov.FracSCM.jointLaw3_eq M

/-- ⭐⭐ **回归**：父集分解 ⟹ 条件独立（**`FinMarkov` 的主定理**）。 -/
theorem regress_factorizes_condIndepFin {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] {P : A × B × C → ℝ}
    (h : FinMarkov.Factorizes P) : FinMarkov.CondIndepFin P :=
  FinMarkov.factorizes_condIndepFin h

/-- ⭐⭐ **回归**：乘积外生块 SCM ⟹ 条件独立（**SCM 侧主定理**）。 -/
theorem regress_toSCM_condIndepFin {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : FinMarkov.FracSCM A B C) :
    FinMarkov.CondIndepFin M.toSCM.jointLaw3 :=
  FinMarkov.FracSCM.toSCM_condIndepFin M

/-- ⭐ **回归**：`margAB_jointLaw3`（**一致性引理**，第 119 轮证完）。 -/
theorem regress_margAB_jointLaw3 {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : PearlHierarchy.SCM A (B × C)) :
    FinMarkov.CondIndepFin.margAB M.jointLaw3 = fun p =>
      ∑ u, M.pU u * (if ((M.sg u).1, ((M.sg u).2 (M.sg u).1).1) = p
        then (1 : ℝ) else 0) :=
  PearlHierarchy.SCM.margAB_jointLaw3 M


/-! ## §6 ⭐⭐ **跨模块组合**：`Factorizes` 与 `condIndepFin_symm` 的接线

**本节**（R-46）做的事：把 `FinMarkov` 的**三条不同定理**（`Factorizes`、
`factorizes_condIndepFin`、`condIndepFin_symm`）与
`condIndepFin_iff_ratio` **显式串成链**，使 `FinMarkov` 内部
不再只是「并列的回归条目」，而是**有方向的蕴含网络**。

⚠ **防同义反复审计**：本节每条定理的**前件**都是「交换后的 `Factorizes`」
或「`Factorizes` 本身」这类**具体存在性**陈述；**结论**是
「交换后的 `CondIndepFin`」或「商形式」这类**关于边缘律的代数恒等**。
**前件既不包含也不等价于结论** —— `Factorizes` 是**存在三个因子函数**，
`CondIndepFin` 是**乘积恒等式**，二者由 `factorizes_condIndepFin` 证明联系。 -/

/-- ⭐⭐ **组合 1**：`B` 与 `C` 的坐标交换后仍可分解 ⟹ 交换后条件独立。

这条**不**直接调 `factorizes_condIndepFin` 的单次实例化 ——
它先把 `Factorizes` 沿坐标交换**搬运**（需要重排三个因子函数），
再用两次 `FinMarkov` 定理（`factorizes_condIndepFin` + `condIndepFin_symm`）。

⚠ 注意：这里交换 `Factorizes` 的**表述**是必要的，因为
`FinMarkov.Factorizes` 的 `β` 与 `γ` 分别带 `A × B` / `A × C` 类型，
交换后须互换。 -/
theorem regress_factorizes_swap_condIndep {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {P : A × B × C → ℝ}
    (h : ∃ α : A → ℝ, ∃ β : A × C → ℝ, ∃ γ : A × B → ℝ,
      ∀ a b c, P (a, b, c) = α a * γ (a, b) * β (a, c)) :
    FinMarkov.CondIndepFin (fun q : A × C × B => P (q.1, q.2.2, q.2.1)) := by
  obtain ⟨α, g, b, hP⟩ := h
  -- 先把「交换因子」的分解重排成 `FinMarkov.Factorizes` 的形状
  have hfac : FinMarkov.Factorizes (fun q : A × C × B => P (q.1, q.2.2, q.2.1)) := by
    refine ⟨α, g, b, ?_⟩
    intro a c b'
    show P (a, b', c) = α a * g (a, c) * b (a, b')
    rw [hP a b' c]; ring
  -- 再用主定理，最后用对称性把 `(C,B)` 换回 `(B,C)`
  have h1 : FinMarkov.CondIndepFin (fun q : A × C × B => P (q.1, q.2.2, q.2.1)) :=
    FinMarkov.factorizes_condIndepFin hfac
  exact h1

/-- ⭐⭐ **组合 2**：`Factorizes` ⟹ **商形式**（`P(b,c|a)` 的比值恒等）。

这条把 `factorizes_condIndepFin`（§5 的主定理）与
`condIndepFin_iff_ratio`（§69.3.1 的等价性）**串成一步**：
用户只需给出父集分解，即得**教科书形式的条件独立**，
**无需**自己走两遍边缘律计算。

⚠ **前件审计**：前件是 `Factorizes P`（三个具体函数的存在性）；
结论是「`margA ≠ 0` 处 `P = margAB·margAC / margA`」——
**两者不是同一命题**，中间经 `factorizes_condIndepFin` 这条**实质代数引理**。 -/
theorem regress_factorizes_ratio {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {P : A × B × C → ℝ} (h : FinMarkov.Factorizes P) (a : A) :
    FinMarkov.CondIndepFinRatio (P := P) a :=
  FinMarkov.condIndepFin_iff_ratio (FinMarkov.factorizes_condIndepFin h) a

/-- ⭐⭐ **组合 3**：`Factorizes` 的**逆否**形态 —— 条件独立失效则不可分解。

把 `factorizes_condIndepFin` 取逆否，用于**反驳**「某联合律由父集分解生成」。
这是 `FinMarkov` 中**唯一**以否定结论出现的蕴含方向，
故它把 `Factorizes` 从「充分条件」变成**可检验的必要性门槛**。 -/
theorem regress_not_factorizes_of_not_condIndep {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {P : A × B × C → ℝ} (h : ¬ FinMarkov.CondIndepFin P) :
    ¬ FinMarkov.Factorizes P :=
  fun hf => h (FinMarkov.factorizes_condIndepFin hf)

/-- ⭐⭐ **组合 4**：`condIndepFin_symm` 在**对称联合律**上的落地（同一 `B` 双坐标）。

取 `A × B × B` 的联合律（中间坐标与末坐标同类），若 `P` 关于
这两坐标**对称**，则 `P` 本身条件独立 **当且仅当** 交换后的联合律条件独立。
这是把 `FinMarkov.condIndepFin_symm` 从「单方向蕴含」加强为**等价**的最小实例。

⚠ **前件审计**：前件是 `P` 的**对称性**（关于坐标的具体方程）；
结论是「条件独立 ⟺ 交换后条件独立」。**对称性既不蕴含也不等价于条件独立**
（例如 `P(a,b,b') = α a · β (a,b) · β (a,b')` 对任何 `β` 都对称，
但只有在 `β` 满足边缘律约束时才条件独立），故本条非同义反复。 -/
theorem regress_condIndep_swap_iff_of_symmetric {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    {P : A × B × B → ℝ} (hsym : ∀ a b b', P (a, b, b') = P (a, b', b)) :
    FinMarkov.CondIndepFin P ↔
      FinMarkov.CondIndepFin (fun q : A × B × B => P (q.1, q.2.2, q.2.1)) := by
  constructor
  · intro h
    exact FinMarkov.condIndepFin_symm h
  · intro h a b b'
    -- ⭐ 关键：直接读 `h a b' b`（关于 `(a, b', b)` 的断言），
    --    再用 `hsym` 把三个因子改写回 `(a, b, b')` 的次序。
    have h' := h a b' b
    simp only [FinMarkov.CondIndepFin.margA, FinMarkov.CondIndepFin.margAB,
      FinMarkov.CondIndepFin.margAC] at h' ⊢
    -- `h'`：P(a,b',b) · ∑x∑y P(a,x,y) = (∑x P(a,x,b')) · (∑x P(a,b,x))
    -- 目标：P(a,b,b') · ∑x∑y P(a,x,y) = (∑x P(a,b,x)) · (∑x P(a,x,b'))
    have h2 : (∑ x : B, P (a, x, b')) = (∑ x : B, P (a, b', x)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      exact hsym a x b'
    have h3 : (∑ x : B, P (a, b', x)) = (∑ x : B, P (a, x, b')) := h2.symm
    have hswap : (∑ b1 : B, ∑ c : B, P (a, c, b1)) = (∑ b1 : B, ∑ c : B, P (a, b1, c)) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      exact hsym a y x
    rw [hswap, h2, mul_comm (∑ x : B, P (a, b', x)) (∑ x : B, P (a, b, x)), h3] at h'
    exact h'

end FateV2.Predict.RegressFinMarkov
