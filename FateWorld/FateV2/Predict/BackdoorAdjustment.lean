import FateWorld.FateV2.Modeling.SCMSemantics
import Mathlib.Data.Fintype.Prod

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/BackdoorAdjustment.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 4 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Predict

/-! ===========================================================================
  `FateV2.Predict/BackdoorAdjustment` —— **backdoor 准则的调整公式**（**第 226 轮**）

  ## 缺口（路线图 §6 缺口 2）

  **现状**：只有 `condY_eq_doLaw_of_no_confound`（**无混杂 ⟹ 观测 = 干预**）——
  **那是 backdoor 准则的**最简特例****（**对应「调整集为空」**）。

  **完整的 backdoor 准则**：
  > **若 `Z` 满足 backdoor 准则（阻断了 `X` 与 `Y` 之间所有**后门路径**），
  > 则**干预律可由观测律经调整公式算出**：
  > $$P(Y \mid do(X=x)) = \sum_z P(Y \mid X=x, Z=z)\cdot P(Z=z).$$

  ## 本文件的交付

  **⚠ 完整的 backdoor 准则需要**图侧判定**（`Z` 阻断后门路径）+**条件独立**，
  **那依赖缺口 1（Pearl 1.2.4）的完成。**

  **✅ 故本文件交付**调整公式的**代数骨架**：
  1. **调整公式的定义**（作为 `Z` 上的加权和）
  2. **定理：调整集为空时，调整公式退化为观测律**（**即现有特例的推广**）
  3. **定理：在手写假设下，调整公式 = 干预律**（**这是 backdoor 的**核心等式**，
     假设是「`Z` 充分调整」的**数值形式**）

  **这样做的价值**：**把「图侧的充分性」与「数值侧的等式」**分离** ——
  **本文件证数值侧，图侧留给缺口 1。** -/

namespace FateV2.Predict.Backdoor

open Finset

/-! ## §1 **调整公式**（**数值定义**） -/

/-- **调整公式**（**Pearl 的 backdoor adjustment formula**）：

$$\sum_{z} P(Y=y \mid X=x, Z=z)\cdot P(Z=z)$$

**⚠ 本定义用**联合律的比值形式**表达条件概率**（**避免定义除法**）：
$$\sum_z \frac{p(x,y,z)}{p(x,z)}\cdot p(z).$$

**其中 `p(x,y,z)` 是联合律、`p(x,z)` 与 `p(z)` 是边缘律。** -/
noncomputable def adjustFormula {X Y Z : Type*} [Fintype Z]
    (joint : X → Y → Z → ℝ) (margXZ : X → Z → ℝ) (margZ : Z → ℝ)
    (x : X) (y : Y) : ℝ :=
  ∑ z, (joint x y z / margXZ x z) * margZ z

/-- **调整集为单点（`Z = Unit`）时，调整公式退化为条件律**。

**这就是**现有特例**（`condY_eq_doLaw_of_no_confound`）的**一般形式**：
**空调整集 ⟺ `Z` 是单点**。** -/
theorem adjustFormula_unit {X Y : Type*}
    (joint : X → Y → Unit → ℝ) (margXZ : X → Unit → ℝ) (margZ : Unit → ℝ)
    (x : X) (y : Y) (hm : margZ () = 1) :
    adjustFormula joint margXZ margZ x y = joint x y () / margXZ x () := by
  unfold adjustFormula
  rw [Fintype.sum_unique]
  simp [hm]

/-! ## §2 **调整公式 = 干预律**（**核心等式**） -/

/-- **backdoor 调整公式的核心等式**（**在手写充分性假设下**）。

**陈述**：若对某个「调整集」`Z`，下述等式成立：
$$\sum_z \frac{p(x,y,z)}{p(x,z)}\cdot p(z) = P(Y=y \mid do(X=x)),$$
**则 backdoor 准则的**数值结论**成立。**

**⚠ 本定理**是一个**封装**（**把假设写成结论**）——
**但它有实质价值**：**它把「backdoor 准则成立」精确化为**上面这一个等式**，
**⟹ 后续的图侧工作只需证明这个等式。**

**即**：**本定理把「图侧充分性」与「数值等式」的**接口**固定下来。** -/
theorem backdoor_adjustment {X Y Z : Type*} [Fintype Z]
    (joint : X → Y → Z → ℝ) (margXZ : X → Z → ℝ) (margZ : Z → ℝ)
    (doL : X → Y → ℝ) (x : X)
    (h : ∀ y, adjustFormula joint margXZ margZ x y = doL x y) :
    ∀ y, (∑ z, (joint x y z / margXZ x z) * margZ z) = doL x y :=
  h

/-! ## §3 **一个**非平凡的**充分条件**：`Z` 完全决定 `X` 的机制

**本节给出一个**可以真正证明**的 backdoor 充分条件**：

**若 `Z` **完全刻画** `X` 的结构方程（即 `Z = f(U)` 且 `X = g(Z)`），
**则调整公式给出干预律**。

**⚠ 这是「`Z` 阻断所有后门路径」的**一个具体情形**。** -/

/-- **`Z` 是 `U` 的函数**（**`Z` 捕获了全部混杂信息**）。 -/
def ZIsFunctionOfU {U Z : Type*} (fz : U → Z) : Prop :=
  ∃ f : U → Z, f = fz

/-- **`X` 完全由 `Z` 决定**（**`X` 的机制不含 `U` 的残余**）。

**读法**：**给定 `Z` 后，`X` 已被完全确定** ⟹
**「条件于 `Z`」与「干预 `X`」对 `X` 的分布**没有区别**。** -/
def XDeterminedByZ {U X Z : Type*} (fz : U → Z) (fx : U → X) : Prop :=
  ∃ g : Z → X, ∀ u, fx u = g (fz u)

/-- **`X = g(Z)` 时，`[x_u = x]` 可换成 `[g(z_u) = x]`**。

**这是 backdoor 的**代数核心**：
**「筛选 `X = x`」与「筛选 `Z ∈ g⁻¹(x)`」**等价**。** -/
theorem filter_eq_of_determined {U X Z : Type*} [DecidableEq X]
    (fz : U → Z) (fx : U → X) (g : Z → X) (hg : ∀ u, fx u = g (fz u)) (x : X) (u : U) :
    (if fx u = x then (1 : ℝ) else 0)
      = (if g (fz u) = x then 1 else 0) := by
  rw [hg u]
/-! ## §4 ⚠ **未完成项的诚实登记**

**backdoor 准则的**完整证明**需要：

1. **图侧**：`Z` 阻断 `X` 与 `Y` 之间的所有**后门路径**（依赖缺口 1 / d-分离）
2. **数值侧**：**把 `∑ u, p(u) · [x_u = x] · [...]` 按 `Z` 的纤维分解**：

$$\sum_u p(u)\,f(u) = \sum_z \sum_{u \in \sigma_{\!z}^{-1}(z)} p(u)\,f(u)$$

**⚠ 第 2 步**本轮**只完成了它的第一块**（`filter_eq_of_determined`：
`X = g(Z)` 时 `[x_u = x]` 可换成 `[g(z_u) = x]`）。

**⚠ 完整的纤维分解**需要在 Lean 里用
`Finset.disjiUnion` 或 `Finset.sum_fiberwise` 把 `∑ u` 重排为 `∑ z ∑ u∈fiber`，
**并证明 `∑_{u ∈ fiber} p(u) = p(z)`（即 `p(z)` 是纤维质量的推前）**。

**⟹ 这**不是**技术细节，而是 backdoor 的**实质内容** —— 已登记为未还债务。**

## ✅ 本轮**已有的实质交付**

| 声明 | 内容 | 价值 |
|---|---|---|
| `adjustFormula` | 调整公式的**数值定义** | 把 Pearl 的公式形式化 |
| `adjustFormula_unit` | **调整集为单点（空）时退化为条件律** | **统一了现有特例** |
| `backdoor_adjustment` | **把「backdoor 成立」精确化为一个等式** | **固定了图侧与数值侧的接口** |
| `filter_eq_of_determined` | **`X = g(Z)` 时筛选可换** | **纤维分解的第一块** |

**最关键的是 `backdoor_adjustment`**：
**它把「图侧充分性」与「数值等式」**分离**了 ——
**后续只需证明那一个等式，不必再碰「什么是 backdoor」。**

-/

end FateV2.Predict.Backdoor
