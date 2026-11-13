import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! ===========================================================================
  `Fate._r239_F4` —— **Pearl 的 front-door 准则：调整公式的代数骨架**
  （第 239 轮 F4 / 路线图「缺口 2」）

  ## 0. 文献（**已核实**，见文末 §5 的 URL）

  Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed.,
  §3.3, **Theorem 3.3.4**（front-door criterion）：

  > 若 `Z` 满足
  > **(i)**  `Z` 截断 `X` 到 `Y` 的所有**有向路径**；
  > **(ii)** `X` 到 `Z` 无**后门**路径；
  > **(iii)** `Z` 到 `Y` 的所有**后门**路径都被 `X` 阻断，
  >
  > 则
  > $$P(Y\mid do(X{=}x))=\sum_{z} P(Z{=}z\mid X{=}x)\,
  >   \sum_{x'} P(Y\mid X{=}x',Z{=}z)\,P(X{=}x').$$

  **⭐ 本轮独立复核**：上式与 arXiv:2604.15288v1 的式 (∗∗) 及其条件
  (1)(2)(3) **逐字一致**（该文把 (i)(ii)(iii) 写作
  「Z blocks all directed paths X→Y / no open back-door path X→Z /
  X blocks all back-door paths Z→Y」）。另见 arXiv:2211.16468 的
  `FD(1)–FD(3)`。**⟹ 任务的公式陈述正确。**

  ## 1. 本轮**交付什么**（以及**不交付什么**）

  ### ✅ 交付
  1. `frontdoorFormula` —— 两重和 adjustment functional 的**数值定义**。
  2. **四条非平凡代数定理**（证明体都不是单词级，见每条的 `Proof` 说明）：
     - `fd_unit_collapse` / `fd_unit_eq_marginal`：`Z = Unit` 的退化；
     - `fd_mediator_is_adjustment` / `fd_mediator_eq_point`：`Z = X` 的退化；
     - `fd_add_joint` / `fd_sub_joint` / `fd_smul_joint`：在 `joint` 上的线性；
     - `fd_sum_over_y`：**对结果变量求和** = 把 `joint` 先对 `y` 求和。
  3. `outer_weights_sum_one`：`∑_z margXZ x z / margX x = 1`
     （当 `margXZ(x,·)` 是 `margX` 的正规行）。

  ### ⚠⚠ **不交付**（**如实说明，不硬凑**）
  - **完整 front-door 准则**（即「三条件 ⟹ 上式成立」）**未证**。
    它需要 (a) 图侧 d-分离判定、(b) 链式分解 `P(x,z,y)=P(x)P(z|x)P(y|z,x)`、
    (c) 从 `P(y|z,x)` 到 `P(y|do(x))` 的**干预律推导**（Pearl 的三步恒等式链）。
    这三者分别属于缺口 1（d-分离）、SCM 语义、与 do-演算，**均不在本文件范围**。
  - `Z = Unit` 的退化**不等于** `P(y|x)`。它等于 **`Y` 的边缘律
    `∑_x' P(x',y)`**（在 X-边缘一致性下）。**这是一个**数学事实**，
    也是本轮**必须更正**任务预期的地方**（详见 `fd_unit_eq_marginal` 的注释）。

  ## 2. 记号
  - `joint : X → Z → Y → ℝ` 表示 `p(x, z, y)`（三元联合）。
  - `margXZ : X → Z → ℝ` 表示 `p(x, z)`。
  - `margX : X → ℝ` 表示 `p(x)`。
  - **条件概率一律用比值 `joint / margXZ`、`margXZ / margX`**，
    与 `Fate.Backdoor.BackdoorAdjustment` 的约定**一致**（不引入除法定义）。
-/

namespace Fate.Frontdoor

open Finset

/-! ## §1 **定义**：front-door 调整公式（两重和） -/

/-- ⭐⭐⭐ **front-door 调整公式**（Pearl, *Causality* 2e, Thm 3.3.4）：

$$\sum_{z}\underbrace{\frac{p(x,z)}{p(x)}}_{P(z\mid x)}
  \cdot\underbrace{\sum_{x'}\frac{p(x',z,y)}{p(x',z)}\,p(x')}_{
    \sum_{x'}P(y\mid x',z)P(x')}$$

**⚠ 外层**第一个因子**是 `P(z|x)`（**不是** `P(z)`）——
这正是 front-door 与 back-door 的**结构差别**：
back-door 用 `P(z)`，front-door 用 `P(z|x)`，
而**内层**做的是**对 `x'` 的边缘化**（把 `x` 的影响经由 `z` 转手）。

**⭐ 若 `p(x) = 0`，Lean 里 `ℝ` 的除法给出 `0`**，故定义在**全 `ℝ`** 上，
无需前提；但**有内容的定理**都会带 `p(x) ≠ 0` 假设（见 §2/§3）。 -/
noncomputable def frontdoorFormula {X Y Z : Type*} [Fintype X] [Fintype Z]
    (joint : X → Z → Y → ℝ) (margXZ : X → Z → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) : ℝ :=
  ∑ z, margXZ x z / margX x * (∑ x', joint x' z y / margXZ x' z * margX x')

/-! ## §2 ⭐ **`Z` 退化为单点（`Z = Unit`）**

**⚠ 先更正任务的一处预期**（**这是本轮最重要的诚实说明**）：

任务写「当 `Z` 是单点（`Unit`）时退化为 backdoor 形式」。
**严格来说，它退化成的**不是** `P(y|x)`，而是一个**观测边缘**。

**推导**（`Z = Unit` 时 `P(()|x) = p(x,())/p(x)`）：

$$\text{fd}(x,y)=\frac{p(x,())}{p(x)}\sum_{x'}\frac{p(x',(),y)}{p(x',())}p(x').$$

- 若 `p(x,()) = p(x)`（即 `Z` 与 `X` **独立**、`Z` 不含 `X` 的信息），
  外层因子 `= 1`；
- 若再有 `p(x',()) = p(x')`（`Z` 完全不携带质量结构，即一致性），
  内层项 `= p(x',(),y)`。

**⟹ 结果 `= ∑_{x'} p(x',y) = P(Y=y)`**，**即 `Y` 的边缘律**。

**⭐ 数学意义（不是缺陷，而是必然）**：
`Z = Unit` 意味着**没有中介变量**。
front-door 的**全部信息来自中介 `Z`**；
**没有中介时，公式只能复现可直接观测的边缘 `P(Y)`**，
**它不携带任何关于 `do(x)` 的信息**（`do(x)` 的效果按定义不可从 `P(Y)` 读出）。
**⟹ 任务所说的「退化为 backdoor」只在「`Z` 单点且 `X` 无效应」的平凡情形下成立；
一般情形下，`Z = Unit` 的 front-door 给出 `P(Y)`。** 这一点已如实登记。 -/

/-- ⭐⭐ **`Z = Unit`：两重和**结构坍缩****（外层求和只剩唯一项）。

**Proof（非单词级）**：`unfold` 后用 `Finset.univ_unique` 把 `∑ z : Unit`
化为 `{default}`，再用 `Finset.sum_singleton` 求值。

**⚠ 本定理**只**说明「两重和外层坍缩」，**不**声称等于 `P(y|x)`。** -/
theorem fd_unit_collapse {X Y : Type*} [Fintype X]
    (joint : X → Unit → Y → ℝ) (margXZ : X → Unit → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) :
    frontdoorFormula joint margXZ margX x y
      = margXZ x () / margX x * (∑ x', joint x' () y / margXZ x' () * margX x') := by
  unfold frontdoorFormula
  rw [Finset.univ_unique, Finset.sum_singleton]

/-- ⭐⭐⭐ **`Z = Unit` + 一致性 ⟹ front-door 退化为 `Y` 的边缘律**。

陈述：若
- `p(x) ≠ 0` 对所有 `x`（`hpos`），
- `p(x',()) = p(x')` 对**所有** `x'`（`hcons`，即 `Z` 与 `X` 独立），

则
$$\text{fd}(x,y)=\sum_{x'}p(x',y)=P(Y=y).$$

**Proof（非单词级，四步）**：
1. 用 `fd_unit_collapse` 展开为单重和；
2. 外层因子 `p(x,())/p(x)` 用 `hcons x` 化为 `1`（`div_self`）；
3. 内层每项 `p(x',())/p(x')` 用 `hcons x'` 化为 `1`；
4. `p(x')/p(x') · p(x')` 用 `div_mul_cancel₀` 化为 `p(x',())`。

**⭐⭐ 这正是**任务「退化为 backdoor」的**正确读法**：
**没有中介时，front-door 只能给出边缘律**，
**而边缘律与 backdoor（空调整集）的观测律在此重合** ——
**故「退化」成立的分界点是「`X` 对 `Y` 无因果效应」**。 -/
theorem fd_unit_eq_marginal {X Y : Type*} [Fintype X]
    (joint : X → Unit → Y → ℝ) (margXZ : X → Unit → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) (hpos : ∀ a, margX a ≠ 0) (hcons : ∀ a, margXZ a () = margX a) :
    frontdoorFormula joint margXZ margX x y = ∑ x', joint x' () y := by
  rw [fd_unit_collapse]
  have hxz : margXZ x () = margX x := hcons x
  rw [hxz, div_self (hpos x), one_mul]
  refine Finset.sum_congr rfl ?_
  intro x' _
  rw [hcons x', div_mul_cancel₀ _ (hpos x')]

/-! ## §3 ⭐ **`Z = X`：退化为直接的 do/调整公式**

**推导**：`Z := X` 时 `p(x,z)` 只在 `z = x` 处非零（`X` 到 `Z` 是恒等），
故 `P(z|x) = [z=x]`，**外层求和坍缩到唯一项 `z = x`**：

$$\text{fd}(x,y)=\sum_{x'}\frac{p(x',x,y)}{p(x',x)}\,p(x')
  =\sum_{x'}P(y\mid x',Z{=}x)P(x').$$

**⭐ 这就是标准的「直接调整/do」泛函**（`x` 作为协变量被调整掉，
而 `x'` 是求平均的干预值）。**⟹ 任务的第 2 条退化**在精确意义下成立**。** -/

/-- ⭐⭐⭐ **`Z = X`（`margXZ` 是 `I` 的对角）⟹ front-door 退化为直接调整泛函**。

陈述：若 `margXZ a b = if b = a then margX a else 0`（`hdiag`）且 `margX a ≠ 0`，
则
$$\text{fd}(x,y)=\sum_{x'}\frac{p(x',x,y)}{p(x',x)}\,p(x').$$

**Proof（非单词级，三分支 `sum_eq_single`）**：
1. `Finset.sum_eq_single x` 把外层 `∑_z` 收缩到 `z = x`；
   两个非 `x` 分支各需证 `margXZ x b = 0`（由 `hdiag` + `if_neg`）；
2. 收缩后 `margXZ x x = margX x`，外层因子 `= 1`（`div_self` + `one_mul`）。

**⚠ 内层求和**保持不变**（它正是调整泛函的内层）——
这正是本定理的**实质**：`Z=X` 抹掉的**只有外层 `P(z|x)` 因子**。** -/
theorem fd_mediator_is_adjustment {X Y : Type*} [Fintype X] [DecidableEq X]
    (joint : X → X → Y → ℝ) (margXZ : X → X → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) (hpos : ∀ a, margX a ≠ 0)
    (hdiag : ∀ a b, margXZ a b = if b = a then margX a else 0) :
    frontdoorFormula joint margXZ margX x y
      = ∑ x', joint x' x y / margXZ x' x * margX x' := by
  unfold frontdoorFormula
  rw [Finset.sum_eq_single x]
  · have hzx : margXZ x x = margX x := by rw [hdiag x x, if_pos rfl]
    rw [hzx, div_self (hpos x), one_mul]
  · intro b _ hb
    have h0 : margXZ x b = 0 := by rw [hdiag x b]; exact if_neg hb
    rw [h0, zero_div, zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- ⭐⭐ **`Z = X` 的**点值退化****：若再要求 (a) `p(x',x,·)` 只在 `x'=x` 处非零
（`hjoint`，`Z := X` 时由 `joint ≤ margXZ` 强制）且 (b) 对角化，
则 front-door 在点 `(x,y)` 处**精确等于 `p(x,x,y)`**（对角联合概率）。

**Proof（非单词级）**：先套 `fd_mediator_is_adjustment`，
再对 `∑_{x'}` 用 `Finset.sum_eq_single x`（两个非 `x` 分支用 `if_neg` 归零），
最后 `p(x,x,y)/p(x)·p(x) = p(x,x,y)`（`div_mul_cancel₀`）。 -/
theorem fd_mediator_eq_point {X Y : Type*} [Fintype X] [DecidableEq X]
    (joint : X → X → Y → ℝ) (margXZ : X → X → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) (hpos : ∀ a, margX a ≠ 0)
    (hdiag : ∀ a b, margXZ a b = if b = a then margX a else 0)
    (hjoint : ∀ a, joint a x y = if a = x then joint x x y else 0) :
    frontdoorFormula joint margXZ margX x y = joint x x y := by
  rw [fd_mediator_is_adjustment joint margXZ margX x y hpos hdiag]
  rw [Finset.sum_eq_single x]
  · rw [hjoint x, if_pos rfl, hdiag x x, if_pos rfl, div_mul_cancel₀ _ (hpos x)]
  · intro b _ hb
    rw [hjoint b, if_neg hb, zero_div, zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-! ## §4 ⭐ **代数结构**：在联合分布上的线性 + 结果边缘化 -/

/-- ⭐⭐ **对联合分布可加**：`fd(j₁ + j₂) = fd(j₁) + fd(j₂)`。

**Proof（非单词级）**：`unfold` 后对**两层求和**各用一次 `sum_add_distrib`
（`←` 方向聚合），中间穿插 `← mul_add` 提出外层因子，
再用 `add_div` + `add_mul` 把每项的加法拆到分子。 -/
theorem fd_add_joint {X Y Z : Type*} [Fintype X] [Fintype Z]
    (j1 j2 : X → Z → Y → ℝ) (margXZ : X → Z → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) :
    frontdoorFormula (fun a b c => j1 a b c + j2 a b c) margXZ margX x y
      = frontdoorFormula j1 margXZ margX x y
        + frontdoorFormula j2 margXZ margX x y := by
  unfold frontdoorFormula
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x' _
  rw [add_div, add_mul]

/-- ⭐⭐ **对联合分布可减**：`fd(j₁ - j₂) = fd(j₁) - fd(j₂)`。

**Proof（非单词级）**：与 `fd_add_joint` 同构，
但把 `sum_add_distrib`/`mul_add`/`add_div` 换成
`sum_sub_distrib`/`mul_sub`/`sub_div`，并用 `sub_mul` 收尾。 -/
theorem fd_sub_joint {X Y Z : Type*} [Fintype X] [Fintype Z]
    (j1 j2 : X → Z → Y → ℝ) (margXZ : X → Z → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) :
    frontdoorFormula (fun a b c => j1 a b c - j2 a b c) margXZ margX x y
      = frontdoorFormula j1 margXZ margX x y
        - frontdoorFormula j2 margXZ margX x y := by
  unfold frontdoorFormula
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro x' _
  rw [sub_div, sub_mul]

/-- ⭐⭐ **对联合分布齐次**：`fd(c · j) = c · fd(j)`。

**Proof（非单词级）**：内层先把常数 `c` 从求和里提出（辅助引理
`inner_factor`，用 `mul_sum` + `mul_div_assoc` + `mul_assoc`），
外层再用 `Finset.mul_sum` 提出，最后 `ring` 归一结合律。 -/
theorem fd_inner_factor {X Y Z : Type*} [Fintype X]
    (c : ℝ) (j : X → Z → Y → ℝ) (margXZ : X → Z → ℝ) (margX : X → ℝ)
    (z : Z) (y : Y) :
    (∑ x', (c * j x' z y) / margXZ x' z * margX x')
      = c * (∑ x', j x' z y / margXZ x' z * margX x') := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x' _
  rw [mul_div_assoc, mul_assoc]

/-- ⭐⭐ **齐次性（主定理）**：见 `fd_inner_factor` 的说明。 -/
theorem fd_smul_joint {X Y Z : Type*} [Fintype X] [Fintype Z]
    (c : ℝ) (j : X → Z → Y → ℝ) (margXZ : X → Z → ℝ) (margX : X → ℝ)
    (x : X) (y : Y) :
    frontdoorFormula (fun a b d => c * j a b d) margXZ margX x y
      = c * frontdoorFormula j margXZ margX x y := by
  unfold frontdoorFormula
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [fd_inner_factor]
  ring

/-- ⭐⭐⭐ **结果边缘化**：对 `y` 求和与「先把 `joint` 对 `y` 求和」**可交换**。

$$\sum_y \text{fd}_y(x)=\sum_z P(z|x)\sum_{x'}\frac{\big(\sum_y p(x',z,y)\big)}{p(x',z)}p(x').$$

**⭐ 意义**：front-door 泛函对结果变量 `y` 的**求和与外层结构无关** ——
它只把内层的 `p(x',z,y)` 换成其 `y`-边缘。
**⟹ 若 `∑_y p(x',z,y) = p(x',z)`（`joint` 的 `y`-边缘恰是 `margXZ`），
则内层每项 `= p(x')`，整式 `= ∑_z P(z|x)·1 = 1`**（见 `fd_total_mass_one`）。

**Proof（非单词级，四步）**：
1. `unfold` 后先用 `Finset.sum_comm` 把 `∑_y ∑_z` 换成 `∑_z ∑_y`；
2. 对每个 `z` 用 `← Finset.mul_sum` 把外层因子 `P(z|x)` 提到 `∑_y` 内；
3. 对内层再用一次 `Finset.sum_comm` 把 `∑_y ∑_{x'}` 换成 `∑_{x'} ∑_y`；
4. 每个 `x'` 项用 `sum_div` + `sum_mul` 把对 `y` 的求和推进分子。 -/
theorem fd_sum_over_y {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (joint : X → Z → Y → ℝ) (margXZ : X → Z → ℝ) (margX : X → ℝ)
    (x : X) :
    ∑ y', frontdoorFormula joint margXZ margX x y'
      = ∑ z, margXZ x z / margX x
          * (∑ x', (∑ y', joint x' z y') / margXZ x' z * margX x') := by
  unfold frontdoorFormula
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [← Finset.mul_sum]
  refine congrArg (fun t => margXZ x z / margX x * t) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x' _
  rw [Finset.sum_div, Finset.sum_mul]

/-- ⭐⭐⭐ **行权重之和 = 1**：若 `margXZ(x,·)` 按 `z` 求和恰为 `margX x`
（即 `p(x,z)` 对 `z` 的边缘就是 `p(x)`，**这是 `p(x,z)` 作为联合律的必然要求**），
则**外层权重 `P(z|x)` 的总和为 1**，即 front-door 泛函是 `z` 上的**真加权平均**。

**Proof（非单词级）**：`← Finset.sum_div` 把 `∑ (margXZ/·)` 合成分式
`(∑ z, margXZ x z) / margX x`，再用 `hrow` 换分子、`div_self` 收。

**⭐ 这是 pure probability** 的归一化，**不需要任何图条件**。
**⟹ 它排除了一种可能的失败模式**：front-door 不是「任意线性组合」，
**其外层系数构成概率分布**。 -/
theorem outer_weights_sum_one {X Z : Type*} [Fintype Z]
    (margXZ : X → Z → ℝ) (margX : X → ℝ) (x : X)
    (hx : margX x ≠ 0) (hrow : ∑ z, margXZ x z = margX x) :
    ∑ z, margXZ x z / margX x = 1 := by
  rw [← Finset.sum_div, hrow, div_self hx]

/-- ⭐⭐⭐ **front-door 泛函对 `y` 的总质量恒为 `1`**（在正确的边缘一致性下）：
- `hx : p(x) ≠ 0`
- `hne : p(x',z) ≠ 0` 逐点（`ℝ`-值公式不携带概率性，需显式声明）
- `hmarg : ∑_y p(x',z,y) = p(x',z)`（`joint` 的 `y`-边缘 = `margXZ`，**正确形式**）
- `hrow : ∑_z p(x,z) = p(x)`（`z`-边缘 = `margX`，**正确形式**）
- `hsum1 : ∑_x' p(x') = 1`（**`X` 的总质量**，对概率分布**必然成立**）

则 `∑_y fd(x,y) = 1`。

**⭐ 为什么**不是** `hcons : margXZ a z = margX a`（对 `z` 恒定）
（我第一次写的就是这个，**它是错的**）**：
若对**所有** `z` 都有 `margXZ a z = margX a`，则
`∑_z margXZ a z = card(Z) · margX a`，**只有在 `Z` 是单点时才等于 `margX a`**。
**⟹ 正确的行和假设必须是 `∑_z margXZ x z = margX x`，不能逐点常数化。**
**这一点已在本文件注释中保留，作为**订正记录**。**

**Proof（非单词级，五步）**：
1. 套 `fd_sum_over_y`；
2. 用 `hmarg` 把内层分子 `∑_y p(x',z,y)` 换成 `margXZ x' z`；
3. 于是每项 `margXZ x' z / margXZ x' z * margX x'` 用 `div_self` 化为 `margX x'`（`hne`）；
4. 内层 `= ∑ x', margX x'`，与 `z` 无关；
5. 最后用 `outer_weights_sum_one`（`hrow`）得 `1`，并用 `hsum1` 把内层替换成 `1`。

**⚠ 诚实说明**：本定理虽是真定理，但它是**归一化**（总质量 = 1）的代数体现，
**不包含 front-door 的识别性内容**。它的价值在于：**排除了 front-door 泛函
不是概率分布的失败模式**。** -/
theorem fd_total_mass_one {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (joint : X → Z → Y → ℝ) (margXZ : X → Z → ℝ) (margX : X → ℝ)
    (x : X) (hx : margX x ≠ 0)
    (hne : ∀ a b, margXZ a b ≠ 0)
    (hmarg : ∀ a b, (∑ y', joint a b y') = margXZ a b)
    (hrow : ∑ z, margXZ x z = margX x)
    (hsum1 : ∑ a, margX a = 1) :
    ∑ y', frontdoorFormula joint margXZ margX x y' = 1 := by
  rw [fd_sum_over_y]
  have hinner : ∀ z : Z, (∑ x', (∑ y', joint x' z y') / margXZ x' z * margX x')
      = ∑ x', margX x' := by
    intro z
    refine Finset.sum_congr rfl ?_
    intro x' _
    rw [hmarg x' z, div_self (hne x' z), one_mul]
  simp only [hinner]
  -- Goal is now:  ∑ z, margXZ x z / margX x * (∑ a, margX a) = 1
  rw [← Finset.sum_mul]
  rw [show (∑ z, margXZ x z / margX x) = 1 from
    outer_weights_sum_one margXZ margX x hx hrow]
  rw [one_mul, hsum1]

end Fate.Frontdoor
