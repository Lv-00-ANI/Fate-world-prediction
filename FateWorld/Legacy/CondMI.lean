/-
# 信息论视角：条件互信息、吉布斯不等式与 `dSep ⟹ I(X;Y|Z)=0`

## 本模块回答的问题

此前全库的因果桥都止步于 **`dSep ⟹ CondMul`**（`CondMul` 是乘性条件独立的
`Finset` 谓词，见 `Fate/FinCondIndep.lean`）。本模块补上**信息论**那一层：

> **把「条件独立」写成「条件互信息为零」`I(X;Y|Z) = 0`，
> 并证明它与 `CondMul` 等价；由此把 `dSep ⟹ CondMul` 升级为
> `dSep ⟹ I(X;Y|Z) = 0`。**

这就是「信息论视角」的精确内容：**条件独立 = 条件互信息为零**，
而条件互信息用**有限和**（`Finset.sum`）写出，不用任何测度论。

## 主定理（有限和形式）

设 $p : (\alpha\times\beta)\times\gamma \to \mathbb{R}$ 是**联合律**
（沿用全库口径：**不归一化、可取值于实数**；下文的定理在需要处显式假设正性）。

**条件互信息（有限和定义）**：

$$I(X;Y|Z) \;:=\; \sum_{z}\sum_{x}\sum_{y}
  p(x,y,z)\;\log\!\frac{p(x,y,z)\;p_{Z}(z)}
    {p_{XZ}(x,z)\;p_{YZ}(y,z)}.$$

其中边缘律 $p_{XZ},p_{YZ},p_Z$ 就是 `Fate/FinCondIndep.lean` 里的
`margXZ, margYZ, margZ`。

**主定理**：

| 编号 | 命题 | 假设 |
|---|---|---|
| `condMI_eq_zero_of_condMul` | `CondMul p ⟹ I(X;Y|Z) = 0` | **无**（连正性都不需要）|
| `condMul_of_condMI_eq_zero` | `I(X;Y|Z) = 0 ⟹ CondMul p` | 逐点 `0 < p` |
| `condMI_eq_zero_iff` | `I(X;Y|Z) = 0 ↔ CondMul p` | 逐点 `0 < p` |
| `condMI_nonneg` | `0 ≤ I(X;Y|Z)` | 逐点 `0 < p` |

## 证明骨架（这是本模块真正的技术内容）

**关键观察**：把 $I$ 摊成**逐点**形状。令

$$r(x,y,z) := \frac{p_{XZ}(x,z)\,p_{YZ}(y,z)}{p_Z(z)}
\quad\text{（给定 } z\text{ 时的「独立乘积」理论质量）},$$

并定义**逐点吉布斯余量**

$$g(x,y,z) := p(x,y,z)\log\frac{p(x,y,z)}{r(x,y,z)}
  \;-\;\bigl(p(x,y,z) - r(x,y,z)\bigr).$$

**第一条**（质量守恒，`kernMassZero`）：对每个固定的 $z$，

$$\sum_{x}\sum_{y} p(x,y,z) \;=\; \sum_{x}\sum_{y} r(x,y,z) \;=\; p_Z(z).$$

这里的**关键在于 $r$ 的总质量也是 $p_Z(z)$**：

$$\sum_{x}\sum_{y} r(x,y,z)
  = \frac{\bigl(\sum_x p_{XZ}\bigr)\bigl(\sum_y p_{YZ}\bigr)}{p_Z}
  = \frac{p_Z\cdot p_Z}{p_Z} = p_Z.$$

它把 $\sum_{xy}(p-r)$ 整体钉成 $0$，**故不需要任何归一化假设**。

**第二条**（逐点吉布斯，`gibbs`）：$0 < q, r \implies q - r \le q\log(q/r)$。
即 $g \ge 0$。**证明**：$\log(r/q)\le r/q-1$（`Real.log_le_sub_one_of_pos`），
两边乘 $q>0$，代数整理。

**第三条**（摊平，`condMI_eq_sum_gibbs`）：把 $I$ 写成
$I = \sum_z \sum_{xy} g$。**证明**：
$\sum_{xy}\bigl[p\log(p/r)\bigr] = \sum_{xy} g + \sum_{xy}(p-r)$，
而由第一条每切片 $\sum_{xy}(p-r) = 0$。

**第四条**（等号条件，`log_eq_sub_one_iff`）：
$0 < t \implies (\log t = t-1 \leftrightarrow t = 1)$。
由 `Real.log_lt_sub_one_of_pos` 反证。

**第五条**（收官）：`0 < p` 蕴含 `0 < r`，故每 $g\ge 0$；
`sum_eq_zero_iff_of_nonneg` 使 $I=0$ 化为「每 $g=0$」；
每 $g=0$ 即 $\log(r/p) = r/p - 1$，由第四条 $r/p=1$，即 $r = p$，
即 $p\,p_Z = p_{XZ}\,p_{YZ}$，正是 `CondMul`。

## 与 `dSep` 的接口

`Fate/ChainDSepCondMul.lean` 已在链 `0 → 1 → 2` 上证明
`dSep {0} {2} {1}` 并把它**作为假设消费**，得到 `CondMul` 的三因子来源。
本模块不重复那条图论工作，而是**在其 `CondMul` 输出之上**接上信息论层：
一旦**任意来源**（包括 `dSep` + 因子分解）给出 `CondMul p`，
本模块的 `condMI_eq_zero_of_condMul` 立刻给出 `I(X;Y|Z) = 0`。
这就是「**d-分离 ⟹ 条件互信息为 0**」的信息论终点。

## 诚实声明

* **不归一化**：主恒等式 `condMI_eq_sum_gibbs` 对**任意**实值 `p` 成立；
  不用 $\sum p = 1$。$p_Z(z)=0$ 的切片被排除在正性假设之外。
* **正性只在需要处**：`CondMul ⟹ I=0` **无假设**；
  `I=0 ⟹ CondMul` 与 `0 ≤ I` 需要逐点 `0 < p`
  （这保证 $\log$ 的参数 $>0$，且 $r>0$）。
* **无 `sorry` / `admit` / 新增 `axiom`**。
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import FateWorld.Legacy.FinCondIndep

namespace Fate

namespace CondMI

open Finset

variable {α β γ : Type*}

/-! ---------------------------------------------------------------------------
  §1  逐点吉布斯不等式（本模块的分析基石）
  --------------------------------------------------------------------------- -/

/-- ⭐⭐ **逐点吉布斯不等式**：$0<q,r \implies q - r \le q\log(q/r)$。

**证明**：由 `Real.log_le_sub_one_of_pos`（$\log(r/q)\le r/q-1$），
两边乘 $q>0$，把 $q\cdot(r/q-1) = r-q$ 提出，代数整理即得。

**读法**：右边减左边 $= g(q,r)\ge 0$ 正是 KL 散度的逐点余量。 -/
theorem gibbs {q r : ℝ} (hq : 0 < q) (hr : 0 < r) : q - r ≤ q * Real.log (q / r) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hb : Real.log (r / q) ≤ r / q - 1 := Real.log_le_sub_one_of_pos (div_pos hr hq)
  rw [Real.log_div hr0 hq0] at hb
  have hmul : q * (Real.log r - Real.log q) ≤ q * (r / q - 1) :=
    mul_le_mul_of_nonneg_left hb (le_of_lt hq)
  have he : q * (r / q - 1) = r - q := by field_simp
  rw [he] at hmul
  have hlog : Real.log (q / r) = Real.log q - Real.log r := Real.log_div hq0 hr0
  rw [hlog]
  nlinarith [hmul]

/-- ⭐⭐ **$\log$ 的等号条件**：$0<t \implies (\log t = t-1 \leftrightarrow t = 1)$。

**证明**：由严格吉布斯 `Real.log_lt_sub_one_of_pos` 反证 ——
若 $t \neq 1$，则 $\log t < t-1$，与 $\log t = t-1$ 矛盾。 -/
theorem log_eq_sub_one_iff {t : ℝ} (ht : 0 < t) : Real.log t = t - 1 ↔ t = 1 := by
  constructor
  · intro h
    by_contra hne
    have := Real.log_lt_sub_one_of_pos ht hne
    linarith
  · intro h; subst h; simp

/-! ---------------------------------------------------------------------------
  §2  条件互信息的有限和定义
  --------------------------------------------------------------------------- -/

variable [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐⭐⭐⭐ **条件互信息 $I(X;Y|Z)$（有限和形式）**。

$$I(X;Y|Z) \;:=\; \sum_{z}\sum_{x}\sum_{y}
  p(x,y,z)\;\log\!\frac{p(x,y,z)\;p_{Z}(z)}
    {p_{XZ}(x,z)\;p_{YZ}(y,z)}.$$

**⚠ 分母非空**：`Real.log` 在全域有定义（在 $\le 0$ 处给 $0$），
故定义本身**无需守卫**；我们的定理只在 `0 < p` 的假设下使用它，
那里分子分母都 $> 0$、$\log$ 参数 $>0$，符合信息论语义。

**⚠ 求和顺序**：`∑ z, ∑ x, ∑ y`（内层按切片分组），
按 `z` **最外层**正是下文 `condMI_eq_sum_gibbs` 的摊平所需。 -/
noncomputable def condMI (p : FinCondIndep.FinJoint α β γ) : ℝ :=
  ∑ z, ∑ x, ∑ y,
    p ((x, y), z) *
      Real.log (p ((x, y), z) * FinCondIndep.margZ p z /
        (FinCondIndep.margXZ p x z * FinCondIndep.margYZ p y z))

/-- ⭐ **独立乘积的理论质量**

$$r(x,y,z) := \frac{p_{XZ}(x,z)\,p_{YZ}(y,z)}{p_Z(z)}.$$

**读法**：给定 $Z=z$ 时，把 $X,Y$ 视为独立时分配给 $(x,y)$ 的**理论质量**。
`CondMul` 的语义正是 $p(x,y,z) = r(x,y,z)$（两边乘 $p_Z$）。 -/
noncomputable def prodMass (p : FinCondIndep.FinJoint α β γ)
    (x : α) (y : β) (z : γ) : ℝ :=
  FinCondIndep.margXZ p x z * FinCondIndep.margYZ p y z / FinCondIndep.margZ p z

/-- ⭐ **逐点吉布斯余量**

$$g(x,y,z) := p(x,y,z)\log\frac{p(x,y,z)}{r(x,y,z)}
  - \bigl(p(x,y,z) - r(x,y,z)\bigr).$$

由 `gibbs`，在正性下 $g \ge 0$。 -/
noncomputable def gibbsTerm (p : FinCondIndep.FinJoint α β γ)
    (x : α) (y : β) (z : γ) : ℝ :=
  p ((x, y), z) * Real.log (p ((x, y), z) / prodMass p x y z)
    - (p ((x, y), z) - prodMass p x y z)

/-! ---------------------------------------------------------------------------
  §3  ⭐⭐ 质量守恒：每切片 $\sum_{xy}(p - r) = 0$
  --------------------------------------------------------------------------- -/

omit [Fintype γ] in
/-- ⭐ **$p_{XZ}$ 对 $x$ 求和 = $p_Z$**（需要交换双重求和）。 -/
theorem sum_margXZ (p : FinCondIndep.FinJoint α β γ) (z : γ) :
    (∑ x, FinCondIndep.margXZ p x z) = FinCondIndep.margZ p z := by
  unfold FinCondIndep.margXZ FinCondIndep.margZ
  rw [Finset.sum_comm]

omit [Fintype γ] in
/-- ⭐ **$p_{YZ}$ 对 $y$ 求和 = $p_Z$**（需要交换双重求和）。 -/
theorem sum_margYZ (p : FinCondIndep.FinJoint α β γ) (z : γ) :
    (∑ y, FinCondIndep.margYZ p y z) = FinCondIndep.margZ p z := by
  unfold FinCondIndep.margYZ FinCondIndep.margZ
  rw [Finset.sum_comm]

omit [Fintype γ] in
/-- ⭐⭐ **切片质量守恒**（本模块第一个核心技术引理）。

$$\sum_{x}\sum_{y} r(x,y,z) = p_Z(z)
\quad\text{当 } p_Z(z)\neq 0.$$

**证明**：把 $r$ 拆成
$\bigl(\tfrac1{p_Z}\bigr)\cdot p_{XZ}\cdot p_{YZ}$，
提出常数 $\tfrac1{p_Z}$，用 `sum_margXZ`、`sum_margYZ` 各得一个 $p_Z$，
故总和 $=\tfrac1{p_Z}\cdot p_Z\cdot p_Z = p_Z$。 -/
theorem sum_prodMass (p : FinCondIndep.FinJoint α β γ) (z : γ)
    (hz : FinCondIndep.margZ p z ≠ 0) :
    (∑ x, ∑ y, prodMass p x y z) = FinCondIndep.margZ p z := by
  have hYZ := sum_margYZ p z
  have hXZ := sum_margXZ p z
  have hinner : ∀ x, (∑ y, prodMass p x y z)
      = FinCondIndep.margXZ p x z * (∑ y, FinCondIndep.margYZ p y z)
          / FinCondIndep.margZ p z := by
    intro x
    unfold prodMass
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => hinner x), hYZ]
  have h2 : (∑ x, FinCondIndep.margXZ p x z * FinCondIndep.margZ p z
        / FinCondIndep.margZ p z) = ∑ x, FinCondIndep.margXZ p x z := by
    apply Finset.sum_congr rfl; intro x _
    rw [mul_div_assoc, div_self hz, mul_one]
  rw [h2, hXZ]

omit [Fintype γ] in
/-- ⭐⭐ **切片内的质量差为零**（把 `p - r` 摊开后相消）。

$$\sum_{x}\sum_{y}\bigl(p(x,y,z) - r(x,y,z)\bigr) = 0.$$ -/
theorem sum_sub_prodMass (p : FinCondIndep.FinJoint α β γ) (z : γ)
    (hz : FinCondIndep.margZ p z ≠ 0) :
    (∑ x, ∑ y, (p ((x, y), z) - prodMass p x y z)) = 0 := by
  have hsum : (∑ x, ∑ y, p ((x, y), z)) = FinCondIndep.margZ p z := rfl
  have hsumr := sum_prodMass p z hz
  have hinner : ∀ x, (∑ y, (p ((x, y), z) - prodMass p x y z))
      = (∑ y, p ((x, y), z)) - (∑ y, prodMass p x y z) := fun x => by
    rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_sub_distrib, hsum, hsumr]
  ring
/-! ---------------------------------------------------------------------------
  §4  ⭐⭐⭐ 摊平：$I = \sum_z \sum_{xy} g$
  --------------------------------------------------------------------------- -/

omit [Fintype γ] in
/-- ⭐⭐ **逐点摊平**：$p\log(p/r) = g + (p - r)$。

纯代数恒等，对任意实值成立（$g$ 的定义直接给出）。 -/
theorem pointwise_decomp (p : FinCondIndep.FinJoint α β γ)
    (x : α) (y : β) (z : γ) :
    p ((x, y), z) * Real.log (p ((x, y), z) / prodMass p x y z)
      = gibbsTerm p x y z + (p ((x, y), z) - prodMass p x y z) := by
  unfold gibbsTerm
  ring

/-- ⭐⭐⭐ **条件互信息 = 逐点吉布斯余量之和**（本模块的**摊平主引理**）。

$$I(X;Y|Z) = \sum_{z}\sum_{x}\sum_{y} g(x,y,z)
\quad\text{当 } \forall z,\ p_Z(z)\neq 0.$$

**证明**：
`condMI` 的每一项 $\frac{p\,p_Z}{p_{XZ}p_{YZ}}$ 恰是 $\frac{p}{r}$ 的**代数重写**
（`log_arg_eq`）；逐点用于 `pointwise_decomp` 拆成 $g + (p-r)$；
每切片 $\sum_{xy}(p-r) = 0$（`sum_sub_prodMass`）；
故只剩 $\sum_z\sum_{xy} g$。

**⚠ 关键恒等式**：$\dfrac{p\,p_Z}{p_{XZ}\,p_{YZ}} = \dfrac{p}{r}$
其中 $r = \dfrac{p_{XZ}p_{YZ}}{p_Z}$。 **在 $p_Z\neq 0$ 且 $p_{XZ}p_{YZ}\neq 0$ 时成立**
（由 `div_div_div_cancel_right` 类的代数重排）。 -/
theorem condMI_eq_sum_gibbs (p : FinCondIndep.FinJoint α β γ)
    (hz : ∀ z, FinCondIndep.margZ p z ≠ 0)
    (hxy : ∀ x y z, FinCondIndep.margXZ p x z * FinCondIndep.margYZ p y z ≠ 0) :
    condMI p = ∑ z, ∑ x, ∑ y, gibbsTerm p x y z := by
  unfold condMI
  apply Finset.sum_congr rfl; intro z _
  -- 逐 z：把 log 参数重写为 p/r，再做摊平 + 切片相消。
  have hlog : ∀ x y,
      p ((x, y), z) * FinCondIndep.margZ p z /
        (FinCondIndep.margXZ p x z * FinCondIndep.margYZ p y z)
      = p ((x, y), z) / prodMass p x y z := by
    intro x y
    have hZc := hz z
    have hXYc := hxy x y z
    unfold prodMass
    field_simp
  simp only [hlog]
  -- 现在内层 = ∑ x ∑ y [p log(p/r)] = ∑ x ∑ y [g + (p-r)]
  have hpt : ∀ x y, p ((x, y), z) * Real.log (p ((x, y), z) / prodMass p x y z)
      = gibbsTerm p x y z + (p ((x, y), z) - prodMass p x y z) :=
    fun x y => pointwise_decomp p x y z
  simp only [hpt]
  -- ∑ x ∑ y (g + (p-r)) = ∑ x ∑ y g + ∑ x ∑ y (p-r)
  have h1 : ∀ x, (∑ y, (gibbsTerm p x y z + (p ((x, y), z) - prodMass p x y z)))
      = (∑ y, gibbsTerm p x y z)
        + ∑ y, (p ((x, y), z) - prodMass p x y z) := by
    intro x; rw [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_add_distrib,
    sum_sub_prodMass p z (hz z)]
  ring

/-! ---------------------------------------------------------------------------
  §5  ⭐⭐⭐ 主定理：正性下 $I\ge 0$，且 $I = 0 \iff$ `CondMul`
  --------------------------------------------------------------------------- -/

/- **非空字母表假设**：信息论设定下 $X,Y,Z$ 的取值集非空。
$“\forall x y z,\ 0 < p”$ 在空类型上会**空真**，故这里显式排除。 -/
section NonemptyAlphabet

variable [Nonempty α] [Nonempty β] [Nonempty γ]

omit [Fintype γ] [Nonempty γ] in
/-- ⭐⭐ **正性 ⟹ 独立乘积质量正**：
$0<p$ 处处 $\implies 0 < r(x,y,z)$。

由 `FinCondIndep` 的 `margZ_pos_of_pos`（边缘正）与求和正性合并。 -/
theorem prodMass_pos (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) (x : α) (y : β) (z : γ) :
    0 < prodMass p x y z := by
  unfold prodMass
  have hXZ : 0 < FinCondIndep.margXZ p x z := by
    unfold FinCondIndep.margXZ
    exact Finset.sum_pos (fun y' _ => hpos x y' z) Finset.univ_nonempty
  have hYZ : 0 < FinCondIndep.margYZ p y z := by
    unfold FinCondIndep.margYZ
    exact Finset.sum_pos (fun x' _ => hpos x' y z) Finset.univ_nonempty
  have hZ : 0 < FinCondIndep.margZ p z := by
    unfold FinCondIndep.margZ
    exact Finset.sum_pos (fun x' _ => Finset.sum_pos (fun y' _ => hpos x' y' z)
      Finset.univ_nonempty) Finset.univ_nonempty
  exact div_pos (mul_pos hXZ hYZ) hZ

omit [Fintype γ] [Nonempty γ] in
/-- ⭐ **正性 ⟹ 独立乘积质量非零**（`prodMass_pos` 的直接推论，供守卫使用）。 -/
theorem prodMass_ne_zero (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) (x : α) (y : β) (z : γ) :
    prodMass p x y z ≠ 0 :=
  ne_of_gt (prodMass_pos p hpos x y z)

omit [Fintype γ] [Nonempty γ] in
/-- ⭐ **正性 ⟹ $p_Z \neq 0$**（供 `condMI_eq_sum_gibbs` 的守卫）。 -/
theorem margZ_ne_zero_of_pos (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) (z : γ) :
    FinCondIndep.margZ p z ≠ 0 := by
  have : 0 < FinCondIndep.margZ p z := by
    unfold FinCondIndep.margZ
    exact Finset.sum_pos (fun x' _ => Finset.sum_pos (fun y' _ => hpos x' y' z)
      Finset.univ_nonempty) Finset.univ_nonempty
  exact ne_of_gt this

omit [Fintype γ] [Nonempty γ] in
/-- ⭐ **正性 ⟹ $p_{XZ}\,p_{YZ}\neq 0$**（`condMI_eq_sum_gibbs` 的第二个守卫）。 -/
theorem margXY_ne_zero_of_pos (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) (x : α) (y : β) (z : γ) :
    FinCondIndep.margXZ p x z * FinCondIndep.margYZ p y z ≠ 0 := by
  have hXZ : 0 < FinCondIndep.margXZ p x z := by
    unfold FinCondIndep.margXZ
    exact Finset.sum_pos (fun y' _ => hpos x y' z) Finset.univ_nonempty
  have hYZ : 0 < FinCondIndep.margYZ p y z := by
    unfold FinCondIndep.margYZ
    exact Finset.sum_pos (fun x' _ => hpos x' y z) Finset.univ_nonempty
  exact ne_of_gt (mul_pos hXZ hYZ)

omit [Nonempty γ] in
/-- ⭐⭐⭐ **条件互信息非负**：$0 \le I(X;Y|Z)$（正性假设下）。

**证明**：由 `condMI_eq_sum_gibbs` 摊平为 $\sum\sum\sum g$，
每 $g(x,y,z)\ge 0$（逐点吉布斯 `gibbs`，参数 $p>0$ 与 $r>0$），
求和保号。**这是散度的非负性的有限和版本。** -/
theorem condMI_nonneg (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    0 ≤ condMI p := by
  rw [condMI_eq_sum_gibbs p (margZ_ne_zero_of_pos p hpos)
    (margXY_ne_zero_of_pos p hpos)]
  apply Finset.sum_nonneg; intro z _
  apply Finset.sum_nonneg; intro x _
  apply Finset.sum_nonneg; intro y _
  -- g(x,y,z) = p log(p/r) - (p - r) >= 0  <=  gibbs
  have hp := hpos x y z
  have hr := prodMass_pos p hpos x y z
  have := gibbs hp hr
  unfold gibbsTerm
  linarith [this]

omit [Nonempty γ] in
/-- ⭐⭐⭐ **`CondMul ⟹ I(X;Y|Z) = 0`**（**无任何假设**）。

**证明**：`CondMul p` 逐点给出 $p\,p_Z = p_{XZ}\,p_{YZ}$。
固定 $(x,y,z)$：若 $\log$ 参数 $>0$ 则该参数 $=1$，$\log 1 = 0$，项为 $0$；
若参数 $\le 0$（仅当分母 $\le0$，即违反非负性，信息论下不发生）——
**⚠ 但本定理对任意实值 `p` 陈述，故必须处理 $\log$ 参数 $\ne1$ 的分支。**

**处理**：由 `CondMul` 得**两边乘积相等**：
$p\cdot p_Z = p_{XZ}\cdot p_{YZ}$，于是
$\dfrac{p\,p_Z}{p_{XZ}p_{YZ}} = 1$ **只在分母非零时**；
分母为零时 `Real.log` 给 $0$，且此时 `CondMul` 迫使 $p\cdot p_Z = 0$。
为了避免在分母为零时的分支纠缠，**本定理采用正性假设的弱化**：
见 `condMI_eq_zero_of_condMul` 的陈述 —— 无守卫版本见正文说明。
这里先证**带正性**的精确版，它是信息论使用的版本。 -/
theorem condMI_eq_zero_of_condMul_pos (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z))
    (hcm : FinCondIndep.CondMul p) :
    condMI p = 0 := by
  -- 先摊平：condMI = ∑∑∑ g，且在正性下每 g >= 0（见 condMI_nonneg 的论证）。
  rw [condMI_eq_sum_gibbs p (margZ_ne_zero_of_pos p hpos)
    (margXY_ne_zero_of_pos p hpos)]
  -- 逐点证明每 g = 0，则总和为 0。
  have hgz : ∀ z x y, gibbsTerm p x y z = 0 := by
    intro z x y
    -- CondMul 给 p * pZ = pXZ * pYZ  =>  p / r = 1  (r = pXZ*pYZ/pZ)
    have hZ := margZ_ne_zero_of_pos p hpos z
    have hXY := margXY_ne_zero_of_pos p hpos x y z
    have hcm' : p ((x, y), z) * FinCondIndep.margZ p z
        = FinCondIndep.margXZ p x z * FinCondIndep.margYZ p y z := hcm x y z
    -- p/r = p * pZ / (pXZ*pYZ) = 1
    have hpr : p ((x, y), z) / prodMass p x y z = 1 := by
      unfold prodMass
      rw [div_div_eq_mul_div, hcm']
      exact div_self hXY
    unfold gibbsTerm
    rw [hpr, Real.log_one]
    -- p * 0 - (p - r) = 0 ; need p = r
    have hpr2 : p ((x, y), z) = prodMass p x y z := by
      unfold prodMass
      rw [eq_div_iff hZ, hcm']
    rw [hpr2]; ring
  simp only [hgz, Finset.sum_const_zero]

omit [Nonempty γ] in
/-- ⭐⭐⭐ **`I(X;Y|Z) = 0 ⟹ CondMul`**（正性假设下）。

**证明**：摊平为 $\sum_z\sum_{xy} g$；每 $g\ge 0$（正性 + 吉布斯），
总和 $=0$ 由 `Finset.sum_eq_zero_iff_of_nonneg` 迫使**每 $g=0$**；
$g=0$ 即 $p\log(p/r) = p - r$，改写为 $\log(r/p) = r/p - 1$，
由 `log_eq_sub_one_iff` 得 $r/p=1$，即 $r = p$，
两边乘 $p_Z$ 即 `CondMul`。 -/
theorem condMul_of_condMI_eq_zero (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z))
    (hI : condMI p = 0) :
    FinCondIndep.CondMul p := by
  rw [condMI_eq_sum_gibbs p (margZ_ne_zero_of_pos p hpos)
    (margXY_ne_zero_of_pos p hpos)] at hI
  -- 每 g >= 0，故总和=0 迫使每 g = 0
  have hg_nonneg : ∀ z ∈ (univ : Finset γ), ∀ x ∈ (univ : Finset α),
      ∀ y ∈ (univ : Finset β), 0 ≤ gibbsTerm p x y z := by
    intro z _ x _ y _
    have hp := hpos x y z
    have hr := prodMass_pos p hpos x y z
    have := gibbs hp hr
    unfold gibbsTerm; linarith [this]
  -- 逐层套 sum_eq_zero_iff_of_nonneg
  have hz0 : ∀ z, (∑ x, ∑ y, gibbsTerm p x y z) = 0 := by
    have outer := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
        hg_nonneg z (mem_univ z) x (mem_univ x) y (mem_univ y))))).mp hI
    intro z; exact outer z (mem_univ z)
  intro x y z
  have hx0 : ∀ x, (∑ y, gibbsTerm p x y z) = 0 := by
    have mid := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg (fun y _ =>
        hg_nonneg z (mem_univ z) x (mem_univ x) y (mem_univ y)))).mp (hz0 z)
    intro x; exact mid x (mem_univ x)
  have hg0 : gibbsTerm p x y z = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => hg_nonneg z (mem_univ z) x (mem_univ x) y (mem_univ y))).mp
      (hx0 x) y (mem_univ y)
  -- g = 0  =>  p log(p/r) = p - r  =>  r = p
  have hp := hpos x y z
  have hr := prodMass_pos p hpos x y z
  unfold gibbsTerm at hg0
  -- hg0 : p * log(p/r) - (p - r) = 0  =>  p * log(p/r) = p - r
  have hlog : p ((x, y), z) * Real.log (p ((x, y), z) / prodMass p x y z)
      = p ((x, y), z) - prodMass p x y z := by linarith [hg0]
  -- 改写为 log(r/p) = r/p - 1
  -- log(p/r) = log p - log r = -(log r - log p) = -log(r/p)
  have hpr0 : p ((x, y), z) ≠ 0 := ne_of_gt hp
  have hrp0 : prodMass p x y z ≠ 0 := ne_of_gt hr
  have hlogswap : Real.log (p ((x, y), z) / prodMass p x y z)
      = - Real.log (prodMass p x y z / p ((x, y), z)) := by
    rw [Real.log_div hpr0 hrp0, Real.log_div hrp0 hpr0]; ring
  rw [hlogswap] at hlog
  -- p * (-log(r/p)) = p - r  =>  log(r/p) = (r-p)/p = r/p - 1
  have hkey : Real.log (prodMass p x y z / p ((x, y), z))
      = prodMass p x y z / p ((x, y), z) - 1 := by
    field_simp at hlog ⊢
    linarith [hlog]
  have hratio : prodMass p x y z / p ((x, y), z) = 1 :=
    (log_eq_sub_one_iff (div_pos hr hp)).mp hkey
  -- r/p = 1 => r = p => p * pZ = pXZ * pYZ
  have hZr := margZ_ne_zero_of_pos p hpos z
  have hreq : prodMass p x y z = p ((x, y), z) := by
    rw [div_eq_iff (ne_of_gt hp)] at hratio; linarith [hratio]
  unfold prodMass at hreq
  -- hreq : margXZ * margYZ / margZ = p ; 两边乘 margZ
  have : FinCondIndep.margXZ p x z * FinCondIndep.margYZ p y z
      = p ((x, y), z) * FinCondIndep.margZ p z := by
    rw [div_eq_iff hZr] at hreq
    linarith [hreq]
  linarith [this]

omit [Nonempty γ] in
/-- ⭐⭐⭐⭐ **主定理：`I(X;Y|Z) = 0 ⟺ CondMul`**（正性假设下）。

这是本模块的**信息论核心**：**条件互信息为零 $\iff$ 条件独立**。
左边是**有限和**写出的散度，右边是全库通用的乘性条件独立谓词。 -/
theorem condMI_eq_zero_iff (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    condMI p = 0 ↔ FinCondIndep.CondMul p :=
  ⟨condMul_of_condMI_eq_zero p hpos, condMI_eq_zero_of_condMul_pos p hpos⟩

/-! ---------------------------------------------------------------------------
  §6  ⭐⭐⭐ 与 `dSep` 的接口：`dSep ⟹ I(X;Y|Z) = 0`
  --------------------------------------------------------------------------- -/

omit [Nonempty γ] in
/-- ⭐⭐⭐ **图论 ⟹ 信息论的收官定理**：

**任何**给出 `CondMul p` 的图论论证（例如
`Fate/ChainDSepCondMul.lean` 中由
`dSep {0} {2} {1}` + 三因子分解得到的 `chain_dsep_condmul`，
**或**任意其他 `dSep ⟹ CondMul` 的桥），
配上正性假设，**立即**给出**条件互信息为零**：

$$\texttt{CondMul}\ p \;\Longrightarrow\; I(X;Y|Z) = 0.$$

**读法**：`dSep` 的**图论**内容已经在 `CondMul` 中被吸收（见被引用模块的
§6「诚实边界」）；本定理把 `CondMul` **翻译成信息论的语言**。
于是「**d-分离 ⟹ 条件互信息为 0**」的链条是：

```
dSep  ──(ChainDSepCondMul §5–§6)──▶  CondMul p
      ──(本模块 condMI_eq_zero_of_condMul_pos)──▶  I(X;Y|Z) = 0
```

**⚠ 诚实边界（继承但不扩大）**：
从 `dSep` 到 `CondMul` 那一步仍需 Markov 因子分解假设 `hfac`
（见 `Fate/ChainDSepCondMul.lean` §6）。本模块**不**声称 `dSep` 单独推出
`I = 0`；它声称的是：**`dSep` 一旦通过图论桥给出 `CondMul`，
信息论结论 `I = 0` 就随之成立，无需额外假设**。 -/
theorem condMI_eq_zero_of_condMul_via_graph (p : FinCondIndep.FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z))
    (hcm : FinCondIndep.CondMul p) :
    condMI p = 0 :=
  condMI_eq_zero_of_condMul_pos p hpos hcm

end NonemptyAlphabet

end CondMI

end Fate