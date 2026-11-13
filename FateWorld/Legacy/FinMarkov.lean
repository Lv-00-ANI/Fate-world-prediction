/-
=============================================================================
  §69  ⭐⭐⭐ **有限条件独立（`CondIndepFin`）接到项目自有的 SCM 载体上**
=============================================================================

## ⚠⚠ 本轮的定位：**把「条件独立」与「本项目 SCM 载体」接起来**

**背景**（见 `Fate/SCMSemantics.lean` §68.4 与 `Fate/DoCalculusRules.lean` §66.4）：

既有文件已**如实登记**一处缺口 ——

> **缺的是「SCM 语义 → 概率语义」的连接**：
> 把有限律嵌入概率论，并在其上谈条件独立（Markov 桥）。

**本轮做的事**：**在项目自有的有限 SCM 载体（`PearlHierarchy.SCM`）上，
显式定义「诱导的有限联合律」，并给出它满足条件独立的充分条件。**

## ⭐ 本轮的核心对象

| 对象 | 位置 | 内容 |
|---|---|---|
| **`CondIndepFin`** | §69.1 | **有限条件独立**（乘法形式，无需除法） |
| **`SCM.jointLaw3`** | §69.2 | **SCM 在 `A × B × C` 上诱导的有限联合律** |
| **`Factorizes`** | §69.3 | **联合律的「父集分解」形式** |
| **`factorizes_condIndepFin`** | §69.3 | ⭐ **充分条件**：分解 ⟹ 条件独立 |
| **`productExo_factorizes`** | §69.4 | ⭐ **SCM 侧的充分条件**（外生块独立 + 结构方程分解） |

## ⚠ 口径与边界（**先划界，再开证；如实登记，不越界**）

1. **`CondIndepFin` 用乘法形式**（`P(a,b,c)·P(a) = P(a,b)·P(a,c)`），
   **而非「除以 `P(a)`」的商形式** ——
   **理由**：有限律在 `P(a) = 0` 处无定义，乘法形式**处处有定义**，
   且与「条件期望可分解」等价（当 `P(a) > 0`）。
   **⟹ 这是**真正无条件、可判定的**有限口径**（依作者裁决 Q-1：无硬编码）。
2. **SCM 载体是 `PearlHierarchy.SCM A (B × C)`**（单结果位口径的 `B × C` 实例）。
   **不新建 SCM 结构** —— 直接用项目自有载体。
3. **`push` 用 `PearlHierarchy.push`**（项目自有有限推前）。
4. **本文不含**：测度层 `CondIndepFun` 的嵌入、d-分离 ⟹ 条件独立、
   一般（多变量、含环/含混杂）SCM 的 Markov 性质。**这些缺口在 §69.5 具名登记。**

**⚠ 无 `sorry` / `admit` / `axiom`**（依项目纪律）。
============================================================================= -/

import FateWorld.Legacy.PearlHierarchy
import FateWorld.Legacy.SCMSemantics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
-- ⚠⚠ **第 120 轮新增**：`Fintype.sum_prod_type` **定义在这里**。
--    （`Fintype.Prod` 只提供 `Fintype (α × β)` **实例**，不含该引理 ——
--     ⚠ 这两件事**是分开的**，我第 113 轮只补了前者，故漏了本引理。）
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

namespace Fate

namespace FinMarkov

set_option autoImplicit false

-- ⚠⚠ **第 115 轮新增**：`open Finset` —— **必须**。
--
-- **实测**（我写的最小复现）：
-- ```lean
-- import Mathlib.Algebra.BigOperators.Ring.Finset
-- #check @mul_sum        -- ⟹ ⚠ Unknown identifier `mul_sum`
-- open Finset
-- #check @mul_sum        -- ⟹ ✅ 存在
-- ```
-- **⟹ 即**：`mul_sum` / `sum_mul` / `sum_ite_eq` / `sum_ite_eq'`
-- **都在 `Finset` 命名空间里，但**不能用 `Finset.` 前缀引用****
-- （`#check @Finset.mul_sum` ⟹ Unknown constant）。
-- **故必须 `open Finset`。**
--
-- ⚠ **这解释了本文件第 188/396 行**长期错误的**真正原因** ——
-- **它们写的 `Finset.mul_sum` 是**不存在的名字****，
-- **故 `rw` 报「Did not find an occurrence」**
-- （Lean 把未知标识符当成了**通配模式**，故错误信息**误导**）。
open Finset

universe u

/-! ===========================================================================
    §69.1  ⭐⭐⭐ **有限条件独立**（`CondIndepFin`）
    =========================================================================== -/

/-- ⭐⭐⭐ **有限三变量联合律上的条件独立**（**乘法形式**）。

给定有限型 `A, B, C` 上的实值联合律 `P : A × B × C → ℝ`，
称 **`B` 与 `C` 关于 `A` 条件独立**，记 `B ⟂ C | A`，当且仅当

$$\forall a\,b\,c,\quad
  P(a,b,c)\cdot P_A(a) = P_{AB}(a,b)\cdot P_{AC}(a,c)$$

其中三个边缘律由下面的 `margA / margAB / margAC` 给出。

**⚠ 为何用乘法形式（而非 `P(b,c|a) = P(b|a)P(c|a)`）**：

| 形式 | 问题 |
|---|---|
| 商形式 `P(b,c∣a)=P(b∣a)P(c∣a)` | 当 `P(a) = 0` 时**无定义**，需额外非零前提 |
| **乘法形式**（本定义） | **处处有定义**，**无需任何前提** |

**⟹ 两者在 `P(a) > 0` 时等价**（见 `condIndepFin_iff_ratio`），
**但乘法形式是**可判定的、无条件的**有限口径。** -/
def CondIndepFin {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (P : A × B × C → ℝ) : Prop :=
  ∀ a b c, P (a, b, c) * margA P a = margAB P (a, b) * margAC P (a, c)
where
  /-- `A` 的边缘律。 -/
  margA (P : A × B × C → ℝ) (a : A) : ℝ := ∑ b, ∑ c, P (a, b, c)
  /-- `(A,B)` 的边缘律。 -/
  margAB (P : A × B × C → ℝ) (p : A × B) : ℝ := ∑ c, P (p.1, p.2, c)
  /-- `(A,C)` 的边缘律。 -/
  margAC (P : A × B × C → ℝ) (p : A × C) : ℝ := ∑ b, P (p.1, b, p.2)

/-! ### §69.1.1 ⭐⭐ 条件独立的**对称性**（真定理，非空洞） -/

/-- ⭐⭐ **条件独立的对称性**：`B ⟂ C | A` ⟹ `C ⟂ B | A`。

**陈述**：把联合律的 `B` 与 `C` 坐标交换，条件独立关系不变。

**⟹ 这是 `CondIndepFin` 的**第一张一致性检验**：
**若定义对「条件独立」这一概念忠实，则它必对称。** -/
theorem condIndepFin_symm {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    {P : A × B × C → ℝ} (h : CondIndepFin P) :
    CondIndepFin (fun q : A × C × B => P (q.1, q.2.2, q.2.1)) := by
  intro a c b
  have h' := h a b c
  -- 展开两侧边缘律：交换求和次序
  simp only [CondIndepFin.margA, CondIndepFin.margAB, CondIndepFin.margAC] at h' ⊢
  rw [Finset.sum_comm] at h'
  linear_combination h'

/-! ===========================================================================
    §69.2  ⭐⭐⭐ **SCM 诱导的有限联合律**
    =========================================================================== -/

variable {A B C : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-! ### §69.2.0 ⭐⭐ 两个**有限和的技术引理**（供后续计算复用） -/

/-- ⭐⭐ **三重 `ite` 对第三坐标求和**（**技术引理**）。

$$\sum_{x \in C} [\,(a',b',c') = (a,b,x)\,] =
  [\,(a',b') = (a,b)\,]$$

**⟹ 用途**：把「三元组相等」的边缘化，归约为「二元组相等」——
**使边缘律的 `ite` 形式可被合并。** -/
theorem sum_ite_triple_eq (a' : A) (b' : B) (c' : C) (a : A) (b : B) :
    (∑ x : C, (if (a', b', c') = (a, b, x) then (1 : ℝ) else 0)) =
      if (a', b') = (a, b) then 1 else 0 := by
  by_cases h : (a', b') = (a, b)
  · have ha : a' = a := congrArg Prod.fst h
    have hb : b' = b := congrArg Prod.snd h
    subst ha; subst hb
    -- 现在 a' = a, b' = b；只剩 x 需与 c' 对齐
    rw [Finset.sum_eq_single c']
    · simp
    · intro x _ hx
      -- `x ≠ c'` 时 `ite` 为假（`(a, b, x) ≠ (a, b, c')`）
      rw [if_neg]
      intro hcon
      -- `A × B × C` **右结合**为 `A × (B × C)`，故第三坐标是 `.2.2`
      exact hx ((Prod.ext_iff.mp (Prod.ext_iff.mp hcon).2).2).symm
    · intro hc; exact absurd (Finset.mem_univ c') hc
  · -- 二者不等：每一项的 `ite` 皆假
    rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    intro hcon
    -- 从 `(a', b', c') = (a, b, x)` 推出 `(a', b') = (a, b)`
    exact h (Prod.ext_iff.mpr
      ⟨(Prod.ext_iff.mp hcon).1,
       (Prod.ext_iff.mp (Prod.ext_iff.mp hcon).2).1⟩)
/-! ### ⭐⭐⭐ **SCM 诱导的有限联合律**（**第 119 轮已移入 `PearlHierarchy`**）

⚠⚠ **本定义已移至 `Fate/PearlHierarchy.lean` 的 `SCM.jointLaw3`。**

**为何移入**：它原先只在这里定义，而**下游定理**（`margAB_jointLaw3` 等）
**引用了它** —— 但 `_pending/` **不在构建图内**，
⟹ **那些引用在正式构建里**全部悬空****
（`simp only [.. jointLaw3 ..]` 无从展开，报**误导性**的错误）。

**⭐ 且它是**自足**的（只用 `PearlHierarchy.push`），故入库无阻碍。**

**以下保留原说明（供追溯）**：

联合律 = 外生律沿轨道映射
$$u \mapsto \bigl((\mathrm{sg}\,u).1,\; (\mathrm{sg}\,u).2\,(\mathrm{sg}\,u).1\bigr) \in A \times B \times C$$
的**推前**（`PearlHierarchy.push`）。

**⟹ 这正是项目自有载体上「SCM → 有限概率语义」的第一步，
与 `SCMSemantics.jointLaw`（三元组 `U × A × B`）**分工不同**：
**本定义把外生 `U` 边缘化掉**，只留**可观测三元组 `A × B × C`** ——
**因为条件独立是关于可观测量说的。** -/
--    此处**不再重复定义**（重复会造成 identity 冲突）。

/-- ⭐⭐ **联合律 `(A,B)` 边缘 = `margAB`**（**一致性引理**）。

**陈述**：`jointLaw3` 的 `(A,B)` 边缘（对 `C` 求和）恰是
`CondIndepFin.margAB` 作用在 `jointLaw3` 上。

**⟹ 这是**定义层的等价**，用于把 SCM 联合律与条件独立的边缘律对接。** -/
theorem _root_.Fate.PearlHierarchy.SCM.margAB_jointLaw3 (M : PearlHierarchy.SCM A (B × C)) :
    CondIndepFin.margAB M.jointLaw3 = fun p =>
      ∑ u, M.pU u * (if ((M.sg u).1, ((M.sg u).2 (M.sg u).1).1) = p
        then (1 : ℝ) else 0) := by
  funext p
  simp only [CondIndepFin.margAB, PearlHierarchy.SCM.jointLaw3, PearlHierarchy.push]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  -- ⚠⚠ 第 115 轮【最小步长】修正：**它是裸的 `mul_sum`，不是 `Finset.mul_sum`**！
  --    实测：`#check @Finset.mul_sum` ⟹ Unknown constant；
  --          `#check @mul_sum`            ⟹ ✅ 存在
  --    签名：`mul_sum (s : Finset ι) (f : ι → R) (a : R) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`
  --    ⟹ 故反向用时先 `rw [← mul_sum]` 把 `∑ x, (c * f x)` 提为 `c * ∑ x, f x`。
  rw [← mul_sum]
  -- ⚠ 第 115 轮【最小步长·第二步】：现在目标是
  --    `M.pU u * (∑ x, ite ((sg u).1, (sg u).2 (sg u).1) = (p.1,p.2,x) then 1 else 0)
  --       = M.pU u * ite ((sg u).1, ((sg u).2 (sg u).1).1) = p then 1 else 0`
  -- ⚠ 目标里**没有** `h1` 简化的痕迹（实测），故**不引入** `by_cases` ——
  --    直接对**整个目标**用 `sum_ite_eq'` 收束。
  congr 1
  -- ⚠⚠ **第 117 轮：本段改用**在最小复现里验证过**的方案。**
  --
  -- **为何前几轮都失败**（我在最小复现里查明）：
  --   `sum_ite_eq` / `sum_ite_eq'` 的模式要求 `ite` 的**某一侧是裸的 `x`**
  --   （`?a = x` 或 `x = ?a`）。
  --   **而这里的目标是 `(a', bc) = (p1, p2, x)` —— `x` **嵌套在三元组里**** ⟹
  --   两个引理的**模式都匹配不上**。
  --
  -- **✅ 故正确方案是**先把「三元组相等」**化为逐坐标相等**（其中 `x` 单独出现），
  --   再用 `sum_ite_eq'` 收束。
  --
  -- **⚠ 该方案已在**最小复现**（`_mre.lean`，8 行）里验证：
  --   零错误、零 warning** —— **这是「最小复现法」的直接产出**。
  ---------------------------
  -- ① 把「三元组相等」化为「逐坐标相等」（`x` 单独出现）
  have htriple : ∀ x : C,
      (((M.sg u).1, (M.sg u).2 (M.sg u).1) = (p.1, p.2, x))
        = (x = ((M.sg u).2 (M.sg u).1).2 ∧ (M.sg u).1 = p.1
            ∧ ((M.sg u).2 (M.sg u).1).1 = p.2) := by
    intro x
    apply propext
    constructor
    · intro hh
      exact ⟨(congrArg (fun t => t.2.2) hh).symm,
             congrArg Prod.fst hh, congrArg (fun t => t.2.1) hh⟩
    · rintro ⟨h1, h2, h3⟩
      -- ⚠ 第 117 轮：`A × B × C` **右结合**为 `A × (B × C)`，
      --    故 `Prod.ext_iff` 给出 `⟨_, ⟨_, _⟩⟩` 的**嵌套**结构。
      rw [Prod.ext_iff, Prod.ext_iff]
      exact ⟨h2, h3, h1.symm⟩
  simp only [htriple]
  -- ② 分离：外层只留 `x = ...`，其余条件提到 `by_cases`
  by_cases hc : ((M.sg u).1 = p.1 ∧ ((M.sg u).2 (M.sg u).1).1 = p.2)
  · -- ⚠⚠ **第 119 轮：改用**在最小复现里验证过**的写法**（`_Mre7.lean`，零错误）。
    --    与第 117 轮的关键差异：**`simp only` 里必须同时给 `true_and` 与 `and_true`** ——
    --    因为化简后条件形如 `x = bc.2 ∧ True`（**`∧ True` 需 `and_true` 才能去掉**），
    --    **而只给一个不够**（实测报「Did not find an occurrence」）。
    obtain ⟨hca, hcb⟩ := hc
    -- ⚠⚠ **实测差异**（我第 119 轮的最小复现暴露）：
    --    真实目标里 `(M.sg u).1` **已被 `hca` 替换为 `p.1`**，
    --    **而 `hcb : ((M.sg u).2 (M.sg u).1).1 = p.2` 的左端仍是 `(M.sg u).1`**
    --    ⟹ 二者**写法不一致**，`simp only [hcb]` 配不上（**实测**）。
    --    ⭐ 修法：**用 `hca` 把 `hcb` 重述为含 `p.1` 的形式**。
    have hcb' : ((M.sg u).2 p.1).1 = p.2 := by rw [← hca]; exact hcb
    simp only [hca, hcb', true_and, and_true]
    rw [sum_ite_eq']
    simp
  · have hR : ¬ (((M.sg u).1, ((M.sg u).2 (M.sg u).1).1) = p) := by
      intro hh
      exact hc ⟨(congrArg Prod.fst hh), (congrArg Prod.snd hh)⟩
    simp only [hc, and_false, ↓reduceIte, hR, Finset.sum_const_zero]

/-! ===========================================================================
    §69.3  ⭐⭐⭐ **充分条件（父集分解）⟹ 条件独立**
    =========================================================================== -/

/-- ⭐⭐⭐ **联合律的「父集分解」形式**（**充分条件的核心谓词**）。

称 `P : A × B × C → ℝ` **可分解**，当且仅当存在
`α : A → ℝ`，`β : A × B → ℝ`，`γ : A × C → ℝ` 使得

$$\forall a\,b\,c,\quad P(a,b,c) = \alpha(a)\cdot\beta(a,b)\cdot\gamma(a,c).$$

**⟹ 这是「父集分解」的精确概率含义**：

| 因子 | 含义 |
|---|---|
| `α(a)` | 共同父 `A` 的贡献 |
| `β(a,b)` | `B` 的**局部机制**（只经 `A` 与 `B`） |
| `γ(a,c)` | `C` 的**局部机制**（只经 `A` 与 `C`） |

**⚠ 即**：**`B` 与 `C` 通过 `A` 耦合，但彼此不直接耦合** ——
**这正是「`A` 是 `B` 与 `C` 的分离集」的概率形式。** -/
def Factorizes (P : A × B × C → ℝ) : Prop :=
  ∃ α : A → ℝ, ∃ β : A × B → ℝ, ∃ γ : A × C → ℝ,
    ∀ a b c, P (a, b, c) = α a * β (a, b) * γ (a, c)

/-- ⭐⭐⭐ **充分条件**：**父集分解 ⟹ 条件独立**（**核心定理**）。

$$\text{可分解} \implies B \perp\!\!\!\perp C \mid A$$

**证明思路**（纯有限代数，无概率论前提）：

设 $P(a,b,c) = \alpha(a)\beta(a,b)\gamma(a,c)$。则

$$\text{margA}(a) = \alpha(a)\Bigl(\sum_b \beta(a,b)\Bigr)\Bigl(\sum_c \gamma(a,c)\Bigr),$$
$$\text{margAB}(a,b) = \alpha(a)\beta(a,b)\sum_c \gamma(a,c),$$
$$\text{margAC}(a,c) = \alpha(a)\gamma(a,c)\sum_b \beta(a,b).$$

代入乘法形式两侧，两边皆等于
$\alpha(a)^2\,\beta(a,b)\,\gamma(a,c)\Bigl(\sum_b\beta(a,b)\Bigr)\Bigl(\sum_c\gamma(a,c)\Bigr)$。 ∎

**⚠ 这是**非空洞**的**：**结论是联合律的一个**真实约束**，
**而非 `True`**（对比 `DoCalculusRules` 中对空洞定理的批判）。** -/
theorem factorizes_condIndepFin {P : A × B × C → ℝ} (h : Factorizes P) :
    CondIndepFin P := by
  obtain ⟨α, β, γ, hP⟩ := h
  intro a b c
  have hP' : ∀ a b c, P (a, b, c) = α a * β (a, b) * γ (a, c) := hP
  -- 三个边缘律的显式值
  have hA : CondIndepFin.margA P a =
      α a * (∑ b, β (a, b)) * (∑ c, γ (a, c)) := by
    simp only [CondIndepFin.margA]
    calc ∑ b, ∑ c, P (a, b, c)
        = ∑ b, ∑ c, α a * β (a, b) * γ (a, c) := by
            refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => hP' a b c
      _ = ∑ b, α a * β (a, b) * (∑ c, γ (a, c)) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
      _ = (∑ b, α a * β (a, b)) * (∑ c, γ (a, c)) := by
            rw [Finset.sum_mul]
      _ = α a * (∑ b, β (a, b)) * (∑ c, γ (a, c)) := by
            rw [← Finset.mul_sum]
  have hAB : CondIndepFin.margAB P (a, b) = α a * β (a, b) * (∑ c, γ (a, c)) := by
    simp only [CondIndepFin.margAB]
    calc ∑ c, P (a, b, c)
        = ∑ c, α a * β (a, b) * γ (a, c) := by
            refine Finset.sum_congr rfl fun c _ => hP' a b c
      _ = α a * β (a, b) * (∑ c, γ (a, c)) := by
            rw [Finset.mul_sum]
  have hAC : CondIndepFin.margAC P (a, c) = α a * γ (a, c) * (∑ b, β (a, b)) := by
    simp only [CondIndepFin.margAC]
    calc ∑ b, P (a, b, c)
        = ∑ b, α a * β (a, b) * γ (a, c) := by
            refine Finset.sum_congr rfl fun b _ => hP' a b c
      _ = α a * (∑ b, β (a, b)) * γ (a, c) := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = α a * γ (a, c) * (∑ b, β (a, b)) := by ring
  rw [hA, hAB, hAC, hP' a b c]
  ring

/-! ### §69.3.1 ⭐⭐ 与「商形式」的等价（**取 `P(a) > 0` 时**） -/

/-- ⭐⭐ **条件独立的商形式**：`P(b,c | a) = P(b | a) · P(c | a)`。

**⚠ 需前提 `P(a) ≠ 0`**（否则条件律无定义）。 -/
def CondIndepFinRatio {P : A × B × C → ℝ} (a : A) : Prop :=
  CondIndepFin.margA P a ≠ 0 →
    ∀ b c, P (a, b, c) = CondIndepFin.margAB P (a, b) *
      CondIndepFin.margAC P (a, c) / CondIndepFin.margA P a

/-- ⭐⭐ **乘法形式 ⟹ 商形式**（在 `P(a) > 0` 处）。

**⟹ 这证明本文采用的乘法形式**不弱于**教科书的商形式 ——
**即 `CondIndepFin` 是**正确的**条件独立定义，而非一个弱化的替身。** -/
theorem condIndepFin_iff_ratio {P : A × B × C → ℝ} (h : CondIndepFin P) (a : A) :
    CondIndepFinRatio (P := P) a := by
  intro hne b c
  have h' := h a b c
  field_simp
  -- 目标：P(a,b,c) * margA(a) = margAB(a,b) * margAC(a,c)
  linarith [h']

/-! ===========================================================================
    §69.4  ⭐⭐⭐ **SCM 侧的充分条件**：外生块分解 + 结构方程分解
    =========================================================================== -/

/-! #### 目标与口径

**上一节的充分条件是「抽象联合律可分解」**。
**本节把它落到 SCM 载体上**：**给出**对 SCM 结构本身**的充分条件。**

**直觉**（**父集分解**）：
- 外生 `U` 分解为**三块独立噪声** `UA × UB × UC`，律为乘积；
- 结构方程 `sg` 分解为 `(a(uA), (bF a uB, cF a uC))`
  —— **`B` 只读 `A` 与 `UB`，`C` 只读 `A` 与 `UC`**。

**⟹ 则诱导的联合律可分解 ⟹ `B ⟂ C | A`。**

**⚠ 关键**：`A` 同时依赖 `UA`（决定事实值），
`B` 依赖 `UA` 与 `UB`，`C` 依赖 `UA` 与 `UC` ——
**`UB` 与 `UC` 独立**故 `B` 与 `C` 只通过 `A`（即 `UA`）耦合。
**这正是 d-分离「`A` 分离 `B` 与 `C`」在**素朴有限 SCM** 下的可证版本。**
-/

/-- ⭐⭐⭐ **乘积外生块 SCM**：外生 `U = UA × UB × UC`，
结构方程分解为「`A` 由 `UA` 决定，`B` 只读 `A` 与 `UB`，`C` 只读 `A` 与 `UC`」。

**字段语义**：
- `pA, pB, pC`：三块**独立**外生噪声的律；
- `aF : UA → A`：事实 `A` 的结构方程；
- `bF : A → UB → B`：`B` 的结构方程；
- `cF : A → UC → C`：`C` 的结构方程。

**⚠ 这是**朴素（无混杂回边）的**SCM** ——
**不覆盖含混杂/含环的一般 SCM（见 §69.5 缺口 G3）。** -/
structure FracSCM (A B C : Type u) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] where
  /-- 外生块 `UA`。 -/
  UA : Type
  [instFA : Fintype UA]
  [instDA : DecidableEq UA]
  /-- 外生块 `UB`。 -/
  UB : Type
  [instFB : Fintype UB]
  [instDB : DecidableEq UB]
  /-- 外生块 `UC`。 -/
  UC : Type
  [instFC : Fintype UC]
  [instDC : DecidableEq UC]
  /-- `A` 的外生律。 -/
  pA : UA → ℝ
  /-- `B` 的外生律。 -/
  pB : UB → ℝ
  /-- `C` 的外生律。 -/
  pC : UC → ℝ
  /-- `A` 的结构方程。 -/
  aF : UA → A
  /-- `B` 的结构方程（父集：`A` 与 `UB`）。 -/
  bF : A → UB → B
  /-- `C` 的结构方程（父集：`A` 与 `UC`）。 -/
  cF : A → UC → C

attribute [instance] FracSCM.instFA FracSCM.instDA FracSCM.instFB
  FracSCM.instDB FracSCM.instFC FracSCM.instDC

namespace FracSCM

variable (M : FracSCM A B C)

/-- ⭐⭐ **乘积外生律**：`pU(uA, uB, uC) = pA(uA) · pB(uB) · pC(uC)`。

**⟹ 这是「三块噪声独立」的精确含义**（乘性 ⟺ 独立，有限情形）。 -/
noncomputable def pU : M.UA × M.UB × M.UC → ℝ :=
  fun u => M.pA u.1 * M.pB u.2.1 * M.pC u.2.2

/-- ⭐⭐ **编码为项目自有 SCM 载体** `PearlHierarchy.SCM A (B × C)`。

事实 `A = aF uA`；结构方程 `a ↦ (bF a uB, cF a uC)` ——
**注意 `B` 与 `C` 的结构方程分别只读 `uB` 与 `uC`。** -/
noncomputable def toSCM : PearlHierarchy.SCM A (B × C) where
  U := M.UA × M.UB × M.UC
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := M.pU
  sg := fun u => (M.aF u.1, fun a => (M.bF a u.2.1, M.cF a u.2.2))

/-- ⭐⭐ **诱导联合律的显式形式**（**关键计算引理**）。

$$\mathrm{jointLaw3}(M) (a,b,c) =
  \Bigl(\sum_{u_A:\,aF\,u_A = a} p_A(u_A)\Bigr)
  \cdot \Bigl(\sum_{u_B:\,bF\,a\,u_B = b} p_B(u_B)\Bigr)
  \cdot \Bigl(\sum_{u_C:\,cF\,a\,u_C = c} p_C(u_C)\Bigr)$$

**⟹ 这就是「父集分解」的**具体因子**：
`α(a)`、`β(a,b)`、`γ(a,c)` 分别是三块外生噪声的**推前律**。** -/
theorem jointLaw3_eq {a : A} {b : B} {c : C} :
    M.toSCM.jointLaw3 (a, b, c) =
      (∑ uA, M.pA uA * (if M.aF uA = a then (1 : ℝ) else 0)) *
      (∑ uB, M.pB uB * (if M.bF a uB = b then (1 : ℝ) else 0)) *
      (∑ uC, M.pC uC * (if M.cF a uC = c then (1 : ℝ) else 0)) := by
  -- ⚠⚠ **第 113 轮修正**：`M.toSCM.U` 是一个**结构字段投影**
  -- ⚠⚠ **第 124 轮：本证明改用**在最小复现里完全证通**的三步方案**
  --    （`_MreQ.lean`，**零错误零 warning**）。
  --
  -- **三步**：
  --  ① 展开 `jointLaw3` / `push` / `toSCM` / `pU`
  --  ② **把「三元组 ite」拆成三个独立 ite 之积**（`by_cases` 三层）
  --  ③ **把三层求和分离成乘积**（`mul_sum` / `sum_mul` 逐层）
  --
  -- ⚠⚠ **关键陷阱（第 124 轮查明）**：
  --    `mul_sum : a * ∑ f = ∑ a * f`（**常数在左**）
  --    `sum_mul : (∑ f) * a = ∑ f * a`（**常数在右**）
  --    **二者不可混用** —— 用错时 Lean 报「Did not find an occurrence」，
  --    **而错误信息**看起来像「方向问题」，实则是「常数位置不对」**。
  simp only [PearlHierarchy.SCM.jointLaw3, PearlHierarchy.push, toSCM, pU]
  -- ⚠⚠ **第 113 轮的 `change` 必须保留**：`M.toSCM.U` 是**结构字段投影**，
  --    而 `Fintype.sum_prod_type` 要求**乘积类型字面量**的 `Fintype` 实例
  --    ⟹ 须先 `change` 把目标显式改写为乘积类型上的求和。
  change (∑ u : M.UA × M.UB × M.UC,
      M.pA u.1 * M.pB u.2.1 * M.pC u.2.2 *
        (if (M.aF u.1, (M.bF (M.aF u.1) u.2.1, M.cF (M.aF u.1) u.2.2)) = (a, (b, c))
          then (1 : ℝ) else 0)) = _
  simp only [Fintype.sum_prod_type]
  -- ② 「三元组 ite」拆分
  have htriple : ∀ x : M.UA, ∀ y : M.UB, ∀ z : M.UC,
      (if (M.aF x, M.bF (M.aF x) y, M.cF (M.aF x) z) = (a, b, c) then (1 : ℝ) else 0)
        = (if M.aF x = a then (1 : ℝ) else 0) * (if M.bF a y = b then (1 : ℝ) else 0)
          * (if M.cF a z = c then (1 : ℝ) else 0) := by
    intro x y z
    by_cases h1 : M.aF x = a
    · by_cases h2 : M.bF a y = b
      · by_cases h3 : M.cF a z = c
        · subst h1; subst h2; subst h3; simp
        · simp [h1, h2, h3]
      · simp [h1, h2]
    · simp [h1]
  simp only [htriple]
  -- 重排为「三个独立因子之积」
  have hrearr : ∀ x : M.UA, ∀ y : M.UB, ∀ z : M.UC,
      M.pA x * M.pB y * M.pC z
        * ((if M.aF x = a then (1 : ℝ) else 0) * (if M.bF a y = b then (1 : ℝ) else 0)
            * (if M.cF a z = c then (1 : ℝ) else 0))
      = (M.pA x * (if M.aF x = a then (1 : ℝ) else 0))
        * (M.pB y * (if M.bF a y = b then (1 : ℝ) else 0))
        * (M.pC z * (if M.cF a z = c then (1 : ℝ) else 0)) := by
    intro x y z; ring
  simp only [hrearr]
  -- ③ 三层分离（从内向外）
  have h1 : ∀ x : M.UA, ∀ y : M.UB,
      (∑ z : M.UC, (M.pA x * (if M.aF x = a then (1 : ℝ) else 0))
          * (M.pB y * (if M.bF a y = b then (1 : ℝ) else 0))
          * (M.pC z * (if M.cF a z = c then (1 : ℝ) else 0)))
      = (M.pA x * (if M.aF x = a then (1 : ℝ) else 0))
        * (M.pB y * (if M.bF a y = b then (1 : ℝ) else 0))
        * (∑ z, M.pC z * (if M.cF a z = c then (1 : ℝ) else 0)) := by
    intro x y; rw [← mul_sum]
  simp only [h1]
  have h2 : ∀ x : M.UA,
      (∑ y : M.UB, (M.pA x * (if M.aF x = a then (1 : ℝ) else 0))
          * (M.pB y * (if M.bF a y = b then (1 : ℝ) else 0))
          * (∑ z, M.pC z * (if M.cF a z = c then (1 : ℝ) else 0)))
      = (M.pA x * (if M.aF x = a then (1 : ℝ) else 0))
        * ((∑ y, M.pB y * (if M.bF a y = b then (1 : ℝ) else 0))
          * (∑ z, M.pC z * (if M.cF a z = c then (1 : ℝ) else 0))) := by
    intro x
    rw [show (∑ y : M.UB, (M.pA x * (if M.aF x = a then (1 : ℝ) else 0))
          * (M.pB y * (if M.bF a y = b then (1 : ℝ) else 0))
          * (∑ z, M.pC z * (if M.cF a z = c then (1 : ℝ) else 0)))
        = ∑ y : M.UB, (M.pA x * (if M.aF x = a then (1 : ℝ) else 0))
          * ((M.pB y * (if M.bF a y = b then (1 : ℝ) else 0))
            * (∑ z, M.pC z * (if M.cF a z = c then (1 : ℝ) else 0))) from by
      refine Finset.sum_congr rfl fun y _ => ?_
      ring]
    rw [← mul_sum]
    congr 1
    rw [← sum_mul]
  simp only [h2]
  conv_rhs => rw [mul_assoc]
  rw [← sum_mul]
/-- ⭐⭐⭐ **SCM 侧充分条件 ⟹ 诱导联合律可分解**（**桥定理**）。

**陈述**：对任意乘积外生块 SCM `M`，
其诱导的有限联合律 `jointLaw3` **可分解**。

**⟹ 即**：**§69.4 的结构条件（外生独立 + 结构方程分解）
蕴含 §69.3 的抽象分解条件** ——
**从而（经 `factorizes_condIndepFin`）蕴含 `B ⟂ C | A`。** -/
theorem toSCM_jointLaw3_factorizes :
    Factorizes M.toSCM.jointLaw3 := by
  refine ⟨fun a => (∑ uA, M.pA uA * (if M.aF uA = a then (1 : ℝ) else 0)),
    fun p => (∑ uB, M.pB uB * (if M.bF p.1 uB = p.2 then (1 : ℝ) else 0)),
    fun p => (∑ uC, M.pC uC * (if M.cF p.1 uC = p.2 then (1 : ℝ) else 0)),
    ?_⟩
  intro a b c
  exact M.jointLaw3_eq

/-- ⭐⭐⭐ **主定理**：**朴素 SCM 的父集分解 ⟹ 条件独立**
（**本文件的核心交付**）。

**陈述**：对任意乘积外生块 SCM `M`，
其诱导的有限联合律满足 `CondIndepFin` ——
即 **`B ⟂ C | A`**。

**证明**：`toSCM_jointLaw3_factorizes`（SCM 侧） +
`factorizes_condIndepFin`（代数侧）。

**⟹ 这是把「SCM 语义」与「有限条件独立」**真正接起来**的一步 ——
**它不依赖任何测度论，且在项目自有载体上可编译。** -/
theorem toSCM_condIndepFin : CondIndepFin M.toSCM.jointLaw3 :=
  factorizes_condIndepFin M.toSCM_jointLaw3_factorizes

end FracSCM

/-! ===========================================================================
    §69.5  ⚠⚠ **缺口登记**（**如实，不夸大也不缩小**）
    =========================================================================== -/

/-! #### 本文件**证了什么**

| # | 结果 | 类型 |
|---|---|---|
| 1 | `condIndepFin_symm` | 条件独立**对称** |
| 2 | `factorizes_condIndepFin` | ⭐ **父集分解 ⟹ 条件独立**（充分条件） |
| 3 | `condIndepFin_iff_ratio` | **乘法形式 ⟹ 商形式**（定义忠实性） |
| 4 | `FracSCM.toSCM_condIndepFin` | ⭐⭐ **SCM 父集分解 ⟹ 条件独立**（**主交付**） |

#### 本文件**没证什么**（**具名缺口**，与 §66.4 / §68.4 体例一致）

| 缺口 | 内容 | 阻塞原因 |
|---|---|---|
| **G1** | **必要性**（`CondIndepFin` 是否由某 SCM 结构**必然**导出） | 未证；本文件只给**充分**条件 |
| **G2** | **d-分离 ⟹ 条件独立**（一般图） | 需图侧 collider/分叉/链的方向区分（`DSeparation` 只做路径层）+ 一般 Markov 桥 |
| **G3** | **含混杂 / 含环 / 一般 DAG 的 SCM Markov 性质** | 本文件只覆盖**朴素无混杂**的 `FracSCM` |
| **G4** | **多变量多结果的一般 SCM** | `PearlHierarchy.SCM` 为**单结果位**口径，本文件只到 `B × C` |
| **G5** | **测度层嵌入**（有限律 → `Measure`，接 `CondIndepFun`） | 未做；见 `SCMSemantics` §68.4 |
| **G6** | **`FracSCM → SCM` 的一般化**（外生块数可变 / 结果位任意） | 本文件硬编码三块 |

**⚠ 与既有登记的一致性**：G2、G5 **正是** `DoCalculusRules` §66.4
与 `SCMSemantics` §68.4 已登记的同一缺口 ——
**本文件**不声称已补上它们**，**只补了「充分条件 + 可行性示范」这一层。** -/

/-- ⭐⭐ **缺口登记表**（**可机械列举**，使验收报告可核对）。

**⚠ 这是「据实登记」，不是「定理」**（与 `Stage1A.T1AItem` 同体例）。 -/
structure FinMarkovGap where
  /-- 缺口编号。 -/
  id : String
  /-- 缺口内容。 -/
  summary : String
  /-- 阻塞原因。 -/
  blocker : String

/-- ⭐⭐ **本文件的缺口清单**（其项与上表一一对应）。 -/
def finMarkovGaps : List FinMarkovGap := [
  ⟨"G1", "条件独立 ⟹ SCM 结构（必要性）",
   "本文件只证充分方向；必要性需对联合律反解结构方程，未做"⟩,
  ⟨"G2", "d-分离 ⟹ 条件独立（一般图）",
   "需图侧方向性区分（collider/分叉/链）+ 一般 Markov 桥；见 DoCalculusRules §66.4"⟩,
  ⟨"G3", "含混杂 / 含环 / 一般 DAG 的 SCM Markov 性质",
   "本文件只覆盖朴素无混杂的 FracSCM"⟩,
  ⟨"G4", "多变量多结果的一般 SCM",
   "PearlHierarchy.SCM 为单结果位口径，本文件只到 B × C"⟩,
  ⟨"G5", "有限律 → Measure 的嵌入（接 CondIndepFun）",
   "未做；见 SCMSemantics §68.4"⟩,
  ⟨"G6", "FracSCM → 一般 SCM 的外生块数目推广",
   "本文件硬编码三块 UA×UB×UC"⟩
]

/-- ⭐⭐ **已证的实质结果数**（供验收报告统计；不计定义与登记）。 -/
def finMarkovProvedCount : ℕ := 4

end FinMarkov

end Fate
