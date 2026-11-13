/-
================================================================================
  Fate/Stage2/ErrorBoundE2b.lean
  —— 把 Hoeffding 的「乘积形式」放大成「纯指数」（Stage2 · E2b）

  前置：Fate/Stage2/ErrorBoundE2.lean（§1..§8，已入库，EXIT=0）。

  本文件只做一件事：把
      exp(t·Σxᵢ) ≤ ∏ᵢ (1 + xᵢ(eᵗ−1))          ← §7 hoeffding_prod_bound
  的第二端逐项用 1 + y ≤ e^y 放大，再合并指数，得到**乘积形式消失**的
  纯指数界
      exp(t·Σxᵢ) ≤ exp((eᵗ−1)·Σxᵢ).

  定理清单（5 条，逐条已用 #print axioms 验证无 sorryAx）：
    §1  one_add_le_exp_scaled     : 1 + x(c−1) ≤ exp(x(c−1))     (x ≥ 0, c ≥ 1)
    §2  prod_exp_eq               : ∏ᵢ exp(fᵢ) = exp(Σᵢ fᵢ)       (任意 f)
    §3  prod_one_add_le_exp       : ∏ᵢ (1+gᵢ) ≤ exp(Σᵢ gᵢ)        (gᵢ ≥ 0)
    §4  hoeffding_prod_to_exp     : exp(t·Σxᵢ) ≤ exp((eᵗ−1)·Σxᵢ)  (xᵢ ∈ [0,1])
    §5  hoeffding_linear_le_scaled: t·Σxᵢ ≤ (eᵗ−1)·Σxᵢ            (xᵢ ∈ [0,1])

  全部无 sorry / 无 admit / 无自定义 axiom。
================================================================================
-/
import FateWorld.Legacy.Stage2.ErrorBoundE2
import Mathlib.Tactic

open Finset
open Fate.Stage2.ErrorBoundE2

namespace Fate.Stage2.ErrorBoundE2b

/-! ## §1  单点情形：`1 + x(c-1) ≤ exp(x(c-1))` -/

/-- ⭐⭐ **单点情形**：对 `x ≥ 0`、`c ≥ 1`，

$$1 + x\,(c-1) \;\le\; e^{\,x(c-1)}$$

**证明**：先由 `c ≥ 1` 得 `0 ≤ c - 1`，故 `y := x(c-1) ≥ 0`；
再用前置 §1 的 `one_add_le_exp : 1 + y ≤ exp y`。

⚠ 本文件里由「右侧非负系数」产生的一切放大都归结为这条。 -/
theorem one_add_le_exp_scaled (x c : ℝ) (hx : 0 ≤ x) (hc : 1 ≤ c) :
    1 + x * (c - 1) ≤ Real.exp (x * (c - 1)) := by
  have hc1 : 0 ≤ c - 1 := by linarith
  have _hy : 0 ≤ x * (c - 1) := mul_nonneg hx hc1
  exact one_add_le_exp (x * (c - 1))

/-! ## §2  乘积 ⟹ 指数和 -/

/-- ⭐⭐⭐ **乘积 ⟹ 指数和**：`∏ᵢ exp(fᵢ) = exp(Σᵢ fᵢ)`。

**证明**：`Real.exp_sum` 给出 `exp(Σ_{i∈s} f i) = ∏_{i∈s} exp(f i)`，
取 `s = univ` 后对称。 -/
theorem prod_exp_eq (n : ℕ) (f : Fin n → ℝ) :
    ∏ i : Fin n, Real.exp (f i) = Real.exp (∑ i : Fin n, f i) := by
  have h := Real.exp_sum (Finset.univ : Finset (Fin n)) f
  simpa using h.symm

/-! ## §3  逐项 `1 + gᵢ ≤ exp(gᵢ)` 放大后合并 -/

/-- ⭐⭐⭐ **乘积 ⟹ 纯指数（纯代数内核，无 `[0,1]` 假设）**：

若 `∀ i, 0 ≤ g i`，则

$$\prod_i (1 + g_i) \;\le\; \exp\left(\sum_i g_i\right)$$

**证明**：
1. `Finset.prod_le_prod`：每项非负（`1 + gᵢ ≥ 0`）+ 每项 `1 + gᵢ ≤ exp(gᵢ)`（前置 `one_add_le_exp`）；
2. `prod_exp_eq`（本文件 §2）把 `∏ exp(gᵢ)` 合并成 `exp(Σ gᵢ)`。

**这是整个 E2b 的核心：乘积形式在这里彻底消失。** -/
theorem prod_one_add_le_exp (n : ℕ) (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∏ i : Fin n, (1 + g i) ≤ Real.exp (∑ i : Fin n, g i) := by
  calc ∏ i : Fin n, (1 + g i) ≤ ∏ i : Fin n, Real.exp (g i) := by
        apply Finset.prod_le_prod
        · intro i _
          have := hg i
          linarith
        · intro i _
          exact one_add_le_exp (g i)
    _ = Real.exp (∑ i : Fin n, g i) := prod_exp_eq n g

/-! ## §4  主定理：Hoeffding 乘积 ⟹ 纯指数 -/

/-- ⭐⭐⭐⭐ **Hoeffding 乘积 ⟹ 纯指数**：

若每项 `xᵢ ∈ [0,1]`，则对任意 `t : ℝ`，

$$\exp\left(t\sum_i x_i\right) \;\le\; \exp\left((e^t - 1)\sum_i x_i\right)$$

**证明**（三步链，无 `sorry`）：
1. 前置 `hoeffding_prod_bound`：`exp(t·Σxᵢ) ≤ ∏ᵢ (1 + xᵢ(eᵗ−1))`
   ⚠ 其前提形态是**两条独立的 `∀`**（`∀ i, 0 ≤ x i` 与 `∀ i, x i ≤ 1`），
   必须从 `hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1` 拆开传入；
2. 本文件 `prod_one_add_le_exp`，取 `gᵢ := xᵢ(eᵗ−1) ≥ 0`
   （`xᵢ ≥ 0` 且 `eᵗ − 1 ≥ 0`；后者来自 `t + 1 ≤ eᵗ` 与 `t ≥ 0`）。
   ⚠ `eᵗ − 1 ≥ 0` 对**负** `t` 不成立，所以此处必须用 `1 + t ≤ eᵗ` 配 `t ≥ 0`，
   而不能凭空引用 `Real.one_le_exp`（它要 `0 ≤ t`）。但这里 `t` **确实无符号假设**
   ——见下：该不等式对负 `t` 由「`Σxᵢ` 上界 + `eᵗ−1 < 0`」的符号分析处理；
3. 合并指数：`Σᵢ xᵢ(eᵗ−1) = (eᵗ−1)·Σᵢ xᵢ`（`Finset.sum_mul`）。

**意义**：`exp` 严格单调（`Real.exp_le_exp`），故上式等价于
`t·Σxᵢ ≤ (eᵗ−1)·Σxᵢ`。当 `Σxᵢ > 0` 时即 `t ≤ eᵗ − 1`，
正是 Chernoff/Hoeffding 对 `t` 求最优的前提：左侧指数**线性**、右侧是
**与 `t` 无关的常数因子**，不必再解超越方程。

**⚠ 可证性说明**：`t ≥ 0` 时本式成立（`t ≤ eᵗ − 1` 是 `one_add_le_exp` 重排）。
`t < 0` 时 `eᵗ − 1 < 0`，而 `t > eᵗ − 1`，只要 `Σxᵢ > 0` 不等式即**反向**。
故本文件的 `hoeffding_prod_to_exp` 带 `ht : 0 ≤ t`（`t ≥ 0` 是 Hoeffding/Chernoff
的标准工作区间：mgf 只在 `t ≥ 0` 上取优）。 -/
theorem hoeffding_prod_to_exp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    Real.exp (t * ∑ i, x i) ≤
      Real.exp ((Real.exp t - 1) * ∑ i, x i) := by
  -- 前提拆分：§7 需要两条独立的 ∀
  have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).1
  have hx1 : ∀ i, x i ≤ 1 := fun i => (hx i).2
  -- 步骤 1：§7 的乘积形式
  have h7 : Real.exp (t * ∑ i, x i) ≤ ∏ i : Fin n, (1 + x i * (Real.exp t - 1)) :=
    hoeffding_prod_bound n t x hx0 hx1
  -- 系数 `eᵗ − 1 ≥ 0`：由 `t + 1 ≤ eᵗ` 与 `t ≥ 0`（⚠ `Real.one_le_exp` 需 `0 ≤ t`）
  have het : 0 ≤ Real.exp t - 1 := by
    have h := Real.add_one_le_exp t
    linarith
  -- 步骤 2：`gᵢ := xᵢ(eᵗ−1) ≥ 0`，逐项放大
  have hg : ∀ i : Fin n, 0 ≤ x i * (Real.exp t - 1) :=
    fun i => mul_nonneg (hx0 i) het
  have h8 : ∏ i : Fin n, (1 + x i * (Real.exp t - 1)) ≤
      Real.exp (∑ i : Fin n, x i * (Real.exp t - 1)) :=
    prod_one_add_le_exp n (fun i => x i * (Real.exp t - 1)) hg
  -- 步骤 3：`Σ xᵢ(eᵗ−1) = (eᵗ−1)·Σ xᵢ`
  have hsum : (∑ i : Fin n, x i * (Real.exp t - 1)) =
      (Real.exp t - 1) * ∑ i : Fin n, x i := by
    -- 目标右侧用 `Finset.mul_sum` 展开成 `∑ c·xᵢ`，再逐项用 `mul_comm` 收口
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_comm (x i) (Real.exp t - 1))
  rw [hsum] at h8
  linarith

/-! ## §5  推论：去掉 `exp` 外壳 -/

/-- ⭐⭐⭐ **§4 的等价形式**（`exp` 严格单调，`Real.exp_le_exp`）：

$$t\sum_i x_i \;\le\; (e^t - 1)\sum_i x_i$$

Chernoff 优化里可直接在指数上比较，无需 `log`。 -/
theorem hoeffding_linear_le_scaled (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    t * ∑ i, x i ≤ (Real.exp t - 1) * ∑ i, x i := by
  have h := hoeffding_prod_to_exp n t ht x hx
  exact Real.exp_le_exp.mp h

/-! ## §6  公理审计 -/

#print axioms one_add_le_exp_scaled
#print axioms prod_exp_eq
#print axioms prod_one_add_le_exp
#print axioms hoeffding_prod_to_exp
#print axioms hoeffding_linear_le_scaled

end Fate.Stage2.ErrorBoundE2b
