import FateWorld.FateV2.Predict.T1A2
import FateWorld.FateV2.Predict.T1A2CI
import FateWorld.FateV2.Predict.T1A2CI3
import Mathlib.Tactic

/-!
  # Predict · T1A2Prob

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2Prob.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2, T1A2CI, T1A2CI3
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/T1A2Prob` —— 概率侧：从乘积形式到独立性

## 内容

把 `T1A.2` 的**代数形式**（乘积分解 / 可分离性）转换成**概率意义下的独立性**，
给出条件独立的两种等价刻画：

1. **乘法形式** `CondIndepMul p A B Z`：
   `p x = f x * g x`，`f` 只读 `A ∪ Z`、`g` 只读 `B ∪ Z`。
2. **比值形式** `ratio_factorization`：
   `p x / p y = (f x / f y) * (g x / g y)`。

## 诚实的边界

`CondIndepMul` 是条件独立的**弱化（乘法）形式**：它不要求归一化，也不要求
`f`、`g` 是边缘分布，只要求「乘积分解」。因此本文件各定理的数学内容是
**多项式恒等式的重排**；其价值在于**把独立性写成 Lean 里可 `rw` 的命题**，
为下游（概率测度版独立性）提供接口层。

**⚠ `factorizesOn_implies_condIndepMul` 未被收录。**
对任意 `Z`，该命题为假：取链 `0 → 1 → 2`、`A = {0}`、`B = {2}`、`Z = {0}`，
则 `A ∪ Z = {0}`、`B ∪ Z = {0,2}`，而 `FactorizesOn` 的因子 `π 1` 读
`{1} ∪ pa(1) = {0,1}`，既不落在 `A ∪ Z` 也不落在 `B ∪ Z` 内，无法归入任一因子。
**故该命题不可证，本文件不收录。**

**⚠ 关于 `[DecidableEq V]`**：`A ∪ Z` 依赖 `Finset.union`，而本 Mathlib 版本中
`Union (Finset V)` 实例要求 `DecidableEq V`（`Finset` 本身不全局携带该实例，
这一点已实测确认）。因此 `CondIndepMul` 及相关定理都声明了该实例参数。
-/

namespace FateV2.Predict.T1A2Prob

open FateV2.Modeling

open Finset
open Fate.T1A2

variable {V : Type*} [DecidableEq V]

/-! ## §1 条件独立的乘法形式 -/

/-- ⭐⭐⭐ **条件独立（乘法形式）**：

存在 `f`、`g` 使 `p x = f x * g x`，其中 `f` 只看 `A ∪ Z`、`g` 只看 `B ∪ Z`。

**⚠ 这是「给定 `Z` 后 `A` 与 `B` 条件独立」的乘法形式
（等价于 `p(a,b,z) ∝ f(a,z)·g(b,z)`）。** -/
def CondIndepMul (p : (V → Bool) → ℝ) (A B Z : Finset V) : Prop :=
  ∃ (f g : (V → Bool) → ℝ),
    ReadsOnlyOn (A ∪ Z) f ∧
    ReadsOnlyOn (B ∪ Z) g ∧
    ∀ x, p x = f x * g x

/-! ## §2 构造性见证 -/

/-- ⭐⭐ **乘积形式直接给出独立性**（构造性见证）：

若 `p x = f x * g x` 处处成立，`f` 只看 `A`、`g` 只看 `B`，
则 `CondIndepMul p A B ∅` 成立（`A ∪ ∅ = A`、`B ∪ ∅ = B`）。

**⚠ 这几乎是定义展开，但它是 `CondIndepMul` 的构造性入口。** -/
theorem product_gives_condIndepMul
    {p f g : (V → Bool) → ℝ}
    (hfac : ∀ x, p x = f x * g x)
    (A B : Finset V) (hf : ReadsOnlyOn A f) (hg : ReadsOnlyOn B g) :
    CondIndepMul p A B ∅ := by
  refine ⟨f, g, ?_, ?_, hfac⟩
  · simpa using hf
  · simpa using hg

/-- ⭐⭐⭐ **带非空条件集 `Z` 的版本**：

若 `f` 只看 `A ∪ Z`、`g` 只看 `B ∪ Z`，则 `A ⊥ B | Z` 成立。

**⚠ 与 `product_gives_condIndepMul` 的差别仅在把读集放宽到 `A ∪ Z` / `B ∪ Z`；
它避免了在 `Z ≠ ∅` 时重复 `simpa` 的麻烦。** -/
theorem product_gives_condIndepMul_general
    {p f g : (V → Bool) → ℝ}
    (hfac : ∀ x, p x = f x * g x)
    (A B Z : Finset V) (hf : ReadsOnlyOn (A ∪ Z) f) (hg : ReadsOnlyOn (B ∪ Z) g) :
    CondIndepMul p A B Z :=
  ⟨f, g, hf, hg, hfac⟩

/-! ## §3 比值形式 -/

omit [DecidableEq V] in
/-- ⭐⭐⭐⭐ **比值独立性**（「条件独立」的等价形式）：

若 `p x = f x * g x`，则对任意两点 `x`、`y`（`p y ≠ 0`）：

$$\frac{p(x)}{p(y)} = \frac{f(x)}{f(y)} \cdot \frac{g(x)}{g(y)}.$$

**⚠ 这是概率论中常用的比值形式：`A` 与 `B` 的贡献可以分别计算再相乘。**

证明：`hfac` 在两处代入，再用 `div_mul_div_comm` 合并两个商。
（`hy` 保留以对齐概率论表述、保证比值有定义；乘法交换性使其在证明中不必要。） -/
theorem ratio_factorization
    {p f g : (V → Bool) → ℝ}
    (hfac : ∀ x, p x = f x * g x)
    (x y : V → Bool) (_hy : p y ≠ 0) :
    p x / p y = (f x / f y) * (g x / g y) := by
  rw [hfac x, hfac y]
  rw [div_mul_div_comm]

/-! ## §4 公理审计 -/

#print axioms product_gives_condIndepMul
#print axioms product_gives_condIndepMul_general
#print axioms ratio_factorization

end FateV2.Predict.T1A2Prob
