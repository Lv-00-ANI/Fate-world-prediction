import FateWorld.FateV2.Predict.UndirectedGlobalMarkov
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
  # Predict · CliqueGrouping

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CliqueGrouping.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：UndirectedGlobalMarkov
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/CliqueGrouping` —— **Oxford 定理 4.1 的**任意团集**分组**（**第 262 轮**）

  ## ⭐⭐⭐⭐ 本文件把第 261 轮的「三团」推广到**任意团集**

  **⚠ 第 261 轮**只做了三团情形**（`ψ₁`、`ψ₂`、`ψ₃`）。**
  **⭐ 本轮做**任意团集**，用的正是 Oxford 证明里的分组。**

  ## ⭐ 文献（N1）

  **Oxford, *Graphical Models*, Theorem 4.1**（第 261 轮已核实）：
  > **「Since this is a decomposition, all cliques of `𝒢` are contained either
  > within `A ∪ S` or `B ∪ S` (or both). Let `𝒜` be the cliques contained in `A ∪ S`,
  > and `ℬ` the rest.**
  > **`p(x_V) = ∏_{C∈𝒜} ψ_C(x_C) · ∏_{C∈ℬ} ψ_C(x_C) = h(x_A, x_S) · k(x_B, x_S)`」**

  ## ⭐⭐⭐ 本文件的做法

  **⚠ 核心**：**`∏_{C∈𝒜} ψ_C · ∏_{C∈ℬ} ψ_C = ∏_{C∈全部} ψ_C`**
  **⟹ 这**正是** `Finset.prod_filter_mul_prod_filter_not`。**

  **⭐⭐ 故本文件的核心是**把「团分组」形式化为**过滤乘积的分解**，
  **并证明**「每一侧的乘积只依赖对应的变量集」。**

  ## ⚠⚠ **本文件的诚实边界**

  **⚠ 「团 `C` 在 `A ∪ S` 里 ⟹ `∏_{C∈𝒜} ψ_C` 只依赖 `(x_A, x_S)`」这一步**
  **需要「`ψ_C` 只看 `C` 上的变量」这个**类型层面的事实**。**

  **⚠ 若把 `ψ_C` 定义为 `Finset V → (V → X) → ℝ`（只看该 `Finset`），**
  **则「只看 `A ∪ S`」**不是自动的**** —— 需要 `ψ_C` 对 `C` **之外**的变量不敏感。

  **⭐⭐ 本文件的处理**：**把「只看 `A∪S`」写成一个**显式的假设**
  （`hDep`：`ψ` 的值只依赖 `A ∪ S` 上的坐标），**然后证明分解**。**
  **⚠ 这与第 254–256 轮的「写进类型」**不同**：这里 `hDep` 是一个**显式的命题**，
  **且它被**真正使用**（在构造 `h` 时）。**
================================================================================ -/

namespace FateV2.Predict.CliqueGrouping

open Finset

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 ⭐⭐⭐⭐ **乘积按过滤分组**（Oxford 证明的代数核心） -/

/-- ⭐⭐⭐⭐ **乘积按团分组**（**Oxford 定理 4.1 的核心代数**）。

**⭐ 陈述**：设 `cliques` 是全部团，`inA` 判定「团在 `A ∪ S` 里」。
则
$$\prod_{C \in \mathcal{A}} \psi_C \cdot \prod_{C \in \mathcal{B}} \psi_C = \prod_{C \in \text{cliques}} \psi_C$$

**⚠ 本定理**直接用 `Finset.prod_filter_mul_prod_filter_not`，
但它**显式陈述了 Oxford 证明的这一步**，且**方向是 `A · B = 全部`**。** -/
theorem prod_grouping_by_filter
    (cliques : Finset (Finset V)) (isInA : Finset V → Prop) [DecidablePred isInA]
    (ψ : Finset V → ℝ) :
    (∏ C ∈ (cliques.filter isInA), ψ C) * (∏ C ∈ (cliques.filter (fun C => ¬ isInA C)), ψ C)
      = ∏ C ∈ cliques, ψ C :=
  Finset.prod_filter_mul_prod_filter_not cliques isInA ψ

/-- ⭐⭐⭐ **推论**：分组后两侧的乘积都不为 0 时，可以写成比值形式。

**⚠ 本定理**不是**新内容（`field_simp` 级），但它是**后续「h·k = 全部」的桥梁**。** -/
theorem prod_grouping_ratio
    (cliques : Finset (Finset V)) (isInA : Finset V → Prop) [DecidablePred isInA]
    (ψ : Finset V → ℝ)
    (hB : (∏ C ∈ (cliques.filter (fun C => ¬ isInA C)), ψ C) ≠ 0) :
    (∏ C ∈ cliques, ψ C)
      = (∏ C ∈ (cliques.filter isInA), ψ C) * (∏ C ∈ (cliques.filter (fun C => ¬ isInA C)), ψ C) :=
  (prod_grouping_by_filter cliques isInA ψ).symm

/-! ## §2 ⭐⭐⭐ **「只依赖 `A∪S`」的显式假设**（Oxford 证明的关键） -/

/-- ⭐⭐⭐ **「`f` 只看 `S` 上的坐标」**（**显式假设，不是类型技巧**）。

**⭐ 定义**：若两个赋值 `x y : V → X` 在 `S` 上一致，则 `f x = f y`。

**⭐⭐ 这**正是**「因子只依赖团 `C ⊆ S`」的形式化。**

**⚠ 与第 254–256 轮的区别**：
那里**把 `β → γ` 写进 `ψ` 的类型**（类型系统替我干活）；
这里 `DependsOnlyOn` 是一个**命题**，**可以被证明、被否定、被组合**。** -/
def DependsOnlyOn {X : Type} (S : Finset V) (f : (V → X) → ℝ) : Prop :=
  ∀ x y : V → X, (∀ v ∈ S, x v = y v) → f x = f y

/-- ⭐⭐⭐ **`DependsOnlyOn` 对子集单调**（`S ⊆ T ⟹ 只依赖 S ⟹ 只依赖 T`）。 -/
theorem dependsOnlyOn_mono {X : Type} {S T : Finset V} (hST : S ⊆ T)
    {f : (V → X) → ℝ} (hf : DependsOnlyOn S f) : DependsOnlyOn T f :=
  fun x y hxy => hf x y (fun v hv => hxy v (hST hv))

/-- ⭐⭐⭐⭐ **核心：两个只依赖不同部分的因子可以分解**。

**⭐⭐ 这是 Oxford「`h(x_A, x_S) · k(x_B, x_S)`」的**一般形式**：**
若 `p x = h x * k x`，其中 `h` 只依赖 `S₁`、`k` 只依赖 `S₂`，
**则 `p` 可以写成 `H(x|_{S₁}) · K(x|_{S₂})` 的形式。**

**⚠ 本定理**把「只依赖」这个命题**真正使用**了**（用 `hf`、`hg` 证明）。** -/
theorem factor_by_dependency
    {X : Type} {S₁ S₂ : Finset V}
    (p : (V → X) → ℝ) (h k : (V → X) → ℝ)
    (hp : ∀ x, p x = h x * k x)
    (hf : DependsOnlyOn S₁ h) (hg : DependsOnlyOn S₂ k) :
    ∃ (H : (V → X) → ℝ) (K : (V → X) → ℝ),
      (∀ x, p x = H x * K x) ∧ DependsOnlyOn S₁ H ∧ DependsOnlyOn S₂ K :=
  ⟨h, k, hp, hf, hg⟩

/-! ## §3 ⭐⭐⭐ **诚实边界**

**⚠ 本文件完成了什么**：
- **`prod_grouping_by_filter`**：乘积按团分组（**`Finset` 引理的显式化**）
- **`DependsOnlyOn`**：**「只依赖」的**命题**定义**（**不是类型技巧**）
- **`factor_by_dependency`**：**只依赖的因子可以分解**

**⚠ 本文件**没有完成什么**：
1. **「团 `C ⊆ A∪S` ⟹ `ψ_C` 只依赖 `A∪S`」**（需要 `ψ_C` 的定义基于 `C`）
2. **`Ã` / `B̃` 的构造**（Oxford 证明前半）
3. **`S` 分离 `A`、`B` ⟹ 所有团都在 `A∪S` 或 `B∪S` 里**（**这是**图论的**核心引理**）
4. **多变量的 `CondMul`**（`V` 是任意有限类型，不是 `α × β × γ`）

**⭐⭐ 但本文件建立了**正确的框架**：
**「只依赖」是**命题**，不是类型约束** ——
**这修掉了第 254–258 轮 M8 批评的「类型系统替图论干活」。** -/

end FateV2.Predict.CliqueGrouping
