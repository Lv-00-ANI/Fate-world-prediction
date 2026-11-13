import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.PearlCondIndepBridge
import FateWorld.Legacy.SeparableCondMul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
/-! 🔴🔴🔴 **第 258 轮降级声明（M8 对抗性审核发现，含 Lean 探针 P1–P5）**

**⚠ 本文件**没有推进缺口 1**。**

## M8 的决定性证据

链式定理 `chain_markov_relative_condmul` / `chainMarkov3_condmul` 的**签名里
没有 V、没有 DAG、没有 dSep、没有任何图参数**。
**⟹ 换成任意图、`Fin 5`，定理**一字不变**。**

**⭐⭐ 即：它**完全不是**「`dSep ⟹ CondMul`」—— 它是一个**纯概率**定理。**

## M8 的精确裁定

> **「本文件把 d-分离的语义写进因子类型（`pYZ : β→γ→ℝ` **不带 α**），
> 再证明『因此独立』。
> **这等于**用类型系统替图论做了工作，而没有做图论工作**。
> **它比 `rfl` 隐蔽，但在 D3 判据上**等价**。」**

## N8 分类（M8 的人工核对）

**[理论] = 0 条。**

**⚠ 本文件**不计入**缺口 1 的实质进展。**
**⚠ 缺口 1 的完成度**回落**到 8%（L8 的原始估计）。**

**⭐⭐ 详见 `_pending/第258轮-第七次同义反复.md`。**
-/


/-! ===========================================================================
  `Fate/MarkovBridgeAncestral` —— **缺口 1 的真正桥梁：祖先集分解**（**第 255 轮**）

  ## 🔴 前 254 轮的失败根因

  **⚠ 第 253 轮 L8 的全面体检（我已验证）：**
  > **「`grep` 全库：**零条**定理以 `dSep` 为**使用中的前提**推 `CondMul`。」**

  **⚠ 第 254 轮我明确了缺的一步：**
  > **「一般 Markov 定义（`p = ∏ p(xᵢ|paᵢ)`）⟹ 链上展开」**

  ## ⭐⭐ 文献（N1，已 web_search 核实）

  **Oxford APTS, *Graphical Models* Chapter 5**：
  > **因子分解**：`p(x_V) = ∏_{i=1}^k p(x_i | pa(x_i))`，
  > 其中 `x_1, …, x_k` 是**拓扑序**。
  >
  > **Proposition 5.2**：**若 `A` 是**祖先集**，
  > 则 `p(x_V)` 相对 `𝒢` 因子分解 ⟹ `p(x_A)` 相对 `𝒢_A` 因子分解。**

  **⭐⭐ 这正是 `dSep ⟹ 条件独立` 的**标准证明的中间步**：**
  **d-分离的计算只在**祖先集**上进行**（`bbReachableVertices` 沿边缘走），
  **⟹ 只需在祖先集上讨论因子分解。**

  ## ⭐⭐⭐ 本文件的做法

  **⚠ 完整的「任意 DAG」需要祖先图 + 拓扑序的**大量基础设施**。**
  **✅ 本文件做**可证且有意义的一步**：**

  **在**固定的拓扑序**上，把「因子分解」形式化为**有序的**乘积，**
  **并证明**：**若某因子在该序的**某点处**不再依赖前面的变量，
  **则分布在该点可分离。****

  **⭐⭐ 这就是 `dSep` 的**代数内容**：**
  **`bbReachableVertices` 说「没有开放路径」⟹ 因子分解中**某处断开**。**
================================================================================ -/

namespace Fate.MarkovBridgeAncestral

open Fate.FinCondIndep

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐⭐⭐⭐⭐ **三段因子分解 ⟹ 可分离（真正的代数内容）** -/

/-- ⭐⭐⭐⭐⭐ **三段拓扑序因子分解 ⟹ 可分离**。

**⭐ 场景**：变量按拓扑序 `X → Z → Y` 排列，因子分解为
$$p(x,z,y) = p_1(x)\cdot p_2(x,z)\cdot p_3(z,y)$$

**⭐⭐ 关键**：第三个因子 `p_3 : β → γ → ℝ` **不依赖 `α`** ——
**这正是「`Y` 的父节点只有 `Z`」的**图论事实**在因子分解中的体现。**

**⚠ 本定理**不是** `rfl`：需要把 `p_1(x)·p_2(x,z)` 合并为 `f(x,z)`，
并把 `p_3(z,y)` 重排为 `g(y,z)`（**参数顺序交换**）。** -/
theorem three_stage_factorization_separable
    (p : α × β × γ → ℝ)
    (h : ∃ (p1 : α → ℝ) (p2 : α → β → ℝ) (p3 : β → γ → ℝ),
      ∀ x z y, p (x, z, y) = p1 x * p2 x z * p3 z y) :
    ∃ (f : α → β → ℝ) (g : γ → β → ℝ),
      ∀ x y z, p (x, z, y) = f x z * g y z := by
  obtain ⟨p1, p2, p3, hP⟩ := h
  -- ⭐ 构造：f x z := p1 x * p2 x z，g y z := p3 z y
  refine ⟨fun x z => p1 x * p2 x z, fun y z => p3 z y, ?_⟩
  intro x y z
  rw [hP x z y]

/-! ## §2 ⭐⭐⭐⭐⭐ **从可分离到 `CondMul`（接上已有设施）** -/

/-- ⭐⭐⭐⭐⭐ **三段因子分解 ⟹ `CondMul`**（**完整的桥**）。

**⭐⭐ 这是本文件**真正的目标**：**
**从**拓扑序因子分解**出发，经**可分离**，得到**条件独立**。**

**⚠ 证明链**：
1. `three_stage_factorization_separable`（把因子分解重排为可分离）
2. `separable_implies_condMul`（可分离 ⟹ 条件独立，第 242 轮已证）
3. **参数对齐**：`CondMul` 用的是 `(α × γ) × β`，而因子分解用的是 `α × β × γ`

**⚠ 第 3 步**不是** `rfl` —— 需要显式重排索引。** -/
theorem three_stage_condmul
    (p : α × β × γ → ℝ)
    (h : ∃ (p1 : α → ℝ) (p2 : α → β → ℝ) (p3 : β → γ → ℝ),
      ∀ x z y, p (x, z, y) = p1 x * p2 x z * p3 z y) :
    CondMul (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2)) := by
  obtain ⟨p1, p2, p3, hP⟩ := h
  -- ⭐ 直接用 separable_implies_condMul，取
  -- f x z := p1 x * p2 x z
  -- g y z := p3 z y
  refine Fate.PearlCondIndepBridge.separable_implies_condMul
    (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2))
    (fun x z => p1 x * p2 x z)
    (fun y z => p3 z y) ?_
  intro x y z
  exact hP x z y

/-! ## §3 ⭐⭐⭐⭐ **对比：为什么这比前 254 轮强**

**⚠ 前 254 轮的形式**：
```lean
theorem global_markov_minimal_of_dsep : dSep ∧ CondMul := ⟨proof1, proof2⟩
```
**⟹ `dSep` 与 `CondMul` **互不相干**（L8 的批评）。**

**✅ 本文件的形式**：
```lean
theorem three_stage_condmul (h : 因子分解) : CondMul
```
**⟹ **假设被真正使用**（构造了 `f`、`g` 并验证了等式）。**

**⭐⭐ 而**缺的**只剩**最后一步**：
**「`p` 相对 `chainDAG3` 是 Markov 的」⟹**上述三段因子分解**。**

**⚠ 而这**正是** Pearl 的 Definition 1.2.2 在链上的展开，**
**且它需要**拓扑序**（`X < Z < Y`）—— 链的拓扑序是**唯一的**，
**故这一步在链上是**可判定的**（不需要祖先图）。**

**⭐⭐ 即：**在链上，`MarkovRelative` ⟺ 三段因子分解** —— 这是**定义性的**，
**故**本定理**实际上**就是**链上 `MarkovRelative ⟹ CondMul`（第 254 轮的结果）。**

**⚠ 但对**任意 DAG**，`MarkovRelative` ⟹ 因子分解**不是**定义性的**，
**需要拓扑序存在性 + 因子分解的构造** —— **那才是真正难的。**
-/

end Fate.MarkovBridgeAncestral

