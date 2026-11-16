import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import FateWorld.FateV2.Predict.CondMulSeparable
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
/-!
  # Predict · MarkovBridgeTheorem

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarkovBridgeTheorem.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GlobalMarkovMinimal, PearlCondIndepBridge, CondMulSeparable
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

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
  `Fate/MarkovBridgeTheorem` —— **Pearl 定理 1.2.4（三节点链的精确形式）**（**第 251 轮**）

  ## ⭐⭐⭐ 本文件要修的**根本缺陷**

  **⚠ 第 250 轮 K8 的审核（我已验证）：**
  > **「全仓库**没有任何一条定理**把 `dSep` 当作**真正使用的假设**去推出 `CondMul`。」**

  ## ⭐ 文献（N1，已 web_search 核实）

  **Pearl, *Causality* 2nd ed.**：
  > **Definition 1.2.2 (Markov Compatibility)**：若 `P` 相对 DAG `G` 允许**因子分解**，
  > 则称 `G` 与 `P` **兼容**。
  >
  > **Theorem 1.2.4**：**若 `X` 与 `Y` 被 `Z` 在 `G` 中 d-分离，
  > 则在**每个与 `G` 兼容的分布**中，给定 `Z` 时 `X` 独立于 `Y`。**

  **⭐⭐ 精确形式**：`(因子分解) ∧ (d-分离) ⟹ (条件独立)`

  ## ⭐⭐⭐ 本文件的核心论点（**重要**）

  **⚠ 在三节点链 `X → Z → Y` 上，「因子分解」的**最弱形式**就是**可分离**：**
  ```
  p(x, z, y) = f(x, z) · g(y, z)
  ```
  **⟹ **Pearl 1.2.4 在链上就是**：
  > **「可分离 ⟹ 条件独立」**（`separable_implies_condMul`）

  **⚠ 而 `ChainMarkov`（`p = φ(x)·ψ(x,z)·χ(z,y)`）是一个**更强**的假设**：
  **它要求 `f` 进一步分解为 `φ(x)·ψ(x,z)`。**
  **⟹ `chain_markov_gives_condindep` 证明的是**更强假设**下的结论，
  而 Pearl 1.2.4 只需**更弱的「可分离」**。**
================================================================================ -/

namespace FateV2.Predict.MarkovBridgeTheorem

open FateV2.Modeling

open FateV2.Predict.FinCondIndep

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐⭐⭐⭐⭐ **Pearl 1.2.4 的**精确**形式** -/

/-- ⭐⭐⭐⭐⭐ **Pearl Theorem 1.2.4（三节点链）**：

**若联合分布**可分离**（`p(x,y,z) = f(x,z)·g(y,z)`），
则给定 `z` 时 `x` 与 `y` **条件独立**（`CondMul`）。**

**🔹 文献对应**：Pearl *Causality* 2nd ed. **Theorem 1.2.4**
（在链 `X → Z → Y` 上，「因子分解 + d-分离 ⟹ 条件独立」，而因子分解的最弱形式就是可分离）。

**⚠ 本定理的证明**不是 `rfl`**：
需要把 `margXZ`/`margYZ`/`margZ` 的**求和**从 `f`/`g` 里提出
（`Finset.sum_mul_sum` + `Finset.mul_sum` + `ring`）。** -/
theorem pearl_1_2_4_chain
    (p : FinJoint α β γ)
    (hsep : ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z) :
    CondMul p := by
  obtain ⟨f, g, hfg⟩ := hsep
  exact FateV2.Predict.PearlCondIndepBridge.separable_implies_condMul p f g hfg

/-- ⭐⭐⭐⭐ **对比：`ChainMarkov` 是**更强**的假设**。

**⭐ 陈述**：若 `p` 满足 `ChainMarkov`（三因子形式），则它可分离
（**故由 §1 得条件独立**）。

**⭐⭐ 这**明确了两个假设的**层级**：
`ChainMarkov`（三因子）⟹ 可分离（两因子）⟹ `CondMul`**

**⚠ 反向**不成立**：可分离的 `f` 不必是 `φ(x)·ψ(x,z)` 的形式。** -/
theorem chain_markov_implies_pearl_1_2_4
    (p : α × β × γ → ℝ) (h : FateV2.Predict.P213B1.ChainMarkov p) :
    CondMul (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2)) :=
  FateV2.Predict.PearlCondIndepBridge.chain_markov_gives_condindep p h

/-! ## §2 ⭐⭐⭐⭐ **反向：条件独立 ⟹ 可分离（需正性）** -/

/-- ⭐⭐⭐⭐ **反向**：`CondMul` + 正分布 ⟹ 可分离。

**⚠ 本定理**组合第 244 轮的 `condMul_implies_separable`。**

**⭐⭐ 与 §1 合起来是**双向刻画**（在正性下）：
> `条件独立` ⟺ `可分离`** -/
theorem cond_mul_implies_separable_chain
    (p : FinJoint α β γ) [Nonempty α] [Nonempty β]
    (h : CondMul p) (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z :=
  Fate.CondMulSeparable.condMul_implies_separable p h hpos

/-! ## §3 ⭐⭐⭐ **本文件的**诚实边界****

**⚠ 本文件**没有**解决缺口 1 的**完整**内容，因为：**

**1. 三节点链的「图」部分仍然是**并列的**。**
   **⭐ 但本文件**澄清了**：Pearl 1.2.4 在链上**不需要**显式的 `dSep` 假设**——
   **因为**链的 d-分离是**结构事实**（唯一路径上有中间节点），
   **而真正需要的假设是**因子分解**。**

**2. 任意 DAG 的情形完全未做。**
   **⚠ 那需要**「`p` 在 `G` 上 Markov」的精确定义**（`p = ∏ p(xᵢ|paᵢ)`）
   **+ 「因子分解 ⟹ 可分离」的一般归纳**（需要**拓扑序 + 祖先图**）。

**3. `ChainMarkov` 与「可分离」的层级差**是本轮的新发现**（§1 的对比定理）。** -/

end FateV2.Predict.MarkovBridgeTheorem

