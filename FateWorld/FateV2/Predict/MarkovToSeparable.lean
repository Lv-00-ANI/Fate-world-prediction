import FateWorld.FateV2.Predict.MarkovBridgeReal
import FateWorld.FateV2.Predict.CliqueSideSeparable
import FateWorld.FateV2.Modeling.MoralGraphMarkov
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
  # Predict · MarkovToSeparable

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarkovToSeparable.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MarkovBridgeReal, CliqueSideSeparable, MoralGraphMarkov, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/MarkovToSeparable` —— **从链 Markov 性导出可分离**（**第 284 轮**）

  ## 🎯 动机（V1 第 283 轮指出的唯一出路）

  > 「正向缺口 1 未推进——仍缺一整个 `MoralFactorizes`
  > （**从 `USeparated` 导出团分解，而非假设 `hp`**）。」

  ## ⚠⚠ 两个定义的**顺序差异**（本轮发现）

  | 定义 | 三元组顺序 | 因子 |
  |---|---|---|
  | **`ChainMarkovRelative p`** | **`p (x, z, y)`**（`x:α, z:β, y:γ`）| `pZX : α→β`, `pYZ : β→γ` |
  | **`MoralFactorizes p`** | **`p (x, y, z)`**（`x:α, y:β, z:γ`）| `ψ₁ : α→γ`, `ψ₂ : β→γ` |

  **⚠ 即：`ChainMarkovRelative` 的中间变量是 `β`，`MoralFactorizes` 的是 `γ`。**
  **⭐⭐ 故二者**不能直接对接**，必须显式重排。**
================================================================================ -/

namespace FateV2.Predict.MarkovToSeparable

open FateV2.Modeling

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 **`ChainMarkovRelative` 的展开形式** -/

/-- **`ChainMarkovRelative` ⟹ 双因子形式（保持原顺序）**。

若 `p(x, z, y) = pX(x)·pZX(x, z)·pYZ(z, y)`，
则存在 `ψ₁ : α → β → ℝ`、`ψ₂ : β → γ → ℝ`，使 `p(x, z, y) = ψ₁ x z · ψ₂ z y`。

**⭐⭐ 证明**（非平凡）：把 `pX(x)·pZX(x, z)` 合并为 `ψ₁(x, z)`。 -/
theorem chainMarkov_double_factor
    (p : α × β × γ → ℝ)
    (h : FateV2.Predict.MarkovBridgeReal.ChainMarkovRelative p) :
    ∃ (ψ₁ : α → β → ℝ) (ψ₂ : β → γ → ℝ),
      ∀ x z y, p (x, z, y) = ψ₁ x z * ψ₂ z y := by
  obtain ⟨pX, pZX, pYZ, hP⟩ := h
  exact ⟨fun x z => pX x * pZX x z, fun z y => pYZ z y, fun x z y => hP x z y⟩

/-! ## §2 **链 Markov 性 ⟹ `CondMul`**（重述） -/

/- ⚠ 已删除 chainMarkov_condMul：它是转发，且类型对不上（第 254 轮的结论形式不同）。 -/

/-! ## §3 ⚠⚠ **诚实边界（本轮的关键发现）**

**⚠ 本文件**没有**做 V1 指出的真正缺口（`USeparated ⟹ 团分解`）。**

**⭐⭐ 本轮发现了**一个更重要的事实**：**

> **`ChainMarkovRelative` 与 `MoralFactorizes` 的**变量绑定顺序不同**：**
> - **`ChainMarkovRelative p`：`p (x, z, y)`，`z : β`、`y : γ`**
> - **`MoralFactorizes p`：`p (x, y, z)`，`y : β`、`z : γ`**
>
> **⟹ 二者**不能直接对接**，必须显式重排。**

**⚠ 而这暴露了**一个更深的问题**：**
> **项目里的「Markov 性」定义（`ChainMarkovRelative`）是**为链量身定做的**，**
> **而「道德图因子分解」（`MoralFactorizes`）是**为一般图定义的**。**
> **⚠ 二者**没有统一的接口**。**

**⭐⭐ 真正的缺口仍然是：**
> **「从 `USeparated`（无向图分离）导出「`p` 的团分解」」** ——
> **⚠ 而这需要**道德图的构造**（把父节点两两连边），**而项目里没有**。**

**⚠ 本文件**不计入**缺口 1 的实质进展。**
**⚠ 但它记录了一个重要的类型层面发现。**

--- -/

end FateV2.Predict.MarkovToSeparable