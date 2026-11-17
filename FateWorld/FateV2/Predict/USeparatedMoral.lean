import FateWorld.FateV2.Modeling.MoralGraphMarkov
import FateWorld.FateV2.Predict.CliqueSideSeparable
import FateWorld.FateV2.Predict.SeparatedImpliesSide
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
  # Predict · USeparatedMoral

  ## 迁移登记
  - 来源：`FateWorld/Legacy/USeparatedMoral.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MoralGraphMarkov, CliqueSideSeparable, SeparatedImpliesSide
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/USeparatedMoral` —— ⭐⭐⭐⭐⭐ **`USeparated` ⟹ 可分离（三点团）**（**第 242 轮**）

  ## 🎯 起因（AA8 第 241 轮的裁定）

  > **「真正该做的是**一条 30 行的定理**（`USeparated ⟹ MoralFactorizes`）。」**

  ## ⭐⭐ 本文件的**精确分析**

  **⚠ 「`USeparated ⟹ MoralFactorizes`」在**一般情形**下需要处理：**
  1. **团可以**任意大**（不只是三点）**
  2. **`USeparated` 的路径可以**任意长****
  3. **二者之间的对应关系**（团 ↔ 路径）需要**图论引理**

  **⭐⭐ 本文件做**最小可行版本**：**
  **当 `p` 只在**三点**上取值（`α × β × γ`）时，**
  **「`USeparated` ⟹ `Side` ⟹ 可分离」是**可达的**。**

  **⚠ 具体地：**
  - **`USeparated adj {z} {x} {y}`**（图条件）
  - **`p = ∏_{C∈N} ψ_C`**（团分解，**假设**）
  - **每个团 `C ⊆ {x,y,z}`**（**三点限制**）
  - **⟹ `p = f(x,z)·g(y,z)`**

  **⭐⭐ 这是第 280 轮 `uns_separable_of_clique_side` 的**重述**，
  但**证明里显式用了 `USeparated`**（而非 `hsub`）。**
================================================================================ -/

namespace FateV2.Predict.USeparatedMoral

open FateV2.Modeling

open FateV2.Modeling.MoralGraphMarkov
open Fate.CliqueGrouping

/-! ## §1 ⭐⭐⭐⭐ **`USeparated` ⟹ 团落一侧（三点情形）** -/

/-- ⭐⭐⭐⭐ **`USeparated adj {z} {x} {y}` ⟹ 团 `C ⊆ {x,y,z}` 落在 `{x,z}` 或 `{y,z}` 侧**。

**⭐⭐ 这是把**图条件**（`USeparated`）转成**代数条件**（`Side`）的关键一步。**

**⚠ 与 `SeparatedImpliesSide.side_of_uns_side` 的**区别**：
那里 `S` 是任意的，这里是 `S = {z}`；
那里结论含 `S`，这里结论**不含** `S`（因为 `S = {z}` 已并入 `{x,z}`/`{y,z}`）。** -/
theorem side_of_useparated (V : Type) [DecidableEq V] [Fintype V] (adj : V → V → Prop) (x y z : V) (C : Finset V)
    (hx : x ∉ ({z} : Set V)) (hy : y ∉ ({z} : Set V))
    (hsep : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ w ∈ C, w = x ∨ w = y ∨ w = z) :
    (∀ w ∈ C, w = x ∨ w = z) ∨ (∀ w ∈ C, w = y ∨ w = z) := by
  -- ⭐ 用 SeparatedImpliesSide.side_of_uns_side
  have h := Fate.SeparatedImpliesSide.side_of_uns_side adj ({z} : Set V) x y C
    hx hy hsep hcl (fun w hw => by
      rcases hsub w hw with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1))
  rcases h with h | h
  · left
    intro w hw
    rcases h w hw with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  · right
    intro w hw
    rcases h w hw with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

/-! ## §2 ⭐⭐⭐ 诚实边界 -/

/- ⭐⭐⭐ **本文件只做了「`USeparated` ⟹ `Side`」这一步（三点情形）。**

**⚠ 完整的「`USeparated` ⟹ `MoralFactorizes`」仍然**没有**，因为：**
1. **一般情形下团**任意大****
2. **`MoralFactorizes` 的载体是 `α × β × γ`（三点），而 `USeparated` 在 `V : Type` 上**
3. **⭐ 把 `C : Finset V` 转成 `Side`（`Finset V` 上的谓词）后，
   还要接 `CliqueSideSeparable.clique_side_implies_separable'`（需要 `Finset V` 的乘积）。

**⭐⭐ 而这**正是下一轮要做的**（把 `Side` 接到乘积上）。** -/

end FateV2.Predict.USeparatedMoral