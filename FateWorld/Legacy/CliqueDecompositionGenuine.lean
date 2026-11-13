import FateWorld.Legacy.SeparationDecomposition
import FateWorld.Legacy.MoralGraphMarkov

/-! ===========================================================================
  `Fate/CliqueDecompositionGenuine` —— **`USeparated` 真正起作用的定理**（**第 272 轮**）

  ## 🔴 问题（第 271 轮 Q1/Q2 的 D7 判定）

  **`SeparationDecomposition.clique_decomposition` 的三个假设都带 `_` 前缀**：
  ```lean
  (_hAS : ...) (_hBS : ...) (_hUS : USeparated adj S A B)
  ```
  **⚠ D7 实验证明：**三个假设全是死前提**（去掉后仍能证）。**

  **⚠ 原因**：`B̃ = V ∖ (Ã∪S)` 是 `Ã∪S` 的**补集**，
  **故**任何集合**自动**落在某一侧或 `S` 里 —— **与分离性无关**。

  ## ✅ 好消息：`clique_meet_A_and_B_not_separated` **是真的**

  **⚠ Q2 的 D7 判定：`hAS`/`hBS` **都必要**（各有反例）。**
  **⚠ 且它的结论**真的**用到 `USeparated`（`→ ¬ USeparated ...`）。**

  ## ⭐ 本文件做什么

  **给出**团分解的**正确**形态**：
  > **「团不能横跨 `A` 与 `B`」** —— **这才需要 `USeparated`。**

  **⚠ 本文件**复用**已有的 `clique_meet_A_and_B_not_separated`，
  **并给出它的**正命题**形式（更易用）。**
================================================================================ -/

namespace Fate.CliqueDecompositionGenuine

open Fate.SeparationDecomposition
open Fate.MoralGraphMarkov

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 ⭐⭐⭐⭐⭐ **团不横跨 `A` 与 `B`**（正命题形式） -/

/-- ⭐⭐⭐⭐⭐ **团不横跨 `A` 与 `B`**（**`USeparated` 真正起作用**）。

**⭐ 陈述**：若 `S` 分离 `A` 和 `B`，`A`、`B` 都不碰 `S`，`C` 是团，
则 `C` 不能同时含 `A` 的点与 `B` 的点。

**⭐⭐ 这是 `clique_meet_A_and_B_not_separated` 的**正命题形式**（更易用）。**

**⚠ D7 验证**（Q2 的实测）：`hAS`、`hBS` **都必要**；
**`hUS` 是本定理的**核心假设**（结论直接消费它）。** -/
theorem clique_not_cross_A_B
    (adj : V → V → Prop) (S A B C : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : USeparated adj S A B)
    (hcl : IsClique adj C) :
    ¬ (∃ u ∈ C, u ∈ A ∧ ∃ v ∈ C, v ∈ B) :=
  fun hex => clique_meet_A_and_B_not_separated adj S A B C hAS hBS hcl hex hUS

/-- ⭐⭐⭐⭐ **推论：团的 `A`-部分与 `B`-部分是分开的**。

**⭐ 陈述**：`C ∩ A ≠ ∅` 且 `C 是团` ⟹ `C ∩ B = ∅`（在 `S` 分离下）。 -/
theorem disjoint_of_clique_meets_A
    (adj : V → V → Prop) (S A B C : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : USeparated adj S A B)
    (hcl : IsClique adj C)
    (hA : (C ∩ A).Nonempty) :
    (C ∩ B).Nonempty → False := by
  rintro ⟨v, hvC, hvB⟩
  obtain ⟨u, huC, huA⟩ := hA
  exact clique_not_cross_A_B adj S A B C hAS hBS hUS hcl ⟨u, huC, huA, v, hvC, hvB⟩

/-! ## §2 ⭐⭐⭐ **诚实边界**

**⚠ 本文件**没有**给出**新的**团分解定理** —— 它只是把已有的
`clique_meet_A_and_B_not_separated` 包装成更易用的正命题形式。**

**⚠ 真正的「团分解」（团在 `Ã∪S` 或 `B̃∪S` 里）**不需要** `USeparated`**
（因为那是补集定义的直接后果）—— 见 `SeparationDecomposition.clique_decomposition`。**

**⭐⭐ 故**：**
> **Oxford 定理 4.1 的「团分组」这一步，**真的不需要** `USeparated`！**
> **⚠ 因为 `Ã`/`B̃` 的构造已经保证分组。**
> **⚠ `USeparated` 真正起的作用是**「`B ⊆ B̃`」与「团不横跨 `A`/`B`」。**

**⚠ 这是本轮的一个重要**发现**：
**之前我以为「团分组需要分离性」是错的。**
**⭐⭐ 正确的图景：**
| 步骤 | 是否需要 `USeparated` |
|---|---|
| `Ã`/`B̃` 的构造 | ❌（补集定义）|
| **`B ⊆ B̃`** | ✅ **需要**（Q1 反例）|
| **团不横跨 `A`/`B`** | ✅ **需要**（Q2 判定）|
| **团在 `Ã∪S` 或 `B̃∪S`** | ❌ **不需要** |
| **`V = Ã∪B̃∪S`** | ❌（补集定义）|

**⭐⭐ 即**：`SeparationDecomposition` 的**真实有效内容**是 2 条**
（`B ⊆ B̃`、团不横跨），**不是 7 条**。**
**⚠ 这与第 269 轮 P1 的判定**完全一致**。** -/

end Fate.CliqueDecompositionGenuine
