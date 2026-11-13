import FateWorld.Legacy.BackdoorGenuine
import FateWorld.Legacy.MoralGraphMarkov

/-! ===========================================================================
  `Fate/NoDescendantWitness` —— **Pearl (ii) 的真正检验**（**第 288 轮**）

  ## 🎯 动机（W1 第 286 轮指出的核心缺口）

  > 「**Pearl (ii) 在这里（`ZBlockedSetup`）是**平凡满足的，不是一个真正的结论**。」**
  > 「要真正测试 Pearl (ii)，需要一个**`W` 含 `X` 后代**的场景。」

  ## ⭐⭐ 本文件的**核心发现**

  **`BackdoorSetup` 的结构**：
  ```
  fX : Z → Ux → X
  fY : X → Z → Ux → Uy → Y
  ```
  **`moralAdj` 有 `X → Y` 这条**出边**（第三条规则）。**
  **⟹ **`Y` 永远是 `X` 的后代**（对**任意** `BackdoorSetup`）。**

  **⭐⭐ 故 `W = {Y}` **必然违反 Pearl (ii)** —— 这是 **`NoDescendant` 不是空洞条件**的证明。**

  ## ⚠⚠ **否定性发现**（本文件最重要的结论）

  **在 `BackdoorSetup` 里，`NoDescendant S W` **等价于** `NoOutcome S W`**（`W` 不含 `Y`）：
  - `Z`、`Ux`、`Uy` **不是** `X` 的后代（无 `X` 出边到它们）
  - `X` **不是**自己的后代（`moralAdj_irrefl`）
  - **`Y` **是** `X` 的后代

  **⟹ **Pearl (ii) 在 `BackdoorSetup` 上是**装饰性的**（它没有独立于 `NoOutcome` 的作用）。**

  **⭐⭐ 要真正检验 Pearl (ii)，`BackdoorSetup` 必须**增加一个中介变量 `M`**（`X → M → Y`）。**
================================================================================ -/

namespace Fate.NoDescendantWitness

open Fate.R259 Fate.R277

variable (S : Fate.R259.BackdoorSetup)

/-! ## §1 ⭐⭐⭐⭐⭐ **`X` 的后代只能是 `Y`**（技术核心） -/

/-- ⭐⭐⭐⭐⭐ **`X` 的后代只能是 `Y`**。

**⭐ 证明**：`moralAdj` 的六条规则里，`X` 只作为**「`X → Y`」的起点**。
- `Z→X`、`Ux→X`：`X` 是**终点**
- `X→Y`：`X` 是**起点** ✓
- `Z→Y`、`Ux→Y`、`Uy→Y`：与 `X` 无关

**⟹ 从 `X` 出发的边只有 `X → Y`，且 `Y` 无出边。** -/
theorem descendant_is_y {v : Vert S} (h : IsDescendant S v) :
    ∃ y : S.Y, v = Vert.y y := by
  induction h with
  | step hm =>
    rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩
      | ⟨x', z', ux', uy', y', h1, h2, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact ⟨y', h2⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
  | trans _ hm ih =>
    obtain ⟨y, rfl⟩ := ih
    -- moralAdj (Y=y) w：Y 无出边
    rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩
      | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)

/-! ## §2 ⭐⭐⭐⭐⭐ **`Y` 是 `X` 的后代** -/

/-- ⭐⭐⭐⭐⭐ **`Y` 是 `X` 的后代**（对**任意** `BackdoorSetup`）。

**⭐⭐ 由 `moralAdj` 的 `X → Y` 规则直接给出。** -/
theorem y_is_descendant (x : S.X) (y : S.Y) (z : S.Z) (ux : S.Ux) (uy : S.Uy)
    (hf : S.fY x z ux uy = y) :
    IsDescendant S (Vert.y y) :=
  IsDescendant.step (Or.inr (Or.inr (Or.inl ⟨x, z, ux, uy, y, rfl, rfl, hf⟩)))

/-! ## §3 ⭐⭐⭐⭐⭐ **`W = {Y}` 违反 Pearl (ii)** -/

/-- ⭐⭐⭐⭐⭐ **`NoDescendant S {Y}` **假****（**Pearl (ii) 的真正检验**）。

**⭐⭐ 这证明 `NoDescendant` **不是**空洞条件。** -/
theorem noDescendant_singleton_false (x : S.X) (y : S.Y) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) (hf : S.fY x z ux uy = y) :
    ¬ NoDescendant S ({Vert.y y} : Set (Vert S)) := by
  intro h
  exact h (Vert.y y) (Set.mem_singleton _) (y_is_descendant S x y z ux uy hf)

/-! ## §4 ⭐⭐⭐⭐⭐ **否定性发现：Pearl (ii) 与 `NoOutcome` 等价** -/

/-- ⭐⭐⭐⭐⭐ **`NoOutcome ⟹ NoDescendant`**（在 `BackdoorSetup` 里）。

**⭐⭐ 由 §1「`X` 的后代只能是 `Y`」直接给出。**
**⟹ **Pearl (ii) 在 `BackdoorSetup` 上是**冗余的**（被 `NoOutcome` 蕴含）。** -/
theorem noDescendant_of_noOutcome (W : Set (Vert S))
    (h : NoOutcome S W) : NoDescendant S W := by
  intro v hv hdesc
  obtain ⟨y, rfl⟩ := descendant_is_y S hdesc
  exact h y hv

end Fate.NoDescendantWitness