import FateWorld.FateV2.Predict.GraphToProbView7
/-!
  # Predict · MainTheoremC

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MainTheoremC.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GraphToProbView7
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  主定理 C（`ancestral_dSep_CondIndep`）：幽灵定理的实质实现

  ## 背景

  `Fate/GraphToProbView7.lean:190` 声称：
  > **### 4.4 ⭐⭐⭐ 主定理 C（无尾块情形，`ancestral_dSep_CondIndep`）**
  > 设 `A = X ∪ Y ∪ Z`，`A` 上因子化 + `FactorNorm` + `hsplit`（`X` 侧 / `Y ∪ Z` 侧），
  > 则 `CondIndep p X Y Z`。

  **但该定理在 Lean 里不存在**（审计确认）。

  ## 本节做什么：分两步实现

  **步骤 1（本文件）**：`Z = ∅` 的情形 —— `Split ⟹ CondIndep p X Y ∅`
  **原因**：`mass ∅ p` 是常数 `∑ p`，分解干净，无自由度纠缠。
  手算验证（`V = {0,1}`、`X={0}`、`Y={1}`）：
  ```
  左 = (f x · g x) · [(∑f)(∑g)]
  右 = (f x · ∑g) · (∑f · g x)     ✅ 相等
  ```

  **步骤 2（后续）**：一般 `Z ≠ ∅` 的情形 —— `mass Z p` 需要
  「`f` 在 `Z∖X` 上自由」这一自由度分析，比 `Z = ∅` 复杂。

  ## 诚实边界

  * **本文件只做 `Z = ∅` 的情形**，一般 `Z` 未做。
  * **`Split` 是 `hsplit` 的最简精确形式**（`p = f * g` 的两侧读集分离）。
  * **本节不证 `dSep ⟹ Split`**（`d`-分离的内容在这个前件里）。
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open FateV2.Modeling

open FateV2.Error
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FinCondIndep

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §0.1 ⭐ `Split`：两侧读集分离 -/

/-- ⭐ **`Split`**：`p = f * g`，其中 `f` 只读 `X`、`g` 只读 `Y ∪ Z`。

**⟹ 这是文档 `hsplit` 的最简精确形式。** -/
def Split (p f g : (V → α) → ℝ) (X Y Z : Finset V) : Prop :=
  (∀ w, p w = f w * g w) ∧
  (∀ w w', (∀ u ∈ X, w u = w' u) → f w = f w') ∧
  (∀ w w', (∀ u ∈ Y ∪ Z, w u = w' u) → g w = g w')

/-! ### §0.2 ⭐⭐ `Z = ∅` 情形的四个 `mass` -/

/-- ⭐ **`mass (X∪Y∪∅) p x = f x · mass (X∪Y) g x`**（`f` 只读 `X`）。 -/
theorem mass_XY_empty (p f g : (V → α) → ℝ) {X Y : Finset V}
    (hfac : ∀ w, p w = f w * g w)
    (hf : ∀ w w', (∀ u ∈ X, w u = w' u) → f w = f w') (x : V → α) :
    mass (X ∪ Y ∪ ∅) p x = f x * mass (X ∪ Y ∪ ∅) g x :=
  shadow_decomp (A := X ∪ Y ∪ ∅) (T := X) (by intro u hu; simp [hu]) hfac
    (fun w w' h => hf w w' (fun u hu => h u (by simp [hu]))) x

/-- ⭐ **`mass (X∪∅) p x = f x · mass (X∪∅) g x`**。 -/
theorem mass_X_empty (p f g : (V → α) → ℝ) {X : Finset V}
    (hfac : ∀ w, p w = f w * g w)
    (hf : ∀ w w', (∀ u ∈ X, w u = w' u) → f w = f w') (x : V → α) :
    mass (X ∪ ∅) p x = f x * mass (X ∪ ∅) g x :=
  shadow_decomp (A := X ∪ ∅) (T := X) (by intro u hu; simp [hu]) hfac
    (fun w w' h => hf w w' (fun u hu => h u (by simp [hu]))) x

/-- ⭐ **`mass (Y∪∅) p x = mass (Y∪∅) f x · g x`**（`g` 只读 `Y`）。 -/
theorem mass_Y_empty (p f g : (V → α) → ℝ) {Y : Finset V}
    (hfac : ∀ w, p w = f w * g w)
    (hg : ∀ w w', (∀ u ∈ Y, w u = w' u) → g w = g w') (x : V → α) :
    mass (Y ∪ ∅) p x = mass (Y ∪ ∅) f x * g x := by
  have hfac' : ∀ w, p w = g w * f w := fun w => by rw [hfac w]; ring
  have h := shadow_decomp (A := Y ∪ ∅) (T := Y) (by intro u hu; simp [hu]) hfac'
    (fun w w' h => hg w w' (fun u hu => h u (by simp [hu]))) x
  rw [h]
  ring

end FateV2.Predict.GraphToProbView7
