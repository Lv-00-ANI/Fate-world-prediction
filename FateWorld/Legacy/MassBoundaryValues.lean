import FateWorld.Legacy.BarCorrected
import FateWorld.Legacy.MassInsertCorrected

/-! ===========================================================================
  §0  `mass` 的**边界值一览**（防错的语义基准）

  ## 背景

  本会话发现 11 处真实数学错误，其中 **3 处属于「空集/全集边界」类**：
  * `mass ∅` 被当作 1（实际是 `∑ w, p w`）
  * `mass A`（`A ⊊ univ`）被当作单点（实际带 `|α|^(|V|-|A|)` 因子）
  * `bar univ` 被当作全体乘积（实际是 1，因 `tail univ = ∏ ∅ = 1`）

  ## 本文件：五条边界基准

  | 定理 | 内容 |
  |---|---|
  | `b_univ` | `mass univ p x = p x` |
  | `b_empty` | `mass ∅ p x = ∑ w, p w` |
  | `b_one` | `mass S 1 x = |α|^(|V| - |S|)` |
  | `b_one_univ` | `mass univ 1 x = 1` |
  | `b_local` | `p` 只读 `S`，`x\|_S = y\|_S` ⟹ `mass S p x = mass S p y` |

  ⟹ 任何涉及 `mass` 的边界断言都应先对照这五条。
  =========================================================================== -/

namespace Fate.C7
open Finset Fate Fate.DAGFactorization
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- ⭐ 边界值一览（正确版本）

-- 1. mass univ p x = p x
theorem b_univ (p : (V → α) → ℝ) (x : V → α) : mass univ p x = p x :=
  mass_univ p x

-- 2. mass ∅ p x = ∑ w, p w
theorem b_empty (p : (V → α) → ℝ) (x : V → α) : mass ∅ p x = ∑ w, p w :=
  mass_empty p x

-- 3. mass S 1 x = |α|^(|V| - |S|)   （S = univ 时 = 1）
theorem b_one (S : Finset V) (x : V → α) :
    mass S (fun _ => (1 : ℝ)) x = ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card)) :=
  Fate.GraphToProbView7.mass_one_card S x

-- 4. mass univ 1 x = 1
theorem b_one_univ (x : V → α) : mass univ (fun _ => (1 : ℝ)) x = 1 := by
  rw [b_one]
  rw [Finset.card_univ]
  simp

-- 5. mass S p x 只依赖 x|_S（p 只读 S）
theorem b_local {S : Finset V} {p : (V → α) → ℝ}
    (hp : ∀ w w', (∀ u ∈ S, w u = w' u) → p w = p w')
    {x y : V → α} (h : ∀ u ∈ S, x u = y u) : mass S p x = mass S p y :=
  mass_congr S p h

end Fate.C7
