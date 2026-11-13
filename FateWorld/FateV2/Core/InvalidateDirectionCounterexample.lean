import FateWorld.FateV2.Core.ClosureAll
open FateV2.Core
open FateV2.Core.DeclGraph
open FateV2.Core.DeclGraphAll

/-!
  # 反例：`invalidate ⊆ closureAll` 的**陈述方向是错的**

  2026-11-02 由协调者实测发现。T8/T10/T14 三个专项追的这条主定理，
  **陈述本身不成立**，不是证不出来。

  ## 方向对比

  | 概念 | 语义 | 方向 |
  |---|---|---|
  | `invalidate g k bk` | 改 `k` 会失效的声明 = **依赖 `k`** 的 | **反向可达**（谁依赖我） |
  | `closureAll g n [k]` | 从 `k` 出发能推出的 | **正向可达**（我依赖谁） |

  两者方向相反，所以「失效集合 ⊆ 正向闭包」不可能普遍成立。
-/

/-- 一条声明：`key = 1`，依赖 `deps = [0]`。 -/
def dtest : Decl Nat :=
  { key := 1, kind := .defn, bodyKind := .body, deps := [0], visibility := .open_ }

/-- 图里只有那一条声明。 -/
def gtest : DeclGraph Nat := [dtest]

def val1 : List Nat := closureAll gtest 1 [0]
def val2 : List Nat := closureAll gtest 2 [0]
def vald : List Nat := depsOfAll gtest 1

/-- 从 `0` 出发，正向闭包**永远只有 `0`**（没有 `key = 0` 的声明，故无边可走）。 -/
theorem closureAll_from_zero_1 : val1 = [0, 0] := rfl

theorem closureAll_from_zero_2 : val2 = [0, 0] := rfl

/-- 但 `1` 的依赖是 `0`：**反向**是可达的。 -/
theorem depsOfAll_one : vald = [0] := rfl

/-- **主定理的反例**：`1 ∉ closureAll gtest 2 [0]`。

    用 `Closure.mem_cons_cases`（零公理）而不是 `List.mem_cons.mp`（带 `propext`）。 -/
theorem key_one_not_in_val : (1 : Nat) ∉ val2 := by
  rw [closureAll_from_zero_2]
  intro h
  have h0 : (1 : Nat) = 0 := by
    rcases mem_cons_cases h with h1 | h1
    · exact h1
    · rcases mem_cons_cases h1 with h2 | h2
      · exact h2
      · exact absurd h2 (List.not_mem_nil)
  exact Nat.noConfusion h0
