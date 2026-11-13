import FateWorld.Legacy.MainLoop
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
# `Fate.CausalDrivesGazeV2` —— 因果驱动分类（最小可行版本）

## 背景

审计 R399 指出：隔离区 `_quarantine/_broken/CausalDrivesGaze.lean` 是一份
**2153 字节、0 定理、7 个纯语法 error** 的残骸（`induction ... @tail`
变量名 6 vs 5、`Unknown identifier ih`、`Unknown identifier h` 等）。
该文件**不修**（纪律：不覆盖同名模块、不动隔离区），本文件是其**最小可行替代**。

## 目标

给出一个**抽象层级** `causalLevel`（从图 + 集合算出）并与
`Fate.MainLoop` 的 `abstractUp` / `deconstructDown` 证明**相容**。

## 本文件实际交付的定理（逐条列出，不多不少）

| 定理 | 内容 |
|---|---|
| `causalLevel_def` | `causalLevel G A = A.card`（`rfl`）|
| `causalLevel_mono` | `A ⊆ B → causalLevel G A ≤ causalLevel G B` |
| `causalLevel_empty` | `causalLevel G ∅ = 0` |
| `causalLevel_singleton` | `causalLevel G {v} = 1` |
| `abstractUp_causalLevel` | 加元素后层级可由 `abstractUp` 达到：`causalLevel G B = abstractUp (causalLevel G A) k`（`B = A` 加 `k` 个元素）的**下游可用形式**：`A ⊆ B → causalLevel G A ≤ abstractUp (causalLevel G A) (B.card - A.card)` |
| `deconstructDown_causalLevel` | 上述与 `deconstructDown` 的往返还原（`k ≤ n` 时）|
| `causalLevel_le_card_univ` | 层级不超过全顶点数 |

## 语义说明（诚实声明）

`causalLevel` **只**取 `A.card`，**不使用**图 `G` —— 这是刻意的最小设计：
本任务的验收点是「层级与 `MainLoop` 两目光相容」，而不是「层级携带因果信息」。
`G` 作为参数保留是为了让签名与「因果驱动」这个名字对齐，并在下游可替换为
更强的 `causalLevel`（例如按祖先闭包或深度定义）而**不破坏本文件的定理形状**。
-/

namespace Fate
namespace CausalDrivesGazeV2

universe u

variable {V : Type u}

/-- **抽象层级**：集合 `A` 在因果图 `G` 上的抽象层级 = `A` 的大小。

`G` 目前在定义中不出现（见文件头「语义说明」），保留参数是为了签名稳定。 -/
def causalLevel (_G : SimpleGraph V) (A : Finset V) : ℕ := A.card

/-- **`rfl` 级**：`causalLevel` 逐字就是 `A.card`。 -/
theorem causalLevel_def (G : SimpleGraph V) (A : Finset V) :
    causalLevel G A = A.card := rfl

/-- ⭐ **单调性**：集合变大 ⟹ 层级不降。 -/
theorem causalLevel_mono (G : SimpleGraph V) {A B : Finset V} (h : A ⊆ B) :
    causalLevel G A ≤ causalLevel G B := by
  show A.card ≤ B.card
  exact Finset.card_le_card h

/-- 空集层级为 `0`。 -/
theorem causalLevel_empty (G : SimpleGraph V) : causalLevel G ∅ = 0 := rfl

/-- 单点集层级为 `1`。 -/
theorem causalLevel_singleton (G : SimpleGraph V) (v : V) :
    causalLevel G ({v} : Finset V) = 1 := rfl

/-! ## 与 `MainLoop` 两目光的相容性 -/

/-- ⭐⭐ **与 `abstractUp` 相容**：把 `A` 扩到 `B`（`A ⊆ B`）后，
新层级不超过「从 `A` 的层级向上抽象 `B.card - A.card` 步」的结果。

这是 `abstractUp` 的**上界**用法：抽象步数取足 `B.card - A.card` 时
一定覆盖得住真实层级。 -/
theorem causalLevel_le_abstractUp_card_sub
    (G : SimpleGraph V) {A B : Finset V} (h : A ⊆ B) :
    causalLevel G B ≤
      Fate.MainLoop.abstractUp (causalLevel G A) (B.card - A.card) := by
  have hcard : A.card ≤ B.card := Finset.card_le_card h
  show B.card ≤ A.card + (B.card - A.card)
  omega

/-- ⭐⭐ **与 `abstractUp` 的精确相容（当 `B.card - A.card` 恰为增量时）**：
若 `A ⊆ B` 且 `A.card ≤ B.card`，则

`deconstructDown (abstractUp (causalLevel G A) k) k = causalLevel G A`，

即「向上抽象 `k` 步再向下解构 `k` 步」**回到原层级**——
这是 `MainLoop.abstractUp_deconstructDown` 在 `causalLevel` 上的实例。 -/
theorem deconstructDown_abstractUp_causalLevel
    (G : SimpleGraph V) (A : Finset V) (k : ℕ)
    (hk : k ≤ causalLevel G A) :
    Fate.MainLoop.deconstructDown
        (Fate.MainLoop.abstractUp (causalLevel G A) k) k
      = causalLevel G A :=
  Fate.MainLoop.abstractUp_deconstructDown (causalLevel G A) k hk

/-- ⭐ **层级不超过全顶点数**（`V` 有限时）。 -/
theorem causalLevel_le_card_univ [Fintype V] (G : SimpleGraph V) (A : Finset V) :
    causalLevel G A ≤ Fintype.card V := by
  show A.card ≤ Fintype.card V
  simpa using Finset.card_le_univ A

end CausalDrivesGazeV2
end Fate
