import FateWorld.FateV2.Predict.SeparationDecomposition
import FateWorld.FateV2.Modeling.MoralGraphMarkov
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
/-!
  # Predict · SetupXMY

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SetupXMY.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SeparationDecomposition, MoralGraphMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴🔴🔴 **第 297 轮降级声明（Z8 审核，含 3 个 D7 探针）**

## 裁定：**重复劳动，贡献 0**

> **「**4. 裁定：重复劳动，贡献 0。**」**

## 证据 1：`useparated_blocks_x_to_y` 是**平凡的**

| 探针 | 内容 | 结果 |
|---|---|---|
| `d7_drop_hf` | 删掉 `hf`，只留 `hedge : adj (vX x) (vY y)` | ✅ **证成** |
| **`d7_general`** | **删掉整个 `Setup` / `fY` / 九条 `adj`**，换成任意图 | ✅ **15 行证成** |
| `d7_symm_not_needed` | `uadj` 对称化多余 | ✅ **证成** |

**定理的真身**：`hedge : adj a b → a ∉ C → b ∉ C → ¬ USeparated adj C {a} {b}`
**⚠ `Setup` 是**纯死前提**，`hnoX/hnoY` 不是图论条件而是**簿记**。**
**判：**定义展开（长度 1 路径），不是图论。**

## 证据 2：本文件**多余**，且比 R259 **低配**

> **「R259 `BackdoorSetup.fY : X → Z → Ux → Uy → Y`，**第一槽就是 `X`**。**
> **「『`fY` 不吃 `X`』是 **R289 `BackdoorWithM`** 的问题，不是 R259。
> **⚠ **第 295 轮的『架构限制』打偏了**。」**

**⚠ 即：我在第 295 轮**误以为 R259 也不吃 `X`**，实际它**吃**。**
**⭐⭐ 故本文件**新建了一个已有解的低配版**，且**没有任何概率层**
（无 `doLaw` / `adjustLaw` / positivity），**全库零引用**。**

## ⭐ Z8 指出的正确方向

> **「该做的是把 `USeparated` 接到**数值层**（Pearl 1.2.4），**
> **而不是再开一个骨架载体。」**

**⭐⭐ 详见 `_pending/第297轮-第十六次失误.md`。**
-/


/-! ===========================================================================
  `Fate/SetupXMY` —— ⭐⭐⭐⭐⭐ **`fY` 也吃 `X` 的载体**（**第 296 轮**）

  ## 🔴 起因（第 295 轮发现的架构层面根本限制）

  > **「在 `SetupWithM` 里，Pearl (ii) **永远无法被『实质使用』** ——**
  > **因为 `fY` 的类型签名（`M → Z → Ux → Uy → Y`，**没有 `X` 槽**）**
  > **已经保证了『`X` 不影响 `Y`』。**
  > **⚠ 要让 Pearl (ii) 真正起作用，必须让 `fY` **吃 `X`**。」**

  ## ⭐⭐ 本文件做什么

  **定义 `SetupXMY`：`fY : X → M → Z → Ux → Uy → Y`（**多了一个 `X` 槽**）。**

  **⭐⭐ 与 `SetupWithM` 的**唯一差别**：`X → Y` 是**直达边**。**
  **⟹ 「`X` 影响 `Y`」**不再**由类型签名保证，而**必须由图论条件（`USeparated`）**排除。**

  ## ⚠ 顶点表示（**用和类型，避免 inductive 的 Fintype 麻烦**）

  `Vert S := (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.M ⊕ S.Y)`
================================================================================ -/

namespace FateV2.Predict.SetupXMY

open FateV2.Modeling

open Finset

/-- ⭐⭐⭐⭐⭐ **`fY` 也吃 `X` 的载体**。 -/
structure Setup where
  Z : Type
  Ux : Type
  Uy : Type
  X : Type
  M : Type
  Y : Type
  [fZ' : Fintype Z]
  [fUx : Fintype Ux]
  [fUy : Fintype Uy]
  [fX' : Fintype X]
  [fM' : Fintype M]
  [fY' : Fintype Y]
  [dZ : DecidableEq Z]
  [dX : DecidableEq X]
  [dM : DecidableEq M]
  [dY : DecidableEq Y]
  pz : Z → ℝ
  px : Ux → ℝ
  py : Uy → ℝ
  fX : Z → Ux → X
  fM : X → Uy → M
  /-- ⭐⭐ **`Y := fY x m z ux uy` —— 吃 `X`！** -/
  fY : X → M → Z → Ux → Uy → Y

attribute [instance] Setup.fZ' Setup.fUx Setup.fUy Setup.fX' Setup.fM' Setup.fY'
  Setup.dZ Setup.dX Setup.dM Setup.dY

/-- ⭐ **顶点**（用和类型，`Fintype` 自动）。 -/
abbrev Vert (S : Setup) : Type := (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.M ⊕ S.Y)

/-- `Z` 顶点。 -/
def vZ {S : Setup} (z : S.Z) : Vert S := Sum.inl (Sum.inl z)
/-- `Ux` 顶点。 -/
def vUx {S : Setup} (ux : S.Ux) : Vert S := Sum.inl (Sum.inr ux)
/-- `Uy` 顶点。 -/
def vUy {S : Setup} (uy : S.Uy) : Vert S := Sum.inr (Sum.inl uy)
/-- `X` 顶点。 -/
def vX {S : Setup} (x : S.X) : Vert S := Sum.inr (Sum.inr (Sum.inl x))
/-- `M` 顶点。 -/
def vM {S : Setup} (m : S.M) : Vert S := Sum.inr (Sum.inr (Sum.inr (Sum.inl m)))
/-- `Y` 顶点。 -/
def vY {S : Setup} (y : S.Y) : Vert S := Sum.inr (Sum.inr (Sum.inr (Sum.inr y)))

/-! ## §2 ⭐⭐⭐⭐⭐ **因果图 `adj`（**含 `X → Y` 直达边**）** -/

/-- ⭐⭐⭐⭐⭐ **因果图的（有向）邻接**。

**⭐ 九条规则（对称化为无向图见 §3）：**
- `Z → X`、`Ux → X`
- `X → M`、`Uy → M`
- ⭐⭐ **`X → Y`**（**直达边 —— 这是与 `SetupWithM` 的唯一实质差别**）
- `M → Y`、`Z → Y`、`Ux → Y`、`Uy → Y` -/
def adj (S : Setup) : Vert S → Vert S → Prop :=
  fun a b =>
    -- Z → X
    (∃ z : S.Z, ∃ ux : S.Ux, ∃ x : S.X,
      a = vZ z ∧ b = vX x ∧ S.fX z ux = x)
    ∨ -- Ux → X
    (∃ z : S.Z, ∃ ux : S.Ux, ∃ x : S.X,
      a = vUx ux ∧ b = vX x ∧ S.fX z ux = x)
    ∨ -- X → M
    (∃ x : S.X, ∃ uy : S.Uy, ∃ m : S.M,
      a = vX x ∧ b = vM m ∧ S.fM x uy = m)
    ∨ -- Uy → M
    (∃ x : S.X, ∃ uy : S.Uy, ∃ m : S.M,
      a = vUy uy ∧ b = vM m ∧ S.fM x uy = m)
    ∨ -- ⭐⭐ X → Y
    (∃ x : S.X, ∃ m : S.M, ∃ z : S.Z, ∃ ux : S.Ux, ∃ uy : S.Uy, ∃ y : S.Y,
      a = vX x ∧ b = vY y ∧ S.fY x m z ux uy = y)
    ∨ -- M → Y
    (∃ x : S.X, ∃ m : S.M, ∃ z : S.Z, ∃ ux : S.Ux, ∃ uy : S.Uy, ∃ y : S.Y,
      a = vM m ∧ b = vY y ∧ S.fY x m z ux uy = y)
    ∨ -- Z → Y
    (∃ x : S.X, ∃ m : S.M, ∃ z : S.Z, ∃ ux : S.Ux, ∃ uy : S.Uy, ∃ y : S.Y,
      a = vZ z ∧ b = vY y ∧ S.fY x m z ux uy = y)
    ∨ -- Ux → Y
    (∃ x : S.X, ∃ m : S.M, ∃ z : S.Z, ∃ ux : S.Ux, ∃ uy : S.Uy, ∃ y : S.Y,
      a = vUx ux ∧ b = vY y ∧ S.fY x m z ux uy = y)
    ∨ -- Uy → Y
    (∃ x : S.X, ∃ m : S.M, ∃ z : S.Z, ∃ ux : S.Ux, ∃ uy : S.Uy, ∃ y : S.Y,
      a = vUy uy ∧ b = vY y ∧ S.fY x m z ux uy = y)

/-- ⭐ **无向邻接**（`USeparated` 需要）。 -/
def uadj (S : Setup) (a b : Vert S) : Prop := adj S a b ∨ adj S b a

/-! ## §3 ⭐⭐⭐⭐⭐ **`X → Y` 直达边存在**（与 `SetupWithM` 的关键差别） -/

/-- ⭐⭐⭐⭐⭐ **`X → Y` 直达边**（**对任意 `Setup`，只要 `fY` 有原像**）。

**⭐⭐ 这是 `SetupWithM` **不可能**有的边**（因为它的 `fY` 不吃 `X`）。** -/
theorem x_to_y_edge (S : Setup) (x : S.X) (m : S.M) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) (y : S.Y) (hf : S.fY x m z ux uy = y) :
    adj S (vX x) (vY y) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, m, z, ux, uy, y, rfl, rfl, hf⟩))))

/-! ## §4 ⭐⭐⭐⭐⭐ **`USeparated` 必须阻断 `X → Y`** -/

/-- ⭐⭐⭐⭐⭐ **若 `{Y}` 不被 `W` 阻断，则 `USeparated` 失败**（**长度 1 的路径**）。

**⭐⭐ 即：`USeparated adj W {X=x} {Y=y}` **强制** `W` 阻断 `X → Y` 直达边。**
**⚠ 这是 `SetupWithM` **不可能**有的性质 ——**
**因为那里 `X → Y` 边不存在，`USeparated` 无法检验它。**

**⭐⭐ 故：**本载体让 Pearl (i) **真正发挥作用**。** -/
theorem useparated_blocks_x_to_y (S : Setup) (W : Set (Vert S))
    (x : S.X) (m : S.M) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y)
    (hf : S.fY x m z ux uy = y)
    (hnoX : vX x ∉ W) (hnoY : vY y ∉ W) :
    ¬ FateV2.Modeling.MoralGraphMarkov.USeparated (uadj S) W {vX x} {vY y} := by
  intro h
  -- 长度 1 的路径 w = [x, y]
  let w : Fin (1 + 1) → Vert S := fun i => if (i : Nat) = 0 then vX x else vY y
  have hw0 : w 0 = vX x := by simp [w]
  have hw1 : w ⟨1, by norm_num⟩ = vY y := by
    simp only [w]
    norm_num
  have hpath : ∀ i : Fin 1,
      uadj S (w i.castSucc) (w i.succ) ∨ uadj S (w i.succ) (w i.castSucc) := by
    intro i
    have hi : (i : Nat) = 0 := by have := i.isLt; omega
    have e0 : (i.castSucc : Fin 2) = 0 := by ext; simpa [Fin.val_castSucc] using hi
    have e1 : (i.succ : Fin 2) = 1 := by ext; simp [Fin.val_succ, hi]
    rw [e0, e1]
    left
    exact Or.inl (x_to_y_edge S x m z ux uy y hf)
  obtain ⟨i, hi⟩ := h 1 w (by simpa using hw0 ▸ Set.mem_singleton (vX x))
    (by simpa using hw1 ▸ Set.mem_singleton (vY y)) hpath
  fin_cases i
  · exact hnoX (by simpa [w] using hi)
  · exact hnoY (by simp only [w] at hi; norm_num at hi; exact hi)

end FateV2.Predict.SetupXMY
