import FateWorld.FateV2.Rules.FCA
/-!
  # Rules · T112UnaryClosure

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T112UnaryClosure.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FCA
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T112UnaryClosure` —— **T1.12 任务 · 步骤 2 探针公用件**

  # 本文件给「一般闭包算子」这一侧提供一个**统一的可陈述框架**

  ## 背景（为什么要这个文件）

  前面几轮失败的模式是：把「一般闭包算子的结论」当成「FCA 特有」。
  本轮把「是否 FCA 特有」化归为一个**可判决的比较**：

  > 候选命题 `P` 若能在 **`Unary` 框架**中陈述，则它 **不是** FCA 特有；
  > 若 `P` 的陈述**必须出现两个不同的底集**，则它是 FCA 特有。

  ## `Unary` 框架 = 「只有一个底集」的 FCA

  取 `γ` 一个类型、`r : γ → γ → Prop`（**两端同型**），
  闭包算子 `uClosure r := lowerPolar r ∘ upperPolar r : ClosureOperator (Set γ)`。
  这与 FCA 的 `polarUp`/`polarDown` **是同一份代码**，只是把 `G` 与 `M`
  强行取成同一个类型 `γ`。

  ## ⚠ 诚实边界

  1. `Unary` **不是**「任意闭包算子」，是「由同型关系诱导的闭包算子」。
     故「在 `Unary` 里成立」⟹ 不能推出「对任意闭包算子成立」。
  2. 但「在 `Unary` 里成立」**足以否证**「FCA 特有」的**强形式**
     （即「必须有 `G ≠ M` 双侧结构」）——因为 `Unary` 里 `G` 与 `M` 是同一个类型。
  3. 对**任意**闭包算子（非 `Unary` 来的），本文件另给 `ArbClosure` 工具：
     直接对任意 `ClosureOperator` 陈述（步骤 2 的**模板 A**）。
================================================================================ -/

namespace FateV2.Rules
open Set

namespace T112Unary

/-- 由同型二元关系 `r : γ → γ → Prop` 诱导的闭包算子（幂集上）。 -/
def uClosure {γ : Type*} (r : γ → γ → Prop) : ClosureOperator (Set γ) :=
  extentClosure r

@[simp] theorem uClosure_apply {γ : Type*} (r : γ → γ → Prop) (A : Set γ) :
    uClosure r A = lowerPolar r (upperPolar r A) := rfl

/-- 单底集版的「extent」。 -/
abbrev UExtent {γ : Type*} (r : γ → γ → Prop) := { s : Set γ // Order.IsExtent r s }

/-- 单底集版的「intent」。⚠ 与 `UExtent` **是同一个类型构造子**（`Subtype (IsExtent r)` vs
`Subtype (IsIntent r)`），这是「两侧坍缩」的第一个形式迹象。 -/
abbrev UIntent {γ : Type*} (r : γ → γ → Prop) := { s : Set γ // Order.IsIntent r s }

/-- ⭐⭐⭐ **`Unary` 框架的坍缩引理 1**：若 `r` 对称，则 `upperPolar r` 与 `lowerPolar r`
是**逐点相等**的算子，从而 `uClosure r = upperPolar r ∘ upperPolar r`。

**这是「只有一个底集」的直接后果**：两侧同型 ⟹ 上极与下极变成同一个算子。 -/
theorem upperPolar_eq_lowerPolar_of_symm {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (s : Set γ) : upperPolar r s = lowerPolar r s := by
  ext x
  simp only [mem_upperPolar_iff, mem_lowerPolar_iff]
  constructor <;> intro h y hy <;> exact hr.symm _ _ (h hy)

/-- ⭐⭐⭐ **坍缩引理 2**：对称 `r` 下，`IsExtent r s ↔ IsIntent r s`（变成同一谓词）。

⚠ 注意：`IsExtent` 用的是 `lowerPolar r (upperPolar r s)`，
`IsIntent` 用的是 `upperPolar r (lowerPolar r s)`。
在对称情形两者**同时**化简为 `lowerPolar r (lowerPolar r s)`——
故「外延」与「内涵」**不可区分**。 -/
theorem isExtent_iff_isIntent_of_symm {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (s : Set γ) :
    Order.IsExtent r s ↔ Order.IsIntent r s := by
  rw [Order.isExtent_iff, Order.isIntent_iff]
  -- 两边同时换成 `upperPolar`: `upperPolar r s = lowerPolar r s`, 故
  -- `lowerPolar r (upperPolar r s) = s ↔ upperPolar r (upperPolar r s) = s`
  -- 以及 `upperPolar r (lowerPolar r s) = s ↔ upperPolar r (upperPolar r s) = s`
  have h1 : upperPolar r s = lowerPolar r s := upperPolar_eq_lowerPolar_of_symm hr s
  have h2 : upperPolar r (lowerPolar r s) = lowerPolar r (lowerPolar r s) :=
    upperPolar_eq_lowerPolar_of_symm hr (lowerPolar r s)
  rw [h2, h1]

/-- ⭐⭐ **对称情形的坍缩形式**：`IsExtent r s ↔ lowerPolar r (lowerPolar r s) = s`。

这是 `Unary` 框架下「双侧结构」的**终点**：两侧已合并，只剩一个算子 `lowerPolar r`。 -/
theorem isExtent_iff_lowerPolar_lowerPolar {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (s : Set γ) : Order.IsExtent r s ↔ lowerPolar r (lowerPolar r s) = s := by
  rw [Order.isExtent_iff, upperPolar_eq_lowerPolar_of_symm hr]

end T112Unary

/-! ## `ArbClosure`：对**任意** `ClosureOperator` 陈述的模板（模板 A） -/

namespace T112Arb

/-- 任意闭包算子 `c` 的**不动点**（= 「闭集」）。 -/
abbrev Fix {α : Type*} [PartialOrder α] (c : ClosureOperator α) := { a : α // c a = a }

/-- 任意闭包算子的不动点类型**自带**一个「闭包关系」：`≤`。
⚠ 这是「单侧」结构的全部——**没有第二个底集**。 -/
theorem fix_ext_eq {α : Type*} [PartialOrder α] (c : ClosureOperator α)
    (p : Fix c) : c p.1 = p.1 := p.2

end T112Arb

end FateV2.Rules