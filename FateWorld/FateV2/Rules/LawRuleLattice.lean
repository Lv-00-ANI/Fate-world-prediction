import FateWorld.FateV2.Rules.LawRule

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/LawRuleLattice.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-002 D-003
  - 改动：namespace/引用 ProperFit→FateV2.Rules（正文 5 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Rules
open FateV2.Model
open FateV2.Modeling

/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules.LawRuleLattice
阶段：**「规则的代数」—— `LawRule` 的格/Frame 结构**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`FateV2.Rules/LawRule.lean` 把规则定义为

    LawRule C X Y := C.Carrier → X.Carrier → Set (Measure Y.Carrier)

并在**注释里**断言「`∘ = 取交` 天然满足结合律」、规则空间「捕获物理规律式约束」。
本文件把这个断言**升格为格论事实**，并回答「规则作为格/Frame 的元素」这一问题：

1. `LawRule` 逐点继承 `Set` 的**完备格**结构（`instCompleteLattice`）；
2. `∘` **就是**格的 `⊓`（`compose_eq_inf`，定义性相等）；
3. `top` / `bot` **就是** `⊤` / `⊥`（定义性相等）；
4. `LawRule` 是 **Frame**（点自由拓扑 / locale 的代数侧）：
   `⊓` 对**任意** `⨆` 分配（`compose_sSup`）。

---------------------------------------------------------------------------
文献定位（详见仓库根 `SOURCES_RuleAlgebra.md`）
---------------------------------------------------------------------------
- **闭包系统 ⟷ 完备格**，`⋀ = ∩`：Davey & Priestley, *Introduction to
  Lattices and Order*, §2.5（标准结果）。本文件是它在 `LawRule` 上的实例。
- **Frame / 点自由拓扑**：Johnstone, *Stone Spaces*, Ch. II；
  Picado & Pultr, *Frames and Locales*, Ch. 1–2。
- ⚠ **不引用** 文献中同名但结构不同的 "rule algebra"（**Behr & Sobociński**
  (*Rule Algebras for Adhesive Categories*, LMCS 16(3:2) 2020, arXiv:1807.00785) 式的
  重写规则**结合半环**）：那里的乘法是**序列复合**而非交，与本文件无关。
  （另一支同名的 *fusion rule algebra* 属 CFT，亦无关。）

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件**不**声称 `∘ = 取交` 是「规则复合」的**语义上正确**的读法；
  它只证明：**在给定该定义的前提下**，结构是 Frame。
  「更强/更弱的规则是 `⊆` 还是 `⊇`」在本仓库**尚未冻结**（登记为开放问题）。
- 数学内容全部由 Mathlib 的 `Pi`/`Set` 实例**继承**，本文件的实质工作是
  **类型对齐 + 把注释级断言变成可 `#check` 的定理**，不重证 Mathlib。
-/


namespace FateV2.Rules

namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ===========================================================================
    §1  完备格结构
    =========================================================================== -/

/-- `LawRule` 的**完备格**结构：逐点继承 `Set (Measure Y.Carrier)` 的
`CompleteBooleanAlgebra`（经 `Pi` 实例）。

数学内容：规则的集合族在逐点包含下封闭于任意交与任意并。 -/
noncomputable instance instCompleteLattice : CompleteLattice (LawRule C X Y) :=
  inferInstanceAs (CompleteLattice (C.Carrier → X.Carrier → Set (Measure Y.Carrier)))

/-- **`∘` 就是格的 `⊓`**。

这把 `LawRule.lean` 注释里的「`∘ = 取交`」定位为**格论下的交**，
因而 `compose_comm` / `compose_assoc` 是 `inf_comm` / `inf_assoc` 的实例。 -/
theorem compose_eq_inf (R₁ R₂ : LawRule C X Y) : compose R₁ R₂ = R₁ ⊓ R₂ := rfl

/-- `top`（允许一切分布 = 无约束）**就是**格的 `⊤`。 -/
theorem top_eq_top : top C X Y = (⊤ : LawRule C X Y) := rfl

/-- `bot`（不允许任何分布 = 矛盾）**就是**格的 `⊥`。 -/
theorem bot_eq_bot : bot C X Y = (⊥ : LawRule C X Y) := rfl

/-- `∘` 以 `⊤` 为单位元 —— 即 `compose_top` 的格论重述。 -/
theorem compose_top_eq (R : LawRule C X Y) : compose R ⊤ = R := inf_top_eq R

/-- `∘` 以 `⊥` 为零元 —— 即 `compose_bot` 的格论重述。 -/
theorem compose_bot_eq (R : LawRule C X Y) : compose R ⊥ = ⊥ := inf_bot_eq R

/-! ===========================================================================
    §2  Frame 结构（点自由拓扑的代数侧）
    =========================================================================== -/

/-- `LawRule` 是 **Frame**：`⊓` 对任意 `⨆` 分配。

直觉：逐点取 `Set` 的交，而 `Set α` 的并是逐元素并，
故「先交后并」与「先并后交」在每一点上都一致。 -/
noncomputable instance instFrame : Order.Frame (LawRule C X Y) :=
  inferInstanceAs (Order.Frame (C.Carrier → X.Carrier → Set (Measure Y.Carrier)))

/-- **`∘` 对任意并分配**（Frame 公理在规则层的显式形式）：

    R ∘ (⨆ S) = ⨆ { R ∘ S' | S' ∈ S }

即「再加一条规则 `R`」与「取一族规则的并」可交换。 -/
theorem compose_sSup (R : LawRule C X Y) (S : Set (LawRule C X Y)) :
    compose R (sSup S) = sSup ((fun x => compose R x) '' S) := by
  have h : compose R (sSup S) = R ⊓ sSup S := rfl
  rw [h, inf_sSup_eq]
  rw [sSup_image]
  rfl

/-- `∘` 对二元并分配（Frame 公理的有限形式，便于使用）。 -/
theorem compose_sup (R R₁ R₂ : LawRule C X Y) :
    compose R (R₁ ⊔ R₂) = (compose R R₁) ⊔ (compose R R₂) := by
  have h : compose R (R₁ ⊔ R₂) = R ⊓ (R₁ ⊔ R₂) := rfl
  rw [h, inf_sup_left]
  rfl

end LawRule

end FateV2.Rules
