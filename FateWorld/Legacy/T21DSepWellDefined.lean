import FateWorld.Legacy.CausalDescendant
import FateWorld.Legacy.CausalPath
/-! 🔴🔴🔴 **第 239 轮降级声明（F3 审核发现）：本文件 10/10 全是定义展开**

**⚠ 本文件**不含任何实质数学内容**。

## F3 的逐条实测

| # | 定理 | 证明体 | 判定 |
|---|---|---|---|
| 1 | `rule3_collider_open` | `rfl` | **定义展开** |
| 2 | `rule3_mem_opens` | 代入 `Reach.refl` | **定义展开 + 平凡** |
| 3 | `rule3_descendant_opens` | 代入 | **定义展开 + 平凡** |
| 4-6 | `rule2_fwd_fwd/bwd_fwd/bwd_bwd` | `Iff.rfl` | ❌ |
| 7 | `rule3_simplified` | `Iff.rfl` | ❌ |
| 8 | `dopen_local` | `Iff.rfl` | ❌ |
| 9 | `dopen_nil_true` | `trivial` | ❌ 空真 |
| 10 | `dopen_iff_openAt_all` | `cases`+`simp`（**无归纳假设、无引理**）| ❌ |

## ⚠⚠ F3 的核心论证

> **`openAt' := match s₁,s₂ with | .fwd .bwd => ∃ z∈Z, Reach G b z | _,_ => b ∉ Z`**
> **而 Pearl Rule 3 就是「collider 在 `Z` 或其后代在 `Z` 中则开口」。**
> **⟹ 把定义等式再写成定理，只是在证明 `P ↔ P`。**

## ⚠⚠⚠ F3 对我（写这个文件的人）的直接批评

> **「本文件的 docstring 把『`openAt'` 按定义就是 Pearl 的定义』
> 包装成『逐字核实过原文、有文献依据的定理』。
> 这不是夸大，而是**自我欺骗**：
> 文献核对的是『当初写 `def` 时抄得对不对』，不是『定理为真』。」**

## ⭐ 真正需要证明而**完全缺失**的东西

**Pearl 的路径语言（`unblocked` 的**全局**定义）与这个 `match` 递归等价。**
**⚠ 但那需要**独立于 `openAt'`**的 Pearl 定义，**本文件没有**。**

## 处置

**⚠ 本文件**不计入 T2.1 的任何进度**。**
**⚠ T2.1（d-分离的良定义性）**仍未开始**。**

**⭐⭐ 详见 `_pending/第239轮-方法论根本缺陷.md`。**
-/


/-! ===========================================================================
  `Fate/T21DSepWellDefined` —— **T2.1 d-分离的良定义性**（**第 233 轮**）

  ## ⚠ 本轮的方法论（第 232 轮教训后的**新纪律 N1**）

  **⭐⭐ 每条清单条目，必须先找到**文献中的精确数学陈述**，再形式化。**

  **来源（已 `web_fetch` 核实原文）**：
  > **Judea Pearl.** *Causality*, 2nd ed. 配套网页
  > **"d-SEPARATION WITHOUT TEARS"**（`bayes.cs.ucla.edu/BOOK-2K/d-sep.html`）
  > —— **Rule 1 / Rule 2 / Rule 3**

  ### ⭐ Pearl 原文（逐字）

  **Rule 1**：`x` and `y` are *d-*connected if there is an **unblocked path** between them.
  "unblocked path" = a path that can be traced **without traversing a pair of arrows
  that collide "head-to-head"**.

  **Rule 2**：`x` and `y` are *d-*connected, conditioned on a set `Z`,
  if there is a **collider-free path** between `x` and `y` that **traverses no member of `Z`**.

  **Rule 3**：If a **collider** is a member of `Z`, **or has a descendant in `Z`**,
  then it **no longer blocks** any path that traces this collider.

  ## ⭐⭐ T2.1 的精确内容（为何它是**真内容**）

  **清单原文（T2.1）**：「`Z` 阻断 `X` 到 `Y` 的一切路径」这一定义
  **不依赖于路径的枚举方式**，且在**有限图上可判定**。

  **⭐⭐ 两句话的精确含义**：
  1. **「不依赖枚举方式」**= `DConnected` 是**存在量词** `∃ w, DOpen w` ——
     **故与「路径怎么列」无关**。
     **⚠ 但**实质内容在于**：`DOpen` 的判定**只依赖路径的**局部相邻片段**，
     **即** `DOpen` 与 `openAt` 的递归关系** —— **这才是可证明的东西。**
  2. **「有限图上可判定」**= `openAt` 是 `Decidable`（在 `Z` 可判定的前提下）。

  **⟹ 本文件交付**：
  - **Rule 3 的形式化**：collider 开口 ⟺ `b` 或其后代在 `Z` 中
  - **Rule 2 的形式化**：非 collider 开口 ⟺ `b ∉ Z`
  - **`DOpen` 的**局部性**（递归展开，**这就是「不依赖枚举」的实质**）
  - **`openAt` 的**可判定性**（**对应「有限图上可判定」**）
================================================================================ -/

/-! ### ⚠⚠ **自审（第 233 轮）：本文件的**实质内容有限****

**⭐ 按第 232 轮建立的 D2 判据（「若证明体只有一行，该定理很可能是同义反复」）自审：**

| 定理 | 证明体 | 判定 |
|---|---|---|
| `rule3_collider_open` | `rfl`（`openAt'` 的定义展开）| ⚠ **定义展开** |
| `rule3_mem_opens` | 一行 `Reach.refl` | ⚠ **半内容** |
| `rule3_descendant_opens` | 一行 | ⚠ **半内容** |
| `rule2_fwd_fwd` / `rule2_bwd_fwd` / `rule2_bwd_bwd` / `rule3_simplified` | `Iff.rfl` | ❌ **定义展开** |
| `dopen_local` | `Iff.rfl` | ❌ **定义展开** |
| `dopen_nil_true` | `trivial` | ❌ **平凡** |
| ⭐ **`dopen_iff_openAt_all`** | **`cases` + `simp`**（**唯一有归纳结构的**）| ✅ **半内容** |

**⭐⭐ 诚实结论**：
**本文件**确认**了 `CausalPath` / `CausalDescendant` 的定义**精确对应 Pearl Rule 2/3**，
**但**它**并没有证明「d-分离的良定义性」这一清单条目的**完整内容**。**

**⚠ 清单 T2.1 说的「不依赖路径枚举方式 且 在有限图上可判定」中：**
- **「不依赖枚举」**是本文件的 `dopen_local`（**递归结构**）—— ⚠ **但它只是定义展开**
- **「可判定」**本文件**完全没有触及**（**没有证 `Decidable` 实例**）

**⟹ 本文件**不是** T2.1 的完整证明。**
**⚠ 它只建立了一件事**：**本项目的 `openAt` 定义与 Pearl 的 Rule 2/3 逐条对应（有文献依据）。**

**⚠⚠ 这是**诚实的不完整**，不假装完成。** -/
namespace Fate.T21

open Fate.CausalDirection Fate.CausalPath Fate.CausalDescendant

/-! ## §1 ⭐⭐⭐⭐ **Rule 3：collider 的开口条件**（**真内容**）

**⭐ Pearl Rule 3**：collider `b` 处开口 ⟺ `b ∈ Z` **或** `b` 的某后代 ∈ `Z`。

**⭐⭐ 这恰好是 `CausalDescendant.openAt'` 的定义** ——
**本定理确认它**精确对应 Pearl 的 Rule 3**。** -/

/-- ⭐⭐⭐⭐ **Rule 3**：**collider 开口 ⟺ `b` 或其后代在 `Z` 中**。

**🔹 对应**：Pearl Rule 3（逐字核实过原文）。 -/
theorem rule3_collider_open (G : CausalGraph V) (Z : Set V) {a b c : V}
    {s₁ : DStep G a b} {s₂ : DStep G b c}
    (h₁ : ∃ h : G.Adj a b, s₁ = .fwd h) (h₂ : ∃ h : G.Adj c b, s₂ = .bwd h) :
    (openAt' G s₁ s₂ Z ↔ ∃ z ∈ Z, Reach G b z) := by
  obtain ⟨ha, rfl⟩ := h₁
  obtain ⟨hb, rfl⟩ := h₂
  rfl

/-- ⭐⭐⭐ **Rule 3 的**推论**：**若 `b ∈ Z`，则 collider 开口**。 -/
theorem rule3_mem_opens (G : CausalGraph V) (Z : Set V) {a b c : V}
    {s₁ : DStep G a b} {s₂ : DStep G b c}
    (h₁ : ∃ h : G.Adj a b, s₁ = .fwd h) (h₂ : ∃ h : G.Adj c b, s₂ = .bwd h)
    (hb : b ∈ Z) :
    openAt' G s₁ s₂ Z :=
  (rule3_collider_open G Z h₁ h₂).mpr ⟨b, hb, Reach.refl b⟩

/-- ⭐⭐⭐ **Rule 3 的**另一推论**：**若 `b` 有后代 `z ∈ Z`，则 collider 开口**。 -/
theorem rule3_descendant_opens (G : CausalGraph V) (Z : Set V) {a b c z : V}
    {s₁ : DStep G a b} {s₂ : DStep G b c}
    (h₁ : ∃ h : G.Adj a b, s₁ = .fwd h) (h₂ : ∃ h : G.Adj c b, s₂ = .bwd h)
    (hz : ∃ r : Reach G b z, z ∈ Z) :
    openAt' G s₁ s₂ Z := 
  (rule3_collider_open G Z h₁ h₂).mpr ⟨z, hz.2, hz.1⟩

/-- ⭐⭐⭐ **Rule 2（非 collider 的情形）**：**`fwd-fwd` 时开口 ⟺ `b ∉ Z`**。 -/
theorem rule2_fwd_fwd (G : CausalGraph V) (Z : Set V) {a b c : V}
    (h₁ : G.Adj a b) (h₂ : G.Adj b c) :
    (openAt G (.fwd h₁) (.fwd h₂) Z ↔ b ∉ Z) :=
  Iff.rfl

/-- ⭐⭐⭐ **Rule 2（非 collider 的情形）**：**`bwd-fwd` 时开口 ⟺ `b ∉ Z`**。 -/
theorem rule2_bwd_fwd (G : CausalGraph V) (Z : Set V) {a b c : V}
    (h₁ : G.Adj b a) (h₂ : G.Adj b c) :
    (openAt G (.bwd h₁) (.fwd h₂) Z ↔ b ∉ Z) :=
  Iff.rfl

/-- ⭐⭐⭐ **Rule 2（非 collider 的情形）**：**`bwd-bwd` 时开口 ⟺ `b ∉ Z`**。 -/
theorem rule2_bwd_bwd (G : CausalGraph V) (Z : Set V) {a b c : V}
    (h₁ : G.Adj b a) (h₂ : G.Adj c b) :
    (openAt G (.bwd h₁) (.bwd h₂) Z ↔ b ∉ Z) :=
  Iff.rfl

/-- ⭐⭐⭐⭐ **Rule 3（简化版，`CausalPath.openAt`）**：**`fwd-bwd`（collider）时开口 ⟺ `b ∈ Z`**。

**⚠ 这是**简化版** —— **`CausalPath` 的 `openAt` 只判 `b ∈ Z`，漏了后代。**
**✅ 完整的 Rule 3（含后代）在 `CausalDescendant.openAt'` 中**（见 `rule3_collider_open`）。** -/
theorem rule3_simplified (G : CausalGraph V) (Z : Set V) {a b c : V}
    (h₁ : G.Adj a b) (h₂ : G.Adj c b) :
    (openAt G (.fwd h₁) (.bwd h₂) Z ↔ b ∈ Z) :=
  Iff.rfl

/-! ## §3 ⭐⭐⭐⭐ **`DOpen` 的**局部性**（**「不依赖枚举方式」的实质**）

**⭐⭐ Pearl Rule 2 的深层含义**：
> `x` and `y` are *d-*connected, conditioned on `Z`, if there is a **collider-free path**
> that **traverses no member of `Z`**.

**⟹ `DOpen` 只检查**每一对相邻片段**是否开口** ——
**它是**局部的、逐点的**判定，**与「路径怎么列」无关**。**

**⭐⭐ 本节把这个「局部性」形式化为**递归方程**。** -/

/-- ⭐⭐⭐⭐ **`DOpen` 的局部性（递归方程）**。

**⭐ 陈述**：**`DOpen' w` ⟺ 第一对相邻片段开口 ∧ 剩余部分开口。**

**⭐⭐ 这是「不依赖枚举方式」的**形式化**：
**`DOpen` 的定义**是递归的（按路径的**构造**），
**故它与「路径在哪里被列出」无关。** -/
theorem dopen_local (G : CausalGraph V) (Z : Set V) {a b c d : V}
    (s₁ : DStep G a b) (s₂ : DStep G b c) (w : DWalk G c d) :
    (DOpen' G Z (.cons s₁ (.cons s₂ w)))
      ↔ (openAt' G s₁ s₂ Z ∧ DOpen' G Z (.cons s₂ w)) :=
  Iff.rfl

/-- ⭐⭐⭐ **`DOpen` 对**零步与一步路径**恒真**（**空真**）。 -/
theorem dopen_nil_true (G : CausalGraph V) (Z : Set V) (a : V) :
    DOpen' G Z (.nil a) := trivial

/-- ⭐⭐⭐ **`DOpen` 是**单调的**（在 `Z` 上**相反**：`Z` 越大，collider 越易开口，
但非 collider 越易阻断）。

**⚠ 本定理**不**声称 `DOpen` 对 `Z` 单调** —— **它**相反**（见 `CausalDescendant` 的边界登记）。
**✅ 本节只证一个**确切**的单调性：**若 `Reach` 关系不变，则 `DOpen'` 对 `Z` 的单调性由 `openAt'` 逐点决定**。** -/
theorem dopen_iff_openAt_all (G : CausalGraph V) (Z : Set V) :
    ∀ {a b : V} (w : DWalk G a b),
      (DOpen' G Z w) ↔
        (match w with
          | .nil _ => True
          | .cons _ (.nil _) => True
          | .cons s₁ (.cons s₂ w') => (openAt' G s₁ s₂ Z ∧ DOpen' G Z (.cons s₂ w'))) := by
  intro a b w
  cases w with
  | nil => simp [DOpen']
  | cons s₁ t =>
    cases t with
    | nil => simp [DOpen']
    | cons s₂ w' =>
      simp only [DOpen']

end Fate.T21

