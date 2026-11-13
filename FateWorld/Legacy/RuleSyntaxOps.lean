import FateWorld.Legacy.RuleSyntax

/-! ===========================================================================
  规则核心链 · **IR 四算子的语法层对应**（乙-2 第 1 件）

  ## 本模块做什么

  `规则层类型学基础.md` §五 给出四算子：

  | 算子 | 语义 | 本模块的语法层实现 |
  |---|---|---|
  | **`α`（抽象）** | 从实例产生规则 | `alphaFrom`（从具体环境 `e` 造出 `xᵢ = eᵢ` 的合取） |
  | **`γ`（泛化）** | 放宽（允许集变大） | `generalize`（加恒真析取项）+ `loosen`（`lt ↦ le`，非平凡） |
  | **`υ`（完善）** | 收窄（允许集变小） | `refine`（加恒真合取项 —— **第一版不真正收窄**） |
  | **`∘`（组合）** | 取交 | `compose`（`and`） |

  这些是**语法项上的构造**（`RuleTerm → RuleTerm`），
  以及它们在两层语义（`RuleTerm.holds` / `toLawRuleWith`）下的**对应定理**。

  ## 定理（全部 `EXIT=0`，无 `sorry`）

  | # | 声明 | 内容 |
  |---|---|---|
  | 1 | `holds_trueTerm` | 恒真项确实恒真 |
  | 2 | `holds_generalize` | ⭐ `t.holds e → (γ t).holds e`（`γ` 放宽） |
  | 3 | `holds_compose_iff` | ⭐ `(a ∘ b).holds e ↔ a.holds e ∧ b.holds e` |
  | 4 | `holds_refine` | ⭐ `(υ t).holds e → t.holds e`（`υ` 的收窄方向） |
  | 5 | `holds_refine_iff` | **第一版 `υ` 在语义上等价于 `t`**（诚实的「不收紧」登记） |
  | 6 | `holds_loosen` | `lt ↦ le` 式放宽保持成立性 |
  | 7 | `holds_alphaFrom_iff` | `α`：从实例 `e` 产生的规则恰在 `x₀=e₀ ∧ … ∧ x_{n-1}=e_{n-1}` 上成立 |
  | 8 | `toLawRuleWith_compose` | ⭐⭐⭐ 组合在 `LawRule` 层 = **逐点取交** |
  | 9 | `toLawRuleWith_generalize_subset` | ⭐⭐⭐ 泛化在 `LawRule` 层 = **包含变大** |
  | 10 | `toLawRuleWith_loosen_subset` | 非平凡泛化同样是包含 |
  | 11 | `toLawRuleWith_refine_subset` | 完善在 `LawRule` 层 = **包含变小**（此处因第 5 条而为等号） |

  ## 诚实边界（务必先读）

  1. **`Fate.LawRule.LawRule` 只是函数别名**
     `LawRule C X Y := C.Carrier → X.Carrier → Set (Measure Y.Carrier)`，
     **没有 `Inf` 实例、没有 `⊆` 实例**（`⊆` 是 `Set` 的，不是 `LawRule` 的）。
     因此本模块**不**写 `toLawRuleWith interp (compose a b)
     = toLawRuleWith interp a ⊓ toLawRuleWith interp b`，
     而是写**逐点**形式
     `∀ c x, toLawRuleWith … (compose a b) c x = … a c x ∩ … b c x`，
     以及**函数层**形式 `funext` 后的等式。
     这正是「绕过缺 `Inf` 实例」的做法：不发明实例，只陈述逐点事实。
  2. **`γ` 的两个版本强度不同**：
     `generalize`（`or` 恒真项）把约束放松到**几乎无约束**
     （`toLawRuleWith` 给出全集）；`loosen`（`lt ↦ le`）是**真正非平凡**的放宽。
     两者都满足「原约束 ⟹ 放宽后约束」，但只有 `loosen` 保留信息。
  3. **`υ`（完善）第一版不真正收窄**：`refine t = and t 恒真`，
     语义**等价**于 `t`（定理 5 如实登记）。
     真正的收窄需要外部数据（哪些分布已被数据排除），
     本模块不假设这类数据存在。
  4. 本模块**不修改任何既有模块**，只新建。
     **未使用 `sorry` / `admit` / `axiom`**。
============================================================================ -/

namespace Fate
namespace RuleSyntaxOps

open Fate.RuleSyntax

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ### §1  `interp` 的记法（与 `RuleSyntax.toLawRuleWith` 同一形状） -/

/-- 「分布 → 环境」的解释：形状与 `RuleSyntax.toLawRuleWith` 的参数完全一致。 -/
abbrev Interp (C : CtxSpace) (X : StateSpace) (Y : OutSpace) [MeasurableSpace Y.Carrier] :=
  C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env

/-! ### §2  恒真项 -/

/-- **恒真约束**：`0 ≤ 0`。

选 `le (const 0) (const 0)` 而不是某个「专门的真构造子」，
是因为 `RuleTerm` 已有 `le`，**不需要也不允许**改 `RuleSyntax.lean`。 -/
def trueTerm : RuleTerm := RuleTerm.le (RuleTerm.const 0) (RuleTerm.const 0)

/-- 恒真项在任何环境下成立。 -/
@[simp] theorem holds_trueTerm (e : Env) : trueTerm.holds e := by
  simp [trueTerm]

/-! ### §3  ⭐ `γ`（泛化）—— 两个版本

**语义要求**（两个版本都必须满足）：`t.holds e → (γ t).holds e`。 -/

/-- ⭐⭐⭐ **【`γ`（泛化）：放松约束 —— 最弱版本】**

`generalize t := t ∨ True`：把 `t` 与恒真项取析取。
这是**最强的放松**（允许一切）。

优点：对**任意** `t` 都能证 `holds_generalize`。
缺点：`toLawRuleWith` 层给出全集（信息全丢）——
故另设 `loosen`（见下）作为**保留信息**的泛化。 -/
def generalize (t : RuleTerm) : RuleTerm := RuleTerm.or t trueTerm

/-- ⭐ **泛化的语义单调性**：原约束成立 ⟹ 泛化后成立。 -/
theorem holds_generalize {t : RuleTerm} {e : Env} (_h : t.holds e) :
    (generalize t).holds e := by
  simp [generalize]

/-- 泛化的**语义无关性**（honest remark 的机器可检验形式）：
`generalize t` 在任何环境下都成立。 -/
@[simp] theorem holds_generalize_all (t : RuleTerm) (e : Env) :
    (generalize t).holds e := by
  simp [generalize]

/-! ### §3b  ⭐ `γ` 的**非平凡**版本：`loosen`（`lt ↦ le`）

`generalize` 太粗（丢光信息）。`loosen` 只把**严格**不等式放宽为**非严格**不等式，
并保持合取 / 析取的结构。

⚠ `not` 分支**不递归**：`¬(a < b) ⇏ ¬(a ≤ b)`，
故 `loosen (not a) = not a`（保持原样，soundness 仍成立）。 -/

/-- ⭐⭐ **【`γ`（泛化）：放宽 —— 非平凡版本】**

递归地把 `lt` 放宽成 `le`，其余构造子保持结构。 -/
def loosen : RuleTerm → RuleTerm
  | .lt a b => .le a b
  | .and a b => .and (loosen a) (loosen b)
  | .or a b => .or (loosen a) (loosen b)
  | t => t

/-- ⭐ **非平凡泛化的语义单调性**：

`t.holds e → (loosen t).holds e`。

注意 `le` 分支：`a < b → a ≤ b`（`le_of_lt`）；
`not` 分支保持原样，故 `¬a → ¬a`。 -/
theorem holds_loosen {t : RuleTerm} {e : Env} (h : t.holds e) : (loosen t).holds e := by
  induction t with
  | lt a b =>
      -- `(loosen (lt a b)).holds e` 定义上就是 `a.eval e ≤ b.eval e`
      simp only [loosen, RuleTerm.holds] at h ⊢
      exact le_of_lt h
  | and a b iha ihb =>
      simp only [loosen, RuleTerm.holds] at h ⊢
      exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb =>
      simp only [loosen, RuleTerm.holds] at h ⊢
      exact h.imp iha ihb
  | const _ | var _ | add _ _ | mul _ _ | eq _ _ | le _ _ | not _ =>
      simpa [loosen] using h

/-! ### §4  ⭐ `υ`（完善）—— 第一版：不真正收窄

**语义要求**：`(υ t).holds e → t.holds e`（收窄 ⟹ 更严格 ⟹ 蕴含原约束）。 -/

/-- ⭐⭐⭐ **【`υ`（完善）：收紧约束 —— 第一版】**

`refine t := t ∧ True`。

⚠ **第一版不真正收窄**：真正的收窄需要「哪些分布在数据下已被排除」这一
**外部信息**，本模块**不假设**它存在。故这里只做「不放松地携带原约束」，
并**如实声明** `refine t` 与 `t` 语义等价（见 `holds_refine_iff`）。 -/
def refine (t : RuleTerm) : RuleTerm := RuleTerm.and t trueTerm

/-- ⭐ **完善的语义方向**：完善后的约束成立 ⟹ 原约束成立。 -/
theorem holds_refine {t : RuleTerm} {e : Env} (h : (refine t).holds e) : t.holds e := by
  simpa [refine] using h

/-- **第一版 `υ` 的语义等价**（诚实的「不收紧」登记）：`υ t` 与 `t` 同真同假。 -/
theorem holds_refine_iff (t : RuleTerm) (e : Env) :
    (refine t).holds e ↔ t.holds e := by
  simp [refine]

/-! ### §5  ⭐ `∘`（组合）—— 取交 -/

/-- ⭐⭐⭐ **【`∘`（组合）：合取（取交）】** -/
def compose (a b : RuleTerm) : RuleTerm := RuleTerm.and a b

/-- ⭐ **组合的语义等价**：`compose a b` 成立 ⟺ `a` 与 `b` 都成立。 -/
theorem holds_compose_iff (a b : RuleTerm) (e : Env) :
    (compose a b).holds e ↔ (a.holds e ∧ b.holds e) :=
  Iff.rfl

/-- 组合在语法层可交换（因语义是合取）。 -/
theorem compose_comm_sem (a b : RuleTerm) : ∀ e : Env,
    (compose a b).holds e ↔ (compose b a).holds e := by
  intro e
  simp [compose, and_comm]

/-- 组合在语法层可结合（因语义是合取）。 -/
theorem compose_assoc_sem (a b d : RuleTerm) : ∀ e : Env,
    (compose (compose a b) d).holds e ↔ (compose a (compose b d)).holds e := by
  intro e
  simp [compose, and_assoc]

/-! ### §6  ⭐ `α`（抽象）—— 从实例产生规则

**语义**：「从实例产生规则」。这里的具体形态：
给定一个**具体环境** `e`（一个实例）与列数 `n`，
产生规则 `x₀ = e₀ ∧ x₁ = e₁ ∧ … ∧ x_{n-1} = e_{n-1}`。 -/

/-- ⭐⭐ **【`α`（抽象）：从实例 `e` 产生规则（前 `n` 个变量）】** -/
def alphaFrom (e : Env) : ℕ → RuleTerm
  | 0 => trueTerm
  | n + 1 => RuleTerm.and (RuleTerm.eq (RuleTerm.var n) (RuleTerm.const (e n)))
      (alphaFrom e n)

/-- ⭐ **`α` 的语义刻画**：从实例产生的规则在一环境上成立，
**当且仅当**该环境与前 `n` 个坐标上与该实例一致。 -/
theorem holds_alphaFrom_iff (e e' : Env) (n : ℕ) :
    (alphaFrom e n).holds e' ↔ ∀ i < n, e' i = e i := by
  induction n with
  | zero =>
      simp [alphaFrom]
  | succ n ih =>
      rw [alphaFrom, RuleTerm.holds, ih]
      constructor
      · rintro ⟨h0, hall⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact hall i hlt
        · subst heq; simpa using h0
      · intro hall
        refine ⟨?_, fun i hi => hall i (Nat.lt_trans hi (Nat.lt_succ_self n))⟩
        simpa using hall n (Nat.lt_succ_self n)

/-! ### §7  ⭐⭐⭐ 四算子在 `LawRule` 层的对应

⚠ `LawRule C X Y` **没有 `Inf` / `⊆` 实例**（它只是函数别名，
`⊆` 只在其值 `Set (Measure Y.Carrier)` 上有），
故以下定理全部写成**逐点**形式 `∀ c x, … ⊆ …` / `∀ c x, … = … ∩ …`。 -/

/-- ⭐⭐⭐ **【组合在 `LawRule` 层 = 逐点取交】**

`toLawRuleWith interp (compose a b)` 在每个 `(c, x)` 上等于两条允许集的交。

（对照 `LawRule.compose` 的定义 `fun c x => R₁ c x ∩ R₂ c x`：这里给出的是
**语法侧构造 `compose`** 与那个语义侧构造的**一致性**。） -/
theorem toLawRuleWith_compose
    (interp : Interp C X Y) (a b : RuleTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (compose a b) c x
      = toLawRuleWith interp a c x ∩ toLawRuleWith interp b c x := by
  ext μ
  simp [toLawRuleWith, compose]

/-- **组合在 `LawRule` 层的函数等式**（`funext` 形式，不依赖 `Inf` 实例）。 -/
theorem toLawRuleWith_compose_fun
    (interp : Interp C X Y) (a b : RuleTerm) :
    toLawRuleWith interp (compose a b)
      = fun c x => toLawRuleWith interp a c x ∩ toLawRuleWith interp b c x := by
  funext c x
  exact toLawRuleWith_compose interp a b c x

/-- ⭐⭐⭐ **【泛化在 `LawRule` 层 = 包含（更大）】**

`toLawRuleWith interp a` 逐点包含于 `toLawRuleWith interp (generalize a)`。

**⟹ 这是「`γ` = 放宽」在语义层的精确形式。** -/
theorem toLawRuleWith_generalize_subset
    (interp : Interp C X Y) (t : RuleTerm) :
    ∀ c x, toLawRuleWith interp t c x ⊆ toLawRuleWith interp (generalize t) c x := by
  intro c x μ h
  simp [toLawRuleWith, generalize]

/-- 泛化后的允许集**就是全集**（第一版 `γ` 的强度登记，机器可检验）。 -/
theorem toLawRuleWith_generalize_eq_univ
    (interp : Interp C X Y) (t : RuleTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (generalize t) c x = Set.univ := by
  ext μ
  simp [toLawRuleWith, generalize]

/-- ⭐⭐⭐ **【非平凡泛化 `loosen` 在 `LawRule` 层也是包含】** -/
theorem toLawRuleWith_loosen_subset
    (interp : Interp C X Y) (t : RuleTerm) :
    ∀ c x, toLawRuleWith interp t c x ⊆ toLawRuleWith interp (loosen t) c x := by
  intro c x μ h
  exact holds_loosen h

/-- ⭐⭐⭐ **【完善在 `LawRule` 层 = 包含（更小）】** -/
theorem toLawRuleWith_refine_subset
    (interp : Interp C X Y) (t : RuleTerm) :
    ∀ c x, toLawRuleWith interp (refine t) c x ⊆ toLawRuleWith interp t c x := by
  intro c x μ h
  exact holds_refine h

/-- **第一版 `υ` 的允许集相等**（与 `holds_refine_iff` 同一事实的集合形式）。 -/
theorem toLawRuleWith_refine_eq
    (interp : Interp C X Y) (t : RuleTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (refine t) c x = toLawRuleWith interp t c x := by
  ext μ
  simp [toLawRuleWith, refine]

/-- **`α` 在 `LawRule` 层的对应**：从实例 `e` 产生的规则，
其允许集恰是「把分布解释成与 `e` 在前 `n` 个坐标一致的分布」之集。 -/
theorem toLawRuleWith_alphaFrom
    (interp : Interp C X Y) (e : Env) (n : ℕ) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (alphaFrom e n) c x
      = {μ | ∀ i < n, interp c x μ i = e i} := by
  ext μ
  simp [toLawRuleWith, holds_alphaFrom_iff]

/-! ### §8  四算子的交互（`γ` / `υ` 与 `∘` 的相容性） -/

/-- **泛化与组合可交换到「先泛化再组合」**：
`compose (generalize a) b` 的允许集包含 `compose a b` 的允许集。 -/
theorem toLawRuleWith_compose_generalize_subset
    (interp : Interp C X Y) (a b : RuleTerm) :
    ∀ c x, toLawRuleWith interp (compose a b) c x
      ⊆ toLawRuleWith interp (compose (generalize a) b) c x := by
  intro c x μ h
  rw [toLawRuleWith_compose] at h ⊢
  exact ⟨toLawRuleWith_generalize_subset interp a c x h.1, h.2⟩

/-- **完善与组合可交换到「先完善再组合」**：
`compose (refine a) b` 的允许集包含于 `compose a b` 的允许集。 -/
theorem toLawRuleWith_compose_refine_subset
    (interp : Interp C X Y) (a b : RuleTerm) :
    ∀ c x, toLawRuleWith interp (compose (refine a) b) c x
      ⊆ toLawRuleWith interp (compose a b) c x := by
  intro c x μ h
  rw [toLawRuleWith_compose] at h ⊢
  exact ⟨toLawRuleWith_refine_subset interp a c x h.1, h.2⟩

/-! ===========================================================================
    §9  R-40 接线：四算子代数律（组合 / 泛化 / 完善）

    本节为 **R-40 Top 86-100 接线**新增（纯追加，不触碰 §1-§8 任何声明）。
    ⚠ 防同义反复：以下每条结论都不是前件的重述。
    =========================================================================== -/

/-- **组合的结合律（`holds` 语义层，三重形式）。** -/
theorem holds_compose_assoc_three (a b d : RuleTerm) (e : Env) :
    (compose (compose a b) d).holds e ↔ a.holds e ∧ b.holds e ∧ d.holds e := by
  rw [holds_compose_iff, holds_compose_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hd⟩; exact ⟨ha, hb, hd⟩
  · rintro ⟨ha, hb, hd⟩; exact ⟨⟨ha, hb⟩, hd⟩

/-- **泛化因子的组合吸收律**：泛化后与任何规则组合，泛化因子不提供约束。 -/
theorem holds_compose_generalize_left (a b : RuleTerm) (e : Env) :
    (compose (generalize a) b).holds e ↔ b.holds e := by
  rw [holds_compose_iff]
  exact ⟨fun h => h.2, fun h => ⟨holds_generalize_all a e, h⟩⟩

/-- **`loosen` 与 `compose` 的方向律（集合层）**：走 `loosen`，右侧不是全集。 -/
theorem toLawRuleWith_compose_loosen_subset
    (interp : Interp C X Y) (a b : RuleTerm) :
    ∀ c x, toLawRuleWith interp (compose a b) c x
      ⊆ toLawRuleWith interp (compose (loosen a) b) c x := by
  intro c x mu hm
  rw [toLawRuleWith_compose] at hm ⊢
  exact ⟨toLawRuleWith_loosen_subset interp a c x hm.1, hm.2⟩

/-- **`refine` 的幂等性（`LawRule` 层）**：连续两次完善不改变允许集。 -/
theorem toLawRuleWith_refine_refine
    (interp : Interp C X Y) (t : RuleTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (refine (refine t)) c x
      = toLawRuleWith interp (refine t) c x := by
  rw [toLawRuleWith_refine_eq, toLawRuleWith_refine_eq]

/-- **`alphaFrom` 的单调性**：列数增加 ⟹ 允许集缩小（方向性包含）。 -/
theorem toLawRuleWith_alphaFrom_subset {e : Env} {n m : ℕ} (hnm : n ≤ m)
    (interp : Interp C X Y) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (alphaFrom e m) c x
      ⊆ toLawRuleWith interp (alphaFrom e n) c x := by
  rw [toLawRuleWith_alphaFrom, toLawRuleWith_alphaFrom]
  intro mu hm i hi
  exact hm i (Nat.lt_of_lt_of_le hi hnm)

end RuleSyntaxOps
end Fate
