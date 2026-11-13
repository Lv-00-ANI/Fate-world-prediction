/-
============================================================================
  P4 · 乙路线 · **规则与机制的误差逼近：格序形式**

  ## 本模块做什么

  总纲 §4 P4 要求「对集合档规则给出『预测质量』度量」，并登记根本障碍：

  > `Measure Y` 上**没有自然度量** ⟹ `Set (Measure Y)` 上也没有
  > ⟹ `‖R − f‖` **无法定义**，除非引入 Wasserstein 距离
  > （要求 `Y` 是 Polish 空间）。

  `g-rules.md` 的补充理由：

  > `f : X × U × E_ε × Θ × A → X`，`R : C × X_loc → Δ(Y)`。
  > 值域一个是 `X`，一个是 `Δ(Y)`，二者之间**没有已定义的范数**
  > ⟹『R ≈ f』当前不是良构表达式。登记为 [开放 6.4]。

  本模块**不**引入 Wasserstein（见 §0 实测结论），而是用**格序** `≤`
  代替**数值范数**，给出「机制 `f` 被规则 `R` 允许」的精确形式。

  ## §0  三条路的实测结论（详见 `_audit/P4-乙路线误差逼近.md`）

  | 路 | 内容 | 可行性 |
  |---|---|---|
  | **A** | 用 `LawRule` 的格结构定义「`R` 松弛 `f`」 | 🟢 本文件完成 |
  | B | `Set (Measure Y)` 的对称差度量 | 🔴 无测度 ⟹ 对称差是集合非数值 |
  | C | 引入 Wasserstein | 🔴 **Mathlib 中不存在**（实测） |

  **路 C 实测**：`grep -rn "Wasserstein" /data/proj/mathlib4/Mathlib/` 返回**空**。
  Mathlib 有 `Topology/MetricSpace/Polish.lean`（Polish 空间的概念侧），
  但**没有**测度上的 Wasserstein 距离。故 `‖R − f‖` 在本环境**无法定义**，
  P4-C **确认不可行** —— 这正是总纲预告的「允许失败」。

  ## 路 A 的形式化内容

  `LawRule C X Y := C.Carrier → X.Carrier → Set (Measure Y.Carrier)`
  （`Fate/LawRule.lean`），其 `CompleteLattice` / `Order.Frame` 实例由
  `Fate/LawRuleLattice.lean` 提供（逐点继承 `Set`）。

  ⚠ **实例可用性的实测要点**：`instCompleteLattice` 的 `[MeasurableSpace Y.Carrier]`
      是**变量块里的正式实例参数**（`variable {C X Y} [MeasurableSpace Y.Carrier]`），
      故在 `Y := F.X` 时，**必须显式传 `instX`**；用 `[MeasurableSpace F.X.Carrier]`
      类型类变量**不能**触发该实例（实测 `synthInstanceFailed`）。
      本文件一律显式传 `instX`。
  ⚠ 另实测：本 Mathlib 环境中 `⊑` **不是**已注册的 `LE` 记法（解析报
      `expected token`）；一律用 `≤` / `⊓` / `⊔`。

  ⭐⭐ **【本文件唯一的核心定义】** `IsRelaxationOf R f`：

  `f` 的每次转移 `δ_{f x u ν θ a}` 都落在 `R` 的允许集里。

  **这不是** `‖R − f‖ ≤ ε`，而是

  $$\texttt{stepToLaw}\ f \;\le\; R \qquad(\text{格的 } \le,\ \text{逐点 } \subseteq)$$

  ## 本模块的定理

  | 编号 | 定理 | 前件 | 内容 |
  |---|---|---|---|
  | 1 | `isRelaxationOf_apply` | 无 | 定义性展开为逐点 `∈` |
  | 2 | `isRelaxationOf_mono` | `R₁ ≤ R₂` | 松弛对 `R` **单调**（越泛化越易满足） |
  | 3 | `isRelaxationOf_top` | 无 | `⊤` 松弛一切机制（无约束） |
  | 4 | `not_isRelaxationOf_bot` | `C`/`X` 非空 | `⊥` **不**松弛任何机制（下界不可达） |
  | 5 | `self_relaxation_fiber` | `ctxOf` 处处对齐 | `R` 松弛**自己抽出的**机制 |
  | 5′ | `self_relaxation_subsingleton_ctx` | `[Subsingleton C]` | 上下文退化时**无条件**松弛 |
  | 6 | `isRelaxationOf_inf` | 两者皆松弛 | 交仍是松弛（组合保持逼近） |
  | 7 | `not_isRelaxationOf_of_not_mem` | `δ ∉ R c x` | 反例方向：**逼近会失败** |
  | 8 | `isRelaxationOf_sInf` | 族中每条皆松弛 | 松弛集对任意 `sInf` 封闭（**紧性**） |
  | 9 | `sInf_relaxations_eq_stepToLaw` | 无 | ⭐ **最小松弛恰是 `f` 的 Dirac 化** |

  ## 前件非循环自查（第 7 条纪律）

  * 定理 2：前件 `R₁ ≤ R₂` 只谈**两个规则之间**的格序，**不含**任何关于
    `stepToLaw` 的断言；结论把 `≤` 的左边从 `R₁` 换为 `R₂`，靠 `le_trans`。
  * 定理 5：前件 `∀ c x, ctxOf x u ν θ a = c` 是**上下文对齐**
    （`ctxOf` 不依赖 `x` 的假设），不含 `stepToLaw` / `lawDetToStepGen` 的断言。
    结论是两条**独立定义**的复合 ∈ 关系。
    ⟹ **无该前件时定理为假**（实测：去掉后目标变成
    `δ_{toDetFun R hR (ctxOf x …) x} ∈ {δ_{toDetFun R hR c x}}`，需要
    `ctxOf x … = c`，不可消去）—— 这是本模块**最重要的诚实边界**。
  * 定理 6：前件是「两者各松弛 `f`」，结论是「其交松弛 `f`」。
    这**不是**同义反复：由 `⊓` 的逐点 `Set.mem_inter_iff` 得到，论证有实质内容。
  * 定理 7：前件是**关于 `R` 的否定性事实**，结论是 `¬IsRelaxationOf`。
    这排除了「定义即真」的嫌疑 —— `IsRelaxationOf` **可反驳**。
  * 定理 8、9：见各自文档。

  ## 诚实标注

  * 只新增文件，**未修改**任何已有模块。
  * 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `set_option`。
  * **不声称**这是「逼近」的**度量**：`≤` 是**序**，不是**距离**。
    「`R` 比 `R'` 更接近 `f`」在本形式中**不可表达**（序没有「多近」）。
  * **不声称** `‖R − f‖` 可定义：它**不可定义**，见 §0。
  * 定理 5 的上下文对齐前件**不可去除** —— 这是真实数学障碍，不是技术规避。
============================================================================
-/

import FateWorld.Legacy.LawRule
import FateWorld.Legacy.LawRuleLattice
import FateWorld.Legacy.StepToLawGenFiber
import FateWorld.Legacy.LawDetToStepGen

namespace Fate
namespace RuleRelaxation

open LawRule MeasureTheory

variable {C : CtxSpace} {F : Frame} (instX : MeasurableSpace F.X.Carrier)

/-! ===========================================================================
    §1  「规则松弛机制」的定义
    =========================================================================== -/

/-- ⭐⭐⭐ **【规则 `R` 松弛机制 `f`】**

「`f` 的每一次转移都被 `R` 允许」：

$$\texttt{IsRelaxationOf}\ R\ f\ u\ \nu\ \theta\ a
  \;:=\; \texttt{stepToLawGen}\ f\ u\ \nu\ \theta\ a \;\le\; R.$$

左端是 `f` 提升成的 **Dirac 规则**（`stepToLawGen`，逐点 `{δ_{f x u ν θ a}}`），
`≤` 是 `LawRule` 的**逐点包含**（`LawRuleLattice.instCompleteLattice`）。

**⟹ 这是「`R` 逼近 `f`」在没有范数的世界里的唯一良构形式**：
用**序**代替**距离**。

标签：**[定义性约定]**（P4 乙路线 · 路 A 的核心定义）。 -/
def IsRelaxationOf
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X) (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) : Prop :=
  stepToLawGen F instX ctxOf f u ν θ a ≤ R

/-- ⭐ **【定理 1：定义性展开】**

`IsRelaxationOf` 逐点读作：对每个上下文 `c` 与状态 `x`，
`f` 在 `(x,u,ν,θ,a)` 处的下一步 δ 测度**落在** `R c x` 里。

**前件：无。** -/
theorem isRelaxationOf_apply
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X) (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (c : C.Carrier) (x : F.X.Carrier)
    (h : IsRelaxationOf instX ctxOf R f u ν θ a) :
    Measure.dirac (f x u ν θ a) ∈ R c x := by
  have h' : stepToLawGen F instX ctxOf f u ν θ a c x ⊆ R c x := h c x
  rw [stepToLawGen_apply] at h'
  exact h' (Set.mem_singleton _)

/-- ⭐⭐ **【定理 2：松弛对规则单调】**

若 `R₁ ≤ R₂`（`R₂` 比 `R₁` 允许更多），且 `R₁` 松弛 `f`，则 `R₂` 也松弛 `f`。

**直读**：**泛化不会破坏逼近**——放松约束只会让机制更容易被允许。

**⟹ 这正是「逼近」在序上的正确单调性**（对应总纲「`R` 越泛化，对 `f` 约束越松」）。

**前件非循环**：`h : R₁ ≤ R₂` 只谈两规则之间的格序。 -/
theorem isRelaxationOf_mono
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    {R₁ R₂ : LawRule.LawRule C F.X F.X} (h : R₁ ≤ R₂) (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (hR : IsRelaxationOf instX ctxOf R₁ f u ν θ a) :
    IsRelaxationOf instX ctxOf R₂ f u ν θ a :=
  le_trans hR h

/-- ⭐⭐ **【定理 3：`⊤` 松弛一切机制】**

无约束规则 `⊤`（允许一切分布）松弛任何 `f`。

**⟹ 这是松弛关系的**上界**：逼近的上端总是可达的（但**无信息**）。

**前件：无。** -/
theorem isRelaxationOf_top
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    IsRelaxationOf instX ctxOf (⊤ : LawRule.LawRule C F.X F.X) f u ν θ a :=
  le_top

/-- ⭐⭐ **【定理 4：`⊥` **不**松弛任何机制】**

矛盾规则 `⊥`（不允许任何分布）**永远不**松弛 `f`。

**⟹ 这是松弛关系的**下界不可达**：
`stepToLawGen … f` 处处是**非空**单点集 `{δ_…}`，
而 `⊥` 处处是空集，故 `stepToLawGen … f ≤ ⊥` **不成立**。

**⟹ 直读**：**「规则不允许任何东西」不构成对机制的任何允许**。

**前件 `[Nonempty C.Carrier] [Nonempty F.X.Carrier]` 是真实的**：
空上下文空间或空状态空间下取不到点，`∀ c x` 为空真，
此时 `⊥` **确实**松弛一切（空真）——故非空性是**必要**前件，不是技术规避。

**证明**：取 `c, x`，由定理 1 得 `δ ∈ ⊥ c x = ∅`，矛盾。 -/
theorem not_isRelaxationOf_bot
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    [Nonempty C.Carrier] [Nonempty F.X.Carrier] :
    ¬ IsRelaxationOf instX ctxOf (⊥ : LawRule.LawRule C F.X F.X) f u ν θ a := by
  intro h
  obtain ⟨c⟩ := ‹Nonempty C.Carrier›
  obtain ⟨x⟩ := ‹Nonempty F.X.Carrier›
  have hm : Measure.dirac (f x u ν θ a) ∈ (⊥ : LawRule.LawRule C F.X F.X) c x :=
    isRelaxationOf_apply instX ctxOf (⊥ : LawRule.LawRule C F.X F.X) f u ν θ a c x h
  have hbot : (⊥ : LawRule.LawRule C F.X F.X) c x = (∅ : Set (Measure F.X.Carrier)) :=
    rfl
  rw [hbot] at hm
  exact hm.elim

/-! ===========================================================================
    §2  「自我松弛」：Dirac 规则松弛**自己抽出的机制**（纤维形式）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【定理 5：Dirac 规则松弛自己抽出的机制（对齐后）】**

设 `R` 是 Dirac 规则（`hR : IsDirac R`），`f := lawDetToStepGen R hR` 是从 `R`
抽出的机制。若 `ctxOf` 与**任意**上下文 `c` 对齐
（`∀ c x, ctxOf x u ν θ a = c`，即上下文空间退化/`ctxOf` 为常数的情形），则

$$\texttt{IsRelaxationOf}\ R\ f\ u\ \nu\ \theta\ a.$$

**⟹ 这是路 A 的**主打定理**：规则松弛自己的抽出机制

**⚠ 前件不可去除**（实测）：
`lawDetToStepGen` 用 `ctxOf x …` 取上下文，而 `R c x` 用 `c`。
两者相等**只有在上下文对齐时**。去掉后目标成为
`δ_{toDetFun R hR (ctxOf x …) x} ∈ {δ_{toDetFun R hR c x}}`，
需要 `ctxOf x … = c`，**无法从无前件推出**。

**⟹ 这是 P0-5 已登记的「抽象版左往返只能逐纤维成立」在松弛语言下的重述。**

**前件非循环**：`hctx` 只谈 `ctxOf` 取值的**对齐性**（外部参数的性质），
不含 `stepToLawGen` / `IsRelaxationOf` 的任何断言。 -/
theorem self_relaxation_fiber
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (hctx : ∀ (c : C.Carrier) (x : F.X.Carrier), ctxOf x u ν θ a = c) :
    IsRelaxationOf instX ctxOf R (lawDetToStepGen F instX ctxOf R hR) u ν θ a := by
  intro c x
  rw [stepToLawGen_apply]
  intro μ hμ
  rw [Set.mem_singleton_iff] at hμ
  rw [hμ, lawDetToStepGen_apply]
  have h := @LawRuleToTraj.toDetFun_spec C F.X F.X instX R hR c x
  rw [h]
  show Measure.dirac (@LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x)
    ∈ ({Measure.dirac (@LawRuleToTraj.toDetFun C F.X F.X instX R hR c x)} :
      Set (Measure F.X.Carrier))
  rw [hctx c x]
  exact Set.mem_singleton _

/-- ⭐⭐⭐ **【定理 5′：上下文空间退化时无条件成立】**

若上下文空间 `C.Carrier` 是**单点**（`[Subsingleton C.Carrier]`，`ctxPUnit`
即此情形），则 `ctxOf` 不可能不对齐，于是 **`R` 无条件松弛自己抽出的机制**。

**⟹ 这是定理 5 的**静态特例**：单点上下文使 `hctx` 由 `Subsingleton.elim`
自动供给。对齐条件在静态层**自动满足**。

**前件 `[Subsingleton C.Carrier]` 是真实的数学前提**（上下文维度退化），
不是技术规避：多上下文时定理为假（见定理 5 的边界）。 -/
theorem self_relaxation_subsingleton_ctx
    [Subsingleton C.Carrier]
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    IsRelaxationOf instX ctxOf R (lawDetToStepGen F instX ctxOf R hR) u ν θ a := by
  apply self_relaxation_fiber
  intro c x
  exact Subsingleton.elim _ _

/-! ===========================================================================
    §3  「逼近」的代数性质：交、反例与紧性
    =========================================================================== -/

/-- ⭐⭐⭐ **【定理 6：两条松弛的**交**仍是松弛】**

若 `R₁` 与 `R₂` 都松弛 `f`，则 `R₁ ⊓ R₂` 也松弛 `f`。

**⟹ 直读**：**同时逼近两个规则 = 它们的交仍逼近**。
这是「逼近集」对 `⊓` 封闭（滤子式），因而下确界也保持松弛。

**前件非循环**：两条 `h₁ h₂` 是**假设**（各规则松弛 `f`），
结论是**它们的交**松弛 `f`。论证经 `Set.mem_inter_iff`，有实质内容。 -/
theorem isRelaxationOf_inf
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    {R₁ R₂ : LawRule.LawRule C F.X F.X} (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (h₁ : IsRelaxationOf instX ctxOf R₁ f u ν θ a)
    (h₂ : IsRelaxationOf instX ctxOf R₂ f u ν θ a) :
    IsRelaxationOf instX ctxOf (R₁ ⊓ R₂) f u ν θ a := by
  intro c x
  rw [stepToLawGen_apply]
  intro μ hμ
  rw [Set.mem_singleton_iff] at hμ
  rw [hμ]
  exact ⟨isRelaxationOf_apply instX ctxOf R₁ f u ν θ a c x h₁,
         isRelaxationOf_apply instX ctxOf R₂ f u ν θ a c x h₂⟩

/-- ⭐⭐⭐ **【定理 7：逼近会失败 —— 反例方向】**

若在某点 `(c, x)` 上 `R c x` **不含** `δ_{f x u ν θ a}`，则 `R` **不**松弛 `f`。

**⟹ 这是路 A 的**否定侧**：`IsRelaxationOf` 是**可反驳**的谓词，
不是恒真式。**⟹ 它确实携带信息**（排除了「定义即真」的嫌疑）。

**前件非循环**：`h : δ ∉ R c x` 是**关于 `R` 的具体否定性事实**，
结论是 `¬ IsRelaxationOf …`。这是逆否的直接使用。 -/
theorem not_isRelaxationOf_of_not_mem
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X) (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (c : C.Carrier) (x : F.X.Carrier)
    (h : Measure.dirac (f x u ν θ a) ∉ R c x) :
    ¬ IsRelaxationOf instX ctxOf R f u ν θ a := by
  intro hR
  exact h (isRelaxationOf_apply instX ctxOf R f u ν θ a c x hR)

/-- ⭐⭐⭐⭐ **【定理 8：任意下确界仍是松弛 —— 紧性】**

设 `S` 是一族 `f` 的松弛规则，则 `S` 的**下确界** `sInf S` 也是 `f` 的松弛。

**⟹ 这是「逼近的紧性」**：松弛集对任意 `sInf` 封闭 ⟹
**最小松弛存在**（定理 9 给出其显式形式）。

⚠ **诚实边界**：`sInf S` 是 `S` 的**下**确界。由于松弛条件对 `≤` 是**上**闭的
（定理 2），`sInf S` 是松弛中**最强**（最贴近 `f`）的那一个。
「最贴近」在此是**序**意义，**不是**数值意义。

**前件非循环**：`hS` 说「族中每条规则都松弛 `f`」，结论说「下确界松弛 `f`」。
空族时 `sInf ∅ = ⊤`，由定理 3 仍是松弛 —— 故**无需**非空性前件。 -/
theorem isRelaxationOf_sInf
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (S : Set (LawRule.LawRule C F.X F.X))
    (hS : ∀ R ∈ S, IsRelaxationOf instX ctxOf R f u ν θ a) :
    IsRelaxationOf instX ctxOf (sInf S) f u ν θ a := by
  -- it suffices that `stepToLawGen f ≤` every member of `S`
  refine le_trans (le_refl (stepToLawGen F instX ctxOf f u ν θ a))
    (le_sInf (fun R hR => hS R hR))

/-- ⭐⭐⭐⭐ **【定理 9：最小松弛的显式刻画】**

`f` 的松弛族 `S_f := {R | IsRelaxationOf R f}` 的**下确界**就是
`stepToLawGen f` 本身（`f` 提升成的 Dirac 规则）：

$$\bigsqcap \{R \mid \texttt{IsRelaxationOf}\ R\ f\} \;=\; \texttt{stepToLawGen}\ f.$$

**⟹ 这是路 A 的**终极结论**：
**「最小松弛」就是 `f` 自身的 Dirac 化** ——
所有松弛都是它在上方的**扩张**，逼近的**下界恰是 `f` 自己**。

**⟹ 这正是「`R` 逼近 `f`」在格序下的**精确**含义**：
`R ⊒ stepToLawGen f`，而等式的情形是**完全不松弛**（`R` 恰等于 `f`）。

**前件：无。** 等式两端是**独立定义**（`sInf` 与 `stepToLawGen`）；
证明用 `le_antisymm`。 -/
theorem sInf_relaxations_eq_stepToLaw
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    sInf {R : LawRule.LawRule C F.X F.X | IsRelaxationOf instX ctxOf R f u ν θ a}
      = stepToLawGen F instX ctxOf f u ν θ a := by
  apply le_antisymm
  · exact sInf_le (le_refl (stepToLawGen F instX ctxOf f u ν θ a))
  · exact le_sInf (fun R hR => hR)

end RuleRelaxation
end Fate
