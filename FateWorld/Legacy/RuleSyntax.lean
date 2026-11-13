import FateWorld.Legacy.LawRule
import FateWorld.Legacy.Frame

/-! ===========================================================================
  规则核心链 · **IR 语法层**（乙-1）

  ## 本模块做什么

  把「规则」从**数学语义**（`Set (Measure Y)`）升级为 **CIC 语法项**
  （一个 `inductive` 类型），并给出**语义解释** `denote` / `toLawRuleWith`。

  ## 为什么这满足「直接基于 CIC 和三条公理」

  * `RuleTerm` 是 Lean 的 **`inductive` 类型** ⟹ 本身就在 CIC 里；
  * `eval` / `holds` / `toLawRuleWith` 都是**普通 `def`** ⟹ 它们的每条
    等式定理只用 `rfl`（不引新公理、不用 `sorry`）；
  * 因此「IR 嵌入 Lean」不是翻译，而是**同一个类型论内的构造**。

  ## 本模块的定理（第一版）

  | # | 声明 | 内容 |
  |---|---|---|
  | 1 | `RuleTerm` | 规则的 CIC 语法项（`inductive`） |
  | 2 | `Env` | 变量求值环境 |
  | 3 | `RuleTerm.eval` | 算术语义：语法项 → 实数 |
  | 4 | `RuleTerm.holds` | 断言语义：语法项 → `Prop` |
  | 5 | `eval_*` / `holds_*` | 各构造子的语义等式（`rfl`） |
  | 6 | `toLawRuleWith` | ⭐ 语法项 → `LawRule`（**IR --语义--> LawRule**） |
  | 7 | `toLawRuleWith_apply` | 逐点展开（`rfl`） |

  ## 诚实边界（务必先读）

  1. **只做算术与逻辑约束**：`const / var / add / mul / eq / le / lt /
     and / or / not`。**无概率、无微分、无积分、无归纳迭代**。
  2. **`interp : Measure Y.Carrier → Env` 是参数，未定**。
     本模块只声明「若给定分布→环境的解释，则约束项可解释为 `LawRule`」，
     **不构造任何具体的 `interp`**。这是「桥的接口」，不是桥的实现。
  3. **未做提取（→ 可执行代码）**，**未做四算子**。那是乙-2 / 乙-5。
  4. **`RuleTerm` 覆盖范围与 `规则载体架构-IR.md` §2.2 的对照，见
     `_audit/IR-1-规则CIC语法层.md`。**
     ⚠ 该文档在仓库内**只有 §7（65 行）**，**不存在 §2.2 要素表**；
     故对照表是对照「`LawRule.lean` §0 已列出的科学形式」做的，已如实登记。

  本模块**不修改任何既有模块**，只新建。
============================================================================ -/

namespace Fate
namespace RuleSyntax

/- `LawRule` 活在下游命名空间 `Fate.LawRule` 内，这里打开以便引用。 -/
open Fate.LawRule

/-! ### §1  变量环境 -/

/-- **变量环境**：变量下标 ↦ 实数。

约定（第一版）：规则里出现的自由变量用自然数编号，
`Env` 给出每个编号的取值。**如何把状态 / 上下文 / 分布编码成编号，
不在本模块范围内**（见 `interp`）。 -/
abbrev Env := ℕ → ℝ

/-! ### §2  规则的 CIC 语法项 -/

/-- **规则的 CIC 语法项**（第一版）。

这是一个 `inductive` 类型 ⟹ 它**本身就在 CIC 内**，
所以「IR 嵌入 Lean」不需要翻译层。

| 构造子 | 科学形式 |
|---|---|
| `const c` | 数值常数 |
| `var n` | 变量 $x_n$ |
| `add a b` | $a + b$ |
| `mul a b` | $a \cdot b$ |
| `eq a b` | 等式约束 $a = b$ |
| `le a b` | 不等式约束 $a \le b$ |
| `lt a b` | 严格不等式 $a < b$ |
| `and a b` | 合取 |
| `or a b` | 析取 |
| `not a` | 否定 |

**⚠ 第一版未包含**：`prob`（概率声明）、`deriv`（求导）、
`integ`（积分）、`iter`（归纳迭代）、`fn`（λ 抽象）。
这些需要 `Measure` / 极限 / 递归结构，留到乙-2。 -/
inductive RuleTerm : Type
  /-- 数值常数 -/
  | const (c : ℝ) : RuleTerm
  /-- 变量（按下标取环境中的值） -/
  | var (n : ℕ) : RuleTerm
  /-- 加法 -/
  | add (a b : RuleTerm) : RuleTerm
  /-- 乘法 -/
  | mul (a b : RuleTerm) : RuleTerm
  /-- 等式约束 `a = b` -/
  | eq (a b : RuleTerm) : RuleTerm
  /-- 不等式约束 `a ≤ b` -/
  | le (a b : RuleTerm) : RuleTerm
  /-- 严格不等式约束 `a < b` -/
  | lt (a b : RuleTerm) : RuleTerm
  /-- 合取 -/
  | and (a b : RuleTerm) : RuleTerm
  /-- 析取 -/
  | or (a b : RuleTerm) : RuleTerm
  /-- 否定 -/
  | not (a : RuleTerm) : RuleTerm

/-! ### §3  语义（第一版）

分**两个**函数，避免「算术子项在断言位置」与「断言子项在算术位置」的
无意义情形被含混地并进同一个返回类型：

* `eval  : RuleTerm → Env → ℝ`    —— 算术语义；
* `holds : RuleTerm → Env → Prop` —— 断言语义。

两者在**不属于自己的构造子上**给出**显式约定值**
（`eval` 给 `0`，`holds` 给 `True`）。
这不是「占位」意义上的假语义，而是**登记在案的约定**：
这类项在 Well-Formed 的 IR 程序中不出现，
约定值只保证函数在全部构造子上是**全函数**（Lean 的 `def` 要求穷尽）。 -/

/-- **算术语义**：把语法项解释成实数。

`const / var / add / mul` 有意义；其余构造子（断言类）在算术位置
按约定给 `0`。 -/
def RuleTerm.eval : RuleTerm → Env → ℝ
  | .const c, _ => c
  | .var n, e => e n
  | .add a b, e => a.eval e + b.eval e
  | .mul a b, e => a.eval e * b.eval e
  | _, _ => 0

/-- **断言语义**：把语法项解释成 `Prop`。

`eq / le / lt / and / or / not` 有意义；其余（算术类）在断言位置
按约定给 `True`。 -/
def RuleTerm.holds : RuleTerm → Env → Prop
  | .eq a b, e => a.eval e = b.eval e
  | .le a b, e => a.eval e ≤ b.eval e
  | .lt a b, e => a.eval e < b.eval e
  | .and a b, e => a.holds e ∧ b.holds e
  | .or a b, e => a.holds e ∨ b.holds e
  | .not a, e => ¬ a.holds e
  | _, _ => True

/-! ### §4  语义等式（全部 `rfl`） -/

@[simp] theorem eval_const (c : ℝ) (e : Env) : (RuleTerm.const c).eval e = c := rfl

@[simp] theorem eval_var (n : ℕ) (e : Env) : (RuleTerm.var n).eval e = e n := rfl

@[simp] theorem eval_add (a b : RuleTerm) (e : Env) :
    (RuleTerm.add a b).eval e = a.eval e + b.eval e := rfl

@[simp] theorem eval_mul (a b : RuleTerm) (e : Env) :
    (RuleTerm.mul a b).eval e = a.eval e * b.eval e := rfl

@[simp] theorem holds_eq (a b : RuleTerm) (e : Env) :
    (RuleTerm.eq a b).holds e = (a.eval e = b.eval e) := rfl

@[simp] theorem holds_le (a b : RuleTerm) (e : Env) :
    (RuleTerm.le a b).holds e = (a.eval e ≤ b.eval e) := rfl

@[simp] theorem holds_lt (a b : RuleTerm) (e : Env) :
    (RuleTerm.lt a b).holds e = (a.eval e < b.eval e) := rfl

@[simp] theorem holds_and (a b : RuleTerm) (e : Env) :
    (RuleTerm.and a b).holds e = (a.holds e ∧ b.holds e) := rfl

@[simp] theorem holds_or (a b : RuleTerm) (e : Env) :
    (RuleTerm.or a b).holds e = (a.holds e ∨ b.holds e) := rfl

@[simp] theorem holds_not (a : RuleTerm) (e : Env) :
    (RuleTerm.not a).holds e = ¬ a.holds e := rfl

/-! ### §5  ⭐ 核心桥：语法项 → `LawRule`（**IR --语义--> LawRule**）

`LawRule C X Y := C.Carrier → X.Carrier → Set (Measure Y.Carrier)`，
而 `RuleTerm.holds : RuleTerm → Env → Prop`。

**缺的一环是「分布 ↦ 环境」**。本模块**不发明**这一环，
而是把它做成**显式参数** `interp`：

* `interp` 把这个 `(c, x)` 下**候选的下一状态分布** `μ` 读成一个环境；
* `t.holds (interp μ)` 说「在这个环境中，约束 `t` 成立」；
* 于是 `t` 允许的分布集正是 `{μ | t.holds (interp μ)}`。

这样「IR → LawRule」变成**定义性的映射**，而「`interp` 该是什么」
是一个**可见的、可审计的**问题，而不是被藏起来的默认假设。 -/

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/- 注：`Y : OutSpace = StateSpace` 已自带 `MeasurableSpace Y.Carrier` 实例字段，
所以上行的显式绑定是**冗余但无害**的（会产生一条 overlapping-instances 警告）。
这**遵从本仓既有约定**：`Fate/LawRule.lean:78` 与 `Fate/LawRuleToTraj.lean:78`
均用完全相同的手法，且同样触发该警告。为保证下游可直接套用既有引理，
本模块不偏离该约定。 -/

/-- ⭐⭐⭐⭐ **【语法项的语义解释：`RuleTerm` → `LawRule`】**

给定「分布 → 环境」的解释 `interp`（依赖上下文 `c` 与状态 `x`），
约束项 `t` 解释为：**允许所有使 `t` 成立的分布**。

⚠ `interp` 是**参数**：本模块不构造它，也不声称它存在。
它的具体形式属于乙-2（需要把状态空间嵌入 `ℝ` 或约定编号）。 -/
def toLawRuleWith (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : RuleTerm) : LawRule C X Y :=
  fun c x => {μ | t.holds (interp c x μ)}

/-- **逐点展开**：`toLawRuleWith` 的成员判据（定义性）。 -/
@[simp] theorem toLawRuleWith_apply
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : RuleTerm) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier) :
    μ ∈ toLawRuleWith interp t c x ↔ t.holds (interp c x μ) :=
  Iff.rfl

/-- **不存在空约束**：若约束在环境 `e` 下成立，则任何 `interp` 映到 `e` 的分布都被允许。

这是桥的**正确性方向**（soundness 的语法侧）：约束成立 ⟹ 分布不被排除。 -/
theorem mem_toLawRuleWith_of_holds
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : RuleTerm) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier) (h : t.holds (interp c x μ)) :
    μ ∈ toLawRuleWith interp t c x :=
  h

/-- **否定的方向**：约束不成立 ⟹ 分布被排除。 -/
theorem not_mem_toLawRuleWith_of_not_holds
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : RuleTerm) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier) (h : ¬ t.holds (interp c x μ)) :
    μ ∉ toLawRuleWith interp t c x :=
  h

/-- **合取 = 取交**：`and` 的语法结构在语义侧对应允许集求交。

这是「语法层的组合子 ↔ 语义层的集合运算」的第一条对应，
也是乙-2 中「规则组合 `∘` = 取交」的语法源头。 -/
theorem toLawRuleWith_and
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (a b : RuleTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (RuleTerm.and a b) c x
      = toLawRuleWith interp a c x ∩ toLawRuleWith interp b c x := by
  ext μ
  simp [toLawRuleWith, RuleTerm.holds]

/-- **析取 = 取并**。 -/
theorem toLawRuleWith_or
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (a b : RuleTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (RuleTerm.or a b) c x
      = toLawRuleWith interp a c x ∪ toLawRuleWith interp b c x := by
  ext μ
  simp [toLawRuleWith, RuleTerm.holds]

/-- **全称约束 = 全集**：算术子项在断言位置按约定为 `True`，
故其允许集是全集（「无约束」）。 -/
theorem toLawRuleWith_const
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (k : ℝ) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (RuleTerm.const k) c x = Set.univ := by
  ext μ
  simp [toLawRuleWith, RuleTerm.holds]

/-- **`interp` 的逐点函数性**：同一约束项，若两个 `interp` 在某个 `μ` 上给出同一环境，
则 `μ` 的允许性一致。这保证「换 `interp` 不改语法」。 -/
theorem toLawRuleWith_congr_point
    (interp₁ interp₂ : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : RuleTerm) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier)
    (h : interp₁ c x μ = interp₂ c x μ) :
    (μ ∈ toLawRuleWith interp₁ t c x ↔ μ ∈ toLawRuleWith interp₂ t c x) := by
  simp [toLawRuleWith, h]

/-! ### §6  语法层的 `Prop` 侧：约束的等价与单调性 -/

/-- **`and` 的消除**（语法侧）。 -/
theorem holds_and_iff (a b : RuleTerm) (e : Env) :
    (RuleTerm.and a b).holds e ↔ (a.holds e ∧ b.holds e) :=
  Iff.rfl

/-- **`not` 的双重否定**：语法上的 `not (not t)` 在语义上还原（经典逻辑下）。 -/
theorem holds_not_not (a : RuleTerm) (e : Env) :
    (RuleTerm.not (RuleTerm.not a)).holds e ↔ a.holds e := by
  simp [RuleTerm.holds]

/-- **算术项的求值只依赖自由变量**：`eval` 在 `add` / `mul` 上的合成律。 -/
theorem eval_add_mul (a b c : RuleTerm) (e : Env) :
    (RuleTerm.add (RuleTerm.mul a b) c).eval e = a.eval e * b.eval e + c.eval e := rfl

end RuleSyntax
end Fate
