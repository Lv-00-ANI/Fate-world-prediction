import FateWorld.FateV2.Rules.RuleSyntax
/-!
  # Rules · RuleSyntaxGen

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RuleSyntaxGen.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RuleSyntax
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  规则核心链 · **IR 语法层的线性有序域泛化**（GEN-1 审计 §3 排名 1）

  ## 本模块做什么

  `Fate/RuleSyntax.lean` 把 IR 语法固化在 `ℝ` 上
  （`abbrev Env := ℕ → ℝ`，`RuleTerm.const (c : ℝ)`）。
  本模块**新增**一个对任意线性有序域参数化的语法类型 `TermK K` 与语义
  `TermK.eval` / `TermK.holds`，并证明：**在 `K = ℝ` 时，泛化版与 `ℝ` 版逐点一致**
  （`TermK.toRuleTerm_eval` / `TermK.toRuleTerm_holds`）。

  ## ⚠ 关于类名（诚实说明）

  任务书要求参数化到 `LinearOrderedField`。**本仓库的 Mathlib 快照
  （v4.35.0）已完成有序代数结构的类层级重构**：`LinearOrderedField` 与
  `LinearOrderedCommRing` 这两个类**已不存在**（`#check` 报 unknown identifier）。
  现行写法是三个假设的组合：

  ```
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  ```

  本模块**不使用任何缩写**，直接把这三个假设作为 binder 写在每个声明上：

  ```
  {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  ```

  这**不是**回避：该组合就是该快照下「`K` 是线性有序域」的唯一写法，
  `ℝ` 与 `ℚ` 都满足（见文末 `demo_le` / `demo_le_rat`）。

  ## 为什么必须新建 `TermK` 而不是复用 `RuleTerm`？

  `RuleTerm.const` 存的是**具体的 `ℝ`**。`ℝ → K` 对任意 `K` **没有可计算映射**
  （`ℝ` 是 Cauchy 完备 Archimedean 域；`K` 可以是 `ℚ`、有限域的有序扩张、
  非 Archimedean 域……）。所以「把 `RuleTerm` 直接在 `K` 上求值」不可实现。
  唯一正确的做法是：**常量位置直接存 `K`** 的新语法类型 `TermK K`。

  这不是「另起炉灶」：`TermK ℝ` 与 `RuleTerm` 之间有**结构翻译**
  `TermK.toRuleTerm`，且本模块证明二者的 `eval` / `holds` 完全一致。

  ## 本模块的声明

  | # | 声明 | 内容 |
  |---|---|---|
  | 1 | `EnvK` | `ℕ → K`，任意线性有序域上的环境 |
  | 3 | `TermK` | 泛化的 CIC 语法项（`const` 存 `K`） |
  | 4 | `TermK.eval` | 泛化算术语义 `TermK K → EnvK K → K` |
  | 5 | `TermK.holds` | 泛化断言语义 `TermK K → EnvK K → Prop` |
  | 6 | `TermK.eval_*` / `TermK.holds_*` | 各构造子的语义等式（`rfl`） |
  | 7 | `TermK.toRuleTerm` | `TermK ℝ → RuleTerm` 的结构翻译 |
  | 8 | `TermK.toRuleTerm_eval` | ⭐ `(t.toRuleTerm).eval e = t.eval e` |
  | 9 | `TermK.toRuleTerm_holds` | ⭐ `(t.toRuleTerm).holds e ↔ t.holds e` |
  | 10 | `TermK.demo_le` / `demo_le_toRuleTerm` | 非空性：同一语句两路径都成立 |

  ## 诚实边界

  * **只做加法与乘法**（与 `RuleTerm` 一致），无减法 / 除法 / 幂。
    因此泛化假设里的 `Field` 部分**尚未被任何定义或定理消耗**——
    `+` / `*` 与序已足够。保留完整假设是为了让下游（含有限域算术）
    能直接复用签名；`Field` 的逆元结构在当前定理中未被使用。
  * **一致性定理只对 `K = ℝ` 陈述**。对一般 `K` 无「与 `ℝ` 版一致」可言
    （`TermK K` 与 `RuleTerm` 甚至不同型）。
  * 未做提取，未做 `LawRule` 桥的泛化（`toLawRuleWith` 仍锁在 `Env`）。
  * 全部定理零 `sorry` / 零 `admit` / 零新增 `axiom`。
  ======================================================================== -/

namespace FateV2.Rules
namespace RuleSyntax
namespace Gen

open RuleSyntax (RuleTerm)

/-- **泛化的求值环境**：变量 ↦ 任意线性有序域 `K` 的元素。 -/
abbrev EnvK (K : Type _) [Field K] [LinearOrder K] [IsStrictOrderedRing K] := ℕ → K

/-- **泛化的语法项**：与 `RuleTerm` 同构，但常量位置直接存 `K`

（`RuleTerm.const` 存 `ℝ`，无法转到任意 `K`，故不能复用）。 -/
inductive TermK (K : Type _) : Type _
  /-- 数值常数（直接存目标域的常量） -/
  | const (c : K) : TermK K
  /-- 变量（按下标取环境中的值） -/
  | var (n : ℕ) : TermK K
  /-- 加法 -/
  | add (a b : TermK K) : TermK K
  /-- 乘法 -/
  | mul (a b : TermK K) : TermK K
  /-- 等式约束 `a = b` -/
  | eq (a b : TermK K) : TermK K
  /-- 不等式约束 `a ≤ b` -/
  | le (a b : TermK K) : TermK K
  /-- 严格不等式约束 `a < b` -/
  | lt (a b : TermK K) : TermK K
  /-- 合取 -/
  | and (a b : TermK K) : TermK K
  /-- 析取 -/
  | or (a b : TermK K) : TermK K
  /-- 否定 -/
  | not (a : TermK K) : TermK K

/-! ### 语义

与 `RuleSyntax` 的 §3 完全同构：
算术位置遇到断言子项按约定给 `0`，断言位置遇到算术子项按约定给 `True`。 -/

/-- **泛化算术语义**：把语法项解释成 `K` 的元素。

`const / var / add / mul` 有意义；其余构造子（断言类）在算术位置
按约定给 `0`（与 `RuleTerm.eval` 的约定一致）。 -/
def TermK.eval {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    TermK K → EnvK K → K
  | .const c, _ => c
  | .var n, e => e n
  | .add a b, e => a.eval e + b.eval e
  | .mul a b, e => a.eval e * b.eval e
  | _, _ => 0

/-- **泛化断言语义**：把语法项解释成 `Prop`。

`eq / le / lt / and / or / not` 有意义；其余（算术类）在断言位置
按约定给 `True`（与 `RuleTerm.holds` 的约定一致）。 -/
def TermK.holds {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    TermK K → EnvK K → Prop
  | .eq a b, e => a.eval e = b.eval e
  | .le a b, e => a.eval e ≤ b.eval e
  | .lt a b, e => a.eval e < b.eval e
  | .and a b, e => a.holds e ∧ b.holds e
  | .or a b, e => a.holds e ∨ b.holds e
  | .not a, e => ¬ a.holds e
  | _, _ => True

/-! ### 语义等式（全部 `rfl`，对任意线性有序域） -/

variable {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

@[simp] theorem TermK.eval_const (c : K) (e : EnvK K) :
    (TermK.const c).eval e = c := rfl

@[simp] theorem TermK.eval_var (n : ℕ) (e : EnvK K) :
    (TermK.var n).eval e = e n := rfl

@[simp] theorem TermK.eval_add (a b : TermK K) (e : EnvK K) :
    (TermK.add a b).eval e = a.eval e + b.eval e := rfl

@[simp] theorem TermK.eval_mul (a b : TermK K) (e : EnvK K) :
    (TermK.mul a b).eval e = a.eval e * b.eval e := rfl

@[simp] theorem TermK.holds_eq (a b : TermK K) (e : EnvK K) :
    (TermK.eq a b).holds e ↔ (a.eval e = b.eval e) := Iff.rfl

@[simp] theorem TermK.holds_le (a b : TermK K) (e : EnvK K) :
    (TermK.le a b).holds e ↔ (a.eval e ≤ b.eval e) := Iff.rfl

@[simp] theorem TermK.holds_lt (a b : TermK K) (e : EnvK K) :
    (TermK.lt a b).holds e ↔ (a.eval e < b.eval e) := Iff.rfl

@[simp] theorem TermK.holds_and (a b : TermK K) (e : EnvK K) :
    (TermK.and a b).holds e ↔ (a.holds e ∧ b.holds e) := Iff.rfl

@[simp] theorem TermK.holds_or (a b : TermK K) (e : EnvK K) :
    (TermK.or a b).holds e ↔ (a.holds e ∨ b.holds e) := Iff.rfl

@[simp] theorem TermK.holds_not (a : TermK K) (e : EnvK K) :
    (TermK.not a).holds e ↔ ¬ a.holds e := Iff.rfl

/-! ### 与 `ℝ` 版的一致性

`TermK ℝ → RuleTerm` 是**纯语法翻译**（常量 `ℝ` 直接搬运，构造子一一对应）。 -/

/-- **`ℝ` 版嵌入**：把 `TermK ℝ` 翻译成 `RuleTerm`（构造子一一对应）。 -/
def TermK.toRuleTerm : TermK ℝ → RuleTerm
  | .const c => .const c
  | .var n => .var n
  | .add a b => .add a.toRuleTerm b.toRuleTerm
  | .mul a b => .mul a.toRuleTerm b.toRuleTerm
  | .eq a b => .eq a.toRuleTerm b.toRuleTerm
  | .le a b => .le a.toRuleTerm b.toRuleTerm
  | .lt a b => .lt a.toRuleTerm b.toRuleTerm
  | .and a b => .and a.toRuleTerm b.toRuleTerm
  | .or a b => .or a.toRuleTerm b.toRuleTerm
  | .not a => .not a.toRuleTerm

/-- **一致性（算术侧）**：泛化求值在 `K = ℝ` 时与 `ℝ` 版求值完全相同。 -/
theorem TermK.toRuleTerm_eval (t : TermK ℝ) (e : EnvK ℝ) :
    (t.toRuleTerm).eval e = t.eval e := by
  induction t with
  | const c => rfl
  | var n => rfl
  | add a b iha ihb => simp only [TermK.toRuleTerm, RuleTerm.eval, TermK.eval, iha, ihb]
  | mul a b iha ihb => simp only [TermK.toRuleTerm, RuleTerm.eval, TermK.eval, iha, ihb]
  | eq a b iha ihb => rfl
  | le a b iha ihb => rfl
  | lt a b iha ihb => rfl
  | and a b iha ihb => rfl
  | or a b iha ihb => rfl
  | not a iha => rfl

/-- **一致性（断言侧）**：泛化判定在 `K = ℝ` 时与 `ℝ` 版判定完全相同。

这是本模块最重要的定理：它把「泛化版」钉死在既有 `ℝ` 版上
（反方向：泛化没有偷偷改语义）。 -/
theorem TermK.toRuleTerm_holds (t : TermK ℝ) (e : EnvK ℝ) :
    (t.toRuleTerm).holds e ↔ t.holds e := by
  induction t with
  | const c => exact Iff.rfl
  | var n => exact Iff.rfl
  | add a b iha ihb => exact Iff.rfl
  | mul a b iha ihb => exact Iff.rfl
  | eq a b iha ihb =>
      show (a.toRuleTerm).eval e = (b.toRuleTerm).eval e ↔ a.eval e = b.eval e
      rw [a.toRuleTerm_eval, b.toRuleTerm_eval]
  | le a b iha ihb =>
      show (a.toRuleTerm).eval e ≤ (b.toRuleTerm).eval e ↔ a.eval e ≤ b.eval e
      rw [a.toRuleTerm_eval, b.toRuleTerm_eval]
  | lt a b iha ihb =>
      show (a.toRuleTerm).eval e < (b.toRuleTerm).eval e ↔ a.eval e < b.eval e
      rw [a.toRuleTerm_eval, b.toRuleTerm_eval]
  | and a b iha ihb =>
      show ((a.toRuleTerm).holds e ∧ (b.toRuleTerm).holds e) ↔ (a.holds e ∧ b.holds e)
      rw [iha, ihb]
  | or a b iha ihb =>
      show ((a.toRuleTerm).holds e ∨ (b.toRuleTerm).holds e) ↔ (a.holds e ∨ b.holds e)
      rw [iha, ihb]
  | not a iha =>
      show ¬ (a.toRuleTerm).holds e ↔ ¬ a.holds e
      rw [iha]

/-! ### 非空性：泛化版在 `K = ℝ` 上的实例 -/

/-- 语句 `x₀ + x₀ ≤ 1 * 2` 在 `x₀ = 0` 下成立（走泛化版路径）。 -/
theorem TermK.demo_le :
    (TermK.le (TermK.add (TermK.var 0) (TermK.var 0))
      (TermK.mul (TermK.const (1 : ℝ)) (TermK.const 2))).holds
      (fun _ => 0) := by
  simp

/-- 同一语句走 `ℝ` 版路径（经 `toRuleTerm`）也成立：跨版本一致。 -/
theorem TermK.demo_le_toRuleTerm :
    ((TermK.le (TermK.add (TermK.var 0) (TermK.var 0))
      (TermK.mul (TermK.const (1 : ℝ)) (TermK.const 2))).toRuleTerm).holds
      (fun _ => 0) := by
  rw [TermK.toRuleTerm_holds]
  exact TermK.demo_le

/-- 泛化版在 `ℚ` 上也有意义（`ℝ` 之外的有序域，证明泛化不是空话）。 -/
theorem TermK.demo_le_rat :
    (TermK.le (TermK.add (TermK.var 0) (TermK.var 0)) (TermK.const (3 : ℚ))).holds
      (fun _ => 1) := by
  show (1 : ℚ) + 1 ≤ 3
  norm_num

end Gen
end RuleSyntax
end FateV2.Rules