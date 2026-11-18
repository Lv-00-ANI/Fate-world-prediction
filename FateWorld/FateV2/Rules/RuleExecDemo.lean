import FateWorld.FateV2.Rules.RuleExec
/-!
  # Rules · RuleExecDemo

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RuleExecDemo.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RuleExec
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  规则可执行引擎 · **`#eval` 演示**（P1-H1）

  ## 为什么有这个文件

  `Fate/RuleExec.lean` 是全仓**唯一**能把规则跑成 `Bool` 的纯可执行引擎
  （`Term.check : Term → EnvQ → Bool`），并且已有
  `Term.check_iff_holds` / `run_iff_holds` 把它钉到语义 `RuleTerm.holds` 上。

  但在 CHAIN-4 审计时它 **0 处 `#eval`**，且仅 `TermSize.lean` /
  `FullPipelineDemo.lean` 两个模块 import 它 —— 「引擎存在但从未被人按按钮」。

  这与 `_algo-frozen` 的「ALGO 线零消费」是同一病灶。本文件给它补上
  **可执行演示**（≥5 处 `#eval`，全部真的跑出 `Bool` 或数值），
  证明它不只是纸面定理，而是真能出数。

  ## 演示内容（每项一个 `#eval`）

  | # | 演示 | 期望 |
  |---|------|------|
  | 1 | 成立等式 `x0 + x0 = 2`，`x0 = 1` | `true` |
  | 2 | 不成立不等式 `2 ≤ 1` | `false` |
  | 3 | 合取 `and`（左真右假） | `false` |
  | 4 | 析取 `or`（左假右真） | `true` |
  | 5 | 否定 `not`（包住一条真规则） | `false` |
  | 6 | 数值侧 `Term.eval`（`ℚ` 出数，不是 `Bool`） | `7` |
  | 7 | 环境敏感：同一项换环境从 `true` 翻成 `false` | `true` / `false` |

  ## 与语义的接线（不是自说自话）

  演示 8 把 `#eval` 的 `true` 结果交给 `Term.check_iff_holds`，
  得到 `RuleTerm.holds`（`Prop`）—— 即**执行侧出 `Bool`，语义侧拿到 `Prop`**。
  这条搬运不靠 `decide`，靠的是 `RuleExec.lean` 已证的一致性定理。

  ## 诚实边界

  § 演示 1–7 是 `#eval`（编译期跑出真值），§ 演示 8 是一条定理（`check` ⟹ `holds`）。
  `#eval` 本身**不证明**任何命题，它只展示引擎能跑；语义保证来自
  `check_iff_holds`，本文件不新增关于语义的断言。
  本文件不含 `sorry` / `admit` / `axiom` / `native_decide`。
-/

namespace FateV2.Rules

open FateV2.Modeling
namespace RuleSyntax
namespace Exec
namespace RuleExecDemo

open FateV2.Rules.RuleSyntax (Env)
open FateV2.Rules.RuleSyntax.Exec

/-! ## §1  环境与项 -/

/-- 环境一：`x0 = 1`，`x1 = 2`，其余变量为 `0`。 -/
def env1 : EnvQ := fun n => if n = 0 then 1 else if n = 1 then 2 else 0

/-- 环境二：`x0 = 5`，`x1 = 2`，其余变量为 `0`。 -/
def env2 : EnvQ := fun n => if n = 0 then 5 else if n = 1 then 2 else 0

/-- 全零环境（与 `RuleExec.lean` 内示例一致）。 -/
def env0 : EnvQ := fun _ => 0

/-- 演示项 A：`x0 + x0 = 2`。 -/
def tA : Term := .eq (.add (.var 0) (.var 0)) (.const 2)

/-- 演示项 B：`2 ≤ 1`（恒假的不等式）。 -/
def tB : Term := .le (.const 2) (.const 1)

/-- 演示项 C：`x0 ≤ x1`。 -/
def tC : Term := .le (.var 0) (.var 1)

/-- 演示项 D：`x0 * x1 + 5`（纯算术，供 `Term.eval` 出数）。 -/
def tD : Term := .add (.mul (.var 0) (.var 1)) (.const 5)

/-! ## §2  演示 1–5：五类逻辑形态都真的返回 `Bool` -/

-- 演示 1：成立的等式（在 `env1` 上 `x0 + x0 = 2`）
#eval tA.check env1

-- 演示 2：不成立的不等式（`2 ≤ 1`）
#eval tB.check env0

-- 演示 3：合取 —— 左真（`x0 = 1`）右假（`2 ≤ 1`），整体应为 `false`
#eval (Term.and tA tB).check env1

-- 演示 4：析取 —— 左假（`2 ≤ 1`）右真（`x0 ≤ x1`），整体应为 `true`
#eval (Term.or tB tC).check env1

-- 演示 5：否定 —— 包住一条在 `env1` 上为真的规则，结果应为 `false`
#eval (Term.not tA).check env1

/-! ## §3  演示 6–7：数值侧与「环境真的会被读」 -/

-- 演示 6：`Term.eval` 出 `ℚ` 而非 `Bool`（`x0 * x1 + 5` 在 `env1` 上 = `1*2+5`）
#eval tD.eval env1

-- 演示 7a：同一项 `tC` 在 `env1`（`x0=1 ≤ x1=2`）上应为 `true`
#eval tC.check env1

-- 演示 7b：同一项 `tC` 在 `env2`（`x0=5 ≤ x1=2`）上应为 `false`
#eval tC.check env2

/-! ## §4  演示 8：`Bool` 结果真的能搬回语义 `Prop`

下面不是 `#eval`，而是把演示 1 的执行结果交给一致性定理，
得到 `RuleTerm.holds`（`Prop`，不可执行，但**已被证明成立**）。

这证明引擎不是「自己跟自己玩」：`check = true` 的每一次真值，
都在语义侧有对应的成立事实。 -/

/-- 演示 1 的项在 `env1` 上语义成立（`RuleTerm.holds`），由 `check_iff_holds` 搬运而来。 -/
theorem demo1_holds :
    tA.toRuleTerm.holds (fun n => ((env1 n : ℚ) : ℝ)) :=
  (Term.check_iff_holds tA env1 (fun n => ((env1 n : ℚ) : ℝ)) (fun _ => rfl)).mp
    (by simp only [tA, env1, Term.check, Term.eval, Nat.reduceEqDiff]; norm_num)

/-- 演示 2 的项语义不成立：可执行侧拿到 `false`，语义侧拿到 `¬ holds`。 -/
theorem demo2_not_holds :
    ¬ tB.toRuleTerm.holds (fun n => ((env0 n : ℚ) : ℝ)) :=
  (run_eq_false_iff_not_holds tB env0 (fun n => ((env0 n : ℚ) : ℝ))
    (fun _ => rfl)).mp (by simp [run, tB, Term.eval])

/-- 一致性的具体落地：`run` 在 `env1` 上对 `tA` 返回 `true`。 -/
theorem demo1_run_true : run tA env1 = true := by
  simp only [run, tA, env1, Term.check, Term.eval, Nat.reduceEqDiff]
  norm_num

end RuleExecDemo
end Exec
end RuleSyntax
end FateV2.Rules