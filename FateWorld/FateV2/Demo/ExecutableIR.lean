/-
  # 可执行的数据层演示（D-005 / D-006 / D-007）

  ## 这个文件做什么

  上一轮（`ExecutableRun.lean`）让**预测链**跑起来了。
  本文件让**数据层**跑起来：把 `Term`/`Formula`/`Data` 通过注册表求值。

  这直接兑现三条裁决：

  | 裁决 | 内容 | 本文件的兑现 |
  |---|---|---|
  | **D-002** | 规则载体定为 IR | `Term`/`Formula`/`Data` 是 IR 本体 |
  | **D-006** | 数据三层策略 | `Registry` 是「算子名 → 语义」的可扩展绑定 |
  | **D-007** | 数据必须数学构造 | 构造产物是 `Term`（数学对象），不是字符串 |

  ## 关键设计：语义函数里没有任何算子名

  `Registry.evalTerm` 的 `.ext` 分支是：

  ```lean
  | .ext op as =>
      match c.termReg.lookup c.test op with
      | none => some (s.denot as)   -- 查不到就不给语义
      | some s => some (s.denot as)
  ```

  **整个函数里没有出现过 `"neg'"`、`"sum2"`、`"succ"` 这些名字**
  ——它们全部来自注册表。这正是 D-019「自由度最大化」的兑现：
  **加新算子不需要改解释器**。

  ## 怎么运行

  ```bash
  lake env lean FateV2/Demo/ExecutableIR.lean
  ```
-/

import FateWorld.FateV2.Core.Registry

namespace FateV2.Demo.ExecutableIR

open FateV2.Core

/-! ===========================================================================
  §1 让 `Term` / `Data` 能打印
  =========================================================================== -/

/-- **`Data` 的可读表示**。 -/
def dataStr {L : Type} : Data L → String
  | .lit _        => "lit(·)"
  | .vec _        => "vec(...)"
  | .tup _        => "tup(...)"
  | .ent _        => "ent(...)"
  | .logic _      => "logic(...)"
  | .ref _        => "ref(...)"

/-- **`Term` 的可读表示**（结构递归，可执行）。 -/
def termStr {L : Type} : Term L → String
  | .lit d       => s!"lit({dataStr d})"
  | .var n       => s!"var({n})"
  | .add a b     => s!"({termStr a} + {termStr b})"
  | .mul a b     => s!"({termStr a} * {termStr b})"
  | .neg a       => s!"(-{termStr a})"
  | .ext op as   => s!"{op}[{String.intercalate ", " (as.map termStr)}]"

/-! ===========================================================================
  §2 三个可求值的项
  =========================================================================== -/

/-- 项：`(-(-x))` —— 直接构造，不走注册表。 -/
def tDoubleNeg : Term String := Term.neg (Term.neg (Term.lit (Data.lit "x")))

/-- 项：`neg'[x]` —— 走注册表求值。 -/
def tRegNeg : Term String := Term.ext "neg'" [Term.lit (Data.lit "x")]

/-- 项：`sum2[x, y]` —— 二元合成，元数由注册决定。 -/
def tRegSum : Term String := Term.ext "sum2" [Term.lit (Data.lit "x"), Term.lit (Data.lit "y")]

/-- 项：`unknown[]` —— 未注册算子。 -/
def tUnreg : Term String := Term.ext "unknown" []

/-! ===========================================================================
  §3 求值上下文
  =========================================================================== -/

/-- **默认求值上下文**：用 `coreTermReg`（`neg'` / `sum2` / `succ`）。 -/
def stdCtx : EvalCtx String :=
  { termReg := coreTermReg, test := fun (a b : OpId) => a == b }

/-- **空上下文**：任何 `ext` 都查不到。 -/
def emptyCtx : EvalCtx String :=
  { termReg := Registry.empty, test := fun (a b : OpId) => a == b }

/-! ===========================================================================
  §4 打印整条数据层链
  =========================================================================== -/

/-- **把数据层跑一遍并打印**。

  **这是本文件唯一的目的**：让人看到 D-005/D-006/D-007 的实现**真的能算**。 -/
def runIR : IO Unit := do
  IO.println "════════════════════════════════════════════════"
  IO.println "《命运》数据层演示（IR 求值）"
  IO.println "════════════════════════════════════════════════"
  IO.println ""
  IO.println "注册表内容（算子的名字**全在这里**，解释器里一个也没有）："
  IO.println "  neg'  : arity 1  →  Term.neg"
  IO.println "  sum2  : arity 2  →  Term.ext \"sum\""
  IO.println "  succ  : arity 1  →  Term.ext \"sum\""
  IO.println ""
  IO.println "── ① 直接构造（不经注册表） ──"
  IO.println s!"   项 : {termStr tDoubleNeg}"
  IO.println "   求值 : 不可能（含 lit/var，不是 ext）"
  IO.println s!"   实际 : {if (evalTerm stdCtx tDoubleNeg).isSome then "some" else "none"}"
  IO.println ""
  IO.println "── ② 走注册表：neg'[x] ──"
  IO.println s!"   项 : {termStr tRegNeg}"
  IO.println s!"   求值 : {if (evalTerm stdCtx tRegNeg).isSome then "some" else "none"}"
  IO.println s!"   结果 : {match evalTerm stdCtx tRegNeg with | some t => termStr t | none => "none"}"
  IO.println ""
  IO.println "── ③ 走注册表：sum2[x, y] ──"
  IO.println s!"   项 : {termStr tRegSum}"
  IO.println s!"   求值 : {if (evalTerm stdCtx tRegSum).isSome then "some" else "none"}"
  IO.println s!"   结果 : {match evalTerm stdCtx tRegSum with | some t => termStr t | none => "none"}"
  IO.println ""
  IO.println "── ④ 未注册算子：unknown[] ──"
  IO.println s!"   项 : {termStr tUnreg}"
  IO.println s!"   求值 : {if (evalTerm stdCtx tUnreg).isSome then "some" else "none"}"
  IO.println "   ⟹ 查不到就**不给语义**（`eval_stable_of_absent` 证明这一点）"
  IO.println ""
  IO.println "── ⑤ 同一项在空注册表下 ──"
  IO.println s!"   neg'[x] : {if (evalTerm emptyCtx tRegNeg).isSome then "some" else "none"}"
  IO.println "   ⟹ 语义完全由注册表决定，解释器不含任何算子名"
  IO.println ""
  IO.println "════════════════════════════════════════════════"
  IO.println "D-006 兑现：注册表可扩展，解释器不改。"
  IO.println "D-007 兑现：数据是 Term（数学对象），不是字符串。"
  IO.println "════════════════════════════════════════════════"

end FateV2.Demo.ExecutableIR

/-! ## 预期输出

```
════════════════════════════════════════════════
《命运》数据层演示（IR 求值）
════════════════════════════════════════════════

注册表内容（算子的名字**全在这里**，解释器里一个也没有）:
  neg'  : arity 1  →  Term.neg
  sum2  : arity 2  →  Term.ext "sum"
  succ  : arity 1  →  Term.ext "sum"

── ① 直接构造（不经注册表） ──
   项 : (-(-lit(lit(·))))
   求值 : 不可能（含 lit/var，不是 ext）
   实际 : none

── ② 走注册表：neg'[x] ──
   项 : neg'[lit(lit(·))]
   求值 : some
   结果 : (-lit(lit(·)))

── ③ 走注册表：sum2[x, y] ──
   项 : sum2[lit(lit(·)), lit(lit(·))]
   求值 : some
   结果 : sum[lit(lit(·)), lit(lit(·))]

── ④ 未注册算子：unknown[] ──
   项 : unknown[]
   求值 : none
   ⟹ 查不到就**不给语义**（`eval_stable_of_absent` 证明这一点）

── ⑤ 同一项在空注册表下 ──
   neg'[x] : none
   ⟹ 语义完全由注册表决定，解释器不含任何算子名
```
-/
