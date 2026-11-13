/-
  # 可执行的依赖图与时空组合演示（D-004 / D-024）

  ## 这个文件做什么

  已有的四个可执行层：

  | 文件 | 覆盖 |
  |---|---|
  | `ExecutableRun.lean` | 预测链 |
  | `ExecutableIR.lean` | 数据层（IR 求值） |
  | `ExecutableExport.lean` | 导出层 |
  | `ExecutableSCM.lean` | SCM 层 |
  | **本文件** | **依赖图（D-004）+ 时空组合（D-024）** |

  ## D-004：规则单位与数据嵌入

  `DeclGraph` 把声明组织成有向图，并提供三个可执行操作：

  ```lean
  def dependents (g : DeclGraph K) (k : K) : List (Decl K)  -- 谁依赖 k
  def invalidate (g : DeclGraph K) (k : K) (bk : BodyKind)  -- 改 k 会失效谁
  def closure    (g : DeclGraph K) (roots : List K)         -- 从 roots 推出
  ```

  **方向是关键**（T14 用零公理反例证过）：
  `invalidate` 是**反向可达**（谁依赖我），`closure` 是**正向可达**（我依赖谁）。

  ## D-024：时空可组合

  ```lean
  structure Step (Γ) where
    fwd : Γ → Γ;  inv : Γ → Γ
    left_inv : ∀ γ, inv (fwd γ) = γ    -- 只要求左逆！

  def comp (s₁ s₂ : Step Γ) : Step Γ  -- 扭复合：inv 顺序相反
  structure Ctx (Γ) where
    state : Γ;  log : List (Γ → Γ)     -- 状态 + 逆日志
  ```

  **只要求左逆**（`inv ∘ fwd = id`，不要求 `fwd ∘ inv = id`）——
  这正是「撤销是单向的」这一论文假设的形式化。

  ## 怎么运行

  ```bash
  lake env lean FateV2/Demo/ExecutableGraph.lean
  ```
-/

import FateWorld.FateV2.Core.DeclGraph
import FateWorld.FateV2.Meta.Context

namespace FateV2.Demo.ExecutableGraph

open FateV2.Core FateV2.Meta

/-! ===========================================================================
  §1 D-004：一个具体的声明图
  =========================================================================== -/

/-- **四条声明的图**（key `0..3`）：

  ```
  0 ──→ 1 ──→ 3
  └───→ 2 ──→ 3
  ```

  即：`1` 与 `2` 都依赖 `0`，`3` 依赖 `1` 和 `2`。 -/
def demoGraph : DeclGraph Nat :=
  [ { key := 0, kind := .defn, bodyKind := .body, deps := [],    visibility := .open_ }
  , { key := 1, kind := .defn, bodyKind := .body, deps := [0],   visibility := .open_ }
  , { key := 2, kind := .defn, bodyKind := .body, deps := [0],   visibility := .open_ }
  , { key := 3, kind := .defn, bodyKind := .body, deps := [1,2], visibility := .open_ }
  ]

/-! ===========================================================================
  §2 D-024：一个具体的可撤销变换
  =========================================================================== -/

/-- **`Int` 上的「加一」步**：`fwd = (+1)`，`inv = (-1)`。

  左逆律 `inv (fwd γ) = γ` 成立：`(γ + 1) - 1 = γ`。 -/
def stepAddOne : Step Int :=
  { fwd := fun γ => γ + 1
  , inv := fun γ => γ - 1
  , left_inv := by intro γ; omega }

/-- **`Int` 上的「乘以二」步**：`fwd = (· * 2)`，`inv = (· / 2)`。

  ⚠ 左逆律**只对偶数成立**，所以这里取一个**只在偶数上工作**的版本：
  `fwd = (· + 2)`，`inv = (· - 2)`。 -/
def stepAddTwo : Step Int :=
  { fwd := fun γ => γ + 2
  , inv := fun γ => γ - 2
  , left_inv := by intro γ; omega }

/-! ===========================================================================
  §3 打印
  =========================================================================== -/

def keysOf (ds : List (Decl Nat)) : List Nat :=
  ds.foldr (fun d acc => d.key :: acc) []

/-- **把依赖图与时空组合各跑一遍并打印**。 -/
def runGraph : IO Unit := do
  IO.println "════════════════════════════════════════════════"
  IO.println "《命运》依赖图 + 时空组合演示（D-004 / D-024）"
  IO.println "════════════════════════════════════════════════"
  IO.println ""
  IO.println "═══════════ 第一部分：D-004 依赖图 ═══════════"
  IO.println ""
  IO.println "图结构："
  IO.println "  0 ──→ 1 ──→ 3"
  IO.println "  └───→ 2 ──→ 3"
  IO.println ""
  IO.println "── ① dependents（谁依赖 k）──"
  for k in [0, 1, 2, 3] do
    IO.println s!"  dependents {k} = {keysOf (FateV2.Core.DeclGraph.dependents demoGraph k)}"
  IO.println ""
  IO.println "── ② invalidate（改 k 会失效谁，D-004 的反向可达）──"
  for k in [0, 1, 2, 3] do
    IO.println s!"  invalidate {k} = {keysOf (FateV2.Core.DeclGraph.invalidate demoGraph k .body)}"
  IO.println ""
  IO.println "  ⚠ 方向：改 0 会让 1、2（以及 3）失效；"
  IO.println "     但改 3 不影响任何人。这就是「反向可达」。"
  IO.println ""
  IO.println "── ③ closure（根 ∪ 直接 deps，**只展开一层**）──"
  for r in [[0], [1], [3]] do
    IO.println s!"  closure {r} = {FateV2.Core.DeclGraph.closure demoGraph r}"
  IO.println ""
  IO.println "  ⚠ closure 的真实语义（T56 审计纠正了本文件早期注释的错误）："
  IO.println "     closure g roots = roots ++ 「roots 里点名的那些声明的 deps」"
  IO.println "     即：**只展开 roots 这一层**，不是传递闭包，也不是「roots 的 deps」。"
  IO.println "     例：closure [1] = [1, 0]（1 点名了，取它的 deps=0）"
  IO.println "         closure [3] = [3, 1, 2]（3 点名了，取它的 deps=[1,2]）"
  IO.println "         closure [0] = [0]（0 点名了，但 0 无 deps）"
  IO.println "     传递闭包版见 closureAll（T10 交付）。"
  IO.println ""
  IO.println "═══════════ 第二部分：D-024 时空组合 ═══════════"
  IO.println ""
  IO.println "── ④ 单步：加一 ──"
  let c0 : Ctx Int := Ctx.init 0
  IO.println s!"  初始 state = {c0.state}, 日志长度 = {c0.log.length}"
  let c1 := Ctx.apply stepAddOne c0
  IO.println s!"  apply(+1) ⟹ state = {c1.state}, 日志长度 = {c1.log.length}"
  IO.println ""
  IO.println "── ⑤ 撤销回原状态 ──"
  let c2 := Ctx.undo c1
  IO.println s!"  undo ⟹ state = {c2.state}, 日志长度 = {c2.log.length}"
  IO.println ""
  IO.println "── ⑥ 多步 + 逐步撤销（后进先出）──"
  let c3 := Ctx.apply stepAddOne (Ctx.apply stepAddTwo c0)
  IO.println s!"  apply(+2) 再 apply(+1) ⟹ state = {c3.state}"
  let c4 := Ctx.undo c3
  IO.println s!"  undo 一次 ⟹ state = {c4.state}  （撤掉 +1）"
  let c5 := Ctx.undo c4
  IO.println s!"  undo 两次 ⟹ state = {c5.state}  （再撤掉 +2）"
  IO.println ""
  IO.println "── ⑦ 扭复合：`comp` 的逆顺序相反 ──"
  let sComp := stepAddOne.comp stepAddTwo
  IO.println s!"  (加一) ∘ (加二) 的 fwd(0) = {sComp.fwd 0}"
  IO.println s!"  其 inv(fwd(0))         = {sComp.inv (sComp.fwd 0)}"
  IO.println "  ⟹ 左逆律成立（D-024 的核心：只要求左逆）"
  IO.println ""
  IO.println "════════════════════════════════════════════════"
  IO.println "D-004 兑现：规则单位组织成图，失效 = 反向可达。"
  IO.println "D-024 兑现：时空步可组合，撤销按后进先出（只要求左逆）。"
  IO.println "════════════════════════════════════════════════"

end FateV2.Demo.ExecutableGraph

/-! ## 预期输出

```
═══════════ 第一部分：D-004 依赖图 ═══════════

── ① dependents（谁依赖 k）──
  dependents 0 = [1, 2]
  dependents 1 = [3]
  dependents 2 = [3]
  dependents 3 = []

── ② invalidate（改 k 会失效谁）──
  invalidate 0 = [1, 2]
  invalidate 1 = [3]
  invalidate 2 = [3]
  invalidate 3 = []

── ③ closure（从 roots 推出）──
  closure [0] = [0, 1, 2, 3]

═══════════ 第二部分：D-024 时空组合 ═══════════

── ④ 单步：加一 ──
  初始 state = 0, 日志长度 = 0
  apply(+1) ⟹ state = 1, 日志长度 = 1

── ⑤ 撤销回原状态 ──
  undo ⟹ state = 0, 日志长度 = 0

── ⑥ 多步 + 逐步撤销（后进先出）──
  apply(+2) 再 apply(+1) ⟹ state = 3
  undo 一次 ⟹ state = 2  （撤掉 +1）
  undo 两次 ⟹ state = 0  （再撤掉 +2）

── ⑦ 扭复合 ──
  (加一) ∘ (加二) 的 fwd(0) = 3
  其 inv(fwd(0))         = 0
```
-/
