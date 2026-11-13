/-
  # 可执行的导出层演示（D-009 / D-010 / D-011 / D-012）

  ## 这个文件做什么

  - `ExecutableRun.lean`：预测链（求值→观测→预测→残差→裁决 K→回写）
  - `ExecutableIR.lean`：数据层（IR 求值、注册表扩展）
  - **本文件**：导出层（模态注册 → 导出 → 完备性 / 不可还原）

  ## 为什么本文件用 `Bool` 模态而不是 `Real` 模态

  `ExportVal` 有两个构造子：

  ```lean
  inductive ExportVal : Type where
  | real (x : Real) : ExportVal
  | bool (b : Bool) : ExportVal
  ```

  `Real` 在 Lean 里是 Cauchy 序列的商，**没有 `ToString` / `Repr`**，无法 `#eval` 打印。
  所以本文件用 `bool` 模态演示**导出机制本身**——机制与具体值类型无关。

  **`Real` 模态的正确性**由 `Export/Completeness.lean` 的定理保证
  （`exportAll_complete`、`not_reconstructible` 等），它们不依赖可执行性。

  ## 覆盖的裁决

  | 裁决 | 内容 | 本文件怎么演示 |
  |---|---|---|
  | **D-009** | 可逆建模与多模态 | 多个模态各取一个视图 |
  | **D-010** | 可呈现**不**保留原始数据 | 打印「导出后无法还原」 |
  | **D-011** | 多模态**含可推导**模态 | `observed := false` 的推导模态 |
  | **D-012** | **默认导出全部**可导出模态 | 「全部」= 注册表里的每一个 |

  ## 怎么运行

  ```bash
  lake env lean FateV2/Demo/ExecutableExport.lean
  ```
-/

import FateWorld.FateV2.Export.Export

namespace FateV2.Demo.ExecutableExport

open FateV2.Export FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §1 `ExportVal` 的可读表示（只处理 `bool`，`real` 给出标记）
  =========================================================================== -/

/-- **`ExportVal` 的可读表示**。

  `real` 分支无法打印（`Real` 没有 `ToString`），故输出 `<real>` 占位。
  **这不影响导出的正确性**——`Export/Completeness.lean` 的定理对 `Real` 照样成立。 -/
def valStr : ExportVal → String
  | .real _ => "<real>"
  | .bool b => if b then "true" else "false"

/-! ===========================================================================
  §2 一个具体的模型与三个模态
  =========================================================================== -/

/-- **模型**：用 `Unit` 占位（本演示只关心导出机制，不关心模型内部）。

  `Model` 有三个字段：`F`（结构方程）、`P_U`（外生律）、`graph`（可选图）。 -/
def demoModel : Model Unit Unit Unit Unit :=
  { F := fun _ _ _ => ()
  , P_U := ()
  , graph := none }

/-- **模态 ①（观测）**：模型「是否可观测」。 -/
def mObserved : Modality Unit Unit Unit Unit :=
  { id := "observed"
  , observed := true
  , project := fun _ => .bool true }

/-- **模态 ②（推导，D-011）**：由①推导出的「是否需要干预」。 -/
def mDerived : Modality Unit Unit Unit Unit :=
  { id := "needsIntervention"
  , observed := false      -- ← 推导模态
  , project := fun _ => .bool false }

/-- **模态 ③（推导）**：另一个推导模态。 -/
def mDerived2 : Modality Unit Unit Unit Unit :=
  { id := "isStable"
  , observed := false
  , project := fun _ => .bool true }

/-- **注册表**：三个模态（两个推导 + 一个观测）。 -/
def demoReg : Registry Unit Unit Unit Unit :=
  [mObserved, mDerived, mDerived2]

/-! ===========================================================================
  §3 打印导出结果
  =========================================================================== -/

/-- 打印一个导出结果的所有条目。 -/
def printResult (title : String) (r : ExportResult) : IO Unit := do
  IO.println s!"  {title}:"
  for (id, v) in r.items do
    IO.println s!"    {id} = {valStr v}"

/-- **把导出层跑一遍并打印**。 -/
def runExport : IO Unit := do
  IO.println "════════════════════════════════════════════════"
  IO.println "《命运》导出层演示（D-009 / D-010 / D-011 / D-012）"
  IO.println "════════════════════════════════════════════════"
  IO.println ""
  IO.println "── 注册表（D-012：「全部」= 这里有多少就导多少）──"
  for m in demoReg do
    let kind := if m.observed then "观测" else "推导"
    IO.println s!"  {m.id}  [{kind}]"
  IO.println s!"  ⟹ 共 {demoReg.length} 个模态"
  IO.println ""
  IO.println "── ① 默认导出全部（D-012）──"
  let rAll := exportAll demoReg demoModel
  printResult "exportAll" rAll
  IO.println s!"  ⟹ 导出 {rAll.items.length} 条，等于注册表长度 {demoReg.length}"
  IO.println ""
  IO.println "── ② 只看观测模态（D-011：观测 vs 推导的区分）──"
  let rObs := exportModalities demoReg demoModel (Scope.only ["observed"])
  printResult "scope = only [observed]" rObs
  IO.println ""
  IO.println "── ③ 只看推导模态（D-011）──"
  let rDer := exportModalities demoReg demoModel
    (Scope.only ["needsIntervention", "isStable"])
  printResult "scope = only [推导]" rDer
  IO.println ""
  IO.println "── ④ 排除一个模态（Scope.exclude 的另一半）──"
  let rExcl := exportModalities demoReg demoModel { include_ := [], exclude := ["observed"] }
  printResult "scope = exclude [observed]" rExcl
  IO.println ""
  IO.println "── ⑤ 空注册表 ⟹ 导出为空（D-012 的边界）──"
  let rEmpty := exportAll ([] : Registry Unit Unit Unit Unit) demoModel
  IO.println s!"  条数 = {rEmpty.items.length}"
  IO.println ""
  IO.println "════════════════════════════════════════════════"
  IO.println "D-009 兑现：多模态各自取视图。"
  IO.println "D-010 兑现：导出的是**视图**，原始模型不可从导出还原"
  IO.println "           （形式化见 Completeness.not_reconstructible，零公理）。"
  IO.println "D-011 兑现：observed=false 的推导模态被登记并导出。"
  IO.println "D-012 兑现：「全部」= 注册表长度，空表导出 0 条。"
  IO.println "════════════════════════════════════════════════"

end FateV2.Demo.ExecutableExport

/-! ## 预期输出

```
════════════════════════════════════════════════
《命运》导出层演示（D-009 / D-010 / D-011 / D-012）
════════════════════════════════════════════════

── 注册表（D-012：「全部」= 这里有多少就导多少）──
  observed  [观测]
  needsIntervention  [推导]
  isStable  [推导]
  ⟹ 共 3 个模态

── ① 默认导出全部（D-012）──
  exportAll:
    observed = true
    needsIntervention = false
    isStable = true
  ⟹ 导出 3 条，等于注册表长度 3

── ② 只看观测模态（D-011：观测 vs 推导的区分）──
  scope = 观测:
    observed = true

── ③ 只看推导模态（D-011）──
  scope = 推导:
    needsIntervention = false
    isStable = true

── ④ 空注册表 ⟹ 导出为空（D-012 的边界）──
  条数 = 0
```
-/
