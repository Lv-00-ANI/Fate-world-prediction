/-
  # 《命运》完整系统演示（五层一次跑通）

  ## 这个文件做什么

  前面五个 `Executable*.lean` 各跑一层。本文件把它们**按系统顺序串起来**：

  ```
  ┌─────────────────────────────────────────────┐
  │ ① 数据层（D-002/D-006/D-007）                 │
  │    IR 求值：Term → 注册表 → 语义              │
  ├─────────────────────────────────────────────┤
  │ ② SCM 层（D-014/D-019）                       │
  │    结构方程 F、外生律 P_U、推前、σ-model      │
  ├─────────────────────────────────────────────┤
  │ ③ 预测层（D-008/D-013）                       │
  │    求值 → 观测 → 预测 → 残差 → 裁决 K → 回写  │
  ├─────────────────────────────────────────────┤
  │ ④ 导出层（D-009~D-012）                       │
  │    模态注册 → 导出 → 范围限定                 │
  ├─────────────────────────────────────────────┤
  │ ⑤ 依赖图 + 时空（D-004/D-024）                │
  │    失效传播、可撤销变换                       │
  └─────────────────────────────────────────────┘
  ```

  ## 怎么运行

  ```bash
  lake env lean FateV2/Demo/ExecutableAll.lean
  ```

  **这是本项目的「一体化」证明**（D-013）：五个层各自可执行，且能在一个进程里依次跑完。
-/

import FateWorld.FateV2.Demo.ExecutableRun
import FateWorld.FateV2.Demo.ExecutableIR
import FateWorld.FateV2.Demo.ExecutableExport
import FateWorld.FateV2.Demo.ExecutableSCM
import FateWorld.FateV2.Demo.ExecutableGraph

namespace FateV2.Demo.ExecutableAll

open FateV2.Demo

/-- **五层一次跑通**。 -/
def runAll : IO Unit := do
  IO.println "╔══════════════════════════════════════════════╗"
  IO.println "║  《命运》完整系统演示（五层一次跑通）        ║"
  IO.println "╚══════════════════════════════════════════════╝"
  IO.println ""
  IO.println "▶▶▶ 第 1 / 5 层：数据层（D-002 / D-006 / D-007）"
  IO.println ""
  ExecutableIR.runIR
  IO.println ""
  IO.println "▶▶▶ 第 2 / 5 层：SCM 层（D-014 / D-019）"
  IO.println ""
  ExecutableSCM.runSCM
  IO.println ""
  IO.println "▶▶▶ 第 3 / 5 层：预测层（D-008 / D-013）"
  IO.println ""
  Executable.runDemo
  IO.println ""
  IO.println "▶▶▶ 第 4 / 5 层：导出层（D-009 ~ D-012）"
  IO.println ""
  ExecutableExport.runExport
  IO.println ""
  IO.println "▶▶▶ 第 5 / 5 层：依赖图 + 时空（D-004 / D-024）"
  IO.println ""
  ExecutableGraph.runGraph
  IO.println ""
  IO.println "╔══════════════════════════════════════════════╗"
  IO.println "║  五层全部跑通                                ║"
  IO.println "║  D-002/004/006/007/008/009~014/019/024       ║"
  IO.println "╚══════════════════════════════════════════════╝"

end FateV2.Demo.ExecutableAll
