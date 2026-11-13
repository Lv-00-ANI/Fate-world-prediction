import FateWorld.FateV2.Bridge.AnalysisBridge
import FateWorld.FateV2.Bridge.LawRuleBridge
import FateWorld.FateV2.Bridge.SupportBridge
import FateWorld.FateV2.Core.Binder
import FateWorld.FateV2.Core.Cache
import FateWorld.FateV2.Core.Cardinality
import FateWorld.FateV2.Core.Closure
import FateWorld.FateV2.Core.ClosureAll
import FateWorld.FateV2.Core.ClosureFirstPos
import FateWorld.FateV2.Core.ClosureFix
import FateWorld.FateV2.Core.ClosureMono
import FateWorld.FateV2.Core.ClosureStable
import FateWorld.FateV2.Core.ClosureStableFinal
import FateWorld.FateV2.Core.ClosureStableFinal2
import FateWorld.FateV2.Core.Decl
import FateWorld.FateV2.Core.DeclGraph
import FateWorld.FateV2.Core.InvalidateClosure
import FateWorld.FateV2.Core.InvalidateClosureAll
import FateWorld.FateV2.Core.InvalidateDirectionCounterexample
import FateWorld.FateV2.Core.InvalidateMixed
import FateWorld.FateV2.Core.Judgment
import FateWorld.FateV2.Core.LawRuleIR
import FateWorld.FateV2.Core.MonoConv
import FateWorld.FateV2.Core.NodupLemmas
import FateWorld.FateV2.Core.Ops
import FateWorld.FateV2.Core.OpsAlgebra
import FateWorld.FateV2.Core.Pointwise
import FateWorld.FateV2.Core.Quote
import FateWorld.FateV2.Core.Rec
import FateWorld.FateV2.Core.Registry
import FateWorld.FateV2.Core.RevClosure
import FateWorld.FateV2.Core.SampleBounds
import FateWorld.FateV2.Core.Subst
import FateWorld.FateV2.Core.SubstCorrect
import FateWorld.FateV2.Core.Syntax
import FateWorld.FateV2.Core.Unified
import FateWorld.FateV2.Core.VerdictAlgebra
import FateWorld.FateV2.Error.MonoConvReal
import FateWorld.FateV2.Meta.Context

/-!
  # GroupD · 清单（由对应子代理独占维护）

  按组构建：`powershell -ExecutionPolicy Bypass -File _check.ps1 -Group D`

  ## 依赖顺序（下面是拓扑序，不是字母序）

  ```
  Core/Syntax            语法族（既有）
  Core/Rec               折叠子（一层遍历机具，零公理）
  Core/Subst             替换定义（mutual，手写列表遍历，零公理）
  Core/SubstCorrect      替换恒等律（单层 + 列表，零公理）
  Core/Judgment          判断（既有）
  Core/Ops               四算子（既有）
  Core/Binder            TermExt：绑定结构（非 mutual，可自由递归）
  Core/Registry          C2 注册表
  Core/Quote             反射（编解码 + 部分保真）
  Core/Decl              声明是一等原子
  Core/DeclGraph         声明依赖图 + 三条主定理
  Core/Cache             内容寻址缓存
  Bridge/SupportBridge   经典定理 → 带 support 的判断
  Bridge/LawRuleBridge   Judgment → LawRule 的解释桥
  Bridge/AnalysisBridge  实数/测度结论的登记通道
  ```

  ## 吸收边界（详见 `理论-文档/11-IR语言化/README.md`）

  吸收旧稿的 §5（可见性与传播）、§6（声明是一等原子）、§7.1/7.4/7.5（闭包、
  缓存键、is_dirty）、§8.8（失效判定）、§13.2（七条元数据验证）。
  **不吸收** §2（CIC 内核）、§4（elaborator）、§9–§10（构建/工具链）、§12（路线图）
  ——那些由 Lean 本体承担，重造是可信基的净损失。
-/


/- 新模块继续追加在下方 -/
