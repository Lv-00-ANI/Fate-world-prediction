import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib

/-!
  # Modeling · ThreeNode

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ThreeNode.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# 具体图：三节点链 `gex`

从 4 个 Bridge 文件收敛而来（见 `_audit/BRIDGE-1-Bridge模块真实诊断.md`）。

原本 `def gex` 在 `BridgeDirect` / `BridgeExpanded` / `BridgeFullFixed` / `BridgeFull`
各定义了一遍（4 份逐字相同，各约 8 行）。现统一到此处。

那 4 个文件里改为：
```lean
def gex : FateV2.Modeling.Graph.DAG (Fin 3) := FateV2.Modeling.Concrete.gex
```
-/

namespace FateV2.Modeling.Concrete

/-- **三节点链图**：`0 → 1`，`2` 孤立。

`0 → 1 → 2` 的「链」形态是 `0 → 1`（`2` 无入边），
用于 `dSep` / `Factorizes` 的演示。 -/
def gex : FateV2.Modeling.Graph.DAG (Fin 3) where
  edge := fun u v => u = 0 ∧ v = 1
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 3,
        Relation.TransGen (fun u v : Fin 3 => u = 0 ∧ v = 1) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single h =>
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2; decide
      | tail _ hstep ih =>
          obtain ⟨h1, h2⟩ := hstep
          subst h1; subst h2; omega
    exact absurd (key v v hv) (lt_irrefl v)

end FateV2.Modeling.Concrete
