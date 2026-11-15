import Mathlib

/-!
  # Core · SetLemmas

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SetLemmas.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Core`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# 通用集合引理

从 Bridge 系列收敛而来（见 `_audit/BRIDGE-1-Bridge模块真实诊断.md`）。

原本这两条在 `BridgeExpanded` / `BridgeFullFixed` / `BridgeFull` 各写了一遍，
**逐字相同**。现统一到此处。
-/

namespace FateV2.Core.SetLemmas

variable {V : Type*} [DecidableEq V]

theorem sub_union_left {X Y Z : Finset V} : X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  simp only [Finset.mem_union] at hu ⊢
  tauto

theorem sub_union_right {X Y Z : Finset V} : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  simp only [Finset.mem_union] at hu ⊢
  tauto

end FateV2.Core.SetLemmas
