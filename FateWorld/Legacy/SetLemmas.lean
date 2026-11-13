import Mathlib

/-!
# 通用集合引理

从 Bridge 系列收敛而来（见 `_audit/BRIDGE-1-Bridge模块真实诊断.md`）。

原本这两条在 `BridgeExpanded` / `BridgeFullFixed` / `BridgeFull` 各写了一遍，
**逐字相同**。现统一到此处。
-/

namespace Fate.SetLemmas

variable {V : Type*} [DecidableEq V]

theorem sub_union_left {X Y Z : Finset V} : X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  simp only [Finset.mem_union] at hu ⊢
  tauto

theorem sub_union_right {X Y Z : Finset V} : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  simp only [Finset.mem_union] at hu ⊢
  tauto

end Fate.SetLemmas
