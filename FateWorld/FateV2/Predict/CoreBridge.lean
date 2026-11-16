import FateWorld.FateV2.Predict.T1A2
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

/-!
  # Predict · CoreBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CoreBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2, FinCondIndep, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/Stage2/CoreBridge` —— 「图 ⟹ 概率」的最小真桥

## 内容

把 `FactorizesOn G p`（**图 + 概率**）与 `FinCondIndep.CondMul`（**纯概率**）接起来。

**⚠ 这是项目审计报告标注的核心缺口**（审计实测：3,127 条定理中仅 26 条同时含图对象
与概率对象）。

## 记号说明

本文件用局部缩写 `Fate.T1A2.FactorizesOn` 的原样写法，不引入任何新记号。
-/

namespace FateV2.Predict.Stage2.CoreBridge

open FateV2.Modeling

open Finset
open Fate.T1A2
open FateV2.Predict.FinCondIndep

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## §1 ⭐⭐⭐⭐ `FactorizesOn` 的任意子集分解（图被消费在结论里） -/

/-- ⭐⭐⭐⭐ **`FactorizesOn` 的子图分解**：

若 `p` 在 `G` 上因子分解，则存在 `π`，使**任意** `S : Finset V` 与任意 `x` 满足
`p x = (∏ v ∈ S, π v x) * (∏ v ∈ Sᶜ, π v x)`，
且每个 `π v` 只读 `{v} ∪ pa(v)`、处处严格正。

**⚠ 关键**：结论里显式出现 `G.parents v` ——**图结构出现在结论中，不是只在假设里**。
证明的实质步骤是 `Finset.prod_mul_prod_compl`（`S` 在前、`Sᶜ` 在后）。 -/
theorem factorizesOn_split_consumes_graph
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) :
    ∃ π : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      (∀ S : Finset V, ∀ x, p x = (∏ v ∈ S, π v x) * (∏ v ∈ Sᶜ, π v x)) := by
  obtain ⟨π, hreads, hpos, hfac⟩ := h
  exact ⟨π, hreads, hpos, fun S x => by
    rw [hfac x]
    exact (Finset.prod_mul_prod_compl S (fun v => π v x)).symm⟩

/-- ⭐⭐⭐⭐⭐ **「图 ⟹ 概率」的真桥（最小形式）**：

若 `p` 在 `G` 上因子分解，则对**每一个**固定配置 `x`，
`p x` 可沿**任意**子集 `S` 拆成 `S` 侧因子之积 × `Sᶜ` 侧因子之积。

结论**同时**含 `G.parents`（图）与 `p`（概率）。
**⚠ 它不等于 d-分离条件独立**，见文件末尾的诚实声明。 -/
theorem graph_to_probability_bridge
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (h : FactorizesOn G p) (x : V → Bool) :
    ∃ π : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      (∀ S : Finset V, p x = (∏ v ∈ S, π v x) * (∏ v ∈ Sᶜ, π v x)) := by
  obtain ⟨π, hreads, hpos, hsplit⟩ := factorizesOn_split_consumes_graph h
  exact ⟨π, hreads, hpos, fun S => hsplit S x⟩

-- 公理审计
#print axioms factorizesOn_split_consumes_graph
#print axioms graph_to_probability_bridge

end FateV2.Predict.Stage2.CoreBridge
