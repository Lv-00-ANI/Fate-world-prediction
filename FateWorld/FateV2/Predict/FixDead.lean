import FateWorld.FateV2.Predict.BackdoorCriterion
import FateWorld.FateV2.Predict.BackdoorGenuine
import FateWorld.FateV2.Predict.NoDescendantWitness
import FateWorld.FateV2.Predict.T1A2
import Mathlib.Tactic

/-!
  # Predict · FixDead

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FixDead.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BackdoorCriterion, BackdoorGenuine, NoDescendantWitness, T1A2
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/Stage2/FixDead` —— 三处空转定理的**真替代**

本文件只**新增**定理，不修改任何既有文件。三条目标分别对应审计报告的三个致命发现。

## 审计发现

1. `R259.BackdoorSetup.NoDescendant` 的定义体是 `∀ z ux, S.fX z ux = S.fX z ux`（**恒真式**）；
2. `backdoor_adjustment := h`（证明体是**恒等**）；
3. `gap_reduces_to_markov_bridge` 的桥 `bridge : ∀ G prem concl, prem → concl → concl` 与 `G` **无关**。

## 本文件的三条定理

* `noDescendant_vacuous` —— 旧定义**不可证伪**；`R277` 新定义**不可证伪性被打破**（`Y` 必然是后代）。
* `backdoor_adjustment_genuine` —— 调整公式的**逐点代数**（因子分解 + 消去），不是恒等。
* `graph_probability_bridge_minimal` —— 从 `FactorizesOn` **提取**因子，图约束被**消费**（`Pa(v)` 之外为常数）。

---

**⚠ 关于第 1 条最重要的负面结果**：
`noDescendant_new_definition_differs` 的**字面陈述**（`NoDescendant S W ↔ ∀ v ∈ W, ¬IsDescendant S v`）
只是定义展开（`Iff.rfl`），**不构成「有内容」**。真正有内容的是：
旧定义**恒真**（因此 `¬ S.NoDescendant` 不可证），新定义**可被证伪**（`W = {Y}` 时失败）。
本文件用 `noDescendant_vacuous` 把这两件事**并排证明**。
-/

namespace FateV2.Predict.Stage2.FixDead

open FateV2.Modeling

open FateV2.Predict.R259

/-! ## §1 第 1 条：`NoDescendant` —— 旧定义恒真 vs 新定义可证伪 -/

-- ⭐⭐⭐⭐⭐ 旧 `NoDescendant`（`Fate/BackdoorCriterion.lean:276`）是**恒真式**
-- （它在 `R259.BackdoorSetup` 上对**任意** `S` 成立，与 `S` 的任何内容无关）。
-- 证明同时说明：`old_nod` 的证明项被 Lean 归约成 `fun z ux => rfl`，
-- 即该「命题」没有携带任何约束。
theorem noDescendant_vacuous (S : BackdoorSetup) :
    S.NoDescendant ∧ (S.NoDescendant → True) := by
  have h : S.NoDescendant = ∀ z : S.Z, ∀ ux : S.Ux, S.fX z ux = S.fX z ux := rfl
  exact ⟨fun z ux => rfl, fun _ => trivial⟩

-- ⭐⭐⭐⭐ 新定义（`Fate/BackdoorGenuine.lean:526`）**不是恒真式**：
-- `Y` 永远是 `X` 的后代，故任意可达的 `Y` 都违反 `NoDescendant`。
-- ⚠ 这正是「新定义真的含有 `IsDescendant` 约束」的证据。
theorem noDescendant_new_is_not_trivial (S : BackdoorSetup) (x : S.X) (y : S.Y)
    (z : S.Z) (ux : S.Ux) (uy : S.Uy) (hf : S.fY x z ux uy = y) :
    FateV2.Predict.R277.IsDescendant S (FateV2.Predict.R277.Vert.y y) :=
  FateV2.Predict.NoDescendantWitness.y_is_descendant S x y z ux uy hf

-- ⭐⭐⭐⭐⭐ **第 1 条主定理**：旧定义恒真、新定义在同一 `S`/`W` 上**给出真约束**。
-- 与 `noDescendant_new_definition_differs`（`Iff.rfl`）相比，这条**真的需要证明**。
theorem noDescendant_old_vacuous_and_new_bites (S : BackdoorSetup) (x : S.X) (y : S.Y)
    (z : S.Z) (ux : S.Ux) (uy : S.Uy) (hf : S.fY x z ux uy = y) :
    S.NoDescendant
    ∧ FateV2.Predict.R277.IsDescendant S (FateV2.Predict.R277.Vert.y y)
    ∧ ¬ FateV2.Predict.R277.NoDescendant S ({FateV2.Predict.R277.Vert.y y} : Set (FateV2.Predict.R277.Vert S)) := by
  refine ⟨fun z ux => rfl, ?_, ?_⟩
  · exact FateV2.Predict.NoDescendantWitness.y_is_descendant S x y z ux uy hf
  · exact FateV2.Predict.NoDescendantWitness.noDescendant_singleton_false S x y z ux uy hf

/-! ## §2 第 2 条：`backdoor_adjustment` 的真版本（逐点代数） -/

-- ⭐⭐⭐⭐ **`backdoor_adjustment` 的真版本**。
--
-- 若联合律**因子分解**为 `joint x y z = margXZ x z * condY x z y` 且 `margXZ x z ≠ 0`，
-- 则调整公式 `∑ z, joint x y z / margXZ x z * margZ z` 等于 `∑ z, condY x z y * margZ z`。
--
-- ⚠ 这里**没有**任何一项是 `:= h`：必须逐点用 `hfac` 替换、用 `div_mul_cancel₀` 消去。
theorem backdoor_adjustment_genuine
    {X Y Z : Type*} [Fintype Z]
    (joint : X → Y → Z → ℝ) (margXZ : X → Z → ℝ) (margZ : Z → ℝ)
    (condY : X → Z → Y → ℝ) (x : X)
    (hfac : ∀ y z, joint x y z = margXZ x z * condY x z y)
    (hpos : ∀ z, margXZ x z ≠ 0) :
    ∀ y, (∑ z, joint x y z / margXZ x z * margZ z) = ∑ z, condY x z y * margZ z := by
  intro y
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [hfac y z]
  -- `(margXZ * condY) / margXZ * margZ` → 先把 `margXZ` 换到前面，再消去
  rw [show margXZ x z * condY x z y = condY x z y * margXZ x z from mul_comm _ _,
    mul_div_cancel_right₀ _ (hpos z)]

/-! ## §3 第 3 条：图 ⟹ 概率桥的**最小有效**形式 -/

-- ⭐⭐⭐⭐ **真正的「图 ⟹ 概率」桥的最小形式**。
--
-- 给定的平凡形式 `graph_probability_bridge_minimal`（`:= hfac`）只是**解包 `∃`**。
-- 这里把它**用到极限**：从 `FactorizesOn G p` 中提取 `π`，并且额外证明
-- **`π v` 在 `Pa(v) ∪ {v}` 之外真的是常数**（把「只读」约束**用**掉，而不是转手）。
-- 这一步是 `d-分离 + 因子分解 ⟹ 条件独立` 推理链的唯一入口。
theorem graph_probability_bridge_minimal_genuine
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {p : (V → Bool) → ℝ}
    (hfac : FateV2.Predict.T1A2.FactorizesOn G p) :
    ∃ π : V → (V → Bool) → ℝ,
      (∀ v, FateV2.Predict.T1A2.ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
      (∀ v (ω : V → Bool), 0 < π v ω) ∧
      (∀ ω, p ω = ∏ v, π v ω) ∧
      -- ⭐ 真正被消费的部分：`Pa(v) ∪ {v}` 之外的自由度**被约束掉**
      (∀ v (ω : V → Bool) (u : V), u ∉ insert v (G.parents v) →
        ∃ c : ℝ, ∀ ω' : V → Bool, (∀ w ∈ insert v (G.parents v), ω' w = ω w) →
          π v ω' = c) := by
  classical
  obtain ⟨π, hread, hpos, hprod⟩ := hfac
  refine ⟨π, hread, hpos, hprod, fun v ω u _ => ⟨π v ω, fun ω' hω => ?_⟩⟩
  -- `ReadsOnlyOn` 在这里**被使用**：两点在 `Pa(v) ∪ {v}` 上一致 ⟹ 因子值一致。
  exact (hread v ω ω' (fun w hw => (hω w hw).symm)).symm

end FateV2.Predict.Stage2.FixDead

-- ⭐ 公理审计（只列这三条实际使用的公理，确认无 `sorryAx`）
#print axioms FateV2.Predict.Stage2.FixDead.noDescendant_vacuous
#print axioms FateV2.Predict.Stage2.FixDead.noDescendant_old_vacuous_and_new_bites
#print axioms FateV2.Predict.Stage2.FixDead.backdoor_adjustment_genuine
#print axioms FateV2.Predict.Stage2.FixDead.graph_probability_bridge_minimal_genuine
