import FateWorld.FateV2.Predict.SinkPeelCounterexample
import FateWorld.FateV2.Predict.MassMultSBridge
import FateWorld.FateV2.Predict.FactorMarkov
/-!
  # Predict · MassSdiffConst

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassSdiffConst.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SinkPeelCounterexample, MassMultSBridge, FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `mass (T \ {s}) = |α| · mass T`（常数情形）

  ## 背景

  `Fate/Strategy9SinkPeelNorm.lean` 的 `sink_peel` 在 `T = {s}` 时有机检反例
  （见 `Fate/SinkPeelCounterexample.lean`）。

  原因是：`mass (T \ {s})` 的纤维比 `mass T` 大 `|α|` 倍
  （少一个约束 `w_s = x_s`）。

  ## 本文件（常数情形）

  `mass_sdiff_of_const`：`mass (T \ {s}) (fun _ => c) x = |α| * mass T (fun _ => c) x`

  ## 一般情形（本轮补完）

  `mass_sdiff_of_reads`：若 `g` 只读 `T \ {s}`，则
    `mass (T \ {s}) g x = |α| * mass T g x`

  **注意假设方向**：是「`g` 只读 `T \ {s}`」而非「`g` 只读 `T`」。
  因为 `T \ {s} ⊆ T`，只读更小的集合是更强条件，只有这个方向能推出结论。
  =========================================================================== -/

namespace FateV2.Predict.C11

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- 换方法：直接对 mass 展开
-- mass (T\{s}) g x = ∑_{w | w|_{T\{s}} = x|_{T\{s}}} g w
-- mass T g x       = ∑_{w | w|_T = x|_T} g w
-- 若 g 不读 s：两组求和的每项 g 值都只依赖 w|_{T\{s}}
--   ⟹ 第一组 = |α| * （第二组的 g 值）= |α| * mass T g x

-- 先做一个简化版：若 g 完全不读任何坐标（常数 c）
theorem mass_sdiff_of_const {T : Finset V} {s : V} (hsT : s ∈ T) (c : ℝ) (x : V → α) :
    mass (T \ {s}) (fun _ => c) x = (Fintype.card α : ℝ) * mass T (fun _ => c) x := by
  -- mass S (fun _ => c) x = c * mass S (fun _ => 1) x
  have hc : ∀ S : Finset V, mass S (fun _ => c) x = c * mass S (fun _ => (1:ℝ)) x := by
    intro S
    unfold mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hh : ∀ u ∈ S, w u = x u
    · simp [hh]
    · simp [hh]
  have h1 : mass (T \ {s}) (fun _ => c) x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - (T \ {s}).card)) * c := by
    rw [hc, FateV2.Predict.GraphToProbView7.mass_one_card]
    ring
  have h2 : mass T (fun _ => c) x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - T.card)) * c := by
    rw [hc, FateV2.Predict.GraphToProbView7.mass_one_card]
    ring
  rw [h1, h2]
  have hcard : (T \ {s}).card = T.card - 1 := by
    rw [Finset.card_sdiff]
    have h : ({s} ∩ T : Finset V) = {s} := by
      ext u; simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro ⟨h1, _⟩; exact h1
      · intro h1; exact ⟨h1, h1 ▸ hsT⟩
    rw [h]
    simp
  rw [hcard]
  have hle : 1 ≤ T.card := Finset.card_pos.mpr ⟨s, hsT⟩
  have hle2 : T.card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  -- |α|^(|V| - (|T|-1)) * c = |α| * (|α|^(|V|-|T|) * c)
  rw [show Fintype.card V - (T.card - 1) = (Fintype.card V - T.card) + 1 from by omega]
  rw [pow_succ]
  ring



-- ⭐ 正确方向：g 只读 T\{s}  时
theorem mass_sdiff_of_reads {T : Finset V} {s : V} (hsT : s ∈ T)
    {g : (V → α) → ℝ} (hg : ∀ w w', (∀ u ∈ T \ {s}, w u = w' u) → g w = g w')
    (x : V → α) :
    mass (T \ {s}) g x = (Fintype.card α : ℝ) * mass T g x := by
  -- g 只读 T\{s} ⟹ g 只读 T（因 T\{s} ⊆ T，条件更强）
  have hgT : ∀ w w', (∀ u ∈ T, w u = w' u) → g w = g w' := by
    intro w w' h
    refine hg w w' (fun u hu => ?_)
    exact h u (Finset.mem_sdiff.mp hu).1
  -- 两边用 mass_self_insert 展开
  have hgS : ∀ w w', (∀ u ∈ T \ {s}, w u = w' u) → g w = g w' := hg
  rw [Fate.S13HoistFixed.mass_self_insert hgS x,
      Fate.S13HoistFixed.mass_self_insert hgT x]
  -- 关键：两个 extEnd 处的 g 值相等
  have hgeq : g (FateV2.Predict.GraphToProbView7.extEnd (T \ {s}) x (fun u : ↥(T \ {s}) => x u.1))
      = g (FateV2.Predict.GraphToProbView7.extEnd T x (fun u : ↥T => x u.1)) := by
    refine hg _ _ fun u hu => ?_
    rw [FateV2.Predict.GraphToProbView7.extEnd_of_mem (T \ {s}) x _ u hu,
        FateV2.Predict.GraphToProbView7.extEnd_of_mem T x _ u (Finset.mem_sdiff.mp hu).1]
  rw [hgeq]
  -- 指数关系
  have hcard : (T \ {s}).card = T.card - 1 := by
    rw [Finset.card_sdiff]
    have h : ({s} ∩ T : Finset V) = {s} := by
      ext u; simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro ⟨h1, _⟩; exact h1
      · intro h1; exact ⟨h1, h1 ▸ hsT⟩
    rw [h]; simp
  rw [hcard]
  have hle : 1 ≤ T.card := Finset.card_pos.mpr ⟨s, hsT⟩
  have hle2 : T.card ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  rw [show Fintype.card V - (T.card - 1) = (Fintype.card V - T.card) + 1 from by omega]
  rw [pow_succ]
  ring



end FateV2.Predict.C11
