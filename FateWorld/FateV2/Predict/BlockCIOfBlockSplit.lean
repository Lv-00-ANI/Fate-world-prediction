import FateWorld.FateV2.Predict.MassADecompFinal
import FateWorld.FateV2.Predict.TailOutExtract
/-!
  # Predict · BlockCIOfBlockSplit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BlockCIOfBlockSplit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassADecompFinal, TailOutExtract
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `blockCI_of_block_split` 修正版的两个关键引理

  ## 背景

  `Fate/BridgeStrategy5FiberBijection.lean` 的 §4 声称落地 `BlockCI_Gap`
  （`blockCI_of_block_split`），但实际没写。

  上一轮（R119）分析出：`f` 只读 `A` 时，`mass C f` 与 `mass Z f` 的求和范围不同，
  要相等必须带上 `|α|^(|Z|-|C|)` 因子。原形式（不带因子）是假的。

  ## 本文件的结果

  `mass_self`：`mass Z f x = |α|^(|V|-|Z|) · f (extEnd Z ω₀ (x|_Z))`
    （用 `mass_eq_card_mul_massA` 取值 A = S = Z，求和只有一项）

  `f_eq_of_agree_C`：`A ⊆ Z`、`C ⊆ A`、`Z∩A = C`、`f` 只读 `A`、
    且 `wZ|_C = x|_C` 时，`f (extEnd Z ω₀ wZ) = f (extEnd Z ω₀ (x|_Z))`
    （因 `f` 只读 `A`，而 `C = Z∩A` 覆盖了 `A`）

  ## 这两条离完整定理还差什么

  还需一步：`mass C f x` 展开后的求和
    `∑ wZ, if (wZ|_C = x|_C) then f (extEnd Z ω₀ wZ) else 0`
  用 `f_eq_of_agree_C` 化为
    `|α|^(|Z|-|C|) · f (extEnd Z ω₀ (x|_Z))`
  然后与 `mass_self` 合并得
    `mass C f x = |α|^(|Z|-|C|) · mass Z f x`。
  这一步未做。
  =========================================================================== -/

namespace FateV2.Predict.C5b

open FateV2.Modeling
open Finset FateV2.Error Fate.View19 Fate.DAGFactorization
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem mass_self {Z : Finset V} {f : (V → α) → ℝ}
    (hf : ∀ w w', (∀ u ∈ Z, w u = w' u) → f w = f w')
    (ω₀ x : V → α) :
    mass Z f x = ((Fintype.card α : ℝ) ^ (Fintype.card V - Z.card))
      * f (Fate.GraphToProbView7.extEnd Z ω₀ (fun u : ↥Z => x u.1)) := by
  rw [Fate.GraphToProbView7.mass_eq_card_mul_massA (A := Z) (S := Z)
    (Finset.Subset.refl Z) hf ω₀ x]
  congr 1
  rw [Finset.sum_eq_single (fun u : ↥Z => x u.1)]
  · simp [Fate.GraphToProbView7.sub]
  · intro b _ hb
    simp only [Fate.GraphToProbView7.sub, Finset.mem_filter, Finset.mem_univ, true_and]
    have : ∃ u : ↥Z, b u ≠ x u.1 := by
      by_contra h; push Not at h; exact hb (funext h)
    obtain ⟨u, hu⟩ := this
    rw [if_neg]; intro hc; exact hu (hc u (by simp))
  · intro h; exact absurd (Finset.mem_univ _) h

-- 关键子引理：对满足 wZ|_C = x|_C 的 wZ，f (extEnd Z ω₀ wZ) = f (extEnd Z ω₀ (x|_Z))
theorem f_eq_of_agree_C {A C Z : Finset V} (hAZ : A ⊆ Z) (hCA : C ⊆ A)
    (hC : Z ∩ A = C)
    {f : (V → α) → ℝ} (hf : ∀ w w', (∀ u ∈ A, w u = w' u) → f w = f w')
    (ω₀ x : V → α) (wZ : ↥Z → α)
    (hag : ∀ u ∈ Fate.GraphToProbView7.sub Z C (Finset.Subset.trans hCA hAZ),
        wZ u = x u.1) :
    f (Fate.GraphToProbView7.extEnd Z ω₀ wZ)
      = f (Fate.GraphToProbView7.extEnd Z ω₀ (fun u : ↥Z => x u.1)) := by
  refine hf _ _ fun u huA => ?_
  have huZ : u ∈ Z := hAZ huA
  rw [Fate.GraphToProbView7.extEnd_of_mem Z ω₀ wZ u huZ,
      Fate.GraphToProbView7.extEnd_of_mem Z ω₀ (fun u : ↥Z => x u.1) u huZ]
  have huC : u ∈ C := hC ▸ Finset.mem_inter.mpr ⟨huZ, huA⟩
  -- u ∈ C ⊆ Z，故 u ∈ Z
  have huZ' : u ∈ Z := Finset.Subset.trans hCA hAZ huC
  have hmem : (⟨u, huZ'⟩ : ↥Z) ∈ Fate.GraphToProbView7.sub Z C (Finset.Subset.trans hCA hAZ) := by
    simp only [Fate.GraphToProbView7.sub, Finset.mem_filter, Finset.mem_univ, true_and]
    exact huC
  exact hag ⟨u, huZ'⟩ hmem

end FateV2.Predict.C5b
