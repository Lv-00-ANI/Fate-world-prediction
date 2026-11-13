import FateWorld.Legacy.BalanceComponents
import FateWorld.Legacy.RebaseSplit

/-! ===========================================================================
  §0  子类型纤维的基数（`blockCI_of_block_split` 的计数部分）

  ## 内容

  `sub_card`：`(sub Z C hCZ).card = C.card`（因 `C ⊆ Z`）。

  `card_sub_fib'`：`{w : ↥Z → α // ∀ u ∈ sub Z C, w u = y u}` 的基数
                  `= |α| ^ (Z.card - C.card)`。

  ## 用途

  这两条是 R121 的 `mass_self`、`f_eq_of_agree_C` 之后的**计数步骤**。
  三者合起来给出：
    `mass C f x = |α|^(|Z|-|C|) · mass Z f x`
  当 `f` 只读 `A`、`A ⊆ Z`、`C = Z∩A`。

  ## 技术要点

  `card_sub_fib'` 直接引用 `Fate.GraphToProbView7.card_subtype_fib`，
  把 `V` 实例化为 `↥Z`，再用 `Fintype.card_coe Z : Fintype.card ↥Z = Z.card`
  和 `sub_card` 化简。需要 `[Nonempty α]`（来自 `card_subtype_fib`）。
  =========================================================================== -/

namespace Fate.C5d

open Finset Fate

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem sub_card {Z C : Finset V} (hCZ : C ⊆ Z) :
    (Fate.GraphToProbView7.sub Z C hCZ).card = C.card := by
  unfold Fate.GraphToProbView7.sub
  rw [Finset.card_filter, Finset.sum_boole]
  apply Finset.card_bij (fun (u : ↥Z) _ => u.1)
  · intro u hu; simpa using hu
  · intro u1 h1 u2 h2 heq; exact Subtype.ext heq
  · intro c hc
    exact ⟨⟨c, hCZ hc⟩, by simpa using hc, rfl⟩

-- 子类型基数：{w : ↥Z → α // ∀ u ∈ sub Z C hCZ, w u = y u} 的基数
theorem card_sub_fib' {Z C : Finset V} (hCZ : C ⊆ Z) (y : ↥Z → α) :
    Fintype.card {w : ↥Z → α // ∀ u ∈ Fate.GraphToProbView7.sub Z C hCZ, w u = y u}
      = Fintype.card α ^ (Z.card - C.card) := by
  -- 关键：↥Z 上有 Fintype.card ↥Z = Z.card
  -- 令 S := sub Z C hCZ
  -- 自由坐标数 = |↥Z| - |S| = Z.card - C.card
  have hZ : Fintype.card ↥Z = Z.card := Fintype.card_coe Z
  -- 用 card_subtype_fib 的思路：把 ↥Z 当作"V"
  -- 这里 ↥Z 是任意类型，S : Finset ↥Z，y : ↥Z → α
  -- 直接引用 card_subtype_fib（它适用于任意 V）
  have := Fate.GraphToProbView7.card_subtype_fib (V := ↥Z) (α := α) (Fate.GraphToProbView7.sub Z C hCZ) y
  rw [this, hZ, sub_card hCZ]

end Fate.C5d
