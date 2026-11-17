import FateWorld.FateV2.Predict.MassInsertCorrected
import FateWorld.FateV2.Predict.TailOutExtract
/-!
  # Predict · MassAEqCorrected

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassAEqCorrected.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassInsertCorrected, TailOutExtract
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `mass_A_eq` 的**正确版本**（原版有三重缺陷）

  ## 原定理（Fate/TailBlockFinal.lean，为假）

  ```lean
  theorem mass_A_eq (hfac) (hread) (hOut : ∀ v ∉ A, R v ⊆ Z) (x) :
      mass A p x = (∏ v ∈ outSet A, ψ v x) * (∏ v ∈ A, ψ v x)
  ```

  ## 三重缺陷

  1. **缺 `Z ⊆ A`**：`mass_extract_out_of_factorizes` 要求 `Z ⊆ S = A`
  2. **缺 `∀ v, R v ⊆ A`**：要证 `∏_{v∈A} ψ v` 只读 `A`（每个 `ψ v` 只读 `R v`）
  3. **缺 `|α|^(|V|-|A|)` 因子**：`mass A` 的纤维有 `|α|^(|V|-|A|)` 个元素，
     不是单个点，所以 `mass A f x ≠ f x`

  ## 正确版本

  ```lean
  theorem mass_A_eq_corrected (hZA : Z ⊆ A) (hRA : ∀ v, R v ⊆ A) (hOut) (x) :
      mass A p x = |α|^(|V|-|A|) * (∏ v ∈ outSet A, ψ v x)
                     * (∏ v ∈ A, ψ v (extEnd A x (x|_A)))
  ```

  证明：`mass_extract_out_of_factorizes` 提取 A 外因子，
  再用 `mass_self_insert`（`MassInsertCorrected.lean`）处理 `mass A`。
  =========================================================================== -/

namespace FateV2.Predict.C6b

open FateV2.Modeling
open Finset FateV2.Error Fate.View19 Fate.DAGFactorization
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- ⭐ mass_A_eq 的正确版本（补 Z ⊆ A、R ⊆ A、|α| 因子）
theorem mass_A_eq_corrected (ψ : V → (V → α) → ℝ) {R : V → Finset V} {p : (V → α) → ℝ}
    {A Z : Finset V} (hfac : ∀ w, p w = ∏ v, ψ v w) (hread : ReadSet ψ R)
    (hZA : Z ⊆ A) (hRA : ∀ v, R v ⊆ A)
    (hOut : ∀ v, v ∉ A → R v ⊆ Z) (x : V → α) :
    mass A p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card))
        * (∏ v ∈ outSet A, ψ v x)
        * (∏ v ∈ A, ψ v (GraphToProbView7.extEnd A x (fun u : ↥A => x u.1))) := by
  rw [mass_extract_out_of_factorizes (A := A) (S := A) (Z := Z) ψ hfac hread
        (Finset.Subset.refl A) hZA hOut x]
  have hg : ∀ w w', (∀ u ∈ A, w u = w' u) → (∏ v ∈ A, ψ v w) = (∏ v ∈ A, ψ v w') := by
    intro w w' h
    refine Finset.prod_congr rfl fun v _ => ?_
    exact hread v w w' (fun u hu => h u (hRA v hu))
  rw [Fate.S13HoistFixed.mass_self_insert hg x]
  ring

end FateV2.Predict.C6b
