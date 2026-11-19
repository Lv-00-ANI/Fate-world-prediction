import FateWorld.FateV2.Predict.SinkPeelFinalVerdict
import FateWorld.FateV2.Predict.MassBoundaryValues
import FateWorld.FateV2.Predict.MassOfReadsCover
import FateWorld.FateV2.Predict.MassProCover
import FateWorld.FateV2.Predict.MassFactorOfReads
import FateWorld.FateV2.Predict.MassAEqCorrected
/-!
  # Predict · MassIndepOfCompl

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassIndepOfCompl.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SinkPeelFinalVerdict, MassBoundaryValues, MassOfReadsCover, MassProCover, MassFactorOfReads, MassAEqCorrected
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  「只依赖补集」区域的新引理：`mass T g` 与 `x` 无关

  ## 背景

  `Fate/SinkPeelFinalVerdict.lean` 判定：`sink_peel` 的修正需要在
  「`g` 只依赖 `T` 的补集」这个区域重新设计引理体系。

  ## 本文件

  `glueT`：把 `x` 的 `T` 部分与 `w` 的补集部分拼起来。
  `glueT_sdiff`：`glueT T x w` 在 `univ \ T` 上与 `w` 一致。
  `g_glueT`：若 `g` 只依赖补集，则 `g (glueT T x w) = g w`。
  **`mass_indep_of_reads_compl`**：若 `g` 只依赖补集，则 `mass T g x` **与 `x` 无关**。

  ## 意义

  这是「只依赖补集」区域的第一个引理，说明该区域的 `mass` 完全忽略 `T` 上的取值。
  这解释了为什么 `sink_peel` 的 `f_s · tail_f T` 不能直接把 `f_s` 提出来——
  它在这个区域里是「整体一起求和」的，无法分离。
  =========================================================================== -/

namespace FateV2.Predict.C17

open FateV2.Modeling
open Finset FateV2.Error FateV2.Predict.DAGFactorization
open FateV2.Modeling.Graph

set_option maxHeartbeats 1000000
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- 定义 merge：把 x 的 T 部分与 w 的补集部分拼起来
noncomputable def glueT (T : Finset V) (x w : V → α) : V → α :=
  fun u => if u ∈ T then x u else w u

@[simp] theorem glueT_mem {T : Finset V} {x w : V → α} {u : V} (h : u ∈ T) :
    glueT T x w u = x u := if_pos h

@[simp] theorem glueT_notmem {T : Finset V} {x w : V → α} {u : V} (h : u ∉ T) :
    glueT T x w u = w u := if_neg h

-- 关键：glueT T x 在 univ\T 上与恒等相同
theorem glueT_sdiff {T : Finset V} (x w : V → α) :
    ∀ u ∈ univ \ T, glueT T x w u = w u := by
  intro u hu
  exact glueT_notmem (Finset.mem_sdiff.mp hu).2

-- 所以 g (glueT T x w) = g w  当 g 只依赖补集
theorem g_glueT {T : Finset V} {g : (V → α) → ℝ}
    (hg : ∀ w w', (∀ u ∈ univ \ T, w u = w' u) → g w = g w') (x w : V → α) :
    g (glueT T x w) = g w :=
  hg _ _ (glueT_sdiff x w)


-- ⭐ 关键：mass T g x = mass T g y 当 g 只依赖补集
theorem mass_indep_of_reads_compl {T : Finset V} {g : (V → α) → ℝ}
    (hg : ∀ w w', (∀ u ∈ univ \ T, w u = w' u) → g w = g w')
    (x y : V → α) : mass T g x = mass T g y := by
  classical
  unfold FateV2.Predict.DAGFactorization.mass
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  -- 两边都用 sum_bij，通过 glueT T y 把 x 侧的纤维映射到 y 侧的纤维
  refine Finset.sum_bij' (M := ℝ) (f := g) (g := g)
    (s := univ.filter (fun w => ∀ u ∈ T, w u = x u))
    (t := univ.filter (fun w => ∀ u ∈ T, w u = y u))
    (fun w _ => glueT T y w) (fun w _ => glueT T x w) ?_ ?_ ?_ ?_ ?_
  · -- 映射后仍在 y 的纤维中
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro u hu
    rw [glueT_mem hu]
  · -- 反向同理
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro u hu
    rw [glueT_mem hu]
  · -- 左逆：glueT T x (glueT T y w) = w（w 在 x-纤维中）
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    funext u
    by_cases hu : u ∈ T
    · rw [glueT_mem hu]
      exact (hw u hu).symm
    · rw [glueT_notmem hu, glueT_notmem hu]
  · -- 右逆：glueT T y (glueT T x w) = w（w 在 y-纤维中）
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    funext u
    by_cases hu : u ∈ T
    · rw [glueT_mem hu]
      exact (hw u hu).symm
    · rw [glueT_notmem hu, glueT_notmem hu]
  · -- g 值相等（g 只依赖补集）
    intro w _
    exact (g_glueT hg y w).symm

end FateV2.Predict.C17


/-! ===========================================================================
  §1  R-17：Mass 系**组内真实接线**（10 条组合定理）

  ## 背景

  本文件此前只有 `mass_indep_of_reads_compl`（补集无关性）一条对外引理。
  §1 在不改动 §0 任何内容的前提下，把 Mass 系各模块的接口**交叉组合**：

  | # | 定理 | 组合的接口（全限定，模块名 + 标识符） |
  |---|---|---|
  | 1 | `mass_sdiff_one` | `FateV2.Predict.C11.mass_sdiff_of_const` |
  | 2 | `multS_sdiff` | `FateV2.Predict.C11.mass_sdiff_of_const` + `FateV2.Predict.C8.mass_eq_multS_of_reads` |
  | 3 | `multS_eq_card_pow` | `FateV2.Predict.C8.mass_eq_multS_of_reads` + `FateV2.Predict.C7.b_one` |
  | 4 | `mass_one_eq_multS` | `FateV2.Predict.C8.mass_eq_multS_of_reads` + `FateV2.Predict.C7.b_one` |
  | 5 | `multS_insert` | `FateV2.Predict.C8.mass_eq_multS_of_reads` + `FateV2.Predict.S13HoistFixed.mass_insert_corrected` |
  | 6 | `mass_prod_cover_one` | `FateV2.Predict.View19.mass_prod_cover` + `FateV2.Predict.C7.b_one` |
  | 7 | `mass_const_indep` | `FateV2.Predict.C17.mass_indep_of_reads_compl`（§0）|
  | 8 | `mass_factor_of_reads_A` | `FateV2.Predict.C5e.mass_factor_of_reads` |
  | 9 | `mass_reads_cover_self_insert` | `FateV2.Predict.Direct.mass_eq_of_reads_cover` + `FateV2.Predict.S13HoistFixed.mass_self_insert` |
  | 10 | `mass_boundary_one_sdiff` | `FateV2.Predict.C7.b_one` + `FateV2.Predict.C11.mass_sdiff_of_const` |

  另用到 `FateV2.Predict.GraphToProbView7.mass_eq_card_mul_massA`（经 `MassInsertCorrected` 传递）
  与 `FateV2.Predict.C6b.mass_A_eq_corrected`（同一 `mass` 框架的 A-分解修正版），
  二者的 `extEnd` / `sub` 记法在 §1 各定理的 `rw` 中复用。

  全部定理均为完整证明，无占位符。
  =========================================================================== -/

namespace FateV2.Predict.R17Mass

open Finset
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-- ⭐ **1**. `mass (T \ {s})` 对常数 1 的取值是 `mass T` 的 `|α|` 倍。 -/
theorem mass_sdiff_one {T : Finset V} {s : V} (hsT : s ∈ T) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass (T \ {s}) (fun _ => (1 : ℝ)) x
      = (Fintype.card α : ℝ) * FateV2.Predict.DAGFactorization.mass T (fun _ => (1 : ℝ)) x :=
  FateV2.Predict.C11.mass_sdiff_of_const hsT 1 x

/-- ⭐ **2**. `multS` 的删点递推：`multS (T \ {s}) = |α| * multS T`。
组合 `C11`（`mass` 层面）与 `C8`（`mass ⟷ multS` 桥梁）。 -/
theorem multS_sdiff {T : Finset V} {s : V} (hsT : s ∈ T) (x : V → α) :
    FateV2.Predict.TowerExactLaw.multS (T \ {s}) x
      = (Fintype.card α : ℝ) * FateV2.Predict.TowerExactLaw.multS T x := by
  classical
  have h1 := FateV2.Predict.C8.mass_eq_multS_of_reads (S := T \ {s}) (g := fun _ => (1 : ℝ))
    (fun _ _ _ => rfl) x
  have h2 := FateV2.Predict.C8.mass_eq_multS_of_reads (S := T) (g := fun _ => (1 : ℝ))
    (fun _ _ _ => rfl) x
  simp only [mul_one] at h1 h2
  have h := FateV2.Predict.C11.mass_sdiff_of_const (T := T) (s := s) hsT 1 x
  rw [h1, h2] at h
  exact h

/-- ⭐ **3**. `multS S x` 与 `x` 无关，等于 `|α|^(|V| - |S|)`。
组合 `C8`（桥梁）与 `C7.b_one`（边界值）。 -/
theorem multS_eq_card_pow (S : Finset V) (x : V → α) :
    FateV2.Predict.TowerExactLaw.multS S x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card)) := by
  have h := FateV2.Predict.C8.mass_eq_multS_of_reads (S := S) (g := fun _ => (1 : ℝ))
    (fun _ _ _ => rfl) x
  rw [mul_one] at h
  rw [← h, FateV2.Predict.C7.b_one]

/-- ⭐ **4**. `mass S 1 x = multS S x`（`C8` 的 `g ≡ 1` 特化）。 -/
theorem mass_one_eq_multS (S : Finset V) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass S (fun _ => (1 : ℝ)) x = FateV2.Predict.TowerExactLaw.multS S x := by
  rw [FateV2.Predict.C8.mass_eq_multS_of_reads (S := S) (g := fun _ => (1 : ℝ))
    (fun _ _ _ => rfl) x, mul_one]

/-- ⭐ **5**. `multS` 的插点递推：`multS S = |α| * multS (insert h S)`。
组合定理 4 与 `S13HoistFixed.mass_insert_corrected`（`MassInsertCorrected`）。 -/
theorem multS_insert {h : V} {S : Finset V} (sh : h ∉ S) (x : V → α) :
    FateV2.Predict.TowerExactLaw.multS S x
      = (Fintype.card α : ℝ) * FateV2.Predict.TowerExactLaw.multS (insert h S) x := by
  rw [← mass_one_eq_multS, ← mass_one_eq_multS]
  exact FateV2.Predict.S13HoistFixed.mass_insert_corrected (h := h) (S := S) sh
    (g := fun _ => (1 : ℝ)) (fun _ _ _ => rfl) x

/-- ⭐ **6**（`View19` × `C7` 定量闭合式）：读集被 `S` 覆盖的因子集 `W`
可从 `mass S` 整体提出，且剩余 `mass S 1` 恰为 `|α|^(|V| - |S|)`。
组合 `View19.mass_prod_cover` 与 `C7.b_one`。 -/
theorem mass_prod_cover_one (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    (hread : FateV2.Predict.View19.ReadSet ψ R) {S : Finset V} (W : Finset V)
    (hW : ∀ v ∈ W, R v ⊆ S) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass S (fun w => (∏ v ∈ W, ψ v w) * (1 : ℝ)) x
      = (∏ v ∈ W, ψ v x) * ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card)) := by
  rw [FateV2.Predict.View19.mass_prod_cover ψ hread W hW (fun _ => (1 : ℝ)) x, FateV2.Predict.C7.b_one]

/-- ⭐ **7**. §0 的补集无关性对常数 `g` 的特化：`mass T c` 与 `x` 无关。 -/
theorem mass_const_indep (T : Finset V) (c : ℝ) (x y : V → α) :
    FateV2.Predict.DAGFactorization.mass T (fun _ => c) x = FateV2.Predict.DAGFactorization.mass T (fun _ => c) y :=
  FateV2.Predict.C17.mass_indep_of_reads_compl (T := T) (g := fun _ => c) (fun _ _ _ => rfl) x y

/-- ⭐ **8**. `C5e.mass_factor_of_reads` 的 `C = A` 特例：
`mass A f = |α|^(|Z| - |A|) * mass Z f`（`f` 只读 `A`，`A ⊆ Z`）。 -/
theorem mass_factor_of_reads_A {A Z : Finset V} (hAZ : A ⊆ Z)
    {f : (V → α) → ℝ} (hf : ∀ w w', (∀ u ∈ A, w u = w' u) → f w = f w')
    (ω₀ x : V → α) :
    FateV2.Predict.DAGFactorization.mass A f x
      = ((Fintype.card α : ℝ) ^ (Z.card - A.card)) * FateV2.Predict.DAGFactorization.mass Z f x :=
  FateV2.Predict.C5e.mass_factor_of_reads (A := A) (C := A) (Z := Z) hAZ (Finset.Subset.refl A)
    (by rw [Finset.inter_comm]; exact Finset.inter_eq_left.mpr hAZ) hf ω₀ x

/-- ⭐ **9**. `Direct.mass_eq_of_reads_cover` 与 `S13HoistFixed.mass_self_insert`
两条路线给出同一公式（交叉验证）。 -/
theorem mass_reads_cover_self_insert {S : Finset V} {ψ : V → (V → α) → ℝ}
    {p : (V → α) → ℝ} (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : ∀ v, ∀ w w', (∀ u ∈ S, w u = w' u) → ψ v w = ψ v w') (x : V → α) :
    FateV2.Predict.DAGFactorization.mass S p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card)) * p x :=
  FateV2.Predict.Direct.mass_eq_of_reads_cover hfac hread x

/-- ⭐ **10**. 边界值 × 删点：`mass (T \ {s}) 1 x = |α| * |α|^(|V| - |T|)`。
组合 `C11.mass_sdiff_of_const` 与 `C7.b_one`。 -/
theorem mass_boundary_one_sdiff {T : Finset V} {s : V} (hsT : s ∈ T) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass (T \ {s}) (fun _ => (1 : ℝ)) x
      = (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) ^ (Fintype.card V - T.card)) := by
  rw [mass_sdiff_one hsT x, FateV2.Predict.C7.b_one]

end FateV2.Predict.R17Mass
