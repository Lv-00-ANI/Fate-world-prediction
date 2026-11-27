/-
================================================================================
  TailOutExtract.lean
  主定理 D 修正路线 · 第一步：A 外因子从 mass S 中提出

  ## 背景

  上一路线试图在 `↥A` 上直接调用 `condIndep_general`，要求
  `hfacA : ∀ w : ↥A → α, pA w = ∏ v : ↥A, ψA v w`，
  这等价于「A 外因子恒为 1」，**证不出来**（除非 A = univ）。

  ## 本文件给什么

  把 `p` 显式分解成「A 内 ∏ × A 外 ∏」，并证明 **A 外部分可从 `mass S` 整体提出**，
  条件是「A 外因子只读 Z」且 `Z ⊆ S`。

  ```lean
  theorem mass_extract_out ...
      : mass S (fun w => (∏ v ∈ A, ψ v w) * (∏ v ∈ W, ψ v w)) x
        = (∏ v ∈ W, ψ v x) * mass S (fun w => ∏ v ∈ A, ψ v w) x
  ```

  其中 `W := univ.filter (· ∉ A)`。

  ## 证明

  直接调用 `FateV2.Predict.View19.mass_prod_cover`，取
  `W := univ.filter (· ∉ A)`，`g := fun w => ∏ v ∈ A, ψ v w`。
  需证 `∀ v ∈ W, R v ⊆ S`：由 `hOut` 得 `R v ⊆ Z`，再由 `hZS : Z ⊆ S` 传递。

  ## 诚实边界

  * 本文件**只证这一条**（A 外部分提取），不做后续配平。
  * 不使用 `sorry` / `admit` / `axiom`。
================================================================================
-/

import FateWorld.FateV2.Predict.MassProCover
namespace FateV2.Predict.View19

open FateV2.Modeling

open Finset
open FateV2.Predict.DAGFactorization

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-!
  # Predict · TailOutExtract

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailOutExtract.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassProCover
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ### §1 A 外因子集 -/

/-- **A 外因子集**：`univ` 中不在 `A` 里的顶点。 -/
def outSet (A : Finset V) : Finset V := Finset.univ.filter (fun v => v ∉ A)

/-- ⭐ **A 外因子集与 A 互补**：`A ∪ outSet A = univ`。 -/
theorem A_union_outSet (A : Finset V) : A ∪ outSet A = (Finset.univ : Finset V) := by
  classical
  unfold outSet
  ext v
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- ⭐ **A 与 outSet A 不交**。 -/
theorem A_disjoint_outSet (A : Finset V) : Disjoint A (outSet A) := by
  classical
  unfold outSet
  refine Finset.disjoint_left.mpr ?_
  intro v hvA hvout
  exact (Finset.mem_filter.mp hvout).2 hvA

/-! ### §2 显式拆分 `p = P_A * P_out` -/

/-- ⭐⭐ **乘积按 `A` / `A` 外拆分**：
`∏ v, ψ v w = (∏ v ∈ A, ψ v w) * (∏ v ∈ outSet A, ψ v w)`。

**⟹ 这是把 `hfac : p w = ∏ v, ψ v w` 改写成「A 内 × A 外」的桥。** -/
theorem prod_split_in_out (ψ : V → (V → α) → ℝ) (A : Finset V) (w : V → α) :
    (∏ v, ψ v w)
      = (∏ v ∈ A, ψ v w) * (∏ v ∈ outSet A, ψ v w) := by
  classical
  rw [← Finset.prod_union (A_disjoint_outSet A), A_union_outSet]

/-! ### §3 ⭐⭐⭐ 主结果：A 外因子可从 `mass S` 中提出 -/

/-- ⭐⭐⭐ **A 外因子提取**。

若 `Z ⊆ S ⊆ A`、`A` 外所有因子的读集都在 `Z` 内，
则 `∏_{v ∉ A} ψ v` 可从 `mass S` 中整体提出（作为 `mass S x` 的系数）。

**⟹ 语义**：`mass S` 内部的自由坐标只在 `A \ S` 上，
而 `A` 外因子只读 `Z ⊆ S`，故它们在 `mass S` 内部恒定。

**证明**：取 `W := outSet A`，对 `mass_prod_cover` 应用
`hW : ∀ v ∈ W, R v ⊆ S`（由 `hOut` + `hZS` 传递）。 -/
theorem mass_extract_out (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    (hread : ReadSet ψ R) {A S Z : Finset V} (_hSA : S ⊆ A) (hZS : Z ⊆ S)
    (hOut : ∀ v, v ∉ A → R v ⊆ Z) (x : V → α) :
    mass S (fun w => (∏ v ∈ A, ψ v w) * (∏ v ∈ outSet A, ψ v w)) x
      = (∏ v ∈ outSet A, ψ v x) * mass S (fun w => ∏ v ∈ A, ψ v w) x := by
  classical
  have hW : ∀ v ∈ outSet A, R v ⊆ S := by
    intro v hv
    unfold outSet at hv
    rw [Finset.mem_filter] at hv
    have hvA : v ∉ A := hv.2
    exact Finset.Subset.trans (hOut v hvA) hZS
  have hcomm : (fun w => (∏ v ∈ A, ψ v w) * (∏ v ∈ outSet A, ψ v w))
      = (fun w => (∏ v ∈ outSet A, ψ v w) * (∏ v ∈ A, ψ v w)) := by
    funext w; ring
  rw [hcomm]
  exact mass_prod_cover ψ hread (outSet A) hW (fun w => ∏ v ∈ A, ψ v w) x

/-! ### §4 用 `p` 的形式表述（更贴近后续使用） -/

/-- ⭐⭐ **`p` 形式版本**：若 `p w = ∏ v, ψ v w`（因子化），
则 `mass S p x = (∏ v ∈ outSet A, ψ v x) * mass S (fun w => ∏ v ∈ A, ψ v w) x`。 -/
theorem mass_extract_out_of_factorizes (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    {p : (V → α) → ℝ} (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : ReadSet ψ R) {A S Z : Finset V} (hSA : S ⊆ A) (hZS : Z ⊆ S)
    (hOut : ∀ v, v ∉ A → R v ⊆ Z) (x : V → α) :
    mass S p x
      = (∏ v ∈ outSet A, ψ v x) * mass S (fun w => ∏ v ∈ A, ψ v w) x := by
  classical
  have hp : p = fun w => (∏ v ∈ A, ψ v w) * (∏ v ∈ outSet A, ψ v w) := by
    funext w
    rw [hfac w, prod_split_in_out ψ A w]
  rw [hp]
  exact mass_extract_out ψ hread hSA hZS hOut x

end FateV2.Predict.View19
