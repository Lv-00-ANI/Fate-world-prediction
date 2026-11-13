import FateWorld.Legacy.SubMassPlan
import FateWorld.Legacy.MassIndepOfCompl
import FateWorld.Legacy.MassInsertCorrected

/-! ===========================================================================
  §0  ⭐ 子系统 `mass` 的两块基石

  ## 背景

  `Fate/SubMassPlan.lean` 指出：`CondIndep` 中四个 `mass` 的 `S` 都是
  `U = X∪Y∪Z` 的子集，若 `p` 只读 `U`，则四个 `mass` 都带同一个
  `|α|^(|V|-|U|)` 因子，可以约掉。

  本文件提供两个基石：

  ## 一、`mass_const`

  ```lean
  theorem mass_const (S) (c) (x) :
      mass S (fun _ => c) x = |α|^(|V| - |S|) * c
  ```

  即常数被积函数时，`mass` 就是纤维大小。

  ## 二、`mass_indep_outside`

  ```lean
  theorem mass_indep_outside (hSU : S ⊆ U) (hg : g 只读 U) (x y) :
      mass S g x = mass S g (glueT U x y)
  ```

  即 `mass S g x` 与 `x` 在 `U` 外的取值**无关**
  （`glueT U x y` 在 `U` 上取 `x`、在 `U` 外取 `y`）。

  ## 用途

  有了这两条，可以把 `mass S g x` 化成「`U` 外固定为某值」的形式，
  再提取 `|α|^(|V|-|U|)` 因子——这正是 `CondIndep` 无 `cover` 版本所需。
  =========================================================================== -/

namespace Fate.Block2
open Finset Fate Fate.DAGFactorization
open Causalean.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

set_option maxHeartbeats 1000000

-- mass_const（已证）
theorem mass_const (S : Finset V) (c : ℝ) (x : V → α) :
    mass S (fun _ => c) x = ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card)) * c := by
  have hc : mass S (fun _ => c) x = c * mass S (fun _ => (1:ℝ)) x := by
    unfold mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hh : ∀ u ∈ S, w u = x u <;> simp [hh]
  rw [hc, Fate.GraphToProbView7.mass_one_card]
  ring

-- mass_indep_outside（已证）
theorem mass_indep_outside {U S : Finset V} (hSU : S ⊆ U) {g : (V → α) → ℝ}
    (hg : ∀ w w', (∀ u ∈ U, w u = w' u) → g w = g w') (x y : V → α) :
    mass S g x = mass S g (Fate.C17.glueT U x y) := by
  apply mass_congr
  intro u hu
  exact (Fate.C17.glueT_mem (hSU hu)).symm

-- ⭐ 关键推论：mass S g x = mass S g (glueT U x x)，而 glueT U x x 在 U 外 = x（还是 x）
-- 实际上 glueT U x x = x。需要 y 在 U 外有特定值才有用。
-- 例如 y := 全 false，则 glueT U x y 在 U 上 = x，在 U 外 = false
-- ⟹ mass S g x = mass S g (固定 U 外的取值)

-- 这告诉我们：可以让 U 外的取值固定为某个常数

-- 下一步：把 mass S g x 写成「U 外固定后」的形式，再用 |α|^(|V|-|U|) 因子

end Fate.Block2
