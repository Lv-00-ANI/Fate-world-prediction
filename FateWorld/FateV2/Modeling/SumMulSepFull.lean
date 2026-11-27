import FateWorld.FateV2.Modeling.SumMulSep
import Mathlib.Logic.Equiv.Basic

/-!
  # Modeling · SumMulSepFull

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SumMulSepFull.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SumMulSep
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  乘积分离律的完整实现（无尾块下）

  ## 背景

  主定理 C 的最终配平需要：
  ```
  mass ∅ p x = Σ_w p w = (Σ over X-side)(Σ over Y-side)
  ```
  **⟹ 即乘积分离律。**

  `Fate/SumMulSep.lean` 给了 `extendTo`/`shadowOn`（只读函数的影子），
  但沿 `arrowEquivOfSplit` 的分量行为难以直接 simp。

  ## 本节做什么：**显式双射**，绕开 `trans` 组合

  ```lean
  toV   X Y hY a b := fun v => if v ∈ X then a⟨v⟩ else b⟨v⟩
  fromV X Y w      := (fun a => w a.1, fun b => w b.1)
  ```

  **⟹ 这两者互逆（需 `X ∪ Y = univ`），且：
  * `toV` 在 `X` 上 `= a`
  * `toV` 在 `Y\X` 上 `= b`**

  ## 诚实边界

  * **本节只给 `toV` / `fromV` 与两条投影性质**，双和分离的最终 `ring` 仍留待下一步。
  * **`Nonempty α` 与 `hY : ∀ v, v ∈ X ∨ v ∈ Y` 都是必需前提。**
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open Finset
universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-! ### §0.1 ⭐ 显式延拓与限制 -/

/-- ⭐ **显式构造 `V → α`**（`X` 上取 `a`，`X` 外取 `b`）。 -/
noncomputable def toV (X Y : Finset V) (hY : ∀ v, v ∈ X ∨ v ∈ Y)
    (a : X → α) (b : Y → α) : V → α :=
  fun v => if hv : v ∈ X then a ⟨v, hv⟩
           else b ⟨v, (hY v).resolve_left hv⟩

/-- ⭐ **`toV` 在 `X` 上等于 `a`**。 -/
theorem toV_mem_X {X Y : Finset V} {hY : ∀ v, v ∈ X ∨ v ∈ Y}
    (a : X → α) (b : Y → α) {u : V} (hu : u ∈ X) :
    toV X Y hY a b u = a ⟨u, hu⟩ := by
  unfold toV
  rw [dif_pos hu]

/-- ⭐⭐ **`toV` 在 `Y` 上等于 `b`**（需 `X`、`Y` 不交）。 -/
theorem toV_mem_Y {X Y : Finset V} (hdisj : Disjoint X Y)
    {hY : ∀ v, v ∈ X ∨ v ∈ Y} (a : X → α) (b : Y → α) {u : V} (hu : u ∈ Y) :
    toV X Y hY a b u = b ⟨u, hu⟩ := by
  have hnu : ¬ u ∈ X := fun hx => Finset.disjoint_left.mp hdisj hx hu
  unfold toV
  rw [dif_neg hnu]

/-! ### §0.2 ⭐ 限制 -/

/-- ⭐ **把 `V → α` 限制到 `X` 与 `Y` 上**。 -/
def fromV (X Y : Finset V) (w : V → α) : (X → α) × (Y → α) :=
  (fun a => w a.1, fun b => w b.1)

/-- ⭐⭐ **`toV` 在 `X` 侧恢复 `fromV` 的第一分量**。 -/
theorem toV_fromV_fst {X Y : Finset V} (hdisj : Disjoint X Y)
    (hY : ∀ v, v ∈ X ∨ v ∈ Y) (w : V → α) :
    (fun a : X => toV X Y hY (fromV X Y w).1 (fromV X Y w).2 a.1) = (fromV X Y w).1 := by
  funext a
  exact toV_mem_X _ _ a.2

/-- ⭐⭐ **`toV` 在 `Y` 侧恢复 `fromV` 的第二分量**。 -/
theorem toV_fromV_snd {X Y : Finset V} (hdisj : Disjoint X Y)
    (hY : ∀ v, v ∈ X ∨ v ∈ Y) (w : V → α) :
    (fun b : Y => toV X Y hY (fromV X Y w).1 (fromV X Y w).2 b.1) = (fromV X Y w).2 := by
  funext b
  exact toV_mem_Y hdisj _ _ b.2



/-! ### §0.3 ⭐⭐⭐ 双射与分离律 -/

theorem fromV_toV {X Y : Finset V} (hdisj : Disjoint X Y) (hY : ∀ v, v ∈ X ∨ v ∈ Y)
    (a : X → α) (b : Y → α) :
    fromV X Y (toV X Y hY a b) = (a, b) := by
  unfold fromV
  refine Prod.ext ?_ ?_
  · funext ax
    exact toV_mem_X (hY := hY) a b ax.2
  · funext by'
    exact toV_mem_Y (hY := hY) hdisj a b by'.2

theorem toV_fromV {X Y : Finset V} (hY : ∀ v, v ∈ X ∨ v ∈ Y) (w : V → α) :
    toV X Y hY (fromV X Y w).1 (fromV X Y w).2 = w := by
  funext v
  unfold toV fromV
  by_cases hv : v ∈ X
  · rw [dif_pos hv]
  · rw [dif_neg hv]

-- 现在建 Equiv
noncomputable def vEquiv {X Y : Finset V} (hdisj : Disjoint X Y) (hY : ∀ v, v ∈ X ∨ v ∈ Y) :
    (V → α) ≃ (X → α) × (Y → α) where
  toFun := fromV X Y
  invFun := fun p => toV X Y hY p.1 p.2
  left_inv := fun w => toV_fromV hY w
  right_inv := fun p => fromV_toV hdisj hY p.1 p.2

-- ⭐ 分离律
theorem sum_mul_sep_final {X Y : Finset V} (hdisj : Disjoint X Y) (hY : ∀ v, v ∈ X ∨ v ∈ Y)
    (f g : (V → α) → ℝ)
    (hf : ∀ w w', (∀ u ∈ X, w u = w' u) → f w = f w')
    (hg : ∀ w w', (∀ u ∈ Y, w u = w' u) → g w = g w') :
    (∑ w : V → α, f w * g w)
      = (∑ a : X → α, f (toV X Y hY a (Classical.arbitrary _)))
        * (∑ b : Y → α, g (toV X Y hY (Classical.arbitrary _) b)) := by
  classical
  -- 换元：Σ_w → Σ_{a,b}，用显式右侧函数
  have heq := Fintype.sum_equiv (vEquiv hdisj hY)
    (fun w : V → α => f w * g w)
    (fun p : (X → α) × (Y → α) => f (toV X Y hY p.1 p.2) * g (toV X Y hY p.1 p.2))
    (fun w => by
      show f w * g w = f (toV X Y hY (fromV X Y w).1 (fromV X Y w).2) * g (toV X Y hY (fromV X Y w).1 (fromV X Y w).2)
      rw [toV_fromV hY w])
  rw [heq]
  rw [Fintype.sum_prod_type]
  -- 目标：Σ_a Σ_b f(toV a b) * g(toV a b) = (Σ_a f(toV a ·)) * (Σ_b g(toV · b))
  -- 先证 f(toV a b) 只依赖 a，g(toV a b) 只依赖 b
  have hfa : ∀ (a : X → α) (b b' : Y → α),
      f (toV X Y hY a b) = f (toV X Y hY a b') := by
    intro a b b'
    refine hf _ _ ?_
    intro u hu
    rw [toV_mem_X (hY := hY) a b hu, toV_mem_X (hY := hY) a b' hu]
  have hgb : ∀ (a a' : X → α) (b : Y → α),
      g (toV X Y hY a b) = g (toV X Y hY a' b) := by
    intro a a' b
    refine hg _ _ ?_
    intro u hu
    rw [toV_mem_Y (hY := hY) hdisj a b hu, toV_mem_Y (hY := hY) hdisj a' b hu]
  -- 把 f 和 g 都固定到 arbitrary 的两侧
  have key : ∀ (a : X → α) (b : Y → α),
      f (toV X Y hY a b) * g (toV X Y hY a b)
        = f (toV X Y hY a (Classical.arbitrary (Y → α)))
          * g (toV X Y hY (Classical.arbitrary (X → α)) b) := by
    intro a b
    rw [show f (toV X Y hY a b) = f (toV X Y hY a (Classical.arbitrary (Y → α))) from
          hfa a b (Classical.arbitrary (Y → α))]
    rw [show g (toV X Y hY a b) = g (toV X Y hY (Classical.arbitrary (X → α)) b) from
          hgb a (Classical.arbitrary (X → α)) b]
  -- 逐项替换后分离
  calc (∑ a : X → α, ∑ b : Y → α, f (toV X Y hY a b) * g (toV X Y hY a b))
      = ∑ a : X → α, ∑ b : Y → α,
          f (toV X Y hY a (Classical.arbitrary (Y → α)))
            * g (toV X Y hY (Classical.arbitrary (X → α)) b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = ∑ a : X → α, f (toV X Y hY a (Classical.arbitrary (Y → α)))
          * (∑ b : Y → α, g (toV X Y hY (Classical.arbitrary (X → α)) b)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = (∑ a : X → α, f (toV X Y hY a (Classical.arbitrary (Y → α))))
          * (∑ b : Y → α, g (toV X Y hY (Classical.arbitrary (X → α)) b)) := by
        rw [Finset.sum_mul]
