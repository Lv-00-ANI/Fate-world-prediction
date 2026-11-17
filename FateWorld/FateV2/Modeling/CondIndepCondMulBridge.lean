import FateWorld.FateV2.Modeling.CondIndepGeneralNZ
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Predict.DAGFactorization
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

/-!
  # Modeling · CondIndepCondMulBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CondIndepCondMulBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CondIndepGeneralNZ, FinCondIndep, DAGFactorization
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §CondIndepCondMulBridge  ⭐⭐⭐ **桥接 `CondIndep` 与 `CondMul`**

  ## 目的

  文档中的三条幽灵

  * `factorizesOn_of_components`
  * `factorizesOn_to_components`
  * `factorizesOn_implies_condMul_fork`

  都声称「无正性因子分解 ⟹ 条件独立」。它们的实质已在一般空间上由
  `Fate.GraphToProbView7.condIndep_general` 实现，但它用的是
  `Fate.FactorMarkov.CondIndep`（`mass` 口径），而文档用的是有限版
  `Fate.FinCondIndep.CondMul`。**本文件证明两者在 `Fin 3` 上是同一命题**，
  从而把「幽灵的一般化」真正落地。

  主定理（**B6**）：

    `CondIndep p {0} {1} {2}  ⟺  CondMul (gamma p)`

  其中 `gamma p ((x,y),z) = p (enc ((x,y),z))`，`enc` 把 `((x,y),z)` 铺成
  `Fin 3 → α`（0 位 `x`、1 位 `y`、2 位 `z`）。

  ## 交付清单

  | 编号 | 名称 | 内容 |
  |---|---|---|
  | **B1** | `enc` / `gamma` | 编码函数及其诱导的有限联合律 |
  | **B2** | `mass_univ3` | `mass univ p x = p x` |
  | **B3** | `mass_single_two` | `mass {2} p x = ∑ a, ∑ b, p (enc ((a,b), x 2))` |
  | **B4** | `mass_pair_zero_two` | `mass {0,2} p x = ∑ b, p (enc ((x 0, b), x 2))` |
  | **B5** | `mass_pair_one_two` | `mass {1,2} p x = ∑ a, p (enc ((a, x 1), x 2))` |
  | **B6** | `condIndep_iff_condMul` | **主定理** |
  | **B7** | `condMul_of_condIndep` / `condIndep_of_condMul` | 两个方向 |
  | **B8** | `condIndep_fin3_of_factorization` | 因子化 ⟹ `CondIndep` |
  | **B9** | `condMul_fin3_of_factorization` | 因子化 ⟹ `CondMul`（幽灵最字面形式）|

  ## 与前两条幽灵的对应

  * `factorizesOn_of_components`（因子化 ⟹ 条件独立）：其 `Fin 3` 可验证实例
    是 **B8**（`CondIndep` 口径）与 **B9**（`CondMul` 口径）。
  * `factorizesOn_implies_condMul_fork`：**B9** 就是它的 `Fin 3` 形态。
  * `factorizesOn_to_components`（由 `CondMul` 反推因子化）：在无正性时**不成立**；
    本文件不主张它。B6 说明至少 `CondMul` 与 `CondIndep` 两个条件独立口径
    **完全一致**，故该幽灵的「条件独立」一侧没有信息损失。

  一般空间（任意 `V`、任意 `A B Z`）上的对应结论由
  `Fate.GraphToProbView7.condIndep_general` 给出；B8/B9 是它在 `Fin 3` 上
  **可以独立验证**的实例。

  ## 诚实边界

  * `CondMul` 与 `CondIndep` 按定义都是**逐点乘性等式**，故 B6 在显式识别
    四个 `mass` 后是**等价的改写**，不含任何正性/归一化假设。
  * B8/B9 假设**完整因子化** `p = f·g·h`（三个单变量因子），比「因子图分离」
    略强；这是为了让 `Fin 3` 实例不依赖因子图分离的附加结构。
  * **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

set_option linter.unusedSectionVars false

namespace FateV2.Modeling

open FateV2.Predict
namespace CondIndepCondMulBridge

open Finset
open Fate.DAGFactorization
open Fate.FactorMarkov

variable {α : Type} [Fintype α] [DecidableEq α]

/-! ### §1 ⭐ 编码函数 `enc : (α × α) × α → (Fin 3 → α)` -/

/-- ⭐ 把 `((x,y),z) : (α × α) × α` 编码成 `Fin 3 → α`：
0 位取 `x`、1 位取 `y`、2 位取 `z`。 -/
noncomputable def enc (q : (α × α) × α) : Fin 3 → α :=
  fun v => if v = 0 then q.1.1 else if v = 1 then q.1.2 else q.2

/-- ⭐ 给定 `x : Fin 3 → α`，`x` 就是其自身三个坐标的编码。 -/
theorem enc_coords (x : Fin 3 → α) : enc ((x 0, x 1), x 2) = x := by
  funext v; fin_cases v <;> simp [enc]

@[simp] theorem enc_zero (q : (α × α) × α) : enc q 0 = q.1.1 := by
  unfold enc; simp

@[simp] theorem enc_one (q : (α × α) × α) : enc q 1 = q.1.2 := by
  unfold enc; simp

@[simp] theorem enc_two (q : (α × α) × α) : enc q 2 = q.2 := by
  unfold enc; simp

/-- ⭐ `gamma p`：把 `(Fin 3 → α) → ℝ` 读成 `FinCondIndep` 口径的有限联合律
`gamma p ((x,y),z) = p (enc ((x,y),z))`。 -/
noncomputable def gamma (p : (Fin 3 → α) → ℝ) : FateV2.Predict.FinCondIndep.FinJoint α α α :=
  fun q => p (enc q)

@[simp] theorem gamma_apply (p : (Fin 3 → α) → ℝ) (q : (α × α) × α) :
    gamma p q = p (enc q) := rfl

/-! ### §2 ⭐ 四个 `mass` 的显式识别 -/

/-- ⭐⭐ **B2**：全空间上的 `mass` 就是密度本身。 -/
theorem mass_univ3 (p : (Fin 3 → α) → ℝ) (x : Fin 3 → α) :
    mass Finset.univ p x = p x :=
  Fate.DAGFactorization.mass_univ p x

/-- ⭐⭐ **B3**：`mass {2}` 展开为对 `X`、`Y` 的双重求和
（顺序 `x` 在外、`y` 在内，与 `margZ` 的求和顺序完全一致）。 -/
theorem mass_single_two (p : (Fin 3 → α) → ℝ) (x : Fin 3 → α) :
    mass {2} p x
      = ∑ a : α, ∑ b : α, p (enc ((a, b), x 2)) := by
  have hset : (insert 1 (insert 0 ({2} : Finset (Fin 3)))) = (Finset.univ : Finset (Fin 3)) :=
    by decide
  rw [Fate.DAGFactorization.mass_insert_sum' (0 : Fin 3) ({2} : Finset (Fin 3))
    (by decide) p x]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fate.DAGFactorization.mass_insert_sum' (1 : Fin 3)
    (insert 0 ({2} : Finset (Fin 3))) (by decide) p (Fate.DAGFactorization.unpin 0 x a)]
  rw [hset]
  simp only [Fate.DAGFactorization.mass_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show Fate.DAGFactorization.unpin 1 (Fate.DAGFactorization.unpin 0 x a) b
      = enc ((a, b), x 2) from by
    funext v; fin_cases v <;> simp [Fate.DAGFactorization.unpin, enc]]

/-- ⭐⭐ **B4**：`mass {0,2}` 只对 `Y`（1 位）求和，`X` 位冻结为 `x 0`。 -/
theorem mass_pair_zero_two (p : (Fin 3 → α) → ℝ) (x : Fin 3 → α) :
    mass ({0, 2} : Finset (Fin 3)) p x
      = ∑ b : α, p (enc ((x 0, b), x 2)) := by
  have h1 : (1 : Fin 3) ∉ ({0, 2} : Finset (Fin 3)) := by decide
  rw [Fate.DAGFactorization.mass_insert_sum' (1 : Fin 3) ({0, 2} : Finset (Fin 3)) h1 p x]
  have huniv : (insert 1 ({0, 2} : Finset (Fin 3))) = (Finset.univ : Finset (Fin 3)) := by decide
  rw [huniv]
  simp only [Fate.DAGFactorization.mass_univ]
  exact Finset.sum_congr rfl fun b _ => by
    rw [show Fate.DAGFactorization.unpin 1 x b = enc ((x 0, b), x 2) from by
      funext v; fin_cases v <;> simp [Fate.DAGFactorization.unpin, enc]]

/-- ⭐⭐ **B5**：`mass {1,2}` 只对 `X`（0 位）求和，`Y` 位冻结为 `x 1`。 -/
theorem mass_pair_one_two (p : (Fin 3 → α) → ℝ) (x : Fin 3 → α) :
    mass ({1, 2} : Finset (Fin 3)) p x
      = ∑ a : α, p (enc ((a, x 1), x 2)) := by
  have h0 : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) := by decide
  rw [Fate.DAGFactorization.mass_insert_sum' (0 : Fin 3) ({1, 2} : Finset (Fin 3)) h0 p x]
  have huniv : (insert 0 ({1, 2} : Finset (Fin 3))) = (Finset.univ : Finset (Fin 3)) := by decide
  rw [huniv]
  simp only [Fate.DAGFactorization.mass_univ]
  exact Finset.sum_congr rfl fun a _ => by
    rw [show Fate.DAGFactorization.unpin 0 x a = enc ((a, x 1), x 2) from by
      funext v; fin_cases v <;> simp [Fate.DAGFactorization.unpin, enc]]

/-! ### §3 ⭐⭐⭐ **主定理 B6**：`CondIndep` 与 `CondMul` 在 `Fin 3` 上等价 -/

/-- ⭐⭐ 三个 `marg` 在 `gamma p` 上的定义展开。 -/
theorem margZ_gamma (p : (Fin 3 → α) → ℝ) (z : α) :
    FateV2.Predict.FinCondIndep.margZ (gamma p) z
      = ∑ a : α, ∑ b : α, p (enc ((a, b), z)) := rfl

theorem margXZ_gamma (p : (Fin 3 → α) → ℝ) (x z : α) :
    FateV2.Predict.FinCondIndep.margXZ (gamma p) x z
      = ∑ b : α, p (enc ((x, b), z)) := rfl

theorem margYZ_gamma (p : (Fin 3 → α) → ℝ) (y z : α) :
    FateV2.Predict.FinCondIndep.margYZ (gamma p) y z
      = ∑ a : α, p (enc ((a, y), z)) := rfl

/-- ⭐⭐⭐ **B6（主定理）**：

`CondIndep p {0} {1} {2}  ⟺  CondMul (gamma p)`。

**证明**：把 `A ∪ B ∪ Z = {0,1,2} = univ`、`A ∪ Z = {0,2}`、`B ∪ Z = {1,2}`、
`Z = {2}` 四个 `mass` 分别用 **B2–B5** 显式展开，`gamma p` 的三个 `marg` 用
定义展开。两边随即成为**逐点上完全相同的乘性等式**。 -/
theorem condIndep_iff_condMul (p : (Fin 3 → α) → ℝ) :
    Fate.FactorMarkov.CondIndep p {0} {1} {2}
      ↔ FateV2.Predict.FinCondIndep.CondMul (gamma p) := by
  have huniv : (({0} : Finset (Fin 3)) ∪ {1} ∪ {2}) = Finset.univ := by decide
  have hXZ : (({0} : Finset (Fin 3)) ∪ {2}) = ({0, 2} : Finset (Fin 3)) := by decide
  have hYZ : (({1} : Finset (Fin 3)) ∪ {2}) = ({1, 2} : Finset (Fin 3)) := by decide
  constructor
  · intro h x y z
    have hx := h (enc ((x, y), z))
    rw [huniv, hXZ, hYZ] at hx
    rw [mass_univ3, mass_pair_zero_two, mass_pair_one_two, mass_single_two] at hx
    simp only [enc_zero, enc_one, enc_two] at hx
    rw [margZ_gamma, margXZ_gamma, margYZ_gamma]
    exact hx
  · intro h x
    have hx := h (x 0) (x 1) (x 2)
    rw [margZ_gamma, margXZ_gamma, margYZ_gamma] at hx
    rw [huniv, hXZ, hYZ, mass_univ3, mass_pair_zero_two, mass_pair_one_two, mass_single_two]
    conv_lhs => rw [show x = enc ((x 0, x 1), x 2) from (enc_coords x).symm]
    exact hx

/-- ⭐⭐ **B7a**：`CondIndep` ⟹ `CondMul`。 -/
theorem condMul_of_condIndep {p : (Fin 3 → α) → ℝ}
    (h : Fate.FactorMarkov.CondIndep p {0} {1} {2}) :
    FateV2.Predict.FinCondIndep.CondMul (gamma p) :=
  (condIndep_iff_condMul p).mp h

/-- ⭐⭐ **B7b**：`CondMul` ⟹ `CondIndep`。 -/
theorem condIndep_of_condMul {p : (Fin 3 → α) → ℝ}
    (h : FateV2.Predict.FinCondIndep.CondMul (gamma p)) :
    Fate.FactorMarkov.CondIndep p {0} {1} {2} :=
  (condIndep_iff_condMul p).mpr h

/-! ### §4 ⭐⭐⭐ 幽灵的 `Fin 3` 形态（B8 / B9） -/

/-- ⭐⭐⭐ **B9**：**无正性因子分解 ⟹ `CondMul`**
（`factorizesOn_implies_condMul_fork` 的 `Fin 3` 形态）。

直接调用 `Fate.FinCondIndep.condMul_of_factorization`，
**不假设** `f, g, h ≥ 0`、**不假设**任何归一化。 -/
theorem condMul_fin3_of_factorization (p : (Fin 3 → α) → ℝ)
    (f g h : α → ℝ)
    (hfac : ∀ x y z, p (enc ((x, y), z)) = f x * g y * h z) :
    FateV2.Predict.FinCondIndep.CondMul (gamma p) :=
  FateV2.Predict.FinCondIndep.condMul_of_factorization (gamma p) f g h hfac

/-- ⭐⭐⭐ **B8**：**因子化 ⟹ `CondIndep`**
（`factorizesOn_of_components` 的 `Fin 3` 形态）。

经 B6 由 B9 转回 `mass` 口径。 -/
theorem condIndep_fin3_of_factorization (p : (Fin 3 → α) → ℝ)
    (f g h : α → ℝ)
    (hfac : ∀ x y z, p (enc ((x, y), z)) = f x * g y * h z) :
    Fate.FactorMarkov.CondIndep p {0} {1} {2} :=
  condIndep_of_condMul (condMul_fin3_of_factorization p f g h hfac)

end CondIndepCondMulBridge

end FateV2.Modeling