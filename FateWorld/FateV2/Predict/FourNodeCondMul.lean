import FateWorld.FateV2.Predict.FactorRecursionRouteB
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
  # Predict · FourNodeCondMul

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FourNodeCondMul.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorRecursionRouteB, FinCondIndep
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/FourNodeCondMul` —— **第 8 路（概率侧）：四节点链上的因子分解 ⟹ 条件独立**

  ## 0. 定位与划界

  图侧（`dSep`）在 `Fate/FourNodeSeparation.lean`。本文件做**概率侧**：
  在四节点链 `0 → 1 → 2 → 3` 上，从**因子分解**形式推出 `CondMul`
  （即 `X ⊥ Y | (Z₁,Z₂)` 的乘性形式）。

  **⚠ 本文件不声称 `LMG ⟹ 全局 Markov`**（那是第 5 路）。
  本文件只做**一个具体的四节点情形**：直接对链做**显式乘积计算**。

  ## 1. 交付清单

  | # | 名称 | 内容 | 状态 |
  |---|---|---|---|
  | **C1** | `Chain4Law` | 四节点链的因子分解**形式**（`φ₀·φ₁·φ₂·φ₃`，读集 = 父集）| ✅ 定义 |
  | **C2** | `Chain4Law.toJoint` | 把它读成 `FinJoint α α (α×α)` | ✅ 定义 |
  | **C3** | `margZ_eq` | ⭐ `margZ = (Σφ₀φ₁)·φ₂·(Σφ₃)` | ✅ 零缺口 |
  | **C4** | `margXZ_eq` | ⭐ `margXZ = φ₀(x)φ₁(x,z₁)·φ₂(z)·(Σφ₃)` | ✅ 零缺口 |
  | **C5** | `margYZ_eq` | ⭐ `margYZ = (Σφ₀φ₁)·φ₂(z)·φ₃(z₂,y)` | ✅ 零缺口 |
  | **C6** | **`chain4_condMul`** | ⭐⭐⭐ **`CondMul (toJoint L)`**（`X ⊥ Y \| (Z₁,Z₂)`）| ✅ 零缺口 |
  | **C7** | `chain4_not_condMul_uncond` | 反例：**不**条件化时 `X ⊥̸ Y` ⟹ 条件集不可去 | ✅ 数值见证 |

  **⟹ 本条是**第一份**在**四节点**上把「因子分解（读集 = 父集）」与
  「`CondMul`」**显式连起来**的机器校验定理。

  ## 2. 链 `0→1→2→3` 的因子分解（`Factorizes` 的口径）

  `FactorRecursionRouteB.Factorizes` 说：`∃ φ, (φ v 只读 pa G v) ∧ p = ∏ φ_v`。

  对链 `0→1→2→3`（拓扑序 `0,1,2,3`）：
  * `pa 0 = ∅` ⟹ `φ₀` 只读空集 ⟹ **`φ₀` 是常数**（❗但我们要保留 `x₀` 的依赖
    —— 不对：`mass` 口径下 `φ₀` 是 `x₀ → ℝ`，因为 `x₀` 是**自由坐标**，
    `pa 0 = ∅` 意味着 `φ₀` **不读任何其它坐标**，但**可以读 `x₀` 自己**）。

  **⟹ 口径对齐（关键）**：`Factorizes` 的「只读 `pa G v`」指
  「`φ_v` 的值只由 `pa G v` 上的坐标决定，**加上 `x v` 自身**」
  —— 否则 `p` 无法依赖 `v` 的取值。本文件把这一点**显式化**：

  $$\varphi_v = \varphi_v\bigl(x_v \;|\; x_{\mathrm{pa}(v)}\bigr),$$

  即 `φ_v : α → (V → α) → ℝ` 形式。为了让下游能直接用，
  本文件给出**并行的独立形式** `Chain4Law`（下文 C1），
  它的四个因子**按读集参数化**（`φ₀ : α → ℝ`、`φ₁ : α → α → ℝ`、
  `φ₂ : α → α → ℝ`、`φ₃ : α → α → ℝ`），语义与 `Factorizes` **一致**。

  ⚠ **诚实边界**：本文件**没有**把 `Chain4Law` 与
  `FactorRecursionRouteB.Factorizes` 的形式**机器等价**地连起来
  （那需要 `pa`/`topoOrder` 的具体化，属段 1 的工作）。本文件的结论是
  **「链形因子分解 ⟹ `CondMul`」**，本身**完整无缺口**，
  并且在语义上正是 `Factorizes` 对链的展开。 -/

namespace FateV2.Predict
namespace FourNodeCondMul

open Finset
open FateV2.Predict.FinCondIndep (FinJoint CondMul margZ margXZ margYZ)

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 `Chain4Law`：四节点链的因子分解形式
  =========================================================================== -/

/-- ⭐ **C1（四节点链的因子分解）**：

$$P(x_0, x_1, x_2, x_3)
  = \varphi_0(x_0)\;\varphi_1(x_0, x_1)\;\varphi_2(x_1, x_2)\;\varphi_3(x_2, x_3).$$

**读集**：`φ_k` 恰好读「`k` 自己 + `pa k = {k-1}`」，与链 `0→1→2→3`
的父集**逐一对齐**：

| 因子 | 读集 | `pa k` | 对齐 |
|---|---|---|---|
| `φ₀` | `{x₀}` | `∅`（+ 自身）| ✅ |
| `φ₁` | `{x₀, x₁}` | `{x₀}` | ✅ |
| `φ₂` | `{x₁, x₂}` | `{x₁}` | ✅ |
| `φ₃` | `{x₂, x₃}` | `{x₂}` | ✅ |

**⟹ 这就是 `Factorizes` 在链上的展开形式**（`φ_v = φ_v(x_v | x_pa(v))`）。 -/
structure Chain4Law (α : Type u) where
  /-- `φ₀(x₀)`：源点的局部机制。 -/
  φ₀ : α → ℝ
  /-- `φ₁(x₀, x₁)`：读 `pa 1 = {0}`。 -/
  φ₁ : α → α → ℝ
  /-- `φ₂(x₁, x₂)`：读 `pa 2 = {1}`。 -/
  φ₂ : α → α → ℝ
  /-- `φ₃(x₂, x₃)`：读 `pa 3 = {2}`。 -/
  φ₃ : α → α → ℝ

/-- **C1′（联合律的读出）**：`Chain4Law` 在 `Fin 4 → α` 上的值。 -/
noncomputable def Chain4Law.p (L : Chain4Law α) (x : Fin 4 → α) : ℝ :=
  L.φ₀ (x 0) * L.φ₁ (x 0) (x 1) * L.φ₂ (x 1) (x 2) * L.φ₃ (x 2) (x 3)

/-- **C2（读成 `FinJoint α α (α × α)`）**：把 `X = 0`、`Y = 3`、
`(Z₁, Z₂) = (1, 2)` 拆出来。

$$p\;((x, y), (z_1, z_2)) = \varphi_0(x)\varphi_1(x, z_1)\varphi_2(z_1, z_2)\varphi_3(z_2, y).$$
-/
noncomputable def Chain4Law.toJoint (L : Chain4Law α) : FinJoint α α (α × α) :=
  fun q => L.φ₀ q.1.1 * L.φ₁ q.1.1 q.2.1 * L.φ₂ q.2.1 q.2.2 * L.φ₃ q.2.2 q.1.2

/-! ===========================================================================
  §2 ⭐ 三个边缘律的**显式值**（零缺口）

  记 `A z₁ := Σ_{x} φ₀(x) φ₁(x, z₁)`、`B z₂ := Σ_{y} φ₃(z₂, y)`
  以及 `C z₁ z₂ := φ₂(z₁, z₂)`。则

  * `margXZ(x, z₁, z₂) = φ₀(x) φ₁(x,z₁) · φ₂(z₁,z₂) · B z₂`
  * `margYZ(y, z₁, z₂) = A z₁ · φ₂(z₁,z₂) · φ₃(z₂, y)`
  * `margZ(z₁, z₂)      = A z₁ · φ₂(z₁,z₂) · B z₂`

  **⟹ 代入乘性等式，两边同等于**
  `φ₀(x)φ₁(x,z₁) · φ₂(z₁,z₂)² · A z₁ · B z₂ · φ₃(z₂,y)`。
  =========================================================================== -/

/-- `A z₁ = Σ_x φ₀(x) φ₁(x, z₁)`（`x` 与 `z₁` 的联合质量，差 `φ₂·φ₃` 因子）。 -/
noncomputable def Chain4Law.A (L : Chain4Law α) (z₁ : α) : ℝ :=
  ∑ x : α, L.φ₀ x * L.φ₁ x z₁

/-- `B z₂ = Σ_y φ₃(z₂, y)`。 -/
noncomputable def Chain4Law.B (L : Chain4Law α) (z₂ : α) : ℝ :=
  ∑ y : α, L.φ₃ z₂ y

/-- **C3**：`margZ (toJoint L) (z₁,z₂) = A z₁ · φ₂(z₁,z₂) · B z₂`。

**零缺口**：逐点展开为三重乘积，内外求和分离。 -/
theorem margZ_eq (L : Chain4Law α) (z₁ z₂ : α) :
    margZ L.toJoint (z₁, z₂) = L.A z₁ * L.φ₂ z₁ z₂ * L.B z₂ := by
  unfold FinCondIndep.margZ Chain4Law.toJoint Chain4Law.A Chain4Law.B
  -- 逐层把与求和无关的因子提出
  have hstep : ∀ x : α,
      (∑ y : α, L.φ₀ x * L.φ₁ x z₁ * L.φ₂ z₁ z₂ * L.φ₃ z₂ y)
        = L.φ₀ x * L.φ₁ x z₁ * L.φ₂ z₁ z₂ * (∑ y : α, L.φ₃ z₂ y) := by
    intro x
    rw [Finset.mul_sum]
  simp only [hstep]
  rw [Finset.sum_mul]
  rw [Finset.sum_mul]

/-- **C4**：`margXZ (toJoint L) x (z₁,z₂) = φ₀(x) φ₁(x,z₁) · φ₂(z₁,z₂) · B z₂`。

**零缺口**。 -/
theorem margXZ_eq (L : Chain4Law α) (x z₁ z₂ : α) :
    margXZ L.toJoint x (z₁, z₂)
      = L.φ₀ x * L.φ₁ x z₁ * L.φ₂ z₁ z₂ * L.B z₂ := by
  unfold FinCondIndep.margXZ Chain4Law.toJoint Chain4Law.B
  rw [Finset.mul_sum]

/-- **C5**：`margYZ (toJoint L) y (z₁,z₂) = A z₁ · φ₂(z₁,z₂) · φ₃(z₂,y)`。

**零缺口**。 -/
theorem margYZ_eq (L : Chain4Law α) (y z₁ z₂ : α) :
    margYZ L.toJoint y (z₁, z₂)
      = L.A z₁ * L.φ₂ z₁ z₂ * L.φ₃ z₂ y := by
  unfold FinCondIndep.margYZ Chain4Law.toJoint Chain4Law.A
  simp only []
  calc (∑ x : α, L.φ₀ x * L.φ₁ x z₁ * L.φ₂ z₁ z₂ * L.φ₃ z₂ y)
      = ∑ x : α, L.φ₀ x * L.φ₁ x z₁ * (L.φ₂ z₁ z₂ * L.φ₃ z₂ y) :=
        Finset.sum_congr rfl fun x _ => by ring
    _ = (∑ x : α, L.φ₀ x * L.φ₁ x z₁) * (L.φ₂ z₁ z₂ * L.φ₃ z₂ y) :=
        (Finset.sum_mul (Finset.univ : Finset α) _ _).symm
    _ = (∑ x : α, L.φ₀ x * L.φ₁ x z₁) * L.φ₂ z₁ z₂ * L.φ₃ z₂ y := by ring

/-! ===========================================================================
  §3 ⭐⭐⭐ **C6：主定理 —— 链形因子分解 ⟹ `CondMul`**
  =========================================================================== -/

/-- ⭐⭐⭐ **C6（主定理）**：四节点链 `0→1→2→3` 上，**任何**满足

$$P = \varphi_0(x_0)\varphi_1(x_0,x_1)\varphi_2(x_1,x_2)\varphi_3(x_2,x_3)$$

的联合律都满足 `X ⊥ Y | (Z₁,Z₂)` 的**乘性**形式：

$$P(x, z_1, z_2, y)\cdot \mathrm{margZ}(z_1,z_2)
  = \mathrm{margXZ}(x,z_1,z_2)\cdot \mathrm{margYZ}(y,z_1,z_2).$$

**证明**：三个边缘律的显式值（C3/C4/C5）代入后，两边同为

$$\varphi_0(x)\varphi_1(x,z_1)\;\varphi_2(z_1,z_2)^2\;A_{z_1}\,B_{z_2}\;\varphi_3(z_2,y).$$

**零缺口**：无 `sorry`、无额外假设（`L` 任意，`α` 任意有限类型）。 -/
theorem chain4_condMul (L : Chain4Law α) : CondMul L.toJoint := by
  intro x y z
  obtain ⟨z₁, z₂⟩ := z
  rw [margZ_eq, margXZ_eq, margYZ_eq]
  simp only [Chain4Law.toJoint]
  ring

/-- **C6′（同一结论，显式写出 `γ` 为乘积槽 `(z₁,z₂)`）**：

`CondMul` 对 `(X, Y, (Z₁, Z₂))` 的**字面**展开。 -/
theorem chain4_condMul_explicit (L : Chain4Law α) :
    ∀ (x y : α) (z₁ z₂ : α),
      L.toJoint ((x, y), (z₁, z₂)) * margZ L.toJoint (z₁, z₂)
        = margXZ L.toJoint x (z₁, z₂) * margYZ L.toJoint y (z₁, z₂) := by
  intro x y z₁ z₂
  exact chain4_condMul L x y (z₁, z₂)

/-! ===========================================================================
  §4 ⭐ **C7：反例 —— 不条件化时 `X ⊥̸ Y`**（条件集不可去）
  =========================================================================== -/

/-- 反例参数（`Fin 2` 上，全部取 `1` 或 `0`，便于手算）。

想造「`0` 与 `3` **边缘不独立**」的链：取 `φ₀ ≡ 1`、`φ₁(x, z) = if x = z then 1 else 0`
（`x₁` 复制 `x₀`）、`φ₂(z, w) = if z = w then 1 else 0`（`x₂` 复制 `x₁`）、
`φ₃(w, y) = if w = y then 1 else 0`（`x₃` 复制 `x₂`）。

**⟹ 只有四个状态有质量（`x₀=x₁=x₂=x₃`），每个质量 `1`。**
于是 `x₀ = x₃` 恒成立 ⟹ **边缘上 `X` 与 `Y` 完全相关**。 -/
def copy₀ : Fin 2 → ℝ := fun _ => 1
/-- `φ₁(x, z) = [x = z]`。 -/
def copy₁ : Fin 2 → Fin 2 → ℝ := fun x z => if x = z then 1 else 0
/-- `φ₂(z, w) = [z = w]`。 -/
def copy₂ : Fin 2 → Fin 2 → ℝ := fun z w => if z = w then 1 else 0
/-- `φ₃(w, y) = [w = y]`。 -/
def copy₃ : Fin 2 → Fin 2 → ℝ := fun w y => if w = y then 1 else 0

/-- 反例的 `Chain4Law`。 -/
def copyLaw : Chain4Law (Fin 2) where
  φ₀ := copy₀
  φ₁ := copy₁
  φ₂ := copy₂
  φ₃ := copy₃

/-- ⭐ **C7**：`copyLaw` 的联合律在**不**条件化时 `X ⊥̸ Y`。

**具体见证**：`(x, y) = (0, 1)`。

* `p(x=0, y=1)` 的边缘质量 = `0`（复制律要求 `x = y`）；
* `p_X(0) · p_Y(1) = 1 · 1 = 1`（每个值恰有一个状态，质量 `1`）。

故 `0 ≠ 1`，**边缘不独立**。

`copyLaw` 在 `X`、`Y` 上的边缘质量（对 `(z₁,z₂)` 求和）： -/
noncomputable def copyXY (x y : Fin 2) : ℝ :=
  ∑ z₁ : Fin 2, ∑ z₂ : Fin 2, copyLaw.toJoint ((x, y), (z₁, z₂))

/-- `copyXY (0, 1) = 0`（复制律 `x₀ = x₃` 被违反）。 -/
theorem copyXY_0_1 : copyXY 0 1 = 0 := by
  unfold copyXY Chain4Law.toJoint copyLaw copy₀ copy₁ copy₂ copy₃
  simp

/-- `copyXY (0, 0) = 1`（唯一状态 `0000`）。 -/
theorem copyXY_0_0 : copyXY 0 0 = 1 := by
  unfold copyXY Chain4Law.toJoint copyLaw copy₀ copy₁ copy₂ copy₃
  simp

/-- `copyXY (1, 1) = 1`（唯一状态 `1111`）。 -/
theorem copyXY_1_1 : copyXY 1 1 = 1 := by
  unfold copyXY Chain4Law.toJoint copyLaw copy₀ copy₁ copy₂ copy₃
  simp

/-- ⭐⭐ **C7（反例）**：`(0,1)` 处 `P(X=0, Y=1) · (总质量) ≠ P(X=0) · P(Y=1)`。

即**不条件化**时 `X` 与 `Y` **不**独立 —— 故 C6 的条件集 `(Z₁,Z₂)` **不可去**。

**计算**：`p(0,1) = 0`、总质量 `= 2`、`p_X(0) = 1`、`p_Y(1) = 1` ⟹ `0·2 = 0 ≠ 1 = 1·1`。 -/
theorem chain4_not_indep_uncond :
    copyXY 0 1 * (copyXY 0 0 + copyXY 0 1 + copyXY 1 0 + copyXY 1 1)
      ≠ (copyXY 0 0 + copyXY 0 1) * (copyXY 0 0 + copyXY 1 0) := by
  rw [copyXY_0_0, copyXY_0_1, copyXY_1_1]
  -- `copyXY 1 0 = 0`（同样违反复制律）
  have h10 : copyXY 1 0 = 0 := by
    unfold copyXY Chain4Law.toJoint copyLaw copy₀ copy₁ copy₂ copy₃
    simp
  rw [h10]
  norm_num

/-! ===========================================================================
  §5 与 `FactorRecursionRouteB` 的接口（**诚实登记不完整**）

  `FactorRecursionRouteB.mass_factorizes_single` 已证：`pa G v ⊆ S` 时

  $$\mathrm{mass}_S\,p\,x = \varphi_v(x)\cdot\mathrm{mass}_S\Bigl(\prod_{w\neq v}\varphi_w\Bigr)x .$$

  **本文件用它对 `chain4DAG` 的四个顶点各做一次**，即可得 `mass` 口径的
  「逐点」结论。**但把它组织成完整 `LMG`/`CondMul` 还需要**：

  1. `pa G v` 对 `chain4DAG` 的**显式值**（`pa 0 = ∅`、`pa 1 = {0}`、
     `pa 2 = {1}`、`pa 3 = {2}`）；
  2. 剩余乘积 `∏_{w≠v} φ_w` 的读集 ⊆ `insert v (nd v ∪ pa v)` —— **对链成立**，
     但需要**逐点**验证（`φ₀` 读 `{x₀}`、`φ₃` 读 `{x₂,x₃}` …）；
  3. `mass` 的 4 次迭代与 `FinJoint` 口径的 `margZ/margXZ/margYZ` 的**对齐**。

  **⟹ 本文件 §3 的 `chain4_condMul` 走的是**直接的乘积计算**路线
  （不经过 `mass`），它**完整覆盖**链形因子分解 ⟹ `CondMul` 这一命题。
  `mass` 路线的对齐**留给段 1/段 2**，本文**不声称**做了它。 -/

end FourNodeCondMul
end FateV2.Predict