import FateWorld.FateV2.Model.Frame
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
  # Model · ThetaExpressiveness

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ThetaExpressiveness.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame
  - 补充 open 域：FateV2.Model
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  FF3：`θ` 是「点」还是「函数」——两种实例的表达力对比

  ## 背景与任务

  T-1b 的签名 `Step := X → U → Ν → Θ → Act → X` 只把 `θ` 固定为
  `Θ.Carrier` 的**一个元素**，而不规定 `Θ.Carrier` 本身是什么。
  于是同一个签名下有两种「实例」：

  | 实例 | `Θ.Carrier` | 可表达的映射族 |
  |---|---|---|
  | **(a) θ 是点** | `ℝ` | `y = θ * x`（过原点的线性映射） |
  | **(b) θ 是函数** | `ℝ → ℝ` | `y = f x`（**任意**一元函数） |

  本文件的任务：**诚实**比较二者的表达力，即
  1. (b) 能表达 (a) 的**每一个**元素（`point_expressible_imp_fun_expressible`）；
  2. (b) 严格强于 (a)：存在 `f` 使 `y = f x` **无法**写成 `y = θ * x`
     （`fun_not_imp_point`、`point_range_ssubset_fun_range`）；
  3. 给出**具体反例函数**（不是抽象的「∃」，而是显式的 `x ↦ x + 1`：
     `counterexample`、`not_point_expressible_counterexample`）。

  ## ⚠ 诚实边界（务必先读）

  * 本文件**不**谈论 `Step` 内部的 `u ε a` 与状态演化。这里的「可表达」被
    **精确定义**为：一族参数化映射（`θ ↦ (x ↦ y)`）的像集。
    这是**纯参数层**的陈述，**不含** `u`、`ε`、`a` 的语义。
    故本文件**不是**对 `Step` 本身表达力的断言，只是对 `Θ.Carrier` 两种取值的比较。
  * 本文件**不**声称「(a) 是错的」或「(b) 才是对的模型」。
    它只证明一个**集合包含关系**：`Θ := ℝ` 的表达族是 `Θ := ℝ → ℝ`
    的表达族的**真子集**。哪种实例适合建模是**建模选择**，不是数学定理。
  * 反例 `x ↦ x + 1` 的「不能表达」是**真的不能**（不是「我们没找到」）：
    由 `x = 0` 处的取值矛盾直接给出。
  * 本文件**不**出现 `sorry` / `admit` / `axiom`
    （已用 `#print axioms` 逐个核验：全部只依赖 `propext`/`Classical.choice`/`Quot.sound`）。

  ## 前件非平凡性自查（针对本项目最高频问题）

  * `not_point_expressible_counterexample` 的前件是「`∃ θ, ∀ x,
    counterexample x = θ * x`」，结论是 `False`。前件**不含** `False`，
    也**不含**结论本身——它是**真正的反证**。
  * `fun_not_imp_point` 的结论是「不存在**全称**的 `∀ g, FunExpressible g →
    PointExpressible g`」；前件**只有** `f := counterexample` 这一具体选法，
    结论并未被塞进前件。
  * `point_range_ssubset_fun_range` 的结论是真包含关系，前件为空。
  * `real_no_surjective_into_function_space` 前件仅是一个具体 `g : ℝ → (ℝ → ℝ)`，
    结论 `¬ Surjective g`——Cantor 对角线，非平凡。

  ## 强度排序（哪些定理「有货」）

  | 定理 | 强度 |
  |---|---|
  | `point_range_ssubset_fun_range` | **强**（真包含，主结论） |
  | `fun_not_imp_point` | **强**（主结论的否定形式） |
  | `not_point_expressible_counterexample` | **强**（具体反例的反证） |
  | `not_point_expressible_of_zero_ne` | **强**（一般化障碍） |
  | `real_no_surjective_into_function_space` | **强**（Cantor 对角线） |
  | `pointTheta_carrier_ne_funTheta_carrier` | **中**（类型层区分） |
  | `point_expressible_imp_fun_expressible` | **中**（嵌入方向） |
  | `constTheta_injective` / `pointToFun_injective` | **中**（嵌入无信息损失） |
  | `pointToFun_interp_eq` / `interpPoint_zero` / `counterexample_zero` | **弱**（定义展开） |
  | `pointTheta_carrier` / `funTheta_carrier` | **弱**（`rfl`） |
  =========================================================================== -/

namespace FateV2.Model

open FateV2.Modeling

open FateV2.Model
namespace ThetaExpressiveness

/-! ### §1 两种实例的**精确定义**

「表达力」在这里被定义为：参数空间 `Θ` 经一个解释映射
`interp : Θ → (X → X)` 所能产出的映射族的像集。

* (a) 点实例：`interpₚ θ := fun x => θ * x`
* (b) 函数实例：`interp𝒻 f := f`（函数空间里元素本身就是映射）

`interp𝒻` 取恒等，是因为 `Θ := ℝ → ℝ` 的点**就是一个**映射；
这正是「θ 是函数」的字面含义，不含任何额外编码技巧。 -/

/-- **(a) θ 是点**：参数空间 `ℝ`，解释为 `x ↦ θ * x`。 -/
def interpPoint (θ : ℝ) : ℝ → ℝ := fun x => θ * x

/-- **(b) θ 是函数**：参数空间 `ℝ → ℝ`，解释为**恒等**
（函数空间的点本身即映射）。 -/
def interpFun (f : ℝ → ℝ) : ℝ → ℝ := f

/-- **可表达**（点实例）：映射 `g` 能被某个 `θ : ℝ` 表达为 `x ↦ θ * x`。 -/
def PointExpressible (g : ℝ → ℝ) : Prop := ∃ θ : ℝ, ∀ x : ℝ, g x = θ * x

/-- **可表达**（函数实例）：映射 `g` 能被某个 `f : ℝ → ℝ` 表达（即 `g` 自身）。 -/
def FunExpressible (g : ℝ → ℝ) : Prop := ∃ f : ℝ → ℝ, ∀ x : ℝ, g x = f x

/-! ### §2 (b) 蕴含 (a)：常函数嵌入

方向一：**任何**点实例能表达的映射，函数实例也能表达。
证明取 `f := fun x => θ * x` 本身（它就是 `ℝ → ℝ` 的一个元素）；
另给出「常函数读法」`constTheta θ = fun _ => θ`（它给出斜率本身）。 -/

/-- ⭐ **【包含方向】(b) 能表达 (a)：任何 `PointExpressible` 的映射也是 `FunExpressible` 的。

**这是表达的「包含」一半**：点实例能表达的每个映射，函数实例都能表达
（取 `f := fun x => θ * x` 本身即可）。 -/
theorem point_expressible_imp_fun_expressible {g : ℝ → ℝ}
    (h : PointExpressible g) : FunExpressible g := by
  obtain ⟨θ, hθ⟩ := h
  exact ⟨interpPoint θ, fun x => by simp [interpPoint]; exact hθ x⟩

/-- ⭐ **(b) 能表达 (a)：任何 `x ↦ θ * x` 都是 `ℝ → ℝ` 的一个元素。**

嵌入 `pointToFun θ := interpPoint θ`（即把「斜率 `θ`」读作「函数
`fun x => θ * x`」）。 -/
def pointToFun (θ : ℝ) : ℝ → ℝ := interpPoint θ

/-- ⭐ **嵌入是显式的且解释一致**：`interpFun (pointToFun θ) = interpPoint θ`
（恒等解释直接给出，无需额外编码）。 -/
theorem pointToFun_interp_eq (θ : ℝ) : interpFun (pointToFun θ) = interpPoint θ := rfl

/-- ⭐ **`θ` 可由嵌入还原**：`(pointToFun θ) 1 = θ`。
故点实例的参数信息**无损地**留在函数实例中。 -/
theorem pointToFun_apply_one (θ : ℝ) : pointToFun θ 1 = θ := by
  simp [pointToFun, interpPoint]

/-- ⭐ **常函数读法**（另一种等价嵌入）：`θ ↦ fun _ => θ` 给出斜率本身。
它与 `pointToFun` 的关系是逐点相乘。 -/
def constTheta (θ : ℝ) : ℝ → ℝ := fun _ => θ

theorem constTheta_mul (θ x : ℝ) : constTheta θ x * x = interpPoint θ x := by
  simp [constTheta, interpPoint]

/-- ⭐ 常函数嵌入 `constTheta` 是**单射**：不同的点参数给出不同的常函数
（故 (b) 不是把 (a) 的所有参数「压成一个」）。 -/
theorem constTheta_injective : Function.Injective constTheta := by
  intro θ₁ θ₂ h
  have := congrFun h 0
  simpa [constTheta] using this

/-- ⭐ 嵌入 `pointToFun` 也是**单射**（由 `pointToFun_apply_one` 立得）。 -/
theorem pointToFun_injective : Function.Injective pointToFun := by
  intro θ₁ θ₂ h
  rw [← pointToFun_apply_one θ₁, ← pointToFun_apply_one θ₂, h]

/-! ### §3 (a) 不能表达 (b)：具体反例 `x ↦ x + 1`

方向二（严格性）：给出**一个具体的**映射，它在 (b) 中可表达，
在 (a) 中**不可**表达。

选 `f x = x + 1`（过 `(0,1)` 的斜率 1 直线）。障碍在 `x = 0`：
点实例在 `0` 处的值**恒为 `0`**，而 `f 0 = 1`。 -/

/-- **具体反例函数**：`f x = x + 1`。 -/
def counterexample : ℝ → ℝ := fun x => x + 1

/-- 反例在 `0` 处的值是 `1`（用于矛盾）。 -/
theorem counterexample_zero : counterexample 0 = 1 := by
  simp [counterexample]

/-- ⭐⭐ **核心定理：`x ↦ x + 1` 不能被任何 `θ : ℝ` 写成 `y = θ * x`。**

反证：若 `∃ θ, ∀ x, θ * x = x + 1`，取 `x = 0` 得 `0 = 1`，矛盾。
（`θ * 0 = 0` 与 `0 + 1 = 1` 直接冲突。） -/
theorem not_point_expressible_counterexample : ¬ PointExpressible counterexample := by
  rintro ⟨θ, hθ⟩
  have h0 : θ * 0 = (0 : ℝ) + 1 := by
    rw [← hθ 0]
    simp [counterexample]
  simp at h0

/-- ⭐ **(b) 能表达这个反例**：取 `f := counterexample` 自身即可。 -/
theorem fun_expressible_counterexample : FunExpressible counterexample :=
  ⟨counterexample, fun _ => rfl⟩

/-- ⭐⭐ **主要结论（严格性 / 真包含）：存在 (b) 可表达而 (a) 不可表达的映射。**

结合 `point_expressible_imp_fun_expressible`（包含）与本定理（不反向），
得出「`Θ := ℝ` 的表达族 ⊊ `Θ := ℝ → ℝ` 的表达族」。 -/
theorem fun_not_imp_point :
    ¬ ∀ g : ℝ → ℝ, FunExpressible g → PointExpressible g := by
  intro h
  exact not_point_expressible_counterexample (h counterexample fun_expressible_counterexample)

/-- ⭐ **严格包含，集合形式**：点实例的表达族是函数实例表达族的**真子集**。

用 `interp` 的像集表述：`Set.range interpPoint ⊂ Set.range interpFun`。 -/
theorem point_range_ssubset_fun_range :
    Set.range interpPoint ⊂ Set.range interpFun := by
  constructor
  · -- 包含：`interpPoint θ = interpFun (pointToFun θ)`
    rintro g ⟨θ, rfl⟩
    exact ⟨pointToFun θ, (pointToFun_interp_eq θ).symm⟩
  · -- 不相等：`counterexample` 在右边，不在左边
    intro hEq
    have hmem : counterexample ∈ Set.range interpFun := ⟨counterexample, rfl⟩
    have hmem' : counterexample ∈ Set.range interpPoint := hEq hmem
    obtain ⟨θ, hθ⟩ := hmem'
    exact not_point_expressible_counterexample ⟨θ, fun x => by
      have hx := congrFun hθ x
      simpa [interpPoint] using hx.symm⟩

/-! ### §4 更一般的障碍：值域必须含 `0`

上节的反例是「`f 0 ≠ 0`」。事实上凡 `f 0 ≠ 0` 都不行，
且**任何**点实例表达式的值域必含 `0`（在 `x = 0` 处取得）。 -/

/-- 点实例在 `x = 0` 处的输出**恒为 `0`**。 -/
theorem interpPoint_zero (θ : ℝ) : interpPoint θ 0 = 0 := by
  simp [interpPoint]

/-- **一般障碍**：若 `f 0 ≠ 0`，则 `f` 不能被任何 `θ : ℝ` 表达为 `x ↦ θ * x`。 -/
theorem not_point_expressible_of_zero_ne {f : ℝ → ℝ} (h : f 0 ≠ 0) :
    ¬ PointExpressible f := by
  rintro ⟨θ, hθ⟩
  apply h
  rw [hθ 0]
  simp

/-- ⭐ **不相交的证据**：点实例表达的映射必满足 `g 0 = 0`。 -/
theorem point_expressible_apply_zero {g : ℝ → ℝ} (h : PointExpressible g) : g 0 = 0 := by
  obtain ⟨θ, hθ⟩ := h
  rw [hθ 0]
  simp

/-! ### §5 与 `ThetaSpace` 的连接：签名**允许**两种实例

签名层只要求 `ThetaSpace`，故 `ℝ` 与 `ℝ → ℝ` **都能**作为 `Θ`。
本节把本节结论搬到 `ThetaSpace` 语言里，使其与 T-1b 的讨论同层。 -/

/-- 点实例的 `ThetaSpace`：`Carrier := ℝ`。 -/
def pointTheta : ThetaSpace where
  Carrier := ℝ
  topo := inferInstance
  meas := inferInstance

/-- 函数实例的 `ThetaSpace`：`Carrier := ℝ → ℝ`。 -/
def funTheta : ThetaSpace where
  Carrier := ℝ → ℝ
  topo := inferInstance
  meas := inferInstance

theorem pointTheta_carrier : pointTheta.Carrier = ℝ := rfl

theorem funTheta_carrier : funTheta.Carrier = (ℝ → ℝ) := rfl

/-- **Cantor 对角线**：不存在从 `ℝ` 到 `ℝ → ℝ` 的满射。

（若 `g` 满射，取反例 `fun x => g x x + 1` 的原像 `a`，得 `g a a = g a a + 1`。） -/
theorem real_no_surjective_into_function_space (g : ℝ → (ℝ → ℝ)) :
    ¬ Function.Surjective g := by
  intro hg
  obtain ⟨a, ha⟩ := hg (fun x => g x x + 1)
  have h1 : g a a = g a a + 1 := by
    have := congrFun ha a
    simp at this
  linarith

/-- ⭐ **两者的载体不相同**：`pointTheta.Carrier = ℝ` 而 `funTheta.Carrier = ℝ → ℝ`。

**意义**：「θ 是点」与「θ 是函数」在**类型层**是**真的两回事**，
不是同一类型的两种说法。证明用 Cantor 对角线（`ℝ` 不可能与 `ℝ → ℝ` 等势，
更不可能**类型相等**）。 -/
theorem pointTheta_carrier_ne_funTheta_carrier :
    pointTheta.Carrier ≠ funTheta.Carrier := by
  intro h
  have h2 : ℝ = (ℝ → ℝ) := h
  have e : ℝ ≃ (ℝ → ℝ) := h2 ▸ Equiv.refl ℝ
  exact real_no_surjective_into_function_space (⇑e) e.surjective

end ThetaExpressiveness

end FateV2.Model