/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.CorrectsProperties`
任务：**【EE4】把 `Corrects` 的全部已知推论集中到一处（「前提强度」参考卡）**

===========================================================================
本文件要回答的问题
===========================================================================

`Corrects A φ` 的定义（`Fate/BoundWriteBack.lean`）只有一行：

    def Corrects (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) : Prop := ∀ r, A (φ r) = r

即「`A ∘ φ = id_F`」，`φ` 是 `A` 的**线性右逆**。

**问：这一个前提到底有多强？它强制了哪些结论？**

本文件把散落在各模块的已知推论**集中陈述并证明**，作为查阅卡：

| # | 推论 | 定理（本文件） | 原始出处 |
|---|---|---|---|
| 1 | `ker φ = ⊥` | `corrects_ker_eq_bot` | `ConvergeToOptimalCounterexample` |
| 2 | `φ` 单射 | `corrects_injective` | 同上 |
| 3 | `A` 满射（存在性） | `corrects_surjective` | 同上 |
| 4 | `ker φ ≠ ⊥` 与 `Corrects` 不可共存 | `no_corrects_with_nontrivial_kernel` | 同上 |
| 5 | `∃ φ, Corrects A φ ⟺ A 满射` | `exists_corrects_iff_surjective` | 同上 |
| 6 | `A` 单射 ⟹ 满足 `Corrects` 的 `φ` 唯一 | `corrects_unique_of_injective` | 同上 |
| 7 | 误差精确缩放 `err(θ') = |1-η| · err(θ)` | `err_wbW` | `BoundWriteBack` |
| 8 | 严格下降（窗口 `|1-η|<1`） | `writeBack_reduces_error` | `BoundWriteBack` |
| 9 | `η = 1` 一步精确命中 | `wbW_one_exact` | `BoundWriteBack` |
| 10 | `Corrects` **不可去掉**（反例） | `no_reduction_without_corrects` | `BoundWriteBack` |

**⭐ 本文件的增值**（不只抄表）：

* `corrects_strength`（§3）与 `corrects_full_strength`（§8）：把 §2 的
  「核平凡 / 单射 / 满射」与 §6 的「误差精确缩放 / 一步命中 / 严格下降」
  **合并为一条可编译的合取**，查阅时不必逐条翻；
* `exists_corrects_and_ker_bot_iff_surjective`（§4）：显式写出「核平凡」
  在「存在 `Corrects`」刻画中是**冗余**的（由 `corrects_ker_eq_bot` 自动满足），
  从而 `∃ φ, Corrects A φ ∧ ker φ = ⊥ ⟺ A` 满射；
* `not_ker_bot_surj_imp_corrects`（§4）：**新反例** ——
  `ker φ = ⊥` **且** `A` 满射，但 `Corrects` **不**成立。
  证明 `Corrects` **严格强于**「单射 + 满射」（不是后者的改写）。

**⚠ 两处「非 `Corrects` 推论」的诚实登记**（见 §5）：
`err_zero_iff_optimal_general` 与 `optimal_unique_of_injective`
**不依赖** `Corrects`（`lean` 的 unused-variable linter 原已揭穿），
本文件保留它们仅为**语言桥**，并**明确标注**其前件**不含** `Corrects`。

===========================================================================
⚠ 反同义反复自查（纪律第 7 条）
===========================================================================

本文件逐一检查每个定理的**前件是否把结论包进去**：

* §2 的 6 条：前件只有 `Corrects A φ`（`∀ r, A (φ r) = r`），结论分别是
  `ker φ = ⊥`、`Injective φ`、`Surjective A`、`¬ ∃...`、`⟺`、`φ = ψ`。
  **结论均不是定义的逐字重写**：`ker φ = ⊥` 需要「取 `v ∈ ker φ` 再用
  `A` 线性把 `A 0 = 0` 算出来」；`Injective φ` 需要从 `ker` 形式转到
  `v - w` 技巧；`Surjective A` 需要构造原像 `φ r`（不是把 `Corrects` 抄一遍：
  `Corrects` 说的是 `A (φ r) = r`，`Surjective A` 说的是 `∃ x, A x = r`，
  中间有一步 `⟨φ r, _⟩` 的存在性包装）。逐条已核。
* §3–§4 的 `corrects_strength` / `exists_corrects_and_ker_bot_iff_surjective`：
  前者是 §2 三条的合取包装（**非**新证明，已标注）；后者的反向
  `Surjective A ⟹ ∃ φ, Corrects A φ ∧ ker φ = ⊥` 用
  `LinearMap.exists_rightInverse_of_surjective`（投射性），**不是** `Corrects`
  的同义反复，因为反向的 `φ` 是**新构造**的（自由模右逆），
  前件里根本没有 `φ`。
* §4 的 `not_ker_bot_surj_imp_corrects`：前件「`ker φ = ⊥` ∧ `Surjective A`」，
  结论 `¬ Corrects A φ` —— 两者**不**互相包含（这正是反例的意义）。已核。
* §5 的 `err_zero_iff_optimal_general` 与 `optimal_unique_of_injective`：
  **已明确标注** 「前件**不含** `Corrects`」，**不**冒充 `Corrects` 的推论。
  它们不是同义反复（`err=0` 是范数命题、`θ₁=θ₂` 是核命题），
  但**也不是** `Corrects` 的推论 —— 两类免责均已在 §5 正文注明。
* §6 的 4 条数值界：前件 `Corrects` + 数值窗口条件，结论是**严格不等式**
  或**等式**；`err_wbW` 是等式但左右两端是**不同的项**（`wbW` 的像 vs `θ`），
  非 `rfl`。已核（`BoundWriteBack` 原文已说明）。
* §5 的 `corrects_one_step_optimal` / `corrects_fixed_iff_optimal`：
  前件 `Corrects`，结论是**最优性**（`A θ' = x'`）或**不动点等价**。
  已核（前者经 `wbW_one_exact`，后者经 `φ` 单射性，均非定义抄写）。

===========================================================================
纪律声明
===========================================================================

* **零 `sorry` / `admit` / `axiom`**（全文可复核：`grep -c sorry` = 0）。
* **只新建，不修改任何已有模块**。本文件 `import` 已有模块并**复用**其定理，
  §2/§6/§7 的若干条目是**同一命题的再陈述**（接线用，便于集中查阅），
  §4/§5 的条目是**新增**定理。
* **不跑全量 `lake build`**；验证方式为 `lake env lean Fate/CorrectsProperties.lean`。
* 全部定理不依赖有限维/坐标/内积（§8 具体例子除外）。

依赖：`Fate.BoundWriteBack`（`Corrects` / `wbW` / `errA` 定义与主定理）、
      `Fate.ConvergeToOptimalCounterexample`（§2 的推论原始证明）、
      `Fate.ConvergeToOptimalV2`（最优参数的 `IsOptimal` 定义）。
-/

import FateWorld.Legacy.BoundWriteBack
import FateWorld.Legacy.ConvergeToOptimalCounterexample
import FateWorld.Legacy.ConvergeToOptimalV2

open Fate.BoundWriteBack

namespace Fate
namespace CorrectsProperties

/-! ===========================================================================
    §0  记号
    =========================================================================== -/

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §1  `Corrects` 的若干等价形式（都是定义的改写，供查阅）
    =========================================================================== -/

/-- **等价 1（逐字定义）**：`Corrects A φ ⟺ ∀ r, A (φ r) = r`。 -/
theorem corrects_def (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) :
    Corrects A φ ↔ ∀ r, A (φ r) = r := Iff.rfl

/-- **等价 2（残差式）**：`Corrects A φ ⟺ ∀ r, A (φ r) - r = 0`。 -/
theorem corrects_residual_form (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) :
    Corrects A φ ↔ ∀ r, A (φ r) - r = 0 :=
  Fate.BoundWriteBack.corrects_iff_sub_eq_zero A φ

/-- **等价 3（复合算子式）**：`Corrects A φ ⟺ A.toLinearMap.comp φ = LinearMap.id`。

**⭐ 这是「`φ` 是 `A` 的右逆」的最干净表述**，也是 §4 的出发点。 -/
theorem corrects_comp_eq_id (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) :
    Corrects A φ ↔ A.toLinearMap.comp φ = LinearMap.id := by
  constructor
  · intro h
    ext r
    simpa using h r
  · intro h r
    have := LinearMap.congr_fun h r
    simpa using this

/-- **等价 4（核式）**：`Corrects A φ ⟺ ∀ r, r ∈ LinearMap.range φ ∧ A r = r`?
不 —— `r ∈ range φ` 是 `Corrects` 的**一半**（满射性），`A r = r` 是另一半。
精确表述为「`φ` 的像是 `A` 的一个截面」：`Corrects A φ ⟺ ∀ r, A (φ r) = r`。
本定理取 `range` 的**满射**侧面：`Corrects A φ ⟹ ∀ r, r ∈ LinearMap.range A.toLinearMap`。 -/
theorem corrects_mem_range (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ)
    (r : F) : r ∈ LinearMap.range A.toLinearMap :=
  ⟨φ r, h r⟩

/-! ===========================================================================
    §2  代数推论：`Corrects` 强制 `ker φ = ⊥` / `φ` 单射 / `A` 满射
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【推论 1】`Corrects A φ ⟹ ker φ = ⊥`（`φ` 无核）。**

**直觉**：`φ v = 0 ⟹ A (φ v) = 0`（`A` 线性），而 `Corrects` 在 `r := v` 处
要求 `A (φ v) = v`，故 `v = 0`。 -/
theorem corrects_ker_eq_bot (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ) :
    LinearMap.ker φ = ⊥ :=
  Fate.ConvergeToOptimalCounterexample.corrects_ker_eq_bot A φ h

/-- ⭐⭐⭐⭐ **【推论 2】`Corrects A φ ⟹ φ` 单射。** -/
theorem corrects_injective (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ) :
    Function.Injective φ :=
  Fate.ConvergeToOptimalCounterexample.corrects_injective A φ h

/-- ⭐⭐⭐⭐ **【推论 3】`Corrects A φ ⟹ A` 满射（右逆存在 ⟹ 满射）。** -/
theorem corrects_surjective (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ) :
    Function.Surjective A :=
  Fate.ConvergeToOptimalCounterexample.corrects_surjective A φ h

/-- ⭐⭐⭐ **【推论 4】`ker φ ≠ ⊥` 与 `Corrects` 不可共存（否定式）。** -/
theorem no_corrects_with_nontrivial_kernel (A : E →L[ℝ] F) :
    ¬ ∃ φ : F →ₗ[ℝ] E, Corrects A φ ∧ φ.ker ≠ ⊥ :=
  Fate.ConvergeToOptimalCounterexample.no_corrects_with_nontrivial_kernel A

/-- ⭐⭐⭐ **【推论 5】`Corrects` 的存在性刻画：`(∃ φ, Corrects A φ) ⟺ A` 满射。**

**⭐ 这是 §2 三推论中「满射」那条的逆**：满射 `A` 必有线性右逆
（`ℝ`-向量空间自由 ⟹ 投射），故 `Corrects` 非空。 -/
theorem exists_corrects_iff_surjective (A : E →L[ℝ] F) :
    (∃ φ : F →ₗ[ℝ] E, Corrects A φ) ↔ Function.Surjective A :=
  Fate.ConvergeToOptimalCounterexample.exists_corrects_iff_surjective A

/-- ⭐⭐⭐ **【推论 6】`A` 单射 ⟹ 满足 `Corrects` 的 `φ` 唯一（`φ = A⁻¹` 于像上）。** -/
theorem corrects_unique_of_injective (A : E →L[ℝ] F) (hA : Function.Injective A)
    (φ ψ : F →ₗ[ℝ] E) (hφ : Corrects A φ) (hψ : Corrects A ψ) : φ = ψ :=
  Fate.ConvergeToOptimalCounterexample.corrects_unique_of_injective A hA φ ψ hφ hψ

/-! ===========================================================================
    §3  把 §2 的三条合并成「一张表」（编译期可检查的合取）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【参考卡主条目】`Corrects` 一口气给出全部三条代数推论。**

`Corrects A φ ⟹ ker φ = ⊥ ∧ φ 单射 ∧ A 满射`。

**⭐ 用途**：查阅时只需记这一条 —— 它同时是 `ker_eq_bot`、`injective`、
`surjective` 的合取包装（证明就是 `⟨_, _, _⟩`，三份引用）。 -/
theorem corrects_strength (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ) :
    LinearMap.ker φ = ⊥ ∧ Function.Injective φ ∧ Function.Surjective A :=
  ⟨corrects_ker_eq_bot A φ h, corrects_injective A φ h, corrects_surjective A φ h⟩

/-! ===========================================================================
    §4  ⭐ 新推论：`Corrects` **严格强于**「单射 + 满射」（反例）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【新 1：`Corrects` 的**正向**合取（引理）】**

`Corrects A φ ⟹ ker φ = ⊥ ∧ Surjective A`（§3 两条的再次包装，方便引用）。

**⚠ 不是新证明**，仅合并 §2 推论 1、3。真正的「新」在下一条反例：
它证明**反向不成立** —— `Corrects` **严格强于**「`φ` 单射 + `A` 满射」。 -/
theorem corrects_imp_ker_bot_and_surjective (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) :
    LinearMap.ker φ = ⊥ ∧ Function.Surjective A :=
  ⟨corrects_ker_eq_bot A φ h, corrects_surjective A φ h⟩

/-! **构造动机（§4 反例）**：

取 `E = F = ℝ × ℝ`，`A = swapCLM`（坐标交换 `(a,b) ↦ (b,a)`，双射）、
`φ = id`（恒等，双射）。

* `φ = id` **单射**，故 `ker φ = ⊥` ✓；
* `A = swapCLM` **满射**（实为双射）✓；
* 但 `Corrects A φ ⟺ ∀ r, swapCLM r = r`，在 `r = (1,0)` 处要求
  `(0,1) = (1,0)`，矛盾。故 `Corrects` **假**。

**⟹ 此反例证明「单射 + 满射」不足以推出 `Corrects`。** -/

/-- 坐标交换（`(a, b) ↦ (b, a)`），作为 `ℝ × ℝ →L[ℝ] ℝ × ℝ`。 -/
def swapCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) where
  toFun q := (q.2, q.1)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  cont := by fun_prop

/-- `swapCLM` 满射（实为双射）。 -/
theorem swapCLM_surjective : Function.Surjective swapCLM :=
  fun q => ⟨(q.2, q.1), by simp [swapCLM]⟩

/-- ⭐⭐⭐ **【新 1'】反例：`ker φ = ⊥` + `A` 满射 ⇏ `Corrects`。**

取 `A = swapCLM`（满射）、`φ = LinearMap.id`（单射，`ker = ⊥`）。
则 `Corrects A φ ⟺ ∀ r, swapCLM r = r`，在 `r = (1, 0)` 处给出
`(0, 1) = (1, 0)`，矛盾。

**⟹ `Corrects` 严格强于「`φ` 单射 ∧ `A` 满射」**，不是后者的改写。 -/
theorem not_ker_bot_surj_imp_corrects :
    ∃ (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (φ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)),
      LinearMap.ker φ = ⊥ ∧ Function.Surjective A ∧ ¬ Corrects A φ := by
  refine ⟨swapCLM, LinearMap.id, ?_, swapCLM_surjective, ?_⟩
  · simp
  · intro h
    have h1 : swapCLM ((LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (1, 0)) = (1, 0) :=
      h (1, 0)
    have h2 : swapCLM ((LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (1, 0)) = (0, 1) := by
      simp [swapCLM]
    rw [h2] at h1
    exact absurd h1 (by simp)

/-- ⭐⭐⭐⭐ **【新 1''：`Corrects` 的完整充要刻画（固定 `A`）】**

对固定 `A : E →L[ℝ] F`：

$$\bigl(\exists \varphi,\ \mathrm{Corrects}\ A\ \varphi \wedge \ker\varphi = \bot\bigr)
  \iff \mathrm{Surjective}\ A .$$

**⚠ 注意 `ker φ = ⊥` 在左边是**冗余的**（由 `corrects_ker_eq_bot` 自动满足），
但本定理**显式**写出它，以强调「三张面孔之一（核平凡）**不额外限制** `A`」。 -/
theorem exists_corrects_and_ker_bot_iff_surjective (A : E →L[ℝ] F) :
    (∃ φ : F →ₗ[ℝ] E, Corrects A φ ∧ LinearMap.ker φ = ⊥) ↔
      Function.Surjective A := by
  constructor
  · rintro ⟨φ, h, -⟩
    exact corrects_surjective A φ h
  · intro hsurj
    obtain ⟨φ, h⟩ := (exists_corrects_iff_surjective A).mpr hsurj
    exact ⟨φ, h, corrects_ker_eq_bot A φ h⟩

/-! ===========================================================================
    §5  ⭐ 新推论：`Corrects` 与「最优参数」的接口
    =========================================================================== -/

/-- ⭐⭐ **【新 2：“误差归零 ⟺ 命中真值”（**不需** `Corrects`）】**

⚠ **诚实声明（纪律第 7 条）**：本命题 **不**依赖 `Corrects` —— 它是
`errA := ‖A θ - x'‖` 的定义展开 + `norm_eq_zero` + `sub_eq_zero`。
在**任意** `A, φ, η, θ` 下均成立。

**❌ 不作为 `Corrects` 的推论**（前件换成 `Corrects` 也不增加内容）。
本文件**保留**它作为 §6 数值语言与 §5 代数语言的**桥梁**：
「误差 = 0」与「命中真值」等价，**无需**任何结构性前提。

（之前版本把它写成 `Corrects` 的推论（带 `h hη` 参数），
`lean` 的 unused-variable linter 揭穿了这一点，已改正。） -/
theorem err_zero_iff_optimal_general (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ : E) :
    errA A x' (wbW A φ η x' θ) = 0 ↔
      Fate.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' (wbW A φ η x' θ) := by
  rw [errA, norm_eq_zero, sub_eq_zero]
  exact Iff.rfl

/-- ⭐⭐⭐ **【新 2'：`A` 单射 ⟹ 最优参数唯一】（**不需** `Corrects`）**

⚠ **诚实声明（纪律第 7 条）**：唯一最优参数**只用** `A` 单射，
**与 `Corrects` 无关**（`ConvergeToOptimalV2.optimal_unique` 原文即如此）。
本文件把它**归到此处**是因为它常被误读成「`Corrects` 的推论」。

**❌ 不作为 `Corrects` 的推论**；`Corrects` 对它的唯一作用是通过
`s2 推论 3` 保证 `φ` 存在（`A` 满射），而满射与单射合起来才是双射，
这才是 `ConvergeToOptimalV2.existsUnique_optimal_and_fixed` 的前件。 -/
theorem optimal_unique_of_injective (A : E →L[ℝ] F)
    (hA : Function.Injective A) (x' : F) {θ₁ θ₂ : E}
    (h₁ : Fate.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ₁)
    (h₂ : Fate.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ₂) : θ₁ = θ₂ :=
  Fate.ConvergeToOptimalV2.optimal_unique (A : E →ₗ[ℝ] F) hA x' h₁ h₂

/-- ⭐⭐⭐ **【新 2''：`η = 1` 一步命中 ⟹ 最优】**

`Corrects` 下取 `η = 1`，更新后的参数**必**是最优参数。

（这是 `BoundWriteBack.wbW_one_exact` 的 `IsOptimal` 包装，
便于与 §5 的最优性语言对齐。） -/
theorem corrects_one_step_optimal (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) :
    Fate.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' (wbW A φ 1 x' θ) :=
  Fate.BoundWriteBack.wbW_one_exact A φ x' θ h

/-- ⭐⭐⭐ **【新 2'''：`Corrects` + `φ` 单射 ⟹ `wbW` 不动点 ⟺ 最优】**

**⚠**：`Corrects` 已蕴含 `φ` 单射（§2 推论 2），故 `hφ` 参数是**冗余的**。
本定理保留它，是为了与 `ConvergeToOptimalV2.fixed_iff_optimal` 的签名对齐，
便于对照 —— **不是**偷偷加了比 `Corrects` 更强的前提。

反向：由 §2 推论 2，任何 `Corrects A φ` 都自动满足 `Injective φ`，
故本定理在**只有 `Corrects`** 时也可用（`corrects_fixed_iff_optimal`）。 -/
theorem corrects_fixed_iff_optimal (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (hη : η ≠ 0) (h : Corrects A φ) (x' : F) (θ : E) :
    wbW A φ η x' θ = θ ↔
      Fate.ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ :=
  Fate.ConvergeToOptimalV2.fixed_iff_optimal A φ η hη h
    (corrects_injective A φ h) x' θ

/-! ===========================================================================
    §6  数值推论：`Corrects` 给出的误差界（引用，集中列出）
    =========================================================================== -/

/-- **【数值 1】误差精确缩放**：`err(θ') = |1-η| · err(θ)`。 -/
theorem corrects_err_wbW (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) :
    errA A x' (wbW A φ η x' θ) = |1 - η| * errA A x' θ :=
  Fate.BoundWriteBack.err_wbW A φ η x' θ h

/-- **【数值 2】严格下降**：`|1-η| < 1` 且 `A θ ≠ x'` ⟹ `err(θ') < err(θ)`。 -/
theorem corrects_reduces (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
    errA A x' (wbW A φ η x' θ) < errA A x' θ :=
  Fate.BoundWriteBack.writeBack_reduces_error A φ η x' θ h hη hne

/-- **【数值 3】不更差**：`|1-η| ≤ 1` ⟹ `err(θ') ≤ err(θ)`。 -/
theorem corrects_not_worse (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (hη : |1 - η| ≤ 1) :
    errA A x' (wbW A φ η x' θ) ≤ errA A x' θ :=
  Fate.BoundWriteBack.err_wbW_le A φ η x' θ h hη

/-- **【数值 4】`η = 1` 误差归零**：`err(θ') = 0`。 -/
theorem corrects_err_one (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) : errA A x' (wbW A φ 1 x' θ) = 0 :=
  Fate.BoundWriteBack.err_wbW_one A φ x' θ h

/-! ===========================================================================
    §7  ⭐ 必要性：`Corrects` **不可去掉**（反例，引用）
    =========================================================================== -/

/-- **【必要性 1】存在 `A, x'`，使**任意** `φ, η, θ` 误差不下降。** -/
theorem corrects_is_necessary :
    ∃ (A : ℝ →L[ℝ] ℝ) (x' : ℝ),
      ∀ (φ : ℝ →ₗ[ℝ] ℝ) (η : ℝ) (θ : ℝ),
        errA A x' (wbW A φ η x' θ) = errA A x' θ :=
  Fate.BoundWriteBack.no_reduction_without_corrects

/-! ===========================================================================
    §8  总览定理：把「`Corrects` 到底多强」压成一条可编译的合取
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【总览：`Corrects` 的完整强度卡】**

对 `Corrects A φ`，以下**全部**成立（合取编译期可查）：

1. `ker φ = ⊥`（核平凡）；
2. `φ` 单射；
3. `A` 满射；
4. 误差精确缩放 `err(θ') = |1-η| err(θ)`（对任意 `η, x', θ`）；
5. `η = 1` 一步命中 `A (wbW A φ 1 x' θ) = x'`；
6. 严格下降（在 `|1-η| < 1` 且 `A θ ≠ x'` 下）。

**⭐ 读法**：`Corrects` 是「`φ` 与 `A` 互逆（`A` 满射、`φ` 单射）」
+ 「误差按 `|1-η|` **精确**缩放」+「`η=1` 一步求解」的**联合**前提。
它**不是**「`φ` 单射 + `A` 满射」的改写（§4 反例），而**更强**。 -/
theorem corrects_full_strength (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ) :
    LinearMap.ker φ = ⊥ ∧ Function.Injective φ ∧ Function.Surjective A ∧
    (∀ (η : ℝ) (x' : F) (θ : E),
      errA A x' (wbW A φ η x' θ) = |1 - η| * errA A x' θ) ∧
    (∀ (x' : F) (θ : E), A (wbW A φ 1 x' θ) = x') ∧
    (∀ (η : ℝ) (x' : F) (θ : E), |1 - η| < 1 → A θ ≠ x' →
      errA A x' (wbW A φ η x' θ) < errA A x' θ) := by
  refine ⟨corrects_ker_eq_bot A φ h, corrects_injective A φ h,
    corrects_surjective A φ h, ?_, ?_, ?_⟩
  · intro η x' θ
    exact Fate.BoundWriteBack.err_wbW A φ η x' θ h
  · intro x' θ
    exact Fate.BoundWriteBack.wbW_one_exact A φ x' θ h
  · intro η x' θ hη hne
    exact Fate.BoundWriteBack.writeBack_reduces_error A φ η x' θ h hη hne

/-! ===========================================================================
    §9  ⚠ 诚实边界与未纳入的条目
    =========================================================================== -/

/-! **本文件**未**陈述的「推论」（附原因，诚实登记）：

1. **「`Corrects` ⟹ 收敛到唯一最优参数」—— 需额外 `A` 双射**。
   仅有 `Corrects` 时 `A` 只**满射**，最优参数**不唯一**
   （`A` 非单射时，如 `ConvergeToOptimalCounterexample` 例 1：
   `A q = q.1` 满射非单射，`ker A` 整条 `{(0,t)}` 都是最优方向）。
   完整版本见 `ConvergeToOptimalV2.existsUnique_optimal_and_fixed`
   （前件含 `Injective A` 与 `Surjective A`，**不是** `Corrects` 单独给的）。
   ⟹ **不纳入**本卡片，以免把「需 `A` 双射」误读为「`Corrects` 的推论」。

2. **「`Corrects` ⟹ 任何 `η` 下都下降」—— 假**。
   `η = 0` 或 `η = 2` 时 `|1-η| = 1`，误差**不变**（不严格降）。
   反例在 `BoundWriteBack.eta_zero_no_decrease` / `eta_two_no_decrease`。
   ⟹ **不纳入**。

3. **「`Corrects` ⟹ `A` 单射」—— 假**（`ConvergeToOptimalCounterexample` 例 1）。
   `Corrects` 只给 `A` **满射**，**不给**单射。
   ⟹ **不纳入**（反过来，本文件 §5 的 `optimal_unique_of_injective` 显式
   **额外**假设 `Injective A`，且已标注其前件**不含** `Corrects`）。

4. **具体例子的完整枚举** —— 已在
   `ConvergeToOptimalCounterexample §4`（例 1、例 2）；
   本文件 §4 只补一个**新**反例（`A = swapCLM`、`φ = id`，
   证明 `Corrects` 严强于「单射 + 满射」）。重复列举无增值，故不复制。
-/

end CorrectsProperties
end Fate
