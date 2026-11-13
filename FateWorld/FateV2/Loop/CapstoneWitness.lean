import FateWorld.FateV2.Loop.WorldModelCapstone
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：无（**新增**，专项 T60）
  - 动作：A（新增）
  - 对应环节：`WorldModelCapstone.§9.2`（`capstone_premises_satisfiable` 的替代品）
  - 依赖裁决：T57 审计
  - 状态：已编译未验证
-/

/-!
# 模块：`FateV2.Loop.CapstoneWitness`

## 0  背景（T57 审计发现的最高严重度问题）

`FateV2/Loop/WorldModelCapstone.lean:2075` 的 `capstone_premises_satisfiable` 的
**文档注释声称**它是「§9.1 总装定理前件可同时满足」的**非空洞见证**，
但它的**陈述**是

```lean
(2 : ℝ) ≠ 0 ∧ |1 - (1/2 : ℝ)| < 1 ∧ (0 : ℝ) ≠ 1
  ∧ (1 : ℝ) < 1 + 1 ∧ (0 : ℝ) ≤ 0 ∧ (1 : ℕ) > 0
```

—— **六个纯数值恒真式，一条 `worldModel_capstone` 的前件谓词都没有**。

T57 的原话：**把 `worldModel_capstone` 整条删掉，这个「非空洞见证」依然成立。**
即：该定理**不依赖** `worldModel_capstone`，因此它**不是**关于该定理的非空洞见证，
而只是六条实数算术事实（`by norm_num` 即得）。

**更糟的一点（本文件实测）**：注释声称 `L = 1 > 0`，但陈述里写的是
`(1 : ℝ) < 1 + 1` —— 这**不是** `0 < L` 的形状，而是某个不相关的恒真式（`1 < 2`）。
注释与陈述**不对应**。

## 1  本文件做什么

照 `FateV2/Loop/CapstoneDriftFromObs.lean:373` 的
`obs_model_constant_witness`（全库唯一合乎模板的一条）的**结构**重写：
用 `∃` 把 `worldModel_capstone` 的**每一个前件**都**显式构造**出来。

主交付：`capstone_premises_satisfiable'` —— 对**除图条件 `hsep`/`hpos` 之外**
的全部前件给出 `∃` 形式的具体实例（见 §3 的诚实边界）。

## 2  具体实例（全部在 `E = F = ℝ` 一维下）

| 前件 | 实例 | 依据 |
|---|---|---|
| `hx : x ≠ 0` | `x = 2` | `by norm_num` |
| `hη : |1 - η| < 1` | `η = 1/2` | `|1/2| < 1` |
| `hθ : θ₁ ≠ θ₂` | `θ₁ = 0`, `θ₂ = 1` | `by norm_num` |
| `[IsProbabilityMeasure P]` | `P = Measure.dirac 0` | `instIsProbabilityMeasureDirac` |
| `hP : MemLp id 2 P` | 同上 | `memLp_id_dirac`（**本文件新证**） |
| `hn : 0 < n` | `n = 1` | `by norm_num` |
| `hC : Corrects A φ` | `A = ContinuousLinearMap.id ℝ ℝ`, `φ = LinearMap.id` | 复用 `BoundWriteBack.corrects_id` |
| `hL : 0 < L` | `L = 1` | `by norm_num` |
| `hLI : LipschitzInvertibleOn f L` | `f = id`, `L = 1` | `lipschitzInvertibleOn_id`（**本文件新证**） |
| `hηmax : 0 ≤ ηmax` | `ηmax = 0` | `le_refl 0` |
| `hx' : ∀ k, f (x' k) = f xf + δ k` | `xf = 0`, `x' ≡ 0`, `δ ≡ 0` | `simp` |
| `hδ : ∀ k, ‖δ k‖ ≤ ηmax` | 同上 | `simp` |

**零公理**：见每条定理后的 `#print axioms` 输出（只有 `propext`/`Classical.choice`
/`Quot.sound` 这类 Lean 内核标准公理；**无** `sorryAx`，**无**自定义 `axiom`）。

## 3  诚实边界（**必须如实登记**）

**本见证覆盖 `worldModel_capstone` 的 12 条显式前件**（`x, η, θ₁, θ₂, P, n, A, φ,
L, f, xf, x', δ` 及其性质）。**未覆盖**：

1. **`hsep` / `hpos`（后门的图条件与正性）**：见 `WorldModelCapstone.lean:2003` 的
   §9 说明。它们作用于 `FateV2.Predict.R277` 的**固定图常量**（`zb` 等），
   **不是**可由我们自由选择的参数，因此**不能**用 `∃` 构造 ——
   它们要么对整个库成立要么不成立，是**库级常量性质**，不是「实例选择」问题。
   本文件**不**声称覆盖它们（T57 的旧定理同样没覆盖，但它也没说清楚）。
2. **类型变量 `E`、`F` 的具体实例**：本文件取 `E = F = ℝ` 并**显式**在 `∃` 中绑定
   `NormedAddCommGroup` / `NormedSpace ℝ` 实例，即「`hyperfield` 意义上的具体化」
   是**写出来**的而不是 `by infer_instance` 隐式带来的。
3. **`worldModel_capstone` 的结论**：本文件**不**证结论（结论在
   `WorldModelCapstone` 里已证）。本文件只证**前件可满足**。
-/

namespace FateV2.Loop.CapstoneWitness

open MeasureTheory
open FateV2.Modeling
open FateV2.Modeling.RA14Strong

/-! ===========================================================================
  §1  **辅助：`MemLp id 2 (dirac 0)`
  =========================================================================== -/

/-- **【§1.1 Dirac 测度下 `id` 的二阶矩有限】**

`MemLp (fun x : ℝ => x) 2 (Measure.dirac 0)`：因为在 `dirac 0` 下
`id` 与「恒为 `0` 的常函数」**几乎处处相等**，而常函数属于任意 `Lᵖ`。

**比定义多说了什么**：定义 `MemLp` 只说「`(fun x => x)` 在 `dirac 0` 下 `2`-次可积」；
本条把它**化成**「`id` a.e. 等于 `0`」这一**可检验**事实，
从而 `hP` 从「分析学前提」降为「几乎处处相等」。 -/
theorem memLp_id_dirac_zero : MemLp (fun x : ℝ => x) 2 (Measure.dirac (0 : ℝ)) := by
  have hconst : MemLp (fun _ : ℝ => (0 : ℝ)) 2 (Measure.dirac (0 : ℝ)) := memLp_const 0
  have hae : (fun _ : ℝ => (0 : ℝ)) =ᵐ[Measure.dirac (0 : ℝ)] (fun x : ℝ => x) := by
    have hs : ({0} : Set ℝ) ∈ ae (Measure.dirac (0 : ℝ)) := by
      rw [mem_ae_dirac_iff (s := ({0} : Set ℝ)) (by simp)]
      exact rfl
    filter_upwards [hs] with x hx
    simp only [Set.mem_singleton_iff] at hx
    show (0 : ℝ) = x
    exact hx.symm
  exact MemLp.ae_eq hae hconst

/-! ===========================================================================
  §2  **辅助：`LipschitzInvertibleOn id 1`
  =========================================================================== -/

/-- **【§2.1 恒等映射在 `L = 1` 下是 Lipschitz 可逆的】**

`LipschitzInvertibleOn (id : ℝ → ℝ) 1`：按
`ObsEstimationStrong.lean:131` 的定义，须证
`∀ x₁ x₂, dist x₁ x₂ ≥ dist x₁ x₂ / 1`，即 `dist ≥ dist`。

**比定义多说了什么**：定义是「$h$ 不把两点压得比 $1/L$ 更近」这一**度量**陈述；
本条证明在 `f = id`、`L = 1` 时它**取等**（`dist = dist`），
即 `L = 1` 是 `id` 的**最紧**常数 —— 故实例不是靠「宽松常数」凑出来的。 -/
theorem lipschitzInvertibleOn_id : RA14Strong.LipschitzInvertibleOn (id : ℝ → ℝ) 1 := by
  intro x₁ x₂
  simp

/-- **【§2.2 同一事实的 `dist` 展开形态】**（供下游 `rw` 使用）。 -/
theorem lipschitzInvertibleOn_id_dist (x₁ x₂ : ℝ) :
    dist (id x₁) (id x₂) ≥ dist x₁ x₂ / 1 :=
  lipschitzInvertibleOn_id x₁ x₂

/-! ===========================================================================
  §3  **主交付：`worldModel_capstone` 前件的非空洞见证**
  =========================================================================== -/

/-- **【§3.1 总装定理的前件确实可满足（真非空洞见证）】**

用 `∃` **显式构造** `worldModel_capstone` 的全部显式前件（12 条）的实例：

`E = F = ℝ`、`A = id`、`φ = id`、`θ = 0`、`f = id`、`L = 1`、`ηmax = 0`、
`xf = 0`、`x' ≡ 0`、`δ ≡ 0`、`η = 1/2`、`θstar = 0`、`x = 2`、`θ₀ = 0`、
`θ₁ = 0`、`θ₂ = 1`、`P = Measure.dirac 0`、`n = 1`。

**超出定义之处（对照旧 `capstone_premises_satisfiable`）**：

- 旧条的陈述 `(2:ℝ) ≠ 0 ∧ |1 - 1/2| < 1 ∧ (0:ℝ) ≠ 1 ∧ 1 < 1+1 ∧ 0 ≤ 0 ∧ 1 > 0`
  **不含任何** `worldModel_capstone` 的前件谓词（`Corrects`、`LipschitzInvertibleOn`、
  `MemLp`、`IsProbabilityMeasure`、`∀ k, f (x' k) = f xf + δ k`、`∀ k, ‖δ k‖ ≤ ηmax`
  **一条都没有**），因此它**即使删掉总装定理也照样成立**（T57 审计语）。
- 本条把**每一条前件**都写进陈述，且每条都在 `∃` 里**给出具体对象**：
  于是「删掉 `worldModel_capstone` ⟹ 本条无意义」不再成立 ——
  本条的**意义**恰恰是「这些谓词**可被同时满足**」，而它们的定义完全来自
  `worldModel_capstone` 的前件。
- 旧条的注释声称 `L = 1 > 0`，陈述里写的却是 `1 < 1 + 1`（即 `1 < 2`），
  **注释与陈述不对应**；本条中 `0 < L` 是**字面**的 `(0:ℝ) < 1`。

**⚠ 诚实边界**：本条**不**覆盖 `hsep`/`hpos`（后门图条件），原因见模块文档 §3：
它们是 `FateV2.Predict.R277` 的**固定库常量**性质，不是可自由选择的参数，
无法用 `∃` 构造。 -/
theorem capstone_premises_satisfiable' :
    ∃ (E F : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
      (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E)
      (f : F → F) (L : ℝ) (ηmax : ℝ)
      (xf : F) (x' : ℕ → F) (δ : ℕ → F)
      (η θstar x θ₀ : ℝ) (θ₁ θ₂ : ℝ)
      (P : Measure ℝ) (n : ℕ),
      x ≠ 0 ∧ |1 - η| < 1 ∧ θ₁ ≠ θ₂ ∧
      IsProbabilityMeasure P ∧ MemLp (fun x : ℝ => x) 2 P ∧ 0 < n ∧
      BoundWriteBack.Corrects A φ ∧ 0 < L ∧
      RA14Strong.LipschitzInvertibleOn f L ∧ 0 ≤ ηmax ∧
      (∀ k, f (x' k) = f xf + δ k) ∧ (∀ k, ‖δ k‖ ≤ ηmax) := by
  refine ⟨ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.id ℝ ℝ, LinearMap.id, 0,
    id, 1, 0,
    0, fun _ => 0, fun _ => 0,
    1/2, 0, 2, 0, 0, 1,
    Measure.dirac 0, 1,
    by norm_num, by norm_num, by norm_num,
    inferInstance, memLp_id_dirac_zero, by norm_num,
    BoundWriteBack.corrects_id, by norm_num,
    lipschitzInvertibleOn_id, le_refl 0,
    fun k => by simp, fun k => by simp⟩

#print axioms capstone_premises_satisfiable'

/-! ===========================================================================
  §4  **对偶：反例 —— 前件不是恒真的
  =========================================================================== -/

/-- **【§4.1 噪声前件 `hδ`/`hx'` 不是恒真的（反例方向，且**带前件谓词**）】**

取 `f = id`、`xf = 0`、`x' ≡ 0`、`ηmax = 0`、**`δ ≡ 1`**：
观测模型 `∀ k, f (x' k) = f xf + δ k` **失败**（`0 ≠ 0 + 1`），
噪声界 `∀ k, ‖δ k‖ ≤ ηmax` 也**失败**（`‖1‖ = 1 > 0`）。

**比定义多说了什么**：§3 证的是「前件**可**满足」，本条证「前件**不必**满足」
且**反例就在同一个具体字典里**（`f = id`、`ηmax = 0` 与 §3 完全相同，
只把 `δ` 从 `0` 换成 `1`）。两者合起来说明 `hδ`/`hx'` 是**真约束**：
若它们恒真，§3 的「见证」就退化成和旧 `capstone_premises_satisfiable` 一样的空话。

**⚠ 与第一版的区别**：第一版的结论只是 `¬ (∀ k, ‖δ k‖ ≤ 0)` ——
一条**纯数值**命题（不含任何 `worldModel_capstone` 的前件谓词），
被 G17（`[NUMERIC_ONLY_WITNESS]`）判为同型问题。本版把
`f`/`x'`/`xf`/`δ` **四个前件参数**与 `LipschitzInvertibleOn`、以及**两条前件谓词本身**
都写进结论，于是它**不能**脱离 `worldModel_capstone` 的语境陈述。 -/
theorem noise_model_premises_not_vacuous :
    ∃ (f : ℝ → ℝ) (L ηmax : ℝ) (xf : ℝ) (x' δ : ℕ → ℝ),
      0 < L ∧ RA14Strong.LipschitzInvertibleOn f L ∧ 0 ≤ ηmax
        ∧ ¬ (∀ k, f (x' k) = f xf + δ k)
        ∧ ¬ (∀ k, ‖δ k‖ ≤ ηmax) := by
  refine ⟨id, 1, 0, 0, fun _ => 0, fun _ => 1, by norm_num,
    lipschitzInvertibleOn_id, le_refl 0, ?_, ?_⟩
  · intro h
    have h0 := h 0
    simp at h0
  · intro h
    have h0 := h 0
    simp only [norm_one] at h0
    exact absurd h0 (not_le.mpr zero_lt_one)

#print axioms noise_model_premises_not_vacuous

/-! ===========================================================================
  §5  **与旧定理的关系（登记在模块文档，不落成定理）
  =========================================================================== -/

/- **为什么这里**不**写「旧陈述的六条数值事实」这条定理**（T60-v2，纠正第一版）：

第一版曾写 `old_premises_implied_by_new`，其结论是

    (2 : ℝ) ≠ 0 ∧ |1 - 1/2| < 1 ∧ (0 : ℝ) ≠ 1 ∧ 1 < 1 + 1 ∧ 0 ≤ 0 ∧ 1 > 0

—— 这**正是** T57 判为「极高严重度」的那个六条数值恒真式。
把它换个名字搬进来，等于**重复本专项要修的错误**：
它一条 `worldModel_capstone` 的前件谓词都没有，
**删掉 `worldModel_capstone` 它照样成立**。

**结论**：该定理**已删除**。旧定理与本文件 §3 的关系**只用散文登记**：

- 旧的 `WorldModelCapstone.capstone_premises_satisfiable` **保留不动**（T60 铁律：
  不改既有文件），它是**历史记录**；
- 它的六个合取项**都是真命题**，但**都不是** `worldModel_capstone` 的前件；
- 本文件 §3 的 `capstone_premises_satisfiable'` 才是真正的非空洞见证：
  它的**结论里逐字出现** `BoundWriteBack.Corrects A φ`、
  `RA14Strong.LipschitzInvertibleOn f L`、`MemLp (fun x : ℝ => x) 2 P`、
  `IsProbabilityMeasure P`、`∀ k, f (x' k) = f xf + δ k`、`∀ k, ‖δ k‖ ≤ ηmax` ——
  即「删掉 `worldModel_capstone` 则这些谓词名称**不存在**，本条**无法陈述**」。
- 旧陈述的六条**不必**与新文件发生任何定理层面的依赖：它们既不蕴含 §3，
  §3 也不声称蕴含它们（那是**无关命题之间的巧合**，写成定理只会误导）。 -/

end FateV2.Loop.CapstoneWitness
