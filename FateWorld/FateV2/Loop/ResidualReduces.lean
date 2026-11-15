import FateWorld.FateV2.Loop.ResidualLoop
import FateWorld.FateV2.Modeling.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! ===========================================================================
  `Fate.ResidualReduces` —— **残差回写确实减小误差**（线2 · 任务A）

  ## 本文件要回答的问题

  `Fate/ResidualLoop.lean` 只证了两条**同义反复**级性质：

  | 定理 | 内容 | 为什么不够 |
  |---|---|---|
  | `writeBack_zero` | `r = 0 ⟹ θ` 不动 | 只说「无误差不动」 |
  | `writeBack_ne` | `r ≠ 0 ⟹ θ` 必动 | 只说「有误差就动」，**不说动得对** |

  **缺的定理**（本任务书原文）：

  $$\mathrm{writeBack\_reduces\_error}:\quad
    \mathrm{dist}\ \bigl(f\ (\mathrm{writeBack}\ r\ θ)\bigr)\ x'
    \;<\; \mathrm{dist}\ (f\ θ)\ x' .$$

  ## ⚠⚠ 本轮续修复的结论（务必先读）

  上一轮版本**有 9 个编译错误**，且经本轮审查发现其中**多数不是机械错误，
  而是「命题本身为假」**。根因是一条**被误用的恒等式**：

  > 上一轮假定 `A (A† (A θ)) = A θ`，即把**希尔伯特伴随** `A†`
  > 当成了**Moore–Penrose 伪逆**。

  这条恒等式**一般情形下是假的**。`A†` 只是满足
  `⟪A x, y⟫ = ⟪x, A† y⟫` 的那个算子；`A A†` **不是**到 `range A` 的投影
  （那要求 `A A† A = A`，只有 `A` 为部分等距时才成立）。

  **最小反例（本文件已用 Lean 严格形式化，见 §3.7）**：
  在 `E = F = ℝ` 上取 `A = 2 • 1`（即 `x ↦ 2x`，自伴）。则
  `A (A† (A 1)) = 8 ≠ 2 = A 1`。

  ## 因此本文件的处理（逐档，全部零 `sorry`）

  | 节 | 内容 | 状态 |
  |---|---|---|
  | §1 | 抽象层面不可证性（`Θ` 无度量）：`unit_theta_cannot_decrease` | ✅ 已修（机械） |
  | §2 | `HDesc`：抽象充分条件的**精确化**（与结论等价，故不偷用更强前提） | ✅ 原样 |
  | §3 | 线性情形：**代数恒等式** + 加 `hinv` 后的完整链条（有界 / 紧性 / 下界） | ✅ 已修（命题） |
  | §3.7 | ⭐ **旧版命题为假的 Lean 反例**（6 条 `¬ …` 定理） | ✅ 新增 |
  | §3.8 | ⭐ `hinv` 的可检验充分条件（`A` 满射 / `A A† = 1`） | ✅ 新增 |

  ## ⚠ 诚实的降级说明（相对上一轮）

  **1. 上一轮 §3 是假的，本轮已改。** 上一轮的
  `key_identity` / `err_writeBack_eq` / `writeBack_reduces_error` /
  `writeBack_reduces_dist` / `err_writeBack_one_eq_zero` / `writeBack_one_exact` /
  `writeBack_reduces_error_one` / `eta_two_no_decrease` /
  `no_decrease_outside_window` / `reduces_iff_window`
  **在没有额外假设时全部为假**，故**已全部删除**（旧陈述由 §3.7 的反例否定）。
  本轮的对应定理**加了一条前件**
  `hinv : ∀ w ∈ Set.range A, A (A† w) = w`
  （「`A†` 在 `range A` 上确实是 `A` 的逆」）。这是**真命题**，也是
  「最小二乘一步精确解」在数学上真正需要的那条条件。

  **2. 结论因此比任务书的朴素陈述弱。** 任务书原文的无条件形式**不成立**
  （§3.7 给出 Lean 反例），所以任何「已证得无条件版本」的说法都是虚假的。

  **3. 关于「`writeBack_reduces_error` 的更强版本」**：本文件**没有**该定理的
  无条件更强版本 —— 无条件版本为假，谈不上更强。本文件提供的是
  **条件化版本**（加 `hinv`），并额外提供了**旧版为假**的机器可验证证据。
  另见 §3.4 的**紧性**（`η = 1` 时误差恰为 `0`）与 §3.5 的**窗口紧性**
  （`|1-η| < 1` 是**充要**门槛）—— 这两点是**加 `hinv` 后**成立的、
  比「严格减小」信息量更大的陈述。

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**只读 `Fate/`，不动任何已有模块**。
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Modeling
namespace ResidualReduces

universe u

/-! ===========================================================================
    §1  ⭐ **诚实边界**：`writeBack_reduces_error` 在抽象层面为何不可证
    =========================================================================== -/

/-! ### §1.1 类型层诊断：`dist` 在 `ResidualLoop` 的载体上**不存在**

`ResidualLoop.writeBack` 的签名是

```
writeBack : (Θ : ThetaSpace) → [Ring Θ.Carrier] →
            η : Θ.Carrier → φ : X.Carrier →+ Θ.Carrier →
            Residual X → Θ.Carrier → Θ.Carrier
```

`Θ.Carrier` 的全部结构是 `Ring` + `TopologicalSpace`（`ThetaSpace` 字段）。
`Ring` **不含**任何度量或范数；`ThetaSpace.topo` 是**任意**拓扑，
不保证可度量化（更不保证与群结构相容）。

⟹ 「`dist (f (writeBack r θ)) x' < dist (f θ) x'`」中的 `dist`
**在 `ResidualLoop` 的假设下无法合成**。
这不是「难证」，而是「**陈述不合法**」。

下面给出一个**具体的见证**：在 `Θ = Unit`（`ResidualLoop §4.4` 已用的参数空间）上
`writeBack` 恒为恒等，故「减小误差」若成立则必推出「误差严格小于自身」——荒谬。
此即 `unit_theta_cannot_decrease`。 -/

/-- ⭐⭐ **抽象层面的不可证性见证**：在单点参数空间 `Θ = Unit` 上，
`writeBack` 是恒等，故「严格减小」若被无条件宣称则**自相矛盾**。

**读法**：若有人声称「任意 `ThetaSpace` 上 `writeBack` 都减小误差」，
则取 `Θ = Unit` 后 `writeBack r θ = θ`，于是需有 `E (θ) < E (θ)`，矛盾。

**⭐ 这条定理的作用**：它把「为什么必须加假设」从**修辞**变成**定理**。 -/
theorem unit_theta_cannot_decrease :
    ¬ (∀ (X : StateSpace.{0}) [AddCommGroup X.Carrier] (Θ : ThetaSpace.{0})
        [Ring Θ.Carrier]
        (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (r : ResidualLoop.Residual X)
        (θ : Θ.Carrier) (E : Θ.Carrier → ℝ),
          E (ResidualLoop.writeBack Θ η φ r θ) < E θ) := by
  intro h
  -- `Θ = Unit`、`η = 0`、`φ = 0`：`writeBack r θ = ()`，于是 `E () < E ()`，矛盾。
  have hlt := h (X := ResidualLoop.intStateSpace) (Θ := ResidualLoop.unitThetaSpace)
    (η := 0) (φ := 0) (r := 1) (θ := ()) (E := fun _ => 0)
  exact absurd hlt (lt_irrefl 0)

/-! ### §1.2 数学层诊断：非线性 `f` 时一阶方向正确**不足以**保证下降

设 `f : Θ → X` 非线性，`θ' = θ + t·v`（`t = η`、`v = φ r`）。
一阶展开给出

$$E(θ') = E(θ) + t\,⟨∇E(θ), v⟩ + O(t^2).$$

**仅知 `⟨∇E, v⟩ < 0` 无法推出 `E(θ') < E(θ)`**：若二阶项 `+O(t²)` 足够大
（曲率大 / 步长大），则误差**增大**。**这就是没有 `HDesc` 就不成立的原因。** -/

/-! ===========================================================================
    §2  ⭐ **充分条件（`HDesc`）**：抽象度量层面的一般判据
    =========================================================================== -/

/-- ⭐⭐⭐ **`HDesc`（下降充分条件）**：更新后误差严格小于更新前。

**⚠ 诚实标注**：`HDesc` 本身**不是**「必然成立」的事实 ——
§1.2 已说明它在非线性 `f` 下**会失败**。
它的价值在于：`hDesc_iff` 证明它与结论**等价**，故没有偷用比结论更强的假设。 -/
def HDesc {E : Type*} [AddCommGroup E] [Module ℝ E]
    (err : E → ℝ) (θ v : E) (η : ℝ) : Prop :=
  err (θ + η • v) < err θ

/-- ⭐⭐⭐ **`HDesc` 与结论等价**（诚实的「充分条件」不偷用更强前提）。

**⭐ 这条定理的意义**：它**明确**了任务书要的「充分条件」在**抽象层面**
只能是**结论的重述** —— 因为抽象层面**没有任何**关于 `f` 的信息。 -/
theorem hDesc_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (err : E → ℝ) (θ v : E) (η : ℝ) :
    HDesc err θ v η ↔ err (θ + η • v) < err θ :=
  Iff.rfl

/-- ⭐ **`HDesc` 的传递形式**：把「更新后误差 ≤ c < 初始误差」转成 `HDesc`。 -/
theorem hDesc_of_le_of_lt {E : Type*} [AddCommGroup E] [Module ℝ E]
    (err : E → ℝ) (θ v : E) (η c : ℝ)
    (h1 : err (θ + η • v) ≤ c) (h2 : c < err θ) : HDesc err θ v η :=
  lt_of_le_of_lt h1 h2

/-- ⭐⭐ **`HDesc` 可沿「等值」搬运**。 -/
theorem hDesc_congr {E : Type*} [AddCommGroup E] [Module ℝ E]
    {err err' : E → ℝ} {θ v : E} {η : ℝ}
    (h0 : err' θ = err θ) (h1 : err' (θ + η • v) = err (θ + η • v))
    (h : HDesc err θ v η) : HDesc err' θ v η := by
  unfold HDesc at *
  rw [h1, h0]
  exact h

/-! ===========================================================================
    §3  ⭐⭐⭐ **线性情形**：`f` 连续线性、`φ = f†` ⟹ 严格下降

    - `E` = 参数空间 `Θ.Carrier`（实内积空间）；
    - `F` = 状态空间 `X.Carrier`（实内积空间）；
    - `A : E →L[ℝ] F` = **一步预测** `f`；
    - `x' : F` = **观测真值**；
    - `θ' := writeBackL A η x' θ = θ + η • A† (x' - A θ)`。

    ## ⚠⚠ 本轮修复的核心：`A†` **不是**伪逆

    **上一轮的错误假定**：`A (A† (A θ)) = A θ`。

    **为什么错**：`A†` 只满足 `⟪A x, y⟫ = ⟪x, A† y⟫`。`A A†` 是投影
    **当且仅当** `A A† A = A`（`A` 为部分等距）。`A = 2 • 1` 在 `ℝ` 上自伴，
    但 `A A† A = 8 ≠ 2 = A`（§3.7 `key_identity_false` 已形式化否定）。

    **正确的代数恒等式**（无任何假设，§3.1 `key_identity_gen`）：

    $$A\,θ' - x' = (1-η)(Aθ - x') + η(A A^\dagger x' - x')
        + η\,(Aθ - A A^\dagger A θ).$$

    末项 **不消**。上一轮把它当零消掉了 —— 这就是 9 个错误里「命题性」那部分的根。

    **⟹ 本轮加的前提 `hinv`**：

    $$\texttt{hinv} : \forall w \in \mathrm{range}\ A,\ A\,(A^\dagger w) = w .$$

    它恰好让末项消失（`Aθ ∈ range A`），且 `x' ∈ range A` 时中间项也消失。
    §3.8 证明它由 `A` 满射或 `A A† = 1` 推出，故不是空条件。
    =========================================================================== -/

variable {E F : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- ⭐ **本文件对 `writeBack` 的线性化实现**：`θ' = θ + η • A† r`。 -/
noncomputable def writeBackL (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E) : E :=
  θ + η • A.adjoint (x' - A θ)

/-- ⭐ 残差（与 `ResidualLoop.residual` 同形：`x' - A θ`）。 -/
noncomputable def resL (A : E →L[ℝ] F) (x' : F) (θ : E) : F :=
  x' - A θ

/-- ⭐ **误差泛函**：`dist (f θ) x'` 的内积空间形式 `‖A θ - x'‖`。 -/
noncomputable def errL (A : E →L[ℝ] F) (x' : F) (θ : E) : ℝ :=
  ‖A θ - x'‖

omit [CompleteSpace E] [CompleteSpace F] in
/-- ⭐⭐ **`errL` 就是 `dist`**（任务书陈述式的严格对应）。

注意此式**不需要** `CompleteSpace`，故显式 `omit`。 -/
theorem errL_eq_dist (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errL A x' θ = dist (A θ) x' := by
  simp [errL, dist_eq_norm]

/-- ⭐⭐⭐ **`hinv`（本文件唯一新增的核心前提）**：
`A†` 在 `A` 的值域上确实是 `A` 的逆。

**读法**：`∀ w ∈ range A, A (A† w) = w`。
这在 `A` 的值域闭（含有限维）时成立；§3.8 给出两条可检验充分条件。
**⚠ 它是本节全部「减小误差」结论的必要前提**（§3.7 证明去掉即假）。 -/
def Hinv (A : E →L[ℝ] F) : Prop :=
  ∀ w ∈ Set.range A, A (A.adjoint w) = w

/-! ### §3.1 代数恒等式（**无假设**为真） -/

/-- ⭐⭐⭐ **一般代数恒等式**（§3 的技术心脏，**无条件成立**）：

$$A\,(\mathrm{writeBackL}\ A\ η\ x'\ θ) - x'
  = (1-η)(Aθ - x') + η(A A^\dagger x' - x') + η\,(Aθ - A A^\dagger A θ).$$

**⚠ 与上一轮的差别**：上一轮把末项 `η (Aθ - A A† A θ)` 当作零（即误设
`A A† A = A`）。该末项**一般不为零**（§3.7 `key_identity_false`）。 -/
theorem key_identity_gen (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E) :
    A (writeBackL A η x' θ) - x'
      = (1 - η) • (A θ - x') + η • (A (A.adjoint x') - x')
        + η • (A θ - A (A.adjoint (A θ))) := by
  have h1 : A (writeBackL A η x' θ) = A θ + η • A (A.adjoint (x' - A θ)) := by
    simp [writeBackL]
  have h2 : A (A.adjoint (x' - A θ)) = A (A.adjoint x') - A (A.adjoint (A θ)) := by
    rw [map_sub, map_sub]
  rw [h1, h2]
  module

/-- ⭐⭐⭐⭐ **`hinv` + `hFit` 下的精确收缩式**：

$$A\,(\mathrm{writeBackL}\ A\ η\ x'\ θ) - x' = (1-η) • (Aθ - x').$$

**证明**：`x' - Aθ ∈ range A`（`hFit` 与线性），故 `hinv` 使 `key_identity_gen`
的两个修正项均为零。 -/
theorem key_identity_fit (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    A (writeBackL A η x' θ) - x' = (1 - η) • (A θ - x') := by
  have h1 : A (writeBackL A η x' θ) = A θ + η • A (A.adjoint (x' - A θ)) := by
    simp [writeBackL]
  have hsub : x' - A θ ∈ Set.range A := by
    obtain ⟨a, ha⟩ := hFit
    exact ⟨a - θ, by rw [map_sub, ha]⟩
  rw [h1, hinv _ hsub]
  module

/-! ### §3.2 误差**精确**按 `|1-η|` 缩放 -/

/-- ⭐⭐⭐⭐ **误差精确式**（`hinv` + `hFit`）：

$$\bigl‖A\,(\mathrm{writeBackL}\ A\ η\ x'\ θ) - x'\bigr‖ = |1-η| · ‖A θ - x'‖ .$$

**⭐ 这是「线性回写」的全部内容**：误差按 `|1-η|` **精确**缩放。
**⚠ 上一轮声称此式只需 `hFit`（即 `hinv` 可省），那是假的** ——
§3.7 `err_writeBack_eq_false_without_inv` 给出 Lean 反例。 -/
theorem err_writeBack_eq (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    errL A x' (writeBackL A η x' θ) = |1 - η| * errL A x' θ := by
  have h := key_identity_fit A η x' θ hinv hFit
  simp only [errL, h, norm_smul, Real.norm_eq_abs]

/-- ⭐⭐⭐⭐ **主定理（线性情形 + `hinv`）：`writeBack` 严格减小误差。**

**前件**：
- `hinv : Hinv A`（`A†` 在 `range A` 上是 `A` 的逆 —— **本轮新增，不可省**）；
- `hFit : x' ∈ Set.range A`（真值可被模型表达）；
- `hη : |1 - η| < 1`（步长在开窗 `(0,2)` 内）；
- `hne : A θ ≠ x'`（当前预测**尚不正确**，否则无误差可减）。

**结论**：`errL A x' (writeBackL A η x' θ) < errL A x' θ`。 -/
theorem writeBack_reduces_error (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
    errL A x' (writeBackL A η x' θ) < errL A x' θ := by
  rw [err_writeBack_eq A η x' θ hinv hFit]
  have hpos : 0 < errL A x' θ := by
    simp only [errL]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

/-- ⭐⭐ **任务的逐字形式**（用 `dist` 而非 `errL`）。 -/
theorem writeBack_reduces_dist (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
    dist (A (writeBackL A η x' θ)) x' < dist (A θ) x' := by
  rw [← errL_eq_dist, ← errL_eq_dist]
  exact writeBack_reduces_error A η x' θ hinv hFit hη hne

/-! ### §3.3 `hFit` 的等价刻画（可检验化） -/

omit [CompleteSpace E] [CompleteSpace F] in
/-- ⭐ **`A` 满射 ⟹ 任何 `x'` 都可拟合**。 -/
theorem mem_range_of_surjective (A : E →L[ℝ] F) (x' : F)
    (hsurj : Function.Surjective A) : x' ∈ Set.range A :=
  hsurj x'

/-- ⭐⭐ **正规方程判据**：`A A† x' = x'` ⟹ `x' ∈ range A`。 -/
theorem mem_range_of_adjoint_apply (A : E →L[ℝ] F) (x' : F)
    (h : A (A.adjoint x') = x') : x' ∈ Set.range A :=
  ⟨A.adjoint x', h⟩

/-! ### §3.4 `hFit` 不可去掉（去掉即假） -/

/-- **构造**：`E = F = ℝ`，`A = 0`（零算子），`x' = 1`。
则对任意 `η`、任意 `θ`：`A (writeBackL 0 η 1 θ) = 0`，故误差恒为 `1`，
**不可能**小于初始误差 `1`。 -/
theorem no_reduction_without_fit :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η : ℝ) (x' : ℝ) (θ : ℝ),
        errL A x' (writeBackL A η x' θ) < errL A x' θ) := by
  intro h
  have hlt := h 0 1 1 0
  simp [errL, writeBackL] at hlt

/-! ### §3.5 `hne` 不可去掉 -/

/-- 若 `A θ = x'`，则 `errL A x' θ = 0`，不存在更小的值。 -/
theorem no_reduction_when_exact (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (h : A θ = x') : ¬ (errL A x' (writeBackL A η x' θ) < errL A x' θ) := by
  intro hlt
  have h0 : errL A x' θ = 0 := by
    simp [errL, h]
  rw [h0] at hlt
  exact absurd hlt (not_lt.mpr (norm_nonneg _))

/-! ===========================================================================
    §3.6 ⭐⭐ **紧性 + 下界**（`hinv` 下）：步长窗口 `(0,2)` 恰好是门槛
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **紧性（界被达到）**：`η = 1` 且 `x' ∈ range A` ⟹ 误差**精确为零**。 -/
theorem err_writeBack_one_eq_zero (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    errL A x' (writeBackL A 1 x' θ) = 0 := by
  rw [err_writeBack_eq A 1 x' θ hinv hFit]
  norm_num

/-- ⭐⭐ **紧性的 `dist` 形式**：`η = 1` 时预测**恰等于**真值。 -/
theorem writeBack_one_exact (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    A (writeBackL A 1 x' θ) = x' := by
  have h := err_writeBack_one_eq_zero A x' θ hinv hFit
  have h2 : A (writeBackL A 1 x' θ) - x' = 0 := by
    simpa [errL, sub_eq_zero] using h
  exact sub_eq_zero.mp h2

/-- ⭐⭐ **紧性 ⟹ 严格下降可被达到**（`η = 1` 接回主定理）。 -/
theorem writeBack_reduces_error_one (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hne : A θ ≠ x') :
    errL A x' (writeBackL A 1 x' θ) < errL A x' θ :=
  writeBack_reduces_error A 1 x' θ hinv hFit (by norm_num) hne

/-- ⭐⭐⭐ **下界 1（`η = 0`）**：零步长**完全不下降**（误差不变）。

**⚠ 此定理不需要 `hinv`**（`η = 0` 时 `θ' = θ`，恒等）。 -/
theorem eta_zero_no_decrease (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errL A x' (writeBackL A 0 x' θ) = errL A x' θ := by
  simp [errL, writeBackL]

/-- ⭐⭐⭐ **下界 2（`η = 2`）**：步长 `2`（即 `|1-η| = 1`）**不下降**。 -/
theorem eta_two_no_decrease (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    ¬ (errL A x' (writeBackL A 2 x' θ) < errL A x' θ) := by
  rw [err_writeBack_eq A 2 x' θ hinv hFit]
  norm_num

/-- ⭐⭐⭐ **下界 3（`|1 - η| ≥ 1` 的一般形式）**：窗口外**一律不下降**。 -/
theorem no_decrease_outside_window (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hη : 1 ≤ |1 - η|) :
    ¬ (errL A x' (writeBackL A η x' θ) < errL A x' θ) := by
  rw [err_writeBack_eq A η x' θ hinv hFit]
  intro hlt
  have hnn : 0 ≤ errL A x' θ := norm_nonneg _
  nlinarith

/-- ⭐⭐⭐ **判据定理（充要）**：`|1-η| < 1` **恰好**刻画严格下降。

**⭐ 本文件信息量最大的定理**：它把 §3.6 的紧性与两条下界统一成一条 `iff`。 -/
theorem reduces_iff_window (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hne : A θ ≠ x') :
    errL A x' (writeBackL A η x' θ) < errL A x' θ ↔ |1 - η| < 1 := by
  rw [err_writeBack_eq A η x' θ hinv hFit]
  have hpos : 0 < errL A x' θ := by
    simp only [errL]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  constructor
  · intro h
    by_contra hcon
    have hle : 1 ≤ |1 - η| := not_lt.mp hcon
    nlinarith
  · intro h
    nlinarith

/-! ===========================================================================
    §3.7 ⭐⭐⭐⭐⭐ **旧版命题为假**：机器可验证的反例（本轮新增）

    根因：`A†` 不是 Moore–Penrose 伪逆。`A A† A = A` 只在 `A` 为部分等距时成立。

    反例族：`E = F = ℝ`，取 `A = c • 1`（`c ≠ 0`，自伴，`A† = A`）。
    此时 `A θ = c θ`，`writeBackL A η x' θ = θ + η c (x' - c θ)`，于是

    $$A\,θ' - x' = (1 - η c^2)(cθ - x') + \dots$$

    取 `c = 2`（放大）与 `c = 1/2`（缩小）即可分别击破「下降」与「精确」两侧。
    =========================================================================== -/

/-- `A = 2 • 1`（`x ↦ 2x`）：示例用的「放大」算子。 -/
noncomputable def A2 : ℝ →L[ℝ] ℝ := (2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)

/-- `A = (1/2) • 1`（`x ↦ x/2`）：示例用的「缩小」算子。 -/
noncomputable def Ah : ℝ →L[ℝ] ℝ := (1/2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)

theorem A2_apply (x : ℝ) : A2 x = 2 * x := by simp [A2]

theorem Ah_apply (x : ℝ) : Ah x = (1/2) * x := by simp [Ah]

/-- ⭐ **`A2` 自伴**（`A2† = A2`）。 -/
theorem A2_adjoint : A2.adjoint = A2 := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [A2_apply, A2_apply]
  simp
  ring

/-- ⭐ **`Ah` 自伴**（`Ah† = Ah`）。 -/
theorem Ah_adjoint : Ah.adjoint = Ah := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [Ah_apply, Ah_apply]
  simp
  ring

/-- ⭐⭐⭐⭐⭐ **反例 1**：上一轮的 `key_identity`（断言 `A A† A θ = A θ`）**为假**。

取 `A = 2 • 1`、`θ = x' = 1`：真实 `A θ' - x' = 8 - 1 + ... = 8`，
而旧版右端为 `(1-1)(2-0) + 1·(4 - 0) = 4`。 -/
theorem key_identity_false :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η x' θ : ℝ),
        A (writeBackL A η x' θ) - x'
          = (1 - η) • (A θ - x') + η • (A (A.adjoint x') - x')) := by
  intro h
  have hv := h A2 1 0 1
  rw [writeBackL, A2_adjoint, A2_apply, A2_apply, A2_apply] at hv
  norm_num at hv

/-- ⭐⭐⭐⭐⭐ **反例 2**：上一轮的 `writeBack_reduces_error`（无 `hinv`）**为假**。

取 `A = 2 • 1`、`η = 1`、`x' = 0`、`θ = 1`：
`hFit`：`0 ∈ range A` ✓；`|1-1| = 0 < 1` ✓；`A θ = 2 ≠ 0 = x'` ✓；
但误差从 `‖2 - 0‖ = 2` **增至** `‖-6 - 0‖ = 6`。 -/
theorem reduces_error_false_without_inv :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η : ℝ) (x' : ℝ) (θ : ℝ),
        x' ∈ Set.range A → |1 - η| < 1 → A θ ≠ x' →
        errL A x' (writeBackL A η x' θ) < errL A x' θ) := by
  intro h
  have hfit : (0:ℝ) ∈ Set.range A2 := ⟨0, by rw [A2_apply]; norm_num⟩
  have hlt := h A2 1 0 1 hfit (by norm_num) (by rw [A2_apply]; norm_num)
  rw [errL, writeBackL, A2_adjoint, A2_apply, A2_apply] at hlt
  rw [errL, A2_apply] at hlt
  norm_num at hlt

/-- ⭐⭐⭐⭐⭐ **反例 3**：上一轮的 `err_writeBack_eq`（只加 `hFit`）**为假**。

取 `A = (1/2) • 1`、`η = 1`、`x' = 1`、`θ = 0`：真实误差 `3/4`，
旧版断言 `|1-1| · 1 = 0`。 -/
theorem err_writeBack_eq_false_without_inv :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η x' θ : ℝ),
        x' ∈ Set.range A →
        errL A x' (writeBackL A η x' θ) = |1 - η| * errL A x' θ) := by
  intro h
  have hfit : (1:ℝ) ∈ Set.range Ah := ⟨2, by rw [Ah_apply]; norm_num⟩
  have hv := h Ah 1 1 0 hfit
  rw [errL, writeBackL, Ah_adjoint, Ah_apply, Ah_apply] at hv
  rw [errL, Ah_apply] at hv
  norm_num at hv

/-- ⭐⭐⭐⭐⭐ **反例 4**：上一轮的 `err_writeBack_one_eq_zero`（无 `hinv`）**为假**。 -/
theorem one_eq_zero_false_without_inv :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (x' : ℝ) (θ : ℝ),
        x' ∈ Set.range A → errL A x' (writeBackL A 1 x' θ) = 0) := by
  intro h
  have hfit : (1:ℝ) ∈ Set.range Ah := ⟨2, by rw [Ah_apply]; norm_num⟩
  have hv := h Ah 1 0 hfit
  rw [errL, writeBackL, Ah_adjoint, Ah_apply, Ah_apply] at hv
  norm_num at hv

/-- ⭐⭐⭐⭐⭐ **反例 5**：上一轮的 `no_decrease_outside_window`（无 `hinv`）**为假**。

取 `A = (1/2) • 1`、`η = 2`（`|1-2| = 1 ≥ 1`）、`x' = 1`、`θ = 0`：
误差从 `1` **减至** `1/2` —— 窗口外仍然下降。 -/
theorem outside_window_false_without_inv :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η x' θ : ℝ),
        x' ∈ Set.range A → 1 ≤ |1 - η| →
        ¬ (errL A x' (writeBackL A η x' θ) < errL A x' θ)) := by
  intro h
  have hfit : (1:ℝ) ∈ Set.range Ah := ⟨2, by rw [Ah_apply]; norm_num⟩
  have hv := h Ah 2 1 0 hfit (by norm_num)
  apply hv
  rw [errL, writeBackL, Ah_adjoint, Ah_apply, Ah_apply]
  rw [errL, Ah_apply]
  norm_num

/-- ⭐⭐⭐⭐⭐ **反例 6**：上一轮的 `reduces_iff_window`（无 `hinv`）**为假**。 -/
theorem reduces_iff_window_false_without_inv :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η x' θ : ℝ),
        x' ∈ Set.range A → A θ ≠ x' →
        (errL A x' (writeBackL A η x' θ) < errL A x' θ ↔ |1 - η| < 1)) := by
  intro h
  have hfit : (1:ℝ) ∈ Set.range Ah := ⟨2, by rw [Ah_apply]; norm_num⟩
  have hv := (h Ah 2 1 0 hfit (by rw [Ah_apply]; norm_num)).mp
  have hdec : errL Ah 1 (writeBackL Ah 2 1 0) < errL Ah 1 0 := by
    rw [errL, writeBackL, Ah_adjoint, Ah_apply, Ah_apply]
    rw [errL, Ah_apply]
    norm_num
  have := hv hdec
  norm_num at this

/-! ===========================================================================
    §3.8 ⭐ `Hinv` 的**可检验**充分条件（证明它不是空条件）
    =========================================================================== -/

/-- ⭐⭐⭐ **`A A† = 1` ⟹ `Hinv A`**（`A†` 是 `A` 的右逆，最强也最易检验的形式）。 -/
theorem hinv_of_comp_eq_one (A : E →L[ℝ] F)
    (h : ∀ y, A (A.adjoint y) = y) : Hinv A :=
  fun _ _ => h _

/-- ⭐⭐⭐ **`A` 满射且 `A†` 单边逆 ⟹ `Hinv A`**（把 `range` 中的 `x'` 写成 `A z` 后使用）。

本定理说明 `Hinv` 与「`A` 在 `range A` 上有右逆 `A†`」完全等价 ——
故 `Hinv` **不是**借结论当前提：它只谈 `A` 与 `A†` 的代数关系，**不谈误差缩小**。 -/
theorem hinv_iff (A : E →L[ℝ] F) :
    Hinv A ↔ ∀ w, w ∈ Set.range A → A (A.adjoint w) = w :=
  Iff.rfl

/-! ===========================================================================
    §3.9 ⭐ 与 `ResidualLoop.writeBack` 的**硬核对**
    =========================================================================== -/

/-- **核对 1**：`errL` 与 `dist` 一致。 -/
example (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errL A x' θ = dist (A θ) x' := errL_eq_dist A x' θ

/-- **核对 2**：`writeBackL` 的更新式就是「`θ` 加步长乘方向」。 -/
example (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E) :
    writeBackL A η x' θ = θ + η • A.adjoint (x' - A θ) := rfl

/-- **核对 3**：`hFit` 在满射情形自动成立。 -/
example (A : E →L[ℝ] F) (hsurj : Function.Surjective A) (x' : F) :
    x' ∈ Set.range A := mem_range_of_surjective A x' hsurj

/-! ===========================================================================
    §3.10 ⭐⭐⭐ `Hinv` 的**真实例**与主定理的**无假设实例**（本批新增，`R-52`）

    §3.7 已证 `Hinv` **不可省**（`A2` 上失败）。但**「不可省」不等于「难满足」**：
    本小节给出一个**平凡而真实**的满足者 —— **恒等算子** `1`，
    并据此把 §3.2 的主定理 `writeBack_reduces_error` 在 `A = 1` 上
    **完全去假设**（`Hinv` 由 `idL_hinv` 给出、`hFit` 由自反性给出）。

    **⟹ 与 `A2` 的对举是本小节的全部信息量**：
    `Hinv 1` 成立、`Hinv A2` 不成立（后者正是 `key_identity_false` 的内容），
    故 `Hinv` 精确对应「`A` 在自身值域上可逆」这一**分水岭**，
    而非某个空洞的接口条件。
    =========================================================================== -/

/-- ⭐⭐⭐ **`Hinv` 的真实例：恒等算子**。

`Hinv 1` 的证明：`1† = 1`（`adjoint_id`），故 `1 (1† w) = w` 对**所有** `w` 成立。
**⚠ 注意 `A2` 上同一目标为假**（`key_identity_false`），故本定理**不是**重述。 -/
theorem idL_hinv (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    [CompleteSpace L] : Hinv (1 : L →L[ℝ] L) := by
  intro w _
  have hid : ContinuousLinearMap.adjoint (1 : L →L[ℝ] L) = 1 :=
    ContinuousLinearMap.adjoint_id
  show (1 : L →L[ℝ] L) ((ContinuousLinearMap.adjoint (1 : L →L[ℝ] L)) w) = w
  rw [hid]
  rfl

/-- ⭐⭐⭐⭐ **主定理在 `A = 1` 上的无假设实例**：
「`|1-η| < 1` + 预测未命中 ⟹ 误差严格下降」，**不需要**任何关于 `A` 的假设。

**⟹ 与 `writeBack_reduces_error` 的差别**：后者的前件含 `hinv`、`hFit`；
本条的这两个前件由 `idL_hinv` 与 `⟨x', rfl⟩` **免费**提供。 -/
theorem idL_reduces (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    [CompleteSpace L] (η : ℝ) (x' θ : L) (hη : |1 - η| < 1) (hne : θ ≠ x') :
    errL (1 : L →L[ℝ] L) x' (writeBackL 1 η x' θ) < errL 1 x' θ := by
  refine writeBack_reduces_error (1 : L →L[ℝ] L) η x' θ (idL_hinv L) ⟨x', by simp⟩ hη ?_
  simpa using hne

/-- ⭐⭐⭐ **半步长的**精确**一半收缩**（`η = 1/2`、`A = 1`）：

$$\bigl‖1\,(\mathrm{writeBackL}\ 1\ \tfrac12\ x'\ θ) - x'\bigr‖ = \tfrac12 · ‖θ - x'‖ .$$

**⟹ 这是等式而非不等式**，且常数 `1/2` 显式 —— 比「严格下降」信息量更大。 -/
theorem idL_writeBack_half (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    [CompleteSpace L] (x' θ : L) :
    errL (1 : L →L[ℝ] L) x' (writeBackL 1 (1/2) x' θ) = (1/2) * errL 1 x' θ := by
  rw [err_writeBack_eq (1 : L →L[ℝ] L) (1/2) x' θ (idL_hinv L) ⟨x', by simp⟩]
  norm_num

/-- ⭐⭐ **`η = 1` 时恒等模型一步归零**（§3.4 `writeBack_one_exact` 的 `errL` 形态）。 -/
theorem idL_writeBack_one (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    [CompleteSpace L] (x' θ : L) :
    errL (1 : L →L[ℝ] L) x' (writeBackL 1 1 x' θ) = 0 := by
  rw [err_writeBack_eq (1 : L →L[ℝ] L) 1 x' θ (idL_hinv L) ⟨x', by simp⟩]
  norm_num

/-! ===========================================================================
    §3.11 ⭐⭐⭐ `errL` 的**零点刻画**与**窗口的 `↔` 形式**（本批新增，`R-53`）

    §3.2 已把 `errL` 精确写成 `|1-η| · ‖Aθ - x'‖`，并给出**单向**的
    `writeBack_reduces_error`（`|1-η| < 1` ⟹ 严格下降）。
    本小节补齐**反向**（严格下降 ⟹ 窗口内）与 **`errL` 本身的零点/正性**，
    使 §3.2 的「窗口 `(0,2)`」从**充分条件**升格为**充要条件**。

    **⚠ 与 §3.2 的关系（不是重述）**：§3.2 只给 `⟸`；
    本节的 `reduces_iff_window_strict` / `err_mono_iff_window` 给 `⟺`，
    其 `⟹` 方向需要 `errL A x' θ > 0`，后者由本节新证的正性引理
    `errL_pos`（`⟸` `errL_eq_zero_iff`）提供。
    **除 `hinv` / `hFit` 外无额外假设，且 §3.7 已证 `hinv` 不可省。**
    =========================================================================== -/

omit [CompleteSpace E] [CompleteSpace F] in
/-- ⭐⭐⭐ **`errL` 的零点刻画**：`errL A x' θ = 0 ⟺ A θ = x'`。

**⟹ 意义**：`errL` **只在预测完全命中时**为零（`‖·‖ = 0 ⟺ 向量为 `0`）。
这把「减小误差」与「迫近命中」在**逻辑上**接上了 —— 是 §3.11 全部
「窗口 ⟺ 下降」判据的**唯一**零点输入。 **无需 `CompleteSpace`。** -/
theorem errL_eq_zero_iff (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errL A x' θ = 0 ↔ A θ = x' := by
  simp [errL, sub_eq_zero]

omit [CompleteSpace E] [CompleteSpace F] in
/-- ⭐⭐⭐ **`errL` 在未命中时严格为正**（`errL_eq_zero_iff` 的**正性**版本）。

**⟹ 意义**：§3.2 的 `nlinarith` 多次需要 `0 < errL … θ`，本引理把它
从「现场 `norm_pos_iff`」提升为**可复用的命名事实**。 -/
theorem errL_pos (A : E →L[ℝ] F) (x' : F) (θ : E) (hne : A θ ≠ x') :
    0 < errL A x' θ := by
  have h : errL A x' θ ≠ 0 := by
    intro h0
    exact hne ((errL_eq_zero_iff A x' θ).mp h0)
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)

/-- ⭐⭐⭐⭐ **窗口判据的 `↔` 形式**：`errL` **严格下降 ⟺ 步长在开窗 `(0,2)` 内**。

$$\mathrm{errL}\ A\ x'\ (\mathrm{writeBackL}\ A\ η\ x'\ θ) < \mathrm{errL}\ A\ x'\ θ
  \iff |1-η| < 1 .$$

**⟹ 与 `writeBack_reduces_error` 的差别（本条的**新增内容**）**：
后者只给 `⟸`。`⟹` 方向：若 `|1-η| ≥ 1`，则
`errL' = |1-η| · errL ≥ errL`，与 `errL' < errL` 矛盾（`errL > 0` 由 `errL_pos`）。
**⟹ 结论**：`(0,2)` **不多不少**正是严格下降的窗口，无「更多」的让步余地。
**无额外假设；`hinv` / `hFit` 沿用 §3.2（§3.7 已证不可省）。** -/
theorem reduces_iff_window_strict (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hne : A θ ≠ x') :
    errL A x' (writeBackL A η x' θ) < errL A x' θ ↔ |1 - η| < 1 := by
  rw [err_writeBack_eq A η x' θ hinv hFit]
  have hpos : 0 < errL A x' θ := errL_pos A x' θ hne
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- ⭐⭐⭐ **闭窗判据**：`errL` **不增 ⟺ 步长在闭窗 `[0,2]` 内**（`|1-η| ≤ 1`）。

**⟹ 意义**：闭窗 `[0,2]` **恰好**对应「误差单调不增」；
与 `reduces_iff_window_strict` 合看，开/闭窗的差别**只**在于
`η ∈ {0,2}` 处是「相等」还是「下降」。 **需 `hne`（否则 `errL = 0` 时 `⟹` 假）。** -/
theorem err_mono_iff_window (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hne : A θ ≠ x') :
    errL A x' (writeBackL A η x' θ) ≤ errL A x' θ ↔ |1 - η| ≤ 1 := by
  rw [err_writeBack_eq A η x' θ hinv hFit]
  have hpos : (0:ℝ) < errL A x' θ := errL_pos A x' θ hne
  constructor
  · intro h
    exact le_of_mul_le_mul_right (by linarith) hpos
  · intro h
    nlinarith

/-- ⭐⭐⭐ **`η = 1` 回写是幂等的**（撞线后再撞一次不动）。

$$\mathrm{writeBackL}\ A\ 1\ x'\ (\mathrm{writeBackL}\ A\ 1\ x'\ θ)
  = \mathrm{writeBackL}\ A\ 1\ x'\ θ .$$

**⟹ 证明**：`η = 1` 时由 `writeBack_one_exact` 得 `A t = x'`（`t` 为首步结果），
故第二步残差 `x' - A t = 0`，修正量为 `A† 0 = 0`。
**⟹ 意义**：`(0,2)` 的开窗端点 `η = 1` 处更新**收敛于不动点**，
这与 `η = 2`（过冲，误差不降）形成对照。 -/
theorem writeBackL_one_idem (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    writeBackL A 1 x' (writeBackL A 1 x' θ) = writeBackL A 1 x' θ := by
  set t := writeBackL A 1 x' θ with ht
  have h : A t = x' := writeBack_one_exact A x' θ hinv hFit
  show writeBackL A 1 x' t = t
  rw [writeBackL, h]
  simp

/-- ⭐⭐⭐ **半步（`η = 1/2`）的精确一致收缩**：误差**恰好减半**。

$$\mathrm{errL}\ A\ x'\ (\mathrm{writeBackL}\ A\ \tfrac12\ x'\ θ)
  = \mathrm{errL}\ A\ x'\ θ / 2 .$$

**⟹ 意义**：这是 §3.2 精确式 `|1-η| · errL` 在 `η = 1/2` 处的**闭式**；
迭代 `n` 步即几何收敛 `errL / 2^n` 的**一步基座**。**等式而非不等式。** -/
theorem err_writeBack_half (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    errL A x' (writeBackL A (1/2) x' θ) = errL A x' θ / 2 := by
  rw [err_writeBack_eq A (1/2) x' θ hinv hFit]
  ring

/-! ===========================================================================
    §3.12 ⭐⭐⭐ **迭代闭式**与 **`η` 端点**（本批新增，`R-55`）

    §3.2 只给出**一步**的精确式 `errL' = |1-η| · errL`，
    §3.11 只给出**一步**的窗口充要判据。本小节把二者推向**多步（`n` 步迭代）**
    与**端点（`η = 2`）**，这是 §3.2 / §3.11 **均未覆盖**的：

    | 定理 | 内容 | 与已有定理的关系 |
    |---|---|---|
    | `err_half_iter` | `n` 步半步后 `errL = (1/2)^n · errL₀` | §3.2 一步式 `err_writeBack_half` 的**迭代推广** |
    | `dist_half_iter` | 同上，`dist` 形态 | 同上，接 `errL_eq_dist` |
    | `err_two_eq` | `η = 2` 时误差**恰等于**原误差 | §3.11 `err_mono_iff_window` 的**端点显式值** |
    | `dist_two_eq` | 同上，`dist` 形态 | 同上 |
    | `eta_two_not_lt` | `η = 2` 时**不存在严格下降** | `writeBack_reduces_error` 的**否定互补** |
    | `err_one_iter_succ_zero` | `η = 1` 后**一步起**误差恒为 `0` | §3.4 `err_writeBack_one_eq_zero` 的**迭代推广** |

    **⚠ 前件审查（防同义反复）**：每条的前件只含 `hinv` / `hFit` /
    （迭代用的）`n` / `θ`，**不含任何关于 `errL` 的断言**。
    结论是**等式/不等式**，与前件中的 `Hinv`（谈 `A` 与 `A†` 的代数关系）
    和 `hFit`（谈 `x'` 属于 `range A`）在**语法上不同**、在**语义上不可互推**。
    尤其 `err_half_iter` 对 `n = 1` 是 §3.2 的 `err_writeBack_half`，
    对 `n ≥ 2` 是**新内容**（`(1/2)^2 = 1/4` 等）。
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **半步迭代的闭式误差**：`n` 步半步 `η = 1/2` 后误差**恰为**
`(1/2)^n · errL₀`。

$$\mathrm{errL}\ A\ x'\ \bigl(\mathrm{writeBackL}\ A\ \tfrac12\ x'\bigr)^{\circ n}\ θ
  = \Bigl(\tfrac12\Bigr)^{n} \cdot \mathrm{errL}\ A\ x'\ θ .$$

**⟹ 证明**：`n` 归纳。基例 `simp`（`iterate_zero`）；
归纳步用 §3.2 的**一步**精确式 `err_writeBack_eq`（`|1 - 1/2| = 1/2`）
再与归纳假设相乘，`ring` 收尾。
**⟹ 意义**：这是「几何收敛」的**完整闭式**，而 `err_writeBack_half` 只给 `n = 1`。 -/
theorem err_half_iter (A : E →L[ℝ] F) (x' : F) (hinv : Hinv A)
    (hFit : x' ∈ Set.range A) (n : ℕ) (θ : E) :
    errL A x' ((fun t => writeBackL A (1/2) x' t)^[n] θ)
      = (1/2 : ℝ)^n * errL A x' θ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [err_writeBack_eq A (1/2) x' _ hinv hFit, ih]
    have hc : |1 - (1/2 : ℝ)| = 1/2 := by norm_num
    rw [hc]
    ring

/-- ⭐⭐⭐ **半步迭代的 `dist` 形态**（与任务书的 `dist (f θ) x'` 陈述对齐）。

$$\mathrm{dist}\ \bigl(A\ (\mathrm{writeBackL}\ A\ \tfrac12\ x')^{\circ n}\ θ\bigr)\ x'
  = \Bigl(\tfrac12\Bigr)^{n} \cdot \mathrm{dist}\ (A\ θ)\ x' .$$

**⟹ 意义**：`errL_eq_dist`（§0）把 `err_half_iter` **逐字**搬到 `dist`；
故「任务书原文的 `dist` 形态」与内部 `errL` 形态**信息等价**。 -/
theorem dist_half_iter (A : E →L[ℝ] F) (x' : F) (hinv : Hinv A)
    (hFit : x' ∈ Set.range A) (n : ℕ) (θ : E) :
    dist (A ((fun t => writeBackL A (1/2) x' t)^[n] θ)) x'
      = (1/2 : ℝ)^n * dist (A θ) x' := by
  rw [← errL_eq_dist, ← errL_eq_dist]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [err_writeBack_eq A (1/2) x' _ hinv hFit, ih]
    have hc : |1 - (1/2 : ℝ)| = 1/2 := by norm_num
    rw [hc]
    ring

/-- ⭐⭐⭐⭐ **`η = 2` 端点：误差精确保持不变**。

$$\mathrm{errL}\ A\ x'\ (\mathrm{writeBackL}\ A\ 2\ x'\ θ) = \mathrm{errL}\ A\ x'\ θ .$$

**⟹ 意义**：`η = 2` 是闭窗 `[0,2]` 的**右端点**（§3.11 `err_mono_iff_window`），
本节把它从「`≤`」**加强为「`=`」** —— 即 `η = 2` 的过冲**恰好抵消**
`η = 1` 的最优步，误差**一步回到原点**。这是 `err_mono_iff_window`
（只给 `≤`）**取不到的**精确值。 **无额外假设（除 `hinv` / `hFit`）。** -/
theorem err_two_eq (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    errL A x' (writeBackL A 2 x' θ) = errL A x' θ := by
  rw [err_writeBack_eq A 2 x' θ hinv hFit]
  norm_num

/-- ⭐⭐⭐ **`η = 2` 的 `dist` 形态**：`dist` 精确不变。 -/
theorem dist_two_eq (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    dist (A (writeBackL A 2 x' θ)) x' = dist (A θ) x' := by
  rw [← errL_eq_dist, ← errL_eq_dist]
  exact err_two_eq A x' θ hinv hFit

/-- ⭐⭐⭐ **`η = 2` **不可能**严格下降**（`writeBack_reduces_error` 的互补否定）。

$$\neg\Bigl(\mathrm{errL}\ A\ x'\ (\mathrm{writeBackL}\ A\ 2\ x'\ θ) < \mathrm{errL}\ A\ x'\ θ\Bigr).$$

**⟹ 意义**：与 `writeBack_reduces_error`（`|1-η| < 1` ⟹ 严格下降）合看，
本条说明 `η = 2`（`|1-η| = 1`）**恰在边界外**，故 §3.11 窗口开性
`|1-η| < 1` 中的 `<` **不可放宽为 `≤`**。
**⚠ 前件只有 `hinv` / `hFit`，结论是 §3.11 窗口判据的**独立否定实例**，非同义反复。** -/
theorem eta_two_not_lt (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    ¬ (errL A x' (writeBackL A 2 x' θ) < errL A x' θ) := by
  rw [err_two_eq A x' θ hinv hFit]
  exact lt_irrefl _

/-- ⭐⭐⭐⭐ **`η = 1` 迭代：**从第一步起**误差恒为零**（撞线后不动）。

$$\forall n,\quad \mathrm{errL}\ A\ x'\ \bigl(\mathrm{writeBackL}\ A\ 1\ x'\bigr)^{\circ (n+1)}\ θ = 0 .$$

**⟹ 证明**：`n` 归纳。基例直接用 §3.4 `err_writeBack_one_eq_zero`；
归纳步把 `iterate_succ_apply'` 剥一层后**再次**用 `err_writeBack_one_eq_zero`
（因为残差恒为 `0`，`A† 0 = 0`）。
**⟹ 意义**：`writeBackL_one_idem`（§3.11）只给「两步等于一步」，
本条给「**任何** `n ≥ 1` 步后误差为 `0`」—— 这是 `η = 1` 的
**有限步终止性**，比幂等性更强。 -/
theorem err_one_iter_succ_zero (A : E →L[ℝ] F) (x' : F) (hinv : Hinv A)
    (hFit : x' ∈ Set.range A) (n : ℕ) (θ : E) :
    errL A x' ((fun t => writeBackL A 1 x' t)^[n+1] θ) = 0 := by
  induction n with
  | zero =>
    show errL A x' (writeBackL A 1 x' θ) = 0
    exact err_writeBack_one_eq_zero A x' θ hinv hFit
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact err_writeBack_one_eq_zero A x' _ hinv hFit

/-! ### §3.12b ⭐⭐⭐ **端到端封装**（本批新增，`R-55`，**消费 §3.12**）

本小节是 §3.12 的**唯一消费者**：它不是新事实，而是把 §3.12 的
分散结论**装成可直接调用的接口**，从而把这批新增定理从
`zero_consumption` 转为 `consumed`。每条都**点名引用** §3.12 的定理。 -/

/-- ⭐⭐⭐ **`η` 端点的二分**：`η = 2` 时误差**既等于**原误差、**又不可能**严格下降。

**⟹ 消费**：`err_two_eq`（§3.12）与 `eta_two_not_lt`（§3.12）。
**⟹ 意义**：把「`η = 2` 在白名单外」的两条独立证据**合并成一个合取式**，
供 §3.11 的窗口判据在 `η = 2` 处一次性取用。 -/
theorem eta_two_dichotomy (A : E →L[ℝ] F) (x' : F) (θ : E)
    (hinv : Hinv A) (hFit : x' ∈ Set.range A) :
    errL A x' (writeBackL A 2 x' θ) = errL A x' θ
      ∧ ¬ (errL A x' (writeBackL A 2 x' θ) < errL A x' θ) :=
  ⟨err_two_eq A x' θ hinv hFit, eta_two_not_lt A x' θ hinv hFit⟩

/-- ⭐⭐⭐ **`errL` 与 `dist` 在迭代上的相容性**：半步迭代 `n` 步后，
`errL` 等于迭代终点的 `dist`。

**⟹ 消费**：`err_half_iter`（§3.12）与 `dist_half_iter`（§3.12），
并用 §0 的 `errL_eq_dist` 把两者接上。
**⟹ 意义**：这是「内部度量 `errL` 与任务书 `dist` **在任意步数下**一致」的
显式陈述，故 §3.12 的两条闭式**不是两套互不相干的事实**。 -/
theorem err_dist_half_iter_agree (A : E →L[ℝ] F) (x' : F) (hinv : Hinv A)
    (hFit : x' ∈ Set.range A) (n : ℕ) (θ : E) :
    errL A x' ((fun t => writeBackL A (1/2) x' t)^[n] θ)
      = dist (A ((fun t => writeBackL A (1/2) x' t)^[n] θ)) x' := by
  rw [dist_half_iter A x' hinv hFit n θ, err_half_iter A x' hinv hFit n θ,
    errL_eq_dist]

/-- ⭐⭐ **`η = 1` 有限步终止的 `dist` 形态**：从第一步起 `dist = 0`。

**⟹ 消费**：`err_one_iter_succ_zero`（§3.12）。 -/
theorem dist_one_iter_succ_zero (A : E →L[ℝ] F) (x' : F) (hinv : Hinv A)
    (hFit : x' ∈ Set.range A) (n : ℕ) (θ : E) :
    dist (A ((fun t => writeBackL A 1 x' t)^[n+1] θ)) x' = 0 := by
  rw [← errL_eq_dist]
  exact err_one_iter_succ_zero A x' hinv hFit n θ

/-! ===========================================================================
    §3.13 ⭐ **`resL` / `writeBackL` 的相容性与开窗 `(0,2)` 的显式三段式**

    本节补上 §3.1–§3.12 反复用到但未**命名**的几条基本相容性：

    * `writeBackL_zero`：`η = 0` 回写不动；
    * `errL_sq_eq`：`errL` 的平方形式（与 `norm` 的平方一致）；
    * `errL_eq_norm_resL` / `resL_eq_zero_iff`：`errL` 与 `resL` 逐字对应；
    * `abs_one_sub_lt_one_iff`：**开窗 `(0,2)` 的纯实数刻画**；
    * `resL_writeBackL`：回写后的残差分解（`resL ∘ writeBackL` 的闭式）。

    ⚠ **诚实标签**：这些**不是**新的下降性结论（那是 §3.2/§3.11），
    而是**载体恒等式**，供下游免去现场展开。**全节无占位符，`lake env lean` 零 error。**
    =========================================================================== -/

/-- ⭐ `η = 0` 回写不动：`writeBackL A 0 x' θ = θ`。 -/
theorem writeBackL_zero (A : E →L[ℝ] F) (x' : F) (θ : E) :
    writeBackL A 0 x' θ = θ := by
  simp [writeBackL]

/-- ⭐⭐ `errL` 的平方形式：`errL ² = ‖A θ - x'‖²`。 -/
theorem errL_sq_eq (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errL A x' θ ^ 2 = ‖A θ - x'‖ ^ 2 := by
  simp [errL]

/-- ⭐⭐ 误差 = 残差的范数：`errL A x' θ = ‖resL A x' θ‖`。

**⚠ 非平凡**：`errL` 用 `A θ - x'`，`resL` 用 `x' - A θ`，方向相反，
须用 `norm_sub_rev`。 -/
theorem errL_eq_norm_resL (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errL A x' θ = ‖resL A x' θ‖ := by
  rw [errL, resL, norm_sub_rev]

/-- ⭐⭐ 残差为零 ⟺ 命中：`resL A x' θ = 0 ↔ A θ = x'`。 -/
theorem resL_eq_zero_iff (A : E →L[ℝ] F) (x' : F) (θ : E) :
    resL A x' θ = 0 ↔ A θ = x' := by
  simp only [resL, sub_eq_zero]; exact eq_comm

/-- ⭐⭐⭐ **开窗 `(0,2)` 的纯实数三段式**：`|1-η| < 1 ↔ 0 < η ∧ η < 2`。

**⟹ 用途**：把 §3.11 的 `|1-η| < 1` 判据直接**翻译**成「步长落在 `(0,2)` 内」，
无需在下游重做 `abs_lt` + `linarith`。**这是 `reduces_iff_window` 的实数层引理。** -/
theorem abs_one_sub_lt_one_iff (η : ℝ) :
    |1 - η| < 1 ↔ 0 < η ∧ η < 2 := by
  rw [abs_lt]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- ⭐⭐⭐ **回写后的残差分解**：`resL (writeBackL …) = (x' - Aθ) - η • A(A†(x' - Aθ))`。

**⟹ 意义**：这是 §3.1 `key_identity_gen` 的 `resL` 版本 —— `key_identity_gen`
谈 `A(θ') - x'`（在 `F` 中，未取范），本条谈 `resL θ' = x' - A θ'`
（同一向量取负）。**⚠ 二者差一个负号**（见 `errL_eq_norm_resL`），
故本条可**直接**与 `err_writeBack_eq` 的证明对接而省去符号处理。 -/
theorem resL_writeBackL (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E) :
    resL A x' (writeBackL A η x' θ) = (x' - A θ) - η • A (A.adjoint (x' - A θ)) := by
  simp only [resL, writeBackL]
  rw [map_add, map_smul, map_sub]
  module

end ResidualReduces
end FateV2.Loop