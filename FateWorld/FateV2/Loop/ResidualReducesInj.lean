import FateWorld.FateV2.Loop.ResidualReduces
/-!
  # Loop · ResidualReducesInj

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ResidualReducesInj.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ResidualReduces
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.ResidualReducesInj` —— **G1 判决：`Hinv` 不可放松为「`A` 有左逆 / `A` 单射」**

  ## 结论（先给判决）

  **G1（「把 `A` 可逆放松到 `A` 单射 / 有左逆」）在 `Hinv` 的定义下【无意义】，
  而且方向是反的。** 本文件用 Lean 给出**机器可验证的反例**：
  存在**单射（有左逆）**算子 `A` 使 `Hinv A` **为假**。

  ⟹ 任务书第 2 步的第 2 条判据（「`Hinv A := ∃ φ, A ∘ φ = id ∧ φ ∘ A = id`
  才使 G1 有意义」）**不成立**：`Hinv` **既不是**左逆形态，**也不是**双逆形态，
  而是**第三形态**（见下）。放松前件会**削弱到不足以推出结论**，
  故 **G1 不可交付**。本文件**不**提供 `writeBack_reduces_error_inj`
  ——因为它是**假命题**（本文件 `no_inj_relaxation` 即其否证）。

  ## (a) `Hinv` 的完整定义（`Fate/ResidualReduces.lean` 原文，第 233–234 行）

  ```lean
  def Hinv (A : E →L[ℝ] F) : Prop :=
    ∀ w ∈ Set.range A, A (A.adjoint w) = w
  ```

  **读法**：`A ∘ A† = id` **在 `range A` 上**。即 `A†` 是 `A` 在**值域上的右逆**。
  注意运算顺序：`A (A† w)` 是「先 `A†` 再 `A`」——这是 **`A` 满射性一侧**
  的条件（`A†` 把 `range A` 送回 `E` 且 `A` 把它原样送回），
  与「`A` 单射 / `A` 有左逆（`φ ∘ A = id`）」**完全是另一侧**。

  ## (b) `writeBack_reduces_error` 的完整签名（原文，第 297–299 行）

  ```lean
  theorem writeBack_reduces_error (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
      (hinv : Hinv A) (hFit : x' ∈ Set.range A) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
      errL A x' (writeBackL A η x' θ) < errL A x' θ
  ```

  ## (c) §3.7 的 6 条 `¬` 定理各否定什么

  | 定理 | 被否定的命题 |
  |---|---|
  | `key_identity_false` | 无条件恒等式 `A θ' - x' = (1-η)(Aθ-x') + η(A A† x' - x')` |
  | `reduces_error_false_without_inv` | **无 `hinv`** 的 `writeBack_reduces_error` |
  | `err_writeBack_eq_false_without_inv` | **无 `hinv`** 的「误差精确按 `\|1-η\|` 缩放」 |
  | `one_eq_zero_false_without_inv` | **无 `hinv`** 的 `η = 1` 时误差归零 |
  | `outside_window_false_without_inv` | **无 `hinv`** 的「窗口外不下降」 |
  | `reduces_iff_window_false_without_inv` | **无 `hinv`** 的「下降 ⟺ 窗口内」 |

  **⚠ 关键**：这 6 条全部是「**把 `hinv` 整个删掉**」的反例。
  它们**没有**、也**不能**说明「**换成单射也不行**」。本文件正是补上这一步判断。

  ## (d) G1 是否有意义？

  **无意义，且前件被削弱后结论为假。** 理由两条，均在下方 Lean 中形式化：

  1. `Hinv` 是「`A†` 在 `range A` 上是右逆」的条件，**不是**可逆性。原证明只在
     **一处**用它（`key_identity_fit`，第 270 行 `rw [h1, hinv _ hsub]`），
     用来消去 `A θ' - x'` 里的修正项 `η • (A (A† (x' - Aθ)) - (x' - Aθ))`。
     这一步恰好需要 `A A† = id` **作用在 `x' - Aθ ∈ range A` 上**，
     即**右逆**方向。
  2. **单射 / 左逆对这一步毫无帮助**：左逆 `φ` 满足 `φ ∘ A = id`，
     它作用于 `E`（`A` 的定义域），而这里需要的是把 `F` 中的 `x' - Aθ`
     拉回并再推出去 —— 那是 `F → E → F` 的往返，正是 `A† ∘ A` 的方向。
     反例：`A = (1/2)•1 : ℝ → ℝ` 有左逆 `φ = 2•1`，但 `Hinv A` 为假
     （`A (A† 1) = 1/4 ≠ 1`），且 `writeBack_reduces_error` 的结论对它为假。

  ## (e) 做到了什么 / 没做什么

  - **做了**：把「G1 不可行」从判断升级为**定理**——
    `leftinv_does_not_give_hinv`（有左逆 ⟹ `Hinv` 为假，即反例存在）、
    `injective_does_not_give_hinv`（单射亦然）、
    `no_inj_relaxation`（**结论**：把 `hinv` 换成「`A` 有左逆」后主定理为**假**）。
  - **没做**：**不提供** `writeBack_reduces_error_inj`。
    原因是它是**假命题**，不是「证明未完成」。若强行给出，唯一出路是加
    `hleft : ∃ φ, φ ∘ A = id` **并且** 把它当装饰（结论仍需 `Hinv`）——
    那就是前件包含结论之外的多余装饰，属本项目明令禁止的形态，故**不写**。
  - **附带发现**：`Hinv` 在唯一被使用处**严格等价**于较熟悉的广义逆条件
    `A A† A = A`（见 `hgen_of_hinv` / `key_identity_fit_of_hgen`）。
    这也说明 `Hinv` **已是最弱可用形态**（就 `A†` 语言而言），
    没有「放松到单射」的余地。

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；未修改任何已有模块。
  =========================================================================== -/

namespace FateV2.Loop
namespace ResidualReduces

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ===========================================================================
    §1  `Hinv` 的形态定位：它是**右逆**型条件，不是可逆性也不是单射性
    =========================================================================== -/

/-- ⭐⭐ **`Hinv` 就是「`A†` 在 `range A` 上是 `A` 的右逆」**。

这一定理把 `Hinv` 从「可逆性」重新定位到「值域上的往返 = id」。
注意 `A ∘ A†` 的复合顺序 —— 它是**满射一侧**的信息，

**⚠ 这条是本文件整个判决的语言基础**：它表明 `Hinv` 根本不是
「`A` 可逆」的强条件，而是「`A` 在其值域上可被 `A†` 右反演」的弱条件，
与「`A` 有左逆 / `A` 单射」**不同方向**。 -/
theorem hinv_is_right_inverse (A : E →L[ℝ] F) (h : Hinv A) :
    ∀ w ∈ Set.range A, A (A.adjoint w) = w := h

/-- ⭐⭐ **右逆 ⟹ `Hinv`**（把 `A†` 换成别的右逆 `φ` 的形式）。

若 `φ` 是 `A` 的**右逆**（`∀ y, A (φ y) = y`）且 `φ = A†`，则 `Hinv A`。
这是 `Hinv` 的**同向**（充分条件），与「左逆」方向相反。

**⚠ 注意**：这里必须要求 `φ = A†`；仅「存在某个右逆 `φ`」**不**给出 `Hinv`，
因为 `Hinv` 的陈述**硬编码**了 `A.adjoint`。这正说明 `Hinv` 是关于
`A` 与 `A†` 之**具体**关系的条件，不可被「存在某个逆」替代。 -/
theorem hinv_of_rightinverse_adjoint (A : E →L[ℝ] F) (φ : F →L[ℝ] E)
    (h : ∀ y, A (φ y) = y) (hphi : A.adjoint = φ) : Hinv A := by
  intro w _
  rw [hphi]
  exact h w

/-! ===========================================================================
    §2  ⭐⭐⭐ **G1 判决**：单射 / 左逆**不能**推出 `Hinv`
    =========================================================================== -/

/-- **`A = (1/2) • 1`（即 `x ↦ x/2`）有左逆 `φ = 2 • 1`**，故为单射。

（`A` 取自 `ResidualReduces` §3.7 的反例族 —— 那里用同样两个算子
击破无 `hinv` 的命题；本文件用它们击破「单射可替代 `hinv`」。） -/
theorem Ah_leftinv : ∃ φ : ℝ →L[ℝ] ℝ, ∀ x, φ (Ah x) = x := by
  refine ⟨(2 : ℝ) • (1 : ℝ →L[ℝ] ℝ), ?_⟩
  intro x
  rw [Ah_apply]; simp

/-- **`Ah` 是单射**（由 `Ah_leftinv` 直接得到，写出便于引用）。 -/
theorem Ah_injective : Function.Injective Ah := by
  intro x y hxy
  rw [Ah_apply, Ah_apply] at hxy
  linarith

/-- ⭐⭐⭐ **`Hinv Ah` 为假**：`A (A† 1) = (1/2) * ((1/2) * 1) = 1/4 ≠ 1`。 -/
theorem Ah_hinv_false : ¬ Hinv Ah := by
  intro h
  have hmem : (1 : ℝ) ∈ Set.range Ah := ⟨2, by rw [Ah_apply]; norm_num⟩
  have hv := h 1 hmem
  rw [Ah_adjoint, Ah_apply, Ah_apply] at hv
  norm_num at hv

/-- **`A = 2 • 1`（即 `x ↦ 2x`）有左逆 `φ = (1/2) • 1`**，故为单射。 -/
theorem A2_leftinv : ∃ φ : ℝ →L[ℝ] ℝ, ∀ x, φ (A2 x) = x := by
  refine ⟨(1/2 : ℝ) • (1 : ℝ →L[ℝ] ℝ), ?_⟩
  intro x
  rw [A2_apply]; simp

/-- **`A2` 是单射**。 -/
theorem A2_injective : Function.Injective A2 := by
  intro x y hxy
  rw [A2_apply, A2_apply] at hxy
  linarith

/-- ⭐⭐⭐ **`Hinv A2` 亦为假**：`A (A† 1) = 4 ≠ 1`。 -/
theorem A2_hinv_false : ¬ Hinv A2 := by
  intro h
  have hmem : (1 : ℝ) ∈ Set.range A2 := ⟨1/2, by rw [A2_apply]; norm_num⟩
  have hv := h 1 hmem
  rw [A2_adjoint, A2_apply, A2_apply] at hv
  norm_num at hv

/-- ⭐⭐⭐⭐⭐ **`Hinv` 不能由「`A` 有左逆」推出** —— 即 **G1 的前件放松不成立**。

反例：`A = Ah = (1/2) • 1` 有左逆（`2 • 1`），但 `¬ Hinv Ah`。

**这是本文件的判决定理**：任务书 G1 所设想的
「`hinv : Hinv A` 放宽为 `∃ φ, φ ∘ A = id`」会**削弱前件到假命题**。 -/
theorem leftinv_does_not_give_hinv :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ), (∃ φ : ℝ →L[ℝ] ℝ, ∀ x, φ (A x) = x) → Hinv A) := by
  intro h
  exact Ah_hinv_false (h Ah Ah_leftinv)

/-- ⭐⭐⭐⭐⭐ **`Hinv` 亦不能由「`A` 单射」推出** —— 同一反例。

（`Function.Injective` 比「有左逆」稍弱；本定理说明即使直接用单射作前件，
也**不足以**取代 `hinv`。） -/
theorem injective_does_not_give_hinv :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ), Function.Injective A → Hinv A) := by
  intro h
  exact Ah_hinv_false (h Ah Ah_injective)

/-- ⭐⭐⭐ **并列对照**：两个**不同的**单射算子**都**不满足 `Hinv`。

这说明「不满足 `Hinv`」不是某个算子的偶然，而是**单射这一侧整体**的性质：
$A = c \cdot 1$（$c \neq \pm 1$）都可作反例。 -/
theorem inj_but_not_hinv_together :
    Function.Injective Ah ∧ ¬ Hinv Ah ∧ Function.Injective A2 ∧ ¬ Hinv A2 :=
  ⟨Ah_injective, Ah_hinv_false, A2_injective, A2_hinv_false⟩

/-! ===========================================================================
    §3  ⭐⭐⭐⭐⭐ **主判决**：把 `hinv` 换成「有左逆」后主定理为**假**

    任务书第 3 步要求交付 `writeBack_reduces_error_inj`。
    本文件**证明它不存在**（即它是假命题）：只需显式给出一个
    「有左逆 + `hFit` + `hη` + `hne` 齐全、但结论失败」的实例。
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **G1 的否证（`A` 有左逆版）**：存在 `A`（**有左逆**）、`η`、`x'`、`θ`，
满足 `hFit : x' ∈ range A`、`hη : |1 - η| < 1`、`hne : A θ ≠ x'`，
但 `¬ (errL A x' (writeBackL A η x' θ) < errL A x' θ)`（误差**未减小**）。

**构造**：`A = A2 = 2 • 1`（`x ↦ 2x`）、`η = 1`、`x' = 0`、`θ = 1`。
- `A2` 有左逆 `(1/2) • 1` ✓（`A2_leftinv`）；
- `0 ∈ range A2`（`= A2 0`）✓；
- `|1 - 1| = 0 < 1` ✓；
- `A2 1 = 2 ≠ 0` ✓。

回写后 `θ' = 1 + 1 • A2† (0 - 2) = 1 + 2·(-2) = -3`，故
误差 `‖A2 (-3) - 0‖ = ‖-6‖ = 6`，**大于**初始 `‖A2 1 - 0‖ = 2`。
**误差从 `2` 增至 `6`** —— 结论失败。 -/
theorem no_inj_relaxation :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η : ℝ) (x' : ℝ) (θ : ℝ),
        (∃ φ : ℝ →L[ℝ] ℝ, ∀ x, φ (A x) = x) →
        x' ∈ Set.range A → |1 - η| < 1 → A θ ≠ x' →
        errL A x' (writeBackL A η x' θ) < errL A x' θ) := by
  intro h
  have hfit : (0 : ℝ) ∈ Set.range A2 := ⟨0, by rw [A2_apply]; norm_num⟩
  have hne : A2 1 ≠ 0 := by rw [A2_apply]; norm_num
  have hlt := h A2 1 0 1 A2_leftinv hfit (by norm_num) hne
  rw [errL, writeBackL, A2_adjoint, A2_apply, A2_apply] at hlt
  rw [errL, A2_apply] at hlt
  norm_num at hlt

/-- ⭐⭐⭐⭐ **与上条等价的「单射」版本**：即使把前件写成 `Function.Injective A`
（比「有左逆」更直接），主定理**仍为假**。

⟹ 本文件对 G1 的判决不依赖于「左逆」这一表述的选择。 -/
theorem no_injective_relaxation :
    ¬ (∀ (A : ℝ →L[ℝ] ℝ) (η : ℝ) (x' : ℝ) (θ : ℝ),
        Function.Injective A →
        x' ∈ Set.range A → |1 - η| < 1 → A θ ≠ x' →
        errL A x' (writeBackL A η x' θ) < errL A x' θ) := by
  intro h
  have hfit : (0 : ℝ) ∈ Set.range A2 := ⟨0, by rw [A2_apply]; norm_num⟩
  have hne : A2 1 ≠ 0 := by rw [A2_apply]; norm_num
  have hlt := h A2 1 0 1 A2_injective hfit (by norm_num) hne
  rw [errL, writeBackL, A2_adjoint, A2_apply, A2_apply] at hlt
  rw [errL, A2_apply] at hlt
  norm_num at hlt

/-! ===========================================================================
    §4  附带发现：`Hinv` 在**唯一被使用处**等价于广义逆条件 `A A† A = A`

    `ResidualReduces.key_identity_fit` 只在 `rw [h1, hinv _ hsub]` 一处用 `hinv`
    （原文第 270 行），那里 `hsub : x' - A θ ∈ Set.range A`。
    故所需信息仅为「`A A†` 在 `range A` 上是 id」，即 `A A† A = A`。
    下面给出该弱化形式**确实足够**（`key_identity_fit_of_hgen`），
    以及二者在前件层面**互相蕴含**（`hgen_of_hinv` + 反向）。
    =========================================================================== -/

/-- ⭐ **广义逆条件** `A A† A = A`（只对 `A` 的像点成立，看似比 `Hinv` 弱）。 -/
def Hgen (A : E →L[ℝ] F) : Prop := ∀ θ, A (A.adjoint (A θ)) = A θ

/-- ⭐ `Hinv A ⟹ Hgen A`（`A θ ∈ range A`）。 -/
theorem hgen_of_hinv (A : E →L[ℝ] F) (h : Hinv A) : Hgen A :=
  fun θ => h (A θ) ⟨θ, rfl⟩

/-- ⭐⭐⭐ **`Hgen` 足以推出收缩式** —— 即 `Hinv` 无法再弱化的印证。

证明与 `ResidualReduces.key_identity_fit` 同路，但只在 `x' - Aθ` 的像点上用条件。 -/
theorem key_identity_fit_of_hgen (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hgen : Hgen A) (hFit : x' ∈ Set.range A) :
    A (writeBackL A η x' θ) - x' = (1 - η) • (A θ - x') := by
  have h1 : A (writeBackL A η x' θ) = A θ + η • A (A.adjoint (x' - A θ)) := by
    simp [writeBackL]
  obtain ⟨a, ha⟩ := hFit
  have hsub : x' - A θ = A (a - θ) := by rw [map_sub, ha]
  have hh : A (A.adjoint (x' - A θ)) = x' - A θ := by
    rw [hsub]; exact hgen (a - θ)
  rw [h1, hh]
  module

/-- ⭐⭐ **`Hgen` 版主定理**：把 `hinv : Hinv A` 换成 `hgen : Hgen A` 后结论仍成立。

⟹ 这就是 G1 方向上**真正可行**的那一小步放松（`Hinv → Hgen`）。
**⚠ 但它不是 G1**：`Hgen` 仍是关于 `A†` 的条件，与「单射 / 左逆」无关；
且 `Hgen` 在 `Hinv` 被使用的那一点上与 `Hinv` **完全等价**（见 `hgen_of_hinv`
与 `hinv_of_hgen`），故**不扩大覆盖面**，只是把条件说得更「局部」。 -/
theorem writeBack_reduces_error_gen (A : E →L[ℝ] F) (η : ℝ) (x' : F) (θ : E)
    (hgen : Hgen A) (hFit : x' ∈ Set.range A) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
    errL A x' (writeBackL A η x' θ) < errL A x' θ := by
  have h := key_identity_fit_of_hgen A η x' θ hgen hFit
  simp only [errL, h, norm_smul, Real.norm_eq_abs]
  have hpos : 0 < ‖A θ - x'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith [abs_nonneg (1 - η), abs_lt.mp hη]

/-- ⭐ **反向：`Hgen` 在「`range A` 上的点」上给出 `Hinv`**。

严格说 `Hinv` 要求对**所有** `w ∈ range A`；`Hgen` 只覆盖 `w = A θ`。
而 `range A` 的每个元素**都**具有 `A θ` 的形式，故二者等价。 -/
theorem hinv_of_hgen (A : E →L[ℝ] F) (h : Hgen A) : Hinv A := by
  intro w hw
  obtain ⟨θ, rfl⟩ := hw
  exact h θ

/-- ⭐⭐⭐ **`Hinv ↔ Hgen`**：G1 方向上已知的最强放松其实**无放松效果**。 -/
theorem hinv_iff_hgen (A : E →L[ℝ] F) : Hinv A ↔ Hgen A :=
  ⟨hgen_of_hinv A, hinv_of_hgen A⟩

end ResidualReduces
end FateV2.Loop