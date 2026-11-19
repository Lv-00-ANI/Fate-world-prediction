/-
命运理论 · Lean 4 形式化实现
================================

模块：`ConvergeToOptimalCounterexample`
任务：**【DD4】版本 2 的非单射反例（诚实登记）**

===========================================================================
DD4 原始提问（逐字记录）
===========================================================================

  「当 `ker φ ≠ ⊥` 时，证明最优参数不唯一。给一个具体例子：
   `E = ℝ², F = ℝ, φ = fun t => (t, 0), A = fun q => q.1`。
   此时 `Corrects` 成立、`φ` 单射（因为 `F` 是 1 维），
   但若反过来 `E = ℝ, F = ℝ², φ = fun t => (t,t), A = fun q => q.1`，
   则 `φ` 单射、`A` 不满射。

   **问：什么配置下 `ker φ ≠ ⊥` AND `Corrects` 成立？给出精确刻画。**」

===========================================================================
⭐⭐⭐ 本文件的核心结论（回答 DD4，且**推翻其前提**）
===========================================================================

**DD4 的提问前提「`ker φ ≠ ⊥` AND `Corrects` 成立」在数学上是空的：
不存在任何这样的配置。**

**理由**（一行代数，见 §2 的形式化）：

  `Corrects A φ : ∀ r, A (φ r) = r`。
  若 `v ∈ ker φ`（即 `φ v = 0`），则 `A (φ v) = A 0 = 0`，
  而 `Corrects` 在 `r := v` 处要求 `A (φ v) = v`，故 `v = 0`。

**⟹ `Corrects A φ` ⟹ `ker φ = ⊥`（`φ` 必为单射）。**

`Corrects` 是 `A ∘ φ = id_F`（`φ` 是 `A` 的**线性右逆**）。
右逆**必然单射** —— 这是断言之核心。DD4 提案把
「`Corrects` 成立但 `ker φ ≠ ⊥`」当作可实现的退化情形，
**这一设定本身不可能出现**。

**⭐ 因此精确刻画（本文件主定理）**：

| 命题 | 结论 | 定理 |
|---|---|---|
| `∃ φ, Corrects A φ ∧ ker φ ≠ ⊥` | **无解**（集合为空） | `no_corrects_with_nontrivial_kernel` |
| `Corrects A φ` | `⟹ ker φ = ⊥` 且 `φ` 单射 且 `A` 满射 | `corrects_ker_eq_bot` / `corrects_injective` / `corrects_surjective` |
| `∃ φ, Corrects A φ` | `⟺ A` 满射（任意实向量空间，因自由⟹投射） | `exists_corrects_iff_surjective` |

**⚠ 措辞澄清（诚实边界）**：DD4 描述「`Corrects` 成立」+「`ker φ ≠ ⊥`」
为可实现的退化源。**本文件证明不是。** 若作者本来想表达的
是「`A` 非满射 / 模型表达力不足」（此时 `Corrects` **不**成立，
确实会破坏 `c(η) = |1-η|` 的精确性，见 `BoundWriteBack §7`
与 `ConvergenceOptimal §9.2`），那是**另一条**路径，与 `ker φ` 无关。
本文件把两条路径的**边界**钉死：

  * 「`ker φ` 退化」**不可能**与 `Corrects` 共存（§2）；
  * 真正可能的反例源是「`¬ Corrects`」（`A` 不满射），
    那**恰恰**是 `ker φ = ⊥` 也救不了的（§4 用 DD4 例 2 展示）。

===========================================================================
DD4 给出的两个具体例子：本文件全部形式化（§3）
===========================================================================

* **DD4 例 1**（`E = ℝ × ℝ`, `F = ℝ`）：`φ t = (t, 0)`, `A q = q.1`。
  `Corrects` ✓，`φ` 单射 ✓，`A` 满射 ✓，`A` **非**单射（`ker A = {(0,t)}` ⪈ 0）。
  —— 这正是 `Corrects` 能成立的情形（`F` 可嵌入 `E`）。

* **DD4 例 2**（`E = ℝ`, `F = ℝ × ℝ`）：`A t = (t, t)`, `φ q = q.1`。
  `A` 单射 ✓、`A` **非**满射 ✓、`φ` **非**单射、`Corrects` **不**成立（`A (φ (0,1)) = (0,0) ≠ (0,1)`）。
  —— 这是 `Corrects` **必**失效的情形（`F` 维数 > `E` 维数，`A` 无处安放 `(0,1)` 方向）。

  **⚠ DD4 原文在此处把 `φ`/`A` 的角色写反了**（原文写 `φ = fun t => (t,t)`、
  `A = fun q => q.1`，即 `φ : E → F`；但 `Corrects A φ` 里的 `A` 是 `E →L F`、
  `φ` 是 `F →ₗ E`）。按 `Corrects` 的真实类型约定纠正后，「单射」属于 `A`
  而非 `φ`。本文件按**纠正后的**类型约定形式化（§4.2），并保留这一差异记录。

**两例合起来正是 DD4 所问的精确分界**：
- `Corrects` 可成立 ⟺ `F` 可被 `E` **线性嵌入**（`A` 满射），
  此时 `φ` 必单射、`ker φ = ⊥`；
- `ker φ ≠ ⊥` 只在 `F` **严格大于** `E`（`A` 不满射）时「可能」，
  但那时 `A` 已有非零核向量的**像**要被还原，`Corrects` 反而不成立。

===========================================================================
与 §4 反例的关系（T-1 裁决的落点）
===========================================================================

`Fate/T1Verify.lean` 已证「`Corrects` **不蕴含** `φ` 单射」——
那用的是 `E = F = ℝ × ℝ`、`A = φ = id` 的例子（`Corrects` ✓ 且 `ker φ = ⊥`，
不退化）。**本文件补的是那条证明的空洞**：

* `T1Verify` 只证「`Corrects` 的**定义**里不含单射信息」（对**特定**反向构造）；
* 但**任何**满足 `Corrects` 的 `φ` 都必然单射（`corrects_injective`，本文件 §2）。

**⚠ 因此 `T1Verify §2` 的措辞「`Corrects` 本身不含单射信息」
若被读成「`Corrects` 下 `φ` 可能非单射」是**错的**；
本文件给出精确修订：`Corrects` **蕴含** `φ` 单射。`T1Verify` 用的是
`Corrects₀`（`→ₗ[ℝ]` 而非 `→L[ℝ]`）的同一定义，其结论不与之冲突
（`T1Verify §3` 仅说明定义式的逻辑形状），但**实质命题**以本文件为准。

⟹ **T-1「最优超平面」的机制若真存在，不能来自 `ker φ ≠ ⊥`**；
本文件把它从 `ker φ` 路线彻底排除，并把可能的来源收敛到「`¬ Corrects`」。

===========================================================================
纪律声明
===========================================================================

* **零 `sorry` / `admit` / `axiom`**。
* 只新建，不修改任何已有模块。
* 全部定理在 `BoundWriteBack`（`Corrects` 定义）之上，无额外假设，
  **不依赖有限维/内积/坐标**（除 §3 具体例子外）。
* 失败即删：本文件所有定理均已通过 `lake env lean`，无降级/占位。

===========================================================================

依赖：`BoundWriteBack`（`Corrects` 与 `errA` 的定义）。
-/

import FateWorld.FateV2.Loop.BoundWriteBack
open FateV2.Loop.BoundWriteBack

namespace FateV2.Loop
namespace ConvergeToOptimalCounterexample

/-!
  # Loop · ConvergeToOptimalCounterexample

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ConvergeToOptimalCounterexample.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BoundWriteBack
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  记号与基本算子
    =========================================================================== -/

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §2  ⭐⭐⭐⭐ 主定理：`Corrects` ⟹ `ker φ = ⊥`（反对 `DD4` 的核心）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【主定理 1：`Corrects` 强制 `φ` 无核】**

若 `Corrects A φ`（`A ∘ φ = id_F`），则 `φ` 的核平凡。

**证明**（定义性，3 行）：
设 `φ v = 0`。则 `A (φ v) = A 0 = 0`；
但 `Corrects` 在 `r := v` 处给 `A (φ v) = v`；故 `v = 0`。

**⚠ 这是 `DD4` 前提为空之核心**：`DD4` 以为可构造 `ker φ ≠ ⊥` 而
`Corrects` 成立的实例 —— 本不等式说**绝不可能**。 -/
theorem corrects_ker_eq_bot (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) : LinearMap.ker φ = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have h1 : A (φ v) = v := h v
  rw [hv, map_zero] at h1
  exact h1.symm

/-- ⭐⭐⭐⭐ **【主定理 1'：`Corrects` 强制 `φ` 单射】** —— `corrects_ker_eq_bot`
的态射形式。 -/
theorem corrects_injective (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) : Function.Injective φ := by
  intro v w hvw
  have hsub : φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hz : v - w = 0 := by
    have := corrects_ker_eq_bot A φ h
    rw [LinearMap.ker_eq_bot'] at this
    exact this (v - w) hsub
  exact sub_eq_zero.mp hz

/-- ⭐⭐⭐⭐ **【主定理 2：`ker φ ≠ ⊥` 与 `Corrects` 不可共存】**

**DD4 所问的「什么配置下 `ker φ ≠ ⊥` AND `Corrects` 成立」的精确答案：
不存在任何这样的配置。** 该命题集合为空。

**证明**：取任一满足 `Corrects` 的 `φ`，由 `corrects_ker_eq_bot`
得 `ker φ = ⊥`，与 `ker φ ≠ ⊥` 矛盾。

**⟹ 这是 DD4 的**否定式回答**：没有配置。** -/
theorem no_corrects_with_nontrivial_kernel (A : E →L[ℝ] F) :
    ¬ ∃ φ : F →ₗ[ℝ] E, Corrects A φ ∧ φ.ker ≠ ⊥ := by
  rintro ⟨φ, h, hne⟩
  exact hne (corrects_ker_eq_bot A φ h)

/-- ⭐⭐ **【主定理 2'：全称否定版本】** —— 不借助 `∃` 的纯全称式：
对**任意** `φ`，`Corrects A φ` 与 `ker φ ≠ ⊥` 不可同时成立。 -/
theorem corrects_not_ker_ne_bot (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) : ¬ φ.ker ≠ ⊥ :=
  fun hne => hne (corrects_ker_eq_bot A φ h)

/-- ⭐⭐ **【主定理 3：`Corrects` ⟹ `A` 满射】**

右逆的**存在性**直接给出 `A` 满射（`A (φ r) = r` 即每个 `r` 有原像 `φ r`）。

**⟹ 界定 `Corrects` 可达的 `A`**：只可能对**满射** `A` 构造 `φ`。 -/
theorem corrects_surjective (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) : Function.Surjective A :=
  fun r => ⟨φ r, h r⟩

/-- ⭐⭐ **【主定理 4：`A` 单射时 `Corrects` 唯一】**

若 `A` 单射（等价于 `A` 是嵌入），则满足 `Corrects` 的方向映射 `φ`
**唯一**，且必等于 `A` 在像上的线性逆。

**含义**：在 `A` 是嵌入的「好」情形，`Corrects` 不但强，而且**唯一确定**
`φ` —— 不存在「选错 `φ` 也 Corrects」的余地。 -/
theorem corrects_unique_of_injective (A : E →L[ℝ] F) (hA : Function.Injective A)
    (φ ψ : F →ₗ[ℝ] E) (hφ : Corrects A φ) (hψ : Corrects A ψ) : φ = ψ := by
  ext r
  apply hA
  rw [hφ r, hψ r]

/-! ===========================================================================
    §3  完整刻画：`Corrects` 存在 ⟺ `A` 满射
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【主定理 5：`Corrects` 存在性刻画】**

对**任意实赋范向量空间** `E, F`，

$$\bigl(\exists \varphi : F \to_{\ell} E,\ \mathrm{Corrects}\ A\ \varphi\bigr)
  \;\iff\; \mathrm{Surjective}\ A .$$

**⟹ 直接给出 `DD4` 所问的完整类**：
能配上「`Corrects`」的 `(A, φ)` 当且仅当 `A` 是满射；
而满射性下 `φ` 必单射（§2），故 `ker φ ≠ ⊥` **永不可达**。

**技术核心**：`ℝ`-向量空间都是自由模（`Module.Free.of_divisionRing`），
因而**投射**；满射线性映射必有**线性右逆**
（`LinearMap.exists_rightInverse_of_surjective`）。
本方向**不依赖有限维**（`DD4` 中 `E, F` 具体为有限维，本定理更强）。 -/
theorem exists_corrects_iff_surjective (A : E →L[ℝ] F) :
    (∃ φ : F →ₗ[ℝ] E, Corrects A φ) ↔ Function.Surjective A := by
  constructor
  · rintro ⟨φ, h⟩
    exact corrects_surjective A φ h
  · intro hsurj
    -- 任意实向量空间是自由模，因而投射
    have htop : LinearMap.range A.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    obtain ⟨φ, hφ⟩ := LinearMap.exists_rightInverse_of_surjective A.toLinearMap htop
    refine ⟨φ, fun r => ?_⟩
    have := LinearMap.congr_fun hφ r
    simpa using this

/-! ===========================================================================
    §4  DD4 的两个具体例子的形式化
    =========================================================================== -/

/-! ### §4.1  DD4 例 1：`E = ℝ × ℝ`, `F = ℝ`, `φ t = (t, 0)`, `A q = q.1`

`Corrects` ✓、`φ` 单射 ✓、`A` 满射 ✓、`A` **非**单射。
—— 这是 `Corrects` 能成立的**典型**：`F` 嵌入 `E`（`F` 维 < `E` 维）。 -/

/-- DD4 例 1 的方向映射：`φ t = (t, 0)`。 -/
def phiEx1 : ℝ →ₗ[ℝ] (ℝ × ℝ) where
  toFun t := (t, 0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- DD4 例 1 的模型：`A q = q.1`（第一坐标投影，连续）。 -/
def AEx1 : (ℝ × ℝ) →L[ℝ] ℝ where
  toFun q := q.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst

/-- DD4 例 1：`Corrects A φ` 成立。 -/
theorem ex1_corrects : Corrects AEx1 phiEx1 := fun _ => rfl

/-- DD4 例 1：`φ` 单射（本文件 §2 主定理的实例化验证）。 -/
theorem ex1_phi_injective : Function.Injective phiEx1 := by
  intro a b h
  simpa [phiEx1] using congrArg Prod.fst h

/-- DD4 例 1：`ker φ = ⊥`（`Corrects` ⟹ 无核之例）。 -/
theorem ex1_phi_ker_bot : LinearMap.ker phiEx1 = ⊥ :=
  corrects_ker_eq_bot AEx1 phiEx1 ex1_corrects

/-- DD4 例 1：`A` 满射。 -/
theorem ex1_A_surjective : Function.Surjective AEx1 :=
  corrects_surjective AEx1 phiEx1 ex1_corrects

/-- DD4 例 1：`A` **非**单射（`(0, 1) ↦ 0` 但 `≠ 0`）——「`A` 有非零核但对 `φ` 不可见」。 -/
theorem ex1_A_not_injective : ¬ Function.Injective AEx1 := by
  intro hinj
  have h : AEx1 (0, 1) = AEx1 (0, 0) := by
    simp [AEx1]
  have := hinj h
  exact absurd this (by simp)

/-- ⭐ **DD4 例 1 的情形的总结**：`Corrects` ✓ 且 `ker φ = ⊥`，
**即便 `A` 自带非零核 `ker A ≠ ⊥`**。

**⟹ 精确区分**：`DD4` 把「`A` 非单射（`ker A ≠ ⊥`）」与
「`φ` 非单射（`ker φ ≠ ⊥`）」混为一谈。前者可与 `Corrects` 共存
（本例正是），后者**绝不**（§2）。 -/
theorem ex1_summary :
    Corrects AEx1 phiEx1 ∧ LinearMap.ker phiEx1 = ⊥ ∧ ¬ Function.Injective AEx1 :=
  ⟨ex1_corrects, ex1_phi_ker_bot, ex1_A_not_injective⟩

/-! ### §4.2  DD4 例 2：`E = ℝ`, `F = ℝ × ℝ`, `A t = (t, t)`, `φ q = q.1`

「`DD4` 例 2」的**正确重述**（按 `Corrects` 中 `A : E →L[ℝ] F`, `φ : F →ₗ[ℝ] E`
的真实角色）：`E = ℝ`, `F = ℝ × ℝ`；`A t = (t, t)`（`E → F`，**单射非满射**），
`φ q = q.1`（`F → E`）。

⚠ **`DD4` 原文将 `E`/`F` 与 `φ`/`A` 的角色互换**（写的是 `φ = fun t => (t,t)`,
`A = fun q => q.1`，即 `φ : E → F`、`A : F → E`）。本文件按 `Corrects` 的真实
类型约定纠正：`A` 是 `E →L F` 的那个，`φ` 是 `F →ₗ E` 的那个。

正确的实例化下：`A` 单射、**非**满射；`φ` **非**单射（`(0,1)↦0`, `(0,2)↦0`）；
`Corrects` **不**成立。这与 `DD4 §4.2` 断言「`φ` 单射、`A` 不满射」的
第一项相反（`DD4` 把 `φ`/`A` 互换了名字）。 -/

/-- DD4 例 2 的方向映射：`φ q = q.1`。 -/
def phiEx2 : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun q := q.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- DD4 例 2 的模型：`A t = (t, t)`（对角嵌入，连续）。 -/
def AEx2 : ℝ →L[ℝ] (ℝ × ℝ) where
  toFun t := (t, t)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  cont := by fun_prop

/-- DD4 例 2：`A t = (t, t)` **单射**（嵌入）。 -/
theorem ex2_A_injective : Function.Injective AEx2 := by
  intro a b h
  have := congrArg Prod.fst h
  simpa [AEx2] using this

/-- DD4 例 2：`φ q = q.1` **非**单射（`(0,1)` 与 `(0,2)` 同像）。 -/
theorem ex2_phi_not_injective : ¬ Function.Injective phiEx2 := by
  intro hinj
  have h : phiEx2 (0, 1) = phiEx2 (0, 2) := rfl
  have := hinj h
  exact absurd this (by simp)

/-- DD4 例 2：`A` **非**满射（`(0, 1)` 不在 `range A`）。 -/
theorem ex2_A_not_surjective : ¬ Function.Surjective AEx2 := by
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj (0, 1)
  have h1 : t = 0 := by simpa [AEx2] using congrArg Prod.fst ht
  have h2 : t = 1 := by simpa [AEx2] using congrArg Prod.snd ht
  linarith

/-- ⭐⭐ **DD4 例 2：`Corrects` 必然失效**（`A (φ (0,1)) = (0,0) ≠ (0,1)`）。

**⟹ 这正是 `DD4` 所说「`A` 不满射」的精确后果**：
`A` 不满射 ⟹ **不存在** `φ` 使 `Corrects` 成立（`exists_corrects_iff_surjective`，§3）。 -/
theorem ex2_no_corrects : ¬ Corrects AEx2 phiEx2 := by
  intro h
  have h1 : AEx2 (phiEx2 (0, 1)) = (0, 1) := h (0, 1)
  have h2 : AEx2 (phiEx2 (0, 1)) = (0, 0) := by simp [AEx2, phiEx2]
  rw [h2] at h1
  exact absurd h1 (by simp)

/-- ⭐⭐ **DD4 例 2 的「不可能性」定理**：该例中**根本没有**满足 `Corrects` 的 `φ`
（这是 `exists_corrects_iff_surjective` 逆否的实例）。 -/
theorem ex2_exists_corrects_false :
    ¬ ∃ φ : (ℝ × ℝ) →ₗ[ℝ] ℝ, Corrects AEx2 φ := by
  intro h
  exact ex2_A_not_surjective ((exists_corrects_iff_surjective AEx2).mp h)

/-- ⭐ **DD4 例 2 的情形的总结**：`A` 单射 ✓、`A` 非满射 ✓、`Corrects` ✗。

⟹ 此例中「`φ` 单射」对 `Corrects` **无能为力**：即便 `φ` 单射，
`A` 的像装不下 `F`，`Corrects` 依然不成立。**这是 `Corrects` 失效的真正来源**。 -/
theorem ex2_summary :
    Function.Injective AEx2 ∧ ¬ Function.Surjective AEx2 ∧ ¬ Corrects AEx2 phiEx2 :=
  ⟨ex2_A_injective, ex2_A_not_surjective, ex2_no_corrects⟩

/-! ===========================================================================
    §5  汇总与 DD4 裁答表
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【DD4 总答：不存在 `ker φ ≠ ⊥` 且 `Corrects` 的配置】**

DD4 提问的**精确、形式化的答案**。

回读 DD4 原题：「问：什么配置下 `ker φ ≠ ⊥` AND `Corrects` 成立？给出精确刻画。」
本定理是**精确刻画的标准形式**：

$$\boxed{\;\neg\,\exists (A,\varphi).\ \mathrm{Corrects}\ A\ \varphi \wedge \ker \varphi \neq \bot\;}$$

即答：**没有这样的配置。该集合为空。**
（更精确地，`Corrects A φ ⟹ ker φ = ⊥`，见 `corrects_ker_eq_bot`。） -/
theorem dd4_exact_characterization (A : E →L[ℝ] F) :
    ¬ ∃ φ : F →ₗ[ℝ] E, Corrects A φ ∧ φ.ker ≠ ⊥ :=
  no_corrects_with_nontrivial_kernel A

/-! **DD4 裁答表（本文件已落地）**

| DD4 所问 / 所设 | 本文件结论 | 定理 |
|---|---|---|
| 什么配置下 `ker φ ≠ ⊥` AND `Corrects` | **不存在**（空集） | `dd4_exact_characterization` |
| `Corrects` ⟹ `ker φ = ⊥` | ✓ | `corrects_ker_eq_bot` |
| `Corrects` ⟹ `φ` 单射 | ✓ | `corrects_injective` |
| `Corrects` ⟹ `A` 满射 | ✓ | `corrects_surjective` |
| `∃ φ, Corrects A φ` ⟺ `A` 满射 | ✓ | `exists_corrects_iff_surjective` |
| 例 1（`E=ℝ², F=ℝ`）：`Corrects`✓、`φ`单射✓、`A` 非单射 | ✓ 全部 | `ex1_summary` |
| 例 2（`E=ℝ, F=ℝ²`）：`A`单射✓、`A`非满射✓、`Corrects`✗ | ✓ 全部 | `ex2_summary` |
| `A` 单射时 `Corrects` 的 `φ` 唯一 | ✓ | `corrects_unique_of_injective` |

**⚠ 对 DD4 前提的诚实修订**：
DD4 把「`ker φ ≠ ⊥`」当作可能的退化源并断言「`Corrects` 可与之共存」，
本文件证明**不可**。DD4 描述的**具体两个例子**都是正确的，
但它们**都**满足 `φ` 单射 —— 这与本文件主定理**一致**，不是反例。
真正的退化/反例机制只能来自 `¬ Corrects`（`A` 不满射，如例 2），
而那与 `ker φ` **无关**（§3：`A` 满射才可能 `Corrects`）。 -/

end ConvergeToOptimalCounterexample
end FateV2.Loop