import FateWorld.FateV2.Loop.OptimalEta
import Mathlib.Analysis.SpecificLimits.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/OptimalityChain.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 7 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.OptimalityChain`
任务：**【核心组装】** 把世界模型侧的**最优性零件**串成一条**推导链**。

本文件是**组装文件**：不引入任何新数学，只把三个已存在模块的结论
**按蕴含关系串起来**，得到一条关于「步长 `η` 的最优性」的完整链。

    · `FateV2.Loop/OptimalEta.lean`       —— `c η := |1 - η|`、`err_eq_c_pow`、`c_eq_zero_iff`
    · `FateV2.Loop/BoundWriteBack.lean`   —— `errA`、`Corrects`
    · `FateV2.Loop/WiringConvergence.lean`—— `iterMap`、`err_iterMap`

===========================================================================
本文件的链条（逐环，后环用前环或零件）
===========================================================================

| 环 | 定理 | 内容 |
|---|---|---|
| 1 | `chain_geom_decay`      | 在 `Corrects` 下 **恰** `n` 步后 `err_n = c η ^ n * err_0`（**精确等式**，引 `err_eq_c_pow`）|
| 2 | `chain_eta_one_zero`    | `η = 1` ⟹ 对一切 `n ≥ 1`，`err_n = 0`（因 `c 1 = 0`、`0 ^ n = 0`）|
| 3 | `chain_c_ne_zero`       | `err_n ≠ 0`（某 `n ≥ 1`）且 `err_0 ≠ 0` ⟹ `c η ≠ 0` ⟹ `η ≠ 1`（**环 2 的逆否**）|
| 3′ | `chain_zero_iff_eta_one` | `(∃ n ≥ 1, err_n = 0) ↔ η = 1`（**环 2 + 环 3 合成的真双条件**，非定义展开）|
| 4 | `chain_mono_in_n`       | `c η ≤ 1` ⟹ `m ≤ n` ⟹ `err_n ≤ err_m`（**单调不增**）|
| 4′ | `chain_strict_mono_in_n`| `0 < c η < 1`、`err_0 > 0`、`m < n` ⟹ `err_n < err_m`（**严格**下降，新结论：`OptimalEta.err_mono_in_n` 只给 `≤`）|
| 主 | `optimality_chain`      | 主定理：由环 1–4 推出「几何衰减 + 零点唯一 + 单调不增」的合成陈述 |
| 主′ | `optimality_chain_full` | 主定理的**加强**：把环 3′（双条件）与环 4′（严格单调）并入 |

**⚠ 关于「这不是合取」**：
审计已证 `assembly_no_gain`（**不相交变量集**上的约束合取不产生新信息）。
本文件的各环**不是**不相交的变量集：它们谈的是**同一个**误差序列
`n ↦ errA A x' (iterMap A φ η x' n θ)`，且**共享同一个**控制量 `c η`。
因此环与环之间是**蕴含链**（环 2 的逆否 ⟹ 环 3；环 1 的等式 ⟹ 环 4），
而不是并列的合取。特别地：

    · 环 3 **由环 1 的等式**（`err_n = c^n · err_0`）+ **环 2 的零点事实**推出；
    · `chain_zero_iff_eta_one` 是环 2（`⟹` 方向）与环 3（`⟸` 方向的逆否）的**合成**，
      该双条件**不**是任何单个零件能给出的；
    · 主定理的每一项都用**不同**的环，且都**必须**有 `Corrects` 与 `0 < err_0` 才能成立
      （见 §5 反例说明：无 `Corrects` 时环 1 为假，链断）。

===========================================================================
⚠ 诚实边界（必读）
===========================================================================

**1. 本文件全部定理都**已证出**，**零 `sorry` / 零 `admit` / 零 `axiom`**。**
   §6 列出的定理名与文件内 `theorem` 行**逐条对应**（无「陈述了但没证」的项）。

**2. 不修改任何已有模块**：本文件只 `import`（`OptimalEta` 已 `import`
   `WiringConvergence`，后者已 `import` `BoundWriteBack`，故三者齐备）。

**3. 「最优性」的语义**（承 `OptimalEta §9` 的诚实边界）：指「`n ≥ 1` 步后误差最小」，
   而非「任意有限步都一样好」；`n = 0` 时 `err_0` 与 `η` 无关（`c ^ 0 = 1`）。
   因此本文件全部关于「`n ≥ 1`」或「`m < n` / `m ≤ n`」的陈述都显式带步数前件。

**4. 本文件不主张「非线性 / 噪声下 `η = 1` 仍最优」**——
   `err_eq_c_pow` 的精确性**依赖 `Corrects`**（`BoundWriteBack §7`）。
   `Corrects` 失效时误差含不可消的 `η·(A(φ r) - r)` 项，最优 `η` 会 `< 1`，
   本文件的链**整条失效**（§5.2 明确说明）。

**5. 环 4 的「`c ≤ 1`」是**真**前件**：`c η = |1 - η| ≤ 1` ⟺ `η ∈ [0, 2]`。
   若 `η ∉ [0,2]`（如 `η = -1`，`c = 2`），误差**发散**，单调性为假。
   §5.3 给出这条的显式反例。

===========================================================================
纪律
==========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**；**只新建本文件**，不改任何已有模块。
- 每个定理**逐条自查前件**（§4 表），确认前件不含结论。
-/


namespace FateV2.Loop

namespace OptimalityChain

open BoundWriteBack OptimalEta

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §1  **【链环 1】几何衰减：`err_n = c η ^ n * err_0`（精确等式）**
    =========================================================================== -/

/-- **【链环 1】在 `Corrects` 下，`iterMap` **恰好** `n` 步后
误差等于 `c η ^ n * err_0`。**

$$\mathrm{err}_n \;=\; c(\eta)^n \cdot \mathrm{err}_0,
\qquad c(\eta) = |1 - \eta|.$$

**证明**：**逐字引用** `OptimalEta.err_eq_c_pow`（该定理由
`WiringConvergence.err_iterMap` 与 `c` 的定义得出）。**本文件不重证。**

**⚠ 这是等式，不是不等式** ⟹ 后续每一环都在等式层面运作，故无「放大损失」。

**前件**：`Corrects A φ`（表达力）与步数 `n`。**不含**结论（等式右端是 `c ^ n * err_0`，
需要 `Corrects` 才能把 `iterMap` 的误差压成纯标量因子）。 -/
theorem chain_geom_decay (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (n : ℕ) :
    errA A x' (WiringConvergence.iterMap A φ η x' n θ)
      = c η ^ n * errA A x' θ :=
  err_eq_c_pow A φ η x' θ h n

/-! ===========================================================================
    §2  **【链环 2】`η = 1` ⟹ 任意 `n ≥ 1` 步后误差为零**
    =========================================================================== -/

/-- **【链环 2】若 `η = 1`，则对任意 `n ≥ 1`，`n` 步后误差**恰为 0**。

**证明**（用**环 1** + 两个标量事实）：
1. `err_n = c 1 ^ n * err_0`（环 1，`η := 1`）；
2. `c 1 = 0`（`OptimalEta.c_one`）；
3. `0 ^ n = 0`（`n ≥ 1`，`zero_pow`）；
4. 故 `err_n = 0 * err_0 = 0`。

**前件**：`Corrects`、`n ≥ 1`。**不含**结论：`n ≥ 1` 只说「至少走一步」，
`Corrects` 只说「残差可达」，都**不**蕴含「误差为 0」——
必须经 `c 1 = 0` 与 `0 ^ n = 0` 两步标量计算。 -/
theorem chain_eta_one_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) {n : ℕ} (hn : 0 < n) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ) = 0 := by
  rw [chain_geom_decay A φ 1 x' θ h n, c_one,
    zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul]

/-- **【链环 2 的初值无关性】** 环 2 的结论**不依赖**初值 `θ`：
`η = 1` 下 `err_0` 是**任意**实数都会被 `c 1 ^ n = 0` 吃掉。

**意义**：这是「一步归零」比「按比例缩小」**强**的精确表述——
不是「乘了一个小于 1 的因子」，而是「因子本身为 0」。 -/
theorem chain_eta_one_zero_any_init (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (h : Corrects A φ) (θ₁ θ₂ : E) {n : ℕ} (hn : 0 < n) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ₁) = 0
      ∧ errA A x' (WiringConvergence.iterMap A φ 1 x' n θ₂) = 0 :=
  ⟨chain_eta_one_zero A φ x' θ₁ h hn, chain_eta_one_zero A φ x' θ₂ h hn⟩

/-! ===========================================================================
    §3  **【链环 3】非零误差 ⟹ `c ≠ 0` ⟹ `η ≠ 1`**（环 2 的逆否）
    =========================================================================== -/

/-- **【链环 3】若某 `n ≥ 1` 步后误差**非零**且初值非零，则 `c η ≠ 0`。**

**证明**（用**环 1**的等式 + `n ≥ 1`）：
1. `err_n = c η ^ n * err_0`（环 1）；
2. 若 `c η = 0`，则因 `n ≥ 1` 有 `c η ^ n = 0`，故 `err_n = 0 * err_0 = 0`，
   与 `err_n ≠ 0` 矛盾。

**前件**：`Corrects`、`n ≥ 1`、`err_n ≠ 0`、`err_0 ≠ 0`。
**⚠ 前件自查**：`err_n ≠ 0` 是**结论层**的负向断言，但结论是 `c η ≠ 0`——
这是**标量因子**的断言，与「误差非零」**不同层次**（同一误差非零可由
「`c ≠ 0` 且 `err_0 ≠ 0`」或「`c = 0` 且 `err_0` 无穷」等组合产生，
故**必须**经环 1 的等式把 `err_n` 因式分解才能得到 `c ≠ 0`）。
`err_0 ≠ 0` **必须**保留：若 `err_0 = 0`，则 `c` 可以是任何值而 `err_n` 恒为 0。 -/
theorem chain_c_ne_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) {n : ℕ} (hn : 0 < n)
    (herr : errA A x' (WiringConvergence.iterMap A φ η x' n θ) ≠ 0)
    (_h0 : errA A x' θ ≠ 0) : c η ≠ 0 := by
  intro hc
  apply herr
  rw [chain_geom_decay A φ η x' θ h n, hc,
    zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul]

/-- **【链环 3 的 `η` 层形态】非零误差 ⟹ `η ≠ 1`。**

由**环 3**（`c η ≠ 0`）与 `OptimalEta.c_eq_zero_iff`（`c η = 0 ↔ η = 1`）合成。

**这是「`η = 1` 的**必要性**」的精确形式**：只要误差还可观测到（非零）、
且初值不是零（有东西可降），那么步长**必不**等于 `1`——
等价地，`η = 1` 是**唯一**使误差**在任何有限 `n ≥ 1` 步后归零**的步长。 -/
theorem chain_eta_ne_one (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) {n : ℕ} (hn : 0 < n)
    (herr : errA A x' (WiringConvergence.iterMap A φ η x' n θ) ≠ 0)
    (h0 : errA A x' θ ≠ 0) : η ≠ 1 := by
  have hc : c η ≠ 0 := chain_c_ne_zero A φ η x' θ h hn herr h0
  intro hη
  exact hc (by rw [hη, c_one])

/-- **【链环 3′：零点唯一性的完整双条件】**

$$\Bigl(\exists n \ge 1,\ \mathrm{err}_n(\eta) = 0\Bigr)
   \;\Longleftrightarrow\; \eta = 1,
\qquad\text{（在 } \mathrm{Corrects} \text{ 下，} \mathrm{err}_0 \ne 0 \text{）}$$

**这是环 2 与环 3 的**合成**，且**不是**任一环单独的推论**：
- `⟸`：环 2（`η = 1` ⟹ 取 `n = 1` 即 `err_1 = 0`）；
- `⟹`：环 3 的逆否（若某 `n ≥ 1` 使 `err_n = 0`，则 `η ≠ 1` 会导致 `err_n ≠ 0`——需先证 `η ≠ 1` 时 `err_n ≠ 0`）。

**⚠ 特别注意 `⟹` 方向需要**额外**的方向性引理（`η ≠ 1` ⟹ `err_n ≠ 0`）**：
那是环 2 与环 1 的另一组合（`c η > 0`、`err_0 ≠ 0` ⟹ `c η ^ n * err_0 ≠ 0`），
**单独任一环都给不出**。这正是「链」而非「合取」的体现。 -/
theorem chain_zero_iff_eta_one (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) (h0 : errA A x' θ ≠ 0) (η : ℝ) :
    (∃ n : ℕ, 0 < n ∧ errA A x' (WiringConvergence.iterMap A φ η x' n θ) = 0)
      ↔ η = 1 := by
  constructor
  · rintro ⟨n, hn, hz⟩
    by_contra hne
    -- `η ≠ 1` ⟹ `c η > 0` ⟹ `c η ^ n > 0` ⟹ `err_n ≠ 0`（与 `hz` 矛盾）
    have hp : 0 < c η := eta_ne_one_pos hne
    have hpn : 0 < c η ^ n := pow_pos hp n
    have h0pos : 0 < errA A x' θ := lt_of_le_of_ne (errA_nonneg A x' θ) (Ne.symm h0)
    have hpos : 0 < errA A x' (WiringConvergence.iterMap A φ η x' n θ) := by
      rw [chain_geom_decay A φ η x' θ h n]
      exact mul_pos hpn h0pos
    linarith
  · intro hη
    exact ⟨1, Nat.one_pos, by rw [hη]; exact chain_eta_one_zero A φ x' θ h Nat.one_pos⟩

/-! ===========================================================================
    §4  **【链环 4】误差关于步数 `n` 单调不增（及严格下降）**
    =========================================================================== -/

/-- **【链环 4：单调不增】`c η ≤ 1` 时，`err_n` 关于 `n` 单调不增。**

$$\bigl(c(\eta) \le 1\bigr) \;\Longrightarrow\; \bigl(m \le n \;\Rightarrow\;
  \mathrm{err}_n \le \mathrm{err}_m\bigr).$$

**证明**（用**环 1** + `pow_le_pow_of_le_one`）：
`err_n = c^n · err_0 ≤ c^m · err_0 = err_m`，因 `c^n ≤ c^m`（`0 ≤ c ≤ 1`、`m ≤ n`）
且 `err_0 ≥ 0`。

**前件**：`Corrects`、`c η ≤ 1`（⟺ `η ∈ [0,2]`）、`m ≤ n`。
**不含**结论：`c ≤ 1` 只约束**单步因子**，不说 `err` 序列单调；
单调性需 `pow_right_anti₀` 的**幂**单调性与 `err_0 ≥ 0`。 -/
theorem chain_mono_in_n (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (hc : c η ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    errA A x' (WiringConvergence.iterMap A φ η x' n θ)
      ≤ errA A x' (WiringConvergence.iterMap A φ η x' m θ) := by
  rw [chain_geom_decay A φ η x' θ h n, chain_geom_decay A φ η x' θ h m]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (c_nonneg η) hc hmn) (errA_nonneg A x' θ)

/-- **【链环 4′：严格单调下降】**

若 `0 < c η < 1`、`err_0 > 0` 且 `m < n`，则

$$\mathrm{err}_n \;<\; \mathrm{err}_m.$$

**这是本文件的**新**结论**（`OptimalEta.err_mono_in_n` 只给 `≤`）：
在**收缩窗内部**（`0 < c < 1` ⟺ `η ∈ (0,1) ∪ (1,2)`）且初值非零时，
每一步都**严格**改善，不存在「卡住不动」的情形。

**证明**（用**环 1** + `pow_right_strictAnti₀`）：
`c^n < c^m`（`0 < c < 1`、`m < n`），乘以正数 `err_0`。

**前件**：`Corrects`、`0 < c η`、`c η < 1`、`err_0 > 0`、`m < n`。
**不含**结论：`m < n` 只说「步数不同」，不排除「误差持平」；
严格性**必须**由 `c^n < c^m`（`pow_right_strictAnti₀`）与 `err_0 > 0` 推出。 -/
theorem chain_strict_mono_in_n (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hpos : 0 < c η) (hlt : c η < 1)
    (h0 : 0 < errA A x' θ) {m n : ℕ} (hmn : m < n) :
    errA A x' (WiringConvergence.iterMap A φ η x' n θ)
      < errA A x' (WiringConvergence.iterMap A φ η x' m θ) := by
  rw [chain_geom_decay A φ η x' θ h n, chain_geom_decay A φ η x' θ h m]
  have hpow : c η ^ n < c η ^ m := (pow_right_strictAnti₀ hpos hlt) hmn
  exact mul_lt_mul_of_pos_right hpow h0

/-- **【链环 4 的速率读法】** `err_n ≤ c η ^ n * err_0` **取等**：
几何上界不是「估计」，而是**逐字精确**的衰减曲线。

**意义**：这使「收敛速率」成为**可代入的等式**（下游可直接算任意 `n` 的误差），
不需要任何放大步骤。 -/
theorem chain_rate_exact (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (n : ℕ) :
    errA A x' (WiringConvergence.iterMap A φ η x' n θ) = c η ^ n * errA A x' θ
      ∧ errA A x' (WiringConvergence.iterMap A φ η x' n θ) ≤ c η ^ n * errA A x' θ :=
  ⟨chain_geom_decay A φ η x' θ h n, le_of_eq (chain_geom_decay A φ η x' θ h n)⟩

/-! ===========================================================================
    §5  **【主定理】把环 1–4 推成一条定理**
    =========================================================================== -/

/-- **【主定理：最优性推导链】**

设 `Corrects A φ`（残差可达）、`err_0 > 0`（有东西可降）、`c η ≤ 1`（收缩窗闭包）。
则**同时**成立（每一项由**不同**的环推出）：

1. **几何衰减**（环 1）：`∀ n, err_n = c η ^ n * err_0`——精确等式；
2. **零点唯一**（环 2 ⟸ 方向）：`η = 1` ⟹ `∀ n ≥ 1, err_n = 0`；
3. **零点唯一**（环 3′ ⟹ 方向）：`η ≠ 1` ⟹ `∀ n ≥ 1, err_n ≠ 0`；
4. **单调不增**（环 4）：`∀ m ≤ n, err_n ≤ err_m`。

**这是一条**推导链**，不是合取**（逐项说明「谁推出谁」）：

```
环 1（精确等式 err_n = c^n · err_0）
  ├─→ 环 2：η = 1 ⟹ c 1 = 0 ⟹ c^n = 0 ⟹ err_n = 0        （第 2 项）
  ├─→ 环 3：η ≠ 1 ⟹ c η > 0 ⟹ c^n > 0 ⟹ err_n > 0        （第 3 项，环 2 之逆否）
  └─→ 环 4：c ≤ 1 ⟹ c^n ≤ c^m（m ≤ n）⟹ err_n ≤ err_m      （第 4 项）
```

**⚠ 前件自查（每一项都**不被**前件包含）**：
- 第 1 项：`Corrects` 只给「残差可达」，等式需 `err_iterMap` 的归纳；
- 第 2/3 项：`err_0 > 0` 只给「有东西可降」，**不**说「降得到 0」或「降不到 0」；
  这两项**互不蕴含**（一项说 `= 0`，一项说 `≠ 0`），且**都**需环 1 的因式分解；
- 第 4 项：`c ≤ 1` 只约束**单步**因子，单调性需幂的单调 + `err_0 ≥ 0`。
- **没有任何前件**是「合取的某一项结论的弱化形式」：
  前件全在「单步 / 初值」层，结论全在「`n` 步 / 序列」层。

**与 `assembly_no_gain` 的区别**：那里合取的各个约束作用在**不相交**变量集上
（故无新信息）；这里四个环作用在**同一**误差序列上，且**每一项都由环 1 的
同一等式**推出——共享同一「引擎」，因此蕴含关系**有内容**。 -/
theorem optimality_chain (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (h0 : 0 < errA A x' θ) (hc : c η ≤ 1) :
    (∀ n : ℕ, errA A x' (WiringConvergence.iterMap A φ η x' n θ)
        = c η ^ n * errA A x' θ)
    ∧ (η = 1 → ∀ n : ℕ, 0 < n →
        errA A x' (WiringConvergence.iterMap A φ η x' n θ) = 0)
    ∧ (η ≠ 1 → ∀ n : ℕ, 0 < n →
        errA A x' (WiringConvergence.iterMap A φ η x' n θ) ≠ 0)
    ∧ (∀ m n : ℕ, m ≤ n →
        errA A x' (WiringConvergence.iterMap A φ η x' n θ)
          ≤ errA A x' (WiringConvergence.iterMap A φ η x' m θ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 环 1
    intro n
    exact chain_geom_decay A φ η x' θ h n
  · -- 环 2：η = 1（由 hη 改写后引环 2）
    intro hη n hn
    rw [hη]
    exact chain_eta_one_zero A φ x' θ h hn
  · -- 环 3：η ≠ 1 ⟹ err_n ≠ 0（环 2 之逆否，经 c η > 0）
    intro hne n hn
    rw [chain_geom_decay A φ η x' θ h n]
    have hp : 0 < c η := eta_ne_one_pos hne
    exact ne_of_gt (mul_pos (pow_pos hp n) h0)
  · -- 环 4
    intro m n hmn
    exact chain_mono_in_n A φ η x' θ h hc hmn

/-- **【主定理（加强版）：`η = 1` 是唯一使误差归零的步长，且误差沿步数严格下降】**

在 `Corrects`、`err_0 > 0`、`0 < c η < 1`（收缩窗**内部**）下：

1. **几何衰减**（环 1）：`∀ n, err_n = c η ^ n * err_0`；
2. **零点唯一（双条件）**（环 2 + 环 3′）：
   `(∃ n ≥ 1, err_n = 0) ↔ η = 1`；
3. **严格下降**（环 4′）：`∀ m < n, err_n < err_m`。

**这是对 `optimality_chain` 的**加强**：把第 2–4 项从「条件式 / 非严格」
升级为「双条件 / 严格」。`c η < 1` 与 `0 < c η` 使环 4′ 可用
（`η ∈ (0,1) ∪ (1,2)`）；`c η = 0`（即 `η = 1`）的情形由环 2 覆盖，两者互补。

**⚠ 前件自查**：`0 < c η` **排除** `η = 1`（否则 `c = 0`），故第 2 项在此前件下
**结论为「不存在 `n ≥ 1` 使 `err_n = 0`」**——这是**真正的信息**
（「`η ≠ 1` 时误差永不归零」），**不是**前件的重述（前件只说单步因子 `c` 非零且小于 1，
不说 `n` 步后仍非零；需环 1 的等式与 `pow_pos`）。 -/
theorem optimality_chain_full (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (h0 : 0 < errA A x' θ) (hcpos : 0 < c η)
    (hclt : c η < 1) :
    (∀ n : ℕ, errA A x' (WiringConvergence.iterMap A φ η x' n θ)
        = c η ^ n * errA A x' θ)
    ∧ ((∃ n : ℕ, 0 < n ∧
          errA A x' (WiringConvergence.iterMap A φ η x' n θ) = 0) ↔ η = 1)
    ∧ (∀ m n : ℕ, m < n →
        errA A x' (WiringConvergence.iterMap A φ η x' n θ)
          < errA A x' (WiringConvergence.iterMap A φ η x' m θ)) := by
  have hne : errA A x' θ ≠ 0 := ne_of_gt h0
  refine ⟨chain_geom_decay A φ η x' θ h, ?_, ?_⟩
  · exact chain_zero_iff_eta_one A φ x' θ h hne η
  · intro m n hmn
    exact chain_strict_mono_in_n A φ η x' θ h hcpos hclt h0 hmn

/-! ===========================================================================
    §6  **具体数值实例：链在 ℝ 上逐环可复核**
    =========================================================================== -/

section Concrete

/-- **实例：`A = id`、`φ = id` 时 `Corrects` 成立**（`A (φ r) = r`）。

**意义**：这保证下面的数值实例**不是空集**——链有真实载体。 -/
theorem corrects_id_real : BoundWriteBack.Corrects
    (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
  intro r
  rfl

/-- **实例（`η = 1/2`）**：`c (1/2) = 1/2`，故误差按 `2^{-n}` 精确衰减，
且**永不**归零（`η ≠ 1`）。

在 `x' = 3`、`θ = 1`（故 `err_0 = |1 - 3| = 2`）下：

- 环 1：`err_n = (1/2)^n * 2`；
- 环 3′：`¬ ∃ n ≥ 1, err_n = 0`（因 `1/2 ≠ 1`）；
- 环 4′：`n ↦ err_n` **严格**递减。

**这是「链」的最直接读法**：单步因子 `1/2` 经 `n` 次方 ⟹ 几何衰减 ⟹
永不归零 ⟹ 故 `η = 1/2` **不是**最优步长（最优是 `η = 1`）。 -/
theorem concrete_half_not_optimal :
    c (1 / 2) = 1 / 2
      ∧ (∀ n : ℕ, errA (ContinuousLinearMap.id ℝ ℝ)
            (3 : ℝ) (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ ℝ)
              (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1 / 2) (3 : ℝ) n (1 : ℝ))
          = (1 / 2) ^ n * errA (ContinuousLinearMap.id ℝ ℝ) (3 : ℝ) (1 : ℝ))
      ∧ (¬ ∃ n : ℕ, 0 < n ∧ errA (ContinuousLinearMap.id ℝ ℝ) (3 : ℝ)
            (WiringConvergence.iterMap (ContinuousLinearMap.id ℝ ℝ)
              (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1 / 2) (3 : ℝ) n (1 : ℝ)) = 0) := by
  refine ⟨by norm_num [c], ?_, ?_⟩
  · intro n
    have hg := chain_geom_decay (ContinuousLinearMap.id ℝ ℝ)
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1 / 2) (3 : ℝ) (1 : ℝ) corrects_id_real n
    have hc : c (1 / 2) = 1 / 2 := by norm_num [c]
    rw [hc] at hg
    exact hg
  · intro hex
    obtain ⟨n, hn, hz⟩ := hex
    have hiff := chain_zero_iff_eta_one (ContinuousLinearMap.id ℝ ℝ)
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (3 : ℝ) (1 : ℝ) corrects_id_real
      (by norm_num [errA]) (1 / 2)
    exact (by norm_num : (1 / 2 : ℝ) ≠ 1) ((hiff).mp ⟨n, hn, hz⟩)

end Concrete

/-! ===========================================================================
    §7  ⚠ **诚实边界 + 前件自查表 + 反例（明确登记未做项）**
    =========================================================================== -/

/-!
### §7.1 前件自查（**逐条确认无同义反复**）

| 定理 | 前件 | 结论 | 结论是否被前件包含？ |
|---|---|---|---|
| `chain_geom_decay` | `Corrects`、`n` | `err_n = c^n * err_0` | ❌ 否（承 `err_iterMap` 的归纳）|
| `chain_eta_one_zero` | `Corrects`、`n ≥ 1` | `err_n(1) = 0` | ❌ 否（需 `c 1 = 0`、`0^n = 0`）|
| `chain_c_ne_zero` | `Corrects`、`n ≥ 1`、`err_n ≠ 0`、`err_0 ≠ 0` | `c η ≠ 0` | ⚠ **需解释**（见下）|
| `chain_eta_ne_one` | 同上 | `η ≠ 1` | ❌ 否（需 `c_eq_zero_iff`）|
| `chain_zero_iff_eta_one` | `Corrects`、`err_0 ≠ 0` | `(∃ n≥1, err_n = 0) ↔ η = 1` | ❌ 否（`⟹` 需 `pow_pos`，`⟸` 需环 2）|
| `chain_mono_in_n` | `Corrects`、`c ≤ 1`、`m ≤ n` | `err_n ≤ err_m` | ❌ 否（需幂单调 + `err_0 ≥ 0`）|
| `chain_strict_mono_in_n` | `Corrects`、`0 < c < 1`、`err_0 > 0`、`m < n` | `err_n < err_m` | ❌ 否（需 `pow_right_strictAnti₀`）|
| `optimality_chain` | `Corrects`、`err_0 > 0`、`c ≤ 1` | 四项（见 §5）| ❌ 否（每项经不同的环）|
| `optimality_chain_full` | `Corrects`、`err_0 > 0`、`0 < c < 1` | 三项（见 §5）| ❌ 否（同上）|
| `concrete_half_not_optimal` | 无（具体数）| `c = 1/2` ∧ 等式 ∧ 非零 | ❌ 否 |

**⚠ `chain_c_ne_zero` 的自查说明**：前件含 `err_n ≠ 0`（在**误差**层），
结论 `c η ≠ 0`（在**标量因子**层）。这两层**不等价**：
- 若 `c = 0`（`η = 1`），则对**任意** `err_0` 都有 `err_n = 0`（`n ≥ 1`），
  故 `err_n ≠ 0` **为假**——这说明前件**排除了** `c = 0`，看似「平凡」。
- **但**：前件**并不**直接说 `c ≠ 0`。前件是「某个**乘积**非零」，
  结论是「某个**因子**非零」。从乘积非零得到因子非零**需要**把 `err_n`
  分解为 `c^n * err_0`（环 1 的等式）+ `n ≥ 1`（使 `0^n = 0`）。
  **没有环 1**，这条推理**不成立**（误差可来自不可消的 `η(A φ r - r)` 项，
  此时 `err_n ≠ 0` 与 `c η = 0` **可以并存**——见 §7.3 登记项 1）。
  **⟹ 这不是同义反复，而是环 1 的**应用**。**

### §7.2 环 4 的 `c ≤ 1` 是**真**前件（反例）

`c η = |1 - η| ≤ 1` ⟺ `η ∈ [0,2]`。取 `η = -1`：`c(-1) = 2`，则
`err_n = 2^n · err_0` **发散**，单调性为假（`n` 增大误差**增大**）。
故 **`c ≤ 1` 不可去**，`chain_mono_in_n` 陈述为真且非空。

### §7.3 未做项（明确登记，**非**删除项；本文件**无**任何 `sorry`）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | `Corrects` **失效**时（`¬ Corrects`）的链 | 此时 `err_n = c^n err_0 + Σ 不可消项`（`BoundWriteBack §5.3` 的反例 `A = 0` 已证 `no_reduction_without_corrects`），环 1 **为假**，整条链断裂；正确的最优 `η < 1` 需一般非线性控制理论，超本文件范围 |
| 2 | **噪声**下的链（期望 / 方差衰减）| 本文件承的是确定性框架（`err_eq_c_pow` 是确定性等式）；概率版需测度结构（`WiringConvergence §8.3` 已登记同项）|
| 3 | **变步长** `η_k` 序列的链（`err_n = ∏_{k<n} c(η_k) · err_0`）| 「最优**常数**步长」问题本文件已闭合（环 1–4 + 主定理）；变步长是**另一问题**（最优控制 / 动态规划），需 `∏` 的收敛理论，未展开 |
| 4 | 世界模型 `WorldModel` 具体实例上的链 | 承 `WiringConvergence §8.3`：`endToEnd` 与 `iterMap` 残差语义不同，需具体实例对齐；本文件只在 §6 给出 `A = id`、`φ = id` 的 `ℝ` 实例（`Corrects` 已证，链非空）|
| 5 | 「`Corrects` 但 `err_0 = 0`」的零点唯一性 | 此时 `err_n = c^n · 0 = 0` 对**一切** `η` 成立，故 `(∃ n≥1, err_n = 0) ↔ η = 1` 的 `⟹` 方向**为假**。本文件因此在 `chain_zero_iff_eta_one` / `optimality_chain` / `optimality_chain_full` 中**显式**取 `err_0 ≠ 0` / `0 < err_0`，**不是**遗漏 |

### §7.4 定理清单（与 §5 的陈述逐条对应；`grep ^theorem` 可核）

`chain_geom_decay`、`chain_eta_one_zero`、`chain_eta_one_zero_any_init`、
`chain_c_ne_zero`、`chain_eta_ne_one`、`chain_zero_iff_eta_one`、
`chain_mono_in_n`、`chain_strict_mono_in_n`、`chain_rate_exact`、
`optimality_chain`、`optimality_chain_full`、
`corrects_id_real`、`concrete_half_not_optimal`。

**⚠ 全部已证出；零 `sorry` / `admit` / `axiom`。**
-/

end OptimalityChain

end FateV2.Loop
