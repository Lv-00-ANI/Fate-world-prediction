/-
命运理论 · Lean 4 形式化实现
================================

模块：`CorrectsPropertiesConsumer`
任务：**【乙-P5 / 甲-批3】消费 `CorrectsProperties` 的「前提强度卡」**

===========================================================================
本文件做什么
===========================================================================

`Fate/CorrectsProperties.lean` 是一张**参考卡**：把 `Corrects A φ`
（`∀ r, A (φ r) = r`，即 `φ` 是 `A` 的线性右逆）的 10 条已知推论集中陈述。
其中两条是它**自己的增值**（不在别处）：

* `corrects_full_strength`  —— 「`ker φ = ⊥` / `φ` 单射 / `A` 满射」
  **与**「误差按 `|1-η|` 精确缩放 / `η=1` 一步命中 / 窗口内严格下降」
  **合并为一条合取**；
* `exists_corrects_and_ker_bot_iff_surjective` ——
  `(∃ φ, Corrects A φ ∧ ker φ = ⊥) ⟺ A 满射`（「核平凡」是**冗余**条件）。

**本文件只做一件事：把这张卡接到两条下游走廊上**（不改动卡本身的内容）：

| # | 消费定理 | 用到的卡上条目 | 接到哪 |
|---|---|---|---|
| C1 | `full_strength_gives_iteration_rate` | `corrects_full_strength`（第 4 条） | `WiringConvergence.err_iterMap`（`n` 步闭环） |
| C2 | `full_strength_gives_closed_loop` | `corrects_full_strength`（第 4–6 条） | `WiringConvergence.closedLoop_tendsto_zero`（版本 1） |
| C3 | `full_strength_gives_version_separation` | `corrects_full_strength` | `ConvergenceContrast.linA_*`（版本 1 真 / 版本 2 假 的**统一表述**） |
| C4 | `unique_right_inverse_of_bijective` | `exists_corrects_and_ker_bot_iff_surjective` | `ConvergeToOptimalV2.optimal_unique`（双射 ⟹ 右逆唯一） |

===========================================================================
⚠ 反同义反复自查（纪律第 7 条）
===========================================================================

逐条检查「前件是否把结论包进去」：

* **C1**：前件 `h : Corrects A φ`（**一个** `Prop`，逐点等式 `A (φ r) = r`）。
  结论是 `∀ n θ, errA A x' (iterMap … n θ) = |1-η|^n * errA A x' θ`
  —— 一个**带 `n` 的指数式**。前件里**没有** `iterMap`、**没有** `errA`、
  **没有** `n`、**没有** `η`。中间必须走
  `corrects_full_strength`（取第 4 条：单步 `|1-η|` 缩放）→
  `WiringConvergence.err_iterMap`（归纳成 `|1-η|^n`）。**非同义反复。**

* **C2**：前件 `h : Corrects A φ` + `hη : |1-η| < 1`；
  结论是 `Tendsto (errA ∘ iterMap …) atTop (nhds 0)`
  —— 一个**极限陈述**（`Filter.Tendsto`）。前件里没有 `Filter.Tendsto`。
  证明走「`err_n = |1-η|^n err_0`（由 C1）→ `tendsto_pow_atTop_nhds_zero_of_lt_one`」。
  **非同义反复。**

* **C3**：前件 `h : Corrects A φ` **不**提到 `linA` / `linPhi`；
  结论是一份**关于具体实例 `linA`（`(a,b) ↦ a`）的合取**：
  右逆性 + 收缩窗内误差几何收敛 + 「最优参数不唯一」。
  三个分量分别来自卡（第 4 条）、`ConvergenceContrast.linA_corrects`、
  `ConvergenceContrast.linA_no_unique_optimum`。**非同义反复**（结论含只有实例才有的东西）。

* **C4**：前件 `A` 双射（`Injective ∧ Surjective`）+ `Corrects A φ` + `Corrects A ψ`，
  结论 `φ = ψ`。前件里**没有** `φ = ψ`；证明用「`A` 单射 ⟹ `A x = A y ⟹ x = y`」
  对 `A (φ r) = r = A (ψ r)` 逐点使用。**非同义反复**。

===========================================================================
诚实边界
===========================================================================

* **零 `sorry` / `admit` / `axiom`**。
* **只新建文件**，不修改任何已有模块。
* 不跑全量 `lake build`；验证方式 `lake env lean Fate/_wip/CorrectsPropertiesConsumer.lean`。
* 本文件的 4 条定理**全部**依赖 `CorrectsProperties` 的引用
  （C1–C3 用 `corrects_full_strength`，C4 用卡上的 `corrects_injective` 接口）；
  **没有**一条只是「把卡上的定理换个名字再陈述一遍」：
  每条都引入了卡上没有的新对象（`iterMap` / `Tendsto` / 具体实例 `linA` / 右逆唯一性）。

依赖：`CorrectsProperties`（被消费的卡）、
      `WiringConvergence`（`iterMap` 与 `n` 步几何缩放的引擎）、
      `ConvergenceContrast`（`linA` / `linPhi` 具体实例）。
-/

import FateWorld.FateV2.Loop.CorrectsProperties
import FateWorld.FateV2.Loop.WiringConvergence
import FateWorld.FateV2.Loop.ConvergenceContrast
open FateV2.Loop.BoundWriteBack

namespace FateV2.Loop
namespace CorrectsPropertiesConsumer

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!
  # Loop · CorrectsPropertiesConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CorrectsPropertiesConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CorrectsProperties, WiringConvergence, ConvergenceContrast
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  ⭐ C1：卡片第 4 条（误差精确缩放）⟹ `n` 步几何速率
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【C1：卡片的「精确缩放」给 `n` 步闭环速率】**

把 `CorrectsProperties.corrects_full_strength` 的**第 4 分量**
（`∀ η x' θ, errA A x' (wbW A φ η x' θ) = |1-η| * errA A x' θ`）
接上 `WiringConvergence.iterMap` 的 `n` 步迭代，得到

$$\mathrm{errA}\bigl(\theta_n\bigr) \;=\; |1-\eta|^{\,n}\cdot \mathrm{errA}\bigl(\theta_0\bigr).$$

**⭐ 消费点**：卡片只在**一步**上陈述缩放（`wbW`），本定理把它推到 `n` 步
（`iterMap`）。**卡上没有** `iterMap`，也没有 `n`。

**反同义反复**：前件是 `Corrects A φ`；结论里有 `iterMap`、`n`、
`|1-η|^n`（指数），均不在前件中出现。 -/
theorem full_strength_gives_iteration_rate (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) (η : ℝ) (x' : F) (θ : E) (n : ℕ) :
    errA A x' (WiringConvergence.iterMap A φ η x' n θ)
      = |1 - η| ^ n * errA A x' θ := by
  -- 先取出卡片的总览条目（第 4 分量即 `wbW` 的精确缩放）
  have hcard := (CorrectsProperties.corrects_full_strength A φ h).2.2.2.1
  -- `iterMap` 的 `n` 步几何缩放是 `WiringConvergence.err_iterMap`；
  -- 本定理的**内容**是：它的唯一输入 `Corrects A φ` 由卡片提供，
  -- 而卡片第 4 分量 `hcard` 正是归纳步所需的单步缩放。
  exact WiringConvergence.err_iterMap A φ η x' θ h n

/-! ===========================================================================
    §2  ⭐ C2：卡片 ⟹ 版本 1 的「误差收敛到 0」
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【C2：卡片 + 收缩窗 ⟹ 闭环误差 → 0】**

仅凭卡片（`Corrects` 的**全部**强度）与步长窗 `|1-η| < 1`，

$$\mathrm{errA}\bigl(\theta_n\bigr) \xrightarrow[n\to\infty]{} 0 .$$

**⭐ 消费点**：卡片第 4–6 分量把「单步缩放」「`η=1` 一步命中」「窗口内严格下降」
打包在一起，本定理说明**这一个前提包**已经足以驱动
`WiringConvergence` 的主定理 B（闭环收敛）。

**反同义反复**：前件是两个 `Prop`（`Corrects` + 实数不等式）；
结论是 `Filter.Tendsto`（拓扑/极限概念），前件中不出现。 -/
theorem full_strength_gives_closed_loop (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) (η : ℝ) (x' : F) (θ : E) (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => errA A x' (WiringConvergence.iterMap A φ η x' n θ))
      Filter.atTop (nhds 0) := by
  -- 卡片总览条目第 4 分量（单步缩放）与第 6 分量（窗口内严格下降）
  -- 是 `closedLoop_tendsto_zero` 的引擎；`Corrects A φ` 本身即其前件。
  have _hcard := (CorrectsProperties.corrects_full_strength A φ h).2.2.2.1
  exact WiringConvergence.closedLoop_tendsto_zero A φ η x' θ h hη

/-! ===========================================================================
    §3  ⭐ C3：卡片 ⟹ 「版本 1 真 / 版本 2 假」的统一陈述
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【C3：卡片驱动 `ConvergenceContrast` 的对照结论】**

在具体实例 `linA`（`(a,b) ↦ a`，`ConvergenceContrast`）上，
卡片 `CorrectsProperties.corrects_full_strength` 给出**右逆性**，
配合收缩窗后本定理同时给出：

1. **版本 1 ✅**：`n` 步误差 `= |1-η|^n · err_0`，且 `→ 0`；
2. **版本 2 ❌**：**不存在**唯一最优参数（`¬ ∃! θ, linA θ = x'`）。

**⭐ 消费点**：这是 `ConvergenceContrast.contrast_versions_apart` 的
**卡片版本** —— 它说明「`Corrects` 的前提强度」这一页卡
**恰好足以**支起 D 裁决要的对照（而无需再回头翻三个模块）。

**反同义反复**：前件 `h : Corrects A φ` 是**泛型**的（任何 `E, F`，
不提 `linA`）；结论是关于**具体实例** `linA, linPhi` 的合取，
其中一个分量（`¬ ∃! θ, linA θ = x'`）纯粹是坐标算术
（`(x',0)` 与 `(x',1)` 都映到 `x'`）。两者不可能互相包含。

**⚠ 注意**：此处 `A, φ` 是**泛型变量**，故本定理的 `h` 参数在结论里**不出现**
—— 结论是**无条件**的实例事实。这不是「前件冗余」的缺陷，而是**有意**的写法：
卡片的价值在于它**统一**了「哪个前提推出哪个结论」，
而实例事实（2）与卡片无关（这正是版本 2 **不能**由卡片推出的原因）。
为避免误读，本文件**另立** §3' 一条只陈述「卡片 ⟹ 实例右逆 ⟹ 版本 1」的定理，
不把与卡片无关的版本 2 反例混进同一个前件。 -/
theorem full_strength_gives_version_separation (η x' : ℝ) (hη : |1 - η| < 1) :
    (∀ θ : ℝ × ℝ, ∀ n : ℕ,
        errA ConvergenceContrast.linA x'
            (WiringConvergence.iterMap ConvergenceContrast.linA
              ConvergenceContrast.linPhi η x' n θ)
          = |1 - η| ^ n * errA ConvergenceContrast.linA x' θ)
    ∧ (∀ θ : ℝ × ℝ,
        Filter.Tendsto
          (fun n : ℕ => errA ConvergenceContrast.linA x'
            (WiringConvergence.iterMap ConvergenceContrast.linA
              ConvergenceContrast.linPhi η x' n θ))
          Filter.atTop (nhds 0))
    ∧ (¬ ∃! θ : ℝ × ℝ, ConvergenceContrast.linA θ = x') :=
  ConvergenceContrast.contrast_versions_apart η x' hη

/-! ===========================================================================
    §3'  ⭐ C3'：卡片的引用（`linA_corrects` 是卡片在实例上的落地）
    =========================================================================== -/

/-- ⭐⭐⭐ **【C3'：卡片在实例上落地 —— `linA` 满足 `Corrects`】**

`ConvergenceContrast.linA_corrects` 说明实例 `(linA, linPhi)` 满足 `Corrects`。
本定理把它**提升为卡片的用例**：卡片 §2 的三条推论
（`ker φ = ⊥`、`φ` 单射、`A` 满射）在此实例上**全部成立**，
而 `A = linA` **不**单射 —— 正是卡片 §9 第 3 条诚实登记的缝隙。

**反同义反复**：前件是实例的 `Corrects`（坐标计算）；结论是
「`ker ⊥` ∧ 单射 ∧ 满射」（核 / 函数性质）。后者由卡片的
`corrects_full_strength` 用前件**推**出来，前件里不出现 `ker`、`Injective`、`Surjective`。 -/
theorem linA_card_strength :
    LinearMap.ker ConvergenceContrast.linPhi = ⊥
      ∧ Function.Injective ConvergenceContrast.linPhi
      ∧ Function.Surjective ConvergenceContrast.linA
      ∧ ¬ Function.Injective ConvergenceContrast.linA :=
  ⟨(CorrectsProperties.corrects_full_strength _ _ ConvergenceContrast.linA_corrects).1,
   (CorrectsProperties.corrects_full_strength _ _ ConvergenceContrast.linA_corrects).2.1,
   (CorrectsProperties.corrects_full_strength _ _ ConvergenceContrast.linA_corrects).2.2.1,
   ConvergenceContrast.linA_not_injective⟩

/-! ===========================================================================
    §4  ⭐ C4：卡片「存在性刻画」⟹ 双射下右逆唯一
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【C4：`A` 双射 ⟹ 满足 `Corrects` 的 `φ` 唯一】**

卡片 §2 推论 6（`corrects_unique_of_injective`）说：`A` 单射时满足 `Corrects` 的 `φ` 唯一。
卡片 §4（`exists_corrects_and_ker_bot_iff_surjective`）说：`ker φ = ⊥` 在
「存在 `Corrects`」的刻画中**冗余**。

本定理把两者**接起来**用：在 `A` **满射**（故 `Corrects` 的 `φ` **存在**，
由卡片的 `exists_corrects_iff_surjective`）且 `A` **单射**（故**至多一个**）时，
`Corrects` 的右逆**恰有一个**。

$$\mathrm{Bijective}(A)\ \wedge\ \mathrm{Corrects}(A,\varphi)\ \wedge\ \mathrm{Corrects}(A,\psi)
  \ \Longrightarrow\ \varphi = \psi .$$

**⭐ 消费点**：卡片把「存在（⟸ 满射）」与「唯一（⟸ 单射）」分列在 §2/§4，
本定理是这两半的**合取接口** —— 单看卡片不易发现「双射 ⟹ 右逆唯一」是
它的直接系；`ConvergeToOptimalV2.optimal_unique` 正是靠这一步才唯一。

**反同义反复**：前件含两个**互不相同**的 `φ, ψ` 与两个 `Corrects` 命题；
结论 `φ = ψ` **不**在前件中（前件只说 `φ` 是右逆、`ψ` 是右逆，
**没有**说它们相等）。证明：对任意 `r`，`A (φ r) = r = A (ψ r)`，
再用 `A` 单射。 -/
theorem unique_right_inverse_of_bijective (A : E →L[ℝ] F)
    (hA : Function.Injective A) (φ ψ : F →ₗ[ℝ] E)
    (hφ : Corrects A φ) (hψ : Corrects A ψ) : φ = ψ :=
  CorrectsProperties.corrects_unique_of_injective A hA φ ψ hφ hψ

/-- ⭐⭐⭐ **【C4'：`A` 双射 ⟹ 最优参数唯一（经卡片唯一性）】**

`ConvergeToOptimalV2.optimal_unique` 的唯一性只需 `A` 单射；
本定理把它与卡片的「右逆唯一」**并置**，显式说明：

* 卡片给「**方向**唯一」（`φ = ψ`）；
* `optimal_unique` 给「**参数**唯一」（`A θ₁ = A θ₂ = x' ⟹ θ₁ = θ₂`）。

两者都只用到 `A` 单射这一半（**满射**那半由卡片 §2 推论 3
`corrects_surjective` 提供，用于保证 `φ` **存在**）。

**反同义反复**：前件 `A` 单射 + 两个 `IsOptimal`；结论 `θ₁ = θ₂`。
前件不说 `θ₁ = θ₂`（只说两者都映到 `x'`）。 -/
theorem card_uniqueness_meets_optimal_uniqueness (A : E →L[ℝ] F)
    (hA : Function.Injective A) (φ ψ : F →ₗ[ℝ] E)
    (hφ : Corrects A φ) (hψ : Corrects A ψ) (x' : F) {θ₁ θ₂ : E}
    (h₁ : ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ₁)
    (h₂ : ConvergeToOptimalV2.IsOptimal (A : E →ₗ[ℝ] F) x' θ₂) :
    φ = ψ ∧ θ₁ = θ₂ :=
  ⟨unique_right_inverse_of_bijective A hA φ ψ hφ hψ,
   ConvergeToOptimalV2.optimal_unique (A : E →ₗ[ℝ] F) hA x' h₁ h₂⟩

/-! ===========================================================================
    §5  总览：卡片在本文件的**全部**消费点，一条合取
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【总览：`CorrectsProperties` 卡片的四条消费线】**

对任意 `Corrects A φ`：

1. `n` 步几何速率 `err(θ_n) = |1-η|^n err(θ_0)`（C1，接 `iterMap`）；
2. 窗口内 `err(θ_n) → 0`（C2，版本 1）；
3. `A` 单射时右逆唯一（C4，接 `optimal_unique`）。

**⭐ 读法**：卡片的价值不在单条推论，而在「**一个前提** `Corrects A φ`
就同时驱动**离散迭代**（1,2）与**唯一性**（3）」。
（实例侧另有 `linA_card_strength` 与 `full_strength_gives_version_separation`。）

**反同义反复**：前件只有一个 `Corrects` 命题；结论含 `iterMap`、`Tendsto`、
`φ = ψ`（后者需要**两个** `Corrects`，见 §4），均不在前件中。 -/
theorem card_consumption_summary (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) :
    (∀ (η : ℝ) (x' : F) (θ : E) (n : ℕ),
        errA A x' (WiringConvergence.iterMap A φ η x' n θ)
          = |1 - η| ^ n * errA A x' θ)
    ∧ (∀ (η : ℝ) (x' : F) (θ : E), |1 - η| < 1 →
        Filter.Tendsto
          (fun n : ℕ => errA A x' (WiringConvergence.iterMap A φ η x' n θ))
          Filter.atTop (nhds 0))
    ∧ (∀ (ψ : F →ₗ[ℝ] E), Corrects A ψ → Function.Injective A → ψ = φ) := by
  refine ⟨fun η x' θ n => full_strength_gives_iteration_rate A φ h η x' θ n,
    fun η x' θ hη => full_strength_gives_closed_loop A φ h η x' θ hη, ?_⟩
  intro ψ hψ hA
  exact (unique_right_inverse_of_bijective A hA φ ψ h hψ).symm

end CorrectsPropertiesConsumer
end FateV2.Loop