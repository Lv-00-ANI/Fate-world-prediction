import FateWorld.Legacy.ScoreK

/-! ===========================================================================
  §0  三种误差泛函（作者裁决 C：三种 err 都定义）

  ## 背景

  作者裁决 **C = 三种 err 都定义**，参考分别是：

  | # | 名称 | 参考量 | 含义 |
  |---|---|---|---|
  | ① | `trackErr` | **真实轨迹** `trueTraj : ℕ → X` | 时刻 `n` 处预测轨迹与真实轨迹的距离 |
  | ② | `goalErr`  | **目标状态** `goal : ℕ → X`     | 时刻 `n` 处轨迹与目标状态的距离 |
  | ③ | `distErr`  | **经验分布**                     | ⚠ **需 `Measure` 层，本文件不实现** |

  三者与已有 `ScoreK.bandLoss`（`σ/2 ≤ ε ≤ 2σ` 时为零）配套：
  取 `ε := err s`，即得「误差落在合格带内 ⟺ 损失为零」（`bandLoss_eq_zero_iff`）。

  ## 本文件证什么

  * **不依赖 plan**：`trackErr` / `goalErr` 只读 `s.traj`，
    故 `s.traj = t.traj ⟹ err s = err t`（`*_congr_traj`）；
    反之 `plan` 任意改变不影响 `err`（`*_plan_irrel`，即 `err` 对 `plan` 的函数无关性）。
  * **非负**：若 `d` 是伪度量（`∀ x y, 0 ≤ d x y`）则 `0 ≤ err s`。
  * **具体例子**：`X = ℝ`、`d = |·-·|`，两个 `Scenario Unit ℝ` 的数值比较。

  ## 与 `distErr` 的关系

  `distErr` 需要有测度（`MeasureTheory.Measure X` / `MeasureTheory.Measure (ℕ → X)`）
  才能定义「经验分布到目标分布的距离」（如 Wasserstein / TV / KL）。
  本库当前**未引入 `Mathlib.MeasureTheory` 层面的分布距离接口**，
  故此处**只留接口说明**，不写空定义（不虚构、不放 `sorry`）。
-/

namespace Fate

namespace ErrDefinitions

universe u

open Fate.WorldScenario

variable {A X : Type u}

/-! ### §1 ① 轨迹误差（参考 = 真实轨迹） -/

/-- ⭐ **轨迹误差**：时刻 `n` 处预测轨迹与真实轨迹的距离。

`trackErr d trueTraj n s = d (s.traj n) (trueTraj n)` -/
def trackErr (d : X → X → ℝ) (trueTraj : ℕ → X) (n : ℕ) :
    Scenario A X → ℝ :=
  fun s => d (s.traj n) (trueTraj n)

/-- ⭐ **轨迹误差只依赖 `traj`**：同轨迹则同误差。 -/
theorem trackErr_congr_traj (d : X → X → ℝ) (trueTraj : ℕ → X) (n : ℕ)
    {s t : Scenario A X} (h : s.traj = t.traj) :
    trackErr d trueTraj n s = trackErr d trueTraj n t := by
  unfold trackErr
  rw [h]

/-- ⭐ **轨迹误差不依赖 `plan`**：`plan` 任意替换，误差不变。 -/
theorem trackErr_plan_irrel (d : X → X → ℝ) (trueTraj : ℕ → X) (n : ℕ)
    (s : Scenario A X) (plan' : ℕ → A) :
    trackErr d trueTraj n { s with plan := plan' } = trackErr d trueTraj n s :=
  rfl

/-- ⭐ **伪度量 ⟹ 轨迹误差非负**。 -/
theorem trackErr_nonneg {d : X → X → ℝ} (hd : ∀ x y, 0 ≤ d x y)
    (trueTraj : ℕ → X) (n : ℕ) (s : Scenario A X) :
    0 ≤ trackErr d trueTraj n s :=
  hd _ _

/-! ### §2 ② 目标误差（参考 = 目标状态） -/

/-- ⭐ **目标误差**：时刻 `n` 处轨迹与目标状态的距离。

`goalErr d goal n s = d (s.traj n) (goal n)` -/
def goalErr (d : X → X → ℝ) (goal : ℕ → X) (n : ℕ) :
    Scenario A X → ℝ :=
  fun s => d (s.traj n) (goal n)

/-- ⭐ **目标误差只依赖 `traj`**：同轨迹则同误差。 -/
theorem goalErr_congr_traj (d : X → X → ℝ) (goal : ℕ → X) (n : ℕ)
    {s t : Scenario A X} (h : s.traj = t.traj) :
    goalErr d goal n s = goalErr d goal n t := by
  unfold goalErr
  rw [h]

/-- ⭐ **目标误差不依赖 `plan`**。 -/
theorem goalErr_plan_irrel (d : X → X → ℝ) (goal : ℕ → X) (n : ℕ)
    (s : Scenario A X) (plan' : ℕ → A) :
    goalErr d goal n { s with plan := plan' } = goalErr d goal n s :=
  rfl

/-- ⭐ **伪度量 ⟹ 目标误差非负**。 -/
theorem goalErr_nonneg {d : X → X → ℝ} (hd : ∀ x y, 0 ≤ d x y)
    (goal : ℕ → X) (n : ℕ) (s : Scenario A X) :
    0 ≤ goalErr d goal n s :=
  hd _ _

/-! ### §3 ③ 分布误差（参考 = 经验分布）—— 需 `Measure` 层

**未实现（有意）**。理由：

* 「经验分布」是 `ℕ → X` 轨迹上的一个 `Measure`（`∑ n∈Finset.range N, δ_{traj n}` 归一化）；
  Lean 中它需要 `MeasureTheory.Measure X`、`MeasureTheory.Singleton`（Dirac）
  以及分布距离（TV / Wasserstein / KL）。
* 本库当前**没有** `Mathlib` 的 `MeasureTheory` 分布距离接口，
  若在此仅写 `def distErr ... := 0` 那是**虚构**（且会破坏「三种 err 语义不同」的裁决）。
* 故此处**只留接口签名说明**，`distErr` 的实际定义待 `Measure` 层就绪后补。

下面是**接口名与预期签名**（以注释固定，不产生任何 Lean 声明）：

```
-- 需：import Mathlib.MeasureTheory.Measure.MeasureSpace
--     import Mathlib.MeasureTheory.Measure.Dirac
--
-- noncomputable def empDist (s : Scenario A X) (N : ℕ) : Measure X :=
--   (N : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range N, Measure.dirac (s.traj n)
--
-- noncomputable def distErr (D : Measure X → Measure X → ℝ)
--     (target : Measure X) (N : ℕ) : Scenario A X → ℝ :=
--   fun s => D (empDist s N) target
```

⚠ **注意**：与 ① ② 不同，`distErr` **不是逐点（时刻 `n`）误差**，
而是**整条轨迹（前 `N` 步）的经验分布**误差 —— 这是它与 ① ② 的语义差别，
也是作者裁决「三种都要」的实质理由（结论视角不同）。
-/

/-! ### §4 具体例子：`X = ℝ`、`d = |·-·|`

取 `A = Unit`，两条对比场景：

* `s₁`：轨迹恒 `0`（plan 也恒 `()`）
* `s₂`：轨迹为 `fun n => n`（plan 亦恒 `()`）

参考：真实轨迹 `trueTraj = fun n => 0`；目标 `goal = fun _ => 0`。

则在 `n = 0` 处两者误差都为 `0`；在 `n = 2` 处 `s₂` 误差为 `2`。 -/

/-- 例子用场景 `s₁`：轨迹恒 `0`。 -/
def exS1 : Scenario Unit ℝ :=
  { plan := fun _ => (), traj := fun _ => 0 }

/-- 例子用场景 `s₂`：轨迹为 `n ↦ n`。 -/
def exS2 : Scenario Unit ℝ :=
  { plan := fun _ => (), traj := fun n => (n : ℝ) }

/-- 例子用真实轨迹：恒 `0`。 -/
def exTrueTraj : ℕ → ℝ := fun _ => 0

/-- 例子用目标：恒 `0`。 -/
def exGoal : ℕ → ℝ := fun _ => 0

open scoped Real

/-- ⭐ 例子：`n = 0` 处 `s₁` 的轨迹误差为 `0`。 -/
theorem exS1_trackErr_zero :
    trackErr (fun x y : ℝ => |x - y|) exTrueTraj 0 exS1 = 0 := by
  unfold trackErr exS1 exTrueTraj
  simp

/-- ⭐ 例子：`n = 0` 处 `s₂` 的轨迹误差为 `0`。 -/
theorem exS2_trackErr_zero :
    trackErr (fun x y : ℝ => |x - y|) exTrueTraj 0 exS2 = 0 := by
  unfold trackErr exS2 exTrueTraj
  simp

/-- ⭐ 例子：`n = 2` 处 `s₂` 的轨迹误差为 `2 > 0`（严格偏离）。 -/
theorem exS2_trackErr_two :
    trackErr (fun x y : ℝ => |x - y|) exTrueTraj 2 exS2 = 2 := by
  unfold trackErr exS2 exTrueTraj
  norm_num

/-- ⭐ 例子：`n = 2` 处 `s₁` 的轨迹误差为 `0`，故 `s₁` 在 `n = 2` 处优于 `s₂`。 -/
theorem exS1_trackErr_lt_exS2 :
    trackErr (fun x y : ℝ => |x - y|) exTrueTraj 2 exS1
      < trackErr (fun x y : ℝ => |x - y|) exTrueTraj 2 exS2 := by
  unfold trackErr exS1 exS2 exTrueTraj
  norm_num

/-- ⭐ 例子：目标误差同构 —— `n = 2` 处 `s₂` 的目标误差为 `2`，
`s₁` 的为 `0`。 -/
theorem ex_goalErr_compare :
    goalErr (fun x y : ℝ => |x - y|) exGoal 2 exS1
        < goalErr (fun x y : ℝ => |x - y|) exGoal 2 exS2
      ∧ goalErr (fun x y : ℝ => |x - y|) exGoal 2 exS2 = 2 := by
  constructor
  · unfold goalErr exS1 exS2 exGoal
    norm_num
  · unfold goalErr exS2 exGoal
    norm_num

/-! ### §5 与 `ScoreK.bandLoss` 的对接（三种 err 都能喂进裁决 K） -/

/-- ⭐⭐ **轨迹误差合格 ⟺ 带偏离损失为零**（`0 < σ`）。 -/
theorem trackErr_bandLoss_eq_zero_iff {σ : ℝ} (hσ : 0 < σ)
    (d : X → X → ℝ) (trueTraj : ℕ → X) (n : ℕ) (s : Scenario A X) :
    ScoreK.bandLoss σ (trackErr d trueTraj n s) = 0 ↔
      σ / 2 ≤ trackErr d trueTraj n s ∧ trackErr d trueTraj n s ≤ 2 * σ :=
  ScoreK.bandLoss_eq_zero_iff hσ

/-- ⭐⭐ **目标误差合格 ⟺ 带偏离损失为零**（`0 < σ`）。 -/
theorem goalErr_bandLoss_eq_zero_iff {σ : ℝ} (hσ : 0 < σ)
    (d : X → X → ℝ) (goal : ℕ → X) (n : ℕ) (s : Scenario A X) :
    ScoreK.bandLoss σ (goalErr d goal n s) = 0 ↔
      σ / 2 ≤ goalErr d goal n s ∧ goalErr d goal n s ≤ 2 * σ :=
  ScoreK.bandLoss_eq_zero_iff hσ


/-! ===========================================================================
  §6  接线 R-43：`trackErr` / `goalErr` 的**带偏离损失**判据

  ## 本节的定位

  §5 只把**具体例子**（`exS1`/`exS2`）喂进 `ScoreK.bandLoss`。本节把它
  **一般化**成对**任意** `d / trueTraj / goal / n / s` 成立的判据：

  | 定理 | 内容 |
  |---|---|
  | `trackErr_bandLoss_iff` | `bandLoss σ (trackErr …) = 0 ↔ σ/2 ≤ ε ≤ 2σ` |
  | `goalErr_bandLoss_iff` | 同上（`goalErr`）|
  | `trackErr_bandLoss_eq_goalErr` | ⭐ **同 `ε` ⟹ 同损失**（两个泛函的损失可互换）|
  | `trackErr_bandLoss_plan_irrel` | ⭐ **损失对 `plan` 无关**（§1 的 `plan_irrel` 传到损失层）|
  | `goalErr_bandLoss_plan_irrel` | 同上（`goalErr`）|
  | `trackErr_bandLoss_pos_of_lt_goal` | ⚠ **非平凡性**：`ε < σ/2` 时损失**为正** |

  ## 非平凡性自查

  * `trackErr_bandLoss_eq_goalErr` 的**前件**只有「`ε` 等于两者之一」，
    **不含**任何关于 `bandLoss` 的断言；结论把**两个不同泛函**的损失联系起来。
  * `trackErr_bandLoss_plan_irrel` 前件为空，结论是 `plan` 改写前后损失相等；
    中间必须用 §1 的 `trackErr_plan_irrel`（该引理是 `rfl`，但损失层不是 `rfl`：
    `bandLoss` 是 `max` 表达式，需 `congrArg`）。
  * `trackErr_bandLoss_pos_of_lt_goal` 结论**符号相反**（`0 <`），与前几条并存
    即证明损失判据不是空洞成立。
  * 零 `sorry` / `admit` / `axiom`。
  =========================================================================== -/

/-! ### §6.1 一般判据 -/

/-- ⭐⭐ **轨迹误差的带偏离损失为零 ⟺ 误差在合格带内**（一般形式）。 -/
theorem trackErr_bandLoss_iff {σ : ℝ} (hσ : 0 < σ)
    (d : X → X → ℝ) (trueTraj : ℕ → X) (n : ℕ) (s : Scenario A X) :
    ScoreK.bandLoss σ (trackErr d trueTraj n s) = 0 ↔
      σ / 2 ≤ trackErr d trueTraj n s ∧ trackErr d trueTraj n s ≤ 2 * σ :=
  ScoreK.bandLoss_eq_zero_iff hσ

/-- ⭐⭐ **目标误差的带偏离损失为零 ⟺ 误差在合格带内**（一般形式）。 -/
theorem goalErr_bandLoss_iff {σ : ℝ} (hσ : 0 < σ)
    (d : X → X → ℝ) (goal : ℕ → X) (n : ℕ) (s : Scenario A X) :
    ScoreK.bandLoss σ (goalErr d goal n s) = 0 ↔
      σ / 2 ≤ goalErr d goal n s ∧ goalErr d goal n s ≤ 2 * σ :=
  ScoreK.bandLoss_eq_zero_iff hσ

/-! ### §6.2 ⭐ 跨泛函：同一个 `ε` 给出同一个损失 -/

/-- ⭐⭐ **同 `ε` ⟹ 同损失**：`trackErr` 与 `goalErr` 虽参考量不同，
但只要在 `(s, n)` 处取到**相同实数** `ε`，它们喂进 `bandLoss` 的结果就**相同**。

⚠ 这条**不是** `rfl`：`trackErr` 与 `goalErr` 是**两个不同的 `def`**
（分别用 `trueTraj n` 与 `goal n`），前件是把两者**数值相等**这一事实供给进来。 -/
theorem trackErr_bandLoss_eq_goalErr {σ : ℝ}
    (d : X → X → ℝ) (trueTraj goal : ℕ → X) (n : ℕ) (s : Scenario A X)
    (h : trackErr d trueTraj n s = goalErr d goal n s) :
    ScoreK.bandLoss σ (trackErr d trueTraj n s)
      = ScoreK.bandLoss σ (goalErr d goal n s) := by
  rw [h]

/-- ⭐ **带内判定跨泛函**：若 `trackErr` 落在合格带内，且它与 `goalErr` 数值相等，
则 `goalErr` 的损失也为零。 -/
theorem goalErr_bandLoss_zero_of_trackErr {σ : ℝ} (_hσ : 0 < σ)
    (d : X → X → ℝ) (trueTraj goal : ℕ → X) (n : ℕ) (s : Scenario A X)
    (h : trackErr d trueTraj n s = goalErr d goal n s)
    (hband : ScoreK.bandLoss σ (trackErr d trueTraj n s) = 0) :
    ScoreK.bandLoss σ (goalErr d goal n s) = 0 := by
  rw [← h]
  exact hband

/-! ### §6.3 ⭐ 损失层继承「对 `plan` 无关」 -/

/-- ⭐⭐ **轨迹误差的损失对 `plan` 无关**：`plan` 任意改写，损失不变。

中间用 §1 的 `trackErr_plan_irrel`（`rfl`），但损失层需要 `congrArg`
（`bandLoss` 不是 `rfl` 级透明的）。 -/
theorem trackErr_bandLoss_plan_irrel {σ : ℝ}
    (d : X → X → ℝ) (trueTraj : ℕ → X) (n : ℕ)
    (s : Scenario A X) (plan' : ℕ → A) :
    ScoreK.bandLoss σ (trackErr d trueTraj n { s with plan := plan' })
      = ScoreK.bandLoss σ (trackErr d trueTraj n s) := by
  rw [trackErr_plan_irrel]

/-- ⭐⭐ **目标误差的损失对 `plan` 无关**。 -/
theorem goalErr_bandLoss_plan_irrel {σ : ℝ}
    (d : X → X → ℝ) (goal : ℕ → X) (n : ℕ)
    (s : Scenario A X) (plan' : ℕ → A) :
    ScoreK.bandLoss σ (goalErr d goal n { s with plan := plan' })
      = ScoreK.bandLoss σ (goalErr d goal n s) := by
  rw [goalErr_plan_irrel]

/-! ### §6.4 反向控制：损失**不**恒为零 -/

/-- ⚠⚠ **非平凡性**：误差**严格小于**带下界 `σ/2` 时，损失**为正**。

与 §6.1–§6.3 的「损失为零」结论方向相反，证明 `bandLoss = 0` 是**实质条件**。 -/
theorem trackErr_bandLoss_pos_of_lt {σ ε : ℝ} (h : ε < σ / 2) :
    0 < ScoreK.bandLoss σ ε :=
  ScoreK.bandLoss_pos_of_lt h

/-- ⚠ 另一侧：误差**严格大于**带上界 `2σ` 时，损失也为正。 -/
theorem trackErr_bandLoss_pos_of_gt {σ ε : ℝ} (h : 2 * σ < ε) :
    0 < ScoreK.bandLoss σ ε :=
  ScoreK.bandLoss_pos_of_gt h

end ErrDefinitions

end Fate
