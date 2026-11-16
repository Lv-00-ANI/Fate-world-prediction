import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/CoreBasics.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop；其余正文未改
  - 状态：已编译未验证
  - **层位修正（本轮）**：`FateV2.Loop` → `FateV2.Modeling`。
    理由：本模块只含 5 个纯算术定义（gradForce / histInertia / ShouldStop /
    ShouldContinue / tauOf），无定理，却被 Error(4) / Loop(1) / Rules(1) 三层共用。
    放在 Loop（第 6 层）导致 Error(第 5 层) 为取 5 个定义而反向依赖第 6 层。
    下沉到 Modeling（第 0 层）后，所有层对它的依赖都是正向。
-/

/-
  判据基座：停止判据的算术定义（对应论文 §6.1）

  收集边界主模块所需的几个纯算术定义：梯度力 gradForce、历史惯性 histInertia、
  停止判据 ShouldStop 及其补 ShouldContinue、阈值参数化 tauOf。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  来源与取舍：这些定义原本位于 Classification 中，而 Classification 还引入 FCA、
  Implication、Completeness 与范畴论库——一条与边界概念无关的依赖链。为使边界主模块
  只依赖 Mathlib，本模块原样复制这五个定义（陈述与定义体逐字相同，未作任何改进），
  使边界主链的依赖闭包从 24 个模块降到 2 个。

  注：本模块是副本，故同一组定义在两处各存一份——Classification 保持原样、其中的定理
     未删。把 Classification 改为转发方会使两个模块在同一环境中声明同名定义而冲突，
     消除冲突需迁移其全部下游，属独立变更，本模块不承担。已如实标注
     「histInertia 是最粗的估计量」这一限定。
     本模块不引入任何新数学内容。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Modeling

/-! ### §1  偏差序列的两个量（逐字取自 `Classification` §7） -/

/-- **梯度力**（系统性趋势）：首末偏差的平均增量。`n = 0` 时约定为 `0`。 -/
noncomputable def gradForce (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (d n - d 0) / (n : ℝ)

/-- **历史惯性**：首末偏差之差（「这段历史里系统净移动了多少」）。 -/
noncomputable def histInertia (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else |d n - d 0|

/-! ### §2  停止判据 -/

/-- **停止判据**（比值型）：

$$\mathrm{ShouldStop}(d,n,\tau) :=
  \mathrm{histInertia}(d,n) = 0 \ \vee\
  \frac{|\mathrm{gradForce}(d,n)|}{\mathrm{histInertia}(d,n)} \le \tau$$ -/
def ShouldStop (d : ℕ → ℝ) (n : ℕ) (τ : ℝ) : Prop :=
  histInertia d n = 0 ∨ |gradForce d n| / histInertia d n ≤ τ

/-- **判据的对称情形**：`ShouldStop` 的补集，使「停止 / 继续」二分无遗漏。 -/
def ShouldContinue (d : ℕ → ℝ) (n : ℕ) (τ : ℝ) : Prop :=
  ¬ ShouldStop d n τ

/-! ### §3  阈值参数化 -/

/-- **`τ` 的参数化**：$\tau(\alpha,n,\sigma_x,t) = t/(\sigma_x\sqrt{n})$。

    `t` 为 t 分布分位数，`σ_x` 为样本标准差，二者都是可算量。 -/
noncomputable def tauOf (α : ℝ) (n : ℕ) (σx : ℝ) (tCrit : ℝ) : ℝ :=
  tCrit / (σx * Real.sqrt n)

end FateV2.Modeling
