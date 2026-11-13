import FateWorld.FateV2.Error.SigmaToVerdict
import FateWorld.FateV2.Error.FitBoundaryN
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · ErrProfileFromData —— 把**样本数 `n`** 接到 `ErrProfileN.var` 分量上

  ## 迁移登记
  - 来源：新写（T47；作者指定的方向 A）
  - 动作：C 重写
  - 对应环节：F7-02（σ / 误差剖面）、F7-11（恰当拟合边界 / 裁决 K）
  - 依赖裁决：**裁决 K**、**D-008**（σ 由建模层给）、**D-020**（双界只作数学界）、
              **D-022**（反空泛）
  - 改动：**只新建本文件**，不改任何已有模块。
  - 状态：已验证（零 `sorry` / 零 `admit` / 零自定义 `axiom`）

  ## 本文件补的是哪一处缺口

  系统里有两个**互不相干**的量，此前从未被接起来：

  * **量 A** —— `ErrProfileN.var γ`（`Error/ErrProfileN.lean`）：
    **模型**在分辨率 `γ` 处的估计误差分量。索引是 **`γ`（自由度）**，
    **里面没有 `n`**。
  * **量 B** —— `varOf P / n`（`Error/SigmaEstimation.lean`）：
    **样本均值**的方差（`variance_meanOf`，精确等式）。
    索引是 **`n`（样本数）**，**里面没有 `γ`**。

  两者**不是同一个东西**：`varOf P / n` 是估计的**精度**（`n → ∞` 时 → 0），
  而 `ErrProfileN.var γ` 是**模型的**估计误差。T46 的诚实边界正是把这两者
  当成同一个量时留下的。

  本文件只做一件事：**把 `n` 真的传进 `var` 分量的定义里**，并证明
  由此得到的剖面在 `n` 上的**单调性**与**收敛性**。全程**不引入任何建模断言**。

  ```
  §1  varProfile P n γ = varOf P / (n+1)  ── 单调不增 + 趋于 0
  §2  profileFromData P b n : ErrProfileN  ── bias 由 γ 定、var 由 n 定
  §3  err(n) 随 n 不增、且收敛到 b γ（**不是**趋于 0）
  §4  与 T46 端点 A 接上：Var[meanOf(n+1)] 恰是一个 varProfile 实例
  §5  接裁决 K：err(n) 落进 `accepts` 带的可执行样本量条件
  ```

  ## ⚠ 对派单命题的逐条核验（本项目第九次派单核对）

  | 派单候选 | 判定 | 依据 |
  |---|---|---|
  | `varProfile_antitone_in_n` | ✅ **成立** | §1 `varProfile_antitone_in_n`。`Antitone (fun n => varProfile P n γ)` 对**任意实数** `varOf P` 都成立（不需要 `0 ≤ varOf P`）。 |
  | `varProfile_tendsto_zero` | ✅ **成立** | §1 `varProfile_tendsto_zero`。同样不需要 `0 ≤ varOf P`。 |
  | `profileFromData` | ✅ **可构造** | §2。`ErrProfileN` 的 `var_nonneg` 字段需要 `0 ≤ varProfile P n γ`，由 `varOf P ≥ 0`（`variance_nonneg`，**无条件**成立）给出。 |
  | `errProfile_mono`（派的原文「剖面的 err 随 n 与 γ 的联合行为」） | ⚠️ **派单没写清是什么单调**。本文件把它拆成两条**真**命题：§3 `errProfile_antitone_in_n`（`n` 方向：不增）与 §3 `errProfile_tendsto_bias`（`n` 方向：收敛到 `b γ`）。**`γ` 方向不单调**——`bias γ` 是任意函数，`profileFromData` 不假设任何结构，硬写会变假（反例 `bias := fun γ => γ`，`n` 固定时 `err` 随 `γ` 递增）。 |

  ## ⚠ 对派单直觉的两处**纠正**（如实登记）

  ### 纠正 1：`err` 的极限是 `b γ`，**不是 `0`**

  派单写的是「`profileFromData` + `errProfile_mono`」并暗示 `err → 0`。
  **这是假命题**：`err(n) = bias γ + varOf P/(n+1)`，`var` 项确实 → 0，
  但 `bias γ` **不依赖 `n`**，故 `err(n) → bias γ`。
  只有当 `bias γ = 0` 时 `err → 0`。
  本文件按真命题交付（`errProfile_tendsto_bias`），并**不**提供 `err → 0`。

  ### 纠正 2：`varProfile` 里的 `γ` **不出现**

  派单给的 `def varProfile (P) (n γ : Nat) := varOf P / ((n : ℝ) + 1)` 里，
  `γ` 是**未被使用的参数**。本文件**照此实现**（因为这是派单明确指定的形式），
  并在 §1 显式登记这一事实，同时给出**补救**：
  * `varProfile` 的 `γ` 参数保留，使 `profileFromData` 里的 `var` 与 `bias`
    共享同一个 `γ` 索引（类型上是同一个 `Nat → Real` 的坐标）；
  * 「自由度越高 ⟹ 有效样本数越少 ⟹ var 越大」这条**领域直觉**
    **没有**被落成定理，也**没有**被当成公理。它**需要一个显式参数**才能成为
    定理——本文件**不**引入它（见文件末「未做的部分」）。

  ## 超出定义之处（逐条登记）

  `varProfile` 的定义是一个除法式；`ErrProfileN` 的定义是四个字段。
  本文件每条定理都**多说了一步**，见各条 docstring 的「**超出定义之处**」段。

  ## 与公理的关系

  `varProfile` / `ErrProfileN` 的类型里都含 `ℝ`。按项目实测，
  **类型含 `Real` ⟹ 三公理** `[propext, Classical.choice, Quot.sound]`
  （类型带来的，与写法无关）。本文件**每条**都 `#print axioms` 实测并登记在
  `_support_registry_T47.csv`，**未使用任何降公理的技巧**。
  所以本文件**零公理的定理为 0 条**，**三公理为全部**——这是诚实的账。

  ## 未做的部分（如实登记）

  * **不证** `varProfile P n γ` 对 `γ` 单调。那需要给 `P` 加结构
    （例如指数族方差 `ExistExpVar`），那是**额外建模**，本文件不做。
  * **不证** `σ = √(varOf P)`。这是 `SigmaFromAIC` 文件头已登记的**不可证建模断言**。
  * **不证** `n` 个样本估计 `γ` 个自由度时「有效样本数 = `n/γ`」。
    这条选择**不影响**本文件的任何定理（因为 `var` 分量本就与 `γ` 无关），
    故本文件**不引入**它——这是**建模选择最小化**的体现。
-/

namespace FateV2.Error.ErrProfileFromData

open MeasureTheory ProbabilityTheory Filter
open FateV2.Error.SigmaEstimation
open FateV2.ErrorN

/-! ===========================================================================
  §1  误差剖面的 var 分量：由单样本方差与样本数决定
  =========================================================================== -/

/-- **误差剖面的 `var` 分量**：`n` 个样本时的估计误差分量。

  $$\mathrm{varProfile}(P, n, \gamma) = \frac{\mathrm{varOf}(P)}{n+1}$$

  ## 为什么是 `n + 1` 而不是 `n`

  `varProfile` 要对**所有** `n : Nat` 有定义（`ErrProfileN.var : Nat → Real`
  在 `0` 处也必须取值）。用 `n + 1` 使分母**恒正**，免去「`n > 0`」这个
  与本质无关的前件——`n = 0` 时退化为「单样本方差」，语义上也合理。

  ## ⚠ 诚实登记：`γ` 在此表达式中**不出现**

  派单给定的就是这个形式。本文件**照此实现**，但必须说清它的后果：
  * `varProfile` 对 `γ` 是**常函数**；「自由度越高估计误差越大」的领域直觉
    **没有**、也**不能**由此定义得到。
  * 该直觉若要做成定理，必须**显式参数化**（给 `P` 加指数族结构）。
    本文件**不引入**该结构（建模选择最小化）。

  **超出定义之处**：定义本身只是一条除法式。它把**测度层**的量
  （`varOf P`）与**样本数层**的量（`n`）放进同一个表达式，
  这是「样本数」第一次进入误差剖面的 `var` 分量。 -/
noncomputable def varProfile (P : Measure ℝ) (n _γ : Nat) : ℝ :=
  varOf P / ((n : ℝ) + 1)

/-- **`varProfile` 非负**（由 `varOf` 的非负性）。

  **超出定义之处**：定义是 `varOf P / (n+1)`，是一条**未指定符号**的除法式。
  本定理说明它对任意 `P`、任意 `n`、任意 `γ` 都非负 —— 这是
  `ErrProfileN.var_nonneg` 字段能填上的**唯一**理由。

  ⚠ `variance_nonneg` 在本项目里是**无条件**的（对任意实值函数与任意测度），
  所以本定理**不需要** `MemLp` / `IsProbabilityMeasure`。
  这一点比 T46 的 `accepts_of_sample_size`（要 `MemLp`）更干净。 -/
theorem varProfile_nonneg (P : Measure ℝ) (n γ : Nat) : 0 ≤ varProfile P n γ := by
  unfold varProfile
  apply div_nonneg (variance_nonneg (fun x : ℝ => x) P)
  positivity

/-- **`varProfile` 对 `n` 单调不增**（数据越多，估计误差的 `var` 分量越小）。

  $$\mathrm{Antitone}\bigl(n \mapsto \mathrm{varProfile}(P, n, \gamma)\bigr).$$

  **超出定义之处**：定义只是 `varOf P / (n+1)`，它本身**没有**任何序结构陈述。
  本定理说明这个函数在 `n` 上是**单调不增**的 ——
  即「更多数据不会让估计误差变大」，这正是 `var` 分量配得上
  「估计误差」这个名字的**数学内容**。

  ## 证明结构（避开负系数 `linarith`，T46 实测陷阱）

  `Antitone` 在 `Nat` 上用 `antitone_nat_of_succ_le` 化归为逐项
  `f (n+1) ≤ f n`，再用 `div_le_div_of_nonneg_left`
  （`0 ≤ v`、`0 < (n+1)+1`、`(n+1) ≤ (n+1)+1`）直接得到。
  **全程不用 `linarith`**：分母的单调性是 `Nat.cast` 后 `linarith` 能处理的
  **加法形**，不是负系数组合。

  ⚠ 本定理对 `v = varOf P` 的**符号无条件成立**（`v < 0` 时两边同为负，
  不等式方向由 `div_le_div_of_nonneg_left` 的 `0 ≤ a` 前件保证——
  `variance_nonneg` 已给出 `0 ≤ v`，所以该前件确实是免费的）。 -/
theorem varProfile_antitone_in_n (P : Measure ℝ) (γ : Nat) :
    Antitone (fun n : Nat => varProfile P n γ) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold varProfile
  apply div_le_div_of_nonneg_left (variance_nonneg (fun x : ℝ => x) P)
  · positivity
  · push_cast; linarith

/-- **`varProfile` 对 `n` 的差形式**（`a ≤ b` ⟹ 越大越小）。

  $$\mathrm{varProfile}(P, b, \gamma) \le \mathrm{varProfile}(P, a, \gamma)
    \qquad (a \le b).$$

  **超出定义之处**：`varProfile_antitone_in_n` 给的是 `Antitone`（一个**谓词**
  形式的整体单调性）；本定理是它的逐点展开式，
  下游（§3）要用**两点形式**而不是谓词形式。
  两者信息量相同，但本形式更贴近 Lean 的 `≤` 链式推理。

  ⚠ **诚实登记**：本定理是 `varProfile_antitone_in_n` 的**直接推论**，
  信息量**没有增加**。保留它是因为 §3 的 `errProfile_antitone_in_n`
  需要的是这个形状——若直接展开 `Antitone` 会让证明长得不可读。 -/
theorem varProfile_le_of_le (P : Measure ℝ) (γ : Nat) {a b : Nat} (hab : a ≤ b) :
    varProfile P b γ ≤ varProfile P a γ :=
  varProfile_antitone_in_n P γ hab

/-- **`varProfile` 随 `n → ∞` 趋于 `0`**（估计误差的 `var` 分量消失）。

  $$\mathrm{varProfile}(P, n, \gamma) \longrightarrow 0 \qquad (n \to \infty).$$

  **超出定义之处**：定义是 `varOf P / (n+1)`，分母里的 `n` 与 `varOf P` 是
  **两个独立的坐标**。本定理说明：固定 `varOf P`（即固定被测分布），
  只让 `n` 走，这个量**一定**趋于 0 —— 与 `varOf P` 的取值、符号**无关**。

  证明：`(n+1) : ℝ → ∞`（`tendsto_atTop_add_const_right` + `Nat.cast`），
  再 `const_div_atTop`。**不用任何 `0 ≤ v` 前件**——`v/g → 0` 对任意实数 `v` 成立。 -/
theorem varProfile_tendsto_zero (P : Measure ℝ) (γ : Nat) :
    Tendsto (fun n : Nat => varProfile P n γ) atTop (nhds 0) := by
  have hg : Tendsto (fun n : Nat => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have := hg.const_div_atTop (varOf P)
  simpa [varProfile] using this

/-- **`varProfile` 的极限翻译成可执行的 `∃N`**（构造性样本量下界）。

  $$\chi > 0 \;\Longrightarrow\; \exists N,\ \forall n \ge N,\
      \mathrm{varProfile}(P, n, \gamma) < \chi .$$

  **超出定义之处**：`varProfile_tendsto_zero` 说的是**极限**（「最终」）；
  本定理把它翻译成**具体的 `N`**。下游（§5）要把 `var` 分量喂给 `accepts`，
  而裁决是**逐样本量**的，需要的正是 `∃N` 形式。
  转换靠 `Filter.Tendsto.eventually` + `Iio_mem_nhds`。 -/
theorem varProfile_exists_lt (P : Measure ℝ) (γ : Nat) {χ : ℝ} (hχ : 0 < χ) :
    ∃ N : Nat, ∀ n ≥ N, varProfile P n γ < χ :=
  eventually_atTop.mp ((varProfile_tendsto_zero P γ).eventually (Iio_mem_nhds hχ))

/-! ===========================================================================
  §2  由数据构造误差剖面
  =========================================================================== -/

/-- **由数据构造误差剖面**：`bias` 由 `γ`（分辨率）决定，`var` 由 `n`（样本数）决定。

  $$\mathrm{profileFromData}(P, b, n) :=
    \bigl\{\ \mathrm{bias} \gamma := b(\gamma),\quad
      \mathrm{var} \gamma := \mathrm{varProfile}(P, n, \gamma)\ \bigr\}.$$

  **超出定义之处**：`ErrProfileN` 是一个四字段的**结构**，其 `bias` 与 `var`
  都是**任意**函数 `Nat → Real`，`n` 在结构里**根本没有槽位**。
  本构造说明：只要把 `n` 收进 `var` 的**闭包**里，`ErrProfileN` 就
  **可以在样本数已知时被实例化** —— 这是「`n` 进入误差剖面」的落地点。

  ⚠ **`bias` 的责任在调用方**：本构造要求调用方提供 `b γ` **及其非负性证明**
  `hb`。这不是建模断言，而是 `ErrProfileN.bias_nonneg` 字段的**必要输入**
  （该字段在结构定义里就是这样要求的）。`profileFromData` **不**猜测 `b`
  的形状，也**不**假设它与 `γ` 的任何单调关系。 -/
noncomputable def profileFromData (P : Measure ℝ) (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (n : Nat) : ErrProfileN where
  bias := b
  var := fun γ => varProfile P n γ
  bias_nonneg := hb
  var_nonneg := fun γ => varProfile_nonneg P n γ

/-- **`profileFromData` 的 `bias` 分量就是传入的函数**。

  **超出定义之处**：结构的投影 `W.bias` 在构造上是 `b`；本条把它写成
  可重写的等式，供下游 `simp` 使用。信息量：**没有**（是 `rfl`）。 -/
theorem profileFromData_bias (P : Measure ℝ) (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (n : Nat) :
    (profileFromData P b hb n).bias = b := rfl

/-- **`profileFromData` 的 `var` 分量就是 `varProfile`**。

  **超出定义之处**：同 `profileFromData_bias`，是 `rfl` 级投影事实。 -/
theorem profileFromData_var (P : Measure ℝ) (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (n : Nat) (γ : Nat) :
    (profileFromData P b hb n).var γ = varProfile P n γ := rfl

/-- **`profileFromData` 的误差展开式**。

  $$\mathrm{err}\bigl(\mathrm{profileFromData}(P, b, n), \gamma\bigr)
    = b(\gamma) + \frac{\mathrm{varOf}(P)}{n+1}.$$

  **超出定义之处**：`ErrProfileN.err` 的定义是 `bias γ + var γ`；
  本定理把**两个抽象投影**换成具体的 `b γ` 与 `varProfile P n γ`，
  于是「误差」第一次成为一个**能对 `n` 求导数的表达式**（`n` 出现在分母上）。
  定义里 `err` 与 `n` 毫无关系。 -/
theorem profileFromData_err (P : Measure ℝ) (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (n γ : Nat) :
    (profileFromData P b hb n).err γ = b γ + varProfile P n γ := rfl

/-! ===========================================================================
  §3  剖面的误差随 `n` 的行为
  =========================================================================== -/

/-- **误差随样本数单调不增**。

  $$a \le b \;\Longrightarrow\;
    \mathrm{err}(b) \le \mathrm{err}(a) \qquad (\text{固定 } \gamma).$$

  **超出定义之处**：`err` 的定义是 `bias γ + var γ`，**两分量都只依赖 `γ`**，
  定义里没有任何「随 `n` 变化」的意思。本定理说明：一旦 `var` 被 `n` 参数化
  （§2），`err` 就**继承**了 `var` 的单调性 —— `bias` 不变，`var` 不增，故和也不增。

  证明：`add_le_add_left` 把 `varProfile P b γ ≤ varProfile P a γ` 抬到
  `b γ + …` 上。**不用 `linarith`**（避开负系数陷阱）。 -/
theorem errProfile_antitone_in_n (P : Measure ℝ) (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (γ : Nat) {a n : Nat} (han : a ≤ n) :
    (profileFromData P b hb n).err γ ≤ (profileFromData P b hb a).err γ := by
  rw [profileFromData_err, profileFromData_err]
  have h := add_le_add_right (varProfile_le_of_le P γ han) (b γ)
  linarith only [h]

/-- **误差随 `n` 收敛到 `bias`**（**不是**收敛到 `0`）。

  $$\mathrm{err}(n) \longrightarrow b(\gamma) \qquad (n \to \infty).$$

  **超出定义之处**（本文件对派单的**核心纠正**）：
  派单暗示 `err → 0`。**这是假命题** —— 反例：`b ≡ 1`、任意 `P`，
  则 `err(n) ≡ 1 + v/(n+1) → 1 ≠ 0`。
  正确结论是：`err` 收敛到**其 `bias` 分量**，因为 `var` 项消失而 `bias` 项不变。

  **读法**：样本数增加**只**能消掉「估计误差」那一半；
  「逼近误差」那一半（分辨率不足）**与样本数无关**，再多数据也消不掉。
  这正是 `ErrProfileN` 把误差拆成 `bias + var` 两分的**数学意义**：
  两分量的**渐近行为不同**（一个是 `O(1)`，一个是 `O(1/n)`）。

  证明：`varProfile_tendsto_zero` + `Tendsto.const_add`。 -/
theorem errProfile_tendsto_bias (P : Measure ℝ) (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (γ : Nat) :
    Tendsto (fun n : Nat => (profileFromData P b hb n).err γ) atTop (nhds (b γ)) := by
  have h := (varProfile_tendsto_zero P γ).const_add (b γ)
  have heq : (fun n : Nat => (profileFromData P b hb n).err γ)
      = (fun n : Nat => b γ + varProfile P n γ) := by
    funext n
    rw [profileFromData_err]
  rw [heq]
  simpa using h

/-- **误差的可执行上界：大样本时 `err` 落在 `b γ + χ` 以内**。

  $$\chi > 0 \;\Longrightarrow\; \exists N,\ \forall n \ge N,\
      \mathrm{err}(n) \le b(\gamma) + \chi .$$

  **超出定义之处**：`errProfile_tendsto_bias` 是**极限**语言；
  本条把它翻成**具体的 `N`**（裁决侧要的是后者）。
  `b γ + χ` 里的 `χ` 就是「样本数买来的精度」——
  **可以买到多少**由 `χ` 指定，**买不到的部分**是 `b γ`（分辨率误差，`n` 无关）。
  这条把「样本数 ⟹ 误差界」拆成了「可降部分 / 不可降部分」两半，是
  本文件对 `ErrProfileN` 两分量的**定量读法**。 -/
theorem errProfile_exists_lt_bias (P : Measure ℝ) (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (γ : Nat) {χ : ℝ} (hχ : 0 < χ) :
    ∃ N : Nat, ∀ n ≥ N, (profileFromData P b hb n).err γ ≤ b γ + χ := by
  obtain ⟨N, hN⟩ := varProfile_exists_lt P γ hχ
  refine ⟨N, fun n hn => ?_⟩
  rw [profileFromData_err]
  have h := add_le_add_right (le_of_lt (hN n hn)) (b γ)
  linarith only [h]

/-! ===========================================================================
  §4  与 T46 端点 A（`variance_meanOf`）接上：`n` 的两条路是**同一个量**
  ===========================================================================

  这一节是本文件对「两个量不是同一个东西」这条断言的**正面回应**：
  它们**不是**同一个量，但它们**可以**被同一个函数 `varProfile` 同时表达 ——
  一端是「模型侧的误差剖面」，另一端 `γ = 0` 处恰好是
  「统计侧的样本均值方差」。**接点在 `n` 上，不在 `γ` 上。**
  =========================================================================== -/

/-- **`n+1` 个样本的均值方差恰是一个 `varProfile` 实例**（在 `γ = 0` 处）。

  $$\mathrm{Var}[\bar\omega_{n+1}] = \mathrm{varProfile}(P, n, 0).$$

  **超出定义之处**（本节最关键的一条）：
  `variance_meanOf` 给的等式是 `Var[meanOf n] = varOf P / n`（**测量层**）；
  `varProfile` 的定义是 `varOf P / (n+1)`（**误差剖面层**）。
  两者**不是**同一个表达式（分母 `n` vs `n+1`），**必须**把下标对齐才相等。
  本定理做的正是这个对齐：`n+1` 个样本的均值方差 = 下标 `n` 的 `varProfile`。

  **读法**：误差剖面的 `var` 分量在 `γ = 0` 处**就是**样本均值的方差。
  ⚠ **这不说** `γ = 0` 有什么特殊地位（本文件没有给 `γ` 任何语义）；
  它只说明**两条路在 `n` 这条轴上可以对齐**。

  证明：`variance_meanOf` 的 `n` 取 `n+1`（故要 `0 < n+1`），再 `push_cast; ring`。 -/
theorem variance_meanOf_succ_eq_varProfile {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : Nat) :
    variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P))
      = varProfile P n 0 := by
  rw [variance_meanOf hP (n + 1) (Nat.succ_pos n), varProfile]
  push_cast
  ring

/-- **样本均值方差被 `varProfile` 控制**（`∃N` 形式，与 T46 同型）。

  $$\chi > 0 \;\Longrightarrow\; \exists N,\ \forall n \ge N,\
      \mathrm{Var}[\bar\omega_{n+1}] \le \chi .$$

  **超出定义之处**：`SigmaEstimation.variance_meanOf_tendsto_zero` 已给
  `Var[meanOf(n+1)] → 0`；本条把它翻成 `∃N`，并**经由 `varProfile`**
  （`variance_meanOf_succ_eq_varProfile` + `varProfile_exists_lt`）走通。
  这不是新的事实（T46 的 `variance_meanOf_tendsto_zero_nat` 已含极限），
  但它是**同一个 `n` 同时喂给 `ErrProfileN.var` 与 `variance`** 的显式见证。 -/
theorem varProfile_controls_sample_variance {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) {χ : ℝ} (hχ : 0 < χ) :
    ∃ N : Nat, ∀ n ≥ N,
      variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P)) ≤ χ := by
  obtain ⟨N, hN⟩ := varProfile_exists_lt P 0 hχ
  refine ⟨N, fun n hn => ?_⟩
  rw [variance_meanOf_succ_eq_varProfile hP n]
  exact le_of_lt (hN n hn)

/-! ===========================================================================
  §5  接裁决 K（`accepts`）
  =========================================================================== -/

/-- **误差不超 `σ + ε` ⟹ 裁决 K 合格**（把 §2 的剖面喂给 `FitBoundaryN.accepts`）。

  $$b(\gamma) < \sigma + \varepsilon,\quad
    \sigma - \varepsilon \le b(\gamma) + \frac{\mathrm{varOf}(P)}{n+1}
    \;\Longrightarrow\;
    \mathrm{accepts}\ \sigma\ \varepsilon\ \bigl(\mathrm{err}(n)\bigr).$$

  **超出定义之处**：`accepts σ ε e` 的定义是 `σ−ε ≤ e ∧ e ≤ σ+ε`，
  它**不知道** `e` 是从哪个剖面来的，更不知道 `n`。
  本定理把 `e` 绑定到 `profileFromData … n .err γ`，
  于是 **`n` 第一次出现在 `accepts` 所判的对象里**。

  ⚠ **诚实边界**（与 T46 的 `accepts_of_sample_size` 同型）：
  结论里的 `e` 是**剖面的误差**（模型侧量），`σ` 仍是**外部给定的**裁决中心。
  本定理**不**声称「`σ` 等于剖面的真边界」，也**不**声称误差随 `n` 一定
  落进带内 —— `hlo` 是**显式前件**，不是结论。 -/
theorem accepts_profileFromData {P : Measure ℝ} (b : Nat → Real)
    (hb : ∀ γ, 0 ≤ b γ) (γ : Nat) {σ ε : ℝ}
    (hhi : b γ + varProfile P n₀ γ ≤ σ + ε) (hlo : σ - ε ≤ b γ) :
    accepts σ ε ((profileFromData P b hb n₀).err γ) := by
  rw [profileFromData_err]
  refine ⟨?_, ?_⟩
  · -- `σ - ε ≤ b γ`，右边要 `b γ + v ≥ b γ`，需 `v ≥ 0`。
    have hv : (0 : ℝ) ≤ varProfile P n₀ γ := varProfile_nonneg P n₀ γ
    linarith only [hlo, hv]
  · exact hhi

end FateV2.Error.ErrProfileFromData
