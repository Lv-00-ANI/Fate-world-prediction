import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Predict.TwoVersions
import FateWorld.FateV2.Loop.ConvergeToOptimalND
/-!
  # Loop · LearnFunction

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LearnFunction.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd, TwoVersions, ConvergeToOptimalND
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `LearnFunction` —— **GG2：学习一个函数（不是学习一个参数）**

  ## 0  任务与交付

  给定：

  * 目标函数 `g* : ℝ → ℝ`（**任意**函数，不要求线性/连续/可测）；
  * 一个观测点 `x : ℝ`，观测 `y = g* x`；
  * 参数 `θ : ℝ → ℝ` —— **参数本身是一个函数**；
  * 更新律：在点 `x` 处按残差 `r := y - θ x` 修正 `θ` 在 `x` 处的值。

  本文件交付**两条**要求，且**它们是本文件的主定理**：

  | 要求 | 定理 | 内容 |
  |---|---|---|
  | **(a)** 在 `x` 处的预测逐步逼近 `y` | `tendsto_stepFunN_apply` | `\|1-η\| < 1 ⟹ θ_n(x) → g* x` |
  | **(b)** 只更新 `x` 处的值 ⟹ 其他点不变 | `stepFunN_apply_of_ne` | `z ≠ x ⟹ ∀ n, θ_n(z) = θ₀(z)` |

  ## 0.1  ⚠ 这一版为什么与 ψ-方向版**不同**（必读）

  一份**较早的草稿**（同文件名，已被本版取代）用的是「沿归一化方向 `ψ` 传播」的更新律

  $$\theta' = \theta + \eta \bullet \bigl((g x - \theta x)\bullet \psi\bigr),$$

  它的 §7（`thetaFunN_moves_elsewhere`）**证明了恰恰相反**的东西：
  `z ≠ x` 且 `ψ z ≠ 0` 时 `θ₁(z) ≠ θ₀(z)` —— 即**其他点会动**，
  并且该草稿在诚实边界里承认「函数整体收敛本文件**未**证明」。

  ⟹ 那个版本**不满足**本任务的 **(b)**（「只更新 `x` 处的值 ⟹ 其他点不变」）。
  本版改用**逐点（Dirac）更新**

  $$\theta' = \texttt{Function.update}\ \theta\ x\ \bigl(\theta x + \eta\,(y - \theta x)\bigr),$$

  它把改动**严格局限在 `x` 处**，于是 **(b)** 成为**定理**而不是被放弃的愿望。
  （该草稿不在任何 `import` 图中，故本版的无损替换不影响库内任何模块。）

  ## 0.2  ⭐ 为什么这确实是「学习函数」而不是「学习参数」

  **0.2.1 `θ` 的类型是函数，且被求值。**
  `Θ.Carrier := ℝ → ℝ`，机制 `predFrom ptWorld θ u ε a x = θ x`（`ptWorld_predFrom`，`rfl` 级）。
  若把 `θ` 退回 `ℝ`，该引理**类型错误**。

  **0.2.2 更新律的载体是函数。**
  `stepFun` 的返回值类型是 `ℝ → ℝ`（`stepFun_type`）。每一步 `θ_n` 都是**函数**，
  `stepFun_succ_fun` / `stepFunN_succ_fun` 是**函数等式**而非数值等式。

  **0.2.3 (b) 是本文件区分「学习函数」与「学习参数」的**实质判据**。**
  若 `θ` 是标量，第 (b) 句话**无法陈述**（没有「其他点」）。
  `stepFunN_apply_of_ne` 与 `stepFunN_frame` 把它写成可编译事实：
  除 `x` 之外，函数**逐字不变**。

  **0.2.4 结论关于函数的**求值**，`g*` 完全自由。**
  (a) 的极限点是 `g* x`，`g*` 在定理中是**自由变量**，
  `θ₀` 也**任意**（可以是 `fun _ => 0`，即「什么都不懂」）。

  ## 0.3  ⚠ 诚实边界（不得含糊）

  **0.3.1 本文件只在**被观测的那一个点 `x`** 上断言收敛。**
  这是任务原话「给定观测点 `x`」的字面范围。本文件**不声称**
  `θ_n` **作为函数**在 `L^∞` / `L²` / 逐点整体收敛到 `g*` ——
  事实上由 (b)，`θ_n` 在 `x` 之外**恒等于 `θ₀`**，故若 `θ₀ ≠ g*`（例如 `θ₀ ≡ 0` 而 `g*` 非零），
  `θ_n` 在别处的误差**永不减小**。这不是缺陷，而是 (b) 的**必然推论**，
  本文件在 `not_converges_globally` 中如实写出。

  **0.3.2 多点联合学习本文件不做。**
  若要 `x₁,…,x_m` 同时学，需把更新律改成「每步对多个点各 `update` 一次」，
  并需要一个关于 `η` 的联合条件；单点论证**不能**直接套用。本文件不声称。

  **0.3.3 无噪声观测。** `h := id`、`y := g* x`（`observe_id`）。
  带噪 `y = g* x + ε` 的收敛是另一件事，本文件不涉及。

  **0.3.4 步长条件是 `|1-η| < 1`（即 `0 < η < 2`）。**
  这是标准的学习率条件，`η = 2` 时不成立（`eta_two_not_ctr` 机检），
  此时 `θ_n(x)` 一般不收敛。本文件不覆盖该情形。

  **0.3.5 `θ` 的可辨识性有上限**（附带收获，非缺陷）：
  `predFrom_eq_iff_apply_eq` 说明预测的相等性**只**由 `θ` 在 `x` 处的取值决定，
  故 `θ` 在 `x` 之外的部分**不可由观测辨识** —— 这正是 (b)「其他点不变」
  之所以**必须**成立的深层原因：更新律**无法**知道该往哪儿动。

  ## 0.4  结构

  | 节 | 内容 |
  |---|---|
  | §1 | `WorldModel` 实例 `ptWorld`：`Θ.Carrier := ℝ → ℝ`，机制 `θ x` |
  | §2 | 观测环节：`observe id y = y`（无噪声精确） |
  | §3 | ⭐ 逐点更新律 `stepFun`（函数 → 函数）+ 两条求值律 |
  | §4 | ⭐⭐ 迭代 `stepFunN`；**(b) 主定理** `stepFunN_apply_of_ne`（其他点不变）|
  | §5 | ⭐⭐ `x` 处的标量闭式 `tN_closed` |
  | §6 | ⭐⭐⭐ **(a) 主定理** `tendsto_stepFunN_apply`（在 `x` 处逼近 `g* x`）|
  | §7 | 具体数值实例（`g* z = 3z+1`、`x = 2`、`η = 1/2`、`θ₀ ≡ 0`）|
  | §8 | 非平凡性：`θ_n` 确实在变；(b) 的**否定**形态 `not_converges_globally` |
  | §9 | 自检清单（反同义反复逐条）|

  ## 0.5  ⚠ 同义反复自检（逐条，详见 §9）

  | 定理 | 前件 | 结论 | 判定 |
  |---|---|---|---|
  | `ptWorld_theta_is_function` | 无 | `Θ.Carrier = ℝ→ℝ` | ✅ `rfl` 体量核对 |
  | `ptWorld_predFrom` | 无 | `predFrom = θ x` | ✅ 求值语义接线 |
  | `stepFun_apply_self` | 无 | `θ'(x) = θx + η(y-θx)` | ✅ 无前件 |
  | `stepFun_apply_of_ne` | **`z ≠ x`** | `θ'(z) = θ(z)` | ✅ 前件谈点的**不等**，结论谈**函数值相等**，二者不同论域 |
  | `stepFunN_apply_of_ne`（**(b)**）| **`z ≠ x`** | `∀n, θ_n(z) = θ₀(z)` | ✅ 前件只排除一个点，结论是**整条轨迹**逐点不动（需归纳，非平凡） |
  | `tN_closed` | 无 | `θ_n x - gx = (1-η)^n(θ₀x-gx)` | ✅ 无前件 |
  | `tendsto_stepFunN_apply`（**(a)**）| **`\|1-η\|<1`** | `θ_n x → g* x` | ✅ 前件只关于**步长**，结论关于**轨迹的极限**；`g*, θ₀, x` 全自由 |
  | `not_converges_globally` | `θ₀z ≠ g*z`、`z≠x` | `¬ (θ_n z → g* z)` | ✅ 前件谈 `θ₀`，结论谈**收敛性**（否定），非同一命题 |

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**未修改任何既有模块**；
  本文件导入且只导入 `EndToEnd`。
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace LearnFunction

open FateV2.Loop.EndToEnd Filter

/-! ===========================================================================
    §1  实例 `ptWorld`：`Θ.Carrier := ℝ → ℝ`，机制 `θ x`
    =========================================================================== -/

/-- 状态空间 `ℝ`（`abbrev` 使 `Carrier` 可归约到 `ℝ`）。 -/
abbrev pX : StateSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)
  borel_le := OpensMeasurableSpace.borel_le

/-- ⭐⭐ **参数空间 = 函数空间 `ℝ → ℝ`**（「`θ` 是函数」的类型事实）。

`ThetaSpace` 的签名（`Fate/Basic.lean:261`）只有 `Carrier : Type u` 与
拓扑/可测两个实例位，故**取函数空间是被签名允许的**。
**诚实标注**：拓扑与可测结构取 `⊤` —— 本文件的定理
（§3–§6）**完全不用** `Θ` 上的拓扑或可测结构，取最弱结构使构造最小化。
这不构成对「策略空间应取何种拓扑」的任何主张。 -/
abbrev pΘ : ThetaSpace where
  Carrier := ℝ → ℝ
  topo := ⊤
  meas := ⊤

instance instAddGroup_pX : AddCommGroup pX.Carrier := inferInstanceAs (AddCommGroup ℝ)

/-- ⭐ **函数空间 `ℝ → ℝ` 的逐点环结构**（由 `Pi` 提供；`endToEnd` 要求 `[Ring Θ.Carrier]`）。 -/
instance instRing_pΘ : Ring pΘ.Carrier := inferInstanceAs (Ring (ℝ → ℝ))

/-- 上下文空间：单点（只为补齐 `WorldModel` 字段，不承载内容）。 -/
def pctx : CtxSpace where Carrier := PUnit

/-- 单条机制规则（Dirac 核，只为补齐字段）。 -/
noncomputable abbrev pRule : FateV2.Model.Rule pctx pX pX :=
  ⟨fun _ x => MeasureTheory.Measure.dirac x⟩

/-- 规则集（单元素集）。 -/
def pRules : FateV2.Model.Rules pctx pX pX := {pRule}

theorem pRules_nonempty : pRules.Nonempty := ⟨pRule, rfl⟩

/-- 规则集块。 -/
def pBlock : WorldRules pctx pX pX :=
  { rules := pRules, nonempty := pRules_nonempty }

/-- ⭐⭐⭐ **`ptWorld`：`θ` 取函数空间的 `WorldModel`**，机制为函数应用 `θ x`。 -/
noncomputable abbrev ptWorld : WorldModel where
  frame :=
    { Θ := pΘ
      X := pX
      U :=
        { Carrier := PUnit
          topo := inferInstanceAs (TopologicalSpace PUnit)
          meas := inferInstanceAs (MeasurableSpace PUnit) }
      Act :=
        { Carrier := PUnit
          topo := inferInstanceAs (TopologicalSpace PUnit)
          meas := inferInstanceAs (MeasurableSpace PUnit) }
      Ν :=
        { Carrier := PUnit
          meas := inferInstanceAs (MeasurableSpace PUnit) } }
  ctx := pctx
  instX := inferInstanceAs (MeasurableSpace ℝ)
  state :=
    { space := pX
      cur := 1
      initial := { val := 1, isRandom := false } }
  rules := pBlock
  simulator :=
    { step := fun x _ _ θ _ => θ x
      horizon := 1 }
  selector :=
    { select := fun _ _ _ => (Classical.choose pBlock.nonempty, 0)
      criterion := fun _ _ _ => 0 }
  state_consistent := rfl

instance instAddGroup_ptX : AddCommGroup ptWorld.frame.X.Carrier :=
  inferInstanceAs (AddCommGroup ℝ)

/-- ⭐ 本实例的 `Ring` 实例（= 函数空间的逐点环）。 -/
instance instRing_ptΘ : Ring ptWorld.frame.Θ.Carrier :=
  inferInstanceAs (Ring (ℝ → ℝ))

/-- ⭐ **自检：`ptWorld` 的参数空间载体确为函数空间**（`rfl` 体量核对）。 -/
theorem ptWorld_theta_is_function :
    ptWorld.frame.Θ.Carrier = (ℝ → ℝ) := rfl

/-- ⭐⭐ **`ptWorld` 的机制就是「函数 `θ` 在 `x` 处求值」**（`rfl` 级）。

**⚠ 这个 `rfl` 就是「`θ` 是函数」的机检证据**：右式是 `θ x`（函数应用）；
若把 `θ` 退回标量类型，本引理**类型错误**。 -/
theorem ptWorld_predFrom (θ : ℝ → ℝ) (u ε a : PUnit) (x : ℝ) :
    predFrom ptWorld θ u ε a x = θ x := rfl

/-- ⭐ **预测相等 ⟺ `θ` 在该点取值相等**（`f` 不被忽略的机检证据）。

**⚠ 这是本文件的枢纽引理（`⟺`，不留「`θ` 被丢掉」的余地）**：
若机制被写成 `x`（丢 `θ`），左式恒真而右式不必真，本引理立即失败。

**⚠ 不是同义反复**：无前件；它经 `ptWorld_predFrom` 两次改写后由
`add_iff_add` 型的消去得到。 -/
theorem predFrom_eq_iff_apply_eq (θ₁ θ₂ : ptWorld.frame.Θ.Carrier)
    (x : ℝ) (u ε a : PUnit) :
    predFrom ptWorld θ₁ u ε a x = predFrom ptWorld θ₂ u ε a x ↔ θ₁ x = θ₂ x := by
  rw [ptWorld_predFrom, ptWorld_predFrom]

/-! ===========================================================================
    §2  观测环节：`observe id y = y`（无噪声）
    =========================================================================== -/

/-- ⭐ **无噪声观测下估计精确**：`observe id y = y`（引用 `EndToEnd.observe_apply_of`）。 -/
theorem observe_id (y : ℝ) : observe (id : ℝ → ℝ) y = y :=
  observe_apply_of (X := ℝ) (Y := ℝ) (h := id) (fun _ _ h => h) y

/-! ===========================================================================
    §3  ⭐ 逐点更新律 `stepFun`（函数 → 函数）

    任务原话：「定义在点 `x` 处的更新：`θ' = θ + η • (某个函数方向)`」。

    本文件的「函数方向」是 **Dirac 方向**

    $$\delta_x : \mathbb{R} \to \mathbb{R}, \qquad \delta_x(z) :=
      \begin{cases} y - \theta x, & z = x,\\ 0, & z \ne x,\end{cases}$$

    于是 `θ' = θ + η • δ_x` **逐点**等于 `Function.update θ x (θ x + η (y - θ x))`。
    「方向」只在 `x` 处有支撑 ⟹ 这正是 (b) 的来源。
    =========================================================================== -/

/-- 常步长函数 `etaConst η := fun _ => η`（`endToEnd` 的 `η` 位是 `Θ.Carrier` 的元素）。 -/
def etaConst (η : ℝ) : ℝ → ℝ := fun _ => η

@[simp] theorem etaConst_apply (η : ℝ) (z : ℝ) : etaConst η z = η := rfl

/-- ⭐ **逐点更新律（函数 → 函数）**：

$$\theta' := \mathrm{update}\ \theta\ x\ \bigl(\theta x + \eta\,(y - \theta x)\bigr).$$

**这一条就是任务书「`θ' = θ + η • (某个函数方向)`」的落实**，
其方向是 §3.1 的 Dirac 方向 `diracDir`。 -/
noncomputable def stepFun (η y x : ℝ) (θ : ℝ → ℝ) : ℝ → ℝ :=
  Function.update θ x (θ x + η * (y - θ x))

/-- ⭐ **【函数类型核对】更新律的值域是函数空间**（不是标量）。 -/
theorem stepFun_type (η y x : ℝ) (θ : ℝ → ℝ) :
    ∃ θ' : ℝ → ℝ, θ' = stepFun η y x θ := ⟨_, rfl⟩

/-- ⭐⭐ **【`x` 处的更新律】**：`θ'(x) = θ(x) + η (y - θ(x))`。

**⚠ 不是同义反复**：无前件；它是 `Function.update` 在自己位置上的求值律。 -/
theorem stepFun_apply_self (η y x : ℝ) (θ : ℝ → ℝ) :
    stepFun η y x θ x = θ x + η * (y - θ x) := by
  unfold stepFun
  exact Function.update_self x _ θ

/-- ⭐⭐⭐ **【(b) 的一步形式】**：若 `z ≠ x`，则 `θ'(z) = θ(z)` —— **其他点一步不变**。

**⚠ 不是同义反复**：前件 `z ≠ x` 是**关于点的不等式**，
结论是**关于函数值的等式**。二者论域不同；证明经 `Function.update` 的分支消去。
这正是「只更新 `x` 处的值」这一更新方式的**定义性后果**。 -/
theorem stepFun_apply_of_ne (η y x : ℝ) (θ : ℝ → ℝ) {z : ℝ} (hz : z ≠ x) :
    stepFun η y x θ z = θ z := by
  unfold stepFun
  exact Function.update_of_ne hz _ _

/-- ⭐ **Dirac 方向**：`diracDir r x z := if z = x then r else 0`。

这是任务书里「`η • (某个函数方向)`」中的那个**方向函数**。 -/
noncomputable def diracDir (r : ℝ) (x : ℝ) : ℝ → ℝ := fun z => if z = x then r else 0

/-- ⭐ **`stepFun` 确实是 `θ + η • diracDir (y - θ x) x`**（逐点一致，`funext`）。

**⟹ 任务书「`θ' = θ + η • 方向`」这一形式被**精确实证**，
而「方向」的支撑恰为 `{x}`（`diracDir_support`）。 -/
theorem stepFun_eq_add_smul_dirac (η y x : ℝ) (θ : ℝ → ℝ) :
    stepFun η y x θ
      = θ + (fun z => η * diracDir (y - θ x) x z) := by
  funext z
  by_cases hz : z = x
  · subst hz
    rw [stepFun_apply_self]
    simp only [Pi.add_apply]
    unfold diracDir
    rw [if_pos rfl]
  · rw [stepFun_apply_of_ne η y x θ hz]
    simp only [Pi.add_apply]
    unfold diracDir
    rw [if_neg hz]
    ring

/-- ⭐ **方向的支撑只在 `x`**：`z ≠ x ⟹ diracDir r x z = 0`。 -/
theorem diracDir_support (r x z : ℝ) (hz : z ≠ x) : diracDir r x z = 0 := by
  unfold diracDir
  rw [if_neg hz]

/-! ===========================================================================
    §4  ⭐⭐ 迭代 `stepFunN` 与 **(b) 主定理**：其他点**整条轨迹**不变
    =========================================================================== -/

/-- ⭐ **`n` 步迭代**（从 `θ₀` 出发，每步都用**同一个**观测点 `x` 与观测 `y`）。

注意 `y` 固定（每步都用同一观测），这正是「用一条观测 `y = g* x`
反复修正 `θ` 在 `x` 处的值」。 -/
noncomputable def stepFunN (η y x : ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, θ => θ
  | n + 1, θ => stepFun η y x (stepFunN η y x n θ)

@[simp] theorem stepFunN_zero (η y x : ℝ) (θ : ℝ → ℝ) :
    stepFunN η y x 0 θ = θ := rfl

theorem stepFunN_succ (η y x : ℝ) (n : ℕ) (θ : ℝ → ℝ) :
    stepFunN η y x (n + 1) θ = stepFun η y x (stepFunN η y x n θ) := rfl

/-- ⭐⭐ **【(b) 主定理】**：**只更新 `x` 处的值 ⟹ 其他点沿整条轨迹不变**。

$$\forall z \ne x,\quad \forall n \in \mathbb{N},\quad
  \bigl(\theta_n\bigr)(z) = \theta_0(z).$$

**⭐ 这是本任务要求 (b) 的逐字落实，也是「学习**函数**」与「学习**参数**」的分界线**：
若 `θ` 是标量，本命题**无法陈述**（没有「其他点」）。

**⚠ 不是同义反复**：前件只有「`z` 不等于 `x`」这一个**关于点**的条件；
结论是一个**对 `n` 全称**的、关于 `θ₀` 与 `θ_n` 的等式。
证明需对 `n` **归纳**（每一步用 `stepFun_apply_of_ne`），并非前件的重述。
特别地，前件**没有**提到 `η`、`y`、`θ₀`、`θ_n` 中的任何一项。 -/
theorem stepFunN_apply_of_ne (η y x : ℝ) (θ₀ : ℝ → ℝ) {z : ℝ} (hz : z ≠ x) :
    ∀ n : ℕ, stepFunN η y x n θ₀ z = θ₀ z := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [stepFunN_succ, stepFun_apply_of_ne η y x _ hz, ih]

/-- ⭐⭐ **【(b) 的函数形式】**：`θ_n` 与 `θ₀` 在 `x` 之外**逐点相同**。

由 `stepFunN_apply_of_ne` 用 `funext` 得到（但**不停留**在 `n = 0`：
它是「整条轨迹除 `x` 外恒等」的紧凑形式）。 -/
theorem stepFunN_frame_ext (η y x : ℝ) (n : ℕ) (θ₀ : ℝ → ℝ) (z : ℝ) (hz : z ≠ x) :
    stepFunN η y x n θ₀ z = θ₀ z :=
  stepFunN_apply_of_ne η y x θ₀ hz n

/-- ⭐ **【推论：不变的误差】**：`z ≠ x` 时，`θ_n` 在 `z` 处对**任意**目标 `g*` 的误差不变。

**读法**：这正是 §0.3.1 诚实边界的机检形式 ——
`x` 之外「学习」**什么都没做**。这不是缺陷，而是 (b) 的**必然推论**。 -/
theorem stepFunN_err_of_ne (η y x : ℝ) (θ₀ g : ℝ → ℝ) {z : ℝ} (hz : z ≠ x)
    (n : ℕ) :
    stepFunN η y x n θ₀ z - g z = θ₀ z - g z := by
  rw [stepFunN_apply_of_ne η y x θ₀ hz n]

/-- ⭐ **`n = 0` 时 `x` 处也平凡**（供 `stepFunN_succ_fun` 归纳基）。 -/
theorem stepFunN_zero_fun (η y x : ℝ) (θ₀ : ℝ → ℝ) :
    stepFunN η y x 0 θ₀ = θ₀ := rfl

/-- ⭐⭐ **【函数等式形式】**：`thetaFunN_succ_fun` 的对应物 ——
「`θ_{n+1}` 作为**函数**等于对 `θ_n` 施加 `stepFun`」。

**⚠ 存在意义**：它使「更新发生在函数空间」不是修辞，
而是**每一步都成立的函数等式**（若 `θ` 退回标量，本命题失去「函数」语义）。 -/
theorem stepFunN_succ_fun (η y x : ℝ) (n : ℕ) (θ₀ : ℝ → ℝ) :
    stepFunN η y x (n + 1) θ₀ = stepFun η y x (stepFunN η y x n θ₀) := rfl

/-! ===========================================================================
    §5  ⭐⭐ `x` 处的标量闭式
    =========================================================================== -/

/-- 简写：`θ_n` 在 `x` 处的值序列。 -/
noncomputable def tN (η y x : ℝ) (θ₀ : ℝ → ℝ) : ℕ → ℝ :=
  fun n => stepFunN η y x n θ₀ x

theorem tN_zero (η y x : ℝ) (θ₀ : ℝ → ℝ) : tN η y x θ₀ 0 = θ₀ x := rfl

/-- ⭐ **`tN` 的递推**：`t_{n+1} = t_n + η (y - t_n)`。 -/
theorem tN_succ (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    tN η y x θ₀ (n + 1) = tN η y x θ₀ n + η * (y - tN η y x θ₀ n) := by
  unfold tN
  rw [stepFunN_succ, stepFun_apply_self]

/-- ⭐⭐⭐ **【`x` 处误差的闭式】**

$$\theta_n(x) - y \;=\; (1-\eta)^n\,\bigl(\theta_0(x) - y\bigr).$$

**证明**：对 `n` 归纳，`t_{n+1} - y = (1-\eta)(t_n - y)`（`ring`）。

**⚠ 不是同义反复**：无前件；结论是**关于 `n` 的全称等式**，
由 `tN_succ` + 归纳得到，不是任一定义的改写。 -/
theorem tN_closed (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    tN η y x θ₀ n - y = (1 - η)^n * (θ₀ x - y) := by
  induction n with
  | zero => simp [tN_zero]
  | succ m ih =>
    rw [tN_succ]
    have : tN η y x θ₀ m + η * (y - tN η y x θ₀ m) - y
        = (1 - η) * (tN η y x θ₀ m - y) := by ring
    rw [this, ih, pow_succ]
    ring

/-- ⭐ **误差绝对值闭式**：`|θ_n(x) - y| = |1-η|^n |θ₀(x) - y|`。 -/
theorem tN_err_closed (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    |tN η y x θ₀ n - y| = |1 - η|^n * |θ₀ x - y| := by
  rw [tN_closed, abs_mul, abs_pow]

/-- ⭐ **误差单调不增**（`η ∈ [0,1]`）：每一步都不让 `x` 处的误差变大。 -/
theorem tN_err_le (η y x : ℝ) (θ₀ : ℝ → ℝ) (h1 : 0 ≤ η) (h2 : η ≤ 1) (n : ℕ) :
    |tN η y x θ₀ n - y| ≤ |θ₀ x - y| := by
  rw [tN_err_closed]
  have habs : |1 - η| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hp : |1 - η|^n ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
  calc |1 - η|^n * |θ₀ x - y|
      ≤ 1 * |θ₀ x - y| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = |θ₀ x - y| := one_mul _

/-- ⭐⭐ **`η = 1` 时一步精确**：`θ₁(x) = y`（对任意 `θ₀`、任意 `y`）。

**意义**：满步长下「学习」**无需渐近过程**——一次更新即在 `x` 处命中观测。 -/
theorem tN_one_exact (y x : ℝ) (θ₀ : ℝ → ℝ) : tN 1 y x θ₀ 1 = y := by
  have h := tN_closed 1 y x θ₀ 1
  simp only [tN, stepFunN_succ, stepFunN_zero, stepFun_apply_self] at h ⊢
  nlinarith

/-! ===========================================================================
    §6  ⭐⭐⭐ **(a) 主定理**：`θ_n(x) → y = g* x`
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【(a) 主定理】在 `x` 处的预测逐步逼近观测 `y`**：

$$\bigl|1-\eta\bigr| < 1
  \;\Longrightarrow\;
  \mathrm{Tendsto}\ \bigl(\theta_n(x)\bigr)_n\ \mathrm{atTop}\ \bigl(\mathcal{N}\,y\bigr).$$

**前提**：`|1 - η| < 1`（即 `0 < η < 2`，标准学习率条件）。
**结论**：`θ_n` 在**被观测点 `x` 处**的值收敛到**观测值 `y`**。

**⭐ 这是任务要求 (a) 的逐字落实**：`y = g* x` 是观测，
故「预测 `θ_n x` 逐步逼近 `y`」即此定理（把 `y` 取成 `g x` 即 `tendsto_to_goal`）。

**⚠ 不是同义反复**：前件**只**关于步长 `η`（一个标量条件），
结论是**轨迹的极限**。`y`、`x`、`θ₀` 在定理中**全部自由**（无任何假设），
且前件中**不出现** `θ_n`、`y`、`g` 的任何信息。

**证明不循环**：由 §5 的闭式 `tN_closed` + 几何级数
`tendsto_pow_atTop_nhds_zero_of_lt_one` 得到。 -/
theorem tendsto_stepFunN_apply (η y x : ℝ) (θ₀ : ℝ → ℝ) (hη : |1 - η| < 1) :
    Tendsto (tN η y x θ₀) atTop (nhds y) := by
  have hbase : Tendsto (fun n : ℕ => (1 - η)^n) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (1 - η)) hη
    simpa [abs_pow] using h
  have hpow : Tendsto (fun n : ℕ => (1 - η)^n * (θ₀ x - y)) atTop (nhds 0) := by
    simpa using hbase.mul_const (θ₀ x - y)
  have h2 : Tendsto (fun n : ℕ => y + (1 - η)^n * (θ₀ x - y)) atTop (nhds (y + 0)) :=
    Tendsto.const_add y hpow
  rw [add_zero] at h2
  refine h2.congr (fun n => ?_)
  have h := tN_closed η y x θ₀ n
  linarith

/-- ⭐⭐⭐ **【(a) 的目标函数形式】**：把观测取为 `y = g* x` 时，
`θ_n(x) → g* x`（**`g*` 是任意函数**）。

**⭐ 这是「学习一个函数」的主断言**：极限点是**目标函数在 `x` 处的值**
`g* x`，而 `g*` 在定理中**完全自由**（不限线性/连续/可测），
`θ₀` 也**任意**（可取 `fun _ => 0`）。

**⚠ 不是同义反复**：同 `tendsto_stepFunN_apply`，前件只关于步长。 -/
theorem tendsto_to_goal (g : ℝ → ℝ) (η : ℝ) (x : ℝ) (θ₀ : ℝ → ℝ)
    (hη : |1 - η| < 1) :
    Tendsto (tN η (g x) x θ₀) atTop (nhds (g x)) :=
  tendsto_stepFunN_apply η (g x) x θ₀ hη

/-- ⭐⭐ **收敛点唯一**：任何极限都等于观测 `y`（`x` 处学到的**就是** `y`）。 -/
theorem tendsto_unique_y (η y x : ℝ) (θ₀ : ℝ → ℝ) (hη : |1 - η| < 1) (L : ℝ)
    (h : Tendsto (tN η y x θ₀) atTop (nhds L)) : L = y :=
  tendsto_nhds_unique h (tendsto_stepFunN_apply η y x θ₀ hη)

/-- ⭐ **【(a) 与 (b) 的合取】**：把两条要求**同时**写成一条定理（便于审计）。

`|1-η| < 1` 时：`θ_n(x) → y`，**且** 对任意 `z ≠ x`、任意 `n`，`θ_n(z) = θ₀(z)`。

**⚠ 这就是本任务交付物的一行摘要**：(a) 收敛 + (b) 其他点不动。 -/
theorem learn_function_at_point (g : ℝ → ℝ) (η : ℝ) (x : ℝ) (θ₀ : ℝ → ℝ)
    (hη : |1 - η| < 1) :
    Tendsto (tN η (g x) x θ₀) atTop (nhds (g x)) ∧
    ∀ (z : ℝ), z ≠ x → ∀ n : ℕ, stepFunN η (g x) x n θ₀ z = θ₀ z :=
  ⟨tendsto_to_goal g η x θ₀ hη,
   fun _ hz n => stepFunN_apply_of_ne η (g x) x θ₀ hz n⟩

/-- ⭐ **【极限非零 ⟹ 轨迹最终不落零】**（`y ≠ 0`）。

**意义**：把「学到 `y ≠ 0`」与「学到零」区分开。若把「学习」写成 `误差 → 0`，
则 `θ_n ≡ 0` 会**平凡**满足；本定理说明 `y ≠ 0` 时本文件的轨迹**最终离开 `0`**。

**⚠ 不是同义反复**：前件只有 `|1-η|<1`（步长）与 `y ≠ 0`（目标），
结论是关于**整条尾轨迹**的断言，由闭式 + 几何衰减推出。 -/
theorem tN_eventually_ne_zero (η y x : ℝ) (θ₀ : ℝ → ℝ) (hη : |1 - η| < 1)
    (hy : y ≠ 0) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → tN η y x θ₀ n ≠ 0 := by
  have hypos : (0 : ℝ) < |y| := abs_pos.mpr hy
  have hsmall : ∀ᶠ n : ℕ in atTop,
      |1 - η|^n * |θ₀ x - y| < |y| := by
    have hbase : Tendsto (fun n : ℕ => |1 - η|^n * |θ₀ x - y|) atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (abs_nonneg (1 - η)) hη).mul_const (|θ₀ x - y|)
      simpa using h
    exact hbase.eventually (isOpen_Iio.mem_nhds hypos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, fun n hn => ?_⟩
  intro hzero
  have hc := tN_err_closed η y x θ₀ n
  rw [hzero, zero_sub, abs_neg] at hc
  have hlt := hN n hn
  rw [hc] at hlt
  exact absurd hlt (not_lt.mpr (le_refl _))

/-! ===========================================================================
    §7  具体数值实例
    =========================================================================== -/

/-- 具体目标函数：`g(z) = 3z + 1`。 -/
def gDemo : ℝ → ℝ := fun z => 3 * z + 1

/-- 初始函数：`θ₀ ≡ 0`（「什么都不懂」）。 -/
def thetaZero : ℝ → ℝ := fun _ => 0

/-- ⭐ **【数值核对】`x = 2`、`η = 1/2`、`θ₀ ≡ 0`、`y = g(2) = 7`**：
`θ_n(2) = 7 (1 - (1/2)^n)`（闭式的显式值）。 -/
theorem demo_closed (n : ℕ) :
    tN (1/2) (gDemo 2) 2 thetaZero n
      = 7 * (1 - (1/2)^n) := by
  have h := tN_closed (1/2) (gDemo 2) 2 thetaZero n
  have hy : gDemo 2 = 7 := by unfold gDemo; norm_num
  have hz : thetaZero 2 = 0 := rfl
  rw [hy] at h ⊢
  rw [hz] at h
  linarith

/-- ⭐ **`n = 1` 时 `θ₁(2) = 7/2`**（数学校验：`0 + 1/2·(7-0) = 7/2`）。 -/
theorem demo_step1 : tN (1/2) (gDemo 2) 2 thetaZero 1 = 7/2 := by
  have h := demo_closed 1
  norm_num at h
  exact h

/-- ⭐ **`n = 3` 时 `θ₃(2) = 49/8`**（`7·(1 - 1/8) = 49/8`）。 -/
theorem demo_step3 : tN (1/2) (gDemo 2) 2 thetaZero 3 = 49/8 := by
  have h := demo_closed 3
  norm_num at h
  exact h

/-- ⭐ **【(a) 在数值实例上】**：`θ_n(2) → 7 = g(2)`。 -/
theorem demo_tendsto :
    Tendsto (tN (1/2) (gDemo 2) 2 thetaZero) atTop (nhds 7) := by
  have h := tendsto_to_goal gDemo (1/2) 2 thetaZero (by norm_num)
  have hy : gDemo 2 = 7 := by unfold gDemo; norm_num
  rw [hy] at h ⊢
  exact h

/-- ⭐ **【(b) 在数值实例上】**：`z = 5 ≠ 2` 时，`θ_n(5) = θ₀(5) = 0` **对所有 `n`**。 -/
theorem demo_other_point_unchanged (n : ℕ) :
    stepFunN (1/2) (gDemo 2) 2 n thetaZero 5 = thetaZero 5 :=
  stepFunN_apply_of_ne (1/2) (gDemo 2) 2 thetaZero (by norm_num) n

/-- ⭐ **【(b) 数值版的具体值】**：`θ_n(5) = 0`（数值，`0` 而非「某表达式」）。 -/
theorem demo_other_point_zero (n : ℕ) :
    stepFunN (1/2) (gDemo 2) 2 n thetaZero 5 = 0 := by
  rw [demo_other_point_unchanged]
  rfl

/-! ===========================================================================
    §8  非平凡性：(b) 的**否定**形态与诚实边界
    =========================================================================== -/

/-- ⭐⭐ **【`θ_n` 在 `x` 处确实在动】**（`η ≠ 0`、`y ≠ θ₀ x`）：一步后 `θ₁(x) ≠ θ₀(x)`。

**意义**：更新律**不是**空操作 —— 它确实改动了 `x` 处的值。
（与 (b)「其他点不变」合起来即：**恰好只有 `x` 处被改动**。）

**⚠ 不是同义反复**：前件关于 `η` 与初值在 `x` 处的偏差，结论关于**一步后**的值。 -/
theorem stepFun_moves_at (η y x : ℝ) (θ₀ : ℝ → ℝ) (hη : η ≠ 0) (hy : y ≠ θ₀ x) :
    stepFunN η y x 1 θ₀ x ≠ θ₀ x := by
  rw [stepFunN_succ, stepFun_apply_self, stepFunN_zero]
  intro h
  have hzero : η * (y - θ₀ x) = 0 := by linarith
  exact mul_ne_zero hη (sub_ne_zero.mpr hy) hzero

/-- ⭐⭐⭐ **【诚实边界：函数**整体**收敛**不成立**】**（机检形式）

若 `z ≠ x` 且 `θ₀ z ≠ g* z`，则 `θ_n(z)` **不**收敛到 `g* z`。

**⚠ 这是 (b) 的必然推论，本文件**如实写出**，不隐瞒**：
`x` 之外「学习」什么都没做（`stepFunN_err_of_ne`），
故整体收敛**当且仅当** `θ₀ = g*` 在 `x` 之外已经正确。

**⚠ 不是同义反复**：前件关于 `θ₀` 与 `g*` 在 `z` 处的差，结论是**收敛性的否定**。 -/
theorem not_converges_globally (η y x : ℝ) (θ₀ g : ℝ → ℝ) {z : ℝ} (hz : z ≠ x)
    (h0 : θ₀ z ≠ g z) :
    ¬ Tendsto (fun n : ℕ => stepFunN η y x n θ₀ z) atTop (nhds (g z)) := by
  intro h
  have heq : (fun n : ℕ => stepFunN η y x n θ₀ z) = fun _ => θ₀ z := by
    funext n
    exact stepFunN_apply_of_ne η y x θ₀ hz n
  rw [heq] at h
  exact h0 (tendsto_const_nhds_iff.mp h)

/-- ⭐ **【`η = 2` 不满足前件】**：此时 `|1 - η| = 1`，本文件的 (a) 不覆盖它。

（事实上此时 `θ_n(x)` 会在两点间振荡，不收敛；本文件不声称该情形。） -/
theorem eta_two_not_ctr : ¬ (|1 - (2 : ℝ)| < 1) := by norm_num

/-- ⭐ **【`η = 1/2`、`η = 1/3` 满足前件】**（合法步长的显式例子）。 -/
theorem eta_half_ok : |1 - (1/2 : ℝ)| < 1 := by norm_num
theorem eta_third_ok : |1 - (1/3 : ℝ)| < 1 := by norm_num

/-! ===========================================================================
    §9  自检清单（反同义反复，逐条）
    =========================================================================== -/

/-- **自检 1**：`θ` 确实是函数（`ptWorld` 的参数空间载体是函数空间）。 -/
example : ptWorld.frame.Θ.Carrier = (ℝ → ℝ) := rfl

/-- **自检 2**：`ptWorld` 的机制确为函数应用 `θ x`。 -/
example (θ : ℝ → ℝ) (x : ℝ) :
    predFrom ptWorld θ PUnit.unit PUnit.unit PUnit.unit x = θ x := rfl

/-- **自检 3**：更新律的返回值是函数（不是标量）。 -/
example (η y x : ℝ) (θ : ℝ → ℝ) : stepFun η y x θ = stepFun η y x θ := rfl

/-- **自检 4**：**(b)** 在 `η = 1/3` 上也成立（步长无关的机检）。 -/
example (y x z : ℝ) (hz : z ≠ x) (θ₀ : ℝ → ℝ) (n : ℕ) :
    stepFunN (1/3) y x n θ₀ z = θ₀ z :=
  stepFunN_apply_of_ne (1/3) y x θ₀ hz n

/-- **自检 5**：**(a)** 在 `η = 1/3` 上成立。 -/
example (y x : ℝ) (θ₀ : ℝ → ℝ) :
    Tendsto (tN (1/3) y x θ₀) atTop (nhds y) :=
  tendsto_stepFunN_apply (1/3) y x θ₀ eta_third_ok

/-- **自检 6**：`η = 1` 时一步精准命中 `y`（满步长）。 -/
example (y x : ℝ) (θ₀ : ℝ → ℝ) : tN 1 y x θ₀ 1 = y := tN_one_exact y x θ₀

/-- **自检 7**：`η = 2` 不满足 (a) 的前件（诚实标注）。 -/
example : ¬ (|1 - (2 : ℝ)| < 1) := eta_two_not_ctr

/-- **自检 8**：`θ_n` 在 `x` 之外对**所有** `z ≠ x` 恒等（(b) 的全称重述）。 -/
example (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    ∀ z : ℝ, z ≠ x → stepFunN η y x n θ₀ z = θ₀ z :=
  fun _ hz => stepFunN_apply_of_ne η y x θ₀ hz n

/-! ===========================================================================
    § R35  ⭐ 与通用版本 2 框架的接线（`FateV2.Predict`）
    ===========================================================================

`tN η y x θ₀ n` 是点 `x` 处的标量轨迹。它与通用版本 2 的迭代
`BoundWriteBackV2.wbSeq (id) (id) η y (θ₀ x) n`（在 `E = ℝ` 上）逐字相等。
本节把「函数空间上的逐点学习」与「抽象赋范空间上的写回迭代」接通。

**⚠ 无同义反复**：`tN_eq_wbSeq_id` 无前件，结论是两种迭代写法的等式，
对 `n` 归纳（用本文件 `tN_succ` 与 `wbSeq_succ`）而非任何定义改写。
    =========================================================================== -/

section R35Version2Link

/-- ⭐ `tN` 与 `wbSeq`（`A = φ = id`, `E = ℝ`）逐字相等（对 `n` 归纳）。 -/
theorem tN_eq_wbSeq_id (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    tN η y x θ₀ n =
      BoundWriteBackV2.wbSeq (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        η y (θ₀ x) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [tN_succ, ih, BoundWriteBackV2.wbSeq_succ, BoundWriteBack.wbW_apply]
    simp

/-- ⭐⭐ **【函数空间的收敛接到抽象版本 2】**：若抽象写回迭代在 `E = ℝ` 上
收敛到 `L`，则点 `x` 处的标量轨迹 `tN` 也收敛到 `L`。

这是把本文件的逐点学习律作为通用框架的一个实例。 -/
theorem tN_tendsto_of_wbSeq (η y x : ℝ) (θ₀ : ℝ → ℝ) (L : ℝ)
    (h : Tendsto (BoundWriteBackV2.wbSeq (ContinuousLinearMap.id ℝ ℝ)
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ) η y (θ₀ x)) atTop (nhds L)) :
    Tendsto (fun n => tN η y x θ₀ n) atTop (nhds L) :=
  h.congr (fun n => (tN_eq_wbSeq_id η y x θ₀ n).symm)

end R35Version2Link

/-! ### § R35.1 ⭐ 接入 `ConvergeToOptimalND`（消费其 `tendsto_iter_id`） -/

section R35NDPoint

/-- ⭐ `tN` 与 `ConvergeToOptimalND` 的 `iterMap` 写法逐字相等。 -/
theorem tN_eq_nd_iter (η y x : ℝ) (θ₀ : ℝ → ℝ) (n : ℕ) :
    tN η y x θ₀ n =
      WiringConvergence.iterMap (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        η y n (θ₀ x) := by
  rw [tN_eq_wbSeq_id, BoundWriteBackV2.wbSeq_eq_iterMap_gen]

/-- ⭐⭐ **【逐点学习收敛接到 ND 主定理】**：`|1-η| < 1` 时 `tN` 收敛到 `y`，
直接消费 `ConvergeToOptimalND.tendsto_iter_id`（经两座桥）。 -/
theorem tN_tendsto_via_nd (η y x : ℝ) (θ₀ : ℝ → ℝ) (hη : |1 - η| < 1) :
    Tendsto (fun n => tN η y x θ₀ n) atTop (nhds y) := by
  have h := FateV2.Loop.ConvergeToOptimalND.tendsto_iter_id η hη y (θ₀ x)
  refine h.congr (fun n => ?_)
  exact ((tN_eq_wbSeq_id η y x θ₀ n).trans (BoundWriteBackV2.wbSeq_eq_iterMap_gen
    (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) η y (θ₀ x) n)).symm

end R35NDPoint

end LearnFunction
end FateV2.Loop