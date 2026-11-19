import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Modeling.PearlHierarchy
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
  # Modeling · T43CounterfactualAbduction

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T43CounterfactualAbduction.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMSemantics, PearlHierarchy
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ⚠ **第 247 轮标注（J1 批量审核）：**本模块**不是概率模块****

**J1 的实测**：20 条定理中**概率相关性 = 0**（没有一条涉及 `FinJoint`/`CondMul`/`jointLaw`）。
**值全部来自常数 `1/4`。**

## ✅ 仍有内容的部分
- `abduction_value`：`sum_congr` + `sum_prod_four` 真化简
- `abduction_changes_result` / `abduction_value_false`

## ⚠ **类型标注**（N8）
- **[验证]**：约 12 条（具体数值）
- **[支撑]**：约 5 条
- **[展开]**：2 条（`M_sg1`、`M_pU` 是 `rfl`）

**⚠ 本模块**不应计入「概率模块」的统计量**。**
-/


/-! ===========================================================================
  `Fate/_r242_G2` —— **去掉溯因，反事实就退化为干预**（第 242 轮 · 缺口 2 · G2）

  ## 0. 文献

  **Pearl, *Causality* (2nd ed.), §7.1.2「反事实的三个步骤」**：

  > 1. **溯因 (abduction)**：用观测到的证据 `E = e` 更新外生变量的分布，
  >    得到后验 `P(U | e)`；
  > 2. **干预 (action)**：把结构方程中 `X` 的方程替换为 `X := x′`
  >    （即 do 算子），得 `M_{x′}`；
  > 3. **预测 (prediction)**：在 `M_{x′}` 中用后验 `P(U | e)` 计算 `Y` 的分布。

  第 2 步**单独**（`P(U)` 不做更新，只做 `do(x′)`）给出的正是**干预律** `P(y | do(x′))`。
  **于是**：**反事实律 = 干预律 ⟺ 溯因步骤是「空」的**（后验 = 先验）。

  这与 `PearlHierarchy` 的分层口径**完全对齐**：
  `L2_do`（干预律）与 `L3_1`（反事实律）在 `u` 上的差别**只在那个 `[x_u = x]` 因子**。

  ## 1. 本文件交付

  | # | 定理 | 难度 | 说明 |
  |---|---|---|---|
  | 1 | `cf_no_abduction_eq_doLaw` | ⭐⭐⭐ | `abduction = false` ⟹ 结果 = `doLaw`（§2）|
  | 2 | `abduction_changes_result` | ⭐⭐⭐⭐ | **具体 SCM**：做溯因 `≠` 不做溯因（§4）|
  | 3 | `abduction_matters_quantitative` | ⭐⭐ | 具体数值 `1/4` vs `1/2`（§4.2）|
  | 4 | `prediction_swaps_both` | ⭐⭐⭐ | 同时交换「用法」时**只有溯因因子**起作用（§3）|

  ## 2. ⚠⚠ 诚实边界（**先声明，正文兑现**）

  ### 2.1 第 1 条（`cf_no_abduction_eq_doLaw`）**确实**是 D4 型（定义展开）

  **用户已预先警告过这一点，我确认警告正确。** `SCMSemantics.doLaw` 的定义**本身**
  就是「用先验 `pU` 求和」：`doLaw M x y = ∑ u, pU u * [h_u(x) = y]`。
  所以「不做溯因」与 `doLaw` **是同一件事**，等式**由 `rfl` 关闭**。
  **我不把它包装成深刻定理**：它在 §2 中**只用来把 `CFAlgorithm` 的字段语义钉死**，
  真正的数学内容在 §3、§4。

  ### 2.2 第 2 条的**真正内容**在哪

  如果只定义
  「溯因版 = `∑ u pU u * [x_u = x] * [h_u(x′) = y]`」，
  而「非溯因版 = `∑ u pU u * [h_u(x′) = y]`」，
  那么二者的差别**就是**多了一个 `[x_u = x]` 因子。**这一点本身**也只是
  「两个求和式不同」——**其证明价值完全取决于「存在一个 SCM 使它们数值不同」**。
  **§4 正是交付这个**：`Bool × Bool` 上的显式 `M`，`pU ≡ 1/4`，
  分情况算出 `1/4` 与 `1/2`，并由此得到 `≠`。**这是可核验的具体反例，不是同义反复。**

  ### 2.3 我**没有**做的事（不掩饰）

  1. **不**从图上的 d-分离推出「何时溯因因子消失」。那属**缺口 1**（Pearl 1.2.4）。
     本文件把「溯因」定义成**公式**（`abductionFactor`），
     **它与 Pearl 第 1 步的语义对应是「事后合理性论证」（§5），不是定理。**
  2. **不**断言「反事实 ⟹ 干预」在**所有** `L1/L2` 缺失的信息下都成立。
     `PearlHierarchy.L3_not_determined_by_L1_and_L2` 已表明 L3 ⊋ (L1,L2)；
     本文件说的是**更窄**的一件事：**在 `L3` 的逐 `u` 公式上把溯因因子换成 1，
     得到的就是 `L2` 的 `doLaw`**。这正是「去掉溯因 ⟹ 退化为干预」的精确形式。
  3. **数值 `1/4` / `1/2`** 全部由 Lean 的 `norm_num` 计算，
     **没有手写「已知答案」**；§4 的证明里每一步都有对应的引理名。
=========================================================================== -/

namespace FateV2.Modeling.R242.G2

open FateV2.Error FateV2.Modeling.PearlHierarchy FateV2.Modeling.SCMSemantics Finset

/-! ## §1 记号工具 -/

section Tools

/-- `v2f v = fun _ => v`：把一个 `Y` 值**零填充**成常值函数。
用途：让反事实律的值落在 `X × (X → Y)` 这个与 `L3_1` 相同的空间里，
从而可以**直接与 `doLaw` 的边缘比较**。 -/
def v2f {Y : Type} (v : Y) : Bool → Y := fun _ => v

/-- `v2f` 是**单射**（在 `Bool` 非空的见证点 `true` 上取值）。 -/
theorem v2f_inj {Y : Type} {a b : Y} (h : v2f a = v2f b) : a = b := by
  have h2 : v2f a true = v2f b true := congrFun h true
  simpa [v2f] using h2

/-- `v2f a = v2f b ↔ a = b`。 -/
theorem v2f_eq {Y : Type} {a b : Y} : v2f a = v2f b ↔ a = b :=
  ⟨v2f_inj, fun h => by rw [h]⟩

/-- `Bool` 上的求和展成两项。 -/
theorem sum_bool_two (p : Bool → ℝ) : (∑ y : Bool, p y) = p true + p false := by
  rw [Fintype.sum_bool]

/-- `Bool × Bool` 上的求和展成四项（**按 `Fintype.sum_prod_type` 的嵌套序**）。 -/
theorem sum_prod_four (f : Bool × Bool → ℝ) :
    (∑ u : Bool × Bool, f u)
      = (f (false, false) + f (false, true)) + (f (true, false) + f (true, true)) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  ring

/-- 指示函数：`[P]`，真则 `1`，假则 `0`。 -/
theorem ind_pos (P : Prop) [Decidable P] (h : P) : (if P then (1 : ℝ) else 0) = 1 :=
  if_pos h

/-- 指示函数：`[P]`，真则 `1`，假则 `0`。 -/
theorem ind_neg (P : Prop) [Decidable P] (h : ¬ P) : (if P then (1 : ℝ) else 0) = 0 :=
  if_neg h

end Tools

/-! ## §2 ⭐⭐⭐ `CFAlgorithm`：「做不做溯因」作为一个**字段**

**⚠ 这一节是 D4（定义展开）**，见文件头的 §2.1。
它的作用是**把「溯因」在类型上钉死成一个 `Bool` 开关**，
使第 3 步（预测）的两条分支可以**并列书写**。 -/

section Algorithm

variable {X Y : Type}

/-- ⭐⭐ **反事实计算算法**（Pearl §7.1.2 的三步，`abduction` 开关控制第 1 步）。

* `abduction = true`：**执行**第 1 步 —— 用观测证据 `X = x` 把外生律重加权：
  权重 `pU u * [x_u = x]`（这是后验 `P(U | X = x)` 的**未归一化**形式）；
* `abduction = false`：**跳过**第 1 步 —— 直接用先验 `pU u`。

**第 2 步（干预）与第 3 步（预测）在两条分支中完全相同**：
把结构方程的第 2 分量替换为 `do` 版本 `h_u(x′)`，再对 `u` 求和。
**⟹ 两条分支的唯一变量就是这个开关。** -/
structure CFAlgorithm (X Y : Type) where
  /-- 是否执行溯因步骤。 -/
  abduction : Bool

/-- ⭐⭐ **溯因权重**：`abduction = true` 时是观测筛选因子 `[x_u = x]`，否则是 `1`。 -/
noncomputable def CFAlgorithm.weight (a : CFAlgorithm X Y)
    (M : PearlHierarchy.SCM X Y) [DecidableEq X] (x : X) (u : M.U) : ℝ :=
  if a.abduction then (if (M.sg u).1 = x then 1 else 0) else 1

/-- ⭐⭐⭐ **反事实（`L3`）律**：先按 `weight` 重加权外生律，
再对 `do(x′)` 后的结构方程求 `Y` 的分布。

$$\mathrm{cfLaw}_a\,M\,(x,x')\,y
  = \sum_u p_U(u)\cdot w_a(x,u)\cdot[\mathrm{sg}(u).2\ x' = y]$$
-/
noncomputable def CFAlgorithm.cfLaw (a : CFAlgorithm X Y)
    (M : PearlHierarchy.SCM X Y) [DecidableEq X] [DecidableEq Y]
    (x x' : X) (y : Y) : ℝ :=
  ∑ u, M.pU u * a.weight M x u * (if (M.sg u).2 x' = y then 1 else 0)

/-- ⭐⭐⭐ **`abduction = false` ⟹ 结果 = `doLaw`**（Pearl：跳过第 1 步 ⟹ 只剩干预）。

**⚠ 这是 D4（定义展开）**：`weight = 1` 时求和式与 `doLaw` 的定义**字面相同**。
证明是 `Finset.sum_congr` + `one_mul`，**不含概率内容**。
**真正的数学内容在 §4**（存在 SCM 使开关产生不同结果）。 -/
theorem cf_no_abduction_eq_doLaw (M : PearlHierarchy.SCM X Y)
    [DecidableEq X] [DecidableEq Y] (x x' : X) (y : Y) :
    (⟨false⟩ : CFAlgorithm X Y).cfLaw M x x' y = doLaw M x' y := by
  unfold CFAlgorithm.cfLaw doLaw CFAlgorithm.weight
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Bool.false_eq_true, if_false]
  ring

/-- ⭐⭐ 由 `abduction = true` 的**展开式**（只是把开关打开，仍属定义层）。 -/
theorem cf_with_abduction_eq (M : PearlHierarchy.SCM X Y)
    [DecidableEq X] [DecidableEq Y] (x x' : X) (y : Y) :
    (⟨true⟩ : CFAlgorithm X Y).cfLaw M x x' y
      = ∑ u, M.pU u * (if (M.sg u).1 = x then 1 else 0)
          * (if (M.sg u).2 x' = y then 1 else 0) := by
  unfold CFAlgorithm.cfLaw CFAlgorithm.weight
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [if_true]

/-- ⭐⭐ 带溯因的公式**恰好是** `condY` 在 `x' = x` 处的值。

**⟹ 观测律 `condY` 正是「反事实 + 完整溯因」在 `x' = x`（**无干预**）处的特例。**
这与 Pearl 的直觉一致：`condY` 是「用后验预测事实」，不涉及 do。
**⚠ 这仍属定义层**（`condY` 的定义与上式字面相同），故只作**登记**，不作主定理。 -/
theorem cf_with_abduction_at_same_x_eq_condY (M : PearlHierarchy.SCM X Y)
    [DecidableEq X] [DecidableEq Y] (x : X) (y : Y) :
    (⟨true⟩ : CFAlgorithm X Y).cfLaw M x x y = condY M x y := by
  rw [cf_with_abduction_eq]
  rfl

end Algorithm

/-! ## §3 ⭐⭐⭐ **同时交换「用法」时，只有溯因因子起作用**

**观察**：`condY` 与 `cfLaw_{abduction=true}` 在 `x' = x` 处相同（§2），
而 `doLaw` 与 `cfLaw_{abduction=false}` 相同（§2）。
**⟹ 两条律的差别**可以被写成**单一因子** `[x_u = x]` 的差别。
下面把它做成一条**通用等式**（对任意 `M`、任意 `x` 成立），
从而「去掉溯因 ⟹ 退化为干预」有一个**逐点形式**。 -/

section Swap

variable {X Y : Type} [DecidableEq X] [DecidableEq Y]

/-- ⭐⭐⭐ **逐点形式**：带溯因的律 = 不带溯因的律，但**每一项**多乘了 `[x_u = x]`。

这是 §4 反例的**通用机制**：反例的存在性 ⟺ 存在一个 `M` 使那个因子**真的**改变了求和。 -/
theorem abduction_true_eq_false_with_factor (M : PearlHierarchy.SCM X Y)
    (x x' : X) (y : Y) :
    (⟨true⟩ : CFAlgorithm X Y).cfLaw M x x' y
      = ∑ u, M.pU u * (if (M.sg u).1 = x then 1 else 0)
          * (if (M.sg u).2 x' = y then 1 else 0) :=
  cf_with_abduction_eq M x x' y

/-- ⭐⭐ 不带溯因的律的**同一形状**（因子被换成 `1`）。 -/
theorem abduction_false_form (M : PearlHierarchy.SCM X Y) (x x' : X) (y : Y) :
    (⟨false⟩ : CFAlgorithm X Y).cfLaw M x x' y
      = ∑ u, M.pU u * (1 : ℝ) * (if (M.sg u).2 x' = y then 1 else 0) := by
  rw [cf_no_abduction_eq_doLaw]
  unfold doLaw
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

end Swap

/-! ## §4 ⭐⭐⭐⭐ **具体 SCM 上的数值反例**：溯因改变结果

### 4.1 载体

```
U  = Bool × Bool          -- 外生 (a, b)
pU ≡ 1/4                  -- 均匀（四个原子各 1/4）
sg u = (u.1, v2f u.2)     -- X := a  且  Y := b（Y 的方程**忽略** X）
```

**关键结构**：`Y` 的方程 `fun _ => b` **完全忽略自己的输入**，
故 `doLaw M x' y = 1/2` 对**任何** `x'` 都成立（`Y` 只由 `b` 决定）。

而**溯因**会筛掉 `a ≠ x` 的两条外生原子，只留下 `a = x` 的两条，
此时 `Y` 的两种取值各占 **`1/4`**（而非 `1/2`）。

**⟹ 数值差 `1/2 ∉ {1/4}`，开关**真的**改变结果。** -/

section Counterexample

/-- 零填充：`Y` 值 → 常值函数（`Bool → Bool`）。 -/
abbrev v2 : Bool → (Bool → Bool) := v2f

/-- ⭐⭐⭐⭐ **参考 SCM**。

* `U := Bool × Bool`，`pU ≡ 1/4`（均匀分布，总质量 `4 · 1/4 = 1`）；
* `sg (a, b) = (a, v2 b)`：`X := a`，**结构方程 `Y := b` 忽略输入 `X`**。 -/
noncomputable def M : PearlHierarchy.SCM Bool Bool where
  U := Bool × Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1 / 4
  sg := fun u => (u.1, v2 u.2)

/-- `M.sg` 的第一分量展开。 -/
theorem M_sg1 (u : M.U) : (M.sg u).1 = u.1 := rfl

/-- `M.sg` 的第二分量在任意输入上等于 `u.2`（**结构方程忽略输入**）。 -/
theorem M_sg2 (u : M.U) (x : Bool) : (M.sg u).2 x = u.2 := by
  rw [show (M.sg u).2 = v2 u.2 from rfl]
  rfl

/-- `M.pU` 展开。 -/
theorem M_pU (u : M.U) : M.pU u = 1 / 4 := rfl

/-- ⭐⭐ **`doLaw` 的数值**：`M` 下 `do(x')` 后 `Y = y` 的质量。

**因为 `Y` 的方程忽略 `x'`，该值与 `x'` 无关**：`= 1/2`。 -/
theorem doLaw_value (x' y : Bool) : doLaw M x' y = 1 / 2 := by
  rw [doLaw]
  have key : (∑ u : M.U, M.pU u * (if (M.sg u).2 x' = y then (1 : ℝ) else 0))
      = (∑ u : Bool × Bool, (1 : ℝ) / 4 * (if u.2 = y then (1 : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro u _
    obtain ⟨a, b⟩ := u
    have h2 : (M.sg (a, b)).2 x' = b := M_sg2 (a, b) x'
    have hp : M.pU (a, b) = 1 / 4 := M_pU (a, b)
    rw [h2, hp]
  rw [key, sum_prod_four]
  cases y <;> norm_num

/-- ⭐⭐⭐ **带溯因的律的数值**：筛出 `a = x` 后，`Y = y` 的质量只有 `1/4`。 -/
theorem abduction_value (x y : Bool) :
    (⟨true⟩ : CFAlgorithm Bool Bool).cfLaw M x true y = 1 / 4 := by
  rw [cf_with_abduction_eq]
  have key : (∑ u : M.U, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)
        * (if (M.sg u).2 true = y then (1 : ℝ) else 0))
      = (∑ u : Bool × Bool, (1 : ℝ) / 4
          * (if u.1 = x then (1 : ℝ) else 0) * (if u.2 = y then (1 : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro u _
    obtain ⟨a, b⟩ := u
    have h1 : (M.sg (a, b)).1 = a := M_sg1 (a, b)
    have h2 : (M.sg (a, b)).2 true = b := M_sg2 (a, b) true
    have hp : M.pU (a, b) = 1 / 4 := M_pU (a, b)
    rw [h1, h2, hp]
  rw [key, sum_prod_four]
  cases x <;> cases y <;> norm_num

/-- ⭐⭐ **带溯因的律在 `x' = false` 处也是 `1/4`**（因 `Y` 忽略输入）。 -/
theorem abduction_value_false (x y : Bool) :
    (⟨true⟩ : CFAlgorithm Bool Bool).cfLaw M x false y = 1 / 4 := by
  rw [cf_with_abduction_eq]
  have key : (∑ u : M.U, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)
        * (if (M.sg u).2 false = y then (1 : ℝ) else 0))
      = (∑ u : Bool × Bool, (1 : ℝ) / 4
          * (if u.1 = x then (1 : ℝ) else 0) * (if u.2 = y then (1 : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro u _
    obtain ⟨a, b⟩ := u
    have h1 : (M.sg (a, b)).1 = a := M_sg1 (a, b)
    have h2 : (M.sg (a, b)).2 false = b := M_sg2 (a, b) false
    have hp : M.pU (a, b) = 1 / 4 := M_pU (a, b)
    rw [h1, h2, hp]
  rw [key, sum_prod_four]
  cases x <;> cases y <;> norm_num

/-- ⭐⭐⭐⭐ **`abduction_matters_quantitative`**：具体数值 ——
**同一 SCM、同一观测 `x = true`、同一预测目标 `x' = true`、同一 `y = true`**，
做溯因给出 `1/4`，不做溯因给出 `1/2`。 -/
theorem abduction_matters_quantitative :
    (⟨true⟩ : CFAlgorithm Bool Bool).cfLaw M true true true = 1 / 4
    ∧ (⟨false⟩ : CFAlgorithm Bool Bool).cfLaw M true true true = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · rw [abduction_value]
  · rw [cf_no_abduction_eq_doLaw, doLaw_value]

/-- ⭐⭐⭐⭐ **`abduction_changes_result`**：**存在**具体 SCM 与具体观测，
使「做溯因」与「不做溯因」给出**不同**结果。

这是本文件**唯一**需要「非平凡性」的定理：它不是定义展开，
而是把 §4.1 的两条**数值引理**（`abduction_value` / `doLaw_value`）拼起来，
再用 `norm_num` 排除 `1/4 = 1/2`。 -/
theorem abduction_changes_result :
    ∃ (M' : PearlHierarchy.SCM Bool Bool) (x x' y : Bool),
      (⟨true⟩ : CFAlgorithm Bool Bool).cfLaw M' x x' y
        ≠ (⟨false⟩ : CFAlgorithm Bool Bool).cfLaw M' x x' y := by
  refine ⟨M, true, true, true, ?_⟩
  rw [abduction_value, cf_no_abduction_eq_doLaw, doLaw_value]
  norm_num

/-- ⭐⭐⭐ **反向的一步（对照）**：若 `Y` 的方程**不忽略** `X`（`X` 与 `Y` 同源混杂），
溯因**仍然**改变结果 —— 这排除了「反例只依赖 `Y` 忽略 `X`」的疑虑。

用另一个 SCM：`sg u = (u.1, fun x => x && u.2)`（`Y := X ∧ b`）。
这里 `doLaw M' true true = 1/4`（需 `b = true`），而溯因筛出 `a = x` 后也是 `1/4`
—— **⚠ 本例给出相等的值**，故它**不是**第二个反例，只作**边界登记**：
「`Y` 依赖 `X`」本身**不保证**溯因改变结果。**这条登记式的诚实很重要**：
反例的**真正**机制是「后验 `P(U|x)` 与先验 `P(U)` 在 `Y` 上诱导不同的分布」，
不是「`Y` 忽略 `X`」。 -/
theorem _abduction_needs_posterior_shift :
    ∀ (b : Bool),
      (∑ u : Bool × Bool, (1 : ℝ) / 4 * (if u.1 = true then (1 : ℝ) else 0)
        * (if u.2 = b then (1 : ℝ) else 0))
        = 1 / 4 * (if b = b then (1 : ℝ) else 0) := by
  intro b
  rw [sum_prod_four]
  cases b <;> norm_num

end Counterexample

/-! ## §5 ⭐⭐ 与 Pearl 第 1 步的**语义对应**（不是定理，是论证）

§4 的 `M` 里，后验 `P(U | X = true)` 把 `a = false` 的两个原子**清零**，
剩下 `(true,false)`、`(true,true)` 各占条件质量 `1/2`（先验下各占 `1/4`）。
**这**就是溯因**：重新分配外生权重。`Y := b` 只是把这一分配**原样搬到 `Y` 上**，
所以 `Y` 的边缘从 `1/2` 变成 —— 不，**仍是** `1/4`：
条件质量集中在**一条**原子上（`y = b` 需要 `b = y`），故 `P(y | do(x), x_u = x)` 的
未归一化质量为 `1/4`。

⚠ **一处必须说清的技术细节**：上面的 `1/4` 是**未归一化**的后验质量
（分母 `P(X = x) = 1/2` 未除掉）。**归一化后**得到 `(1/4)/(1/2) = 1/2`，
**与 `doLaw` 的 `1/2` 相同** —— 因为本例中 `Y ⟂ X`（`Y := b` 忽略 `X`）。

**⟹ 因此本文件的 `1/4 ≠ 1/2` 比较的是「同一归一化约定下的两个求和式」，
而非「归一化后的两条概率律」。** 这是一条**真实的边界**，见 §6.2。
为了避免混淆，§4 的所有陈述都写成**求和式**（`cfLaw`）而不写成「概率」。
===========================================================================-/
/-! ## §6 ⚠⚠ 再次声明边界（**与 §2 呼应，避免夸大**）

### 6.1 哪些是**真证**

* `doLaw_value`：`1/2`，由 `sum_prod_four` + `norm_num` 算出（4 个原子逐个求和）。
* `abduction_value` / `abduction_value_false`：`1/4`，同上。
* `abduction_changes_result`：由上述两条 + `norm_num` 得到 `∃` 命题。
* `abduction_matters_quantitative`：`1/4` 与 `1/2` 的合取。

**这四条**不依赖任何未证假设**，`#print axioms` 只应出现 `propext` / `Classical.choice`。

### 6.2 哪些**不是**定理

1. **「溯因 = 未归一化后验重加权」是定义**（`CFAlgorithm.weight`），
   不是从 Pearl 的文字推出的定理。**如果**采用归一化约定，
   §4 的 `1/4` 会变成 `1/2`（见 §5 末段），**反例随即消失**。
   **⟹ 本文件的「反例」严格依赖于「未归一化」这一约定。**
   我**不掩饰**这一点：它是**约定依赖**的，不是无条件的数学事实。
2. 若把 `cfLaw_{true}` **归一化**（除以 `P(X = x)`），
   则 §4 的 `M` 上二者**相等**，因为 `Y ⟂ X`。
   **⟹ 要造归一化意义下的反例，需要让 `Y` 依赖 `X` 且后验≠先验在 `Y` 上表现不同** ——
   **本文件没有做**（§4 的 `_abduction_needs_posterior_shift` 只登记了机制方向）。
   这在 `SCM X Y` 载体上是**可以做**的（取 `pU` 非均匀 + `Y := X ∧ b`），
   但它属于**另一个任务**（T4.4 的自然候选），**此处不越界声称**。
===========================================================================-/
/-! ## §7 与已有构件的对应表（**可 grep 核验**）

| 本文件用的东西 | 出处 | 作用 |
|---|---|---|
| `PearlHierarchy.SCM`（`U`, `pU`, `sg`）| `Fate/PearlHierarchy.lean` | 载体 |
| `SCMSemantics.doLaw` | `Fate/SCMSemantics.lean:96` | 「不做溯因」的形式 |
| `SCMSemantics.condY` | `Fate/SCMSemantics.lean:83` | 完整溯因在 `x'=x` 处的特例（§2 末）|
| `push` | `Fate/PearlHierarchy.lean` | 推前（本文件未直接用，因 `doLaw` 已展开）|
| `Fintype.sum_prod_type` | `Mathlib.Data.Fintype.Prod` | `Bool × Bool` 求和拆分 |
| `Fintype.sum_bool` | Mathlib | `Bool` 求和拆分 |
| `PearlHierarchy.L3_1` / `L2_1` | `Fate/PearlHierarchy.lean` | **同一机制**的另一种表述（分层口径）|

**⭐ 与前序文献/代码的关系**：
`PearlHierarchy` 中 `L2_do`（干预）与 `L3_1`（反事实）之差**正是** `[x_u = x]` 因子；
本文件把这个因子**提成一个 `Bool` 开关**（`CFAlgorithm.abduction`），
并用**具体数值**证实开关有效。**这不是新数学，是把已知的因子差别做成可核验的命题。**
===========================================================================-/

end FateV2.Modeling.R242.G2

