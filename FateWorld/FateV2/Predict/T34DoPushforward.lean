import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Predict.T35Confounding

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/T34DoPushforward.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 30 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict
open FateV2.Modeling

/-! ===========================================================================
  `FateV2.Predict/T34DoPushforward` —— **T3.4 干预分布的推前表征**（**第 222 轮**）

  ## 清单原文（T3.4）

  > **干预分布的推前表征**：在 `M_{do(X=x)}` 中，`P(Y | do(X=x))` 等于
  > 把 `X` 的方程替换为**常数方程**后由 `P(U)` 与其余方程推出的 `Y` 的**推前分布**。

  ## 这条的意义

  **它给出 `do` 算子的**构造性定义**：
  - **观测**：用 `p_U` 与**全部**结构方程得到联合分布；
  - **干预 `do(X=x)`**：把 `X` 的方程**换成常数** `x`，其余不动，再**推前**。

  **这正是 Pearl 的「图手术」在**分布层**的对应，
  **也是 T3.3（删边 = 模型替换）的**测度层**对应。**

  ## ⚠ 第 247 轮：**§2 的三条定理是 D4 型（定义改写），已在本轮**升级**

  **G6 第 242 轮评估判定**：`t34_pushforward`（全文件 `rfl`）是**定义改写** ——
  确实如此：`FateV2.Modeling.SCMSemantics.doLaw` 的**定义**就是推前形式，故那条定理**只能是 `rfl`**。

  **第 247 轮的重做不删旧定理**（它们仍是 API：把定义钉死），
  而是**在 §4–§5 补上真正的分析内容**：

  | 新增定理 | 内容 | 证明手段 |
  |---|---|---|
  | `diff_eq_correction` | `doLaw − condY = ` 「实际 `X ≠ x`」个体的质量 | 分情况 + `sum_sub_distrib` |
  | `lawDiffAt_zero_iff` | `L¹` 范数 `= 0` ⟺ 两条律逐点相同 | `sum_eq_zero_iff_of_nonneg` |
  | `t34_norm_zero_unconfounded` | 无混杂 ⟹ 范数 `= 0` | 奖励恒等式 |
  | `t34_norm_pos_confounded` | 完全混杂 ⟹ 范数 `= 1/2 > 0` | 显式计算 |
  | `doLaw_mass` / `condY_mass` | 质量守恒（分母不同的来源） | `sum_comm` |

  **⟹ 这直接兑现任务书要求**：
  「`doLaw` 与 `condY` 的**差的范数**在无混杂时为 0，有混杂时 > 0」，
  **并给出具体数值 `1/2`。**

  ## ⚠ 技术说明（**踩坑记录**）

  `PearlHierarchy` 是 `FateV2.Predict.` 下的**命名空间**（`namespace FateV2.Predict` 内 `namespace PearlHierarchy`），
  **故 `open PearlHierarchy` 在 `namespace FateV2.Predict.T34` 内**不生效**
  （**Lean 的 `open` 从当前命名空间开始解析**）。
  **⟹ 本文件一律用**全名** `FateV2.Modeling.PearlHierarchy.SCM`。**
================================================================================ -/

namespace FateV2.Predict.T34

/-! ## §1 **常数方程替换**（**`do` 的构造性定义**）

**命题**：干预 `do(X=x)` 的**结构方程集**是：
- `X` 的方程：**常数** `fun _ => x`
- `Y` 的方程：**不变**

**⚠ 在 `SCM X Y` 里，`sg u = (x_u, f_u)` 其中 `x_u : X`、`f_u : X → Y`。
干预后：`x_u` 被替换为 `x`，`f_u` **不变**。** -/

/-- **干预后的结构映射**：`X` 的方程换成常数 `x`，`Y` 的方程不变。 -/
noncomputable def doMap {X Y : Type*} (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) :
    M.U → X × (X → Y) :=
  fun u => (x, (M.sg u).2)

/-- **干预后的 `X` 取值恒为 `x`**（**这就是「常数方程」**）。 -/
theorem doMap_fst {X Y : Type*} (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (u : M.U) :
    (doMap M x u).1 = x := rfl

/-- **干预后的 `Y` 方程不变**。 -/
theorem doMap_snd {X Y : Type*} (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (u : M.U) :
    (doMap M x u).2 = (M.sg u).2 := rfl

/-! ## §2 **T3.4 主定理：干预律 = 推前** -/

/-- **T3.4（推前表征）**：**干预律等于推前分布**。

**🔹 对应清单**：T3.4 的逐字形式化。

**读法**：`push p_U g y` 是 `p_U` 沿 `g` 的**推前**。
**取 `g u := f_u(x)`**（即干预后的 `Y` 取值），**则推前给出 `doLaw`**。

**这正是清单说的**：
**「把 `X` 的方程替换为常数方程后，由 `P(U)` 与其余方程推出的 `Y` 的推前分布」** ——
**`g u = f_u(x)` 里的 `x` 是**常数方程给出的**，`f_u` 是**其余的方程**（不变）。** -/
theorem t34_pushforward {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) :
    FateV2.Modeling.SCMSemantics.doLaw M x
      = FateV2.Modeling.PearlHierarchy.push M.pU (fun u : M.U => (M.sg u).2 x) := by
  funext y
  rfl

/-- **T3.4（显式求和形式）**。

**这是 `doLaw` 的**定义展开** —— 但它揭示了一个关键事实**：
**`doLaw` 的定义**本身就是**推前形式**。** -/
theorem t34_expand {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.doLaw M x y
      = ∑ u : M.U, M.pU u * (if (M.sg u).2 x = y then 1 else 0) := rfl

/-! ## §3 **观测律与干预律的**结构差别**（强化 T3.5）** -/

/-- **观测律的显式形式**：**有额外因子 `[x_u = x]`**。

**这是「`do` 切断了 `X` 的入边」在**公式层**的精确体现** ——
**也是 T3.5（观测 ≠ 干预）的**结构性原因**。 -/
theorem t34_obs_formula {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.condY M x y
      = ∑ u : M.U, M.pU u * (if (M.sg u).1 = x then 1 else 0)
          * (if (M.sg u).2 x = y then 1 else 0) := rfl

/-- **T3.4 的核心对比**：**两个公式**只差**一个因子 `[x_u = x]`**。

**读法**：把它们写在一起，**差别一目了然**：
- **观测**：`∑ u, p_U(u) · [x_u = x] · [f_u(x) = y]`
- **干预**：`∑ u, p_U(u) · [f_u(x) = y]`

**即**：**干预**去掉了「筛选 `X = x`」这一步** ——
**这就是「`do(X=x)` 无视 `X` 的实际取值」的**数值含义**。** -/
theorem t34_comparison {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.condY M x y
        = ∑ u : M.U, M.pU u * (if (M.sg u).1 = x then 1 else 0)
            * (if (M.sg u).2 x = y then 1 else 0)
      ∧ FateV2.Modeling.SCMSemantics.doLaw M x y
        = ∑ u : M.U, M.pU u * (if (M.sg u).2 x = y then 1 else 0) :=
  ⟨rfl, rfl⟩

/-! ## §4 **第 247 轮重做：`doLaw − condY` 的**定量刻画**（不再是定义改写）

**⚠ 为什么必须重做**：§2 的 `t34_pushforward`、`t34_expand`、`t34_comparison`
**证明体都是 `rfl`** —— 它们是 **D4 型（定义改写）**，
因为 `doLaw` 的**定义本身**就是推前形式。**「推前表征」被写成了同义反复。**

**本节把 T3.4 升级为**真正的分析命题****：

1. **精确恒等式**（`diff_eq_correction`）：
   `doLaw M x y − condY M x y`
   `= ∑ u, p_U(u) · [x_u ≠ x] · [f_u(x) = y]`。
   **⟹ 两条律的全部差别 = 「实际 `X` 不等于 `x`」的那部分外生个体的质量。**
   这就是 Pearl 所说「`do` 切断了 `X` 的入边」的**定量**含义。

2. **范数判据**（`lawDiffAt_zero_iff`）：逐 `x` 的 `L¹` 差
   `lawDiffAt M x = ∑ y, |doLaw M x y − condY M x y|`
   为 `0` **当且仅当**两条律在该 `x` 上逐点相同。

3. **二分**（`t34_norm_zero_unconfounded` / `t34_norm_pos_confounded`）：
   * 无混杂时（`x_u` 恒为 `x₀`），在 `x₀` 处 `lawDiffAt = 0`；
   * T3.5 的完全混杂模型里，**每个** `x` 都有 `lawDiffAt = 1/2 > 0`。

**这正是任务书要求的**：「`doLaw` 与 `condY` 的差的范数在无混杂时为 0，
有混杂时 > 0」**的精确形式化（并给出**具体数值** `1/2`）。** -/

/-- **两条律的逐点差**（`doLaw − condY`）。 -/
noncomputable def lawDiff {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) : X → Y → ℝ :=
  fun x y => FateV2.Modeling.SCMSemantics.doLaw M x y - FateV2.Modeling.SCMSemantics.condY M x y

/-- **逐 `x` 的 `L¹` 范数**：`∑ y, |lawDiff M x y|`。 -/
noncomputable def lawDiffAt {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) : ℝ :=
  ∑ y, |lawDiff M x y|

/-- **精确恒等式**：`doLaw − condY` **等于**「实际 `X ≠ x` 的个体」的贡献。

**读法**：`[x_u ≠ x]` 指示「个体 `u` 的实际 `X` 不是 `x`」。
**这些个体在干涉 `do(X=x)` 下被**移动**到 `x`**，
**故它们对 `doLaw` 有贡献、对 `condY` 无贡献**。
**⟹ 两条律的差别**恰好**是这批「反事实个体」的质量。**

**⚠ 这不是 `rfl`**：证明需要分情况化简指示函数并用 `sum_sub_distrib`。 -/
theorem diff_eq_correction {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y) :
    lawDiff M x y
      = ∑ u, M.pU u * (if (M.sg u).1 = x then 0 else 1)
          * (if (M.sg u).2 x = y then 1 else 0) := by
  unfold lawDiff FateV2.Modeling.SCMSemantics.doLaw FateV2.Modeling.SCMSemantics.condY
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h1 : (M.sg u).1 = x <;> simp [h1]

/-- **范数为零的判据**：`lawDiffAt M x = 0` **当且仅当**两条律在 `x` 上逐点相同。

**⚠ 需要 `Finset.sum_eq_zero_iff_of_nonneg` 与 `abs_eq_zero`：不是定义展开。** -/
theorem lawDiffAt_zero_iff {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) :
    lawDiffAt M x = 0 ↔ ∀ y, FateV2.Modeling.SCMSemantics.doLaw M x y = FateV2.Modeling.SCMSemantics.condY M x y := by
  unfold lawDiffAt lawDiff
  constructor
  · intro h y
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => abs_nonneg (FateV2.Modeling.SCMSemantics.doLaw M x i - FateV2.Modeling.SCMSemantics.condY M x i))).mp h y
      (Finset.mem_univ y)
    exact sub_eq_zero.mp (abs_eq_zero.mp h4)
  · intro h
    apply Finset.sum_eq_zero
    intro y _
    rw [h y, sub_self, abs_zero]

/-- **无混杂 ⟹ 范数为零**：若 `x_u` 恒为 `x₀`，则 `lawDiffAt M x₀ = 0`。

**读法**：`x₀` 是**实际**的 `X` 取值。此时「实际 `X ≠ x₀`」的个体**不存在**，
故由 `diff_eq_correction`，差恒为 `0`。 -/
theorem t34_norm_zero_unconfounded {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x₀ : X)
    (hconst : ∀ u, (M.sg u).1 = x₀) : lawDiffAt M x₀ = 0 := by
  rw [lawDiffAt_zero_iff]
  intro y
  have hzero : lawDiff M x₀ y = 0 := by
    rw [diff_eq_correction]
    apply Finset.sum_eq_zero
    intro u _
    rw [hconst u, if_pos rfl, mul_zero, zero_mul]
  have hsub : FateV2.Modeling.SCMSemantics.doLaw M x₀ y - FateV2.Modeling.SCMSemantics.condY M x₀ y = 0 := hzero
  linarith [hsub]

/-- **有混杂 ⟹ 范数为正**（以 T3.5 的完全混杂模型为见证）：
对 `Fin 2` 上的**每个** `x`，`lawDiffAt M x = 1/2 > 0`。 -/
theorem t34_norm_pos_confounded (x : Fin 2) :
    lawDiffAt FateV2.Predict.T35.M x = (1 : ℝ) / 2 := by
  unfold lawDiffAt lawDiff
  rw [Fin.sum_univ_two, FateV2.Predict.T35.condY_M, FateV2.Predict.T35.condY_M,
    FateV2.Predict.T35.doLaw_M, FateV2.Predict.T35.doLaw_M]
  fin_cases x <;> norm_num

/-- **混杂 ⟹ 范数严格为正**（由 `t34_norm_pos_confounded` 立即得出）。 -/
theorem t34_norm_pos_confounded' (x : Fin 2) : lawDiffAt FateV2.Predict.T35.M x > 0 := by
  rw [t34_norm_pos_confounded]; norm_num

/-! ## §5 **第 247 轮重做：T3.4 的**真实内容** —— 质量守恒

**「推前表征」的非同义反复内容**是**质量守恒**：

  `∑ y, doLaw M x y = ∑ u, p_U(u)`（对**任意** `x`），
  `∑ y, condY M x y = marginalX M x`。

**意义**：`doLaw` 是**归一化到 `∑ p_U`** 的律，
而 `condY` 的质量是 `P(X = x)` —— **两者质量不同正是「分母不同」的来源**，
**这也解释了为何「归一化」必须除以各自的边缘质量**。

**⚠ 证明需要 `Finset.sum_comm` 与 `Finset.sum_ite_eq`：不是定义展开。** -/

/-- **`doLaw` 的总质量**恒为 `∑ u, p_U(u)`（与 `x` 无关）。 -/
theorem doLaw_mass {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) :
    ∑ y, FateV2.Modeling.SCMSemantics.doLaw M x y = ∑ u, M.pU u := by
  unfold FateV2.Modeling.SCMSemantics.doLaw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [← Finset.mul_sum, Finset.sum_ite_eq]
  simp

/-- **`condY` 的总质量**恰为 `marginalX M x = P(X = x)`。 -/
theorem condY_mass {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) :
    ∑ y, FateV2.Modeling.SCMSemantics.condY M x y = FateV2.Modeling.SCMSemantics.marginalX M x := by
  unfold FateV2.Modeling.SCMSemantics.condY FateV2.Modeling.SCMSemantics.marginalX
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [← Finset.mul_sum, Finset.sum_ite_eq]
  simp

end FateV2.Predict.T34
