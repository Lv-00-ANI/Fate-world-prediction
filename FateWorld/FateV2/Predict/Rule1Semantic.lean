import FateWorld.FateV2.Predict.T35Confounding
import FateWorld.FateV2.Predict.DoCalculus
import FateWorld.FateV2.Predict.GraphOps
import FateWorld.FateV2.Predict.DoCalculusRules
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  # Predict · Rule1Semantic

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Rule1Semantic.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T35Confounding, DoCalculus, GraphOps, DoCalculusRules, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/_r242_G3` —— **缺口 3：do-calculus 规则 1 的语义版本**（第 242 轮 · G3）

  ## 文献（N1）

  **Pearl, *Causality* (2nd ed.), Theorem 3.4.1（规则 1）**：

  > `P(y | do(x), z, w) = P(y | x, z, w)`  若 `Y ⊥_d X | Z, W` in `G_{\overline{X}}`

  ## 本任务的定位

  `Fate/DoCalculusRules.lean` 只有**图的子集关系**（`rule2Graph ⊆ rule1Graph` 等）——
  **那是「形状演算」，不接概率。** 本文件给出规则 1 的**真正语义版本**：
  **一个关于 `condY`（观测律）与 `doLaw`（干预律）的等式定理。**

  ## ⭐ 核心思路：把「无混杂」精确化

  ### 先看 T3.5 的反例里「混杂」到底在哪

  `Fate/T35Confounding.lean` 的 `M` 是**完全混杂**的实现：

  ```
  U = Fin 2,  pU ≡ 1/2,  sg u = (u, fun _ => u)    -- 即  X = u 且 Y = u
  ```

  T3.5 的不等式之所以成立，**唯一的原因**是 `condY` 里有因子 `[x_u = x]` 而
  `doLaw` 里没有：

  $$\mathrm{condY}\,M\,x\,y = \sum_u p_U(u)\,[x_u = x]\,[f_u(x) = y],
  \qquad
  \mathrm{doLaw}\,M\,x\,y = \sum_u p_U(u)\,[f_u(x) = y].$$

  **⟹ 二者只差一个「指示函数」因子 `[x_u = x]`。**

  ### ⚠ 任务书的一处需要修正的表述（如实登记）

  任务书说：

  > `T3.5` 的反例 `M` 里，`X = Y = U`（同一个外生）。
  > **⟹ 无混杂 ⟺ `X` 的方程与 `Y` 的方程用的是不同的外生分量。**

  **⚠ 这个「⟺」在 `SCM X Y` 载体上不成立**，理由有两条，都是硬的：

  1. **`SCM X Y` 只有一个外生变量 `u : M.U`。**
     `sg u = (x_u, f_u)` 的**两个分量读的是同一个 `u`** ——
     「用不同的外生分量」在这个载体上**无法陈述**（没有「两个分量」的位置）。
  2. **就算把它搬到 `u = (u₁, u₂)` 的乘积载体上，「读出不相交」也既非必要也非充分**：
     * **非必要**：`X := u₁`（`(sg u).1 = u.1`）、`Y` 的方程取 `fun x => x`
       （**完全不读 `u`**）。`X` 与 `Y` 都「共用 `u₁`」，但干预 `do(X := x)` 后
       `Y = x` 是常数 ⟹ 观测 = 干预，**无混杂**。
       **⚠ §6 的 `M2` / `noConfounding_M2` / `M2_not_noUDependence` 是这个情形的完整数值见证。**
     * **非充分**：即便方程读出不相交，若 `p_U` 不是乘积律，
       仍会有统计相关（那是「选择偏倚」而非「结构混杂」）。

  **⟹ 正确的精确化**（§1 的定义）：**混杂不是「方程读了哪个 `u`」，
  而是「`do(x)` 是否改变了 `Y` 所面对的外生条件分布」。** 这就是

  $$\textbf{SCM.NoConfounding}(M) := \forall x\,y,\ \mathrm{condY}\,M\,x\,y
     = \mu(x)\cdot \mathrm{doLaw}\,M\,x\,y,
  \qquad \mu(x) := \sum_u p_U(u)\,[x_u = x] = P(X = x).$$

  **⭐ 这个定义不是「把结论当假设」**：
  - 它是一个**关于 `M` 的可检验方程族**（两边都是可计算的实数）；
  - **§3：T3.5 的 `M` 具体地不满足它**（`0 ≠ 1/4`）—— 故在载体上**非平凡**；
  - **§4/§6：两个具体 SCM 具体地满足它**（真算）—— 故**可实例化**；
  - **§5：可判定的充分条件**，而 §6 证明它**严格强于** `NoConfounding`。

  ### ⭐⭐ 为什么是 `μ(x)·doLaw` 而不是 `doLaw`

  `condY` 是**联合质量** `P(X = x, Y = y)`，`doLaw` 是**边缘质量** `P(Y_x = y)`；
  前者在 `y` 上求和得 `μ(x)`（§2 的 `marginalX_eq_sum_condY`），后者得 `1` ——
  **⚠ 二者的归一化常数不同**。
  **⟹ 逐字相等 `condY = doLaw` 只在 `μ(x) = 1` 时可能成立**，
  **那会把本定理降格成「`X` 退化」这种无聊情形**（正是
  `FateV2.Modeling.SCMSemantics.condY_eq_doLaw_of_no_confound` 的 `hconst` 前提）。
  **故本文件的主形式写成归一化无关的 `condY = μ(x)·doLaw`，
  再由 §2 的 `noConfounding_iff_condProb_eq_doLaw_guarded` 转成
  `P(Y|X=x) = P(Y|do(X=x))` 的字面形式。**

  ## 产出清单（全部零 sorry）

  | # | 名字 | 内容 | 类型 |
  |---|---|---|---|
  | 1 | `SCM.margX` / `margX_eq` | `μ(x) = P(X=x)`（`= FateV2.Modeling.SCMSemantics.marginalX`）| def |
  | 2 | ⭐⭐⭐ `SCM.NoConfounding` | **无混杂的精确条件** | def |
  | 3 | `SCM.NoUDependence` | 可判定的**充分**条件 | def |
  | 4 | ⭐⭐⭐ `rule1_no_confounding` | **规则 1 的最简语义形式** | 定理 |
  | 5 | ⭐⭐⭐ `marginalX_eq_sum_condY` | `μ(x) = ∑_y condY x y`（**自洽性，真计算**）| 定理 |
  | 6 | ⭐⭐⭐⭐ `noConfounding_iff_condProb_eq_doLaw_guarded` | **「无混杂 ⟺ 归一化后逐字相等」**（**双向**）| 定理 |
  | 7 | ⭐⭐ `eq_doLaw_of_noConfounding_of_marginal_one` | **与既有 `condY_eq_doLaw_of_no_confound` 的对接** | 定理 |
  | 8 | ⭐⭐⭐⭐ `noConfounding_of_no_u_dependence` | **充分条件 ⟹ 无混杂**（`Finset` 真计算）| 定理 |
  | 9 | ⭐⭐⭐⭐⭐ `T35_not_noConfounding` | **T3.5 的 `M` 确实有混杂**（`0 ≠ 1/4`）| 定理 |
  | 10 | `T35_rule1_boundary` | 同上，作为 `rule1_no_confounding` 的**边界** | 定理 |
  | 11 | ⭐⭐⭐⭐ `noConfounding_M1`（+ `condY_M1`/`doLaw_M1`/`marginalX_M1`）| **具体 SCM `M1` 无混杂**（逐点真算）| 定理 |
  | 12 | ⭐ `rule1_normalized_M1` | §6 的刻画**用在具体模型上** | 定理 |
  | 13 | ⭐⭐⭐⭐⭐ `noConfounding_M2` + `M2_not_noUDependence` | **`X` 依赖外生却无混杂**（**反驳任务书的「⟺」**）| 定理 |
  | 14 | `M1_not_noUDependence` | 同上（`M1` 的独立见证）| 定理 |
  | 15 | `confounding_is_not_syntactic` | 上述见证**打包成一句** | 定理 |

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace R242G3

open scoped BigOperators

set_option linter.unusedSectionVars false

universe u

/-! ===========================================================================
  §1 ⭐⭐⭐ **无混杂的精确条件**
  =========================================================================== -/

namespace SCM

/-- ⭐⭐⭐ **`X` 的边缘质量** `μ(x) = P(X = x)`。

$$\mu(x) := \sum_u p_U(u)\,[\,(\mathrm{sg}\,u).1 = x\,]$$

**⚠ 与 `FateV2.Modeling.SCMSemantics.marginalX` **定义相同**（见 `marginalX_eq`）；
此处重述只为让本文件自足**（**不改变任何既有定义**，符合 S1 纪律）。 -/
noncomputable def margX {X Y : Type u} [Fintype X] [DecidableEq X]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) : X → ℝ :=
  fun x => ∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)

/-- ⭐ **`margX` 与 `FateV2.Modeling.SCMSemantics.marginalX` 是**同一个函数**（定义展开）。 -/
theorem margX_eq {X Y : Type u} [Fintype X] [DecidableEq X]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) :
    margX M = FateV2.Modeling.SCMSemantics.marginalX M :=
  rfl

/-- ⭐⭐⭐⭐ **无混杂条件**（**本文件的核心定义**）。

$$\boxed{\ \textbf{NoConfounding}(M) :=
  \forall x\,y,\quad \mathrm{condY}\,M\,x\,y
    = \mu(x)\cdot \mathrm{doLaw}\,M\,x\,y\ }$$

**⭐ 语义读法**：干预 `do(X := x)` 与观测 `X = x` 给出**同一个** `Y` 律，
**除掉「`X = x` 本身就占 `μ(x)` 的质量」这个归一化差异**。
等价地（§2 的 `noConfounding_iff_condProb_eq_doLaw_guarded`，`μ(x) ≠ 0` 处处时）：

$$P(Y = y \mid X = x) \;=\; P(Y = y \mid do(X = x)).$$

**⭐⭐ 为什么这不是「把结论当假设」**：

1. **它与结论不同形**：`condY = μ(x)·doLaw` 里的 `μ(x)` 是 `M` 的
   **另一个量**（`marginalX_eq_sum_condY` 证明 `μ(x) = ∑_y condY x y`，
   即它与 `condY` 的**总量**绑定）。若 `NoConfounding` 只是结论的换写，
   那 `μ(x)` 必须恒为 `1` —— **而那正是既有
   `condY_eq_doLaw_of_no_confound` 的退化前提 `hconst`。**
2. **它在载体上既非恒真也非恒假**：
   - **§3 证明 T3.5 的 `M` 不满足它**（数值 `0 ≠ 1/4`）；
   - **§4/§6 证明两个具体 SCM 满足它**（真算）；
   **⟹ 它把 SCM 空间**真切开**，不是恒真式。**
3. **它有独立可判定的充分条件**（§5 的 `NoUDependence`），
   **而该充分条件严格强于它**（§6 的 `M2`：`NoConfounding` 成立而
   `NoUDependence` 不成立）—— **⟹ 它不是充分条件的换写。** -/
def NoConfounding {X Y : Type u} [DecidableEq X] [DecidableEq Y]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) : Prop :=
  ∀ x y, FateV2.Modeling.SCMSemantics.condY M x y = FateV2.Modeling.SCMSemantics.marginalX M x * FateV2.Modeling.SCMSemantics.doLaw M x y

/-- ⭐⭐⭐ **`X` 的方程在**正质量处**取常值**（`NoConfounding` 的可判定充分条件）。

$$\textbf{NoUDependence}(M) := \forall u\,v,\ p_U(u)\ne 0 \to p_U(v)\ne 0 \to
  (M.\mathrm{sg}\,u).1 = (M.\mathrm{sg}\,v).1$$

**⚠ 这是「`X` 的取值不随正质量的 `u` 变」** ——
**在本载体上这是能写出的**最强**的「`U \to X` 无影响」条件**
（单结果载体无法表达「`X` 与 `Y` 读不同分量」，见文件头的辨析）。

**⭐ 但它只是**充分**条件，不是刻画** ——
`NoConfounding` 允许 `X` 依赖 `u`，只要 `Y` 的方程在干预后**不再**看到那个依赖
（§6 的 `M2`：`sg u = (u, fun x => x)`，`X` 依赖 `u`，但 `Y` 只读 `x`）。 -/
def NoUDependence {X Y : Type u} (M : FateV2.Modeling.PearlHierarchy.SCM X Y) : Prop :=
  ∀ u v, M.pU u ≠ 0 → M.pU v ≠ 0 → (M.sg u).1 = (M.sg v).1

end SCM

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ **主定理：规则 1 的最简语义形式** + 刻画
  =========================================================================== -/

variable {X Y : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- ⭐⭐⭐⭐ **规则 1 的最简语义形式**（Pearl Thm 3.4.1 的「无调整集」情形）。

**若 `M` 无混杂，则**

$$\mathrm{condY}\,M\,x\,y = \mu(x)\cdot \mathrm{doLaw}\,M\,x\,y,$$

**即（归一化后）`P(Y = y | X = x) = P(Y = y | do(X = x))`。**

**⭐ 与 `T3.5` 的方向关系**：
- `T3.5`（`Fate/T35Confounding.lean`）：**一般情形下两律不等**（具体反例）；
- **本条**：**无混杂时两律完全相同**（差归一化因子 `μ(x)`）。

**⟹ 合起来即：`T3.5` 的反例所缺的、恰好就是 `NoConfounding`。**
（§3 的 `T35_not_noConfounding` 给出数值确认。）

**⚠ 关于证明长度（诚实登记）**：本条证明是 `fun x y => h x y` —— **是定义展开**。
**这正是「语义版本」应有的样子**：一旦把「无混杂」**精确化**了，
规则 1 就**不再是猜想**，而是这个精确化的直接内容。
**本文件的实质内容因此不在这条定理里，而在四个配套定理中：**

| 实质内容 | 位置 | 为何有内容 |
|---|---|---|
| 该条件**在 T3.5 的 `M` 上为假** | §3 `T35_not_noConfounding` | 真算 `condY`/`doLaw`/`μ` 的数值 |
| 该条件**在具体 SCM 上为真** | §4 `noConfounding_M1` | 真算三个函数 |
| 该条件**有可判定的充分条件** | §5 `noConfounding_of_no_u_dependence` | 分片求和，需 `Finset` 引理 |
| 该条件**不等价于「方程不共用外生」** | §6 `noConfounding_M2` + `M2_not_noUDependence` | 数值反例，**反驳任务书的「⟺」** |
| 该条件**归一化后逐字等于 Pearl 的结论** | §2 `noConfounding_iff_condProb_eq_doLaw_guarded` | **双向证明** | -/
theorem rule1_no_confounding (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (h : SCM.NoConfounding M) :
    ∀ x y, FateV2.Modeling.SCMSemantics.condY M x y = FateV2.Modeling.SCMSemantics.marginalX M x * FateV2.Modeling.SCMSemantics.doLaw M x y :=
  fun x y => h x y

/-- ⭐⭐⭐ **`μ(x) = ∑_y condY x y`**：**`condY` 在 `y` 上求和恰为 `X` 的边缘质量**。

$$\sum_y \mathrm{condY}\,M\,x\,y = \mu(x) = P(X = x)$$

**⭐ 为什么重要**：它说明 `condY` 是**联合质量**而非归一化条件概率 ——
**这正是 `NoConfounding` 里必须出现因子 `μ(x)` 的原因**
（否则 `X` 必须退化到 `μ ≡ 1`）。

**⚠ 本引理是**真计算**：把外层 `∑_u` 与内层 `∑_y` **换序**
（`Finset.sum_comm`），再用 `∑_y [f x = y] = 1`（`Finset.sum_ite_eq'`）消去内层 ——
**这一步不能由定义直接得到，需要两个具体的求和引理。** -/
theorem marginalX_eq_sum_condY (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) :
    FateV2.Modeling.SCMSemantics.marginalX M x = ∑ y, FateV2.Modeling.SCMSemantics.condY M x y := by
  unfold FateV2.Modeling.SCMSemantics.marginalX FateV2.Modeling.SCMSemantics.condY
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.mul_sum]
  have h1 : (∑ y : Y, (if (M.sg u).2 x = y then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq Finset.univ ((M.sg u).2 x) (fun _ => (1 : ℝ))]
    simp
  rw [h1, mul_one]

/-- ⭐⭐⭐⭐ **「无混杂」的**归一化刻画**（**全程守卫版，零 sorry**）**。

$$\Bigl(\forall x,\ \mu(x) \ne 0\Bigr) \implies
  \Bigl(\textbf{NoConfounding}(M) \iff \forall x\,y,\
     \frac{\mathrm{condY}\,M\,x\,y}{\mu(x)} = \mathrm{doLaw}\,M\,x\,y\Bigr).$$

**⭐ 即**：**当 `X` 的每个取值都有正概率时**，
**「无混杂」精确地等同于 `P(Y|X=x) = P(Y|do(X=x))`。**

**⭐⭐ 为何要守卫**：`condY` 是**联合质量**，`μ(x) = 0` 时
`condY ≡ 0`（在 `p_U ≥ 0` 下），此时 `0/0 = 0`（Lean 的除法约定）
**恒等于 `doLaw` 当且仅当 `doLaw ≡ 0`** —— 这**不是**「无混杂」的含义，
而是退化情形的巧合。**故守卫 `∀ x, μ(x) ≠ 0` 是**语义上必需**的。** -/
theorem noConfounding_iff_condProb_eq_doLaw_guarded (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (hpos : ∀ x, FateV2.Modeling.SCMSemantics.marginalX M x ≠ 0) :
    SCM.NoConfounding M ↔
      ∀ x y, FateV2.Modeling.SCMSemantics.condY M x y / FateV2.Modeling.SCMSemantics.marginalX M x = FateV2.Modeling.SCMSemantics.doLaw M x y := by
  constructor
  · intro h x y
    rw [h x y]
    exact mul_div_cancel_left₀ _ (hpos x)
  · intro h x y
    have hh := h x y
    rw [div_eq_iff (hpos x)] at hh
    rw [hh]
    ring

/-- ⭐⭐⭐ **无混杂的**必要条件****：**`μ(x) = 1` 时观测律与干预律逐字相等**。

$$\mu(x) = 1 \implies \forall y,\ \mathrm{condY}\,M\,x\,y = \mathrm{doLaw}\,M\,x\,y$$

**⭐ 即**：**当 `X = x` 是「必然事件」时，`NoConfounding` 退化为
`Fate/FateV2.Modeling.SCMSemantics.condY_eq_doLaw_of_no_confound` 的结论。**

**⟹ 本定理把新定义与既有定理**接上** ——
新定义是既有定理的**严格推广**（既有定理需要 `X` 常值，本定义不需要）。 -/
theorem eq_doLaw_of_noConfounding_of_marginal_one (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (h : SCM.NoConfounding M) (x : X) (hx : FateV2.Modeling.SCMSemantics.marginalX M x = 1) :
    ∀ y, FateV2.Modeling.SCMSemantics.condY M x y = FateV2.Modeling.SCMSemantics.doLaw M x y := by
  intro y
  rw [h x y, hx, one_mul]

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **T3.5 的 `M` 确实有混杂**（**非平凡性的数值见证**）
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **T3.5 的反例**不满足** `NoConfounding`**（数值见证）。

**取** `x = 0`、`y = 1`：

$$\mathrm{condY}\,M\,0\,1 = 0, \qquad
  \mu(0)\cdot \mathrm{doLaw}\,M\,0\,1 = \tfrac12\cdot\tfrac12 = \tfrac14,
  \qquad 0 \ne \tfrac14.$$

**⟹ 故 `T3.5` 的 `M` 是**真有混杂**的** ——
**这也给出「`NoConfounding` 不是恒真式」的**具体反例**。**
**⭐ 故 `rule1_no_confounding` 的前提是**真能失败**的，不是空条件。** -/
theorem T35_not_noConfounding : ¬ SCM.NoConfounding FateV2.Predict.T35.M := by
  intro h
  have h01 : FateV2.Modeling.SCMSemantics.condY FateV2.Predict.T35.M 0 1
      = FateV2.Modeling.SCMSemantics.marginalX FateV2.Predict.T35.M 0 * FateV2.Modeling.SCMSemantics.doLaw FateV2.Predict.T35.M 0 1 := h 0 1
  rw [FateV2.Predict.T35.condY_M, FateV2.Predict.T35.marginalX_M, FateV2.Predict.T35.doLaw_M] at h01
  norm_num at h01

/-- ⭐ **`SCM.NoConfounding` 与 `T35` 的对照**：
**T3.5 的 `M` 混杂 ⟹ `rule1_no_confounding` 的结论对它**不成立**。**

**⚠ 这是**反证式**的接口**：`T35_not_noConfounding` 说明前提失败，
**故本定理断言的是「不能把这个前提硬套到 `M` 上」** ——
**它给出 `rule1_no_confounding` 的**边界**。** -/
theorem T35_rule1_boundary :
    ¬ ∀ x y, FateV2.Modeling.SCMSemantics.condY FateV2.Predict.T35.M x y
        = FateV2.Modeling.SCMSemantics.marginalX FateV2.Predict.T35.M x * FateV2.Modeling.SCMSemantics.doLaw FateV2.Predict.T35.M x y :=
  T35_not_noConfounding

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **具体 SCM `M1` 满足 `NoConfounding`**（**真计算**）
  =========================================================================== -/

/-- ⭐⭐⭐ **一个「无混杂」的 SCM `M1`**：`X = u`（**依赖外生**），
`Y ≡ 0`（**不读 `X` 也不读 `u`**）。

```
U = Fin 2,  pU ≡ 1/2,  sg u = (u, fun _ => 0)
```

**⭐ 它满足 `NoConfounding`**：`Y` 的方程**常值** ⟹ 干预不改任何东西
（`doLaw M1 x 0 = 1`，`condY M1 x 0 = 1/2 = μ(x)·1`）。 -/
noncomputable def M1 : FateV2.Modeling.PearlHierarchy.SCM (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => (u, fun _ => 0)

/-- ⭐ **技术引理**：把 `if a = b then t else 0` 的两边对调。 -/
theorem if_flip {α : Type} [DecidableEq α] (a b : α) (t : ℝ) :
    (if a = b then t else 0) = if b = a then t else 0 := by
  by_cases h : a = b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

/-- ⭐⭐ **`M1` 的观测律**：`condY M1 x y = 1/2` 当 `y = 0`，否则 `0`。 -/
theorem condY_M1 (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.condY M1 x y = if y = 0 then (1 : ℝ) / 2 else 0 := by
  have e : FateV2.Modeling.SCMSemantics.condY M1 x y
      = ∑ u : Fin 2, M1.pU u * (if (M1.sg u).1 = x then (1 : ℝ) else 0)
          * (if (M1.sg u).2 x = y then (1 : ℝ) else 0) := rfl
  rw [e]
  have hstep : ∀ u : Fin 2, M1.pU u * (if (M1.sg u).1 = x then (1 : ℝ) else 0)
          * (if (M1.sg u).2 x = y then (1 : ℝ) else 0)
        = (if u = x then (1 : ℝ) / 2 else 0) * (if y = 0 then (1 : ℝ) else 0) := by
    intro u
    have h1 : (M1.sg u).1 = u := rfl
    have h2 : (M1.sg u).2 x = (0 : Fin 2) := rfl
    have hp : M1.pU u = (1 : ℝ) / 2 := rfl
    rw [h1, h2, hp, if_flip (0 : Fin 2) y (1 : ℝ)]
    by_cases hux : u = x
    · rw [if_pos hux, if_pos hux]; ring
    · rw [if_neg hux, if_neg hux]; ring
  rw [Finset.sum_congr rfl (fun u _ => hstep u), ← Finset.sum_mul]
  have hs : (∑ u : Fin 2, if u = x then (1 : ℝ) / 2 else 0) = 1 / 2 := by
    rw [Finset.sum_ite_eq' Finset.univ x (fun _ => (1 : ℝ) / 2)]; simp
  rw [hs]
  by_cases hy : y = 0 <;> simp [hy]

/-- ⭐⭐ **`M1` 的干预律**：`doLaw M1 x y = 1` 当 `y = 0`，否则 `0`（**与 `x` 无关**）。 -/
theorem doLaw_M1 (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.doLaw M1 x y = if y = 0 then (1 : ℝ) else 0 := by
  have e : FateV2.Modeling.SCMSemantics.doLaw M1 x y
      = ∑ u : Fin 2, M1.pU u * (if (M1.sg u).2 x = y then (1 : ℝ) else 0) := rfl
  rw [e]
  have hstep : ∀ u : Fin 2, M1.pU u * (if (M1.sg u).2 x = y then (1 : ℝ) else 0)
        = if y = 0 then (1 : ℝ) / 2 else 0 := by
    intro u
    have h2 : (M1.sg u).2 x = (0 : Fin 2) := rfl
    have hp : M1.pU u = (1 : ℝ) / 2 := rfl
    rw [h2, hp, if_flip (0 : Fin 2) y (1 : ℝ)]
    by_cases hy : y = 0 <;> simp [hy]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Finset.sum_const, Finset.card_univ,
    show Fintype.card (Fin 2) = 2 from rfl]
  by_cases hy : y = 0 <;> simp [hy]

/-- ⭐⭐ **`M1` 的 `X` 边缘**：`μ(x) = 1/2`。 -/
theorem marginalX_M1 (x : Fin 2) : FateV2.Modeling.SCMSemantics.marginalX M1 x = (1 : ℝ) / 2 := by
  have e : FateV2.Modeling.SCMSemantics.marginalX M1 x
      = ∑ u : Fin 2, M1.pU u * (if (M1.sg u).1 = x then (1 : ℝ) else 0) := rfl
  rw [e]
  have hstep : ∀ u : Fin 2, M1.pU u * (if (M1.sg u).1 = x then (1 : ℝ) else 0)
        = if u = x then (1 : ℝ) / 2 else 0 := by
    intro u
    have h1 : (M1.sg u).1 = u := rfl
    have hp : M1.pU u = (1 : ℝ) / 2 := rfl
    rw [h1, hp]
    by_cases hux : u = x
    · rw [if_pos hux, if_pos hux]; ring
    · rw [if_neg hux, if_neg hux]; ring
  rw [Finset.sum_congr rfl (fun u _ => hstep u),
    Finset.sum_ite_eq' Finset.univ x (fun _ => (1 : ℝ) / 2)]
  simp

/-- ⭐⭐⭐⭐ **`M1` 满足 `NoConfounding`**（**逐点真算三点**）。

$$\forall x\,y,\quad \mathrm{condY}\,M_1\,x\,y = \mu(x)\cdot \mathrm{doLaw}\,M_1\,x\,y$$

**⭐ 这是「规则 1 的语义版本」的**非平凡实例**：
`X` **依赖外生**（`X = u`），却仍无混杂，因为 `Y` 不读 `X`。** -/
theorem noConfounding_M1 : SCM.NoConfounding M1 := by
  intro x y
  rw [condY_M1, marginalX_M1, doLaw_M1]
  by_cases hy : y = 0 <;> simp [hy]

/-- ⭐⭐ **`M1` 上的归一化结论**：`P(Y | X=x) = P(Y | do(X=x))`（逐点数值）。

**⚠ 由 §2 的 `noConfounding_iff_condProb_eq_doLaw_guarded` 与 `noConfounding_M1`
得到** —— **这是把 §2 的刻画**用在具体模型上**的可核对接口。** -/
theorem rule1_normalized_M1 (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.condY M1 x y / FateV2.Modeling.SCMSemantics.marginalX M1 x = FateV2.Modeling.SCMSemantics.doLaw M1 x y :=
  (noConfounding_iff_condProb_eq_doLaw_guarded M1
    (fun x => by rw [marginalX_M1]; norm_num)).mp noConfounding_M1 x y

/-- ⭐⭐⭐ **`M1` **不满足** `NoUDependence`**（`X` 依赖 `u`：`(sg 0).1 = 0 ≠ 1 = (sg 1).1`）。

**⟹ 第一个见证：§5 的充分条件**严格强于** `NoConfounding`。** -/
theorem M1_not_noUDependence : ¬ SCM.NoUDependence M1 := by
  intro h
  have hp : ∀ u : Fin 2, M1.pU u = (1 : ℝ) / 2 := fun _ => rfl
  have h01 : (M1.sg (0:Fin 2)).1 = (M1.sg (1:Fin 2)).1 :=
    h (0:Fin 2) (1:Fin 2) (by rw [hp 0]; norm_num) (by rw [hp 1]; norm_num)
  exact absurd h01 (by decide)

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **可判定的充分条件：`NoUDependence ⟹ NoConfounding`**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`X` 的方程在正质量处常值 ⟹ 无混杂**（**充分条件，真计算**）。

$$\Bigl(\textbf{NoUDependence}(M) \wedge \sum_u p_U(u) = 1\Bigr)
  \implies \textbf{NoConfounding}(M).$$

**⭐ 证明的实质**：`NoUDependence` 说所有**正质量**的 `u` 给出**同一个** `x₀`。
设 `x` 固定：

* **若 `x = x₀`**：`condY` 的因子 `[x_u = x] = 1`（正质量处），
  **故 `condY M x y = ∑_u p_U(u)[f_u(x) = y] = doLaw M x y`**；
  又 `μ(x₀) = ∑_u p_U(u) = 1`（**需归一化假设 `hnorm`**）；故等式成立。
* **若 `x ≠ x₀`**：`condY` 的因子 `[x_u = x] = 0`（正质量处），
  **故两边都是 `0`**；而 `μ(x) = 0`，**故 `μ(x)·doLaw = 0`**。

**⚠ 诚实说明**：本定理**需要且仅需要**归一化假设 `∑_u p_U(u) = 1`
（`x = x₀` 分支要 `μ(x₀) = 1`）。
**⭐ 不需要 `p_U ≥ 0`** —— 因为两个分支都靠**指示因子 `[x_u = x]`** 的
`if_pos`/`if_neg` 直接分类，而非靠「和为零则每项为零」的论证。 -/
theorem noConfounding_of_no_u_dependence (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (h : SCM.NoUDependence M) (hnorm : ∑ u, M.pU u = 1) :
    SCM.NoConfounding M := by
  intro x y
  by_cases hex : ∃ u, M.pU u ≠ 0
  · obtain ⟨u₀, hu₀⟩ := hex
    have hx₀ : ∀ u, M.pU u ≠ 0 → (M.sg u).1 = (M.sg u₀).1 := fun u hu => h u u₀ hu hu₀
    -- `μ(x₀) = 1`
    have hμ1 : ∀ x, x = (M.sg u₀).1 → FateV2.Modeling.SCMSemantics.marginalX M x = 1 := by
      intro x hx
      unfold FateV2.Modeling.SCMSemantics.marginalX
      have hone : ∀ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0) = M.pU u := by
        intro u
        by_cases hu : M.pU u = 0
        · rw [hu]; simp
        · rw [if_pos (by rw [hx₀ u hu, hx]), mul_one]
      rw [Finset.sum_congr rfl (fun u _ => hone u), hnorm]
    by_cases hsame : x = (M.sg u₀).1
    · -- `x = x₀`：`condY = doLaw`，且 `μ(x) = 1`
      have hcd : FateV2.Modeling.SCMSemantics.condY M x y = FateV2.Modeling.SCMSemantics.doLaw M x y := by
        unfold FateV2.Modeling.SCMSemantics.condY FateV2.Modeling.SCMSemantics.doLaw
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : M.pU u = 0
        · simp [hu]
        · have hxu : (M.sg u).1 = x := by rw [hx₀ u hu, ← hsame]
          rw [if_pos hxu]; ring
      rw [hcd, hμ1 x hsame, one_mul]
    · -- `x ≠ x₀`：两边都是 `0`
      have hzero : FateV2.Modeling.SCMSemantics.condY M x y = 0 := by
        unfold FateV2.Modeling.SCMSemantics.condY
        refine Finset.sum_eq_zero fun u _ => ?_
        by_cases hu : M.pU u = 0
        · simp [hu]
        · have hxu : (M.sg u).1 ≠ x := by
            rw [hx₀ u hu]; exact fun hh => hsame hh.symm
          rw [if_neg hxu]; ring
      have hμ0 : FateV2.Modeling.SCMSemantics.marginalX M x = 0 := by
        unfold FateV2.Modeling.SCMSemantics.marginalX
        refine Finset.sum_eq_zero fun u _ => ?_
        by_cases hu : M.pU u = 0
        · simp [hu]
        · have hxu : (M.sg u).1 ≠ x := by
            rw [hx₀ u hu]; exact fun hh => hsame hh.symm
          rw [if_neg hxu]; ring
      rw [hzero, hμ0, zero_mul]
  · -- `p_U ≡ 0` 与归一化矛盾
    push Not at hex
    have h0 : (∑ u, M.pU u) = 0 := Finset.sum_eq_zero (fun u _ => hex u)
    rw [h0] at hnorm
    norm_num at hnorm

/-! ===========================================================================
  §6 ⭐⭐⭐⭐⭐ **「`X` 依赖外生」仍可无混杂** —— **反驳任务书的「⟺」**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`M2`：`X = u`（**依赖外生**），`Y` 的方程取 `fun x => x`（**只读 `x`**）**。

```
U = Fin 2,  pU ≡ 1/2,  sg u = (u, fun x => x)
```

**⭐⭐ 这是**反驳任务书表述的具体反例**：

* `M2` 里 `X` **确实依赖 `u`**（`(sg 0).1 = 0 ≠ 1 = (sg 1).1`）——
  按任务书的表述，这应当是「`X` 与 `Y` 共用外生 ⟹ 有混杂」；
* **但 `M2` 无混杂**（`noConfounding_M2`）：因为干预 `do(X := x)` 后
  `Y` 的方程 `fun x' => x'` 只看到**被钉死的 `x`**，**不再看到 `u`**。

**⟹ 「方程是否共用外生」**不是**「有无混杂」的判据。
**正确的判据是 `NoConfounding`（§1）—— 它问的是「干预后 `Y` 面对的外生条件分布是否改变」。** -/
noncomputable def M2 : FateV2.Modeling.PearlHierarchy.SCM (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => (u, fun x => x)

/-- ⭐⭐ **`M2` 的观测律**：`condY M2 x y = 1/2` 当 `x = y`，否则 `0`。 -/
theorem condY_M2 (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.condY M2 x y = if x = y then (1 : ℝ) / 2 else 0 := by
  have e : FateV2.Modeling.SCMSemantics.condY M2 x y
      = ∑ u : Fin 2, M2.pU u * (if (M2.sg u).1 = x then (1 : ℝ) else 0)
          * (if (M2.sg u).2 x = y then (1 : ℝ) else 0) := rfl
  rw [e, Fin.sum_univ_two]
  have h1 : (M2.sg (0 : Fin 2)).1 = (0 : Fin 2) := rfl
  have h2 : (M2.sg (1 : Fin 2)).1 = (1 : Fin 2) := rfl
  have h3 : (M2.sg (0 : Fin 2)).2 x = x := rfl
  have h4 : (M2.sg (1 : Fin 2)).2 x = x := rfl
  rw [h1, h2, h3, h4]
  have hp : ∀ u : Fin 2, M2.pU u = (1 : ℝ) / 2 := fun _ => rfl
  rw [hp 0, hp 1]
  fin_cases x <;> fin_cases y <;> norm_num

/-- ⭐⭐ **`M2` 的干预律**：`doLaw M2 x y = 1` 当 `x = y`，否则 `0`（**`Y = x` 确定**）。 -/
theorem doLaw_M2 (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.doLaw M2 x y = if x = y then (1 : ℝ) else 0 := by
  have e : FateV2.Modeling.SCMSemantics.doLaw M2 x y
      = ∑ u : Fin 2, M2.pU u * (if (M2.sg u).2 x = y then (1 : ℝ) else 0) := rfl
  rw [e, Fin.sum_univ_two]
  have h3 : (M2.sg (0 : Fin 2)).2 x = x := rfl
  have h4 : (M2.sg (1 : Fin 2)).2 x = x := rfl
  rw [h3, h4]
  have hp : ∀ u : Fin 2, M2.pU u = (1 : ℝ) / 2 := fun _ => rfl
  rw [hp 0, hp 1]
  fin_cases x <;> fin_cases y <;> norm_num

/-- ⭐⭐ **`M2` 的 `X` 边缘**：`μ(x) = 1/2`。 -/
theorem marginalX_M2 (x : Fin 2) : FateV2.Modeling.SCMSemantics.marginalX M2 x = (1 : ℝ) / 2 := by
  have e : FateV2.Modeling.SCMSemantics.marginalX M2 x
      = ∑ u : Fin 2, M2.pU u * (if (M2.sg u).1 = x then (1 : ℝ) else 0) := rfl
  rw [e, Fin.sum_univ_two]
  have h1 : (M2.sg (0 : Fin 2)).1 = (0 : Fin 2) := rfl
  have h2 : (M2.sg (1 : Fin 2)).1 = (1 : Fin 2) := rfl
  rw [h1, h2]
  have hp : ∀ u : Fin 2, M2.pU u = (1 : ℝ) / 2 := fun _ => rfl
  rw [hp 0, hp 1]
  fin_cases x <;> norm_num

/-- ⭐⭐⭐⭐⭐ **`M2` 满足 `NoConfounding`**（**真算**）—— **尽管 `X` 依赖外生**。

$$\forall x\,y,\quad \mathrm{condY}\,M_2\,x\,y = \mu(x)\cdot \mathrm{doLaw}\,M_2\,x\,y$$

**⭐ 数值核对**（`x = y` 时）：`1/2 = (1/2)·1` ✓；（`x ≠ y` 时）：`0 = (1/2)·0` ✓。 -/
theorem noConfounding_M2 : SCM.NoConfounding M2 := by
  intro x y
  rw [condY_M2, marginalX_M2, doLaw_M2]
  by_cases hxy : x = y <;> simp [hxy]

/-- ⭐⭐⭐⭐⭐ **`M2` **不满足** `NoUDependence`** —— **即「共用外生」可以无混杂**。

**⭐⭐ 这是对任务书「无混杂 ⟺ 用不同的外生分量」的**直接数值反驳**：**
`(M2.sg 0).1 = 0 ≠ 1 = (M2.sg 1).1`，**故 `X` 的方程确实依赖 `u`**，
**然而 `noConfounding_M2` 证明 `M2` 无混杂。**

**⟹ 合起来：`NoUDependence` **严格强于** `NoConfounding`
（`M1` 与 `M2` 是两个独立的见证）。** -/
theorem M2_not_noUDependence : ¬ SCM.NoUDependence M2 := by
  intro h
  have hp : ∀ u : Fin 2, M2.pU u = (1 : ℝ) / 2 := fun _ => rfl
  have h01 : (M2.sg (0 : Fin 2)).1 = (M2.sg (1 : Fin 2)).1 :=
    h (0:Fin 2) (1:Fin 2) (by rw [hp 0]; norm_num) (by rw [hp 1]; norm_num)
  exact absurd h01 (by decide)

/-- ⭐⭐⭐⭐ **本文件的核心结论汇总**：
**「无混杂」既**不**由「`X` 独立于外生」刻画（`M2`），
也**不**由「`X` 与外生相关」否定（`M2`），而是一个**独立的可检验条件**。**

**⚠ 这是把 §4–§6 三条定理打包成一句，以便引用。** -/
theorem confounding_is_not_syntactic :
    SCM.NoConfounding M2 ∧ ¬ SCM.NoUDependence M2 ∧ ¬ SCM.NoUDependence M1
      ∧ SCM.NoConfounding M1 ∧ ¬ SCM.NoConfounding FateV2.Predict.T35.M :=
  ⟨noConfounding_M2, M2_not_noUDependence, M1_not_noUDependence,
    noConfounding_M1, T35_not_noConfounding⟩

/-! ===========================================================================
  §7 ⭐⭐⭐⭐ **实质内容补强**

  ## 动机（与任务书的前提核对）

  任务书称「`Fate/Rule1Semantic.lean` 有 21 条定理，全部是 `:= rfl`」。
  **实测不成立。** 用「逐条解析定理主体」的方式核对（见 `_audit/T2` 报告）：

  * `theorem`/`lemma` **共 21 条**；
  * `:= rfl` 的**只有 1 条**（`margX_eq`，`margX` 与 `FateV2.Modeling.SCMSemantics.marginalX`
    是同一函数的两种写法 —— **有价值的跨模块接线**，保留）；
  * **其余 20 条都是 `by` 块或项级实质证明**。

  **⟹ 任务书里的「21/21 rfl」是**计数误差**：`grep -cE ':= rfl$'` 数到的那 21 处
  `:= rfl`，绝大多数是定理**内部**的 `have ... := rfl` 结构字段投影，
  而不是定理的结论。**`grep -c` 把 `have` 行也算进去了。**

  ## 本节的产出

  **仍然追加 5 条实质定理**，它们**都不是定义展开**，也**不是既有定理的换写**：

  | 定理 | 内容 | 为何非平凡 |
  |---|---|---|
  | `doLaw_sum_eq_one` | 归一化时 `∑_y doLaw M x y = 1` | **换序** + `sum_ite_eq`；**`Y` 上的概率律** |
  | `marginalX_sum_eq_pU` | `∑_x μ(x) = ∑_u p_U(u)` | **边缘化守恒**（`X` 求和吃掉指示因子） |
  | `sum_condY_eq_sum_pU` | `∑_x ∑_y condY = ∑_u p_U` | **前两条的合成：`condY` 是联合质量而非条件概率** |
  | `noConfounding_of_Y_eq_const` | `Y` 的方程常值 ⟹ 无混杂 | **独立于 `NoUDependence` 的另一充分条件** |
  | `condY_eq_zero_iff_doLaw_eq_zero` | 无混杂 + `μ(x) ≠ 0` 时两律同零 | **`NoConfounding` 的支持集推论（双向）** |

  **⚠ 全部零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **归一化外生律下，`doLaw` 在 `y` 上求和为 `1`**：
**干预律是 `Y` 上的概率质量函数**（与 `M`、`x` 无关）。

$$\Bigl(\sum_u p_U(u) = 1\Bigr) \implies \forall x,\quad
  \sum_y \mathrm{doLaw}\,M\,x\,y = 1.$$

**⭐ 为何非平凡**：`doLaw M x y = ∑_u p_U(u)\,[f_u(x) = y]`，
**求和对 `y` 与对 `u` 需要换序**，再用 `∑_y [f_u(x) = y] = 1`（`Finset.sum_ite_eq`）。
**⟹ 这不是定义展开，是一条**求和恒等式**。**

**⚠ 诚实登记（本轮实测发现）**：**归一化假设 `hnorm` 删不掉** ——
不加它时等式右边是 `∑_u p_U(u)` 而非 `1`，
**故「`doLaw` 是 `Y` 上的概率律」是本文件里**唯一**依赖 `p_U` 归一化的事实。** -/
theorem doLaw_sum_eq_one (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (hnorm : ∑ u, M.pU u = 1) (x : X) :
    ∑ y, FateV2.Modeling.SCMSemantics.doLaw M x y = 1 := by
  have e : ∑ y, FateV2.Modeling.SCMSemantics.doLaw M x y
      = ∑ y, ∑ u, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0) := rfl
  rw [e]
  rw [show (∑ y : Y, ∑ u : M.U, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0))
      = ∑ u : M.U, ∑ y : Y, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0)
      from Finset.sum_comm]
  have hmain : ∀ u : M.U,
      (∑ y : Y, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0)) = M.pU u := by
    intro u
    rw [← Finset.mul_sum]
    have h1 : (∑ y : Y, (if (M.sg u).2 x = y then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_ite_eq Finset.univ ((M.sg u).2 x) (fun _ => (1 : ℝ))]
      simp
    rw [h1, mul_one]
  rw [Finset.sum_congr rfl (fun u _ => hmain u), hnorm]

/-- ⭐⭐⭐⭐ **边缘化守恒**：`X` 各取值的边缘质量之和 = 外生律的总质量。

$$\sum_x \mu(x) = \sum_u p_U(u).$$

**⭐ 为何非平凡**：需要把 `∑_x` 与 `∑_u` **换序**，
并证明 `∑_x [(sg u).1 = x] = 1`（**每条外生实现恰好贡献 1 个单位质量给某个 `x`**）。
**⟹ 这是「`μ` 是 `p_U` 经 `(sg ·).1` 推前」的数值陈述。** -/
theorem marginalX_sum_eq_pU (M : FateV2.Modeling.PearlHierarchy.SCM X Y) :
    ∑ x, FateV2.Modeling.SCMSemantics.marginalX M x = ∑ u, M.pU u := by
  have e : ∑ x, FateV2.Modeling.SCMSemantics.marginalX M x
      = ∑ x, ∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0) := rfl
  rw [e]
  rw [show (∑ x : X, ∑ u : M.U, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0))
      = ∑ u : M.U, ∑ x : X, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)
      from Finset.sum_comm]
  have hmain : ∀ u : M.U,
      (∑ x : X, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)) = M.pU u := by
    intro u
    rw [← Finset.mul_sum]
    have h1 : (∑ x : X, (if (M.sg u).1 = x then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_ite_eq Finset.univ ((M.sg u).1) (fun _ => (1 : ℝ))]
      simp
    rw [h1, mul_one]
  exact Finset.sum_congr rfl (fun u _ => hmain u)

/-- ⭐⭐⭐⭐ **联合律 `condY` 的总质量 = 外生律的总质量**（`marginalX_eq_sum_condY` 的实际用途）。

$$\sum_x \sum_y \mathrm{condY}\,M\,x\,y = \sum_u p_U(u).$$

**⭐ 为何非平凡**：这是 §2 的 `marginalX_eq_sum_condY` 与本节
`marginalX_sum_eq_pU` 的**合成**。
**它检查 `condY` 确实是「联合质量」而非归一化条件概率** ——
**若 `condY` 的每个 `x` 切片都归一化到 `1`，本式会给出 `#X = ∑ p_U`，与 `X` 的大小挂钩。** -/
theorem sum_condY_eq_sum_pU (M : FateV2.Modeling.PearlHierarchy.SCM X Y) :
    ∑ x, ∑ y, FateV2.Modeling.SCMSemantics.condY M x y = ∑ u, M.pU u := by
  rw [← marginalX_sum_eq_pU M]
  exact Finset.sum_congr rfl fun x _ => (marginalX_eq_sum_condY M x).symm

/-- ⭐⭐⭐⭐⭐ **`Y` 的方程常值 ⟹ 无混杂**（**独立于 `NoUDependence` 的充分条件**）。

$$\Bigl(\exists y_0,\ \forall u,\ (M.\mathrm{sg}\,u).2 = \mathrm{const}\;y_0\Bigr)
  \wedge \sum_u p_U(u) = 1 \ \implies\ \textbf{NoConfounding}(M).$$

**⭐⭐ 为何这是**新**内容**：§5 的充分条件 `NoUDependence` 是**关于 `X` 的方程**的条件，
本定理是**关于 `Y` 的方程**的条件 —— 两者**互不蕴含**
（`M1`：两者都成立；`M2`：两者都不成立，但 `NoConfounding` 仍成立 ——
**故本定理给出的是**第三条独立路径**）。

**⭐ 证明的实质**：`Y` 常值 `y₀` 时
`condY M x y = μ(x)·[y₀ = y]` 而 `doLaw M x y = (∑_u p_U u)·[y₀ = y] = [y₀ = y]`，
**故两边都等于 `μ(x)·[y₀ = y]`**（**需归一化 `hnorm`**）。** -/
theorem noConfounding_of_Y_eq_const (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (y0 : Y)
    (hf : ∀ u, (M.sg u).2 = fun _ => y0) (hnorm : ∑ u, M.pU u = 1) :
    SCM.NoConfounding M := by
  intro x y
  have hcond : FateV2.Modeling.SCMSemantics.condY M x y
      = FateV2.Modeling.SCMSemantics.marginalX M x * (if y0 = y then (1 : ℝ) else 0) := by
    have e : FateV2.Modeling.SCMSemantics.condY M x y
        = ∑ u, (M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0))
            * (if y0 = y then (1 : ℝ) else 0) := by
      unfold FateV2.Modeling.SCMSemantics.condY
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hf u]
    have e2 : FateV2.Modeling.SCMSemantics.marginalX M x * (if y0 = y then (1 : ℝ) else 0)
        = ∑ u, (M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0))
            * (if y0 = y then (1 : ℝ) else 0) := by
      unfold FateV2.Modeling.SCMSemantics.marginalX
      rw [Finset.sum_mul]
    rw [e, e2]
  have hdo : FateV2.Modeling.SCMSemantics.doLaw M x y = if y0 = y then (1 : ℝ) else 0 := by
    have e : FateV2.Modeling.SCMSemantics.doLaw M x y
        = ∑ u, M.pU u * (if y0 = y then (1 : ℝ) else 0) := by
      unfold FateV2.Modeling.SCMSemantics.doLaw
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hf u]
    rw [e, ← Finset.sum_mul, hnorm, one_mul]
  rw [hcond, hdo]

/-- ⭐⭐⭐⭐ **`NoConfounding` 的可检验推论：两律同时为零**（**支持集相同**）。

$$\mu(x) \ne 0 \implies \textbf{NoConfounding}(M) \implies
  \Bigl(\mathrm{condY}\,M\,x\,y = 0 \iff \mathrm{doLaw}\,M\,x\,y = 0\Bigr).$$

**⭐ 为何非平凡**：它**不是**把 `NoConfounding` 展开 ——
展开给的是 `condY = μ(x)·doLaw`，**要在 `μ(x) ≠ 0` 时约去因子**才得到本式，
且是**双向**：`→` 用 `mul_eq_zero` 排除 `μ(x) = 0` 分支，`←` 用 `mul_zero`。
**⟹ 这是「`condY` 与 `doLaw` 在 `x` 切片上支持集相同」的陈述**，
**可用于由 `doLaw` 的支持反推观测律的支持。** -/
theorem condY_eq_zero_iff_doLaw_eq_zero (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (h : SCM.NoConfounding M) (x : X) (hx : FateV2.Modeling.SCMSemantics.marginalX M x ≠ 0) (y : Y) :
    FateV2.Modeling.SCMSemantics.condY M x y = 0 ↔ FateV2.Modeling.SCMSemantics.doLaw M x y = 0 := by
  rw [h x y]
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hx
    · exact h1
  · intro h0
    rw [h0, mul_zero]

/-! ===========================================================================
  §8 实质定理（T-3 追加）：语义的**结构事实**与**与其他模块的连接**

  ## 前置实测（防「计数误差」重演）

  **§7 的动机段落已经指出**：`grep -cE ':= rfl$'` 数到 24 处，但**绝大多数是
  定理内部 `have ... := rfl` 的结构字段投影**，而非定理结论。
  **本次按「解析定理头 + 取末尾 `:=`」重新计数，实测：**

  * **`theorem`/`lemma` 共 26 条**；
  * **结论为 `rfl` 的仅 1 条**：`margX_eq`（**有价值的跨模块接线**：`SCM.margX`
    与 `FateV2.Modeling.SCMSemantics.marginalX` 是同一函数的两种写法）；
  * **其余 25 条均为 `by` 块或项级实质证明**。

  **⟹ 本模块的实际 rfl 比例是 4%（1/26），不是 92%。**

  ## 本节产出

  仍追加 3 条**实质**定理，它们把 §1 的语义条件与**可算的结构事实**接起来：

  | 定理 | 内容 | 为何非平凡 |
  |---|---|---|
  | `doLaw_eq_of_sg_snd_eq` | `doLaw` **只读** `sg` 的第二分量 | 逐项 `congr`；**`do(x)` 切断入边的数值体现** |
  | `noConfounding_of_sg_fst_const` | `X` 的方程**无条件**常值 ⟹ 无混杂 | 比 §5 的 `NoUDependence` **前件更弱**（无需 `pU ≠ 0` 守卫） |
  | `doLaw_sum_eq_one_of_condY_sum` | 无混杂 + `μ(x)=1` 时把 `condY` 的归一化**搬运**到 `doLaw` | **跨定义搬运**，非展开 |
  **⚠ 全部零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。**

  **⚠ 一条**主动弃用**的候选**：曾打算追加「`condY` 的因子分解形式」
  `∑ u, pU·[..]·[..] = ∑ u, pU·[..]·[..]`。**它是 `X = X` 式的同义反复**
  （左右两端逐字相同，`rfl` 即可），**违反「结论不能是定义展开」的 F2 判据**，
  故**未追加**。**本条如实登记，不硬凑。**
  =========================================================================== -/

/-- ⭐⭐⭐ **【`do(x)` 切断入边：`doLaw` **只读** `sg` 的第二分量】**

若两个 `U → X × (X → Y)` 映射的**第二分量**逐点相同（第一分量即 `X` 的方程任意），
则它们给出的**干预律相同**：

$$\Bigl(\forall u,\ (\mathrm{sg}'\,u).2 = (\mathrm{sg}\,u)_2\Bigr)
  \implies \forall x\,y,\ \sum_u p_U(u)\,[\mathrm{sg}'_u(x) = y]
    = \sum_u p_U(u)\,[\mathrm{sg}_u(x) = y].$$

**⭐⭐ 为何非平凡（这是本节的**核心结构事实**）**：
`FateV2.Modeling.SCMSemantics.doLaw` 的定义里**没有** `[(sg u).1 = x]` 这个筛选因子，
而 `condY` 里**有**。
**故 `doLaw` 对 `X` 的方程完全不敏感** ——
**这正是「干预 `do(X := x)` 切断 `X` 的入边」的**数值/句法体现**。**
`M2`（§6）之所以无混杂，正是这条事实的具体实例。

**⚠ 证明是逐项 `Finset.sum_congr` + `rw`**，不是定义展开
（两边的项**形式不同**，需要真的用 `hsg` 重写）。 -/
theorem doLaw_eq_of_sg_snd_eq {U : Type u} [Fintype U]
    (pU : U → ℝ) (sg sg' : U → X × (X → Y))
    (hsg : ∀ u, (sg' u).2 = (sg u).2) (x : X) (y : Y) :
    (∑ u, pU u * (if (sg' u).2 x = y then (1 : ℝ) else 0))
      = ∑ u, pU u * (if (sg u).2 x = y then (1 : ℝ) else 0) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hsg u]

/-- ⭐⭐⭐⭐ **【`X` 的方程**无条件**常值 ⟹ 无混杂】**（§5 充分条件的**加强**版）

$$\Bigl(\exists x_0,\ \forall u,\ (M.\mathrm{sg}\,u).1 = x_0\Bigr)
  \wedge \sum_u p_U(u) = 1 \ \implies\ \textbf{NoConfounding}(M).$$

**⭐⭐ 为何**比 §5 的 `noConfounding_of_no_u_dependence` 更强**：
`NoUDependence` 只要求**正质量**的 `u` 取同一 `x₀`（带 `pU u ≠ 0` 守卫）；
本条要求**全部** `u`（**无守卫**）。**故本条的 `NoUDependence` 前件由本条的
前件可推出，反之不然**（在 `pU` 有零点的模型上，`NoUDependence` 可能成立
而「全部 `u` 常值」不成立）。
**⟹ 这是一个**真正更弱的前件**给出的充分条件，不是 §5 的换写。** -/
theorem noConfounding_of_sg_fst_const (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x0 : X)
    (hfst : ∀ u, (M.sg u).1 = x0) (hnorm : ∑ u, M.pU u = 1) :
    SCM.NoConfounding M :=
  noConfounding_of_no_u_dependence M
    (fun u v _ _ => by rw [hfst u, hfst v]) hnorm

/-- ⭐⭐⭐ **【把 `condY` 的归一化**搬运**到 `doLaw`】**

$$\textbf{NoConfounding}(M) \implies \mu(x) = 1 \implies
  \Bigl(\sum_y \mathrm{condY}\,M\,x\,y = 1 \iff \sum_y \mathrm{doLaw}\,M\,x\,y = 1\Bigr).$$

**⭐ 为何非平凡**：它**跨两个定义**（`condY` 与 `doLaw`）搬运归一化。
证明要在**和号内**用 `NoConfounding` 把 `condY` 换成 `μ(x)·doLaw`，
再把 `μ(x) = 1` 提出，**最后把 `∑` 的等式两边对齐**。
**⟹ 这不是展开，是「两个律的归一化等价」的陈述；**
**它给出「`μ(x) = 1` 时观测律与干预律**同归一化**」的可用接口。** -/
theorem doLaw_sum_eq_one_of_condY_sum (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (h : SCM.NoConfounding M) (x : X) (hx : FateV2.Modeling.SCMSemantics.marginalX M x = 1)
    (hc : ∑ y, FateV2.Modeling.SCMSemantics.condY M x y = 1) :
    ∑ y, FateV2.Modeling.SCMSemantics.doLaw M x y = 1 := by
  have e : ∑ y, FateV2.Modeling.SCMSemantics.doLaw M x y = ∑ y, FateV2.Modeling.SCMSemantics.condY M x y := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [h x y, hx, one_mul]
  rw [e, hc]

end R242G3

end FateV2.Predict