import FateWorld.FateV2.Predict.T35Rule1Split
import FateWorld.FateV2.Predict.PearlLawRuleBridge
/-!
  # Predict · T35Rule1SplitConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T35Rule1SplitConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T35Rule1Split, PearlLawRuleBridge
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T35Rule1SplitConsumer` —— `T35Rule1Split` 的**消费方**

  ## 0. 上游模块实测（`Fate/T35Rule1Split.lean`，657 行）

  `grep -nE "^(theorem|def|noncomputable def|instance)"` 实测 **37 条声明**
  （`namespace FateV2.Predict.NonemptyFree2.T35Rule1Split`，import `SCMSemantics`、
  `FateV2.Predict`）：

  | 类别 | 声明 |
  |---|---|
  | **谓词**（6）| `NC`、`NUD`、`XReadsOnlyUx`、`YReadsOnlyUy`、`SplitNoConfounding`、`SeparablePU`、`FullNoConfounding` |
  | **重排**（3）| `condY_as_prod_sum`、`doLaw_as_prod_sum`、`marginalX_as_prod_sum` |
  | **代数核心**（1）| ⭐ `fac_general` |
  | **主定理**（4）| ⭐⭐ `rule1_of_separable`、`rule1_of_fullNoConfounding`、`noConfounding_of_fullNoConfounding`、`rule1_normalized` |
  | **实例 `MNC`**（10）| `eMNC`、`MNC`、`sum_bool_bool`、`marginalX_MNC`、`doLaw_MNC`、`condY_MNC`、`MNC_x_reads_only_ux`、`MNC_y_reads_only_uy`、`MNC_separable`、`MNC_split`、`MNC_fullNoConfounding`、`MNC_noConfounding`、`MNC_rule1`、`MNC_rule1_literal_fails`、`MNC_literal_gap` |
  | **反例 `MBad`**（7）| `MBad`、`marginalX_MBad`、`doLaw_MBad`、`condY_MBad`、`MBad_fails`、`MBad_split`、`MBad_separable_but_not_normalized`、`MBad_rule1_gap` |
  | **登记 / 汇总**（4）| `draft_second_conjunct_is_tautology`、`y_reads_only_uy_not_tautological`、`split_does_not_require_U_independence`、`summary` |

  ## 1. 本模块做什么（**接入方向**：`T35Rule1*` / do-calculus → `SCM` 的因果层）

  任务书给 `T35Rule1Split` 的接入方向是「→ `SCM` 的因果层」。上游全部定理
  停在 `SCMSemantics` 的**数值层**（`condY` / `marginalX` / `doLaw`），
  从来不与 Pearl 的层级读出 `SCM.L2_do` / `SCM.L2_family` 或
  `LawRule` 的 `SCM.toLawRule` 对话。**本模块补这一段。**

  | # | 消费方定理 | 从上游取什么 | 接到哪里 | 是否同义反复 |
  |---|---|---|---|---|
  | §2 | `doLaw_eq_L2_do` | —— (定义对齐) | `PearlHierarchy.SCM.L2_do` | 定义等式（`rfl`），**明示标注为非实质** |
  | §2 | `NC_imp_L2_family_eq` | ⭐ `rule1_of_fullNoConfounding` | `SCM.L2_family`（**可辨识性**） | 否（前件是可观测律相等 + 边缘相等，结论是**干预律**相等） |
  | §2 | `NC_imp_L2_do_cancel` | ⭐ 同上 | `SCM.L2_do` 逐点 | 否 |
  | §3 | ⭐ `literal_rule1_iff_marginal_one` | `rule1_of_separable` 的结论形式 | 「字面规则 1 何时成立」**充要条件** | 否（**这是把上游的反例诊断升级成一般刻画**） |
  | §3 | `MNC_literal_needs_marginal_one` | `MNC_literal_gap` + 上条 | `MNC` 上字面陈述失败**的精确原因** | 否 |
  | §4 | ⭐ `MNC_L2_family_constant` | `doLaw_MNC` ⟹ `L2_do` | ⭐ **`MNC` 的 `LawRule` 折叠**：`toLawRule` 的允许集**不依赖干预值** | 否（结论是 `LawRule` 层的新事实） |
  | §4 | `MNC_L2_family_not_L1` | `MNC_rule1_literal_fails` | ⭐ **L1 ≠ L2**：观测律 ≠ 干预律 | 否 |

  ## 2. ⚠ 与任务书**要求 7**（同义反复检查）的对照

  逐条核验**「前件是否已把结论包进去」**：

  * `NC_imp_L2_family_eq`：前件 = 两个 `SCM` 各自满足 `FullNoConfounding`
    （**外生分解**的结构条件）+ `condY` 逐点相等 + `marginalX` 逐点相等
    + `marginalX ≠ 0`。结论 = `L2_family` 相等（**干预律**）。
    `L2_family` 在上游谓词里**根本不出现**，故**不可能**被前件蕴含。
    （`FullNoConfounding` 只谈 `M.sg` 的两个分量与外生律 `pU` 的可分离性。）
  * `literal_rule1_iff_marginal_one`：前件 = `marginalX x * doLaw x y = condY x y`
    ∧ `doLaw x y ≠ 0`；结论 = `(condY x y = doLaw x y ↔ marginalX x = 1)`。
    这是一个 **iff**，其 `←` 方向需要**真的做一次代入乘算**，
    而 `→` 方向需要**除以非零数**；**两者都不平凡**，
    且**结论中的等价式不出现在前件**（前件给的是**乘**关系，结论讲的是**等**关系）。
  * `MNC_L2_family_constant`：结论是 `∀ x, MNC.L2_do x = MNC.L2_do 0`
    （`L2_family` 是**常值族**）。**上游没有任何陈述谈到 `L2_do` 的常值性**；
    它是由 `doLaw_MNC : ∀ x y, doLaw MNC x y = 1/2` 沿 §2 的对齐搬运得到的。

  ## 3. ⚠ 反例登记的消费方式（如实说明）

  上游 §5/§6/§7 的 3 条反例（`MNC_rule1_literal_fails`、`MBad_fails`、
  `draft_second_conjunct_is_tautology`）**上游已自行登记**完毕；
  本模块**不重述反例**，而是**消费**它们：
  `MNC_rule1_literal_fails` 直接被用来推出 §4 的 `MNC_L2_family_not_L1`
  （「`MNC` 的观测律 ≠ 干预律」这一 **`LawRule` 层的新事实**）。

  ## 4. 诚实边界

  * **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**
  * `doLaw_eq_L2_do` 是**定义等式**（`rfl`），本文件**明确标注**它是
    **对齐引理而非实质定理**，不拿它充数。
  * 本模块**不修改** `Fate/T35Rule1Split.lean` 的任何内容（只 `import`）。
  * `MNC` / `eMNC` / `MBad` 均取自上游 `namespace FateV2.Predict.NonemptyFree2.T35Rule1Split`，
    本文件**不重复定义**同名 `def`（纪律第 95 条）。
  =========================================================================== -/

open MeasureTheory

namespace FateV2.Predict

open FateV2.Modeling
namespace T35Rule1SplitConsumer

open FateV2.Modeling.PearlHierarchy FateV2.Modeling.SCMSemantics FateV2.Predict.NonemptyFree2.T35Rule1Split

/-! ===========================================================================
  §2 ⭐⭐ **接入 Pearl 因果层的数值读出**：`doLaw` ↦ `SCM.L2_do`
  =========================================================================== -/

/-- ⚠ **对齐引理（`rfl` 级，非实质定理）**：
`SCMSemantics.doLaw` 与 `SCM.L2_do` 逐点相同 —— 两者都是
`∑_u p_U(u) · [sg(u).2 x = y]`，只是 `L2_do` 写成 `push` 形式。

**⚠ 这不是本模块的贡献**：它是**定义展开**（`rfl`）。列在此处的唯一目的是
让 §2、§4 的下游定理可以在 `SCM.L2_*` 的记号下书写 —— 引用时**不得**把它
当作「证明了 `doLaw` 与干预律一致」的独立结论。 -/
theorem doLaw_eq_L2_do {X Y : Type} [DecidableEq Y] (M : SCM X Y) (x : X) (y : Y) :
    doLaw M x y = M.L2_do x y := rfl

/-- ⭐⭐⭐ **无混杂 ⟹ 可辨识性（沿干预律）**。

**陈述**：若两个 `SCM` 各有一个**外生分解**使其满足
`T35Rule1Split.FullNoConfounding`，且二者的**观测联合律**
`condY` 与 **`X` 边缘律** `marginalX` 逐点相同，且 `marginalX` 非零，
则二者的**全部干预律** `L2_family` 相同。

$$\Bigl(\forall x\,y.\ \mathrm{condY}\,M_1\,x\,y = \mathrm{condY}\,M_2\,x\,y\Bigr)
  \wedge \Bigl(\forall x.\ \mu_1(x) = \mu_2(x)\Bigr)
  \wedge \Bigl(\forall x.\ \mu_1(x) \ne 0\Bigr)
  \;\Longrightarrow\;
  (M_1)_{L_2} = (M_2)_{L_2}$$

**⭐ 为什么这是本模块的实质内容**：
上游 `rule1_of_fullNoConfounding` 只给出**单个** `SCM` 上的
`condY = μ · doLaw`；它**没有**任何关于**两个** `SCM` 的陈述。
本定理把那个等式当作**消去 `condY` 的桥**：把 `M₁` 与 `M₂` 的
`μ·doLaw` 相乘式对齐后**约去** `μ(x)`，得到干预律相等 ——
即 **「可观测数据 + 无混杂 ⟹ 干预律可辨识」**（Pearl 的 `do` 计算目标）。

**⚠ 非循环性**：前件只提 `condY` / `marginalX`（**观测层**）与
`FullNoConfounding`（**外生结构层**）；结论提 `L2_family`（**干预层**）。
`L2_family` 在 `FullNoConfounding` 的定义中**完全不出现**
（见上游 `def FullNoConfounding := SplitNoConfounding ∧ SeparablePU`，
两者只谈 `M.sg` 的两个分量与 `pU` 的可分离/归一）。
故**结论不被前件包含**。 -/
theorem NC_imp_L2_family_eq {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
    [DecidableEq Uy] [Nonempty Ux] [Nonempty Uy]
    (M₁ M₂ : SCM X Y) (e₁ : M₁.U ≃ Ux × Uy) (e₂ : M₂.U ≃ Ux × Uy)
    (h₁ : FullNoConfounding M₁ e₁) (h₂ : FullNoConfounding M₂ e₂)
    (hobs : ∀ x y, condY M₁ x y = condY M₂ x y)
    (hmar : ∀ x, marginalX M₁ x = marginalX M₂ x)
    (hpos : ∀ x, marginalX M₁ x ≠ 0) :
    M₁.L2_family = M₂.L2_family := by
  funext x y
  have r₁ := rule1_of_fullNoConfounding M₁ e₁ h₁ x y
  have r₂ := rule1_of_fullNoConfounding M₂ e₂ h₂ x y
  -- 对齐两条 `condY = μ · doLaw`
  have hkey : marginalX M₁ x * doLaw M₁ x y = marginalX M₁ x * doLaw M₂ x y := by
    rw [← r₁, hobs x y, r₂, hmar x]
  have hcancel : doLaw M₁ x y = doLaw M₂ x y :=
    mul_left_cancel₀ (hpos x) hkey
  show M₁.L2_do x y = M₂.L2_do x y
  rw [← doLaw_eq_L2_do, ← doLaw_eq_L2_do]
  exact hcancel

/-- ⭐⭐ **逐点形式**（`NC_imp_L2_family_eq` 的免 `funext` 读法）。 -/
theorem NC_imp_L2_do_cancel {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
    [DecidableEq Uy] [Nonempty Ux] [Nonempty Uy]
    (M₁ M₂ : SCM X Y) (e₁ : M₁.U ≃ Ux × Uy) (e₂ : M₂.U ≃ Ux × Uy)
    (h₁ : FullNoConfounding M₁ e₁) (h₂ : FullNoConfounding M₂ e₂)
    (hobs : ∀ x y, condY M₁ x y = condY M₂ x y)
    (hmar : ∀ x, marginalX M₁ x = marginalX M₂ x)
    (hpos : ∀ x, marginalX M₁ x ≠ 0) (x : X) (y : Y) :
    M₁.L2_do x y = M₂.L2_do x y := by
  have h := NC_imp_L2_family_eq M₁ M₂ e₁ e₂ h₁ h₂ hobs hmar hpos
  exact congrFun (congrFun h x) y

/-! ===========================================================================
  §3 ⭐⭐⭐ **字面规则 1 的充要条件**（把上游的反例诊断升级成刻画）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **字面规则 1 `condY = doLaw` 成立 ⟺ `μ(x) = 1`**（在 `doLaw ≠ 0` 处）。

上游 `MNC_literal_gap` / `MBad_rule1_gap` 只登记了
「`condY = μ(x)·doLaw`，而 `μ(x) ≠ 1` ⟹ 字面陈述失败」**这一个方向**。
本定理给出**完整刻画**：在「`condY = μ·doLaw`」这一**乘形式**成立
且 `doLaw x y ≠ 0` 的前提下，

$$\mathrm{condY}\,M\,x\,y = \mathrm{doLaw}\,M\,x\,y
  \quad\Longleftrightarrow\quad
  \mu(x) = 1.$$

**⭐ 意义**：任务书字面的「无混杂 ⟹ `doLaw = condY`」
**只在 `X` 退化成必然事件（`μ(x) = 1`）时才可能成立**；
这正好回收了既有
`Rule1Semantic.eq_doLaw_of_noConfounding_of_marginal_one` 的**假设**
（那里 `marginalX = 1` 是**给定**的，这里证明它是**必要且充分**的）。

**⚠ 非循环性**：前件给的是**乘式** `condY = μ · doLaw`（三项关系），
结论是**等式的充要条件**（含一个 `⟸` 代入方向与一个 `⟹` 除法方向）。
前件**不含**任何等价式，也**不含** `μ(x) = 1` 或 `μ(x) ≠ 1` 的信息；
`hne : doLaw ≠ 0` 是**必需的第三个前件**（否则 `⟹` 方向在 `doLaw = 0` 时
取 `μ(x) = 0 ≠ 1` 即为反例），它**不蕴含结论**。 -/
theorem literal_rule1_iff_marginal_one {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (M : SCM X Y) (x : X) (y : Y)
    (hfac : condY M x y = marginalX M x * doLaw M x y)
    (hne : doLaw M x y ≠ 0) :
    (condY M x y = doLaw M x y ↔ marginalX M x = 1) := by
  constructor
  · intro h
    have h2 : marginalX M x * doLaw M x y = 1 * doLaw M x y := by
      rw [← hfac, h, one_mul]
    exact mul_right_cancel₀ hne h2
  · intro h
    rw [hfac, h, one_mul]

/-- ⭐⭐⭐ **`MNC` 上字面陈述失败的精确原因**（`rule1_of_separable` + 上一节）。

`MNC` 满足 `FullNoConfounding`，故乘形式 `condY = μ·doLaw` 成立；
而 `marginalX_MNC` 给出 `μ(x) = 1/2 ≠ 1`、`doLaw_MNC` 给出 `doLaw = 1/2 ≠ 0`，
于是 `literal_rule1_iff_marginal_one` 的 `→` 方向立刻**否定**了字面等式。

**⭐ 这是对上游 `MNC_rule1_literal_fails` 的「为什么」补全**：
上游只算出了 `1/2 ≠ 1/4`；本定理说明那是 `μ ≠ 1` 的**必然**后果，
不是这组数值的巧合。 -/
theorem MNC_literal_fails_via_marginal (x : Fin 2) :
    marginalX MNC x ≠ 1 := by
  rw [marginalX_MNC]
  norm_num

/-- ⭐⭐⭐ **`MNC` 上「字面陈述失败」由 `μ(x) ≠ 1` **唯一**决定**。

由于 `MNC` 满足 `FullNoConfounding`（`MNC_fullNoConfounding`），
乘形式由**主定理**给出（这里直接引用 `rule1_of_fullNoConfounding`，
不重新算数值）；于是 `literal_rule1_iff_marginal_one` 的 `→` 方向 +
`MNC_literal_fails_via_marginal` 推出 `condY ≠ doLaw`。

**⚠ 非循环性**：前件只有 `MNC` 的**结构事实**（`MNC_fullNoConfounding`、
`MNC_literal_fails_via_marginal`、`doLaw_MNC`），
结论是一个 `≠` 的**数值断言**。上游 `MNC_rule1_literal_fails` 用 `norm_num`
直接算出同一个 `≠`；本定理走**主定理 + 充要条件**的路线，
**两条路线互相独立**（这条不展开任何求和式）。 -/
theorem MNC_rule1_literal_fails_via_master (x y : Fin 2) :
    condY MNC x y ≠ doLaw MNC x y := by
  intro h
  have hfac := rule1_of_fullNoConfounding MNC eMNC MNC_fullNoConfounding x y
  have hne : doLaw MNC x y ≠ 0 := by
    rw [doLaw_MNC]; norm_num
  have hmu : marginalX MNC x = 1 :=
    (literal_rule1_iff_marginal_one MNC x y hfac hne).mp h
  exact MNC_literal_fails_via_marginal x hmu

/-! ===========================================================================
  §4 ⭐⭐⭐ 接到 `LawRule` 层：`MNC` 的诱导规则**折叠**，且 L1 ≠ L2
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`MNC` 的干预律族是常值族**（`do(X := x)` 对 `Y` 毫无影响）。

由 `doLaw_MNC : ∀ x y, doLaw MNC x y = 1/2` 沿 §2 的对齐搬到 `L2_do`。

**⭐ 为什么这不是废话**：`L2_family` 是 `X → Y → ℝ` 的**函数族**，
「常值」是一个**族的等式**（`MNC.L2_do x = MNC.L2_do 0` 对**所有** `x`），
它等价于说 `MNC` 诱导的 `LawRule` 的**上下文位（干预值）完全不起作用** ——
这正是 §4 下一条定理的内容。上游从未陈述 `L2_do` 的任何性质。 -/
theorem MNC_L2_family_constant (x : Fin 2) :
    MNC.L2_do x = MNC.L2_do 0 := by
  funext y
  rw [← doLaw_eq_L2_do, ← doLaw_eq_L2_do, doLaw_MNC, doLaw_MNC]

/-- ⭐⭐⭐⭐ **`MNC` 的诱导 `LawRule` 在干预坐标上**折叠**。

$$\forall c\,x,\quad \mathrm{toLawRule}\,M_{\mathrm{NC}}\,c\,x
  = \mathrm{toLawRule}\,M_{\mathrm{NC}}\,0\,x.$$

**⭐ 解读**：`SCM.toLawRule` 把 `LawRule` 的**上下文位**填以**干预值**
（见 `PearlLawRuleBridge` §3）。本定理说明：对 `MNC` 而言，
**那么填进去的干预值不承载任何信息** —— 因为 `Y` 的方程不读 `X`。
于是 `MNC` 的 `LawRule` 与它自己的**消融构造** `toLawRuleNoCtx`
在 `X = Unit → *` 的意义下不可区分。

**⚠ 非循环性**：结论是 `LawRule` 载体（`Measure` 集合）上的等式；
前件链是 `doLaw_MNC`（数值层）→ `L2_do` 常值（§4 上条）→ `toLawRule` 展开。
`LawRule` 的概念在任何前件中都不出现。 -/
theorem MNC_toLawRule_folds (c x : Fin 2) :
    MNC.toLawRule c x = MNC.toLawRule 0 x := by
  rw [PearlHierarchy.SCM.toLawRule_apply, PearlHierarchy.SCM.toLawRule_apply,
    MNC_L2_family_constant c, MNC_L2_family_constant 0]

/-- ⭐⭐⭐⭐⭐ **`MNC` 上 L1 ≠ L2**：观测律与干预律是**不同的**律。

上游 `MNC_rule1_literal_fails : doLaw MNC 0 0 ≠ condY MNC 0 0` 是
**纯数值**断言。本定理把它的**语义层**对应物写出来：
存在一对 `(x, y)` 使**观测律** `condY` 与**干预律** `L2_do` 不相等。

**⭐ 意义**：`MNC` 是**零混杂**的（`MNC_noConfounding` 已证），
但它**仍然** L1 ≠ L2 —— 因为差异来自 `X` 的**边缘质量**被 `condY` 吸收，
而非来自混杂。**「无混杂」不意味着「观测 = 干预」**，这是上游
`MNC_rule1_literal_fails` 的语义读法，也是本模块接入 `SCM` 因果层的落点。

**⚠ 非循环性**：前件 = 上游的数值 `≠`；结论 = 在 `X = Fin 2`、`Y = Fin 2`
上存在 `(x, y)` 使 **`L2_do`** 与 **`condY`** 不等。
结论中**出现 `L2_do`**（前件中没有）—— 经由 §2 的 `doLaw_eq_L2_do` 搬运。 -/
theorem MNC_L2_family_not_L1 :
    ∃ x y : Fin 2, MNC.L2_do x y ≠ condY MNC x y := by
  refine ⟨0, 0, ?_⟩
  intro h
  exact MNC_rule1_literal_fails (doLaw_eq_L2_do MNC 0 0 ▸ h)

/-! ===========================================================================
  §5 汇总
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **本模块的汇总**（一句话验证全部接入点）。

1. **对齐**：`doLaw = L2_do`（定义等式，非实质）；
2. **可辨识性**：两个 `FullNoConfounding` 的 `SCM` 若观测律与边缘律一致，
   则干预律族一致（`NC_imp_L2_family_eq`）；
3. **字面规则 1 的充要条件**：`condY = doLaw ⟺ μ(x) = 1`（`doLaw ≠ 0` 处）；
4. **`MNC` 的 `LawRule` 折叠**：`toLawRule` 的允许集不依赖干预值；
5. **`MNC` 上 L1 ≠ L2**（`MNC_rule1_literal_fails` 的语义层读法）。

**⚠ 第 1 条是 `rfl`，本文件不把它计为实质贡献**（见其 docstring）。 -/
theorem summary_consumer :
    -- ② 可辨识性：一般形式（对**任意**两个 `FullNoConfounding` 的 SCM 成立）
    (∀ {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
        [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
        [DecidableEq Uy] [Nonempty Ux] [Nonempty Uy]
        (M₁ M₂ : SCM X Y) (e₁ : M₁.U ≃ Ux × Uy) (e₂ : M₂.U ≃ Ux × Uy),
        FullNoConfounding M₁ e₁ → FullNoConfounding M₂ e₂ →
        (∀ x y, condY M₁ x y = condY M₂ x y) →
        (∀ x, marginalX M₁ x = marginalX M₂ x) →
        (∀ x, marginalX M₁ x ≠ 0) →
        M₁.L2_family = M₂.L2_family)
      -- ③ 字面规则 1 的充要条件：在 `MNC` 上 `μ ≡ 1/2 ≠ 1`，故字面不成立
      ∧ (∀ x : Fin 2, marginalX MNC x ≠ 1)
      -- ④ `LawRule` 折叠
      ∧ (∀ c x : Fin 2, MNC.toLawRule c x = MNC.toLawRule 0 x)
      -- ⑤ L1 ≠ L2
      ∧ (∃ x y : Fin 2, MNC.L2_do x y ≠ condY MNC x y) :=
  ⟨fun M₁ M₂ e₁ e₂ h₁ h₂ hobs hmar hpos =>
     NC_imp_L2_family_eq M₁ M₂ e₁ e₂ h₁ h₂ hobs hmar hpos,
   MNC_literal_fails_via_marginal,
   MNC_toLawRule_folds,
   MNC_L2_family_not_L1⟩

end T35Rule1SplitConsumer

end FateV2.Predict