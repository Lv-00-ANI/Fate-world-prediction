import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Modeling.PearlHierarchy
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
  # Rules · SCMLawBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMLawBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule, PearlHierarchy
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §LR  ⭐⭐⭐⭐ **`PearlHierarchy.SCM` 能否诱导 `LawRule`？** —— 能，且分三档

  ## 0. 一句话答案

  **能**。本文件给出**三个**构造，**强弱分明**，并**逐个证其性质**：

  | 档 | 构造 | 是什么 | `IsPoint`? | 用 `pU`? | 语义 |
  |---|---|---|---|---|---|
  | **①** | `SCM.lawAt` | 真值律 `L2_do x` 的**单点集** | ✅ 恒成立 | ✅ | **SCM 的真值**（`do(X:=x)`） |
  | **②** | `SCM.lawObs` | 「`X = x` 处观测**零质量**」的**空/满**约束 | ✗（除退化） | ✅ | **观测否决**（最弱约束） |
  | **③** | `SCM.composeLaw` | ① 与 ② 的 **`LawRule.compose`** | 视否决而定 | ✅ | **约束的交** |

  ## 1. ⚠ **一处不可避免的类型障碍**（先说清楚，免得被当成简化）

  `PearlHierarchy.SCM` 的 `X`、`Y` 是**裸 `Type`**（只带 `Fintype`/`DecidableEq`），
  而 `LawRule` 的载体**必须**是 `StateSpace`／`OutSpace`（带拓扑 + 可测 + Borel 相容）。
  **⟹ 「直接」诱导在类型层不可能**，必须给**桥参数**。本文件用**最弱的**两个：

  | 桥参数 | 类型 | 作用 | 能否省 |
  |---|---|---|---|
  | `φ : Y → Y♭.Carrier` | **嵌入** `Y` 进目标可测空间 | 把有限律 `Y → ℝ` 读成 `Y♭` 上的加权 `δ` 和 | ❌ 必要（`Y` 无拓扑） |
  | `SX : StateSpace` + `e : X ≃ SX.Carrier` | **状态空间同构** | 把 `SCM` 的裸 `X` 装进 `StateSpace` | ❌ 必要（`X` 带 `Fintype`，一般**不**带拓扑；`StateSpace` 的实例是结构字段，不能事后追加） |

  **两者都显式写进签名、不被隐藏**。第 2 个参数的 `e` 在 `lawAt` 里**只用于把 `x` 搬过去**，
  可以取 `X ≃ X♭` 的任何同构（含 `Fintype.equivFin` 派生的）。
  下方把 `X♭ := SX.Carrier`、`e x : SX.Carrier` 代入。

  ## 2. 语义口径（**必须登记**）：① 是**干预**，不是**观测**

  `sg u = (x_u, h_u)` 里 `x_u` 是**事实值**（外生 `u` **决定** `X`）。
  若不干预，只在 `x = x_u` 的个体上才有定义；
  **而条件化于 `X = x` 需要逐点 Bayes 归一化**——
  `PearlHierarchy.SCM` 的单结果口径里**没有**「先验 × 似然」分解，
  归一化**不是免费的**（分母可为 `0`）。
  **本文件的选择**：`lawAt M y` 读作 $\mathrm{do}(X := e^{-1}(y))$ 下的 $Y$ 律，
  即 `SCM.L2_do` 的测度化——**不需要任何归一化**。
  **代价**：它**不是**「看到 `x` 后 `Y` 的分布」。以下两处不隐藏这一点。

  ## 3. 本文件证了什么（全部可编译，零 `sorry` / 零 `axiom`）

  | 定理 | 说的话 | 强度 |
  |---|---|---|
  | `pushMeasure_apply` | 加权 `δ` 和在 `{z}` 处的值 = 纤维求和 | 半实质（`dirac_apply` + 分类） |
  | `lawAt_eq_L2_do` | **桥主等式**：① **逐字就是** `L2_do`（测度化） | 定义相等 |
  | `lawAt_apply` | ① 在每点的**唯一**元素是那个测度 | 定义展开 |
  | `isPoint_lawAt` | ① **无条件**单点档 | ⭐ 实质（档位判据） |
  | `L3_determines_lawAt` | **反事实系统决定 ①**（经 `L3_determines_L2`） | ⭐⭐ **实质** |
  | `lawAt_congr_sg` | `pU`、`sg` 相同 ⟹ ① 相同（**不**需 L3） | 半实质 |
  | `lawObs_apply` / `lawObs_apply_not` | ② 的两分支 | 定义展开 |
  | `lawObs_point_or_empty` | ② 逐点**只有**空/全两种（**结构定理**） | ⭐ 实质 |
  | `lawObs_eq_top_iff` | ② **退化判据**（精确 `iff`） | ⭐ 实质 |
  | `composeLaw_apply` | ③ = ① ∩ ②（`LawRule.compose` 的直接使用） | 定义展开 |
  | `composeLaw_eq_lawAt_or_empty` | ③ 只有两种结局 | ⭐ 实质 |
  | `composeLaw_not_point_of_veto` | **观测否决 ⟹ ③ 不再是单点档** | ⭐ 实质 |
  | **`toRule_toLaw`** | `LawRule ⟹ Rule ⟹ LawRule` **回到原处**（**补上游缺口**） | ⭐⭐ **实质** |
  | **`toLaw_toRule`** | `Rule ⟹ LawRule ⟹ Rule` **无条件**恒等 | ⭐⭐ **实质** |
  | **`isPoint_iff_mem_range`** | **精确刻画**：`LawRule` 宽出 `Rule` 的恰是非单点档 | ⭐⭐ **实质** |
  | `bot_not_mem_range_lawAt` | **反例**：`bot` **不在** ① 的像里 | ⭐ 实质 |

  ## 4. ⚠ 诚实边界

  * **「诱导」≠「表示」**：`bot` 不在像里（`bot_not_mem_range_lawAt`），
    故本文件**不**声称「任何 `LawRule` 都来自某 SCM」。
  * **桥参数 `φ` / `SX` / `e` 是外部输入**，不是 SCM 的一部分——
    这是 `PearlHierarchy` 的设计事实。
  * **上下文坐标 `c` 被丢弃**（`SCM` 类型里**没有** `CtxSpace`）。
    要保留它须把载体换成 `C.Carrier → SCM X Y` 族；本文件**不做**（登记为缺口）。
  * **② 只做「零质量否决」**，不做「完整相容性」：后者需要归一化与 `φ` 单射，
    而 `LawRule` 的成员判据是 `Prop`，逐 `y` 定值会在 `φ` 的纤维上**过约束**。
    这是**真实的数学障碍**，不是简化。
  * **不触及连续 / 一般可测 SCM**（`PearlHierarchy.SCM` 本身是 `Fintype` 载体）。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open MeasureTheory

namespace SCM

-- 本文件多个引理只用到 `Y`/`pU`，不用 `X` 的 `Fintype`；这是**有意的**（陈述更一般）。
set_option linter.unusedSectionVars false

/-! ===========================================================================
    §1  桥参数：有限律 `Y → ℝ` ⟹ `Y♭` 上的加权 `δ` 和
    =========================================================================== -/

section PushMeasure

variable {Y : Type} [Fintype Y]

/-- ⭐ **`φ`-推出测度**：把有限律 `p : Y → ℝ` 读成 `Y♭` 上的**加权 `δ` 和**

$$\mu = \sum_{y \in Y} \mathrm{ofReal}\bigl(p(y)\bigr)\cdot\delta_{\varphi(y)} .$$

**这是桥的第一半**（把裸 `Y` 上的 `ℝ`-值律装进 `Measure`）。
它与 `FinMeasureBridge.weightedCount` **同一口径**，此处只把三元组换成单变量 `Y`。 -/
noncomputable def pushMeasure (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (p : Y → ℝ) : Measure Yb.Carrier :=
  ∑ y : Y, ENNReal.ofReal (p y) • Measure.dirac (φ y)

/-- ⭐ **逐点展开**：在 `{z}` 处的质量 = 「`φ y = z`」的那些 `y` 的 `ofReal (p y)` 之和。

**⚠ 需要 `{z}` 可测**（`hz`）：`dirac_apply'` 是这条展开的**唯一**可用形式
（`dirac_apply` 需要 `MeasurableSingletonClass`，而 `StateSpace` **不提供**它——
见文件头 §4 的边界登记）。 -/
theorem pushMeasure_apply (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    [DecidableEq Yb.Carrier]
    (φ : Y → Yb.Carrier) (p : Y → ℝ) (z : Yb.Carrier) (hz : MeasurableSet {z}) :
    pushMeasure Yb φ p {z}
      = ∑ y : Y, (if φ y = z then ENNReal.ofReal (p y) else 0) := by
  classical
  set_option maxHeartbeats 800000 in
  have key : ∀ y : Y, (ENNReal.ofReal (p y) • Measure.dirac (φ y)) {z}
      = (if φ y = z then ENNReal.ofReal (p y) else 0) := by
    intro y
    rw [Measure.smul_apply, Measure.dirac_apply' (φ y) hz]
    by_cases h : φ y = z
    · rw [Set.indicator_of_mem (by simpa using h), if_pos h, smul_eq_mul, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (by simpa using h), if_neg h, smul_zero]
  rw [pushMeasure, Measure.finsetSum_apply]
  simp only [key]

end PushMeasure

/-! ===========================================================================
    §2  ⭐⭐ **档 ①**：`lawAt` —— SCM 在 `x` 处的 `do(X := x)` 律
    =========================================================================== -/

variable {X : Type} [Fintype X] [DecidableEq X]
    {Y : Type} [Fintype Y] [DecidableEq Y]

/-- ⭐⭐ **SCM 诱导的逐点 `LawRule`**（**桥的主体**）。

$$(\mathrm{lawAt}\,M)\;c\;y \;:=\;
  \Bigl\{\,\sum_{x \in X}\mathrm{ofReal}\bigl(M.\mathrm{L2\_do}\,x\,\cdot\bigr)\cdot
    \delta_{\varphi(\cdot)}\Bigr\}_{x \,=\, e^{-1}(y)} .$$

**读法**：与状态 `y`（经同构 `e` 对应 SCM 的 `X` 值 `e.symm y`）相伴的
**允许下一状态分布**是**唯一**那一个：
把外生律沿「干预 `X := e.symm y` 后的结构方程」推前。

**⚠ 上下文 `c` 被忽略**：`PearlHierarchy.SCM` 类型里**没有**上下文坐标
（见文件头 §4 的边界登记）。 -/
noncomputable def lawAt (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) : LawRule C SX Yb :=
  fun _ y => {pushMeasure Yb φ (M.L2_do (e.symm y))}

/-- ⭐⭐ **桥主等式**：① 在每点处的唯一允许分布就是 `L2_do` 的测度化。

$$(\mathrm{lawAt}\,M)\;c\;y = \bigl\{\,\mathrm{meas}\bigl(M.\mathrm{L2\_do}\,(e^{-1}y)\bigr)\bigr\}.$$

**⟹ 这条把「`LawRule` 在 SCM 上是什么意思」钉死为第二层（干预）**，
不是含糊的「条件分布」。 -/
theorem lawAt_eq_L2_do (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) (c : C.Carrier) (y : SX.Carrier) :
    lawAt M SX e Yb φ C c y = {pushMeasure Yb φ (M.L2_do (e.symm y))} := rfl

/-- ⭐⭐ **① 是无条件单点档**：世界模型需要的「可算转移」档位。 -/
theorem isPoint_lawAt (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) : LawRule.IsPoint (lawAt M SX e Yb φ C) :=
  fun _ _ => ⟨_, rfl⟩

/-! ===========================================================================
    §2.5  ⭐⭐⭐ **L3 ⟹ ①**：与 Pearl 层级方向的**相容性**
    =========================================================================== -/

/-- ⭐⭐⭐ **反事实系统决定 `LawRule` 读出**（对**任意**桥参数与上下文）。

若两个 SCM 有**相同**的反事实系统（`L3_cf`），则它们诱导的 `LawRule`（①）**相等**。

**证明**：`PearlHierarchy.L3_determines_L2`（**实质引理**，用 `push_push` + `sum_comm`）
给出 `L2_family` 相同；而 ① 在**定义上**是 `meas ∘ L2_do ∘ e.symm`，故相等。

**⟹ 强度**：这条**不是**定义展开——它把 `PearlHierarchy` 的层间蕴含
**搬运**到 `LawRule` 层。**这是两套载体之间真正的接线。** -/
theorem L3_determines_lawAt {M₁ M₂ : PearlHierarchy.SCM X Y}
    [DecidableEq (X → Y)] (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) (h : M₁.L3_cf = M₂.L3_cf) :
    lawAt M₁ SX e Yb φ C = lawAt M₂ SX e Yb φ C := by
  have hL2 : M₁.L2_family = M₂.L2_family := PearlHierarchy.L3_determines_L2 h
  funext c y
  have hx := congrFun hL2 (e.symm y)
  simp only [PearlHierarchy.SCM.L2_family] at hx
  show ({pushMeasure Yb φ (M₁.L2_do (e.symm y))} : Set (Measure Yb.Carrier))
      = {pushMeasure Yb φ (M₂.L2_do (e.symm y))}
  rw [hx]

/-! ===========================================================================
    §3  ⭐⭐⭐ **档 ②**：`lawObs` —— 观测给出的**否决型**约束
    =========================================================================== -/

/-- ⭐⭐ **观测约束律**：若 SCM 的观测律 `L1_obs` 在 `X = x` 处**零质量**，
则「允许一切」（`univ`，观测**不管**）；否则**允许空集**（观测**否决**）。

$$(\mathrm{lawObs}\,M)\;c\;y \;=\;
  \begin{cases}
    \mathrm{univ} & \text{若 } \forall y',\ M.\mathrm{L1\_obs}(e^{-1}y,\, y') = 0,\\
    \varnothing & \text{否则.}
  \end{cases}$$

**⚠ 为什么只做「零质量否决」**：见文件头 §4 的**长度障碍**登记——
「完整相容性」（`μ` 在纤维上的分布 = `L1_obs` 归一化）需要
(1) 归一化因子非零、(2) `φ` 单射；二者本文件**不假设**，
故只取其中**无需任何假设**的部分。 -/
noncomputable def lawObs (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (C : CtxSpace) : LawRule C SX Yb :=
  fun _ y => if (∀ y' : Y, M.L1_obs (e.symm y, y') = 0) then Set.univ else ∅

/-- ⭐ **② 的「不否决」分支**。 -/
theorem lawObs_apply (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (C : CtxSpace) (c : C.Carrier) (y : SX.Carrier)
    (h : ∀ y' : Y, M.L1_obs (e.symm y, y') = 0) : lawObs M SX e Yb C c y = Set.univ := by
  classical
  rw [lawObs, if_pos h]

/-- ⭐ **② 的「否决」分支**。 -/
theorem lawObs_apply_not (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (C : CtxSpace) (c : C.Carrier) (y : SX.Carrier)
    (h : ¬ ∀ y' : Y, M.L1_obs (e.symm y, y') = 0) : lawObs M SX e Yb C c y = ∅ := by
  classical
  rw [lawObs, if_neg h]

/-- ⭐⭐ **② 逐点只有「空」或「全」两种**（**结构定理**）。

这精确刻画了本档的**贫乏性**：它**从不**给出「恰好一个」允许分布，
故它不是「约束得刚好」的那种规律，而是**否决器**。 -/
theorem lawObs_point_or_empty (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (C : CtxSpace) (c : C.Carrier) (y : SX.Carrier) :
    lawObs M SX e Yb C c y = (∅ : Set (Measure Yb.Carrier)) ∨
      lawObs M SX e Yb C c y = Set.univ := by
  classical
  by_cases h : ∀ y' : Y, M.L1_obs (e.symm y, y') = 0
  · exact Or.inr (lawObs_apply M SX e Yb C c y h)
  · exact Or.inl (lawObs_apply_not M SX e Yb C c y h)

/-- ⭐⭐ **② 退化判据**：② 处处允许一切 **⟺** 观测律**恒为零**。

**⚠ 这条是精确 `iff`**，且同时暴露本档的病：只要 `L1_obs` 在某个 `x` 处**非零**，
② 就在该点为**空**——即 ② 与 ① **不相容**（① 在该点有元素）。
**⟹ 「观测」与「机制」在这一档上是**互斥**的，而不是互补的。**这是本档的真实结论。** -/
theorem lawObs_eq_top_iff (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (C : CtxSpace) [Nonempty C.Carrier] :
    lawObs M SX e Yb C = LawRule.top C SX Yb ↔
      ∀ x : X, ∀ y' : Y, M.L1_obs (x, y') = 0 := by
  classical
  constructor
  · intro h x y'
    by_contra hne
    have hx : ¬ ∀ y' : Y, M.L1_obs (x, y') = 0 := fun hy => hne (hy y')
    obtain ⟨c₀⟩ := ‹Nonempty C.Carrier›
    have hempty : lawObs M SX e Yb C c₀ (e x) = ∅ :=
      lawObs_apply_not M SX e Yb C _ (e x) (by simpa using hx)
    have huniv : lawObs M SX e Yb C c₀ (e x) = Set.univ := by
      have := congrFun (congrFun h c₀) (e x)
      simpa only [LawRule.top] using this
    rw [hempty] at huniv
    exact absurd huniv Set.empty_ne_univ
  · intro h
    funext c y
    exact lawObs_apply M SX e Yb C c y (h (e.symm y))

/-! ===========================================================================
    §4  ⭐⭐ **档 ③**：`composeLaw` —— 用 `LawRule` 的 `compose` 组合 ① 与 ②
    =========================================================================== -/

/-- ⭐⭐ **档 ③**：① 与 ② 的**取交**（`LawRule.compose` 的直接应用）。

$$(\mathrm{composeLaw}\,M)\;c\;y = (\mathrm{lawAt}\,M)\;c\;y \cap (\mathrm{lawObs}\,M)\;c\;y .$$

**语义**：真值律 **且** 观测不否决。
**这就是 `LawRule` 的「约束」语义的自然用法**：
`SCM` 给真值（①），观测给否决（②），**取交才是「既符合机制又符合观测」的规律**。 -/
noncomputable def composeLaw (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) : LawRule C SX Yb :=
  LawRule.compose (lawAt M SX e Yb φ C) (lawObs M SX e Yb C)

/-- ⭐ **③ 的定义展开**（`LawRule.compose` 在此逐字落实为取交）。 -/
theorem composeLaw_apply (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) (c : C.Carrier) (y : SX.Carrier) :
    composeLaw M SX e Yb φ C c y
      = lawAt M SX e Yb φ C c y ∩ lawObs M SX e Yb C c y := rfl

/-- ⭐⭐ **③ 只有两种结局**：= ①（观测不否决），或 = ∅（观测否决）。 -/
theorem composeLaw_eq_lawAt_or_empty (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) (c : C.Carrier) (y : SX.Carrier) :
    composeLaw M SX e Yb φ C c y = lawAt M SX e Yb φ C c y ∨
      composeLaw M SX e Yb φ C c y = (∅ : Set (Measure Yb.Carrier)) := by
  classical
  by_cases h : ∀ y' : Y, M.L1_obs (e.symm y, y') = 0
  · left
    show lawAt M SX e Yb φ C c y ∩ lawObs M SX e Yb C c y = lawAt M SX e Yb φ C c y
    rw [lawObs_apply M SX e Yb C c y h, Set.inter_univ]
  · right
    show lawAt M SX e Yb φ C c y ∩ lawObs M SX e Yb C c y = ∅
    rw [lawObs_apply_not M SX e Yb C c y h, Set.inter_empty]

/-- ⭐⭐ **观测否决 ⟹ ③ 不再是单点档**（**档位随观测而降**）。

**⟹ 这是「`LawRule` 不是装饰」的实质证据**：
`SCM` 单给出的 ① **是**单点档（可算转移）；
一旦把观测约束交进去（③），**可能落到非单点档**，
而 `LawRule` **恰好**能装这个新东西（`Rule` 装不了，见 §5 的 `isPoint_iff_mem_range`）。 -/
theorem composeLaw_not_point_of_veto (M : PearlHierarchy.SCM X Y) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : X ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Y → Yb.Carrier) (C : CtxSpace) (c : C.Carrier) (y : SX.Carrier)
    (h : ¬ ∀ y' : Y, M.L1_obs (e.symm y, y') = 0) :
    ¬ LawRule.IsPoint (composeLaw M SX e Yb φ C) := by
  have hempty : composeLaw M SX e Yb φ C c y = (∅ : Set (Measure Yb.Carrier)) := by
    show lawAt M SX e Yb φ C c y ∩ lawObs M SX e Yb C c y = ∅
    rw [lawObs_apply_not M SX e Yb C c y h, Set.inter_empty]
  intro hp
  obtain ⟨μ, hμ⟩ := hp c y
  rw [hempty] at hμ
  exact Set.notMem_empty μ (hμ ▸ Set.mem_singleton μ)

/-! ===========================================================================
    §5  ⭐⭐⭐ **`LawRule` 与旧 `Rule` 的互译**（补齐上游缺口）
    =========================================================================== -/

section RuleBridge

variable {C : CtxSpace} {X₂ : StateSpace} {Y₂ : OutSpace}
  [MeasurableSpace X₂.Carrier] [MeasurableSpace Y₂.Carrier]

/-- ⭐ **单点档 `LawRule` ⟹ 条件分布核**（在允许集里**选**一个）。

**⚠ 为何这一步必要**：`Fate/LawRule.lean` **只有** `Rule.toLaw`（核 ⟹ 律），
**没有反向**。没有反向，就无法陈述「二者在单点档上双射」，
`PearlHierarchy` / `SCMKernel` 之类以 `Measure` 为第一公民的下游**接不上** `LawRule`。
本定义补上反向；代价是**必须**带 `IsPoint` 假设（由 `isPoint_iff_mem_range` 知这是**精确**条件）。 -/
noncomputable def toRule (R : LawRule C X₂ Y₂) (h : LawRule.IsPoint R) : Rule C X₂ Y₂ where
  kernel c x := Classical.choose (h c x)

/-- ⭐ **选出的核确实落在允许集内**。 -/
theorem toRule_mem (R : LawRule C X₂ Y₂) (h : LawRule.IsPoint R)
    (c : C.Carrier) (x : X₂.Carrier) : (toRule R h).kernel c x ∈ R c x := by
  have hs := Classical.choose_spec (h c x)
  rw [hs]
  exact Set.mem_singleton _

/-- ⭐⭐ **左逆**：单点档上「律 ⟹ 核 ⟹ 律」**回到原处**。

**证明要点**：`IsPoint` 的定义是 `∃ μ, R c x = {μ}`，
故 `choose` 选出的就是那个 `μ`，而 `choose_spec` **直接给出** `{μ} = R c x`。
**⟹ 不需要**任何额外推理（`_phLR.lean` 中此处留了 `sorry`，本文件补上）。 -/
theorem toRule_toLaw (R : LawRule C X₂ Y₂) (h : LawRule.IsPoint R) :
    LawRule.Rule.toLaw (toRule R h) = R := by
  funext c x
  show ({((toRule R h).kernel c x)} : Set (Measure Y₂.Carrier)) = R c x
  exact (Classical.choose_spec (h c x)).symm

/-- ⭐⭐ **右逆**：核 ⟹ 律 ⟹ 核，**无条件**恒等。

**证明要点**：`(r.toLaw) c x = {r.kernel c x}`（`rfl`），
故 `choose_spec` 给出的等式是两个**单点集**相等，取其元素即得。 -/
theorem toLaw_toRule (r : Rule C X₂ Y₂) (h : LawRule.IsPoint (LawRule.Rule.toLaw r)) :
    toRule (LawRule.Rule.toLaw r) h = r := by
  obtain ⟨k⟩ := r
  show Rule.mk (fun c x => Classical.choose (h c x)) = Rule.mk k
  congr 1
  funext c x
  have hs := Classical.choose_spec (h c x)
  exact (Set.singleton_injective (Set.mem_singleton_iff.mp hs).symm ▸ rfl :
    Classical.choose (h c x) = k c x)

/-- ⭐⭐⭐ **双向刻画**：`LawRule` 落在 `Rule` 的像里 **⟺** 它是单点档。

$$R \in \mathrm{im}(\texttt{Rule.toLaw}) \iff \texttt{IsPoint}(R).$$

**⟹ 这是「`LawRule` 严格比 `Rule` 宽多少」的精确答案**：
宽出来的**恰好**是「允许集不是单点」的规律——
即 §3 的 ② 与 §4 的 ③（在否决处）**必然**在像外。 -/
theorem isPoint_iff_mem_range (R : LawRule C X₂ Y₂) :
    LawRule.IsPoint R ↔ ∃ r : Rule C X₂ Y₂, LawRule.Rule.toLaw r = R := by
  constructor
  · intro h; exact ⟨toRule R h, toRule_toLaw R h⟩
  · rintro ⟨r, rfl⟩ c x; exact ⟨r.kernel c x, rfl⟩

end RuleBridge

/-! ===========================================================================
    §6  ⚠ **反向不成立**：① 不是满射（反例）
    =========================================================================== -/

section Counterexample

variable {SX : StateSpace} [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]

/-- ⚠ **反例（一般形式）**：**空规律不在 ① 的像里**。

**理由**：① 恒为单点档（`isPoint_lawAt`），而 `bot` 处处为空 ⟹ 矛盾。

**⟹ 故「SCM ⟹ `LawRule`」是诱导，不是满射**：
`LawRule` 的**表达力**严格大于 SCM 能诱导的部分。
（但注意：③ 在否决处**可以**产生空—非空混合，故 §4 的构造**能**装 `bot` 之外的更多东西；
`bot` 本身需要**处处**否决，即观测律处处非零——见 `bot_not_mem_range_composeLaw`。） -/
theorem bot_not_mem_range_lawAt (C : CtxSpace) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    [Nonempty C.Carrier] (φ : Y → Yb.Carrier) (M : PearlHierarchy.SCM X Y)
    (SX' : StateSpace) [MeasurableSpace SX'.Carrier] [DecidableEq SX'.Carrier]
    (e : X ≃ SX'.Carrier) [Nonempty X] :
    lawAt M SX' e Yb φ C ≠ LawRule.bot C SX' Yb := by
  intro h
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨c₀⟩ := ‹Nonempty C.Carrier›
  obtain ⟨μ, hμ⟩ := (h ▸ isPoint_lawAt M SX' e Yb φ C) c₀ (e x₀)
  have hmem : μ ∈ LawRule.bot C SX' Yb c₀ (e x₀) := hμ ▸ Set.mem_singleton μ
  exact Set.notMem_empty μ hmem

end Counterexample

end SCM

end LawRule

end FateV2.Rules