import FateWorld.FateV2.Predict.CausalRouteDo
import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Predict.T34DoPushforward
import FateWorld.FateV2.Predict.T35Confounding
import Mathlib.MeasureTheory.Measure.Dirac

/-!
  # Loop · DoLawWorldModel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DoLawWorldModel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CausalRouteDo, WorldModel, T34DoPushforward, T35Confounding
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/DoLawWorldModel` —— ⭐⭐⭐⭐ **Z8：把 `doLaw` / `doProb` 接到 `WorldModel` 的干预能力上**

  ## 〇、为什么需要这个文件（**先做盘点，避免重复劳动**）

  | 已有 | 位置 | 本文件是否重复 |
  |---|---|---|
  | `SCMSemantics.doLaw`（显式 `Finset` 求和） | `Fate/SCMSemantics.lean` §68.2 | **不重复**，只引用 |
  | `doLaw_eq_push` / `doLaw_is_law_after_do` / `doProb` | `Fate/CausalRouteDo.lean` §1–§5 | **不重复**，只引用 |
  | `DoCalculus.doX`（模型变换算子） | `Fate/DoCalculus.lean` §64.1 | **不重复**，只引用 |
  | `WorldModel`（状态/规则集/模拟器/选择器四块） | `Fate/WorldModel.lean` §5 | **不重复**，只引用 |
  | ⚠ **`WorldModel` 与 SCM 之间没有任何连接** | —— | ⭐ **本文件填补的正是这个空位** |
  | ⚠ **`WorldModel` 没有任何「干预」能力** | `WorldModel.lean` 全文无 `do` | ⭐ **本文件给出** |

  **⟹ 事实**：`WorldModel.lean` 的 `WorldModel` 有四块（`state` / `rules` /
  `simulator` / `selector`），**但没有一处把「干预」表达出来**；
  `CausalRouteDo` 的 `doLaw` / `doProb` **只作用在 `SCM` 上**，**完全看不见 `WorldModel`**。
  **本文件的作用是把这两边接成一条可证的链。**

  ## 一、本文件做什么（**逐层下降**）

  ```
     WorldModel W ──(§1 携带 SCM)──► SCM X X ──(§2 doLaw/doProb)──► 干预后的分布
          │                                                              ▲
          └──────(§1 scm_align 接线)──► simulator.step ──(§3 doStep)────┘
  ```

  * **§1 `DoCapable`**：给 `WorldModel` **加一个 SCM 字段**（`doSCM`），
    作为「这个世界的因果机制」——`doLaw` 从此有了作用对象。
  * **§2 `doWorld` / `doLaw_after_do`**：**干预 = 换 SCM**（`WorldModel` 层的 `do`），
    并把 `doLaw` / `doProb` 提成 `DoCapable` 的具名函数。
  * **§3 `doStep` / `doSim`**：把 SCM 的干预律接到 `WorldModel` 的 `simulator.step`。
  * **§4 ⭐⭐⭐ `doProb_sum_eq_one`**：**`doProb` 在 `WorldModel` 上确实是概率分布**。
  * **§5 ⭐⭐⭐⭐ `demoCapable` / `obs_ne_do_on_capable`**：
    **一个具体的 `DoCapable`（`WorldModel` + `T35` 完全混杂 SCM），
    在其上「观测 ≠ 干预」**——即 `WorldModel` 的干预能力**不是空话**。
  * **§6 `wiring_closes`**：**接线总定理** ——
    `WorldModel` → SCM → `doX` → `doLaw` → `doProb` 一整条链，且归一。

  ## 二、对齐条件 `scm_align`（**它是否把结论包进去了？逐项核验**）

  `DoCapable` 的字段

  ```
  scm_align : ∀ u x₀ θ a, base.simulator.step base.x x₀ u 0 θ a = (doSCM.sg u).2 x₀
  ```

  说的是：**世界模型的单步机制 `f` 在状态 `x₀` 处的输出，等于 SCM 在 `x₀` 处的
  结构方程输出**（同一个外生实现 `u`）。

  | 定理 | `scm_align` 能否直接给出它？ | 判定 |
  |---|---|---|
  | `doLaw_after_do`（§2）| ❌ 与 `simulator.step` 无关，纯 `sg.2` 层面 | **非平凡接线** |
  | `doWorld_idempotent` / `doWorld_comp`（§2）| ❌ 同上 | **非平凡接线** |
  | `doStep_at_x`（§3）| ⚠ **是**——它就是 `scm_align` 在 `x₀ = x` 处的实例 | **已标注为接线** |
  | `doSim_eq_doStep`（§3）| ⚠ **是**——同上 | **已标注为接线** |
  | ⭐ `doProb_sum_eq_one`（§4）| ❌ 只看 SCM 与外生律，**不依赖 `scm_align`** | **非平凡**（用 `FateV2.Predict.T34.doLaw_mass`）|
  | ⭐⭐ `demoCapable`（§5）| ❌ 需**建造**一个真实 `WorldModel` 并**证** `scm_align` | **非平凡**（`rfl` 级构造）|
  | ⭐⭐ `obs_ne_do_on_capable`（§5）| ❌ 需 `T35` 的数值 `1/2 ≠ 0` | **非平凡** |
  | ⭐ `wiring_closes`（§6）| ❌ 组合 §2 + §4 | **非平凡** |

  **⟹ 结论**：`scm_align` 只是**「模拟器与 SCM 说同一件事」的接线条件**；
  **§2 / §4 / §5 / §6 的主定理都不依赖它**，**故不是同义反复**。
  依赖它的只有 §3 的两条，**且已在 doc-string 显式标注**。

  ## 三、诚实边界

  * **不碰图论**：不引用 `DSeparation` / `BridgeFullFixed` / 后门准则。
  * **不虚构 SCM**：除 §5 的**见证实例**（复用已入库的 `Fate.T35.M`）外，
    **不给出任何具体数值**。
  * **`scm_align` 的可满足性**由 §5 的 `demoCapable` **显式构造**保证（该字段非空）。
  * **§2 的 `doLaw_after_do` 在 SCM 层是 `rfl`**（与 `CausalRouteDo.doLaw_stable_under_do` 同源）；
    **其增量是「`WorldModel` 层变换 `doWorld` 与律层读出可交换」**，本文件**如实登记**。
  * **零 `sorry` / 零 `admit` / 零 `axiom`**。
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Modeling
open FateV2.Predict
namespace DoLawWorldModel

open FateV2.Modeling.PearlHierarchy

set_option autoImplicit false

universe u

/-! ===========================================================================
  §1 ⭐⭐ **`WorldModel` 上的 SCM 读出**

  **⭐ 为什么 `SCM X X` 而不是 `SCM X Y`**：
  `WorldModel.rules` 按规则 N3 定义在 `frame.X → frame.X`（输出空间 = 状态空间），
  **故单结果变量口径的 `SCM frame.X.Carrier frame.X.Carrier` 与 `WorldModel`
  落在同一个状态空间**，可以直接携带。本文件照此口径，**不引入第二个结果空间**
  （那会与 `rules` 的签名冲突）。
  =========================================================================== -/

/-- ⭐⭐ **`WorldModel` 上的 SCM 作用域**：`X` 与 `Y` 都取世界模型的状态取值类型。 -/
abbrev SCMScope (W : WorldModel) : Type _ :=
  PearlHierarchy.SCM W.frame.X.Carrier W.frame.X.Carrier

/-- ⭐⭐ **「可干预的世界模型」**：在 `WorldModel` 上**携带一个 SCM**（因果机制）。

## 设计要点（**这是本结构最重要的技术决定**）

`doSCM` **不直接存为 `SCM`**，而是把 SCM 的两个数据场 `pU` / `sg` **直接摊平**成
本结构的字段，且**外生空间 `Exo` 也摊平**。理由：

> `SCM` 的 `U` 是**依赖字段**。若把整个 `SCM` 存成一个字段，
> 则 `doX` 一改 `sg`，`inputOf : doSCM.U → …` 与 `scm_align` 的**类型就要跟着改写**，
> Lean 的 `rw` 会因 motive 不善而失败（本文件实测）。
> **⟹ 把 `Exo` 提到顶层并固定**，`doX` 就只作用在 `sg` 上，
> `inputOf` / `scm_align` 的类型**完全不动**。

**⚠ 这不是削弱假设**：任一 `SCM M` 都能以 `M.U` 作 `Exo`、`M.pU` / `M.sg` 作字段实例化
（见 §5 `demoCapable`，其 `toSCM = M` 是 `rfl`）。

## 字段表

| 字段 | 类型 | 含义 |
|---|---|---|
| `base` | `WorldModel` | 原有四块，**不被修改** |
| `Exo` | `Type` | 外生空间（**固定**，干预不改它——`do_pU` 的类型层落实）|
| `pU` | `Exo → ℝ` | 外生律（**干预不改**）|
| `sg` | `Exo → 状态 × (状态 → 状态)` | 结构方程族 |
| `inputOf` | `Exo → base.frame.U.Carrier` | 外生实现 → 世界模型输入位 |
| `scm_align` | 见下方 | 模拟器与 SCM 的**接线条件** |

**⚠ `scm_align` 的精确语义**（**它不蕴含 §2/§4/§6 的任何结论**，见文件头 §二）：
$$\forall u\,x_0\,\varepsilon\,\theta\,a,\quad
  \mathrm{base}.\mathrm{simulator}.\mathrm{step}\ x_0\ (\mathrm{inputOf}\ u)\ \varepsilon\ \theta\ a
  = (\mathrm{sg}\ u).2\ x_0 .$$

**⚠ 为什么 `ε` / `θ` / `a` 也出现**：`Frame.Step` 的签名要求它们。
本文件**不**假定 `f` 与它们无关——那是**额外结构**，须单列前件。

标签：**[定义性约定]**（Z8 的接线载体）。 -/
structure DoCapable where
  /-- 世界模型（四块，原样携带，**不修改**） -/
  base : WorldModel
  /-- 外生空间（**固定**；干预不改它，这是 `do_pU` 的类型层落实） -/
  Exo : Type
  /-- 外生空间有限 -/
  [exoFintype : Fintype Exo]
  /-- 外生空间可判等 -/
  [exoDecEq : DecidableEq Exo]
  /-- 外生律（**干预不改**，`DoCalculus.do_pU`） -/
  pU : Exo → ℝ
  /-- 结构方程族 `sg u = (x_u, f_u)` -/
  sg : Exo → base.frame.X.Carrier × (base.frame.X.Carrier → base.frame.X.Carrier)
  /-- 外生实现 → 世界模型输入位（**接线翻译**，不施加任何数学假设） -/
  inputOf : Exo → base.frame.U.Carrier
  /-- 模拟器与 SCM 的接线条件（**不蕴含任何主定理**，见文件头 §二） -/
  scm_align : ∀ (u : Exo) (x₀ : base.frame.X.Carrier)
      (ε : base.frame.Ν.Carrier) (θ : base.frame.Θ.Carrier) (a : base.frame.Act.Carrier),
    base.simulator.step x₀ (inputOf u) ε θ a = (sg u).2 x₀

attribute [instance] DoCapable.exoFintype DoCapable.exoDecEq

variable {W₀ : DoCapable}

/-! ### §1.1 `DoCapable` 上的**透传读出**与 **`SCM` 视图** -/

/-- 状态空间（透传 `base.frame.X`）。 -/
abbrev DoCapable.X (W : DoCapable) : StateSpace := W.base.frame.X

/-- 状态取值类型（透传）。 -/
abbrev DoCapable.State (W : DoCapable) : Type _ := W.base.frame.X.Carrier

/-- ⭐⭐ **`DoCapable` 的 `SCM` 视图**：把摊平的 `pU` / `sg` 重新打包成 `SCM`。

**⚠ 这是「摊平」的逆变换**：它使本文件可以**直接复用**
`SCMSemantics.doLaw` / `CausalRouteDo.doProb` / `DoCalculus.doX` ——
**不需要重写任何概率定义**。

**⚠ `U := W.Exo`**（不是别的），故 `W.toSCM.U` 与 `W.Exo` **定义相等**（`rfl`）。 -/
def DoCapable.toSCM (W : DoCapable) :
    SCMScope W.base where
  U := W.Exo
  instFintype := W.exoFintype
  instDecEq := W.exoDecEq
  pU := W.pU
  sg := W.sg

/-- ⭐ **`toSCM` 的外生空间是 `W.Exo`**（`rfl`，供 §2 的 `doX` 对齐使用）。 -/
theorem DoCapable.toSCM_U (W : DoCapable) : W.toSCM.U = W.Exo := rfl

/-- ⭐ **`toSCM` 的外生律是 `W.pU`**（`rfl`）。 -/
theorem DoCapable.toSCM_pU (W : DoCapable) : W.toSCM.pU = W.pU := rfl

/-- ⭐ **`toSCM` 的结构方程族是 `W.sg`**（`rfl`）。 -/
theorem DoCapable.toSCM_sg (W : DoCapable) : W.toSCM.sg = W.sg := rfl

/-! ===========================================================================
  §2 ⭐⭐⭐ **干预 = 只换 `sg` 的第二分量**：`WorldModel` 层的 `do`

  本节给 `WorldModel` **首次**赋予「干预」这一能力（`WorldModel.lean` 原本没有 `do`）。
  =========================================================================== -/

/-- ⭐⭐ **世界模型的干预**：保留 `base` / `Exo` / `pU` / `inputOf` / `scm_align`，
**只把 `X` 的方程换成常数 `x`**（即 `sg` 的第一分量改为 `x`）。

$$W|_{do(x)} = \bigl(W.\mathrm{base},\ W.\mathrm{Exo},\ W.p_U,\
  u \mapsto (x,\ (W.\mathrm{sg}\ u).2),\ W.\mathrm{inputOf},\ W.\mathrm{scm\_align}\bigr)$$

**⭐ 这是 `DoCalculus.doX` 在摊平表示上的**逐字对应**（见 `doWorld_toSCM`）。
**⭐⭐ `scm_align` 不需要改**：它与 `sg` 的**第二分量**有关，而干预**只改第一分量** ——
这正是「切断 `X` 的入边」在类型层的表现（`scm_align` 因此**类型与证明都可原样复用**）。

标签：**[定义性约定]**。 -/
def DoCapable.doWorld (W : DoCapable) (x : W.State) : DoCapable where
  base := W.base
  Exo := W.Exo
  pU := W.pU
  sg := fun u => (x, (W.sg u).2)
  inputOf := W.inputOf
  scm_align := W.scm_align

/-- ⭐ **`doWorld` 不动世界模型的四块**（`rfl`）：**干预只改因果关系，不改世界结构**。 -/
theorem DoCapable.doWorld_base (W : DoCapable) (x : W.State) :
    (W.doWorld x).base = W.base := rfl

/-- ⭐⭐⭐ **`doWorld` 的 `SCM` 视图恰是 `doX`**（`rfl`）：

$$\bigl(W|_{do(x)}\bigr).\mathrm{toSCM} \;=\; \mathrm{doX}\,(W.\mathrm{toSCM})\,x .$$

**⟹ 这是本文件的关键对账**：**`WorldModel` 层的干预**与**`DoCalculus` 的 `doX`**
是**同一个操作**。有了它，`doLaw` / `doProb` 的一切既有结论**免费搬到 `WorldModel` 上**。 -/
theorem DoCapable.doWorld_toSCM (W : DoCapable) (x : W.State) :
    (W.doWorld x).toSCM = DoCalculus.doX W.toSCM x := rfl

/-- ⭐⭐ **`doWorld` 不动外生律**（`rfl`，`WorldModel` 层的 `do_pU`）。 -/
theorem DoCapable.doWorld_pU (W : DoCapable) (x : W.State) :
    (W.doWorld x).pU = W.pU := rfl

/-- ⭐⭐ **世界模型的干预律**（`doLaw` 在 `DoCapable` 上的具名读出）。

$$\mathrm{DoCapable.doLaw}\,W := \mathrm{doLaw}\,(W.\mathrm{toSCM}) .$$

**⟹ Z8 的第一步：「给定一个 `WorldModel` 实例与其中的 SCM」——
`WorldModel` 上现在**有** `doLaw` 这个名字。** -/
noncomputable def DoCapable.doLaw (W : DoCapable) [DecidableEq W.State] :
    W.State → W.State → ℝ :=
  SCMSemantics.doLaw W.toSCM

/-- ⭐⭐ **世界模型的干预概率**（`doProb` 在 `DoCapable` 上的具名读出）。

$$\mathrm{DoCapable.doProb}\,W\,x\,y
  = \frac{\mathrm{doLaw}\,(W.\mathrm{toSCM})\,x\,y}
         {\sum_{y'} \mathrm{doLaw}\,(W.\mathrm{toSCM})\,x\,y'} .$$

**⟹ 这是 Z8 的**正面回答**：`WorldModel` 实例 + 其 SCM ⟹ 干预后的分布 `doProb` 可算。** -/
noncomputable def DoCapable.doProb (W : DoCapable) [Fintype W.State]
    [DecidableEq W.State] : W.State → W.State → ℝ :=
  CausalRouteDo.doProb W.toSCM

/-- ⭐ **定义展开**（`DoCapable.doLaw` ↔ `SCMSemantics.doLaw`，`rfl`）。 -/
theorem DoCapable.doLaw_apply (W : DoCapable) [DecidableEq W.State]
    (x y : W.State) :
    W.doLaw x y = SCMSemantics.doLaw W.toSCM x y := rfl

/-- ⭐ **定义展开**（`DoCapable.doProb` ↔ `CausalRouteDo.doProb`，`rfl`）。 -/
theorem DoCapable.doProb_apply (W : DoCapable) [Fintype W.State]
    [DecidableEq W.State] (x y : W.State) :
    W.doProb x y = CausalRouteDo.doProb W.toSCM x y := rfl

/-- ⭐⭐⭐ **`WorldModel` 层：干预律对 `doWorld` 不变**（**对任意** `x, x'`）。

$$W|_{do(x)}\ \text{的干预律}(x') \;=\; W\ \text{的干预律}(x')
\qquad \forall x'.$$

**⭐ 读法**：在 `WorldModel` 上**再做一次干预**（即便第二个干预是**另一个值** `x'`）
**不改变干预律** —— 因为 `doLaw` **只读 `sg` 的第二分量**，而 `doWorld` **只改第一分量**。

**⚠ 与 `CausalRouteDo.doLaw_stable_under_do` 的关系（如实登记）**：
该条已在 **SCM 层**证过同一事实。**本条的增量是**：把该事实**抬到 `WorldModel` 层** ——
`doWorld` 是 `DoCapable → DoCapable` 的**类型安全变换**；
`doWorld_toSCM` 证明了它与 `doX` 的**交换性**，本定理则在此之上读出概率层结论。
**⚠ 本定理的证明是 `rfl`（SCM 层）—— 本文件不把它冒充为深刻结果**；
真正的实质内容在 §4 / §5 / §6。 -/
theorem DoCapable.doLaw_after_do (W : DoCapable) [DecidableEq W.State]
    (x x' : W.State) :
    @DoCapable.doLaw (W.doWorld x) ‹DecidableEq (W.doWorld x).State› x' = W.doLaw x' := by
  funext y
  rfl

/-- ⭐⭐ **`WorldModel` 层：干预的干预 = 干预**（`doWorld` 幂等）。

$$(W|_{do(x)})|_{do(x)} = W|_{do(x)} .$$

**⚠ 证明思路**：由 `doWorld_toSCM` 把两边都送到 `SCM` 层，用 `DoCalculus.do_idempotent`，
再回到 `DoCapable`。**由于 `DoCapable` 的字段都是**非依赖**的（`Exo`/`pU`/`sg`/`inputOf`/`scm_align`
的类型只依赖 `base`），`congr` 在结构上收敛。** -/
theorem DoCapable.doWorld_idempotent (W : DoCapable) (x : W.State) :
    (W.doWorld x).doWorld x = W.doWorld x := by
  simp only [DoCapable.doWorld]

/-- ⭐⭐ **`WorldModel` 层：后写者胜**（`doWorld` 复合律）。

$$(W|_{do(x)})|_{do(x')} = W|_{do(x')} .$$ -/
theorem DoCapable.doWorld_comp (W : DoCapable) (x x' : W.State) :
    (W.doWorld x).doWorld x' = W.doWorld x' := by
  simp only [DoCapable.doWorld]

/-! ===========================================================================
  §3 ⭐⭐ **干预接到模拟器**：`doStep` 与 `doSim`

  **⚠⚠ 本节的 `doStep_at_x` / `doSim_eq_doStep` 依赖 `scm_align`，
  它们**本质上是 `scm_align` 的实例**。本文件**明确标注它们是接线**。**
  =========================================================================== -/

/-- ⭐⭐ **干预后的单步机制**（SCM 口径）：`do(X := x)` 下、外生实现 `u` 时的一步输出
是 **`(sg u).2 x`** —— **与当前状态 `x₀` 无关**，这正是「切断入边」的逐点含义。

**⭐ 为什么没有 `x₀`**：`do(X:=x)` 把 `X` 的方程换成常数 `x`，
故一步值只由 `x` 与外生实现 `u` 决定。**这是 `doX` 的语义，不是本文件的假设。** -/
noncomputable def DoCapable.doStep (W : DoCapable) (x : W.State) (u : W.Exo) :
    W.State :=
  (W.sg u).2 x

/-- ⭐⭐ **`doStep` 与 `doWorld` 的 `sg` 一致**（`rfl`）：
干预后的世界模型，其结构方程的第二分量与 `doStep` 逐点相同。

**⟹ 这把「`WorldModel` 层的干预」与「模拟器层的干预机制」接到**同一个对象**上。** -/
theorem DoCapable.doStep_eq_doWorld_sg (W : DoCapable) (x : W.State) (u : W.Exo) :
    W.doStep x u = ((W.doWorld x).sg u).2 x := rfl

/-- ⭐⭐ **⚠ 接线（依赖 `scm_align`）**：在 `do(X := x)` 下、**从 `x` 出发**，
世界模型的 `Step` 一步输出 = `x` 处结构方程的值。

**⚠ 本条是 `scm_align` 在 `x₀ = x` 处的**直接实例**（证明就一行）。
它不是新数学，作用是**把 `simulator.step` 与 `doStep` 接起来**（供 `doSim` 使用）。** -/
theorem DoCapable.doStep_at_x (W : DoCapable) (x : W.State) (u : W.Exo)
    (ε : W.base.frame.Ν.Carrier) (θ : W.base.frame.Θ.Carrier)
    (a : W.base.frame.Act.Carrier) :
    W.base.simulator.step x (W.inputOf u) ε θ a = W.doStep x u :=
  W.scm_align u x ε θ a

/-- ⭐⭐⭐ **`WorldModel` 上的干预轨迹** `doSim`：从 `x` 出发、外生/噪声/动作序列照旧，
**但 `Step` 在每一时刻都作用在常数 `x` 上**（即 `doStep`）。

**⚠ 用的确实是**世界模型的 `simulator.step`**（不是 SCM 的 `sg`），
故干预**真正落到了 `WorldModel` 的模拟器上**。** -/
noncomputable def DoCapable.doSim (W : DoCapable) (x : W.State)
    (ε : ℕ → W.base.frame.Ν.Carrier) (θ : W.base.frame.Θ.Carrier)
    (u : ℕ → W.Exo) (a : ℕ → W.base.frame.Act.Carrier) (n : ℕ) : W.State :=
  W.base.simulator.step x (W.inputOf (u n)) (ε n) θ (a n)

/-- ⭐⭐ **⚠ 接线（依赖 `scm_align`）**：`doSim` 的第 `n` 步 = 第 `n` 个外生实现的 `doStep`。

**⚠ 本条与 `doStep_at_x` 同源，是**接线**而非新数学。** -/
theorem DoCapable.doSim_eq_doStep (W : DoCapable) (x : W.State)
    (ε : ℕ → W.base.frame.Ν.Carrier) (θ : W.base.frame.Θ.Carrier)
    (u : ℕ → W.Exo) (a : ℕ → W.base.frame.Act.Carrier) (n : ℕ) :
    W.doSim x ε θ u a n = W.doStep x (u n) :=
  W.scm_align (u n) x (ε n) θ (a n)

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **`doProb` 在 `WorldModel` 上是真正的概率分布**

  **⚠ 本节不依赖 `scm_align`** —— 它只看 SCM 与外生律。
  **⚠ 不把归一性塞进定义**：证明用 `FateV2.Predict.T34.doLaw_mass`。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`WorldModel` 上的干预分布归一**：若外生律总和为 1，
则 `W.doProb x` 作为 `y` 上的函数**总和为 1**。

$$\Bigl(\sum_u p_U(u) = 1\Bigr) \;\Longrightarrow\;
  \sum_y \mathrm{doProb}(W)\,x\,y = 1 .$$

**⭐ 这是「`doProb` 是真正的概率分布」在 `WorldModel` 层的证明。**
证明分两步：`∑ y, doLaw x y = ∑ u, pU u = 1`（`FateV2.Predict.T34.doLaw_mass` + `hU`），
再逐项除以该和。

**⚠ 前件 `hU` 是**真实的外生律归一假设**，不是结论的改写。** -/
theorem DoCapable.doProb_sum_eq_one (W : DoCapable)
    [Fintype W.State] [DecidableEq W.State]
    (hU : ∑ u, W.pU u = 1) (x : W.State) :
    ∑ y, W.doProb x y = 1 := by
  have hU' : ∑ u, W.toSCM.pU u = 1 := by rw [DoCapable.toSCM_pU]; exact hU
  have hmass : ∑ y, SCMSemantics.doLaw W.toSCM x y = ∑ u, W.toSCM.pU u :=
    FateV2.Predict.T34.doLaw_mass W.toSCM x
  have hne : (∑ y, SCMSemantics.doLaw W.toSCM x y) ≠ 0 := by
    rw [hmass, hU']; norm_num
  have hsplit : ∑ y, W.doProb x y
      = (∑ y, SCMSemantics.doLaw W.toSCM x y)
        / (∑ y, SCMSemantics.doLaw W.toSCM x y) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [DoCapable.doProb_apply]
    rfl
  rw [hsplit, div_self hne]

/-- ⭐⭐⭐ **`doProb` 非负**（当 `pU ≥ 0` 且分母为正）。 -/
theorem DoCapable.doProb_nonneg (W : DoCapable) [Fintype W.State] [DecidableEq W.State]
    (hpU : ∀ u, 0 ≤ W.pU u) (hpos : ∀ x, 0 < ∑ y', SCMSemantics.doLaw W.toSCM x y')
    (x y : W.State) : 0 ≤ W.doProb x y := by
  rw [DoCapable.doProb_apply, CausalRouteDo.doProb]
  have hpU' : ∀ u, 0 ≤ W.toSCM.pU u := by
    intro u; rw [DoCapable.toSCM_pU]; exact hpU u
  apply div_nonneg
  · refine Finset.sum_nonneg (fun u _ => mul_nonneg (hpU' u) ?_)
    by_cases h : (W.toSCM.sg u).2 x = y <;> simp [h]
  · exact le_of_lt (hpos x)
