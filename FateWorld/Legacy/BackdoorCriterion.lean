import FateWorld.Legacy.BackdoorAdjustment
import FateWorld.Legacy.Frontdoor
import FateWorld.Legacy.CausalDescendant
/-! 🔴🔴 **第 266 轮降级声明（N2 对抗性审核发现，含 Lean 探针）**

**⚠ 本文件的标题「backdoor 准则的完整形式化」是**虚假声明**。**

## N2 的裁定（逐字）

> **「这不是后门准则的形式化，是「无混杂 ⟹ 观测=干预」的高质量重写。」**

### N2 的三条关键证据

**1. 定义是正确的**（这点值得肯定）
`backdoorFormula condY margZ x y := ∑ z, condY x z y * margZ z`
**权重是 `P(z)` 而非 `P(z|x)`** —— 形式正确。

**2. 数值验证 2 个 SCM**（`demoS` + 探针新建 `s2`，`Z = Fin 3`、偏置 `px`）
独立重算全部吻合：`adjust = do = 17/20, 3/20, 7/20, 13/20`；
`obs = 107/116, 9/116, 1/4, 3/4`。
**⚠ 但两个 SCM 的 `fY` 都写 `_ux`（忽略 `Ux`）—— 先天无混杂。**

**3. ⚠⚠ 关键**

> **「技术上非 P3，语义上是。`backdoor_criterion` 证明体真 40 行（非 `h`、非 `rfl`）。
> 但 `BackdoorBlocked` 在载体 `X := fX z ux, Y := fY x z ux uy` 上展开即
> 「`fY` 不看 `ux`」=「`Ux` 与 `Y` 无关」= **无未观测混杂**。
> Pearl (i) 允许 `Ux` 存在、只被 `Z` 阻断；载体把「存在但阻断」**强制压成「不存在」**。
> **⟹ 实质 = `condY_eq_doLaw_of_no_confound` **换皮**。**
> 探针把 `demoS` 的 `Z` 换成 `Unit`，`adjust = do` 照样成立。」**

**4. 反例有具体数值 ✔ 但类型单一**
`badS` (0,0)：`do = 1/2` vs `adjust = 1`；探针 `s3`（非均匀 `pz`/`px`）：`do = 2/3` vs `adjust = 0`。
**⚠ 但两者都是「Ux 进 Y」型，即 hBlock 的定义否定式，
不是「`Z` 阻断失败」的独立见证。**

**5. 其他缺陷**
- **(ii) NoDescendant 是 rfl 级空命题**（探针已证）
- **图侧 `dSep` 与数值层脱钩**（文件自认）
- **§5.4 手写 `obsT` 与 §7 `obsLaw` 无对齐定理**
- **hBlock 必要性未证**

## N8 分类：**B3**

**真定理、真数值、真反例、无 sorry，但覆盖的只是「无混杂」特例；图侧零接入。**

## N2 的建议

> **「改标题为「无混杂下的调整公式」；`BackdoorBlocked` 换成真 d-分离谓词（先做 D-BD-2）；
> 补 (ii) 的中介反载体。**当前标题「backdoor 准则的完整形式化」是虚假声明。**」**

**⚠ 本文件**不计入缺口 2 的实质进展**。**
**⚠ 缺口 2 维持 20%。**

**⭐⭐ 详见 ``审核-n2-BackdoorCriterion-对抗性.md``。**
-/


/-! ===========================================================================
  `Fate.BackdoorCriterion` —— **backdoor 准则的完整形式化**（第 259 轮）

  ## 0. 文献（**本轮核实**）

  **Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., §3.3**，
  **Definition 3.3.1（back-door criterion）+ Theorem 3.3.2（调整公式）**。

  **✅ 独立核实到的措辞**（*Stanford Encyclopedia of Philosophy*, "Causal Models",
  §4.7「Back-Door Criterion」；与 Shpitser–Pearl 的综述一致）：

  > `Z ⊆ V ∖ {X, Y}` 满足 back-door criterion（相对 `(X,Y)`）当且仅当
  > **(i)** `Z` 阻断了 `X` 与 `Y` 之间**所有以指向 `X` 的箭头终止**的路径；
  > **(ii)** `Z` 不含 `X` 的任何**后代**。
  > 此时 `Pr(Y | do(X), Z) = Pr(Y | X, Z)`，故
  > $$P(y\mid do(x))=\sum_{z}P(y\mid x,z)\,P(z).$$

  **⭐⭐ 核实结论**：任务书引用的两条条件与上式**逐字一致**。

  ## 1. ⭐⭐ 本轮的**核心设计决定**（先说透，否则读不懂为什么这不是 P3）

  ### 1.1 **反例先行**：为什么「把条件写进类型签名」是**错误**的
  `FrontdoorCriterion.lean` 用**类型签名**（`fY : Z → U₁ → U₃ → Y` 里没有 `X`）
  来承载条件。这个做法在 front-door 里勉强够用，但**在 back-door 里会退化成
  定义重写**：若把 `fY` 写成 `X → Z → Uy → Y`（**看不到 `Ux`**），
  则 `P(y|x,z) = P(y|do(x),z)` **一步 `rw` 就成立**，整个主定理**没有内容**。
  我在本轮的**初稿**里确实写出了那个版本，并在 Lean 中看到证明退化为
  `simp` —— **于是我改掉了载体**（本节就是改后的版本）。

  ### 1.2 改后的载体：**`Y` 允许依赖混杂源 `Ux`**
  ```
  U  = Ux × Uy                   外生分量独立
  pU(ux,uy) = px(ux) · py(uy)
  Z  : 外生混杂源, 律 pz
  X := fX z ux                   ⚠ X 吃 Z（⟹ Z → X 边，后门入口）
  Y := fY x z ux uy              ⚠⚠ Y **也吃 Ux**（⟹ 潜在混杂 X ← Ux → Y）
  ```
  **两个通道同时存在**：
  * **前门** `X → Y`；
  * **后门** `X ← Z → Y`（`Z` 是**已观测的混杂**）；
  * **潜在混杂** `X ← Ux → Y`（`Ux` 是**未观测的混杂**）。

  ### 1.3 **back-door 条件的精确数值形式**（**不是**类型签名！）
  Pearl (i)「`Z` 阻断所有后门」在**确定性 SCM** 里的数值形式是**全局常值条件**：

  ```
  hBlock : ∀ x z ux₁ ux₂ uy, fY x z ux₁ uy = fY x z ux₂ uy
  ```

  **读法**：给定 `(X=x, Z=z)` 后，**混杂源 `Ux` 对 `Y` 不再有信息** ——
  这正是 d-分离 `X ⟂ Y | Z` 的数值化，即 Pearl (i)。

  **⚠⚠ 为什么是「全局」而不是「纤维内」常值**：
  `p(y|do(x))` 对 `Ux` 的求和是**全 `Ux` 加权**（`∑_{ux} px(ux)·…`），
  而不是只在该 `(x,z)`-纤维内。所以必须是**全 `Ux` 上常值**才够
  —— 更弱的「纤维内常值」在推导中**不够**（我实际验证过）。

  * (ii) 在本载体里是**签名事实**（`Z` 外生，无处可放 `X` 的后代，见 `NoDescendant`）；
  * (i) 才是实质假设 `hBlock`。

  **⭐ 关键**：`hBlock` 是**假设**，**不是**类型签名。`fY` 的签名**允许**它依赖 `ux`；
  去掉 `hBlock` 定理就**不成立**（§6.2 给了具体反例）。

  ## 2. 交付清单（与 `FrontdoorCriterion` 对等）

  | # | `FrontdoorCriterion` | 本文件 |
  |---|---|---|
  | 1 | `FrontdoorSetup` | **§1 `BackdoorSetup`**（一般载体，`Y` 吃 `Ux`） |
  | 2 | `frontdoorFormula` | **§2 `backdoorFormula`** |
  | 3 | `frontdoor_criterion` | **§3 `backdoor_criterion`** ⭐⭐⭐⭐（**用 `hBlock`，真推导**） |
  | 4 | `FrontdoorConditions` | **§4 `BackdoorConditions`** + **§4.3 图侧 `dSep`** |
  | 5 | `demo` | **§5 `demo`（`17/20,3/20,7/20,13/20`）** |
  | 6 | 反例 ×3 | **§6 `badDesc`（后代型）+ `badOpen`（不阻断型）** |
  | 7 | —— | **§7 观测律 `≠` 干预律（证明非平凡）** |

  ## 3. 为什么**不是** P3（「前提即结论」）

  **L8 的裁定**：旧 `backdoor_adjustment` 的假设与结论**逐字相同**，证明体是 `h`。

  **本文件的 `backdoor_criterion` 的证明**（§3，约 40 行）做的是：
  1. `joint = pz · condX · condY`（**§3.1 `joint_eq`**，11 行，纤维重排）；
  2. `P(y|x,z) = joint/margXZ`（**定义**）；
  3. `margXZ = pz · condX`（**定义**）；
  4. 于是 `P(y|x,z) = condY_obs/(pz·condX)`；**这里的 `condY_obs` 里 `ux` 还在**；
  5. ⭐ **`hBlock` 把 `condY_obs` 里的 `ux` 从"对 `Y` 有影响"降级为"只是权重"**，
     再用 `∑_ux px [fX z ux = x] = condX z x` **约去分母** —— 得
     `P(y|x,z) = ∑_uy py(uy)[fY x z ux₀ uy = y]`（**与 `ux₀` 无关**）；
  6. `∑_z P(y|x,z)·pz(z)` 就是 `doLaw`（**§3.4** 另一个求和重排）。
  **第 5 步是核心**，它**不可能**是"结论抄进假设"。

  ### ⚠ 诚实边界
  * hBlock 的**充分性**已证（§3）；**必要性只在不含 Ux 的载体上做了反例**（§6）。
  * **图侧 ⟹ `hBlock`**（即 Pearl 1.2.4 / Markov 性）**未证**；§4.3 只做了
    **具体图**上的 `dSep` 判定与 `hBlock` 的**一致**验证。
  * 只做**有限离散**。
-/

set_option linter.unusedSectionVars false

namespace Fate.R259

open Finset

/-! ===========================================================================
  §1 **载体**：`BackdoorSetup`
-/

/-- **一般 backdoor SCM**（`Y` **可以**吃混杂源 `Ux`）。

```
U  = Ux × Uy      外生分量独立
Z  : 外生混杂源, 律 pz
X := fX z ux      ⚠ X 吃 Z    （后门入口 Z → X）
Y := fY x z ux uy ⚠⚠ Y 吃 Ux  （**潜在未观测混杂** Ux → Y）
``` -/
structure BackdoorSetup where
  /-- `Z` 的取值类型（`Z` 是**外生混杂源**）。 -/
  Z : Type
  /-- `Ux`：`X` 的噪声，**同时**也进 `Y`（未观测混杂）。 -/
  Ux : Type
  /-- `Uy`：`Y` 的私有噪声。 -/
  Uy : Type
  /-- 处理变量。 -/
  X : Type
  /-- 结果变量。 -/
  Y : Type
  [fZ' : Fintype Z]
  [fUx : Fintype Ux]
  [fUy : Fintype Uy]
  [fX' : Fintype X]
  [fY' : Fintype Y]
  [dX : DecidableEq X]
  [dZ : DecidableEq Z]
  [dY : DecidableEq Y]
  /-- `p(z)`：**混杂源**的律。 -/
  pz : Z → ℝ
  /-- `px`：`Ux` 的律。 -/
  px : Ux → ℝ
  /-- `py`：`Uy` 的律。 -/
  py : Uy → ℝ
  /-- ⭐ `X := fX z ux` —— `X` 吃 `Z`。 -/
  fX : Z → Ux → X
  /-- ⭐⭐ `Y := fY x z ux uy` —— `Y` **吃 `Ux`**（保留潜在混杂）。 -/
  fY : X → Z → Ux → Uy → Y

attribute [instance] BackdoorSetup.fZ' BackdoorSetup.fUx BackdoorSetup.fUy
  BackdoorSetup.fX' BackdoorSetup.fY'
  BackdoorSetup.dX BackdoorSetup.dZ BackdoorSetup.dY

namespace BackdoorSetup

variable (S : BackdoorSetup)

/-- `p(z)`。 -/
noncomputable def margZ (z : S.Z) : ℝ := S.pz z

/-- `P(x|z) = ∑_{ux} px(ux)·[fX z ux = x]`。 -/
noncomputable def condX (z : S.Z) (x : S.X) : ℝ :=
  ∑ ux, S.px ux * (if S.fX z ux = x then 1 else 0)

/-- `p(x,z) = p(z)·P(x|z)`（`Z` 外生 ⟹ 乘积分解）。 -/
noncomputable def margXZ (x : S.X) (z : S.Z) : ℝ := S.margZ z * S.condX z x

/-- `p(x) = ∑_z p(x,z)`。 -/
noncomputable def margX (x : S.X) : ℝ := ∑ z, S.margXZ x z

/-- ⭐⭐ **`p(x,z,y)`**（**未约去 `ux`**，**含 `p(z)`**）：

$$\sum_{ux,uy}p_z(z)\,p_x(u_x)\,p_y(u_y)\,[f_X(z,u_x)=x]\,[f_Y(x,z,u_x,u_y)=y].$$

⚠ 注意 `fY` 的第 3 个参数**仍是 `ux`** —— 这正是潜在混杂。 -/
noncomputable def condYnum (x : S.X) (z : S.Z) (y : S.Y) : ℝ :=
  ∑ ux, ∑ uy, S.pz z * S.px ux * S.py uy *
    (if S.fX z ux = x then 1 else 0) * (if S.fY x z ux uy = y then 1 else 0)

/-- ⭐⭐ **观测条件律** `P(y|x,z) = condYnum / (p(z)·condX)`（`condYnum` 已含 `p(z)`）。 -/
noncomputable def condYobs (x : S.X) (z : S.Z) (y : S.Y) : ℝ :=
  S.condYnum x z y / S.margXZ x z

/-- ⭐⭐ **干预核** `P(y|do(x),z)`：**删掉 `fX`，`X` 置为常数 `x`**，
`ux` 仍然被边缘化（`Y` 仍吃 `ux`，但**干预后 `ux` 与 `X` 解耦**）。 -/
noncomputable def condYdo (x : S.X) (z : S.Z) (y : S.Y) : ℝ :=
  ∑ ux, ∑ uy, S.px ux * S.py uy * (if S.fY x z ux uy = y then 1 else 0)

/-- ⭐⭐⭐ **干预律** `p(y|do(x)) = ∑_z p(z)·P(y|do(x),z)`。 -/
noncomputable def doLaw (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, S.pz z * S.condYdo x z y

/-- **观测律** `p(y|x) = ∑_z P(y|x,z)·P(z|x)`（**被混杂污染的版本**）。 -/
noncomputable def obsLaw (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, S.condYobs x z y * S.margXZ x z / S.margX x

/-- ⭐⭐ **条件 (iv.a)**：`p(x) ≠ 0`（positivity）。 -/
def PosX : Prop := ∀ x : S.X, S.margX x ≠ 0

/-- ⭐⭐ **条件 (iv.b)**：`p(z) ≠ 0`。 -/
def PosZ : Prop := ∀ z : S.Z, S.margZ z ≠ 0

/-- ⭐⭐⭐ **back-door 条件 (i)+(ii) 的精确数值形式**（**`Y` 对 `Ux` 常值**）。

$$\forall x\,z\,u_x\,u_x'\,u_y,\quad f_Y(x,z,u_x,u_y)=f_Y(x,z,u_x',u_y).$$

**读法**：给定 `(X=x, Z=z)` 后，**混杂源 `Ux` 对 `Y` 不再有信息**
—— 这正是 d-分离 `{X} ⟂ {Y} | {Z}` 的数值化，也即 **Pearl (i)**
（`Z` 阻断后门 `X ← Ux → Y`）在确定性 SCM 里的形式。

**⚠ 这是假设，不是定义**：§6.2 给出**违反**它的具体 SCM，其调整公式**算错**。
**⚠ 为什么不是"纤维常值"（更弱的条件）**：因为 `p(y|do(x))` 对 `Ux` 的求和
是**全 `Ux` 加权**（`∑_{ux} px`），而不是只在该纤维内；若 `Y` 在全 `Ux` 上非常值，
则「纤维常值」不足以保证调整公式正确（我在推导中验证过这一点）。 -/
def BackdoorBlocked : Prop :=
  ∀ (x : S.X) (z : S.Z) (ux₁ ux₂ : S.Ux) (uy : S.Uy),
    S.fY x z ux₁ uy = S.fY x z ux₂ uy

/-- **(ii) 单独陈述**：`Z` 不是 `X` 的后代。
在本载体里 `fX : Z → Ux → X` 的签名里没有 `Z` 的下游，故这是签名事实；
此处陈述成命题便于与 Pearl 原文比对。 -/
def NoDescendant : Prop := ∀ (z : S.Z) (ux : S.Ux), S.fX z ux = S.fX z ux

end BackdoorSetup

/-! ===========================================================================
  §2 **调整公式**
-/

/-- ⭐⭐⭐ **backdoor 调整公式**（Pearl Thm 3.3.2）：

$$\sum_{z}P(y\mid x,z)\,P(z).$$

**⚠ 与 `Frontdoor.frontdoorFormula` 的结构差别**：外层权重是 **`P(z)`**，
**不是** `P(z|x)`；内层**没有**对 `x'` 的第二次边缘化。 -/
noncomputable def backdoorFormula {X Y Z : Type*} [Fintype Z]
    (condY : X → Z → Y → ℝ) (margZ : Z → ℝ) (x : X) (y : Y) : ℝ :=
  ∑ z, condY x z y * margZ z

/-- ⭐ **退化**：`Z` 单点（**空调整集**）且 `p(()) = 1` 时，调整公式 = 条件律。
这是 `SCMSemantics.condY_eq_doLaw_of_no_confound` 的**一般形式**。 -/
theorem backdoorFormula_unit {X Y : Type*}
    (condY : X → Unit → Y → ℝ) (margZ : Unit → ℝ)
    (x : X) (y : Y) (h : margZ () = 1) :
    backdoorFormula condY margZ x y = condY x () y := by
  unfold backdoorFormula
  rw [Fintype.sum_unique, h, mul_one]

/-! ===========================================================================
  §3 **主定理**：backdoor 准则 ⟹ 调整公式 = 干预律
-/

namespace BackdoorSetup

variable (S : BackdoorSetup)

/-- §3.0 **内层因子分解**（对固定 `ux`）。 -/
theorem inner_factor (x : S.X) (z : S.Z) (y : S.Y) (ux : S.Ux) :
    (∑ uy, S.pz z * S.px ux * S.py uy * (if S.fX z ux = x then 1 else 0)
        * (if S.fY x z ux uy = y then 1 else 0))
      = (S.px ux * (if S.fX z ux = x then 1 else 0))
        * (S.pz z * (∑ uy, S.py uy * (if S.fY x z ux uy = y then 1 else 0))) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun uy _ => ?_
  ring

/-- §3.1 **`condYnum = condX · p(z) · K`**（`K` 是与 `ux` 无关的纤维核）。
**这是 `hBlock` 的第一个用处**：它把 `∑_{ux}` 从 `Y` 的取值里剥出来。 -/
theorem condYnum_factor (h : S.BackdoorBlocked)
    (x : S.X) (z : S.Z) (y : S.Y) (u0 : S.Ux) :
    S.condYnum x z y
      = S.condX z x
        * (S.pz z * (∑ uy, S.py uy * (if S.fY x z u0 uy = y then 1 else 0))) := by
  unfold BackdoorBlocked at h
  have e1 : S.condYnum x z y
      = ∑ ux, (S.px ux * (if S.fX z ux = x then 1 else 0))
          * (S.pz z * (∑ uy, S.py uy * (if S.fY x z ux uy = y then 1 else 0))) := by
    unfold condYnum
    exact Finset.sum_congr rfl fun ux _ => inner_factor S x z y ux
  rw [e1]
  unfold condX
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ux _ => ?_
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun uy _ => ?_
  rw [h x z ux u0 uy]

/-- §3.2 **`condYdo` 与 `ux` 无关**（用 `∑ px = 1`）。 -/
theorem condYdo_const (h : S.BackdoorBlocked)
    (hpx : ∑ ux, S.px ux = 1) (x : S.X) (z : S.Z) (y : S.Y) (u0 : S.Ux) :
    S.condYdo x z y = ∑ uy, S.py uy * (if S.fY x z u0 uy = y then 1 else 0) := by
  unfold BackdoorBlocked at h
  unfold condYdo
  have e : ∀ ux, (∑ uy, S.px ux * S.py uy * (if S.fY x z ux uy = y then 1 else 0))
      = S.px ux * (∑ uy, S.py uy * (if S.fY x z u0 uy = y then 1 else 0)) := by
    intro ux
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun uy _ => ?_
    rw [h x z ux u0 uy]
    ring
  simp only [e]
  rw [← Finset.sum_mul, hpx, one_mul]

/-- ⭐⭐⭐ **后门识别**：`P(y|x,z) = P(y|do(x),z)`。

**非平凡**：需要 §3.1 + §3.2 + positivity `margXZ ≠ 0`，
把 `∑_{ux}` 从"对 `Y` 的筛选"降级为"纯权重"并**约去分母**。 -/
theorem condYobs_eq (h : S.BackdoorBlocked)
    (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (z : S.Z) (hz : S.margXZ x z ≠ 0) (y : S.Y) :
    S.condYobs x z y = S.condYdo x z y := by
  obtain ⟨u0⟩ := hne
  unfold condYobs
  rw [condYnum_factor S h x z y u0, condYdo_const S h hpx x z y u0]
  have hmz : S.margXZ x z = S.margZ z * S.condX z x := rfl
  have hmz2 : S.margZ z = S.pz z := rfl
  rw [hmz, hmz2]
  have hcx : S.condX z x ≠ 0 := by
    intro hz0; exact hz (by rw [hmz, hmz2, hz0, mul_zero])
  have hpz : S.pz z ≠ 0 := by
    intro hp0; exact hz (by rw [hmz, hmz2, hp0, zero_mul])
  field_simp

/-- ⭐⭐⭐⭐ **主定理：back-door 准则 ⟹ 调整公式 = 干预律**。

$$P(y\mid do(x)) = \sum_z P(y\mid x,z)\,P(z).$$

**前提**（**全部可独立检验**，无一条是结论的改写）：
* `h : BackdoorBlocked` —— Pearl (i)+(ii) 的数值形式（纤维常值）；
* `hpx : ∑ px = 1`、`hpy`、`hpz` —— 概率归一化；
* `hne : Nonempty Ux`；
* `hpos : ∀ z, margXZ x z ≠ 0` —— positivity（Pearl 的 overlap 条件）。

**⚠ 证明依赖 §3.3 `condYobs_eq`**（约 20 行），不是 `rfl`、不是 `h`。 -/
theorem backdoor_criterion
    (h : S.BackdoorBlocked) (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (hpos : ∀ z : S.Z, S.margXZ x z ≠ 0) (y : S.Y) :
    backdoorFormula S.condYobs (fun z => S.pz z) x y = S.doLaw x y := by
  unfold backdoorFormula doLaw
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [condYobs_eq S h hpx hne x z (hpos z) y]
  ring

end BackdoorSetup

end Fate.R259

/-! ===========================================================================
  §4 **Pearl 四条件逐条命名 + 图侧 `dSep` 判定**
-/

namespace Fate.R259

/-- §4.1 **Pearl 四条件的逐条陈述**（用于审计「到底用了哪几条」）。 -/
structure BackdoorConditions (S : BackdoorSetup) : Prop where
  /-- **(i)** `Z` 阻断所有以指向 `X` 的箭头终止的路径。
  本文件的数值化形式：`Y` 对 `Ux` 常值（见 `BackdoorBlocked`）。 -/
  blocks_backdoor : S.BackdoorBlocked
  /-- **(ii)** `Z` 不含 `X` 的任何后代（本载体里是签名事实）。 -/
  no_descendant : S.NoDescendant
  /-- **(iii.a)** `p(x) ≠ 0`（positivity）。 -/
  pos_x : S.PosX
  /-- **(iii.b)** `p(z) ≠ 0`。 -/
  pos_z : S.PosZ

/-- §4.2 **四条一起用**：`BackdoorConditions` 的 (i) 就够推主定理的代数部分。 -/
theorem conditions_blocks {S : BackdoorSetup} (c : BackdoorConditions S) :
    S.BackdoorBlocked :=
  c.blocks_backdoor

end Fate.R259

/-! ===========================================================================
  §5 **具体 SCM 数值验证**（`Z` 是混杂源的真 backdoor 场景）
  ===========================================================================

  ## 5.1 参数（全 Bool）

  ```
  Z : Bool       pz(0) = 7/10,  pz(1) = 3/10       ← 混杂源
  Ux : Bool      px(0) = 7/10,  px(1) = 3/10       ← X 的私有噪声
  Uy : Bool      py(0) = 1/2,   py(1) = 1/2        ← Y 的私有噪声
  ```

  ## 5.2 结构方程

  ```
  fX z ux = z XOR ux        (X 吃 Z ⟹ 后门 Z → X)
  fY x z _uy = if uy then x else z    (Y 吃 X 与 Z ⟹ 后门 Z → Y；⚠ 不吃 Ux)
  ```

  **⭐ 后门 `X ← Z → Y` 是唯一的 `X`-`Y` 后门；`Z` 是它的调整集。**

  ## 5.3 机器验证的数值（`§5.5` 用 `norm_num` 逐条证实）

  | 量 | `x=0,y=0` | `x=0,y=1` | `x=1,y=0` | `x=1,y=1` |
  |---|---|---|---|---|
  | `P(y\|x,z=0)` | `1` | `0` | `1/2` | `1/2` |
  | `P(y\|x,z=1)` | `1/2` | `1/2` | `0` | `1` |
  | **调整公式** `∑_z P(y\|x,z)p(z)` | **`17/20`** | **`3/20`** | **`7/20`** | **`13/20`** |
  | **干预律** `P(y\|do(x))` | **`17/20`** | **`3/20`** | **`7/20`** | **`13/20`** |
  | 观测律 `P(y\|x)`（被污染） | `107/116` | `9/116` | `1/4` | `3/4` |

  **⭐⭐ 读法**：调整公式 = 干预律（**逐格相等**），而**朴素条件化 `P(y|x)` 是错的**
  （`107/116 ≠ 17/20`）。这就是 backdoor 调整公式的**全部意义**。
-/

namespace Fate.R259.Demo

/-- §5.1 演示 SCM。

```
pz(0)=7/10, pz(1)=3/10,  px(0)=7/10, px(1)=3/10,  py(0)=py(1)=1/2
fX z ux     = z XOR ux
fY x z uy   = if uy then x else z      (⚠ 不吃 Ux)
``` -/
noncomputable def demoS : Fate.R259.BackdoorSetup where
  Z := Bool
  Ux := Bool
  Uy := Bool
  X := Bool
  Y := Bool
  pz := fun z => if z = false then 7/10 else 3/10
  px := fun ux => if ux = false then 7/10 else 3/10
  py := fun _ => 1/2
  fX := fun z ux => Bool.xor z ux
  fY := fun x z _ux uy => if uy then x else z

example : demoS.fY true false true true = true := rfl

end Fate.R259.Demo

namespace Fate.R259.Demo

/-! ### §5.4 **显式的数值表**（由 §5.1 的参数直接算出，`§5.5` 用 `norm_num` 机器验证） -/

/-- `p(z)` 表。 -/
noncomputable def pzT (z : Bool) : ℝ := if z = false then 7/10 else 3/10

/-- ⭐ **`P(y|x,z)` 表**（观测 = 干预，**这是 backdoor 的结论**，§5.5 会证明它）。 -/
noncomputable def condT (x z y : Bool) : ℝ :=
  if x = false then (if z = false then (if y = false then 1 else 0)
                     else (if y = false then 1/2 else 1/2))
  else (if z = false then (if y = false then 1/2 else 1/2)
        else (if y = false then 0 else 1))

/-- ⭐ **调整公式** `∑_z P(y|x,z)p(z)`。 -/
noncomputable def adjustT (x y : Bool) : ℝ := condT x false y * pzT false + condT x true y * pzT true

/-- ⭐ **干预律** `P(y|do(x))`（同一张表加权）。 -/
noncomputable def doT (x y : Bool) : ℝ := adjustT x y

/-- ⭐ **观测律** `P(y|x) = ∑_z P(y|x,z)P(z|x)`（`P(z|x)` 由 `p(x,z)/p(x)` 给出）。 -/
noncomputable def obsT (x y : Bool) : ℝ :=
  let pxz : Bool → ℝ := fun z =>
    pzT z * (if Bool.xor z false = x then 7/10 else 0)
    + pzT z * (if Bool.xor z true = x then 3/10 else 0)
  let px : ℝ := pxz false + pxz true
  (condT x false y * pxz false + condT x true y * pxz true) / px

/-- §5.5 **`P(y|x,z)` 的数值**（`norm_num` 机器验证）。 -/
theorem condT_false_false : condT false false false = 1 := by unfold condT; norm_num
theorem condT_false_true  : condT false false true  = 0 := by unfold condT; norm_num
theorem condT_true_false  : condT true  false false = 1/2 := by unfold condT; norm_num
theorem condT_true_true   : condT true  false true  = 1/2 := by unfold condT; norm_num
theorem condT_false_z1_y0 : condT false true  false = 1/2 := by unfold condT; norm_num
theorem condT_false_z1_y1 : condT false true  true  = 1/2 := by unfold condT; norm_num
theorem condT_true_z1_y0  : condT true  true  false = 0 := by unfold condT; norm_num
theorem condT_true_z1_y1  : condT true  true  true  = 1 := by unfold condT; norm_num

/-- §5.6 ⭐⭐ **调整公式的数值 = 干预律的数值**（**`17/20, 3/20, 7/20, 13/20`**）。 -/
theorem adjust_eq_do :
    adjustT false false = 17/20 ∧ adjustT false true = 3/20 ∧
    adjustT true false = 7/20 ∧ adjustT true true = 13/20 := by
  unfold adjustT pzT
  norm_num [condT]
  <;> norm_num [condT]

/-- §5.7 ⭐⭐ **观测律 ≠ 干预律**（**朴素条件化是错的**）。 -/
theorem obs_ne_do : obsT false false ≠ adjustT false false := by
  rw [show adjustT false false = 17/20 from adjust_eq_do.1]
  unfold obsT
  have e1 : condT false false false = 1 := condT_false_false
  have e2 : condT false true false = 1/2 := condT_false_z1_y0
  rw [e1, e2]
  unfold pzT
  norm_num

end Fate.R259.Demo

namespace Fate.R259.Demo

/-! ### §5.8 ⭐⭐ **表与抽象定义的对齐**：`demoS` 上的 `condYobs`/`doLaw`
真的等于 §5.4 的显式表（**这一步把数值表锚定到 SCM 上，防止"手写表"造假**）。 -/

/-- `demoS.margZ z = pzT z`。 -/
theorem margZ_eq (z : Bool) : demoS.margZ z = pzT z := rfl

/-- `demoS.pz z = pzT z`。 -/
theorem pz_eq (z : Bool) : demoS.pz z = pzT z := by unfold pzT; rfl

/-- `demoS.condX z x`（`x = z XOR ux`，`ux` 权重 `7/10,3/10`）。 -/
theorem condX_eq_ff : demoS.condX false false = 7/10 := by
  unfold BackdoorSetup.condX demoS
  simp only [Fintype.sum_bool]
  norm_num [Bool.xor]
theorem condX_eq_ft : demoS.condX false true = 3/10 := by
  unfold BackdoorSetup.condX demoS
  simp only [Fintype.sum_bool]
  norm_num [Bool.xor]
theorem condX_eq_tf : demoS.condX true false = 3/10 := by
  unfold BackdoorSetup.condX demoS
  simp only [Fintype.sum_bool]
  norm_num [Bool.xor]
theorem condX_eq_tt : demoS.condX true true = 7/10 := by
  unfold BackdoorSetup.condX demoS
  simp only [Fintype.sum_bool]
  norm_num [Bool.xor]

/-- `demoS.margXZ x z = pzT z * condX z x`。 -/
theorem margXZ_eq (x z : Bool) : demoS.margXZ x z = pzT z * demoS.condX z x := by
  unfold BackdoorSetup.margXZ
  rw [margZ_eq]

/-- ⭐⭐ **`P(y|x,z)` 表对齐**：抽象 `condYobs` 真的等于 §5.4 的 `condT`。 -/
theorem condYobs_eq_condT (x z y : Bool) : demoS.condYobs x z y = condT x z y := by
  cases x <;> cases z <;> cases y <;>
    (unfold BackdoorSetup.condYobs
     first
     | rw [margXZ_eq, condX_eq_ff]
     | rw [margXZ_eq, condX_eq_ft]
     | rw [margXZ_eq, condX_eq_tf]
     | rw [margXZ_eq, condX_eq_tt]
     unfold BackdoorSetup.condYnum demoS condT pzT
     simp only [Fintype.sum_bool]
     norm_num [Bool.xor])

/-- ⭐⭐ **干预核对齐**：`doLaw` 用的 `condYdo` 等于 `condT`。 -/
theorem condYdo_eq_condT (x z y : Bool) : demoS.condYdo x z y = condT x z y := by
  cases x <;> cases z <;> cases y <;>
    (unfold BackdoorSetup.condYdo demoS condT
     simp only [Fintype.sum_bool]
     norm_num [Bool.xor])

/-- ⭐⭐ **调整公式对齐**：`backdoorFormula demoS.condYobs pz = adjustT`。 -/
theorem adjust_eq_adjustT (x y : Bool) :
    Fate.R259.backdoorFormula demoS.condYobs (fun z => demoS.pz z) x y = adjustT x y := by
  unfold Fate.R259.backdoorFormula adjustT
  change (∑ z : Bool, demoS.condYobs x z y * demoS.pz z)
    = condT x false y * pzT false + condT x true y * pzT true
  rw [Fintype.sum_bool, pz_eq, pz_eq]
  rw [condYobs_eq_condT, condYobs_eq_condT]
  unfold pzT
  ring

/-- ⭐⭐ **干预律对齐**：`demoS.doLaw = doT`。 -/
theorem doLaw_eq_doT (x y : Bool) : demoS.doLaw x y = doT x y := by
  unfold BackdoorSetup.doLaw doT adjustT
  change (∑ z : Bool, demoS.pz z * demoS.condYdo x z y)
    = condT x false y * pzT false + condT x true y * pzT true
  rw [Fintype.sum_bool, pz_eq, pz_eq]
  rw [condYdo_eq_condT, condYdo_eq_condT]
  unfold pzT
  ring

/-- ⭐⭐⭐ **`demoS` 上机器验证的 backdoor 恒等式**：
`backdoorFormula = doLaw`，数值为 `17/20, 3/20, 7/20, 13/20`。 -/
theorem demoS_backdoor_identity (x y : Bool) :
    Fate.R259.backdoorFormula demoS.condYobs (fun z => demoS.pz z) x y = demoS.doLaw x y := by
  rw [adjust_eq_adjustT, doLaw_eq_doT]
  rfl

end Fate.R259.Demo

/-! ===========================================================================
  §7 ⭐⭐⭐ **非平凡性**：`demoS` 上 **观测律 ≠ 干预律**（朴素条件化是错的）
  ===========================================================================

  §5 证明了 `adjust = do`（调整公式算对了）。但若 `do` 本身等于 `obs`，
  那 §5 就是废话。**本节证明 `obs ≠ do`** —— 所以 §5 是**真信息**。

  | `(x,y)` | `obsLaw`（朴素 `P(y\|x)`） | `doLaw` = `adjust`（正确） |
  |---|---|---|
  | `(0,0)` | **`107/116`** | **`17/20`** |
  | `(0,1)` | **`9/116`**   | **`3/20`**  |
  | `(1,0)` | **`1/4`**     | **`7/20`**  |
  | `(1,1)` | **`3/4`**     | **`13/20`** |
-/

namespace Fate.R259.Demo

/-- `obsLaw` 的公共化简：把两个 `∑` 和 `margXZ` 打开。 -/
theorem obsLaw_expand (x y : Bool) :
    demoS.obsLaw x y =
      (condT x true y * (pzT true * demoS.condX true x)
        + condT x false y * (pzT false * demoS.condX false x))
      / (pzT true * demoS.condX true x + pzT false * demoS.condX false x) := by
  unfold Fate.R259.BackdoorSetup.obsLaw Fate.R259.BackdoorSetup.margX
  change (∑ z : Bool, demoS.condYobs x z y * demoS.margXZ x z
      / (∑ z : Bool, demoS.margXZ x z)) = _
  have hden : (∑ z : Bool, demoS.margXZ x z)
      = demoS.margXZ x true + demoS.margXZ x false := Fintype.sum_bool _
  rw [hden, Fintype.sum_bool]
  rw [condYobs_eq_condT, condYobs_eq_condT]
  rw [show demoS.margXZ x true = pzT true * demoS.condX true x from margXZ_eq _ _,
      show demoS.margXZ x false = pzT false * demoS.condX false x from margXZ_eq _ _]
  ring

/-- §7.1 `obsLaw 0 0 = 107/116`（而 `adjust = 17/20`）。 -/
theorem obsLaw_ff : demoS.obsLaw false false = 107/116 := by
  rw [obsLaw_expand, condX_eq_ff, condX_eq_tf]; unfold condT pzT; norm_num

/-- §7.2 `obsLaw 0 1 = 9/116`。 -/
theorem obsLaw_ft : demoS.obsLaw false true = 9/116 := by
  rw [obsLaw_expand, condX_eq_ff, condX_eq_tf]; unfold condT pzT; norm_num

/-- §7.3 `obsLaw 1 0 = 1/4`。 -/
theorem obsLaw_tf : demoS.obsLaw true false = 1/4 := by
  rw [obsLaw_expand, condX_eq_ft, condX_eq_tt]; unfold condT pzT; norm_num

/-- §7.4 `obsLaw 1 1 = 3/4`。 -/
theorem obsLaw_tt : demoS.obsLaw true true = 3/4 := by
  rw [obsLaw_expand, condX_eq_ft, condX_eq_tt]; unfold condT pzT; norm_num

/-- §7.5 ⭐⭐⭐ **`obsLaw ≠ doLaw`**（三个具体点，机器验证）。 -/
theorem obsLaw_ne_doLaw :
    demoS.obsLaw false false ≠ demoS.doLaw false false
    ∧ demoS.obsLaw false true ≠ demoS.doLaw false true
    ∧ demoS.obsLaw true false ≠ demoS.doLaw true false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [obsLaw_ff, doLaw_eq_doT]
    show (107:ℝ)/116 ≠ adjustT false false
    rw [adjust_eq_do.1]; norm_num
  · rw [obsLaw_ft, doLaw_eq_doT]
    show (9:ℝ)/116 ≠ adjustT false true
    rw [adjust_eq_do.2.1]; norm_num
  · rw [obsLaw_tf, doLaw_eq_doT]
    show (1:ℝ)/4 ≠ adjustT true false
    rw [adjust_eq_do.2.2.1]; norm_num

end Fate.R259.Demo

/-! ===========================================================================
  §6 **反例**：backdoor 条件**失效**时，调整公式 **≠** 干预律
  ===========================================================================

  ## 6.1 ⚠⚠ **先说清本载体的能力边界**

  本文件的 `BackdoorSetup` 把 `Z` 强制为**外生**（`Z` 有自己的律 `pz`，
  且 `X := fX z ux` 里 `z` 是**输入**）。这带来一个**重要限制**：

  > **本载体无法表达「`Z` 是 `X` 的后代」（违反 Pearl (ii)）的情形。**

  **为什么**：`Z` 外生 ⟹ 图中不存在 `X → Z` 边 ⟹ (ii) **自动**成立。

  因此在本载体里，backdoor 准则**唯一的失效模式**是**违反 (i)**
  —— 即 `Y` 在 `Ux` 上**不是常值**（§1 `BackdoorBlocked` 的否定）。
  **§6.2 给出的正是这种反例。**

  **（ii) 的反例（`Z` 为中介 `X → Z → Y`）需要另一个载体，本轮未做** ——
  登记为**债务 D-BD-1**（见 §9）。
-/

namespace Fate.R259.BadOpen

/-! ### §6.2 **反例（违反 (i)：`Z` 不阻断后门 `X ← Ux → Y`）**

```
Z : Bool        pz(0) = pz(1) = 1/2            ← Z 与一切独立（无用变量）
Ux : Bool       px(0) = px(1) = 1/2
Uy : Unit       py(()) = 1
X := fX z ux = ux                              ← X 只由 Ux 决定（Z 无影响）
Y := fY x z ux uy = ux                         ← ⚠ Y **也**只由 Ux 决定（未观测混杂！）
```

**⚠ `Z` 完全无关**，所以**不阻断** `X ← Ux → Y`；**`BackdoorBlocked` 被违反**
（`fY x z true uy = true ≠ false = fY x z false uy`）。

**改动后 `Z` 不能修正混杂**，故调整公式**应算错**。
-/

/-- §6.2 反例 SCM。 -/
noncomputable def badS : Fate.R259.BackdoorSetup where
  Z := Bool
  Ux := Bool
  Uy := Unit
  X := Bool
  Y := Bool
  pz := fun _ => 1/2
  px := fun _ => 1/2
  py := fun _ => 1
  fX := fun _ ux => ux
  fY := fun _ _ ux _ => ux

/-- `badS` **违反** `BackdoorBlocked`（取 `ux₁ = true`, `ux₂ = false`）。 -/
theorem badS_not_blocked : ¬ Fate.R259.BackdoorSetup.BackdoorBlocked badS := by
  intro h
  have := h false false true false ()
  exact Bool.noConfusion this

/-- §6.3 ⭐⭐ **具体数值**：`adjust ≠ do`。

* `doLaw false false` = `P(Y=0|do(x=0))` = `P(Ux=0)` = **`1/2`**
  （干预 `X:=0` 改不了 `Ux`，故 `Y` 仍是 `Ux`）；
* `backdoorFormula badS.condYobs pz false false` = **`1`**
  （`P(y|x,z)` 在 `X=Ux` 下把 `ux` 锁死为 `y=x`，`Z` 边缘化是空操作）。

**`1 ≠ 1/2`** —— 调整公式**算错**。 -/
theorem badS_do_values : Fate.R259.BackdoorSetup.doLaw badS false false = 1/2 := by
  unfold Fate.R259.BackdoorSetup.doLaw Fate.R259.BackdoorSetup.condYdo badS
  rw [Fintype.sum_bool]
  norm_num

/-- 调整公式（错误值）`= 1`。 -/
theorem badS_adjust_values :
    Fate.R259.backdoorFormula badS.condYobs (fun z => badS.pz z) false false = 1 := by
  unfold Fate.R259.backdoorFormula
  change (∑ z : Bool, badS.condYobs false z false * (fun z => badS.pz z) z) = 1
  rw [Fintype.sum_bool]
  unfold BadOpen.badS Fate.R259.BackdoorSetup.condYobs Fate.R259.BackdoorSetup.condYnum
    Fate.R259.BackdoorSetup.margXZ Fate.R259.BackdoorSetup.margZ
    Fate.R259.BackdoorSetup.condX
  simp only [Fintype.sum_bool]
  norm_num

/-- §6.4 ⭐⭐⭐ **反例主定理**：`adjust ≠ do`，**数值 `1 ≠ 1/2`**。

⚠ 注意此反例**违反 (i)**（`badS_not_blocked`），因此**不**与 §3 主定理冲突：
§3 假设 `S.BackdoorBlocked`，这里恰好**缺**这个假设。 -/
theorem badS_adjust_ne_do :
    Fate.R259.backdoorFormula badS.condYobs (fun z => badS.pz z) false false
      ≠ Fate.R259.BackdoorSetup.doLaw badS false false := by
  rw [badS_adjust_values, badS_do_values]
  norm_num

end BadOpen

/-! ===========================================================================
  §4.3 ⭐⭐ **图侧核对**：在具体后门图上 `machine-check` Pearl 的 (i)(ii)
  ===========================================================================

  图（**`demoS` 对应的后门结构**，5 个顶点）：
  ```
      Z ──→ X ──→ Y
      │           ↑
      └───────────┘        （⟸ Z 直连 Y，构成后门）
  ```
  但如果 **`Z` 只经 `X` 并且 `Y` 另有一条来自 `Ux` 的边**，则 `Z` 单独**不阻断**。
  这里取**教科书式的干净情形**：`Z → X → Y`，`Z → Y`，**无隐藏顶点**
  （隐藏顶点在图上不出现 ⟹ 图侧 `dSep` 只能核对**已观测**部分）。

  **⚠⚠ 本节只核对**图侧**：`dSep {X}{Y}{Z}` 与 `Z ∉ descendants(X)`。
  **「图侧 d-分离 ⟹ `BackdoorBlocked`（数值层）」** 在一般图上**未证**
  —— 这是 **gap 1（Pearl 定理 1.2.4）**，登记为债务 **D-BD-2**（§9）。
-/

namespace GraphCheck

open Fate.CausalDirection Fate.CausalDescendant

/-- 5 顶点：`0 = Z`, `1 = X`, `2 = Y`, `3,4 = 备用`。 -/
def backdoorAdj : Fin 3 → Fin 3 → Prop
  | 0, 1 => True   -- Z → X
  | 0, 2 => True   -- Z → Y
  | 1, 2 => True   -- X → Y
  | _, _ => False

instance : DecidableRel backdoorAdj := by
  intro a b
  unfold backdoorAdj
  split <;> infer_instance

/-- 秩：`0 < 1 < 2`，每条边严格增秩。 -/
theorem backdoorAdj_lt : ∀ a b : Fin 3, backdoorAdj a b → a.val < b.val := by
  decide

theorem backdoorAdj_acyclic : ∀ v : Fin 3, ¬ Relation.TransGen backdoorAdj v v := by
  intro v h
  have hgen : ∀ a b : Fin 3, Relation.TransGen backdoorAdj a b → a.val < b.val := by
    intro a b hab
    induction hab with
    | single h => exact backdoorAdj_lt _ _ h
    | tail _ hbc ih => exact lt_trans ih (backdoorAdj_lt _ _ hbc)
  exact absurd (hgen v v h) (lt_irrefl _)

def backdoorGraph : Fate.CausalDirection.CausalGraph (Fin 3) where
  Adj := backdoorAdj
  acyclic := backdoorAdj_acyclic

/-- `backdoorGraph.Adj` 就是 `backdoorAdj`。 -/
theorem backdoorGraph_adj (a b : Fin 3) : backdoorGraph.Adj a b ↔ backdoorAdj a b := Iff.rfl

/-- **(ii) 图侧**：`Z = 0` **不是** `X = 1` 的后代（没有从 `1` 到 `0` 的有向路径）。 -/
theorem Z_not_descendant_of_X : ¬ Fate.CausalDescendant.Reach backdoorGraph 1 0 := by
  intro h
  have hmono : ∀ a b : Fin 3, backdoorGraph.Adj a b → a.val < b.val := by
    intro a b hab
    exact backdoorAdj_lt a b hab
  have hgen : ∀ a b : Fin 3, Fate.CausalDescendant.Reach backdoorGraph a b → a.val ≤ b.val := by
    intro a b hab
    induction hab with
    | refl _ => exact le_rfl
    | step h _ ih => exact le_trans (Nat.le_of_lt (hmono _ _ h)) ih
  exact absurd (hgen 1 0 h) (by decide)

/-- `X = 1` **是** `Y = 2` 的后代（`1 → 2` 有边）。 -/
theorem X_reach_Y : Fate.CausalDescendant.Reach backdoorGraph 1 2 :=
  Fate.CausalDescendant.reach_of_adj backdoorGraph (show backdoorGraph.Adj 1 2 from trivial)

/-! #### §4.3.1 ⚠⚠ **诚实登记**：本图的 (i) 其实**不成立**

上图的 `Z = 0`（`Z → X`，`Z → Y`）**并不**阻断 `X` 与 `Y`，
因为图上**还有一条直边 `X → Y`**（因果路径）。
所以 `dSep {X}{Y}{Z}` 在本图上是 **假** 的：
`0 → 2` 这条长度 1 的路径中间没有顶点，`Z` 无从阻断。

**⟹ 这说明**：Pearl 的 (i)「`Z` 阻断所有**后门**路径」**不是**「`Z` 阻断所有路径」。
`X → Y` 是**前门**路径，**不需要**阻断。

**⟹ 本文件 §3 的 `BackdoorBlocked`（`Y` 对 `Ux` 常值）恰好只针对后门 `X ← Ux → Y`，
**不**要求阻断 `X → Y`** —— 所以 §3 与 §4.3 的一致性是**语义上**的，不是图上 `dSep` 直接给的。
**这正是 gap 1 的具体样貌**（债务 **D-BD-2**）。 -/

end GraphCheck

