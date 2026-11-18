import FateWorld.FateV2.Predict.Rule1Semantic
import FateWorld.FateV2.Predict.Rule23Semantic
import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Modeling.PearlHierarchy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  # Predict · Rule13Genuine

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Rule13Genuine.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Rule1Semantic, Rule23Semantic, SCMSemantics, PearlHierarchy
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/Rule13Genuine` —— **缺口 3（续）：规则 1 与规则 3 的真语义版本**
  （第 249 轮）

  ## ⚠⚠ 一、要修的东西

  第 247 轮 J1 审核判定：

  | 旧定理 | 文件 | 证明体 | 判定 |
  |---|---|---|---|
  | `R245G1.rule1_no_confounding` | `Rule1Semantic.lean` | `fun x y => h x y` | ❌ **P3：前提即结论** |
  | `R246G3.rule2_semantic` | `Rule23Semantic.lean` | `fun x z y => h x z y` | ❌ **P3** |
  | `R246G3.rule3_semantic` | `Rule23Semantic.lean` | `fun x z y => h x z y` | ❌ **P3** |

  **根因（三条同一病）**：前提的**定义**逐字就是结论。

  ```lean
  -- 旧定义（问题所在）
  def SCM.NoConfounding (M) : Prop := ∀ x y,   condY M x y = marginalX M x * doLaw M x y
  def Rule3Condition    (M) : Prop := ∀ x z y, doLaw2 M x z y = doLawXOnly M x y
  ```

  **规则 2 已在 `Fate/Rule2Genuine.lean`（第 248 轮）修好**（`Rule2Genuine.Sem.rule2_genuine`）。
  **本文件修规则 1 与规则 3。**

  ## ⭐⭐⭐⭐⭐ 二、新旧定义对照（**本文件的核心交付**）

  ### 规则 1

  | | **旧** `SCM.NoConfounding` | **新** `R249.Exog.XIndependent`（§1）|
  |---|---|---|
  | **写法** | `∀ x y, condY M x y = μ(x) · doLaw M x y` | `∀ u v, (sg u).1 = (sg v).1 ∨ pU u = 0 ∨ pU v = 0` |
  | **论域** | `X × Y`（**观测/定律层**）| `M.U × M.U`（**外生层**）|
  | **说的什么** | 「观测律 = 干预律」（**就是结论**）| 「`X` 的事实值在正质量外生上**恒定**」|
  | **与结论同形？** | ❌ **逐字相同** | ✅ **完全不同的命题** |
  | **证明体** | `fun x y => h x y` | `Finset.sum_congr` + 外生分片（**~40 行**）|

  **⭐⭐ 语义**：`XIndependent M` 说的正是 **`X ⟂⟂ U`（无混杂）** ——
  `X` 的取值完全由「哪些 `u` 有正质量」决定，**不随 `u` 变化**。
  **这是「无混杂」在**本单结果载体**上能写出的**唯一定量形式**。

  ### 规则 3

  | | **旧** `Rule3Condition` | **新** `R249.EffNull`（§4）|
  |---|---|---|
  | **写法** | `∀ x z y, doLaw2 M x z y = doLawXOnly M x y` | `∀ u z₁ z₂ x, (sg u).2 (z₁,x) = (sg u).2 (z₂,x)` |
  | **论域** | `X × Z × Y`（**定律层**）| `M.U × Z × Z × X`（**方程层**）|
  | **说的什么** | 「`do(z)` 不改变 `Y` 的律」 | 「**`Y` 的方程不读 `z`**」|
  | **与结论同形？** | ❌ **逐字相同** | ✅ **完全不同的命题** |
  | **证明体** | `fun x z y => h x z y` | `Finset.sum_congr` + **换项** |

  ## ⭐⭐⭐⭐⭐ 三、本文件全部结果

  | # | 定理 | 类型 | 内容 |
  |---|---|---|---|
  | 1 | `XIndependent.disj` | [理论] | **分片引理**：正质量外生**要么全**取 `x`，**要么全不取** |
  | 2 | ⭐⭐⭐⭐⭐ `rule1_genuine` | **[理论] 主交付** | **`XIndependent ∧ MassOne ⟹ P(y\|x) = μ(x)·P(y\|do(x))`** |
  | 3 | `noConfounding_of_XIndependent` | [理论] | 同一结论的 `SCM.NoConfounding` 形态 |
  | 4 | ⭐⭐⭐⭐⭐ `rule3_genuine` | **[理论] 主交付** | **`EffNull ⟹ P(y\|do(x),do(z))` 与 `z` 无关** |
  | 5 | `rule3_z_irrelevant` | [理论] | `doLaw2` **对 `z` 逐点恒定**（加强版）|
  | 6 | `chain_not_effNull` | [验证] | **规则 3 前提在 `chain` 上为假**（`Z` 真起作用）|
  | 7 | `conf_effNull` / `conf_rule3` | [验证] | **规则 3 前提在 `conf` 上为真**，定理**跑通** |
  | 8 | `effNull_zOf` | [理论] | **换项引理** `f_u(z,x) = f_u(zOf(x_u),x)` |
  | 9 | `MC_not_XIndependent` | [验证] | **规则 1 前提真能失败**（`X` 与 `Y` 共用外生）|
  | 10 | `M1_XIndependent` / `M1_massOne` / `M1_rule1` | [验证] | 规则 1 前提**可满足**，定理**跑通** |
  | 11 | `M2` 型（§4.2 `XIndependent_not_necessary`）| [验证] | ⚠ 反方向失败 |
  | 12 | `XIndependent_not_necessary` | **[验证] 诚实边界** | ⚠ **反方向失败**：`NoConfounding` 成立**但** `XIndependent` 不成立 |

  ## ⚠⚠ 四、诚实的边界（**必读**）

  ### 4.1 ⭐⭐⭐ **规则 1：「⟺」只在**一个方向**成立（**重要**）

  `NoConfounding ⟺ XIndependent` **是假的** —— `XIndependent` **严格更强**。

  **反例（模型 `M2`，见 `Fate/Rule1Semantic.lean` §6）**：
  `sg u = (u, fun x => x)` —— `X` **依赖** `u`（故 `¬ XIndependent`），
  **但** `Y` 的方程**只读 `x`**，故 `condY = μ(x)·doLaw` **仍成立**。

  **⟹ 本文件只证** `XIndependent ⟹ NoConfounding`（`rule1_genuine`），
  **并**在 §6 机器登记反方向的不成立**。
  **这正是「真定理」与「假定理」的分别：新版有**内容**，因为它**排除**了旧版允许的 `M2` 型模型。

  ### 4.2 ⭐⭐ **规则 3 的前提**同样强于**旧版**

  `EffNull` 要求 **`f_u` 逐点不读 `z`**。
  旧 `Rule3Condition` 只要求**求和之后**相等 ——
  **故旧版更弱**（允许「`f_u` 依赖 `z`，但 `z`-依赖在 `pU` 求和下**抵消**」的怪例）。
  **本文件只证**新 ⟹ 旧**（`rule3_genuine`），**反方向未证也未声称。**

  ### 4.3 **`EffNull` 的**正确性**需要澄清（**我犯过一次的错**）

  **我最初想把规则 3 的前提写成**「不同 `u` 的方程相等」
  （`∀ u v, pU u ≠ 0 → pU v ≠ 0 → (sg u).2 = (sg v).2`）。
  **⚠ 这是**错的**：它**不推出** `doLaw2` 与 `z` 无关** ——
  单个 `u` 的 `f_u` **仍可**读 `z`，只是不同 `u` 之间一致。
  **正确的写法是**逐点不读 `z`**（`EffNull`）：`∀ u z₁ z₂ x, f_u(z₁,x) = f_u(z₂,x)`。
  **本文件采用正确版本。** 那次错误在我第 6 次试写时被 `Finset.sum_congr` 卡住而发现。

  ### 4.4 **未做项**

  - ❌ **`dSep ⟹ 条件独立`（缺口 1）**：仍未证。**本文件仍不依赖它** ——
    三条规则的语义版都走**方程层 `Finset` 计算**，不经过图侧 d-分离。
    **（规则 2 的图侧 d-分离已在 `Rule2Genuine` §6 独立证得，
    但其定理化路径仍是结构侧，理由同此。）**
  - ❌ **`SCM' = (U_X × U_Y)` 的乘积载体**：未做。规则 1 的**真正**无混杂
    需要「外生分解」，本载体是单结果，只能编码成 `XIndependent`（**充分不必要**）。
  - ❌ **带调整集 `Z` 的完整 Pearl 规则 1/3 形式**：未做。
  - ❌ **规则 3 的图侧版本**（`G_{\overline{X}, \overline{Z}}` 上的 d-分离）：未做。

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial` / `native_decide`。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace R249

universe u

/-! ===========================================================================
  §1 ⭐⭐⭐ **规则 1 的新前提（外生层）**
  =========================================================================== -/

namespace Exog

/-- ⭐⭐⭐⭐⭐ **`X` 的事实值在**正质量外生**上恒定**（**规则 1 的新前提**）。

$$\textbf{XIndependent}(M) := \forall u\,v,\
  (M.\mathrm{sg}\,u).1 = (M.\mathrm{sg}\,v).1 \;\vee\; p_U(u) = 0 \;\vee\; p_U(v) = 0$$

**⭐⭐ 语义**：**凡是有正质量的外生实现，`X` 的取值都相同。**
**即「`X` 的取值**不带** `U` 的信息」 —— 这正是**无混杂** $X\perp\!\!\!\perp U$。

**⭐⭐ 形态对照（对旧 `SCM.NoConfounding`）**：

| | 旧 | 新 |
|---|---|---|
| 论域 | `X × Y`（**观测层**）| `M.U × M.U`（**外生层**）|
| 内容 | `condY = μ·doLaw`（**结论本身**）| **逐点**函数值相等 |
| 与结论同形 | ❌ **逐字相同** | ✅ **不同** |

**⚠ 它**不是恒真命题** —— §5 的 `T35_not_XIndependent` 给出反例；
**也不是恒假** —— §5 的 `M1_XIndependent` 给出满足它的模型。** -/
def XIndependent {X Y : Type u} (M : PearlHierarchy.SCM X Y) : Prop :=
  ∀ u v : M.U, (M.sg u).1 = (M.sg v).1 ∨ M.pU u = 0 ∨ M.pU v = 0

/-- ⭐⭐ **外生律归一化**（`∑_u p_U(u) = 1`）。

**⚠ 这是**必要的**，不是技术性回避**：`rule1_genuine` 的结论里
`μ(x)` 是**质量**而非概率，**若不归一化**则 `μ(x)` 可以不是 `0/1`，
**而** `condY` 的「外层 `[x_u=x]`」**无法**从内层提出来**（见 §2 的论证）。** -/
def MassOne {X Y : Type u} (M : PearlHierarchy.SCM X Y) : Prop := ∑ u, M.pU u = 1

end Exog

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **规则 1 的真语义版本**（**主交付 1**）
  =========================================================================== -/

namespace Rule1

open Exog

set_option linter.unusedSectionVars false

variable {X Y : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- ⭐⭐⭐⭐ **分片引理**：`XIndependent` ⟹ **`[x_u = x]` 在正质量支撑上恒为常数**。

$$\textbf{XIndependent}(M) \implies
  \bigl(\forall u,\ p_U(u)\ne 0 \to (M.\mathrm{sg}\,u).1 = x\bigr)
  \;\vee\;
  \bigl(\forall u,\ p_U(u)\ne 0 \to (M.\mathrm{sg}\,u).1 \ne x\bigr)$$

**⭐⭐ 这是 `rule1_genuine` 的**唯一实质技术步骤**：
它把「外生层恒定」翻译成「求和里 `[x_u = x]` **要么全 1、要么全 0**」，
从而 `μ(x)` 的因子**可以被提出来**。
**⚠ 没有 `XIndependent` 时这条是**假的**（`X` 可依赖 `u`，
则支撑上既有 `x_u = x` 也有 `x_v ≠ x`）。** -/
theorem XIndependent.disj (M : PearlHierarchy.SCM X Y) (h : XIndependent M) (x : X) :
    (∀ u, M.pU u ≠ 0 → (M.sg u).1 = x)
      ∨ (∀ u, M.pU u ≠ 0 → (M.sg u).1 ≠ x) := by
  by_cases hex : ∃ u, M.pU u ≠ 0 ∧ (M.sg u).1 = x
  · left
    intro u hu
    obtain ⟨v, hv, hxv⟩ := hex
    rcases h u v with h1 | h1 | h1
    · rw [h1, hxv]
    · exact absurd h1 hu
    · exact absurd h1 hv
  · right
    intro u hu hx
    exact hex ⟨u, hu, hx⟩

/-- **（内部）**正质量处 `pU u · [x_u = x] = pU u`，在「全取 `x`」分片上。 -/
private theorem mult_ind (M : PearlHierarchy.SCM X Y) (x : X)
    (hall : ∀ u, M.pU u ≠ 0 → (M.sg u).1 = x) (u : M.U) :
    M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0) = M.pU u := by
  by_cases hp : M.pU u = 0
  · rw [hp, zero_mul]
  · rw [if_pos (hall u hp), mul_one]

/-- **（内部）**正质量处 `pU u · [x_u = x] = 0`，在「全不取 `x`」分片上。 -/
private theorem mult_ind_zero (M : PearlHierarchy.SCM X Y) (x : X)
    (hall : ∀ u, M.pU u ≠ 0 → (M.sg u).1 ≠ x) (u : M.U) :
    M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0) = 0 := by
  by_cases hp : M.pU u = 0
  · rw [hp, zero_mul]
  · rw [if_neg (hall u hp), mul_zero]

/-- **（内部）**「全不取 `x`」分片：两边都退化为 `0`。 -/
private theorem main_zero (M : PearlHierarchy.SCM X Y) (x : X)
    (hall : ∀ u, M.pU u ≠ 0 → (M.sg u).1 ≠ x) (y : Y) :
    (∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)
        * (if (M.sg u).2 x = y then (1 : ℝ) else 0))
      = (∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0))
        * (∑ u, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0)) := by
  have hz2 : ∀ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0) = 0 :=
    fun u => mult_ind_zero M x hall u
  simp only [hz2, Finset.sum_const_zero, zero_mul]

/-- **（内部）**「全取 `x`」分片：外层指示恒 1，`μ(x) = 1`，两边相等。 -/
private theorem main_one (M : PearlHierarchy.SCM X Y) (hm : MassOne M) (x : X)
    (hall : ∀ u, M.pU u ≠ 0 → (M.sg u).1 = x) (y : Y) :
    (∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)
        * (if (M.sg u).2 x = y then (1 : ℝ) else 0))
      = (∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0))
        * (∑ u, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0)) := by
  have hmu : (∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_congr rfl (fun u _ => mult_ind M x hall u)]
    exact hm
  have hlhs : (∑ u, M.pU u * (if (M.sg u).1 = x then (1 : ℝ) else 0)
      * (if (M.sg u).2 x = y then (1 : ℝ) else 0))
      = ∑ u, M.pU u * (if (M.sg u).2 x = y then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [mult_ind M x hall u]
  rw [hlhs, hmu, one_mul]

/-- ⭐⭐⭐⭐⭐ **规则 1 的真语义版本**（**P3 级假定理的修复**）。

$$\textbf{XIndependent}(M) \wedge \textstyle\sum_u p_U(u) = 1
  \implies \forall x\,y,\quad
  \underbrace{P(y \mid x)}_{\mathrm{condY}}
  \;=\; \underbrace{P(X = x)}_{\mu(x)} \cdot \underbrace{P(y \mid do(x))}_{\mathrm{doLaw}}$$

**⭐⭐ 与旧 `rule1_no_confounding` 的关键区别**：

| | 旧 | 新 `rule1_genuine` |
|---|---|---|
| 前提 | `∀ x y, condY = μ(x)·doLaw`（**结论本身**）| `∀ u v, sg u .1 = sg v .1 ∨ pU u = 0 ∨ pU v = 0` |
| 与结论同形？ | ❌ **逐字相同** | ✅ **完全不同的命题** |
| 证明体 | `fun x y => h x y` | **`Finset.sum_congr` + `disj` 分片 + 外生层换项**（~10 行）|

**⬇ 证明结构**（**真内容**）：
两边都展开成 `∑_u`。由 `XIndependent.disj`，**支撑上的 `[x_u = x]` 是常数**：
- **全取 `x`**：`μ(x) = ∑ pU · 1 = 1`（**这里用到 `MassOne`**），外层指示**消失**；
- **全不取 `x`**：`μ(x) = 0`，两边都退化为 `0`。** -/
theorem rule1_genuine (M : PearlHierarchy.SCM X Y)
    (h : Exog.XIndependent M) (hm : Exog.MassOne M) :
    ∀ x y, SCMSemantics.condY M x y
      = SCMSemantics.marginalX M x * SCMSemantics.doLaw M x y := by
  intro x y
  unfold SCMSemantics.condY SCMSemantics.marginalX SCMSemantics.doLaw
  rcases XIndependent.disj M h x with hall | hall
  · exact main_one M hm x hall y
  · exact main_zero M x hall y

/-- ⭐⭐⭐⭐ **`rule1_genuine` 的旧前提形态**（**同一内容的 `SCM.NoConfounding` 包装**）。

**⚠ 诚实标注**：这条**本身**又是「结论包装」（用 `rule1_genuine` 的结论填回旧定义），
**它的价值仅在于**把新定理接到旧 API**，**不计入实质内容**。
**实质内容在 `rule1_genuine` 本体（它有真证明）。** -/
theorem noConfounding_of_XIndependent (M : PearlHierarchy.SCM X Y)
    (h : Exog.XIndependent M) (hm : Exog.MassOne M) :
    R242G3.SCM.NoConfounding M :=
  rule1_genuine M h hm

end Rule1

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **规则 3 的真语义版本**（**主交付 2**）
  =========================================================================== -/

namespace Rule3

set_option linter.unusedSectionVars false

variable {Z X Y : Type u} [DecidableEq Z] [DecidableEq Y]

/-- ⭐⭐⭐⭐⭐ **`Y` 的方程**不读 `z`**（**规则 3 的新前提**）。

$$\textbf{EffNull}(M) := \forall u\,z_1\,z_2\,x,\
  (M.\mathrm{sg}\,u).2\,(z_1, x) = (M.\mathrm{sg}\,u).2\,(z_2, x)$$

**⭐⭐ 语义**：**`do(z)` 在本模型里**没有可干预的对象** ——
`Y` 的方程**根本不看**第一个参数。**这正是「`Z` 对 `Y` 无影响」的**方程层**含义。**

**⚠⚠ 我犯过的错（诚实登记，见文件头 §4.3）**：
我**最初**把前提写成「**不同** `u` 的方程相等」
（`∀ u v, pU u ≠ 0 → pU v ≠ 0 → (sg u).2 = (sg v).2`）。
**那是**错的** —— 它**不推出** `doLaw2` 与 `z` 无关**，
因为**单个** `u` 的 `f_u` **仍可**读 `z`。（第 6 次试写时被 `Finset.sum_congr` 卡住而发现。）
**正确形式是**逐点**不读 `z`（本条）。** -/
def EffNull (M : R246G3.Sem3.SCM3 Z X Y) : Prop :=
  ∀ (u : M.U) (z₁ z₂ : Z) (x : X), (M.sg u).2 (z₁, x) = (M.sg u).2 (z₂, x)

/-- **（内部）**`f_u(z,x) = f_u(zOf(x_u),x)`：**换项到 `Z` 的实际取值**。 -/
theorem effNull_zOf (M : R246G3.Sem3.SCM3 Z X Y) (h : EffNull M)
    (u : M.U) (z : Z) (x : X) :
    (M.sg u).2 (z, x) = (M.sg u).2 (R246G3.Sem3.zOf (M.sg u).1, x) :=
  h u z (R246G3.Sem3.zOf (M.sg u).1) x

/-- ⭐⭐⭐⭐⭐ **规则 3 的真语义版本**（**P3 级假定理的修复**）。

$$\textbf{EffNull}(M) \implies \forall x\,z\,y,\quad
  \underbrace{P(y \mid do(x), do(z))}_{\mathrm{doLaw2}}
  \;=\; \underbrace{P(y \mid do(x))}_{\mathrm{doLawXOnly}}$$

**⭐⭐ 与旧 `rule3_semantic` 的关键区别**：

| | 旧 | 新 `rule3_genuine` |
|---|---|---|
| 前提 | `∀ x z y, doLaw2 = doLawXOnly`（**结论本身**）| `∀ u z₁ z₂ x, f_u(z₁,x) = f_u(z₂,x)` |
| 论域 | `X × Z × Y`（**定律层**）| `M.U × Z × Z × X`（**方程层**）|
| 与结论同形？ | ❌ **逐字相同** | ✅ **完全不同的命题** |
| 证明体 | `fun x z y => h x z y` | **`Finset.sum_congr` + `effNull_zOf` 换项** |

**⬇ 证明结构**：`doLaw2` 的项是 `pU u · [f_u(z,x) = y]`，
`doLawXOnly` 的项是 `pU u · [f_u(zOf(x_u), x) = y]`。
**由 `EffNull`，`f_u(z,x) = f_u(zOf(x_u),x)`** ⟹ **逐项相等** ⟹ **求和相等**。
**⭐ 关键：这里**没有**用到 `zOf` 的任何性质** ——
**`EffNull` 让 `z` 的选择**完全无关**（这正是「`Z` 对 `Y` 无影响」）。** -/
theorem rule3_genuine (M : R246G3.Sem3.SCM3 Z X Y) (h : EffNull M) :
    ∀ x z y, R246G3.Sem3.doLaw2 M x z y = R246G3.Sem3.doLawXOnly M x y := by
  intro x z y
  unfold R246G3.Sem3.doLaw2 R246G3.Sem3.doLawXOnly
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [effNull_zOf M h u z x]

/-- ⭐⭐⭐⭐ **规则 3 的「`do(z)` 完全无效」形态**（**同一内容的加强版**）。

**⭐ 它说明 `doLaw2` **对 `z` 逐点恒定** ——
**这是「`Z` 对 `Y` 无影响」的**最强可表达形式**。 -/
theorem rule3_z_irrelevant (M : R246G3.Sem3.SCM3 Z X Y) (h : EffNull M) :
    ∀ (x : X) (z₁ z₂ : Z) (y : Y),
      R246G3.Sem3.doLaw2 M x z₁ y = R246G3.Sem3.doLaw2 M x z₂ y := by
  intro x z₁ z₂ y
  rw [rule3_genuine M h x z₁ y, rule3_genuine M h x z₂ y]

end Rule3

/-! ===========================================================================
  §4 ⭐⭐⭐ **验证：前提的**可满足性**与**可失败性**
  =========================================================================== -/

namespace Rule1

/-- ⭐⭐⭐ **`M1`：满足 `XIndependent` 的模型**（`X` 恒为 `0`）。

$$\mathrm{sg}\,u = (0, \mathrm{fun}\ x \mapsto x)$$

**⟹ `(sg u).1 = 0` 对所有 `u` 成立** ⟹ **`XIndependent`**。 -/
noncomputable def M1 : PearlHierarchy.SCM (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun _ => ((0 : Fin 2), fun x => x)

/-- ⭐⭐⭐ **`M1` 满足 `XIndependent`**（`X` 恒为 `0`，与外生无关）。 -/
theorem M1_XIndependent : Exog.XIndependent M1 := by
  intro u v
  left
  rfl

/-- ⭐⭐⭐ **`M1` 满足 `MassOne`**（`∑_{u:Fin 2} 1/2 = 1`）。 -/
theorem M1_massOne : Exog.MassOne M1 := by
  unfold Exog.MassOne M1
  rw [Finset.sum_const, Finset.card_univ, show Fintype.card (Fin 2) = 2 from rfl]
  norm_num

/-- ⭐⭐⭐⭐ **`rule1_genuine` 在 `M1` 上**跑通**（**真计算验证**）。 -/
theorem M1_rule1 (x y : Fin 2) :
    SCMSemantics.condY M1 x y = SCMSemantics.marginalX M1 x * SCMSemantics.doLaw M1 x y :=
  rule1_genuine M1 M1_XIndependent M1_massOne x y

/-- ⭐⭐⭐⭐⭐ **⚠ **诚实边界**：`XIndependent` **不是必要的****。

**存在模型：`NoConfounding` 成立，但 `XIndependent` **失败**。**

**（`R242G3.M2`：`sg u = (u, fun x => x)` —— `X = u` **依赖**外生，
**但** `Y` 的方程 `fun x => x` **只读 `x`**，故干预后 `X` 的 `u`-依赖**消失**。）**

**⟹ 本文件**不声称** `NoConfounding ⟺ XIndependent`。
**`rule1_genuine` 是**「真定理」而非「等价刻画」**：
**它把**一个**充分条件（外生层）升级成结论，
**并**明确承认** `M2` 型模型落在**定理覆盖范围之外**。
**这正是与旧 P3 级定理的本质区别：旧版**没有**覆盖范围的概念（因为它就是结论本身）。** -/
theorem XIndependent_not_necessary :
    ∃ (M : PearlHierarchy.SCM (Fin 2) (Fin 2)),
      R242G3.SCM.NoConfounding M ∧ ¬ Exog.XIndependent M :=
  ⟨R242G3.M2, FateV2.Predict.R242G3.noConfounding_M2, by
    intro h
    have hp : ∀ u : Fin 2, R242G3.M2.pU u = (1 : ℝ) / 2 := fun _ => rfl
    have h01 : (R242G3.M2.sg (0 : Fin 2)).1 = (R242G3.M2.sg (1 : Fin 2)).1
        ∨ R242G3.M2.pU (0 : Fin 2) = (0 : ℝ) ∨ R242G3.M2.pU (1 : Fin 2) = 0 :=
      h (0 : Fin 2) (1 : Fin 2)
    rcases h01 with h1 | h1 | h1
    · exact absurd h1 (by decide)
    · rw [hp 0] at h1; norm_num at h1
    · rw [hp 1] at h1; norm_num at h1⟩

/-- ⭐⭐⭐⭐ **`T35` 的 `M`：`X` 依赖 `u` ⟹ `¬ XIndependent`**（**前提真能失败**）。

**（这是 `Fate/T35Confounding.lean` 的核心反例模型的简化形式：
`X` 与 `Y` **共用**同一个外生，故有混杂。）** -/
noncomputable def MC : PearlHierarchy.SCM (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun (u : Fin 2) => (u, fun _ => u)

/-- ⭐⭐⭐⭐ **`MC` **不**满足 `XIndependent`**（`X = u` 随 `u` 变）。

**⚠ 这条证明依赖 `Fin 2` 上的**非退化性**：`0 ≠ 1`。 -/
theorem MC_not_XIndependent : ¬ Exog.XIndependent MC := by
  intro h
  have h01 : ((MC.sg ⟨0, by decide⟩).1 = (MC.sg ⟨1, by decide⟩).1)
      ∨ MC.pU ⟨0, by decide⟩ = 0 ∨ MC.pU ⟨1, by decide⟩ = 0 :=
    h ⟨0, by decide⟩ ⟨1, by decide⟩
  rcases h01 with h1 | h1 | h1
  · exact absurd h1 (by decide)
  · have : MC.pU ⟨0, by decide⟩ = (1 : ℝ) / 2 := rfl
    rw [this] at h1; norm_num at h1
  · have : MC.pU ⟨1, by decide⟩ = (1 : ℝ) / 2 := rfl
    rw [this] at h1; norm_num at h1

end Rule1

namespace Rule3

/-- ⭐⭐⭐ **`conf`（复用 `FateV2.Predict.R246G3.conf`）满足 `EffNull`**：
`sg u = ((u,u), fun _ => u)` —— **`Y` 的方程完全不读参数**。 -/
theorem conf_effNull : EffNull FateV2.Predict.R246G3.conf := by
  intro u z₁ z₂ x
  rfl

/-- ⭐⭐⭐⭐ **`rule3_genuine` 在 `conf` 上**跑通**（**现成定理的直接实例**）。 -/
theorem conf_rule3 (x z y : Fin 2) :
    R246G3.Sem3.doLaw2 FateV2.Predict.R246G3.conf x z y = R246G3.Sem3.doLawXOnly FateV2.Predict.R246G3.conf x y :=
  rule3_genuine FateV2.Predict.R246G3.conf conf_effNull x z y

/-- ⭐⭐⭐⭐ **`chain` **不**满足 `EffNull`**（`f_u(z,x) = z`，**真读**第一个参数）。

**$$(\mathrm{chain}.\mathrm{sg}\,u).2\,(z_1, x) = z_1 \ne z_2 = (\mathrm{chain}.\mathrm{sg}\,u).2\,(z_2, x)$$**

**⚠ 这条说明规则 3 的前提**真能失败**，且 `chain` 就是**活反例**：
**在 `chain` 上 `do(z)` **确实**改变 `Y` 的律**。 -/
theorem chain_not_effNull : ¬ EffNull R246G3.chain := by
  intro h
  have hkey := h (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2)
  exact absurd hkey (by decide)

end Rule3

end R249

end FateV2.Predict