import Mathlib.Data.Set.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Predict.Counterfactual
/-!
  # Predict · FrameBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FrameBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame, Counterfactual
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §2  把 `Model`/`Obs` 接到本项目的 `Frame`（突破的具体化）

  **背景**：`Fate/Counterfactual.lean` 的突破（商上单值化）是在**抽象 `Model`** 上证的：

  ```lean
  structure Model where
    SCM : Type*      -- 结构方程集
    CF  : Type*      -- 反事实预测空间
    Obs : SCM → CF   -- 反事实观测泛函
  ```

  **本节的任务**：把这个抽象接到本项目的**具体类型**上。

  ## 接法

  本项目的主公式是
  $$x_{t+1} = f(x_t, u_t, \varepsilon_t;\ \theta,\ a_t)$$
  其中 `FateV2.Model.Step F` 就是 $f$ 的类型。

  **故**：
  - **`SCM`** := **`FateV2.Model.Step F`**（机制，即"结构方程"）
  - **`CF`** := **轨迹生成器** `TrajGen F ι` 的像（反事实预测 = "若机制是 f，轨迹会怎样"）
  - **`Obs`** := 从机制到其诱导轨迹的映射

  **⚠ 诚实标注**：`Obs` 的具体构造**需要轨迹生成器** `TrajGen` 的具体实现，
  而本项目只给了 `TrajGen` 的**类型**（未给具体函数）。
  **故本节给出的是「接口」，`Obs` 作为参数传入** —— 这是**忠实于现状**的做法，
  不假装已经构造出 `Obs`。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
open FateV2.Predict
namespace FrameBridge

open FateV2.Predict.Counterfactual

variable (F : FateV2.Model.Frame)

/-! ### §2.1 核心对应：`SCM` ↔ `Step` -/

/-- ⭐ **本项目的桥模型**：把抽象的 `Model` 具体化为「机制 → 反事实」的观测结构。

**三个字段的对应**：

| 抽象字段 | 本项目的具体化 |
|---|---|
| `SCM` | **`FateV2.Model.Step F`** —— 机制 $f$（即"结构方程"）|
| `CF` | 反事实预测空间（**由调用者给出**）|
| `Obs` | 从机制读出反事实（**由调用者给出**）|

**⚠ 为什么 `CF` 与 `Obs` 仍作参数**：
本项目只给了 `TrajGen` 的**类型**，未给具体实现；
`Obs` 的具体形式依赖轨迹生成器如何实现。
**强行构造会给出一条未经验证的断言** —— 故此处**如实留参数**。 -/
def frameModel (CF : Type*) (Obs : FateV2.Model.Step F → CF) : FateV2.Predict.Counterfactual.Model where
  SCM := FateV2.Model.Step F
  CF := CF
  Obs := Obs

/-! ### §2.2 桥纤维在 `Step` 上的具体形态 -/

/-- ⭐ **桥的纤维**（在 `Step` 上的具体化）：
给定一个机制 $f_0$，**与它观测不可区分的全部机制**。

$$\mathfrak{F}|_{f_0} := \{\, f : \mathrm{Step}\,F \mid \mathrm{Obs}\,f = \mathrm{Obs}\,f_0 \,\}$$

**这是抽象 `𝔉|_G` 在本项目里的精确落点**：
- 抽象里的"给定图 $G$" → 本项目里"给定机制 $f_0$"
- 抽象里的"全部 𝓕" → 本项目里"全部 `FateV2.Model.Step F`" -/
def bridgeFiber {CF : Type*} (Obs : FateV2.Model.Step F → CF) (f₀ : FateV2.Model.Step F) : Set (FateV2.Model.Step F) :=
  { f | Obs f = Obs f₀ }

/-! ### §2.3 ⭐ 把突破的定理搬到 `Step` 上 -/

/-- ⭐⭐ **突破的具体化**：桥在「反事实商」上单值。

**这是 `Counterfactual.obsOnQuot_injective` 在本项目类型上的直接实例化。**

**含义**：
即使 $\mathfrak{F}|_{f_0}$ 本身含**无穷多个**机制（桥多值），
把它们按「反事实不可区分」商掉之后，
**反事实观测在商上是单射的** —— **即桥在该商上单值化。**

**⚠ 无前件**：本定理对**任意** `Obs` 成立（不需要 `Obs` 单射或常值）。 -/
theorem bridge_single_valued_on_quotient {CF : Type*} (Obs : FateV2.Model.Step F → CF)
    (f₀ : FateV2.Model.Step F) :
    Function.Injective
      (obsOnQuot (frameModel F CF Obs) (bridgeFiber F Obs f₀)) :=
  obsOnQuot_injective (frameModel F CF Obs) (bridgeFiber F Obs f₀)

/-- ⭐ **桥商单值 ⟺ 观测在纤维上常值**（`cfQuotient_subsingleton_iff` 的实例化）。

**即**：桥**完全塌缩**当且仅当该机制与它纤维内的**所有**机制反事实等价。 -/
theorem bridge_quot_subsingleton_iff {CF : Type*} (Obs : FateV2.Model.Step F → CF)
    (f₀ : FateV2.Model.Step F) :
    Subsingleton (cfQuotient (frameModel F CF Obs) (bridgeFiber F Obs f₀))
      ↔ ∀ f ∈ bridgeFiber F Obs f₀, ∀ g ∈ bridgeFiber F Obs f₀, Obs f = Obs g :=
  cfQuotient_subsingleton_iff (frameModel F CF Obs) (bridgeFiber F Obs f₀)

/-- ⭐ **三情形穷尽**（`trichotomy` 的实例化）：

对任意机制 $f_0$ 与任意观测泛函，桥的纤维必落于**三情形之一**：

| 情形 | 含义 |
|---|---|
| **A 塌缩** | 观测在纤维上常值（商单点）|
| **B 忠实** | 观测在纤维上单射（商 ≅ 纤维，**桥不单值**）|
| **C 中间地带** | 既非常值又非单射 |

**⚠ 情形 C 的商基数未给闭式** —— 见 `Counterfactual` 的诚实标注。 -/
theorem bridge_trichotomy {CF : Type*} (Obs : FateV2.Model.Step F → CF) (f₀ : FateV2.Model.Step F) :
    Collapse (frameModel F CF Obs) (bridgeFiber F Obs f₀)
      ∨ Faithful (frameModel F CF Obs) (bridgeFiber F Obs f₀)
      ∨ MiddleZone (frameModel F CF Obs) (bridgeFiber F Obs f₀) :=
  trichotomy (frameModel F CF Obs) (bridgeFiber F Obs f₀)

/-! ### §2.4 ⭐⭐ 关键：项目里「桥多值」的具体见证 -/

/-- ⭐⭐ **见证：只要存在「观测不可区分的不同机制」，桥的商就非单点。**

**构造**：取两个**不同的机制** `f ≠ g`，但 `Obs f = Obs g`。
则纤维 `{f, g}` 的商至少含**两个不同的类**（因为 `f` 与 `g` 在 `Obs` 下相同 ——
等等，此处须注意方向）。

**⚠ 精确定理内容**：本定理断言的是
$$\exists F_0,\ \neg\,\mathrm{Subsingleton}\bigl(\mathfrak{F}_{F_0}/\sim_{\mathrm{cf}}\bigr)$$
其中 $\sim_{\mathrm{cf}} = \ker(\mathrm{Obs}|_{F_0})$。

**⟹ 若 `Obs` 在 `{f,g}` 上**单射**（即 `Obs f ≠ Obs g`），则商含两点，非单点。**

**故前件应是 `Obs f ≠ Obs g`（而非相等）** —— 这是本定理的**正确形式**。 -/
theorem bridge_multivalued_witness {CF : Type*} (Obs : FateV2.Model.Step F → CF)
    {f g : FateV2.Model.Step F} (hne : f ≠ g) (hfg : Obs f ≠ Obs g) :
    ∃ F₀ : Set (FateV2.Model.Step F), ¬ Subsingleton (cfQuotient (frameModel F CF Obs) F₀) := by
  classical
  refine ⟨{f, g}, ?_⟩
  intro hs
  have hmem_f : f ∈ ({f, g} : Set (FateV2.Model.Step F)) := by simp
  have hmem_g : g ∈ ({f, g} : Set (FateV2.Model.Step F)) := by simp
  have heq : (Quotient.mk _ ⟨f, hmem_f⟩ : cfQuotient (frameModel F CF Obs) {f, g})
           = (Quotient.mk _ ⟨g, hmem_g⟩ : cfQuotient (frameModel F CF Obs) {f, g}) :=
    hs.elim _ _
  exact hfg (Quotient.exact heq)

end FrameBridge

end FateV2.Predict
