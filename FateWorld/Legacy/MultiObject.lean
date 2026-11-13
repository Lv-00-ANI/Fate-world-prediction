import FateWorld.Legacy.Frame
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! ===========================================================================
  §0  多对象系统 = 积空间（作者裁决）

  **作者原话**：**「独立是一个对象，合在一起也是一个对象，它面向任何系统」**

  ## 核心洞察：对象层是自相似的

  任何东西都可以是 `O`。**⟹ 「多对象」不是特殊情形，只是「选了更大的对象」。**

  ## 作者裁决：全部取积空间

  | 空间 | 联合系统 |
  |---|---|
  | 状态 `X` | `X₁ × X₂` |
  | 参数 `Θ` | `Θ₁ × Θ₂` |

  **⚠ 为什么取积**：**保留个体可分解性**。若参数不积，
  就无法追问「是 `O₁` 的参数错了，还是 `O₂` 的」—— 而这正是理论的核心价值。

  ## ⭐ 技术关键：`SecondCountableTopology` 作为普通参数

  **障碍**：`StateSpace` 的 `TopologicalSpace` 是**实例字段**（`[topo : ...]`），
  故在**类型类参数位置**引用它会导致实例搜索循环：

  ```
  需要 SecondCountableTopologyEither → 需要 TopologicalSpace → 需要 letI 绑定
  letI 绑定时 Lean 尝试实例搜索 → 又需要 SecondCountableTopologyEither
  ```

  **解法**：把 `SecondCountableTopology` 作为**普通参数**（`@SecondCountableTopology X.Carrier X.topo`），
  而不是 `[...]` 类型类参数。**实测有效。**

  **⚠ 为什么积空间需要它**：Mathlib 的 `Prod.opensMeasurableSpace` 需要
  `[SecondCountableTopologyEither]`，而后者需要第二可数性。

  ## 理论开放问题 8.13 的部分解答

  | 概念 | 联合系统 |
  |---|---|
  | **命** | `θ = (θ₁, θ₂)` —— **可分解**（本节已证）|
  | **运** | 取积 —— 可含对方的**状态**（即「相互影响」）|
  | **命运** | `{x_t}` 在 `X₁ × X₂` 上的**联合轨迹** |

  ## ⚠ 本节**未做**的

  1. **`Frame.prod`**（五空间全取积）—— 需 `InputSpace` 等的 `TopologicalSpace` 前提，
     尚未处理。
  2. **「外生性的相对性」** —— 是观察，不是定理。
  3. **联合系统的转移核** —— 需把两个 `Step` 组合，涉及「耦合后单步怎么算」。
  4. **任何动力学性质**。
  =========================================================================== -/

namespace Fate

universe u

/-! ### §0.1 空间的积（在 Fate 根命名空间，便于字段记法 `X.prod Y`） -/

/-- **两个 `StateSpace` 的积**。

**`SecondCountableTopology` 作为普通参数**（非类型类参数）—— 见文件头说明。 -/
def StateSpace.prod (X₁ X₂ : StateSpace.{u})
    (h₁ : @SecondCountableTopology X₁.Carrier X₁.topo)
    (h₂ : @SecondCountableTopology X₂.Carrier X₂.topo) : StateSpace.{u} :=
  letI : TopologicalSpace X₁.Carrier := X₁.topo
  letI : TopologicalSpace X₂.Carrier := X₂.topo
  letI : MeasurableSpace X₁.Carrier := X₁.meas
  letI : MeasurableSpace X₂.Carrier := X₂.meas
  haveI : SecondCountableTopology X₁.Carrier := h₁
  haveI : SecondCountableTopology X₂.Carrier := h₂
  haveI : OpensMeasurableSpace X₁.Carrier := ⟨X₁.borel_le⟩
  haveI : OpensMeasurableSpace X₂.Carrier := ⟨X₂.borel_le⟩
  { Carrier := X₁.Carrier × X₂.Carrier
    topo := inferInstance
    meas := inferInstance
    borel_le := OpensMeasurableSpace.borel_le }

/-- **两个 `ThetaSpace` 的积**（命的联合）。

**保留可分解性**：`(θ₁, θ₂)` 可分别投影，从而能追问「是谁的参数错了」。

**⚠ 无需第二可数性** —— `ThetaSpace` 不需要 Borel 相容性字段。 -/
def ThetaSpace.prod (Θ₁ Θ₂ : ThetaSpace.{u}) : ThetaSpace.{u} :=
  letI : TopologicalSpace Θ₁.Carrier := Θ₁.topo
  letI : TopologicalSpace Θ₂.Carrier := Θ₂.topo
  letI : MeasurableSpace Θ₁.Carrier := Θ₁.meas
  letI : MeasurableSpace Θ₂.Carrier := Θ₂.meas
  { Carrier := Θ₁.Carrier × Θ₂.Carrier
    topo := inferInstance
    meas := inferInstance }

/-! ### §0.2 ⭐ 可分解性（核心性质）

**这是「能追问是谁的参数错了」的形式化** —— 也是「全部取积」的真正理由。 -/

/-- **参数的第一分量**（取 `O₁` 的参数）。 -/
def thetaFst {Θ₁ Θ₂ : ThetaSpace.{u}} (θ : (Θ₁.prod Θ₂).Carrier) : Θ₁.Carrier := θ.1

/-- **参数的第二分量**（取 `O₂` 的参数）。 -/
def thetaSnd {Θ₁ Θ₂ : ThetaSpace.{u}} (θ : (Θ₁.prod Θ₂).Carrier) : Θ₂.Carrier := θ.2

/-- ⭐ **参数的分解互逆**：拆开再装回是恒等。

**⟹ 联合参数不丢信息** —— 可以无损地拆回各自的参数。 -/
theorem theta_decompose_recompose {Θ₁ Θ₂ : ThetaSpace.{u}}
    (θ : (Θ₁.prod Θ₂).Carrier) : (thetaFst θ, thetaSnd θ) = θ := rfl

/-- ⭐ **参数的分解是满射**：任何一对参数都能装配成联合参数。 -/
theorem theta_prod_surjective {Θ₁ Θ₂ : ThetaSpace.{u}} :
    Function.Surjective (fun (p : Θ₁.Carrier × Θ₂.Carrier) =>
      (p : (Θ₁.prod Θ₂).Carrier)) :=
  fun p => ⟨p, rfl⟩

/-- ⭐ **状态的分解互逆**（同参数）。 -/
theorem state_decompose_recompose {X₁ X₂ : StateSpace.{u}}
    (h₁ : @SecondCountableTopology X₁.Carrier X₁.topo)
    (h₂ : @SecondCountableTopology X₂.Carrier X₂.topo)
    (x : (X₁.prod X₂ h₁ h₂).Carrier) : (x.1, x.2) = x := rfl

namespace MultiObject

/-! ### §0.3 ⭐ 相互影响 -/

/-- **单向耦合**：`O₁` 的外生输入依赖 `O₂` 的状态。

这是「相互作用」的最简形式 —— 也是理论里唯一需要的机制。 -/
def Coupling (F₁ F₂ : Frame) : Type _ := F₂.X.Carrier → F₁.U.Carrier

/-- **双向耦合**：两个对象互相影响。 -/
def BidirectionalCoupling (F₁ F₂ : Frame) : Type _ :=
  (F₂.X.Carrier → F₁.U.Carrier) × (F₁.X.Carrier → F₂.U.Carrier)

/-! ### §0.4 ⚠ 「外生」是相对于对象边界的（观察，非定理）

**若 `u^{(1)}` 依赖 `x^{(2)}`**：
* **从 `O₁` 看**：`u^{(1)}` 确实外生（不由 `O₁` 的机制产生）
* **从联合系统看**：`u^{(1)}` 不外生（由 `O₂` 决定）

**⟹ 「外生」不是绝对的，是相对于边界而言的。**

这与作者「对象层自相似」完全一致：**边界自己选，外生性随之变**。
-/

end MultiObject

end Fate
