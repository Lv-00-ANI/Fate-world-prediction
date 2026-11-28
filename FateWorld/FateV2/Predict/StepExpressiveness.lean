import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Predict.WorldModel
/-!
  # Predict · StepExpressiveness

  ## 迁移登记
  - 来源：`FateWorld/Legacy/StepExpressiveness.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame, WorldModel
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  T-1b：`Step` 签名的表达能力上限（第 44 轮，主控直接构造）

  ## 背景

  T-1 有两层：
  * **T-1a（参数层）**：`Corrects A φ` ⟹ `φ` 单射 ⟹ 最优参数唯一。**已完成。**
  * **T-1b（签名层）**：`Step := X → U → Ν → Θ → Act → X` 把 `θ` 固化成
    **`Θ.Carrier` 的一个点**，故「`θ` 是函数（策略 / 因果图 / 结构）」
    **在类型层不可表达**。**本文件是它的第一块基石。**

  ## ⭐ 为什么这条必须带 `Step`

  前几轮的 8+ 条定理全部是 `A`/`φ`/`θ*` 层事实，
  **换掉 `Step` 签名后依然为真** ⟹ 对「表达能力上限」零信息量。

  本文件的定理**陈述里出现 `Step F`** ⟹ 换签名后**不再为真**。

  ## 诚实边界

  * 本文件的定理**很弱**（接近同义反复），但它是**第一个携带 `Step` 的定理**。
  * 本文件**不**声称「`Step` 无法表达一切」——那需要反例。
  * 本文件**不**构造「θ 是算子」的平行 Frame（宇宙层级问题，见 §3 说明）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
open FateV2.Model
open FateV2.Predict
namespace StepExpressiveness

variable {F : Frame}

/-! ### §1 ⭐ 核心事实：`Step` 的 θ 位是单点 -/

/-- ⭐⭐ **【带 `Step` 的定理】固定 `x u ε a` 后，`θ ↦ s x u ε θ a` 是一个函数。**

**这是 T-1b 的出发点**：`Step` 把 `θ` 当作 `Θ.Carrier` 的**一个点**消费，
而非可作用于 `X` 的算子。

**⚠ 这条定理极弱**（`⟨_, fun _ => rfl⟩`），但它是库里
**第一个陈述里出现 `Step` 的定理**。 -/
theorem step_theta_fixed_by_signature (s : Step F) (x : F.X.Carrier)
    (u : F.U.Carrier) (ε : F.Ν.Carrier) (a : F.Act.Carrier) :
    ∃ g : F.Θ.Carrier → F.X.Carrier, ∀ θ, s x u ε θ a = g θ :=
  ⟨fun θ => s x u ε θ a, fun _ => rfl⟩

/-- ⭐ **`Step` 的 θ 参数位是**最后一个单点**，不是函数空间元素。**

若 `θ` 要是函数（如策略 `X → Act`），必须 `F.Θ.Carrier` 本身是函数空间。 -/
theorem step_theta_is_point (s : Step F) (x : F.X.Carrier) (u : F.U.Carrier)
    (ε : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    s x u ε θ a = (fun θ' => s x u ε θ' a) θ :=
  rfl

/-! ### §2 ⭐ `Θ.Carrier` 是任意类型：签名**允许** θ 是算子

**⟹ T-1b 的真实内容是：**签名允许 θ 取函数空间，但**没有任何实例真的这样做**。**

**证据**：`grep "Carrier := .*→" Fate/*.lean` 零命中
（即没有 `Θ.Carrier := X → X` 之类的实例）。 -/

/-- ⭐ **签名不禁止 `Θ.Carrier` 是函数空间**：存在 `ThetaSpace` 使
`Carrier = (F.X.Carrier → F.X.Carrier)`。

这是 §2 的形式化（**不构造完整 Frame**，只证 `ThetaSpace` 部分）。 -/
abbrev FunTheta (F : Frame) : ThetaSpace where
  Carrier := F.X.Carrier → F.X.Carrier
  topo := ⊥
  meas := ⊥

/-- ⭐ **`FunTheta` 的载体确实是函数空间**（`rfl`）。 -/
theorem funTheta_carrier (F : Frame) :
    (FunTheta F).Carrier = (F.X.Carrier → F.X.Carrier) :=
  rfl

end StepExpressiveness

end FateV2.Predict
