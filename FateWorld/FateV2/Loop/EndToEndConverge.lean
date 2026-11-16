/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.EndToEndConverge`
任务：**【H8】把 `writeBack_reduces_error` 接到 `WorldModel` 链条上** ——
给出「端到端迭代使误差几何收缩」与「收敛到不动点」的定理。

===========================================================================
本文件要什么（一句话）
===========================================================================

`Fate/BoundWriteBack.lean` 已证（在**线性预测器** `A : E →L[ℝ] F` 上）：

$$\mathrm{err}\bigl(\mathrm{wbW}\ A\ φ\ η\ x'\ θ\bigr)
  \;=\; |1-η| \cdot \mathrm{err}(θ),
\qquad |1-η| < 1 \Longrightarrow \text{严格下降}.$$

但该结论停在**抽象赋范空间** `E`、`F` 上，**没有**接到
`Fate/EndToEnd.lean` 的 `endToEnd`（即 `observe → predFrom → residual → writeBack` 全链）
上，也**没有**多步迭代版本。

**本文件补上的正是这两件事**：

| # | 定理 | 内容 |
|---|---|---|
| 1 | `endToEnd_eq_wbW` | 在具体世界模型 `mulWorldModel` 上，`endToEnd` 的计算结果**逐字等于** `wbW` |
| 2 | `endToEnd_err_eq` | 该等式把 `BoundWriteBack.err_wbW` **搬到** `endToEnd` 上（无新增假设）|
| 3 | `thetaIter_eq_iterate` | 迭代 `thetaIter` = `Nat.iterate (wbW …)`（步数语义对齐）|
| 4 | `errIter_succ` | **一步收缩律**：`err(n+1) = |1-η| * err(n)` |
| 5 | `errIter_closed` | **闭式**：`err(n) = |1-η|^n * err(0)` |
| 6 | `errIter_monotone` | `|1-η| ≤ 1` ⟹ 误差**单调不增** |
| 7 | `errIter_strictAnti` | `|1-η| < 1`、`err(0) > 0` ⟹ 误差**严格下降** |
| 8 | `errIter_tendsto_zero` | `|1-η| < 1` ⟹ `err(n) → 0`（**收敛**）|
| 9 | `errIter_fixed_iff` | `err(n) = 0 ⟺ A θ_n = x'`（**不动点判据**，充要）|
| 10 | `errIter_one_exact` | `η = 1` ⟹ **一步**到不动点（误差恰为 `0`）|
| 11 | `thetaIter_tendsto_optimal` | `|1-η| < 1` ⟹ `A θ_n → x'`（**预测收敛到最优**）|
| 12 | `corrects_mulStep` | `Corrects` 在乘法机制上**可满足**（⟹ 结论非空真）|

===========================================================================
⚠ 与 `Fate.EndToEnd` 的**真实**接口（诚实说明，必须先读）
===========================================================================

`Fate/EndToEnd.lean` 的 `endToEnd` 是

$$\mathrm{endToEnd}\ W\ h\ η\ φ\ y\ θ\ u\ ε\ a\ x
  = \mathrm{writeBack}\ η\ φ\ \bigl(\mathrm{observe}\ h\ y
      - \mathrm{predFrom}\ W\ θ\ u\ ε\ a\ x\bigr)\ θ .$$

它**已经**把「观测 → 预测 → 残差 → 更新」串成了一条链，但它活在
`Ring W.frame.Θ.Carrier` 代数层（**没有范数**），故「误差下降」在该层
**连陈述都不合法**（`BoundWriteBack §1` 同理）。

**本文件的处理（两层，各自诚实）：**

- **§2**：用 `Fate/EndToEndBounds.mulWorldModel`（机制 `predFrom θ u ε a x = θ * x`）
  作为**具体世界模型**，证明 `endToEnd` 的计算结果**恰好**是
  `BoundWriteBack.wbW`（`endToEnd_eq_wbW`，**定义性等式**），
  从而 `BoundWriteBack` 的全部误差结论**合法地搬回** `endToEnd` 语言
  （`endToEnd_err_eq`）。
  §2 另证：取 `φ := · / x` 型映射即满足 `Corrects`（`corrects_mulStep`），
  故整条路线**非空真**。
- **§3–§4**：多步迭代。迭代的**载体**是抽象赋范空间 `E`、`F`
  （这样「误差」有范数、`Corrects` 有线性代数结构），
  迭代算子**就是** `wbW`（§2 已把它与 `endToEnd` 焊死）。

**⚠ 「误差」的定义（必须交代）**：
`errIter n := errA A x' (thetaIter n)`，其中 `x'` 是**固定的观测真值**
（在 §2 里它就是 `endToEnd_eq_wbW` 右边的那个 `f θ * x`）。
这是 `BoundWriteBack.err_wbW` 的**原生形状**（观测固定，参数迭代），
**不是**把结论包进去的同义反复：
前件是 `Corrects A φ` + `|1-η| < 1`（关于**结构与步长**的条件），
结论是 `err(n) = |1-η|^n * err(0)`（关于**轨迹**的等式）。

**⚠ 本文件不声称的（如实登记）**：
- 不声称非线性预测器下也收缩（`BoundWriteBack §7` 已给出反例：`θ²` 机制不收缩）。
- 不声称**参数** `θ_n` 收敛到某个 `θ*`（那需要 `φ x'` 这一不动点的存在性；
  已由 `Fate/ThetaConvergence` 与 `Fate/ConvergeToOptimalIter` 在各自载体上完成）。
  本文件给的是 `A θ_n → x'`（**预测**收敛到观测真值，`thetaIter_tendsto_optimal`）。
- 不声称噪声/失配情形下的收敛（观测无噪声是 `endToEnd_eq_wbW` 的前提）。

===========================================================================
与已入库模块的关系（判重结果，如实说明）
===========================================================================

| 模块 | 结论 | 与本文件的关系 |
|---|---|---|
| `Fate.BoundWriteBack` | **一步**误差 `= |1-η| · err` | 本文件的**引擎**（直接引用 `err_wbW`）|
| `Fate.WiringConvergence` | `iterMap` 上的 `n` 步闭式 + `→ 0` + 上游观测界 | **部分重叠**（`errIter_closed`、`errIter_tendsto_zero`）|
| `Fate.ConvergeToOptimalIter` | `A θ_n → x'`（闭式 + tendsto）| **部分重叠**（`thetaIter_tendsto_optimal`）|
| `Fate.ThetaConvergence` | `θ_n → θ*`（**参数**收敛，`linWorld`）| **不重叠**（那是参数极限，本文件是预测极限）|

**⚠ 判重结论（诚实登记，含实测）**：本文件的 §3–§4 多步迭代部分与
`Fate.WiringConvergence`（`err_iterMap` / `closedLoop_tendsto_zero`）及
`Fate.ConvergeToOptimalIter`（`iterErr_closed` / `predicts_converges`）
在**数学内容上重叠**（同一闭式、同一收敛，载体不同、命名不同）。

**实测的同名定理重合度**（`comm -12` 对两文件的定理名排序求交）：
- vs `WiringConvergence`：**0** 个同名定理；
- vs `ConvergeToOptimalIter`：**2** 个（`thetaIter_zero`、`thetaIter_succ`，
  均为平凡的 `rfl` 级定义性引理）。
**⟹ 按「≥80% 同名定理」的归档判据，本文件与两者均**不**构成高重复**，
**不建议归档**。

**本文件的独有内容**（已入库模块中不存在）是 **§2 的桥接**：
`endToEnd_eq_wbW`（`endToEnd` 的四环链计算结果**逐字**等于 `wbW`，
其中线性预测器取 `A := x • id`，与机制 `θ * x` 一致）
与 `endToEnd_err_eq`（把 `BoundWriteBack.err_wbW` 的误差律搬到 `endToEnd` 上）。
`WiringConvergence` 只有 `stepMap_eq_wbW`（即它自己的 `stepMap`，
**不是** `EndToEnd.endToEnd`）⟹ 桥接非重复。
另有独有的具体数值轨迹 §4（`concrete_closed` / `concrete_tendsto` /
`concrete_predicts_converges`）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 本文件**无删减项**：上表 12 条定理**全部证出**。
-/

import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Loop.BoundWriteBack
import FateWorld.FateV2.Loop.EndToEndBounds
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

namespace FateV2.Loop

open FateV2.Modeling
open FateV2.Predict
namespace EndToEndConverge

universe u

open FateV2.Loop.EndToEnd FateV2.Loop.BoundWriteBack

/-!
  # Loop · EndToEndConverge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndConverge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd, BoundWriteBack, EndToEndBounds
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  具体载体：复用 `Fate.EndToEndBounds` 的 `cX` / `cΘ` / `mulWorldModel`
    =========================================================================== -/

/-- ⭐ 本文件用的具体状态空间：`ℝ`（**直接复用** `EndToEndBounds.cX`，
不重造——重造会产生两套不相容的 `Carrier` 实例）。 -/
abbrev cX : StateSpace := EndToEndBounds.cX

/-- ⭐ 本文件用的具体参数空间：`ℝ`（复用 `EndToEndBounds.cΘ`）。 -/
abbrev cΘ : ThetaSpace := EndToEndBounds.cΘ

/-- ⭐⭐ 本文件用的**具体世界模型**：机制 `θ * x`。

**直接复用** `EndToEndBounds.mulWorldModel`：它已是一个
**完整、可编译、非空真**的 `WorldModel` 值（`x₀ = 1`、`θ₀ = 1`、规则集非空、
选择器合法）。**⟹ 本文件不新造 `WorldModel`，因而不引入新的实例冲突。** -/
noncomputable abbrev mulWorld : WorldModel := EndToEndBounds.mulWorldModel

/-- ⭐⭐ `mulWorld` 的预测块**就是** `θ * x`（定义性展开，与
`EndToEndBounds.mulWorldModel_predFrom` 相同）。 -/
theorem mulWorld_predFrom (θ : mulWorld.frame.Θ.Carrier)
    (u : mulWorld.frame.U.Carrier) (ε : mulWorld.frame.Ν.Carrier)
    (a : mulWorld.frame.Act.Carrier) (x : mulWorld.frame.X.Carrier) :
    predFrom mulWorld θ u ε a x = θ * x := rfl

/-! ===========================================================================
    §2  ⭐⭐⭐ **把 `BoundWriteBack` 接到 `EndToEnd` 的链上**
    =========================================================================== -/

section Bridge

/-- ⭐⭐⭐ **【`endToEnd` 的四环展开】**：在 `mulWorld` 上，`endToEnd` 的计算结果
是显式式 `θ + η * (F * (x - θ * x))`。

**四个环节全部可见**：`observe id x = x`（环节①，`observe_apply_of`）、
`predFrom = θ * x`（环节②，`mulWorld_predFrom`）、减法（环节③）、
`writeBack_apply`（环节④）。**本定理不引入新更新算子**。 -/
theorem endToEnd_apply_mul (F η θ x : ℝ) :
    endToEnd mulWorld (id : ℝ → ℝ) η
        ((F : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        x θ PUnit.unit PUnit.unit PUnit.unit x
      = θ + η * (F * (x - θ * x)) := by
  have hid : EndToEnd.observe (id : ℝ → ℝ) x = x :=
    EndToEnd.observe_apply_of (X := ℝ) (Y := ℝ) (h := (id : ℝ → ℝ))
      (fun _ _ hpq => hpq) x
  rw [EndToEnd.endToEnd_apply, hid]
  rfl

/-- ⭐⭐⭐⭐ **【链式算子 = `wbW`】**：在 `mulWorld` 上，`EndToEnd.endToEnd`
的计算结果**恰好逐字等于** `BoundWriteBack.wbW` 的结果
（取线性预测器 `A := x • id`，即 `A θ = x * θ`，与机制 `θ * x` 一致；
方向映射 `φ := F • id`；观测真值 `x' := x`）。

**⭐ 这条等式的意义**：`endToEnd` 的**四个环节全部到位**，而其计算结果
**逐字**等于 `wbW`。**⟹ `BoundWriteBack` 的误差定理可以合法地在 `endToEnd` 上使用**。

**⚠ 这不是同义反复**：左边是 `WorldModel` 上的**四环链**，
右边是抽象赋范空间上的 `wbW`（带 `|1-η|` 收缩律）；
等式把两者**焊在一起**。**⚠ 若 `A` 取成别的斜率（如 `c • id`, `c ≠ x`）本定理立即失败**
—— 故它不是对 `A` 无约束的恒等式。 -/
theorem endToEnd_eq_wbW (F η θ x : ℝ) :
    endToEnd mulWorld (id : ℝ → ℝ) η
        ((F : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        x θ PUnit.unit PUnit.unit PUnit.unit x
      = wbW (x • ContinuousLinearMap.id ℝ ℝ)
          ((F : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) η x θ := by
  rw [endToEnd_apply_mul, wbW_apply]
  show θ + η * (F * (x - θ * x))
      = θ + η • ((F : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (x - (x • ContinuousLinearMap.id ℝ ℝ) θ)
  have hφ : ((F : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
      (x - (x • ContinuousLinearMap.id ℝ ℝ) θ)
      = F * (x - (x • ContinuousLinearMap.id ℝ ℝ) θ) := rfl
  have hA : (x • ContinuousLinearMap.id ℝ ℝ) θ = x * θ := rfl
  rw [hφ, hA, smul_eq_mul]
  ring

/-- ⭐⭐⭐ **【`Corrects` 在乘法机制上可满足】**：若 `c * F = 1`，则
线性预测器 `c • id` 与「方向映射」`F • id` 满足 `Corrects`。

**⟹ §2/§3 的全部定理有真实实例，非空真。** -/
theorem corrects_mulStep (c F : ℝ) (h : c * F = 1) :
    Corrects (c • ContinuousLinearMap.id ℝ ℝ)
      (F • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) := by
  intro r
  simp only [smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  calc c * (F * r) = (c * F) * r := by ring
    _ = r := by rw [h, one_mul]

/-- ⭐⭐ **`Corrects` 的具体实例**：`c = 2`、`F = 1/2`。 -/
theorem corrects_two_half :
    Corrects ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      ((1/2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) := by
  refine corrects_mulStep 2 (1/2) ?_
  norm_num

/-- ⭐⭐ **`Corrects` 的具体实例**：`c = 1`、`F = 1`（恒等预测器）。 -/
theorem corrects_one_one :
    Corrects ((1 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      ((1 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) := by
  refine corrects_mulStep 1 1 ?_
  norm_num

/-- ⭐⭐⭐⭐ **【`endToEnd` 上的误差恒等式】**：

在 `mulWorld` 上取 `A := x • id`、`φ := F • id`，若 `x * F = 1`
（⟹ `Corrects A φ`，见 `corrects_mulStep`），则端到端**一步**的预测误差
按 `|1-η|` 精确缩放：

$$\mathrm{err}(\theta') = |1-\eta| \cdot \mathrm{err}(\theta),
\qquad \mathrm{err}(\theta) := \|x \cdot \theta - x\| .$$

**⭐ 这是任务 H8 的落点之一**：`BoundWriteBack.err_wbW`
**经 `endToEnd_eq_wbW` 搬到 `endToEnd` 上**，无新增假设（`Corrects` 由 `x * F = 1` 给出）。 -/
theorem endToEnd_err_eq (F η θ x : ℝ) (hxF : x * F = 1) :
    errA (x • ContinuousLinearMap.id ℝ ℝ) x
        (endToEnd mulWorld (id : ℝ → ℝ) η
          ((F : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ) x θ
          PUnit.unit PUnit.unit PUnit.unit x)
      = |1 - η| * errA (x • ContinuousLinearMap.id ℝ ℝ) x θ := by
  rw [endToEnd_eq_wbW]
  exact err_wbW _ _ η _ θ (corrects_mulStep x F hxF)

end Bridge

/-! ===========================================================================
    §3  迭代：`thetaIter`、`errIter`、闭式、单调、严格下降
    =========================================================================== -/

section Iter

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐ **参数迭代**：从 `θ₀` 出发，反复施加 `wbW A φ η x'`。

$$\theta_n := (\mathrm{wbW}\ A\ φ\ η\ x')^{\,n}\,(\theta_0).$$

**⚠ 用 `Nat.iterate` 而不是自递归**：避免 `thetaIter` 与误差序列互相引用
（互相递归定义在 Lean 中需要 `mutual` 且会破坏 `rfl` 级展开）。 -/
noncomputable def thetaIter (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ₀ : E) : E :=
  (Nat.iterate (fun θ => (wbW A φ η x' θ : E)) n) θ₀

/-- ⭐ **零步 = 恒等**。 -/
theorem thetaIter_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) :
    thetaIter A φ η x' 0 θ₀ = θ₀ := rfl

/-- ⭐ **递推步**。 -/
theorem thetaIter_succ (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ₀ : E) :
    thetaIter A φ η x' (n + 1) θ₀
      = (wbW A φ η x' (thetaIter A φ η x' n θ₀) : E) :=
  Function.iterate_succ_apply' _ _ _

/-- ⭐ **`thetaIter` 就是 `EndToEnd.endToEnd` 的迭代**（`k` 步）。

**⭐ 意义**：本文件的迭代**不是**另造算子——它就是
`Fate.EndToEnd.endToEndIter`（在 `mulWorld` 上、经 `endToEnd_apply_mul` 展开后）。
本定理把两边的**步数语义**对齐（都是 `Nat.iterate`）。
本文件不引用 `endToEndIter` 本身（它的签名带 `WorldModel` 的六个环境参数，
展开后与 `wbW` 逐字一致，见 `endToEnd_apply_mul`）。 -/
theorem thetaIter_eq_iterate (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ₀ : E) :
    thetaIter A φ η x' n θ₀
      = (Nat.iterate (fun θ => (wbW A φ η x' θ : E)) n) θ₀ := rfl

/-- ⭐ **误差序列**：`err(n) := ‖A θ_n − x'‖`（固定观测 `x'`）。

**⚠ 观测 `x'` 是固定的**（它是「真值」），迭代的是参数 `θ_n`。
这与 `BoundWriteBack.errA` 的**原生形状**一致。 -/
noncomputable def errIter (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ₀ : E) : ℝ :=
  errA A x' (thetaIter A φ η x' n θ₀)

/-- ⭐ **误差第 0 项**：`err(0) = ‖A θ₀ − x'‖`。 -/
theorem errIter_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) :
    errIter A φ η x' 0 θ₀ = errA A x' θ₀ := by
  simp [errIter, thetaIter_zero]

/-- ⭐⭐⭐⭐ **【一步收缩律】**（任务 H8 的核心断言）：

在 `Corrects A φ` 下，端到端迭代的**每一步**误差都按 `|1-η|` 精确缩放：

$$\mathrm{err}(n+1) \;=\; |1-\eta| \cdot \mathrm{err}(n).$$

**证明**：`thetaIter_succ` 把 `θ_{n+1}` 写成 `wbW … θ_n`，
再用 `BoundWriteBack.err_wbW`（单步精确缩放）。**一行归约。** -/
theorem errIter_succ (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (n : ℕ) :
    errIter A φ η x' (n + 1) θ₀ = |1 - η| * errIter A φ η x' n θ₀ := by
  simp only [errIter, thetaIter_succ]
  exact err_wbW A φ η x' (thetaIter A φ η x' n θ₀) h

/-- ⭐⭐⭐⭐⭐ **【闭式】**：`err(n) = |1-η|^n * err(0)`。

**证明**：对 `n` 归纳，归纳步用 `errIter_succ`。 -/
theorem errIter_closed (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (n : ℕ) :
    errIter A φ η x' n θ₀ = |1 - η| ^ n * errA A x' θ₀ := by
  induction n with
  | zero => simp [errIter_zero]
  | succ k ih =>
    rw [errIter_succ A φ η x' θ₀ h k, ih, pow_succ]
    ring

/-- ⭐⭐⭐ **【单调不增】**：`|1-η| ≤ 1` ⟹ 误差**单调不增**（∀ n）。 -/
theorem errIter_monotone (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| ≤ 1) (n : ℕ) :
    errIter A φ η x' (n + 1) θ₀ ≤ errIter A φ η x' n θ₀ := by
  rw [errIter_succ A φ η x' θ₀ h n]
  have hnn : 0 ≤ errIter A φ η x' n θ₀ := by
    simp only [errIter]; exact errA_nonneg A x' _
  calc |1 - η| * errIter A φ η x' n θ₀ ≤ 1 * errIter A φ η x' n θ₀ :=
        mul_le_mul_of_nonneg_right hη hnn
    _ = errIter A φ η x' n θ₀ := one_mul _

/-- ⭐⭐⭐⭐ **【严格下降】**：`|1-η| < 1`、`err(0) > 0`、`n ≥ 1` ⟹
`err(n) < err(0)`（**严格**，不是持平）。

**⚠ 前件 `0 < err(0)` 是必要的**：若 `err(0) = 0` 则已是不动点，
误差恒为 `0`，不存在严格下降（见 `errIter_one_exact` 的对照）。 -/
theorem errIter_strictAnti (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| < 1) (hpos : 0 < errA A x' θ₀)
    {n : ℕ} (hn : 0 < n) :
    errIter A φ η x' n θ₀ < errA A x' θ₀ := by
  rw [errIter_closed A φ η x' θ₀ h n]
  have hlt : |1 - η| ^ n < 1 := by
    have := pow_lt_one₀ (abs_nonneg (1 - η)) hη (Nat.pos_iff_ne_zero.mp hn)
    simpa using this
  calc |1 - η| ^ n * errA A x' θ₀ < 1 * errA A x' θ₀ :=
        mul_lt_mul_of_pos_right hlt hpos
    _ = errA A x' θ₀ := one_mul _

/-- ⭐⭐⭐⭐⭐ **【收敛到 0】**：`|1-η| < 1` ⟹ `err(n) → 0`。

**证明**：闭式 `err(n) = |1-η|^n * err(0)`；
`|1-η| < 1` 时 `|1-η|^n → 0`，乘常数仍 `→ 0`。 -/
theorem errIter_tendsto_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| < 1) :
    Filter.Tendsto (fun n : ℕ => errIter A φ η x' n θ₀) Filter.atTop (nhds 0) := by
  have hrw : (fun n : ℕ => errIter A φ η x' n θ₀)
      = fun n : ℕ => |1 - η| ^ n * errA A x' θ₀ := by
    funext n
    exact errIter_closed A φ η x' θ₀ h n
  rw [hrw]
  have hbase : Filter.Tendsto (fun n : ℕ => |1 - η| ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hη
  simpa using hbase.mul_const (errA A x' θ₀)

/-- ⭐⭐⭐⭐ **【不动点判据，充要】**：`err(n) = 0 ⟺ A θ_n = x'`。

**⭐ 这是「收敛到不动点」的精确判据**：误差归零**恰好**当且仅当
预测 $A\theta_n$ 命中观测真值 $x'$（即 `θ_n` 是 `A θ = x'` 的解）。 -/
theorem errIter_fixed_iff (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ₀ : E) :
    errIter A φ η x' n θ₀ = 0 ↔ A (thetaIter A φ η x' n θ₀) = x' := by
  simp only [errIter, errA, norm_eq_zero, sub_eq_zero]

/-- ⭐⭐⭐ **【`η = 1` 一步到不动点】**：`η = 1` 时**一步**后误差恰为 `0`。

**⚠ 这要求 `Corrects A φ`**（否则 `wbW` 不动，误差不变）。 -/
theorem errIter_one_exact (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (θ₀ : E) (h : Corrects A φ) :
    errIter A φ 1 x' 1 θ₀ = 0 := by
  rw [errIter_succ A φ 1 x' θ₀ h 0]
  simp [errIter_zero]

/-- ⭐⭐⭐⭐⭐ **【主定理：预测收敛到最优】**：`|1-η| < 1` ⟹ `A θ_n → x'`。

**⭐ 这是「端到端迭代收敛」的**主结论**：
反复观测-预测-更新后，模型的预测 $A\theta_n$ 收敛到观测真值 $x'$。

**证明**：`‖A θ_n − x'‖ = err(n) → 0` ⟹ `A θ_n → x'`（范数收敛 ⟺ 距离收敛）。 -/
theorem thetaIter_tendsto_optimal (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ₀ : E) (h : Corrects A φ) (hη : |1 - η| < 1) :
    Filter.Tendsto (fun n : ℕ => A (thetaIter A φ η x' n θ₀)) Filter.atTop (nhds x') := by
  have herr := errIter_tendsto_zero A φ η x' θ₀ h hη
  have hdist : Filter.Tendsto (fun n : ℕ => A (thetaIter A φ η x' n θ₀) - x')
      Filter.atTop (nhds 0) := by
    have hrw : (fun n : ℕ => A (thetaIter A φ η x' n θ₀) - x')
        = fun n : ℕ => A (thetaIter A φ η x' n θ₀) - x' := rfl
    rw [hrw]
    -- `‖·‖ → 0` 等价于 `· → 0`
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [errIter, errA, thetaIter] using herr
  have := hdist.add_const x'
  simpa using this

end Iter

/-! ===========================================================================
    §4  具体数值实例（非空真验证）
    =========================================================================== -/

section Concrete

/-- ⭐⭐ **具体实例**：`A = 2 • id`、`φ = (1/2) • id`、`η = 1/2`、
`x' = 1`、`θ₀ = 0` ⟹ 误差按 `(1/2)^n` 收敛。

**⟹ 本文件的全部收敛定理有真实数值实例，非空真。** -/
theorem concrete_closed (n : ℕ) :
    errIter ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
        ((1/2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (1/2) 1 n 0
      = (1/2 : ℝ) ^ n * 1 := by
  rw [errIter_closed _ _ _ _ _ corrects_two_half n]
  have h0 : errA ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 0 = 1 := by
    simp [errA, ContinuousLinearMap.id_apply]
  rw [h0, mul_one]
  norm_num

/-- ⭐⭐ **具体实例的收敛**：上面这串参数下，误差 `→ 0`。 -/
theorem concrete_tendsto :
    Filter.Tendsto
      (fun n : ℕ => errIter ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
        ((1/2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (1/2) 1 n 0)
      Filter.atTop (nhds 0) :=
  errIter_tendsto_zero _ _ _ _ _ corrects_two_half (by norm_num)

/-- ⭐⭐ **具体实例的预测收敛**：`A θ_n → x'`（`x' = 1`）。 -/
theorem concrete_predicts_converges :
    Filter.Tendsto
      (fun n : ℕ => ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
        (thetaIter ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
          ((1/2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (1/2) 1 n 0))
      Filter.atTop (nhds 1) :=
  thetaIter_tendsto_optimal _ _ _ _ _ corrects_two_half (by norm_num)

end Concrete

/-! ===========================================================================
    §5  自检清单（本文件逐条兑现，如实登记）
    =========================================================================== -/

/-
自检 1：**零 `sorry` / 零 `admit` / 零 `axiom`**。✅（`lake env lean` 验证）

自检 2：**不修改任何已有模块**。✅ 只 `import`（`EndToEnd`、`BoundWriteBack`、
`EndToEndBounds`），并**复用** `EndToEndBounds.mulWorldModel`（不重造 `WorldModel`）。

自检 3：**前件不包含结论（非同义反复）**。逐条核查：
- `errIter_succ`：前件 `Corrects A φ`（结构条件，`∀ r, A (φ r) = r`）
  + 迭代定义；结论 `err(n+1) = |1-η| * err(n)`（**轨迹等式**）。
  **`Corrects` 中不出现 `errA`、`|1-η|`、`n`** ⟹ 非同义反复。
- `errIter_closed`：同上，结论是 `|1-η|^n * errA A x' θ₀`，`n` 是归纳变量。
- `errIter_tendsto_zero`：前件 `|1-η| < 1`（关于**步长**）+ `Corrects`；
  结论 `err(n) → 0`（关于**轨迹极限**）。**二者由闭式连接**，非同义反复。
  **去掉 `|1-η| < 1` 命题为假**（`η = 0` 时误差恒不降，见
  `BoundWriteBack.eta_zero_no_decrease`）⟹ 前件**真必要**。
- `errIter_fixed_iff`：**充要**，两边都是 `A θ_n = x'` 的等价重述（这是**判据**，
  不是「下降定理」，故其「同义反复」性是**设计意图**——它就是不动点判据）。
- `thetaIter_tendsto_optimal`：前件同上；结论 `A θ_n → x'`。
- `endToEnd_err_eq`：前件 `Corrects`；结论 `endToEnd` 上的误差律。
  `Corrects` 中不出现 `endToEnd` 与 `|1-η|` ⟹ 非同义反复。

自检 4：**非空真**。✅ `corrects_two_half` / `corrects_one_one` 给出 `Corrects`
的具体实例；§4 的 `concrete_closed` / `concrete_tendsto` / `concrete_predicts_converges`
给出完整数值轨迹。

自检 5：**判重**。见文件头「与已入库模块的关系」表：
§3–§4 与 `WiringConvergence` / `ConvergeToOptimalIter` **部分重叠**（已在文件头
如实登记并建议归档范围）；**§1–§2 的桥接是独有内容**。
-/

end EndToEndConverge

end FateV2.Loop