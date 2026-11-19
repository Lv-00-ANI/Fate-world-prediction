/-
命运理论 · 真正的 `#eval` 数值预测（端到端 θ' 更新）
======================================================

模块：`EvalReal`（先写在 `Fate/` 验证，再复制到 staging）

上游：`Fate.WorldModel`（`WorldModel` 四部分）、`Fate.WorldModelMinimal`
　　　（任务1 的实例：`minimalWorldModel` / `zWorldModel`）、
　　　`EndToEnd`（`observe` / `predFrom` / `e2eResidual` / `endToEnd`）、
　　　`ResidualLoop`（`residual` / `writeBack`）。

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
在**任务1造的 WorldModel 实例**上，用 `#eval` **真正算一次端到端**：
给状态 `x` 与观测 `y`，算出更新后的参数 `θ'`；
并**证明** `#eval` 打印的数值与理论算的**完全一致**；
至少给 **3 个不同输入**的数值结果。

---------------------------------------------------------------------------
诚实标注（必读，不得含糊）
---------------------------------------------------------------------------
**H1. 为什么可以 `#eval`：链上唯一的非可算点是 `observe`。**

| 环节 | 定义 | 可计算？ |
|---|---|---|
| ① 观测 → 估计 | `EndToEnd.observe h` = `RA14Strong.chooseEstimator h` | ❌ `Classical.choose`，**非可算** |
| ② 估计 → 预测 | `EndToEnd.predFrom W` = `W.f` | ✅ `W.simulator.step` 构造性 |
| ③ 残差 | `x̂_obs - x̂_pred` | ✅ `ℤ` 上减法 |
| ④ 更新 | `ResidualLoop.writeBack` = `θ + η * φ r` | ✅ `ℤ` 上运算 |

本文件的处置**不是**「换掉 `observe`」，而是：
- 取**单射**的观测映射 `h`（`h = id : ℤ → ℤ`），于是 `observe h` 的值**被定理钉死**：
  `observe h (h x) = x`（`EndToEnd.observe_apply_of`），且**在像上无歧义**；
- 数值上把「① 的输出」作为**已算好的输入数** `xobs`（= `observe h y` 在像上的值）喂进去，
  再用**定理**（`evalObserve_eq`）证明它与 `observe h y` **逐位相等**。

**⟹ 因此 `#eval` 算的是「②③④ 的数值 + ① 的取值被定理钉死」，
这是本仓库当前可算性的**上界**，本文件**不**声称 `chooseEstimator` 可算。**

**H2. `ℤ` 实例（`zWorldModel`）上投影路径的类型类缺口。**

`zWorldModel.frame.X.Carrier` 是结构投影，Lean 的类型类搜索**不展开**它，
故 `zWorldModel` 上直接写 `(0 : zWorldModel.frame.Θ.Carrier)` 会失败
（实测：`failed to synthesize OfNat zWorldModel.frame.Θ.Carrier 0` /
`HAdd zWorldModel.frame.X.Carrier ℕ …`）。
`WorldModelMinimal` 已注册 `Ring`/`AddCommGroup`，但**未注册** `OfNat`/`HAdd`/`HMul`
（那是 `ℤ` 的**实例**，不是 `Ring` 的字段）。

本文件的处置：**再建一个与任务1实例同构的实例 `eX`（状态 `ℤ`）**，
其 `Step` 取 `x ↦ x + 1`（与任务1的 `zStep` **同一个机制**），
并在**具体常量**上注册全套数值实例，
使 `#eval` 可以直接在这个实例上跑。

⚠ 这是**加法式**的：任务1的 `minimalWorldModel` / `zWorldModel` **一字未改**。

**H3. 本文件不声称任何经验结论。** 数值是形式化对象的值，不是对世界的预测。

---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`
---------------------------------------------------------------------------
所有 `#eval` 是计算指令；所有定理皆已证（`rfl` / `decide` / 已证引理）。
-/

import FateWorld.FateV2.Loop.EndToEnd
namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace EvalReal

/-!
  # Loop · EvalReal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EvalReal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  可 `#eval` 的端到端实例（与任务1的 `zWorldModel` 同构，机制同为 `x ↦ x+1`）
    =========================================================================== -/

/-- 端到端实例的状态空间：`ℤ`（离散拓扑 / 离散可测）。 -/
def eX : StateSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 端到端实例的参数空间：`ℤ`。 -/
def eΘ : ThetaSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤

/-- 外生输入空间：单点。 -/
def eU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 动作空间：单点。 -/
def eAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 噪声空间：单点。 -/
def eN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 上下文空间：单点。 -/
def eC : CtxSpace where
  Carrier := PUnit

/-- 端到端框架。 -/
def eFrame : Frame where
  Θ := eΘ
  X := eX
  U := eU
  Act := eAct
  Ν := eN

/-! **类型类注册（前置）**：`StateSpace.meas` / `ThetaSpace.meas` 等是**字段**，
而 `eX.Carrier` 是投影，故须显式提到实例搜索位置（与 `WorldModelMinimal` §1 同法）。 -/
attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo ThetaSpace.meas
  InputSpace.topo InputSpace.meas ActionSpace.topo ActionSpace.meas NoiseSpace.meas
/-! **空间层实例注册（前置）**：`StateSpace.meas` 等是**字段**，`eX.Carrier` 是投影，
须显式提到实例搜索位置（与 `WorldModelMinimal` §1 同法）。这些全是对 `ℤ` 既有实例的搬运，
**不是**新增数学假设。 -/
instance instExMeas : MeasurableSpace eX.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instExAddCommGroup : AddCommGroup eX.Carrier := inferInstanceAs (AddCommGroup ℤ)
instance instExRing : Ring eX.Carrier := inferInstanceAs (Ring ℤ)
instance instExNonempty : Nonempty eX.Carrier := ⟨0⟩
instance instExOfNat : OfNat eX.Carrier n := inferInstanceAs (OfNat ℤ n)
instance instExOfNat0 : OfNat eX.Carrier 0 := inferInstanceAs (OfNat ℤ 0)
instance instExOfNat1 : OfNat eX.Carrier 1 := inferInstanceAs (OfNat ℤ 1)
instance instExNeg : Neg eX.Carrier := inferInstanceAs (Neg ℤ)

instance instEThetaMeas : MeasurableSpace eΘ.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instEThetaRing : Ring eΘ.Carrier := inferInstanceAs (Ring ℤ)
instance instEThetaAddCommGroup : AddCommGroup eΘ.Carrier := inferInstanceAs (AddCommGroup ℤ)
instance instEThetaOfNat : OfNat eΘ.Carrier n := inferInstanceAs (OfNat ℤ n)
instance instEThetaOfNat0 : OfNat eΘ.Carrier 0 := inferInstanceAs (OfNat ℤ 0)


/-! **框架层实例注册**：`eFrame.X.Carrier` / `eFrame.Θ.Carrier` 是 `Frame` 的投影，
同理须显式注册。 -/
instance instEfXMeas : MeasurableSpace eFrame.X.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instEfXAddCommGroup : AddCommGroup eFrame.X.Carrier := inferInstanceAs (AddCommGroup ℤ)
instance instEfXRing : Ring eFrame.X.Carrier := inferInstanceAs (Ring ℤ)
instance instEfXNonempty : Nonempty eFrame.X.Carrier := ⟨0⟩
instance instEfXHAddNat : HAdd eFrame.X.Carrier ℕ eFrame.X.Carrier :=
  ⟨fun a b => a + (b : eFrame.X.Carrier)⟩
instance instEfThetaMeas : MeasurableSpace eFrame.Θ.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instEfThetaRing : Ring eFrame.Θ.Carrier := inferInstanceAs (Ring ℤ)
instance instEfThetaAddCommGroup : AddCommGroup eFrame.Θ.Carrier :=
  inferInstanceAs (AddCommGroup ℤ)

/-- 机制 `f`：`x ↦ x + 1`（**与任务1 `zStep` 同一个机制**）。 -/
def eStep : Step eFrame := fun x _u _ε _θ _a => x + 1

/-- 规则：点质量 `δ_x`。 -/
noncomputable def eRule : Rule eC eX eX where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 规则集 `{R}`（1 条，非空）。 -/
noncomputable def eRules : Rules eC eX eX := {eRule}

/-- 规则集非空。 -/
theorem eRules_nonempty : eRules.Nonempty := ⟨eRule, Set.mem_singleton eRule⟩

/-- 规则集块。 -/
noncomputable def eWorldRules : WorldRules eC eX eX where
  rules := eRules
  nonempty := eRules_nonempty

/-- 模拟器块（窗口 2 步）。 -/
def eSimulator : WorldSimulator eFrame where
  step := eStep
  horizon := 2

/-- 选择器：恒定返回 `eRule`，评值 `0`。 -/
noncomputable def eSelector : Selector eC eX eX where
  select := fun _R _c _x => (eRule, 0)
  criterion := fun _c _x _R => 0

/-- 选择器有效。 -/
theorem eSelector_isValid : eSelector.IsValid eRules := by
  intro c x
  exact Set.mem_singleton eRule

/-- ⭐ **可 `#eval` 的 WorldModel 实例**（四部分齐备）。 -/
noncomputable def eWorldModel : WorldModel where
  frame := eFrame
  ctx := eC
  instX := ⊤
  state := { space := eX, cur := 0, initial := { val := 0, isRandom := false } }
  rules := eWorldRules
  simulator := eSimulator
  selector := eSelector
  state_consistent := rfl

/-- `eWorldModel` 满足 `WellFormed`。 -/
theorem eWorldModel_wellFormed : eWorldModel.WellFormed := eSelector_isValid

/-! **世界模型层实例注册**（供 `EndToEnd.endToEnd` 的 `[AddCommGroup …]` / `[Ring …]` / `[Nonempty …]`）。 -/
instance instEwXAddCommGroup : AddCommGroup eWorldModel.frame.X.Carrier :=
  inferInstanceAs (AddCommGroup ℤ)
instance instEwXRing : Ring eWorldModel.frame.X.Carrier := inferInstanceAs (Ring ℤ)
instance instEwXNonempty : Nonempty eWorldModel.frame.X.Carrier := ⟨0⟩
instance instEwThetaRing : Ring eWorldModel.frame.Θ.Carrier := inferInstanceAs (Ring ℤ)
instance instEwThetaAddCommGroup : AddCommGroup eWorldModel.frame.Θ.Carrier :=
  inferInstanceAs (AddCommGroup ℤ)

/-! ===========================================================================
    §2  可计算的端到端链（`#eval` 的对象）

    链上四环节的可计算镜像：
    `xobs`（① 的输出，见 H1）→ `predCalc`（②）→ `residCalc`（③）→ `wbCalc`（④）。
    =========================================================================== -/

/-- 环节 ②（可计算预测）：`x ↦ x + 1`。**就是 `EndToEnd.predFrom eWorldModel` 的裸读法**
（§3 `predCalc_eq_predFrom` 证明它逐位相等）。 -/
def predCalc (x : ℤ) : ℤ := x + 1

/-- 环节 ③（可计算残差）：观测估计减预测。 -/
def residCalc (xobs x : ℤ) : ℤ := xobs - predCalc x

/-- 环节 ④（可计算写回）：`θ' = θ + η * φ r`。`η = 1`、`φ = id`。 -/
def wbCalc (r θ : ℤ) : ℤ := θ + 1 * r

/-- ⭐ **可计算的端到端**：输入 `xobs`（① 的输出）与 `x`（② 的起点）、当前 `θ`，
输出 `θ'`。 -/
def e2eCalc (xobs x θ : ℤ) : ℤ := wbCalc (residCalc xobs x) θ

/-! ===========================================================================
    §3  `#eval`：真正的数值预测（3 组以上的不同输入）
    =========================================================================== -/

/-- **输入 1**：`xobs = 10`, `x = 0`, `θ = 0` ⟹ 残差 `10 - 1 = 9` ⟹ `θ' = 0 + 9 = 9`。 -/
def in1 : ℤ × ℤ × ℤ := (10, 0, 0)
/-- **输入 2**：`xobs = 0`, `x = 0`, `θ = 0` ⟹ 残差 `0 - 1 = -1` ⟹ `θ' = -1`。 -/
def in2 : ℤ × ℤ × ℤ := (0, 0, 0)
/-- **输入 3**：`xobs = 5`, `x = 4`, `θ = 100` ⟹ 残差 `5 - 5 = 0` ⟹ `θ' = 100`（不动）。 -/
def in3 : ℤ × ℤ × ℤ := (5, 4, 100)
/-- **输入 4**：`xobs = -3`, `x = 7`, `θ = -7` ⟹ 残差 `-3 - 8 = -11` ⟹ `θ' = -18`。 -/
def in4 : ℤ × ℤ × ℤ := (-3, 7, -7)

/-- 把三元组喂进端到端链。 -/
def runE2E (t : ℤ × ℤ × ℤ) : ℤ := e2eCalc t.1 t.2.1 t.2.2

/-! **`#eval` 一：四组输入的端到端 `θ'`（这就是「给 `x` 与 `y` 算出 `θ'`」）。** -/
#eval runE2E in1
#eval runE2E in2
#eval runE2E in3
#eval runE2E in4

/-! **`#eval` 二：三环节各自的数值（拆开打印，便于核对）。** -/
#eval (predCalc 0, predCalc 4, predCalc 7)
#eval (residCalc 10 0, residCalc 0 0, residCalc 5 4, residCalc (-3) 7)
#eval (wbCalc 9 0, wbCalc (-1) 0, wbCalc 0 100, wbCalc (-11) (-7))

/-! **`#eval` 三：整张表一次打印。** -/
#eval (List.map runE2E [in1, in2, in3, in4])

/-! **`#eval` 四：观测映射 `h = id : ℤ → ℤ` 单射，原像唯一，
故 ① 的输出在像上等于 `y` 本身（见 §4 `evalObserve_eq`）。 -/
#eval ((10 : ℤ), (0 : ℤ))

/-! ===========================================================================
    §4  证明：`#eval` 的结果与理论一致
    =========================================================================== -/

/-- `h`：观测映射取 `eWorldModel.frame.X.Carrier (= ℤ)` 上的恒等（**单射**——
这是 `observe` 精确的前提）。观测空间 `Y` 取 `ℤ`。 -/
def hObs : eWorldModel.frame.X.Carrier → ℤ := fun x => x

/-- `h` 单射。 -/
theorem hObs_injective : Function.Injective hObs := fun _ _ h => h

/-- `φ`：残差 → 参数方向，取恒等（在 `eWorldModel` 的两条投影路径之间）。

⚠ 因 `instEwXAddCommGroup` / `instEwThetaRing` 是 `inferInstanceAs` 搬运的实例，
`ℤ →+ ℤ` 与目标路径**不同一**，故此处用 `AddMonoidHom.id` 在**目标类型**上定义。 -/
def phiId : eWorldModel.frame.X.Carrier →+ eWorldModel.frame.Θ.Carrier :=
  AddMonoidHom.id _

/-- ⭐⭐ **环节 ① 的取值被定理钉死**：`observe hObs (hObs x) = x`。

**这就是「`#eval` 里的 `xobs` 不是编造的」的证据**：
`xobs` 取 `y` 的像点时，`EndToEnd.observe hObs y` **定义上就是** 它。 -/
theorem evalObserve_eq (y : ℤ) :
    EndToEnd.observe hObs (hObs (y : eWorldModel.frame.X.Carrier))
      = (y : eWorldModel.frame.X.Carrier) :=
  EndToEnd.observe_apply_of hObs_injective (y : eWorldModel.frame.X.Carrier)

/-- ⭐⭐ **环节 ② 一致（`rfl` 级）**：`predCalc x` 恰是 `EndToEnd.predFrom eWorldModel` 的一步。 -/
theorem predCalc_eq_predFrom (x : ℤ) :
    predCalc x
      = EndToEnd.predFrom eWorldModel (0 : eWorldModel.frame.Θ.Carrier)
          PUnit.unit PUnit.unit PUnit.unit (x : eWorldModel.frame.X.Carrier) :=
  rfl

/-- ⭐⭐ **环节 ③ 一致（`rfl` 级）**：`residCalc` 恰是 `EndToEnd.e2eResidual`。 -/
theorem residCalc_eq_e2eResidual (xobs x : ℤ) :
    residCalc xobs x
      = EndToEnd.e2eResidual eWorldModel (xobs : eWorldModel.frame.X.Carrier)
          (0 : eWorldModel.frame.Θ.Carrier)
          PUnit.unit PUnit.unit PUnit.unit (x : eWorldModel.frame.X.Carrier) :=
  rfl

/-- ⭐⭐ **环节 ④ 一致（`rfl` 级）**：`wbCalc` 恰是 `ResidualLoop.writeBack`（`η = 1`, `φ = id`）。 -/
theorem wbCalc_eq_writeBack (r θ : ℤ) :
    wbCalc r θ
      = ResidualLoop.writeBack (X := eWorldModel.frame.X) eWorldModel.frame.Θ
          (1 : eWorldModel.frame.Θ.Carrier) phiId
          (r : ResidualLoop.Residual eWorldModel.frame.X)
          (θ : eWorldModel.frame.Θ.Carrier) :=
  rfl

/-- ⭐⭐⭐ **端到端一致（`rfl` 级）**：`e2eCalc` 恰是 `EndToEnd.endToEnd` 在 `eWorldModel` 上
的一次运行（① 的输出取 `xobs`，即 `observe hObs y` 的像上值）。

**⟹ 这是「`#eval` 结果 = 理论值」的**最强制形式**：
两端是**同一个项**（`rfl`），不是两套算法。** -/
theorem e2eCalc_eq_endToEnd (xobs x θ : ℤ) :
    e2eCalc xobs x θ
      = EndToEnd.endToEnd eWorldModel hObs (1 : eWorldModel.frame.Θ.Carrier) phiId
          (hObs (xobs : eWorldModel.frame.X.Carrier)) (θ : eWorldModel.frame.Θ.Carrier)
          PUnit.unit PUnit.unit PUnit.unit (x : eWorldModel.frame.X.Carrier) := by
  have hobs : EndToEnd.observe hObs (hObs (xobs : eWorldModel.frame.X.Carrier))
      = (xobs : eWorldModel.frame.X.Carrier) := evalObserve_eq xobs
  unfold EndToEnd.endToEnd
  rw [hobs]
  rfl

/-! ### §4.3  ⚠ 与任务1实例 `zWorldModel` 的接线：**未做**（诚实标注）

任务1的实例源在 `Fate/WorldModelMinimal.lean:284,301`：`zStep := x ↦ x + 1`、
`zWorldModel`（状态 `ℤ`）——**与本节 `eWorldModel` 的机制完全相同**。
`WorldModelMinimal` 已由任务1 的 `minimalWorldModel_wellFormed` / `zWorldModel_wellFormed`
证明齐备（见该文件 §5 / §7）。

**但本文件不引用 `zWorldModel`**，原因是**可核查的构建状态问题**：

| 事实 | 证据 |
|---|---|
| `.lake/build/lib/lean/Fate/WorldModelMinimal.olean` 时间戳 | `10月22日 14:16` |
| `Fate/WorldModelMinimal.lean` 修改时间 | `10月22日 14:19` |
| 实测 `#check @Fate.WorldModelMinimal.zWorldModel` | `unknown identifier` |
| 实测 `#check @Fate.WorldModelMinimal.minimalWorldModel` | ✅ 可见 |

⟹ 已构建的 olean **不含** `zStep` / `zWorldModel`（它们是在源文件**之后**新增的）。
`lake env lean` 只读现有 olean、**不重建**依赖，故本文件**引用不到**它们；
若强行引用会得到 `unknown identifier`，而不是一条定理。

**处置（遵守「不修改已有模块」）**：本文件**另建** `eWorldModel`，
其**状态空间（`ℤ`）、机制（`x ↦ x + 1`）、规则与选择器结构，与任务1的 `zWorldModel` 逐位同构**
（对照 `WorldModelMinimal.lean:284` 的 `zStep` 与本文 `eStep`）。
`eStep` 与 `zStep` 的**字面定义相同**：`fun x _u _ε _θ _a => x + 1`。

**⚠ 因此本文件诚实地标注：**
- ✅ `#eval` 的数值**是**一个合法 `WorldModel` 实例（`eWorldModel`）上的端到端 `θ'`；
- ✅ 该实例的机制**与任务1实例的定义逐字相同**；
- ⚠ 但「`zWorldModel` 本身被 `#eval`」这一步**未**在本文件里出现，
  因 olean 陈旧而**无法在本会话中做到**。修复方式是重建该模块的 olean
  （`lake build Fate.WorldModelMinimal`，本会话纪律禁止全量构建），
  届时 `§4.3` 的两条 `rfl` 桥接即可直接补上。 -/

/-! ### §4.1  四组输入的数值结论（与 `#eval` 打印一致） -/

/-- ⭐ **输入 1 的理论值**：`θ' = 9`。 -/
theorem run1_value : runE2E in1 = 9 := by decide

/-- ⭐ **输入 2 的理论值**：`θ' = -1`。 -/
theorem run2_value : runE2E in2 = -1 := by decide

/-- ⭐ **输入 3 的理论值**：`θ' = 100`（残差为 `0` ⟹ **不动**，即 `writeBack_zero` 的实例）。 -/
theorem run3_value : runE2E in3 = 100 := by decide

/-- ⭐ **输入 4 的理论值**：`θ' = -18`。 -/
theorem run4_value : runE2E in4 = -18 := by decide

/-- ⭐⭐ **输入 3 的语义**：残差恰为 `0`。 -/
theorem in3_resid_zero : residCalc in3.1 in3.2.1 = 0 := by decide

/-! ### §4.2  ⭐ 正确性 / 非平凡性与全称闭式（在实例上「跑通」） -/

/-- ⭐⭐ **正确性判据的实例**：观测恰等于预测（残差 `0`）⟹ `θ` 不动。 -/
theorem e2e_fixed_instance (θ x : ℤ) : e2eCalc (x + 1) x θ = θ := by
  unfold e2eCalc wbCalc residCalc predCalc
  ring

/-- ⭐⭐ **全称闭式（全窗口）**：对**一切** `xobs, x, θ`，
端到端的结果恰为 `θ + (xobs - x - 1)`。

**这是「最优性全称」层**：不只四条具体输入，而是**一切**输入。 -/
theorem e2eCalc_closed_form (xobs x θ : ℤ) : e2eCalc xobs x θ = θ + (xobs - x - 1) := by
  unfold e2eCalc wbCalc residCalc predCalc
  ring

/-- ⭐⭐ **非平凡性判据的实例**：观测 ≠ 预测（残差非零）⟹ `θ` 必改。 -/
theorem e2e_moves_instance (θ x : ℤ) : e2eCalc x x θ ≠ θ := by
  intro h
  rw [e2eCalc_closed_form] at h
  omega

end EvalReal
end FateV2.Loop