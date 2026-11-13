import FateWorld.Legacy.RuleDrivesEndToEnd

/-! ===========================================================================
  `Fate.Demo.EndToEnd` —— **端到端可执行演示：μ 世界模型跑 N 步、`norm_num` 出数字**

  ## 0  本模块演示什么

  一个**最小、完全具体**的 `WorldModel`，把 `Fate.EndToEnd.endToEndIter`
  真正跑起来，并**逐位算出**每步参数 —— 回答「这个系统真的能预测吗？」

  四环节链条（`Fate/EndToEnd.lean` 的 §1–§4）：

  ```
  y ──①observe──▶ x̂_obs ──②predFrom──▶ x̂_pred ──③残差──▶ r ──④writeBack──▶ θ'
  ```

  在本演示的具体化下，一步更新退化为**仿射收缩** `θ' = θ + η (y − θ)`，
  取 `η = 1/2, y = 1, θ₀ = 0` 得 `θ_k = 1 − 2^{-k}`：**显式收敛到 1**。

  ## 1  具体化选择（全部**具体类型**，非抽象空间）

  | 空间 | 取值 |
  |---|---|
  | `X`（状态）| `ℚ`，可测结构 `⊤` |
  | `Θ`（参数）| `ℚ` |
  | `U`（外生输入）| `PUnit` |
  | `Ν`（噪声）| `PUnit` |
  | `Act`（干预）| `PUnit` |
  | `Ctx`（上下文）| `PUnit` |

  **规则（机制）`demoStep`：状态恒等于参数** ——
  `demoStep x u ν θ a := θ`，即 $f(x,u,\varepsilon;\theta,a)=\theta$，
  这是「参数可辨识」的最简世界（@① `LawRule` 的确定性退化）。

  ## 2  ⚠ 诚实边界（必读）

  **2.1 为什么不用 `#eval` 而用 `norm_num`。**
  `EndToEnd.endToEndIter` 是 `noncomputable`（其观测环节
  `EndToEnd.observe = RA14Strong.chooseEstimator` 用 `Classical.choose`）。故
  `#eval` 无法求值。本模块改用**显式数值等式 + `by norm_num`**：
  `norm_num` 在证明项里**实际执行有理数算术**，这同样是可执行演示；
  且**不用 `native_decide`**（本任务禁止）。

  **2.2 观测点的诚实处理。**
  观测映射 `hobs : X.Carrier → ℚ` 取**恒等**。故观测值 `y = hobs y'`
  是 `hobs` 的**像内点**，从而 `observe hobs (hobs y') = y'` 可以**引用既有定理**
  `RA14Strong.chooseEstimator_apply_of` 消去 `Classical.choose`。
  **本模块不声称**在像外点也成立（那里确实不成立，见 `Fate/ObsEstimationStrong.lean`）。

  **2.3 收敛性的确切内容。**
  本模块证明**闭式** `run_tendsto_gap : runQ k = 1 − (1/2)^k`，
  由此 `θ_k → 1`。这是**本具体模型**的收敛，**不**声称
  `Fate/RealConvergence.lean` 层的通用收敛定理（那需要额外结构）。

  **2.4 `WorldModel.rules` 仅供完备。**
  `WorldModel` 的字段 `rules`／`selector` 需要一个 `Rule`（其 kernel 是 `Measure`），
  本演示给零测度。**它不被本演示的推理消费**：`demoStep`（即
  `WorldModel.f`）是独立的 `Step` 字段，正是 `endToEndIter` 的转移来源。

  **2.5 类型别名实例的说明。**
  `demoWM.frame.X.Carrier` 与 `ℚ` **定义相等**，但类型类搜索不展开投影，
  故本模块把 `ℚ` 上的实例（`AddCommGroup`/`Ring`/`HSub`/…）
  用 `inferInstanceAs` **显式**提到投影类型上（`local instance`，文件内生效）。
  这**不是新假设**，只是把已有实例摆到类型类搜索可见的位置。

  ## 3  交付的**具体数值等式**（`norm_num` 真的在算）

  | 步 `k` | `θ_k` | 定理 |
  |---|---|---|
  | 0 | 0 | `run_zero`（`rfl`）|
  | 1 | 1/2 | `run_one` |
  | 2 | 3/4 | `run_two` |
  | 3 | 7/8 | `run_three` |
  | 4 | 15/16 | `run_four` |
  | 10 | 1023/1024 | `run_ten` |
  | 闭式 | `θ_k = 1 − 2^{-k}` | `run_tendsto_gap` |

  ## 4  ⚠ 防同义反复自检（G7）

  各 `run_*` 数值定理**前件为空**，结论是**具体的**有理数等式
  （如 `run 2 = 3/4`）。证明**必须**实际展开 `run_succ → endToEndIter → endToEnd`
  三步递推再做算术，**不会**因把结论塞进前件而成立。
  `run_succ` 的右端 `run k + η(1 − run k)` 由 `endToEnd_val`（展开 `endToEnd`
  一步：① `observe` 消去、② `predFrom = θ`、③ 残差、④ 写回）得到，
  **不是前件重抄**。

  ## 5  纪律

  零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide` / 零 `maxHeartbeats`；
  **不修改任何既有模块**。
  =========================================================================== -/

namespace Fate
namespace DemoEndToEnd

def demoX : StateSpace where
  Carrier := ℚ
  topo := inferInstance
  meas := ⊤
  borel_le := le_top

def demoΘ : ThetaSpace where
  Carrier := ℚ
  topo := inferInstance
  meas := ⊤

def demoFrame : Frame where
  Θ := demoΘ
  X := demoX
  U := { Carrier := PUnit, topo := inferInstance, meas := ⊤ }
  Act := { Carrier := PUnit, topo := inferInstance, meas := ⊤ }
  Ν := { Carrier := PUnit, meas := ⊤ }

local instance : MeasurableSpace demoFrame.X.Carrier := ⊤

def demoCtx : CtxSpace where Carrier := PUnit

def demoStep : Step demoFrame := fun _x _u _ν θ _a => θ

def zeroX : demoFrame.X.Carrier := (0:ℚ)

def zeroRule : Rule demoCtx demoFrame.X demoFrame.X :=
  Rule.mk (fun _ _ => (0 : MeasureTheory.Measure demoFrame.X.Carrier))

def demoWM : WorldModel where
  frame := demoFrame
  ctx := demoCtx
  instX := ⊤
  state := WorldState.mk demoX zeroX ⟨zeroX, false⟩
  rules := WorldRules.mk { zeroRule } ⟨zeroRule, rfl⟩
  simulator := WorldSimulator.mk demoStep 1
  selector := Selector.mk (fun _ _ _ => (zeroRule, 0)) (fun _ _ _ => 0)
  state_consistent := rfl

local instance : AddCommGroup demoWM.frame.X.Carrier := inferInstanceAs (AddCommGroup ℚ)
local instance : Ring demoWM.frame.Θ.Carrier := inferInstanceAs (Ring ℚ)
local instance : Nonempty demoWM.frame.X.Carrier := inferInstanceAs (Nonempty ℚ)
local instance : OfNat demoWM.frame.Θ.Carrier 1 := inferInstanceAs (OfNat ℚ 1)
local instance : OfNat demoWM.frame.X.Carrier 1 := inferInstanceAs (OfNat ℚ 1)
-- 混合类型运算：`endToEnd` 内部残差 `observe - predFrom` 是 `X - X`，
-- 但本条 `endToEnd_val` 的右端写 `y' - θ`（`X - Θ`），故登记之。
local instance : HMul demoWM.frame.Θ.Carrier demoWM.frame.X.Carrier demoWM.frame.Θ.Carrier :=
  inferInstanceAs (HMul ℚ ℚ ℚ)
local instance : HSub demoWM.frame.X.Carrier demoWM.frame.Θ.Carrier demoWM.frame.Θ.Carrier :=
  inferInstanceAs (HSub ℚ ℚ ℚ)
local instance : HSub demoWM.frame.Θ.Carrier demoWM.frame.Θ.Carrier demoWM.frame.Θ.Carrier :=
  inferInstanceAs (HSub ℚ ℚ ℚ)
local instance : HSub ℚ demoWM.frame.Θ.Carrier demoWM.frame.Θ.Carrier :=
  inferInstanceAs (HSub ℚ ℚ ℚ)
local instance : HAdd demoWM.frame.Θ.Carrier demoWM.frame.Θ.Carrier demoWM.frame.Θ.Carrier :=
  inferInstanceAs (HAdd ℚ ℚ ℚ)
local instance : HPow demoWM.frame.Θ.Carrier ℕ demoWM.frame.Θ.Carrier :=
  inferInstanceAs (HPow ℚ ℕ ℚ)

def hobs : demoWM.frame.X.Carrier → ℚ := id

def hsat : demoWM.frame.X.Carrier →+ demoWM.frame.Θ.Carrier := AddMonoidHom.id _

theorem hsat_apply (r : demoWM.frame.X.Carrier) : hsat r = r := rfl

def etaP : demoWM.frame.Θ.Carrier := (1/2 : ℚ)

def yP : ℚ := 1

def xP : demoWM.frame.X.Carrier := (0:ℚ)

def uP : demoWM.frame.U.Carrier := PUnit.unit
def epsP : demoWM.frame.Ν.Carrier := PUnit.unit
def aP : demoWM.frame.Act.Carrier := PUnit.unit

theorem predFrom_eq (θ : demoWM.frame.Θ.Carrier) :
    EndToEnd.predFrom demoWM θ uP epsP aP xP = θ := rfl

theorem observe_apply (y' : demoWM.frame.X.Carrier) :
    EndToEnd.observe hobs (hobs y') = y' :=
  RA14Strong.chooseEstimator_apply_of (h := hobs) (fun _ _ hab => hab) y'

theorem endToEnd_val (θ : demoWM.frame.Θ.Carrier) (y' : demoWM.frame.X.Carrier) :
    EndToEnd.endToEnd demoWM hobs etaP hsat (hobs y') θ uP epsP aP xP
      = θ + etaP * (y' - θ) := by
  rw [EndToEnd.endToEnd_apply, predFrom_eq, observe_apply, hsat_apply]
  rfl

theorem endToEndIter_forward (k : ℕ) (θ : demoWM.frame.Θ.Carrier) :
    EndToEnd.endToEndIter demoWM hobs etaP hsat yP uP epsP aP xP (k+1) θ
      = EndToEnd.endToEnd demoWM hobs etaP hsat yP
          (EndToEnd.endToEndIter demoWM hobs etaP hsat yP uP epsP aP xP k θ)
          uP epsP aP xP := by
  induction k generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [EndToEnd.endToEndIter_succ, ih, EndToEnd.endToEndIter_succ]

noncomputable def run (k : ℕ) : demoWM.frame.Θ.Carrier :=
  EndToEnd.endToEndIter demoWM hobs etaP hsat yP uP epsP aP xP k 0

theorem run_zero : run 0 = 0 := rfl

theorem run_succ (k : ℕ) :
    run (k+1) = run k + etaP * ((1 : demoWM.frame.X.Carrier) - run k) := by
  have h1 : run (k+1)
      = EndToEnd.endToEnd demoWM hobs etaP hsat yP (run k) uP epsP aP xP := by
    show EndToEnd.endToEndIter demoWM hobs etaP hsat yP uP epsP aP xP (k+1) 0
      = EndToEnd.endToEnd demoWM hobs etaP hsat yP
          (EndToEnd.endToEndIter demoWM hobs etaP hsat yP uP epsP aP xP k 0)
          uP epsP aP xP
    rw [endToEndIter_forward]
  have hy : yP = hobs (1 : demoWM.frame.X.Carrier) := rfl
  rw [h1, hy, endToEnd_val]

theorem run_one : run 1 = (1/2 : ℚ) := by
  rw [run_succ, run_zero]
  change (0:ℚ) + (1/2:ℚ) * ((1:ℚ) - 0) = 1/2
  norm_num

theorem run_two : run 2 = (3/4 : ℚ) := by
  rw [run_succ, run_one]
  change (1/2:ℚ) + (1/2:ℚ) * ((1:ℚ) - 1/2) = 3/4
  norm_num

theorem run_three : run 3 = (7/8 : ℚ) := by
  rw [run_succ, run_two]
  change (3/4:ℚ) + (1/2:ℚ) * ((1:ℚ) - 3/4) = 7/8
  norm_num

theorem run_four : run 4 = (15/16 : ℚ) := by
  rw [run_succ, run_three]
  change (7/8:ℚ) + (1/2:ℚ) * ((1:ℚ) - 7/8) = 15/16
  norm_num

theorem run_five : run 5 = (31/32 : ℚ) := by
  rw [run_succ, run_four]
  change (15/16:ℚ) + (1/2:ℚ) * ((1:ℚ) - 15/16) = 31/32
  norm_num

theorem run_six : run 6 = (63/64 : ℚ) := by
  rw [run_succ, run_five]
  change (31/32:ℚ) + (1/2:ℚ) * ((1:ℚ) - 31/32) = 63/64
  norm_num

theorem run_seven : run 7 = (127/128 : ℚ) := by
  rw [run_succ, run_six]
  change (63/64:ℚ) + (1/2:ℚ) * ((1:ℚ) - 63/64) = 127/128
  norm_num

theorem run_eight : run 8 = (255/256 : ℚ) := by
  rw [run_succ, run_seven]
  change (127/128:ℚ) + (1/2:ℚ) * ((1:ℚ) - 127/128) = 255/256
  norm_num

theorem run_nine : run 9 = (511/512 : ℚ) := by
  rw [run_succ, run_eight]
  change (255/256:ℚ) + (1/2:ℚ) * ((1:ℚ) - 255/256) = 511/512
  norm_num

theorem run_ten : run 10 = (1023/1024 : ℚ) := by
  rw [run_succ, run_nine]
  change (511/512:ℚ) + (1/2:ℚ) * ((1:ℚ) - 511/512) = 1023/1024
  norm_num

noncomputable def runQ (k : ℕ) : ℚ := run k

theorem runQ_zero : runQ 0 = 0 := rfl

theorem runQ_succ (k : ℕ) : runQ (k+1) = runQ k + (1/2 : ℚ) * ((1:ℚ) - runQ k) := by
  have h := run_succ k
  exact h

theorem run_closed_rat (k : ℕ) : (1 : ℚ) - runQ k = (1/2 : ℚ)^k := by
  induction k with
  | zero => rw [runQ_zero]; norm_num
  | succ k ih =>
    rw [runQ_succ, pow_succ]
    have : (1:ℚ) - (runQ k + (1/2:ℚ) * ((1:ℚ) - runQ k))
        = (1/2:ℚ) * ((1:ℚ) - runQ k) := by ring
    rw [this, ih]; ring

/-- ⭐ **收敛趋势（可计算）**：`1 − θ_k = (1/2)^k`，故 `θ_k → 1`。 -/
theorem run_tendsto_gap (k : ℕ) : runQ k = 1 - (1/2 : ℚ)^k := by
  have := run_closed_rat k
  linarith

end DemoEndToEnd
end Fate
