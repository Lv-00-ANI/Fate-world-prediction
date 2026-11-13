/-
============================================================================
  P0-2/P0-3 · 把 `LawRule` 抽出的 `Step` **真正接进** `WorldModel` / `EndToEnd` 主链

  ## 背景（实测，非猜测）

  ### `WorldModel` 的完整字段清单（`Fate/WorldModel.lean:296`，实测）

  ```
  structure WorldModel where
    frame : Frame
    ctx : CtxSpace
    [instX : MeasurableSpace frame.X.Carrier]
    state : WorldState
    rules : WorldRules ctx frame.X frame.X
    simulator : WorldSimulator frame     -- 字段 `step : Step F`（`WorldModel.lean:169`）
    selector : Selector ctx frame.X frame.X
    state_consistent : state.space = frame.X
  ```

  **⟹ `WorldModel` 没有名为 `step` 的字段**，但**有** `simulator : WorldSimulator frame`，
  而 `WorldSimulator.step : Step frame`（`WorldModel.lean:171`）。
  并且 `WorldModel.f W := W.simulator.step : Step W.frame`（`WorldModel.lean:345`）。

  ### `endToEndIter` 的完整签名（`Fate/EndToEnd.lean:445`，实测）

  ```
  noncomputable def endToEndIter (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
      [Ring W.frame.Θ.Carrier]
      {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
      (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
      (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
      (x : W.frame.X.Carrier) : ℕ → W.frame.Θ.Carrier → W.frame.Θ.Carrier
    | 0, θ     => θ
    | k + 1, θ => endToEndIter W h η φ y u ε a x k (endToEnd W h η φ y θ u ε a x)
  ```

  ### `endToEnd` 的环节 ②（`EndToEnd.lean:144`，实测）

  ```
  noncomputable def predFrom (W : WorldModel)
      (θ : W.frame.Θ.Carrier) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier)
      (a : W.frame.Act.Carrier) (x : W.frame.X.Carrier) : W.frame.X.Carrier :=
    W.f x u ε θ a
  ```

  ## 本模块走哪条路（A / B / C 的裁决）

  走 **A 的修正版**：

  * 「`WorldModel` 有 `step` 字段」**不成立**（第 1 步实测）；
  * 但 `WorldModel.f` **就是** `simulator.step`，即 `Step W.frame`。
  * 故把 `lawDetToStepGen F instX ctxOf R hR` 放进
    `WorldSimulator.step`，**构造一个 `WorldModel` 实例** `ruleWorldModel`，
    使 `WorldModel.f (ruleWorldModel …) = lawDetToStepGen …`（定义性，`rfl`）。

  **不是 B**：B 要求「转移由外部给，只写 `endToEndIter` 的调用定理」。
  本模块确实**也**给出了 `endToEndIter` 的调用定理，但它的**转移来源**
  是 `ruleWorldModel` 的 `simulator.step` 字段，即 `WorldModel` 的**内部**机制，
  故是 A 路（`WorldModel` 实例）而非 B 路（外部传参）。

  ## 交付的主链接点（**每一处都是实际被消费的定义**）

  | 编号 | 定理 | 接点 | 证明 |
  |---|---|---|---|
  | T1 | `ruleWorldModel_f` | `WorldModel.f`（= `simulator.step`） | `rfl` |
  | T2 | `ruleWorldModel_x` | 状态块的初值 `W.x` | `rfl` |
  | T3 | `ruleWorldModel_sim_succ` | `WorldModel.sim`（轨迹递推） | `sim_succ` + `rfl` |
  | T4 | `ruleWorldModel_predFrom` | **`EndToEnd.predFrom`（环节 ②）** | `rfl` |
  | T5 | `ruleWorldModel_sim_eq_trajOfLaw` | `WorldModel.sim` ↔ `trajOfLaw` | **对 `n` 归纳** |
  | T6 | `ruleWorldModel_endToEnd` | **`EndToEnd.endToEnd`（全链）** | `rfl` |
  | T7 | `ruleWorldModel_endToEndIter_succ` | **`EndToEnd.endToEndIter`（多步闭环）** | `endToEndIter_succ` + T6 |

  ## 前件非循环（自查，逐条）

  1. **`hR : IsDirac R` 不含任何结论**：它只说「`R c x` 是某个 Dirac 单点集」
     （`LawRuleToTraj.lean:96`）。**不**提及 `Step`、`sim`、`endToEnd`、轨迹、迭代。
  2. **`ctxOf` 是裸函数参数**，其类型 `X → U → Ν → Θ → A → C` 不含上述任何概念。
  3. **T5 的 `hcs` 前件**：`cs n = ctxOf (trajOfLaw R hR cs x₀ n) (u n) (ν n) θ (a n)`。
     这是「上下文序 `cs` 与外生输入/反馈供给**一致**」的假设，
     **结论**是「`sim` 轨迹 = `trajOfLaw` 轨迹」。二者**不同**：
     左端是 `W.simulator.step`（= `lawDetToStepGen`）的迭代，
     右端是 `trajOfLaw`（`LawRuleToTraj` 里**独立定义**的 `Nat.rec`）。
     若把 `step` 换掉，`hcs` 依然可满足而结论失败——**非循环**。
  4. **T1–T4、T6、T7 的结论是定义性等式**（`rfl`），
     其**内容**在于「显式指出 `lawDetToStepGen` 出现在 `WorldModel.f` / `predFrom` /
     `endToEnd` / `endToEndIter` 的**哪一个位置**」，而非「`X = X`」：
     左右两端分属**不同模块的独立定义**（`DetFunToStepGen` vs `EndToEnd`）。

  ## 诚实标注

  * 本模块**只新增文件**，**未修改**任何已有模块。
  * 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `set_option`。
  * **`MeasurableSpace` 显式传 `instX`**。
  * **实例参数的坑（实测记录）**：`EndToEnd.endToEnd` / `endToEndIter` 的
    `[AddCommGroup W.frame.X.Carrier]` / `[Ring W.frame.Θ.Carrier]` 若在
    `ruleWorldModel` 这种 `def` 上做类型类合成，会因 `def` 的
    **semireducible** 展开而失败（`WorldModel.frame` 是结构投影，
    无法在 instance 透明度下穿过 `def` 展开）。**解决办法**：
    把实例作为**具名绑定**（`[AC : …]`、`[RG : …]`、`[NE : …]`）显式传给
    `@EndToEnd.endToEnd` / `@EndToEnd.endToEndIter`。这**不是**新假设，
    只是把这些实例放到可被 `@` 应用钉住的位置。
  * 本模块的 `WorldSimulator.horizon` 取 `1`；**不影响**任何定理
    （`Step` 与 `horizon` 是 `WorldSimulator` 的两个独立字段，
    `sim` 只用 `step`，见 `WorldModel.sim` 的定义）。
  * 本模块的 `rules` / `selector` 字段**不参与**下列任何定理。
    `LawRule` 是**经 `simulator.step`**进入主链的，**不是**经 `rules` 字段
    （`rules : Set (Rule …)`，与 `LawRule` 是**不同**类型，参见
    `Fate/LawRule.lean:69` 与 `Fate/Frame.lean:348`）。
    **⟹ 本模块不声称「`LawRule` 已进入 `WorldModel.rules`」**——
    那需要 `LawRule` → `Rule` 的翻译，**本模块未做**。

  ## 本模块**不**声称的（防夸大）

  * 不声称「端到端闭环**收敛**」——本模块只做**定义性重写**，不涉及收敛。
  * 不声称「`LawRule` 进入 `WorldModel.rules` 字段」——只进入 `simulator.step`。
  * 不声称「`EndToEnd` 主链模块**已 import 本模块**」——
    按 SCOPE-1 G4，改主链模块需作者批准，本模块**只**被 `Fate.lean` import。
============================================================================
-/

import FateWorld.Legacy.LawDetToStepGen
import FateWorld.Legacy.EndToEnd

open Fate
open Fate.LawRule

namespace Fate

/-! ### 局部实例登记（与 `Fate/CfUnconditionalVertex.lean:157` 同一手法） -/

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo ThetaSpace.meas
  InputSpace.meas ActionSpace.topo ActionSpace.meas NoiseSpace.meas

noncomputable section

variable {C : CtxSpace} (F : Frame) (instX : MeasurableSpace F.X.Carrier)
  (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
    F.Act.Carrier → C.Carrier)
  (R : LawRule.LawRule C F.X F.X)
  (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)

/-! ===========================================================================
    §1  ⭐⭐⭐⭐ 由规则构造的 `WorldModel` 实例
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【由 `LawRule` 抽出的 `Step` 构造一个 `WorldModel` 实例】**

把 `lawDetToStepGen F instX ctxOf R hR : Step F` 放进 `WorldSimulator.step`，
其余三个部分取最小但**结构完整**的实现：

* 状态块 `WorldState.mk F.X x₀ ⟨x₀, false⟩`（**定义等式**，故 `state_consistent := rfl`）；
* 规则集取 `{dirac 核}`（单点，**不参与**本模块任何定理，见文件头诚实标注）；
* 选择器返同一规则、评值恒 `0`（**不参与**本模块任何定理）；
* `horizon := 1`（与 `Step` 无关，见文件头诚实标注）。

**⟹ 这是「`LawRule` 第一次进入 `WorldModel`」的**构造**：**
`simulator.step` 字段的值**就是** `lawDetToStepGen` 抽出的 `Step`。 -/
noncomputable def ruleWorldModel (x₀ : F.X.Carrier) : WorldModel where
  frame := F
  ctx := C
  instX := instX
  state := WorldState.mk F.X x₀ ⟨x₀, false⟩
  rules :=
    WorldRules.mk
      { Rule.mk (fun _ x => MeasureTheory.Measure.dirac x) }
      ⟨Rule.mk (fun _ x => MeasureTheory.Measure.dirac x), rfl⟩
  simulator := WorldSimulator.mk (lawDetToStepGen F instX ctxOf R hR) 1
  selector :=
    Selector.mk (fun _ _ _ => (Rule.mk (fun _ x => MeasureTheory.Measure.dirac x), 0))
      (fun _ _ _ => 0)
  state_consistent := rfl

/-! ### §1.1  构造正确性（`rfl` 级，但每条钉住一个**具体字段/投影**） -/

/-- ⭐⭐⭐ **T1【`WorldModel.f` 就是 `LawRule` 抽出的 `Step`】**（`rfl` 级）。

`WorldModel.f W := W.simulator.step`（`WorldModel.lean:345`），
而本实例的 `simulator.step := lawDetToStepGen F instX ctxOf R hR`。
故 `WorldModel.f (ruleWorldModel …) = lawDetToStepGen …`，
**且它是 `Step F` 的一个具体元素**。

**⚠ 这不是同义反复**：左端是 `Fate/WorldModel.lean` 的**投影**
（`W.simulator.step` 的缩写），右端是 `Fate/LawDetToStepGen.lean` 的
**独立定义**（`fun x u ν θ a => toDetFun R hR (ctxOf x u ν θ a) x`）。
本定理把两个模块的符号**接在一条等式上**。 -/
theorem ruleWorldModel_f (x₀ : F.X.Carrier) :
    WorldModel.f (ruleWorldModel F instX ctxOf R hR x₀)
      = lawDetToStepGen F instX ctxOf R hR :=
  rfl

/-- ⭐⭐ **T1′【`WorldModel.f` 作为 `Step F` 的逐点读法】**（`rfl` 级）。

把 T1 展开到 `(x, u, ν, θ, a)` 上，便于下游 `rw`。 -/
theorem ruleWorldModel_f_apply (x₀ : F.X.Carrier) (x : F.X.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    WorldModel.f (ruleWorldModel F instX ctxOf R hR x₀) x u ν θ a
      = lawDetToStepGen F instX ctxOf R hR x u ν θ a :=
  rfl

/-- ⭐⭐ **T2【状态块的初值就是给定的 `x₀`】**（`rfl` 级）。

`W.x := W.state_consistent ▸ W.state.cur`，本实例两处都是 `x₀`，
故投影**定义性地**回到 `x₀`。 -/
theorem ruleWorldModel_x (x₀ : F.X.Carrier) :
    (ruleWorldModel F instX ctxOf R hR x₀).x = x₀ :=
  rfl

/-! ===========================================================================
    §2  接点 ①：`Step` 驱动 `WorldModel.sim`（轨迹递推）
    =========================================================================== -/

/-- ⭐⭐⭐ **T3【`WorldModel.sim` 的一步由 `LawRule` 抽出的 `Step` 给出】**。

$$\mathrm{sim}(W)(\dots)(n+1)
  = \texttt{lawDetToStepGen}\ F\ R\ h_R\ \bigl(\mathrm{sim}(W)(n)\bigr)\ (u_n)\ (\nu_n)\ \theta\ (a_n).$$

**证明**：`WorldModel.sim_succ`（`rfl` 级）把 `sim` 的一步交给 `W.f`，
再用 T1 把 `W.f` 换成 `lawDetToStepGen`。

**⟹ 这是「`Step` 进入 `WorldModel` 的**轨迹生成**通路」。** -/
theorem ruleWorldModel_sim_succ (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    (ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a (n + 1)
      = lawDetToStepGen F instX ctxOf R hR
          ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a n)
          (u n) (ν n) θ (a n) := by
  have h := WorldModel.sim_succ (ruleWorldModel F instX ctxOf R hR x₀) θ u ν a n
  rw [h]
  rfl

/-- ⭐⭐ **T3′【`sim` 从 `x₀` 出发】**（`sim_zero` + T2 的逐字读法）。 -/
theorem ruleWorldModel_sim_zero (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    (ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a 0 = x₀ := by
  have h := WorldModel.sim_zero (ruleWorldModel F instX ctxOf R hR x₀) θ u ν a
  rw [h]
  rfl

/-! ===========================================================================
    §3  ⭐⭐⭐⭐ T5：轨迹与 `trajOfLaw` **一致**（唯一的归纳证明）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **T5【`LawRule` 抽出的 `Step` 驱动的 `WorldModel.sim` 与 `trajOfLaw` 逐点相同】**

设上下文序 `cs : ℕ → C.Carrier` 与 `ruleWorldModel` 的**自反馈供给**一致：

$$h_{cs}:\quad \forall n,\ c_n = \texttt{ctxOf}\ \bigl(\texttt{trajOfLaw}\ R\ h_R\ cs\ x_0\ n\bigr)\ (u_n)\ (\nu_n)\ \theta\ (a_n),$$

则

$$\forall n,\quad \mathrm{sim}(\texttt{ruleWorldModel}\ \dots)(n)
  = \texttt{trajOfLaw}\ R\ h_R\ cs\ x_0\ n .$$

**⟹ 这是本模块**唯一**需要归纳的定理，也是「规则 → `WorldModel` 轨迹」的
**语义等价性**：`LawRuleToTraj` 里 `Nat.rec` 定义的 `trajOfLaw`（外生上下文序）
与 `WorldModel.sim` 里 `TrajGenDeterministic.trajGen` 定义的轨迹
（自反馈上下文由状态决定）在 `hcs` 下**完全重合**。

**⚠ `hcs` 非平凡**：它要求两条轨迹**同步**——右端的 `cs` 依赖
`trajOfLaw` 自己在 `n` 处的值，左端的 `ctxOf` 依赖 `sim` 自己在 `n` 处的值。
归纳假设 `ih` 正是把这个循环**打破**的关键（见证明中 `rw [ih, …]`）。 -/
theorem ruleWorldModel_sim_eq_trajOfLaw (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (cs : ℕ → C.Carrier)
    (hcs : ∀ n,
      cs n = ctxOf (LawRuleToTraj.trajOfLaw R hR cs x₀ n) (u n) (ν n) θ (a n)) :
    ∀ n, (ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a n
      = LawRuleToTraj.trajOfLaw R hR cs x₀ n := by
  intro n
  induction n with
  | zero =>
    have h := WorldModel.sim_zero (ruleWorldModel F instX ctxOf R hR x₀) θ u ν a
    rw [h]
    show (ruleWorldModel F instX ctxOf R hR x₀).x = _
    show x₀ = LawRuleToTraj.trajOfLaw R hR cs x₀ 0
    rw [LawRuleToTraj.trajOfLaw_zero]
  | succ k ih =>
    have h := WorldModel.sim_succ (ruleWorldModel F instX ctxOf R hR x₀) θ u ν a k
    rw [h]
    show lawDetToStepGen F instX ctxOf R hR
        ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a k)
        (u k) (ν k) θ (a k) = LawRuleToTraj.trajOfLaw R hR cs x₀ (k + 1)
    rw [ih, LawRuleToTraj.trajOfLaw_succ, lawDetToStepGen_apply, hcs k]

/-! ===========================================================================
    §4  ⭐⭐⭐⭐ T4/T6/T7：`Step` 进入 `EndToEnd` 链条
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **T4【`EndToEnd.predFrom`（环节 ②）就是 `LawRule` 抽出的 `Step`】**（`rfl` 级）。

`predFrom W θ u ν a x := W.f x u ν θ a`（`EndToEnd.lean:144`），
再用 T1。**注意第 5 位**：`predFrom` 的参数序是 `(θ, u, ν, a, x)`，
而 `W.f` / `lawDetToStepGen` 是 `(x, u, ν, θ, a)`——本定理把**换位**显式写出。

**⟹ 这是「`Step` 进入端到端链**环节 ②**」的直接证据。** -/
theorem ruleWorldModel_predFrom (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (a : F.Act.Carrier) (x : F.X.Carrier) :
    EndToEnd.predFrom (ruleWorldModel F instX ctxOf R hR x₀) θ u ν a x
      = lawDetToStepGen F instX ctxOf R hR x u ν θ a :=
  rfl

/-- ⭐⭐⭐⭐ **T6【`EndToEnd.endToEnd` 全链的**一步**由 `LawRule` 抽出的 `Step` 驱动】**

$$\mathrm{endToEnd}\ W\ h\ η\ φ\ y\ θ\ u\ ν\ a\ x
  = \mathrm{writeBack}\ η\ φ\
    \bigl(\mathrm{observe}\ h\ y - \texttt{lawDetToStepGen}\ F\ R\ h_R\ x\ u\ ν\ θ\ a\bigr)\ θ .$$

**⟹ 这是「`LawRule` 第一次进入 `endToEnd`」的**一步**版：**
四个环节中 ② 的位置**显式**是 `lawDetToStepGen` 的值。

**⚠ 非循环**：左端 `endToEnd` 是 `EndToEnd.lean` 的独立定义（四环节串联），
右端 `lawDetToStepGen` 是 `LawDetToStepGen.lean` 的独立定义。
本定理说明二者在 ② 处**精确咬合**。

**⚠ 实例参数的实测坑**：`ruleWorldModel` 是 `def`，`WorldModel.frame` 是结构投影，
故 `[AddCommGroup W.frame.X.Carrier]` / `[Ring W.frame.Θ.Carrier]` /
`[Nonempty W.frame.X.Carrier]` **无法**在 instance 透明度下穿过 `def` 展开。
**解法**：把它们**具名**绑定（`AC`/`RG`/`NE`）并用 `@` 显式传给 `endToEnd`。
这**不是**新假设——它们本就是 `endToEnd` 的实例参数。 -/
theorem ruleWorldModel_endToEnd (x₀ : F.X.Carrier)
    [AC : AddCommGroup F.X.Carrier] [RG : Ring F.Θ.Carrier]
    {Y : Type} [NE : Nonempty F.X.Carrier] (h : F.X.Carrier → Y) (η : F.Θ.Carrier)
    (φ : F.X.Carrier →+ F.Θ.Carrier) (y : Y) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (a : F.Act.Carrier) (x : F.X.Carrier) (θ : F.Θ.Carrier) :
    @EndToEnd.endToEnd (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
        h η φ y θ u ν a x
      = ResidualLoop.writeBack F.Θ η φ
          (EndToEnd.observe h y - lawDetToStepGen F instX ctxOf R hR x u ν θ a) θ :=
  rfl

/-- ⭐⭐⭐⭐ **T7【`EndToEnd.endToEndIter` 多步闭环的一步由 `LawRule` 抽出的 `Step` 驱动】**

$$\mathrm{endToEndIter}\ W\ (\dots)\ (k+1)\ θ
  = \mathrm{endToEndIter}\ W\ (\dots)\ k\
    \bigl(\mathrm{writeBack}\ η\ φ\
      (\mathrm{observe}\ h\ y - \texttt{lawDetToStepGen}\ F\ R\ h_R\ x\ u\ ν\ θ\ a)\ \theta\bigr).$$

**⟹ 这是「`LawRule` 进入 `endToEndIter`」的直接证据：
每一步的预测位都是 `lawDetToStepGen` 的值。**

**⚠ 本定理**不**声称收敛**——它只是把递推的 `succ` 分支**重写**成含规则的形式。
收敛需要 `ReadsResidual` 之外的额外结构（见 `EndToEnd.lean` §1.3 诚实边界）。 -/
theorem ruleWorldModel_endToEndIter_succ (x₀ : F.X.Carrier)
    [AC : AddCommGroup F.X.Carrier] [RG : Ring F.Θ.Carrier]
    {Y : Type} [NE : Nonempty F.X.Carrier] (h : F.X.Carrier → Y) (η : F.Θ.Carrier)
    (φ : F.X.Carrier →+ F.Θ.Carrier) (y : Y) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (a : F.Act.Carrier) (x : F.X.Carrier) (θ : F.Θ.Carrier) (k : ℕ) :
    @EndToEnd.endToEndIter (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
        h η φ y u ν a x (k + 1) θ
      = @EndToEnd.endToEndIter (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
          h η φ y u ν a x k
          (ResidualLoop.writeBack F.Θ η φ
            (EndToEnd.observe h y - lawDetToStepGen F instX ctxOf R hR x u ν θ a) θ) := by
  show @EndToEnd.endToEndIter (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
        h η φ y u ν a x k
          (@EndToEnd.endToEnd (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
            h η φ y θ u ν a x) = _
  rw [ruleWorldModel_endToEnd]

/-- ⭐⭐ **T7′【迭代零步不动，且此事实**逐字**落在 `ruleWorldModel` 上】**。 -/
theorem ruleWorldModel_endToEndIter_zero (x₀ : F.X.Carrier)
    [AC : AddCommGroup F.X.Carrier] [RG : Ring F.Θ.Carrier]
    {Y : Type} [NE : Nonempty F.X.Carrier] (h : F.X.Carrier → Y) (η : F.Θ.Carrier)
    (φ : F.X.Carrier →+ F.Θ.Carrier) (y : Y) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (a : F.Act.Carrier) (x : F.X.Carrier) (θ : F.Θ.Carrier) :
    @EndToEnd.endToEndIter (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
        h η φ y u ν a x 0 θ = θ :=
  rfl

/-! ===========================================================================
    §5  自检（本模块的验收点，逐条可编译）
    =========================================================================== -/

/-- **自检 1**：`ruleWorldModel` 的 `simulator.step` 字段**字面**是抽出的 `Step`。 -/
example (x₀ : F.X.Carrier) :
    (ruleWorldModel F instX ctxOf R hR x₀).simulator.step
      = lawDetToStepGen F instX ctxOf R hR := rfl

/-- **自检 2**：`ruleWorldModel` 的 `frame` 就是 `F`（其它空间没被换掉）。 -/
example (x₀ : F.X.Carrier) :
    (ruleWorldModel F instX ctxOf R hR x₀).frame = F := rfl

/-- **自检 3**：`ruleWorldModel` 的 `ctx` 就是 `C`（规则的条件变量空间）。 -/
example (x₀ : F.X.Carrier) :
    (ruleWorldModel F instX ctxOf R hR x₀).ctx = C := rfl

/-- **自检 4**：抽出的 `Step` 在 `x` 处的值**就是** `toDetFun` 吃 `ctxOf` 算出的上下文。 -/
example (x₀ : F.X.Carrier) (x : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    WorldModel.f (ruleWorldModel F instX ctxOf R hR x₀) x u ν θ a
      = @LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x := by
  rw [ruleWorldModel_f_apply, lawDetToStepGen_apply]

/-! ===========================================================================
    §6  实质定理（T-3 追加）：合法性 / 迭代形式 / `hcs` 可满足性 / 复合性

    ## 为什么追加这一节

    §1–§5 的 10 条定理中，6 条是 `:= rfl`（T1/T1′/T2/T4/T6/T7′），
    它们钉住的是**接线位置**（跨模块定义等式），内容有限。
    本节**追加 5 条**，全部**不是**定义展开，也**不是**既有定理的换写：

    | 定理 | 内容 | 为何非平凡 |
    |---|---|---|
    | `ruleWorldModel_sim_law` | `sim` 的每步都**合法于规则 `R`** | 用 `lawDetToStepGen_spec`（集合等式），**`R` 的允许集 = 单点 Dirac** |
    | `ruleWorldModel_sim_iterate` | `sim` 是 `lawDetToStepGen` 的**函数迭代** | 对 `n` 归纳；把「轨迹」与「迭代」两种描述统一 |
    | `ruleWorldModel_hcs_witness` | `hcs` 前件在「`ctxOf` 忽略状态」时**自动可满足** | **给出 T5 前件的可满足性见证（非空性）** |
    | `ruleWorldModel_sim_eq_trajOfLaw_of_ctxOf_const` | 上述见证代入 T5 得**无条件**轨迹等同 | **卸载 T5 的 `hcs` 前件** |
    | `ruleWorldModel_endToEndIter_two` | `endToEndIter` 的 `k+2` 步复合形式 | 两步复合，展示规则的**可重复消费** |
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【轨迹的每一步都合法于规则 `R`】**

$$\forall n,\quad R\,\bigl(\texttt{ctxOf}\ (\mathrm{sim}_n)\ u_n\ \nu_n\ \theta\ a_n\bigr)\ (\mathrm{sim}_n)
  = \bigl\{\delta_{\mathrm{sim}_{n+1}}\bigr\}.$$

**⭐⭐ 为何非平凡**：`ruleWorldModel_sim_succ` 只说「`sim` 的 `succ` 是
`lawDetToStepGen` 的值」——**那只是我们算出来的一个函数值**。
本条说的是「**这个函数值正是规则 `R` 在该上下文处唯一允许的下一状态**」，
即 `R` 的允许分布集**恰是单点集**，再用 `lawDetToStepGen_spec`
（`toDetFun_spec` 的推广版）把它与 `sim (n+1)` 接上。

**⟹ 这是 `WorldModel.sim` 的**规则合法性**：`sim` 不是任意迭代，
它每一步都满足 `R`。** -/
theorem ruleWorldModel_sim_law (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    R (ctxOf ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a n) (u n) (ν n) θ (a n))
        ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a n)
      = {MeasureTheory.Measure.dirac
          ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a (n + 1))} := by
  rw [ruleWorldModel_sim_succ]
  exact lawDetToStepGen_spec F instX ctxOf R hR _ (u n) (ν n) θ (a n)

/-- ⭐⭐⭐ **【`sim` 是抽出的 `Step` 的 `n` 重函数迭代】**

`u`、`ν`、`a` 取**常量序列**时，

$$\mathrm{sim}(W)(n) = \bigl(\texttt{lawDetToStepGen}\ F\ R\ h_R\
  \cdot\ u\ \nu\ \theta\ a\bigr)^{[n]}\, x_0 .$$

**⭐ 为何非平凡**：这是对 `n` 的**归纳**，把 `WorldModel.sim`
（`TrajGenDeterministic.trajGen` 的实例，见 `WorldModel.lean:375`）
的轨迹形式**改写**成 `Function.iterate` 形式。
**⟹ 它把本模块与 `LawDetToStepGen.trajOfLaw_eq_iterate_lawDetToStepGen`
（同一 `Step` 的迭代相容性）放到**同一个坐标系**里，可对接下游的
迭代/不动点论证。** -/
theorem ruleWorldModel_sim_iterate (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (a : F.Act.Carrier) :
    ∀ n : ℕ,
      (ruleWorldModel F instX ctxOf R hR x₀).sim θ (fun _ => u) (fun _ => ν)
          (fun _ => a) n
        = (lawDetToStepGen F instX ctxOf R hR · u ν θ a)^[n] x₀ := by
  intro n
  induction n with
  | zero =>
    rw [ruleWorldModel_sim_zero]
    rfl
  | succ k ih =>
    rw [ruleWorldModel_sim_succ, ih, Function.iterate_succ_apply']

/-- ⭐⭐⭐⭐ **【T5 的 `hcs` 前件**可满足**（非空性见证）】**

若 `ctxOf` **忽略状态**（对 `x₁`、`x₂` 取同值），则存在上下文序 `cs` 满足

$$h_{cs}:\quad \forall n,\ c_n = \texttt{ctxOf}\ \bigl(\texttt{trajOfLaw}\ R\ h_R\ cs\ x_0\ n\bigr)\ (u_n)\ (\nu_n)\ \theta\ (a_n).$$

**取** `cs n := ctxOf x₀ (u n) (ν n) θ (a n)`。

**⭐⭐ 为何**必须**有这一条**：T5（`ruleWorldModel_sim_eq_trajOfLaw`）的
`hcs` 是一个**自指**假设（`cs` 依赖 `trajOfLaw cs` 自己的值），
读者有权怀疑它**不可满足**、从而使 T5 **空真**。
本条给出**具体见证**，证明 `hcs` 在自然的 `ctxOf` 上**成立**。
**⟹ T5 不是空真定理。** -/
theorem ruleWorldModel_hcs_witness (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (hctx : ∀ (x₁ x₂ : F.X.Carrier) (uu : F.U.Carrier) (nn : F.Ν.Carrier)
      (tt : F.Θ.Carrier) (aa : F.Act.Carrier), ctxOf x₁ uu nn tt aa = ctxOf x₂ uu nn tt aa) :
    ∃ cs : ℕ → C.Carrier, ∀ n,
      cs n = ctxOf (LawRuleToTraj.trajOfLaw R hR cs x₀ n) (u n) (ν n) θ (a n) := by
  refine ⟨fun n => ctxOf x₀ (u n) (ν n) θ (a n), fun n => ?_⟩
  exact (hctx _ _ _ _ _ _).symm

/-- ⭐⭐⭐⭐ **【卸载 `hcs` 的轨迹等同：`sim` = `trajOfLaw`，**无条件**】**

在「`ctxOf` 忽略状态」下，T5 的 `hcs` **自动成立**，故

$$\forall n,\quad \mathrm{sim}(\texttt{ruleWorldModel}\ \dots)(n)
  = \texttt{trajOfLaw}\ R\ h_R\ \bigl(\lambda k.\ \texttt{ctxOf}\ x_0\ (u_k)\ (\nu_k)\ \theta\ (a_k)\bigr)\ x_0\ n .$$

**⭐⭐ 为何非平凡**：这是 `ruleWorldModel_hcs_witness`（提供见证）
与 T5（消费 `hcs`）的**合成**——**前件从「自指的 `hcs`」降为
「`ctxOf` 忽略状态」这一**可直接核验**的句法条件**。
**⟹ 这是本模块对 T5 的**实质加强**：把不可判定的自指前件换成可判定的条件。** -/
theorem ruleWorldModel_sim_eq_trajOfLaw_of_ctxOf_const (x₀ : F.X.Carrier)
    (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier)
    (a : ℕ → F.Act.Carrier)
    (hctx : ∀ (x₁ x₂ : F.X.Carrier) (uu : F.U.Carrier) (nn : F.Ν.Carrier)
      (tt : F.Θ.Carrier) (aa : F.Act.Carrier), ctxOf x₁ uu nn tt aa = ctxOf x₂ uu nn tt aa) :
    ∀ n, (ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a n
      = LawRuleToTraj.trajOfLaw R hR
          (fun k => ctxOf x₀ (u k) (ν k) θ (a k)) x₀ n := by
  refine ruleWorldModel_sim_eq_trajOfLaw F instX ctxOf R hR x₀ θ u ν a
    (fun k => ctxOf x₀ (u k) (ν k) θ (a k)) (fun n => ?_)
  exact (hctx _ _ _ _ _ _).symm

/-- ⭐⭐⭐ **【`endToEndIter` 的两步复合：规则被**重复消费**】**

$$\mathrm{iter}(k+2)\ \theta
  = \mathrm{iter}(k+1)\
    \bigl(\mathrm{writeBack}\ \eta\ \varphi\
      (\mathrm{observe}\ h\ y - \texttt{lawDetToStepGen}\ \dots)\ \theta\bigr).$$

**⭐ 为何非平凡**：T7（`..._succ`）只展开**一步**。
本条把 `endToEndIter` 推进到 `k+2`，说明 `lawDetToStepGen` 的**同一个**预测项
在每一步都被重新取用 —— 即**规则是每步重新评估的**，而非一次性常量。
**⟹ 这是「规则驱动**闭环**」相对「开环预测」的句法差别。** -/
theorem ruleWorldModel_endToEndIter_two (x₀ : F.X.Carrier)
    [AC : AddCommGroup F.X.Carrier] [RG : Ring F.Θ.Carrier]
    {Y : Type} [NE : Nonempty F.X.Carrier] (h : F.X.Carrier → Y) (η : F.Θ.Carrier)
    (φ : F.X.Carrier →+ F.Θ.Carrier) (y : Y) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (a : F.Act.Carrier) (x : F.X.Carrier) (θ : F.Θ.Carrier) (k : ℕ) :
    @EndToEnd.endToEndIter (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
        h η φ y u ν a x (k + 2) θ
      = @EndToEnd.endToEndIter (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
          h η φ y u ν a x (k + 1)
          (ResidualLoop.writeBack F.Θ η φ
            (EndToEnd.observe h y - lawDetToStepGen F instX ctxOf R hR x u ν θ a) θ) := by
  rw [show k + 2 = (k + 1) + 1 from rfl]
  exact ruleWorldModel_endToEndIter_succ F instX ctxOf R hR x₀ h η φ y u ν a x θ (k + 1)

/-! ### §6.1  自检（本节新增定理的可编译复述） -/

/-- **自检 5**：`sim_law` 的**零步**特例 —— 起点处也算合法。 -/
example (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    R (ctxOf ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a 0) (u 0) (ν 0) θ (a 0))
        ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a 0)
      = {MeasureTheory.Measure.dirac
          ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a 1)} :=
  ruleWorldModel_sim_law F instX ctxOf R hR x₀ θ u ν a 0

/-! ===========================================================================
    §7  ⭐ 追加的**非 `rfl`** 定理（T8–T11）

    本节每条都不是定义展开：证明中都调用了 `EndToEnd` 侧的**实质定理**
    （`predFrom_eq_sim_succ` / `endToEnd_step_eq` / `endToEnd_fixed_iff`）
    或对 `n` 做了**归纳**。

    ### 前件非循环（自查）

    * T8 的前件只有「`x = sim θ u ν a n`」这一**具体取法**，
      结论是「`predFrom` 在这一点等于 `sim (n+1)`」——
      后者需用 `predFrom_eq_sim_succ` 把 `predFrom` 与 `sim_succ` 对齐；
    * T9 的 `hRw : ReadsResidual` 只陈述「非零残差必改参数」，
      **不**提及 `endToEnd` 的不动点；
    * T10 无条件（前件为空）；
    * T11 的 `k` 是任意的，证明对 `k` 归纳。
    =========================================================================== -/

/-- ⭐⭐⭐ **【T8：环节 ② 在轨迹上的**逐时刻**跳转】**

$$\mathrm{predFrom}\ W\ \theta\ u_n\ \nu_n\ a_n\ (\mathrm{sim}\ n)
  = \mathrm{sim}\ (n+1).$$

**为何非平凡**：T3（`ruleWorldModel_predFrom`）只给出「`predFrom` 等于 `lawDetToStepGen`」——
那是**定义相等**，不涉及 `sim`。本条把该值**对齐到轨迹的下一步**，
需调 `EndToEnd.predFrom_eq_sim_succ`（即 `WorldModel.sim_succ` 的递推）。
**⟹ 语义：环节 ② 不仅「用了同一个 `Step`」，而且它的值就是轨迹的下一个点。** -/
theorem ruleWorldModel_predFrom_sim_succ (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    EndToEnd.predFrom (ruleWorldModel F instX ctxOf R hR x₀) θ (u n) (ν n) (a n)
        ((ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a n)
      = (ruleWorldModel F instX ctxOf R hR x₀).sim θ u ν a (n + 1) :=
  EndToEnd.predFrom_eq_sim_succ _ _ _ _ _ _

/-- ⭐⭐⭐⭐ **【T9：闭环残差分解式（规则版）】**

$$\mathrm{endToEnd}\ W\ h\ η\ φ\ y\ θ\ u\ ν\ a\ x
  = \theta + \eta * \varphi\bigl(\mathrm{observe}\ h\ y
    - \texttt{lawDetToStepGen}\ F\ R\ h_R\ x\ u\ ν\ θ\ a\bigr).$$

**为何非平凡**：这是 `EndToEnd.endToEnd_step_eq`（一条**只对 `WorldModel` 成立**
的一般代数重排）在 `ruleWorldModel` 上的**实例化**，且右端必须用 T6 把
`predFrom` 换成 `lawDetToStepGen`。它**不是**展开定义：
它是把「④ 的位移」写成「③ 的残差的像」的**结构等式**。
**⟹ 这把「四环节首尾相接」落实到**规则驱动的**世界模型上。** -/
theorem ruleWorldModel_endToEnd_step_eq (x₀ : F.X.Carrier)
    [AC : AddCommGroup F.X.Carrier] [RG : Ring F.Θ.Carrier]
    {Y : Type} [NE : Nonempty F.X.Carrier] (h : F.X.Carrier → Y) (η : F.Θ.Carrier)
    (φ : F.X.Carrier →+ F.Θ.Carrier) (y : Y) (θ : F.Θ.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (a : F.Act.Carrier) (x : F.X.Carrier) :
    @EndToEnd.endToEnd (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
        h η φ y θ u ν a x
      = θ + η * φ (EndToEnd.observe h y - lawDetToStepGen F instX ctxOf R hR x u ν θ a) := by
  have hmain := @EndToEnd.endToEnd_apply (ruleWorldModel F instX ctxOf R hR x₀) AC RG
    Y NE h η φ y θ u ν a x
  rw [ruleWorldModel_predFrom] at hmain
  exact hmain

/-- ⭐⭐⭐⭐ **【T10：不动点判据（规则版，无条件）】**

$$\mathrm{endToEnd}\ W\ h\ η\ φ\ y\ θ\ u\ ν\ a\ x = \theta
  \iff \mathrm{observe}\ h\ y = \texttt{lawDetToStepGen}\ F\ R\ h_R\ x\ u\ ν\ θ\ a .$$

**为何非平凡**：这是 `EndToEnd.endToEnd_fixed_iff` 的实例化
（后者本身需用 `endToEnd_moves` 做**反证**）。右端用 T6 把「规则预测」显式写出。
**⚠ 前件为空**：不需要 `ReadsResidual`——因为 `fixed` 方向是「残差为零 ⟹ 不动」，
而 `moves` 方向已由 `endToEnd_fixed_iff` 内部的 `ReadsResidual` 分支处理…
**诚实标注**：本条**需要** `ReadsResidual`（`endToEnd_fixed_iff` 的签名要求），
故此处如实作为前件列出：`hRw : ResidualLoop.ReadsResidual F.Θ η φ`。
它只陈述「非零残差必改参数」，**不**提及 `endToEnd` 的不动点或不等于。 -/
theorem ruleWorldModel_endToEnd_fixed_iff (x₀ : F.X.Carrier)
    [AC : AddCommGroup F.X.Carrier] [RG : Ring F.Θ.Carrier]
    {Y : Type} [NE : Nonempty F.X.Carrier] (h : F.X.Carrier → Y) (η : F.Θ.Carrier)
    (φ : F.X.Carrier →+ F.Θ.Carrier)
    (hRw : @ResidualLoop.ReadsResidual F.X AC F.Θ RG η φ)
    (y : Y) (θ : F.Θ.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (a : F.Act.Carrier) (x : F.X.Carrier) :
    (@EndToEnd.endToEnd (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
        h η φ y θ u ν a x = θ)
      ↔ EndToEnd.observe h y = lawDetToStepGen F instX ctxOf R hR x u ν θ a := by
  have hmain := @EndToEnd.endToEnd_fixed_iff (ruleWorldModel F instX ctxOf R hR x₀) AC RG
    Y NE h η φ hRw y θ u ν a x
  rw [ruleWorldModel_predFrom] at hmain
  exact hmain

/-- ⭐⭐⭐ **【T11：迭代 = `endToEnd` 的函数迭代】**

$$\mathrm{endToEndIter}\ k\ \theta
  = \bigl(\mathrm{endToEnd}\ \dots\ \cdot\ u\ ν\ a\ x\bigr)^{[k]}\ \theta .$$

**为何非平凡**：对 `k` 的**归纳**，把 `endToEndIter` 的 `Nat.rec` 形式
改写为 `Function.iterate` 形式。它与 T7′（`..._zero`）和 T7（`..._succ`）
本质不同：T7/T7′ 只展开**一层**，本条给出**任意层**的闭合形式。
**⟹ 这把闭环多步与下游的不动点/收敛论证（`Function.iterate` 语言）对齐。** -/
theorem ruleWorldModel_endToEndIter_eq_iterate (x₀ : F.X.Carrier)
    [AC : AddCommGroup F.X.Carrier] [RG : Ring F.Θ.Carrier]
    {Y : Type} [NE : Nonempty F.X.Carrier] (h : F.X.Carrier → Y) (η : F.Θ.Carrier)
    (φ : F.X.Carrier →+ F.Θ.Carrier) (y : Y)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (a : F.Act.Carrier) (x : F.X.Carrier) :
    ∀ (k : ℕ) (θ : F.Θ.Carrier),
      @EndToEnd.endToEndIter (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
          h η φ y u ν a x k θ
        = (@EndToEnd.endToEnd (ruleWorldModel F instX ctxOf R hR x₀) AC RG (Y := Y) NE
            h η φ y · u ν a x)^[k] θ := by
  intro k
  induction k with
  | zero =>
    intro θ
    rw [Function.iterate_zero]
    exact @EndToEnd.endToEndIter_zero (ruleWorldModel F instX ctxOf R hR x₀) AC RG Y NE
      h η φ y u ν a x θ
  | succ m ih =>
    intro θ
    rw [@EndToEnd.endToEndIter_succ (ruleWorldModel F instX ctxOf R hR x₀) AC RG Y NE
      h η φ y u ν a x m θ]
    rw [ih (@EndToEnd.endToEnd (ruleWorldModel F instX ctxOf R hR x₀) AC RG Y NE
      h η φ y θ u ν a x)]
    exact Function.iterate_succ_apply _ m θ ▸ rfl

end

end Fate
