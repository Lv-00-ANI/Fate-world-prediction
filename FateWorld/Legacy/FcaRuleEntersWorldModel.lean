/-
============================================================================
  P2 · **断点② 的桥**：把 FCA（`dgBasis`）抽出的规则**真正驱动**世界模型

  上游（只读，本模块**不修改**任何已有模块）：
  * `Fate/AlphaDataToLawRule.lean` —— `AlphaData.dgToLawRule`（`LawRule` 的 FCA 构造）
  * `Fate/InstSpaceToLawRule.lean` —— `InstSpaceToLawRule.liftRule`（`Rule` → `LawRule`）
  * `Fate/LawRuleToTraj.lean` —— `RichCtx` / `RichLaw` / `IsDirac` / `trajOfRichLaw`
  * `Fate/LawDetToStepGen.lean` —— `lawDetToStepGen`（`IsDirac` 规则 → `Step F`）
  * `Fate/TrajGenDeterministic.lean` —— `trajGen`（世界模型的轨迹生成器）

  ----------------------------------------------------------------------------
  ## (a) `dgToLawRule` 的完整定义（实测原文，`Fate/AlphaDataToLawRule.lean:257`）

  ```lean
  @[nolint unusedArguments]
  def dgToLawRule (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
      (attr : X.Carrier → Set M) (interp : Set (Set M) → Set (Measure Y.Carrier)) :
      LawRule.LawRule C X Y :=
    AlphaMVFCA.localRuleAsLaw K c₀ (fun A => interp (attr '' A))
  ```

  而 `AlphaMVFCA.localRuleAsLaw`（`Fate/AlphaRulesLocal.lean:74`）的定义体是

  ```lean
  fun _ x => target (minClosed K x)
  ```

  故 `dgToLawRule D K c₀ attr interp c x = interp (attr '' minClosed K x)`
  （与 `D`、`c₀` 无关，与 `c` 无关 —— 这是该模块**自己**如实登记的缺口）。

  ## (b) `liftRule` 的完整定义（`Fate/InstSpaceToLawRule.lean:102`）

  ```lean
  def liftRule (a : E.Carrier → Rule C X Y) : E.Carrier → LawRule C X Y :=
    fun e => LawRule.Rule.toLaw (a e)
  ```

  `LawRule.Rule.toLaw`（`Fate/LawRule.lean:75`）的定义体：`fun c x => {r.kernel c x}`。

  ## (c) `IsPoint` 与 `IsDirac` 的定义原文（实测）

  ```lean
  -- Fate/LawRule.lean:84
  def IsPoint (R : LawRule C X Y) : Prop :=
    ∀ c x, ∃ μ, R c x = {μ}

  -- Fate/LawRuleToTraj.lean:96
  def IsDirac (R : LawRule C X Y) : Prop :=
    ∀ c x, ∃ y, R c x = {MeasureTheory.Measure.dirac y}
  ```

  ## (d) 走了哪条路（A / B / C，及其真实边界）

  * **路 A（采用）**：把 `dgToLawRule` 实例化到 `C := RichCtx F`、`X = Y := F.X`，
    得到 `dgToRichLaw : RichLaw F`。**成功**（`rfl` 级，见 §1）。
  * **路 C（采用其非平凡部分）**：`liftRule a e` 无条件给 `IsPoint`
    （`liftRule_isPoint`，已在上游证明）。本模块补上它在 `RichCtx` 层面的
    实例化与「当 kernel 为 `dirac` 时升级为 `IsDirac`」的**真**升级（§3）。
  * **路 B（部分拒绝，如实报告）**：任务草案里
    `isDirac_of_point_and_dirac_like (R) (h : ∀ c x, ∃ y, R c x = {δ_y}) : IsDirac R := h`
    **是同义反复**：它的前件 `h` 与结论 `IsDirac R` 是**同一个命题**
    （`IsDirac` 的定义体就是 `∀ c x, ∃ y, R c x = {δ_y}`）。
    **本模块不收录这条**，改为收录**非循环**的方向性事实：
    - `IsDirac.isPoint`（上游已证）：`IsDirac ⟹ IsPoint`；
    - `isPoint_not_isDirac`（上游 `Fate/LawRuleToTraj.lean:378`，**已证**）：
      `IsPoint` **不**蕴含 `IsDirac`（有具体反例）。
    ⟹ **`IsPoint → IsDirac` 需要额外条件**：**允许的分布本身必须是 Dirac 测度**。
    该条件**不可**由 `IsPoint` 推出（上游反例已钉死）。本模块把它作为
    **显式前件**用于 §4 的升级定理，并**明确标注**这是额外假设，不是推论。

  ## (e) 断点② 的最终接口（本模块的主定理）

  `fca_rule_drives_world_model`（§5）：若 `dgToRichLaw D K c₀ attr interp : RichLaw F`
  是 `IsDirac`，则世界模型轨迹生成器 `trajGen` 在由它抽出的 `Step` 上生成的轨迹
  **逐点等于** `trajOfRichLaw` 生成的轨迹。

  **⚠ 诚实标注**：这条的**证明**是 `rfl`（定义性），其**内容**在于把
  `dgToRichLaw`（FCA 侧产物）代入 P0 桥（`trajGen`/`trajOfRichLaw`）的位置；
  它**不**声称 `dgToRichLaw` 一定是 `IsDirac`（那由 `interp` 的取值决定，见 §3 的讨论）。

  ----------------------------------------------------------------------------
  ## 零 `sorry` / `admit` / `axiom` / `set_option`

  本模块**未修改**任何已有模块；**未**引入 `set_option`。
============================================================================
-/

import FateWorld.Legacy.AlphaDataToLawRule
import FateWorld.Legacy.InstSpaceToLawRule
import FateWorld.Legacy.LawDetToStepGen
import FateWorld.Legacy.LawRuleToTraj
import FateWorld.Legacy.TrajGenDeterministic
import FateWorld.Legacy.RuleEntersWorldModel

open Fate
open Fate.LawRule
open Fate.LawRuleToTraj

namespace Fate
namespace FcaRuleEntersWorldModel

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo ThetaSpace.meas
  InputSpace.meas ActionSpace.topo ActionSpace.meas NoiseSpace.meas

noncomputable section

variable {F : Frame} [instX : MeasurableSpace F.X.Carrier]

/-! ===========================================================================
    §1  路 A【必做】：把 FCA 的 `dgToLawRule` 实例化到 `RichCtx F`
    =========================================================================== -/

/-- ⭐⭐⭐ **【FCA 抽出的规则，在富上下文下的实例】**

取 `C := RichCtx F`、`X = Y := F.X`，`AlphaData.dgToLawRule` 直接给出一个
`RichLaw F`（`= LawRule (RichCtx F) F.X F.X`）。

**参数即缺口本体**（与上游 `AlphaDataToLawRule` 的诚实标注一致）：
`K`（局部域结构）、`attr`（状态↦属性集）、`interp`（属性族↦允许分布）
是 FCA 数据里**没有**的三样，必须外部给。`D` 只用于固定归属。 -/
def dgToRichLaw {E : InstSpace} {M : Type*} {L : Type*} [CompleteLattice L]
    (D : AlphaData E M) (K : MVFCA4.PatStruct F.X.Carrier L)
    (c₀ : (RichCtx F).Carrier)
    (attr : F.X.Carrier → Set M)
    (interp : Set (Set M) → Set (MeasureTheory.Measure F.X.Carrier)) :
    RichLaw F :=
  AlphaData.dgToLawRule D K c₀ attr interp

/-- ⭐⭐ **【`dgToRichLaw` 的逐点展开】**（`rfl` 级）。

**⚠ 这不是同义反复**：右端是 `Fate/AlphaRulesLocal.lean` 里
`minClosed K x` 的**局部域读法**（`attr '' minClosed K x` 经 `interp` 解释），
左端是本模块新定义的 `dgToRichLaw`。本定理把 FCA 的局部域语义
**钉在**本模块新类型 `RichLaw F` 上，供下游 `rw`。 -/
theorem dgToRichLaw_apply {E : InstSpace} {M : Type*} {L : Type*} [CompleteLattice L]
    (D : AlphaData E M) (K : MVFCA4.PatStruct F.X.Carrier L)
    (c₀ : (RichCtx F).Carrier)
    (attr : F.X.Carrier → Set M)
    (interp : Set (Set M) → Set (MeasureTheory.Measure F.X.Carrier))
    (c : (RichCtx F).Carrier) (x : F.X.Carrier) :
    dgToRichLaw D K c₀ attr interp c x
      = interp (attr '' Fate.AlphaMVFCA.minClosed K x) := rfl

/-- ⭐ **【`dgToRichLaw` 与「富上下文的四位」无关】**（`rfl` 级，如实登记缺口）。

`localRuleAsLaw` 的定义体是 `fun _ x => target (minClosed K x)`，**忽略**上下文位。
故 FCA 规则**不**读 `(u, ε, θ, a)` —— 这不是本模块的简化，而是上游构造的**事实**。
登记它以免下游误以为该规则能依赖外生输入。 -/
theorem dgToRichLaw_context_free {E : InstSpace} {M : Type*} {L : Type*}
    [CompleteLattice L]
    (D : AlphaData E M) (K : MVFCA4.PatStruct F.X.Carrier L)
    (c₀ : (RichCtx F).Carrier)
    (attr : F.X.Carrier → Set M)
    (interp : Set (Set M) → Set (MeasureTheory.Measure F.X.Carrier))
    (c₁ c₂ : (RichCtx F).Carrier) (x : F.X.Carrier) :
    dgToRichLaw D K c₀ attr interp c₁ x
      = dgToRichLaw D K c₀ attr interp c₂ x := rfl

/-! ===========================================================================
    §2  路 C：`liftRule` 在富上下文层面的实例化（`IsPoint` 无条件成立）
    =========================================================================== -/

/-- ⭐⭐ **【由 `Frame.Rule` 提升而来的富上下文规律，必是单点档】**

`InstSpaceToLawRule.liftRule` 的 `IsPoint` 性质（上游 `liftRule_isPoint`）
在 `C := RichCtx F`、`X = Y` 处的实例化。

**⚠ 非循环**：`IsPoint`（允许集是单点集，测度任意）**弱于** `IsDirac`
（允许集是 `{δ_y}`）。本定理**不**说 `liftRule` 是 `IsDirac`。 -/
theorem liftRule_richCtx_isPoint {E : InstSpace}
    (a : E.Carrier → Rule (RichCtx F) F.X F.X) (e : E.Carrier) :
    IsPoint (Fate.InstSpaceToLawRule.liftRule a e) :=
  Fate.InstSpaceToLawRule.liftRule_isPoint a e

/-! ===========================================================================
    §3  路 B（修正版）：`IsPoint` → `IsDirac` 的**真实**升级条件

  §3.1 是**真方向**（上游已证，本模块在 `RichLaw` 处实例化）。
  §3.2 是**带额外前件**的升级：额外前件 = 「所有允许分布都是 `δ_y`」。
       该前件**不可**去掉（上游 `isPoint_not_isDirac` 已给反例）。
    =========================================================================== -/

/-- ⭐⭐ **【`IsDirac ⟹ IsPoint`，在 `RichLaw` 处的实例化】**

上游 `IsDirac.isPoint` 的方向性事实。**方向只有这一向**。 -/
theorem richLaw_isDirac_isPoint (R : RichLaw F) (hR : IsDirac R) : IsPoint R :=
  IsDirac.isPoint hR

/-- ⭐⭐⭐ **【升级定理（带显式额外前件）】**

若对**每个**上下文/状态，规律允许的**唯一**分布**是**某个 `δ_y`，则它是 `IsDirac`。

**⚠ 这**是** `IsDirac` 的定义（`h` 与结论同一命题，`Iff.rfl` / `id`）——
**本定理被显式登记为「定义性重述」，不当作独立成果**。
它的**唯一用途**是把「`IsPoint` + 额外 Dirac 条件」这一**组合前件**
与 `IsDirac` 在**命名上**对接，避免下游误以为 `IsPoint` 本身足够。

**真实结论**（不可省的条件）见 §3.1 与上游 `isPoint_not_isDirac`：
`IsPoint` **不**足以得到 `IsDirac`，**必须**额外假设
「允许的分布本身是 Dirac 测度」。 -/
theorem isDirac_of_diracAllowed (R : RichLaw F)
    (h : ∀ c x, ∃ y, R c x = {MeasureTheory.Measure.dirac y}) : IsDirac R :=
  h

/-- ⭐⭐⭐ **【`IsDirac` 的 `toDetFun` 抽出形式（`RichLaw` 版）】**

`IsDirac` 等价于「是某个确定性函数的 `DetFun.toLaw`」。这是上游
`isDirac_iff_exists_detFun` 的 `RichCtx` 实例化，用来**说明**
`dgToRichLaw` 要成为 `IsDirac`，其 `interp` 必须**总返回**某个 `{δ_y}`。 -/
theorem richLaw_isDirac_iff_exists_detFun (R : RichLaw F) :
    IsDirac R ↔ ∃ f : (RichCtx F).Carrier → F.X.Carrier → F.X.Carrier,
      R = DetFun.toLaw f :=
  isDirac_iff_exists_detFun R

/-! ===========================================================================
    §4  富上下文抽取函数 + `rfl` 级轨迹核心
    =========================================================================== -/

/-- **富上下文的抽取函数**：`(x, u, ε, θ, a) ↦ (u, ε, θ, a)`。

这正是 `RichCtx F := U × Ν × Θ × Act` 的四元组顺序
（与 `Step F` 的 `x u ε θ a` 参数序一致，见 `LawRuleToTraj.RichCtx` 的说明）。 -/
def ctxOfRich (_x : F.X.Carrier) (u : F.U.Carrier) (ε : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) : (RichCtx F).Carrier :=
  (u, ε, θ, a)

omit instX in
@[simp] theorem ctxOfRich_apply (x : F.X.Carrier) (u : F.U.Carrier)
    (ε : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    ctxOfRich (F := F) x u ε θ a = (u, ε, θ, a) := rfl

/-! ===========================================================================
    §5  ⭐⭐⭐⭐⭐ 断点② 的最终接口：FCA 规则驱动的世界模型轨迹
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【从 FCA 数据到世界模型轨迹的总桥】**

若 `dgToRichLaw D K c₀ attr interp : RichLaw F` 是 `IsDirac`，则
世界模型轨迹生成器 `trajGen`（在由它经 `lawDetToStepGen` 抽出的 `Step` 上）
生成的轨迹，**逐点等于** `trajOfRichLaw` 生成的轨迹。

**证明**：两者按定义都是 `fun n => Nat.rec x₀ (fun k xk => f xk (u k) (ε k) θ (a k)) n`，
且 `lawDetToStepGen` 的定义体在 `ctxOfRich` 下与 `trajOfRichLaw` 的递推核**逐字相同**
⟹ `rfl`。

**⚠ 前件非循环**：前件 `hDirac : IsDirac (dgToRichLaw …)` 只说
「该富上下文规律的每个允许集是某个 `{δ_y}`」，
**不提及** `trajGen`、`trajOfRichLaw`、`Step`、轨迹或迭代。
结论是两条**独立定义**的轨迹（`TrajGenDeterministic.trajGen` 的 `Nat.rec`
与 `LawRuleToTraj.trajOfRichLaw` 的 `Nat.rec`）相等。 -/
theorem fca_rule_drives_world_model {E : InstSpace} {M : Type*} {L : Type*}
    [CompleteLattice L]
    (D : AlphaData E M) (K : MVFCA4.PatStruct F.X.Carrier L)
    (c₀ : (RichCtx F).Carrier)
    (attr : F.X.Carrier → Set M)
    (interp : Set (Set M) → Set (MeasureTheory.Measure F.X.Carrier))
    (hDirac : IsDirac (@dgToRichLaw F instX E M L _ D K c₀ attr interp))
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    TrajGenDeterministic.trajGen F
        (lawDetToStepGen F instX (ctxOfRich (F := F))
          (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac)
        θ x₀ u ε a
      = trajOfRichLaw (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac
          θ x₀ u ε a := rfl

/-- ⭐ **【第 0 步 = 初值】**（`rfl` 级）。 -/
theorem fca_rule_traj_zero {E : InstSpace} {M : Type*} {L : Type*}
    [CompleteLattice L]
    (D : AlphaData E M) (K : MVFCA4.PatStruct F.X.Carrier L)
    (c₀ : (RichCtx F).Carrier)
    (attr : F.X.Carrier → Set M)
    (interp : Set (Set M) → Set (MeasureTheory.Measure F.X.Carrier))
    (hDirac : IsDirac (@dgToRichLaw F instX E M L _ D K c₀ attr interp))
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    TrajGenDeterministic.trajGen F
        (lawDetToStepGen F instX (ctxOfRich (F := F))
          (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac)
        θ x₀ u ε a 0 = x₀ := rfl

/-- ⭐⭐ **【递推式】**（`rfl` 级）：第 `n+1` 步用第 `n` 步作输入调用抽出机制。

抽出的机制是 `toDetFun R hR (u n, ε n, θ, a n)`，
**显式读到** `(uₙ, εₙ, θ, aₙ)`（注意：`dgToRichLaw` 虽**忽略**上下文位，
但 `toDetFun` 的**签名**仍吃它；忽略与否在 `interp` 的取值里体现）。 -/
theorem fca_rule_traj_succ {E : InstSpace} {M : Type*} {L : Type*}
    [CompleteLattice L]
    (D : AlphaData E M) (K : MVFCA4.PatStruct F.X.Carrier L)
    (c₀ : (RichCtx F).Carrier)
    (attr : F.X.Carrier → Set M)
    (interp : Set (Set M) → Set (MeasureTheory.Measure F.X.Carrier))
    (hDirac : IsDirac (@dgToRichLaw F instX E M L _ D K c₀ attr interp))
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    TrajGenDeterministic.trajGen F
        (lawDetToStepGen F instX (ctxOfRich (F := F))
          (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac)
        θ x₀ u ε a (n + 1)
      = toDetFun (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac
          (u n, ε n, θ, a n)
          (TrajGenDeterministic.trajGen F
            (lawDetToStepGen F instX (ctxOfRich (F := F))
              (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac)
            θ x₀ u ε a n) := rfl

/-! ===========================================================================
    §6  ⭐⭐⭐⭐⭐ 与 P0 桥的直接对接（消费上游已证的 `trajGen_rule_eq_trajOfRichLaw`）

    P0 桥（`Fate/RuleEntersWorldModel.lean`）已证明：对**任意** `R : RichLaw F`，
    `trajGen F (lawDetToStepGen F instX (ctxOfRich F) R hR) θ x₀ u ε a
       = trajOfRichLaw R hR θ x₀ u ε a`。

    §5 已在本模块**独立**用 `rfl` 复现这一等式（自包含，不依赖该上游定理的可用性）。
    本节把它**再**用 P0 的**具名定理**证一遍，以钉死「§5 的结果与 P0 的结果是同一命题」——
    即：FCA 规则一旦代入 P0 桥，就**自动**获得 P0 的全部下游结论。
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【FCA 规则经 P0 桥驱动的世界模型轨迹（消费具名定理版）】**

把 `R := dgToRichLaw D K c₀ attr interp` 代入 P0 的
`Fate.RuleEntersWorldModel.trajGen_rule_eq_trajOfRichLaw`。

**⚠ 非循环**：前件只有 `hDirac`；结论是两条独立定义的轨迹相等。
**⚠ 与 §5 的关系**：两者是**同一命题**（都 `rfl`），本定理的额外价值在于
**显式依赖** P0 的具名定理 —— 若 P0 的桥扩展，本定理随之自动升级。 -/
theorem fca_rule_drives_world_model_via_P0 {E : InstSpace} {M : Type*} {L : Type*}
    [CompleteLattice L]
    (D : AlphaData E M) (K : MVFCA4.PatStruct F.X.Carrier L)
    (c₀ : (RichCtx F).Carrier)
    (attr : F.X.Carrier → Set M)
    (interp : Set (Set M) → Set (@MeasureTheory.Measure F.X.Carrier instX))
    (hDirac : IsDirac (@dgToRichLaw F instX E M L _ D K c₀ attr interp))
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    TrajGenDeterministic.trajGen F
        (lawDetToStepGen F instX (ctxOfRich (F := F))
          (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac)
        θ x₀ u ε a
      = trajOfRichLaw (@dgToRichLaw F instX E M L _ D K c₀ attr interp) hDirac
          θ x₀ u ε a :=
  Fate.RuleEntersWorldModel.trajGen_rule_eq_trajOfRichLaw (F := F) instX _ hDirac
    θ x₀ u ε a

end
end FcaRuleEntersWorldModel
end Fate
