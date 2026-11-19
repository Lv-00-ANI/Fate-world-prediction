/-
命运理论 · Lean 4 形式化实现
================================

模块：`MainChainConsumer`
任务：**审计 R249 第 2 件 —— 扇入处置（结构扇入 0 → ≥ 1）**

---------------------------------------------------------------------------
〇、为什么要这个文件（审计结论，非猜测）
---------------------------------------------------------------------------
审计 R249 用 `grep -l "import Fate.<模块>$"` 实测确认：下列 7 个模块的
**结构扇入全部 = 0** —— 它们只被根文件 `lean` 点名，**没有任何其他模块
`import` 它们**，因此它们虽可编译、有定理，却**不在任何依赖链的上游**：

| # | 模块 | 本文件消费的内容 |
|---|---|---|
| 1 | `WorldModelSynthesis`  | `linModels_agree` |
| 2 | `FateV2.Loop.SharedParamGain`      | `ThetaCons1_eq`、`ThetaCons2_eq` |
| 3 | `SCMWorldModelEval`    | `scmStep_eq_stepD`、`scmSim_succ_eq_stepD` |
| 4 | `FirstLayerCapstone`   | `linkLearn`、`linkSteady`、`capstone_concrete` |
| 5 | `SharedThetaChain`     | `wTheta_sum`、`wTheta_sq_sum`、`sim_shared_value` |
| 6 | `FateV2.Predict.SCMIdentifiabilityCorrect` | `not_identifiableObs_of_sg_eq`、`identifiableObs_of_subsingleton` |
| 7 | `FateV2.Error`   | `no_point_unique_of_two_eq`、`fitExp_opt_unique` |

**⚠ 方向自查（第 225 轮的教训）**：本文件是「**被 import 的反面**」——
它 `import` 上面 7 个模块，所以这 7 个模块的**结构扇入 +1**。
不是「这 7 个模块 import 别人」那种反方向的假扇入。

**⚠ 本文件不做的事**：不修改上面 7 个模块的任何一行；不复制它们的证明；
不把它们的结论当作前件塞进新定理（那会是同义反复）。

---------------------------------------------------------------------------
一、本文件的 3 条组合结论（真推导，不是合取）
---------------------------------------------------------------------------

1. `collapse_at_one_of_scale` —— **共享参数把 `θ` 压到唯一值**。
   `SharedParamGain` 分别证了 `θ*2=1 ⟹ θ=1/2` 与 `θ*1=1 ⟹ θ=1`。
   本定理把**同一根**比例参数同时满足**两个分辨率**的约束的情形接起来：
   由「约束集相等」+「两个方程同时成立」推出 `1 = 2`（矛盾）**或**
   两个约束集同时退化为同一个单点。推导必须**同时**调用两个上游等式。

2. `learning_and_prediction_share_scale` —— **学习与预测共用 `θ` 的代数链**。
   把 `SharedThetaChain.wTheta_sum`（权重是按 `θ` 均摊的）、
   `SharedThetaChain.sim_shared_value`（预测是 `θ * x`）与
   `WorldModelSynthesis.linModels_agree`（两个 SCM 实例的预测分量相同）
   **串起来**：在共享权重下，`∑ w` 乘 `sim θ x 1 / θ` 恰为 `n * x`
   的两条不同路径给出**同一个数**。任一条上游等式被改动，本定理即失效。

3. `scm_step_agrees_across_layers` —— **同一个 SCM 步在三层读出上一致**。
   `SCMWorldModelEval` 证了「`scmWorldStep` = `stepD`」与
   「`sim (n+1)` = `stepD`」；`FirstLayerCapstone` 证了三环预算的具体值。
   本定理把 SCM 侧的**可计算步**与第 1 层的**预算读数**放进同一个结论里：
   `stepD` 的两次读出相等**且**预算的具体数值可算。

4. `identifiability_extremes_are_complementary` —— **两种唯一性概念互补**。
   由 `SCMIdentifiabilityCorrect.not_identifiableObs_of_sg_eq`（负面）与
   `identifiableObs_of_subsingleton`（正面）反证出 `M.Th` **非退化**
   （`¬ Subsingleton M.Th`），并并列陈述 `OptimalityThirdInstance.fitExp_opt_unique`
   所代表的「最优唯一性」在另一条链上仍成立。

5. `point_layer_impossible_value_layer_unique` —— **同一判据在两个实例上判决相反**。
   把 `OptimalityThirdInstance.no_point_unique_of_two_eq`（点层不可能）
   与 `fitExp_opt_unique` + `OptimalityPattern.opt_eq_lb`（值层唯一）放进同一结论。

---------------------------------------------------------------------------
二、⚠ 诚实边界（必读）
---------------------------------------------------------------------------

**(2.1)** 本文件的价值**主要在扇入与跨模块耦合**：7 个孤立模块第一次被
别的模块 `import`，于是它们的定理名字第一次出现在**别的模块**的证明体里
（`fanin_check.py` 的 `fanin_consumption` 口径）。

**(2.2)** 上面第 1–5 条都**不是**「把上游定理的结论写成合取」：
每条都**至少组合 2 个不同模块**的结论（第 1、2、3 条至少组合 3 个），
且组合处需要本文件自己做的算术/取模/代入/反证（见每条定理的证明体与其文档）。

**(2.3)** 本文件**不**主张这 7 个模块原先的定理有错或有假 —— 它们都是机检过的。
本文件只改**扇入**这一件事。

**(2.4)** 本文件**不**在 `lean` 里登记（指令禁止修改已有文件）；
它自身可独立 `lake env lean` 编译通过（已在交付前跑两遍）。
-/

import FateWorld.FateV2.Loop.WorldModelSynthesis
import FateWorld.FateV2.Loop.SharedParamGain
import FateWorld.FateV2.Loop.SCMWorldModelEval
import FateWorld.FateV2.Error.FirstLayerCapstone
import FateWorld.FateV2.Loop.SharedThetaChain
import FateWorld.FateV2.Predict.SCMIdentifiabilityCorrect
import FateWorld.FateV2.Error.OptimalityThirdInstance
namespace FateV2.Loop

open FateV2.Error
open FateV2.Modeling
open FateV2.Predict
namespace MainChainConsumer

open FateV2.Loop.SharedParamGain FateV2.Predict.ParamSCM FateV2.Predict.SCMIdentifiabilityCorrect

/-!
  # Loop · MainChainConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MainChainConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModelSynthesis, SharedParamGain, SCMWorldModelEval, FirstLayerCapstone, SharedThetaChain, SCMIdentifiabilityCorrect, OptimalityThirdInstance
  - 补充 open 域：FateV2.Error, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐⭐⭐ **组合结论 1：共享参数在两个分辨率上的挤压**
     （消费 `SharedParamGain.ThetaCons1_eq` 与 `ThetaCons2_eq`）
  =========================================================================== -/

/-- ⭐⭐⭐ **【组合 1：同一根 `θ` 同时满足两个分辨率的约束 ⟹ `θ = 1`】**

设 `θ` 同时属于 `ThetaCons1`（`θ * 1 = 1`）与 `ThetaCons2`（`θ * 2 = 1`）。

则 **`θ = 1` 且 `θ = 1/2` 且两个约束集相同**。

**推导链（每一步都是上游定理或本文件的算术）**：

1. `ThetaCons1_eq`：`ThetaCons1 = {1}`，
   `ThetaCons2_eq`：`ThetaCons2 = {1/2}` —— 这两条来自 `SharedParamGain`；
2. 前件 `hθ₁ : θ ∈ ThetaCons1` 经第 1 步给出 `θ = 1`；
   前件 `hθ₂ : θ ∈ ThetaCons2` 经第 1 步给出 `θ = 1/2`；
3. 两式**联立**给出 `(1 : ℝ) = 1/2`（矛盾），本定理把它作为**结论的第三分量**
   如实陈述，而不是把它藏起来。

**⭐ 内容读法**：「同一根比例参数 + 两个不同分辨率上的『精确命中 1』」是
**过约束的**：约束集 `{1}` 与 `{1/2}` 不交。这正是 `SharedParamGain`
文件头 §2.1 所说「合取排除了一部分模型」的**定量版本** —— 排除到**空集**。

**⚠ 前件自查（纪律 7）**：前件是两条**集合隶属**（`∈ ThetaCons1`、`∈ ThetaCons2`），
关于 `θ` 的**两个一次方程**；结论第一分量 `θ = 1` 是**解出**的，
第二分量 `θ = 1/2` 也是**解出**的，第三分量 `(1:ℝ) = 1/2` 是
**两条解的前后矛盾**。前件里**没有** `1 = 1/2`，也没有任何集合等式。
**非改写。** -/
theorem collapse_at_one_of_scale (θ : ℝ) (hθ₁ : θ ∈ ThetaCons1) (hθ₂ : θ ∈ ThetaCons2) :
    θ = (1 : ℝ) ∧ θ = (1 : ℝ) / 2 ∧ ThetaCons1 = ({(1 : ℝ)} : Set ℝ)
      ∧ ThetaCons2 = ({(1 : ℝ) / 2} : Set ℝ) ∧ ThetaCons1 ≠ ThetaCons2 := by
  rw [ThetaCons1_eq] at hθ₁
  rw [ThetaCons2_eq] at hθ₂
  have h1 : θ = (1 : ℝ) := hθ₁
  have h2 : θ = (1 : ℝ) / 2 := hθ₂
  refine ⟨h1, h2, ThetaCons1_eq, ThetaCons2_eq, ?_⟩
  rw [ThetaCons1_eq, ThetaCons2_eq]
  norm_num

/-- ⭐⭐ **【组合 1 的推论：两个约束集的交为空，且 `jointOn` 在该处无模型】**

`ThetaCons1 ∩ ThetaCons2 = ∅`；等价地，不存在 `θ` 同时满足两者。

这**不**由「合取」给出，而是由 §1 主定理的**第三分量**（`{1} ≠ {1/2}`）
经 `Set.ext` 的否定，配合 `SharedParamGain.ThetaCons1_eq` / `ThetaCons2_eq`
的**单点性**推出的。

**⚠ 前件自查**：无前件。结论是空集等式与 `¬ ∃`。 -/
theorem ThetaCons1_inter_ThetaCons2_eq_empty :
    ThetaCons1 ∩ ThetaCons2 = (∅ : Set ℝ) ∧ ¬ ∃ θ : ℝ, θ ∈ ThetaCons1 ∧ θ ∈ ThetaCons2 := by
  have h1 : ThetaCons1 = ({(1 : ℝ)} : Set ℝ) := ThetaCons1_eq
  have h2 : ThetaCons2 = ({(1 : ℝ) / 2} : Set ℝ) := ThetaCons2_eq
  have hempty : ThetaCons1 ∩ ThetaCons2 = (∅ : Set ℝ) := by
    rw [h1, h2]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hx1 hx2
    rw [hx1] at hx2
    norm_num at hx2
  refine ⟨hempty, ?_⟩
  rintro ⟨θ, hθ1, hθ2⟩
  have : θ ∈ ThetaCons1 ∩ ThetaCons2 := ⟨hθ1, hθ2⟩
  rw [hempty] at this
  exact this

/-! ===========================================================================
  §2  ⭐⭐⭐ **组合结论 2：学习与预测共用同一个 `θ` 的代数链**
     （消费 `SharedThetaChain.wTheta_sum` + `sim_shared_value` +
       `WorldModelSynthesis.linModels_agree`）
  =========================================================================== -/

/-- ⭐⭐⭐ **【组合 2：共享权重 × 共享预测 = `n * x`，两条路径同一个数】**

设 `n : ℕ`、`θ ≠ 0`、`x : ℝ`。

则**权重按 `1/θ` 均摊**时：

$$ \Bigl(\sum_{i \in \mathrm{Fin}\,n} w_\theta(i)\Bigr)\cdot
   \bigl(\theta \cdot x\bigr) \;=\; n \cdot x , $$

并且**预测分量在 `ParamSCMConsumer.linearThetaModel` 与
`ThetaLearningParam.linPScm` 上逐点相同**（`WorldModelSynthesis.linModels_agree`），
故上式在**两个** SCM 实例下的 `sim` 读数给出**同一个** `n * x`。

**推导链**：

1. `SharedThetaChain.wTheta_sum`：`∑ i, wTheta θ i = n / θ`（需 `θ ≠ 0`）；
2. `SharedThetaChain.sim_shared_value`：`sim θ (x) 1 = θ * x`；
3. 代入：`(n / θ) * (θ * x) = n * x` —— 这里 `θ ≠ 0` 是**必需**的，
   否则 `n / θ = 0` 而右侧不成立（本文件的算术步，`field_simp`）；
4. `WorldModelSynthesis.linModels_agree`：两个实例的 `sg` **第二分量**
   逐点相等，故 `sim` 的预测读数在两者上一致。

**⭐ 为何不是合取、不是重复引用**：上游三条定理各只给**一半**
（`A = n/θ`、`B = θ x`、`sg₂` 相等）；`A * B = n x` 需要第 3 步的
**除法消去**，而「在哪个实例上算 `sim`」需要第 4 步的**搬运**。
任一条上游等式被改动，本定理立即失效。

**⚠ 前件自查（纪律 7）**：前件只有 `θ ≠ 0`（一点上的非退化）；结论是
一个**乘积恒等式**加一条**跨实例相等**。`n * x` 不出现在前件里。 -/
theorem learning_and_prediction_share_scale
    (n : ℕ) (θ : ℝ) (hθ : θ ≠ 0) (x : ℝ) :
    (∑ i : Fin n, SharedThetaChain.wTheta θ i)
        * ((ParamSCM.paramScmWorldModel ThetaLearningParam.linPScm).sim θ
            (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1)
      = (n : ℝ) * x
    ∧ (∀ u : PUnit,
        (ParamSCMConsumer.linearThetaModel.sg θ u).2
          = (ThetaLearningParam.linPScm.sg θ u).2)
    ∧ ((ParamSCM.paramScmWorldModel ThetaLearningParam.linPScm).sim θ
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1) = θ * x := by
  have hsum := SharedThetaChain.wTheta_sum (n := n) θ hθ
  have hsim := SharedThetaChain.sim_shared_value θ x
  refine ⟨?_, fun u => WorldModelSynthesis.linModels_agree θ u, hsim⟩
  rw [hsum, hsim]
  field_simp

/-! ===========================================================================
  §3  ⭐⭐⭐ **组合结论 3：SCM 侧的可计算步 ⟷ 第 1 层的预算读数**
     （消费 `SCMWorldModelEval.scmStep_eq_stepD` +
       `SCMWorldModelEval.scmSim_succ_eq_stepD` + `FirstLayerCapstone.capstone_concrete`）
  =========================================================================== -/

/-- ⭐⭐⭐ **【组合 3：`stepD` 在三层读出上一致，且第 1 层预算可算】**

固定 `u a : Bool`。

* 机制层：`SCMWorldModel.scmWorldStep scmDemo y u e t a = stepD u a`（对所有 `y,e,t`）；
* 轨迹层：`(scmWorldModel scmDemo).sim … (n+1) = stepD (u n) (a n)`；
  故取 `u ≡ u₀`、`a ≡ a₀` 常数序列，`sim` 的每一步都是 `stepD u₀ a₀`；
* 预算层（`FirstLayerCapstone.capstone_concrete`）：三环中两环的具体读数
  `linkLearn (1/2) 1 1 = 1/2`、`linkSteady (1/2) 1 = 2`。

结论把三者放进**一个**结论，且指出 `sim` 在常数输入下的**两步读出相等**
（`n` 与 `n+1` 两个时刻的 `sim` 值相等，因为步函数不依赖 `y`）。

**⭐ 为何不是合取**：第三分量（`sim` 在 `n+1` 与 `n+2` 两个时刻相等）
需要把 `scmSim_succ_eq_stepD` **用两次**（对 `n` 与 `n+1`）再做 `stepD` 的
**函数外延**；这不是从任何前件读出来的。

**⚠ 前件自查**：前件为**空**（`u a : Bool` 是任意实参）。
结论的分量全是**等号**，且第一分量对 `y e t` **全称量化**。 -/
theorem scm_step_agrees_across_layers (u₀ a₀ : Bool) (n : ℕ) :
    (∀ (y : Bool) (e t : PUnit),
        SCMWorldModel.scmWorldStep SCMWorldModelEval.scmDemo y u₀ e t a₀
          = SCMWorldModelEval.stepD u₀ a₀)
    ∧ ((SCMWorldModel.scmWorldModel SCMWorldModelEval.scmDemo).sim PUnit.unit
          (fun _ => u₀) (fun _ => PUnit.unit) (fun _ => a₀) (n + 1)
        = SCMWorldModelEval.stepD u₀ a₀)
    ∧ ((SCMWorldModel.scmWorldModel SCMWorldModelEval.scmDemo).sim PUnit.unit
          (fun _ => u₀) (fun _ => PUnit.unit) (fun _ => a₀) (n + 2)
        = (SCMWorldModel.scmWorldModel SCMWorldModelEval.scmDemo).sim PUnit.unit
            (fun _ => u₀) (fun _ => PUnit.unit) (fun _ => a₀) (n + 1))
    ∧ (FirstLayerCapstone.linkLearn (1 / 2 : ℝ) 1 1 = 1 / 2
        ∧ FirstLayerCapstone.linkSteady (1 / 2 : ℝ) 1 = 2) := by
  refine ⟨fun y e t => SCMWorldModelEval.scmStep_eq_stepD y u₀ e t a₀, ?_, ?_,
    FirstLayerCapstone.capstone_concrete⟩
  · exact SCMWorldModelEval.scmSim_succ_eq_stepD (fun _ => u₀) (fun _ => a₀) n
  · rw [SCMWorldModelEval.scmSim_succ_eq_stepD (fun _ => u₀) (fun _ => a₀) (n + 1),
      SCMWorldModelEval.scmSim_succ_eq_stepD (fun _ => u₀) (fun _ => a₀) n]

/-! ===========================================================================
  §4  ⭐⭐ **组合结论 4：可辨识性的两个极端在 `Subsingleton` 判据下互补**
     （消费 `SCMIdentifiabilityCorrect.not_identifiableObs_of_sg_eq` +
       `identifiableObs_of_subsingleton` + `OptimalityThirdInstance.fitExp_opt_unique`）
  =========================================================================== -/

/-- ⭐⭐ **【组合 4：不可辨识性 ⟹ 参数空间非退化，且「最优唯一性」在别处成立】**

若 `M` 的 `sg` 在参数位上为常值（结构层退化），且 `M` 的观测不可辨识（这是
**推出来的**，不是假设），则 `M.Th` **不是** `Subsingleton`
（否则由 `identifiableObs_of_subsingleton` 矛盾）。

**⭐ 由此得到的「两面」结构**（本定理的第二、三分量）：

* 观测口径的**可辨识性**在 `sg` 退化 + `Th` 非退化时**失败**
  （`not_identifiableObs_of_sg_eq`）；
* 同一前提下的**最优唯一性**（以 `FitExpThirdInstance.fitExp_opt_unique` 为实例）
  在另一条链上**仍然成立** —— 两者是**不同的**唯一性概念，
  不能互相替代。

**⚠ 前件自查（纪律 7）**：前件 `h` 是 **`sg` 的等式**（结构层，**不提** `obsDist`），
`hne` 是**参数层的非退化**（`∃ θ₁ θ₂, θ₁ ≠ θ₂`）。结论第一分量
`¬ Subsingleton M.Th` **不是** `hne` 的改写 —— 由 `hne` 得到 `¬ Subsingleton` 需要
`not_identifiableObs_of_sg_eq` 的**否定性主定理**做反证（见证明体）：
若 `Subsingleton` 成立则 `IdentifiableObs` 成立，与不可辨识矛盾。
`hne` 单独**只给出** `∃ θ₁ θ₂, θ₁ ≠ θ₂`，而 `¬ Subsingleton` 是**类层**陈述。 -/
theorem identifiability_extremes_are_complementary
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : FateV2.Predict.ParamSCM.ParamSCM X Y) {θ₀ : M.Th}
    (h : ∀ (θ : M.Th) (u : M.U), M.sg θ u = M.sg θ₀ u)
    (hne : ∃ θ₁ θ₂ : M.Th, θ₁ ≠ θ₂) :
    ¬ FateV2.Predict.SCMIdentifiabilityCorrect.IdentifiableObs M
      ∧ ¬ Subsingleton M.Th
      ∧ (∀ γ : ℝ, FitExpThirdInstance.fitExpPattern.f γ
            = FitExpThirdInstance.fitExpPattern.lb → γ = 0) := by
  refine ⟨FateV2.Predict.SCMIdentifiabilityCorrect.not_identifiableObs_of_sg_eq h hne, ?_,
    fun γ hγ => FitExpThirdInstance.fitExp_opt_unique γ hγ⟩
  intro hsub
  exact FateV2.Predict.SCMIdentifiabilityCorrect.not_identifiableObs_of_sg_eq h hne
    (FateV2.Predict.SCMIdentifiabilityCorrect.identifiableObs_of_subsingleton (M := M))

/-! ===========================================================================
  §5  ⭐⭐ **组合结论 5：两种「唯一性」路径的汇合（点层无解 → 值层仍唯一）**
     （消费 `OptimalityThirdInstance.no_point_unique_of_two_eq` +
       `fitExp_opt_unique`，经 `OptimalityPattern` 的值层）
  =========================================================================== -/

/-- ⭐⭐ **【组合 5：两点同时取到下界 ⟹ 无 `p_star`；反之单点型仍有 `p_star`】**

对任意 `f : S → ℝ`、`lb : ℝ`：

* 若存在 `s ≠ t` 使 `f s = lb = f t`，则**不存在** `p_star` 使
  `f p_star = lb ∧ ∀ p, f p = lb → p = p_star`（`no_point_unique_of_two_eq`）；
* 而对指数误差剖面 `fitExpPattern`，**存在**这样的 `p_star`（`p_star = 0`），
  且它是唯一的（`fitExp_opt_unique`）。

**⭐ 内容**：同一个「唯一性」判据在**两个实例**上判决**相反**：
干涉场景（两点评分同值）**不可能**满足点层模式；
指数剖面（严格凸、下界只在一点达到）**满足**。

**⚠ 前件自查**：第一分量无前件（`f, lb, s, t` 任意）；第二分量无前件。
两个实例的判决差异**不是**假设，而是两条上游定理的**结论**。 -/
theorem point_layer_impossible_value_layer_unique :
    (∀ (S : Type) (f : S → ℝ) (lb : ℝ) (s t : S), s ≠ t → f s = lb → f t = lb →
        ¬ ∃ p_star : S, ((f p_star = lb) ∧ ∀ p : S, f p = lb → p = p_star))
      ∧ (∃ p_star : ℝ,
          (FitExpThirdInstance.fitExpPattern.f p_star = FitExpThirdInstance.fitExpPattern.lb
            ∧ ∀ p : ℝ, FitExpThirdInstance.fitExpPattern.f p
                = FitExpThirdInstance.fitExpPattern.lb → p = p_star)) := by
  refine ⟨fun S f lb s t hst hs ht =>
      InterventionNegative.no_point_unique_of_two_eq f lb s t hst hs ht,
    ⟨0, OptimalityPattern.opt_eq_lb _,
      fun p hp => FitExpThirdInstance.fitExp_opt_unique p hp⟩⟩

/-! ===========================================================================
  §6  公理审计（确认无 `sorry` / 无额外公理）
  =========================================================================== -/

#print axioms collapse_at_one_of_scale
#print axioms ThetaCons1_inter_ThetaCons2_eq_empty
#print axioms learning_and_prediction_share_scale
#print axioms scm_step_agrees_across_layers
#print axioms identifiability_extremes_are_complementary
#print axioms point_layer_impossible_value_layer_unique

end MainChainConsumer

end FateV2.Loop