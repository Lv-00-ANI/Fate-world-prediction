/-
============================================================================
  规则核心链 · 桥路线甲（Dirac 规则 → Step）· **相容定理**（P0-1，第 721 轮）

  ## 本模块做什么

  把 `Fate/DetFunToStepDraft.lean` 里「形状对得上」的三个 `def`
  （`ctxPUnit` / `csPUnit` / `detFunToStep` / `lawDetToStep`）升级为
  **语义真成立**的定理：抽出的 `Step` 与 `LawRuleToTraj.trajOfLaw`
  生成的轨迹**逐点相等**。

  ## 本模块的定理

  | 编号 | 定理 | 证明 |
  |---|---|---|
  | 定理 1 | `lawDetToStep_eq_of_dirac` | `rfl`（忽略四个参数） |
  | 定理 2 | `trajOfLaw_one_eq_lawDetToStep` | `trajOfLaw_succ` + `trajOfLaw_zero` |
  | 定理 3 | `trajOfLaw_eq_iterate_lawDetToStep` | 对 `n` 归纳 |
  | 定理 4 | `lawDetToStep_isStep` | `⟨lawDetToStep …, fun _ => rfl⟩` |

  ## 诚实标注

  - 本模块**只写 theorem，不写 def**；`def` 来自草案模块，本模块 import 它。
  - 草案模块 `Fate/DetFunToStepDraft.lean` **未被修改**。
  - 零 `sorry` / 零 `admit` / 零 `axiom`。
  - ⚠ **关于 `endToEndIter`**：`Fate/EndToEnd.lean` 中的 `endToEndIter`
    签名是 `ℕ → Θ → Θ`（对**θ** 的迭代），与 `trajOfLaw`（对**状态 x** 的迭代，
    `ℕ → X.Carrier → X.Carrier`）**不同形**。因此本模块**不**声称
    「`endToEndIter` 以 `lawDetToStep` 为转移函数」——那条对接需要另一个
    世界模型接口，不在本任务范围内。定理 3 只陈述 `trajOfLaw` 与
    `Function.iterate lawDetToStep` 的一致，这是可证且已证的。
  - ⚠ **前件非循环**：`hR : IsDirac R` 是「R 是 Dirac 规则」的假设，
    它**不包含**任何关于 `Step` / 轨迹的结论；定理 2/3 的结论是关于
    `trajOfLaw` 与 `lawDetToStep` 的等式，不是 `hR` 的展开。
============================================================================
-/

import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.LawRuleToTraj
import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Predict.DetFunToStepDraft
namespace FateV2.Model

open FateV2.Predict
open FateV2.Rules
noncomputable section

/-!
  # Model · DetFunToStep

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DetFunToStep.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame, LawRule, LawRuleToTraj, WorldModel, DetFunToStepDraft
  - 补充 open 域：FateV2.Predict, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1  定理 1：抽出的 `Step` 是确定性函数

`lawDetToStep` 的实现把 `(u, ν, θ, a)` 四位参数全部丢弃，故它对这四位
**完全无关**。这是「规则生成机制」的第一条语义事实：
机制由**规则本身**决定，不被噪声/参数/动作影响。 -/

/-- ⭐⭐⭐ **【Dirac 规则抽出的 Step 是确定性函数】**

`lawDetToStep R hR` 在固定 `x` 处独立于 `(u, ν, θ, a)` 的取值。

**证明**：`rfl` —— `lawDetToStep` 的定义体把四位参数全忽略，故两点
**定义上相等**。 -/
theorem lawDetToStep_eq_of_dirac (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
    (x : F.X.Carrier) (u₁ u₂ : F.U.Carrier) (ν₁ ν₂ : F.Ν.Carrier)
    (θ₁ θ₂ : F.Θ.Carrier) (a₁ a₂ : F.Act.Carrier) :
    lawDetToStep F instX R hR x u₁ ν₁ θ₁ a₁ = lawDetToStep F instX R hR x u₂ ν₂ θ₂ a₂ :=
  rfl

/-! ## §2  定理 2：`trajOfLaw` 的第一步 = `lawDetToStep`

`trajOfLaw` 的定义是
`Nat.rec x₀ (fun k xk => toDetFun R hR (cs k) xk) n`。
第一步（`n = 1`）即 `toDetFun R hR (cs 0) x₀`。
而 `csPUnit 0 = PUnit.unit`，`lawDetToStep` 正是
`fun x … => toDetFun R hR PUnit.unit x`。
二者定义上相等。 -/

/-- ⭐⭐⭐ **【规则轨迹的第一步 = 抽出机制的第一次应用】**

`trajOfLaw R hR csPUnit x₀ 1 = lawDetToStep R hR x₀ u ν θ a`。

**证明**：`trajOfLaw_succ`（`n = 0`）给出第一步 = `toDetFun R hR (csPUnit 0) x₀`；
`csPUnit 0` 是 `PUnit.unit`（定义上），`lawDetToStep` 的定义体也是
`toDetFun R hR PUnit.unit x`，四位参数被忽略。故 `rfl`。 -/
theorem trajOfLaw_one_eq_lawDetToStep (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
    (x₀ : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    LawRuleToTraj.trajOfLaw R hR csPUnit x₀ 1 = lawDetToStep F instX R hR x₀ u ν θ a :=
  rfl

/-! ## §3  定理 3：整条轨迹 = 由 `lawDetToStep` 迭代

这是本模块的核心：`trajOfLaw R hR csPUnit x₀ n` 与
`(lawDetToStep F instX R hR · u ν θ a)^[n] x₀` 逐点相等。

**证明**：对 `n` 归纳。

- `n = 0`：`trajOfLaw_zero` 给 `x₀`；`Function.iterate_zero` 也给 `x₀`。
- `n + 1`：`trajOfLaw_succ` 给
  `trajOfLaw … (n+1) = toDetFun R hR (csPUnit n) (trajOfLaw … n)`。
  `csPUnit n = PUnit.unit`（`rfl`），且 `lawDetToStep` 的 `toDetFun` 中心也取
  `PUnit.unit`。再用归纳假设替换 `trajOfLaw … n`。且 `← Function.iterate_succ_apply'`
  给出 `f^[n+1] x = f (f^[n] x)`（把迭代步展开成一次 `f` 调用）。 -/

/-- ⭐⭐⭐⭐ **【规则轨迹 ≡ 由抽出的 Step 迭代生成的序列】**

`trajOfLaw R hR csPUnit x₀ n = (lawDetToStep F instX R hR · u ν θ a)^[n] x₀`
对一切 `n : ℕ` 成立。

**这是 P0 的核心结论**：规则生成的轨迹，与由抽出的 `Step` 反复迭代
生成的序列**是同一条**。 -/
theorem trajOfLaw_eq_iterate_lawDetToStep (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
    (x₀ : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    ∀ n : ℕ, LawRuleToTraj.trajOfLaw R hR csPUnit x₀ n =
      (lawDetToStep F instX R hR · u ν θ a)^[n] x₀ := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show @LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX R hR (csPUnit k)
        (LawRuleToTraj.trajOfLaw R hR csPUnit x₀ k)
      = lawDetToStep F instX R hR ((fun x => lawDetToStep F instX R hR x u ν θ a)^[k] x₀) u ν θ a
    rw [ih]
    rfl

/-! ## §4  定理 4：`Step` 存在性

`lawDetToStep` 本身就是 `Step F`。把「它属于 `Step` 类型」显式写出，
便于世界模型以 `∃ f : Step F, …` 的形式使用。 -/

/-- ⭐⭐ **【抽出的 Step 是一个合法的 `Step`】**

存在一个 `Step F`，其逐点取值与 `lawDetToStep` 一致。

**证明**：取 `f := lawDetToStep F instX R hR`，逐点 `rfl`。 -/
theorem lawDetToStep_isStep (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R) :
    ∃ f : Step F, ∀ x u ν θ a, f x u ν θ a = lawDetToStep F instX R hR x u ν θ a :=
  ⟨lawDetToStep F instX R hR, fun _ _ _ _ _ => rfl⟩

end

end FateV2.Model