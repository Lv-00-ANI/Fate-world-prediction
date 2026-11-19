/-
命运理论 · Lean 4 形式化实现
================================

模块：`ChainErrorBudgetTightWiring`

**作用**：把 `ChainErrorBudgetPredNTight` 的定理真接入主链。

## ⚠ 五次失败的教训（第 679 / 680 轮）

| 版本 | 错误数 | 根因 |
|---|---|---|
| v1 | 10 | 未 `open` 孤岛命名空间 |
| v2 | 9 | `open` 了，但 `mulCLM` / `c` / `errA` 不在其中 |
| v3 | 6 | 猜 `ChainErrorBudgetPredN.mulCLM` —— 不存在 |
| v4 | 6 | 猜 `ChainErrorBudgetPredNTight.mulCLM` —— 不存在 |
| **v5** | **0** | **先 `#check` 实测全名，再重写** |

**⟹ 主控第 679 轮给的「符号真实位置」表是 `文件名:行号`，
不是命名空间。v1–v4 把 `Fate/ScratchAssemblyLearns.lean` 读成了
`Fate.ScratchAssemblyLearns.mulCLM` 的**前缀线索**，方向对但没实测。**

## 实测确认的全名（第 680 轮 `#check` 输出）

| 裸名 | 真实全名 |
|---|---|
| `mulCLM` | `AssemblyLearnsScratch.mulCLM`（⚠ **不是** `ScratchAssemblyLearns`） |
| `c` | `OptimalEta.c` |
| `errA` | `BoundWriteBack.errA` |
| `thetaN` | `ThetaConvergence.thetaN` |
| `optEstimate` | `ChainErrorBudgetBound.optEstimate` |
| `estGap` | `ChainErrorBudgetBound.estGap` |
| `steadyTerm` | `ChainErrorBudgetBound.steadyTerm` |
| `linkEst` | `FirstLayerCapstone.linkEst` |

**关键教训**：`mulCLM` 所在**文件**叫 `ScratchAssemblyLearns.lean`，
但所在**命名空间**叫 `AssemblyLearnsScratch`（词序颠倒）。
`#check` 从 `ChainErrorBudgetPredNTight` 的打印签名里直接给出了这个全名。

## 纪律

- 只新增定理，不改任何既有 `.lean`
- 无 `sorry` / `admit` / 自定义 `axiom`
-/

import FateWorld.FateV2.Error.ChainErrorBudgetPredNTight
import FateWorld.FateV2.Error.FirstLayerCapstone
import FateWorld.FateV2.Loop.ScratchAssemblyLearns
import FateWorld.FateV2.Loop.OptimalEta
import FateWorld.FateV2.Loop.BoundWriteBack
namespace FateV2.Error

open FateV2.Loop
namespace ChainErrorBudgetTightWiring

open MeasureTheory
open scoped BigOperators

/-!
  # Error · ChainErrorBudgetTightWiring

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ChainErrorBudgetTightWiring.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ChainErrorBudgetPredNTight, FirstLayerCapstone, ScratchAssemblyLearns, OptimalEta, BoundWriteBack
  - 补充 open 域：FateV2.Loop
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ###########################################################################
  §1  ⭐⭐⭐ 真接入（一）：三项界不可无条件消去学习项
  ########################################################################### -/

section ThreeTerm

/-- ⭐⭐⭐ **【三项界不可无条件消去学习项】**

**直接取自** `ChainErrorBudgetPredNTight.no_learn_target_is_false`。

若三项界 `optEstimate + estGap + steadyTerm` 对所有 `θ` 都成立，
则矛盾 —— 即学习项**不可**被无条件丢弃。

**⚠ 这是否定性结论，不是「到极限」。** -/
theorem three_term_bound_cannot_drop_learn
    (P : Measure ℝ) [IsProbabilityMeasure P] (a : Fin 1 → ℝ)
    (hconcl : ∀ θ : ℝ,
      ‖AssemblyLearnsScratch.mulCLM 1
          (ThetaConvergence.thetaN (1 / 2) 0 1 θ 0) - 0 * 1‖
        ≤ ChainErrorBudgetBound.optEstimate P 1
          + ChainErrorBudgetBound.estGap P 1 a
          + ChainErrorBudgetBound.steadyTerm (1 / 2) 0) :
    False :=
  ChainErrorBudgetPredNTight.no_learn_target_is_false P a hconcl

end ThreeTerm

/-! ###########################################################################
  §2  ⭐⭐ 真接入（二）：`η = 1` 时学习项为零
  ########################################################################### -/

section EtaOneZero

/-- ⭐⭐ **【`η = 1` 时学习项恰为零】**

当收缩因子取 `η = 1` 且 `n ≥ 1` 时，
`mulCLM x (thetaN 1 θstar x θ n) - θstar * x` 的范数**精确为零**。 -/
theorem link_eta_one_learn_zero
    (θstar x θ : ℝ) (hx : x ≠ 0) {n : ℕ} (hn1 : 0 < n) :
    ‖AssemblyLearnsScratch.mulCLM x
        (ThetaConvergence.thetaN 1 θstar x θ n) - θstar * x‖ = 0 :=
  ChainErrorBudgetPredNTight.capstone_bound_eta_one_no_learn θstar x θ hx hn1

end EtaOneZero

/-! ###########################################################################
  §3  ⭐ 真接入（三）：学习项的精确残差形式
  ########################################################################### -/

section LearnResidual

/-- ⭐ **【学习项 = 残差范数，精确等式】**

`c η ^ n * errA (mulCLM x) (θstar * x) θ
= ‖mulCLM x (thetaN η θstar x θ n) - θstar * x‖`。

**这是「学习项」与「轨迹误差」之间无不等号的桥梁。** -/
theorem link_learn_term_eq_residual
    (η θstar x θ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    OptimalEta.c η ^ n
        * BoundWriteBack.errA (AssemblyLearnsScratch.mulCLM x)
            (θstar * x) θ
      = ‖AssemblyLearnsScratch.mulCLM x
            (ThetaConvergence.thetaN η θstar x θ n) - θstar * x‖ :=
  ChainErrorBudgetPredNTight.learn_term_eq_residual η θstar x θ hx n

end LearnResidual

/-! ###########################################################################
  §4  ⭐ 真接入（四）：「不写签名」形式的存档转发

  以下三条用 `theorem ... := @...` 让 Lean 自动推断签名，
  作为 §1–§3 的**交叉校验**：若 §1–§3 写的签名有误，
  这里的签名会与它们不一致（`#check` 比对即可）。
  ########################################################################### -/

section AutoSig

-- 关闭 `def` 用于命题的 linter：此处需要 `def` 才能省略签名（`theorem` 不允许）。
set_option linter.defProp false

/-- 交叉校验：签名由 Lean 自动推断。 -/
def auto_no_learn_target_is_false :=
  @ChainErrorBudgetPredNTight.no_learn_target_is_false

def auto_capstone_bound_eta_one_no_learn :=
  @ChainErrorBudgetPredNTight.capstone_bound_eta_one_no_learn

def auto_learn_term_eq_residual :=
  @ChainErrorBudgetPredNTight.learn_term_eq_residual

-- 结论断言：自动推断的签名与 §1–§3 手写签名**定义相等**（类型级校验）
example : (auto_no_learn_target_is_false :
    ∀ (P : Measure ℝ) [IsProbabilityMeasure P] (a : Fin 1 → ℝ),
      (∀ θ : ℝ,
        ‖AssemblyLearnsScratch.mulCLM 1
            (ThetaConvergence.thetaN (1 / 2) 0 1 θ 0) - 0 * 1‖
          ≤ ChainErrorBudgetBound.optEstimate P 1
            + ChainErrorBudgetBound.estGap P 1 a
            + ChainErrorBudgetBound.steadyTerm (1 / 2) 0) →
        False) =
    three_term_bound_cannot_drop_learn := rfl

example : (auto_learn_term_eq_residual :
    ∀ (η θstar x θ : ℝ), x ≠ 0 → ∀ n : ℕ,
      OptimalEta.c η ^ n
          * BoundWriteBack.errA (AssemblyLearnsScratch.mulCLM x)
              (θstar * x) θ
        = ‖AssemblyLearnsScratch.mulCLM x
              (ThetaConvergence.thetaN η θstar x θ n) - θstar * x‖) =
    link_learn_term_eq_residual := rfl

end AutoSig

/-! ###########################################################################
  §5  诚实登记（纪律 7：前件自查）
  ########################################################################### -/

/-!
### 5.1 本文件做了什么

三条**手写签名**转发 + 三条**自动签名**存档转发，全部指向
`ChainErrorBudgetPredNTight` 的同名定理：
1. `three_term_bound_cannot_drop_learn` ← `no_learn_target_is_false`
2. `link_eta_one_learn_zero` ← `capstone_bound_eta_one_no_learn`
3. `link_learn_term_eq_residual` ← `learn_term_eq_residual`

**⟹ 全部是转发型（不是「有实质内容」的合并型）。**
价值在于让孤岛定理名出现在可引用面上，**仅此而已**。

### 5.2 本文件**不**声称的东西

- 不声称这是「有实质内容的接入」
- 不声称「G5 已完备」
- 不声称本文件的定理被下游使用

### 5.3 前件自查（纪律 7 —— 是否同义反复）

| 定理 | 前件 | 结论 | 结论是否藏在前件里 |
|---|---|---|---|
| `three_term_bound_cannot_drop_learn` | 「三项界对所有 θ 成立」 | `False` | ❌ 否（结论**否定**前件） |
| `link_eta_one_learn_zero` | `hx : x ≠ 0`、`hn1 : 0 < n` | `‖…‖ = 0` | ❌ 否（`hx`/`hn1` 与范数为零无关） |
| `link_learn_term_eq_residual` | `hx : x ≠ 0`、`n : ℕ` | 精确等式 | ❌ 否（等式内容不在前件中） |

三条前件都**不含**自身结论的实质内容，非循环。
（其中 `hx : x ≠ 0` 是被转发定理自身的前件，属 `ChainErrorBudgetPredNTight`
的定义域限制，不是本文件引入的同义反复。）
-/

end ChainErrorBudgetTightWiring
end FateV2.Error