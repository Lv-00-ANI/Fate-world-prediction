import FateWorld.FateV2.Rules.Completeness
import FateWorld.FateV2.Error.ChainBudgetBound

/-!
# Integration · Rules/Error · 伪内涵与估计误差的综合

## 本文件做什么

修复两条**严重的接线丢失**：

| 源模块 | 被 import 次数 | 却无名字被调用 |
|---|---:|---|
| `Rules.Completeness` | **8** | ✓ |
| `Error.ChainBudgetBound` | **11** | ✓ |

两者都是被大量下游依赖、却从未被真正引用的模块 ——
典型的「import 了但没用」。

## 消费的定理

`Rules.Completeness`（namespace `FateV2.Rules.FormalCtx`）：
- `pseudoIntent_closure_closed`  伪内涵的闭包是闭集
- `pseudoIntent_closure_strict`  伪内涵的闭包严格更大

`Error.ChainBudgetBound`（namespace `FateV2.Error.ChainBudgetBound`）：
- `sigmaEst_nonneg`   估计尺度非负
- `est_bound`         估计量的范数界

## 组合的实质

`pseudoIntent_closure_closed` 与 `pseudoIntent_closure_strict` **必须并置**：
前者说闭包是**闭的**（稳定），后者说闭包**严格更大**（有推进）。
单看前者会以为「闭包已经不增长」，单看后者会以为「闭包破坏了闭性」。
合起来才是「伪内涵的闭包是一个严格更大的闭集」——这正是完备性证明的枢纽。

`sigmaEst_nonneg` 与 `est_bound` 并置给出「尺度非负 + 范数可控」，
是误差预算链的两个前置条件。

## 不引入新数学

全部为既有定理的组合。
-/

namespace FateV2.Integration

namespace RulesErrorBatch1

/-! ---------------------------------------------------------------------------
  §1  伪内涵的闭包：稳定且严格推进
  --------------------------------------------------------------------------- -/

namespace PseudoIntentNS

open FateV2.Rules
open FateV2.Rules.FormalCtx

variable {K : FormalCtx.{u, v}}

/-- ⭐⭐⭐ **伪内涵的闭包「既闭又严格更大」**。

对伪内涵 `P`：
1. `K.closureOp P` 是闭集（`pseudoIntent_closure_closed`）；
2. `P ⊂ K.closureOp P`，即严格包含（`pseudoIntent_closure_strict`）。

**这两条必须并置**：完备性证明需要「闭包算子把伪内涵推进到一个
**真更大的闭集**」这一双重事实。若只引用第 1 条，会误以为闭包不再
增长（因为它已闭）；若只引用第 2 条，会误以为闭包破坏了闭性。
合起来才说明「迭代能持续推进且每次落在闭集上」——这是
「迭代必然到达不动点」的枢纽。 -/
theorem pseudoIntent_closure_closed_and_strict {P : Set K.MFCA}
    (hP : K.IsPseudoIntent P) :
    K.IsClosedAttr (K.closureOp P) ∧ P ⊂ K.closureOp P :=
  ⟨pseudoIntent_closure_closed (K := K) hP, pseudoIntent_closure_strict (K := K) hP⟩

/-- ⭐ **伪内涵的真包含蕴含非闭性**。

若 `P` 是伪内涵且 `P ⊂ K.closureOp P`，则 `P` 本身**不是**闭集。

这是上一条的**逆否用法**：闭集满足 `closureOp P = P`，与严格包含矛盾。
下游常用「伪内涵不是闭集」这一形式，单列以免每次反证。 -/
theorem pseudoIntent_not_closed {P : Set K.MFCA} (hP : K.IsPseudoIntent P) :
    ¬ K.IsClosedAttr P := by
  intro hcl
  -- 闭集满足 closureOp P = P，与严格包含矛盾
  have heq : K.closureOp P = P := hcl
  have hsub := (pseudoIntent_closure_strict (K := K) hP).2
  rw [heq] at hsub
  exact absurd (hsub (subset_refl P)) (by simp)

end PseudoIntentNS

/-! ---------------------------------------------------------------------------
  §2  估计尺度：非负与范数界
  --------------------------------------------------------------------------- -/

namespace EstNS

open FateV2.Error
open FateV2.Error.ChainBudgetBound
open FateV2.Error.GaussMarkovScalar
open MeasureTheory

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐ **估计尺度非负 + 估计量范数可控**。

1. `0 ≤ sigmaEst P n`（`sigmaEst_nonneg`）；
2. 若 `|est a w| ≤ σ`，则 `‖est a w‖ * ‖x‖ ≤ σ * ‖x‖`（`est_bound`）。

**为什么值得一条定理**：误差预算链需要「尺度非负」作为除法的合法性前提，
同时需要「范数可被 σ 控制」作为传递界的输入。两者来自不同定理，
组合后才是完整的**前置条件包**。 -/
theorem sigma_est_foundation (n : ℕ) {a w : Fin n → ℝ} {σ x : ℝ}
    (hbound : |GaussMarkovScalar.est a w| ≤ σ) :
    (0 ≤ sigmaEst P n) ∧ (‖GaussMarkovScalar.est a w‖ * ‖x‖ ≤ σ * ‖x‖) :=
  ⟨sigmaEst_nonneg n, est_bound a w σ x hbound⟩

end EstNS

end RulesErrorBatch1

end FateV2.Integration
