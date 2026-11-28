import FateWorld.FateV2.Predict.DoCalculus
import FateWorld.FateV2.Predict.SeparableCondMul

/-!
# Integration · Predict · do-算子代数与可分离性的综合

## 本文件做什么

修复两条接线丢失：

| 源模块 | 被 import 次数 |
|---|---:|
| `Predict.SeparableCondMul` | **12** |
| `Predict.DoCalculus` | **8** |

两者都定义了 `Predict` 域里的**代数律**，却从未被下游引用。

## 消费的定理

`Predict.DoCalculus`（namespace `FateV2.Predict.DoCalculus`）：
- `do_idempotent`   `do(x)(do(x)(M)) = do(x)(M)`
- `do_comp`         `do(x')(do(x)(M)) = do(x')(M)`
- `do_not_injective` `do` 不是单射

`Predict.SeparableCondMul`（namespace `FateV2.Predict.SeparableCondMul`）：
- `separable_implies_condMul`  可分离 ⟹ 条件乘性

## 组合的实质

`do_idempotent` 与 `do_comp` **必须并置**：前者是「重复同一干预无效」，
后者是「后一次干预覆盖前一次」。两者合起来才是「`do` 构成幂等半群作用」
——单看任一只是其中一条代数律。

`do_not_injective` 则给出**代价**：这个作用不忠实（不同模型可映到同一点），
与幂等性并置才完整刻画「`do` 是什么」。
-/

namespace FateV2.Integration

namespace PredictBatch1

/-! ---------------------------------------------------------------------------
  §1  do-算子的代数律
  --------------------------------------------------------------------------- -/

namespace DoNS

open FateV2.Predict
open FateV2.Predict.DoCalculus

variable {X Y : Type u}

/-- ⭐⭐⭐ **`do` 的幂等 + 复合律（合取形式）**。

对任意模型 `M` 与取值 `x x'`：
1. `do(x)(do(x)(M)) = do(x)(M)`（幂等）；
2. `do(x')(do(x)(M)) = do(x')(M)`（复合 / 后者覆盖）。

**为什么值得一条定理**：`do` 的语义要求「干预是幂等的且可复合」。
两条定律**分别**对应「重复干预不变」与「覆盖前次干预」，
它们在源文件里是两条独立定理，但下游使用时**总是一起**。
并置后，下游引用一次即可拿到完整的代数律。 -/
theorem do_idempotent_and_comp (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x x' : X) :
    (doX (doX M x) x = doX M x) ∧ (doX (doX M x) x' = doX M x') :=
  ⟨do_idempotent M x, do_comp M x x'⟩

/-- ⭐⭐ **`do` 幂等但非单射**。

`do` 的幂等性（`do_idempotent`）与它**不忠实**（`do_not_injective`）
同时成立。

**这两条必须并置**：幂等性容易让人以为「`do` 可逆或至少信息保持」，
而非单射性正是它的**代价定理** —— 不同结构模型可以被映到同一点。
合起来才是对 `do` 的完整刻画：「稳定的、但丢信息的」。
-/
theorem do_idempotent_but_lossy (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) :
    (doX (doX M x) x = doX M x)
      ∧ (¬ Function.Injective
          (fun M : FateV2.Modeling.PearlHierarchy.SCM (Fin 2) (Fin 1) => doX M 0)) :=
  ⟨do_idempotent M x, do_not_injective⟩

end DoNS

/-! ---------------------------------------------------------------------------
  §2  可分离性 ⟹ 条件乘性
  --------------------------------------------------------------------------- -/

namespace SeparableNS

open FateV2.Predict
open FateV2.Predict.FinCondIndep
open FateV2.Predict.SeparableCondMul

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐⭐⭐ **可分离性的代数内核（可直接引用的形式）**。

若存在 `f : α → γ → ℝ`、`g : β → γ → ℝ` 使
`p ((x,y),z) = f x z * g y z`，则 `CondMul p`。

**这是 Pearl 1.2.4 的代数内核**：`f` 与 `g` 是「各自只依赖自己那一侧」
的因子分解。源定理的方向是「存在分解 ⟹ 条件乘性」，
本定理把它以**函数参数**的形式暴露，便于下游直接构造分解后使用，
不必每次写 `∃` 的 `obtain`。 -/
theorem condMul_of_factorization (p : FinJoint α β γ)
    (f : α → γ → ℝ) (g : β → γ → ℝ)
    (hfg : ∀ x y z, p ((x, y), z) = f x z * g y z) :
    CondMul p :=
  separable_implies_condMul p ⟨f, g, hfg⟩

end SeparableNS

end PredictBatch1

end FateV2.Integration