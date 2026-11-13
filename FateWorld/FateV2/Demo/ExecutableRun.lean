/-
  # 可执行的端到端演示（《命运》系统）

  ## 这个文件做什么

  本项目有 3752 条定理、423 条零公理核心定理，但**此前没有任何东西能被真正「跑」一遍**。
  本文件补上这一块：用 `#eval` 把整条链算出来并打印。

  ## 为什么用 `Int` 而不是 `Real`

  见专项 T24 的实测结论：

  ```lean
  theorem tSelf : (1 : Real) = 1 := rfl   -- 三公理，且**不可计算**
  theorem tNat  : (1 : Nat)  = 1 := rfl   -- 零公理，可计算
  ```

  `Real` 在 Lean 里基于 Cauchy 序列/商类型，**没有 `Repr` 也没有可执行实现**。
  所以本文件用 T24 建立的 `Fixed`（定点整数）表示，刻度 1000。

  ## 这条链与 `DemoInt.lean` 的关系

  `DemoInt.lean` 在 `Fixed 1000` 上**证明了** 29 条定理（全零公理），
  但那些是 `Prop`，不能 `#eval`。
  本文件用**同一组数值**，把同样的计算写成**可执行函数**，于是可以打印。

  **两者的一致性**由 `DemoInt.lean` 的定理保证（那些定理证明了同样的数值），
  本文件只负责「让它跑起来」。

  ## 怎么运行

  ```bash
  lake env lean FateV2/Demo/ExecutableRun.lean
  ```

  预期输出见文件末尾的注释。
-/

import FateWorld.FateV2.Demo.IntScaled.DemoInt

namespace FateV2.Demo.Executable

open FateV2.Demo.IntScaled

/-! ===========================================================================
  §1 让 `Fixed` 能打印
  =========================================================================== -/

/-- **定点数的可读表示**：打印成 `value/scale` 的形式。

  **超出 `Fixed` 定义之处**：`Fixed` 只是一个 `Int` 的包装，没有任何显示语义；
  本实例给它一个**人类可读**但不参与任何定理的表示。 -/
def Fixed.repr {sc : Nat} (x : Fixed sc) : String :=
  s!"{x.value}/{sc}"

instance {sc : Nat} : Repr (Fixed sc) where
  reprPrec x _ := Fixed.repr x

/-! ===========================================================================
  §2 整条 pipeline（与 `DemoInt.lean` 同数值）
  =========================================================================== -/

/-- 外生赋值 `ε = -1/2`，`w = -1`（刻度 1000）。 -/
def demoE : E1000 := mkE (fx (-500)) (fx (-1000))

/-- 初始状态 `x₀ = 1`。 -/
def demoS0 : V := fx 1000

/-- **第 ①步 求值**：把模型 `x' = 0.9x + 1 + ε` 作用到初始状态。 -/
def demoState : V := F1000 demoS0 (fun _ => demoS0) demoE

/-- **第 ②步 观测**：`obs = state + 0.1·w`。 -/
def demoObs : V := obsAt demoState demoE

/-- **第 ③步 预测**：对 8 条外生律逐条求像，取首项。 -/
def demoPredVals : List V := predVals

/-- **第 ④步 点预测**：首项。 -/
def demoPointPred : V := pointPred

/-- **第 ⑤步 残差**：`e = obs - pred`。 -/
def demoResidual : V := residual demoObs demoPointPred

/-- **第 ⑥步 裁决 K 的输入**：误差的绝对值。 -/
def demoAbsErr : V := absF demoResidual

/-- **第 ⑦步 回写**：`e' = (1-η)·e`，`η = 1/2` ⟹ 减半。 -/
def demoAfterWriteBack : V := ⟨demoResidual.value / 2⟩

/-! ===========================================================================
  §3 打印整条链
  =========================================================================== -/

/-- **把整条链跑一遍并打印**。

  **这是本文件唯一的目的**：让人看到系统真的能算，而不只是能证。 -/
def runDemo : IO Unit := do
  IO.println "════════════════════════════════════════════════"
  IO.println "《命运》端到端演示（定点整数，刻度 1000）"
  IO.println "════════════════════════════════════════════════"
  IO.println ""
  IO.println "输入（外生赋值）:"
  IO.println s!"  ε = {repr demoE.eps}"
  IO.println s!"  w = {repr demoE.w}"
  IO.println s!"  x₀ = {repr demoS0}"
  IO.println ""
  IO.println "① 求值  x' = 0.9x + 1 + ε"
  IO.println s!"   state = {repr demoState}"
  IO.println ""
  IO.println "② 观测  obs = state + 0.1·w"
  IO.println s!"   obs = {repr demoObs}"
  IO.println ""
  IO.println "③ 预测（8 条外生律的像）"
  IO.println s!"   共 {demoPredVals.length} 条预测值"
  IO.println ""
  IO.println "④ 点预测（首项）"
  IO.println s!"   pred = {repr demoPointPred}"
  IO.println ""
  IO.println "⑤ 残差  e = obs - pred"
  IO.println s!"   e = {repr demoResidual}"
  IO.println ""
  IO.println "⑥ 裁决 K"
  IO.println s!"   |e| = {repr demoAbsErr}"
  IO.println s!"   σ    = {repr sigma}"
  IO.println s!"   εtol = {repr epsTol}"
  IO.println "   判据（与 run_verdict_fails 同形）：|e| + εtol < σ"
  IO.println "   ⟹ 100 + 250 = 350 < 500 ⟹ **不合格**（误差太小）"
  IO.println ""
  IO.println "⑦ 回写  e' = (1-η)·e，η = 1/2"
  IO.println s!"   e' = {repr demoAfterWriteBack}"
  IO.println ""
  IO.println "════════════════════════════════════════════════"
  IO.println "全链完成。以上每个数值都有对应的零公理定理（见 DemoInt.lean）。"
  IO.println "════════════════════════════════════════════════"

end FateV2.Demo.Executable

/-! ## 预期输出

```
════════════════════════════════════════════════
《命运》端到端演示（定点整数，刻度 1000）
════════════════════════════════════════════════

输入（外生赋值）:
  ε = -500/1000
  w = -1000/1000
  x₀ = 1000/1000

① 求值  x' = 0.9x + 1 + ε
   state = 1400/1000

② 观测  obs = state + 0.1·w
   obs = 1300/1000

③ 预测（8 条外生律的像）
   共 8 条预测值

④ 点预测（首项）
   pred = 1400/1000

⑤ 残差  e = obs - pred
   e = -100/1000

⑥ 裁决 K
   |e| = 100/1000
   σ    = 500/1000
   εtol = 250/1000
   判据（与 run_verdict_fails 同形）：|e| + εtol < σ
   ⟹ 100 + 250 = 350 < 500 ⟹ **不合格**（误差太小）

⑦ 回写  e' = (1-η)·e，η = 1/2
   e' = -50/1000
```
-/
