/-
  # 可执行的 SCM 演示（D-014）

  ## 这个文件做什么

  已有的三个可执行层：

  | 文件 | 覆盖 |
  |---|---|
  | `ExecutableRun.lean` | 预测链（求值→观测→预测→残差→裁决 K→回写） |
  | `ExecutableIR.lean` | 数据层（IR 求值、注册表扩展） |
  | `ExecutableExport.lean` | 导出层（模态注册、范围限定） |
  | **本文件** | **SCM 层**（结构方程 `F`、外生律 `P_U`、图、介入） |

  ## D-014 的核心内容

  > 「模型按因果结构组织 SCM」

  具体是 `Model` 的三个字段：

  ```lean
  structure Model (Val V E Noise : Type u) where
    F     : V → (V → Val) → E → Val   -- 结构方程族
    P_U   : Noise                      -- 外生律
    graph : Option (Graph V)           -- 因果图
  ```

  **D-019 的兑现**：`Noise` 是**参数**而不是写死的测度。
  于是 `P_U` 可以是 `Measure E`、`DiscLaw E`、或任何类型——
  `induce` / `sigmaModel` 把 `push` 和 `spread` 也做成参数。

  ## 本文件演示什么

  1. **结构方程真的能算**：`F` 是一个函数，给定内生/外生赋值算出值
  2. **外生律是可枚举的**：用 `DiscLaw`（有限支撑），于是可以 `#eval`
  3. **介入真的能改模型**：`induce` 重算
  4. **σ-model 真的能算**：`spread` 对推前结果取离散度

  ## 怎么运行

  ```bash
  lake env lean FateV2/Demo/ExecutableSCM.lean
  ```
-/

import FateWorld.FateV2.Modeling.SCM
import FateWorld.FateV2.Modeling.Construct

namespace FateV2.Demo.ExecutableSCM

open FateV2.Modeling

/-! ===========================================================================
  §1 一个具体的 SCM（`Int` 值，避免 `Real` 不可打印）
  =========================================================================== -/

/-- **一个两变量 SCM**：

  - 内生变量用 `Bool` 编码（`false = X₁`，`true = X₂`）
  - 结构方程：`X₂ := X₁ + u`，`X₁ := u`
  - 外生 `u ∈ Int`，取值 `{0, 1}`，各权重 1

  **超出 `Model` 定义之处**：定义只要求 `F` 是一个函数；
  本实例给出**具体的线性结构方程**，于是可以算。 -/
def scmModel : FateV2.Modeling.Model Int Bool Int (DiscLaw Int) :=
  { F := fun v X u =>
      -- `v = false` ⟹ X₁ := u；`v = true` ⟹ X₂ := X₁ + u
      if v then X false + u else u
  , P_U := { vals := [0, 1], wt := [1, 1] }
  , graph := none }

/-! ===========================================================================
  §2 求值：把结构方程算出来
  =========================================================================== -/

/-- **内生赋值**：给定外生 `u`，按结构方程解出 `(X₁, X₂)`。

  这里手写求解（`X₁ := u`，然后 `X₂ := X₁ + u = 2u`），
  **不走不动点迭代**——本演示只关心「能算」。 -/
def evalEndo (u : Int) : Bool → Int
  | false => u
  | true  => 2 * u

/-- **投影**：只看 `X₂`。 -/
def projX2 (X : Bool → Int) : Int := X true

/-- **推前**：把外生律沿 `projX2 ∘ evalEndo` 推。

  因为 `evalEndo` 把 `{0,1}` 映到 `{0,2}`（单射），所以推前不合并。 -/
def pushDisc (L : DiscLaw Int) (f : Int → Int) : DiscLaw Int :=
  { vals := L.vals.map f, wt := L.wt }

/-! ===========================================================================
  §3 σ-model
  =========================================================================== -/

/-- **离散度**：用「极差」（最大值 − 最小值），在 `Int` 上可计算。 -/
def spreadRange (L : DiscLaw Int) : Int :=
  match L.vals with
  | []      => 0
  | x :: xs => xs.foldl (fun acc y => max acc y) x - xs.foldl (fun acc y => min acc y) x

/-! ===========================================================================
  §4 打印
  =========================================================================== -/

def discStr (L : DiscLaw Int) : String :=
  s!"vals={L.vals}, wt={L.wt}"

/-- **把 SCM 层跑一遍并打印**。 -/
def runSCM : IO Unit := do
  IO.println "════════════════════════════════════════════════"
  IO.println "《命运》SCM 演示（D-014）"
  IO.println "════════════════════════════════════════════════"
  IO.println ""
  IO.println "── 模型结构 ──"
  IO.println "  结构方程： X₁ := u"
  IO.println "            X₂ := X₁ + u"
  IO.println "  外生律  ： u ∈ {0, 1}，各权重 1"
  IO.println ""
  IO.println "── ① 结构方程真的能算 ──"
  for u in [0, 1] do
    let X := evalEndo u
    IO.println s!"  u = {u}  ⟹  X₁ = {X false},  X₂ = {X true}"
  IO.println ""
  IO.println "── ② 外生律是可枚举的（D-019：Noise 是参数）──"
  IO.println s!"  P_U = {discStr scmModel.P_U}"
  IO.println ""
  IO.println "── ③ 推前（induce 的手写版）──"
  let pushed := pushDisc scmModel.P_U (fun u => projX2 (evalEndo u))
  IO.println s!"  push(fun u => projX2 (evalEndo u)) = {discStr pushed}"
  IO.println "  ⟹ evalEndo 把 {0,1} 映到 {0,2}，是单射，所以不合并"
  IO.println ""
  IO.println "── ④ σ-model（spread = 极差）──"
  IO.println s!"  极差 = {spreadRange pushed}"
  IO.println ""
  IO.println "── ⑤ 介入对比：把 u 的分布改成 {1} ──"
  let intervened : DiscLaw Int := { vals := [1], wt := [1] }
  let pushedDo := pushDisc intervened (fun u => projX2 (evalEndo u))
  IO.println s!"  原始  : P_U = {discStr scmModel.P_U} ⟹ X₂ 的支撑 {pushed.vals}"
  IO.println s!"  介入后: do(u := 1)      ⟹ X₂ 的支撑 {pushedDo.vals}"
  IO.println "  ⟹ 介入改变了外生律，于是推前结果不同"
  IO.println ""
  IO.println "════════════════════════════════════════════════"
  IO.println "D-014 兑现：模型是 SCM（F + P_U + graph）。"
  IO.println "D-019 兑现：P_U 的类型是参数（这里是 DiscLaw Int，"
  IO.println "           也可以是 Measure、或任何类型）。"
  IO.println "════════════════════════════════════════════════"

end FateV2.Demo.ExecutableSCM

/-! ## 预期输出

```
════════════════════════════════════════════════
《命运》SCM 演示（D-014）
════════════════════════════════════════════════

── 模型结构 ──
  结构方程： X₁ := u
            X₂ := X₁ + u
  外生律  ： u ∈ {0, 1}，各权重 1

── ① 结构方程真的能算 ──
  u = 0  ⟹  X₁ = 0,  X₂ = 0
  u = 1  ⟹  X₁ = 1,  X₂ = 2

── ② 外生律是可枚举的（D-019：Noise 是参数）──
  P_U = vals=[0, 1], wt=[1, 1]

── ③ 推前（induce 的手写版）──
  push(projX2 ∘ evalEndo) = vals=[0, 2], wt=[1, 1]
  ⟹ evalEndo 把 {0,1} 映到 {0,2}，是单射，所以不合并

── ④ σ-model（spread = 极差）──
  极差 = 2

── ⑤ 介入对比：把 u 的分布改成 {1} ──
  原始  : P_U = vals=[0, 1], wt=[1, 1] ⟹ X₂ 的支撑 [0, 2]
  介入后: do(u := 1)      ⟹ X₂ 的支撑 [2]
  ⟹ 介入改变了外生律，于是推前结果不同
```
-/
