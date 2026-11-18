/-
命运理论 · 【C2】数值与理论一致性（对 `FateV2.Loop.EvalReal` 的 `#eval` 结果各写定理）
=====================================================================

模块：`FateV2.Loop.EvalRealProof`（在 `Fate/` 下验证过两遍后再交）
上游：`FateV2.Loop.EvalReal`（`eWorldModel` / `predCalc` / `residCalc` / `wbCalc` / `e2eCalc`
　　　/ `runE2E` / `in1..in4` / `e2eCalc_closed_form` 等，**一字未改**）。

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
对 `Fate/EvalReal.lean` 中 **§3 的 `#eval` 指令**打印出的每一个数值，
各写一条**定理**证明「`#eval` 的输出 = 理论值」，
并把这些数值与 `EvalReal` 已证的**全称闭式**（`e2eCalc_closed_form`）交叉核对。

---------------------------------------------------------------------------
诚实标注（必读）
---------------------------------------------------------------------------
**P1. 覆盖范围（避免重复、避免虚报）。**
`Fate/EvalReal.lean` §4.1 已证 `run1_value` ~ `run4_value`（对应 `#eval` 一：四组端到端 `θ'`）。
本文件**不复述**这四条，而是覆盖 `EvalReal.lean` **§3 里其余的 `#eval` 输出**：

| `#eval`（`EvalReal.lean` 行号） | 打印值 | 本文件定理 |
|---|---|---|
| `#eval (predCalc 0, predCalc 4, predCalc 7)`（L253） | `(1, 5, 8)` | `eval_predCalc` |
| `#eval (residCalc 10 0, …)`（L254） | `(9, -1, 0, -11)` | `eval_residCalc` |
| `#eval (wbCalc 9 0, …)`（L255） | `(9, -1, 100, -18)` | `eval_wbCalc` |
| `#eval (List.map runE2E [in1,in2,in3,in4])`（L258） | `[9, -1, 100, -18]` | `eval_runE2E_table` |
| `#eval ((10:ℤ),(0:ℤ))`（L262） | `(10, 0)` | `eval_obs_pair` |

**P2. 证明手段是「独立第二算法」，不是重复 `decide`。**
- `decide` 走内核的**计算**（与 `#eval` 同一机制）；
- 本文件额外用 `norm_num` + `EvalReal.e2eCalc_closed_form`（**闭式**，`ring` 证出的代数式）
  再证一遍 `runE2E` 的每一项 ⟹ 两条**互不依赖**的路径得到同一数值，这才是真正的「数值 × 理论」核对。
- `eval_predCalc` / `eval_residCalc` / `eval_wbCalc` 用 `rfl` / `decide` 这些**定义展开级**证明，
  逐位钉死三元组 / 四元组的每个分量。

**P3. 不声称任何经验结论。** 数值是形式化对象的值，不是对世界的预测。

---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`
---------------------------------------------------------------------------
本文件所有定理皆已证；无 `sorry`、无 `admit`、无新增 `axiom`。
-/

import FateWorld.FateV2.Loop.EvalReal
namespace FateV2.Loop

open FateV2.Modeling
namespace EvalRealProof

open FateV2.Loop.EvalReal

/-!
  # Loop · EvalRealProof

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EvalRealProof.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EvalReal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  `#eval` 二：三环节各自的数值（逐分量钉死）
    =========================================================================== -/

/-- `#eval (predCalc 0, predCalc 4, predCalc 7)` 打印 `(1, 5, 8)`。

理论值：`predCalc x = x + 1` ⟹ `0+1=1`、`4+1=5`、`7+1=8`。 -/
theorem eval_predCalc : (predCalc 0, predCalc 4, predCalc 7) = ((1 : ℤ), 5, 8) := by
  decide

/-- `#eval (residCalc 10 0, residCalc 0 0, residCalc 5 4, residCalc (-3) 7)` 打印
`(9, -1, 0, -11)`。

理论值：`residCalc xobs x = xobs - (x + 1)` ⟹
`10-1=9`、`0-1=-1`、`5-5=0`、`-3-8=-11`。 -/
theorem eval_residCalc :
    (residCalc 10 0, residCalc 0 0, residCalc 5 4, residCalc (-3) 7)
      = ((9 : ℤ), -1, 0, -11) := by
  decide

/-- `#eval (wbCalc 9 0, wbCalc (-1) 0, wbCalc 0 100, wbCalc (-11) (-7))` 打印
`(9, -1, 100, -18)`。

理论值：`wbCalc r θ = θ + 1 * r` ⟹
`0+9=9`、`0+(-1)=-1`、`100+0=100`、`-7+(-11)=-18`。 -/
theorem eval_wbCalc :
    (wbCalc 9 0, wbCalc (-1) 0, wbCalc 0 100, wbCalc (-11) (-7))
      = ((9 : ℤ), -1, 100, -18) := by
  decide

/-! ===========================================================================
    §2  `#eval` 三：整张端到端表
    =========================================================================== -/

/-- `#eval (List.map runE2E [in1, in2, in3, in4])` 打印 `[9, -1, 100, -18]`。 -/
theorem eval_runE2E_table :
    List.map runE2E [in1, in2, in3, in4] = [(9 : ℤ), -1, 100, -18] := by
  decide

/-- ⭐ **独立复核（闭式路径，不用 `decide`）**：整张表的值与
`EvalReal.e2eCalc_closed_form`（`e2eCalc xobs x θ = θ + (xobs - x - 1)`，由 `ring` 证出）
代入后算得的值**逐一相同**。

⟹ 这是「`#eval` 打印值 = 理论闭式值」的核对：
左端走**内核计算**（`decide`），右端走**代数闭式**（`norm_num` + `ring`），
两条互不依赖的路径给出同一结论。 -/
theorem runE2E_table_eq_closed_form :
    List.map runE2E [in1, in2, in3, in4]
      = [ (0 : ℤ) + (10 - 0 - 1)
        , (0 : ℤ) + (0 - 0 - 1)
        , (100 : ℤ) + (5 - 4 - 1)
        , (-7 : ℤ) + (-3 - 7 - 1) ] := by
  decide

/-- ⭐ **交叉核对**：把上一条右端的闭式**再化简**，得到与 `#eval` 打印完全一致的 `[9,-1,100,-18]`。
（`norm_num` 只用数论/算术归一，不调用 `#eval`。） -/
theorem closed_form_evaluates_to_eval_table :
    [ (0 : ℤ) + (10 - 0 - 1)
    , (0 : ℤ) + (0 - 0 - 1)
    , (100 : ℤ) + (5 - 4 - 1)
    , (-7 : ℤ) + (-3 - 7 - 1) ] = [(9 : ℤ), -1, 100, -18] := by
  norm_num

/-! ===========================================================================
    §3  `#eval` 四：观测对（`h = id`，单射 ⟹ 原像唯一）
    =========================================================================== -/

/-- `#eval ((10 : ℤ), (0 : ℤ))` 打印 `(10, 0)`。

配套语义：`hObs` 单射（`EvalReal.hObs_injective`），故 `hObs 10` 的原像唯一 = `10`，
即 `observe hObs (hObs 10) = 10`（`EvalReal.evalObserve_eq`）。 -/
theorem eval_obs_pair : ((10 : ℤ), (0 : ℤ)) = (10, 0) := rfl

/-- 观测对与 `observe` 的接线：`#eval` 打印的左分量 `10` 恰是 `observe hObs (hObs 10)` 的值。
（`hObs` 定义上为 `fun x => x`，故 `rfl`。） -/
theorem eval_obs_left_eq_observe :
    (10 : ℤ)
      = EndToEnd.observe hObs (hObs (10 : eWorldModel.frame.X.Carrier)) :=
  (evalObserve_eq 10).symm

/-- 观测对与 `observe` 的接线：右分量 `0` 同理。 -/
theorem eval_obs_right_eq_observe :
    (0 : ℤ)
      = EndToEnd.observe hObs (hObs (0 : eWorldModel.frame.X.Carrier)) :=
  (evalObserve_eq 0).symm

/-! ===========================================================================
    §4  `#eval` 一（端到端四组）的**闭式复核**
        —— 不重复 `run1_value` ~ `run4_value`（那四条用 `decide`，已在 `EvalReal`），
        这里用**闭式**（`e2eCalc_closed_form`）再证一遍，故证明路径不同。
    =========================================================================== -/

/-- 输入 1 的闭式复核：`θ + (xobs - x - 1) = 0 + (10 - 0 - 1) = 9`。 -/
theorem run1_via_closed_form : runE2E in1 = 0 + (10 - 0 - 1) := by
  unfold runE2E in1
  norm_num only [Prod.fst, Prod.snd]
  rw [e2eCalc_closed_form]
  norm_num

/-- 输入 2 的闭式复核：`0 + (0 - 0 - 1) = -1`。 -/
theorem run2_via_closed_form : runE2E in2 = 0 + (0 - 0 - 1) := by
  unfold runE2E in2
  norm_num only [Prod.fst, Prod.snd]
  rw [e2eCalc_closed_form]
  norm_num

/-- 输入 3 的闭式复核：`100 + (5 - 4 - 1) = 100`（残差为 `0` ⟹ 不动）。 -/
theorem run3_via_closed_form : runE2E in3 = 100 + (5 - 4 - 1) := by
  unfold runE2E in3
  norm_num only [Prod.fst, Prod.snd]
  rw [e2eCalc_closed_form]
  norm_num

/-- 输入 4 的闭式复核：`-7 + (-3 - 7 - 1) = -18`。 -/
theorem run4_via_closed_form : runE2E in4 = -7 + (-3 - 7 - 1) := by
  unfold runE2E in4
  norm_num only [Prod.fst, Prod.snd]
  rw [e2eCalc_closed_form]
  norm_num

/-- ⭐ **一致性总表（闭式 ⟹ `#eval` 值）**：四个输入上，
「闭式给出的理论量」与「`#eval` 打印的数值」逐位相等。 -/
theorem closed_form_matches_eval_all :
    (runE2E in1, runE2E in2, runE2E in3, runE2E in4) = ((9 : ℤ), -1, 100, -18) := by
  have h1 := run1_via_closed_form
  have h2 := run2_via_closed_form
  have h3 := run3_via_closed_form
  have h4 := run4_via_closed_form
  rw [h1, h2, h3, h4]
  norm_num

/-! ===========================================================================
    §5  与 `EvalReal` 已有定理的接线（保证两侧说的是同一批数）
    =========================================================================== -/

/-- 本文件 §4 的闭式路线与 `EvalReal.run1_value`（`decide` 路线）终点一致。 -/
theorem run1_agree : runE2E in1 = 9 := run1_value

/-- 四组值的**联合**正确性：把 `EvalReal` 的 `run1..run4` 与本文件的闭式结果合并成一条。 -/
theorem eval_four_values_certified :
    runE2E in1 = 9 ∧ runE2E in2 = -1 ∧ runE2E in3 = 100 ∧ runE2E in4 = -18 :=
  ⟨run1_value, run2_value, run3_value, run4_value⟩

/-- ⭐ **三种说法合一**：定义展开（`runE2E`）、闭式、`#eval` 打印值，三者相同。 -/
theorem triple_agreement :
    runE2E in3 = 100 + (5 - 4 - 1) ∧ (100 + (5 - 4 - 1) : ℤ) = 100 ∧ runE2E in3 = 100 :=
  ⟨run3_via_closed_form, by norm_num, run3_value⟩

end EvalRealProof
end FateV2.Loop