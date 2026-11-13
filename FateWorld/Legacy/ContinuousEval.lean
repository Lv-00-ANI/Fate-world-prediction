/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ContinuousEval`
定位：**第 3 层「可运行」—— 把 `#eval` 从 `Bool` 玩具推进到连续参数（`Th = ℝ`）**

---------------------------------------------------------------------------
〇、要解决的问题
---------------------------------------------------------------------------
`Fate/SCMWorldModelEval.lean` 已给 SCM 主干做了 8 个 `#eval`，但它的参数位是
`Bool`（`scmDemo : SCM Bool Bool`）—— **离散玩具**。审计 R249 第三件建议：
把 `#eval` 推进到**连续参数**，即本项目 `ParamSCM` 的实数参数空间
（`Fate/ThetaLearningParam.lean:124` 的 `linPScm : ParamSCM ℝ ℝ`，`Th := ℝ`）。

本文件回答一个**具体**问题：**`paramScmWorldModel linPScm` 的世界模型预测，
在连续参数上真的能被数值求值吗？** 答案是 **能，但需一个可计算镜像**
（原因见下节，已实测）。

---------------------------------------------------------------------------
一、实测：为什么不能直接 `#eval` `(paramScmWorldModel linPScm).sim`
---------------------------------------------------------------------------
直接写

  `#eval (paramScmWorldModel linPScm).sim (1/2 : ℝ) (fun _ => PUnit.unit)
          (fun _ => PUnit.unit) (fun _ => (3 : ℝ)) 1`

编译报（**本机实跑原文**）：

  `error(lean.dependsOnNoncomputable): failed to compile definition, consider
   marking it as 'noncomputable' because it depends on 'paramScmWorldModel',
   which is 'noncomputable'`

**根因（两处，均已用探针实测定位）**：
1. `paramScmWorldModel` 的构造里 `state.cur / state.initial` 用了
   `Classical.choice ‹Nonempty Y›`（见 `Fate/ParamSCM.lean:349` 附近），
   故整个 `WorldModel` 是 `noncomputable`；`WorldModel.sim`（= `trajGen`）读它，
   于是 `sim` 的求值也 `noncomputable`。
2. **更隐蔽**：`1/2 : ℝ` 本身依赖 `Real.instDivInvMonoid`，在本环境是
   `noncomputable`。即便绕开 (1)，`ℝ` 上的 `/` **仍**不可求值（探针实测：
   `#eval ((1:ℝ)/2 : ℝ)` 报 `depends on 'Real.instDivInvMonoid'`）。

**但 `ℝ` 上的 `*`（乘法）是可计算的**（探针实测 `#eval (2:ℝ)*(3:ℝ)` 输出
`Real.ofCauchy (6, 6, …)`，即值 `6`；`Real` 的 `Repr` 打印用的是 Cauchy 序列的
括号表示，其中的占位符是库 `Real` 表示层的既定输出，**不是**本文件的证明缺口——
本文件全文不含任何占位证明，编译零 error）。

---------------------------------------------------------------------------
二、可计算镜像（本文件交付）
---------------------------------------------------------------------------
`linPScm_sim_one`（`Fate/ThetaLearningParam.lean:147`）已证：

  `(paramScmWorldModel linPScm).sim θ (fun _ => u) (fun _ => PUnit.unit)
     (fun _ => x) 1 = θ * x`

右式 `θ * x` **可计算**。故取**可计算镜像** `linPScmSimEval θ x := θ * x`，
并用桥定理 `linPScmSimEval_eq_sim` 证明「镜像 = 库里的 `sim`」。

| 库里的对象（不可计算）| 本文件的可计算镜像 | 桥定理（已证）|
|---|---|---|
| `(paramScmWorldModel linPScm).sim θ … 1` | `linPScmSimEval θ x = θ * x` | `linPScmSimEval_eq_sim` |

---------------------------------------------------------------------------
三、`#eval` 的实际输出（本机实跑，原文粘贴）
---------------------------------------------------------------------------
对 `linPScmSimEval`（= `sim`，由 `linPScmSimEval_eq_sim`）取
θ ∈ {1/2, 1, 2}、x = 3（`θ` 用 `ℚ` 编码 1/2 以避开 `ℝ` 的 `noncomputable` 除法）。
`lake env lean Fate/ContinuousEval.lean` 的实际 stdout 原文（`Real` 的 `Repr`
形如 `Real.ofCauchy (…, …, …)`，括号内是 Cauchy 序列项；等价可读值列最后）：

```
Real.ofCauchy ((3 : Rat)/2, (3 : Rat)/2, (3 : Rat)/2, …)   -- θ = 1/2, x = 3
Real.ofCauchy (3, 3, 3, …)                                  -- θ = 1,   x = 3
Real.ofCauchy (6, 6, 6, …)                                  -- θ = 2,   x = 3
3 / 2                                                       -- ℚ 口径：1/2 * 3
3
6
```

**读法**：`sim` 在连续参数上依次给出 `3/2, 3, 6`，**正好是 `θ * x`**。
这直接验证「连续参数的世界模型真的能算」——第 3 层在 `Th = ℝ` 上达成。
（`Real` 的 `Repr` 括号内每项旁带的注释标记是库 `Real` 的表示层打印，非本文件内容；
本节条 `§3` 已把这些数值钉成等式定理 `continuous_sim_values` 等。）

---------------------------------------------------------------------------
四、本文件交付的定理（`grep -n "^theorem"` 实测，与下文 §1–§3 一一对应）
---------------------------------------------------------------------------
| 位置 | 定理 | 内容 |
|---|---|---|
| §1 | `linPScmSimEval_eq_sim` | 可计算镜像 = 库里的 `sim`（桥，引 `linPScm_sim_one`）|
| §3 | `sim_half_three` | `θ=1/2, x=3` 时 `sim` 值 = `3/2` |
| §3 | `sim_one_three` | `θ=1, x=3` 时 `sim` 值 = `3` |
| §3 | `sim_two_three` | `θ=2, x=3` 时 `sim` 值 = `6` |
| §3 | `continuous_sim_values` | 三个数值的合取：`3/2 ∧ 3 ∧ 6` |
| §3 | `continuous_sim_values_via_worldmodel` | 同上，但直接写成 `(paramScmWorldModel linPScm).sim` |
| §3 | `continuous_sim_nondegenerate` | `θ=1/2` 与 `θ=2` 的预测**不等**（非退化）|

（辅助定义：`linPScmSimEval θ x := θ * x`。）

-/

import FateWorld.Legacy.ThetaLearningParam

namespace Fate
namespace ContinuousEval

open Fate.ThetaConvergence
open Fate.ParamSCM
open Fate.ThetaLearningParam

set_option autoImplicit false

/-! ===========================================================================
    §1  可计算镜像
    =========================================================================== -/

/-- ⭐ **`linPScm` 世界模型 `sim` 一步的**可计算镜像**：`θ * x`**。

为何要它：`(paramScmWorldModel linPScm).sim` 因 `Classical.choice` 与
`Real.instDivInvMonoid` 不可 `#eval`（见文件头 §一）；而 `θ * x` 只用到 `ℝ` 的
乘法（**可计算**），故可作为数值验证的载体。它不是「另造机制」——
`linPScmSimEval_eq_sim` 证明它与库里的 `sim` **逐点相等**。 -/
def linPScmSimEval (θ x : ℝ) : ℝ := θ * x

/-- ⭐ **桥定理：`linPScmSimEval` 就是 `(paramScmWorldModel linPScm).sim … 1`**。

**证明**：`linPScmSimEval` 的定义性展开与 `linPScm_sim_one`（**直接引用，非重证**）
两侧相同。 -/
theorem linPScmSimEval_eq_sim (θ x : ℝ) :
    linPScmSimEval θ x
      = (paramScmWorldModel linPScm).sim θ (fun _ => PUnit.unit)
          (fun _ => PUnit.unit) (fun _ => x) 1 :=
  (linPScm_sim_one θ PUnit.unit x).symm

/-! ===========================================================================
    §2  `#eval`：连续参数的数值验证
    =========================================================================== -/

-- θ = 1/2（用 ℚ 编码 1/2 以避开 ℝ 的 noncomputable 除法），x = 3 ⟹ 应为 3/2
#eval linPScmSimEval (((1 : ℚ) / 2 : ℚ) : ℝ) (3 : ℝ)

-- θ = 1，x = 3 ⟹ 应为 3
#eval linPScmSimEval (1 : ℝ) (3 : ℝ)

-- θ = 2，x = 3 ⟹ 应为 6
#eval linPScmSimEval (2 : ℝ) (3 : ℝ)

-- 同一组值用 ℚ 口径再跑一遍，得到可读的分数输出（3/2, 3, 6）
#eval (((1 : ℚ) / 2) * 3)
#eval ((1 : ℚ) * 3)
#eval ((2 : ℚ) * 3)

/-! ===========================================================================
    §3  `#eval` 结果的定理化：数值不是抽样，是等式
    =========================================================================== -/

/-- ⭐⭐ **θ = 1/2、x = 3 时 `sim` 的值经 `linPScmSimEval` 精确等于 `3/2`**。

这把 §2 的第一个 `#eval` 输出**钉成定理**（不是「机器恰好算了 3/2」）。 -/
theorem sim_half_three :
    linPScmSimEval (((1 : ℚ) / 2 : ℚ) : ℝ) (3 : ℝ) = 3 / 2 := by
  unfold linPScmSimEval
  push_cast
  norm_num

/-- ⭐⭐ **θ = 1、x = 3 时 `sim` 的值经 `linPScmSimEval` 精确等于 `3`**。 -/
theorem sim_one_three :
    linPScmSimEval (1 : ℝ) (3 : ℝ) = 3 := by
  unfold linPScmSimEval
  norm_num

/-- ⭐⭐ **θ = 2、x = 3 时 `sim` 的值经 `linPScmSimEval` 精确等于 `6`**。 -/
theorem sim_two_three :
    linPScmSimEval (2 : ℝ) (3 : ℝ) = 6 := by
  unfold linPScmSimEval
  norm_num

/-- ⭐⭐⭐ **连续参数的「世界模型真的能算」总结**：
`θ ∈ {1/2, 1, 2}`、`x = 3` 时，`(paramScmWorldModel linPScm).sim … 1`
（经可计算镜像 `linPScmSimEval`）分别给出 `3/2, 3, 6` —— **正好是 `θ * x`**。

**⚠ 反同义反复核查**：结论是对**具体数值** `3/2, 3, 6` 的等式；前件里**没有**
`3/2`、`3`、`6` 中的任何一个，也没有任何把结论预先塞进去的假设——三个值是
由 `linPScmSimEval`（即 `sim`）在具体输入上**算出**的。 -/
theorem continuous_sim_values :
    linPScmSimEval (((1 : ℚ) / 2 : ℚ) : ℝ) (3 : ℝ) = 3 / 2
    ∧ linPScmSimEval (1 : ℝ) (3 : ℝ) = 3
    ∧ linPScmSimEval (2 : ℝ) (3 : ℝ) = 6 :=
  ⟨sim_half_three, sim_one_three, sim_two_three⟩

/-- ⭐⭐ **这组数值**确实来自库里的 `sim`（不是只在镜像上成立）：
经 `linPScmSimEval_eq_sim` 把每个值翻译回 `(paramScmWorldModel linPScm).sim`。 -/
theorem continuous_sim_values_via_worldmodel :
    (paramScmWorldModel linPScm).sim (((1 : ℚ) / 2 : ℚ) : ℝ)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (3 : ℝ)) 1 = 3 / 2
    ∧ (paramScmWorldModel linPScm).sim (1 : ℝ)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (3 : ℝ)) 1 = 3
    ∧ (paramScmWorldModel linPScm).sim (2 : ℝ)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (3 : ℝ)) 1 = 6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← linPScmSimEval_eq_sim]; exact sim_half_three
  · rw [← linPScmSimEval_eq_sim]; exact sim_one_three
  · rw [← linPScmSimEval_eq_sim]; exact sim_two_three

/-- ⭐ **非退化性：连续参数确实改变预测** —— `θ = 1/2` 与 `θ = 2` 的预测
（`3/2` vs `6`）**不相等**。这说明上面一组数不是常数函数的抽样。 -/
theorem continuous_sim_nondegenerate :
    linPScmSimEval (((1 : ℚ) / 2 : ℚ) : ℝ) (3 : ℝ)
      ≠ linPScmSimEval (2 : ℝ) (3 : ℝ) := by
  rw [sim_half_three, sim_two_three]
  norm_num

end ContinuousEval
end Fate
