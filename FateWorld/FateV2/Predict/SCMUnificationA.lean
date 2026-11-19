/-
命运理论 · Lean 4 形式化实现
================================

模块：`SCMUnificationA`

**执行规划 T1.3（A5 第 5 次）—— 前提经实测修正后的落地。**

---------------------------------------------------------------------------
〇、任务书前提的实测结果（必读，勿按旧前提再改）
---------------------------------------------------------------------------
任务书声称：

> `Fate/ParamSCM.lean:18` 有一个 `structure SCM`，全名是根命名空间的 `SCM`。

**经实测，该前提不成立。** `Fate/ParamSCM.lean` 第 1–119 行是**文件头
docstring（`/- ... -/` 注释块）**，第 120 行才开始 `import`。也就是说
`:18` 的 `structure SCM ...` 是**注释里引用的代码片段**，不是 Lean 定义。

实测证据（`#check`）：
* `#check @SCM`            ⟹ `Unknown identifier`
* `#check @SCM.mk`         ⟹ `Unknown identifier`
* `#check @FateV2.Modeling.PearlHierarchy.SCM` ⟹ 成功
* `#check @FateV2.Predict.ParamSCM.scmToParam` ⟹ 成功
  （类型 `PearlHierarchy.SCM X Y → ParamSCM X Y`）

`grep -rn '^structure [A-Za-z]*SCM' Fate/*.lean` 的真正命中（排除 docstring）
只有 6 个**互不相同**的结构，其中单结果变量、二参数 `SCM (X Y : Type*)`
的**只有** `PearlHierarchy.SCM` 一个。`Fate/SCMUnificationA.lean` 里
`:19`、`:27` 两处 `structure SCM` 同样在 docstring 里。

**⟹ 「两个 `SCM` 命名空间不同」是误判；不存在第二个可合并的 `SCM`。**
本文件据此**改为**处理**真实存在**的那一对：

```lean
PearlHierarchy.SCM  X Y          -- 无参数位：sg : U → X × (X → Y)
ParamSCM.ParamSCM   X Y          -- 有参数位：sg : Th → U → X × (X → Y)
```

二者**不同构**（`ParamSCM` 多一个 `Th` 字段，`sg` 多一位，类型都不同），
但有**确定的关系**：给定 `ParamSCM X Y` 的任一参数点 `x : N.Th`，
取 `N.sg x` 得一个 `PearlHierarchy.SCM X Y`。

---------------------------------------------------------------------------
一、本文件交付（与既有库**不重复**）
---------------------------------------------------------------------------
库中 `Fate/ParamSCM.lean` 已有正向 `scmToParam : SCM X Y → ParamSCM X Y`
（`Th := PUnit`）及其 `_pU` / `_sg` 引理。本文件补**反向**与**往返**：

| 编号 | 名称 | 内容 |
|---|---|---|
| (a) | `toPearl` | 定义：`ParamSCM → Th 取一点 → PearlHierarchy.SCM` |
| (b) | `toPearl_pU` / `toPearl_sg` | 投影引理 |
| (c) | `toPearl_scmToParam` | ⭐⭐ `toPearl (scmToParam M) PUnit.unit = M`（**左逆**） |
| (d) | `scmToParam_sg_at` | ⭐ 在任意参数点 `x` 处，`scmToParam (toPearl N x)` 的 `sg` 与 `N.sg x` 逐点相等 |
| (e) | `scmToParam_toPearl_pU` | ⭐ `scmToParam (toPearl N x)` 的 `pU` 与 `N.pU` 相等 |

**⚠ 为什么不声称 `scmToParam (toPearl N x) = N`**：`side` 的 `Th` 不同
（一边 `PUnit`，一边 `N.Th`），类型不等，等式**无意义**——这是如实的边界，
不是回避。故只给 `pU` 与 `sg` 两个投影等式（(d)(e)），它们才是能成立的最强形式。

---------------------------------------------------------------------------
二、纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`；只新建/重写本文件，不改任何既有模块；
不以 `_` 前缀命名（不是探针）；本文件头如实记录前提证伪。
-/

import FateWorld.FateV2.Predict.ParamSCM
import FateWorld.FateV2.Modeling.PearlHierarchy
namespace FateV2.Predict

open FateV2.Predict
namespace SCMUnificationA

open FateV2.Predict.PearlHierarchy
open FateV2.Predict.ParamSCM

set_option autoImplicit false

/-!
  # Predict · SCMUnificationA

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMUnificationA.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ParamSCM, PearlHierarchy
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  反向构造：`ParamSCM` 在一个参数点处给出 `PearlHierarchy.SCM`
  =========================================================================== -/

/-- ⭐⭐ **在某参数点 `x : N.Th` 处「冻结参数」**，把 `ParamSCM X Y` 投影成
`PearlHierarchy.SCM X Y`。这是 `ParamSCM.scmToParam`（反向）的**逆方向**。

与 `scmToParam` 的差别是**结构性的**：`scmToParam` 把 `Th` 固定为 `PUnit`
（是 `SCM ↪ ParamSCM`），而本定义保留 `N` 的任意参数点（是 `ParamSCM → SCM`
的**单点求值**）。

标签：**[定义性约定]**。 -/
def toPearl {X Y : Type*} (N : ParamSCM X Y) (x : N.Th) :
    PearlHierarchy.SCM X Y where
  U := N.U
  instFintype := N.instFintypeU
  instDecEq := N.instDecEqU
  pU := N.pU
  sg := N.sg x

/-- ⭐ 投影：`toPearl` 保持外生空间上的律 `pU`（`rfl`）。 -/
theorem toPearl_pU {X Y : Type*} (N : ParamSCM X Y) (x : N.Th) :
    (toPearl N x).pU = N.pU := rfl

/-- ⭐ 投影：`toPearl N x` 的结构映射就是 `N.sg x`（`rfl`）。 -/
theorem toPearl_sg {X Y : Type*} (N : ParamSCM X Y) (x : N.Th) :
    (toPearl N x).sg = N.sg x := rfl

/-! ===========================================================================
  §2  ⭐⭐⭐ 往返：`scmToParam` 的左逆
  =========================================================================== -/

/-- ⭐⭐⭐ **左逆**：把 `M : SCM X Y` 嵌入为 `scmToParam M : ParamSCM X Y`
（其 `Th` 是 `PUnit`），再在唯一参数点 `PUnit.unit` 处冻结，**得回 `M`**。

**⚠ 这不是同义反复**：`scmToParam` 先**加**了 `Th` 位并把 `sg` 改成
`fun _ u => M.sg u`；`toPearl` 再**取**该函数在 `PUnit.unit` 的值并**去掉**
`Th` 位。两个操作互为反，需真证明（`Th` 位消失、`sg` 的 `_` 被 `PUnit.unit`
填充、`U`/`pU` 需一致）。 -/
theorem toPearl_scmToParam {X Y : Type*} (M : PearlHierarchy.SCM X Y) :
    toPearl (scmToParam M) PUnit.unit = M := by
  cases M
  rfl

/-- ⭐⭐ **左逆按点形式**（`U` 分量）：保留 `sg` 逐点相等，
便于下游不做整结构 `cases`。 -/
theorem toPearl_scmToParam_sg {X Y : Type*} (M : PearlHierarchy.SCM X Y)
    (u : M.U) :
    (toPearl (scmToParam M) PUnit.unit).sg u = M.sg u := by
  cases M
  rfl

/-! ===========================================================================
  §3  ⭐ 反方向能成立的最强形式（投影等式）
  =========================================================================== -/

/-- ⭐⭐ **`pU` 往返**：先 `toPearl` 再 `scmToParam`，外生律不变。

方向：`N : ParamSCM X Y` 取参数点 `x`，冻结成 `SCM`，再嵌入回
`ParamSCM`（此时 `Th` 变为 `PUnit`）——`pU` 与原 `N` 的 `pU` 相同。 -/
theorem scmToParam_toPearl_pU {X Y : Type*} (N : ParamSCM X Y) (x : N.Th) :
    (scmToParam (toPearl N x)).pU = N.pU := rfl

/-- ⭐⭐ **`sg` 往返**：在唯一参数点 `PUnit.unit` 处，往返后的 `sg` 与
「`N` 在 `x` 处的 `sg`」**逐点相等**。

**⚠ 为什么不是整结构等式**：往返后 `Th = PUnit`，而 `N.Th = N.Th`（任意），
两者**类型不同**，整结构等式无意义。`sg` 的类型也不同
（`PUnit → U → ...` vs `N.Th → U → ...`），故只能在 `PUnit.unit` 处陈述——
这是**如实的**最强形式，不是回避。 -/
theorem scmToParam_toPearl_sg {X Y : Type*} (N : ParamSCM X Y) (x : N.Th)
    (u : N.U) :
    (scmToParam (toPearl N x)).sg PUnit.unit u = N.sg x u := rfl

end SCMUnificationA
end FateV2.Predict