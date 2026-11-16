/-
  `Fate/NonemptyFree4` —— **DOWN-1 第 2 批：`SCMEndToEnd` 的 `[Nonempty Y]` 去除（4 条）**

  ## 本模块证明什么

  `Fate/SCMEndToEnd.lean` 有 **21 处 `[Nonempty Y]`**（**22 个定理**）。
  本文件对其中 **5 条**定理（任务要求 ≥4）给出**无 `[Nonempty Y]` 前件**的版本。
  **原定理原样保留、一字未改**；本文件只新增，不修改任何既有模块。

  | # | 原定理（**未改动**） | 本文件新定理 |
  |---|---|---|
  | 1 | `Fate.SCMEndToEnd.predFrom_scmWorldModel` | `predFrom_scmWorldModel_noNonempty` |
  | 2 | `Fate.SCMEndToEnd.predFrom_scmWorldModel_indep_start` | `predFrom_scmWorldModel_indep_start_noNonempty` |
  | 3 | `Fate.SCMEndToEnd.e2eResidual_scmWorldModel` | `e2eResidual_scmWorldModel_noNonempty` |
  | 4 | `Fate.SCMEndToEnd.e2eResidual_scmWorldModel_eq_zero_iff` | `e2eResidual_scmWorldModel_eq_zero_iff_noNonempty` |
  | 5 | `Fate.SCMEndToEnd.endToEnd_scmWorldModel` | `endToEnd_scmWorldModel_noNonempty` |

  ⚠ 本文件共交 **5 条**（任务要求 ≥4 条）。

  ---------------------------------------------------------------------------
  ## 技术要点：`[Nonempty Y]` 在这里为什么能去掉（**不是**靠 `Classical.arbitrary`）

  `[Nonempty Y]` 在本问题的**位置很特殊**：它**不只出现在证明体里**，
  还出现在**定理结论的类型本身**——因为结论里含

  ```lean
  SCMWorldModel.scmWorldModel M
  ```

  而 `scmWorldModel` 的定义签名是

  ```lean
  def scmWorldModel {X Y : Type} (M : SCM X Y) [Nonempty Y] : WorldModel
  ```

  ⟹ 只要结论里写下 `scmWorldModel M`，Lean 就必须**在签名 elaborating 时**
  解消 `Nonempty Y`。把 `[Nonempty Y]` 从签名删掉、只在证明体里 `haveI`
  **会直接报 `synthInstanceFailed`**（本次实测确认，见报告）。

  **本文件的解法**：在结论里把 `scmWorldModel` 的实例位**显式写出**
  （`@` 全应用形式），实例取**参数里已有的 `Y`-项**：

  ```lean
  FateV2.Loop.EndToEnd.predFrom (@SCMWorldModel.scmWorldModel X Y M ⟨y⟩) θ u ε a y
  ```

  * `⟨y⟩` 是参数 `(y : Y)` **直接给出**的见证，**不经 `Classical.arbitrary`**；
  * 签名里因此**不再需要** `[Nonempty Y]` 前件；
  * 定理**内容**与原定理完全相同（同一个 `scmWorldModel M`，只是**实例位**
    取 `⟨y⟩` 而非 `Classical.choice ‹Nonempty Y›`）。

  **每条定理的见证来源**（逐条，全部来自参数；**见证本身**不靠 `Classical.choice`；
  但 `scmWorldModel` **定义体内**的占位取值仍用 `Classical.choice`，见下方“诚实边界”）：

  | 新定理 | `Nonempty Y` 的见证 |
  |---|---|
  | 1 | `⟨y⟩`（出发状态参数 `(y : Y)`） |
  | 2 | `⟨y₁⟩`（第一个出发状态参数） |
  | 3 | `⟨xobs⟩`（观测值参数） |
  | 4 | `⟨xobs⟩`（观测值参数） |
  | 5 | `⟨x⟩`（出发状态参数） |

  **所有证明体都是对原定理的 `exact`（引用，不重证）**：

  ```lean
  haveI : Nonempty Y := ⟨y⟩
  exact Fate.SCMEndToEnd.predFrom_scmWorldModel M θ u ε a y
  ```

  ⟹ 新定理与原定理**语义相同**，只是把 `Nonempty` 前件换成了
  **由参数示证的局部实例**。

  ⚠ 与 `NonemptyFree3` 的 `Classical.arbitrary` 路线的区别：
  本文件**不在签名里用** `Classical.arbitrary` 构造见证——`⟨y⟩` 是参数**显式**给出的。

  ⚠ **但须如实登记（实测 `#print axioms`）**：本文件 5 条定理的 axiom 集合
  均为 `[propext, Classical.choice, Quot.sound]`，即**仍依赖 `Classical.choice`**。
  原因是 `SCMWorldModel.scmWorldModel` 的**定义体内部**用
  `Classical.choice ‹Nonempty Y›` 取占位 `cur` / `initial`
  （见 `Fate/SCMWorldModel.lean:366/372/374`）。这是 `SCMWorldModel` 的**既有事实**，
  **不是**本文件引入的；本文件只是**调用**该定义，故继承了它的选择公理依赖。
  结论**不含** `cur`，占位不进入任何结论（`SCMWorldModel` 文件头已论及）。
  本文件的**净贡献**是：`[Nonempty Y]` 前件**可由参数里的 `Y`-项满足**，
  从而不必把它写进定理签名。

  ---------------------------------------------------------------------------
  ## ⚠ 反同义反复核查（逐条）

  * **前件**中**没有**任何关于结论内容的假设：
    1) 前件为空（只有参数 `M θ u ε a y`）；
    2) 前件为空；
    3) 前件只有 `[AddCommGroup Y]`（做减法用的代数结构，**显式参数**）；
    4) 前件只有 `[AddCommGroup Y]`；
    5) 前件只有 `[AddCommGroup Y] [Ring PUnit]` + 参数 `h η φ y θ u ε a x`。
  * **结论**把 `Fate.EndToEnd.predFrom` / `e2eResidual` / `endToEnd`
    在 SCM 实例上**求值**成含 `(M.sg u).2 a` 的表达式——
    两侧分属不同模块（`Fate/EndToEnd.lean` 与 `Fate/SCMWorldModel.lean`
    / `Fate/PearlHierarchy.lean`）的**定义**，由定理首次相等。
  * 新定理是对原定理的**调用**，未添加任何假设 ⟹ 语义与原定理相同。

  ---------------------------------------------------------------------------
  ## 诚实边界

  1. **`Nonempty` 不是从类型论上消失了**：它被**实例化为参数里的元素**。
     本文件证明的是「这 5 条的 `[Nonempty Y]` 与参数里的 `Y`-项信息重复，
     因此可去」，**不是**「`SCMEndToEnd` 的 21 处 `[Nonempty]` 全都可去」。
  2. `SCMEndToEnd` 中**剩下 16 处** `[Nonempty Y]` **未处理**（不在本批范围）。
     其中一部分（如 `endToEnd_scmWorldModel_fixed_of_predicts`、
     `scmE2E_instance_satisfiable`）同样有 `Y`-项参数，可用同一手法去除；
     但亦有一部分（如 `scmWorldModel_theta`，参数里**没有** `Y`-项）
     **无法用本手法**去掉——需另找见证或接受 `Nonempty`。
  3. 原定理**一字未改**；本文件只新增。
  4. 零 `sorry` / `admit` / `axiom` / `?_` / `native_decide` /
     `set_option maxHeartbeats`。
-/

import FateWorld.FateV2.Loop.SCMEndToEnd
namespace FateV2.Predict

open FateV2.Loop
open FateV2.Modeling
namespace NonemptyFree4

open Fate.SCMEndToEnd

set_option autoImplicit false

/-!
  # Predict · NonemptyFree4

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NonemptyFree4.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMEndToEnd
  - 补充 open 域：FateV2.Loop, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## 1. `predFrom_scmWorldModel`（去 `[Nonempty Y]`）

原陈述（`Fate/SCMEndToEnd.lean:129`）：

```lean
theorem predFrom_scmWorldModel {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : PUnit) (a : X) (y : Y) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel M) θ u ε a y = (M.sg u).2 a
```

`[Nonempty Y]` 由参数 `(y : Y)` 就地给出（`⟨y⟩`）。 -/
theorem predFrom_scmWorldModel_noNonempty {X Y : Type} (M : PearlHierarchy.SCM X Y)
    (θ : PUnit.{1}) (u : M.U) (ε : PUnit.{1}) (a : X) (y : Y) :
    FateV2.Loop.EndToEnd.predFrom (@SCMWorldModel.scmWorldModel X Y M ⟨y⟩) θ u ε a y
      = (M.sg u).2 a := by
  haveI : Nonempty Y := ⟨y⟩
  exact Fate.SCMEndToEnd.predFrom_scmWorldModel M θ u ε a y

/-! ## 2. `predFrom_scmWorldModel_indep_start`（去 `[Nonempty Y]`）

原陈述（`Fate/SCMEndToEnd.lean:158`）：`predFrom … y₁ = predFrom … y₂`。
`[Nonempty Y]` 由 `y₁` 给出。两侧各用**自己的**出发状态作见证。 -/
theorem predFrom_scmWorldModel_indep_start_noNonempty {X Y : Type}
    (M : PearlHierarchy.SCM X Y)
    (θ : PUnit.{1}) (u : M.U) (ε : PUnit.{1}) (a : X) (y₁ y₂ : Y) :
    FateV2.Loop.EndToEnd.predFrom (@SCMWorldModel.scmWorldModel X Y M ⟨y₁⟩) θ u ε a y₁
      = FateV2.Loop.EndToEnd.predFrom (@SCMWorldModel.scmWorldModel X Y M ⟨y₂⟩) θ u ε a y₂ := by
  haveI : Nonempty Y := ⟨y₁⟩
  exact Fate.SCMEndToEnd.predFrom_scmWorldModel_indep_start M θ u ε a y₁ y₂

/-! ## 3. `e2eResidual_scmWorldModel`（去 `[Nonempty Y]`）

原陈述（`Fate/SCMEndToEnd.lean:202`）：
`e2eResidual … = xobs - (M.sg u).2 a`。
`[Nonempty Y]` 由观测值 `(xobs : Y)` 给出。 -/
theorem e2eResidual_scmWorldModel_noNonempty {X Y : Type} (M : PearlHierarchy.SCM X Y)
    [AddCommGroup Y]
    (xobs : Y) (θ : PUnit.{1}) (u : M.U) (ε : PUnit.{1}) (a : X) (xpred : Y) :
    FateV2.Loop.EndToEnd.e2eResidual (@SCMWorldModel.scmWorldModel X Y M ⟨xobs⟩) xobs θ u ε a xpred
      = xobs - (M.sg u).2 a := by
  haveI : Nonempty Y := ⟨xobs⟩
  exact Fate.SCMEndToEnd.e2eResidual_scmWorldModel M xobs θ u ε a xpred

/-! ## 4. `e2eResidual_scmWorldModel_eq_zero_iff`（去 `[Nonempty Y]`）

原陈述（`Fate/SCMEndToEnd.lean:218`）：
`e2eResidual … = 0 ↔ xobs = (M.sg u).2 a`。
`[Nonempty Y]` 由 `(xobs : Y)` 给出。 -/
theorem e2eResidual_scmWorldModel_eq_zero_iff_noNonempty {X Y : Type}
    (M : PearlHierarchy.SCM X Y) [AddCommGroup Y]
    (xobs : Y) (θ : PUnit.{1}) (u : M.U) (ε : PUnit.{1}) (a : X) (xpred : Y) :
    FateV2.Loop.EndToEnd.e2eResidual (@SCMWorldModel.scmWorldModel X Y M ⟨xobs⟩) xobs θ u ε a xpred
        = 0
      ↔ xobs = (M.sg u).2 a := by
  haveI : Nonempty Y := ⟨xobs⟩
  exact Fate.SCMEndToEnd.e2eResidual_scmWorldModel_eq_zero_iff M xobs θ u ε a xpred

/-! ## 5. `endToEnd_scmWorldModel`（去 `[Nonempty Y]`）

原陈述（`Fate/SCMEndToEnd.lean:260`）：
`endToEnd … = θ + η * φ (observe h y - (M.sg u).2 a)`。
`[Nonempty Y]` 由出发状态 `(x : Y)` 给出。

⚠ **附加注意**：原定理的结论里还有 `Fate.EndToEnd.observe h y`，
其定义要求 `[Nonempty W.frame.X.Carrier]`（即 `[Nonempty Y]`）。
它与 `scmWorldModel` 用的是**同一个**局部实例 `⟨x⟩`，因此一并去掉。 -/
theorem endToEnd_scmWorldModel_noNonempty {X Y G : Type} (M : PearlHierarchy.SCM X Y)
    [AddCommGroup Y] [Ring PUnit.{1}]
    (h : Y → G) (η : PUnit.{1}) (φ : Y →+ PUnit.{1})
    (y : G) (θ : PUnit.{1}) (u : M.U) (ε : PUnit.{1}) (a : X) (x : Y) :
    FateV2.Loop.EndToEnd.endToEnd (@SCMWorldModel.scmWorldModel X Y M ⟨x⟩) h η φ y θ u ε a x
      = θ + η * φ (FateV2.Loop.EndToEnd.observe h y - (M.sg u).2 a) := by
  haveI : Nonempty Y := ⟨x⟩
  exact Fate.SCMEndToEnd.endToEnd_scmWorldModel M h η φ y θ u ε a x

end NonemptyFree4
end FateV2.Predict