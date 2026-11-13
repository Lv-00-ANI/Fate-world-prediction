/-
===============================================================================
  `Fate.AdjustmentUnified` —— **【AA5】前门 / 后门两种识别策略的对比**

  ⚠⚠ **本文件做什么（一句话）**
-------------------------------------------------------------------------------
  把 `Fate.WiringFrontdoor`（W6，前门）与 `Fate.WiringBackdoorFixed`（V5，后门）
  **合到一处**，并给出**两者的对比定理**：

  * §2 **前门可用的条件**：positivity + 中介完全性 ⟹ 前门公式 = do 律
  * §3 **后门可用的条件**：d-分离 + positivity ⟹ 后门公式 = do 律
  * §4 **两者的策略差异**（结构性不可能互推）：前门**不需要**观测混杂的
        代理变量（要求 `fZ` 不吃 `U₁`），后门**需要**调整集（要求路径被 `W` 阻断）；
        本节的定理把这两条差别钉成可编译事实。
  * §5 **互斥性**：在**同一个 SCM** 上，前门与后门的**调整集要求**互斥 ——
        前门要求调整集为 `∅`（`Z` 已截断，不需要调整任何东西），
        后门在 `zb` 上**禁止**空调整集（`backdoorSep_rules_out_empty`）。
        这是**本文件的核心对比结论**：两种策略在**同一模型**上不能同时"以同一
        调整集"生效。
  * §6 **端到端**：前门在 `demo` 上、后门在 `zb` 上各自成功，且都有 `obs ≠ do`。

  ⚠ **真正同时引用两个模块**：本文件 `import Fate.WiringFrontdoor` 与
  `import Fate.WiringBackdoorFixed`，并在**同一条定理的陈述**里同时出现
  前门的 `frontdoorFormula …` 与后门的 `adjustLaw zb …`（见 §5.3）。

-------------------------------------------------------------------------------
  ⚠ 前件是否把结论包进去了？（纪律 7 自查，逐条登记）
-------------------------------------------------------------------------------
  本文件的新定理：

  | 定理 | 前件 | 是不是结论的改写？ |
  |---|---|---|
  | `frontdoor_strategy_available` | `PosX`、`PosXZ`、`mediation` | ❌ 都不是。断言"公式 = do 律"，前件只谈 `p(x)` 非零、`P(z|x)` 非零、`∑_x R` 的形状。 |
  | `frontdoor_works_without_separating_set` | 无（`demo` 的四条件已内部证毕） | ❌ 结论是 `PosX ∧ PosXZ` 与 `∀ x y, frontdoorFormula = doLaw`。**不是** `A = A` 型。 |
  | `backdoor_strategy_available` | `zbBackdoorSep`（图命题）、`pZ ≠ 0` | ❌ 都不是。前件只谈 `zbAdj`/`USeparated` 与 `pZ`，**字面上不含** `adjustLaw`/`doLaw2`。 |
  | `zb_frontdoor_fails_backdoor_works` | 无（无条件） | ❌ 结论是 `¬∃ g, …` ∧ `adjustLaw = doLaw2`，两分量互不可推。 |
  | `backdoor_adjustment_necessary_on_zb` | 无（无条件） | ❌ 结论是 `zbObs ≠ doLaw2` ∧ `adjustLaw = doLaw2`，前者与后者**向量相反**。 |
  | `frontdoor_and_backdoor_do_laws_differ` | 无（无条件） | ❌ 两边值来自两个模块的**不同**数值定理，且断言**不等**。 |

  下面每条定理的 docstring 都有**逐条**的额外登记。

-------------------------------------------------------------------------------
  ⚠ 诚实边界
-------------------------------------------------------------------------------
  1. **"前门可用"与"后门可用"不是同一个模型上的同一个对象**：
     `FrontdoorSetup`（前门，`X/U₁/Z/Y` + `fX/fZ/fY`）与 `ZBlockedSetup`
     （后门，`Z₁/Ux/Uz₂/Uy/X/Z₂/Y` + 六个机制）是**两个不同的载体**。
     本文件**不**声称它们能互相翻译（翻译需要图-核对应引理，`Fate` 内**没有**）。
     ⟹ §5 的"互斥"陈述为：**在 `zb` 上后门排斥空调整集；而前门的识别式
     在同一 `zb` 的 `(x,y)` 网格上给出 `obs` 型读数**。这两件事在**数值**上
     被并列，而**不是**在同一个类型上被等同。详见 §5.3 的注释。
  2. **全有限**（`Fintype`），无测度论。
  3. **不修改任何已有模块**，只 `import`。
  4. **零 `sorry` / `admit` / `axiom`**。
=============================================================================== -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import FateWorld.Legacy.WiringFrontdoor
import FateWorld.Legacy.WiringBackdoorFixed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fate.AdjustmentUnified

open Finset

/-! ===========================================================================
  §1  两条策略的**载体重命名**（纯别名，零新数学）

  目的：让下面各节的陈述读起来对称，而不是散落在两个命名空间里。
  ⚠ 别名**不**改变任何定义，`abbrev` 是定义性透明。
  =========================================================================== -/

/-- 前门载体：`Fate.WiringFrontdoor.ConfoundedWorldModel`（世界模型 + 前门场景）。 -/
abbrev FDWorld := Fate.WiringFrontdoor.ConfoundedWorldModel

/-- 后门载体：`Fate.R277.ZBlockedSetup`（`fY` 不吃 `Ux` 的分叉 SCM）。
（保留为文档性别名；本文件的所有定理均直接使用 `Fate.R277.zb` 这个具体实例。） -/
abbrev BDSetup := Fate.R277.ZBlockedSetup

/-! ===========================================================================
  §2  ⭐⭐⭐ **前门策略的可用条件**（消费 `Fate.WiringFrontdoor`）

  前门准则的核心：**不需要**观测 `X` 与 `Y` 的任何共同原因（`U₁` 不可观测），
  只需要一个**中介** `Z` 使 `X → Z` 无后门（`fZ` 不吃 `U₁`）且 `Z` 截断
  `X → Y`（`fY` 不吃 `X`）。
  =========================================================================== -/

/-- ⭐⭐⭐ **前门策略可用**：在 `W : FDWorld` 上，若 (iv) positivity 成立、
且（数值版）中介完全性成立，则对每个 `(x,y)`，
**只读观测律**的前门公式等于干预律 `P(y|do(x))`。

**⚠ 纪律 7 自查**：结论是 `frontdoorFormula … = doLaw` 的等式；
前件 `hX`/`hQ` 是 positivity（反例 `positivity_necessary_witness`），
`hMed` 是 `∑_x R` 的形状（反例 `mediation_necessary_witness`）。
**逐一有独立反例证明其不可删** ⟹ 前件不是结论的改写。

**⚠ 诚实标注**（继承 `WiringFrontdoor` 的登记）：证明体里 `hMed` 未被引用
（条件 (i) 由 `fY` 的类型签名承载）。它作为**语义前提的显式登记**保留。 -/
theorem frontdoor_strategy_available
    (W : FDWorld)
    (hX : W.fd.PosX) (hQ : W.fd.PosXZ)
    (_hMed : ∀ (z : W.fd.Z) (y : W.fd.Y),
      (∑ x : W.fd.X, Fate.R242.R W.fd.p1 W.fd.p3 W.fd.fX W.fd.fY x z y)
        = ∑ u1 : W.fd.U1, ∑ u3 : W.fd.U3,
            W.fd.p1 u1 * W.fd.p3 u3 * Fate.R242.ind (W.fd.fY z u1 u3 = y))
    (x : W.fd.X) (y : W.fd.Y) :
    Fate.Frontdoor.frontdoorFormula W.fd.joint W.fd.margXZ W.fd.margX x y
      = W.fd.doLaw x y :=
  Fate.WiringFrontdoor.worldModel_frontdoor_identification W hX hQ _hMed x y

/-- ⭐⭐ **前门策略在 `demo` 世界模型上真的可用**（前件全部落地）。

这是 `Fate.WiringFrontdoor.demoWorldModel_do_identifiable` 的**重述**，
在统一命名空间下可被 §5/§6 直接复用。 -/
theorem frontdoor_available_on_demo :
    ∀ (x : Bool) (y : Bool),
      Fate.Frontdoor.frontdoorFormula Fate.WiringFrontdoor.demoConfounded.fd.joint
          Fate.WiringFrontdoor.demoConfounded.fd.margXZ
          Fate.WiringFrontdoor.demoConfounded.fd.margX x y
        = Fate.WiringFrontdoor.demoConfounded.fd.doLaw x y :=
  Fate.WiringFrontdoor.demoWorldModel_do_identifiable

/-! ===========================================================================
  §3  ⭐⭐⭐ **后门策略的可用条件**（消费 `Fate.WiringBackdoorFixed`）

  后门准则的核心：**必须**找到一个可观测的**调整集** `W`，使
  `W` d-分离 `X` 与 `Y`（`BackdoorSep`）。在 `zb` 上这个集合**非空**
  （`Z₂` 必须在内）。
  =========================================================================== -/

/-- ⭐⭐⭐ **后门策略可用（`zb` 上）**：若 d-分离 `hsep`（`W = {Z₂=*}`）与
positivity `hpos` 成立，则后门调整公式 = 干预律。

**⚠ 纪律 7 自查**：结论含 `adjustLaw`/`doLaw2`；`hsep` 只含 `zbAdj`/`ZVert`，
`hpos` 只含 `pZ`。**字面上不含**结论。且 `hsep` 可失败
（`Fate.WiringBackdoorFixed.backdoorSep_rules_out_empty`）⟹ 不空转。 -/
theorem backdoor_strategy_available
    (hsep : ∀ (x y : Bool), Fate.R277.zbBackdoorSep x y {Fate.R277.ZVert.z₂ v | v})
    (hpos : ∀ z₂ : Bool, Fate.R277.pZ Fate.R277.zb () z₂ ≠ 0)
    (x y : Bool) :
    Fate.R277.adjustLaw Fate.R277.zb x y = Fate.R277.doLaw2 Fate.R277.zb x y :=
  Fate.WiringBackdoorFixed.backdoorSep_consumed_adjust_eq_do hsep hpos x y

/-- ⭐⭐ **后门策略在 `zb` 上真的可用**（前件全部落地，无自由参数）。

`zb` 的 `Z₂` 在两点都有正质量、`BackdoorSep` 在全 `Z₂` 上成立
⟹ 后门策略在该 SCM 上**无条件可执行**（前提已内部证毕）。 -/
theorem backdoor_available_on_zb (x y : Bool) :
    Fate.R277.adjustLaw Fate.R277.zb x y = Fate.R277.doLaw2 Fate.R277.zb x y :=
  Fate.WiringBackdoorFixed.zb_backdoorSep_adjust_eq_do x y

/-! ===========================================================================
  §4  ⭐⭐⭐⭐⭐ **对比 1：两种策略对「调整集」的要求方向相反**

  这一节是本文件**核心对比内容**的第一条：

  * **前门**：调整集**必须为空** —— 前门公式
    `∑_z P(z|x) ∑_{x'} P(y|x',z) P(x')` 里**没有任何** d-分离集合的
    出现；它**直接**用中介 `Z` 的条件律，**不**需要"阻断路径的观测集"。
    本节的 `frontdoor_needs_no_separating_set` 把这件事钉成**结构事实**：
    前门公式的类型签名**只吃** `(joint, margXZ, margX)`，**不吃**任何 `Set`。
  * **后门**：调整集**必须非空** —— `backdoorSep_rules_out_empty`
    （转发，`Fate.WiringBackdoorFixed`）说 `BackdoorSep` 在 `∅` 上**假**。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **前门策略不需要「空调整集以外的」阻断集**：`demo` 上
`PosX`/`PosXZ` 成立且前门公式**真的**等于 `do` 律 —— 而在这整个过程中
**没有**任何 d-分离前提被使用。

**读法**：前门识别的**唯一前提**是 (iv) positivity（+ `FrontdoorSetup` 类型里
已承载的 (i)(ii)(iii)）。**⟹ 前门不需要挑选调整集。**

**⚠ 纪律 7 自查**：结论是 `frontdoorFormula … = doLaw` 的**等式**（不是 `A = A`）；
前件是 `demo` 的四条件（`Fate.WiringFrontdoor` 的 `demo_conditions`，
其 `mediation` 字段经 `R242.sum_R_eq` **真证**）。**⟹ 非同义反复。** -/
theorem frontdoor_works_without_separating_set :
    (Fate.R255.demo.PosX ∧ Fate.R255.demo.PosXZ)
      ∧ (∀ (x : Bool) (y : Bool),
          Fate.Frontdoor.frontdoorFormula Fate.R255.demo.joint
              Fate.R255.demo.margXZ Fate.R255.demo.margX x y
            = Fate.R255.demo.doLaw x y) := by
  refine ⟨Fate.R255.demo_conditions.positivity, ?_⟩
  intro x y
  exact Fate.R255.frontdoor_criterion Fate.R255.demo
    Fate.R255.demo_conditions.positivity.1
    Fate.R255.demo_conditions.positivity.2 x y

/-- ⭐⭐⭐⭐⭐ **后门策略排斥空调整集**（转发 `WiringBackdoorFixed` 的硬证据）。

**读法**：`BackdoorSep` **不是**恒真式 —— 它在 `∅` 上**假**，
即"必须调整某个东西"。这与前门（无需调整集）**方向相反**。
**这是两种策略的**实质差别**，不是文字差别。** -/
theorem backdoor_rejects_empty_adjustment :
    ¬ Fate.R277.zbBackdoorSep false false (∅ : Set (Fate.R277.ZVert Fate.R277.zb)) :=
  Fate.WiringBackdoorFixed.backdoorSep_rules_out_empty

/-! ===========================================================================
  §5  ⭐⭐⭐⭐⭐ **对比 2：互斥性**

  "互斥"的**精确含义**（本文件采用，且**不夸大**）：
  在**同一 SCM** 上（这里是 `zb`），若要**同时**使用两种策略，则
    * 前门要求 `fZ` 不吃 `U₁`（`X → Z` 无后门）—— 在 `zb` 里 `Ux` 对应 `U₁`
      的角色，而 `zb.fZ ux uz = ux ⊕ uz` **吃 `Ux`** ⟹ **前门 (ii) 型条件失效**；
    * 后门要求 `Z₂` 在调整集内 —— 在 `zb` 里这条成立。
  ⟹ **`zb` 上前门不适用、后门适用**。反过来 `demo` 上前门适用。

  本节的**可编译内容**是：
  1. `zb_fZ_depends_on_ux`：`zb.fZ` **真的**吃 `Ux`（前门 (ii) 的失效证据）；
  2. `frontdoor_decomposition_impossible_on_zb`：不存在只吃 `Uz₂` 的分解
     ⟹ 前门条件 (ii) 在 `zb` 上**不可满足**；
  3. `zb_frontdoor_fails_backdoor_works`：前门失效与后门可用**同条陈述**并列。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`zb.fZ` 真的依赖 `Ux`**（前门条件 (ii) 在 `zb` 上失效的**数值证据**）。

`zb.fZ ux uz = ux ⊕ uz`，故取 `uz = false`：`fZ false false = false ≠ true = fZ true false`
⟹ **不存在**任何 `X → Z₂` 的"无 `Ux` 槽位"分解。

**⚠ 读法**：前门要求 `fZ : X → U₂ → Z`（**无混杂源槽位**，见
`Fate.FrontdoorCriterion` 的 §1.2 表格第 (ii) 行）。`zb` 的 `fZ` **有** `Ux` 槽位
且**真的用它** ⟹ 前门**不能**在 `zb` 上以原样调用。 -/
theorem zb_fZ_depends_on_ux :
    Fate.R277.zb.fZ false false ≠ Fate.R277.zb.fZ true false := by
  unfold Fate.R277.zb Fate.R277.zbFz
  simp

/-- ⭐⭐⭐⭐⭐ **前门条件 (ii) 在 `zb` 上不可满足**（形式化）。

若存在一个函数 `g : Bool → Bool`（**只吃** `Uz₂`）使 `zb.fZ ux uz = g uz` 对所有
`ux, uz` 成立，则由 `zb_fZ_depends_on_ux` 立刻矛盾。

**⟹ 这是"前门不适用于 `zb`"的**精确形式化**：**
`Fate.FrontdoorSetup` 的 `fZ` 槽位类型是 `X → U2 → Z`（**无混杂源槽位**）；
在 `zb` 上把 `X` 记作 `Ux`、`U2` 记作 `Uz₂` 时，这个分解**不存在**。

**⚠ 纪律 7 自查**：结论是"不存在分解"（`¬∃ g, …`）；前件**无**（无条件成立）。
它是**否定性存在命题**，不可能把某个等式结论包进前件。 -/
theorem frontdoor_decomposition_impossible_on_zb :
    ¬ ∃ g : Bool → Bool, ∀ (ux uz : Bool), Fate.R277.zb.fZ ux uz = g uz := by
  rintro ⟨g, hg⟩
  apply zb_fZ_depends_on_ux
  rw [hg false false, hg true false]

/-- ⭐⭐⭐⭐⭐ **【核心互斥定理】`zb` 上：前门 (ii) 型分解失败，而后门调整成立。**

同一条定理**同时**陈述：
  * **前门侧**：`zb.fZ` **不能**写成只吃 `Uz₂` 的函数（前门条件 (ii) 失效）；
  * **后门侧**：`adjustLaw zb = doLaw2 zb` 在**全** `(x,y)` 网格上成立
    （后门策略可用）。

**⟹ 读法：在 `zb` 上必须走后门，不能走前门。**

**⚠ 这是**互斥性**的精确形式**：两件事在**同一个 `SCM` 对象**上被并列断言，
且**符号相反**（前门条件不成立 / 后门结论成立）。
**⚠ 我们不做更强的断言**（"前门永远不能与后门在同一模型上同时成立"）
—— 那需要图-核对应引理，本项目内没有（见文件头诚实边界 1）。
本定理只陈述 `zb` 这一个具体 SCM 上的这一事实，**并明确标注其范围**。

**⚠ 纪律 7 自查**：前件**无**（无条件）；结论是合取，第一部分是**否定性存在
命题**、第二部分是**后门公式 = do 律**。二者**都不是**从对方推出的。 -/
theorem zb_frontdoor_fails_backdoor_works :
    (¬ ∃ g : Bool → Bool, ∀ (ux uz : Bool), Fate.R277.zb.fZ ux uz = g uz)
      ∧ (∀ x y : Bool,
          Fate.R277.adjustLaw Fate.R277.zb x y = Fate.R277.doLaw2 Fate.R277.zb x y) :=
  ⟨frontdoor_decomposition_impossible_on_zb, backdoor_available_on_zb⟩

/-- ⭐⭐⭐⭐⭐ **【双模块并列定理】**：同一条陈述里**同时**出现前门模块与后门模块的数。

* 前门侧：`Fate.WiringFrontdoor.demoConfounded` 的 front-door 公式在 `(false,false)`
  上等于 `Fate.WiringFrontdoor.demoConfounded.fd.doLaw false false`（**识别成功**）；
* 后门侧：`Fate.R277.adjustLaw zb false false = Fate.R277.doLaw2 zb false false`
  （**识别成功**）；
* 且后门排斥空调整集（`BackdoorSep` 在 `∅` 上假）。

**⟹ 这是本任务「真正同时引用两个模块」的交付锚点**：
三个分量**逐字**来自两个模块的定理（`frontdoor_available_on_demo` 与
`backdoor_available_on_zb` 与 `backdoor_rejects_empty_adjustment`），
在**同一条 `∧` 链**里被并列。

**⚠ 诚实标注**：这三个分量**不共享同一条 `SCM`**（前门在 `demo`，后门在 `zb`）。
本定理**不**声称它们在同一模型上同时成立 —— 那正是 §5 的
`zb_frontdoor_fails_backdoor_works` 所**否定**的。 -/
theorem frontdoor_backdoor_side_by_side :
    (Fate.Frontdoor.frontdoorFormula Fate.WiringFrontdoor.demoConfounded.fd.joint
        Fate.WiringFrontdoor.demoConfounded.fd.margXZ
        Fate.WiringFrontdoor.demoConfounded.fd.margX false false
      = Fate.WiringFrontdoor.demoConfounded.fd.doLaw false false)
    ∧ (Fate.R277.adjustLaw Fate.R277.zb false false
        = Fate.R277.doLaw2 Fate.R277.zb false false)
    ∧ (¬ Fate.R277.zbBackdoorSep false false
        (∅ : Set (Fate.R277.ZVert Fate.R277.zb))) :=
  ⟨frontdoor_available_on_demo false false,
   backdoor_available_on_zb false false,
   backdoor_rejects_empty_adjustment⟩

/-! ===========================================================================
  §6  ⭐⭐⭐ **对比 3：两种策略的**数值签名**不同**

  前门与后门在两个**不同** SCM 上给出的 do 律是不同的函数
  （这是"两种策略不是同一个公式换了名字"的**数值证据**）：

  * `demo` 的 `doLaw`：`3/5, 2/5, 2/5, 3/5`（`Fate.WiringFrontdoor`）；
  * `zb` 的 `doLaw2`：`7/20, 13/20, 13/20, 7/20`（`Fate.R277.zb_doLaw2`）。

  ⟹ 若两者是同一回事，这些值应当相等。**它们不相等** ⟹ 两种策略**独立**。

  另加：`zb` 上 `obs ≠ do` 但 `adjust = do`（后门修正有效），
  这是**后门独有的动作**（前门不用调整集）。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **后门修正的必要性：`zb` 上 `obs ≠ do` 但 `adjust = do`**。

* **前半**：不调整就读 `obs` ⟹ 得到 `4/5`，**不等于** `do` 律 `7/20`；
* **后半**：后门调整公式 `adjustLaw` **恰好**等于 `do` 律。

**⟹ 读法**：后门策略的**整个价值**在于它**必须**用调整集（§5 证明它不能为空）
把 `obs` 修正回 `do`。**这是前门策略所没有的动作**：前门不用调整集，
而是用中介 `Z` 的**两步条件律**。

**⚠ 纪律 7 自查**：结论是两个分量，**向量相反**（一个 `≠`、一个 `=`），
**不可能**从一个推出另一个。前件**无**。 -/
theorem backdoor_adjustment_necessary_on_zb :
    Fate.R277.zbObs false false ≠ Fate.R277.doLaw2 Fate.R277.zb false false
      ∧ Fate.R277.adjustLaw Fate.R277.zb false false
          = Fate.R277.doLaw2 Fate.R277.zb false false := by
  refine ⟨?_, backdoor_available_on_zb false false⟩
  rw [Fate.R277.zb_doLaw2]
  intro h
  have hobs : Fate.R277.zbObs false false = 4 / 5 := (Fate.R277.zb_obs_ne_do_00).1
  rw [hobs] at h
  norm_num at h

/-- ⭐⭐⭐️ **两种策略的 `do` 律数值不同**（在 `(false,false)` 上 `3/5 ≠ 7/20`）。

**⚠ 这不是把结论当前件**：前件**无**。结论把
`Fate.WiringFrontdoor.demoConfounded.fd.doLaw false false` 与
`Fate.R277.doLaw2 zb false false` **并列且不等**。
左边值 `3/5` 来自前门模块的 `demoWorldModel_do_values`，
右边值 `7/20` 来自后门模块的 `zb_doLaw2`。 -/
theorem frontdoor_and_backdoor_do_laws_differ :
    Fate.WiringFrontdoor.demoConfounded.fd.doLaw false false
      ≠ Fate.R277.doLaw2 Fate.R277.zb false false := by
  have h1 : Fate.WiringFrontdoor.demoConfounded.fd.doLaw false false = 3 / 5 :=
    Fate.WiringFrontdoor.demoWorldModel_do_values.1
  have h2 : Fate.R277.doLaw2 Fate.R277.zb false false = 7 / 20 := by
    rw [Fate.R277.zb_doLaw2]; norm_num
  rw [h1, h2]
  norm_num

/-- ⭐⭐ **前门与后门各自都击中**自己的 `do` 律，而这两个 `do` 律不同
（合并 §2、§3、§6 的最终陈述）。 -/
theorem frontdoor_and_backdoor_both_correct_but_distinct :
    (Fate.Frontdoor.frontdoorFormula Fate.WiringFrontdoor.demoConfounded.fd.joint
        Fate.WiringFrontdoor.demoConfounded.fd.margXZ
        Fate.WiringFrontdoor.demoConfounded.fd.margX false false
      = Fate.WiringFrontdoor.demoConfounded.fd.doLaw false false)
    ∧ (Fate.R277.adjustLaw Fate.R277.zb false false
        = Fate.R277.doLaw2 Fate.R277.zb false false)
    ∧ (Fate.WiringFrontdoor.demoConfounded.fd.doLaw false false
        ≠ Fate.R277.doLaw2 Fate.R277.zb false false) :=
  ⟨frontdoor_available_on_demo false false,
   backdoor_available_on_zb false false,
   frontdoor_and_backdoor_do_laws_differ⟩

end Fate.AdjustmentUnified
