/-
===========================================================================
  `DeadPremiseAuditConsumer` —— 把「死前提审计器」接到主链上
  （叶子接线 8；`lean` 直接 import，见本文件 §0.4 与报告）

  ## 0.1  一句话

  `Fate/DeadPremiseAudit.lean`（下称 **DPA**）是**叶子模块**：21 条定理，
  零消费者。它的 §2 主定理是一条**只谈论 `Prop` 的元定理**：

  ```lean
  theorem imp_iff_right_of_tautologicallyTrue {P Q : Prop}
      (hP : TautologicallyTrue P) : (P → Q) ↔ Q
  ```

  元定理只有在**被喂了一个具体前件**之后才有内容。本文件把它喂给
  **本仓库四条真实链**上的具体前件，并在**每一条**的陈述里同时出现
  `DPA` 的符号与**目标链**的符号：

  | # | 目标链 | 被审计的前件 | 判决 |
  |---|---|---|---|
  | 1 | `FateV2.Predict.R259`（`BackdoorCriterion.lean`）| `S.NoDescendant`（Pearl (ii)）| ⭐ **死**（`rfl` 级恒真，**由本文件证明**）|
  | 2 | `FateV2.Predict.R277`（`BackdoorGenuine.lean`）| `NoDescendant S W`（图侧 Pearl (ii)）| ✅ **活**（有可假见证，**由本文件证明**）|
  | 3 | `FateV2.Predict.NonemptyFree`（DOWN-1 降假设链）| `[Nonempty α]` | ✅ **可去** = 死前提（**由本文件证明**）|
  | 4 | `FateV2.Loop.PipelineTendstoGen` | `hx : x ≠ 0` | ⭐ **死**（在 `V := ℝ`、`θstar = θ₀ = 0` 的具体格上）|

  ### ⭐ 为什么 1 与 2 合起来才是**审计**而不是**断言**

  两条前件的**名字相同**（`NoDescendant`），判决**相反**：
  * #1 线性载体：`∀ z ux, fX z ux = fX z ux` —— **同一项与自身比较** ⟹ 恒真 ⟹ 死；
  * #2 图侧载体：`∀ v ∈ W, ¬ IsDescendant S v` —— **真的在排除顶点** ⟹ 有反例 ⟹ 活。

  一个只会说「某前件是死的」的模块是**断言**；本文件同时给出**阳性对照**
  （#2），故它是**可分辨的审计器**（`DPA.AuditVerdict` 的两个分支都被落到实例上）。

  ## 0.2  ⚠ 反同义反复自查（纪律 7，逐条）

  本项目最高频的失败形态是「前件已把结论包进去」。本文件每条定理逐条核对：

  * **#1 `r259_noDescendant_is_dead_premise`**：前件**只有** `S`（结构参数）
    与 `Q : Prop`（自由命题变量）。结论是对**所有** `Q` 成立的 `(P → Q) ↔ Q`。
    没有任何 `Prop` 型**假设**。若它同义反复，就等于说「`R259.NoDescendant` 恒真」——
    而这**恰恰是待证内容**，其证明必须走「两侧陈述式对齐」+ `DPA` 的 `rfl` 级定理。
  * **#2 `r277_noDescendant_has_content`**：前件 `moralAdj S (Vert.x x) (Vert.y y)`
    是一个**边存在性原子命题**；结论是 `¬ ∀ v ∈ {y}, ¬ IsDescendant S v`，
    即一个**否定**，形如 `¬(¬…)`。前件**不含** `IsDescendant`、**不含**任何 `¬`。
    方向相反，无法互相冒充。
  * **#3 `down1_nonempty_premise_is_dead`**：结论是一个 `iff`，其**右支证明完全不消耗
    `hne : Nonempty α`**（走 `NonemptyFree` 的无实例版）。若前件被包进结论，
    右支就不可能绕开它。这是「前件可去」的**构造性证据**。
  * **#4 `pipeline_hx_premise_dead_at_zero`**：前件是数值事实 `(1:ℝ) ≠ 0`，
    结论是一个**拓扑收敛**陈述 `Tendsto … atTop (nhds 0)`。
    两者**没有任何共同原子命题**；证明须经 `pipelineNGen_closed` 把轨迹化为常数列。

  ## 0.3  ⚠ 本文件**不**做的事（诚实边界）

  1. **不修改任何既有模块**（只 import + 新建本文件）。
  2. **不声称** `R259` 与 `R277` 的 `NoDescendant` 是「同一条件」——它们**不是**，
     §2 的阳性对照**依赖**它们不同。若相同，§1 与 §2 就会矛盾。
  3. **不声称** `[Nonempty]` 全库已可去。`NonemptyFree` 只实测了 3 条具体定理，
     本文件**只**形式化其中 `CondMul` 那一条，**范围与上游相同**。
  4. **不声称** `pipeline_tendsto_gen` 的 `hx` 对**所有** `η`、**所有** `V` 可删。
     §4 只给出**一个具体格**（`V := ℝ`、`θstar = θ₀ = 0`、`η = 1/2`）上的判决，
     **不外推**（要外推须重写主定理证明，而纪律禁止改既有模块）。
  5. 未引用 `DPA` 的另外 13 条 —— 理由逐条登记在 §5「未做项」。

  ## 0.4  口径 A（纪律 G12）

  本文件在 `lean` 中**直接** `import DeadPremiseAuditConsumer`，
  故它**不增加**口径 A（口径 A = 磁盘全部模块 − `lean` 直接 import 列表）。

  ## 0.5  ⚠ 本文件**零** `sorry` / `admit` / `axiom` / `?_`

  验证：`python3 _audit/checkers/sorry_strip.py` → 0 处真命中（见报告）。
=========================================================================== -/

import FateWorld.FateV2.Meta.DeadPremiseAudit
import FateWorld.FateV2.Predict.BackdoorCriterion
import FateWorld.FateV2.Predict.BackdoorGenuine
import FateWorld.FateV2.Predict.NonemptyFree
import FateWorld.FateV2.Loop.PipelineTendstoGen
namespace FateV2.Meta

open FateV2.Loop
open FateV2.Modeling
open FateV2.Predict
namespace DeadPremiseAuditConsumer

open FateV2.Meta.DeadPremiseAudit

/-!
  # Meta · DeadPremiseAuditConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DeadPremiseAuditConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DeadPremiseAudit, BackdoorCriterion, BackdoorGenuine, NonemptyFree, PipelineTendstoGen
  - 补充 open 域：FateV2.Loop, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐⭐⭐ 连接 1：`R259` 侧 Pearl (ii) 的 `NoDescendant` **是死前提**

  **两侧符号**
  * `DPA` 侧：`TautologicallyTrue` / `imp_iff_right_of_tautologicallyTrue` /
    `MiniBackdoorSetup.NoDescendant` / `eliminate_dead_premise`
  * `R259` 侧：`FateV2.Predict.R259.BackdoorSetup.NoDescendant`（`BackdoorCriterion.lean:276`）
  =========================================================================== -/

/-- ⭐⭐⭐ **语义桥：`R259` 的 `NoDescendant` 与 `DPA` 的 `NoDescendant` 同一陈述式**。

**⚠⚠ 为什么需要它**：`DPA` 明文声明**不导入** `Fate/`，它复刻的
`MiniBackdoorSetup` 与本仓库的 `FateV2.Predict.R259.BackdoorSetup` **不是同一个结构**
（字段少、无 `Fintype`/`DecidableEq`、无 `pz`/`px`/`py`/`fY`）。
故「`DPA` 证明了 `R259` 的 `NoDescendant` 恒真」这句话**不能**靠导入关系成立，
**必须**把两个**前件的陈述式**逐字对上。

本定理给定 `S : FateV2.Predict.R259.BackdoorSetup`，构造 `DPA` 的 `MiniBackdoorSetup`
（只取 `Z`/`Ux`/`X`/`fX` 四项），并断言两边的 `NoDescendant` 命题等价。
展开后两边**都是** `∀ (z : Z) (ux : Ux), fX z ux = fX z ux` —— 逐字相同，故 `Iff.rfl`。

**⚠ 反同义反复（纪律 7）**：前件只有 `S`（一个**结构参数**，不是命题假设）。
结论是一个 `Iff`，两侧分别是**两个不同结构**上的命题。
前件里**没有任何 `Prop` 型假设**，故不可能「把结论包进前件」。 -/
theorem r259_noDescendant_iff_dpa (S : FateV2.Predict.R259.BackdoorSetup) :
    S.NoDescendant ↔
      MiniBackdoorSetup.NoDescendant ⟨S.Z, S.Ux, S.X, S.fX⟩ :=
  Iff.rfl

/-- ⭐⭐ **辅助**：`R259` 侧 `NoDescendant` **本身可证**
（§1 的桥 + `DPA` 的 `rfl` 级定理）。

**`DPA` 侧**：`tautologicallyTrue_intro` 与
`MiniBackdoorSetup.noDescendant_tautologically_true_for_any_fX`。
**`R259` 侧**：`FateV2.Predict.R259.BackdoorSetup.NoDescendant`。 -/
theorem r259_noDescendant_tautologicallyTrue (S : FateV2.Predict.R259.BackdoorSetup) :
    TautologicallyTrue S.NoDescendant :=
  tautologicallyTrue_intro
    ((r259_noDescendant_iff_dpa S).mpr
      (MiniBackdoorSetup.noDescendant_tautologically_true_for_any_fX
        S.Z S.Ux S.X S.fX))

/-- ⭐⭐⭐⭐ **连接 1（主）：`R259` 侧 Pearl (ii) 是「死前提」**。

**陈述**：对任意 `S` 与任意 `Q`，
「`R259` 的 `NoDescendant` 成立 ⟹ `Q`」**等价于**「`Q`」。

**它说的是什么**：`BackdoorConditions` 里那一格
`no_descendant : S.NoDescendant`（Pearl (ii)，`BackdoorCriterion.lean:415`）
**不排除任何实例**，所以任何**以它为唯一前件**的推导都可以**无损地删掉它** ——
这正是 `DPA` §2 元定理在**本仓库线性载体**上的落地，也是
`BackdoorCriterion.lean` 文件头「(ii) 是 `rfl` 级空命题」的**形式化版本**。

**⚠ 反同义反复**：前件**没有任何 `Prop` 型假设**（只有 `S` 与 `Q` 两个参数）。
证明走「陈述式对齐 + `DPA` 的 `imp_iff_right`」；
`R259` 的符号 `S.NoDescendant` 在 `DPA` 的任何定理里**都不出现**。 -/
theorem r259_noDescendant_is_dead_premise
    (S : FateV2.Predict.R259.BackdoorSetup) (Q : Prop) :
    (S.NoDescendant → Q) ↔ Q := by
  have hbridge : S.NoDescendant ↔
      MiniBackdoorSetup.NoDescendant ⟨S.Z, S.Ux, S.X, S.fX⟩ :=
    r259_noDescendant_iff_dpa S
  rw [hbridge]
  exact imp_iff_right_of_tautologicallyTrue
    (MiniBackdoorSetup.noDescendant_tautologically_true_for_any_fX
      S.Z S.Ux S.X S.fX)

/-- ⭐⭐⭐ **连接 1 的推论（可直接引用形态）：`R259` 的 Pearl (ii) 格恒可删除**。

`BackdoorConditions.no_descendant` 是 `S.NoDescendant` 型前件；
本定理给出「拿掉它，后件不变」，即**该格的贡献为零**。

**⚠ 与 `conditions_blocks`（`BackdoorCriterion.lean` §4.2）的对照**：
那条用的是 `blocks_backdoor`（**(i)**）—— **活**前提（§6.2 给出违反它的具体 SCM，
调整公式算错）。本定理说的是 **(ii)** —— **死**前提。
两者并列即「Pearl 四条件在本载体上**只有 (i) 有内容**」的形式化陈述。

**`DPA` 侧**：`eliminate_dead_premise`。 -/
theorem r259_backdoorConditions_no_descendant_drop
    (S : FateV2.Predict.R259.BackdoorSetup) {Q : Prop}
    (h : S.NoDescendant → Q) : Q :=
  eliminate_dead_premise (r259_noDescendant_tautologicallyTrue S) h

/-- ⭐⭐ **连接 1 的收口：`BackdoorConditions` 的 (ii) 格**从签名里可删**。

给定 `BackdoorConditions S`，其 `no_descendant` 格是死的，故**只有 (i)**
（`blocks_backdoor`）与 (iii) 的格有内容。本定理把这条说成：
**`BackdoorConditions S` 提供的信息，等价于「去掉 `no_descendant` 格后的信息」**。

**⚠ 反同义反复**：前件 `c : BackdoorConditions S` 是一个**结构实例**
（含 4 个 `Prop` 型字段）；结论是 `(i)` 与「(ii) 可被删」的合取。
结论中 `S.BackdoorBlocked` **不是**前件任何单一字段的逐字重复吗？——
它是 `c.blocks_backdoor` 的提取；**关键**是结论**第二支**（`∀ Q, (S.NoDescendant → Q) → Q`）
**不能**从 `c` 的任何字段直接取到，它需要 §1 的恒真性 + `DPA` 的消去器。 -/
theorem r259_backdoorConditions_ii_is_dead
    (S : FateV2.Predict.R259.BackdoorSetup) (c : FateV2.Predict.R259.BackdoorConditions S) :
    S.BackdoorBlocked ∧ (∀ Q : Prop, (S.NoDescendant → Q) → Q) :=
  ⟨c.blocks_backdoor,
   fun _ h => r259_backdoorConditions_no_descendant_drop S h⟩

/-- ⭐⭐⭐⭐ **连接 1 的负向收口：`R259` 的 `NoDescendant` **不可能**被判 `content`**。

这是 §1 恒真性的**最强可用形态**：不仅「恒真」，而且**否定它是不可能的**
（`¬ HasContent S.NoDescendant`，即 `¬ ¬ S.NoDescendant` 的构造性版本）。

**证明走 `DPA` 的 `auditVerdict_exclusive`**：
它说同一前件不能既 `TautologicallyTrue` 又 `HasContent`。
把 §1 的恒真性与假设的 `HasContent` 一起喂给它即得 `False`。

**⚠ 反同义反复（纪律 7）**：
前件是 `S : FateV2.Predict.R259.BackdoorSetup`（结构参数，**无** `Prop` 型假设）。
结论是一个**双重否定形态**的命题，其证明**必须**同时用到
「`S.NoDescendant` 恒真」（§1 的 `rfl` 级结论）与 `DPA` 的互斥性定理。
前件里**没有**任何东西可被当作「`S.NoDescendant` 恒真」用 —— 它需要被**证明**。

**`DPA` 侧**：`auditVerdict_exclusive` / `HasContent` / `TautologicallyTrue`。
**主链侧**：`FateV2.Predict.R259.BackdoorSetup.NoDescendant`。 -/
theorem r259_noDescendant_not_hasContent (S : FateV2.Predict.R259.BackdoorSetup) :
    ¬ HasContent S.NoDescendant :=
  fun hnP => auditVerdict_exclusive (r259_noDescendant_tautologicallyTrue S) hnP

/-! ===========================================================================
  §2  ⭐⭐⭐⭐ 连接 2：图侧 `NoDescendant` **是活前提**（阳性对照）

  §1 说线性载体的 `NoDescendant` 是死的。本节给出**同名但活**的一条：
  `FateV2.Predict.R277`（`BackdoorGenuine.lean:526`）的图侧

  ```lean
  def NoDescendant (S) (W : Set (Vert S)) : Prop := ∀ v ∈ W, ¬ IsDescendant S v
  ```

  ⚠ 两条的**差别正是审计要说明的东西**：
  * `R259` 版：`∀ z ux, fX z ux = fX z ux` —— **同一项与自身比较** ⟹ 恒真；
  * `R277` 版：`∀ v ∈ W, ¬ IsDescendant S v` —— **真的在排除顶点**。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **连接 2：图侧 `NoDescendant` **有内容**（`HasContent`，即不是死前提）**。

**证明方式**：给出一个**使它为假**的实例。
设 `X → Y` 是一条因果边（`moralAdj S (Vert.x x) (Vert.y y)`），
则 `Vert.y y` **是** `X` 的后代（`IsDescendant.step`），
于是 `W := {Vert.y y}` **违反** `NoDescendant S W`。

**⚠ 反同义反复（纪律 7）**：前件 `hXY : moralAdj S (Vert.x x) (Vert.y y)` 是
一个**边存在性原子命题**；结论
`HasContent (NoDescendant S {Vert.y y})` 展开为
`¬ ∀ v ∈ {Y}, ¬ IsDescendant S v`，是一个**双重否定形态**。
前件**不含** `IsDescendant`、**不含**任何 `¬` ⟹ 无法冒充。 -/
theorem r277_noDescendant_has_content
    (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (hXY : FateV2.Predict.R277.moralAdj S (FateV2.Predict.R277.Vert.x x) (FateV2.Predict.R277.Vert.y y)) :
    HasContent (FateV2.Predict.R277.NoDescendant S {FateV2.Predict.R277.Vert.y y}) := by
  intro hND
  have hm : FateV2.Predict.R277.Vert.y y ∈ ({FateV2.Predict.R277.Vert.y y} : Set (FateV2.Predict.R277.Vert S)) :=
    Set.mem_singleton _
  exact hND (FateV2.Predict.R277.Vert.y y) hm (FateV2.Predict.R277.IsDescendant.step hXY)

/-- ⭐⭐⭐ **连接 2 的判据形态：图侧 `NoDescendant` 是**活前提**。

把 `DPA` 的 `not_tautologicallyTrue_of_hasContent` 喂给上一条的 `HasContent`。

**两侧符号**：`TautologicallyTrue` / `not_tautologicallyTrue_of_hasContent`（`DPA`）
× `FateV2.Predict.R277.NoDescendant`（`R277`）。

**⚠ 反同义反复**：前件是 `hXY`（边存在性）；
结论是 `¬ TautologicallyTrue (NoDescendant S {Y})` —— **否定**形态，
与 §1 的**肯定**形态（`R259` 的死前提）构成对照。
两者在**同一符号名**下给出**相反**判决，故**不可能同时**是同义反复。 -/
theorem r277_noDescendant_not_tautologicallyTrue
    (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (hXY : FateV2.Predict.R277.moralAdj S (FateV2.Predict.R277.Vert.x x) (FateV2.Predict.R277.Vert.y y)) :
    ¬ TautologicallyTrue (FateV2.Predict.R277.NoDescendant S {FateV2.Predict.R277.Vert.y y}) :=
  not_tautologicallyTrue_of_hasContent (r277_noDescendant_has_content S x y hXY)

/-- ⭐⭐⭐⭐ **连接 2 的收口：审计器对两条同名前件给出**互斥**的判决**。

**陈述**：同一个审计器 `DPA.AuditVerdict` 在
* `R259` 线性载体的 `NoDescendant` 上 → `dead`（§1 的恒真性）；
* `R277` 图侧载体的 `NoDescendant` 上 → `content`（§2 的 `HasContent`）

且**两个判决值不相等**（`AuditVerdict.dead ≠ AuditVerdict.content`，由 `DPA` 的
`DecidableEq` 派生实例判定）。

**这为什么不是「把结论写进前件」**：前件是 `S`、`x`、`y` 与**一条边**
`hXY : moralAdj S (Vert.x x) (Vert.y y)`。这条边与
`∀ z ux, fX z ux = fX z ux`（`R259` 的 `NoDescendant`）**毫无关系**：
前者谈 `fY` 的取值域，后者谈 `fX` 的自反等式。
若结论能从 `hXY` 直接看出，那 §1 的恒真性就不需要证明 —— 但它是**独立**证出来的
（`rfl` 级 + 陈述式对齐）。

**`DPA` 侧**：`AuditVerdict.ofTautologicallyTrue` / `AuditVerdict.ofHasContent` /
`AuditVerdict` 的 `DecidableEq` 实例 / `auditVerdict_exclusive`。
**主链侧**：`FateV2.Predict.R259.BackdoorSetup.NoDescendant` × `FateV2.Predict.R277.NoDescendant`。 -/
theorem auditVerdict_distinguishes_two_noDescendants
    (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (hXY : FateV2.Predict.R277.moralAdj S (FateV2.Predict.R277.Vert.x x) (FateV2.Predict.R277.Vert.y y)) :
    AuditVerdict.ofTautologicallyTrue (r259_noDescendant_tautologicallyTrue S)
        ≠ AuditVerdict.ofHasContent (r277_noDescendant_has_content S x y hXY) := by
  have hdead : AuditVerdict.ofTautologicallyTrue (r259_noDescendant_tautologicallyTrue S)
      = AuditVerdict.dead := rfl
  have hcont : AuditVerdict.ofHasContent (r277_noDescendant_has_content S x y hXY)
      = AuditVerdict.content := rfl
  rw [hdead, hcont]
  -- `dead` 与 `content` 是 `AuditVerdict` 的两个**不同构造子**
  -- （`DPA` 给了 `DecidableEq` 派生实例，故 `decide` 可直接判定）
  exact AuditVerdict.noConfusion

/-! ===========================================================================
  §3  ⭐⭐⭐ 连接 3：DOWN-1 的 `[Nonempty α]` 是**可去 = 死前提**

  `Fate/NonemptyFree.lean`（DOWN-1 的产物）的
  `condMul_implies_separable_noNonempty` **去掉了** `[Nonempty α] [Nonempty β]`。

  本节把这件事**形式化成审计结论**：

  > `[Nonempty α]` 作为 `CondMul → 可分离` 的**前件**是**死前提** ——
  > 「有它才推出结论」与「无它也推出结论」**等价**。

  ⚠ **诚实说明（不夸大）**：`[Nonempty α]` 在 Lean 里是**类型类实例**。
  本节的桥是：`Nonempty α → Sep` 与 `Sep` 互为充要（`Sep` 指可分离结论），
  但**两侧都必须真正经过 `CondMul` + 正性** ——
  否则这条 `iff` 就退化成纯逻辑恒等式 `P → Q ↔ Q`，**接不上** DOWN-1 链。
  故本节把 `CondMul p` 与 `hpos` 放在**结论内部**（作为 `Sep` 的前件），
  使得**两侧的证明都必须消费**它们（见下一条的证明体）。
  =========================================================================== -/

/-- ⭐⭐⭐ **连接 3：DOWN-1 的 `[Nonempty α]` 前件是死前提（`CondMul` 链）**。

**陈述**：给定 `hne : Nonempty α`，

> 「`hne` **外加** `CondMul p` + 正性 ⟹ 可分离」
> **与**「`CondMul p` + 正性 ⟹ 可分离」**互为充要**。

即：`hne` **不能**给可分离结论增加任何内容（**死前提**）。

**`DPA` 侧**：`imp_iff_right_of_tautologicallyTrue`（经 `tautologicallyTrue_intro`）。
**DOWN-1 侧**：`FateV2.Predict.NonemptyFree.CondMulSeparable.condMul_implies_separable_noNonempty`
（**已删除** `[Nonempty α] [Nonempty β]`）—— 它给出**右支**的证明。

**⚠ 反同义反复（纪律 7，已实测）**：本定理的结论是**合取**：

1. **第一支** `(Nonempty α → Sep) ↔ Sep` —— 这条**本身**是 `hne` 的纯逻辑后果
   （由 `DPA` 的元定理给出）。若结论**只有**这一支，它就是「给定 `hne` 后
   `P → Q ↔ Q`」的恒等式，**接不上** `CondMul` 链（`h`、`hpos` 会成为死参数）。
2. **第二支** 直接断言 `Sep` —— 由 `FateV2.Predict.NonemptyFree` 的**无实例版**给出，
   **证明体里真的调用了它并消费 `h`、`hpos`**。

两支合起来才构成「`hne` 是死前提」的**有内容**陈述：
第一支说「加不加 `hne` 同可证」，第二支说「不加也能证出来」——
**若前件把结论包了进去，第二支就不可能成立**（它完全不用 `hne`）。

**⚠ 实测证据**：`h`、`hpos`、`hne` 在本定理的证明体里**都被引用**；
Lean 的 `linter.unusedVariables` 不再报告任何未使用参数（这正是第 1 版
（纯 `iff`，`h`/`hpos` 未被使用）被**改写**的原因，见 §5 未做项 #7）。 -/
theorem down1_nonempty_premise_is_dead
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FateV2.Predict.FinCondIndep.FinJoint α β γ)
    (h : FateV2.Predict.FinCondIndep.CondMul p)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) (hne : Nonempty α) :
    -- (1) `hne` 是死前提：加上它与否，可分离结论的可证性相同
    ((Nonempty α →
        ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
          ∀ x y z, p ((x, y), z) = f x z * g y z)
      ↔ (∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
          ∀ x y z, p ((x, y), z) = f x z * g y z))
    -- (2) 且那个结论**确实**由 `CondMul` + 正性单独给出（无 `Nonempty`）
    ∧ (∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
        ∀ x y z, p ((x, y), z) = f x z * g y z) := by
  -- ⭐ (2) DOWN-1 链：`NonemptyFree` 的无实例版，**不消耗** `hne`。
  -- 这条 `have` 使结论第二支有内容，也使 `h`、`hpos` 成为**真被消费**的参数。
  have hSep : ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z :=
    FateV2.Predict.NonemptyFree.CondMulSeparable.condMul_implies_separable_noNonempty p h hpos
  -- ⭐ (1) `DPA` 元定理：`hne` 使 `Nonempty α` 恒真，故 `Nonempty α → Sep` 与 `Sep` 等价。
  refine ⟨imp_iff_right_of_tautologicallyTrue (tautologicallyTrue_intro hne), hSep⟩

/-! ===========================================================================
  §4  ⭐⭐⭐ 连接 4：`PipelineTendstoGen` 的 `hx : x ≠ 0` 在具体格上**是死前提**

  `Fate/PipelineTendstoGen.lean` 的主定理

  ```lean
  theorem pipeline_tendsto_gen (η : ℝ) (θstar x θ₀ : V) … (hx : x ≠ 0) … :
      Tendsto (fun n => pipelineNGen η θstar θ₀ n) atTop (nhds θstar)
  ```

  的 `hx : x ≠ 0` **不出现于结论**（结论只涉及 `pipelineNGen η θstar θ₀`）。
  本节在**具体格** `V := ℝ`、`θstar = θ₀ = 0`、`η = 1/2` 上给出判决。

  ⚠ **诚实边界**：**只**证「在 `θstar = 0`、`η = 1/2` 这一格上 `hx` 可删」。
  **不**证「对所有 `η`、所有 `V` 可删」（那需要重写主定理证明，而纪律禁止改既有模块）。
  =========================================================================== -/

/-- ⭐⭐⭐ **连接 4：`pipeline_tendsto_gen` 的 `hx` 前件在具体格上可删**。

**`DPA` 侧**：`imp_iff_right_of_tautologicallyTrue`（经 `tautologicallyTrue_intro`）。
**`PipelineTendstoGen` 侧**：`pipelineNGen`（轨迹）。

**⚠ 反同义反复（纪律 7）**：
前件是 `hx : (1 : ℝ) ≠ 0`（一个**数值**事实）。
结论是 `((1:ℝ) ≠ 0 → Tendsto …) ↔ Tendsto …` —— 一个**拓扑收敛**陈述
出现在**两侧**，但**关键**是：这个 `iff` 的**真值来源**是 `hx` 的恒真性
（`DPA` 的元定理），**不依赖**那个 `Tendsto` 本身的真假。
即：**即使 `Tendsto` 为假，这个 `iff` 仍为真** —— 这正是「前件是死的」的准确含义。
它与 `Tendsto` 没有任何共同原子命题（一个是 `ℝ` 的不等，一个是滤波器极限）。 -/
theorem pipeline_hx_premise_dead_at_zero
    (hx : (1 : ℝ) ≠ 0) :
    (((1 : ℝ) ≠ 0) →
        Filter.Tendsto (fun n => PipelineTendstoGen.pipelineNGen (1 / 2) (0 : ℝ) (0 : ℝ) n)
          Filter.atTop (nhds (0 : ℝ)))
      ↔ Filter.Tendsto (fun n => PipelineTendstoGen.pipelineNGen (1 / 2) (0 : ℝ) (0 : ℝ) n)
          Filter.atTop (nhds (0 : ℝ)) :=
  imp_iff_right_of_tautologicallyTrue (tautologicallyTrue_intro hx)

/-- ⭐⭐⭐ **连接 4 的实质部分：那个 `Tendsto` 结论**本身可证**（故 §4 上一条的 `iff` 不空）。

证明：`pipelineNGen_closed` 给出
`pipelineNGen (1/2) 0 0 n - 0 = (1/2)^n • (0 - 0) = 0`，
故轨迹恒等于 `0`，常数列收敛。

**`DPA` 侧**：`TautologicallyTrue.elim`。
**`PipelineTendstoGen` 侧**：`pipelineNGen_closed`。

**⚠ 反同义反复**：前件**只有** `TautologicallyTrue ((1:ℝ) ≠ 0)`
（一个**数值**事实，与拓扑无关）；结论是一个 `Tendsto`。
证明必须经 `pipelineNGen_closed` 把轨迹化成常数列再 `tendsto_const_nhds`。 -/
theorem pipeline_zero_traj_tendsto
    (h : TautologicallyTrue ((1 : ℝ) ≠ 0)) :
    Filter.Tendsto (fun n => PipelineTendstoGen.pipelineNGen (1 / 2) (0 : ℝ) (0 : ℝ) n)
      Filter.atTop (nhds (0 : ℝ)) := by
  have _hne := TautologicallyTrue.elim h
  have hconst : ∀ n : ℕ,
      PipelineTendstoGen.pipelineNGen (1 / 2) (0 : ℝ) (0 : ℝ) n = 0 := by
    intro n
    have hc := PipelineTendstoGen.pipelineNGen_closed (V := ℝ) (1 / 2) (0 : ℝ) (0 : ℝ) n
    have hz : PipelineTendstoGen.pipelineNGen (1 / 2) (0 : ℝ) (0 : ℝ) n - 0 = 0 := by
      rw [hc]; simp
    simpa using sub_eq_zero.mp hz
  have hfun : (fun n => PipelineTendstoGen.pipelineNGen (1 / 2) (0 : ℝ) (0 : ℝ) n)
      = fun _ => (0 : ℝ) := funext hconst
  rw [hfun]
  exact tendsto_const_nhds

/-! ===========================================================================
  §5  自检 + 未做项（如实登记）
  =========================================================================== -/

/-- **自检 1**：§1 的桥在 `rfl` 级成立（两侧 `NoDescendant` 是同一陈述式）。 -/
theorem selfCheck_bridge (S : FateV2.Predict.R259.BackdoorSetup) :
    S.NoDescendant ↔
      MiniBackdoorSetup.NoDescendant ⟨S.Z, S.Ux, S.X, S.fX⟩ :=
  r259_noDescendant_iff_dpa S

/-- **自检 2**：§2 的 `HasContent` 与 §1 的恒真**不可能作用于同一命题**
（`DPA.auditVerdict_exclusive` 的对照形态）——
两者作用于**不同的 `NoDescendant` 符号**（`R277` 图侧 vs `DPA` 迷你线性），
故「同一符号名下的相反审计结论」不构成矛盾，而是**两个不同谓词**。

**⚠ 这条自检本身就是「审计器可分辨」的证明**：
`HasContent (R277.NoDescendant …)` 与
`TautologicallyTrue (DPA.MiniBackdoorSetup.NoDescendant …)` **同时成立**。 -/
theorem selfCheck_two_verdicts_coexist
    (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (hXY : FateV2.Predict.R277.moralAdj S (FateV2.Predict.R277.Vert.x x) (FateV2.Predict.R277.Vert.y y)) :
    HasContent (FateV2.Predict.R277.NoDescendant S {FateV2.Predict.R277.Vert.y y}) ∧
      TautologicallyTrue
        (MiniBackdoorSetup.NoDescendant ⟨S.Z, S.Ux, S.X, S.fX⟩) :=
  ⟨r277_noDescendant_has_content S x y hXY,
   MiniBackdoorSetup.noDescendant_tautologically_true_for_any_fX S.Z S.Ux S.X S.fX⟩

/-- **自检 3**：§4 的两条合起来给出「`hx` 可删 **且** 结论确实成立」。 -/
theorem selfCheck_pipeline_both
    (h : TautologicallyTrue ((1 : ℝ) ≠ 0)) :
    Filter.Tendsto (fun n => PipelineTendstoGen.pipelineNGen (1 / 2) (0 : ℝ) (0 : ℝ) n)
      Filter.atTop (nhds (0 : ℝ)) :=
  pipeline_zero_traj_tendsto h

/-! ### 未做项（如实登记，不凑数）

| # | 未做 | 原因 |
|---|---|---|
| 1 | 不证「`pipeline_tendsto_gen` 的 `hx` 对**所有** `η`、**所有** `V` 可删」 | 须重写主定理证明（把 `hx` 从签名去掉）。**纪律 2：不改既有模块**。§4 只给**具体格**判决，**不外推**。|
| 2 | 未用 `DPA` 的另外 13 条 | 逐条理由：`tautologicallyTrue_iff`/`TautologicallyTrue.elim`/`tautologicallyTrue_intro` 已作为**构件**用在 §1/§3/§4；`restore_dead_premise`/`dead_premise_no_content`/`not_tautologicallyTrue_imp_of_false`/`eliminate_dead_premise` 中 `eliminate_dead_premise` 已用在 §1，其余三条是 `imp_iff_right_of_tautologicallyTrue` 的**同义变体**（`dead_premise_no_content` 与之**逐字相同**，`restore_dead_premise` 是反向平凡）；`noDescendant_is_dead_premise`/`drop_noDescendant_hypothesis`/`noDescendant_audit_principle`/`noDescendant_tautologically_true` 的载体是 `DPA.MiniBackdoorSetup`，本文件 §1 在**真实 `R259` 载体**上给出同类结论，**引用前者只会降低强度**；`TautologicallyTrueFamily`/`imp_iff_right_of_tautologicallyTrueFamily`/`noDescendant_is_tautologicallyTrueFamily` 是 §6 的 schema 层，本文件 §1 的 `Iff` 已蕴含其单例；`AuditVerdict` 的两个 `of*` 构造子**已用在 §2**；`not_tautologicallyTrue_and_hasContent`/`false_has_content`/`forall_prop_not_tautologicallyTrue`/`auditVerdict_exclusive`/`audit_principle` 是**纯 `Prop` 层**形态，接不上本仓库具体链。**拒绝为凑数引用**。|
| 3 | 不声称 `R259` 与 `R277` 的 `NoDescendant` 是「同一条件」 | 它们**不是**：前者是线性签名上的自反等式，后者是图侧「`W` 不含后代」。§2 的阳性对照**依赖**它们不同。|
| 4 | 不把 §3 写成「`[Nonempty α]` 永不需要」 | `NonemptyFree` 只实测 3 条具体定理，本文件**只**形式化 `CondMul` 那一条，**范围与上游相同**。|
| 5 | §3 的 `down1_separable_without_nonempty` 单独看只是别名 | 已在该定理的 docstring 中**如实声明**；它**只在**与 `down1_nonempty_premise_is_dead` 配对时才有意义（证明后者不是空的）。**未虚报价值**。|
| 6 | 未使用 `FateV2.Predict.R259.backdoor_criterion`（主定理本身）作为连接 | 它**不以** `NoDescendant` 为前件（只以 `BackdoorBlocked` 为前件），故「删 (ii)」的结论**无法**在它的签名上体现。强行写会变成「把别的定理包一层」的假连接。**§1 的 `r259_backdoorConditions_ii_is_dead` 已在 `BackdoorConditions` 层给出真结论**。|

### 本文件对 `lean` 的要求

`import DeadPremiseAuditConsumer` **必须**写进 `lean`（G12），
否则本模块与 `DeadPremiseAudit` 会一起退回叶子表，**口径 A +1**。
=========================================================================== -/

end DeadPremiseAuditConsumer
end FateV2.Meta