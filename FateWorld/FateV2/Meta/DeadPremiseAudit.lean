/-!
  # Meta · DeadPremiseAudit —— 死前提审计器

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DeadPremiseAudit.lean`（原 `Fate/DeadPremiseAudit.lean`）
  - 动作：B 适配（改命名空间 `Fate.DeadPremiseAudit` → `FateV2.Meta.DeadPremiseAudit`）
  - 对应环节：元层 · 反空泛判据（D-022）
  - 依赖裁决：**D-022**（撤销空泛证明）、**D-001**（验收判据）
  - 改动：仅命名空间。全部定义、定理、证明体**逐字保留**。
  - 状态：已迁移，待公理审计
  - 特性：**零 import、零外部依赖**（原文件自足）

  ## 这个模块做什么

  把「一次性审计」做成**可复用审计器**：

  1. 定义 `TautologicallyTrue`（恒真）与 `DeadPremise`（死前提）
  2. 证明：**前件恒真 ⟹ 以它为假设的定理没有内容**（`P` 恒真时 `P → Q` 等价于 `Q`）
  3. 提供可判定的反审计：只有能构造出**使前件为假**的实例，前件才不是死前提

  **⟹ 这是 D-022「反空泛证明」的工具层实现。**

  ---
  以下为原文件内容（逐字保留）：
  ---
-/
namespace FateV2.Meta.DeadPremiseAudit

open Classical

/-! ===========================================================================
  §1 **核心定义：恒真 / 死前提**
=========================================================================== -/

/-- **恒真（tautologically true）**。

  `TautologicallyTrue P` 与 `P` **定义上等价**（`Iff.rfl` 可证），
  故意做成零成本别名：审计只需要一个**记号**来标记「这一格是恒真的」，
  不需要（也不应该）引入额外的合取项。

  ⚠ 与 `P ∧ True` 的关系：`P ∧ True ↔ P` 是 `and_true`，两者**信息量相同**；
  本定义选更简单的形式，使 `rfl` 级证明**保持** `rfl` 级。 -/
def TautologicallyTrue (P : Prop) : Prop := P

/-- **恒真的判据（等价形式）**：`P` 恒真 ⟺ `P`。 -/
theorem tautologicallyTrue_iff (P : Prop) : TautologicallyTrue P ↔ P := Iff.rfl

/-- 恒真的命题**可证**（这条看起来「显然」，但它是审计链的第一环：
  从「被标记为恒真」推出「确实成立」）。 -/
theorem TautologicallyTrue.elim {P : Prop} (h : TautologicallyTrue P) : P := h

/-- 可证的命题**恒真**。 -/
theorem tautologicallyTrue_intro {P : Prop} (h : P) : TautologicallyTrue P := h

/-! ===========================================================================
  §2 **「以 `P` 为前件的定理没有内容」的形式化**

  ▶ 这是本文件最有价值的一条：它把「死前提」的**后果**说成一条 `iff`，
  使得任何 `h : P → Q` 在 `P` 恒真时**可以无损地**退化成 `Q`。
=========================================================================== -/

/-- ⭐⭐⭐ **（主定理）前件恒真 ⟹ 蕴含式与后件等价**。

  $$\text{TautologicallyTrue}(P)\ \Longrightarrow\ \bigl((P \to Q) \leftrightarrow Q\bigr).$$

  **读法**：若前件 `P` 恒真，则「`P` 推出 `Q`」与「`Q`」**同真同假**
  —— 换句话说，**该定理的全部内容就是 `Q`**，前件是**装饰**。

  证明：`P` 恒真给出 `P`；于是 `P → Q` 与 `Q` 互相推出（`imp_iff_right`）。 -/
theorem imp_iff_right_of_tautologicallyTrue {P Q : Prop}
    (hP : TautologicallyTrue P) : (P → Q) ↔ Q :=
  imp_iff_right hP

/-- **退化（消去前件）**：恒真的前件可以从任何定理的**假设表**里删掉。

  `h : P → Q` 且 `P` 恒真 ⟹ `Q`。 -/
theorem eliminate_dead_premise {P Q : Prop}
    (hP : TautologicallyTrue P) (h : P → Q) : Q :=
  h hP

/-- **反方向（审计的「无损失」保证）**：`Q` 也可以重新**加回**死前件。
  即：消去前件**不丢失**任何信息。 -/
theorem restore_dead_premise {P Q : Prop}
    (_hP : TautologicallyTrue P) (h : Q) : P → Q :=
  fun _ => h

/-- ⭐⭐ **死前提 ⟹ 定理无内容**（`Prop` 层面的精确陈述）。

  一个「以 `P` 为前件的定理」`h : P → Q`，在 `P` 恒真时，
  **等价于**「`Q` 本身可证」：
  「存在 `P → Q` 的证明」与「存在 `Q` 的证明」**互为充要**。 -/
theorem dead_premise_no_content {P Q : Prop} (hP : TautologicallyTrue P) :
    (P → Q) ↔ Q :=
  imp_iff_right_of_tautologicallyTrue hP

/-- ⭐⭐ **推论**：恒真的前件**无法**用来「撑起」一个假后件
  —— 若 `P → Q` 可证且 `P` 恒真，则 `Q` 可证（`Q` 不能是假命题）。 -/
theorem not_tautologicallyTrue_imp_of_false {P Q : Prop}
    (hP : TautologicallyTrue P) (h : P → Q) : Q :=
  h hP

/-! ===========================================================================
  §3 **`NoDescendant` 例子：恒真（`rfl`）**

  下面**同形复刻** `Fate/BackdoorCriterion.lean` §1 的载体与 `NoDescendant`
  定义（**不导入** `Fate`，故不耦合）。逐行对照：

  | Fate 原文件 | 本文件 |
  |---|---|
  | `fX : Z → Ux → X` | 同 |
  | `def NoDescendant : Prop := ∀ (z : S.Z) (ux : S.Ux), S.fX z ux = S.fX z ux` | 同（一字不差） |
=========================================================================== -/

/-- **与 `Fate.R259.BackdoorSetup` **签名同形**的极小载体**（仅保留 `Z`、`Ux`、`X`、`fX`
  这四项 —— 这正是 `NoDescendant` 的**全部**依赖）。

  ⚠ 这里**故意**不加 `Fintype` / `DecidableEq` 等实例要求：
  `NoDescendant` 的恒真性**与它们无关**，这正是审计要说明的
  「它由**签名**决定，而非由**语义**决定」。 -/
structure MiniBackdoorSetup where
  /-- `Z` 的取值类型（外生混杂源）。 -/
  Z : Type
  /-- `Ux`：`X` 的噪声。 -/
  Ux : Type
  /-- 处理变量 `X`。 -/
  X : Type
  /-- ⭐ `X := fX z ux` —— `X` 吃 `Z`（后门入口）。 -/
  fX : Z → Ux → X

namespace MiniBackdoorSetup

variable (S : MiniBackdoorSetup)

/-- ⭐⭐⭐ **`NoDescendant`（与 `Fate.R259.BackdoorSetup.NoDescendant` 一字不差）**：
  `Z` 不是 `X` 的后代。

  **注意**：右端全是 `fX z ux = fX z ux` —— 同一项与自身比较。 -/
def NoDescendant : Prop := ∀ (z : S.Z) (ux : S.Ux), S.fX z ux = S.fX z ux

/-- ⭐⭐⭐⭐ **〔任务 2 的核心〕`NoDescendant` 恒真**。

  证明是 `rfl` 级别的 `Eq.refl`：`∀ z ux, fX z ux = fX z ux` 就是
  `∀ z ux, rfl`。用 `fun z ux => rfl` 写出，比 `rfl` 更**透明地**
  显示「每一处都是自反等号」。 -/
theorem noDescendant_tautologically_true : TautologicallyTrue S.NoDescendant :=
  fun _ _ => rfl

/-! ⚠⚠ **〔第 619 轮：删除 `noDescendant_iff_true` —— 空洞形态〕**

  原有一条

  ```lean
  theorem noDescendant_iff_true : S.NoDescendant ↔ True :=
    ⟨fun _ => trivial, fun _ _ _ => rfl⟩
  ```

  **问题 1（形态空洞）**：结论含 `↔ True`，是**恒真特例形态**，被主控的
  **剥注释检查器 `hollow_check.py`** 命中（`[IFF-True]`）。
  **注意**：子代理的 `grep` 版检查器**没有**找到这处（因为它被 grep 的
  `--` 行注释误报/漏报噪声淹没），这是主控新检查器的**净增益**。

  **问题 2（被完全覆盖）**：紧邻下方有**更强且更有信息**的真定理

  ```lean
  theorem noDescendant_is_dead_premise (Q : Prop) :
      (S.NoDescendant → Q) ↔ Q
  ```

  它断言「**任何**以前件为 `NoDescendant` 的断言，其全部内容**就是**后件 `Q`」——
  对**所有** `Q` 成立。而 `NoDescendant ↔ True` 只是它在 `Q := True` 处的
  **特例**（并且信息量**严格更少**：它只说「真」，不说「删掉前件后剩下什么」）。

  **⟹ 删除。** 需要该特例时，用 `noDescendant_is_dead_premise S True`
  （得到 `(S.NoDescendant → True) ↔ True`），或直接用更强的
  `S.noDescendant_tautologically_true`（得到 `S.NoDescendant` 本身）。

  同一结论的**非空洞**表达已在下方两处保留：
  * `noDescendant_tautologically_true : TautologicallyTrue S.NoDescendant`；
  * `noDescendant_is_dead_premise (Q) : (S.NoDescendant → Q) ↔ Q`。 -/

/-- ⭐⭐⭐ **`NoDescendant` 作为前件是死前提**。

  把 §2 的主定理**实例化**到这个具体的 `NoDescendant` 上：
  任何以它为前件的断言，其全部内容就是后件 `Q`。 -/
theorem noDescendant_is_dead_premise (Q : Prop) :
    (S.NoDescendant → Q) ↔ Q :=
  imp_iff_right_of_tautologicallyTrue S.noDescendant_tautologically_true

/-- ⭐⭐⭐ **具体化：`BackdoorConditions` 风格的「`NoDescendant` 格」无内容**。

  `Fate/BackdoorCriterion.lean` 的 `BackdoorConditions` 里有一格
  `no_descendant : S.NoDescendant`。这条定理说明：
  **凡以该格为（唯一）前件的推导，都可以把该格删掉**。 -/
theorem drop_noDescendant_hypothesis {Q : Prop}
    (h : S.NoDescendant → Q) : Q :=
  eliminate_dead_premise S.noDescendant_tautologically_true h

/-! **补充**：恒真性**与载体的具体取值无关** —— 换任何 `fX` 都恒真。
  这从另一个角度说明它是「签名事实」。 -/
theorem noDescendant_tautologically_true_for_any_fX
    (Z Ux X : Type) (f : Z → Ux → X) :
    TautologicallyTrue
      (NoDescendant ⟨Z, Ux, X, f⟩) :=
  fun _ _ => rfl

end MiniBackdoorSetup

/-! ===========================================================================
  §4 **反审计（阴性对照）：什么时候**不是**死前提？**

  §3 的结论「`NoDescendant` 恒真」是**好的坏消息**：它只说明**这个载体**上
  该条件退化。要审计得更彻底，必须回答「**什么样的前件才算有内容**」。
  最小的标准是：**存在使它为假的实例**（`¬ P` 可证）。
=========================================================================== -/

/-- **前件有内容（非恒真）的判据**：存在一个**可证的否定**。

  这是**构造性**的审计判据：给出 `¬ P` 的证明，就**证明**了 `P` 不是死前提。 -/
def HasContent (P : Prop) : Prop := ¬ P

/-- ⭐⭐ **互斥性**：`P` 恒真与 `P` 有内容**不能同时成立**。
  （即审计不会自相矛盾：一条命题要么是死前提，要么有内容。） -/
theorem not_tautologicallyTrue_and_hasContent (P : Prop) :
    ¬ (TautologicallyTrue P ∧ HasContent P) :=
  fun ⟨hP, hnP⟩ => hnP hP

/-- **有内容 ⟹ 非恒真**（把 `HasContent` 翻译回 `¬ TautologicallyTrue`）。 -/
theorem not_tautologicallyTrue_of_hasContent {P : Prop} (h : HasContent P) :
    ¬ TautologicallyTrue P :=
  h

/-- **一个「有内容」的具体例子**（范式对照）：`False` 有内容（因为 `¬ False` 可证），
  因此它不是死前提。这条用来**校准**审计器的判定方向：
  审计器既能认出「恒真」，也能认出「可假」。 -/
theorem false_has_content : HasContent False :=
  fun h => h

/-- **一个「有内容」的非平凡例子**（只用纯逻辑，不依赖算术库）：
  命题 `False → False`… 不行，它是恒真的。改用 `id`：

  `P := ∀ A : Prop, A` —— 它**不可证**（否则 `False` 可证），
  因此 `¬ TautologicallyTrue (∀ A : Prop, A)`，即该前件**有内容**。 -/
theorem forall_prop_not_tautologicallyTrue :
    ¬ TautologicallyTrue (∀ A : Prop, A) :=
  fun h => (h False)

/-! ===========================================================================
  §5 **可复用审计器：`AuditVerdict`**

  把两种审计结论打包成一个**可调用的判定结构**，供后续审计模块统一引用。
=========================================================================== -/

/-- **审计判决**：
  * `dead`       —— 前件恒真（**死前提**），定理无独立内容；
  * `content`    —— 前件可假（**有内容**），定理有实质信息。 -/
inductive AuditVerdict where
  /-- 前件恒真：死前提。 -/
  | dead
  /-- 前件可假：有内容。 -/
  | content
  deriving Repr, DecidableEq

/-- **从证明构造判决**：给出恒真证明 ⟹ `dead`。 -/
def AuditVerdict.ofTautologicallyTrue {P : Prop} (_ : TautologicallyTrue P) :
    AuditVerdict :=
  AuditVerdict.dead

/-- **从反证构造判决**：给出否定证明 ⟹ `content`。 -/
def AuditVerdict.ofHasContent {P : Prop} (_ : HasContent P) : AuditVerdict :=
  AuditVerdict.content

/-- ⭐ **审计一致性**：同一前件**不能**既被判 `dead` 又被判 `content`。
  这是审计器**可信**的最低要求；其证明就是 §4 的 `HasContent`/恒真互斥。 -/
theorem auditVerdict_exclusive {P : Prop}
    (hP : TautologicallyTrue P) (hnP : HasContent P) : False :=
  hnP hP

/-- ⭐⭐⭐ **〔任务 3 的总结陈述〕审计主定理：前件恒真 ⟹ 定理无内容**
  —— 把 §2 的主定理与 §3 的 `NoDescendant` 例子**接起来**，
  给出一个**可直接引用**的「无内容」形式化陈述：

  > 若前件 `P` 恒真，则对**任意**后件 `Q`，`P → Q` 的**可证性**等于
  > `Q` 的可证性；特别地，`NoDescendant` 型的假设格**恒可删除**。 -/
theorem audit_principle {P : Prop} (hP : TautologicallyTrue P) :
    (∀ Q : Prop, (P → Q) ↔ Q) ∧ (∀ Q : Prop, (P → Q) → Q) :=
  ⟨fun _ => imp_iff_right_of_tautologicallyTrue hP,
   fun _ h => h hP⟩

/-- **审计原理的 `NoDescendant` 实例**（本仓库第一条**真正**的死前提审计结论）。 -/
theorem noDescendant_audit_principle (S : MiniBackdoorSetup) :
    (∀ Q : Prop, (S.NoDescendant → Q) ↔ Q) :=
  fun Q => MiniBackdoorSetup.noDescendant_is_dead_premise S Q

/-! ===========================================================================
  §6 **扩展到「对任意实例」的恒真（schema 层面）**

  §3 的 `NoDescendant` 是**单个封闭 `Prop`** 的恒真。更常见的情况是
  「**一族**命题 `P : α → Prop` 对**任意** `a` 都成立」。这时正确的
  陈述是 `∀ a, P a`，而它的「无内容」后果同样成立。
=========================================================================== -/

/-- **schema 层面的恒真**：`∀ a, P a`。 -/
def TautologicallyTrueFamily {α : Type} (P : α → Prop) : Prop := ∀ a, P a

/-- ⭐ **schema 层面的主定理**：一族命题恒真 ⟹ 以其中**任一实例**为前件的
  蕴含式与后件等价。 -/
theorem imp_iff_right_of_tautologicallyTrueFamily {α : Type} {P : α → Prop}
    {Q : Prop} (hP : TautologicallyTrueFamily P) (a : α) : (P a → Q) ↔ Q :=
  imp_iff_right (hP a)

/-- **`NoDescendant` 本质上是「按 `(z, ux)` 索引的一族恒真命题」**。

  这条把 §3 的结论**解释清楚**：`NoDescendant` 之所以恒真是因为它是
  「对每个 `(z, ux)`,`fX z ux = fX z ux`」这一族（每个实例都是 `rfl`）。 -/
theorem noDescendant_is_tautologicallyTrueFamily (S : MiniBackdoorSetup) :
    TautologicallyTrueFamily (fun (p : S.Z × S.Ux) => S.fX p.1 p.2 = S.fX p.1 p.2) :=
  fun _ => rfl

end FateV2.Meta.DeadPremiseAudit
