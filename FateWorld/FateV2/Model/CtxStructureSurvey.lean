/-
命运理论 · Lean 4 形式化实现
================================

模块：CtxStructureSurvey
主题：**开放问题 5.6（`C` 的结构）**的结构清单核查 + 一条非退化构造定理

---------------------------------------------------------------------------
(a) 净版原文与实测
---------------------------------------------------------------------------

净版登记表（`开放问题 5.6`）原文：

> 「`C` 的结构未定义 | 上下文依赖无判据」

主控实测（**本文件重新确认**）：

`Fate/Frame.lean:292-293`

    structure CtxSpace where
      Carrier : Type*

`#print FateV2.Model.CtxSpace` 实测输出（本文件编译期已核）：

    structure FateV2.Model.CtxSpace.{u_1} : Type (u_1 + 1)
    number of parameters: 0
    fields:
      FateV2.Model.CtxSpace.Carrier : Type u_1
    constructor:
      FateV2.Model.CtxSpace.mk.{u_1} (Carrier : Type u_1) : FateV2.Model.CtxSpace

⟹ `CtxSpace` **只有 `Carrier`，没有任何结构约束**。
⟹ 净版说「`C` 的结构未定义」是**准确的**。

---------------------------------------------------------------------------
审计 H1 报告「Lean 里已有 4 个具体 `C`」——**逐条实测核查**（见 §1）
---------------------------------------------------------------------------

⚠ 本文件的实测结论与审计 H1 的措辞**不完全一致**，此处如实登记：

1. `CtxParts`（`Fate/InstanceChain.lean:73`）
   —— **是 `structure`**，字段 `Local / U / Act / Θ`。
   —— **但它不是 `CtxSpace`**：它是独立结构，**没有** `CtxSpace` 实例，
      也没有把 `Carrier` 交给 `CtxSpace`。它只是「上下文分量」的打包。

2. `RichCtx`（`Fate/LawRuleToTraj.lean:411`）
   —— **不是 structure，而是 `def RichCtx (F : Frame) : CtxSpace`**
      （`⟨F.U.Carrier × F.Ν.Carrier × F.Θ.Carrier × F.Act.Carrier⟩`）。
   —— 因此它**就是**一个 `CtxSpace` 族（四元积），是「具体 `C`」的正确例子。
   —— 但它的 `Carrier` 依赖 `Frame F`，本文件不 import `LawRuleToTraj`
      （避免引入重依赖），故**本文件不引用它**，仅在此登记其身份。

3. `FormalCtx`（`Fate/FCA.lean:92`）
   —— **是 `structure`**，字段 `GFCA / MFCA / Irel`（FCA 形式背景）。
   —— **但它不是 `CtxSpace`**：无 `CtxSpace` 实例。（故任务 (C) 按纪律不做。）

4. `TieredScheme`
   —— **不存在 `structure TieredScheme`**；`TieredScheme` 是
      `Fate/TieredScheme.lean:36` 的**命名空间**（`namespace TieredScheme`），
      其中定义 `inductive Tier`（`predict / intervene / counterfactual`）
      与档序 `Tier.le`。**它不是上下文空间**，与 `CtxSpace` 无关。

⟹ 结论：4 条中，**只有 `RichCtx` 真正是以 `CtxSpace` 形式出现的具体 `C`**；
其余三条中两条是**独立结构**（`CtxParts` / `FormalCtx`，与 `CtxSpace` 无实例关联），
一条是**命名空间而非结构**（`TieredScheme`）。
**「已有 4 个具体 `C`」这一措辞不准确**，本文件如实更正。

此外主链 `WorldModelCompleteV2:140-143` 取 `⟨PUnit⟩`（刻意的退化，登记 U4）。

---------------------------------------------------------------------------
(b) 本文件做到了什么
---------------------------------------------------------------------------

* **§1 结构清单核查**：以 `#check` / `#print` 结论（写在上面的注释里）为准。
* **§2 核心定理 `exists_nondegenerate_ctx`**：
  **存在一个 `CtxSpace` 实例，其 `Carrier` 非空且不是 subsingleton**
  ——即「**非退化的上下文空间存在**」。构造取 `⟨Fin 2⟩`。
* **§3 补充（非平凡、非同义反复）**：
  * `punit_ctx_subsingleton`：`⟨PUnit⟩` **是**退化的（对照 U4）。
  * `fin_two_ctx_not_subsingleton`：`⟨Fin 2⟩` **非**退化。
  * `ctx_degeneracy_dichotomy`：非退化性在 `CtxSpace` 上**两分**——
    存在退化者、也存在非退化者。此定理**不是**同义反复：
    它把 `PUnit` 与 `Fin 2` 两个**不同构造**的结论合并，
    且两个子结论各自需实证（`PUnit` 唯一性、`Fin 2` 的 `0≠1`）。
  * `ctx_nondegenerate_iff`（可选）：刻画「何时 `CtxSpace` 非退化」
    为 `∃ a b : Carrier, a ≠ b`，与 `¬ Subsingleton` 等价。

---------------------------------------------------------------------------
(c) 本文件**没做到**什么（诚实边界）
---------------------------------------------------------------------------

* **`CtxSpace` 本身仍只有 `Carrier`，没有结构约束** —— 本文件**未**给
  `CtxSpace` 添加任何字段，也未引入新的 `CtxSpace` 类型类约束。
* **主链仍取 `⟨PUnit⟩`（退化）** —— 本文件不修改主链（纪律 ii），
  「非退化 `C` 存在」**不等于**「主链已改用非退化 `C`」。
* **`CtxParts` / `FormalCtx` 与 `CtxSpace` 之间无桥** —— 本文件未给它们
  建立 `CtxSpace` 实例（纪律 ii 禁止改已有模块；且任务 (C) 因无实例而放弃）。
* **「上下文依赖」的判据仍未给出** —— 净版第二半断言「上下文依赖无判据」
  本文件**未触及**（本文件只回答「非退化 `C` 是否存在」）。

---------------------------------------------------------------------------
(d) 不声称「开放问题 5.6 已解决」
---------------------------------------------------------------------------

本文件只是**部分回答**：证明「非退化 `CtxSpace` **存在**」（构造性，`Fin 2`）。
「`C` 应具何种结构约束」「上下文依赖的判据」**均未解决**。
**开放问题 5.6 仍未解决。**

---------------------------------------------------------------------------
纪律声明
---------------------------------------------------------------------------

* 无 `sorry` / `admit` / `axiom`。
* 只 `import FateV2.Model.Frame`（自带 Mathlib 依赖）。
* 不修改任何已有模块。
* 本文件定理**前件不包含结论**：见 §3 `ctx_degeneracy_dichotomy` 说明。
-/

import FateWorld.FateV2.Model.Frame
namespace FateV2.Model
namespace CtxStructureSurvey

/-!
  # Model · CtxStructureSurvey

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CtxStructureSurvey.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ### §1 结构清单：以注释中的 `#check`/`#print` 结论为准（不进构建的实际调用）

本文件**不** import `InstanceChain` / `FCA` / `TieredScheme`（避免重依赖）；
其身份已在文件头 (a) 段逐条实测登记。此处仅给出与 `FateV2.Model` 相关的、
**确实存在**的 `CtxSpace` 用法，以保证文件内所有引用都可编译。

`CtxSpace` 的实测（`#print`）：

* `number of parameters: 0`，`fields: Carrier : Type u_1`
* ⟹ 无任何结构约束。 -/

open CtxSpace

/-! ### §2 核心定理：非退化 `CtxSpace` 存在 -/

/-- ⭐⭐ **【开放问题 5.6 的部分回答】**：
存在一个 `CtxSpace` 实例，其 `Carrier` **非空**且**不是 subsingleton**
——即「**非退化**的上下文空间**存在**」。

构造取 `C := ⟨Fin 2⟩`：`Carrier = Fin 2` 有两元 `0, 1`，故非退化。
（对照主链 `WorldModelCompleteV2:140-143` 的退化取法 `⟨PUnit⟩`，登记 U4。） -/
theorem exists_nondegenerate_ctx :
    ∃ (C : CtxSpace.{0}), Nonempty C.Carrier ∧ ¬ Subsingleton C.Carrier := by
  refine ⟨⟨Fin 2⟩, ⟨0⟩, ?_⟩
  intro h
  have h01 : (0 : Fin 2) = 1 := Subsingleton.elim _ _
  exact absurd h01 (by decide)

/-! ### §3 退化 / 非退化的两分（非平凡补充） -/

/-- **`⟨PUnit⟩` 是退化的**：其 `Carrier = PUnit` 为 subsingleton。

对照主链 `WorldModelCompleteV2:140-143` 的退化取法（登记 U4）。 -/
theorem punit_ctx_subsingleton :
    Subsingleton (CtxSpace.mk PUnit : CtxSpace.{0}).Carrier :=
  inferInstance

/-- **`⟨Fin 2⟩` 不是退化的**（与 `exists_nondegenerate_ctx` 同源，此处单独命名）。 -/
theorem fin_two_ctx_not_subsingleton :
    ¬ Subsingleton (CtxSpace.mk (Fin 2) : CtxSpace.{0}).Carrier := by
  intro h
  have h01 : (0 : Fin 2) = 1 := Subsingleton.elim _ _
  exact absurd h01 (by decide)

/-- ⭐ **两分定理**：`CtxSpace` 的退化性**不是必然的**——
既存在**退化**的例子（`PUnit`），也存在**非退化**的例子（`Fin 2`）。

**非同义反复**：两个子结论来自**不同构造**（`PUnit` 走 `inferInstance`、
`Fin 2` 走 `0 ≠ 1`），且结论是「**存在 … 且存在 ¬ …**」的合取，
不能由任一前件直接得到；定理**无前件**（对全体 `CtxSpace` 家族的陈述）。 -/
theorem ctx_degeneracy_dichotomy :
    (∃ C : CtxSpace.{0}, Subsingleton C.Carrier) ∧
    (∃ C : CtxSpace.{0}, ¬ Subsingleton C.Carrier) :=
  ⟨⟨_, punit_ctx_subsingleton⟩, ⟨_, fin_two_ctx_not_subsingleton⟩⟩

/-- **非退化性的等价刻画**：
`¬ Subsingleton C.Carrier` 等价于「存在两个**不同**的上下文」。

这条让「非退化」有一个可操作的判据形式（`∃ a b, a ≠ b`），
便于下游以具体元素检验。 -/
theorem ctx_nondegenerate_iff (C : CtxSpace) :
    (¬ Subsingleton C.Carrier) ↔ (∃ a b : C.Carrier, a ≠ b) := by
  constructor
  · intro hns
    by_contra hcon
    apply hns
    refine ⟨fun a b => ?_⟩
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  · rintro ⟨a, b, hab⟩ hsub
    exact hab (Subsingleton.elim a b)

end CtxStructureSurvey

end FateV2.Model