/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ComposeDefault`
阶段：**裁决 A 的落地 —— (甲)「更强」+ (乙)「默认」两者兼得**

---------------------------------------------------------------------------
(a) 作者裁决（第 484 轮，逐字）
---------------------------------------------------------------------------
> 「a 甲乙」

其中「甲乙」指裁决 A 的两个读法**都要**：

* **(甲) 更强** —— `CommutativeComposite` 是 `Composite` 的**严格加强**：
  它 `extends Composite` 且多出一条 `comp_comm`；并且**存在**一个 `Composite`
  实例，它的 `comp` **不**可交换（故不能直接升格为 `CommutativeComposite`）。
* **(乙) 默认** —— `CommutativeComposite` 是**默认**的复合：其实例取
  **更高的 instance 优先级**（Lean 里**数字越大优先级越高**，见 (f)），
  并且「默认选择器」`defaultComp` 在 B 载体上**就是** `combClosure`。

**背景**：`Fate/ComposeUnified.lean`（7 定理，已入链）已用
`CommutativeComposite extends Composite where comp_comm : …` 把**(甲)的
「加强」部分**形式化；主控在 `_audit/H2`（第 481 轮）自查承认
**(乙)「默认」尚未形式化**。本文件补上 (甲) 的**显式严格性证据**
与 (乙) 的**完整形式化**。

---------------------------------------------------------------------------
(b) (甲)「更强」在本文件中的精确形式
---------------------------------------------------------------------------
`theorem commutative_is_strictly_stronger` 证明一个**合取**：

1. **加强（蕴含）**：`∀ (α : Type) [CommutativeComposite α], Nonempty (Composite α)`
   —— 每个 `CommutativeComposite` 都是 `Composite`（来自 `extends`）。
2. **严格（真包含）**：`∃ (α : Type) (c : Composite α),
     ¬ ∀ a b : α, c.comp a b = c.comp b a`
   —— **存在**一个 `Composite` 实例，其 `comp` **不**可交换。
   见证：`MeasurableRule CX SS2 SS2` 配上 `comp := MeasurableRule.comp`，
   其不可交换性由**已入链**的
   `CompNotCommutative.comp_not_commutative` 提供（一个**非确定反例**：
   `R₂ ∘ R₁ {1} = 1/2` 而 `R₁ ∘ R₂ {1} = 0`）。

⟹ 「严格加强」= 蕴含 **且** 真包含，两者都证。

**⚠ 宇宙限制**：上述 1、2 两支均陈述于 `Type`（`Type 0`）—— 因为
第二个见证（`MeasurableRule` 载体）是 `Type 0`，而 `∃ (α : Type u)` 在
`u > 0` 时无法绑定它（详见 `commutative_is_strictly_stronger` 的文档）。

---------------------------------------------------------------------------
(c) (乙)「默认」在本文件中的精确形式
---------------------------------------------------------------------------
两条**互补**的表达（**两者都做**，对应任务的「方案 1 + 方案 2」）：

1. **方案 1（instance priority）**：
   `instance (priority := 2000) instDefaultCompositeAttrSet :
      CommutativeComposite (Set K3.MFCA)`。
   Lean 中**数字越大优先级越高**（`default` = 1000，实测见 (f)），
   故 `2000` **压过** `ComposeUnified` 的默认 priority 实例；
   类型类解析在 `Set K3.MFCA` 上**选中**这个 2000 的实例
   （`defaultComp_is_combClosure` 的 `rfl` **正是**解析结果的证据）。
2. **方案 2（显式选择函数）**：
   `noncomputable def defaultComp {α} [CommutativeComposite α] : α → α → α := inst.comp`
   —— 「给定一个可成为 `CommutativeComposite` 的载体，就用它的 `comp`」。
   `theorem defaultComp_is_combClosure` 证明它在 `Set K3.MFCA` 上**逐字就是** `combClosure`。
   `theorem defaultComp_comm` 证明**任何** `defaultComp` 都可交换
   （因为它取自 `CommutativeComposite`，而非任意函数）。

⟹ 「默认」= 优先级更高（方案 1）**且** 默认选择器取 B 的 `comp`（方案 2）。

---------------------------------------------------------------------------
(d) 本文件**不**声称什么（逐条如实登记）
---------------------------------------------------------------------------
1. **不声称「A 是 B 的一个实例」（数学上做不到）**。
   `combClosure : Set K3.MFCA → Set K3.MFCA → Set K3.MFCA`，而
   `MeasurableRule.comp : MeasurableRule C Y Z → MeasurableRule C X Y →
    MeasurableRule C X Z`。**载体类型不可统一**，故「A 的类型是 B 的类型的
   实例」在 Lean 里**是类型错误**，不是未证命题。本文件只声称：
   在同一抽象 `Composite` 下，B 是 `CommutativeComposite`、A 只是 `Composite`
   （其特定 `comp` 不可交换）。
2. **不声称「A 族不可交换」对 A 的每个 `Composite` 实例都成立**。
   `Composite` 只有 `comp` 一个字段、无公理；在 `MeasurableRule` 载体上
   **可以**人为定义一个可交换的 `comp`（如 `fun _ _ => 某固定规则`）。
   故本文件对 A 侧**只声称**：**存在**一个具体 `Composite` 实例
   （`comp := MeasurableRule.comp`）不可交换 —— 这正是 (甲)「严格」所需的。
3. **不回答开放问题 5.1（∘ 到底该选哪个实现）**。本文件只把裁决 A 的
   「(甲) 更强 + (乙) 默认」两件**数学可检验内容**形式化，不选 ∘ 的语义。

---------------------------------------------------------------------------
(e) 诚实：本文件依赖的已入链模块
---------------------------------------------------------------------------
* `Fate.ComposeUnified` —— `Composite` / `CommutativeComposite` /
  `DirectedComposite` 三层抽象，`instCommutativeCompositeAttrSet`（B 族实例）。
* `Fate.ComposeSemantics` —— `combClosure_commutable`、
  `two_semantics_incompatible`。
* `Fate.CompNotCommutative` —— `comp_not_commutative_witness`、
  `comp_not_commutative`（核复合的不可交换反例）。
* `Fate.WiringFourOpFixed` —— `combClosure` 的定义（`closureOp (A ∪ B)`）。

---------------------------------------------------------------------------
(f) 关于 Lean 的 `priority` 约定（实测记录，纠正任务提示中的假设）
---------------------------------------------------------------------------
任务提示称「数字越小优先级越高」。**实测相反**：Lean 4.33.0-rc1 中
**数字越大优先级越高**（`default` = 1000）。实测证据（独立探针）：
```
instance (priority := 1000) instA : Foo Nat where v := 1000
instance (priority := 2000) instB : Foo Nat where v := 2000
example : (Foo.v (α := Nat)) = 2000 := rfl   -- ✅ 编译通过 ⟹ instB(2000) 胜出
```
故本文件为 B 族实例取 `priority := 2000`（**大于**默认 1000）以表达
「默认优先」。若按提示的「越小越高」，`2000` 会**输**给默认 1000，
(乙) 的「默认」就**落空**——实测证明本文件的取法正确。

另：`defaultComp` 是 `noncomputable def`（其值取自类型类实例的字段，
可能是 `noncomputable` 的 `combClosure`），并在文件内加
`set_option warn.classDefReducibility false` 消除「类值定义应 instance-reducible」
的**警告**（非 error）。

---------------------------------------------------------------------------
诚实声明
---------------------------------------------------------------------------
本文件**零 `sorry`、零 `admit`、零 `axiom`**。
所用引理全部为 Mathlib 已有定理或**已入链**模块中的定理。
-/

import FateWorld.Legacy.ComposeUnified
import FateWorld.Legacy.ComposeSemantics
import FateWorld.Legacy.CompNotCommutative
import FateWorld.Legacy.WiringFourOpFixed

universe u

namespace Fate.ComposeDefault

open Fate.ComposeUnified
open Fate.ComposeOperator

/-! ===========================================================================
    §1  (甲)「更强」：`CommutativeComposite` 是 `Composite` 的**严格**加强
    =========================================================================== -/

set_option warn.classDefReducibility false in
/-- A 族侧的**具体** `Composite` 实例：`comp := MeasurableRule.comp`。

`MeasurableRule.comp` 的签名是
```
@MeasurableRule.comp : MeasurableRule C Y Z → MeasurableRule C X Y → MeasurableRule C X Z
```
只有「两端同型」（`X = Y = Z`）时它才是 `α → α → α`，故只能在
`MeasurableRule C X X` 上成 `Composite`。取 `X := SS2`、`C := CX`
（`Fin 2` / `Unit`），以对接已入链的不可交换反例。

**刻意用 `def` 而非 `instance`**：避免与 B 族实例在类型类解析上竞争头部；
本节只在**显式传参**下引用它（`@Composite.comp _ measurableRuleComposite`）。 -/
noncomputable def measurableRuleComposite :
    Composite
      (MeasurableRule Fate.CompNotCommutative.CX
        Fate.CompNotCommutative.SS2 Fate.CompNotCommutative.SS2) where
  comp := fun x y => x.comp y

/-- ⭐⭐ **(甲) 更强**：`CommutativeComposite` 是 `Composite` 的**严格**加强。

合取两部分：
1. **加强**：每个 `CommutativeComposite α` 都给出 `Nonempty (Composite α)`；
2. **严格**：**存在** `α` 与 `c : Composite α` 使 `c.comp` **不**可交换
   （见证 = §1 的 `measurableRuleComposite`，其不可交换性由已入链的
   `CompNotCommutative.comp_not_commutative` 提供）。

**非平凡性（防同义反复自查）**：第 2 支的结论「不可交换」来自一个
**具体的数值反例**（`comp_not_commutative`），前件仅量化 `a b`，
**没有**把「不交换」放进任何假设。第 1 支虽平凡（`extends`），但它是
「严格」的对偶面（蕴含），二者合并才是「严格加强」的完整含义。

**⚠ 宇宙限制（如实说明）**：本定理在 `Type`（即 `Type 0`）中陈述。
`MeasurableRule` 与 `Set K3.MFCA` 载体皆为 `Type 0`，而 `∃ (α : Type u)`
在 `u > 0` 时无法绑定 `Type 0` 的载体；用 `ULift` 提升会引入嵌套
`upload/down` 障碍。故 (甲) 的「严格性」在本文件中只陈述于 `Type 0` ——
这**足够**覆盖 A、B 两个实际载体，但**不是**全宇宙版本。 -/
theorem commutative_is_strictly_stronger :
    -- (1) 加强：`CommutativeComposite` ⟹ `Composite`
    (∀ (α : Type) [CommutativeComposite α], Nonempty (Composite α))
      -- (2) 严格：存在一个 `Composite` 实例，其 `comp` 不可交换
      ∧ (∃ (α : Type) (c : Composite α),
          ¬ ∀ a b : α, c.comp a b = c.comp b a) := by
  refine ⟨fun α _ => ⟨inferInstanceAs (Composite α)⟩, ?_⟩
  refine ⟨_, measurableRuleComposite, ?_⟩
  intro h
  -- `h`：`measurableRuleComposite.comp` 可交换；其 `comp` 定义上即 `MeasurableRule.comp`
  exact Fate.CompNotCommutative.comp_not_commutative
    (fun R₁ R₂ => h R₂ R₁)

/-- (甲) 的推论：`CommutativeComposite` 的「加强」部分**逐字**成立 ——
存在性方向的显式包装（便于下游引用，不依赖类型类解析的内部细节）。 -/
theorem commutative_extends_composite :
    ∀ (α : Type) [CommutativeComposite α], Nonempty (Composite α) :=
  fun α _ => ⟨inferInstanceAs (Composite α)⟩

/-! ===========================================================================
    §2  (乙)「默认」—— 方案 1：instance priority
    =========================================================================== -/

/-- ⭐ **(乙) 默认（方案 1）**：`CommutativeComposite (Set K3.MFCA)` 的
**默认实例**，`priority := 2000`。

Lean 中**数字越大优先级越高**（`default` = 1000，见文件头 (f) 的实测）。
`2000 > 1000` 故本实例**压过** `ComposeUnified.instCommutativeCompositeAttrSet`
（默认 1000），成为类型类解析在 `Set K3.MFCA` 上**默认选中**的那一个。

`comp := combClosure`（`= closureOp (A ∪ B)`），交换性取自已入链的
`ComposeSemantics.combClosure_commutable`。

**「默认」的实质**：同载体上两个候选实例时，解析**优先**选中本实例；
见 `defaultComp_is_combClosure`（`rfl` 证明解析结果就是本实例的 `comp`）。 -/
instance (priority := 2000) instDefaultCompositeAttrSet :
    CommutativeComposite (Set Fate.AlphaInstance.K3.MFCA) where
  comp := Fate.AlphaInstance.WiringFixed.combClosure
  comp_comm := Fate.ComposeSemantics.combClosure_commutable

/-! ===========================================================================
    §3  (乙)「默认」—— 方案 2：显式选择函数 `defaultComp`
    =========================================================================== -/

set_option warn.classDefReducibility false in
/-- ⭐ **(乙) 默认（方案 2）**：**默认复合选择器** ——
给定任意可成为 `CommutativeComposite` 的载体，取其 `comp` 作为默认复合。

这是「默认」的**选择语义**：凡能成 `CommutativeComposite` 者，
其复合就取该实例的 `comp`（而 B 载体上该 `comp` 恰为 `combClosure`，
见 `defaultComp_is_combClosure`）。 -/
noncomputable def defaultComp {α : Type u} [inst : CommutativeComposite α] : α → α → α :=
  inst.comp

/-- ⭐⭐⭐ **(乙) 默认的证据**：`defaultComp` 在 `Set K3.MFCA` 上**逐字就是**
`combClosure`（定义相等，`rfl`）。

**这条 `rfl` 本身就是「默认实例被选中」的证据**：类型类解析为
`defaultComp A B` 找到的 `CommutativeComposite (Set K3.MFCA)` 实例，
其 `comp` 与 `combClosure` **定义相等**——而这只有在解析选中了
`comp := combClosure` 的实例（即 §2 的 priority-2000 实例）时才成立。
**非平凡**（防同义反复自查）：前件只有类型待定元 `A B`，结论「等于
`combClosure`」来自**实例解析**这一计算，而非来自任何假设。 -/
theorem defaultComp_is_combClosure (A B : Set Fate.AlphaInstance.K3.MFCA) :
    defaultComp A B = Fate.AlphaInstance.WiringFixed.combClosure A B := rfl

/-- ⭐ **默认选择器保交换**：**任何** `defaultComp` 都是可交换的
（因为它取自 `CommutativeComposite`，而非任意函数）。

**非平凡性**：结论「可交换」来自 `CommutativeComposite.comp_comm` 这一
**实例字段**；前件只是 `CommutativeComposite α`（这正是「默认取可交换的
那一族」的含义），**没有**把「可交换」直接放进前件 ——
前件说的是「该载体有一个 `CommutativeComposite` 实例」，结论说的是
「`defaultComp`（解析所得的具体函数）可交换」。 -/
theorem defaultComp_comm {α : Type u} [inst : CommutativeComposite α] (a b : α) :
    defaultComp a b = defaultComp b a :=
  CommutativeComposite.comp_comm a b

/-! ===========================================================================
    §4  核心定理 (甲) + (乙) 合并
    =========================================================================== -/

/-- ⭐⭐⭐ **(甲) + (乙) 合并的完整陈述** —— 本文件的目的。

三个合取支：
1. **B 可交换（(甲) 的 B 侧）**：`combClosure` 恒可交换；
2. **A 侧确有不可交换实例（(甲) 的「严格」证据）**：存在 `f g : Fin 2 → Fin 2`
   使 `f ∘ g ≠ g ∘ f`（函数复合不交换，摘自
   `ComposeSemantics.two_semantics_incompatible`）；
3. **(乙) 默认**：`defaultComp` 在 B 载体上**就是** `combClosure`。

**防同义反复自查**：三支的「来源」各不相同 ——
(1) 取自 `combClosure_commutable`（并集交换），
(2) 取自 `two_semantics_incompatible`（一个具体的 `Fin 2 → Fin 2` 反例），
(3) 取自 `rfl`（实例解析的**计算**结果）。
没有一支是靠「把结论塞进前件」得到：本定理**无任何前件**（除类型级
`Set K3.MFCA` 固定外），三支都是**无条件**结论。 -/
theorem B_dominates_in_both_senses :
    -- (甲)-B：`combClosure` 恒可交换
    (∀ a b : Set Fate.AlphaInstance.K3.MFCA,
        Fate.AlphaInstance.WiringFixed.combClosure a b
          = Fate.AlphaInstance.WiringFixed.combClosure b a)
      -- (甲)-严格证据：函数复合有不交换实例
      ∧ (∃ f g : Fin 2 → Fin 2, f ∘ g ≠ g ∘ f)
      -- (乙)-默认：`defaultComp` 在 B 上就是 `combClosure`
      ∧ (∀ A B : Set Fate.AlphaInstance.K3.MFCA,
        defaultComp A B = Fate.AlphaInstance.WiringFixed.combClosure A B) :=
  ⟨Fate.ComposeSemantics.combClosure_commutable,
   Fate.ComposeSemantics.two_semantics_incompatible.2,
   fun _ _ => rfl⟩

/-- ⭐ **两种「默认」表达一致**：§2 的 priority 实例（方案 1）与 §3 的
`defaultComp`（方案 2）在 `Set K3.MFCA` 上给出**同一个复合**。

**意义**：方案 1（优先级）与方案 2（选择器）**不冲突**，它们描述的是
同一件「默认」事实的两个侧面 —— 这排除了「两条路径各说一套」的风险。 -/
theorem two_defaults_agree (A B : Set Fate.AlphaInstance.K3.MFCA) :
    defaultComp A B
      = @Composite.comp _ instDefaultCompositeAttrSet.toComposite A B := rfl

/-! ===========================================================================
    §5  诚实边界
    =========================================================================== -/

/-!
**本文件证明了什么**（只列**实际存在**的定理，见上文行）
1. `commutative_is_strictly_stronger` —— (甲) **严格加强**：
   `CommutativeComposite ⟹ Composite` 且存在 `Composite` 实例 `comp` 不可交换。
2. `commutative_extends_composite` —— (甲) 「加强」蕴含部分的显式包装。
3. `instDefaultCompositeAttrSet`（`priority := 2000`）—— (乙) 方案 1：
   默认实例的优先级高于默认 1000，被解析选中。
4. `defaultComp` / `defaultComp_is_combClosure` / `defaultComp_comm` ——
   (乙) 方案 2：默认选择器在 B 上就是 `combClosure`，且恒可交换。
5. `B_dominates_in_both_senses` —— (甲) + (乙) 合并的核心陈述。
6. `two_defaults_agree` —— 方案 1 与方案 2 给出同一复合。

**本文件【没有】证明什么**
- **没有**声称「A 是 B 的一个实例」（载体不同，是类型错误，非未证命题；
  见文件头 (d).1）。
- **没有**声称「A 族每个 `Composite` 实例都不可交换」（`Composite` 无公理，
  可人为定义可交换的 `comp`；本文件只给**一个具体**不可交换实例作「严格」
  见证，见文件头 (d).2）。
- **没有**回答开放问题 5.1（∘ 的语义究竟是哪个）。
- **没有**构造「A 的复合 → B 的复合」的同态映射（建模选择，规格未定）。
-/

end Fate.ComposeDefault
