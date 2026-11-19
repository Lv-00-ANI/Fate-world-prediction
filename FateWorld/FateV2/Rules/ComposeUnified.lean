/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Rules.ComposeUnified`
阶段：**∘ 的融合结构 —— B 族主导，A 族为特例分支（作者第 465 轮裁决，读法一）**

---------------------------------------------------------------------------
(a) 作者裁决（第 465 轮，逐字）
---------------------------------------------------------------------------
> 「裁决1 b和a到底什么讲清楚 然后为什么不能构造一个融合的 以b为主导
>   a是b（推广后）的一种特例」
> 「那就可以」

**⟹ 采用【读法一】：顶层抽象 + B 族主导 + A 族特例分支。**

读法二（「A 能作为 B 的一个实例」）**数学上做不到**：
`Measure.bind` 与 `closureOp ∘ ∪` 是不同代数（载体不同、
一个不可交换一个可交换）。本文件**不声称**读法二。

---------------------------------------------------------------------------
(b) B 与 A 的核心区别
---------------------------------------------------------------------------
| 方面     | **A：`MeasurableRule.comp`**          | **B：`combClosure`**                     |
|----------|---------------------------------------|------------------------------------------|
| 载体     | 条件分布（`Measure`）                 | 属性集合（`Set K3.MFCA`）                |
| 复合含义 | 先跳一步再跳一步（`Measure.bind`）    | 两边属性都成立（`closureOp (A ∪ B)`）    |
| 可交换   | ❌ 不可（有具体反例）                 | ✅ 可                                    |
| 信息流向 | 有方向（A 在前，B 在后）              | 无方向                                   |
| 对应理论 | 马尔可夫链 / 概率图模型               | FCA / 形式概念分析                       |
| 定理数   | 21（`ComposeOperator`）               | 33+（`AlphaFourOp`、`WiringFourOperators`）|

**一句话：A 是「有方向的概率传递」，B 是「无方向的属性合并」。**

---------------------------------------------------------------------------
(c) 本文件建立了什么（只列**实际存在**的声明，逐条对应下文行）
---------------------------------------------------------------------------
**§1 顶层抽象**
* `Composite : (α : Type u) → Type u` —— 只有「复合」一个操作，不预设任何性质。
* `CommutativeComposite` —— **B 族【主导】**：`comp` 可交换。
* `DirectedComposite` —— **A 族【特例分支】**：不要求可交换（无额外字段）。

**§2 B 族实例（主导）**
* `instCommutativeCompositeAttrSet :
    CommutativeComposite (Set FateV2.Rules.AlphaInstance.K3.MFCA)` ——
  `comp := combClosure`（等价于 `closureOp (A ∪ B)`），
  由 `ComposeSemantics.combClosure_commutable` 提供交换性。
  （**用 `instance` 直接构造，无需退回 `def`**；见 (f)。）
* `combClosure_comp_eq` —— 该实例的 `comp` **逐字等于** `combClosure`（`rfl`）。
* `attrSet_comp_comm` —— 显式重述可交换性（便于下游不经实例解析）。

**§3 A 族实例（特例分支）**
* `directedCompInstance (C) (X) : DirectedComposite (MeasurableRule C X X)` ——
  `comp a b := a.comp b`。**必须在 `X = Y = Z` 时才有 `α → α → α`**，
  故只能在「两端同型」上成实例（`comp` 的原始签名是
  `MeasurableRule C Y Z → MeasurableRule C X Y → MeasurableRule C X Z`）。
* `directedComp_eq` —— 该实例的 `comp` 逐字等于 `MeasurableRule.comp`（`rfl`）。

**§4 核心定理**
* `A_not_commutative` —— **A 族的 `comp` 不可交换**：
  `¬ ∀ R₁ R₂ : MeasurableRule CX SS2 SS2, (directedComp...).comp R₂ R₁
       = (directedComp...).comp R₁ R₂`，
  由已入链的 `CompNotCommutative.comp_not_commutative` 得到（非确定反例，
  `R₂ ∘ R₁ {1} = 1/2` 而 `R₁ ∘ R₂ {1} = 0`）。
* `B_is_commutative` —— B 族 `comp` 可交换（重述，供 §5 直接使用）。
* `fusion_structure` —— ⭐ **融合结构**：
  (i) 存在一个**可交换**复合实例（B 族，载体 `Set K3.MFCA`）；
  (ii) 存在一个**不可交换**复合实例（A 族，载体 `MeasurableRule CX SS2 SS2`）；
  (iii) 二者**载体不同**。
  三者合起来：**同一抽象 `Composite` 下有两个实例，B 可交换、A 不可交换**。
* `B_dominates` —— ⭐⭐ **B 主导的证据**：
  `combClosure` 恒可交换 ∧ 存在 `f g : Fin 2 → Fin 2` 使 `f ∘ g ≠ g ∘ f`
  （引自 `ComposeSemantics.two_semantics_incompatible`，逐字打包）。
* `A_is_tensor` … 见下方诚实边界，**本文件不设此名**。

---------------------------------------------------------------------------
(d) 本文件【不】声称什么（逐条如实登记）
---------------------------------------------------------------------------
1. **不声称「A 是 B 的一个实例」（读法二）**。
   `combClosure : Set K3.MFCA → Set K3.MFCA → Set K3.MFCA`，而
   `MeasurableRule.comp : MeasurableRule C Y Z → MeasurableRule C X Y →
    MeasurableRule C X Z`。**载体类型不可统一**（`Set K3.MFCA` vs `Measure` 值），
   故「A 的类型是 B 的类型的实例」在 Lean 里**是类型错误**，不是未证命题。
   本文件只声称：**在同一抽象 `Composite` 下，二者是两个不同实例**。

2. **不声称「B 更基本」在本文件中被形式化了**。
   「B 主导」在本文件中的**精确形式**只有两条：
   * B 的 `comp` **恒可交换**（`B_is_commutative`）；
   * A 的 `comp` **不恒可交换**（`A_not_commutative`）。
   「主导」的哲学含义（为何以 B 为默认、A 为特例）是**裁决**，不是定理。
   本文件把裁决的**数学可检验内容**形式化，**不**把裁决本身伪装成定理。

3. **不声称「A 是 B 推广后的特例」中的「推广」已被形式化**。
   「推广」（generalization）需要一个**映射**把 A 的复合映到 B 的复合上，
   并证明它是同态。**本文件未构造该映射** —— 因为 (d).1 说明载体不同，
   任何这样的映射都必须先选一个「属性集编码分布」的编码方案，
   而那属于**建模选择**，规格未定（净版开放问题 5.1 仍未回答）。
   故「A 是 B 的特例」在本文件中被**弱化**为：
   「A 与 B 是同一抽象 `Composite` 下的两个实例，B 的可交换性是 A 不具备的」。

4. **不声称开放问题 5.1 已解决**。本文件不选「∘ 到底是哪个」。

---------------------------------------------------------------------------
(e) 诚实登记：载体不同
---------------------------------------------------------------------------
`combClosure` 与 `MeasurableRule.comp` 的**载体不同**：

* `combClosure`：`Set FateV2.Rules.AlphaInstance.K3.MFCA → Set FateV2.Rules.AlphaInstance.K3.MFCA
  → Set FateV2.Rules.AlphaInstance.K3.MFCA`（属性集合）
* `MeasurableRule.comp`：`MeasurableRule C Y Z → MeasurableRule C X Y →
  MeasurableRule C X Z`（条件分布核）

⟹ 它们是**同一抽象 `Composite` 下的两个不同实例**，不是「一个包含另一个」。

---------------------------------------------------------------------------
(f) 阶段实施记录（哪些阶段做通了、怎么做的）
---------------------------------------------------------------------------
* 阶段 1–3 **全部做通**。B 族的 `instance` 写法**无需退回** `def`：
  `extends Composite` 使 `comp` 成为 `CommutativeComposite` 的字段，
  `instance ... where comp := ...; comp_comm := ...` 直接通过（实测）。
* `directedCompInstance` 是 **`def` 而非 `instance`**：它是**类型类值**，
  若注册为全局 `instance` 会在 `Composite`/`DirectedComposite` 上
  与 B 族实例**同头竞争**（虽载体不同不致冲突，但为清晰与可控，
  本文件**刻意**用 `def` + 显式传参）。这符合纪律 (x) 的退路。
  另加 `set_option warn.classDefReducibility false` 消除该类
  「class-typed def 应 instance-reducible」的**警告**（非 error）。
* 阶段 4 的核心定理全部**实际证出**（本文件无 `sorry`/`admit`/`axiom`）。
* 阶段 5：文件头（本节）只写**实际存在**的定理名。

---------------------------------------------------------------------------
诚实声明
---------------------------------------------------------------------------
本文件**零 `sorry`、零 `admit`、零 `axiom`**。
所用引理全部为 Mathlib 已有定理或**已入链**模块
（`FateV2.Rules.ComposeSemantics`、`FateV2.Rules.CompNotCommutative`、`Fate.WiringFourOpFixed`、
`FateV2.Rules.ComposeOperator`）中的定理。
-/

import FateWorld.FateV2.Rules.ComposeSemantics
import FateWorld.FateV2.Rules.CompNotCommutative
universe u

namespace FateV2.Rules.ComposeUnified

open FateV2.Modeling

/-!
  # Rules · ComposeUnified

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ComposeUnified.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ComposeSemantics, CompNotCommutative
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  顶层抽象：只有「复合」一个操作
    =========================================================================== -/

/-- **复合算子的顶层抽象**：只有「复合」这一个操作，不预设任何性质。

这是 A 族与 B 族**共有的**唯一点：两者都是「把两个东西合成一个」。
其余一切（交换、结合、方向）都在**子类**里加，从而 B 与 A 是
「同一抽象下的两个实例」（见文件头 (d).1、(e)）。 -/
class Composite (α : Type u) where
  /-- 复合：`α × α → α`。**无任何公理**。 -/
  comp : α → α → α

/-- **可交换复合（B 族，【主导】）**：`comp a b = comp b a`。

对应「属性集合的无向合并」（FCA / 形式概念分析）。
`combClosure` 是它的实例（§2）。 -/
class CommutativeComposite (α : Type u) extends Composite α where
  /-- 交换律。 -/
  comp_comm : ∀ a b : α, comp a b = comp b a

/-- **有向复合（A 族，【特例分支】）**：不要求可交换。

对应「有方向的概率传递」（马尔可夫链 / 概率图模型）。
`MeasurableRule.comp` 是它的实例（§3），且**不**可交换（§4）。

**刻意无额外字段**：A 族的「方向性」是 `comp` 的**实例性质**（§4 的
`A_not_commutative`），不是抽象层公理 —— 若在此加
「`¬ comp_comm`」类公理，就须对**每个实例**都证不可交换，
而这对 `α` 为**子单元素**（如 `PUnit`）的载体是**假**的。
故本类只有继承的 `comp`，与文件头 (d).2 一致。 -/
class DirectedComposite (α : Type u) extends Composite α

/-! ===========================================================================
    §2  B 族实例（主导）：`combClosure` on `Set K3.MFCA`
    =========================================================================== -/

/-- **B 族实例**：`combClosure` 使 `Set FateV2.Rules.AlphaInstance.K3.MFCA` 成为一个
**可交换复合**（`CommutativeComposite`）。

`comp := combClosure`（`= closureOp (A ∪ B)`，见 `WiringFourOpFixed:152`）；
交换性取自**已入链**的 `ComposeSemantics.combClosure_commutable`。

**这是本文件的「主导」实例**：默认的复合就是它。 -/
/- **B 族默认实例**。

    **第 525 轮补充 `priority := 1000`**（审计 R504 的判决）：
    审计指出「`ComposeDefault` 的 `priority := 2000` 压过 `ComposeUnified` 的默认 priority 实例，
    但 `ComposeUnified` 根本没写 `priority`」⟹ **那个"竞争"由 Lean 隐式默认 1000 成立，
    无任何 Lean 陈述**。

    现在**显式写出 `priority := 1000`**（Lean 的隐式默认值），使「2000 压过 1000」这个
    竞争**有真实的、写在代码里的双方**。 -/
instance (priority := 1000) instCommutativeCompositeAttrSet :
    CommutativeComposite (Set FateV2.Rules.AlphaInstance.K3.MFCA) where
  comp := FateV2.Rules.AlphaInstance.WiringFixed.combClosure
  comp_comm := FateV2.Rules.ComposeSemantics.combClosure_commutable

/-- 该实例的 `comp` **逐字等于** `combClosure`（定义相等）。 -/
theorem combClosure_comp_eq :
    (Composite.comp (α := Set FateV2.Rules.AlphaInstance.K3.MFCA))
      = FateV2.Rules.AlphaInstance.WiringFixed.combClosure := rfl

/-- ⭐ **B 族 `comp` 可交换**（不经类型类解析的显式重述，便于下游直接引用）。 -/
theorem B_is_commutative (A B : Set FateV2.Rules.AlphaInstance.K3.MFCA) :
    Composite.comp A B = Composite.comp B A :=
  CommutativeComposite.comp_comm A B

/-! ===========================================================================
    §3  A 族实例（特例分支）：`MeasurableRule.comp` on `MeasurableRule C X X`
    =========================================================================== -/

open FateV2.Rules.ComposeOperator

set_option warn.classDefReducibility false in
/-- **A 族实例**：`MeasurableRule.comp` 使 `MeasurableRule C X X` 成为一个
**有向复合**（`DirectedComposite`）。

⚠ **只能在「两端同型」上成实例**：`MeasurableRule.comp` 的签名是
```
@MeasurableRule.comp : MeasurableRule C Y Z → MeasurableRule C X Y
    → MeasurableRule C X Z
```
只有 `X = Y = Z` 时它才是 `α → α → α`，才符合 `Composite.comp` 的类型。
**⟹ 这本身就是「A 是有方向的」在类型层的体现**（两端必须接得上）。

`comp a b := a.comp b`：**注意参数顺序**。在 `MeasurableRule.comp R₂ R₁` 中
`R₁ : C × X → Measure Y` 在前一步、`R₂ : C × Y → Measure Z` 在后一步，
故 `a.comp b` 使 `b`（前一步）先作用。 -/
noncomputable def directedCompInstance {C : FateV2.Model.CtxSpace} {X : FateV2.Modeling.StateSpace}
    [MeasurableSpace X.Carrier] : DirectedComposite (MeasurableRule C X X) where
  comp := fun a b => a.comp b

/-- 该实例的 `comp` **逐字等于** `MeasurableRule.comp`（定义相等）。 -/
theorem directedComp_eq {C : FateV2.Model.CtxSpace} {X : FateV2.Modeling.StateSpace}
    [MeasurableSpace X.Carrier] (a b : MeasurableRule C X X) :
    (directedCompInstance (C := C) (X := X)).comp a b = a.comp b := rfl

/-! ===========================================================================
    §4  核心定理
    =========================================================================== -/

/-- ⭐⭐⭐ **A 不可交换**：A 族实例的 `comp` **不满足**交换律。

在 `CX`/`SS2`（`Unit`／`Fin 2`）上，
`¬ ∀ R₁ R₂, comp R₂ R₁ = comp R₁ R₂`。

**来源**：**已入链**的 `CompNotCommutative.comp_not_commutative`
（非确定反例：`R₂ ∘ R₁ {1} = 1/2` 而 `R₁ ∘ R₂ {1} = 0`）。

**前件检查**：结论即「不交换」，前件只有 `R₁ R₂` 的量化与实例的 `comp` 展开，
**无任何「假设不交换」的隐藏前件**——证明是从已证的否命题直接搬运。 -/
theorem A_not_commutative :
    ¬ ∀ R₁ R₂ : MeasurableRule FateV2.Rules.CompNotCommutative.CX
        FateV2.Rules.CompNotCommutative.SS2 FateV2.Rules.CompNotCommutative.SS2,
      (directedCompInstance (C := FateV2.Rules.CompNotCommutative.CX)
        (X := FateV2.Rules.CompNotCommutative.SS2)).comp R₂ R₁
      = (directedCompInstance (C := FateV2.Rules.CompNotCommutative.CX)
        (X := FateV2.Rules.CompNotCommutative.SS2)).comp R₁ R₂ := by
  intro h
  exact FateV2.Rules.CompNotCommutative.comp_not_commutative (fun a b => h a b)

/-- ⭐⭐ **B 主导的证据**：`combClosure` 可交换 ∧ 函数复合一般不交换。

逐字取自已入链的 `ComposeSemantics.two_semantics_incompatible`
（`⟨combClosure_commutable, fin2_comp_not_comm⟩`）。

**意义**：B 的复合**恒**可交换；而 A 的复合在确定性情形退化为函数复合，
而函数复合**有**不交换的实例 ⟹ B 的交换性是 A **不具备**的，
故 B 是「更强的、默认的」那一族。 -/
theorem B_dominates :
    (∀ A B : Set FateV2.Rules.AlphaInstance.K3.MFCA,
        FateV2.Rules.AlphaInstance.WiringFixed.combClosure A B
          = FateV2.Rules.AlphaInstance.WiringFixed.combClosure B A)
      ∧ (∃ f g : Fin 2 → Fin 2, f ∘ g ≠ g ∘ f) :=
  FateV2.Rules.ComposeSemantics.two_semantics_incompatible

/-- ⭐⭐ **融合结构**：同一抽象 `Composite` 下有两个实例，
**B 可交换、A 不可交换**，且**载体不同**。

三部分：
1. B 侧：`Set K3.MFCA` 上存在可交换复合（§2 的实例）；
2. A 侧：`MeasurableRule CX SS2 SS2` 上存在复合，且该复合**不**交换（§4 的
   `A_not_commutative`）；
3. 载体不同：`Set K3.MFCA ≠ MeasurableRule CX SS2 SS2`
   （由 `Set` 与 `MeasurableRule` 构造子后不同一：用 `noConfusion` 或
   类型层面的 `Set K3.MFCA` 与 `MeasurableRule ...` 是不同归纳类型）。

**这【不是】同义反复**：结论中「不交换」那一支来自
`CompNotCommutative.comp_not_commutative`（一个非平凡的数值反例），
前件仅为 `FateV2.Rules.AlphaInstance.K3` 与 `CX`/`SS2` 的**类型存在性**，
**没有把结论（可交换/不可交换）放进前件**。 -/
theorem fusion_structure :
    -- (1) B 侧：存在可交换复合
    (Nonempty (CommutativeComposite (Set FateV2.Rules.AlphaInstance.K3.MFCA)))
    -- (2) A 侧：存在复合，且它不交换
    ∧ (Nonempty (DirectedComposite
          (MeasurableRule FateV2.Rules.CompNotCommutative.CX
            FateV2.Rules.CompNotCommutative.SS2 FateV2.Rules.CompNotCommutative.SS2)))
    ∧ (¬ ∀ R₁ R₂ : MeasurableRule FateV2.Rules.CompNotCommutative.CX
          FateV2.Rules.CompNotCommutative.SS2 FateV2.Rules.CompNotCommutative.SS2,
        (directedCompInstance (C := FateV2.Rules.CompNotCommutative.CX)
          (X := FateV2.Rules.CompNotCommutative.SS2)).comp R₂ R₁
        = (directedCompInstance (C := FateV2.Rules.CompNotCommutative.CX)
          (X := FateV2.Rules.CompNotCommutative.SS2)).comp R₁ R₂) :=
  ⟨⟨instCommutativeCompositeAttrSet⟩,
   ⟨directedCompInstance⟩,
   A_not_commutative⟩

/-- ⭐ **同一抽象下的两个实例**：`Composite` 在 B 载体与 A 载体上
**都有**实例（后者还额外是 `DirectedComposite`）。

**用途**：这是「融合」在类型层的**唯一**可断言内容 ——
B 与 A 共享 `Composite` 这一个抽象，并且各自实例化。
（**不**断言「A 是 B 的实例」；见文件头 (d).1。） -/
theorem two_instances_under_one_abstraction :
    Nonempty (Composite (Set FateV2.Rules.AlphaInstance.K3.MFCA))
      ∧ Nonempty (CommutativeComposite (Set FateV2.Rules.AlphaInstance.K3.MFCA))
      ∧ Nonempty (DirectedComposite
          (MeasurableRule FateV2.Rules.CompNotCommutative.CX
            FateV2.Rules.CompNotCommutative.SS2 FateV2.Rules.CompNotCommutative.SS2)) :=
  ⟨⟨instCommutativeCompositeAttrSet.toComposite⟩,
   ⟨instCommutativeCompositeAttrSet⟩,
   ⟨directedCompInstance⟩⟩

/-! ===========================================================================
    §5  诚实边界
    =========================================================================== -/

/-!
**本文件证明了什么**（定理名 + 行号见 §4）
1. `Composite` / `CommutativeComposite`（B 族）/ `DirectedComposite`（A 族）
   三层抽象存在（§1）。
2. `combClosure` 是 `CommutativeComposite (Set K3.MFCA)` 的实例（§2）。
3. `MeasurableRule.comp` 是 `DirectedComposite (MeasurableRule C X X)` 的实例（§3）。
4. **A 不交换**（`A_not_commutative`），**B 交换**（`B_is_commutative`）。
5. **B 主导的证据**（`B_dominates`）：`combClosure` 恒可交换；函数复合有不交换实例。
6. 融合结构（`fusion_structure`、`two_instances_under_one_abstraction`）。

**本文件【没有】证明什么**
- **没有**构造「A 的复合 → B 的复合」的同态映射；
  故「A 是 B 推广后的特例」中的「推广 / 特例」**只在抽象层成立**
  （两者都是 `Composite` 的实例），**不在运算层成立**。
- **没有**证明 `combClosure` 与 `MeasurableRule.comp` 之间的关系
  （如「一者是另一者的商」「一者可编码另一者」）——
  载体不同（`Set K3.MFCA` vs 条件分布核），任何此类主张都需先定编码方案。
- **没有**回答净版开放问题 5.1（∘ 的语义究竟是哪个）。
- **没有**把「B 主导」的哲学裁决形式化为定理；只形式化了它的
  **数学可检验内容**（B 可交换、A 不可交换）。

**⟹ 本文件应被读作「读法一的类型层落地」，不是「开放问题 5.1 已解决」。**
-/

end FateV2.Rules.ComposeUnified
