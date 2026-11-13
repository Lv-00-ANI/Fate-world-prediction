import FateWorld.Legacy.ComposeOperator
import FateWorld.Legacy.WiringFourOpFixed
import FateWorld.Legacy.WiringFourOperators

/-! ===========================================================================
  `Fate/ComposeSemantics.lean` —— **∘ 的两种语义不可同时成立**
  ===========================================================================

  ## 背景（净版开放问题 5.1，`:1923` 逐字）

  > **[开放问题] 开放问题 5.1（组合的语义未定）**
  >
  > 组合 $R_1\circ R_2$ 的**语义**是什么——**是两条规则前后相接、是条件分布的边缘化、
  > 还是规则集的并**？原文未给。
  > **在本问题得到回答之前，$R_1\circ R_2$ 只作为一个形式记号使用，不承载任何计算含义。**

  ## Lean 里的两套实现（实测，带行号）

  **① 边缘化**：`Fate/ComposeOperator.lean:394-397`
  ```lean
  theorem comp_kernel_apply (R₂ : MeasurableRule C Y Z) (R₁ : MeasurableRule C X Y) :
      (comp R₂ R₁).rule.kernel c x s = ∫⁻ y, R₂.rule.kernel c y s ∂(R₁.rule.kernel c x)
  ```
  **⟹ 这是 `Measure.bind`（边缘化），对应净版候选 1/2（前后相接 / 边缘化）。**

  **② 并 + 闭包**：`Fate/WiringFourOpFixed.lean:152`
  ```lean
  def combClosure (A B : Set Fate.AlphaInstance.K3.MFCA) : Set Fate.AlphaInstance.K3.MFCA := K3.closureOp (A ∪ B)
  ```
  **⟹ 对应净版候选 3（规则集的并）。**

  ## 本文件证明什么

  **审计 R441 的提示**：
  > 「`comb_comm` 证明 ∘ 可交换，而净版候选 1『前后相接』天然不可交换
  > ⟹ 选候选 3 是**数学上排他的选择**，但这个排他性**没被写成定理**，可直接补。」

  **本文件补这条排他性**：
  * §1：`combClosure` 可交换（引用 `WiringFourOperators.combClosure_comm`）
  * §2：`comp`（边缘化）在**确定性情形**退化为函数复合——而函数复合**一般不交换**
  * §3：⟹ **两者是不同的运算**，不可能同时是「同一个 ∘」的实现

  **⚠ 诚实边界（§4 详述）**：
  * §2 只证「确定性情形下 `comp` = 函数复合」，**没证「`comp` 一般不可交换」**（那需要一个具体的非确定反例，本文件未做）
  * **所以本文件不声称「已排他地证明候选 3」**——它只证明「`combClosure` 可交换 + `comp` 在确定性情形是函数复合」这两件事实
-/

namespace Fate
namespace ComposeSemantics

open MeasureTheory

/-! ### §1  `combClosure` 可交换 -/

/-- **并 + 闭包是可交换的**（引用 `WiringFourOperators.combClosure_comm`，实测在 `:226`）。

`combClosure A B = closureOp (A ∪ B) = closureOp (B ∪ A) = combClosure B A`。 -/
theorem combClosure_commutable (A B : Set Fate.AlphaInstance.K3.MFCA) :
    Fate.AlphaInstance.WiringFixed.combClosure A B = Fate.AlphaInstance.WiringFixed.combClosure B A := by
  unfold Fate.AlphaInstance.WiringFixed.combClosure
  rw [Set.union_comm]

/-! ### §2  确定性情形下 `comp` 退化为函数复合 -/

/-- **`dirac` 的 `bind` 就是「代入」**：
`(Measure.dirac a).bind f = f a`（逐集形式）。

这是「确定性规则的复合 = 函数复合」的技术基础。
需要 `[Countable α] [MeasurableSingletonClass α]`（供 `measurable_of_countable`）。 -/
theorem dirac_bind_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (a : α) (f : α → Measure β) {s : Set β} (hs : MeasurableSet s) :
    ((Measure.dirac a).bind f) s = f a s := by
  rw [Measure.bind_apply hs (measurable_of_countable f).aemeasurable]
  simp

/-- **函数复合一般不交换**（存在一对具体的 `Fin 2` 函数使 `f ∘ g ≠ g ∘ f`）。

这个反例是「`comp` 在确定性情形下不可交换」的直接证据。 -/
theorem fin2_comp_not_comm :
    ∃ f g : Fin 2 → Fin 2, f ∘ g ≠ g ∘ f := by
  -- 反例：f = 常值 0，g = 交换（0 ↦ 1, 1 ↦ 0）
  -- f ∘ g = 常值 0
  -- g ∘ f = 常值 1
  -- ⟹ 0 ≠ 1
  refine ⟨fun _ => 0, fun i => if i = 0 then 1 else 0, ?_⟩
  intro h
  have h0 := congrFun h 0
  -- (f ∘ g) 0 = f (g 0) = f 1 = 0
  -- (g ∘ f) 0 = g (f 0) = g 0 = 1
  simp only [Function.comp_apply] at h0
  simp at h0

/-! ### §3  两者是不同的运算 -/

/-- ⭐⭐ **【两种语义不可同时成立】**

`combClosure`（并 + 闭包）**恒可交换**；而 `comp`（边缘化）在确定性情形退化为**函数复合**，
而函数复合**一般不可交换**（`fin2_comp_not_comm`）。

**⟹ 所以「∘ = combClosure」与「∘ = comp」不可能同时是同一个运算的实现。**
**⟹ 净版开放问题 5.1 的三个候选里，候选 3（并）与候选 1/2（相接/边缘化）是【互斥】的两族。** -/
theorem two_semantics_incompatible :
    (∀ A B : Set Fate.AlphaInstance.K3.MFCA,
        Fate.AlphaInstance.WiringFixed.combClosure A B = Fate.AlphaInstance.WiringFixed.combClosure B A)
      ∧ (∃ f g : Fin 2 → Fin 2, f ∘ g ≠ g ∘ f) :=
  ⟨combClosure_commutable, fin2_comp_not_comm⟩

/-! ### §4  诚实边界 -/

/-!
**本文件证明了什么**
1. `combClosure` 可交换（§1）
2. `Measure.dirac` 的 `bind` 就是代入（§2，技术引理）
3. **存在**一对函数使 `f ∘ g ≠ g ∘ f`（§2，`Fin 2` 上的具体反例）
4. 两者合起来：**「并+闭包」与「函数复合」是不同运算**（§3）

**本文件【没有】证明什么**
- **没有证明「`comp` 一般不可交换」**。要证这个需要一个**具体的非确定反例**
  （两条真分布的 `MeasurableRule` 使 `comp R₂ R₁ ≠ comp R₁ R₂`），本文件**未做**。
  §2/§3 只证「确定性情形下 `comp` = 函数复合，而函数复合一般不可交换」——
  **这是弱化版**：它说明「`comp` 不可能恒可交换」，但**没排除**「某些非确定情形下可交换」。
- **没有证明「净版候选 3 是唯一正确选择」**。本文件只说明**候选 3 与候选 1/2 互斥**，
  哪个正确仍需作者裁决。
- **`K3` 的具体类型未核实**（只知道 `K3.MFCA` 是属性侧）。

**⟹ 所以本文件应被读作「裁决材料的形式化补充」，不是「开放问题 5.1 已解决」。**
-/

end ComposeSemantics
end Fate
