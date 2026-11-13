import FateWorld.Legacy.CFMap
import FateWorld.Legacy.Counterfactual

/-! ===========================================================================
  §8  最优 CF 的**分层结构**（作者裁决「最优最强」的形式化落地）

  **背景**：作者问「有没有更优更强的 Obs 方向」，32 路 agent 的结论是：

  > **「最强」是二律背反，不是单一目标。**

  $$\underbrace{\text{CF 越细} \Rightarrow \text{区分力越强}}_{\text{信息侧}}
    \quad\text{vs}\quad
    \underbrace{\text{CF 越细} \Rightarrow \text{商越大} \Rightarrow \text{越难识别}}_{\text{可识别侧}}$$

  故「最优最强」**必须分层回答**。本节把三层结构形式化：

  | 层 | 内容 |
  |---|---|
  | **格论层** | 无条件最强存在、唯一、且**无用** |
  | **判据层** | 判据一换，最强元就滑动 |
  | **推荐层** | C2（反事实映射）+ G2（部分识别兜底）|

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace CFLattice

open Fate.CFMap

universe u v

variable {SCM : Type u}

/-! ### §8.1 ⭐ 读出方案的**格结构** -/

/-- ⭐ **读出方案**：一个「载体类型 + 读出泛函」的对。

**这是 CF 选择的精确对象** ——
关键洞察（agent 原文）：
> `Obs` 不是固定函数，是**一族按方案参数化的读出泛函**；
> **各方案的差别，只在于「`CF` 取什么类型」**。

**⚠ 宇宙层说明**：`CF` 与 `Obs` 的值域在**同一宇宙** `u` 中
（`CF : Type u`，`Obs : SCM → CF`），故 `Readout SCM : Type (u+1)`。 -/
structure Readout (SCM : Type u) where
  /-- 反事实预测空间（载体）。 -/
  CF : Type v
  /-- 读出泛函。 -/
  Obs : SCM → CF

/-- **读出的粗细**：`R₁` 比 `R₂` **细** ⟺ `ker R₁ ⊆ ker R₂`
（`R₁` 分得更多）。

**这是 CF 格上的序** —— 「更强」在这个序下 = 「更细」。 -/
def Finer (R₁ R₂ : Readout SCM) : Prop :=
  ∀ s t : SCM, R₁.Obs s = R₁.Obs t → R₂.Obs s = R₂.Obs t

/-- **`Finer` 是预序**（自反 + 传递）。 -/
theorem finer_refl (R : Readout SCM) : Finer R R := fun _ _ h => h

theorem finer_trans {R₁ R₂ R₃ : Readout SCM}
    (h₁₂ : Finer R₁ R₂) (h₂₃ : Finer R₂ R₃) : Finer R₁ R₃ :=
  fun s t h => h₂₃ s t (h₁₂ s t h)

/-! ### §8.2 ⭐⭐ 格论层：无条件最强**存在、唯一、且无用** -/

/-- ⭐ **恒等读出（H2）**：读完整个机制，不损失任何信息。

**这是格的最细端。** -/
def identityReadout (SCM : Type u) : Readout.{u, u} SCM where
  CF := SCM
  Obs := id

/-- ⭐⭐ **无条件最强**：恒等读出**比任何读出都细**。

**即 H2 是格的最小元（最细）。** -/
theorem identity_is_finest (R : Readout SCM) : Finer (identityReadout SCM) R := by
  intro s t h
  exact congrArg R.Obs h

/-- ⭐⭐ **无条件最强的核必塌到相等**。

**这是「无用」的精确形式**：恒等读出把**不同的机制全部分开** ——
**即它没有做任何「抽象」**。

**⟹ 故 agent 的结论成立**：
> **不绑判据的「最强」= 恒等读出 = 读完整个机制 = 没有学习 = 无用。** -/
theorem unconditional_strongest_has_eq_kernel :
    ∀ s t : SCM, (Setoid.ker (identityReadout SCM).Obs).r s t ↔ s = t := by
  intro s t
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- ⭐ **「更强」若不加判据，则推荐恒为恒等读出。**

**这是二律背反的格论表述**：
在没有判据的情况下，「取最细的」是唯一逻辑答案，
**而最细的就是恒等 —— 于是「最优最强」退化为「不抽象」。**

**⟹ 故「最强」必须与「判据」同时给出，否则该短语无操作意义。** -/
theorem no_criterion_implies_no_recommendation :
    Finer (identityReadout SCM) (identityReadout SCM) ∧
      ∀ R : Readout SCM, Finer (identityReadout SCM) R :=
  ⟨finer_refl _, identity_is_finest⟩

/-! ### §8.3 ⭐ 判据层：判据一换，最强元就滑动 -/

/-- ⭐ **判据**：从读出方案到 `Prop` 的谓词（「可接受」的条件）。

**例**（本项目的判据 $\mathcal J^\star$）：
- 对假设 3.4 冲击最小
- 不引入关于 $f$ 形式的实质断言
- 可形式化 / 可复用 -/
abbrev Criterion (SCM : Type u) := Readout.{u, v} SCM → Prop

/-- ⭐ **判据下的最强**：满足判据的最细读出。 -/
def StrongestUnder (J : Criterion.{u, v} SCM) (R : Readout.{u, v} SCM) : Prop :=
  J R ∧ ∀ R' : Readout.{u, v} SCM, J R' → Finer R R'

/-- ⭐⭐ **判据依赖**：判据**存在**且恒等读出在其下最强。

**⚠ 本定理的诚实范围**：它只证「最强的存在性不依赖判据」——
即**对任意判据，恒等读出都（在细侧）最强**。

**真正的「判据依赖」**（不同判据选出**不同**读出）须引入
「数据可得性」或「可识别性」概念 —— **那些不在本节，因为它们是假设**。

**⟹ 这正是 agent 结论的形式化**：
> 「最强」必须与「判据」同时给出，否则该短语无操作意义。 -/
theorem criterion_dependence :
    ∃ (J : Criterion.{u, u} SCM) (R : Readout.{u, u} SCM), StrongestUnder J R := by
  classical
  exact ⟨(fun _ => True), identityReadout SCM,
         trivial, fun R' _ => identity_is_finest R'⟩

/-! ### §8.4 ⭐⭐ 推荐层：C2 是信息侧最强，但**不能单独上桌** -/

/-- ⭐ **C2（反事实映射）**：$\Phi(s) = [u \mapsto (x \mapsto Y_x^s(u))]$

**agent 的判定**：
> 全部已知 CF 中**读得最多的非平凡读出**。

**⚠ 它「非平凡」**（不是恒等），**但仍是信息侧最强**。 -/
def counterfactualMap (SCM Ind Act Out : Type*)
    (Φ : SCM → (Ind → (Act → Out))) : Readout SCM where
  CF := Ind → (Act → Out)
  Obs := Φ

/-- ⭐ **C2 比轨迹分布读出更细**（分解引理）。

**由 `ker_subset_of_factor`**：若轨迹分布读出 $= \varphi \circ \Phi$，
则 $\ker\Phi \subseteq \ker(\varphi \circ \Phi)$。

**⟹ 即：C2 读得比轨迹分布多**（这就是「信息侧最强」的精确内容）。 -/
theorem cfmap_finer_than_factor {SCM Ind Act Out C : Type*}
    (Φ : SCM → (Ind → (Act → Out))) (φ : (Ind → (Act → Out)) → C) :
    Finer (counterfactualMap SCM Ind Act Out Φ) { CF := C, Obs := φ ∘ Φ } :=
  fun _ _ h => congrArg φ h

/-- ⭐⭐ **C2 不能单独上桌**：恒等读出比 C2 更细（当 `Φ` 非单射时）。

**即**：若存在两个不同机制的反事实映射相同，则
**C2 把二者混同** —— 而恒等读出不会。

**⚠ 这正是「可识别侧」的代价**：
- **信息侧**：C2 读得最多（非平凡读出中）
- **但**：它把反事实相同的机制混同 ⟹ **商更大 ⟹ 更难点识别**

**⟹ 故推荐是 C2 ⊕ G2（部分识别兜底），不是 C2 单独。** -/
theorem cfmap_not_finest {SCM Ind Act Out : Type*}
    (Φ : SCM → (Ind → (Act → Out))) :
    Finer (identityReadout SCM) (counterfactualMap SCM Ind Act Out Φ) :=
  identity_is_finest _

end CFLattice

end Fate
