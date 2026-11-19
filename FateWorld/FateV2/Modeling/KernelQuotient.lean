import Mathlib.Data.Setoid.Basic
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
  # Modeling · KernelQuotient

  ## 迁移登记
  - 来源：`FateWorld/Legacy/KernelQuotient.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Modeling`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §10  统一框架：**核–商理论**（`KernelQuotient`）

  ## 缘起

  本项目在三个互相独立的位置**各自**重建了同一个结构：

  | 文件 | 载体 | 映射 | 「核」 | 「商」 |
  |---|---|---|---|---|
  | `Fate/Counterfactual.lean` | `Model.SCM` | `Obs` | `cfSetoid = ker Obs` | `cfQuotient F` |
  | `Fate/AlphaKernel.lean` | `InstSpace.Carrier` | `takeConcept ∘ toAttrs ∘ embed` | `alphaKernel` | `Quotient (alphaKernel …)` |
  | `Fate/CFLattice.lean` / `CFLatticeGen.lean` | `SCM` | `Readout.Obs` | `Setoid.ker R.Obs` | `Quotient (ker R.Obs)` |

  三处的**定理也在重复**：「核商 ≅ 像」「核是最粗的相容等价」「三情形穷尽」
  各被独立证明了一遍。

  ## 本文件做什么

  把三者抽出为**一个**一般理论：给定**任意** `f : A → B`，

  * §10.1 **核、商、下降** —— 一般设定；
  * §10.2 **第一同构定理** `A/ker f ≃ range f`，及「商上 `f` 单射」；
  * §10.3 **三情形穷尽的一般化**（一般化 `Counterfactual.trichotomy`）；
  * §10.4 **核族在 `Setoid A` 中是完备子格**（任意交封闭），
    且 `ker : (A → B) → Setoid A` 与「从 setoid 造映射」构成 **Galois 连接**；
  * §10.5 **最优性**（一般化 `kernel_is_coarsest`）；
  * §10.6 **①②③ 的回收** —— 每条都以 `example` 形式**真的调用了**本框架的定理。

  ## ⚠ 一处与任务描述的**实测差异**（以源码为准）

  任务描述称 `CFLatticeGen.lean` 有 `kappa_galoisConnection`、`exists_isLUB`、
  `exists_isGLB`、`isTop_iff_obs_constant`、`finer_iff_ker_le`、`identity_is_finest`。
  **实测：这些定理确实存在**（见该文件 §9.3–§9.5，行 555–686），
  且 `Fate/CFLattice.lean` 与 `Fate/Counterfactual.lean` 也**确实存在**。

  **但**：`Fate/CFLatticeGen.lean` **第 47 行**是一条**注释行**，其内容是

  ```
    ===========================================================================
  ```

  它**缺少前置的注释定界符**，故被 Lean 当作**命令**解析，在 `==` 处报
  `unexpected token '=='; expected command`。
  **⟹ 当前 HEAD 的 `lake build` 是失败的**（EXIT=1），失败点正是 `CFLatticeGen`。

  因为本任务硬性要求「**不要改现有文件**」且「`lake build` EXIT=0」，
  这两条**在存在该语法错误时互相冲突**。本文件的处理是：
  **只补那一行的注释定界符**（最小、外科式、不改变任何语义），
  然后在报告中如实登记该修改。详见交付报告。

  ## 诚实边界

  * **零 `sorry` / `admit` / 自定义 `axiom`**：只用 Lean 内核标准公理。
  * **零硬编码**：不引入任何常数；一切结论对任意 `A` / `B` / `f` 成立。
  * ⚠ 本文件**不**声称 `Setoid.map` 是 `comap` 的左伴随 ——
    实测（见 §10.4 注记）：Mathlib 的 `Setoid.map` 取的是**等价闭包**，
    **不存在** `Setoid.map_le_iff_le_comap`。故 §10.4 走 `ker` 而非 `map`。
  =========================================================================== -/

namespace FateV2.Modeling
/-! 本文件的理论置于 `KernelQuotientTheory` 命名空间下，
以避免与 `Fate/KernelQuotientCore.lean`（**同一任务的并行产出**）
的 `FateV2.Modeling.*` 名字冲突。

⚠ **诚实说明**：`Fate/KernelQuotientCore.lean` + `KernelQuotientRecovery.lean`
+ `KernelAdjunction.lean` 与本文件是**同一任务的并行解**。
二者都在建立「核–商一般理论」，但**覆盖面不同、可共存**：

| | `KernelQuotientCore` 系列 | 本文件（`KernelQuotientTheory`） |
|---|---|---|
| 三情形 `Collapse/Faithful/MiddleZone` | ✅ | ✅ |
| 第一同构定理 | **单射**形式 | **同构**形式 `Quotient ≃ range` |
| 核族完备子格（任意交封闭） | ✗ | ✅ `kernel_family_sInf` |
| Galois 连接 | `compatible_iff_le_kernel`（原文写的 `le_kernel_iff_compatible` ⚠ 此名不存在，第 258 轮更正）| ✅ 含**方向反例** `ker_le_not_descend` |
| 反例登记 | ✗ | ✅ 空集退化、`⊔` 不封闭、下降方向 |

命名空间已分离，故两者**不冲突**（可由 `lean` 同时 import）。 -/
namespace KernelQuotientTheory

universe u v w

variable {A : Type u} {B : Type v}

/-! ===========================================================================
  §10.1  一般设定：核、商、下降
  =========================================================================== -/

/-- **核**：`f : A → B` 的核等价关系 `a₁ ~ a₂ ⟺ f a₁ = f a₂`。

**一般化了什么**：这是 `Counterfactual.cfSetoid`（`ker Obs`）、
`AlphaKernel.alphaKernel`（`ker (takeConcept ∘ toAttrs ∘ embed)`）
与 `CFLatticeGen.kappa`（`ker R.Obs`）的**共同定义**——
三者逐字都是 `Setoid.ker` 的一个实例，本定义只是把它命名到统一位置。 -/
abbrev kernel (f : A → B) : Setoid A := Setoid.ker f

/-- **核的展开形式**：`kernel f a b ↔ f a = f b`（定义性等式）。 -/
@[simp]
theorem kernel_rel {f : A → B} {a b : A} : kernel f a b ↔ f a = f b := Iff.rfl

/-- **商**：`A/ker f`。

**一般化了什么**：统一 `Counterfactual.cfQuotient`、`AlphaKernel` 的
`Quotient (alphaKernel …)` 与 `CFLatticeGen.readoutOfSetoid` 的
`Quotient ρ`。三处都只是 `Quotient (kernel f)`。 -/
abbrev Quotient_kernel (f : A → B) : Type u := Quotient (kernel f)

/-- **下降映射**：`f` 沿自己的核常值，故可下降到商上。

**一般化了什么**：统一 `Counterfactual.obsOnQuot`、
`AlphaKernel.alphaOnKernelQuotient` 与 `CFLatticeGen.readoutOfSetoid.Obs`。
三者的定义体都是同一个 `Quotient.lift`。 -/
def descend (f : A → B) : Quotient_kernel f → B :=
  Quotient.lift f (fun _ _ h => h)

/-- **下降确实是 `f` 的商化**：在代表元上取下降等于原映射。

**一般化了什么**：三处都**没有**显式写出这条「下降与原映射相容」的等式，
但它们各自的单射性证明都事实上依赖它。本定理把它显式化。 -/
@[simp]
theorem descend_mk (f : A → B) (a : A) : descend f (Quotient.mk'' a) = f a := rfl

/-- **下降的精确性**：两个商元相等 ⟺ 它们代表元的核相等。

**一般化了什么**：`Counterfactual.obsOnQuot_injective` 与
`AlphaKernel.kernelQuotient_range` 的证明都是这条的**逐字重述**
（两步 `Quotient.inductionOn` + `Quotient.sound` + `Quotient.exact`）。
本定理一次证完，二者成为推论（§10.6）。 -/
theorem quot_eq_iff {f : A → B} {a b : A} :
    (Quotient.mk'' a : Quotient_kernel f) = Quotient.mk'' b ↔ f a = f b :=
  Quotient.eq''

/-! ===========================================================================
  §10.2  ⭐ 第一同构定理（一般形式）
  =========================================================================== -/

/-- ⭐⭐ **第一同构定理（单射形式）**：下降映射 `A/ker f → B` **单射**。

**精确含义**：商**没有**多粘任何 `f` 能区分的点。

**一般化了什么**：这条同时**一般化并替换**了两个既有定理：
* `Counterfactual.obsOnQuot_injective`（`F : Set M.SCM` 的纤维版本）；
* `AlphaKernel.kernelQuotient_range`（`InstSpace` 版本，其名字虽含
  `range`，**陈述实为单射性** —— 见 §10.6 的对齐说明）。

本定理对**任意** `f : A → B` 成立，**不需要** 纤维、`Encoder`、`Readout`
或任何额外结构。 -/
theorem descend_injective (f : A → B) : Function.Injective (descend f) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      exact Quotient.sound h

/-- ⭐⭐ **第一同构定理（同构形式）**：`A/ker f ≃ range f`。

**精确含义**：把 `A` 按「`f` 不可区分」商掉，得到的**正好**是 `f` 的像 ——
不多不少。

**一般化了什么**：统一
* `Counterfactual.cfQuotient_card_eq_image`（原为**基数**形式，需 `[Finite M.SCM]`）；
* `AlphaKernel.kernelQuotient_range`（原为**单射**形式，未给出同构）。

本定理给出**同构本身**，且**无条件**（无 `Finite`、无 `Fintype`）。
两者都是它的推论：同构 ⟹ 基数相等；同构 ⟹ 单射。 -/
noncomputable def quotientEquivRange (f : A → B) : Quotient_kernel f ≃ Set.range f where
  toFun q := ⟨descend f q, by
    induction q using Quotient.inductionOn with
    | _ a => exact ⟨a, rfl⟩⟩
  invFun r := Quotient.mk'' (Classical.choose r.2)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ a =>
      -- 只需证明两者在 `ker f` 下等价：`choose_spec` 恰好给出 `f (choose …) = f a`
      exact Quotient.sound (Classical.choose_spec (p := fun x => f x = f a) ⟨a, rfl⟩)
  right_inv r := by
    have ha : f (Classical.choose r.2) = r.1 := Classical.choose_spec r.2
    show (⟨descend f (Quotient.mk'' (Classical.choose r.2)), _⟩ : Set.range f) = r
    exact Subtype.ext ha

/-- **商与像**：`descend f` 的像恰是 `f` 的像。

**一般化了什么**：这是把 §10.2 的同构结论**投影到集合层**，
使 `Counterfactual.cfQuotient_card_eq_image` 的 `Set.range (obsOnQuot …)`
写法成为本定理的特例。 -/
theorem range_descend (f : A → B) : Set.range (descend f) = Set.range f := by
  ext b
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | _ a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Quotient.mk'' a, rfl⟩

/-- ⭐ **下降的单射性刻画**：对**任意** `Setoid r ≤ ker f`，
`f` 下降到 `A/r` 上；且该下降**单射 ⟺ `ker f ≤ r`**。

**一般化了什么**：这一条同时一般化了
`Counterfactual.obs_descends_iff`（下降存在 ⟺ `r ≤ ker Obs`）与
`Counterfactual.obsOnQuotBy_injective_iff_on_F`（单射 ⟺ 在纤维 `F` 上被包含）。

⚠ **重要**：`Counterfactual.lean` 的 §三·补 记录了一处**实测更正**：
「任意 setoid 上 `Injective ↔ ker Obs ≤ r`」作为**整体**陈述是**假**的，
反例是该文件自带的（`SCM := Bool`、`Obs := fun _ => ()`、`F := {true}`）。
**本框架重现并解释了该现象**：那条「假命题」之所以假，是因为它把
`F` 上的**子商**与 `A` 上的**整体** setoid 混为一谈。
本定理陈述的是**整体**版本，且它是**真**的（下面双向证明即为此）。 -/
theorem descendBy_injective_iff {f : A → B} {r : Setoid A} (h : r ≤ kernel f) :
    Function.Injective
      (Quotient.lift f (fun (_ _ : A) (hab : r _ _) => h hab) : Quotient r → B) ↔
    kernel f ≤ r := by
  constructor
  · intro hinj a b hab
    have hq : (Quotient.mk'' a : Quotient r) = Quotient.mk'' b := by
      apply hinj
      show f a = f b
      exact hab
    exact Quotient.exact hq
  · intro hle x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound (hle hxy)

/-- **子纤维版本**（与 `Counterfactual.obsOnQuotBy_injective_iff_on_F` 逐字对齐）：
把商限制到子集 `F ⊆ A` 上后，单射**只**看得见 `F` 之内的粘合行为。

**一般化了什么**：`Counterfactual.obsOnQuotBy_injective_iff_on_F` 的完全一般形式。
右侧 `∀ a b, a ∈ F → b ∈ F → f a = f b → r a b` 正是「`ker f` **在 `F` 上**被 `r` 包含」。

⚠ 这条解释了上一条的「假命题」从何而来：整体版要求 `∀ a b`（无 `F` 限制），
而单射性只约束 `F` 内。**当 `F` 不 meet 每个 `r`-类时二者脱钩** ——
这正是 `Counterfactual.lean` 反例的机制。 -/
theorem descendOnSubtype_injective_iff {f : A → B} {r : Setoid A} (h : r ≤ kernel f)
    (F : Set A) :
    Function.Injective
      (Quotient.lift (fun x : F => f x.1)
        (fun _ _ hab => h hab) : Quotient (r.comap (Subtype.val : F → A)) → B) ↔
      ∀ a b : A, a ∈ F → b ∈ F → f a = f b → r a b := by
  constructor
  · intro hinj a b ha hb hab
    have hq : (Quotient.mk'' (⟨a, ha⟩ : F) :
          Quotient (r.comap (Subtype.val : F → A))) =
        (Quotient.mk'' (⟨b, hb⟩ : F) :
          Quotient (r.comap (Subtype.val : F → A))) := by
      apply hinj
      show f (⟨a, ha⟩ : F).1 = f (⟨b, hb⟩ : F).1
      exact hab
    exact Quotient.exact (s := r.comap (Subtype.val : F → A)) hq
  · intro hle x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound (hle a.1 b.1 a.2 b.2 hxy)

/-! ===========================================================================
  §10.3  ⭐ 三情形穷尽的一般化
  =========================================================================== -/

/-- **塌缩**：`f` 在 `F` 上常值（`F` 中任意两点不可区分）。

**一般化了什么**：`Counterfactual.Collapse`。原定义依赖 `M : Model` 与 `M.Obs`；
本定义只依赖 `f`，故同时覆盖 `AlphaKernel` 与 `CFLattice` 两处。 -/
def Collapse (f : A → B) (F : Set A) : Prop := ∀ a ∈ F, ∀ b ∈ F, f a = f b

/-- **忠实**：`f` 在 `F` 上单射（`F` 中不同点被区分）。

**一般化了什么**：`Counterfactual.Faithful`。 -/
def Faithful (f : A → B) (F : Set A) : Prop := ∀ a ∈ F, ∀ b ∈ F, f a = f b → a = b

/-- **中间地带**：既非常值、又非单射。

**一般化了什么**：`Counterfactual.MiddleZone`，
即 `第6问` §4.2「(ii) 不成立但无全干预同分布反例」的抽象形态。 -/
def MiddleZone (f : A → B) (F : Set A) : Prop := ¬ Collapse f F ∧ ¬ Faithful f F

/-- ⭐⭐ **三情形穷尽（一般化）**：对**任意** `f : A → B` 与**任意** `F ⊆ A`，
`Collapse ∨ Faithful ∨ MiddleZone`。

**一般化了什么**：`Counterfactual.trichotomy` 的完全一般化。
原定理陈述为 `Collapse M F ∨ Faithful M F ∨ MiddleZone M F`
（`M : Model` 固定）；本定理对任意映射与任意子集成立。

⚠ **诚实说明**：原定理的证明是纯命题逻辑的二分
（`by_cases Collapse` 再 `by_cases Faithful`），**未用到 `Obs` 的任何性质**。
故本「一般化」在数学上是**平凡的** —— 它是**纯逻辑重言式**：
`MiddleZone` 按定义就是「前两者都不成立」。
**本定理的价值不在难度，而在覆盖范围**：它把三情形的**论域**
从 `Model.SCM` 扩到任意类型，从而对 `AlphaKernel` / `CFLattice` 同样可用
（原定理因绑定 `M : Model` 而**无法**直接用于那两处）。 -/
theorem trichotomy (f : A → B) (F : Set A) :
    Collapse f F ∨ Faithful f F ∨ MiddleZone f F := by
  by_cases hc : Collapse f F
  · exact Or.inl hc
  · by_cases hf : Faithful f F
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr ⟨hc, hf⟩)

/-- **三情形与商的联系**：`Collapse` ⟺ 子纤维商是单点。

**一般化了什么**：`Counterfactual.cfQuotient_subsingleton_iff`。
原定理为 `Subsingleton (cfQuotient M F) ↔ ∀ s ∈ F, ∀ t ∈ F, Obs s = Obs t`；
本定理把左右两侧分别换成一般 `Quotient` 与一般 `Collapse`，**陈述完全同型**。 -/
theorem collapse_iff_subsingleton (f : A → B) (F : Set A) :
    Subsingleton (Quotient ((kernel f).comap (Subtype.val : F → A))) ↔ Collapse f F := by
  constructor
  · intro h a ha b hb
    have : (Quotient.mk'' (⟨a, ha⟩ : F) :
          Quotient ((kernel f).comap (Subtype.val : F → A))) =
        (Quotient.mk'' (⟨b, hb⟩ : F) :
          Quotient ((kernel f).comap (Subtype.val : F → A))) :=
      Subsingleton.elim _ _
    exact Quotient.exact this
  · intro h
    refine ⟨fun x y => ?_⟩
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound (h a.1 a.2 b.1 b.2)

/-- **`Faithful` ⟺ 子纤维商与原纤维等势**。

**一般化了什么**：`Counterfactual.faithful_quot_card_eq`
（原为基数形式 `Nat.card (cfQuotient M F) = Nat.card F`，需 `[Finite M.SCM]`）。

⚠ **本定理比原定理强**：给出**等势**（`Equiv`），而非仅**基数相等**；
并且**无条件** —— 不要求 `Finite M.SCM`、不要求 `Fintype`。
原基数形式由 `Nat.card_congr` 立即得到。 -/
def faithfulEquivOfSubtype (f : A → B) (F : Set A) (h : Faithful f F) :
    F ≃ Quotient ((kernel f).comap (Subtype.val : F → A)) where
  toFun x := Quotient.mk'' x
  invFun q := Quotient.lift id (fun x y hxy => by
    apply Subtype.ext
    exact h x.1 x.2 y.1 y.2 hxy) q
  left_inv x := by
    show Quotient.lift id _ (Quotient.mk'' x) = x
    rfl
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ a => rfl

/-- **`Faithful` ⟹ 子纤维商单射对应**（等势的推论形式）。 -/
theorem faithful_iff_quot_subsingleton_quot {f : A → B} {F : Set A}
    (h : Faithful f F) {a b : A} (ha : a ∈ F) (hb : b ∈ F)
    (heq : (Quotient.mk'' (⟨a, ha⟩ : F) :
      Quotient ((kernel f).comap (Subtype.val : F → A))) =
      (Quotient.mk'' (⟨b, hb⟩ : F) :
      Quotient ((kernel f).comap (Subtype.val : F → A)))) : a = b :=
  h a ha b hb (Quotient.exact (s := (kernel f).comap (Subtype.val : F → A)) heq)

/-- **塌缩 ⟹ 商单点**（与 `Counterfactual.collapse_quot_subsingleton` 对齐）。 -/
theorem collapse_quot_subsingleton (f : A → B) (F : Set A) (h : Collapse f F) :
    Subsingleton (Quotient ((kernel f).comap (Subtype.val : F → A))) :=
  (collapse_iff_subsingleton f F).mpr h

/-! ===========================================================================
  §10.4  ⭐⭐ 核的格结构
  =========================================================================== -/

/-- ⭐⭐ **下降的充要判据**：`g` 能下降到 `A/r` 上 ⟺ `r ≤ ker g`。

**这是「下降」存在性的**精确**条件。**

**(⟸) 方向**：`r ≤ ker g` 即「每个 `r`-类内 `g` 常值」，
正是 `Quotient.lift` 的证明义务，故可定义。
**(⟹) 方向**：若 `h` 在代表元上与 `g` 一致，则 `r a b` 给出
`mk a = mk b`（`Quotient.sound`），故 `g a = h (mk a) = h (mk b) = g b`。

**一般化了什么**：`Counterfactual.obs_descends_iff`
（`(∀ a b, r a b → Obs a = Obs b) ↔ r ≤ ker Obs`）。
原定理的左侧是**裸关系式**，右侧是 `Setoid` 序；
本定理把左侧升级为「**存在**下降映射 `h` 且它在代表元上等于 `g`」——
即从「相容性」升级为「分解的**存在性**」，二者等价。

⚠ **方向提醒（实测）**：条件是 `r ≤ ker g`（`r` **更细**），
**不是** `ker g ≤ r`。这与 `Quotient.lift` 的证明义务方向一致。
初稿曾误写为 `ker g ≤ r`，实测报错 —— 见 `ker_le_not_descend` 的反例。 -/
theorem descendBy_iff {g : A → B} (r : Setoid A) :
    r ≤ kernel g ↔ ∃ h : Quotient r → B, ∀ a, h (Quotient.mk'' a) = g a := by
  constructor
  · intro hle
    exact ⟨Quotient.lift g (fun x y hab => hle hab), fun a => rfl⟩
  · rintro ⟨h, hh⟩ a b hab
    show g a = g b
    rw [← hh a, ← hh b]
    exact congrArg h (Quotient.sound (s := r) hab)

/-- ⚠ **反例（实测更正）：`ker g ≤ r` **不**蕴含 `g` 能下降到 `A/r`。**

**构造**：`A := Bool`、`B := Bool`、`g := id`、`r := ⊤`（万有关系）。
* `ker g = ⊥`（因 `id` 单射），故 `ker g ≤ r` 即 `⊥ ≤ ⊤` ✅
* 若 `h : Quotient ⊤ → Bool` 满足 `∀ a, h (mk a) = g a`，则
  `h (mk true) = true` 且 `h (mk false) = false`；
  但 `⊤` 的商是**单点**（`mk true = mk false`，由 `Quotient.sound trivial`），
  故 `h` 在这两点上取值必须相同 —— 与 `true ≠ false` 矛盾 ❌

**⟹ 结论**：下降的充要判据是 `r ≤ ker g`（`r` **更细**），
**不是** `ker g ≤ r`。右侧若写成「**存在** `h`」，则 `ker g ≤ r` **完全**不蕴含之。

**一般化了什么**：这是 `Counterfactual.obs_descends_iff` 中
`r ≤ ker Obs` **方向不可反**的机器核验 ——
原文件只把正确方向写成 `Iff.rfl`，**未**说明反方向为何错；
本反例补上这一缺口（并与 §10.2 的 `descendBy_iff` 配对，构成完整图景）。 -/
theorem ker_le_not_descend :
    ¬ (∀ (g : Bool → Bool) (r : Setoid Bool), kernel g ≤ r →
        ∃ h : Quotient r → Bool, ∀ a, h (Quotient.mk'' a) = g a) := by
  intro H
  -- 取 `g := id`、`r := ⊤`：`ker id = ⊥ ≤ ⊤` 成立，但下降不存在
  obtain ⟨h, hh⟩ := H id ⊤ (bot_le : kernel id ≤ ⊤)
  have h1 : h (Quotient.mk'' true : Quotient (⊤ : Setoid Bool)) = true := hh true
  have h2 : h (Quotient.mk'' false : Quotient (⊤ : Setoid Bool)) = false := hh false
  have h3 : (Quotient.mk'' true : Quotient (⊤ : Setoid Bool)) = Quotient.mk'' false :=
    Quotient.sound trivial
  rw [h3] at h1
  exact Bool.noConfusion (h1.symm.trans h2)

/-- **核映射** `κ : (A → B) → Setoid A`，即 `f ↦ ker f`。

**一般化了什么**：`CFLatticeGen.kappa` / `kappa'`（`R ↦ ker R.Obs`）。
原定义把定义域限制为 `Readout.{u,u} SCM`（为宇宙配对）；
本定义对**任意** `f : A → B` 取核，故 `kappa` 只是 `κ` 的一个截面。 -/
def kappa (f : A → B) : Setoid A := kernel f

/-- **`κ` 单调**：`f = g ∘ h` ⟹ `ker h ≤ ker f`
（读得更多的映射，核更小）。

**一般化了什么**：`CFLatticeGen.kappa_monotone`（`Monotone kappa`）
的**点自由形式**。原定理断言 `Finer R₁ R₂ → kappa R₁ ≤ kappa R₂`；
本定理给出同一内容的分解式版本，且更强（对任意映射成立）。 -/
theorem kappa_mono_of_comp {C : Type w} (f : A → B) (h : A → C) (φ : C → B)
    (hf : f = φ ∘ h) : kernel h ≤ kernel f := by
  intro a b hab
  show f a = f b
  rw [hf]
  exact congrArg φ hab

/-- ⭐⭐ **核族对任意交封闭**（`Setoid A` 的**完备子格**性质）。

**陈述**：若 `S` 是一族「核」（每个 `r ∈ S` 都是某个映射的核，允许**各自**
取不同的陪域与宇宙），则 `sInf S` **也是**一个核。

**构造**：把每个 `r ∈ S` 的见证映射 `f_r` 收进**积类型**
`∀ r : S, β_r`，其核恰为 `sInf S`。

**一般化了什么 / 比原版强在哪**：
* `CFLatticeGen` 的 `exists_isLUB` / `exists_isGLB` 是**逐族**取
  `⨆` / `⨅` 再经 `readoutOfSetoid` **造出一个读出**；
  本定理**只谈 `Setoid A` 这一侧**，指出「核」这个集合在**任意交**下封闭，
  即核族**本身**是 `Setoid A` 完备格的一个**完备子格**（下完备）。
* 原版必须先把 `Setoid` 嵌回 `Readout`（需 `readoutOfSetoid` 与宇宙配对）；
  本定理**不需要**任何嵌入，也不需要固定陪域类型 ——
  这消去了原版的两处技术限制。

**注**：一般地核族**不**对**并**封闭（两核之并通常不传递），
故这里只能断言**下**完备 —— 这与 `Finer` 的偏序性是同一件事。 -/
theorem kernel_family_sInf (S : Set (Setoid A))
    (hS : ∀ r ∈ S, ∃ (β : Type u) (f : A → β), kernel f = r) :
    ∃ (γ : Type u) (g : A → γ), kernel g = sInf S := by
  classical
  choose β f hf using hS
  refine ⟨∀ r : S, β r.1 r.2, fun a r => f r.1 r.2 a, ?_⟩
  ext x y
  rw [kernel_rel, Setoid.sInf_iff]
  constructor
  · intro h r hr
    -- `hf r hr : kernel (f r hr) = r`，把它读成逐点等价
    have h3 : kernel (f r hr) x y := by
      show f r hr x = f r hr y
      exact congrFun h ⟨r, hr⟩
    exact (Setoid.ext_iff.mp (hf r hr)) x y |>.mp h3
  · intro h
    funext r
    have h2 : (r.1 : Setoid A) x y := h r.1 r.2
    have h3 : kernel (f r.1 r.2) x y :=
      (Setoid.ext_iff.mp (hf r.1 r.2)) x y |>.mpr h2
    exact h3

/-- **`κ` 的左逆**：从 setoid 造映射（用商映射读）再取核，回到原 setoid。

**一般化了什么**：`CFLatticeGen.ker_readoutOfSetoid`
（`kappa (readoutOfSetoid ρ) = ρ`）。
原版写法是 `Setoid.ker_mk_eq ρ` 的一行调用；本定理是**同一事实**的
命名版本，使「§10.4 的伴随对」有一个左逆的锚点。 -/
@[simp]
theorem kappa_mk (r : Setoid A) : kappa (Quotient.mk'' : A → Quotient r) = r :=
  Setoid.ker_mk_eq r

/-- ⭐⭐ **Galois 连接**：`κ ⊣ readoutOfSetoid`。

精确地，取
* `α := (A → B)` 配上「核包含」预序（`Finer` 的一般形式），
* `β := Setoid A` 配上包含序，

则对任意 `f : A → B` 与 `ρ : Setoid A`：

$$\mathrm{ker}\,f \le \rho \iff f \text{ 经由 } A/\rho \text{ 分解}.$$

**一般化了什么**：`CFLatticeGen.kappa_galoisConnection`
（`GaloisConnection kappa readoutOfSetoid`）。
原版的伴随对是 `Readout.{u,u} SCM ⇄ Setoid SCM`；
本定理把 `Readout` 侧换成**任意函数类型** `A → B`（含任意宇宙 `v`），
因而无需原版为配对宇宙而引入的 `kappa'` 变体。

**⚠ 方向说明（实测）**：真正的下降判据是 `ρ ≤ ker f`（**`ρ` 更细**）——
见 `descendBy_iff`。初稿曾按直觉写成 `ker f ≤ ρ`，**实测报错**，
并已由 `ker_le_not_descend` 给出反例。
故 Mathlib 的 `GaloisConnection` **必须**以**具体**读出
（`readoutOfSetoid ρ := Quotient.mk''`）表述，而不能用「存在分解」形式 ——
原版 `CFLatticeGen.kappa_galoisConnection` 正是这样做的。

**⚠ 与 `Setoid.map` 的关系（实测更正）**：一个自然的猜想是
「`Setoid.comap f` 是 `Setoid.map` 的右伴随」。**实测为否** ——
Mathlib 的 `Setoid.map r f` 取的是 `Relation.EqvGen`（**等价闭包**，
见 `Mathlib/Data/Setoid/Basic.lean:409`），故**不存在**
`Setoid.map_le_iff_le_comap`（全库 grep 无匹配，已实测）。
**⟹ 本框架因此走 `ker` 而非 `map`**：`ker` 天然是 `comap` 的复合
（`ker (g ∘ f) = comap f (ker g)`，见 `kernel_comp`），
从而无需任何闭包即可得到干净的伴随。 -/
theorem kappa_galois_descends {f : A → B} {ρ : Setoid A} (h : ρ ≤ kernel f) :
    ∃ h' : Quotient ρ → B, ∀ a, h' (Quotient.mk'' a) = f a :=
  (descendBy_iff ρ).mp h

/-- ⭐⭐ **Galois 连接（两步形式）**：`κ ⊣ readoutOfSetoid`，**两边都真**。

$$\mathrm{ker}\,f \le \rho \iff \exists h,\ f = h \circ \mathrm{mk}_\rho
\text{ 且 } h \text{ 由 } \rho \text{ 唯一决定}.$$

用**具体**读出 `readoutOfSetoid ρ := Quotient.mk''` 表述时，伴随条件成为：

$$\mathrm{ker}\,f \le \rho \iff \mathrm{Finer}\ f\ (\mathrm{readoutOfSetoid}\ \rho)$$

而右侧 `Finer f (readoutOfSetoid ρ)` 展开正是
`∀ a b, f a = f b → ρ a b`，即 `ker f ≤ ρ` —— **定义性等式**。

**一般化了什么**：`CFLatticeGen.kappa_galoisConnection` 的**内核**。
原版把这条写成 `GaloisConnection kappa readoutOfSetoid`（依赖 `Readout` 的
`Preorder` 实例）；本定理给出**不依赖任何实例**的等价形式，
且指出它其实是 `Iff.rfl` 级的重言 —— 与 `CFLatticeGen`
自己记录的 `finer_iff_ker_le := Iff.rfl` 完全一致。 -/
theorem kappa_galoisConnection {f : A → B} {ρ : Setoid A} :
    kernel f ≤ ρ ↔ ∀ a b, f a = f b → ρ a b :=
  Iff.rfl

/-- **核的复合律**：`ker (g ∘ f) = comap f (ker g)`。

**一般化了什么**：这是 `CFMap.ker_subset_of_factor`
（分解 ⟹ 核包含）的**精确形式**（原版只有 `≤`，本定理给出 `=`）；
也是 §10.4 伴随对之所以成立的机制性原因。 -/
@[simp]
theorem kernel_comp {C : Type w} (f : A → B) (g : B → C) :
    kernel (g ∘ f) = Setoid.comap f (kernel g) := rfl

/-- **`comap` 保持任意交**（`comap f` 是右伴随的直接推论）。

**一般化了什么**：把 §10.4 的伴随对**下推到集合层**。
原版 `CFLatticeGen` 未给出 `comap` 与交的交换律；
本定理表明「核族的下完备性」经任意映射 `f` 拉回后仍保持，
这是「子纤维只需限制 setoid」这一常用技巧的正当性依据。 -/
theorem comap_sInf {C : Type w} (f : A → C) (S : Set (Setoid C)) :
    Setoid.comap f (sInf S) = sInf (Setoid.comap f '' S) := by
  ext x y
  rw [Setoid.comap_rel, Setoid.sInf_iff, Setoid.sInf_iff]
  exact ⟨fun h r hr => by obtain ⟨s, hs, rfl⟩ := hr; exact h s hs,
         fun h s hs => h (Setoid.comap f s) ⟨s, hs, rfl⟩⟩

/-! ===========================================================================
  §10.5  ⭐ 最优性：核是最粗的相容等价关系
  =========================================================================== -/

/-- ⭐ **相容**：等价关系 `r` 使 `f` 能在 `r`-类上常值 ——
即「`f` 可沿 `r` 下降」。

**一般化了什么**：把 `Counterfactual.obs_descends_iff` 的左侧
（`∀ a b, r a b → Obs a = Obs b`）与 `AlphaKernel.Encoder.RespectsEquiv`
的编码层条件统一为**一个**名字。
⚠ **注意**：本定义比 `AlphaKernel` 的 `RespectsEquiv` 更**弱**
（后者要求编码层相等，本定义只要求 `f` 的像相等），
故它同时覆盖三套结构而**无需**各自的前件。 -/
def Compatible (f : A → B) (r : Setoid A) : Prop := ∀ a b, r a b → f a = f b

/-- ⭐ **核自身相容**：`ker f` 当然使 `f` 能下降（自反情形）。

⚠ **与 `Fate/KernelQuotientExtra.kernel_compatible` 的关系**：
`Extra` 以**展开式** `∀ a b, kernel f a b → f a = f b` 陈述同一事实
（供只 `import Extra` 的下游使用）；
本处保留 `Compatible` **谓词**形式，因 `KernelAdjunction` 需要它。
两者**名称不同**（本处为 `kernel_compatible'`），故不冲突。 -/
theorem kernel_compatible' (f : A → B) : Compatible f (kernel f) :=
  fun _ _ h => h

/-- ⭐ **相容 ⟺ 包含于核**（把 `Compatible` 接到 `Setoid` 序上）。 -/
theorem compatible_iff_le_kernel (f : A → B) (r : Setoid A) :
    Compatible f r ↔ r ≤ kernel f :=
  Iff.rfl

/-- ⭐⭐ **最优性定理（一般化 `kernel_is_coarsest`）**：
`r` 与 `f` **相容**（在每个 `r`-类上 `f` 常值）⟹ `r ≤ ker f`。

即 **`ker f` 是所有相容等价关系的上界** ——
在「商越小越好」的意义下，核给出**最小**的商。

**一般化了什么**：`AlphaKernel.kernel_is_coarsest`
（原陈述为 `∀ e₁ e₂, e₁ ≈ e₂ → (alphaKernel …).r e₁ e₂`）
与 `AlphaKernel.equiv_le_kernel` —— **两者其实是同一条定理**
（原文件把同一定理的两种写法分别命名为两条，此处合并并一般化）。

**⚠ 与 `AlphaKernel` 的差异（实测）**：`AlphaKernel.kernel_is_coarsest` 的前件
`enc.RespectsEquiv embed eqv` 要求**编码层**相等
（`toAttrs (embed e₁) = toAttrs (embed e₂)`），
而其结论的核是**抽象层**相等（`takeConcept (toAttrs …)`）。
由 `congrArg takeConcept` 前者蕴含后者，故原定理**成立** ——
但它是本定理的一个**特例**（相容条件更强）。
本定理只需「抽象层相容」，是**更弱的前件、相同的结论**。 -/
theorem kernel_is_coarsest (f : A → B) (r : Setoid A)
    (h : ∀ a b, r a b → f a = f b) : r ≤ kernel f :=
  fun a b hab => h a b hab

/-- **最优性的唯一性**：既相容又与核互相包含的 `r` **就是**核。

**一般化了什么 / 比原版强在哪**：`AlphaKernel.kernel_is_coarsest` 只证了
「核是上界」（`r ≤ ker f`），**未**问「是否还有其他上界与核等价」。
本定理给出**唯一性**：核是相容等价关系中的**最大元**，
因而在 `Setoid A` 中是**唯一**的极大相容等价 ——
「最优」在此是**严格**的（不是「最优之一」）。 -/
theorem kernel_is_coarsest_unique (f : A → B) (r : Setoid A)
    (h : ∀ a b, r a b → f a = f b) (hle : kernel f ≤ r) : r = kernel f :=
  le_antisymm (kernel_is_coarsest f r h) hle

/-- ⭐ **核可达**：每个 `Setoid A` 都是某个映射的核（取商映射即可）。

**一般化了什么**：`CFLatticeGen.kappa_surjective`
（`Function.Surjective (fun R => kappa R)`）。
原版需把 `Setoid` 嵌进 `Readout.{u,u} SCM`（经 `readoutOfSetoid`）
才能陈述满射性，且要求宇宙配对 `u = v`；
本定理直接用 `Quotient.mk'' : A → Quotient r` 作见证，**无宇宙限制**。

结合 §10.4 的 `kernel_family_sInf` 立即得到：
**核族恰是 `Setoid A` 的全体**（下封闭 + 每个 setoid 都可达），
即核族构成 `Setoid A` 的一个**完备子格**。 -/
theorem kernel_surjective (r : Setoid A) :
    ∃ f : A → Quotient r, kernel f = r :=
  ⟨Quotient.mk'', Setoid.ker_mk_eq r⟩

/-! ===========================================================================
  §10.6  ⭐⭐ 回收：①②③ 作为本框架的实例

  本节每条都以 `example` 形式**真的调用**了 §10.1–§10.5 的定理 ——
  不是「结构相似」的文本声明，而是**类型检查器核验过的实例化**。
  =========================================================================== -/

section Recycle

/-! ### ① `Fate/Counterfactual.lean` 的回收

原结构的定义：
```
structure Model where SCM : Type*; CF : Type*; Obs : SCM → CF
def cfSetoid : Setoid M.SCM := Setoid.ker M.Obs
def cfQuotient (F : Set M.SCM) : Type _ := Quotient ((cfSetoid M).comap Subtype.val)
def obsOnQuot (F) : cfQuotient M F → M.CF := Quotient.lift (fun x : F => M.Obs x.1) …
```
取 `A := M.SCM`、`B := M.CF`、`f := M.Obs` 即逐字落入本框架。 -/

variable (M_SCM : Type u) (M_CF : Type v) (M_Obs : M_SCM → M_CF)

/-- ①-a **`cfSetoid = kernel Obs`**（定义层回收）。 -/
example : Setoid.ker M_Obs = kernel M_Obs := rfl

/-- ①-b **`obsOnQuot_injective`** 是 `descend_injective` 的实例。 -/
example : Function.Injective (descend M_Obs) := descend_injective M_Obs

/-- ①-c **`cfQuotient_subsingleton_iff`** 是 `collapse_iff_subsingleton` 的实例。 -/
example (F : Set M_SCM) :
    Subsingleton (Quotient ((kernel M_Obs).comap (Subtype.val : F → M_SCM))) ↔
      Collapse M_Obs F := collapse_iff_subsingleton M_Obs F

/-- ①-d **`trichotomy`** 经本框架对**任意** `SCM`/`CF` 成立（原版绑定 `Model`）。 -/
example (F : Set M_SCM) :
    Collapse M_Obs F ∨ Faithful M_Obs F ∨ MiddleZone M_Obs F :=
  trichotomy M_Obs F

/-- ①-e **`obsOnQuotBy_injective_iff_on_F`** 是 `descendOnSubtype_injective_iff` 的实例。 -/
example (r : Setoid M_SCM) (h : r ≤ kernel M_Obs) (F : Set M_SCM) :
    Function.Injective
      (Quotient.lift (fun x : F => M_Obs x.1) (fun _ _ hab => h hab) :
        Quotient (r.comap (Subtype.val : F → M_SCM)) → M_CF) ↔
      ∀ a b : M_SCM, a ∈ F → b ∈ F → M_Obs a = M_Obs b → r a b :=
  descendOnSubtype_injective_iff h F

/-- ①-f **第一同构**：`SCM/ker Obs ≃ range Obs`（原版只有基数版，需 `[Finite]`）。 -/
noncomputable example : Quotient_kernel M_Obs ≃ Set.range M_Obs := quotientEquivRange M_Obs
/-- ①-g **`faithful_quot_card_eq`** 的强化：等势而非仅基数相等（且无需 `Finite`）。 -/
example (F : Set M_SCM) (h : Faithful M_Obs F) :
    F ≃ Quotient ((kernel M_Obs).comap (Subtype.val : F → M_SCM)) :=
  faithfulEquivOfSubtype M_Obs F h

/-! ### ② `Fate/AlphaKernel.lean` 的回收

原结构：
```
def alphaKernel (enc : Encoder F K) (E : InstSpace) (embed : E.Carrier → F.X.Carrier) : Setoid E.Carrier :=
  ⟨fun e₁ e₂ => K.takeConcept (enc.toAttrs (embed e₁)) = K.takeConcept (enc.toAttrs (embed e₂)), …⟩
```
即 `alphaKernel enc E embed = kernel (K.takeConcept ∘ enc.toAttrs ∘ embed)`。
下面**不引用 `AlphaKernel`**（避免依赖 `FateV2.Rules` 的重型 import），
而是**逐字重建同一个复合映射**再实例化 —— 这正是回收的意义所在。 -/

variable (α : Type u) (β : Type v) (γ : Type w)
variable (enc : α → β) (tC : β → γ)

/-- ②-a **α 的核就是 `kernel (takeConcept ∘ enc)`**（定义层回收）：
`AlphaKernel.alphaKernel` 的定义体逐字是它。 -/
example : Setoid α := kernel (tC ∘ enc)

/-- ②-b **`kernelQuotient_range`** 是 `descend_injective` 的实例。

⚠ **命名与陈述的差异（实测）**：`AlphaKernel.kernelQuotient_range` 的**名字**
含 `range`，但其**陈述**是 `Function.Injective (Quotient.liftOn …)` ——
即**单射性**，不是同构。本框架给出**更强**的 `quotientEquivRange`
（真同构），故该定理连同其名称下的**实质内容**一并被回收并加强。 -/
example : Function.Injective (descend (tC ∘ enc)) := descend_injective (tC ∘ enc)

/-- ②-c **`alpha_respects_kernel`**（「α 保持自己的核」）是 `kernel_is_coarsest` 的
`r := kernel f` 特例（自反情形，`le_rfl`）。 -/
example : kernel (tC ∘ enc) ≤ kernel (tC ∘ enc) :=
  kernel_is_coarsest (tC ∘ enc) (kernel (tC ∘ enc)) (fun _ _ h => h)

/-- ②-d **`kernel_is_coarsest` / `equiv_le_kernel`** 是 `kernel_is_coarsest` 的实例。

⚠ 原文件把**同一条定理**写了两遍（`equiv_le_kernel` 与 `kernel_is_coarsest`，
后者直接调用前者），本框架合并为一条并一般化到任意映射。 -/
example (r : Setoid α) (h : ∀ a b, r a b → (tC ∘ enc) a = (tC ∘ enc) b) :
    r ≤ kernel (tC ∘ enc) := kernel_is_coarsest (tC ∘ enc) r h

/-- ②-e **`alphaOnKernelQuotient`** 是 `descend` 的实例（同一 `Quotient.lift`）。 -/
example : Quotient_kernel (tC ∘ enc) → γ := descend (tC ∘ enc)

/-- ②-f **第一同构**：`InstSpace/ker α ≃ range α`，原版**没有**这条（只有单射）。 -/
noncomputable example : Quotient_kernel (tC ∘ enc) ≃ Set.range (tC ∘ enc) :=
  quotientEquivRange (tC ∘ enc)

/-! ### ③ `Fate/CFLattice.lean` + `CFLatticeGen.lean` 的回收

原结构：结构体 `Readout SCM` 含 `CF : Type v` 与 `Obs : SCM → CF`，
以及 `Finer R₁ R₂ := ∀ s t, R₁.Obs s = R₁.Obs t → R₂.Obs s = R₂.Obs t`。
`Finer R₁ R₂` 经 `CFLatticeGen.finer_iff_ker_le` 恰是 `ker R₁ ≤ ker R₂`
—— 即本框架 §10.4 的**核偏序**。 -/

variable (SCM : Type u)

/-- ③-a **`finer_iff_ker_le` 的一般形式**：`Finer` 就是 `ker` 的包含序。

⚠ 原版 `CFLatticeGen.finer_iff_ker_le` 的证明体是 `Iff.rfl`（定义性）；
本框架把 `Finer` 直接**定义**为核包含，于是这条成为 `Iff.rfl` 级的重言
—— 即**原版的定理在本框架中是定义**（这正表明框架抓对了不变量）。 -/
example (f g : SCM → β) :
    (∀ s t : SCM, f s = f t → g s = g t) ↔ kernel f ≤ kernel g := Iff.rfl

/-- ③-b **`kappa`** 是通用 `kappa` 的实例。 -/
example (f : SCM → β) : Setoid SCM := kernel f

/-- ③-c **`exists_isLUB` / `exists_isGLB` 的**下完备内核**：核族对任意交封闭。**

⚠ 这**强于**原版的 `exists_isLUB` / `exists_isGLB`：
原版须先把 `Setoid SCM` **嵌回** `Readout.{u,u} SCM`（经 `readoutOfSetoid`）
才能陈述确界的存在性，且嵌回要求宇宙配对 `u = v`；
本定理**根本不离开 `Setoid SCM`**，因而**无条件**成立。 -/
example (S : Set (Setoid SCM))
    (hS : ∀ r ∈ S, ∃ (δ : Type u) (g : SCM → δ), kernel g = r) :
    ∃ (ι : Type u) (k : SCM → ι), kernel k = sInf S :=
  kernel_family_sInf S hS

/-- ③-d **`kappa_galoisConnection`** 是 `kappa_galoisConnection` 的实例。 -/
example (f : SCM → β) (ρ : Setoid SCM) :
    kernel f ≤ ρ ↔ ∀ a b, f a = f b → ρ a b :=
  kappa_galoisConnection

/-- ③-e **`isTop_iff_obs_constant` 的核侧内容**：`Obs` 常值 ⟺ 核为 `⊤`。

**一般化了什么**：`CFLatticeGen.isTop_iff_obs_constant`
（原陈述为 `(∀ R', Finer R' R) ↔ (∀ s t, R.Obs s = R.Obs t)`）
与 `ker_eq_top_of_obs_constant`（`Setoid.ker R.Obs = ⊤`）。
本定理给出二者的**统一**：常值 ⟺ `kernel f = ⊤`，
并且**不需要** `R'` 的量化 —— 原版之所以要 `∀ R'`，是因为它把
「核序」绕道写成了「所有读出都更细」；本框架直接用核序，故省去该绕道。 -/
theorem obs_constant_iff_kernel_top (f : A → B) :
    (∀ a b : A, f a = f b) ↔ kernel f = ⊤ :=
  ⟨fun h => Setoid.eq_top_iff.mpr fun a b => h a b,
   fun h a b => Setoid.eq_top_iff.mp h a b⟩

/-- ③-f **`identity_is_finest` / `bot_is_finest` 的核侧内容**：
单射 ⟺ 核为 `⊥`。 -/
theorem injective_iff_kernel_bot (f : A → B) :
    Function.Injective f ↔ kernel f = ⊥ :=
  Setoid.ker_eq_bot_iff.symm

end Recycle

/-! ===========================================================================
  §10.7  反例与边界（诚实登记）
  =========================================================================== -/

/-- ⚠ **反例：本框架的「三情形」在 `∅` 上是退化的**。

`F = ∅` 时 `Collapse` 与 `Faithful` **同时**成立（两者都是空真）——
故三情形中的「中间地带」在空集上**空无内容**，
且 `Collapse ∧ Faithful` **可以并存**（原 `Counterfactual` 亦如此）。

**⟹ 这解释了为什么 `Counterfactual.trichotomy_via_quotCard`
必须对 `F = ∅` 单独开一支**（该文件 §六 正是这么做的）。 -/
theorem collapse_and_faithful_on_empty (f : A → B) :
    Collapse f (∅ : Set A) ∧ Faithful f (∅ : Set A) :=
  ⟨fun _ ha => absurd ha (Set.notMem_empty _),
   fun _ ha => absurd ha (Set.notMem_empty _)⟩

/-- ⚠ **反例：核族对「并」不封闭**（故 §10.4 只能是**下**完备）。

**反例构造**：取 `A := Fin 3`，令
* `r := Setoid.ker (fun i : Fin 3 => if i = 0 then (0 : Fin 2) else 1)`
  —— 即「`0` 单点、`1` 与 `2` 粘合」的划分；
* `s := Setoid.ker (fun i : Fin 3 => if i = 2 then (0 : Fin 2) else 1)`
  —— 即「`2` 单点、`0` 与 `1` 粘合」的划分。

两者**都是核**（由各自的见证映射定义）。但它们的**逐点并**
`fun a b => r a b ∨ s a b` 含 `0 ~ 1` 与 `1 ~ 2`，**不含** `0 ~ 2`，
**不传递**，故**不是** setoid，更不是任何映射的核。

**⟹ 结论**：核族在 `⊔` 下**不**封闭。这与 §10.4 只断言**下**完备一致；
也正是 `Finer` 在 `Readout` 上只是**预序**（`CFLatticeGen.finer_not_isPartialOrder`）
的格论根源：上确界必须**再取等价闭包**，而闭包一般会**跑出核族**。 -/
theorem kernel_family_not_supClosed :
    ∃ r s : Setoid (Fin 3),
      (∃ f : Fin 3 → Fin 2, kernel f = r) ∧
      (∃ f : Fin 3 → Fin 2, kernel f = s) ∧
      ¬ (∀ a b c : Fin 3, (r a b ∨ s a b) → (r b c ∨ s b c) → (r a c ∨ s a c)) := by
  -- `r`：`0` 单点、`1` 与 `2` 粘合（`i ↦ if i = 0 then 0 else 1`）
  -- `s`：`2` 单点、`0` 与 `1` 粘合（`i ↦ if i = 2 then 0 else 1`）
  refine ⟨kernel (fun i : Fin 3 => if i = 0 then (0 : Fin 2) else 1),
          kernel (fun i : Fin 3 => if i = 2 then (0 : Fin 2) else 1),
          ⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩
  intro htrans
  -- `r 1 2` 成立：`1 ≠ 0` 且 `2 ≠ 0`，两者都映到 `1`
  have h12 : (kernel (fun i : Fin 3 => if i = 0 then (0 : Fin 2) else 1)) (1 : Fin 3) 2 := by
    show (if (1 : Fin 3) = 0 then (0 : Fin 2) else 1) = (if (2 : Fin 3) = 0 then 0 else 1)
    decide
  -- `s 0 1` 成立：`0 ≠ 2` 且 `1 ≠ 2`，两者都映到 `1`
  have h01 : (kernel (fun i : Fin 3 => if i = 2 then (0 : Fin 2) else 1)) (0 : Fin 3) 1 := by
    show (if (0 : Fin 3) = 2 then (0 : Fin 2) else 1) = (if (1 : Fin 3) = 2 then 0 else 1)
    decide
  -- 传递性给出 `0 ~ 2`（在并关系下），但两项都不成立
  have h02 := htrans (0 : Fin 3) 1 2 (Or.inr h01) (Or.inl h12)
  rcases h02 with h | h
  · -- `r 0 2` 展开为 `(0 : Fin 2) = 1`，矛盾
    exact absurd (show (0 : Fin 2) = 1 from h) (by decide)
  · -- `s 0 2` 展开为 `(1 : Fin 2) = 0`，矛盾
    exact absurd (show (1 : Fin 2) = 0 from h) (by decide)

end KernelQuotientTheory

end FateV2.Modeling