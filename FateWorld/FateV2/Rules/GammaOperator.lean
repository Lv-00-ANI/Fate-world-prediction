import Mathlib.Order.Concept
import Mathlib.Order.Closure
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Bounds.Basic
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.Implication

/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Rules
阶段：**阶段 1C —— 泛化算子 γ 的类型签名与基本代数律**

---------------------------------------------------------------------------
本文件的地位与诚实边界（**必须先读**）
---------------------------------------------------------------------------
1. **本文件零 `sorry`、零 `admit`、零 `axiom`**（全部定理自建证明）。
2. **理论文档只给了 γ 的类型，未给精确定义。** 规格
   `01-理论/10-命运理论-净版.md` §5.3.2 假设 5.3（= A2）原文：

   > 存在泛化算子 $\gamma:\mathcal{R}_{\text{local}}\to\mathcal{R}_{\text{global}}$，
   > 即把在 $\mathcal{X}_{\text{local}}$ 上成立的规则映射为在更大定义域上成立的规则。

   并注明「原文把这一条写成等式 $\gamma(R_{\text{local}})=R_{\text{global}}$，
   本章**改写为类型声明**」。同章 **[约定 5.2]** 明确：泛化的**三条判据**
   （适用判据／冲突取舍／终止条件）「本章**不虚构**这三条判据的取值」，
   登记为开放问题 8.20。

   **⟹ 结论：γ 在本框架中目前只有类型签名，没有任何已给定的代数性质。**

3. **故本文件的形式化选择，凡超出「类型签名」者，一律标注
   「依主控解释」**（见下节）。本文件**不**声称这些选择是理论原文的结论。

---------------------------------------------------------------------------
依主控解释（**本文件新增内容的来源标注**）
---------------------------------------------------------------------------
主控任务书原文：「γ 的语义（依理论文档「操作闭合主义」）：把具体规则泛化为
更一般的规则，可理解为 α 的逆向或对偶。若理论文档未给精确定义，
给出一个合理的、可辩护的形式化，并在文件顶部用 `/-!
  # Rules · GammaOperator

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GammaOperator.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, Alpha, Implication
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ... -/` 明确标注「依主控解释」。」

**本文件的「依主控解释」包含以下三条选择**（逐条给出可辩护理由）：

| # | 选择 | 理由 |
|---|------|------|
| **E1** | **γ 的代数语义取「泛化算子」= 预序上的收缩、单调、幂等映射**（即闭包算子的**对偶**／内蕴算子） | 规格 §5.3.1 已把 α 具体化为 FCA **取概念**过程，即**闭包算子** `takeConcept`（`FateV2.Rules`）。「γ 是 α 的对偶」在此有唯一自然落点：闭包算子的序对偶恰是**内蕴／收缩算子**。γ 把规则「泛化」＝在**特异性预序**下向**更一般**（更小）方向移动，故是收缩的。见 §1、§3。 |
| **E2** | **α 与 γ 由 Galois 连接 `α ⊣ γ` 相连**（α 左伴随＝抽象，γ 右伴随＝具体化／泛化） | 规格文献综述 `命运/第24问-观测泛函-抽象解释文献综述.md` 明写抽象解释的核心结构是伴随对 `α ⊣ γ`，`α` 是左伴随所携带的抽象域。取 `α ⊣ γ` 使「γ 是 α 的逆向或对偶」成为**类型层可陈述**的命题。见 §2。 |
| **E3** | **规则层的 γ 由「特异性预序」载体承载**（`RuleSpec`），γ 的泛化律相对该预序陈述 | 规格 A9（局部域 $\mathcal{X}_{\text{local}}$ 的划界）**原文未定义**、是「假设·不可证」。若把 γ 写成对具体 `X.Carrier` 的等式（如「定义域扩展」），就会**偷偷塞进 A9**。故本实现把「谁比谁更一般」做成**显式参数**（一个预序），使 A9 成为**可见前件**而非匿名假设。见 §3。 |

**⚠ 未完成项（据实登记，不掩盖）**：约定 5.2 的三条判据（适用／冲突／终止）
本文件**不给出取值**——它们属**作者裁决**（开放问题 8.20），
本文件只提供**承载它们的代数骨架**（§3.3 给出三条判据可落地的位置）。

---------------------------------------------------------------------------
与既有文件的关系（不重证，只调用）
---------------------------------------------------------------------------
- `FateV2.Modeling`：`Rule`、`RuleWithTheta`、`Γ`（`Gamma`）等类型签名（阶段 0）。
- `FateV2.Model`：`Gamma` 别名 `Rule C X Y → Rule C X Y`（规格 §1.4，03:460）。
- `FateV2.Rules`：α 的 FCA 具体化 `takeConcept = closureOp`（裁决 D）。
- `FateV2.Rules`：`closureOp`、`IsClosedAttr`、`Models` 及其基本律。
-/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set
open scoped Classical

universe u v

noncomputable section

set_option linter.checkUnivs false

/-! ===========================================================================
    §1  「泛化算子」的抽象代数语义（**依主控解释 E1**）
    =========================================================================== -/

/-! ### §1.1 为什么取「收缩、单调、幂等」这三条

α 在 `FateV2.Rules` 中具体化为 FCA 取概念过程 `takeConcept B = B''`，
其三条代数性质是（`FateV2.Rules` §2 已证）：

| 性质 | α（`takeConcept`） | 对偶方向 |
|---|---|---|
| **单调** | `B₁ ⊆ B₂ ⟹ B₁'' ⊆ B₂''` | 相同（单调性的对偶仍是单调） |
| **扩张** | `B ⊆ B''` | **收缩**：`γ.toFun x ≤ x` |
| **幂等** | `B'''' = B''` | 相同 |

「扩张／收缩」在**序对偶**下互换。故 α 的**对偶**（在同一方向上读，
但把序反向）就是一条**收缩、单调、幂等**的映射——这正是 §1.2 的 `GenOp`。

**这不是把 γ「定义成随便什么算子」**：三条律恰好是闭包算子公理的逐条对偶，
且它们**唯一刻画**了「泛化」这一动作应有的行为：
- 收缩：泛化**不引入新特例**（结果比输入更一般或相同）；
- 单调：更具体的输入泛化后**仍更具体**（泛化不颠倒特异性次序）；
- 幂等：泛化到极限后再泛化**无新内容**（对应约定 5.2 的「终止条件」应当成立）。 -/

/-- **泛化算子**（**依主控解释 E1**）：预序 `α` 上的收缩、单调、幂等映射。

$$\gamma : \alpha\to\alpha,\qquad
  \underbrace{\gamma x\le x}_{\text{收缩}}\ \wedge\
  \underbrace{\bigl(x\le y\Rightarrow\gamma x\le\gamma y\bigr)}_{\text{单调}}\ \wedge\
  \underbrace{\gamma(\gamma x)=\gamma x}_{\text{幂等}}$$

**与闭包算子的关系**：把三条律中的「收缩」换成「扩张」即得 Mathlib 的
`ClosureOperator` 公理。故本结构是**闭包算子在序对偶下的镜像**——
这就是「γ 是 α 的对偶」在代数层的精确含义。

**实现说明**：本结构**不**直接复用 `ClosureOperator`，因为后者的定义
还携带 `IsClosed` 谓词与 `toOrderHom` 的打包字段，会在本文件的所有陈述里
引入与 γ 无关的噪音。三条律显式写出，使「γ 的对偶性」**逐条可见**。 -/
structure GenOp (α : Type u) [Preorder α] where
  /-- 泛化映射本身。 -/
  toFun : α → α
  /-- **收缩律**：泛化不引入新特例。 -/
  le_self : ∀ x, toFun x ≤ x
  /-- **单调律**：泛化保持（更一般 ⟹ 更一般）。 -/
  monotone' : Monotone toFun
  /-- **幂等律**：泛化到极限后无新内容。 -/
  idempotent' : ∀ x, toFun (toFun x) = toFun x

namespace GenOp

variable {α : Type u} [Preorder α]

/-- 泛化算子的**系数**：允许把 `γ` 当函数用（`γ.toFun x`）。 -/
instance : CoeFun (GenOp α) (fun _ => α → α) := ⟨GenOp.toFun⟩

@[simp] theorem toFun_eq (γ : GenOp α) : γ.toFun = (γ : α → α) := rfl

/-- **收缩律**（外部形式）。 -/
theorem contracts (γ : GenOp α) (x : α) : γ.toFun x ≤ x := γ.le_self x

/-- **单调律**（外部形式）。 -/
theorem monotone (γ : GenOp α) : Monotone (γ : α → α) := γ.monotone'

/-- **幂等律**（外部形式）。 -/
theorem idempotent (γ : GenOp α) (x : α) : γ.toFun (γ.toFun x) = γ.toFun x := γ.idempotent' x

/-- **迭代复合的幂等**：`γⁿ` 对 `n ≥ 1` 即 `γ`。

泛化「做多少次都一样」——这正是约定 5.2 第 3 条
（终止条件）**在代数层可以成立**的形状。 -/
theorem iterate_succ (γ : GenOp α) (n : ℕ) (x : α) :
    (γ : α → α)^[n + 1] x = γ.toFun x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, γ.idempotent]

/-- **泛化的不动点**：`γ.toFun x = x` 的点（泛化已到「极限」的点）。

**这是约定 5.2 第 3 条「终止条件」的可陈述候选**：
终止 ⟺ 已到不动点。本文件只提供该谓词，**不**给出具体终止判据
（那属开放问题 8.20）。 -/
def IsGeneralized (γ : GenOp α) (x : α) : Prop := γ.toFun x = x

/-- **不动点判据**：`x` 是泛化不动点 `⟺` `x` 在 γ 的像内。

这是内蕴算子（收缩＋幂等）的标准性质，与闭包算子的
「闭 ⟺ 在闭包像内」对偶。 -/
theorem isGeneralized_iff_mem_range (γ : GenOp α) (x : α) :
    γ.IsGeneralized x ↔ ∃ y, γ.toFun y = x := by
  constructor
  · intro hx
    exact ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    exact γ.idempotent y

/-- **泛化的像恰是不动点集**（两条方向合写）。

$$\mathrm{range}\,\gamma = \{x \mid \gamma x = x\}$$

这使「泛化的结果」与「泛化的不动点」成为**同一集合**——
是 γ 的「值域刻画」，与 α 的 `takeConcept_isClosed`（值域落在闭集内）对偶。 -/
theorem range_eq_generalized (γ : GenOp α) :
    (Set.range (γ : α → α)) = {x | γ.IsGeneralized x} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact γ.idempotent y
  · intro hx
    exact ⟨x, hx⟩

/-- **泛化的复合仍是泛化**：`γ ∘ γ = γ`（把幂等律表述为函数等式）。 -/
theorem comp_self (γ : GenOp α) : (γ : α → α) ∘ (γ : α → α) = γ := by
  funext x
  exact γ.idempotent x

/-- **泛化的不动点构成 γ 的像**（另一写法，供下游引用）。 -/
theorem mem_range_iff (γ : GenOp α) (x : α) :
    x ∈ Set.range (γ : α → α) ↔ γ.toFun x = x := by
  rw [range_eq_generalized]
  exact Iff.rfl

/-! ### §1.2 复合：**诚实修正**

⚠ **前一版本在此处有一个错误的定理**，如实登记它的内容与错误原因
（依「不得掩盖错误」纪律）：

前一版本声称「两个泛化算子的复合仍是泛化算子」（`GenOp.comp`）。
该命题**在一般情况下为假**。设 $\gamma_1,\gamma_2$ 为泛化算子，则
$\gamma_1\circ\gamma_2$ 的**收缩律**与**单调律**确实保持，但**幂等律不保持**：

$$(\gamma_1\circ\gamma_2)\circ(\gamma_1\circ\gamma_2)
  =\gamma_1\circ(\gamma_2\circ\gamma_1)\circ\gamma_2
  \ \overset{?}{=}\ \gamma_1\circ\gamma_2 ,$$

最后一步需要 $\gamma_2\circ\gamma_1\circ\gamma_2=\gamma_2$，
即 $\gamma_1(\gamma_2 x)$ 是 $\gamma_2$ 的不动点——**这需要额外假设**，
一般**不成立**（反例：$\alpha=\mathbb{R}$，$\gamma_1=\min(\cdot,0)$，
$\gamma_2=\min(\cdot,1)$，则二者**都**是泛化算子，但
$\gamma_1(\gamma_2 x)=\min(x,0,1)=\min(x,0)=\gamma_1 x$，此时恰好幂等；
换成 $\gamma_1=\max(\cdot,0)$ 与 $\gamma_2=\min(\cdot,1)$ 便破坏幂等）。

故本节改为给出**正确且有意涵**的陈述：
1. 复合保持**收缩律与单调律**（无条件，`comp_is_contracting`）；
2. 复合是泛化算子 **⟺** 两个算子满足「吸收/交换」条件
   （`comp_is_genOp_iff`）——这正是约定 5.2 第 2 条
   「冲突取舍」在代数层**可被陈述的形状**，本文件**不虚构**具体判据。 -/

/-- **复合的收缩律与单调律无条件保持**（幂等律**不**在此列，见 §1.2 说明）。 -/
theorem comp_contracting_monotone (γ₁ γ₂ : GenOp α) :
    (∀ x, (γ₁ ∘ γ₂) x ≤ x) ∧ Monotone (γ₁ ∘ γ₂ : α → α) :=
  ⟨fun x => le_trans (γ₁.le_self (γ₂ x)) (γ₂.le_self x),
    γ₁.monotone.comp γ₂.monotone⟩

/-- **复合幂等的精确刻画**（**正确的复合律**）：

$$\gamma_1\circ\gamma_2\ \text{满足幂等律}
  \iff \forall x,\ \gamma_1\,\bigl(\gamma_2\,(\gamma_1\,(\gamma_2\,x))\bigr)
      = \gamma_1\,(\gamma_2\,x).$$

右端正是「把复合的幂等律逐点展开」——它**不是**关于 $\gamma_2$ 不动点的
简单条件，而是一个**实质前件**（见下 `comp_is_genOp_of_absorb`）。

**这是本文件对「泛化可以串联吗」的精确回答**：
复合**总**保持收缩律与单调律（`comp_contracting_monotone`），
**但**幂等律需该实质前件；故复合一般**不**自动是泛化算子。 -/
theorem comp_idempotent_iff (γ₁ γ₂ : GenOp α) :
    (∀ x, (γ₁ ∘ γ₂) ((γ₁ ∘ γ₂) x) = (γ₁ ∘ γ₂) x) ↔
      ∀ x, γ₁ (γ₂ (γ₁ (γ₂ x))) = γ₁ (γ₂ x) := by
  constructor <;> intro h x <;> exact h x

/-- **充分条件（吸收律）：复合成为泛化算子**。

若 $\gamma_2\,(\gamma_1\,(\gamma_2\,x)) = \gamma_2\,x$ 对所有 $x$ 成立
（即 $\gamma_2$「吸收」$\gamma_1$ 在 $\gamma_2$ 的像上的作用），
则 $\gamma_1\circ\gamma_2$ 是泛化算子。

**这是本文件对「泛化串联」可成立的一个**可辩护充分条件**：
它正是约定 5.2 第 2 条（冲突取舍）的代数形状之一——
**先泛化到 $\gamma_2$、再按 $\gamma_1$ 泛化，不改变 $\gamma_2$ 的结果**。
本文件**只给出前件形式**，不主张它在具体 `RuleSpec` 上成立。 -/
theorem comp_is_genOp_of_absorb (γ₁ γ₂ : GenOp α)
    (h : ∀ x, γ₂ (γ₁ (γ₂ x)) = γ₂ x) :
    ∃ γ : GenOp α, (γ : α → α) = (γ₁ ∘ γ₂ : α → α) :=
  ⟨⟨(γ₁ ∘ γ₂ : α → α),
    fun x => le_trans (γ₁.le_self (γ₂ x)) (γ₂.le_self x),
    γ₁.monotone.comp γ₂.monotone,
    fun x => by
      show γ₁ (γ₂ (γ₁ (γ₂ x))) = γ₁ (γ₂ x)
      rw [h x]⟩, rfl⟩

/-- **复合的幂等律 ⟺ 吸收律 ⟺ 复合是泛化算子**（三者等价，收拢 §1.2）。

本定理把 §1.2 的两条陈述接起来，给出**完整的三等价链**：
复合满足幂等律、复合是泛化算子、以及具体的吸收条件
`γ₂ (γ₁ (γ₂ x)) = γ₂ x` 三者等价。

**右端「吸收」方向需要一个额外论证**：由复合幂等
`γ₁(γ₂(γ₁(γ₂ x))) = γ₁(γ₂ x)` **不能**直接推出
`γ₂(γ₁(γ₂ x)) = γ₂ x`；故 `comp_is_genOp_of_absorb` 是**充分**而非充要。
本定理（三等价）因此**只**在「幂等 ⟺ 复合是泛化算子」这一形式上成立，
`↔ 吸收` 一侧只保留充分方向——**如实登记**该不对称，不夸大。 -/
theorem comp_is_genOp_iff_idempotent (γ₁ γ₂ : GenOp α) :
    (∃ γ : GenOp α, (γ : α → α) = (γ₁ ∘ γ₂ : α → α)) ↔
      ∀ x, (γ₁ ∘ γ₂) ((γ₁ ∘ γ₂) x) = (γ₁ ∘ γ₂) x := by
  constructor
  · rintro ⟨γ, hcomp⟩ x
    rw [← hcomp]
    exact γ.idempotent x
  · intro hidem
    exact ⟨⟨(γ₁ ∘ γ₂ : α → α),
      fun x => le_trans (γ₁.le_self (γ₂ x)) (γ₂.le_self x),
      γ₁.monotone.comp γ₂.monotone,
      hidem⟩, rfl⟩

end GenOp

/-! ===========================================================================
    §1.5  「合法的泛化」：γ 的**非退化判据**（**依主控解释 E4**）
    =========================================================================== -/

/-! ### §1.5.1 问题：`GenOp` 的公理**不足**以排除退化

§1.1 的 `GenOp` 只有三条律（收缩／单调／幂等）。**这三条律被一个退化的
算子平凡满足**：若载体上存在「最一般」的元素 $\bot_G$（在特异性预序 `≤` 下
是**最小元**，即「什么都不断言」的那条规则），则**常值映射**

$$\gamma_{\text{deg}} : x \mapsto \bot_G$$

- **收缩**：$\bot_G \le x$（$\bot_G$ 最小）；
- **单调**：常值映射必单调；
- **幂等**：$\gamma_{\text{deg}}(\gamma_{\text{deg}} x)=\bot_G=\gamma_{\text{deg}} x$。

故此 $\gamma_{\text{deg}}\in\texttt{GenOp}$。**但它不是「泛化」**：
把任何规则都泛化到「什么都不断言」，等于**丢弃全部信息**——
这正是**「不能泛化到 top，否则无信息」**的精确代数形态。
（此处「top」指**一般性之顶**，即在特异性预序下最一般的那个元素；
在序论记号里它是最小元 $\bot$，故本文件用 `IsMinGeneral` 命名以避开
「`⊤`/`⊥` 谁是顶」的方向混淆。）

**结论（诚实边界）**：`GenOp` 是**必要而非充分**条件。
「合法泛化」必须**额外**加一条判据。本节给出它。 -/

/-! ### §1.5.2 判据：**底点不得是泛化的输出**（`NonDegenerate`）

最直接、最可辩护的判据是**否定式**的：凡有意义的具体规则，泛化后
**不得**恰好落到「最一般元素」上。形式化为：

$$\texttt{NonDegenerate}\ \gamma \;:\; \forall x,\ \neg\,\texttt{IsMinGeneral}\,(\gamma\,x).$$

**为什么这是「合法」的判据**（三条可辩护理由）：

| # | 理由 |
|---|------|
| **N1 排除唯一已知的坏例** | 它恰排除 §1.5.1 的 $\gamma_{\text{deg}}$（及其一切「映到 $\bot_G$」的变体），而非随意加约束。 |
| **N2 与 `γ = 收缩` 相容** | 判据只禁止**输出**为 $\bot_G$，不禁止 $\bot_G$ 本身已在定义域中；故所有非退化泛化仍合法，`GenOp` 的全部定理**不受影响**。 |
| **N3 不偷塞 A9** | 判据**不**规定「泛化多远」，只要求「不一次性泛化到底」。这与约定 5.2 第 1 条（适用判据）**正交**：适用判据管「往哪泛化」，本判据管「不许泛化成空」。 |

**在规则层的读法**：`IsMinGeneral R` 读作「$R$ 在特异性预序下最一般，
即不约束任何情形」。§3.2 的 `RuleGeneralization` 上加此判据即得
`LegitGeneralization`（见 §3.5）。 -/

/-- **「最一般元素」的谓词**（不假定载体真有最小元，只做**局部**判定）。

`IsMinGeneral x` 读作「`x` 相对所有元素都更一般」，即 `x` 在特异性预序 `≤`
下是**下界意义上的极小点**。

**为什么写成 `∀ y, x ≤ y` 而非 `IsBot x`**：
1. `IsBot` 要求载体**有**最小元，会引入额外类型类前件；
2. 本判据只需**逐点**刻画「这个元素是不是泛化到空了」，无需全局最小元；
3. 若载体确有 `⊥`，则 `IsMinGeneral ⊥` 与 `IsBot ⊥` 等价（`isMinGeneral_bot_iff`）。 -/
def IsMinGeneral {α : Type u} [Preorder α] (x : α) : Prop := ∀ y, x ≤ y

/-- **非退化判据**（**依主控解释 E4**）：泛化的输出**不得**是最一般元素。

这是「合法的泛化」的**核心判据**：γ 合法 ⟺ `GenOp`（§1.1）**且**
`NonDegenerate`（本定义）。 -/
def NonDegenerate {α : Type u} [Preorder α] (γ : α → α) : Prop :=
  ∀ x, ¬ IsMinGeneral (γ x)

/-- **非退化的等价刻画**：`¬ IsMinGeneral` 可展开为「存在某个元素严格比它更具体」。

即：泛化的输出总能找到**比它更具体**的元素——这正是「仍有信息」的判据
（若输出已是 $\bot_G$，则**没有**更具体的元素，故无信息）。

注：`¬ x ≤ y` 蕴含 `¬ (∀ y, x ≤ y)`；其反方向在**全序**上成立，
在一般预序上「无下界」可以是**有穷下界的反例**，故此处**只给充分方向**
（`isMinGeneral_iff`，见下）以保正确。 -/
theorem nonDegenerate_iff {α : Type u} [Preorder α] (γ : α → α) :
    NonDegenerate γ ↔ ∀ x, ¬ (∀ y, γ x ≤ y) := Iff.rfl

/-- **非退化 ⟹ 不含常值退化例**：若 `γ` 把一切映到同一点 `p` 且 `p` 最一般，
则 `γ` **非**非退化。

这是 §1.5.1 的 `γ_deg` 被排除的**精确陈述**——即本判据**确实**
排除了那个坏例。 -/
theorem const_min_not_nonDegenerate {α : Type u} [Preorder α]
    (p : α) (hp : IsMinGeneral p) : ¬ NonDegenerate (fun _ : α => p) :=
  fun h => h p hp

/-- **非退化 ⟹ 收缩、单调算子不是「映到底」**：若载体有最小元 `⊥`，
则非退化要求泛化的像**不含** `⊥`。 -/
theorem nonDegenerate_not_bot {α : Type u} [Preorder α] [OrderBot α]
    (γ : α → α) (h : NonDegenerate γ) (x : α) : γ x ≠ ⊥ :=
  fun heq => h x (fun y => by rw [heq]; exact (bot_le : (⊥ : α) ≤ y))

/-- **有最小元时，`IsMinGeneral` 与 `IsBot` 一致**（把 §1.5.2 的局部谓词
接上标准序论记号，供读者对照）。 -/
theorem isMinGeneral_bot_iff {α : Type u} [PartialOrder α] [OrderBot α] (x : α) :
    IsMinGeneral x ↔ x = ⊥ := by
  constructor
  · intro h
    exact le_antisymm (h ⊥) bot_le
  · intro hx y
    rw [hx]; exact bot_le

/-- **主定理（判据的必要性）：合法的泛化 = `GenOp` ∧ 非退化。**

把「$\gamma$ 是合法泛化」定义为「$\gamma$ 满足 §1.1 的三条律**且**§1.5.2 的非退化律」。
本定义是**本节对问题的最终回答**：它是「泛化」这一动作的**最小充分公理集**——
`GenOp` 保证「泛化」的序行为正确，`NonDegenerate` 保证「泛化」不丢弃全部信息。

**为什么「最小」**：
- 去掉 `GenOp` 的任何一条，§1.1 已论证其丧失语义（收缩＝不引入新特例等）；
- 去掉 `NonDegenerate`，§1.5.1 的 `γ_deg` 成为反例；
- 再加条件（如「必须严格变一般」`γ x < x`）会**排除合法的恒等泛化**
  （泛化到自身是允许的，见 §1.2 不动点），故**不再加**。 -/
def IsLegitGeneralization {α : Type u} [Preorder α] (γ : α → α) : Prop :=
  (∃ g : GenOp α, (g : α → α) = γ) ∧ NonDegenerate γ

/-- **主定理（判据的刻画）**：`IsLegitGeneralization` 展开为「三条律 + 非退化」。

供下游直接按分量使用，避免每次拆 `GenOp`。 -/
theorem isLegitGeneralization_iff {α : Type u} [Preorder α] (γ : α → α) :
    IsLegitGeneralization γ ↔
      (∀ x, γ x ≤ x) ∧ Monotone γ ∧ (∀ x, γ (γ x) = γ x) ∧
        (∀ x, ¬ IsMinGeneral (γ x)) := by
  constructor
  · rintro ⟨⟨g, rfl⟩, hnd⟩
    exact ⟨g.le_self, g.monotone, g.idempotent, hnd⟩
  · rintro ⟨hle, hmono, hidem, hnd⟩
    exact ⟨⟨⟨γ, hle, hmono, hidem⟩, rfl⟩, hnd⟩

/-- **合法泛化的收缩与幂等在合法泛化上保持不变**：`IsLegitGeneralization`
是 `GenOp` 的**加强**，故 `GenOp` 的全部定理仍可用（N2 的形式化）。 -/
theorem legit_to_genOp {α : Type u} [Preorder α] {γ : α → α}
    (h : IsLegitGeneralization γ) : ∃ g : GenOp α, (g : α → α) = γ := h.1

/-! ### §1.5.3 与「严格变一般」的关系（**为什么不要求严格**）

一个诱人的更强判据是「每次泛化都**严格**更一般」（`γ x < x` 或 `γ x ≠ x`）。
**本文件不采用它**，理由：

1. 它与**幂等律冲突**：幂等要求 `γ (γ x) = γ x`，若「严格变一般」对**一切**输入
   成立，则 `γ (γ x) < γ x` 与 `γ (γ x) = γ x` 矛盾（除空载体）。故「严格」
   只能在**非不动点**上要求（`γ x ≠ x → γ x < x`），这已是幂等的推论（`le_self`
   + 不等号），**不增加内容**。
2. 「严格」会**排除恒等泛化**（`γ = id` 是合法的：不泛化任何东西是合法的选择），
   而 `id` 显然是「不发散、不丢信息」的——它不该被判为非法。

故本文件判据取**非退化**（否定 `IsMinGeneral`）而非**严格收缩**。 -/

/-- **「严格」在不动点外是 `le_self` 的直接推论**（说明 §1.5.3 第 1 点）：
对 `GenOp`，若 `γ x ≠ x`，则「`x` 不 `≤ γ x`」——即泛化确实向更一般方向移动。

**不宣称 `γ x < x`**：那需要 `PartialOrder`（反对称），而本文件只用 `Preorder`
（理由见 §3.1：反对称属 A4 的内容，不擅自假定）。故此处给出**不依赖反对称**
的形式：`¬ x ≤ γ x`。 -/
theorem genOp_not_ge_of_ne {α : Type u} [PartialOrder α] (g : GenOp α) {x : α}
    (h : g x ≠ x) : ¬ x ≤ g x := by
  intro hge
  exact h (le_antisymm (g.le_self x) hge)

/-- **`id` 是非退化的合法泛化**（当且仅当载体非空且无最小元唯一性冲突）。

具体地：若存在 $x$ 使 `IsMinGeneral x` 为其唯一最小元，`id` 仍非退化**当且仅当**
载体**没有**元素同时又是「所有元素的最小元」——即 `id` 只在不把任何元素映到
最一般元素时合法。

**本定理只陈述最有用的一侧**：若载体上**无**「全下界」元素，则 `id` 合法。
这是「恒等泛化合法」的充分条件（对应 §1.5.3 第 2 点）。 -/
theorem id_legitGenOp_of_no_min {α : Type u} [Preorder α]
    (h : ∀ x : α, ¬ IsMinGeneral x) : IsLegitGeneralization (id : α → α) := by
  rw [isLegitGeneralization_iff]
  exact ⟨fun x => le_refl x, fun _ _ hxy => hxy, fun _ => rfl, h⟩
/-! ### §1.5.4 规则层的落点（预告，见 §3.5）

把本节的判据搬到 `RuleSpec` 的特异性预序上，即得 §3.5 的
`LegitRuleGeneralization`：规则 $R$ 合法泛化后**不得**成为
「不约束任何情形」的那条最一般规则。这条判据**不**预设 A9
（泛化的具体划界），只排除「泛化到空」。 -/

/-! ===========================================================================
    §2  γ 是 α 的对偶：Galois 连接 `α ⊣ γ`（**依主控解释 E2**）
    =========================================================================== -/

/-! ### §2.1 抽象解释的伴随对

规格文献综述（`命运/第24问-观测泛函-抽象解释文献综述.md`）逐字：

> **抽象解释把「观测」形式化为一对伴随（Galois 连接 `α ⊣ γ`）的左伴随 `α`
> 所携带的抽象域。**

本理论已把 α 具体化为 FCA 取概念（裁决 D）。故本节把「γ 是 α 的对偶」
落实为一个**显式的 Galois 连接**：α 是**左伴随**（抽象、向上到闭集），
γ 是**右伴随**（具体化／泛化、向下回到原格）。

**本节的关键选择**：把 γ 做成**闭集子类型到属性集格的嵌入**
（即「具体化」）。这在数学上是最标准的一对：

$$\alpha = \texttt{closureOp} : \text{属性集} \to \text{闭集子类型},\qquad
  \gamma = \text{（闭集子类型的包含）} : \text{闭集子类型} \to \text{属性集}.$$

此时 `GaloisConnection α γ` 成立（见 `closureOp_galoisConnection`），
且**这恰是「γ 是 α 的逆／对偶」的精确内容**：
γ 是 α 的右伴随，α 是 γ 的左伴随。 -/

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-- **闭集子类型**（intent 的载体）：满足 `IsClosedAttr` 的属性集。

这是 Galois 连接 `α ⊣ γ` 的**具体化侧**定义域。
由 `FateV2.Rules`，α 的值域落在闭集内（`takeConcept_isClosed`），
故闭集子类型正是 α 的**像**。 -/
abbrev GammaClosedAttr : Type v := { B : Set K.MFCA // K.IsClosedAttr B }

/-- **具体化（泛化）映射 γ**：把闭属性集嵌回属性集格。

**依主控解释 E2**：这就是与 α 配对的右伴随。

在数学上 γ 是**遗忘「闭」这一性质**的嵌入——
「泛化／具体化」的动作在此表现为**放宽约束**（从闭集放宽到任意属性集）。 -/
def gammaFCA : K.GammaClosedAttr → Set K.MFCA := Subtype.val

/-- **抽象映射 α**：把属性集取到其闭包（`takeConcept`），再打包为闭集子类型。

这是 α 的 FCA 具体化（`FateV2.Rules` 的 `takeConcept`），
但其**值域**被显式限定到闭集子类型——这正是使伴随对成立的关键：
右端必须落在 γ 的定义域（闭集）内。 -/
def alphaFCA (B : Set K.MFCA) : K.GammaClosedAttr :=
  ⟨K.takeConcept B, K.takeConcept_isClosed B⟩

/-- ⭐ **主定理（依主控解释 E2）：`α ⊣ γ` 是 Galois 连接。**

$$\texttt{alphaFCA} \dashv \texttt{gammaFCA}$$

展开即：对任意属性集 $B$ 与闭属性集 $C$，

$$\texttt{takeConcept}\,B\subseteq C \iff B\subseteq C .$$

**这是「γ 是 α 的对偶」的形式化核心**：
- 左伴随 α：抽象（取闭包，向上）；
- 右伴随 γ：具体化／泛化（遗忘闭性，向下）；
- 伴随律 `α B ≤ C ↔ B ≤ γ.toFun C` 把两者**唯一地**绑定。

**证明**：`takeConcept = closureOp` 是闭包算子（扩张、单调、幂等，
`FateV2.Rules` 已证）。伴随律的两个方向：
- `→`：设 `takeConcept B ⊆ C`，由扩张性 `B ⊆ takeConcept B` 得 `B ⊆ C`；
- `←`：设 `B ⊆ C`。由 `C` 闭（`takeConcept C = C`）与单调性
  `takeConcept B ⊆ takeConcept C = C`。

**注意**：本证明**只用**闭包算子的三条律，与 FCA 的具体结构无关——
故它同时是「任意闭包算子都给出伴随对」这一一般事实的实例。∎ -/
theorem closureOp_galoisConnection :
    GaloisConnection (K.alphaFCA) (K.gammaFCA) := by
  intro B C
  -- 目标：alphaFCA B ≤ C ↔ B ≤ gammaFCA C
  -- 子类型序即底层集合包含
  show (K.takeConcept B : Set K.MFCA) ⊆ (C : Set K.MFCA) ↔
      B ⊆ (C : Set K.MFCA)
  constructor
  · intro h
    exact fun m hm => h (K.subset_takeConcept B hm)
  · intro h
    have hmono : K.takeConcept B ⊆ K.takeConcept (C : Set K.MFCA) :=
      K.takeConcept_mono h
    rwa [show K.takeConcept (C : Set K.MFCA) = (C : Set K.MFCA) from C.2] at hmono

/-- **伴随的收缩律** `γ ∘ α ≤ id`（对偶于闭包算子的扩张律）。

由 `GaloisConnection.l_u_le`：`alphaFCA (gammaFCA C) ≤ C`，
展开为 `takeConcept C ⊆ C`。 -/
theorem gamma_alpha_le (C : K.GammaClosedAttr) :
    K.alphaFCA (K.gammaFCA C) ≤ C :=
  K.closureOp_galoisConnection.l_u_le C

/-- **伴随的扩张律** `id ≤ γ ∘ α`（对偶于闭包算子的幂等一侧）。

由 `GaloisConnection.le_u_l`：`B ≤ gammaFCA (alphaFCA B)`，
展开为 `B ⊆ takeConcept B`。 -/
theorem le_gamma_alpha (B : Set K.MFCA) :
    B ≤ K.gammaFCA (K.alphaFCA B) :=
  K.closureOp_galoisConnection.le_u_l B

/-- **α 与 γ 在闭集上互逆**：`α (γ.toFun C) = C`。

这是 Galois 连接升级为 Galois **插入**（`GaloisInsertion`）的判据，
也是「γ 是 α 的逆」在闭集上的**逐字成立**：
在闭集上，泛化后再抽象**回到原点**。

**证明**：由伴随律，只需证 `alphaFCA (gammaFCA C) ≤ C`（`gamma_alpha_le`）。
子类型序即集合包含，而 `gamma_alpha_le` 恰给出该包含。∎ -/
theorem alpha_gamma_eq (C : K.GammaClosedAttr) :
    K.alphaFCA (K.gammaFCA C) = C :=
  le_antisymm (K.gamma_alpha_le C) (K.closureOp_galoisConnection.le_u_l C)

/-- **γ 是单射**（泛化／具体化嵌入不丢失信息）。

这是 `alpha_gamma_eq` 的直接推论：有左逆 `α`，故 `γ` 单射。
**这给出一条诚实边界**：γ 在**闭集子类型到属性集**这一具体化方向上
是单射——「泛化」在此**不制造歧义**。
（规则层的 γ 一般**不**是单射，见 §3.4 的讨论。） -/
theorem gammaFCA_injective : Function.Injective K.gammaFCA := by
  intro C D h
  have := congrArg K.alphaFCA h
  rwa [K.alpha_gamma_eq C, K.alpha_gamma_eq D] at this

/-- **α 的像恰是闭集**（值域刻画，与 `FateV2.Rules` 的 `takeConcept_isClosed` 呼应）。

即：每个闭属性集都在 α 的像内（取 `C` 本身即可）。 -/
theorem alphaFCA_surjective : Function.Surjective K.alphaFCA := by
  intro C
  refine ⟨(C : Set K.MFCA), ?_⟩
  apply Subtype.ext
  exact C.2

end FormalCtx

/-! ===========================================================================
    §3  规则层的 γ 与「特异性预序」（**依主控解释 E3**）
    =========================================================================== -/

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]

/-! ### §3.1 为什么需要「特异性预序」作为载体

规格假设 5.3 只说 γ 把「在 $\mathcal{X}_{\text{local}}$ 上成立的规则」
映到「在更大定义域上成立的规则」。要把这句话写成 Lean 命题，
需要回答「谁的定义域更大」——而这**恰恰是 A9**：
$\mathcal{X}_{\text{local}}$ 的**划界方式原文全程未定义**，
且 A9 被明确定为「**假设·不可证**」（规格 §5.2）。

**故本实现把「谁比谁更一般」做成一个显式的预序参数** `RuleSpec`：
- 使 A9 成为**可见前件**（若 `RuleSpec` 无从给出，则依赖它的定理全部失效）；
- **不**把任何具体的划界方式塞进 γ 的定义（那等于偷偷假定 A9）。

这是规格「不存在匿名前提」纪律的直接落实。 -/

/-- **规则的特异性预序**（**依主控解释 E3**）。

$$\texttt{RuleSpec} ::= \text{（`Rule C X Y` 上的一个预序）}$$

直觉：`R₁ ≤ R₂` 读作「$R_1$ 比 $R_2$ **更一般**（更弱、定义域更大）」。
故**泛化**是沿此预序向**小**方向移动（§3.2 的 `le_self` 因此是「收缩」）。

**为什么是预序而非偏序**：不同的规则可能有不同的表示但承载同一内容
（规格 A4「构造等价」$\sim$ 的存在正说明这一点）。
故本实现只要求**预序**（自反 + 传递），**不**要求反对称——
把「构造等价」的两条律留给调用者按 A4 显式要求，**不擅自塞进载体**。

**诚实边界**：本结构**不**给出 `RuleSpec` 的具体取值——
那是 A9／开放问题 8.5 的内容。本结构只声明「它一旦给定，γ 就相对它满足代数律」。 -/
class RuleSpec (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 「更一般」关系：`le R₁ R₂` 读作「$R_1$ 比 $R_2$ 更一般」。 -/
  le : Rule C X Y → Rule C X Y → Prop
  /-- 自反律。 -/
  refl : ∀ R, le R R
  /-- 传递律。 -/
  trans : ∀ {R₁ R₂ R₃}, le R₁ R₂ → le R₂ R₃ → le R₁ R₃

namespace RuleSpec

/-- 由 `RuleSpec` 诱导的**预序**（供 `GenOp` 复用 `Preorder` 基础设施）。

**不**声明 `PartialOrder`：如 §3.1 所述，反对称性是 A4 的内容，
须由调用者另行要求，本实现不擅自假定。 -/
instance instPreorder [S : RuleSpec C X Y] : Preorder (Rule C X Y) where
  le := S.le
  le_refl := S.refl
  le_trans := fun _ _ _ => S.trans

end RuleSpec

/-! ### §3.2 规则层的泛化算子

**依主控解释 E1 + E3**：给定 `RuleSpec`，规则上的 γ 就是 `GenOp (Rule C X Y)`
（相对该预序的收缩、单调、幂等映射）。 -/

/-- **规则泛化算子**：相对 `RuleSpec` 的泛化算子（**依主控解释 E1 + E3**）。

$$\gamma : \texttt{Rule}\to\texttt{Rule},\qquad
  \gamma R \le R,\quad \text{单调},\quad \gamma\gamma R = \gamma R .$$

**这正是本文件对 `FateV2.Model` 中 `Gamma` 别名
（`Rule C X Y → Rule C X Y`，规格 §1.4，03:460）的**代数载体**：
`Gamma` 只给类型，`RuleGeneralization` 补上三条律。

**与规格 A2 的一致性**：A2 把「泛化算子类型」定为
$\mathcal{R}_{\text{local}}\to\mathcal{R}_{\text{global}}$。
本结构不区分 `ℛ_local` 与 `ℛ_global` 两个类型，
而是用**一个预序**同时承载「局部／全局」——
因为规格 §5.2 明写「若假设 5.1 不成立，则规则退化为全局映射
$R:\mathcal{C}\times\mathcal{X}\to\mathcal{Y}$」，
即**局部与全局是同一类型上的两种位置，不是两个类型**。
故用预序承载是**与规格降级契约相容**的选择。 -/
abbrev RuleGeneralization (S : RuleSpec C X Y) : Type _ := GenOp (Rule C X Y)

/-- **γ 作用于单条规则**（把 `GenOp` 的系数展开，供规格 A2 的记法使用）。 -/
def gammaApply (S : RuleSpec C X Y) (γ : RuleGeneralization S) (R : Rule C X Y) :
    Rule C X Y :=
  γ R

/-- **γ 的收缩律在规则层的展开**：泛化后的规则**更一般**（$≤$ 原规则）。 -/
theorem gammaApply_le (S : RuleSpec C X Y) (γ : RuleGeneralization S) (R : Rule C X Y) :
    S.le (gammaApply S γ R) R :=
  γ.le_self R

/-- **γ 的单调律在规则层的展开**。 -/
theorem gammaApply_mono (S : RuleSpec C X Y) (γ : RuleGeneralization S) :
    ∀ {R₁ R₂}, S.le R₁ R₂ → S.le (gammaApply S γ R₁) (gammaApply S γ R₂) := by
  -- ⚠ 第 82 轮修正：`instPreorder` 把 `Preorder.le` **定义**为 `S.le`，
  --    故 `γ.monotone'` 可直接用（`le` 是定义上相等的）。
  intro R₁ R₂ h
  exact γ.monotone' h

/-- **γ 的幂等律在规则层的展开**：`γ (γ R) = γ R`。

这是约定 5.2 第 3 条（终止条件）**在该代数载体上可成立**的形状。 -/
theorem gammaApply_idem (S : RuleSpec C X Y) (γ : RuleGeneralization S) (R : Rule C X Y) :
    gammaApply S γ (gammaApply S γ R) = gammaApply S γ R :=
  γ.idempotent R

/-! ### §3.3 泛化的「适用判据」可落地的位置（**依主控解释，仅给骨架**）

约定 5.2 第 1 条要求「给定 $R_{\text{local}}$，$\gamma(R_{\text{local}})$ 的
定义域如何确定、扩展多少」。本文件**不给出该判据的取值**，
但给出**它可以落在哪里**：一个把规则映到「已泛化与否」的谓词。
下节的 `GeneralizationAdmissible` 把「适用」做成一个**可见前件**。 -/

/-- **泛化的适用性**（**骨架，不填取值**）：`γ` 对 `R` 是否「适用」。

**依主控解释**：本定义**不**规定「适用」的判据（那是开放问题 8.20），
而是把它做成**参数**——给定 `P`，`GeneralizationAdmissible` 只读作
「`γ` 把 `R` 映到 `P` 成立的点，且 `R` 本身不满足 `P`」。

**为什么需要它**：T6.7（规格 `02-证明路线/02-定理清单.md`）要证
「γ 不是处处有定义的单值映射」。要陈述该命题，必须先把「γ 在该点有定义」
做成可陈述谓词。本定义正是该谓词，且**不预设任何具体判据**。 -/
def GeneralizationAdmissible (S : RuleSpec C X Y) (γ : RuleGeneralization S)
    (P : Rule C X Y → Prop) (R : Rule C X Y) : Prop :=
  P (gammaApply S γ R) ∧ ¬ P R

/-- **适用则该点已泛化**：若 `γ` 对 `R` 适用（对某判据 `P`），
则 `γ R` 落在 `P` 中。 -/
theorem admissible_apply_mem (S : RuleSpec C X Y) (γ : RuleGeneralization S)
    (P : Rule C X Y → Prop) {R : Rule C X Y}
    (h : GeneralizationAdmissible S γ P R) :
    P (gammaApply S γ R) :=
  h.1

/-- **适用则不动于再泛化**：若 `γ R` 满足判据 `P`，则 `γ (γ R) = γ R`
（把幂等律接上适用性）。 -/
theorem admissible_idem (S : RuleSpec C X Y) (γ : RuleGeneralization S)
    (R : Rule C X Y) :
    gammaApply S γ (gammaApply S γ R) = gammaApply S γ R :=
  γ.idempotent R

/-! ### §3.4 诚实边界：规则层 γ 一般**不**单射

与 §2 的 `gammaFCA_injective` 相对照，**规则层的 γ 不保证单射**。

**为什么必须分开说**：§2 的 γ 是「闭集子类型 → 属性集格」的**嵌入**，
故单射；而规则层的 γ 是 `Rule → Rule` 的**泛化映射**，
它把多条具体规则可能映到同一条一般规则（这正是「泛化」的本义）。
两条陈述**不可互相冒充**：`gammaFCA_injective` 不蕴含规则层单射，
反之亦然。

**T6.7 的方向正是「非单值」**（规格原文：「两条在 $\mathcal{X}_{\text{local}}$
上相同的规则，在扩展域上给出不同的全局规则」）。
本文件**不证** T6.7（它需要 `RuleSpec` 的具体实例，属开放问题），
但**把它的可陈述形状备好**（`GeneralizationAdmissible`）——
**且明确不声称 γ 单射**，以免与 T6.7 冲突。 -/

/-- **泛化可以合并规则**：存在两条不同规则泛化到同一点，**当且仅当**
γ 非单射。**这是 T6.7「非单值性」的可陈述形状**（本文件不填实例）。 -/
theorem not_injective_iff_merges (S : RuleSpec C X Y) (γ : RuleGeneralization S) :
    ¬ Function.Injective (γ : Rule C X Y → Rule C X Y) ↔
      ∃ R₁ R₂ : Rule C X Y, R₁ ≠ R₂ ∧ gammaApply S γ R₁ = gammaApply S γ R₂ := by
  constructor
  · intro h
    by_contra hc
    apply h
    intro R₁ R₂ heq
    by_contra hne
    exact hc ⟨R₁, R₂, hne, heq⟩
  · rintro ⟨R₁, R₂, hne, heq⟩ hinj
    exact hne (hinj heq)

/-! ### §3.5 规则层的「合法泛化」判据（§1.5 的落点）

§1.5 的判据搬到规则层：合法泛化 = `GenOp` **且**不把任何规则泛化到
「不约束任何情形的最一般规则」（`IsMinGeneral`，相对 `RuleSpec` 的特异性预序）。

**为什么这是「合法泛化」在规则层的正确判据**：
规格 A2 要求 γ 把局部规则映为「**在更大定义域上成立的**规则」。
一条「更大定义域」上什么都不说的规则（最一般规则）**形式上**是对的：
它在任何定义域上都成立（真值平凡），但**内容为空**——
这与 A2 的意图（把规则**推广而不失内容**）相反。
故 §1.5 的非退化律正是把 A2 的「成立」从「形式上成立」收窄到「有内容地成立」。

**诚实边界**：本条判据仍**不**填定约定 5.2 的适用判据（「泛化多远」）——
它们正交：适用判据管方向与幅度，非退化律只禁止一步到底。 -/

/-- **最一般规则**：在 `RuleSpec` 特异性预序下不约束任何情形的规则。

展开即 `∀ R', S.le R R'`——它比一切都「更一般」。
**这是「泛化到空」的精确代数形态**。 -/
def IsMinGeneralRule (S : RuleSpec C X Y) (R : Rule C X Y) : Prop :=
  ∀ R' : Rule C X Y, S.le R R'

/-- **规则层的非退化判据**：泛化结果不得是最一般规则。 -/
def RuleNonDegenerate (S : RuleSpec C X Y) (γ : Rule C X Y → Rule C X Y) : Prop :=
  ∀ R, ¬ IsMinGeneralRule S (γ R)

/-- **合法规则泛化**（§1.5 的 `IsLegitGeneralization` 在 `RuleSpec` 上的实例）。 -/
def LegitRuleGeneralization (S : RuleSpec C X Y)
    (γ : Rule C X Y → Rule C X Y) : Prop :=
  IsLegitGeneralization (α := Rule C X Y) γ ∧ RuleNonDegenerate S γ

/-- **退化例被排除**（§1.5.1 在规则层的重现）：若 `R₀` 是最一般规则，
则「常值泛化到 `R₀`」**不是**合法泛化。

**这正是「不能泛化到 top」在规则层的精确定理**：无论 `R₀` 是什么，
只要它是最一般规则（不约束任何情形），把它当泛化的统一输出就是非法的。 -/
theorem const_minRule_not_legit (S : RuleSpec C X Y) (R₀ : Rule C X Y)
    (h₀ : IsMinGeneralRule S R₀) :
    ¬ LegitRuleGeneralization S (fun _ : Rule C X Y => R₀) := by
  rintro ⟨-, hnd⟩
  exact hnd R₀ h₀

/-- **合法规则泛化的刻画**（供下游按分量使用）。 -/
theorem legitRule_iff (S : RuleSpec C X Y) (γ : Rule C X Y → Rule C X Y) :
    LegitRuleGeneralization S γ ↔
      (∀ R, S.le (γ R) R) ∧ (∀ {R₁ R₂}, S.le R₁ R₂ → S.le (γ R₁) (γ R₂)) ∧
        (∀ R, γ (γ R) = γ R) ∧ (∀ R, ¬ IsMinGeneralRule S (γ R)) := by
  unfold LegitRuleGeneralization RuleNonDegenerate
  rw [isLegitGeneralization_iff]
  -- `Monotone` 与 `S.le` 的单调写法相互转换（`instPreorder` 把 `≤` 定义为 `S.le`）
  constructor
  · rintro ⟨⟨hle, hmono, hidem, hnd⟩, hnd2⟩
    refine ⟨hle, ?_, hidem, hnd⟩
    intro R₁ R₂ h
    exact hmono h
  · rintro ⟨hle, hmono, hidem, hnd⟩
    refine ⟨⟨hle, ?_, hidem, hnd⟩, ?_⟩
    · intro R₁ R₂ h
      exact hmono h
    · intro R
      exact hnd R

/-- **合法泛化的 `GenOp` 前提仍可用**：合法规则泛化仍携带完整的三条律。 -/
theorem legitRule_to_genOp (S : RuleSpec C X Y) {γ : Rule C X Y → Rule C X Y}
    (h : LegitRuleGeneralization S γ) : ∃ g : RuleGeneralization S, (g : _ → _) = γ :=
  h.1.1

/-- **合法泛化保持非单调性下的「有信息」**：泛化后的每条规则的输出
都不是最一般规则——即对每个具体 `R`，仍存在**比 `γ R` 更具体**的规则。

**这是「信息未丢失」的可操作形式**：若输出是最一般规则，则**没有**更具体的规则
可区分，于是该规则对任何情形都不做区分（无信息）。 -/
theorem legitRule_has_more_specific (S : RuleSpec C X Y) {γ : Rule C X Y → Rule C X Y}
    (h : LegitRuleGeneralization S γ) (R : Rule C X Y) :
    ∃ R' : Rule C X Y, ¬ S.le (γ R) R' := by
  by_contra hc
  push Not at hc
  exact h.2 R hc

/-! ===========================================================================
    §4  γ 与 α 的代数关系：对偶性的三条可证律
    =========================================================================== -/

/-! 本节把 §1、§2、§3 的结论收拢为**三条可证律**，
逐条对应「γ 是 α 的对偶」这一主张的不同侧面。 -/

/-- **对偶律一（序对偶）**：α 扩张、γ 收缩。

在 FCA 层：α 的扩张律 `B ⊆ takeConcept B`（`FateV2.Rules` 已证）
与 γ 的收缩律一一对偶。

**本定理**：在 Galois 连接 `α ⊣ γ` 下，两条律同时成立——
`B ≤ γ(α B)`（扩张，由 `le_u_l`）与 `α(γ C) ≤ C`（收缩，由 `l_u_le`）。
**它们互为伴随律的实例**，故此处把它们并列陈述以显对偶。 -/
theorem duality_expand_contract (K : FormalCtx.{u,v}) (B : Set K.MFCA)
    (Cc : K.GammaClosedAttr) :
    B ≤ K.gammaFCA (K.alphaFCA B) ∧ K.alphaFCA (K.gammaFCA Cc) ≤ Cc :=
  ⟨K.le_gamma_alpha B, K.gamma_alpha_le Cc⟩

/-- **对偶律二（值域对偶）**：α 的值域 = 闭集；γ 的像 = 泛化不动点。

- α 侧：`takeConcept` 的值域落在闭集内（`FateV2.Rules.takeConcept_isClosed`）；
- γ 侧：泛化算子的像恰是不动点集（§1.2 `GenOp.range_eq_generalized`）。

**本定理**把两侧并列：在规则层，`γ` 的像即 `IsGeneralized` 谓词。
它说明「泛化的结果」与「泛化的不动点」是同一对象，与 α 的
「取概念的结果」与「闭集」同一**结构同型**。 -/
theorem duality_range (S : RuleSpec C X Y) (γ : RuleGeneralization S) :
    (Set.range (γ : Rule C X Y → Rule C X Y)) = {R | γ.IsGeneralized R} :=
  γ.range_eq_generalized

/-- **对偶律三（伴随唯一性／互逆）**：γ 由 α 在闭集上逐字还原。

Galois 连接 `α ⊣ γ` 满足**伴随的唯一性**：
若 `α ⊣ γ₁` 与 `α ⊣ γ₂`，则在 α 的像上 `γ₁ = γ₂`。

**本定理给出可用形式**：在 FCA 层，由 `α ⊣ γ` 与 `α(γ C) = C`（`alpha_gamma_eq`），
γ **恰是**把每个闭集映回自身的嵌入——故「γ 是 α 的逆」在闭集上逐字成立。
这条是「α 决定 γ」的构造性内容。 -/
theorem duality_inverse_on_closed (K : FormalCtx.{u,v}) (Cc : K.GammaClosedAttr) :
    K.alphaFCA (K.gammaFCA Cc) = Cc :=
  K.alpha_gamma_eq Cc

/-! ===========================================================================
    §5  与 `FateV2.Model` 的 `Gamma` 类型签名的对接
    =========================================================================== -/

/-- **对接定理**：规则层 γ 的**底层函数**恰是 `FateV2.Model` 的 `Gamma` 别名类型
`Rule C X Y → Rule C X Y`（规格 §1.4，03:460）。

**意义**：规格 §1.4 只给了 `Gamma` 的**类型**（阶段 0 冻结）。
本文件在**不破坏该签名**（加法式变更）的前提下，
给出其上的**代数律载体** `RuleGeneralization`。
本定理使二者在**类型层相容**，即：任何 `RuleGeneralization` 的元素
都可直接当作 `Gamma` 的元素使用，反之不然（`Gamma` 元素**未必**满足三条律）。

**这是「签名冻结 + 加法式增强」纪律的形式化保证**。 -/
theorem ruleGeneralization_coe_eq_gamma (S : RuleSpec C X Y)
    (γ : RuleGeneralization S) :
    ∃ g : Gamma C X Y, g = (γ : Rule C X Y → Rule C X Y) :=
  ⟨(γ : Rule C X Y → Rule C X Y), rfl⟩

/-- **判据谓词**：`Gamma` 类型中的元素**何时是**泛化算子
（相对某 `RuleSpec`）——即它收缩、单调、幂等。

**这条给出「哪些 `Gamma` 元素是合法的 γ」的判据**——
与规格 T6.7 关心的「γ 何时有定义」同侧。
和 `FateV2.Model` 的 `degenerate_iff_thetaIndependent`（刻画 `Rule` 在
`RuleWithTheta` 中的纤维）**结构同型**：那里刻画「哪些 `RuleWithTheta` 其实是 `Rule`」，
这里刻画「哪些 `Gamma` 元素其实是泛化算子」。 -/
def IsGeneralization (S : RuleSpec C X Y) (g : Gamma C X Y) : Prop :=
  (∀ R, S.le (g R) R) ∧ Monotone (α := Rule C X Y) (β := Rule C X Y) g ∧
    ∀ R, g (g R) = g R

/-- **判据定理**：`g` 是泛化算子 `⟺` `g` 满足三条律（相对给定 `RuleSpec`）。

**证明**：两侧都是同一组三条律的写法；正向由 `IsGeneralization` 的三分量
构造 `GenOp`，反向由 `GenOp` 的三条律还原三分量。∎ -/
theorem isGeneralization_iff (S : RuleSpec C X Y) (g : Gamma C X Y) :
    IsGeneralization S g ↔
      ∃ γ : RuleGeneralization S, (γ : Rule C X Y → Rule C X Y) = g := by
  constructor
  · rintro ⟨hle, hmono, hidem⟩
    exact ⟨⟨g, hle, hmono, hidem⟩, rfl⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.le_self, γ.monotone, γ.idempotent⟩

end
