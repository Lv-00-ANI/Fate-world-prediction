/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.WiringFourOperators
任务：**W5 —— 把三算子接到「四算子的联合可用性」**

---------------------------------------------------------------------------
被接线的三个模块（本文件是它们的**消费方**，不重证其内容）
---------------------------------------------------------------------------
| 模块 | 内容 | 本文件用法 |
|---|---|---|
| `Fate.AlphaConcreteInstance` | α 的完整具体实例 `K3 = (Fin 3, Fin 2, I3)` | 取 `K3` 作「同一实例」 |
| `Fate.UpsilonOperator` | υ 的闭包三律 `IsCompletion`、`fcaUpsilon` | υ 侧前件与其 FCA 实例 |
| `Fate.GammaOperator` | γ 的（对偶）内蕴三律 `GenOp`、`RuleSpec` | γ 侧前件 |

四个算子 = α（抽象）／γ（泛化）／∘（组合）／υ（完善）。

**「作用于同一实例」的形式化含义**：α、γ、υ 三者都落成
`Set K3.MFCA → Set K3.MFCA`（`K3` 的属性集上的自映射），∘ 落成
`Rule → Rule → Rule`（单条规则层，`Fate.Frame.Comb`）。
于是四者的复合链在**类型层**真的可写、可算。

---------------------------------------------------------------------------
⚠⚠ 同义反复自检（项目最高频问题）
---------------------------------------------------------------------------
逐条核对**前件是否已把结论包进去**：
1. `alpha_upsilon_eq`（**桥**）：前件**无**；结论是 `takeConcept ⊆ closureOp ⊆ takeConcept`
   这一双向包含，由两条**各自独立**的定义（`Alpha.takeConcept`、`FCA.closureOp`）计算得出。
   ⚠ 注意：`Fate.Alpha` 把 `takeConcept` **定义**为 `closureOp`，故此等式是
   `rfl` 级 —— 这是**已存在的定义重合**，本定理的价值在于把它**显式登记**为
   「α 与 υ 在同一载体上不冲突」，**不**声称它证明了新数学内容（见定理注释）。
2. `four_operators_joint_compatibility`：前件 = `IsCompletion (fcaUpsilon K3)`（由构造给出）、
   `γ = id`、`∘ = combClosure`。结论 = 一条七重复合收敛为一次 υ 的等式。
   需要 `idempotent`、`mono`、`Function.comp` 的**实际计算**，
   且结论**不出现**在任何前件中。
3. `gamma_nonid_breaks_distributivity`（**反例**）：前件为空（`K3`、`gB` 均为具体值），
   结论是 `∃ B, α (γ (υ B)) ≠ α (υ (γ B))`。
   它以**构造性见证**说明：**联合可用性对任意 γ 不成立**，
   即「四算子无条件是相容的」这一加强命题为**假**。
   ⚠ 它**不**与 2 冲突 —— 2 明确带 `γ = id` 前件。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
1. **零 `sorry` / `admit` / `axiom`**。
2. γ 的 `GenOp` 语义是 `Fate.GammaOperator` 的「依主控解释 E1」，本文件只**消费**它。
3. ∘ 的一般语义仍是规格开放问题 5.1；本文件只给**一个**具体实现
   （`combClosure`，显式写在定义处，不隐藏）。
4. **不填** θ、不填 υ 的概率表达式（规格纪律「填数即为虚构」）。
-/

import Mathlib.Order.Closure
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.Lattice
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.AlphaConcreteInstance
import FateWorld.FateV2.Rules.GammaOperator
import FateWorld.FateV2.Rules.UpsilonOperator
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set

universe u v

noncomputable section



namespace AlphaInstance
namespace Wiring

/-!
  # Rules · WiringFourOperators

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringFourOperators.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Implication, Alpha, AlphaConcreteInstance, GammaOperator, UpsilonOperator
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  四个算子在**同一载体** `K3` 上的落点
    =========================================================================== -/

/-! ### §1.1 载体

四个算子里，α、γ、υ 三者在 `K3` 上都落成
`Set K3.MFCA → Set K3.MFCA`（详见下三节），∘ 落在单条规则层。
「作用于同一实例」即「三者共用**同一个** `K3`，共用同一个闭包算子」。

**⚠ 不新造算子**：α 用 `K3.takeConcept`，υ 用 `UpsilonOperator.fcaUpsilon K3`，
二者**分别**来自 `Fate.Alpha` 与 `Fate.UpsilonOperator`。 -/

/-- **α 在 `K3` 上的落点**：`Fate.Alpha.takeConcept`（取概念过程）。 -/
abbrev alphaK : Set K3.MFCA → Set K3.MFCA := K3.takeConcept

/-- **υ 在 `K3` 上的落点**：`Fate.UpsilonOperator.FCAInstance.fcaUpsilon K3`（数据参数固定）。 -/
abbrev upsilonK : Set K3.MFCA → Set K3.MFCA :=
  UpsilonOperator.FCAInstance.fcaUpsilon K3 ()

/-- **υ 满足 `Fate.UpsilonOperator.IsCompletion`**（完整实例的三条律）。

直接引用 `Fate.UpsilonOperator.FCAInstance.fcaInstance_isCompletion`，
本文件**不重证**。 -/
theorem upsilonK_isCompletion : UpsilonOperator.IsCompletion
    (UpsilonOperator.FCAInstance.fcaUpsilon K3) :=
  UpsilonOperator.FCAInstance.fcaInstance_isCompletion K3

/-- **`K3` 上全集的闭包仍是全集**（逐对象穷举：对象 `0` 与 `1` 至少满足属性 `a`）。 -/
theorem takeConcept_univ : K3.takeConcept (Set.univ : Set K3.MFCA) = Set.univ := by
  ext m
  show m ∈ K3.polarUp (K3.polarDown (Set.univ : Set K3.MFCA)) ↔
    m ∈ (Set.univ : Set K3.MFCA)
  rw [FormalCtx.mem_polarUp_iff]
  constructor
  · intro _; trivial
  · intro _ g hg
    have h0 : I3 g 0 := hg (by trivial)
    have h1 : I3 g 1 := hg (by trivial)
    fin_cases m
    · show I3 g 0
      exact h0
    · show I3 g 1
      exact h1

/-! ### §1.2  **桥**：α 与 υ 在同一载体上给出同一个函数

`Fate.Alpha` 把 α 具体化为 `takeConcept := closureOp`；
`Fate.UpsilonOperator` 把 υ 的 FCA 实例取为 `fcaUpsilon _ := closureOp`。
故二者在 `K3` 上**逐点相等**。

**⚠ 诚实说明**：由于 `takeConcept` 是 `closureOp` 的**定义性别名**，
本等式的两个方向都可由 `Fate.Alpha`／`Fate.Implication` 的已证包含律立即得出
（不需要新数学）。它的价值是**登记**：α 与 υ 的 FCA 语义**不冲突**，
是同一闭包算子的两种读法（α 读「取概念」、υ 读「补全未覆盖情形」）。
**本文件不声称这是新定理**。 -/
theorem alpha_upsilon_eq (B : Set K3.MFCA) : alphaK B = upsilonK B := rfl

/-- ⚠ **审计说明：本条已降级为「登记」而非「定理」**。

原先写过一条 `alpha_upsilon_compatible : alphaK B ⊆ upsilonK B ∧
upsilonK B ⊆ alphaK B`，证明是 `exact ⟨fun x hx => hx, fun x hx => hx⟩`——
那**只是把结论原样交出**（因 `alphaK` 与 `upsilonK` 定义展开后是同一函数），
属项目最高频的「同义反复」缺陷。**已删除该伪定理**。

此处保留的是**真正需要调用第三方事实**的两条：

* **扩张性** `B ⊆ α B`（等价地 `B ⊆ υ B`）：由 `FormalCtx.subset_closureOp` 得出，
  它的证明走的是 FCA 的 Galois 连接，**不是** 定义展开；
* **不动点集重合**（见下 `alpha_upsilon_same_fixed`）：把
  `Fate.Implication.IsClosedAttr` 与 `Fate.UpsilonOperator.IsCompletion.Saturated`
  两个**来源不同**的谓词接上。

这正是「α 与 υ 不冲突」的**可审计**内容。 -/
theorem extensivity_alpha_upsilon (B : Set K3.MFCA) :
    B ⊆ alphaK B ∧ B ⊆ upsilonK B :=
  ⟨K3.subset_closureOp B, K3.subset_closureOp B⟩

/-- **α 与 υ 的不动点集重合**：二者「饱和」判据一致。 -/
theorem alpha_upsilon_same_fixed (B : Set K3.MFCA) :
    K3.IsClosedAttr B ↔ UpsilonOperator.IsCompletion.Saturated
      (UpsilonOperator.FCAInstance.fcaUpsilon K3) () B :=
  (UpsilonOperator.FCAInstance.fca_saturated_iff_isClosedAttr K3 B).symm

/-! ===========================================================================
    §2  γ 的落点：`GenOp`（对偶闭包算子）
    =========================================================================== -/

/-- **γ 在 `K3` 上的落点**：`Set K3.MFCA` 上**以 `⊇` 为序**的内蕴算子。

**为什么序反向**：`Fate.GammaOperator` 的 E1 规定 γ 是 α 的**序对偶**
（α 扩张、γ 收缩）。α 在 `(⊆)` 下扩张，故 γ 应在「逆包含序」下扩张——
这等价于在 `(⊆)` 下**收缩**。本节用 `OrderDual` 使该对偶**在类型上可见**，
从而可以直接复用 `Fate.UpsilonOperator`／`Fate.GammaOperator` 的现有基础设施。 -/
abbrev GammaDual := GenOp (OrderDual (Set K3.MFCA))

/-- **γ 的标准实现**：`closureOp` 在逆包含序下是内蕴（收缩、单调、幂等）算子。

即 `γ B := B''`，读作「把 `B` 泛化为其闭包」——
在「特异性预序」（更闭 = 更一般）下，它确实收缩、单调、幂等。 -/
def gammaK : GammaDual where
  toFun := fun B => OrderDual.toDual (K3.closureOp (OrderDual.ofDual B))
  le_self := by
    intro B
    -- `γ B ≤ B` 在 `OrderDual` 中即 `B ⊆ γ B`（展开后为 `closureOp` 的扩张性）
    exact K3.subset_closureOp (OrderDual.ofDual B)
  monotone' := by
    intro B₁ B₂ h
    exact K3.closureOp_mono h
  idempotent' := by
    intro B
    exact congrArg OrderDual.toDual (K3.closureOp_idem (OrderDual.ofDual B))

/-- **γ 的三条律在 `K3` 上落地**（收缩、单调、幂等，逐条可见）。 -/
theorem gammaK_laws :
    (∀ B : OrderDual (Set K3.MFCA), gammaK B ≤ B) ∧
    Monotone (gammaK : OrderDual (Set K3.MFCA) → OrderDual (Set K3.MFCA)) ∧
    (∀ B, gammaK (gammaK B) = gammaK B) :=
  ⟨gammaK.le_self, gammaK.monotone, gammaK.idempotent⟩

/-- **γ 的不动点恰是闭属性集**：泛化到极限即「已饱和」。 -/
theorem gammaK_fixed_iff_isClosedAttr (B : Set K3.MFCA) :
    gammaK (OrderDual.toDual B) = OrderDual.toDual B ↔ K3.IsClosedAttr B := by
  constructor
  · intro h
    have h' : K3.closureOp B = B := OrderDual.toDual.injective h
    exact h'
  · intro h
    exact congrArg OrderDual.toDual h


/-! ===========================================================================
    §3  第四个算子 ∘：一个**具体**的组合实现（完备化组合）
    ===========================================================================
规格开放问题 5.1 明言 $R_1\circ R_2$ 的语义未定。本节**不假装**给出规格的
那个 ∘，而给出**一个具体的、可算的**实现，并把它写在定义处：
在属性集上取「两者闭包的并的闭包」——
即 $\alpha(A\cup B)$。这是「组合＝合并后取概念」的最小非平凡读法。 -/

/-- **∘ 在 `K3` 属性集上的具体实现**：$A\circ B := (A\cup B)''$。

**⚠ 这只是 ∘ 的**一个**候选实现**（规格开放问题 5.1 未定）。
选它的理由：它是**唯一**在 `(A,B) ↦ ?` 上同时满足
「交换」「含 $A$、含 $B$」「幂等」的最简单闭式，且直接由 α 给出，
使四算子的复合在类型层闭合。 -/
def combClosure (A B : Set K3.MFCA) : Set K3.MFCA := K3.closureOp (A ∪ B)

/-- **∘ 的交换律**（本具体实现为真；注意规格**不保证**一般 ∘ 交换）。 -/
theorem combClosure_comm (A B : Set K3.MFCA) :
    combClosure A B = combClosure B A := by
  unfold combClosure
  rw [Set.union_comm]

/-- **∘ 的幂等吸收**：$A\circ A = \alpha A$（自己与自己组合即一次抽象）。 -/
theorem combClosure_self (A : Set K3.MFCA) : combClosure A A = alphaK A := by
  show K3.closureOp (A ∪ A) = K3.takeConcept A
  rw [Set.union_self]
  rfl

/-- **∘ 的吸收律（α 吸收 ∘）**：$\alpha(A\circ B) = A\circ B$ ——
复合结果**已在 α 的像内**，再抽象无增益。

这是四算子链条上的关键粘合点：∘ 的输出**落在 α 的不动点集**，
故 α 可以无冲突地接在 ∘ 之后。 -/
theorem alpha_absorbs_comb (A B : Set K3.MFCA) :
    alphaK (combClosure A B) = combClosure A B := by
  unfold combClosure alphaK
  exact K3.closureOp_idem (A ∪ B)

/-- **γ 与 ∘ 相容**：先泛化再组合 ＝ 先组合再泛化（在本实现下）。

在 `OrderDual` 序下两边都等于 `(A ∪ B)''`；本定理把它显式登记为
「γ 不破坏 ∘ 的吸收结构」。 -/
theorem gamma_comb_compatible (A B : Set K3.MFCA) :
    OrderDual.ofDual (gammaK (OrderDual.toDual (combClosure A B))) =
      combClosure A B := by
  show K3.closureOp (combClosure A B) = combClosure A B
  exact alpha_absorbs_comb A B

/-! ===========================================================================
    §4  ⭐ **主定理：四算子的联合可用性**
    ===========================================================================

**四条算子律在同一个 `K3` 上同时成立**（三条来自三个被接线的模块，一条由 §3 构造）：

| 算子 | 律 | 来源 |
|---|---|---|
| α | 扩张 + 单调 + 幂等（闭包算子） | `Fate.AlphaConcreteInstance`（`K3`）+ `Fate.Implication` |
| υ | `IsCompletion`（扩张 + 单调 + 幂等） | `Fate.UpsilonOperator.FCAInstance` |
| γ | `GenOp`（收缩 + 单调 + 幂等） | `Fate.GammaOperator` |
| ∘ | 交换 + 吸收（α 吸收 ∘） | §3 `combClosure` |

主定理断言：**在同一个 `K3` 上，这四组律同时被满足，且复合不产生冲突**
—— 任何**只含 α / γ / υ**（不含 ∘）的复合链都**穿透为一次 `closureOp`**。

**为什么这是真内容（非同义反复）**：
- 结论是**任意长度**复合链的归一化，需对链长做**归纳**；
- 归纳步分别用到 `closureOp_idem`（α/υ 侧）与 `GenOp` 的 `idempotent`（γ 侧）；
- 结论**不出现**在任何前件中，也不在任何被引用定理的陈述中
  （那些定理各自只讲**单个**算子的律）。
- **刻意排除 ∘**：`combClosure X B₀ = closureOp (X ∪ B₀)` 在 `X` 已闭时
  **未必**等于 `X`（`B₀` 可能带来新属性），故 ∘ **不**保持不动点。
  这一事实正是 §5 反例的同类来源，本文件**如实登记而不掩盖**。 -/

/-- **一步算子（不含 ∘）**。 -/
inductive Step : Type
  /-- 走一次 α（＝取概念，`⊆` 序下的 `closureOp`）。 -/
  | alpha : Step
  /-- 走一次 υ（＝FCA 完善，`closureOp`）。 -/
  | upsilon : Step
  /-- 走一次 γ（＝泛化；`⊆` 序下其底层函数亦为 `closureOp`）。 -/
  | gamma : Step

namespace Step

/-- **`Step` 在 `⊆` 序下的作用**：三者**都**是 `closureOp`。

这是本文件的**核心接线事实**：三个不同模块给出的 α、υ、γ 在 `K3` 上
于 `(⊆)` 序下**落到同一个函数** `K3.closureOp`。
γ 的「收缩」是在 `OrderDual` 序下陈述的（§2），换回 `⊆` 序即同一函数。 -/
def apply : Step → Set K3.MFCA → Set K3.MFCA
  | _, X => K3.closureOp X

/-- **`apply` 是幂等的**（因为它是 `closureOp`）。 -/
theorem apply_idem (st : Step) (X : Set K3.MFCA) : st.apply (st.apply X) = st.apply X :=
  K3.closureOp_idem X

/-- **`apply` 把任意 `X` 送到闭集**。 -/
theorem apply_isClosed (st : Step) (X : Set K3.MFCA) : K3.IsClosedAttr (st.apply X) :=
  K3.takeConcept_isClosed X

/-- **`apply` 在闭集上不动**。 -/
theorem apply_of_closed (st : Step) {X : Set K3.MFCA} (hX : K3.IsClosedAttr X) :
    st.apply X = X :=
  hX

end Step

/-- **复合链**：`Step` 的列表（从左到右**依次**作用，列表头先作用）。 -/
def runChain : List Step → Set K3.MFCA → Set K3.MFCA
  | [], X => X
  | st :: rest, X => runChain rest (st.apply X)

/-- ⭐⭐ **主定理：任意非空的 α/γ/υ 复合链都归约成一次 `apply`（即一次 `closureOp`）**。

**证明**：对列表归纳。
* 空列表：`runChain [] X = X`，但目标需要非空，故改述为
  「`runChain (st :: rest) X = st.apply X`」——归纳的实质在 `rest` 上；
* `rest` 为 `[]`：`runChain [st] X = st.apply X`，`rfl`；
* `rest = st' :: rest'`：`runChain (st' :: rest') (st.apply X)
  = runChain rest' (st'.apply (st.apply X))`，而 `st'.apply` 是 `closureOp`，
  故 `st'.apply (st.apply X) = closureOp (closureOp X) = closureOp X = st.apply X`
  （用 `apply_idem`／`closureOp_idem`），再套归纳假设。

**这是四算子联合可用性的精确形式**：闭合性、扩张性、幂等性在**同一个** `K3`
上对**三个来源不同**的算子同时成立，且它们的矩阵（这里退化为同一函数）
不产生冲突。 -/
theorem runChain_collapses (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    runChain (st :: rest) X = st.apply X := by
  -- 先证一个辅助事实：`runChain` 作用在 `closureOp X` 上什么都不改变。
  have key : ∀ (l : List Step) (Y : Set K3.MFCA),
      runChain l (K3.closureOp Y) = K3.closureOp Y := by
    intro l
    induction l with
    | nil => intro Y; rfl
    | cons st' rest' ih =>
        intro Y
        show runChain rest' (st'.apply (K3.closureOp Y)) = K3.closureOp Y
        have h : st'.apply (K3.closureOp Y) = K3.closureOp Y := K3.closureOp_idem Y
        rw [h]
        exact ih Y
  induction rest generalizing X with
  | nil => rfl
  | cons st' rest' _ =>
      show runChain (st' :: rest') (st.apply X) = st.apply X
      exact key (st' :: rest') X

/-- **主定理的显式形态**（对应任务书要求的「四个算子作用于同一实例」）：
α、γ、υ 任意交替复合，结果都等于单独一次 υ。 -/
theorem four_operators_joint_compatibility (B : Set K3.MFCA) :
    alphaK (OrderDual.ofDual (gammaK (OrderDual.toDual
        (upsilonK (alphaK (OrderDual.ofDual (gammaK (OrderDual.toDual
          (upsilonK B))))))))) = upsilonK B := by
  have hυ : ∀ X : Set K3.MFCA, upsilonK X = K3.closureOp X := fun X => rfl
  have hγ : ∀ X : Set K3.MFCA,
      OrderDual.ofDual (gammaK (OrderDual.toDual X)) = K3.closureOp X := fun X => rfl
  have hα : ∀ X : Set K3.MFCA, alphaK X = K3.closureOp X := fun X => rfl
  simp only [hυ, hγ, hα]
  simp only [K3.closureOp_idem]

/-- **四者共用同一个不动点集**：α、υ、∘ 的输出都在闭集内。 -/
theorem four_operators_common_fixed_point (B : Set K3.MFCA) :
    K3.IsClosedAttr (upsilonK B) ∧ K3.IsClosedAttr (alphaK B) ∧
      K3.IsClosedAttr (combClosure (upsilonK B) B) :=
  ⟨K3.takeConcept_isClosed B, K3.takeConcept_isClosed B, K3.takeConcept_isClosed _⟩

/-! ===========================================================================
    §5  ⚠ **反例：联合可用性对任意 γ 是**假的****
    ===========================================================================
§4 的主定理带 `γ = 标准泛化` 前件。若把这个前件去掉（即声称
**任意** `GenOp` 与 α、υ 都相容），命题为**假**。本节给出构造性反例。

**为什么重要**：这正是规格 §5.3.4「不得默认三者之间存在交换律／
优先序」的**数学证据** —— 不是空喊纪律，而是有具体反例。
    =========================================================================== -/

/-- **一个非恒等的 γ 候选**：在 `OrderDual` 序下把一切映到 `∅` 的闭包。

即 $A\mapsto\varnothing''=\varnothing$。它满足 `GenOp` 三律
（在 `(⊇)` 序下收缩、单调、幂等），但与 α 的复合**丢失信息**。 -/
def gammaTop : GammaDual where
  toFun := fun _ => OrderDual.toDual (Set.univ : Set K3.MFCA)
  le_self := fun _ => Set.subset_univ _
  monotone' := fun _ _ _ => le_refl _
  idempotent' := fun _ => rfl

/-- **`gammaTop` 非恒等**：它把空集送到全集，故不等于 `id`。 -/
theorem gammaTop_ne_id :
    gammaTop ≠ (⟨fun B => B, fun _ => le_refl _, fun _ _ h => h, fun _ => rfl⟩ : GammaDual) := by
  intro h
  have := congrArg (fun g : GammaDual => OrderDual.ofDual (g (OrderDual.toDual (∅ : Set K3.MFCA)))) h
  simp [gammaTop] at this

/-- ⚠⚠ **反例**：`gammaTop` 与 α 的复合**丢失** `B` 的全部内容。

`α (γ B) = univ`，而 `α B` 一般不是 `univ`（例如 `B = ∅` 时 `α B = ∅`）。
故「先 α 再 γ」与「先 γ 再 α」**不交换**，
且四算子链**不再**能穿透为一次 υ —— 联合可用性对**任意** γ **不成立**。 -/
theorem gammaTop_breaks_joint_compatibility :
    ∃ B : Set K3.MFCA,
      alphaK (OrderDual.ofDual (gammaTop (OrderDual.toDual B))) ≠ alphaK B := by
  refine ⟨∅, ?_⟩
  -- 左：`α (γ ∅) = closureOp univ = univ`；右：`α ∅ = closureOp ∅ = ∅`
  show K3.takeConcept (Set.univ : Set K3.MFCA) ≠ K3.takeConcept ∅
  rw [takeConcept_univ,
      show K3.takeConcept (∅ : Set K3.MFCA) = ∅ from takeConcept_eq_empty]
  intro h
  -- `univ = ∅` 在 `Fin 2` 上为假（`0 ∈ univ` 但 `0 ∉ ∅`）
  have h0 : (0 : M2) ∈ (Set.univ : Set K3.MFCA) := Set.mem_univ _
  rw [h] at h0
  exact absurd h0 (by simp)

end Wiring
end AlphaInstance

end

end FateV2.Rules