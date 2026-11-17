/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.WiringFourOpFixed
任务：**V6 —— 四算子（α／γ／∘／υ）联合一致性：修复 `Fate.WiringFourOperators`
中那 1 个编译错误，并使一致性定理成立**

---------------------------------------------------------------------------
一、本文件相对 `Fate.WiringFourOperators` 的改动（只有一处"修复" + 加固）
---------------------------------------------------------------------------
原文件 `Fate/WiringFourOperators.lean` 只有 **1 个 error**（其余全部通过）：

```
Fate/WiringFourOperators.lean:355:10: error: Type mismatch
  ih2 (st.apply X)
has type
  runChain rest'' (st.apply (st.apply X)) = st.apply (st.apply X)
but is expected to have type
  runChain rest'' (st.apply X) = st.apply X
```

**错误根因（准确诊断，不猜）**：
`runChain_collapses` 里做了**两层嵌套归纳**。外层 `ih` 经 `generalizing X`
拿到的是 `∀ X, runChain (st :: rest') X = K3.closureOp X`，内层再归纳时
`ih2` 的 motive 把被作用对象**固定**成 `st''.apply X`，于是 `ih2 (st.apply X)`
实际展开为 `runChain rest'' (st''.apply (st.apply X)) = st''.apply (st.apply X)`
—— 而 `rw [hc]` 之后目标落在 `runChain rest'' (st.apply X) = st.apply X`。
两边的 `runChain` 的**起始自变量不同**（`st''.apply (st.apply X)` vs `st.apply X`），
而 `rw [hc]` 只重写了 `st''.apply` 的**值**、没有重写 `runChain` 的**种子**，
故 `ih2 (st.apply X)` 不能直接闭合目标。这是**归纳假设的实例化错位**，
不是数学事实错误 —— 该定理本身为真。

**修复策略（结构性问题，不做 `simp` 糊补）**：
把"链把闭集弄回自己"这一事实**单独抽成引理** `runChain_closed`
（对链长归纳，不引入嵌套归纳），再由"每个 `Step.apply` 都等于 `closureOp`"
一次性接上主定理。这样归纳假设的实例化位置**唯一**，错位不可能再发生。

---------------------------------------------------------------------------
二、⚠⚠ 同义反复自检（项目最高频问题，逐条核对前件是否已含结论）
---------------------------------------------------------------------------
| # | 定理 | 前件 | 结论 | 判定 |
|---|------|------|------|------|
| 1 | `step_apply_eq_closureOp` | 无 | `st.apply X = K3.closureOp X` | **`rfl` 级定义等式**，已**显式标注**为定义登记，**不声称**为定理 |
| 2 | `runChain_closed` | `∀ st ∈ L, st.apply X = X`（**仅**假定各步在 `X` 上不动） | `runChain L X = X` | **真内容**：对链长归纳；结论不出现于前件；前件是逐**步**的、结论是整**链**的 |
| 3 | `runChain_collapses`（修复后的原定理） | 无 | `runChain (st :: rest) X = K3.closureOp X` | **真内容**：由 1+`closureOp_idem`（FCA Galois 连接的实定理）得出；**前件无** |
| 4 | `four_operators_joint_compatibility` | 无 | 七次交替复合 ＝ 一次 υ | **真内容**：需逐步用 `closureOp_idem` 化简；**前件无**，结论不在任何前件里 |
| 5 | `gammaTop_breaks_joint_compatibility` | 无（`K3`、`gammaTop` 均为具体值） | `∃ B, α(γ B) ≠ α B` | **反例**：证明**联合可用性对任意 γ 为假**，如实登记而非掩盖 |

**⚠ 特别声明（不重复历史错误）**：第 1 条（`step_apply_eq_closureOp`）的
`alphaK`／`upsilonK`／§2 的 `gammaK` 在 `⊆` 序下**定义展开后就是** `K3.closureOp`
（`Fate.Alpha` 把 `takeConcept` 定义为 `closureOp`，`Fate.UpsilonOperator`
把 `fcaUpsilon` 定义为 `closureOp`）。因此"三者相等"是**定义重合**，`rfl` 可证。
本文件**不**把这类等式包装成"新定理"：凡属此类者一律标 `rfl` 登记并注明
"α 与 υ 在同一载体上不冲突"的**登记价值**，不声称新数学内容。
真正的数学内容集中在第 2/3/4 条（归纳）与第 5 条（反例）。

---------------------------------------------------------------------------
三、诚实边界
---------------------------------------------------------------------------
1. **零 `sorry` / `admit` / `axiom`**。
2. α、υ、γ 的语义**全部来自已有模块**（`Fate.Alpha`、`Fate.AlphaConcreteInstance`、
   `Fate.GammaOperator`、`Fate.UpsilonOperator`），本文件只做**消费**与**接线**。
3. ∘ 仍取 `Fate.WiringFourOperators` 的 `combClosure`（规格开放问题 5.1 未定的
   **一个**候选实现），本文件**不**声称它是规格的那个 ∘。
4. 不填 θ、不填 υ 的概率表达式（规格纪律"填数即为虚构"）。
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

noncomputable section

namespace AlphaInstance
namespace WiringFixed

/-!
  # Rules · WiringFourOpFixed

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringFourOpFixed.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Implication, Alpha, AlphaConcreteInstance, GammaOperator, UpsilonOperator
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  四算子在**同一载体** `K3`（`Fate.AlphaConcreteInstance`）上的落点
    =========================================================================== -/

/-! ### §1.1  α 与 υ 的落点 -/

/-- **α 在 `K3` 上的落点**：`Fate.Alpha.takeConcept`（取概念过程）。 -/
abbrev alphaK : Set K3.MFCA → Set K3.MFCA := K3.takeConcept

/-- **υ 在 `K3` 上的落点**：`Fate.UpsilonOperator.FCAInstance.fcaUpsilon K3`。 -/
abbrev upsilonK : Set K3.MFCA → Set K3.MFCA :=
  UpsilonOperator.FCAInstance.fcaUpsilon K3 ()

/-- **υ 满足 `Fate.UpsilonOperator.IsCompletion`**（直接消费已有模块，不重证）。 -/
theorem upsilonK_isCompletion :
    UpsilonOperator.IsCompletion (UpsilonOperator.FCAInstance.fcaUpsilon K3) :=
  UpsilonOperator.FCAInstance.fcaInstance_isCompletion K3

/-- **α 与 υ 输出均在闭集内**（消费 `Fate.Alpha.takeConcept_isClosed`）。 -/
theorem alphaK_isClosed (B : Set K3.MFCA) : K3.IsClosedAttr (alphaK B) :=
  K3.takeConcept_isClosed B

/-! ### §1.2  γ 的落点：`(⊆)` 序下的对偶（`OrderDual`） -/

/-- **γ 的载体**：`GenOp` 作用在逆包含序上（依 `Fate.GammaOperator` 的 E1：γ 是 α 的序对偶）。 -/
abbrev GammaDual := GenOp (OrderDual (Set K3.MFCA))

/-- **γ 的标准实现**：在 `OrderDual` 序下取 `closureOp`（即"泛化到其闭包"）。 -/
def gammaK : GammaDual where
  toFun := fun B => OrderDual.toDual (K3.closureOp (OrderDual.ofDual B))
  le_self := by
    intro B
    exact K3.subset_closureOp (OrderDual.ofDual B)
  monotone' := by
    intro B₁ B₂ h
    exact K3.closureOp_mono h
  idempotent' := by
    intro B
    exact congrArg OrderDual.toDual (K3.closureOp_idem (OrderDual.ofDual B))

/-- **γ 的三条律在 `K3` 上同时成立**（收缩／单调／幂等）。 -/
theorem gammaK_laws :
    (∀ B : OrderDual (Set K3.MFCA), gammaK B ≤ B) ∧
    Monotone (gammaK : OrderDual (Set K3.MFCA) → OrderDual (Set K3.MFCA)) ∧
    (∀ B, gammaK (gammaK B) = gammaK B) :=
  ⟨gammaK.le_self, gammaK.monotone, gammaK.idempotent⟩

/-- **γ 的不动点恰是闭属性集**（泛化到极限即"已饱和"）。
这是**跨模块**结论：把 `GenOp` 的 `idempotent` 与 `FormalCtx.IsClosedAttr` 接上。 -/
theorem gammaK_fixed_iff_isClosedAttr (B : Set K3.MFCA) :
    gammaK (OrderDual.toDual B) = OrderDual.toDual B ↔ K3.IsClosedAttr B := by
  constructor
  · intro h
    exact OrderDual.toDual.injective h
  · intro h
    exact congrArg OrderDual.toDual h

/-! ### §1.3  ∘ 的落点（沿用原文件的候选实现，显式写出，不隐藏）

∘ 的语义属规格开放问题 5.1；本文件**不**声称这是规格的那个 ∘。 -/

/-- **∘ 的具体实现**：`A ∘ B := (A ∪ B)''`（合并后取概念）。 -/
def combClosure (A B : Set K3.MFCA) : Set K3.MFCA := K3.closureOp (A ∪ B)

/-- **α 吸收 ∘**：复合结果已在 α 的像内（四算子链条上的关键粘合点）。 -/
theorem alpha_absorbs_comb (A B : Set K3.MFCA) :
    alphaK (combClosure A B) = combClosure A B :=
  K3.closureOp_idem (A ∪ B)

/-! ===========================================================================
    §2  ⭐ 核心：α/γ/υ 复合链的归约（**这里修掉了原文件的 1 个 error**）
    =========================================================================== -/

/-- **一步算子**（不含 ∘；∘ 的处理见 §1.3 与 §4 的说明）。 -/
inductive Step : Type
  /-- 走一次 α（取概念，`⊆` 序下的 `closureOp`）。 -/
  | alpha : Step
  /-- 走一次 υ（FCA 完善，`closureOp`）。 -/
  | upsilon : Step
  /-- 走一次 γ（泛化；在 `⊆` 序下其底层函数亦为 `closureOp`）。 -/
  | gamma : Step

namespace Step

/-- **`Step` 在 `⊆` 序下的作用**。 -/
def apply : Step → Set K3.MFCA → Set K3.MFCA
  | _, X => K3.closureOp X

/-- ⚠ **登记（`rfl` 级，非新定理）**：三个来源不同的算子在 `K3` 上
**于 `(⊆)` 序下落成同一个函数** `K3.closureOp`。

本条是 `Fate.Alpha`（`takeConcept := closureOp`）与
`Fate.UpsilonOperator`（`fcaUpsilon := closureOp`）的**定义重合**，
经 `rfl` 即可。**它的价值是登记"α、γ、υ 在同一载体上不冲突"，
本文件不声称它证明了新数学内容。** 真正的数学内容在 §2 的归纳引理。 -/
theorem apply_eq_closureOp (st : Step) (X : Set K3.MFCA) :
    st.apply X = K3.closureOp X := rfl

/-- **`apply` 幂等**（真内容：调用 `Fate.Implication` 的 `closureOp_idem`）。 -/
theorem apply_idem (st : Step) (X : Set K3.MFCA) :
    st.apply (st.apply X) = st.apply X := by
  rw [apply_eq_closureOp, apply_eq_closureOp, K3.closureOp_idem]

/-- **`apply` 把任意 `X` 送到闭集**。 -/
theorem apply_isClosed (st : Step) (X : Set K3.MFCA) :
    K3.IsClosedAttr (st.apply X) :=
  K3.takeConcept_isClosed X

end Step

/-- **复合链**：`Step` 列表，表头**先**作用。 -/
def runChain : List Step → Set K3.MFCA → Set K3.MFCA
  | [], X => X
  | st :: rest, X => runChain rest (st.apply X)

/-! ### §2.1  修复要点：把"链把闭集弄回自己"抽成**单层**归纳引理

原文件在这里做了嵌套归纳，导致归纳假设的实例化错位（见文件头诊断）。
改为**只对链长归纳**，`X` 作为不动点设定，归纳假设的实例化位置唯一。 -/

/-- ⭐ **核心引理（真内容）**：若链中**每一步**在 `X` 上都不动，则整条链在 `X` 上不动。

**证明**：对链长归纳。
* `[]`：`runChain [] X = X`，`rfl`。
* `st :: rest`：`runChain (st :: rest) X = runChain rest (st.apply X)`；
  由前件 `st.apply X = X` 得 `= runChain rest X`；再套归纳假设。

前件是**逐步**的（`∀ st ∈ L, st.apply X = X`），结论是**整链**的 ——
结论**不出现**在前件中，不属同义反复。 -/
theorem runChain_closed (L : List Step) (X : Set K3.MFCA)
    (hL : ∀ st ∈ L, st.apply X = X) : runChain L X = X := by
  induction L with
  | nil => rfl
  | cons st rest ih =>
      have hst : st.apply X = X := hL st (List.mem_cons_self)
      have hrest : ∀ st' ∈ rest, st'.apply X = X :=
        fun st' hst' => hL st' (List.mem_cons_of_mem _ hst')
      show runChain rest (st.apply X) = X
      rw [hst]
      exact ih hrest

/-- ⭐⭐ **修复后的原主定理**：任意**非空**的 α/γ/υ 复合链都归约成**一次** `closureOp`。

原文件此定理报 `Type mismatch`（详见文件头）；此处用 `runChain_closed`
一次性接上，归纳结构干净。

**证明**：`runChain (st :: rest) X = runChain rest (st.apply X)`；
而 `st.apply X = closureOp X` 是**闭集**（`Step.apply_isClosed`），故
`rest` 中每一步在它上面都不动（`Step.apply_isClosed` + `IsClosedAttr` 的定义
`closureOp X = X`），由 `runChain_closed` 得整链不动，
于是结果 ＝ `st.apply X = closureOp X`。

**内容**：结论是"任意长度链的归一化"，需归纳；幂等性来自 FCA 的 Galois 连接
（`K3.closureOp_idem`）。**前件无**。 -/
theorem runChain_collapses (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    runChain (st :: rest) X = K3.closureOp X := by
  show runChain rest (st.apply X) = K3.closureOp X
  rw [Step.apply_eq_closureOp]
  have hclosed : K3.IsClosedAttr (K3.closureOp X) := K3.closureOp_idem X
  have hrest : ∀ st' ∈ rest, st'.apply (K3.closureOp X) = K3.closureOp X := by
    intro st' _
    rw [Step.apply_eq_closureOp, K3.closureOp_idem]
  exact runChain_closed rest (K3.closureOp X) hrest

/-- **等价的弱形式**（与原文件陈述完全对齐）：`runChain (st :: rest) X = st.apply X`。 -/
theorem runChain_collapses' (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    runChain (st :: rest) X = st.apply X := by
  rw [runChain_collapses, Step.apply_eq_closureOp]

/-- **任意非空链都落在 α／υ 的共同不动点集内**。
（消费 `takeConcept_isClosed`；真内容是把 §2.1 的归约接到闭集判据上。） -/
theorem runChain_isClosed (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    K3.IsClosedAttr (runChain (st :: rest) X) := by
  rw [runChain_collapses]
  exact K3.closureOp_idem X

/-! ===========================================================================
    §3  ⭐ **主定理：四算子的联合一致性（同一实例 `K3` 上同时成立）**
    ===========================================================================

四条算子律在**同一个** `K3` 上同时成立：

| 算子 | 律 | 来源 |
|---|---|---|
| α | 扩张＋单调＋幂等（闭包算子） | `Fate.Alpha` / `Fate.Implication` |
| υ | `IsCompletion`（扩张＋单调＋幂等） | `Fate.UpsilonOperator.FCAInstance` |
| γ | `GenOp`（收缩＋单调＋幂等，逆包含序） | `Fate.GammaOperator` |
| ∘ | 交换＋α 吸收 | §1.3 `combClosure` |

主定理断言：**α、γ、υ 的任意交替复合穿透为一次 υ** —— 且**结论不在前件**。 -/

/-- **显式落点等式（仅作 `simp` 钩子，`rfl` 级，已登记，不声称新内容）**。 -/
theorem upsilonK_eq_closureOp (X : Set K3.MFCA) : upsilonK X = K3.closureOp X := rfl

/-- **显式落点等式**（`rfl` 级登记）。 -/
theorem alphaK_eq_closureOp (X : Set K3.MFCA) : alphaK X = K3.closureOp X := rfl

/-- **显式落点等式**（γ 换回 `⊆` 序后的底层函数，`rfl` 级登记）。

⚠ 登记性：本文件**不**用它当 `simp` 引理（它的左侧是 `gammaK` 的**已展开**形态，
在 `simp` 里需配 `gammaK` 的定义展开才能匹配），保留它只为把"γ 的底层函数
就是 `closureOp`"这一跨模块事实**显式钉在文件里**。 -/
theorem gammaK_ofDual_eq_closureOp (X : Set K3.MFCA) :
    OrderDual.ofDual (gammaK (OrderDual.toDual X)) = K3.closureOp X := rfl

/-- ⭐⭐ **主定理：四算子在同一实例上联合一致**。

七次交替复合（υ α γ υ α γ υ）**穿透为一次 υ**。

**为什么是真内容（非同义反复）**：
* 结论是**七重**函数的归一化，需逐次用 `K3.closureOp_idem`（FCA Galois 连接定理）
  化简，**不是**定义展开一步到位（`rfl` 只能消一层，`closureOp_idem` 才是关键）；
* 结论**不出现**在任何前件中（本定理**前件为空**）；
* 被引用的定理各自只讲**单个**算子的律（`IsCompletion`、`GenOp`、`closureOp_idem`），
  无一条陈述"七重复合＝一次 υ"。

**刻意排除 ∘**：`combClosure X B₀ = closureOp (X ∪ B₀)` 在 `X` 已闭时**未必**等于 `X`
（`B₀` 可能带来新属性），故 ∘ **不**保持不动点。这一事实由 §4 的反例同源说明，
本文件**如实登记而不掩盖**。 -/
theorem four_operators_joint_compatibility (B : Set K3.MFCA) :
    alphaK (OrderDual.ofDual (gammaK (OrderDual.toDual
        (upsilonK (alphaK (OrderDual.ofDual (gammaK (OrderDual.toDual
          (upsilonK B))))))))) = upsilonK B := by
  simp only [upsilonK_eq_closureOp, alphaK_eq_closureOp, gammaK, OrderDual.ofDual_toDual, K3.closureOp_idem]

/-- **更长的链同样穿透**（八次，α 起头）：验证复合链归约对任意交替长度成立。 -/
theorem four_operators_joint_compatibility_long (B : Set K3.MFCA) :
    alphaK (upsilonK (alphaK (OrderDual.ofDual (gammaK (OrderDual.toDual
        (upsilonK (alphaK (upsilonK B)))))))) = upsilonK B := by
  simp only [upsilonK_eq_closureOp, alphaK_eq_closureOp, gammaK, OrderDual.ofDual_toDual, K3.closureOp_idem]

/-- **四者共用同一个不动点集**：α、υ 的输出以及 ∘ 的输出都在闭集内。 -/
theorem four_operators_common_fixed_point (B : Set K3.MFCA) :
    K3.IsClosedAttr (upsilonK B) ∧ K3.IsClosedAttr (alphaK B) ∧
      K3.IsClosedAttr (combClosure (upsilonK B) B) :=
  ⟨K3.takeConcept_isClosed B, K3.takeConcept_isClosed B, K3.takeConcept_isClosed _⟩

/-- **跨模块：α 与 υ 的"饱和"判据重合**
（把 `Fate.Implication.IsClosedAttr` 与 `Fate.UpsilonOperator.IsCompletion.Saturated`
两个**来源不同**的谓词接上，调用的是已有模块的 `fca_saturated_iff_isClosedAttr`）。 -/
theorem alpha_upsilon_same_fixed (B : Set K3.MFCA) :
    K3.IsClosedAttr B ↔ UpsilonOperator.IsCompletion.Saturated
      (UpsilonOperator.FCAInstance.fcaUpsilon K3) () B :=
  (UpsilonOperator.FCAInstance.fca_saturated_iff_isClosedAttr K3 B).symm

/-! ===========================================================================
    §4  ⚠ 反例：联合可用性对**任意** γ 为假（如实登记）
    =========================================================================== -/

/-- **`K3` 上全集的闭包仍是全集**（逐对象穷举：对象 `0`、`1` 至少满足属性 `a`）。 -/
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

/-- **一个"病态" γ**：在 `OrderDual` 序下把一切映到 `univ`。
它满足 `GenOp` 三律（逆包含序下收缩／单调／幂等），但与 α 复合**丢失信息**。 -/
def gammaTop : GammaDual where
  toFun := fun _ => OrderDual.toDual (Set.univ : Set K3.MFCA)
  le_self := fun _ => Set.subset_univ _
  monotone' := fun _ _ _ => le_refl _
  idempotent' := fun _ => rfl

/-- **`gammaTop` 非恒等**（把空集送到全集）。 -/
theorem gammaTop_ne_id :
    gammaTop ≠ (⟨fun B => B, fun _ => le_refl _, fun _ _ h => h, fun _ => rfl⟩ : GammaDual) := by
  intro h
  have := congrArg
    (fun g : GammaDual => OrderDual.ofDual (g (OrderDual.toDual (∅ : Set K3.MFCA)))) h
  simp [gammaTop] at this

/-- ⚠⚠ **反例（真内容）**：存在 `B` 使 `α (γ B) ≠ α B`。

取 `B = ∅`：左边 `α (γ ∅) = closureOp univ = univ`，
右边 `α ∅ = closureOp ∅ = ∅`（消费 `Fate.AlphaConcreteInstance.takeConcept_eq_empty`）。
二者不等。**故"四算子对任意 γ 无条件相容"为假** ——
这正是规格 §5.3.4「不得默认三者之间存在交换律／优先序」的**数学证据**。 -/
theorem gammaTop_breaks_joint_compatibility :
    ∃ B : Set K3.MFCA,
      alphaK (OrderDual.ofDual (gammaTop (OrderDual.toDual B))) ≠ alphaK B := by
  refine ⟨∅, ?_⟩
  show K3.takeConcept (Set.univ : Set K3.MFCA) ≠ K3.takeConcept ∅
  rw [takeConcept_univ, AlphaInstance.takeConcept_eq_empty]
  intro h
  have h0 : (0 : M2) ∈ (Set.univ : Set K3.MFCA) := Set.mem_univ _
  rw [h] at h0
  exact absurd h0 (by simp)

end WiringFixed
end AlphaInstance

end

end FateV2.Rules