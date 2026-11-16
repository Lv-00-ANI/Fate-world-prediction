import FateWorld.FateV2.Rules.T112UnaryClosure
/-!
  # Rules · T112PairProbe

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T112PairProbe.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T112UnaryClosure
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T112PairProbe` —— **T1.12 · 步骤 2 的「两个底集」探针**

  # 本文件做什么

  前面 5 个候选都被 `Fate/T112Candidates` 的探针判为「非 FCA 特有」。
  这个文件换一个角度：**不猜命题，而是把「两个底集」当成一个结构来测**。

  ## 核心观察（本文件 §1）

  > **FCA = `setPVar` 上的两个闭包算子的组合**，
  > 即 `polarUp ∘ polarDown` 与 `polarDown ∘ polarUp` 互相「转置」。

  更精确地说，**任何** `FormalCtx K` 都满足：

  * `polarUp ∘ polarDown` 是 `Set K.MFCA` 上的闭包算子（`intentClosure`）
  * `polarDown ∘ polarUp` 是 `Set K.GFCA` 上的闭包算子（`extentClosure`）
  * **两者有相同的不动点集**（经 `polar` 对应）：`|Ext| = |Int|`

  第三条是一个 `Cardinal`/`Equiv` 层面的**双侧**事实。

  ## ⚠ 探针（§2）：这条的双侧性

  * 在 `Unary`（单底集）里，第三条**退化为 `|X| = |X|`**（恒真）——**没有内容**。
  * 在 FCA 里，第三条说的是「两个**不同底集**的幂集上的两个闭包算子
    有**相同**的不动点基数」——**这是内容**。

  **⟹ 判定**：第三条 + 「`Ext ≃ Int` 的**具体对应**由 `polar` 给出」是双侧的。

  ⚠ **但**：`Ext ≃ Int` 本身可由 `GaloisConnection` 的**一般理论**给出
  （`gc.l_u_l_eq_l`、`OrderIso` 的标准构造）——**故它不是 FCA 特有**。
  **只是它的「陈述」必须两个底集。** 这正是本轮元结论的内容。
================================================================================ -/

namespace FateV2.Rules

open FateV2.Modeling
open Set

/-! ## §1  两个闭包算子与它们的不动点对应 -/

namespace T112Pair

variable (K : FormalCtx)

/-- `Set K.GFCA` 上的闭包算子（外延闭包）。 -/
def cObj : ClosureOperator (Set K.GFCA) := extentClosure K.Irel

/-- `Set K.MFCA` 上的闭包算子（内涵闭包）。 -/
def cAttr : ClosureOperator (Set K.MFCA) := intentClosure K.Irel

@[simp] theorem cObj_apply (A : Set K.GFCA) : cObj K A = K.polarDown (K.polarUp A) := rfl
@[simp] theorem cAttr_apply (B : Set K.MFCA) : cAttr K B = K.polarUp (K.polarDown B) := rfl

/-- **两个闭包算子的不动点集经 `polar` 一一对应**（`Ext ≃ Int`）。

⚠ 这是**一般 Galois 连接**的结论（`upperPolar`/`lowerPolar` 构成 `GaloisConnection`），
**不是 FCA 特有**。但它的**陈述需要两个底集**——这一点是本轮要测的。 -/
def fixEquiv : { A : Set K.GFCA // cObj K A = A } ≃ { B : Set K.MFCA // cAttr K B = B } where
  toFun p := ⟨K.polarUp p.1, by
    show K.polarUp (K.polarDown (K.polarUp p.1)) = K.polarUp p.1
    rw [K.polarUp_polarDown_polarUp]⟩
  invFun q := ⟨K.polarDown q.1, by
    show K.polarDown (K.polarUp (K.polarDown q.1)) = K.polarDown q.1
    rw [K.polarDown_polarUp_polarDown]⟩
  left_inv p := by
    refine Subtype.ext ?_
    show K.polarDown (K.polarUp p.1) = p.1
    exact p.2
  right_inv q := by
    refine Subtype.ext ?_
    show K.polarUp (K.polarDown q.1) = q.1
    exact q.2

/-- **`Ext` 与 `Int` 等势**（`fixEquiv` 的直接后果）。 -/
theorem card_ext_eq_card_int :
    Nonempty ({ A : Set K.GFCA // cObj K A = A } ≃ { B : Set K.MFCA // cAttr K B = B }) :=
  ⟨fixEquiv K⟩

end T112Pair

/-! ## §2  探针：`Unary` 情形下 `fixEquiv` 退化为 `id` -/

namespace T112PairProbe

open Fate.T112Unary

/-- ⭐ **探针（一）**：单底集里，外延闭包 `lowerPolar ∘ upperPolar`
与内涵闭包 `upperPolar ∘ lowerPolar` 在**对称** `r` 下**逐点相等**。

⟹ §1 的 `fixEquiv` 在单底集里是**同一算子的恒等对应**，信息量为 0。 -/
theorem unary_cObj_apply_eq_cAttr_apply {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (A : Set γ) :
    (extentClosure r) A = (intentClosure r) A := by
  rw [show (extentClosure r) A = lowerPolar r (upperPolar r A) from rfl,
      show (intentClosure r) A = upperPolar r (lowerPolar r A) from rfl,
      upperPolar_eq_lowerPolar_of_symm hr (lowerPolar r A),
      upperPolar_eq_lowerPolar_of_symm hr A]

/-- ⭐⭐ **探针（二）**：`fixEquiv` 之所以能「跨类型」，纯粹因为 `Set K.GFCA`
与 `Set K.MFCA` 是**两个类型**。

在 `Unary` 里它们都是 `Set γ`，故 `fixEquiv` 两端**类型相同**——`Equiv` 退化。
下面把这一点写成**类型层面的等式**（`Set γ = Set γ`），
其**平凡性正是判据**：单底集情形里「两侧的对应」不携带信息。 -/
theorem unary_fix_same_type {γ : Type*} :
    (Set γ : Type _) = Set γ :=
  rfl

end T112PairProbe

end FateV2.Rules