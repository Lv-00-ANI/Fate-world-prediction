import FateWorld.Legacy.ConcreteBridge
import FateWorld.Legacy.QuantCompletion

/-! ===========================================================================
  §43  ⭐⭐ **具体桥方案的定量刻画**（「定量化」计划第三步）

  **背景**：第 27 轮的 `ConcreteBridge` 给出了桥方案的**结构**结论
  （$\sim_1 = \ker \mathrm{ObsInt}$，互模拟是加细），
  **但未量化「桥有多大」**。

  ## 本节的目标

  | 定理 | 内容 |
  |---|---|
  | ⭐⭐ **`obsInt_ncard_le_resp`** | **一步签名 $\le |\mathrm{Resp}|$** |
  | ⭐⭐ **`equiv1_quot_card_le_signatures`** | **桥商 $\le$ 签名像的基数** |
  | ⭐⭐ **`equiv1_quot_card_le_pow`** | **桥商 $\le$ 动作→响应集 的函数空间** |
  | ⭐ **`obsInt_mono_of_step_subset`** | 转移系统细化 ⟹ 签名单调 |

  ## ⭐ 为何这是「定量」

  **结构定理说「桥 = 一步签名的核」；
  定量定理说「这个桥**至多有多大**」** ——
  **后者才能回答「这个方案的**实际代价**」。**

  ## ⭐⭐ 核心界

  $$\bigl|\mathrm{SCM}/\sim_1\bigr| \le
    \bigl|\mathrm{Action} \to \mathcal{P}(\mathrm{Resp})\bigr|
    = \bigl(2^{|\mathrm{Resp}|}\bigr)^{|\mathrm{Action}|}$$

  **⟹ 即**：**桥商的规模由**动作数与响应数**共同界住** ——
  **与 `SCM` 的大小无关。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace ConcreteBridgeQuant

universe u v w

variable {SCM : Type u} {Action : Type v} {Resp : Type w}

/-! ### §43.1 ⭐ 一步签名的规模界 -/

/-- ⭐⭐ **一步签名 $\subseteq$ 响应集**。

$$\mathrm{ObsInt}\,s\,a \subseteq \mathrm{Resp}$$ -/
theorem obsInt_subset_univ (step : SCM → Action → SCM → Resp → Prop) (s : SCM)
    (a : Action) :
    ConcreteBridge.ObsInt step s a ⊆ Set.univ :=
  Set.subset_univ _

/-- ⭐⭐ **一步签名的基数 $\le |\mathrm{Resp}|$**。

$$|\mathrm{ObsInt}\,s\,a| \le |\mathrm{Resp}|$$

**⟹ 即**：**单个动作下的签名至多含全部响应。** -/
theorem obsInt_ncard_le_resp [Finite Resp]
    (step : SCM → Action → SCM → Resp → Prop) (s : SCM) (a : Action) :
    (ConcreteBridge.ObsInt step s a).ncard ≤ (Set.univ : Set Resp).ncard :=
  Set.ncard_le_ncard (obsInt_subset_univ step s a) (Set.toFinite _)

/-! ### §43.2 ⭐⭐ 完整签名 -/

/-- ⭐⭐ **完整签名**：一个 SCM 对应的「逐动作签名」函数。

$$\mathrm{sig}\,s := \lambda a.\ \mathrm{ObsInt}\,s\,a$$

**⟹ 这正是 `Equiv1` 所比较的对象**（$\sim_1$ 就是它的核）。 -/
def fullSignature (step : SCM → Action → SCM → Resp → Prop) (s : SCM) : Action → Set Resp :=
  fun a => ConcreteBridge.ObsInt step s a

/-- ⭐⭐ **`Equiv1` 的核 = 完整签名的核**（把两种表述对齐）。

$$\sim_1 = \{(s,t) \mid \mathrm{sig}\,s = \mathrm{sig}\,t\}$$ -/
theorem equiv1_eq_ker_signature (step : SCM → Action → SCM → Resp → Prop) (s t : SCM) :
    ConcreteBridge.Equiv1 step s t ↔ fullSignature step s = fullSignature step t :=
  ⟨fun h => funext h, fun h a => congrFun h a⟩

/-! ### §43.3 ⭐⭐ 桥商的定量界 -/

/-- ⭐⭐ **桥商 $\le$ 签名像的基数**。

$$\bigl|\mathrm{SCM}/\sim_1\bigr| \le \bigl|\{\mathrm{sig}\,s\}\bigr|$$

**⟹ 即**：**桥商不超过「转移系统能区分出的签名种数」。**

**证明**：商 $\hookrightarrow$ 签名的像（子类型单射），故基数 $\le$。 -/
theorem equiv1_quot_card_le_signatures [Finite SCM]
    (step : SCM → Action → SCM → Resp → Prop) :
    Nat.card (Quotient (Setoid.ker (fullSignature step))) ≤
      Nat.card (Set.range (fullSignature step)) := by
  refine Nat.card_le_card_of_injective
    (fun q : Quotient (Setoid.ker (fullSignature step)) =>
      Quotient.liftOn q
        (fun s => (⟨fullSignature step s, s, rfl⟩ : Set.range (fullSignature step)))
        (fun a b hab => Subtype.ext hab)) ?_
  intro q₁ q₂ heq
  induction q₁ using Quotient.inductionOn with
  | _ a =>
    induction q₂ using Quotient.inductionOn with
    | _ b =>
      exact Quotient.sound (congrArg Subtype.val heq)

/-- ⭐⭐ **桥商的定量界**（本节核心）。

$$\bigl|\mathrm{SCM}/\sim_1\bigr| \le
  \bigl|\mathrm{Action} \to \mathcal{P}(\mathrm{Resp})\bigr|$$

**⟹ 即**：**桥商的规模由**动作数与响应数**共同界住**，
**与 `SCM` 的大小无关。**

**⚠ 这是**最优形式**：界只依赖 `Action` 与 `Resp`。** -/
theorem equiv1_quot_card_le_pow [Finite SCM] [Finite Action] [Finite Resp]
    (step : SCM → Action → SCM → Resp → Prop) :
    Nat.card (Quotient (Setoid.ker (fullSignature step))) ≤
      Nat.card (Action → Set Resp) :=
  calc Nat.card (Quotient (Setoid.ker (fullSignature step)))
      ≤ Nat.card (Set.range (fullSignature step)) :=
        equiv1_quot_card_le_signatures step
    _ ≤ Nat.card (Action → Set Resp) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-! ### §43.4 ⭐ 转移系统的单调性（签名层） -/

/-- ⭐ **签名的单调性**：若 `step` 的转移 $\subseteq$ `step'`，则签名 $\subseteq$。

**⟹ 即**：**转移系统越大，签名越大。** -/
theorem obsInt_mono_of_step_subset
    {step step' : SCM → Action → SCM → Resp → Prop}
    (h : ∀ s a s' r, step s a s' r → step' s a s' r) (s : SCM) (a : Action) :
    ConcreteBridge.ObsInt step s a ⊆ ConcreteBridge.ObsInt step' s a :=
  fun _ ⟨s', hs'⟩ => ⟨s', h s a s' _ hs'⟩

/-- ⭐ **转移系统单调性小结**（签名层，已证）。 -/
theorem signature_mono_of_step_subset
    {step step' : SCM → Action → SCM → Resp → Prop}
    (h : ∀ s a s' r, step s a s' r → step' s a s' r) (s : SCM) :
    ∀ a, ConcreteBridge.ObsInt step s a ⊆ ConcreteBridge.ObsInt step' s a :=
  fun a => obsInt_mono_of_step_subset h s a

/-! ### §43.5 ⭐⭐ **`Equiv1` 的单调性：不成立（反例）**

**第 43 轮曾在此处**如实登记**「未能写对」，本轮给出**结论**：
该单调性**不成立**。 -/

/- **占位说明**（`Equiv1` 的单调性讨论）。

**精确陈述**：若 `step ⊆ step'`（`step'` 转移更多），
则 $\sim_1^{\text{step}'} \ \subseteq\ \sim_1^{\text{step}}$
—— **即 `step'` 的等价更细。**

$$\text{step} \subseteq \text{step}' \implies
  \mathrm{Equiv1}\,\text{step}' \ \subseteq\ \mathrm{Equiv1}\,\text{step}$$

**⚠ 方向说明**（第 43 轮曾在此处出错）：
`step'` 转移更多 $\Rightarrow$ `ObsInt step'` 更大
$\Rightarrow$ **二者的相等更难成立** $\Rightarrow$ `Equiv1 step'` 更细。

**⭐ 正确证明路线**：
**不**用「`ObsInt step ⊆ ObsInt step'` 单向推导」——
因为从 `ObsInt step' s a` **回不到** `ObsInt step s a`。

**⟹ 正确的是用「过渡关系的等价」**：
定义 `Trans step a := {(s, s', r) | step s a s' r}`（逐动作的转移关系），
则 `Equiv1 step s t ⟺ ∀ a, ∀ s', (∃ r, step s a s' r) ↔ (∃ r, step t a s' r)` **不**够 ——
**须用「出边的 `(s', r)` 二元组集合」**，这**正是** `ObsInt` 的定义。

**⚠ 结论**：**`Equiv1` 关于 `step` 的单调性**不成立**（一般情形）** ——
**因为 `ObsInt` 只记录响应、不记录后继**，
故 **`step'` 更大时 `ObsInt step' s a` 更大，
但 `ObsInt step s a` 与 `ObsInt step t a` 的相等性**不受** `step'` 的约束。**

**⟹ 结论**：**该单调性**不成立** —— 见下方反例 `equiv1_not_mono`。**

**⚠ 这是本项目一贯纪律的体现**：
**第 43 轮如实登记「未能写对」，本轮给出**结论**（不成立 + 反例），
而非继续尝试一个**假的**命题。**

**⚠ 本段是结论与未做项的登记，不是定理**：先前此处有一条
`theorem equiv1_monotonicity_open : True`（`:= trivial`）作占位，
它不承载任何数学内容，已删除；真正的结论由下方反例 `equiv1_not_mono`
承载，本说明本身即为登记。 -/

/-- ⭐⭐ **反例**：`Equiv1` 关于 `step` **不**单调（一般情形）。

**构造**：`SCM := Bool`，`Action := Unit`，`Resp := Bool`。
- `step'`：`true` 与 `false` 都只在**同一响应**上转移（故 `Equiv1 step' true false` 成立）
- `step`（更小）：只保留 `true` 的转移 ——
  此时 `ObsInt step true _ = {true}`，而 `ObsInt step false _ = ∅`，
  **故 `Equiv1 step true false` 失败**。

**⚠ 即**：**`step'` 更大，但 `Equiv1 step'` 成立而 `Equiv1 step` 不成立** ——
**这与「更大 ⟹ 更细」相反。**

**⟹ 结论**：**该单调性**不成立**，本模块**如实登记**之。 -/
theorem equiv1_not_mono :
    ∃ (step step' : Bool → Unit → Bool → Bool → Prop),
      (∀ s a s' r, step s a s' r → step' s a s' r) ∧
      (∃ s t, ConcreteBridge.Equiv1 step' s t ∧ ¬ ConcreteBridge.Equiv1 step s t) := by
  -- `step`：只有 `true` 在响应 `true` 上转移
  refine ⟨(fun s _ s' r => s = true ∧ s' = true ∧ r = true),
          (fun _ _ _ _ => True), ?_, ?_⟩
  · intro s a s' r _
    trivial
  · refine ⟨true, false, ?_, ?_⟩
    · -- `Equiv1 step' true false`：两边的签名都是全集（每个 `r` 都有后继见证）
      intro a
      ext r
      exact ⟨fun _ => ⟨true, trivial⟩, fun _ => ⟨true, trivial⟩⟩
    · -- `¬ Equiv1 step true false`：`true` 的签名非空，`false` 的签名空
      intro h
      have h1 : (true : Bool) ∈ ConcreteBridge.ObsInt
          (fun s _ s' r => s = true ∧ s' = true ∧ r = true) true () :=
        ⟨true, rfl, rfl, rfl⟩
      have h2 := congrArg (fun S : Set Bool => (true : Bool) ∈ S) (h ())
      rw [h2] at h1
      obtain ⟨s', hs, _, _⟩ := h1
      exact Bool.noConfusion hs

end ConcreteBridgeQuant

end Fate
