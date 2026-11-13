import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

/-! ===========================================================================
  §1  反事实等价与商结构（桥问题的突破）

  **来源**：作者问「能不能尝试突破这个局限换一下视角」，
  服务器 36 路 agent 的探索结论。

  **核心突破**：**不求 `𝔉|_G` 单值，而求 `𝔉|_G / ker(Obs)` 单值。**

  形式化：把「反事实」做成观测泛函 `Obs : SCM → CF`，则
  $$\sim_{\mathrm{cf}} = \ker(\text{Obs})$$
  商恰是 `Obs` 的像（集合版第一同构），商上 `Obs` **单值且单射**。

  **⚠ 未决**：中间地带（既非常值又非单射）的商基数**登记为不知道** ——
  等价于一般 SCM 的可识别性（中心开放问题）。

  **⚠ 无硬编码**（依作者裁决 Q-1）：本节不引入任何常数。
  =========================================================================== -/

namespace Fate

namespace Counterfactual

set_option linter.checkUnivs false

/-- **观测/反事实泛函**：把 SCM 送到其一切反事实预测（算法 3.1 的输出）。
    `CF` 是反事实预测空间；`Obs` 是「从机制读出全部反事实」的映射。 -/
structure Model where
  /-- 结构方程集（或其抽象）。 -/
  SCM : Type*
  /-- 反事实预测空间。 -/
  CF : Type*
  /-- 从机制读出全部反事实。 -/
  Obs : SCM → CF

variable (M : Model)

/-- **反事实等价 $\sim_{\mathrm{cf}}$**：`Obs` 的核关系（`_refs/14` 定理 D 的 $\sim_f$）。 -/
def cfSetoid : Setoid M.SCM := Setoid.ker M.Obs

/-- **商 $\mathfrak F|_G/\sim_{\mathrm{cf}}$**：纤维 `F` 按 $\sim_{\mathrm{cf}}$ 取商。 -/
def cfQuotient (F : Set M.SCM) : Type _ :=
  Quotient ((cfSetoid M).comap (Subtype.val : F → M.SCM))

/-! ## 一、商的基数上界（无条件结构定理） -/

/-- **商是有限型**（`SCM` 有限时）。这是 §六 一切基数论证的**前提实例**：
    商映射 `F ↠ 𝔉|_G/∼_cf` 满射，故商继承 `F` 的有限性。
    （原文件缺此实例，`faithful_iff_quotCard_eq` 的 `Nat.card_le_card_of_injective`
    要求 `[Finite β]` 因而无法合成——见 §六 注记。） -/
instance instFiniteCfQuotient [Finite M.SCM] (F : Set M.SCM) : Finite (cfQuotient M F) :=
  Finite.of_surjective (Quotient.mk _)
    (fun q => Quotient.inductionOn q fun x => ⟨x, rfl⟩)

/-- **商的基数不超过原纤维**：$\#(\mathfrak F|_G/\sim_{\mathrm{cf}}) \le \#\mathfrak F|_G$
    （有限化陈述；无穷时退化为 `Nat.card = 0` 的平凡上界）。 -/
theorem cfQuotient_card_le [Finite M.SCM] (F : Set M.SCM) :
    Nat.card (cfQuotient M F) ≤ Nat.card F := by
  classical
  exact Nat.card_le_card_of_surjective (Quotient.mk _)
    (fun q => Quotient.inductionOn q fun x => ⟨x, rfl⟩)

/-! ## 二、单值性的精确刻画：商单点 ⟺ `Obs` 常值 -/

/-- **商单点 ⟺ 反事实泛函在 $\mathfrak F|_G$ 上常值**。
    与 Q18 判词衔接：单值的代价是 `Obs` 已在纤维上不可区分——
    **单值性不来自商，而来自 `Obs` 本身。** -/
theorem cfQuotient_subsingleton_iff (F : Set M.SCM) :
    Subsingleton (cfQuotient M F) ↔
      ∀ s ∈ F, ∀ t ∈ F, M.Obs s = M.Obs t := by
  constructor
  · intro h s hs t ht
    have hsub : Subsingleton (cfQuotient M F) := h
    have : (Quotient.mk _ ⟨s, hs⟩ : cfQuotient M F) =
           (Quotient.mk _ ⟨t, ht⟩ : cfQuotient M F) := hsub.elim _ _
    exact Quotient.exact this
  · intro h
    refine ⟨fun a b => ?_⟩
    refine Quotient.inductionOn₂ a b (fun x y => ?_)
    exact Quotient.sound (h x.1 x.2 y.1 y.2)

/-! ## 三、信息保持：商上的 `Obs` 单值且单射 -/

/-- **商上的下降**：`Obs` 沿 $\sim_{\mathrm{cf}}$ 常值，下降到商。 -/
def obsOnQuot (F : Set M.SCM) : cfQuotient M F → M.CF :=
  Quotient.lift (fun x : F => M.Obs x.1) (fun _ _ h => h)

/-- **下降后单值**：商上 `Obs` 是函数。 -/
theorem obsOnQuot_single_valued (F : Set M.SCM) (a : cfQuotient M F) :
    ∃! c : M.CF, obsOnQuot M F a = c :=
  ⟨obsOnQuot M F a, rfl, fun _ h => h.symm⟩

/-- **下降后单射**：商恰是 `Obs` 的核，故 `obsOnQuot` 单射——
    商没有丢失 `Obs` 能区分的任何信息，也没有多粘任何点。 -/
theorem obsOnQuot_injective (F : Set M.SCM) :
    Function.Injective (obsOnQuot M F) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      exact h

/-- **商 $\cong$ 像**（集合版第一同构）：$\mathfrak F|_G/\sim_{\mathrm{cf}}$
    与 `Obs` 在 $\mathfrak F|_G$ 上像的**基数相同**。 -/
theorem cfQuotient_card_eq_image [Finite M.SCM] (F : Set M.SCM) :
    Nat.card (cfQuotient M F) = Nat.card (Set.range (obsOnQuot M F)) := by
  classical
  exact Nat.card_congr (Equiv.ofInjective (obsOnQuot M F) (obsOnQuot_injective M F))

/-! ## 三·补、⭐ 泛化：**任意** `Setoid` 商上的单射性

    上文 §三 的 `Obs` 单射性只针对**特定的** `∼_cf = ker Obs` 商。
    本节把它泛化到**任意** `Setoid r`：

    * 下降存在（`Obs` 沿 `r` 常值）⟺ `r ≤ ker Obs`；
    * 下降单射 ⟸ `ker Obs ≤ r`（**单向**，见下）。

    ⚠ **重要更正**（实测）：原文件把第二条写成**双向**的
    `Injective (obsOnQuotBy …) ↔ ker Obs ≤ r`，该命题**为假**。
    反例（Lean 已验证）：取 `SCM := Bool`、`Obs := fun _ => ()`、
    `F := {true}`（单点纤维）、`r := ⊥`（相等）。则
    `r ≤ ker Obs` 成立、商是单点子商故 `obsOnQuotBy` 单射，
    但 `ker Obs ≤ r` 要求 `true = false`，为假。
    **根因**：单射性只看得见 `F` **之内**的信息，而 `ker Obs ≤ r` 是
    `M.SCM` 上的**整体**陈述；当 `F` 不meet每个 `r`-类时二者脱钩。

    正确的充要刻画必须把 `ker Obs ≤ r` **限制到 `F` 上**
    （见 `obsOnQuotBy_injective_iff_on_F`）。 -/

/-- **任意 `Setoid` 上的商**：纤维 `F` 按**给定** `Setoid r`（不预设是 `ker Obs`）取商。
    `r` 视为 `M.SCM` 上的关系，经 `Subtype.val` 拉回到 `F` 上。 -/
def quotBySetoid (r : Setoid M.SCM) (F : Set M.SCM) : Type _ :=
  Quotient (r.comap (Subtype.val : F → M.SCM))

/-- **下降存在 ⟺ `r ≤ ker Obs`**：`Obs` 能沿 `r` 降到商上，当且仅当
    `r` 比观测核**更细**（每个 `r`-类内 `Obs` 常值）。
    这是 `Quotient.lift` 可定义性的**精确**条件。 -/
theorem obs_descends_iff (r : Setoid M.SCM) :
    (∀ a b : M.SCM, r a b → M.Obs a = M.Obs b) ↔
      r ≤ Setoid.ker M.Obs := by
  rfl

section
variable (r : Setoid M.SCM)

/-- **满足下降条件时的下降映射**（`Quotient.lift`）。 -/
def obsOnQuotBy (h : r ≤ Setoid.ker M.Obs) (F : Set M.SCM) :
    quotBySetoid M r F → M.CF :=
  Quotient.lift (fun x : F => M.Obs x.1)
    (fun _ _ hab => h hab)

/-- ⭐ **泛化的单射性（单向）**：对**任意** `Setoid r`，若 `ker Obs ≤ r`
    则下降**单射**。这是 §三 `obsOnQuot_injective` 的**无条件泛化**：
    取 `r = ker Obs` 时 `≤` 自反，即回收原结论。 -/
theorem obsOnQuotBy_injective_of_le (h : r ≤ Setoid.ker M.Obs) (F : Set M.SCM)
    (hle : Setoid.ker M.Obs ≤ r) :
    Function.Injective (obsOnQuotBy M r h F) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      exact hle hab

/-- ⭐⭐ **正确的充要刻画**：下降**单射 ⟺ `ker Obs` 在 `F` 上被 `r` 包含**。
    即单射性只刻画 `F` **之内**的粘合行为；`F` 之外的 `r`-类完全不可见。
    这正是把 `obsOnQuotBy_injective_of_le` 补成双向的**唯一**正确方式。 -/
theorem obsOnQuotBy_injective_iff_on_F (h : r ≤ Setoid.ker M.Obs) (F : Set M.SCM) :
    Function.Injective (obsOnQuotBy M r h F) ↔
      ∀ a b : M.SCM, a ∈ F → b ∈ F → M.Obs a = M.Obs b → r a b := by
  constructor
  · intro hinj a b ha hb hab
    have heq : (Quotient.mk (r.comap (Subtype.val : F → M.SCM)) (⟨a, ha⟩ : F) :
          quotBySetoid M r F) =
        (Quotient.mk (r.comap (Subtype.val : F → M.SCM)) (⟨b, hb⟩ : F) :
          quotBySetoid M r F) := by
      apply hinj
      show M.Obs (⟨a, ha⟩ : F).1 = M.Obs (⟨b, hb⟩ : F).1
      exact hab
    show r a b
    exact Quotient.exact (s := r.comap (Subtype.val : F → M.SCM)) heq
  · intro hle a b hab
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        exact hle x.1 y.1 x.2 y.2 hab

/-- **特例回收**：取 `r := ker Obs` 时，`F` 上的条件 `ker Obs a b → ker Obs a b`
    平凡成立，故泛化定理退化为 §三 的单射性（此处直接给出，不依赖上条）。 -/
theorem obsOnQuotBy_ker_injective (F : Set M.SCM) :
    Function.Injective (obsOnQuotBy M (Setoid.ker M.Obs) le_rfl F) :=
  obsOnQuotBy_injective_of_le M (Setoid.ker M.Obs) le_rfl F le_rfl

end

/-! ## 四、把 `第6问` §4.2 的「中间地带」编码为真值三分 -/

/-- **情形 A（塌缩 / 单值）**：`Obs` 在 $\mathfrak F|_G$ 上常值 ⟹ 商单点。 -/
def Collapse (F : Set M.SCM) : Prop := ∀ s ∈ F, ∀ t ∈ F, M.Obs s = M.Obs t

/-- **情形 B（完全可区分 / 单射）**：`Obs` 在 $\mathfrak F|_G$ 上单射 ⟹ 商 $\cong\mathfrak F|_G$。 -/
def Faithful (F : Set M.SCM) : Prop := ∀ s ∈ F, ∀ t ∈ F, M.Obs s = M.Obs t → s = t

/-- **情形 C（中间地带）**：既非常值、又非单射。
    正是 `第6问` §4.2「(ii) 不成立但无全干预同分布反例」的抽象形态。 -/
def MiddleZone (F : Set M.SCM) : Prop := ¬ Collapse M F ∧ ¬ Faithful M F

/-- **情形 A ⟹ 商单值**（问题 16 的「能」支，但代价是信息全失）。 -/
theorem collapse_quot_subsingleton (F : Set M.SCM) (h : Collapse M F) :
    Subsingleton (cfQuotient M F) :=
  (cfQuotient_subsingleton_iff M F).mpr h

/-- **情形 B ⟹ 商与纤维等势**（「不能」支：$\#\mathfrak F|_G\ge2$ 时商多值）。 -/
theorem faithful_quot_card_eq [Finite M.SCM] (F : Set M.SCM) (h : Faithful M F) :
    Nat.card (cfQuotient M F) = Nat.card F := by
  classical
  let f : F → cfQuotient M F := fun s => Quotient.mk _ s
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact h x.1 x.2 y.1 y.2 (Quotient.exact hxy)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact ⟨x, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm

/-- **三情形穷尽**：任一 `Obs` 必落于 A、B、C 之一。 -/
theorem trichotomy (F : Set M.SCM) :
    Collapse M F ∨ Faithful M F ∨ MiddleZone M F := by
  by_cases hc : Collapse M F
  · exact Or.inl hc
  · by_cases hf : Faithful M F
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr ⟨hc, hf⟩)

/-- **情形 B 且纤维至少含两点 ⟹ 商不单点**：桥在该商上**不单值**。
    这是问题 16「能否单值」的否定见证（在忠实档）。 -/
theorem faithful_quot_nontrivial {s t : M.SCM} (hst : s ≠ t)
    (h : Faithful M ({s, t} : Set M.SCM)) :
    ¬ Subsingleton (cfQuotient M ({s, t} : Set M.SCM)) := by
  intro hs
  have heq : (Quotient.mk _ ⟨s, by simp⟩ : cfQuotient M ({s, t} : Set M.SCM)) =
             (Quotient.mk _ ⟨t, by simp⟩ : cfQuotient M ({s, t} : Set M.SCM)) :=
    hs.elim _ _
  exact hst (h s (by simp) t (by simp) (Quotient.exact heq))

/-! ## 五、情形 B 的最小实例：`SCM := ℝ`、`Obs := id`、纤维含 $\ge2$ 点

    此时商 $\cong$ 纤维，故 $\#\text{商} = \#\mathfrak F|_G \ge 2$，
    **桥不单值**——与 `桥文件` 命题 2.2(ii) 的 $2^{\aleph_0}$ 下界同型。 -/

/-- 情形 B 见证：`Obs := id` 时商不单点（取 `F = {0, 1}`）。 -/
theorem real_id_not_subsingleton :
    ¬ Subsingleton
      (cfQuotient ⟨ℝ, ℝ, id⟩ ({0, 1} : Set ℝ)) := by
  apply faithful_quot_nontrivial ⟨ℝ, ℝ, id⟩ (s := 0) (t := 1) (by norm_num)
  intro s _ t _ h
  exact h

/-! ## 六、多情形推广：按核（商）的基数分层

    三情形 `A/B/C` 其实是**商基数**的一个 2 比特影子。精确地说，令
    $$\kappa(M,F) := \#\bigl(\mathfrak F|_G / \sim_{\mathrm{cf}}\bigr)$$
    即 `Obs` 在纤维上取到的**不同反事实值的个数**。则

    | 情形 | 等价刻画 |
    |---|---|
    | `Collapse` | `κ = 1`（商单点）|
    | `Faithful` | `κ = #F`（商 ≅ 纤维）|
    | `MiddleZone` | `1 < κ < #F` |

    于是「三情形」只是 `κ` 分层中 `{1} ∪ {=#F}` 这两个退化层的并。
    下面给出**任意有限档数** `n` 的穷尽劈分（`cardStratification`），
    并证明 `κ` 把 `A/B/C` 精确刻画（`trichotomy_via_quotCard`）——
    即 `κ` 是比三情形更细、且**完全**的不变量（在纤维基数固定时，
    `κ` 确定商等价类型）。**⟹ 推广成立**：档数 `n` 可任意升高。

    **⚠ 修复注记**：`faithful_iff_quotCard_eq` 的原证明在
    `Nat.card_le_card_of_injective` 处要求 `[Finite (cfQuotient M F)]`，
    原文件未提供该实例故报 `failed to synthesize Finite`。
    本文件在 §一 补 `instFiniteCfQuotient`，并改用
    「满射 + 基数相等 ⟹ 单射」的显式有限型论证。 -/

/-- **商基数（核基数）**：`Obs` 在纤维 `F` 上取到的不同值个数。
    这是比 `Collapse/Faithful` 更细的不变量——三情形是它的退化读法。 -/
noncomputable def quotCard (F : Set M.SCM) : ℕ := Nat.card (cfQuotient M F)

/-- **辅助（有限型）**：有限型之间的满射若基数不降，则必单射。
    证明：去掉一个点后满射性保持，而基数严格下降，矛盾。 -/
theorem injective_of_surjective_of_card_le {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (hsurj : Function.Surjective f)
    (hcard : Nat.card α ≤ Nat.card β) : Function.Injective f := by
  classical
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  have hcard' : Fintype.card α ≤ Fintype.card β := by
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  clear hcard
  intro x y hxy
  by_contra hne
  have hsurj' : Function.Surjective (fun z : {z : α // z ≠ x} => f z.1) := by
    intro b
    obtain ⟨z, hz⟩ := hsurj b
    by_cases hzx : z = x
    · subst hzx
      refine ⟨⟨y, fun h => hne h.symm⟩, ?_⟩
      show f y = b
      rw [← hxy]; exact hz
    · exact ⟨⟨z, hzx⟩, hz⟩
  have hle := Fintype.card_le_of_surjective (fun z : {z : α // z ≠ x} => f z.1) hsurj'
  have hlt : Fintype.card {z : α // z ≠ x} < Fintype.card α := by
    have h1 : Fintype.card {z : α // z ≠ x}
        = Fintype.card α - Fintype.card {z : α // z = x} :=
      Fintype.card_subtype_compl (fun z : α => z = x)
    have h2 : Fintype.card {z : α // z = x} = 1 :=
      Fintype.card_ofSubsingleton ⟨x, rfl⟩
    have h3 : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
    omega
  omega

/-- ⭐ **塌缩 ⟺ 商基数 `= 1`**（空纤维时 `κ = 0`，也满足 `Collapse`）。 -/
theorem collapse_iff_quotCard_eq_one (F : Set M.SCM) :
    Collapse M F ↔ F.Nonempty ∧ quotCard M F = 1 ∨ F = ∅ := by
  constructor
  · intro h
    by_cases hempty : F = ∅
    · exact Or.inr hempty
    · left
      obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      refine ⟨⟨s, hs⟩, ?_⟩
      have hsub : Subsingleton (cfQuotient M F) := collapse_quot_subsingleton M F h
      haveI : Nonempty (cfQuotient M F) := ⟨Quotient.mk _ ⟨s, hs⟩⟩
      rw [quotCard]
      exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
  · rintro (⟨⟨s, hs⟩, hcard⟩ | hempty)
    · have hsub : Subsingleton (cfQuotient M F) :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      intro a ha b hb
      have : (Quotient.mk _ (show F from ⟨a, ha⟩)) =
             (Quotient.mk _ (show F from ⟨b, hb⟩)) := hsub.elim _ _
      exact Quotient.exact this
    · subst hempty; intro a ha; exact absurd ha (by simp)

/-- ⭐ **忠实 ⟺ 商基数 `= #F`**（商与纤维等势，即 `Obs` 在纤维上单射）。 -/
theorem faithful_iff_quotCard_eq [Finite M.SCM] (F : Set M.SCM) :
    Faithful M F ↔ quotCard M F = Nat.card F := by
  constructor
  · intro h
    rw [quotCard]; exact faithful_quot_card_eq M F h
  · intro h s hs t ht hst
    -- 商映射 `F ↠ 商` 满射，且 `h` 给出两基数相等；
    -- 由 `injective_of_surjective_of_card_le` 得商映射单射，从而 `s = t`。
    have hsurj : Function.Surjective
        (fun x : F => (Quotient.mk _ x : cfQuotient M F)) :=
      fun q => Quotient.inductionOn q fun x => ⟨x, rfl⟩
    haveI : Finite (cfQuotient M F) := instFiniteCfQuotient M F
    have hinj : Function.Injective
        (fun x : F => (Quotient.mk _ x : cfQuotient M F)) :=
      injective_of_surjective_of_card_le _
        (by simpa [quotCard] using hsurj) (by show Nat.card F ≤ quotCard M F; rw [h])
    exact congrArg Subtype.val (hinj (Quotient.sound (show
      (Setoid.ker M.Obs) (⟨s, hs⟩ : F).1 (⟨t, ht⟩ : F).1 from hst)))

/-- ⭐⭐ **多情形穷尽（按核基数分层）**：对任意档数 `n : ℕ`，商基数 `κ` 必落在

$$\kappa \in \{0\} \cup \{1,\dots,n\} \cup \{n+1, n+2, \dots\}$$

三段之一。取 `n = 1`、剔除空纤维后，即回收三情形 `A/B/C`（见 `trichotomy`）。
这是「三情形」向「任意 `n` 情形」的**直接推广**：档数可任意升高。 -/
theorem cardStratification (F : Set M.SCM) (n : ℕ) :
    quotCard M F = 0
      ∨ (1 ≤ quotCard M F ∧ quotCard M F ≤ n)
      ∨ n < quotCard M F := by
  rcases Nat.eq_zero_or_pos (quotCard M F) with h | h
  · exact Or.inl h
  · rcases Nat.lt_or_ge n (quotCard M F) with hlt | hle
    · exact Or.inr (Or.inr hlt)
    · exact Or.inr (Or.inl ⟨h, hle⟩)

/-- ⭐⭐ **三情形 = 核基数分层的退化读法**：把 `trichotomy` 完全用 `quotCard` 重述，
显示 `A/B/C` 恰对应 `κ` 的三个区域。这让「三」与「多」在同一组不变量下统一。

    **⚠ 成立性核查**（原证明在 338/349/357–359 行有 5 处笔误，但**陈述为真**）：
    * 空纤维：`κ = 0 = #F`，第二支成立；
    * 塌缩且非空：`κ = 1`，第一支成立；
    * 忠实：`κ = #F`，第二支成立；
    * 中间地带：`¬Faithful` 给 `κ ≠ #F`，配 `cfQuotient_card_le` 得 `κ < #F`；
      `¬Collapse` 配 `collapse_iff_quotCard_eq_one` 及 `F ≠ ∅`（故 `F.Nonempty`）
      得 `κ ≠ 1`，且 `F.Nonempty` 给 `κ ≥ 1`，故 `1 < κ`。`omega` 收尾。 -/
theorem trichotomy_via_quotCard [Finite M.SCM] (F : Set M.SCM) :
    (F.Nonempty ∧ quotCard M F = 1)
      ∨ quotCard M F = Nat.card F
      ∨ (1 < quotCard M F ∧ quotCard M F < Nat.card F) := by
  classical
  rcases trichotomy M F with hc | hf | hmz
  · -- 塌缩档：`F = ∅` 时走第二支（`κ = 0 = #F`），否则走第一支
    rcases (collapse_iff_quotCard_eq_one M F).mp hc with ⟨hne, h1⟩ | hemp
    · exact Or.inl ⟨hne, h1⟩
    · -- `F = ∅`：商与纤维都空，故 `κ = 0 = #F`
      right; left
      haveI : IsEmpty F := by rw [hemp]; infer_instance
      haveI : IsEmpty (cfQuotient M F) :=
        ⟨fun q => Quotient.inductionOn q fun x => (isEmptyElim x : False)⟩
      rw [quotCard, Nat.card_eq_zero.mpr (Or.inl inferInstance),
        Nat.card_eq_zero.mpr (Or.inl inferInstance)]
  · -- 忠实档：`κ = #F`
    exact Or.inr (Or.inl ((faithful_iff_quotCard_eq M F).mp hf))
  · -- 中间地带：`¬Collapse ∧ ¬Faithful`，证 `1 < κ < Nat.card F`
    obtain ⟨hnc, hnf⟩ := hmz
    have hle : quotCard M F ≤ Nat.card F := cfQuotient_card_le M F
    have hne_card : quotCard M F ≠ Nat.card F :=
      fun heq => hnf ((faithful_iff_quotCard_eq M F).mpr heq)
    have hlt_card : quotCard M F < Nat.card F := lt_of_le_of_ne hle hne_card
    -- `F.Nonempty`：`¬Collapse` 蕴含 `F ≠ ∅`
    have hne_empty : F ≠ ∅ := by
      intro hemp
      exact hnc (fun a ha => absurd ha (by simp [hemp]))
    have hnonempty : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hne_empty
    -- `κ ≠ 0`：`F.Nonempty` ⟹ 商非空 ⟹ `κ ≥ 1`
    have hne0 : quotCard M F ≠ 0 := by
      rw [quotCard]
      exact Nat.card_ne_zero.mpr
        ⟨⟨Quotient.mk _ ⟨Classical.choose hnonempty, Classical.choose_spec hnonempty⟩⟩,
          inferInstance⟩
    -- `κ ≠ 1`：否则 `Collapse` 成立
    have hne1 : quotCard M F ≠ 1 :=
      fun h1 => hnc ((collapse_iff_quotCard_eq_one M F).mpr (Or.inl ⟨hnonempty, h1⟩))
    refine Or.inr (Or.inr ⟨?_, hlt_card⟩)
    omega

end Counterfactual

end Fate
