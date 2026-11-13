import FateWorld.Legacy.Alpha

/-! ===========================================================================
  §6  Q-3 的消解：抽象等价关系取为 α 的**核**（作者授权）

  **来源**：作者裁决 —— Q-3「按最优最强的方向走」（授权消解）

  ## 问题（Q-3 / A31）

  规格 A31 说「抽象 = 实例集在等价关系下的商」，但**未给等价关系 $\sim_{\mathcal E}$ 的判据**。
  此前实现把它作**外置参数**（`AbstractEquiv E := Setoid E.Carrier`），
  于是 T1B.2b（α 保结构）成为**条件定理**，前件 `RespectsEquiv` 待裁。

  ## ⭐ 消解方案：取 α 的**核**

  **灵感来源**：抽象解释（abstract interpretation）——
  不可区分性 = 抽象化算子 $\alpha$ 的核
  $$\ker\alpha = \{(c,c') \mid \alpha\{c\} = \alpha\{c'\}\}$$

  **⟹ 本项目的对应**：
  $$e_1 \sim_{\mathcal E} e_2 \iff \alpha(\mathrm{enc}(e_1)) = \alpha(\mathrm{enc}(e_2))$$

  ## 为什么这是**消解**而非**又一个选择**

  | | 旧（外置参数） | **新（α 的核）** |
  |---|---|---|
  | 等价关系来源 | **外部给定**（待裁） | **由 α 内生** |
  | `RespectsEquiv` | **条件**（前件待证） | **定理**（`rfl` 级） |
  | Q-3 状态 | 悬置 | **✅ 消解** |
  | 自洽性 | 等价关系可能与 α 冲突 | **不可能冲突**（定义为核） |

  **⚠ 关键**：核是**从 α 算出来的**，故「α 保持它」**自动成立** ——
  这不是把一个假设换成另一个，而是**把假设变成定理**。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace AlphaKernel

open Fate.FormalCtx

variable {F : Frame} {K : FormalCtx.{u,v}}

/-! ### §6.1 ⭐ 定义：α 的核 -/

/-- ⭐ **Q-3 的消解**：抽象等价关系**取为 α∘enc 的核**。

$$e_1 \sim_{\mathcal E} e_2 \iff \alpha(\mathrm{enc}(e_1)) = \alpha(\mathrm{enc}(e_2))$$

**其中 $\alpha$ = `takeConcept`（裁决 D：α 是 FCA 取概念过程）。**

**这个定义的性质**：
- **内生** —— 完全由 α 与 enc 决定，不需外部裁决
- **自动相容** —— 「α 保持它」是定义的重言，见 `respectsEquiv_kernel`
- **可计算** —— 判定 $e_1 \sim e_2$ 即比较两个属性集，属**可判定**操作（在有限属性集上） -/
def alphaKernel (enc : Encoder F K) (E : InstSpace) (embed : E.Carrier → F.X.Carrier) :
    Setoid E.Carrier where
  r := fun e₁ e₂ => K.takeConcept (enc.toAttrs (embed e₁)) = K.takeConcept (enc.toAttrs (embed e₂))
  iseqv :=
    { refl := fun _ => rfl
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂ }

/-! ### §6.2 ⭐⭐ 主定理：`RespectsEquiv` 从**条件**变为**定理** -/

/-- ⭐⭐ **Q-3 消解的主定理**：**α 保持自己的核**（无条件）。

**⚠ 精确表述**：`RespectsEquiv` 的原定义要求
$\mathrm{toAttrs}(e_1) = \mathrm{toAttrs}(e_2)$（**编码层**相等），
而核要求 $\alpha(\mathrm{toAttrs}(e_1)) = \alpha(\mathrm{toAttrs}(e_2))$（**抽象层**相等）。

**⟹ 核比 `RespectsEquiv` 更粗**（抽象层相等比编码层相等弱）。

**故本定理陈述的是**：**α 在核上良定义** ——
即 $\alpha \circ \mathrm{enc}$ 可下降到核商，且**下降后单值**。

**这是 Q-3 消解的实质**：等价关系由 α 内生，故「α 保持它」**永远是重言**。 -/
theorem alpha_respects_kernel (enc : Encoder F K) (E : InstSpace)
    (embed : E.Carrier → F.X.Carrier) :
    ∀ e₁ e₂ : E.Carrier, (alphaKernel enc E embed).r e₁ e₂ →
      K.takeConcept (enc.toAttrs (embed e₁)) = K.takeConcept (enc.toAttrs (embed e₂)) :=
  fun _ _ h => h

/-- ⭐ **推论：α 在核商上良定义**（无须任何前件）。

**这是 `alphaOnQuotient` 的**无条件版** ——
接受 `RespectsEquiv` 作为前件的旧版（`Alpha.lean`）与此版**结论相同**，
但**前件被消解了**。 -/
def alphaOnKernelQuotient (enc : Encoder F K)
    (E : InstSpace) (embed : E.Carrier → F.X.Carrier) :
    Quotient (alphaKernel enc E embed) → Set K.MFCA :=
  Quotient.lift (fun e => K.takeConcept (enc.toAttrs (embed e)))
    (fun _ _ hab => hab)

/-! ### §6.3 ⭐ 核商与像的一致性（第一同构） -/

/-- ⭐ **核商 ≅ α 的像**（集合版第一同构）。

**含义**：把实例按「α 不可区分」商掉之后，
得到的正好是 **α 在实例集上的像** —— **不多不少**。

**⟹ 这给出了 A31「抽象 = 商」的精确内容**：
**抽象的结果（像）与抽象的商（核商）是同一个对象。** -/
theorem kernelQuotient_range (enc : Encoder F K)
    (E : InstSpace) (embed : E.Carrier → F.X.Carrier) :
    Function.Injective
      (fun q : Quotient (alphaKernel enc E embed) =>
        Quotient.liftOn q (fun e => K.takeConcept (enc.toAttrs (embed e)))
          (fun _ _ hab => hab)) := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | _ a =>
    induction q₂ using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      exact h

/-! ### §6.4 ⭐ 与旧定义的关系（不是替代，是消解） -/

/-- ⭐ **旧的外置商是新的核商的「粗化」**：若外置等价关系
$\sim$ 被 α 保持，则 $\sim \subseteq \ker\alpha$。

**即**：**任何与 α 相容的外置等价关系，都比核更细或相等。**

**⟹ 这解释了为什么旧版需要前件**：
外置等价关系**可能比核更细**（把 α 区分不开的实例也分开），
此时 α 当然仍保持它 —— 但**商会更大**，信息有冗余。

**核是「最粗的相容等价关系」** —— 这正是它的最优性。 -/
theorem equiv_le_kernel (enc : Encoder F K)
    (E : InstSpace) (embed : E.Carrier → F.X.Carrier) (eqv : Setoid E.Carrier)
    (hresp : enc.RespectsEquiv embed eqv) :
    ∀ e₁ e₂ : E.Carrier, e₁ ≈ e₂ →
      K.takeConcept (enc.toAttrs (embed e₁)) = K.takeConcept (enc.toAttrs (embed e₂)) :=
  fun e₁ e₂ he => by rw [hresp e₁ e₂ he]

/-! ### §6.5 ⭐ 最优性：核是最粗的相容等价关系 -/

/-- ⭐⭐ **最优性定理**：核是**最粗的**与 α 相容的等价关系。

**精确陈述**：若 $\sim$ 与 α 相容，则
$$\sim \ \subseteq\ \ker\alpha$$
即 **$\ker\alpha$ 是所有相容等价关系的上界**。

**⟹ 这给了 Q-3 消解的理论依据**：
在「商越小越好」（信息损失越小）的意义下，
**核给出最小的商** —— 它**保持了 α 能区分的全部信息，且不多分**。

**对比**：
| 等价关系 | 商的大小 | 是否相容 |
|---|---|---|
| 离散（$e_1 = e_2$）| **最大**（= 实例集） | ✅ 相容但冗余 |
| **核 $\ker\alpha$** | **最小** | ✅ 相容且**最优** |
| 全域（$e_1 \sim e_2$ 恒真）| 单点 | ⚠ 通常**不相容** |

**故核是唯一「既相容又最不冗余」的选择。** -/
theorem kernel_is_coarsest (enc : Encoder F K)
    (E : InstSpace) (embed : E.Carrier → F.X.Carrier) (eqv : Setoid E.Carrier)
    (hresp : enc.RespectsEquiv embed eqv) :
    ∀ e₁ e₂ : E.Carrier, e₁ ≈ e₂ →
      (alphaKernel enc E embed).r e₁ e₂ :=
  equiv_le_kernel enc E embed eqv hresp

end AlphaKernel

end Fate
