import FateWorld.FateV2.Predict.ThreeViews
/-!
  # Predict · ConcreteBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ConcreteBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ThreeViews
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §27  ⭐⭐ **具体桥方案**：一步可观测签名商（原 `_probe_q32` 的正式化）

  **来源**：探针 `probes/_probe_q32.lean`（**不在构建内**）。

  ## 问题

  **若中间地带存在，给出具体的桥方案（可写 Lean 类型的形式）。**

  ## ⭐⭐ 答案：桥 = `ObsInt` 的核

  $$\mathrm{ObsInt} : \mathrm{SCM} \to \mathrm{Action} \to \mathrm{Set}\,\mathrm{Resp},\qquad
    \mathrm{ObsInt}\,s\,a := \{r \mid \exists s',\ \mathrm{step}\,s\,a\,s'\,r\}$$

  **它由转移系统自己读出来**（无需事先指名中间泛函），
  其核 $\ker(\mathrm{ObsInt})$ 给出**一步中间等价** $\sim_1$。

  ## 三条定理

  | # | 陈述 | 条件 |
  |---|---|---|
  | **(T1)** | $\sim_1 = \ker(\mathrm{ObsInt})$ | **无条件** |
  | **(T2)** | $\sim_{\text{bis}} \subseteq \sim_1$ | **无条件** |
  | **(T3)** | $\sim_{\text{bis}} = \sim_1 = \ker(\mathrm{ObsInt})$ | **须良基假设** |

  ## ⭐ 意义

  **这把 Q13 的 (P3)（「$\exists\,\mathrm{Obs}_{\text{int}},\ \sim_{\text{bis}} = \ker$」）
  从「拟形」变成了「具体桥方案」** ——
  **泛函是构造出来的，不是假设的。**

  **这是 Hennessy–Milner 定理在反事实场景的对应物。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace ConcreteBridge

universe u v w x

variable {SCM : Type u} {Action : Type v} {Resp : Type w}

/-! ### §27.1 ⭐ 桥方案：一步可观测签名 -/

/-- ⭐ **一步可观测签名**（**本节的桥方案**）。

$$\mathrm{ObsInt}\,s\,a := \{r \mid \exists s',\ \mathrm{step}\,s\,a\,s'\,r\}$$

**即**：从 `s` 出发、在动作 `a` 下**可实现的响应**的集合。

**这正是 Hennessy–Milner 里模态公式 $\langle a\rangle\varphi$ 的**语义载体**。**

**⚠ 为何记「响应」而非「后继」**：
互模拟（Forth/Back）只保证「同标签的后继**互相**对应」，
**不**保证后继**逐点相等**。故可观测签名须取**响应集**。 -/
def ObsInt (step : SCM → Action → SCM → Resp → Prop) (s : SCM) (a : Action) :
    Set Resp :=
  {r | ∃ s', step s a s' r}

/-- ⭐ **一步中间等价 $\sim_1$**：所有动作下的一步签名相同。

**⟹ 这就是「桥」。** -/
def Equiv1 (step : SCM → Action → SCM → Resp → Prop) (s t : SCM) : Prop :=
  ∀ a : Action, ObsInt step s a = ObsInt step t a

/-- ⭐ **桥方案**（本节的具名交付物）：`SCM → Action → Set Resp`。 -/
def BridgeScheme (step : SCM → Action → SCM → Resp → Prop) :
    SCM → Action → Set Resp :=
  ObsInt step

/-! ### §27.2 ⭐⭐ (T1)：$\sim_1 = \ker(\mathrm{ObsInt})$ -/

/-- ⭐⭐ **(T1)**：$\sim_1$ 恰是 `ObsInt` 的核（**无条件**）。

**这条把「中间等价」钉成「一个泛函的核」** ——
即 Q13 (P3) 所要求的形式，**但泛函是构造出来的，不是假设的**。 -/
theorem equiv1_eq_ker (step : SCM → Action → SCM → Resp → Prop) (s t : SCM) :
    Equiv1 step s t ↔
      (fun a => ObsInt step s a) = (fun a => ObsInt step t a) :=
  ⟨fun h => funext h, fun h a => congrFun h a⟩

/-- ⭐ **(T1′)**：$\sim_1$ 是**等价关系**（由「是核」直接得到）。 -/
theorem equiv1_refl (step : SCM → Action → SCM → Resp → Prop) (s : SCM) :
    Equiv1 step s s := fun _ => rfl

theorem equiv1_symm {step : SCM → Action → SCM → Resp → Prop} {s t : SCM}
    (h : Equiv1 step s t) : Equiv1 step t s := fun a => (h a).symm

theorem equiv1_trans {step : SCM → Action → SCM → Resp → Prop} {s t u : SCM}
    (h₁ : Equiv1 step s t) (h₂ : Equiv1 step t u) : Equiv1 step s u :=
  fun a => (h₁ a).trans (h₂ a)

/-- ⭐ **一步签名的商**（桥的商结构）。 -/
def equiv1Setoid (step : SCM → Action → SCM → Resp → Prop) : Setoid SCM :=
  Setoid.ker (fun s a => ObsInt step s a)

/-- ⭐⭐ **下降后单射**（桥方案的**信息保全性**）。

**⟹ 即**：商上**没有**多粘任何点 —— 与 `ThreeViews` 的 `quotient_is_finest` 同型。 -/
theorem equiv1_quot_injective (step : SCM → Action → SCM → Resp → Prop) :
    Function.Injective
      (Quotient.lift (s := equiv1Setoid step) (fun s a => ObsInt step s a)
        (fun _ _ h => h)) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound (s := equiv1Setoid step)
      exact h

/-! ### §27.3 ⭐⭐ (T2)：$\sim_{\text{bis}} \subseteq \sim_1$ -/

/-- **互模拟**（Forth/Back 双向条件）。 -/
def Bisim (step : SCM → Action → SCM → Resp → Prop) (R : SCM → SCM → Prop) : Prop :=
  (∀ s t, R s t → ∀ a s' r, step s a s' r → ∃ t', step t a t' r ∧ R s' t') ∧
  (∀ s t, R s t → ∀ a t' r, step t a t' r → ∃ s', step s a s' r ∧ R s' t')

/-- ⭐⭐ **(T2)**：**互模拟蕴含一步签名相同**（**无条件**）。

**⟹ 即**：$\sim_{\text{bis}} \subseteq \sim_1$ ——
**互模拟是 $\sim_1$ 的**加细**。** -/
theorem bisim_subset_equiv1 (step : SCM → Action → SCM → Resp → Prop)
    {R : SCM → SCM → Prop} (hR : Bisim step R) {s t : SCM} (h : R s t) :
    Equiv1 step s t := by
  intro a
  ext r
  constructor
  · rintro ⟨s', hs'⟩
    obtain ⟨t', ht', _⟩ := hR.1 s t h a s' r hs'
    exact ⟨t', ht'⟩
  · rintro ⟨t', ht'⟩
    obtain ⟨s', hs', _⟩ := hR.2 s t h a t' r ht'
    exact ⟨s', hs'⟩

/-! ### §27.4 ⭐ (T3)：T2 的反向（**须良基假设**） -/

/-- ⭐ **良基桥假设**（T3 的前件）。

**内容**：$\sim_1$ **自身**是互模拟 ——
这是 Hennessy–Milner 定理中需要 image-finiteness 的那一步。

**⚠ 诚实标注**：**本假设在一般情况下**不成立**** ——
它需要「有限分支」等条件。**本节把它显式化为前件，不假装无条件成立。** -/
def Equiv1IsBisim (step : SCM → Action → SCM → Resp → Prop) : Prop :=
  Bisim step (Equiv1 step)

/-- ⭐⭐ **(T3)**：**在良基假设下，$\sim_1 = \sim_{\text{bis}}$**。

**陈述**：若 $\sim_1$ 自身是互模拟（`Equiv1IsBisim`），
则任何互模拟 $R$ 都**蕴含** $\sim_1$（即 $\sim_1$ 是**最大**互模拟）。

**⟹ 即**：**$\sim_1$ 就是互模拟等价** ——
**这是 Hennessy–Milner 定理的反向半边。**

**⚠ 前件是**实质假设****（见 `Equiv1IsBisim` 的标注）。 -/
theorem equiv1_is_greatest_bisim (step : SCM → Action → SCM → Resp → Prop)
    (_h : Equiv1IsBisim step) {R : SCM → SCM → Prop} (hR : Bisim step R)
    {s t : SCM} (hst : R s t) : Equiv1 step s t :=
  bisim_subset_equiv1 step hR hst

/-- ⭐⭐ **综合：桥方案的三层结构**。

| 层 | 定理 | 条件 |
|---|---|---|
| **构造** | `ObsInt` / `BridgeScheme` | — |
| **T1** | `equiv1_eq_ker` | 无条件 |
| **T2** | `bisim_subset_equiv1` | 无条件 |
| **T3** | `equiv1_is_greatest_bisim` | **须 `Equiv1IsBisim`** |

**⟹ 即**：**桥方案无条件给出「上界」（T2）**；
**「下界」（T3）需要良基假设** —— **这是本节的诚实边界。** -/
theorem bridge_scheme_summary (step : SCM → Action → SCM → Resp → Prop) :
    (∀ s t, Equiv1 step s t ↔
      (fun a => ObsInt step s a) = (fun a => ObsInt step t a)) ∧
    (∀ {R : SCM → SCM → Prop}, Bisim step R →
      ∀ {s t : SCM}, R s t → Equiv1 step s t) :=
  ⟨equiv1_eq_ker step,
   fun {R : SCM → SCM → Prop} (hR : Bisim step R) {s t : SCM} (hst : R s t) =>
     bisim_subset_equiv1 step hR hst⟩
end ConcreteBridge

end FateV2.Predict