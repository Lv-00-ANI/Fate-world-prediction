import FateWorld.Legacy.MinimalSufficient

/-! ===========================================================================
  §26  ⭐⭐ **代理细化反事实等价**（原 `_probe_q18b` 的正式化）

  **来源**：探针 `probes/_probe_q18b.lean`（**不在构建内**）。

  ## 问题

  **若 $u$ 可部分观测（如通过代理变量），$\sim_{\text{cf}}$ 会变细吗？**

  ## ⭐⭐ 答案

  $$\boxed{\ \text{代理（对 } u \text{ 的部分观测）}
    \ \Longrightarrow\ \sim_{\text{cf}} \text{ 只会} \subseteq \text{-变细（或不变），绝不} \supset \text{-变粗}\ }$$

  **严格变细 $\iff$ 代理额外区分开了某两个「反事实相同、而代理不同」的 SCM。**

  | 代理 | 效果 |
  |---|---|
  | **常值**（无信息）| **不变** |
  | **单射**（完全钉住 $u$）| **细到相等** `=` |

  ## 形式化策略

  「$u$ 可部分观测」= 存在**代理泛函** $\mathrm{proxy} : \mathcal F \to M$。

  「用代理去细化」= **联合读取**：
  $$\mathrm{Obs}_{\mathrm{aug}} := (\mathrm{Obs},\ \mathrm{proxy})$$

  **⟹ 本问的全部数学内容 = 比较 $\ker(\mathrm{Obs})$ 与 $\ker(\mathrm{Obs}, \mathrm{proxy})$ 的粗细。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace ProxyRefinement

universe u v w

variable {SCM : Type u} {CF : Type v} {M : Type w}

/-! ### §26.1 载体：联合读取 -/

/-- **联合读取**：`Obs` 与 `proxy` 配对。

**⟹ 「用代理去细化反事实等价」的精确形式。** -/
def aug (Obs : SCM → CF) (proxy : SCM → M) : SCM → CF × M :=
  fun s => (Obs s, proxy s)

/-- **原始反事实等价** $\sim_{\text{cf}} = \ker(\mathrm{Obs})$。 -/
def cfRel (Obs : SCM → CF) : SCM → SCM → Prop := fun s t => Obs s = Obs t

/-- **加入代理后的反事实等价** $\sim_{\text{cf}}^{\mathrm{aug}}
  = \ker(\mathrm{aug}\,\mathrm{Obs}\,\mathrm{proxy})$。 -/
def cfRelAug (Obs : SCM → CF) (proxy : SCM → M) : SCM → SCM → Prop :=
  fun s t => aug Obs proxy s = aug Obs proxy t

/-! ### §26.2 ⭐⭐ 主定理一：代理**只会使等价变细** -/

/-- ⭐⭐ **主定理一（单调细化）**：$\ker(\mathrm{Obs}, \mathrm{proxy}) \subseteq \ker(\mathrm{Obs})$。

**这是「用 $u$ 的信息去区分 SCM」的全部方向性内容** ——
**代理不可能把两个原本反事实不同的 SCM 说成相同。** -/
theorem aug_refines (Obs : SCM → CF) (proxy : SCM → M) :
    ∀ s t, cfRelAug Obs proxy s t → cfRel Obs s t :=
  fun _ _ h => congrArg Prod.fst h

/-- ⭐ **等价类版**：对每个 `s`，代理后的等价类 $\subseteq$ 原等价类。 -/
theorem aug_class_subset (Obs : SCM → CF) (proxy : SCM → M) (s : SCM) :
    {t | cfRelAug Obs proxy s t} ⊆ {t | cfRel Obs s t} :=
  fun _ ht => aug_refines Obs proxy _ _ ht

/-! ### §26.3 ⭐⭐ 主定理二：**严格**变细的充要条件 -/

/-- **严格变细的见证**：一对反事实相同、而代理不同的 `s, t`。 -/
def RefinesStrictly (Obs : SCM → CF) (proxy : SCM → M) : Prop :=
  ∃ s t, cfRel Obs s t ∧ ¬ cfRelAug Obs proxy s t

/-- ⭐⭐ **主定理二（严格判据）**。

$$\text{严格变细} \iff \exists s\,t,\ \mathrm{Obs}\,s = \mathrm{Obs}\,t \wedge \mathrm{proxy}\,s \neq \mathrm{proxy}\,t$$

**⟹ 这是「$u$ 的部分观测确实带来了反事实区分力」的精确判据。** -/
theorem aug_strict_iff (Obs : SCM → CF) (proxy : SCM → M) :
    RefinesStrictly Obs proxy ↔
      ∃ s t, Obs s = Obs t ∧ proxy s ≠ proxy t := by
  constructor
  · rintro ⟨s, t, hcf, hnot⟩
    refine ⟨s, t, hcf, ?_⟩
    intro hp
    exact hnot (by simp only [cfRelAug, aug]; rw [hcf, hp])
  · rintro ⟨s, t, hcf, hp⟩
    refine ⟨s, t, hcf, ?_⟩
    intro h
    exact hp (congrArg Prod.snd h)

/-! ### §26.4 ⭐ 主定理三：常值代理 ⟹ **完全不细化** -/

/-- ⭐ **常值代理（无信息）不产生任何细化**。

**陈述**：若 `proxy` 是常值，则 $\sim_{\text{cf}}^{\mathrm{aug}} = \sim_{\text{cf}}$（**两方向**）。

**⟹ 即**：**「代理若完全不携带 $u$ 的信息，则等价关系纹丝不动」。** -/
theorem aug_const_noop (Obs : SCM → CF) (c : M) :
    ∀ s t, cfRelAug Obs (fun _ => c) s t ↔ cfRel Obs s t := by
  intro s t
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    show (Obs s, c) = (Obs t, c)
    rw [h]

/-! ### §26.5 ⭐⭐ 主定理四：单射代理 ⟹ **细到相等** -/

/-- ⭐⭐ **单射代理（完全观测）⟹ 反事实等价坍缩为相等**。

**陈述**：若 `proxy` 单射，则 $\sim_{\text{cf}}^{\mathrm{aug}}$ **恰是**类型相等。

**⟹ 与 §26.4 构成两端**：
| 代理 | 结果 |
|---|---|
| **常值** | **最粗**（不细化）|
| **单射** | **最细**（细到 `=`）|

**中间情形由 §26.3 的判据刻画。** -/
theorem aug_injective (Obs : SCM → CF) (proxy : SCM → M)
    (hinj : Function.Injective proxy) :
    ∀ s t, cfRelAug Obs proxy s t ↔ s = t := by
  intro s t
  constructor
  · intro h
    exact hinj (congrArg Prod.snd h)
  · intro h
    subst h
    rfl

/-! ### §26.6 ⭐ 复合律 -/

/-- ⭐ **两个代理可以复合**（依次细化）。

**陈述**：先加 `proxy₁` 再加 `proxy₂`，等价于一次加 `(proxy₁, proxy₂)`。

**⟹ 即**：**细化的「加信息」操作是**可结合**的** ——
**这与 `MinimalSufficient` 的「粗化」方向相反，但同样有良好的代数。** -/
theorem aug_trans (Obs : SCM → CF) (proxy₁ : SCM → M) {N : Type*} (proxy₂ : SCM → N) :
    ∀ s t, (cfRelAug (aug Obs proxy₁) proxy₂ s t ↔
      cfRelAug Obs (fun s => (proxy₁ s, proxy₂ s)) s t) := by
  intro s t
  constructor
  · intro h
    -- `h : ((Obs s, proxy₁ s), proxy₂ s) = ((Obs t, proxy₁ t), proxy₂ t)`
    have h1 : (Obs s, proxy₁ s) = (Obs t, proxy₁ t) := congrArg Prod.fst h
    have h2 : proxy₂ s = proxy₂ t := congrArg Prod.snd h
    rw [Prod.mk.injEq] at h1
    show (Obs s, (proxy₁ s, proxy₂ s)) = (Obs t, (proxy₁ t, proxy₂ t))
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨h1.1, h1.2, h2⟩
  · intro h
    have h1 : Obs s = Obs t := congrArg Prod.fst h
    have h2 : proxy₁ s = proxy₁ t := congrArg (Prod.fst ∘ Prod.snd) h
    have h3 : proxy₂ s = proxy₂ t := congrArg (Prod.snd ∘ Prod.snd) h
    show ((Obs s, proxy₁ s), proxy₂ s) = ((Obs t, proxy₁ t), proxy₂ t)
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨⟨h1, h2⟩, h3⟩

end ProxyRefinement

end Fate
