import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-! ===========================================================================
  §20  ⭐⭐ **退守方案**：中间地带为空时的两条断言（原 `_probe_q33d` 的正式化）

  **来源**：探针 `probes/_probe_q33d.lean`（**不在构建内**）。

  ## 问题

  若中间地带不存在，**退守方案**是什么？

  ## ⭐ 答案：退守不是「放弃多值」，而是「把多值读法的立足点否定掉」

  ### 前件的精确刻画

  | 概念 | 定义 |
  |---|---|
  | **中间地带 $Z$** | $\{(\mathcal F, \mathcal F') \mid \mathcal F \sim_{\text{cf}} \mathcal F' \wedge \mathcal F \neq \mathcal F'\}$ |
  | **$Z = \varnothing$** | 即本节的**前件** |

  **⭐ 判据**：$Z = \varnothing \iff \Phi$ **单射**（`middleZone_empty_iff_injective`）。

  ### 两条断言

  | # | 内容 | 精确形式 |
  |---|---|---|
  | **(T1)** | 反事实需**完整** $\mathcal F$ | $Z = \varnothing \iff$ **纤维处处单点** |
  | **(T2)** | **桥必须单值化** | $Z = \varnothing \wedge$ 保真桥 $\implies$ **纤维单点** |

  ## ⭐⭐ 关键洞察

  **退守方案的两条都不是「假设」，而是**前件的等价改写****：
  * (T1)：$Z = \varnothing$ **等价于**「无被丢弃的坐标」
  * (T2)：在前件下，桥**不可能**多值 —— 多值即「纤维含两个不同 $\mathcal F$」，
    而保真性 + $\Phi$ 单射把它们**逼成相等**

  **⟹ 即**：**桥单值化是必然的、免费的**，不是因为加了假设。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace RetreatPlan

universe u v

variable {SCM : Type u} {CF : Type v}

/-! ### §20.1 载体：反事实泛函与中间地带 -/

/-- **反事实泛函 $\Phi$**。 -/
abbrev PhiFun (SCM CF : Type*) : Type _ := SCM → CF

/-- **反事实等价 $\sim_{\text{cf}}$**：$\Phi$ 的核。 -/
def CfEquiv (Phi : PhiFun SCM CF) (s t : SCM) : Prop := Phi s = Phi t

/-- **中间地带 $Z$**：反事实等价但 $\mathcal F$ 不等的点对。 -/
def MiddleZone (Phi : PhiFun SCM CF) : Set (SCM × SCM) :=
  {p | CfEquiv Phi p.1 p.2 ∧ p.1 ≠ p.2}

/-- **「中间地带不存在」= 本节的前件**。 -/
def MiddleZoneEmpty (Phi : PhiFun SCM CF) : Prop := MiddleZone Phi = ∅

/-! ### §20.2 ⭐ 前件 = $\Phi$ 单射 -/

/-- ⭐ **判据**：$Z = \varnothing \iff \Phi$ 单射。

**⟹ 故「中间地带不存在」这一前件**就是**「$\Phi$ 单射」。** -/
theorem middleZone_empty_iff_injective (Phi : PhiFun SCM CF) :
    MiddleZoneEmpty Phi ↔ Function.Injective Phi := by
  constructor
  · intro h s t hst
    by_contra hne
    have hmem : (s, t) ∈ MiddleZone Phi := ⟨hst, hne⟩
    rw [MiddleZoneEmpty] at h
    rw [h] at hmem
    exact Set.notMem_empty (s, t) hmem
  · intro h
    rw [MiddleZoneEmpty, MiddleZone]
    ext p
    constructor
    · intro hp
      exact absurd (h hp.1) hp.2
    · intro hp
      exact absurd hp (Set.notMem_empty p)

/-! ### §20.3 ⭐⭐ (T1)：反事实需**完整** $\mathcal F$ -/

/-- **纤维单点性**：$\Phi$ 的每个纤维是单点集。

**读作**：「反事实预测**完整决定**了 $\mathcal F$」——
即「$\mathcal F$ **无**被反事实读不到的坐标」。 -/
def FibersSingleton (Phi : PhiFun SCM CF) : Prop :=
  ∀ c : CF, ∀ s t : SCM, Phi s = c → Phi t = c → s = t

/-- ⭐⭐ **(T1) 主定理**：中间地带不存在 $\iff$ 反事实**完整决定** $\mathcal F$。

$$\boxed{\ \mathrm{MiddleZoneEmpty}\,\Phi \iff \mathrm{FibersSingleton}\,\Phi\ }$$

**⟹ 这就是「明确承认反事实需完整 $\mathcal F$」的**精确数学形式****：
退守方案的第一条**不是假设**，而是**前件的等价改写**。 -/
theorem retreat_T1_fullF (Phi : PhiFun SCM CF) :
    MiddleZoneEmpty Phi ↔ FibersSingleton Phi := by
  rw [middleZone_empty_iff_injective]
  constructor
  · intro h c s t hs ht
    exact h (hs.trans ht.symm)
  · intro h s t hst
    exact h (Phi s) s t rfl hst.symm

/-- ⭐ **(T1) 推论**：只要 $\mathcal F$ 有一个「反事实读不到的坐标」，退守前件就**失败**。 -/
theorem lost_coordinate_breaks_retreat (Phi : PhiFun SCM CF)
    (h : ∃ s t : SCM, s ≠ t ∧ Phi s = Phi t) : ¬ MiddleZoneEmpty Phi := by
  rw [middleZone_empty_iff_injective]
  rintro hinj
  obtain ⟨s, t, hne, heq⟩ := h
  exact hne (hinj heq)

/-! ### §20.4 ⭐⭐ (T2)：桥必须单值化 -/

/-- **桥**：`Graph → Set SCM`。 -/
abbrev Bridge (Graph SCM : Type*) : Type _ := Graph → Set SCM

/-- **保真桥（信实桥）**：桥的核**不粗于**反事实核。

**即**：落在同一纤维的 $\mathcal F$ 反事实**不可区分** ——
这是「按图取商能承载反事实」的**必要条件**。 -/
def FaithfulBridge {Graph : Type*} (bridge : Bridge Graph SCM) (Phi : PhiFun SCM CF) : Prop :=
  ∀ g s t, s ∈ bridge g → t ∈ bridge g → CfEquiv Phi s t

/-- **纤维单点**：每根纤维至多一点。 -/
def FibersAreSingletons {Graph : Type*} (bridge : Bridge Graph SCM) : Prop :=
  ∀ g s t, s ∈ bridge g → t ∈ bridge g → s = t

/-- ⭐⭐ **(T2) 主定理**：若中间地带为空（$\Phi$ 单射），则**任何保真桥的纤维是单点**。

$$\mathrm{MiddleZoneEmpty}\,\Phi \ \Rightarrow\ \mathrm{FaithfulBridge} \ \Rightarrow\
  \mathrm{FibersAreSingletons}$$

**⟹ 这就是「桥必须单值化」的严格含义**：
在前件下，桥**不可能**多值 —— 多值即「纤维含两个不同 $\mathcal F$」，
而**保真性 + $\Phi$ 单射把它们逼成相等**。 -/
theorem retreat_T2_bridge_single_valued {Graph : Type*}
    (Phi : PhiFun SCM CF) (bridge : Bridge Graph SCM)
    (hZ : MiddleZoneEmpty Phi) (hB : FaithfulBridge bridge Phi) :
    FibersAreSingletons bridge := by
  have hinj : Function.Injective Phi := (middleZone_empty_iff_injective Phi).mp hZ
  intro g s t hs ht
  exact hinj (hB g s t hs ht)

/-- ⭐ **(T2) 推论：单值选择无损**。

在前件下，任何「从每根纤维挑一个代表」的选择都**完全还原**桥 ——
即 `bridge g` 至多含一个元素。

**⟹ 这是视角一「纤维非单点 ⟹ 有损」的**前件翻转版**：
那里多值 ⟹ 有损；**这里单值 ⟹ 无损**。 -/
theorem retreat_T2_section_lossless {Graph : Type*}
    (Phi : PhiFun SCM CF) (bridge : Bridge Graph SCM)
    (hZ : MiddleZoneEmpty Phi) (hB : FaithfulBridge bridge Phi)
    {g : Graph} {s t : SCM} (hs : s ∈ bridge g) (ht : t ∈ bridge g) : s = t :=
  retreat_T2_bridge_single_valued Phi bridge hZ hB g s t hs ht

/-- ⭐ **(T2) 完整形式**：纤维恰是**子单点集**。

**即**：`bridge g` 至多含一个元素 —— **多值性彻底消失**。 -/
theorem retreat_T2_fiber_subsingleton {Graph : Type*}
    (Phi : PhiFun SCM CF) (bridge : Bridge Graph SCM)
    (hZ : MiddleZoneEmpty Phi) (hB : FaithfulBridge bridge Phi) (g : Graph) :
    ∀ s t, s ∈ bridge g → t ∈ bridge g → s = t :=
  fun s t hs ht => retreat_T2_bridge_single_valued Phi bridge hZ hB g s t hs ht

/-! ### §20.5 ⭐ 合成：退守方案 -/

/-- ⭐⭐ **退守方案（合成陈述）**。

**前件**：中间地带为空（$\iff \Phi$ 单射）。

**结论**：
1. **(T1)** 反事实**完整决定** $\mathcal F$（纤维处处单点）
2. **(T2)** 任何保真桥**必然单值化**（纤维单点）

**⟹ 即**：**退守不是「放弃多值」，而是「把多值读法的立足点（$\Phi$ 非单射）否定掉」。** -/
theorem q33_retreat_plan (Phi : PhiFun SCM CF) (hZ : MiddleZoneEmpty Phi) :
    FibersSingleton Phi ∧ Function.Injective Phi :=
  ⟨(retreat_T1_fullF Phi).mp hZ, (middleZone_empty_iff_injective Phi).mp hZ⟩

/-- ⭐ **退守与前件的双向刻画**：退守方案**成立** $\iff$ 中间地带为空。

**⟹ 即**：**退守方案的有效性**精确等价于**前件**，
**故它不是额外假设，是前件的重述。** -/
theorem q33_retreat_iff_empty (Phi : PhiFun SCM CF) :
    MiddleZoneEmpty Phi ↔ FibersSingleton Phi :=
  retreat_T1_fullF Phi

end RetreatPlan

end Fate
