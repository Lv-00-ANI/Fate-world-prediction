import FateWorld.Legacy.ViewOneCounterfactual

/-! ===========================================================================
  §31  ⭐⭐ **视角三能否支撑反事实**（原 `_probe_q28` 的正式化）

  **来源**：探针 `probes/_probe_q28.lean`（**不在构建内**）。

  ## 问题

  **视角三（换商）能否支撑反事实？充要条件是什么？**

  ## ⭐⭐ 答案：**能 ⟺ 桥核细于反事实核**

  $$\text{视角三支撑反事实} \iff \ker(\mathrm{bridge}) \subseteq \ker(\mathrm{Obs})$$

  **即**：**桥不可区分的 SCM，反事实必须也相同。**

  ## ⭐ 与视角一的**对称**

  | 视角 | 支撑反事实的条件 | 代价 |
  |---|---|---|
  | **一**（多值当资源）| 须 `Obs` 在纤维上**常值** | 输出**集合值** |
  | **三**（换商）| 须桥核**细于**反事实核 | **粘合**丢信息 |

  **⟹ 两者的条件互不相同，且各有代价。**

  ## ⭐ 修法：增广桥

  **若条件不满足，可**增广**桥（把 `Obs` 并入图坐标）使其满足** ——
  **这是「换商」视角的**自适应机制**。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace ViewThreeCounterfactual

universe u v w

variable {Graph : Type u} {SCM : Type v} {CF : Type w}

/-! ### §31.1 视角三的桥商 -/

/-- **集合值桥**。 -/
abbrev Bridge (Graph SCM : Type*) : Type _ := Graph → Set SCM

/-- **视角三的桥商**（同 `ThreeViews`）：`s₁ ~ s₂ ⟺` 在所有纤维中同进同出。 -/
def bridgeSetoid (bridge : Bridge Graph SCM) : Setoid SCM where
  r := fun s₁ s₂ => ∀ g, s₁ ∈ bridge g ↔ s₂ ∈ bridge g
  iseqv :=
    { refl := fun _ _ => Iff.rfl
      symm := fun h g => (h g).symm
      trans := fun h₁ h₂ g => (h₁ g).trans (h₂ g) }

/-! ### §31.2 ⭐⭐ 充要条件 -/

/-- ⭐⭐ **充分面**：若桥不可区分 $\implies$ 反事实相同，则反事实泛函**可下降到桥商**。

$$\ker(\mathrm{bridge}) \subseteq \ker(\mathrm{Obs}) \implies
  \exists\,\mathrm{Obs}_Q : \mathrm{SCM}/\sim \to \mathrm{CF}$$

**⟹ 即**：**视角三**支撑**反事实** ——
**`Obs` 在商上是良定义的（单值）。** -/
theorem bridge_supports_cf_of_finer (bridge : Bridge Graph SCM) (Obs : SCM → CF)
    (h : ∀ s t, (bridgeSetoid bridge).r s t → Obs s = Obs t) :
    ∃ ObsQ : Quotient (bridgeSetoid bridge) → CF,
      ∀ s, ObsQ (Quotient.mk _ s) = Obs s :=
  ⟨Quotient.lift Obs (fun _ _ hr => h _ _ hr), fun _ => rfl⟩

/-- ⭐⭐ **必要面**：若反事实泛函**可下降到桥商**，则桥核细于反事实核。

**⟹ 与充分面合起来给出**充要条件**。** -/
theorem cf_finer_of_bridge_supports (bridge : Bridge Graph SCM) (Obs : SCM → CF)
    (h : ∃ ObsQ : Quotient (bridgeSetoid bridge) → CF,
      ∀ s, ObsQ (Quotient.mk _ s) = Obs s) :
    ∀ s t, (bridgeSetoid bridge).r s t → Obs s = Obs t := by
  obtain ⟨ObsQ, hObsQ⟩ := h
  intro s t hst
  rw [← hObsQ s, ← hObsQ t, Quotient.sound hst]

/-- ⭐⭐ **充要条件（主定理）**。

$$\text{视角三支撑反事实} \iff \ker(\mathrm{bridge}) \subseteq \ker(\mathrm{Obs})$$

**即**：**桥不可区分的 SCM，反事实必须也相同。** -/
theorem supports_cf_iff (bridge : Bridge Graph SCM) (Obs : SCM → CF) :
    (∃ ObsQ : Quotient (bridgeSetoid bridge) → CF,
      ∀ s, ObsQ (Quotient.mk _ s) = Obs s) ↔
      (∀ s t, (bridgeSetoid bridge).r s t → Obs s = Obs t) :=
  ⟨cf_finer_of_bridge_supports bridge Obs, bridge_supports_cf_of_finer bridge Obs⟩

/-! ### §31.3 ⭐ 一般桥**不**支撑（反例） -/

/-- **诱导桥**：由正向映射 `induce` 定义的桥（视角二的标准构造）。 -/
def induceBridge (induce : SCM → Graph) : Bridge Graph SCM :=
  fun g => {s | induce s = g}

/-- ⭐ **诱导桥的商 = `induce` 的核**。 -/
theorem bridgeSetoid_induce_eq (induce : SCM → Graph) (s t : SCM) :
    (bridgeSetoid (induceBridge induce)).r s t ↔ induce s = induce t := by
  constructor
  · intro h
    have h1 : t ∈ induceBridge induce (induce s) := (h (induce s)).mp rfl
    exact (h1 : induce t = induce s).symm
  · intro h g
    constructor
    · intro hs
      change induce t = g
      rw [← h]
      exact hs
    · intro hs
      change induce s = g
      rw [h]
      exact hs

/-- ⭐⭐ **一般诱导桥**不**支撑反事实**（反例）。

**构造**：`induce := fun _ => ()`（常值），`Obs := id`。
则桥商是**万有关系**，而 `Obs` 单射 ——
**故条件 `ker(bridge) ⊆ ker(Obs)` 失败。**

**⟹ 即**：**视角三**不自动**支撑反事实** —— **须额外条件。** -/
theorem induce_bridge_fails_cf :
    ∃ (induce : Bool → Unit) (Obs : Bool → Bool),
      ¬ (∀ s t, (bridgeSetoid (induceBridge induce)).r s t → Obs s = Obs t) := by
  refine ⟨fun _ => (), id, ?_⟩
  intro h
  have hst : (bridgeSetoid (induceBridge (fun _ : Bool => ()))).r true false := by
    intro g
    constructor <;> intro _ <;> rfl
  exact Bool.noConfusion (h true false hst)

/-! ### §31.4 ⭐⭐ 修法：**增广桥** -/

/-- ⭐⭐ **增广桥**：把 `Obs` 并入图坐标。

$$\mathrm{augBridge}\,\mathrm{induce}\,\mathrm{Obs} : \mathrm{Graph} \times \mathrm{CF} \to \mathrm{Set}\,\mathrm{SCM}$$
$$\mathrm{augBridge}\,(g, c) := \{s \mid \mathrm{induce}\,s = g \wedge \mathrm{Obs}\,s = c\}$$

**⟹ 这是「换商」视角的**自适应机制**：
条件不满足时，**细化桥**使其满足。** -/
def augBridge (induce : SCM → Graph) (Obs : SCM → CF) : Bridge (Graph × CF) SCM :=
  fun gc => {s | induce s = gc.1 ∧ Obs s = gc.2}

/-- ⭐⭐ **增广桥必支撑反事实**（**无条件**）。

**⟹ 即**：**「换商」视角**总能**通过细化桥来支撑反事实** ——
**代价是商变得更细（粘合更少）。**

**这是与视角一的关键差别**：
- **视角一**：条件不满足就**只能给集合值**（无法修）
- **视角三**：条件不满足可以**增广桥**（可修，代价是商变细） -/
theorem augBridge_supports_cf (induce : SCM → Graph) (Obs : SCM → CF) :
    ∃ ObsQ : Quotient (bridgeSetoid (augBridge induce Obs)) → CF,
      ∀ s, ObsQ (Quotient.mk _ s) = Obs s := by
  apply bridge_supports_cf_of_finer
  intro s t hst
  have h1 : t ∈ augBridge induce Obs (induce s, Obs s) :=
    (hst (induce s, Obs s)).mp ⟨rfl, rfl⟩
  exact (h1 : induce t = induce s ∧ Obs t = Obs s).2.symm

/-! ### §31.5 ⭐⭐ 三视角的**对称总结** -/

/-- ⭐⭐ **三视角能否支撑反事实**（综合陈述）。

| 视角 | 支撑条件 | 不满足时 |
|---|---|---|
| **一**（多值当资源）| `Obs` 在纤维上常值 | **只能给集合值** |
| **三**（换商）| 桥核细于反事实核 | ⭐ **可增广桥来修** |

**⟹ 即**：**视角三比视角一**更有适应性**** ——
**它能通过细化桥来「自动」满足条件**，
**而视角一在条件失败时只能退回集合值。** -/
theorem three_views_summary (bridge : Bridge Graph SCM) (Obs : SCM → CF)
    (induce : SCM → Graph) :
    ((∃ ObsQ : Quotient (bridgeSetoid bridge) → CF,
        ∀ s, ObsQ (Quotient.mk _ s) = Obs s) ↔
      (∀ s t, (bridgeSetoid bridge).r s t → Obs s = Obs t)) ∧
      (∃ ObsQ : Quotient (bridgeSetoid (augBridge induce Obs)) → CF,
        ∀ s, ObsQ (Quotient.mk _ s) = Obs s) :=
  ⟨supports_cf_iff bridge Obs, augBridge_supports_cf induce Obs⟩

end ViewThreeCounterfactual

end Fate
