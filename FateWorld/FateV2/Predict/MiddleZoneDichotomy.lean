import FateWorld.FateV2.Predict.RetreatPlan
/-!
  # Predict · MiddleZoneDichotomy

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MiddleZoneDichotomy.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RetreatPlan
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §22  ⭐⭐ **中间地带的二分法**（原 `_probe_q25` 的正式化，本节为**收束**）

  **来源**：探针 `probes/_probe_q25.lean`（**不在构建内**）。

  ## 问题

  **能否证明中间地带为空**（即 $\sim_{\text{cf}} \iff \mathcal F$ 相同）？

  ## ⭐⭐ 答案：**判据**（本节的收束性结论）

  $$\boxed{\ Z = \varnothing \iff \Phi\ \text{单射} \iff \mathcal F\ \text{无「反事实读不到」的坐标}\ }$$

  **两侧都有具体见证**：

  | 侧 | 读法 | 见证 |
  |---|---|---|
  | **非空** | **结构模型读法 S**（$\mathcal F$ = 结构方程 + 内部表示）| `middle_zone_not_empty` |
  | **空** | **反事实函数读法 F**（$\mathcal F$ = 反事实函数本身）| `readingF_empty` |

  ## ⭐ 关键洞察

  **「$Z$ 非空」不是无条件的** —— 它**恰好等价于 $\Phi$ 非单射**。

  **只要把 $\mathcal F$ 缩到「反事实函数本身」，$Z$ 立刻为空。**

  **⟹ 即**：**中间地带的非空性是一个**读法依赖**的事实** ——
  它取决于「$\mathcal F$ 携带多少反事实读不到的自由度」。

  ## ⭐ 与前三节的**收束关系**

  | 节 | 内容 |
  |---|---|
  | `CounterfactualStrictness`（16）| $\sim_{\text{cf}}$ **严格弱于** $=$（读法 S）|
  | `EquivalenceLevels`（17）| 三等价层级 $\sim_{\text{cf}} \subseteq \sim_{\text{int}} \subseteq \sim_{\text{obs}}$ |
  | `RetreatPlan`（20）| 中间地带**为空**时的退守方案 |
  | **本节（22）** | ⭐ **统一的二分判据** |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace MiddleZoneDichotomy

universe u v

variable {SCM : Type u} {CF : Type v}

/-! ### §22.1 载体（与 `RetreatPlan` 逐字同型） -/

/-- **反事实泛函 $\Phi$**。 -/
abbrev PhiFun (SCM CF : Type*) : Type _ := SCM → CF

/-- **反事实等价**。 -/
def CfEquiv (Phi : PhiFun SCM CF) (s t : SCM) : Prop := Phi s = Phi t

/-- **反事实不等价**。 -/
def CfNotEquiv (Phi : PhiFun SCM CF) (s t : SCM) : Prop := ¬ CfEquiv Phi s t

/-- **中间地带 $Z$**。 -/
def MiddleZone (Phi : PhiFun SCM CF) : Set (SCM × SCM) :=
  {p | CfEquiv Phi p.1 p.2 ∧ p.1 ≠ p.2}

/-- **$Z = \varnothing$**。 -/
def MiddleZoneEmpty (Phi : PhiFun SCM CF) : Prop := MiddleZone Phi = ∅

/-! ### §22.2 ⭐⭐ 充要判据 -/

/-- ⭐⭐ **判据**：$Z = \varnothing \iff \Phi$ 单射。

**⟹ 这是本节的**收束性结论**** ——
它把「中间地带是否存在」这一**看似关于 $\mathcal F$ 的问题**
归约为**一个纯函数论条件**。 -/
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

/-- ⭐ **判据的对偶形式**：$Z \neq \varnothing \iff \Phi$ **非**单射。 -/
theorem middleZone_nonempty_iff_not_injective (Phi : PhiFun SCM CF) :
    (MiddleZone Phi).Nonempty ↔ ¬ Function.Injective Phi := by
  rw [Set.nonempty_iff_ne_empty]
  exact not_congr (middleZone_empty_iff_injective Phi)

/-- ⭐ **单射 ⟹ $Z$ 空**（判据的一个方向，独立陈述）。 -/
theorem middleZone_empty_of_injective (Phi : PhiFun SCM CF)
    (h : Function.Injective Phi) : MiddleZoneEmpty Phi :=
  (middleZone_empty_iff_injective Phi).mpr h

/-- ⭐ **$Z$ 空 ⟹ 单射**（判据的另一方向）。 -/
theorem injective_of_middleZone_empty (Phi : PhiFun SCM CF)
    (h : MiddleZoneEmpty Phi) : Function.Injective Phi :=
  (middleZone_empty_iff_injective Phi).mp h

/-! ### §22.3 ⭐⭐ 两侧的**具体见证** -/

/-- **结构模型读法 S**：$\mathcal F$ = 结构方程 + **反事实读不到的** `tag`。 -/
structure SModel where
  /-- 结构方程（反事实可见）。 -/
  mech : ℕ → ℕ
  /-- 反事实**读不到**的内部自由度。 -/
  tag : Bool

/-- **结构模型读法下的 $\Phi$**（只看 `mech`）。 -/
def SModel.Phi (F : SModel) : ℕ → ℕ := F.mech

/-- ⭐⭐ **非空侧见证**：在**结构模型读法 S** 下，$Z \neq \varnothing$。

**构造**：`⟨id, true⟩` 与 `⟨id, false⟩` ——
`mech` 相同（故反事实等价），`tag` 不同（故 $\mathcal F$ 不等）。 -/
theorem middle_zone_not_empty : ¬ MiddleZoneEmpty SModel.Phi := by
  rw [middleZone_empty_iff_injective]
  intro hinj
  have h : (⟨id, true⟩ : SModel) = ⟨id, false⟩ :=
    hinj rfl
  exact Bool.noConfusion (SModel.mk.injEq _ _ _ _ ▸ h |>.2)

/-- **反事实函数读法 F**：$\mathcal F$ = 反事实函数**本身**（恒等泛函）。 -/
theorem readingF_empty : MiddleZoneEmpty (Phi := (id : CF → CF)) :=
  middleZone_empty_of_injective id Function.injective_id

/-- ⭐⭐ **二分法（收束陈述）**：**两侧同时成立**。

| 读法 | $Z$ |
|---|---|
| **S**（结构模型）| **非空** |
| **F**（反事实函数）| **空** |

**⟹ 即**：**中间地带的非空性是**读法依赖**的** ——
**判定它是否存在，等价于判定 $\Phi$ 是否单射。** -/
theorem q25_dichotomy :
    (¬ MiddleZoneEmpty SModel.Phi) ∧
      MiddleZoneEmpty (Phi := (id : CF → CF)) :=
  ⟨middle_zone_not_empty, readingF_empty⟩

end MiddleZoneDichotomy

end FateV2.Predict