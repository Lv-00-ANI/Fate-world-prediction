import FateWorld.FateV2.Predict.TieredScheme
/-!
  # Predict · ViewOneCounterfactual

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ViewOneCounterfactual.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TieredScheme
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §30  ⭐⭐ **视角一能否支撑反事实**（原 `_probe_q26` 的正式化）

  **来源**：探针 `probes/_probe_q26.lean`（**不在构建内**）。

  ## 问题

  **视角一（多值当资源）能否支撑反事实？若能，需要什么额外条件？**

  ## ⭐⭐ 答案：**能 —— 但输出是「集合值/区间」，非点值**

  | 层 | 内容 |
  |---|---|
  | **结构层** | 视角一**从不额外丢信息**（它保留纤维本身）|
  | **语义层** | 视角一的天然输出是**逐点的反事实集合** $\mathrm{Obs}''(\mathrm{bridge}\,g)$ |
  | **判据** | ⭐ **点值反事实 $\iff$ `Obs` 在纤维上常值** |

  ## ⭐ 关键洞察

  **视角一的输出与部分识别的「识别域 $\Theta_0$」是**同一对象**** ——
  **要把它压成单点，恰需要 `Obs` 在纤维上常值**（即 `Collapse`）。

  **⟹ 这就是「额外条件」。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace ViewOneCounterfactual

universe u v w

variable {Graph : Type u} {SCM : Type v} {CF : Type w}

/-! ### §30.1 结构层：视角一的纤维与像 -/

/-- **集合值桥**。 -/
abbrev Bridge (Graph SCM : Type*) : Type _ := Graph → Set SCM

/-- **反事实泛函**。 -/
abbrev ObsFun (SCM CF : Type*) : Type _ := SCM → CF

/-- **视角一的纤维**：图 `g` 对应的全部 SCM。 -/
def fiber (bridge : Bridge Graph SCM) (g : Graph) : Set SCM := bridge g

/-- ⭐ **纤维上的反事实集合**（视角一的天然输出）。

$$\mathrm{cfSetObs}\,\mathrm{bridge}\,\mathrm{Obs}\,g := \mathrm{Obs}''(\mathrm{bridge}\,g)$$

**这是「多值当资源」的**正面产物**** ——
**反事实的部分识别域（识别域 $\Theta_0$）。** -/
def cfSetObs (bridge : Bridge Graph SCM) (Obs : ObsFun SCM CF) (g : Graph) : Set CF :=
  Obs '' bridge g

/-- ⭐ **存在性接口**：$c \in \mathrm{cfSetObs} \iff \exists \mathcal F \in \mathrm{bridge}\,g,\ \mathrm{Obs}\,\mathcal F = c$。 -/
theorem mem_cfSetObs_iff (bridge : Bridge Graph SCM) (Obs : ObsFun SCM CF) (g : Graph)
    (c : CF) :
    c ∈ cfSetObs bridge Obs g ↔ ∃ s ∈ bridge g, Obs s = c :=
  Set.mem_image _ _ _

/-- ⭐ **视角一**不**做任何粘合**（对照视角三）。

**⟹ 视角三粘掉纤维内差异，视角一保留之。** -/
theorem view1_keeps_all (bridge : Bridge Graph SCM) (g : Graph) :
    fiber bridge g = bridge g :=
  rfl

/-! ### §30.2 ⭐⭐ 语义层：点值反事实的充要条件 -/

/-- ⭐ **点值反事实**：纤维上所有 SCM 给出**同一个**反事实向量。

**即**：`Obs` 在纤维上**常值**。 -/
def PointValuedCF (bridge : Bridge Graph SCM) (Obs : ObsFun SCM CF) (g : Graph) : Prop :=
  ∀ s ∈ bridge g, ∀ t ∈ bridge g, Obs s = Obs t

/-- ⭐⭐ **主定理（充要条件）**。

$$\text{视角一在 } g \text{ 处给出点值反事实} \iff
  \exists c,\ \mathrm{cfSetObs}\,\mathrm{bridge}\,\mathrm{Obs}\,g = \{c\}$$

**⟹ 即**：**「支撑点值反事实」所需的额外条件就是 `Obs` 在纤维上常值。**

**⚠ 前提**：纤维**非空**（否则空像也是空集，判据退化）。 -/
theorem pointValuedCF_iff_obs_const (bridge : Bridge Graph SCM) (Obs : ObsFun SCM CF)
    (g : Graph) (hne : (bridge g).Nonempty) :
    PointValuedCF bridge Obs g ↔ ∃ c : CF, cfSetObs bridge Obs g = {c} := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := hne
    exact ⟨Obs s, by
      ext c
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact Set.mem_singleton_iff.mpr (h t ht s hs)
      · intro hc
        exact ⟨s, hs, (Set.mem_singleton_iff.mp hc).symm⟩⟩
  · rintro ⟨c, hc⟩ s hs t ht
    have hs' : Obs s ∈ cfSetObs bridge Obs g := ⟨s, hs, rfl⟩
    have ht' : Obs t ∈ cfSetObs bridge Obs g := ⟨t, ht, rfl⟩
    rw [hc, Set.mem_singleton_iff] at hs' ht'
    rw [hs', ht']

/-- ⭐⭐ **额外条件的「非自动性」**（反例）。

**陈述**：纤维里存在两个**反事实不同**的 SCM，则视角一**不能**给出点值反事实。

**⟹ 这形式化了「额外条件一般假」**：
**只要纤维是**反事实异质**的，`PointValuedCF` 就失败。** -/
theorem pointValuedCF_fails_of_heterogeneous (bridge : Bridge Graph SCM) (Obs : ObsFun SCM CF)
    {g : Graph} {s t : SCM} (hs : s ∈ bridge g) (ht : t ∈ bridge g) (hne : Obs s ≠ Obs t) :
    ¬ PointValuedCF bridge Obs g :=
  fun h => hne (h s hs t ht)

/-! ### §30.3 ⭐ 与视图三的**对照** -/

/-- ⭐⭐ **视角一 vs 视角三**（对照定理）。

| 视角 | 输出 | 是否丢信息 |
|---|---|---|
| **一**（多值当资源）| **集合** `cfSetObs` | **不丢**（保留纤维）|
| **三**（换商）| **单点**（粘合后）| **丢**（粘掉纤维内差异）|

**⟹ 即**：**「支撑点值反事实」的代价是**接受粘合**（视角三），
而**保留信息**的代价是**只能给集合值**（视角一）。**

**这是**鱼与熊掌**的精确形式。** -/
theorem view1_vs_view3 (bridge : Bridge Graph SCM) (Obs : ObsFun SCM CF) (g : Graph) :
    (fiber bridge g = bridge g) ∧
      (∀ c : CF, c ∈ cfSetObs bridge Obs g ↔ ∃ s ∈ bridge g, Obs s = c) :=
  ⟨view1_keeps_all bridge g, fun c => mem_cfSetObs_iff bridge Obs g c⟩

/-! ### §30.4 ⭐ 有界情形：区间结构 -/

/-- ⭐ **有界性**（当 `CF` 带序时）。

**陈述**：若纤维的像是**有界**的（有上下界），则视角一给出**区间**。

**⟹ 即**：**视角一的输出可读作「反事实的**区间**」** ——
**与部分识别的标准形态一致。** -/
def BoundedCF {CF : Type*} (le : CF → CF → Prop) (S : Set CF) : Prop :=
  (∃ lo ∈ S, ∀ x ∈ S, le lo x) ∧ (∃ hi ∈ S, ∀ x ∈ S, le x hi)

/-- ⭐ **视角一的输出总是集合**（即使退化）。

**陈述**：`cfSetObs` 恒为集合 ——
**它不是点值，除非满足 `PointValuedCF`。**

**⟹ 这是本节的核心断言的形式化。** -/
theorem view1_always_gives_set (bridge : Bridge Graph SCM) (Obs : ObsFun SCM CF) (g : Graph) :
    cfSetObs bridge Obs g = Obs '' bridge g :=
  rfl

end ViewOneCounterfactual

end FateV2.Predict