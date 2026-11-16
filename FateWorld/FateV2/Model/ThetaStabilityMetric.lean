import FateWorld.FateV2.Model.Frame
/-!
  # Model · ThetaStabilityMetric

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ThetaStabilityMetric.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §Q-1b  **稳定性的度量细化**（修正审计的一处数学错误）

  **背景**：审计建议增加一个「度量版稳定」并声称
  $$\mathrm{ThetaStableOn}\,\mathrm{ext}\,S \iff \mathrm{ThetaStableWithin}\,\mathrm{ext}\,S\,0$$

  **⚠ 该等价在 `PseudoMetricSpace` 下为假** —— 见下。

  ## ⚠ 审计的错误（如实记录）

  `PseudoMetricSpace` **允许** $\mathrm{dist}\,a\,b = 0$ 而 $a \neq b$
  （这正是「伪」的含义：不可区分点距离为零）。

  **⟹ 后果**：
  - $\Rightarrow$ 方向（常值 $\Rightarrow$ 距离 $\le 0$）**成立**（因为 $\mathrm{dist}\,a\,a = 0$）
  - $\Leftarrow$ 方向（距离 $\le 0$ $\Rightarrow$ 常值）**不成立** ——
    $\mathrm{dist}\,a\,b = 0$ **不蕴含** $a = b$

  **⟹ 故审计的等价式须分裂为两方向，且 $\Leftarrow$ 向须 `MetricSpace`（真度量）。

  ## 本节的做法

  | 定理 | 前件 | 内容 |
  |---|---|---|
  | `stableWithin_zero_of_stable` | **`PseudoMetricSpace`** | 常值 $\Rightarrow$ 距离 $\le 0$ ✅ |
  | `stable_of_stableWithin_zero` | **`MetricSpace`** | 距离 $\le 0$ $\Rightarrow$ 常值 ✅ |
  | `stable_iff_stableWithin_zero` | **`MetricSpace`** | 完整等价（真度量下成立）|

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Model

open FateV2.Modeling
namespace ThetaStabilityMetric

variable {E : InstSpace} {Θ : ThetaSpace}

/-- ⭐ **度量版稳定**：提取值在 `S` 上**距离不超过 `ε`**。

$$\forall e_1, e_2 \in S,\quad \mathrm{dist}\,(\mathrm{extract}\,e_1)\,(\mathrm{extract}\,e_2) \le \varepsilon$$

**与 `ThetaStableOn` 的关系**：后者是「取常值」（二值），
本定义是**定量**版本（`ε` 刻度）。

**⚠ 度量实例作参数传入** —— 因为 `ThetaSpace` 本身**不带度量**
（这正是审计说的「须给 `ThetaSpace` 加度量，属冻结签名改动」）。
**本节不改 `ThetaSpace`，而是把度量作前件** —— 符合裁决 I 的「加前件」方案。 -/
def ThetaStableWithin [PseudoMetricSpace Θ.Carrier]
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier) (ε : ℝ) : Prop :=
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, dist (ext.extract e₁) (ext.extract e₂) ≤ ε

/-! ### §Q-1b.1 ⭐ 单向：常值 ⟹ 距离 ≤ 0（**只在伪度量下即成立**） -/

/-- ⭐ **常值 ⟹ 距离 ≤ 0**（`(⇒)` 方向）。

**前件只需 `PseudoMetricSpace`** —— 因为 `dist a a = 0` 对伪度量也成立。

**⟹ 即：审计的 `(⇒)` 方向是**对的**，问题在反向。** -/
theorem stableWithin_zero_of_stable [PseudoMetricSpace Θ.Carrier]
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier)
    (h : ThetaStableOn ext S) : ThetaStableWithin ext S 0 := by
  intro e₁ h₁ e₂ h₂
  rw [h e₁ h₁ e₂ h₂]
  exact le_of_eq (dist_self _)

/-! ### §Q-1b.2 ⭐⭐ 反向：距离 ≤ 0 ⟹ 常值（**须真度量**） -/

/-- ⭐⭐ **距离 ≤ 0 ⟹ 常值**（`(⇐)` 方向）。

**⚠ 前件须 `MetricSpace`（真度量），不能是 `PseudoMetricSpace`** ——
因为伪度量允许 `dist a b = 0` 而 `a ≠ b`，此时反向不成立。

**⟹ 这正是审计漏掉的地方。** -/
theorem stable_of_stableWithin_zero [MetricSpace Θ.Carrier]
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier)
    (h : ThetaStableWithin ext S 0) : ThetaStableOn ext S := by
  intro e₁ h₁ e₂ h₂
  have hle : dist (ext.extract e₁) (ext.extract e₂) ≤ 0 := h e₁ h₁ e₂ h₂
  have hz : dist (ext.extract e₁) (ext.extract e₂) = 0 := le_antisymm hle (dist_nonneg)
  exact dist_eq_zero.mp hz

/-! ### §Q-1b.3 ⭐ 完整等价（**真度量下成立**） -/

/-- ⭐⭐ **完整等价**（`MetricSpace` 下）。

**⚠ 这是审计声称的定理的**正确形式** —— 前件从 `PseudoMetricSpace`
加强到 `MetricSpace`。**

$$\mathrm{ThetaStableOn}\,\mathrm{ext}\,S \iff \mathrm{ThetaStableWithin}\,\mathrm{ext}\,S\,0$$ -/
theorem stable_iff_stableWithin_zero [MetricSpace Θ.Carrier]
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier) :
    ThetaStableOn ext S ↔ ThetaStableWithin ext S 0 :=
  ⟨stableWithin_zero_of_stable ext S, stable_of_stableWithin_zero ext S⟩

/-! ### §Q-1b.4 ⭐ 伪度量下的**正确**刻画 -/

/-- ⭐⭐ **伪度量下的精确刻画**：`ε = 0` 的稳定等价于「提取值在 `S` 上
落在**同一个 `dist = 0` 类**中」。

**这是审计所声称等价式的**真正正确的替代** ——
它明确承认「距离为零」比「相等」**弱**。

**形式**：$\mathrm{ThetaStableWithin}\,\mathrm{ext}\,S\,0 \iff
\forall e_1,e_2 \in S,\ \mathrm{dist}(\ldots) = 0$

**⟹ 即**：伪度量下，`ε = 0` 稳定刻画的是「**识别不可区分**」而非「相等」。 -/
theorem stableWithin_zero_iff_dist_eq_zero [PseudoMetricSpace Θ.Carrier]
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier) :
    ThetaStableWithin ext S 0 ↔
      ∀ e₁ ∈ S, ∀ e₂ ∈ S, dist (ext.extract e₁) (ext.extract e₂) = 0 := by
  constructor
  · intro h e₁ h₁ e₂ h₂
    exact le_antisymm (h e₁ h₁ e₂ h₂) dist_nonneg
  · intro h e₁ h₁ e₂ h₂
    exact le_of_eq (h e₁ h₁ e₂ h₂)

/-- ⭐ **伪度量下 `ThetaStableOn` 更强**（严格性见证）。

**陈述**：`ThetaStableOn ⟹ ThetaStableWithin _ 0`，但反之不然（伪度量下）。

**⟹ 即：审计的等价式在伪度量下是**真的单向**，反向须真度量。** -/
theorem stable_imp_stableWithin_zero [PseudoMetricSpace Θ.Carrier]
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier) :
    ThetaStableOn ext S → ThetaStableWithin ext S 0 :=
  stableWithin_zero_of_stable ext S

end ThetaStabilityMetric

end FateV2.Model