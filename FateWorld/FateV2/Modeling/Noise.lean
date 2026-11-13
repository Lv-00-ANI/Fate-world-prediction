import FateWorld.FateV2.Modeling.SCM
import Mathlib.Tactic

/-!
  # Modeling · Noise — 外生律 `P_U`

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：F5-07（外生律）
  - 依赖裁决：**D-014**（模型 = SCM，`P_U` 是外生律）、**D-019**（自由度最大化）
  - 改动：从空壳补成实现。`Model.P_U : Noise` 只是**载体参数**，
          本模块给出实际承载方式，并钉住「确定性 = 单点噪声」。
  - 状态：已编译

  ## 为什么 `Noise` 是类型参数而不是 `Measure E`

  `D-019` 要求自由度最大化：外生律可以是

  | 载体 | 适用 |
  |---|---|
  | `Measure E` | 连续 / 一般概率 |
  | 有限分布（`E → ℝ` + 归一） | 有限支撑、可计算 |
  | 单点（`E`） | 确定性系统（无噪声） |

  **确定性系统不该被逼着写测度**——这是把 `Noise` 设为参数的实际理由。

  ## 关键事实：无噪声是 `Noise` 的退化元

  单点噪声的离散度为 0 ⟹ `σ_model = 0` ⟹ 裁决 K 要求误差也 ≈ 0。
  这解释了「确定性世界里误差必须趋于零」不是额外假设，
  而是 σ 定义的推论（见 `DiracNoise` 与 `IsSpreadZeroOnDirac`）。
-/

namespace FateV2.Modeling

universe u

/-! ## §1 · 有限离散噪声 -/

/-- **有限离散噪声**：取值表 + 权重（不要求归一，归一性单独判）。

    用 `List` 而非 `Finset`，是为了保持可计算性（对应 `Demo/Executable*`）。 -/
structure FinNoise (E : Type u) where
  /-- 取值表 -/
  vals : List E
  /-- 权重表，与 `vals` 等长同序 -/
  wts  : List ℝ

namespace FinNoise

variable {E : Type u}

/-- 总权重。 -/
def total (μ : FinNoise E) : ℝ := μ.wts.sum

/-- **良构**：两支等长，且权重非负。 -/
def WellFormed (μ : FinNoise E) : Prop :=
  μ.vals.length = μ.wts.length ∧ ∀ w ∈ μ.wts, 0 ≤ w

/-- **归一**：总权重为 1。 -/
def Normalized (μ : FinNoise E) : Prop := μ.total = 1

/-- 良构 + 归一 ⟹ 这是一个真概率分布。 -/
def IsProb (μ : FinNoise E) : Prop := μ.WellFormed ∧ μ.Normalized

/-- 空表的总权重是 0。 -/
theorem total_nil : (⟨[], []⟩ : FinNoise E).total = 0 := by
  simp [total]

/-- **总权重非负**：良构时成立（权重全非负 ⟹ 和也非负）。 -/
theorem total_nonneg (μ : FinNoise E) (h : μ.WellFormed) : 0 ≤ μ.total := by
  obtain ⟨-, hw⟩ := h
  unfold total
  exact List.sum_nonneg hw

end FinNoise

/-! ## §2 · 确定性 = 单点噪声 -/

/-- **单点噪声**：只有一个可能取值的外生律。

    这是「确定性系统」的表示，不是"没有外生律"——
    它仍是一个外生律，只是支撑退化。 -/
structure DiracNoise (E : Type u) where
  /-- 唯一取值 -/
  only : E

namespace DiracNoise

variable {E : Type u}

/-- 把单点噪声看成有限噪声（单元素表，权重 1）。 -/
def toFin (d : DiracNoise E) : FinNoise E := ⟨[d.only], [1]⟩

/-- **单点噪声归一**：总权重恰为 1。 -/
theorem total_toFin (d : DiracNoise E) : d.toFin.total = 1 := by
  simp [toFin, FinNoise.total]

/-- **单点噪声良构**。 -/
theorem wellFormed_toFin (d : DiracNoise E) : d.toFin.WellFormed := by
  refine ⟨rfl, ?_⟩
  intro w hw
  simp [toFin] at hw
  linarith

/-- **单点噪声是真概率分布**（退化但合法）。

    这条钉住「确定性系统仍是 `Noise` 的合法实例」，
    于是它不会被 `IsProb` 过滤掉。 -/
theorem isProb_toFin (d : DiracNoise E) : d.toFin.IsProb :=
  ⟨d.wellFormed_toFin, d.total_toFin⟩

end DiracNoise

/-! ## §3 · 离散度的零性 -/

section Spread

/-- **确定性 ⟹ 零离散度**。

    这是 `IsSpread`（非负）之外的第二条要求：
    确定性系统的离散度必须是零，否则裁决 K 会要求一个正误差，
    与「无噪声时误差应趋于零」矛盾。

    ⟹ **它把「无噪声」与「σ = 0」在定义层就对上了**，
    不需要额外公理。 -/
def IsSpreadZeroOnDirac
    (spread : {E : Type u} → FinNoise E → ℝ) : Prop :=
  ∀ (E : Type u) (d : DiracNoise E), spread d.toFin = 0

end Spread

end FateV2.Modeling
