import FateWorld.FateV2.Error.FitBoundaryN
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · Loss —— 三层损失，都按裁决 K 判

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F7-05（三层损失）、F7-11（误差判据）
  - 依赖裁决：**裁决 K**、**D-009 §三**（损失源分离）、**D-023 C1**（`ε_model` 用裁决 K）
  - 改动：新文件（离散版，配合 `ErrProfileN` / `FitBoundaryN`）。
  - 状态：已验证

  ## 三层损失（D-009 §三）

  | 层 | 有损？ | 损失名 | 判据 |
  |---|---|---|---|
  | 建模（`construct`） | ❌ 无损 | —— | 0 |
  | 抽象（α） | ✅ | `abstLoss` | 误差 ≈ σ |
  | 预测（predict） | ✅ | `predLoss` | 误差 ≈ σ |

  ⚠ **降级**：本批**没有**把「建模无损」证出来（那要 `Model` 里含 `RawData`，
  按 D-009 §二 构造，会改动只读的 `SCM.Model`）。
  此处只把「建模层损失 = 0」写成**字段值**，并注明是约定而非定理。

  ## 超出定义之处
  * `total_lower` / `total_upper`：三层**各自**落在 `σ±ε` ⟹ 总和落在 `3σ±3ε`。
    这**不是**定义展开——每层容差独立，把「各自合格」合成为「总和合格」
    需要对每项各用一次不等式加法。
  * `modelLoss_ok`：裁决 K 与「建模无损」**不冲突**（只要区间含 0）。
-/

namespace FateV2.ErrorN

/-! ===========================================================================
  §1  三层损失
  =========================================================================== -/

/-- **三层损失**：建模 / 抽象 / 预测。 -/
structure Loss where
  /-- 建模层损失（D-009 §三：**无损**，取 0） -/
  modelLoss : Real
  /-- 抽象层损失（α 抽规则时的有损） -/
  abstLoss : Real
  /-- 预测层损失 -/
  predLoss : Real

/-- **三层皆零的损失**（「建模层无损」这一约定的载体）。 -/
def Loss.zero : Loss :=
  { modelLoss := 0, abstLoss := 0, predLoss := 0 }

/-- 三层损失之和。 -/
def Loss.total (L : Loss) : Real := L.modelLoss + L.abstLoss + L.predLoss

/-- **合格判定**（与 `FitBoundaryN.accepts` 逐字相同）。

  D-023 C1：`ε_model` **依旧用裁决 K** ⟹ 三层共用**同一个**谓词。 -/
def Loss.ok (σ ε e : Real) : Prop := accepts σ ε e

/-- **三层都合格**。 -/
def Loss.allOk (L : Loss) (σ ε : Real) : Prop :=
  Loss.ok σ ε L.modelLoss ∧ Loss.ok σ ε L.abstLoss ∧ Loss.ok σ ε L.predLoss

/-! ===========================================================================
  §2  性质
  =========================================================================== -/

/-- **建模层恒合格**（只要容差区间含 0）。

  D-009 §三 说建模层无损；本定理把它与裁决 K 接上：
  若 `[σ−ε, σ+ε]` 含 0，则建模层的损失 0 **自动合格**——
  于是「建模无损」与「误差 ≈ σ」这两条要求**不冲突**。
  若不相容，D-023 C1 的答复（`ε_model` 用裁决 K）就会与 D-009 打架。 -/
theorem modelLoss_ok (σ ε : Real) (h : accepts σ ε 0) :
    Loss.ok σ ε Loss.zero.modelLoss := h

/-- **三层合格 ⟹ 总损失下界**。

  **超出定义之处**：`Loss.allOk` 是三个**独立**的区间包含，
  `Loss.total` 是三项之和。把「三个都在 `σ±ε`」合成为「和 ≥ `3σ−3ε`」
  需要对每一项各用一次下界，再把 `σ+σ+σ` 对齐到 `3σ`——定义本身完全没有这条。 -/
theorem total_lower (L : Loss) (σ ε : Real) (h : L.allOk σ ε) :
    3 * σ - 3 * ε ≤ L.total := by
  rcases h with ⟨h1, h2, h3⟩
  unfold Loss.ok accepts at h1 h2 h3
  obtain ⟨h1a, _⟩ := h1
  obtain ⟨h2a, _⟩ := h2
  obtain ⟨h3a, _⟩ := h3
  unfold Loss.total
  linarith

/-- **三层合格 ⟹ 总损失上界**。 -/
theorem total_upper (L : Loss) (σ ε : Real) (h : L.allOk σ ε) :
    L.total ≤ 3 * σ + 3 * ε := by
  rcases h with ⟨h1, h2, h3⟩
  unfold Loss.ok accepts at h1 h2 h3
  obtain ⟨_, h1b⟩ := h1
  obtain ⟨_, h2b⟩ := h2
  obtain ⟨_, h3b⟩ := h3
  unfold Loss.total
  linarith

/-- **三层合格 ⟹ 总损失落在 `[3σ−3ε, 3σ+3ε]`**（把上两条合成一条）。 -/
theorem total_sound (L : Loss) (σ ε : Real) (h : L.allOk σ ε) :
    3 * σ - 3 * ε ≤ L.total ∧ L.total ≤ 3 * σ + 3 * ε :=
  ⟨total_lower L σ ε h, total_upper L σ ε h⟩

end FateV2.ErrorN
