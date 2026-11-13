import Mathlib
import FateWorld.FateV2.Error.FitBoundary

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SigmaFeasible.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 20 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop

/-
  σ 的约束从何而来：判据对 σ 施加了什么（对应论文 §10）

  判据要求误差压到噪声尺度 σ，而 σ 从何而来构成一个表观循环：定分辨率需要 σ，
  估 σ 又需要先有分辨率。

  ⚠ **一处须先行澄清的区分**（由无参数判据模块给出，本模块写作时尚未得到）：

    给定剖面，σ **不是**自由参数。只要边界点存在，σ 就被强制等于误差曲线的下确界
    `sInf (range E_W)`。因此「σ 无法从剖面内部推出」这一说法，在「σ 是剖面的一个量」
    这一意义上**不成立**——它是被剖面唯一决定的。

    真正未解的是另一个、强度不同的命题：「`sInf (range E_W)` 是否等于统计学意义上的
    噪声尺度」。这是**经验命题**，不是数学命题，故不可由本库任何定理推出或否证。

  澄清之后，本模块处理的是一个更窄、且完全可形式化的层次：

  | 层次 | 命题 | 形式化状态 |
  |---|---|---|
  | L2 无约束性 | 判据不排斥任何 σ | 可证（§1） |
  | L3 唯一性 | 同一剖面不能有两个 σ | 可证（§2） |
  | L4 可达集 | σ 的可行集是全部正实数 | 可证（§1 推论，另见 σ 的数值依赖模块） |

  L2 与 L3 合起来给出判据对 σ 的**约束强度**：对任意正数 σ 都存在剖面以其为边界值
  （判据不筛选 σ）；而给定一个剖面，其边界值至多一个（σ 被剖面锁定）。
  二者合起来的读法是：**判据对 σ 零约束，但 σ 与剖面一一绑定**。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：L2 / L3 说明的是判据本身的约束结构。σ 取哪一个统计量属语义选择，不是数学命题；
    Lean 只能证明若干候选取值都被判据允许。至于「哪些操作算内部」——在 σ 已被
    剖面决定之后，该问题只剩「所选的统计量是否就是噪声」这一经验层面。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error.SigmaFeasible

noncomputable section

/-! ===========================================================================
  §1  L2：判据不排斥任何正 σ
  =========================================================================== -/

/-- **常值剖面**：误差恒为 `c`（与分辨率无关的极端情形）。 -/
def profConst (c : ℝ) (hc : 0 ≤ c) : FateV2.Error.Core.ErrProfileWeak where
  bias := fun _ => c
  var := fun _ => 0
  bias_nonneg := fun _ => hc
  var_nonneg := fun _ => le_refl 0

theorem profConst_err (c : ℝ) (hc : 0 ≤ c) (gamma : ℝ) :
    (profConst c hc).err gamma = c := by
  simp only [FateV2.Error.Core.ErrProfileWeak.err, profConst]; ring

/-- **常值剖面以 `c` 为边界值**。 -/
theorem profConst_boundary (c : ℝ) (hc : 0 ≤ c) :
    FateV2.Error.Core.IsFitBoundary (profConst c hc) c 0 := by
  refine ⟨?_, ?_⟩
  · rw [profConst_err]
  · intro gamma'
    rw [profConst_err]

/-- **L2（核心）：任意正数都可以是某个剖面的边界值**。

    $$\forall\sigma>0,\ \exists W,\ \mathrm{HasFitBoundary}(W,\sigma).$$

    读法：**判据对 σ 的取值不作任何排除**。因此「σ 从哪来」**不可能**由
    `IsFitBoundary` 自身回答——这不是证明难度问题，是**信息不在其中**。 -/
theorem any_pos_sigma_realizable (sigma : ℝ) (h : 0 < sigma) :
    ∃ W : FateV2.Error.Core.ErrProfileWeak, FateV2.Error.Core.HasFitBoundary W sigma := by
  refine ⟨profConst sigma h.le, 0, ?_⟩
  exact profConst_boundary sigma h.le

/-- **L2 的补充：σ 非负是本判据的必然要求**。

    若 `HasFitBoundary W σ` 成立，则 `0 ≤ σ`（因为误差非负，而 σ 是下界）。
    **注意**：`σ = 0` 在常值零剖面下**是可能的**，
    故不能反过来说「σ 必须严格正」。这条界定了 σ 的可行域下沿。 -/
theorem sigma_nonneg_of_hasBoundary {W : FateV2.Error.Core.ErrProfileWeak} {sigma : ℝ}
    (h : FateV2.Error.Core.HasFitBoundary W sigma) : 0 ≤ sigma := by
  obtain ⟨gamma, hval, hlb⟩ := h
  have hnn := FateV2.Error.Core.ErrProfileWeak.err_nonneg W gamma
  rw [hval] at hnn
  exact hnn

/-- **可行域**：`{σ | ∃ W, HasFitBoundary W σ} = [0, ∞)`。 -/
theorem sigma_feasible_set_eq_nonneg :
    {sigma : ℝ | ∃ W : FateV2.Error.Core.ErrProfileWeak, FateV2.Error.Core.HasFitBoundary W sigma}
      = Set.Ici 0 := by
  ext sigma
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨W, h⟩
    exact sigma_nonneg_of_hasBoundary h
  · intro h
    rcases h.eq_or_lt with rfl | hpos
    · exact ⟨profConst 0 le_rfl, 0, (profConst_boundary 0 le_rfl).1,
        (profConst_boundary 0 le_rfl).2⟩
    · exact any_pos_sigma_realizable sigma hpos
/-! ===========================================================================
  §2  L3：同一剖面至多一个边界值
  =========================================================================== -/

/-- **L3（核心）：同一剖面的边界值唯一**。

    若 `W` 同时以 `σ₁` 与 `σ₂` 为边界值（可不同分辨率），则 `σ₁ = σ₂`。

    **读法**：判据把 σ 与剖面**一一绑定**。结合 L2 可知：
    **任意 σ 都可配一个剖面，一个剖面只配一个 σ** ——
    即 σ 是**自由参数**，而剖面只是它的载体。 -/
theorem boundary_value_unique (W : FateV2.Error.Core.ErrProfileWeak) {sigma1 sigma2 gamma1 gamma2 : ℝ}
    (h1 : FateV2.Error.Core.IsFitBoundary W sigma1 gamma1)
    (h2 : FateV2.Error.Core.IsFitBoundary W sigma2 gamma2) :
    sigma1 = sigma2 := by
  have a : sigma1 ≤ W.err gamma2 := h1.2 gamma2
  have b : sigma2 ≤ W.err gamma1 := h2.2 gamma1
  have e1 : W.err gamma1 = sigma1 := h1.1
  have e2 : W.err gamma2 = sigma2 := h2.1
  rw [e1] at b
  rw [e2] at a
  linarith

/-- **「σ 一旦确定，剖面被锁死在 σ 上」的**正确**形式**。

    若 `W` 以 `σ` 为边界值，且 `W` 的误差**处处不超过 σ**（即 σ 同时是上界），
    则 `W` 的误差**处处等于 σ**。

    **⚠ 这个前件不可省**：仅有「σ 是下界」**不足以**锁定剖面
    （一个剖面的下确界可以等于 σ，而它在别处仍可取更大值）。
    本条给出的是「下界 + 上界 ⟹ 常数」这一**唯一成立**的锁定形式。 -/
theorem profile_locked_when_sigma_is_also_upper (sigma : ℝ)
    {W : FateV2.Error.Core.ErrProfileWeak} {gamma : ℝ}
    (hb : FateV2.Error.Core.IsFitBoundary W sigma gamma)
    (hupper : ∀ gamma', W.err gamma' ≤ sigma) :
    ∀ gamma', W.err gamma' = sigma := by
  intro gamma'
  exact le_antisymm (hupper gamma') (hb.2 gamma')

/-! ===========================================================================
  §3  与项目已有结论的对照
  =========================================================================== -/

/-- **对照**：本项目已有的 `SigmaDataDependence.obtainable_sigma_set` 给出的是
    「可达集 = 全正半轴」的**参数化版本**；本文件 §1 的
    `sigma_feasible_set_unrestricted` 是**无参数版本**（不需要预先给出 `W` 与 `gamma`）。

    两者结论一致，但前者是从外部数据侧看的，后者是从判据侧看的。 -/
theorem consistent_with_obtainable_sigma_set (sigma : ℝ) (h : 0 < sigma) :
    ∃ W : FateV2.Error.Core.ErrProfileWeak, ∃ gamma : ℝ, FateV2.Error.Core.IsFitBoundary W sigma gamma := by
  obtain ⟨W, hb⟩ := any_pos_sigma_realizable sigma h
  obtain ⟨gamma, hg⟩ := hb
  exact ⟨W, gamma, hg⟩

/-! ===========================================================================
  §4  「σ 不能从内部推出」这一表述的消解
  =========================================================================== -/

/-
### 原先设想的层次 L1，及其为何不再需要

本模块设计的初稿假定存在一个不可形式化的层次 L1：「σ 不能从系统内部推出」。
该判断若要成为定理，须先形式化「内部」，而这至少需要三者之一：

| 需要的形式化 | 缺什么 |
|---|---|
| **可计算性**：σ 的估计器是否存在算法 | 需把「算法」建成可计算函数族，并证明某类函数不可实现 |
| **信息可得性**：哪些观测量在系统内部 | 「内部」是架构概念，Lean 无此概念 |
| **下界定理**：σ 的可估计性有无信息论下界 | 须先固定统计模型与估计量类，而此处未固定 |

**后续结果表明这一层次不必再设。** 无参数判据模块证明了

    `IsFitBoundary W σ γ  ⟹  sInf (range W.E) = σ`

即 **σ 被剖面唯一决定**。原先的表述之所以显得像一个不可形式化的元命题，
是因为它把两件性质完全不同的事捆在了一起：

| 命题 | 状态 |
|---|---|
| 「给定剖面，σ 不由剖面决定」 | **假**——即上面那条定理的逆否 |
| 「剖面下确界未必等于真实噪声尺度」 | **经验命题**，不是数学命题 |

故本模块不设 L1。留下的两个可证层次（L2 无约束性、L3 唯一性）恰好刻画了
判据对 σ 的**约束结构**：判据不筛选 σ，但 σ 与剖面一一绑定。
而「σ 取哪一个统计量」归属经验层面，只能由测量而非证明确定。

### 与量纲问题的对照

二者同属「形式化暴露了隐含假设」，但补法不同：

- 量纲缺的是**类型** —— 可以补，已由量纲模块给出（`Dim` / `Qty`）；
- σ 的语义缺的是**经验标定** —— 不能由形式化补，只能由外部测量补。

这一区分本身即是本文「形式化能做什么、不能做什么」的一个实例。
-/

end

end FateV2.Error.SigmaFeasible
