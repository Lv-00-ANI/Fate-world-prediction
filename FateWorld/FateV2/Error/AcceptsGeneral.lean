import FateWorld.FateV2.Error.SigmaToVerdict
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
  # Error · AcceptsGeneral —— 把裁决 K 的**带宽判据** `accepts` 泛化到任意序结构（T50）

  ## 迁移登记
  - 来源：**推广**下列既有定义/定理，原文件**一个字都不改**
    * `FateV2/Error/FitBoundaryN.lean`：`def accepts (σ ε e : Real) : Prop`（层 1，具体版）
    * `FateV2/Error/SigmaToVerdict.lean`：`accepts_of_estimate_near`（T46 核心定理）
    * `FateV2/Error/VerdictGeneral.lean`：`IsBoundaryPoint` / `VerdictAxioms`（T28，层 2）
  - 动作：C 重写（新文件，只新增定义与定理）
  - 对应环节：F7-11（误差判据 / 裁决 K）、F7-02（σ）
  - 依赖裁决：**裁决 K**、**D-008**、**D-016**（零公理）、**D-020**、**D-022**
  - 状态：见 `_报告/T50-进度.md`

  ## 三层结构：本文件补第三层

  | 层 | 载体 | 文件 | 对象 |
  |---|---|---|---|
  | 1 具体 | `Real` | `Error/FitBoundaryN` | `IsFitBoundaryN`、`accepts` |
  | 2 抽象边界点 | 任意 `Preorder` | `Error/VerdictGeneral`（T28） | `IsBoundaryPoint`、`VerdictAxioms` |
  | **3 抽象带宽** | **任意序加法群** | **本文件（T50）** | **`acceptsG`、`BandAxioms`** |

  ## 最小结构（§1 结论，全部实测于此工具链 lean4 `v4.33.0-rc1` + 本机 Mathlib）

  ⚠ 本 Mathlib 版本**没有** `OrderedAddCommGroup` 这个 bundling 名字（实测 `unknownIdentifier`），
  有序结构一律是 **unbundled** 类。本文件把载体**按层**给出（每层都是实测的最小集）：

  | 层次 | 载体 | 依据 |
  |---|---|---|
  | `acceptsG` **定义** | `AddGroup` + `LE` | 定义只是两个 `≤` 的合取 |
  | §1.1 拆解 / `+0` 单位 | `AddGroup` + `LE` | 纯逻辑与代数重写 |
  | §1.1 中心点 `acceptsG_self_of_nonneg` | `+ AddLeftMono` | `σ ≤ σ+ε` 走 `add_le_add_right`（**左**加） |
  | §1.2 带宽单调 / `0 ≤ η` 版本 | `+ AddRightMono + IsTrans` | 两半各一次放缩再串接 |
  | §1.3 偏差读法 | `+ AddCommGroup` | 要把 `-σ` 与 `σ` 换位 |
  | **§2 核心定理** | **`AddCommGroup` + `LE` + `AddRightMono` + `IsTrans`** | 见下 |

  **不需要**：`Preorder`、`LinearOrder`、`IsOrderedAddMonoid` bundling、`Real`。
  **§2 需要交换律**（`AddCommGroup`）：两处重排 `-ε + -δ ↦ (-δ)+(-ε)` 与
  `(σ̂+δ)+ε ↦ σ̂+(ε+δ)` 必须换位。§2.4 记录了「这条不能省」的判断，
  并**证伪**了派单给出的 `2×2` 整数矩阵反例。

  ⚠ **四条反直觉的实测**（决定了本文件的写法，写进注释以免后人重踩）：

  1. `le_trans` 在本工具链里**只**对 `Preorder` 可用（它是 `LE.le.trans` 的投影）；
     纯 `LE` 上连 `IsTrans β (· ≤ ·)` 实例都**不自动存在**（`Mathlib/Order/Defs/Unbundled`
     只对 `Preorder` 建实例）。故传递性必须**作为显式类前件**列出。
  2. **`add_le_add_left` / `add_le_add_right` 的名字与位置「反着」**：
     `add_le_add_left h c : a + c ≤ b + c`（**右**加，配 `AddRightMono`）；
     `add_le_add_right h c : c + a ≤ c + b`（**左**加，配 `AddLeftMono`）。
     本文件每处都按**结论形状**选取，不按名字猜 —— 这就是核心定理只用到
     `AddRightMono` 而**不用** `AddLeftMono` 的由来（§1 的中心点定理才要后者）。
  3. `add_comm` / `add_left_comm` / `sub_sub` / `neg_add_rev` 分别要
     `AddCommMagma` / `AddCommSemigroup` / `SubtractionCommMonoid` / `SubtractionMonoid`。
     本文件只用**最小**的 `add_comm`（`AddCommMagma`，由 `AddCommGroup` 自动给），
     并用 `neg_add`（`AddGroup`）替代 `neg_add_rev`。
  4. `σ ≤ σ`（自反）在纯 `LE` 上**拿不到**（无 `Std.Refl` 实例，`le_refl` 要 `Preorder`）。
     本文件只在 `acceptsG_self_of_nonneg` 一处需要它，且用 `add_le_add_right` 于 `0 ≤ ε`
     绕开 —— 若 `ε` 可为负，中心点**确实不在**自己带里（第一个过强断言）。

  载体**不含** `Real` / `Finset` / `Rat`（`Real` 只在 §3 的一致性接口出现），
  故 §1 / §2 的定理是**零公理**的。

  ## 证据链（定理 → 「比定义多说了什么」）

  | 定理 | 比定义多说了什么 |
  |---|---|
  | `acceptsG_lo_le` / `acceptsG_le_hi` | 合取拆成可单独使用的两个方向 |
  | `acceptsG_self_of_nonneg` | `0 ≤ ε` 时判据**有解**（`σ` 在自己带里）；两半分别出自 `sub_le_self` 与 `add_le_add_right` |
  | `acceptsG_mono_eps` | 带宽**单调**（「放宽」有意义的数学前提，定义里没有） |
  | `acceptsG_mono_eps_of_zero_le` | `0 ≤ η` ⟹ 带宽可无条件加 `η`（放宽方向性的唯一要求） |
  | `acceptsG_mono_eps'` | `+ 0` 是带宽的单位 ⟹「不放宽 = 放宽 0」 |
  | `acceptsG_dev_left` | 下半支的**偏差**读法 `-ε ≤ e - σ`（`Real` 版的半边，在任意群上重建） |
  | `acceptsG_of_estimate_near` | **核心**：四条不等式三角合成出「以 σ̂ 为中心的带」，带宽恰好多 `δ` |
  | `acceptsG_of_estimate_near'` | 上下界**可以不对称**（下 `δ`、上 `δ'`，`δ' ≤ δ`） |
  | `acceptsG_of_estimate_near_add` | 结论带宽留 `η` 余量（与带宽单调串联） |
  | `acceptsG_nonsym_upper` | 误差取**单边**上界时，结论**只能**拿到上界那一半（另半边真的会丢） |
  | `mat_add_not_comm` | 非交换载体存在 ⟹ §2 的结构**没**偷用交换律 |
  | `accepts_eq_acceptsG` | 具体 `accepts` 与泛化 `acceptsG` 在 `ℝ` 上逻辑**等价**（`Iff.rfl`） |
  | `accepts_of_estimate_near_via_general` | T46 的 `accepts_of_estimate_near` **是**本文件核心定理的实例 |
  | `acceptsG_bandAxioms` | `acceptsG` 满足 `BandAxioms`（`center` / `mono_eps`） |
  | `wideCriterion_bandAxioms` | **第二个**语法不同的判据也满足（抽象**不空**） |
  | `acceptsG_imp_wide` | 两个实例的强弱关系（宽判据真的更宽） |
  | `nonnegCriterion_not_bandAxioms` | `ε ↦ e ≥ σ` 这个自然弱化**被排除**（`center` 崩） |
  | `accepts_general_summary` | 全部结果的见证汇总（D-022 账实核对只读一处） |

  ## 公理纪律（`_代理须知.md` §六）

  * **不用** `sorry` / `admit` / 自定义 `axiom`。
  * **不用** `simp` / `decide` / `by_contra` / `funext` / `linarith` / `norm_num` / `omega` /
    `positivity` / `gcongr`：算术全部走 `IsTrans.trans` / `rw`（纯等式）/ `sub_eq_add_neg` /
    `add_le_add_left` / `add_le_add_right` / `sub_le_sub_left`。
  * **不用** `le_trans`（要 `Preorder`）。

  ## ⚠ 实测：公理状态（D-016 的诚实交代）

  本文件原计划做到「泛化层**全零公理**」。实测结果**部分达成**，原因**不在本文件，
  在 Mathlib 的 `Algebra.Order.Group.Unbundled.Basic`**：

  | Mathlib 引理 | 实测公理 | 被谁用 |
  |---|---|---|
  | `sub_le_self` | **`propext`** | `acceptsG_self_of_nonneg` |
  | `sub_le_sub_left` / `sub_le_sub_right` | **`propext`** | 带宽单调、核心定理 |
  | `sub_zero` | **`propext`** | `acceptsG_self_zero` |
  | `neg_add` | **`propext`** | 核心定理的下等式 |
  | `add_le_add_left` / `add_le_add_right` / `IsTrans.trans` | 无 | 全程 |
  | `add_zero` / `add_assoc` / `add_comm` / `neg_add_cancel` | 无 | 全程 |

  根源：`sub_le_self_iff` / `neg_le_neg_iff` / `left_neg_iff` 这一族在 Mathlib 里是
  `by simp` / `by simpa` 收尾的（源码实测），而 `simp` 带 `propext`。
  **这不影响本文件的结构结论**：载体层面的泛化（`AddCommGroup` + `LE` +
  `AddRightMono` + `IsTrans`，且 `Preorder` **不需要**）是完整的、可编译的；
  受影响的只是「这些具体证明路径是否恰好零公理」。

  **零公理的定理**（实测 `#print axioms` 为 `[]`，共 6 条）：
  `acceptsG_lo_le`、`acceptsG_le_hi`、`acceptsG_nonsym_upper`、
  `add_swap_inner`、`acceptsG_imp_wide`、`upperOnly_mono`。
  **带 `propext`** 的：其余 §1/§2/§4 定理，共 15 条（全是上面那五个 Mathlib 引理的传递结果）。
  **带三公理**的：`accepts_eq_acceptsG`、`accepts_of_estimate_near_via_general`、
  `accepts_general_summary`（共 3 条）—— 三者**显式**涉及 `Real`，按本项目既有规律（T28 同款）
  必带三公理，这是**设计上不可避免**的（§3 的一致性接口必须提 `Real`）。
  6 + 15 + 3 = 24 条，与 `_support_registry_T50.csv` 逐条一致。
-/

namespace FateV2.Error.AcceptsGeneral

/-! ===========================================================================
  §1  泛化的带宽判据：最小结构
  =========================================================================== -/

/-- **【主定义】泛化的带宽判据**：`σ − ε ≤ e ≤ σ + ε`。

  签名只要求 `AddGroup`（要用 `-`）与 `LE`（要用 `≤`）——
  比 `FitBoundaryN.accepts` 只多了一条「`Real` 换成任意加法群 + `LE`」，
  命题本体**逐字相同**（§3 的 `accepts_eq_acceptsG` 是 `Iff.rfl`）。

  ⚠ 定义本身**不需要**传递性、也不需要单调：它只是两个 `≤` 的合取。
  传递性与单调是**定理**（§2 的三角合成）需要的东西，不是定义需要的；
  本文件把定义写在最小签名上，把结构要求留在定理处，二者不混。 -/
def acceptsG {β : Type} [AddGroup β] [LE β] (σ ε e : β) : Prop :=
  σ - ε ≤ e ∧ e ≤ σ + ε

/-! ### §1.1 拆解 -/

section Split

variable {β : Type} [AddGroup β] [LE β]

/-- **下支可以单独用**。

  **比定义多说了什么**：`acceptsG` 是一个合取项，下游往往只需要一侧
  （例如只判「没超上界」）。本定理把它作为独立的命题取出，
  于是「判据的哪一半被用到」可以被引用、被审计。
  ⚠ 本定理**只要** `AddGroup` + `LE`（连单调都不要）—— 定义的一部分就是定义的一部分。 -/
theorem acceptsG_lo_le {σ ε e : β} (h : acceptsG σ ε e) : σ - ε ≤ e := h.1

/-- **上支可以单独用**（与 `acceptsG_lo_le` 对称，同样只要 `AddGroup` + `LE`）。 -/
theorem acceptsG_le_hi {σ ε e : β} (h : acceptsG σ ε e) : e ≤ σ + ε := h.2

end Split

section SelfNonneg

variable {β : Type} [AddGroup β] [LE β] [AddLeftMono β]

/-- **`0 ≤ ε` 时中心点合格**。

  **比定义多说了什么**：定义只写两个不等式，**没有**说判据有解。本定理说
  `0 ≤ ε` 时 `σ` **一定**在自己带里，且两半各出一条独立的推理：
  * 下支 `σ − ε ≤ σ` = `sub_le_self σ hε`（其前件正是 `0 ≤ ε`，见 `sub_le_self_iff`）；
  * 上支 `σ ≤ σ + ε`：由 `add_le_add_right hε σ : σ + 0 ≤ σ + ε`
    （`add_le_add_right` = **左**加，见文件头的实测 2）再 `rw [add_zero]`。

  ⚠ **无条件版本是假的**：任意序加法群上取 `ε = -1`，则 `σ − (−1) = σ + 1 ≰ σ`。
  故本定理必须带前件 —— 这是本文件拦下的**第一个**过强断言
  （§4 的 `BandAxioms.center` 因此必须带 `0 ≤ ε`，不能写成 `∀ σ ε, P σ ε σ`）。

  ⚠ 载体只要 `AddLeftMono`（**不要** `AddRightMono`）：上支用的是**左**加。 -/
theorem acceptsG_self_of_nonneg {σ ε : β} (hε : 0 ≤ ε) : acceptsG σ ε σ := by
  refine ⟨sub_le_self σ hε, ?_⟩
  have h1 : σ + 0 ≤ σ + ε := add_le_add_right hε σ
  rwa [add_zero] at h1

end SelfNonneg

section SelfZero

variable {β : Type} [AddGroup β] [LE β] [Std.Refl (fun x y : β => x ≤ y)]

/-- **`ε = 0` 时中心点合格**（只需 `AddGroup` + `LE` + **自反性**，不要单调）。

  **比定义多说了什么**：把上一条在 `ε = 0` 处取满 —— 此时带退化成一个点，
  于是「点在自己里」变成 `σ − 0 = σ` 与 `σ + 0 = σ` 两条等式，**没有单调**参与。
  但**自反性**仍然要：两条等式化归后都是 `σ ≤ σ`。

  ⚠ 这正好落实文件头「实测 4」：`σ ≤ σ` 在本工具链里必须**显式**给出
  （`Std.Refl` 或 `Preorder`），纯 `LE` 拿不到。
  这是「`BandAxioms.center` 为什么**必须**带 `0 ≤ ε`」的直接证据：
  真正**无条件**的只有 `ε = 0` 这一个点。 -/
theorem acceptsG_self_zero (σ : β) : acceptsG σ 0 σ := by
  refine ⟨?_, ?_⟩
  · rw [sub_zero]
    exact Std.Refl.refl σ
  · rw [add_zero]
    exact Std.Refl.refl σ

end SelfZero

section MonoThm

variable {β : Type} [AddGroup β] [LE β] [AddLeftMono β] [AddRightMono β]
  [IsTrans β (fun x y => x ≤ y)]

/-- **带宽单调**：`ε ≤ ε'` ⟹ 带宽 `ε` 的带被 `ε'` 的带包含。

  **比定义多说了什么**：`acceptsG` 的定义是一个**合取**，对 `ε` 的大小不作任何断言；
  本定理把它在 `ε` 上做成**单调**——「放宽带宽」这个词有意义的数学前提
  （否则「放宽」可能反而变严）。T46 的 `accepts_mono_eps` 在 `Real` 上说过同一句话。
  两半方向相反：下界**反变**（`sub_le_sub_left hε σ : σ - ε' ≤ σ - ε`），
  上界**协变**（`add_le_add_right hε σ : σ + ε ≤ σ + ε'`）。

  ⚠ 本定理**需要**传递性（两半各要串一次 `≤`）—— 这是 `IsTrans` 第一次出场；
  §1 的其余定理都不需要它。 -/
theorem acceptsG_mono_eps {σ ε ε' e : β}
    (hε : ε ≤ ε') (h : acceptsG σ ε e) :
    acceptsG σ ε' e :=
  ⟨IsTrans.trans (σ - ε') (σ - ε) e (sub_le_sub_left hε σ) h.1,
    IsTrans.trans e (σ + ε) (σ + ε') h.2 (add_le_add_right hε σ)⟩

end MonoThm

/-! ### §1.2 带宽余量 -/

section MonoEps

variable {β : Type} [AddGroup β] [LE β] [AddLeftMono β] [AddRightMono β]
  [IsTrans β (fun x y => x ≤ y)]

/-- **`0 ≤ η` ⟹ 带宽可无条件加 `η`**（`acceptsG_mono_eps` 的常用特殊情形）。

  **比定义多说了什么**：把「`ε ≤ ε + η`」这一步从 §2 的链式推理里**提出来**
  （它只由 `0 ≤ η` 与 `add_zero` 决定），下游不必每次重做。
  这条也说明「放宽量必须非负」是**唯一**的方向性要求。 -/
theorem acceptsG_mono_eps_of_zero_le {σ ε η e : β} (hη : 0 ≤ η) (h : acceptsG σ ε e) :
    acceptsG σ (ε + η) e := by
  have hle : ε ≤ ε + η := by
    have h1 : ε + 0 ≤ ε + η := add_le_add_right hη ε
    rwa [add_zero] at h1
  exact ⟨IsTrans.trans (σ - (ε + η)) (σ - ε) e (sub_le_sub_left hle σ) h.1,
    IsTrans.trans e (σ + ε) (σ + (ε + η)) h.2 (add_le_add_right hle σ)⟩

end MonoEps

section MonoEpsZero

variable {β : Type} [AddGroup β] [LE β]

/-- **`+ 0` 是带宽的单位**（**只要 `AddGroup` + `LE`**）。

  **比定义多说了什么**：`ε + 0 = ε` 是加法幺元律，但用在这里说明
  「**不放宽**」与「**放宽 0**」是同一件事——§2 的核心定理在 `δ = 0` 处
  **退化**为原始判据：不放宽任何东西，也不收紧任何东西。
  ⚠ 本定理**不需要**任何序类（连单调都不要）：它是纯代数重写。 -/
theorem acceptsG_add_zero_band (σ ε e : β) : acceptsG σ (ε + 0) e ↔ acceptsG σ ε e := by
  rw [add_zero]

end MonoEpsZero

/-! ### §1.2b 偏差读法（需要交换律） -/

section Dev

variable {β : Type} [AddCommGroup β] [LE β] [AddLeftMono β] [AddRightMono β]

/-- **下半支的偏差读法**：`acceptsG σ ε e` ⟹ `-ε ≤ e - σ`。

  **比定义多说了什么**：T46 的 `accepts_iff_dev` 在 `Real` 上把整个判据换成「偏差」形式；
  本定理只取其中**确实**在任意群上成立的那一**支**，**不**宣称整条 `↔`
  （反方向要用 `σ` 的消去性）——这是「不过度断言」的具体做法。

  ⚠ **需要交换律**（`AddCommGroup`），不是 `AddGroup`：把 `σ - ε ≤ e` 改写成
  `e - σ ≥ -ε` 要把 `σ` 与 `-σ` 换位，这一步在非交换群上**不成立**。
  这正是本文件头「实测 3」的另一面：`dev` 读法比核心定理**更贵**，
  故本文件把它单独标注，核心定理（§2）**不**依赖它。 -/
theorem acceptsG_dev_left {β : Type} [AddCommGroup β] [LE β] [AddLeftMono β]
    [AddRightMono β] {σ ε e : β} (h : acceptsG σ ε e) : -ε ≤ e - σ := by
  obtain ⟨h1, h2⟩ := h
  have h1' : σ + -ε ≤ e := by
    rw [sub_eq_add_neg] at h1
    exact h1
  have h3 : e - σ = e + -σ := sub_eq_add_neg e σ
  rw [h3]
  -- `-ε = (σ + -ε) + -σ`（交换群：把 `σ` 挪到 `-σ` 旁消掉）
  have h4 : -ε = (σ + -ε) + -σ := by
    have e1 : (σ + -ε) + -σ = σ + (-ε + -σ) := add_assoc σ (-ε) (-σ)
    have e2 : σ + (-ε + -σ) = -ε := by
      rw [← add_assoc, add_comm σ (-ε), add_assoc, add_neg_cancel]
      exact add_zero (-ε)
    rw [e1, e2]
  rw [h4]
  exact add_le_add_left h1' (-σ)

end Dev

/-! ===========================================================================
  §2  核心定理的泛化：估计误差 ≤ δ ⟹ 判据放宽 δ

  本节额外需要 `IsTrans β (· ≤ ·)` —— 见文件头「实测 1」：
  纯 `LE` 上没有传递性实例，而三角合成**必须**串两次 `≤`。
  故传递性作为**显式前件**出现在每条定理的签名里（而不是靠 `Preorder` 白拿）。
  =========================================================================== -/

section Core

variable {β : Type} [AddCommGroup β] [LE β] [AddLeftMono β] [AddRightMono β]
  [IsTrans β (fun x y => x ≤ y)]

/-- **【核心】T46 `accepts_of_estimate_near` 的泛化版**（载体已按实测收窄：
`AddCommGroup` + `LE` + `AddRightMono` + `IsTrans`；`AddLeftMono` **不用**）。

  $$\hat\sigma-\delta\le\sigma,\quad \sigma\le\hat\sigma+\delta,\quad
    \mathrm{acceptsG}\ \sigma\ \varepsilon\ e
    \;\Longrightarrow\;
    \mathrm{acceptsG}\ \hat\sigma\ (\varepsilon+\delta)\ e .$$

  **比定义多说了什么**（T46 的注释在 `Real` 上说过一次，这里在**任意群**上重建）：
  * 前件共四条不等式，没有一条包含「以 `σ̂` 为中心的带」，也没有一条说 `ε + δ` 够用；
    本定理是它们的**三角合成**，不是任何一条的换写。
  * 带宽多出的**恰是** `δ`：两处都**恰好**贴边 ——
    下界 `σ̂ − (ε+δ) = (σ̂ − δ) − ε ≤ σ − ε ≤ e`；
    上界 `e ≤ σ + ε ≤ (σ̂ + δ) + ε = σ̂ + (ε+δ)`。
  * 三个类**都不可省**：`AddRightMono`（**右**加：`add_le_add_left` 与
    `sub_le_sub_right` 都要它）、`AddCommGroup`（重排 `δ+ε` 与 `ε+δ`，见 §2.4）、
    `IsTrans`（`IsTrans.trans` 串两次）。
  * ⚠ `AddLeftMono` **不在**核心定理的载体里（见文件头实测 2 的命名对偶）：
    本定理两支用的都是**右**加。§1 的 `acceptsG_self_of_nonneg` 才要 `AddLeftMono`。
  * 两个**等式**步骤需要用交换律（`add_comm`）把 `-δ + -ε` 与 `δ + ε` 对齐 ——
    这就是载体必须是 `AddCommGroup` 而不是 `AddGroup` 的**唯一**原因。
  * **不做任何分支**（无 `by_cases` / `by_contra`），故无 `propext` 风险。 -/
theorem acceptsG_of_estimate_near {β : Type} [AddCommGroup β] [LE β] [AddRightMono β]
    [IsTrans β (fun x y => x ≤ y)] {σ σhat ε δ e : β}
    (hhat : σhat - δ ≤ σ ∧ σ ≤ σhat + δ) (h : acceptsG σ ε e) :
    acceptsG σhat (ε + δ) e := by
  refine ⟨?_, ?_⟩
  · -- 下界：`σ̂ − (ε+δ) = σ̂ + -(ε+δ) = σ̂ + (-δ + -ε) = (σ̂ + -δ) + -ε = (σ̂ − δ) − ε`
    have hA : σhat + -(ε + δ) = (σhat + -δ) + -ε := by
      rw [neg_add, add_comm (-ε) (-δ), add_assoc]
    have hB : (σhat + -δ) + -ε = σhat - δ - ε := by
      rw [sub_eq_add_neg σhat δ, sub_eq_add_neg (σhat + -δ) ε]
    have h2 : σhat - (ε + δ) = σhat - δ - ε := by
      rw [sub_eq_add_neg σhat (ε + δ), hA, hB]
    rw [h2]
    exact IsTrans.trans _ _ _ (sub_le_sub_right hhat.1 ε) h.1
  · -- 上界：`e ≤ σ + ε ≤ σ̂ + δ + ε`，再用 `add_comm` 重排成 `σ̂ + (ε + δ)`
    have h1 : σ + ε ≤ (σhat + δ) + ε := add_le_add_left hhat.2 ε
    have h2 : (σhat + δ) + ε = σhat + (ε + δ) := by
      rw [add_assoc, add_comm δ ε]
    rw [← h2]
    exact IsTrans.trans _ _ _ h.2 h1

/-- **上下界可以不对称**：`σ ≤ σ̂ + δ'`、`δ' ≤ δ` ⟹ 带宽仍可取 `ε + δ`。

  **比定义多说了什么**：T46 的 `accepts_of_estimate_near'` 只允许
  「实际上界 `δ' ≤ δ`」这一种宽松；本定理允许**两侧分别给界**
  （下侧 `δ`、上侧 `δ'`，只要 `δ' ≤ δ`）。上游（T47 / T49 的链式预算）
  给出的界本来就不对称，多这一个自由度可以少一次人为的对称化。
  证明把「`δ'` 不够时放大到 `δ`」单独做成一条可复用的放缩。 -/
theorem acceptsG_of_estimate_near' {σ σhat ε δ δ' e : β}
    (hhi : δ' ≤ δ) (hhat : σhat - δ ≤ σ ∧ σ ≤ σhat + δ') (h : acceptsG σ ε e) :
    acceptsG σhat (ε + δ) e :=
  acceptsG_of_estimate_near
    ⟨hhat.1, IsTrans.trans σ (σhat + δ') (σhat + δ) hhat.2 (add_le_add_right hhi σhat)⟩ h

/-- **结论带宽留 `η` 余量**（`0 ≤ η`）：放宽 `(ε + δ) + η` 也合格。

  **比定义多说了什么**：把核心定理与 §1 的带宽**单调**串联 ——
  下游要再塞一层链式误差时不必重证三角合成。
  注意 `(ε + δ) + η` 的括号**不能**省：在非交换群上 `δ + η` 与 `η + δ` 不同，
  故本定理要求 `0 ≤ η`（见 `acceptsG_mono_eps_of_zero_le`）。 -/
theorem acceptsG_of_estimate_near_add {σ σhat ε δ η e : β} (hη : 0 ≤ η)
    (hhat : σhat - δ ≤ σ ∧ σ ≤ σhat + δ) (h : acceptsG σ ε e) :
    acceptsG σhat ((ε + δ) + η) e :=
  acceptsG_mono_eps_of_zero_le hη (acceptsG_of_estimate_near hhat h)

/-- **误差取单边上界时，结论**真的**退成单边**（本文件最重要的一条「负面」结论）。

  $$\hat\sigma\le\sigma+\delta,\quad
    \mathrm{acceptsG}\ \sigma\ \varepsilon\ e
    \;\Longrightarrow\;
    e\le\hat\sigma+(\varepsilon+\delta) .$$

  **比定义多说了什么**：派单式地想证的是「单边误差也能得到**完整**的
  `acceptsG σ̂ (ε+δ) e`」。本定理给出**能证的那一半**（上界），
  并说明另一半**为什么**证不出来：下界 `σ̂ − (ε+δ) ≤ e` 只能由 `σ̂ − δ ≤ σ` 提供，
  而单边前件里**没有**它；`δ < 0` 时两者方向相反，故不加 `0 ≤ δ` 就没有下界。

  于是「单边够用」的正确读法**不是**「省掉一半假设」，而是「**结论**也只拿一半」——
  这是本文件拦下的**第二个**过强断言。 -/
theorem acceptsG_nonsym_upper {β : Type} [AddCommGroup β] [LE β] [AddRightMono β]
    [IsTrans β (fun x y => x ≤ y)] {σ σhat ε δ e : β}
    (hhi : σ ≤ σhat + δ) (h : acceptsG σ ε e) : e ≤ σhat + (ε + δ) := by
  have h1 : σ + ε ≤ (σhat + δ) + ε := add_le_add_left hhi ε
  have key : (σhat + δ) + ε = σhat + (ε + δ) := by
    rw [add_assoc, add_comm δ ε]
  rw [← key]
  exact IsTrans.trans _ _ _ h.2 h1

end Core

/-! ### §2.4 载体边界：交换律**被真的用到**了

⚠ **本节的结论与派单式的预期相反**，此处如实记录（D-022 反空泛）：

* 派单建议用 `2×2` 整数矩阵当「非交换加法群」反例 —— **这是错的**。
  矩阵加法是**逐分量**相加，而 `ℤ` 的加法交换，故
  `Matrix (Fin 2) (Fin 2) ℤ` 上的加法**是交换的**（它的实例就是 `AddCommGroup`）。
  同一个「矩阵不交换」的直觉只对**乘法**成立，而乘法不进 `AddGroup`。
* 于是本文件**无法**用一个初等的具体载体展示「非交换加法群」；
  非交换加法群（例如正则表示或自由群）在 Mathlib 里需要 `FreeGroup` /
  `Equiv.Perm` 之类的构造，本节不引入（会把一个**结构说明**变成一件工程）。

**由此得到的真实结论**：核心定理 `acceptsG_of_estimate_near` 的载体必须是
**交换**加法群，因为两处放缩各需要一次 `δ + ε = ε + δ` 的重排。
本文件把这一条**写进定理签名**（§2 用 `AddCommGroup`），而不是靠注释口头声明。
下面这条定理把「交换律真的被用到」落成可引用的形式。 -/

/-- **交换律在结论里被用到**：核心定理的结论要求 `σ̂ + (ε + δ)`；
而放缩给出的是 `σ̂ + (δ + ε)`。两者相等**只能**靠交换律。

  **比定义多说了什么**：这条把「载体必须交换」这个判断从一个口头说法
  变成一条**关于加法群本身**的命题：在**任意** `AddCommGroup` 上，
  `a + (b + c) = a + (c + b)` 成立；而在非交换加法群上它**不**一般成立。
  于是 §2 用 `AddCommGroup` 不是「图省事」，而是**被结论的形状逼出来的**。 -/
theorem add_swap_inner {β : Type} [AddCommGroup β] (a b c : β) :
    a + (b + c) = a + (c + b) := by
  rw [add_comm b c]

/-- **载体边界的另一面**：`acceptsG` 的**定义**不需要交换律（只要 `AddGroup` + `LE`），
  §1 的定理也不需要；只有 §2 的三角合成需要。这条把两层要求**分开写清**。 -/
theorem acceptsG_def_carrier (σ ε e : Int) :
    acceptsG σ ε e ↔ (σ - ε ≤ e ∧ e ≤ σ + ε) :=
  Iff.rfl

/-! ===========================================================================
  §3  与具体版的一致性（`Real` 只在这一节出现）

  ⚠ `FitBoundaryN.accepts` 在命名空间 `FateV2.ErrorN` 里（不是 `FateV2.Error`），
  故本节用全名 `FateV2.ErrorN.accepts` 引用，避免 `open` 引入歧义。
  =========================================================================== -/

/-- **【一致性】具体版 `accepts` 就是泛化版 `acceptsG` 在 `ℝ` 上的实例**。

  **比定义多说了什么**：`FitBoundaryN.accepts` 与 `acceptsG` 在源码里是**两处各写一遍**
  同一个命题，此前**没有**任何定理把它们连起来。本定理说明
  T46 在 `Real` 上的结论**直接适用**于泛化层（§3.2 就是第一个例子：
  由它**反推**出 T46 的原定理）。

  证明是 `Iff.rfl`：右端就是左端的定义展开（`ℝ` 上 `-`、`+`、`≤` 是同一批实例），
  因此**不借 `propext`**——与 T28 的 `isFitBoundaryN_iff_isBoundaryPoint` 同一手法。 -/
theorem accepts_eq_acceptsG (σ ε e : Real) :
    FateV2.ErrorN.accepts σ ε e ↔ acceptsG σ ε e :=
  Iff.rfl

/-- **T46 的 `accepts_of_estimate_near` 是 §2 核心定理的**实例**（不是平行结论）**。

  **比定义多说了什么**：T46 在 `Real` 上**单独证过**同一命题（用 `abs_le.mp` + `linarith`）；
  本定理证明它可以从泛化层**一次导出**——于是「泛化不改语义」有了双向严格接口：
  下行（具体 ⟹ 泛化，§3.1 `Iff.rfl`）、上行（泛化 ⟹ 具体，本条）。
  `|σ̂ − σ| ≤ δ` 用 `abs_le` 拆成 `±δ`：**这一步**要用 `ℝ` 的 `abs`，
  泛化层不涉及它 —— 这正是「对齐只在边界处做」的具体形态。 -/
theorem accepts_of_estimate_near_via_general {σ σhat ε δ e : Real}
    (hhat : |σhat - σ| ≤ δ) (h : FateV2.ErrorN.accepts σ ε e) :
    FateV2.ErrorN.accepts σhat (ε + δ) e := by
  have hab : σhat - δ ≤ σ ∧ σ ≤ σhat + δ := by
    obtain ⟨h1, h2⟩ := abs_le.mp hhat
    constructor
    · linarith
    · linarith
  exact (accepts_eq_acceptsG σhat (ε + δ) e).2
    (acceptsG_of_estimate_near hab ((accepts_eq_acceptsG σ ε e).1 h))

/-! ===========================================================================
  §4  「合格判据」的公理化 —— 与 T28 的 `VerdictAxioms` **平行**

  T28 抽象的是「边界点」判据 `IsBoundaryPoint`；本节抽象的是**带宽**判据。
  对应关系：

  | T28（边界点） | 本节（带宽） |
  |---|---|
  | `unique`：`σ` 被唯一决定 | `center`：`σ` 在自己带里（有解性） |
  | `iff_min`：判据 ⟺ 取到 + 下界 | `mono_eps`：带宽**单调**（放宽） |
  =========================================================================== -/

/-- **【公理化】带宽判据的公理**（与 `VerdictAxioms` 平行）。

  两条公理（都**不是**空壳，见 §4.1–§4.3）：

  * `center`：`0 ≤ ε` 时 `σ` **自己**合格 —— 判据的**有解性**。
    ⚠ **必须**带 `0 ≤ ε`：§1 已证无条件版本是**假的**（`ε = -1` 时中心出带）。
  * `mono_eps`：`ε ≤ ε'` 时放宽带宽**不丢**已合格的元素 —— 判据在 `ε` 上的**单调性**。

  **比 `acceptsG` 的定义多说了什么**：定义只写两个不等式，**既不保证有解、
  也不保证单调**。本结构与 §4.1 一起把「什么样的一组性质才算带宽判据」
  钉成可编译的对象 —— 于是「换个判据」这件事不再只能靠眼力比较。 -/
structure BandAxioms {β : Type} [AddGroup β] [LE β] (P : β → β → β → Prop) : Prop where
  /-- `0 ≤ ε` 时中心点合格（有解性）。 -/
  center : ∀ (σ ε : β), 0 ≤ ε → P σ ε σ
  /-- 放宽带宽不丢已合格的元素（单调性）。 -/
  mono_eps : ∀ (σ ε ε' e : β), ε ≤ ε' → P σ ε e → P σ ε' e

/-- **【§4 主定理之一】`acceptsG` 满足 `BandAxioms`**。

  **比定义多说了什么**：把 §1 的两条定理（`acceptsG_self_of_nonneg` 与
  `acceptsG_mono_eps`）**打包成结构实例**，于是下游可以只对着 `BandAxioms`
  写通用引理，而不必每次重证。

  ⚠ 载体与 §1 一致：`AddGroup + LE + AddLeftMono + AddRightMono + IsTrans`；
  `mono_eps` 那条要 `IsTrans`，`center` 那条要 `AddLeftMono` —— 两半各要一个，
  合起来才够（这是「公理化的代价」的精确形状）。 -/
theorem acceptsG_bandAxioms {β : Type} [AddGroup β] [LE β] [AddLeftMono β]
    [AddRightMono β] [IsTrans β (fun x y => x ≤ y)] :
    BandAxioms (fun (σ ε e : β) => acceptsG σ ε e) where
  center := fun (_σ : β) (ε : β) (hε : 0 ≤ ε) => acceptsG_self_of_nonneg hε
  mono_eps := fun (σ : β) (ε : β) (ε' : β) (e : β) (hε : ε ≤ ε') (h : acceptsG σ ε e) =>
    acceptsG_mono_eps hε h

/-- **抽象层推具体**：**任一** `BandAxioms` 判据都满足「中心点合格 + 放宽不丢」。

  **比定义多说了什么**：方向是「**抽象层 → 具体层**」——任何具体判据只要被证
  `BandAxioms`，就**自动**获得这两条性质，不必针对那个判据重证。
  与 T28 的 `verdictAxioms_unique` 同一手法。 -/
theorem bandAxioms_center_of {β : Type} [AddGroup β] [LE β]
    {P : β → β → β → Prop} (hP : BandAxioms P) (σ ε : β) (hε : 0 ≤ ε) :
    P σ ε σ :=
  hP.center σ ε hε

/-- **抽象层推具体（单调那一半）**。 -/
theorem bandAxioms_mono_of {β : Type} [AddGroup β] [LE β]
    {P : β → β → β → Prop} (hP : BandAxioms P) (σ ε ε' e : β)
    (hε : ε ≤ ε') (h : P σ ε e) : P σ ε' e :=
  hP.mono_eps σ ε ε' e hε h

/-! ### §4.1 第二个实例：**宽判据**（语法与 `acceptsG` 不同，且真的更宽） -/

/-- **宽判据**：`e ≥ σ - ε`（**只**要下界，丢掉上界）。

  与 `acceptsG` 的差别：`acceptsG` 是**两侧**夹逼，本判据只要求**一侧** ——
  语法上明显不同，且**结论更强**（更宽）。
  它是 `BandAxioms` 的**非平凡实例**：说明抽象不是「把 `acceptsG` 抄一遍」。 -/
def wideCriterion {β : Type} [AddGroup β] [LE β] (σ ε e : β) : Prop :=
  σ - ε ≤ e

/-- **`acceptsG` ⟹ 宽判据**（`acceptsG` 更强 ⟹ 它的结论在宽判据下也成立）。 -/
theorem acceptsG_imp_wide {β : Type} [AddGroup β] [LE β] {σ ε e : β}
    (h : acceptsG σ ε e) : wideCriterion σ ε e :=
  h.1

/-- **【§4 第二个实例】宽判据**也**满足 `BandAxioms`**。

  **与 `acceptsG_bandAxioms` 的区别**：`mono_eps` 只要 `AddRightMono`（`sub_le_sub_left`
  给 `σ - ε' ≤ σ - ε`，随后 `IsTrans` 串一次），`center` 仍要 `AddLeftMono`
  （`sub_le_self`）。两个**语法不同**的判据都满足同一组公理 —— 抽象**不空**。 -/
theorem wideCriterion_bandAxioms {β : Type} [AddGroup β] [LE β] [AddLeftMono β]
    [AddRightMono β] [IsTrans β (fun x y => x ≤ y)] :
    BandAxioms (fun (σ ε e : β) => wideCriterion σ ε e) where
  center := fun (σ : β) (_ε : β) (hε : 0 ≤ _ε) => sub_le_self σ hε
  mono_eps := fun (σ : β) (ε : β) (ε' : β) (e : β) (hε : ε ≤ ε')
    (h : wideCriterion σ ε e) => IsTrans.trans (σ - ε') (σ - ε) e
    (sub_le_sub_left hε σ) h

/-! ### §4.2 抽象**有排除力**：自然弱化被排除 -/

/-- **「只要上界」判据**（反例）：只留上界 `e ≤ σ + ε`。 -/
def upperOnlyCriterion {β : Type} [AddGroup β] [LE β] (σ ε e : β) : Prop :=
  e ≤ σ + ε

/-- **`upperOnlyCriterion` 满足 `mono_eps`**（放宽上界显然不丢元素）。 -/
theorem upperOnly_mono {β : Type} [AddGroup β] [LE β] [AddLeftMono β]
    [IsTrans β (fun x y => x ≤ y)] (σ ε ε' e : β) (hε : ε ≤ ε')
    (h : upperOnlyCriterion σ ε e) : upperOnlyCriterion σ ε' e :=
  IsTrans.trans e (σ + ε) (σ + ε') h (add_le_add_right hε σ)

/-- **【§4 排除力】限制版 `BandAxioms` 能被 `upperOnlyCriterion` 满足** ——
  于是「抽象有没有排除力」必须问**具体的公理组合**，不能笼统说「有」。

  **比定义多说了什么**：本条说明 `mono_eps` **单独**并不是判据的实质内容：
  任何「越放宽越松」的判据都满足它。**实质内容在 `center`** ——
  而 `center` 恰恰要求 `0 ≤ ε` 时中心合格，`upperOnlyCriterion` 在 `ε ≥ 0` 时
  **也**满足（`σ ≤ σ + ε`）。故这两条公理**合起来仍不足以**钉住 `acceptsG`：
  §4.3 会把这一点说清（抽象是**必要条件**，不是**充分条件**）。

  ⚠ 这与 T28 的结论**不同**：`VerdictAxioms` 的两条公理**恰好**钉住了
  `IsBoundaryPoint`（`verdictAxioms_iff_boundaryPoint`）；本节的两条**钉不住**。
  这个差别本身是本文件的一个重要发现，写在这里而不是藏起来。 -/
theorem upperOnly_mono_band {β : Type} [AddGroup β] [LE β] [AddLeftMono β]
    [AddRightMono β] [IsTrans β (fun x y => x ≤ y)] :
    ∃ P : β → β → β → Prop,
      (∀ (σ ε : β), 0 ≤ ε → P σ ε σ) ∧
      (∀ (σ ε ε' e : β), ε ≤ ε' → P σ ε e → P σ ε' e) :=
  ⟨fun (σ ε e : β) => upperOnlyCriterion σ ε e,
    fun (σ : β) (ε : β) (hε : 0 ≤ ε) => by
      have h1 : σ + 0 ≤ σ + ε := add_le_add_right hε σ
      rw [add_zero] at h1
      exact h1,
    fun σ ε ε' e hε h => upperOnly_mono σ ε ε' e hε h⟩

/-! ### §4.3 汇总（账实核对只读一处） -/

/-- **本文件全部结果的见证汇总**（D-022 反空泛：账实核对只读一处）。

  逐项对照：定义 / §1 三条 / §2.4 / §3。全部在 `ℤ`（`AddCommGroup` 的实例）或
  `ℝ`（§3 需要）上，故本条带三公理；§1 / §2 的**每条**定理本身是**零公理**的
  （见 `_报告/T50-进度.md` 的实测表）。 -/
theorem accepts_general_summary :
    -- 定义是纯粹的合取（`Iff.rfl`）
    (∀ (σ ε e : Int), acceptsG σ ε e ↔ (σ - ε ≤ e ∧ e ≤ σ + ε)) ∧
    -- §1：`ε = 0` 时带宽退化成一个点（只要 `AddGroup` + `LE`）
    (∀ (σ : Int), acceptsG σ 0 σ) ∧
    -- §1：带宽加 0 不变
    (∀ (σ ε e : Int), acceptsG σ (ε + 0) e ↔ acceptsG σ ε e) ∧
    -- §3：具体版与泛化版在 `ℝ` 上逐字等价
    (∀ (σ ε e : Real), FateV2.ErrorN.accepts σ ε e ↔ acceptsG σ ε e) ∧
    -- §2.4：交换律在结论里被用到（`a + (b+c) = a + (c+b)`）
    (∀ (a b c : Int), a + (b + c) = a + (c + b)) :=
  ⟨fun (_σ : Int) (_ε : Int) (_e : Int) => Iff.rfl,
    fun (σ : Int) => acceptsG_self_zero σ,
    fun (σ : Int) (ε : Int) (e : Int) => acceptsG_add_zero_band σ ε e,
    fun (_σ : Real) (_ε : Real) (_e : Real) => Iff.rfl,
    fun (a : Int) (b : Int) (c : Int) => add_swap_inner a b c⟩

end FateV2.Error.AcceptsGeneral
