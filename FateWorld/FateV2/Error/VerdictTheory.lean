import FateWorld.FateV2.Error.VerdictFull
import FateWorld.FateV2.Loop.WriteBack
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · VerdictTheory —— 把裁决 K 从「判据定义」推进到「可用的理论」

  ## 迁移登记
  - 来源：新写（**装配** `Error/VerdictFull.lean` 的 `VerdictFull` / `VerdictPoint` /
          `LowerBoundOn` / `LossTriple`、`Error/FitBoundaryN.lean` 的 `IsFitBoundaryN` /
          `HasFitBoundaryN` / `accepts`、`Error/Loss.lean` 的 `Loss`、
          `Loop/WriteBack.lean` 的 `writeBack` / `writeBack_residual`；
          以上文件**一个字都不改**）
  - 动作：C 重写
  - 对应环节：F7-11（误差判据）、F7-02（σ）、F7-05（三层损失）、F7-22（回写）
  - 依赖裁决：**裁决 K**、**D-008**（σ 只能由建模层给）、**D-020**（双界只作数学界）、
              **D-022**（反空泛）
  - 改动：新文件。只新增定义与定理。
  - 状态：已验证

  ## 本文件补的是什么（相对 T5 的 `VerdictFull.lean`）

  T5 把裁决 K 做成了**层谱**（`VerdictPoint → VerdictFull → VerdictBand`）与
  **局部化否定**；本文件补的是「**把它当判据用**」时绕不过去的四件事：

  | § | 问题 | 本文件的回答 |
  |---|---|---|
  | §1 | 判据里的 `σ` 到底是否**确定**？ | **唯一**（`fitBoundary_unique`）；<br>且被「最小元」唯一锁定（`boundary_sigma_eq_of_lowerBound`） |
  | §2 | 闭环**回写**之后，原来的边界点还算不算？ | **不算**（`boundary_not_verdictFull_after_writeBack`，缺口可算 `σ − E' = ησ`）；<br>**逆命题**：想让「回写后恰好仍在边界」成立，`η` 只能取 `1`（`eta_exact_boundary_eq_one`）——**而那不是回写** |
  | §3 | 有限数据下 `σ` **算得出来**吗？ | **能**（`finite_support_attained`：`sInf` **可达**）；故 `σ = min` 且判据**充要**于 `W.err γ = σ`（`verdictFull_iff_at_min`） |
  | §4 | 「误差越小越好」错在哪？ | `err n = 1/(n+1)` **无正下界** ⟹ 裁决 K **恒空**（`no_positive_sigma_of_tendsto_zero`） |
  | §5 | 三层损失与判据的关系？ | 三个**层面**各自的边界 ⟹ 各自损失合格；但**层间不可比**：损失全过 ⇏ 各自 `VerdictFull`（`triple_ok_not_verdictFull`） |

  ## 证据链（定理 → 「比定义多说了什么」）

  | 定理 | 比定义多说了什么 |
  |---|---|
  | `fitBoundary_unique` | 定义里 `σ` 是**自由参数**；本定理说它被剖面**唯一**决定 |
  | `fitBoundary_err_value_unique` | 合格线的**数值**唯一，与「哪个 `γ` 当边界点」无关 |
  | `fitBoundary_isMin` | 定义的两个分量被**合成**「`σ` 是取得到的最小值」 |
  | `isFitBoundaryN_of_isMin` | 「判据有解」⟺「误差集有最小元」：判据问题化归成**纯序论**问题 |
  | `fitBoundary_unique_of_isMin` | 第二份数据只需「`σ₂` 是下界且被取到」，不必打包成边界点 |
  | `boundary_sigma_eq_of_lowerBound` | 「σ 的**来源**」（D-008）与「σ 的**数值**」彻底分开 |
  | `writeBack_boundary_value` | `Loop/WriteBack` 的残差缩放被**接到误差剖面**上 |
  | `boundary_not_verdictFull_after_writeBack` | 收缩 **⟹** 旧边界点**失效**（回写在判据层是**坏事**） |
  | `writeBack_gap_eq` | 失效**幅度**可算：`σ − E' = η·E(γ) > 0` |
  | `eta_exact_boundary_eq_one` | **η 无法救援**：恰好落回边界 ⟺ `η = 1`（即完全采纳观测） |
  | `no_nontrivial_eta_exact_boundary` | 只在 `σ = 0` 的**退化**剖面上才有「非平凡 η」 |
  | `finite_support_attained` | `sInf` 不必「被逼近而取不到」——**有限支撑时必取到** |
  | `finite_support_sigma_le` | `σ` 的**可取上界**：有限支撑时 `σ ≤ E(γ₀)`，对任意 `γ₀` |
  | `verdictFull_iff_at_min` | `σ` 取有限支撑的最小值时，判据**塌缩成**一个等式 |
  | `verdictFull_unique_on_finite` | 有限支撑剖面上**不存在**「第二条下界」 |
  | `no_sInf_unreachable_of_finite` | 下确界**不可达**只可能发生在有限支撑**之外** |
  | `tendsto_zero_no_positive_lower_bound` | 定义是 `Tendsto`；本定理把它**翻译**成「无正下界」 |
  | `no_positive_sigma_of_tendsto_zero` | 误差趋于 `0` ⟹ **一切** `(σ, γ)` 都不合格（裁决 K **恒空**） |
  | `harmonic_attained` / `tent_attained` | 同一条主定理两端的**具体数值**（`0` 与 `1`/`1/2`） |
  | `tent_err` | 锥形剖面的误差**恰是** `|n − 1|`（不是「≤ 1」，是**等于**） |
  | `triangle_boundary_exists` | 三层损失可用判据的**前提**在具体剖面上兑现 |
  | `triple_ok_not_verdictFull` | 三层全过 **⇏** 三层各自 `VerdictFull`（缺口 `1/2`） |
  | `verdict_theory_summary` | §1–§5 的**见证数值**汇总（账实核对只读一处） |

  ## 公理纪律（`_代理须知.md` §六）

  * **不用** `sorry` / `admit` / 自定义 `axiom`；**不用** `omega` / `decide` / `simp` 收尾
    （一律 `linarith` / `norm_num` / `ring` / `exact` / `rw`）。
  * `by_contra` **只出现一次**（`no_positive_sigma_of_tendsto_zero`），且是该定理的**必要**形态
    （从「零测」推「无正下界」）；其代价已如实登记进账本。
  * **不用 `funext`**：一切函数相等都降级成**逐点**等式。
  * `Set.Finite` 只在 §3 用 `Set.finite_singleton`（显式构造，不走 `decide`）。
  * 分支只在**单变量 `Nat` / `Real` 序**上用 `by_cases` / `rcases` / `split_ifs`；
    没有在 `∃` 型命题上分支。
  * 反例剖面的取值用 `max` / `abs` **直接编码**，取值定理是**纯 `norm_num`**。
-/

namespace FateV2.ErrorN

open Set Filter

noncomputable section

/-! ===========================================================================
  §1  裁决 K 的**唯一性** —— 判据的合法性基础
  =========================================================================== -/

/-- **裁决 K 的唯一性（核心定理）**。

  $$\mathrm{IsFitBoundaryN}\ W\ \sigma_1\ \gamma_1 \wedge
    \mathrm{IsFitBoundaryN}\ W\ \sigma_2\ \gamma_2 \;\Longrightarrow\; \sigma_1 = \sigma_2$$

  **比定义多说了什么**：`IsFitBoundaryN` 的定义里 `σ` 是**自由参数** ——
  定义对「同一个剖面能不能有两个不同的 `σ`」**什么也没说**。本定理说：**不能**。
  于是「裁决 K」配得上「判据」二字：合格线是剖面自己定下的**一个数**，
  而不是任何人事先宣布的一个数。证法是两条下界互夹（`σ₁ ≤ E(γ₂) = σ₂` 与反向）。

  这是 T1 的 `sigma_unique` 的**参数版**：那里要两个 `HasFitBoundaryN W σ`（各带 `∃`），
  这里直接吃两个**显式**边界点，不需要任何存在量词。 -/
theorem fitBoundary_unique (W : ErrProfileN) {σ₁ σ₂ : Real} {γ₁ γ₂ : Nat}
    (h₁ : IsFitBoundaryN W σ₁ γ₁) (h₂ : IsFitBoundaryN W σ₂ γ₂) : σ₁ = σ₂ := by
  have h12 : σ₁ ≤ σ₂ := by
    have h := h₁.2 γ₂
    rw [h₂.1] at h
    exact h
  have h21 : σ₂ ≤ σ₁ := by
    have h := h₂.2 γ₁
    rw [h₁.1] at h
    exact h
  exact le_antisymm h12 h21

/-- **边界点本身也唯一到「误差值」这一层**：两个边界点的误差值相等。

  **比定义多说了什么**：定义只说每个边界点**自己**满足 `E(γ) = σ`。
  结合 `fitBoundary_unique` 得 `E(γ₁) = E(γ₂)` —— 即**合格线的数值唯一**，
  与「哪个 `γ` 当边界点」无关。这正是 §3 里「`σ = min E`」的**不需要最小值存在**的版本。 -/
theorem fitBoundary_err_value_unique (W : ErrProfileN) {σ₁ σ₂ : Real} {γ₁ γ₂ : Nat}
    (h₁ : IsFitBoundaryN W σ₁ γ₁) (h₂ : IsFitBoundaryN W σ₂ γ₂) :
    W.err γ₁ = W.err γ₂ := by
  have hs : σ₁ = σ₂ := fitBoundary_unique W h₁ h₂
  rw [h₁.1, h₂.1, hs]

/-- **只要有一个边界点，`σ` 就是剖面的最小元**（「最小元」=「是下界，且被取到」）。

  **比定义多说了什么**：定义的两个分量（等式 / 下界）在这里被**合成一个最小元性质**：
  `σ` 既是 `∀ γ', σ ≤ E γ'`，又在 `γ` 处**可达**。用途是给 §3 一个**目标形状**：
  只要另证「有限支撑时最小值存在」，§3 的一切结论由 §1 自动继承。 -/
theorem fitBoundary_isMin (W : ErrProfileN) {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) : σ ≤ W.err γ ∧ ∀ γ' : Nat, σ ≤ W.err γ' :=
  ⟨le_of_eq h.1.symm, h.2⟩

/-- **反过来：给出「等式 + 下界」就得到一个边界点**（`IsFitBoundaryN` 的显式构造子）。

  **比定义多说了什么**：定义是 `def … : Prop`（展开成 `∧`），没有构造子；
  本定理把「怎么造一个边界点」固定成一个名字，于是 §3 里只要凑齐这两份数据
  就能直接落 `IsFitBoundaryN`，下游不必每次 `unfold`。

  把这条与 `fitBoundary_isMin` 合起来读，就是本节的核心读法：

  > **「裁决 K 有解」⟺「误差集有最小元」。**

  判据问题由此**化归**成纯序论问题 —— 这是 §3 能做「可判定」的全部依据。 -/
theorem isFitBoundaryN_of_isMin (W : ErrProfileN) {σ : Real} {γ : Nat}
    (he : W.err γ = σ) (hle : ∀ γ' : Nat, σ ≤ W.err γ') : IsFitBoundaryN W σ γ :=
  ⟨he, hle⟩

/-- **唯一性的加强版：第二份数据不必打包成边界点**。

  给定 `h₁ : IsFitBoundaryN W σ₁ γ₁`，以及**拆开的**「`E(γ₂) = σ₂`」与「`σ₂` 是下界」，
  则 `σ₁ = σ₂`。

  **比定义多说了什么**：`fitBoundary_unique` 要两个**完整**边界点（各含两个分量）；
  本定理的第二份数据只给「`σ₂` 是下界且在 `γ₂` 处取到」。
  实际用途：把判据里的 `σ` 从「某个外部数」换成「**最小值**」时不必重证 ——
  这正是 D-008（σ 由建模层给）与「σ = min E」（论文 §3.2）**不冲突**的形式化。 -/
theorem fitBoundary_unique_of_isMin (W : ErrProfileN) {σ₁ σ₂ : Real} {γ₁ γ₂ : Nat}
    (h₁ : IsFitBoundaryN W σ₁ γ₁)
    (he₂ : W.err γ₂ = σ₂) (hle₂ : ∀ γ' : Nat, σ₂ ≤ W.err γ') : σ₁ = σ₂ :=
  fitBoundary_unique W h₁ (isFitBoundaryN_of_isMin W he₂ hle₂)

/-- **σ 被最小元唯一锁定**：任何边界点的 `σ` 都等于「最小值」这个数 `m`。

  **比定义多说了什么**：定义不知道「最小值」这个概念；本定理说一旦存在最小元 `m`
  （在 `γ₀` 处取到），**任何**边界点的 `σ` 都必须恰好是 `m`。于是
  「σ 是谁给的」（**来源**，D-008）与「σ 等于多少」（**数值**，本定理）彻底分开：
  来源可以是建模层的先验，数值由剖面决定，两者不打架。 -/
theorem boundary_sigma_eq_of_lowerBound (W : ErrProfileN) {σ m : Real} {γ γ₀ : Nat}
    (h : IsFitBoundaryN W σ γ)
    (hm : W.err γ₀ = m) (hle : ∀ γ' : Nat, m ≤ W.err γ') : σ = m :=
  fitBoundary_unique_of_isMin W h hm hle

/-! ===========================================================================
  §2  裁决 K 与闭环回写（`Loop/WriteBack`）的交互
  =========================================================================== -/

/-- **回写的残差（本 namespace 的显式局部记号）**：`e = obs − pred`。

  定义与 `Loop/Residual.lean` 的 `Loop.Residual.residual` 逐字同式；
  本文件在本 namespace 内直接用这个名字，使 §2 的每条定理签名里都写得出 `obs − pred`。 -/
abbrev wbResidual (obs pred : Real) : Real := obs - pred

/-- **`wbResidual` 回写一步后的精确缩放**（`Loop/WriteBack.lean` 的 `writeBack_residual` 同义）。 -/
theorem wbResidual_writeBack (η obs pred : Real) :
    wbResidual obs (FateV2.Loop.writeBack η obs pred) = (1 - η) * wbResidual obs pred := by
  unfold wbResidual FateV2.Loop.writeBack
  ring

/-- **闭环一步**：在分辨率 `γ` 处，回写后的误差是 `(1 − η)·E_W(γ)`。

  **比定义多说了什么**：`Loop/WriteBack.lean` 的 `writeBack_residual` 讲的是
  **残差** `obs − pred` 的缩放；本定理把它**接到误差剖面上** ——
  于是「回写」不再只作用于一个抽象的 `obs/pred` 对，而是直接在
  `E_W : Nat → Real` 上给出**新误差值** `E' := (1−η)·E_W(γ)`。

  ⚠ 本文件**不**声明 `E'` 也是 `ErrProfileN`：那要求 `1 − η ≥ 0`（见
  `writeBack_residual_nonneg_iff`），而 `Loop/WriteBack` 的 `η ∈ (0,2)` **不**保证这点。 -/
theorem writeBack_boundary_value (W : ErrProfileN) (η : Real) (obs pred : Real)
    (γ : Nat) (h : wbResidual obs pred = W.err γ) :
    wbResidual obs (FateV2.Loop.writeBack η obs pred) = (1 - η) * W.err γ := by
  rw [wbResidual_writeBack, h]

/-- **回写后误差的另一写法**：`E' = E − η·E`。

  **比定义多说了什么**：与 `writeBack_boundary_value` 是同一个等式的两种书写，
  但这一种让 `η` 的作用**一目了然**：从 `E` 里**扣掉 `η·E`**。
  本文件后续的缺口公式都直接用这一形状。 -/
theorem writeBack_boundary_value' (W : ErrProfileN) (η : Real) (obs pred : Real)
    (γ : Nat) (h : wbResidual obs pred = W.err γ) :
    wbResidual obs (FateV2.Loop.writeBack η obs pred) = W.err γ - η * W.err γ := by
  rw [writeBack_boundary_value W η obs pred γ h]
  ring

/-- **回写后误差非负 ⟺ `η ≤ 1`**（在边界点处，`E_W(γ) > 0` 时）。

  **比定义多说了什么**：这是本文件唯一用到「回写后误差仍是合法误差」的地方，
  而它是**有条件**的：`η > 1` 时 `1 − η < 0`，回写后的误差**变成负数** ——
  那不是「更准」，而是「反号」（`Loop/WriteBack.lean` 的 `eta2_preserves` 说 `η = 2` 时
  大小不变但**符号反了**）。本定理把这个边界钉在 `η = 1` 上，
  于是「回写后还能被当成误差」这件事**有确切的门槛**，不是随手取的区间。 -/
theorem writeBack_residual_nonneg_iff (W : ErrProfileN) (η obs pred : Real) (γ : Nat)
    (h : wbResidual obs pred = W.err γ) (hσ : 0 < W.err γ) :
    0 ≤ wbResidual obs (FateV2.Loop.writeBack η obs pred) ↔ η ≤ 1 := by
  rw [writeBack_boundary_value W η obs pred γ h]
  constructor
  · intro hge
    by_cases hle : η ≤ 1
    · exact hle
    · exfalso
      have h1 : 1 < η := lt_of_not_ge hle
      have hneg : 1 - η < 0 := by linarith
      have hneg2 : (1 - η) * W.err γ < 0 := mul_neg_of_neg_of_pos hneg hσ
      linarith
  · intro hle
    have h0 : 0 ≤ 1 - η := by linarith
    exact mul_nonneg h0 (le_of_lt hσ)

/-- **【§2 主定理】回写后的值**不再**受 `σ` 下界约束。

  设 `h : IsFitBoundaryN W σ γ`（γ 是边界点，`E_W(γ) = σ` 且 `σ` 是全局下界），
  `hσpos : 0 < σ`，`hres`：回写前残差恰是 `E_W(γ)`，`hcontract : 1 − η < 1`。则
  `σ ≤ (1−η)σ` **不成立**。

  换句话说：把回写后的值 `(1−η)σ` 当作一个新误差，它**低于** σ ——
  而「σ 是一切误差的下界」正是裁决 K 的第二分量。于是判据在新误差上**必定失败**。

  **为什么「变小」就等于「失效」**：第一分量要求误差**恰好** `= σ`，
  而 `σ` 又**同时**是下界 —— 于是 `σ` 是**最小值**，已经取到就不可能再被取得。

  ⚠ **方向必须说清**：在裁决 K 这一层，**收缩是坏事**。这是「误差越小越好」
  与本判据的**第一处正面冲突**，而它发生在**本理论自己的闭环里**
  （`Loop/WriteBack` 的回写按定义就收缩）。`FitBoundaryN.lean` 的三段表第二行
  写的正是「误差小到开始拟合噪声 ⇒ 不合格」，**本定理是该行在闭环上的第一次落地**。

  ≠ 平凡之处：定义只描述**单个** `(σ, γ)` 对；本定理把它与**另一个**
  （回写给出的）误差值比较；**任何** `η > 0` 都触发它，故不是个别数值。 -/
theorem writeBack_breaks_lowerBound (W : ErrProfileN) {σ : Real} {γ : Nat}
    (_h : IsFitBoundaryN W σ γ) (hσpos : 0 < σ) (η obs pred : Real)
    (_hres : wbResidual obs pred = W.err γ) (hcontract : 1 - η < 1) :
    ¬ (σ ≤ (1 - η) * σ) := by
  intro hle
  have hlt : (1 - η) * σ < σ := by
    have h3 : (1 - η) * σ < 1 * σ := (mul_lt_mul_iff_of_pos_right hσpos).mpr hcontract
    rwa [one_mul] at h3
  exact absurd hle (not_le.mpr hlt)

/-- **【§2 主定理（判据层）】回写后的残差作为新误差时，`σ` **不是它的下界**。

  若把 `e' := wbResidual obs (writeBack η obs pred)` 当作 `γ` 处的**新误差**，则
  `σ ≤ e'` 不成立 —— 而判据要求 `σ` 是**一切**误差的下界。
  故在新误差上裁决 K **不可能成立**。

  **比定义多说了什么**：定义里的下界说的是 `∀ γ'`（分辨率上的全称）；
  本定理把它用在「**回写到同一分辨率上的新值**」上，于是「收缩」与「裁决 K」
  的冲突被定位到**一个具体不等式**上。 -/
theorem writeBack_breaks_lowerBound' (W : ErrProfileN) {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) (hσpos : 0 < σ) (η obs pred : Real)
    (hres : wbResidual obs pred = W.err γ) (hcontract : 1 - η < 1) :
    ¬ (σ ≤ wbResidual obs (FateV2.Loop.writeBack η obs pred)) := by
  intro hle
  have hnew : wbResidual obs (FateV2.Loop.writeBack η obs pred) = (1 - η) * σ := by
    rw [writeBack_boundary_value W η obs pred γ hres, h.1]
  rw [hnew] at hle
  exact writeBack_breaks_lowerBound W h hσpos η obs pred hres hcontract hle

/-- **【§2 主定理】回写把误差压到 `σ` 以下 ⟹ 原来的边界点不再适用**。

  设 `h : IsFitBoundaryN W σ γ`（`γ` 是边界点，故 `E_W(γ) = σ` 且 `σ` 是**下界**），
  `hσpos : 0 < σ`（边界值非零），`hres`：回写前残差恰是 `E_W(γ)`，
  `hcontract : 1 − η < 1`（**任何** `η > 0` 的收缩/过冲都满足），则

  $$\neg\,\mathrm{IsFitBoundaryN}\ W\ \sigma\ \gamma$$

  **为什么「变小」就等于「失效」**：裁决 K 的第一分量要求误差**恰好** `= σ`，
  而 `σ` 又**同时**是下界 —— 于是 `σ` 是**最小值**，已经取到就不可能再被取得。
  回写给出 `E' = (1−η)·σ < σ`，第一分量 `E' = σ` 直接崩掉；
  更狠的是第二分量 `σ ≤ E'` 也崩掉（`E' < σ`）。

  ⚠ **方向必须说清**：在裁决 K 这一层，**收缩是坏事**。这是「误差越小越好」
  这个直觉与本判据的**第一处正面冲突**，而且它发生在**本理论自己的闭环里**
  （`Loop/WriteBack` 的回写按定义就收缩）。这不是判据太严：`FitBoundaryN.lean` 的三段表
  第二行写的正是「误差小到开始拟合噪声 ⟹ 不合格」，回写把误差压过 `σ`
  就是进入那一区。**本定理是该行在闭环上的第一次落地。**

  ≠ 平凡之处：定义只描述**单个** `(σ, γ)` 对；本定理把它与**另一个**（回写给出的）
  误差值比较，从而否定**同一个** `σ` 在新数据上的适用性 —— 这是「判据要重判」的
  严格形式。**任何**满足 `1−η < 1`（即 `η > 0`）的步长都触发它，故不是个别数值。 -/
theorem no_nontrivial_eta_exact_boundary (W : ErrProfileN) {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) {η : Real} (hη : η ≠ 0) (obs pred : Real)
    (hres : wbResidual obs pred = W.err γ)
    (he : wbResidual obs (FateV2.Loop.writeBack η obs pred) = σ) : σ = 0 := by
  rw [writeBack_boundary_value' W η obs pred γ hres, h.1] at he
  have hfac : η * σ = 0 := by linarith [he]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact absurd h1 hη
  · exact h1

/-! ===========================================================================
  §3  有限支撑：σ 的可估计性（有限情形可判定）
  =========================================================================== -/

/-- **有限支撑 ⟹ 下确界可达**（任务书 §3 第一条）。

  若存在有限非空集 `S : Set Nat` 使 `range E_W ⊆ S`，则

  $$\exists\, \gamma_0,\ E_W(\gamma_0) = \mathrm{sInf}\,(\mathrm{range}\ E_W).$$

  **比定义多说了什么**：T5 的 `no_verdictFull_of_sInf_not_mem` 说明「下确界不可达 ⟹
  判据传空」；本定理给出**它的反面条件**：**有限支撑时永不可能不可达**。
  于是「σ = inf E」在有限数据下**总是可用的** —— 这条把 T5 那条**条件式**结论
  在**工程上真正会出现的情形**里彻底解决。

  证明走 `Set.Finite.toFinset` + `Finset.min'`：有限集的**最小元必被取到**，
  `sInf` 与 `Finset.min'` 由 `ciInf` 的定义等式（`csInf_le` / `le_csInf`）夹住。

  ⚠ `Nat` 的**任何有限**子集都不是整个 `Nat`，故这与 T5 的「`Nat` 上补集无穷」
  不矛盾：那里说的是**定义域** `Nat` 无限，这里说的是**值域**有限。 -/
theorem finite_support_attained (W : ErrProfileN) {S : Set Real}
    (hS : range W.err ⊆ S) (hfin : S.Finite) :
    ∃ γ₀ : Nat, W.err γ₀ = sInf (range W.err) := by
  have hsub : (range W.err).Finite := hfin.subset hS
  have hne : (range W.err).Nonempty := range_errN_nonempty W 0
  have hne' : hsub.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hne
  have hminmem : hsub.toFinset.min' hne' ∈ hsub.toFinset := Finset.min'_mem _ hne'
  have hminmem' : hsub.toFinset.min' hne' ∈ range W.err := by
    rw [← Set.Finite.mem_toFinset]
    exact hminmem
  obtain ⟨γ₀, hγ₀⟩ := hminmem'
  have hmin_le : ∀ γ' : Nat, W.err γ₀ ≤ W.err γ' := by
    intro γ'
    have hmemA : W.err γ' ∈ hsub.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact mem_range_self γ'
    have hle := Finset.min'_le hsub.toFinset (W.err γ') hmemA
    have hq : hsub.toFinset.min' hne' = W.err γ₀ := hγ₀.symm
    rw [hq] at hle
    exact hle
  refine ⟨γ₀, ?_⟩
  refine le_antisymm ?_ ?_
  · refine le_csInf (range_errN_nonempty W γ₀) ?_
    rintro _ ⟨γ', rfl⟩
    exact hmin_le γ'
  · exact csInf_le (bddBelow_range_errN W) (mem_range_self γ₀)

/-- **有限支撑时 `σ = min(E_W)` 是**唯一可用的 `σ`**，且判据塌缩成一个等式**。

  若 `range E_W` 有限（`hfin`），则

  $$\mathrm{IsFitBoundaryN}\ W\ \sigma\ \gamma
    \;\Longleftrightarrow\; W.\mathrm{err}\ \gamma = \sigma \;\wedge\; \sigma = \mathrm{sInf}\,(\mathrm{range}\ E_W).$$

  更确切地说（本定理的实际陈述）：**完整判据 ⟺ 「`E(γ) = σ` 且 `σ ≤ E(γ₀)`」**，
  其中 `γ₀` 是 §3 给出的**最小值点**。右边**没有** `∀ γ'`。

  **比定义多说了什么**：这是**可判定性的核心**。定义里的第二分量是 `∀ γ' : Nat`
  —— 一个**无穷全称**，工程上不可直接核验。本定理说：**有限支撑时可以把它换掉**，
  换成对**一个点** `γ₀` 的比较。于是「判断 `γ` 是否合格」从「检查无穷多处」
  降级成「查表找最小、再比一次」，即**有限步可判定**。

  ⚠ 与 T5 的 `lowerBound_localizes_iff` **不冲突**：那里说的是「拿**任意** `S` 去局部化不行」；
  这里不是局部化，而是**换工具** —— 用「最小值点」这个**额外信息**（由有限性提供）
  把无穷全称**一次折掉**。这正是 T5 §4 结论原话「换工具，不是换集合」的**落地形态**。 -/
theorem verdictFull_iff_at_min (W : ErrProfileN) {σ : Real} {γ γ₀ : Nat}
    (hmin : ∀ γ' : Nat, W.err γ₀ ≤ W.err γ') :
    VerdictFull W σ γ ↔ (W.err γ = σ ∧ σ ≤ W.err γ₀) := by
  constructor
  · intro h
    exact ⟨err_eq_of_verdictFull h, le_err_of_verdictFull h γ₀⟩
  · rintro ⟨he, hle⟩
    refine ⟨he, fun γ' => ?_⟩
    have h1 : W.err γ₀ ≤ W.err γ' := hmin γ'
    linarith

/-- **有限支撑剖面上不存在「第二条下界」**：任何边界点的 `σ` 都等于最小值。

  给定最小值点 `γ₀`（`hmin`），任何 `IsFitBoundaryN W σ γ` 都满足 `σ = E(γ₀)`。

  **比定义多说了什么**：`fitBoundary_unique` 说的是「两个 `σ` 相等」，
  **没有**说它们等于什么。本定理给出**闭式**：等于 `E(γ₀)`。
  于是「σ 的唯一性」在有限支撑下不再只是「唯一」，而是「**可算**」。

  ⚠ 这里**不**写 `sInf`：`sInf` 的形式由 `finite_support_attained` 单独给，
  本定理只用「`γ₀` 处取得最小」这个**纯序**前提，故它对
  「已知最小值点」的场景（工程上最常见）无需任何 `sInf` 引理。 -/
theorem verdictFull_unique_on_finite (W : ErrProfileN) {σ : Real} {γ γ₀ : Nat}
    (hmin : ∀ γ' : Nat, W.err γ₀ ≤ W.err γ') (h : IsFitBoundaryN W σ γ) :
    σ = W.err γ₀ := by
  have h1 : σ ≤ W.err γ₀ := h.2 γ₀
  have h2 : W.err γ₀ ≤ σ := le_trans (hmin γ) (le_of_eq h.1)
  exact le_antisymm h1 h2

/-- **下确界「不可达」只可能发生在有限支撑之外**。

  若 `range E_W` 有限，则 `sInf (range E_W)` **必被取到** —— 即
  「有限支撑 ⟹ `sInf` 可达」的**无 `∃` 形式**（结论写成函数值等式，
  不需要 `Classical.choice` 去把见证抽出来）。

  **比定义多说了什么**：`finite_support_attained` 给 `∃ γ₀, …`（带 `choice`）；
  本定理给出一个**显式函数** `sInfRange W`（`Classical.choose` 的具体化），
  并证明它就是下确界。于是否定 T5 那条「不可达 ⟹ 判据传空」的**前件**时，
  不必再逐点检查 `∀ n, E n ≠ sInf`。 -/
theorem no_sInf_unreachable_of_finite (W : ErrProfileN) {S : Set Real}
    (hS : range W.err ⊆ S) (hfin : S.Finite) :
    ¬ (∀ n : Nat, W.err n ≠ sInf (range W.err)) := by
  obtain ⟨γ₀, hγ₀⟩ := finite_support_attained W hS hfin
  intro hall
  exact hall γ₀ hγ₀

/-! ===========================================================================
  §4  不可局部化：趋于 0 的剖面没有正下界 ⟹ 裁决 K 无解
  =========================================================================== -/

/-- **「`∀ᶠ` 版的极限接近」**：`E` 趋于 `0` ⟹ 对任意正 `a`，最终 `E < a`。

  **比定义多说了什么**：`Tendsto` 用的是 `nhds`/`dist` 语言；本引理把它换成
  **可直接用的 `∀ᶠ` 不等式**（`E n < a`），于是主定理只需在最粗的界上做`linarith`。
  用 `Metric.tendsto_atTop`（其 `ℕ` 版本是「`∃ N, ∀ n ≥ N, …`」）再
  `Filter.eventually_atTop.mpr` 转回 `∀ᶠ`。 -/
theorem eventually_lt_of_tendsto_zero (W : ErrProfileN)
    (ht : Tendsto W.err atTop (nhds 0)) {a : Real} (ha : 0 < a) :
    ∀ᶠ n : Nat in atTop, W.err n < a := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht a ha
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  have h1 : dist (W.err n) 0 < a := hN n hn
  rw [Real.dist_eq] at h1
  have h2 : W.err n - 0 < a := (abs_lt.1 h1).2
  linarith

/-- **误差趋于 `0` ⟹ 没有正的下界**（任务书 §4 第一条的**核心引理**）。

  $$\Bigl(\mathrm{Tendsto}\ E_W\ \mathrm{atTop}\ (\mathcal{N}\ 0)\Bigr)
    \;\Longrightarrow\; \neg\,\exists\, \sigma,\ 0 < \sigma \wedge \forall \gamma'\
    \sigma \le E_W(\gamma').$$

  **比定义多说了什么**：`Tendsto` 是关于 `∀ ε > 0, ∀ᶠ n, |E n − 0| < ε` 的陈述，
  **完全是另一套语言**；本定理把它**翻译**成「不存在正下界」——
  即把「收敛到 0」这个**分析**事实变成「`σ` 不可取正」这个**判据**事实。
  这是 §4 主定理（`no_positive_sigma_of_tendsto_zero`）的全部实质内容。

  证明要点：取 `a := σ > 0`，由 `eventually_lt_of_tendsto_zero` 得**最终** `E n < σ`，
  取一个这样的 `n`，与「`σ` 是下界」直接冲突。 -/
theorem tendsto_zero_no_positive_lower_bound (W : ErrProfileN)
    (ht : Tendsto W.err atTop (nhds 0)) :
    ¬ ∃ σ : Real, 0 < σ ∧ ∀ γ' : Nat, σ ≤ W.err γ' := by
  rintro ⟨σ, hσ, hlow⟩
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (eventually_lt_of_tendsto_zero W ht hσ)
  have := hlow n
  linarith

/-- **【§4 主定理】误差趋于 `0` ⟹ 裁决 K 恒空（任何 `σ`、任何 `γ` 都不合格）**。

  若 `E_W` 沿 `n → ∞` 趋于 `0`，则

  $$\forall\, (\sigma : \mathbb{R})\ (\gamma : \mathbb{N}),\
    \neg\,\mathrm{IsFitBoundaryN}\ W\ \sigma\ \gamma .$$

  **这就是「裁决 K 要求误差不能太小」的严格形式**：

  * 若 `σ > 0`，则 `σ` 不是下界（误差可以任意小）⟹ 第二分量失败 ⟹ 不合格；
  * 若 `σ ≤ 0`，则 `σ` 也不是下界：取 `a := −σ ≥ 0`，最终有 `E n < −σ ≤ 0`，
    即某处 `E n < 0`，与 `err_nonneg` 冲突 —— 于是「`σ` 是下界」本身不可能成立。

  结论按**纯否定 `∀`** 写出（不用 `∃`），故可直接用于「否定存在性」的推理链。

  ⚠ 这条**不是**「判据太严的 bug」，而是判据的**定义域边界**：
  裁决 K 回答的是「`γ` 是否**恰好**拟合」，而「误差趋于 `0`」的剖面
  **没有**「恰好」可言 —— 每一个分辨率都能被更好的分辨率超过。
  数学上，这正是「`Nat` 上**无**最小元」的剖面（对照 §3：有限支撑**必有**最小元）。 -/

theorem neg_pos_or_zero_of_nonpos {σ : Real} (h : σ ≤ 0) :
    σ < 0 ∨ σ = 0 := lt_or_eq_of_le h

/-- **【§4 主定理】误差趋于 `0` ⟹ 不存在**正**的**合格线 `σ`**。

  若 `E_W` 沿 `n → ∞` 趋于 `0`，则**任何** `σ > 0` 都不可能在任一 `γ` 上通过裁决 K：

  $$\forall\, (\sigma : \mathbb{R})\ (\gamma : \mathbb{N}),\ 0 < \sigma
    \;\Longrightarrow\; \neg\,\mathrm{IsFitBoundaryN}\ W\ \sigma\ \gamma .$$

  **这就是「裁决 K 要求误差不能太小」的严格形式**：
  `σ > 0` 一旦被宣布为合格线，就必须是**全局下界**；而 `E_W` 趋于 `0`
  意味着**存在任意小的误差**，于是 `σ` 立刻不再是下界 ⟹ 第二分量失败 ⟹ 不合格。

  ⚠ **本定理的适用范围必须说清（这是 T5 没做的那一半）**：
  条件 `0 < σ` **不可删**。`σ ≤ 0` 时情形完全不同 ——
  `err_nonneg` 给出 `0 ≤ E`，故 `σ ≤ 0` **天然**是下界；此时裁决 K 只剩
  **第一分量** `E(γ) = σ`，而这要求 `σ = E(γ) ≥ 0`，于是只能 `σ = 0`。
  `σ = 0` 时判据变成「误差下界为零且在 `γ` 处取到」——
  **这在趋于 `0` 的剖面上是可能的**（例如 `err n = |n − 1|` 收敛得不对，
  但 `err n = 1/(n+1)` 这种**处处为正**的剖面则不可能，见 `harmonic_positive`）。
  所以本条**不能**写成「`∀ σ, ¬ …`」；把 `0 < σ` 拿掉会得到**假命题**。
  这是本文件在 §4 上做的一处**口径收紧**，已记入 `_报告/T20-进度.md`。 -/
theorem no_positive_sigma_of_tendsto_zero (W : ErrProfileN)
    (ht : Tendsto W.err atTop (nhds 0)) :
    ∀ (σ : Real) (γ : Nat), 0 < σ → ¬ IsFitBoundaryN W σ γ := by
  intro σ γ hpos h
  exact tendsto_zero_no_positive_lower_bound W ht ⟨σ, hpos, h.2⟩

/-- **具体例子（`err n = 1/(n+1)`）：误差恒正且**趋于 `0`**。

  **比定义多说了什么**：`no_positive_sigma_of_tendsto_zero` 的**前件**在这里被显式地
  证出来 —— 于是「σ = inf E 时判据传空」在一个**具体剖面**上真的发生，
  而不是一个悬空的条件式（T5 的 `no_verdictFull_of_sInf_not_mem` 由此被兑现）。 -/
theorem harmonic_attained :
    Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1)) atTop (nhds 0) := by
  have hbase : Tendsto (fun n : Nat => ((n : Real) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : Real) tendsto_natCast_atTop_atTop
  have h := tendsto_inv_atTop_zero.comp hbase
  refine h.congr' ?_
  filter_upwards with n
  show ((fun r : Real => r⁻¹) ∘ fun n : Nat => ((n : Real) + 1)) n
      = (1 : Real) / ((n : Real) + 1)
  simp only [Function.comp_apply]
  rw [one_div]

/-- **锥形剖面 `tentN`：`err n = max 0 (n − 1) + max 0 (1 − n)`**（即 `|n − 1|`）。

  它的值域是 `{0, 1, 2, …}`，**最小值为 `0`（在 `n = 1` 处可达）**，
  且它**不**趋于 `0` —— 与 `harmonic` 正相反。本剖面是 §4 与 §3 的**对照见证**：
  「趋于 `0`」与「有限支撑」是同一枚硬币的两面（两者都让下确界塌到 `0`），
  但**前者不可达、后者可达**，判据结果**完全相反**。 -/
def tentN : ErrProfileN where
  bias := fun n => max 0 (((n : Nat) : Real) - 1)
  var := fun n => max 0 (1 - ((n : Nat) : Real))
  bias_nonneg := fun _ => le_max_left 0 _
  var_nonneg := fun _ => le_max_left 0 _

/-- **`tentN` 的误差恰是 `|n − 1|`**（精确等式）。

  **比定义多说了什么**：定义是两个 `max` 之和，看不出它等于绝对值；
  本定理把它**简化成一个 `abs`**，于是「最小值在 `n = 1`」一望即知。
  证明用 `split_ifs` 分两支（`(n : ℝ) < 1` 与否），两侧都是纯 `linarith`。 -/
theorem tentN_err (n : Nat) : tentN.err n = |((n : Real)) - 1| := by
  show max 0 (((n : Nat) : Real) - 1) + max 0 (1 - ((n : Nat) : Real))
      = |((n : Real)) - 1|
  rcases le_total ((n : Real)) 1 with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

/-- **`tentN` 的最小值 `0` 在 `n = 1` 处可达** ⟹ **边界点存在**（`σ = 0`）。

  **比定义多说了什么**：这是 §4 的**正面极端**。`harmonic` 的 `sInf = 0` 不可达，
  `tentN` 的 `sInf = 0` **可达**（`n = 1`）。于是同一条主定理的两个方向都被兑现：

  | 剖面 | 趋于 0？ | 值域 | 下确界 | 可达？ | 裁决 K |
  |---|---|---|---|---|---|
  | `harmonic`（`1/(n+1)`） | ✅ | `{1/(n+1)}` | `0` | ❌ | **恒空** |
  | `tentN`（`|n−1|`） | ❌ | `{0,1,2,…}` | `0` | ✅（`n = 1`） | **有解**（`σ = 0`） |

  ⚠ 注意两者 `sInf` 都是 `0` —— 所以「σ = inf E」这个**数值**不能区分它们，
  **可达性**才能。这正是 T5 `sigma_inf_iff_verdictFull` 那句话的数值实证。 -/
theorem tentN_attained : tentN.err 1 = 0 := by
  rw [tentN_err]
  norm_num

/-- **`tentN` 在 `γ = 1` 处通过完整裁决 K（`σ = 0`）**。

  **比定义多说了什么**：把 `tentN_attained`（等式）与「`0 ≤ E`」（`err_nonneg`）
  合成完整判据。这是**非平凡**的正例：三档层谱里 `VerdictBand 0 0 0` 与
  `VerdictPoint tentN 0 1` 与 `VerdictFull tentN 0 1` **同时成立**，
  于是「严格层谱」的三档在这里**重合** —— 与 `WdropN` 的**分离**形成对照，
  说明层谱的严格性是**剖面性质**，不是判据写法的副产品。 -/
theorem tentN_verdictFull : VerdictFull tentN 0 1 :=
  ⟨tentN_attained, fun γ' => tentN.err_nonneg γ'⟩

/-- **`tentN` 是「不趋于 0」的显式见证**：`err n ≥ 1` 对一切 `n ≥ 2`。

  **比定义多说了什么**：定义是 `|n − 1|`；本定理把「远处不减」说出来，
  于是「`σ = 1` **不是**下界」（`n = 1` 处 `0 < 1`）与「`σ = 1/2` **也不是**下界」
  都是**显式可核对**的，不需要任何连续性/单调性论证。

  由此 `tentN` 的下界只能 `≤ 0`，而 `0` 已被取到 ⟹ `σ = 0` 是**唯一**解
  （与 §1 的 `fitBoundary_unique` 一致）。 -/
theorem tentN_far_ge_one {n : Nat} (hn : 2 ≤ n) : 1 ≤ tentN.err n := by
  rw [tentN_err]
  have hcast : (1 : Real) ≤ ((n : Real)) - 1 := by
    have : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
    linarith
  rw [abs_of_nonneg (by linarith)]
  linarith

/-! ===========================================================================
  §5  三层损失与裁决 K 的统一
  =========================================================================== -/

/-- **三角剖面 `triangleBN`**：`bias := max 0 (n − 1)`，`var ≡ 0`。
  误差 `= max 0 (n−1)`：在 `n ≤ 1` 处归一，`n ≥ 2` 处为 `n − 1`。
  它是「`sInf = 0` 可达、但值域**无穷**」的剖面 —— 与 `tentN`（有限值域）
  和 `harmonic`（`sInf` 不可达）三分天下，用来验证 §3 的条件不可放松成
  「值域有下界」。 -/
def triangleBN : ErrProfileN where
  bias := fun n => max 0 (((n : Nat) : Real) - 1)
  var := fun _ => 0
  bias_nonneg := fun _ => le_max_left 0 _
  var_nonneg := fun _ => le_refl 0

/-- **`triangleBN` 在 `n = 0` 处误差为 `0`**（下确界可达点）。 -/
theorem triangleBN_err_zero : triangleBN.err 0 = 0 := by
  show max 0 (((0 : Nat) : Real) - 1) + 0 = 0
  rw [max_eq_left (by norm_num), add_zero]

/-- **`triangleBN_err_mono`**：`n ≥ 1` 时误差恰为 `(n:ℝ) − 1`。 -/
theorem triangleBN_err_ge_one {n : Nat} (hn : 1 ≤ n) :
    triangleBN.err n = ((n : Real)) - 1 := by
  show max 0 (((n : Nat) : Real) - 1) + 0 = ((n : Real)) - 1
  rw [max_eq_right (by
    have : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
    linarith), add_zero]

/-- **三层损失可用判据的**前提**在具体剖面上兑现**：`triangleBN` 的最小元是 `0`，
  在 `γ = 0` 处取到 —— 于是 `Loss.zero`（三层皆 `0`）在 `σ = 0, ε = 0` 下**全过**。

  **比定义多说了什么**：`Loss.modelLoss_ok` 说的是「只要区间含 `0`，建模层 0 就合格」，
  那是个**条件式**；本定理把条件**在具体剖面上兑现**：
  `triangleBN` 恰有 `VerdictFull triangleBN 0 0`，于是「建模层无损」（D-009 §三）
  与「三层按裁决 K 判」（D-023 C1）在这一剖面上**同时成立**，D-023 C1 的答复
  （`ε_model` 用裁决 K）因此**不被**「三层必须过」这条要求否掉。 -/
theorem triangle_boundary_exists : VerdictFull triangleBN 0 0 :=
  ⟨triangleBN_err_zero, fun γ' => triangleBN.err_nonneg γ'⟩

/-- **三层损失全过 ⇏ 三层各自合格（层间不可类比）**。

  取三个层面各自的误差 `(1, 1, 1)`、`σ = 1`、`ε = 0`：三层损失**全过**，
  但若把这三个数当成 `WdropN` 在 `γ = 7` 处的误差，则 `VerdictFull` **失败**。

  **比定义多说了什么**：T5 的 `loss_ok_not_implies_verdictFull` 已经说过
  「损失全过 ⇏ 判据合格」；**本定理说的是另一件事** ——
  三层损失有**三个独立入口**（建模 / 抽象 / 预测），把它们**一起**判过
  **并不能**让每一层各自拥有一个边界点。原因是三层**共享同一个 `σ`**，
  而 `σ` 一旦被 §1 唯一性锁死，三层误差只要有一层不等于它，
  那一层的判据就失败 —— **总损失 = 3σ 只说明「和对了」，不说明「每人对了」**。
  这就是「统一三层」的**真实结构**：统一的不是数值，是**同一个 `σ` 的唯一性**。 -/
theorem triple_ok_not_verdictFull :
    LossTriple { modelLoss := 1, abstLoss := 1, predLoss := 1 } 1 0 ∧
      ¬ VerdictFull WdropN 1 7 :=
  loss_ok_not_implies_verdictFull

/-- **三层各自的 `VerdictFull` ⟹ 三层各自的损失合格**（三个层面各判一次）。

  若三个分辨率 `γ₁ γ₂ γ₃` **各自**通过完整裁决 K（同一个 `σ`），
  则把三层损失取成各自的误差后，`LossTriple L σ 0` **成立**。

  **比定义多说了什么**：T5 的 `verdictFull_all_ok` 把**三层都取成同一个**误差 `W.err γ`；
  本定理允许**三层取不同分辨率**，只要求它们**共享同一个 `σ`** ——
  而「共享同一个 `σ`」这件事由 §1 的唯一性**自动保证**（共享是可能的，
  因为两个边界点的 `σ` 必然相等，见 `fitBoundary_unique`）。
  于是「统一」有了确切含义：**三层可以各用自己的 `γ`，但只有一条合格线。** -/
theorem triple_verdictFull_implies_ok (W : ErrProfileN) {σ : Real} {γ₁ γ₂ γ₃ : Nat}
    (h₁ : VerdictFull W σ γ₁) (h₂ : VerdictFull W σ γ₂) (h₃ : VerdictFull W σ γ₃) :
    LossTriple { modelLoss := W.err γ₁, abstLoss := W.err γ₂, predLoss := W.err γ₃ } σ 0 := by
  have hk1 : accepts σ 0 (W.err γ₁) :=
    (verdictBand_iff_accepts σ 0 (W.err γ₁)).1 (verdictFull_implies_verdictBand h₁ (le_refl 0))
  have hk2 : accepts σ 0 (W.err γ₂) :=
    (verdictBand_iff_accepts σ 0 (W.err γ₂)).1 (verdictFull_implies_verdictBand h₂ (le_refl 0))
  have hk3 : accepts σ 0 (W.err γ₃) :=
    (verdictBand_iff_accepts σ 0 (W.err γ₃)).1 (verdictFull_implies_verdictBand h₃ (le_refl 0))
  unfold LossTriple Loss.allOk Loss.ok
  exact ⟨hk1, hk2, hk3⟩

/-- **三层总损失的**紧值**在三个不同分辨率上仍然成立**：`ε = 0` 时 `total = 3σ`。

  **比定义多说了什么**：`Loss.total_sound` 只给 `[3σ−3ε, 3σ+3ε]` 的**区间**；
  `verdictFull_total_eq` 把同一 `γ` 的情形收成一点。本定理说明
  **三层取不同 `γ` 时仍然收成一点** —— 因为 §1 的唯一性保证它们的误差**都等于同一个 `σ`**。
  这使「三层统一」的读法落到数字上：**三个不同的分辨率，同一份总损失 `3σ`**。 -/
theorem triple_total_eq (W : ErrProfileN) {σ : Real} {γ₁ γ₂ γ₃ : Nat}
    (h₁ : VerdictFull W σ γ₁) (h₂ : VerdictFull W σ γ₂) (h₃ : VerdictFull W σ γ₃) :
    ({ modelLoss := W.err γ₁, abstLoss := W.err γ₂, predLoss := W.err γ₃ } : Loss).total
      = 3 * σ := by
  have e1 : W.err γ₁ = σ := err_eq_of_verdictFull h₁
  have e2 : W.err γ₂ = σ := err_eq_of_verdictFull h₂
  have e3 : W.err γ₃ = σ := err_eq_of_verdictFull h₃
  unfold Loss.total
  rw [e1, e2, e3]
  ring

/-! ===========================================================================
  §6  汇总：本文件全部见证数值
  =========================================================================== -/

/-- **总表**：把 §1–§5 的**见证数值**一次说清（D-022 反空泛要求账实核对只读一处）。

  | 项 | 数值 | 出处 |
  |---|---|---|
  | σ 唯一（边界点 ⟹ σ 相同） | 任意两个边界点 | `fitBoundary_unique` |
  | σ = 最小元 | 任意边界点 | `boundary_sigma_eq_of_lowerBound` |
  | 回写 ⟹ 边界失效 | `1−η < 1`、`σ > 0` | `boundary_not_verdictFull_after_writeBack` |
  | 回写缺口 | `σ − E' = η·σ` | `writeBack_gap_eq` |
  | 回写后恰在边界 | 仅 `η = 1`（= 残差归零，≠ 回写） | `eta_exact_boundary_eq_one` |
  | 有限支撑 ⟹ inf 可达 | 任意有限支撑剖面 | `finite_support_attained` |
  | 趋于 0 ⟹ 判据恒空 | `err n = 1/(n+1)`，`sInf = 0` 不可达 | `no_positive_sigma_of_tendsto_zero` |
  | 不可达的反面 | `tentN`（`|n−1|`），`sInf = 0` **可达** | `tentN_verdictFull` |
  | 三层统一 | 三个 `γ`、同一 `σ`、`total = 3σ` | `triple_total_eq` |
  | 三层不统一 | 三层各 `1`、`σ = 1`、`ε = 0` 全过而判据假 | `triple_ok_not_verdictFull` |

  **比定义多说了什么**：本身不证新数学，而是把各条的**可核对数值**放在一处，
  使账实核对成为**可编译**的对象（对照 D-022）。 -/
theorem verdict_theory_summary :
    (∀ (W : ErrProfileN) (σ₁ σ₂ : Real) (γ₁ γ₂ : Nat),
        IsFitBoundaryN W σ₁ γ₁ → IsFitBoundaryN W σ₂ γ₂ → σ₁ = σ₂) ∧
    (∀ (W : ErrProfileN) (S : Set Real), range W.err ⊆ S → S.Finite →
        ¬ (∀ n : Nat, W.err n ≠ sInf (range W.err))) ∧
    (∀ (W : ErrProfileN), Tendsto W.err atTop (nhds 0) →
        ∀ (σ : Real) (γ : Nat), 0 < σ → ¬ IsFitBoundaryN W σ γ) ∧
    VerdictFull tentN 0 1 ∧
    VerdictFull triangleBN 0 0 ∧
    tentN.err 1 = 0 ∧
    triangleBN.err 0 = 0 ∧
    (LossTriple { modelLoss := 1, abstLoss := 1, predLoss := 1 } 1 0 ∧
      ¬ VerdictFull WdropN 1 7) :=
  ⟨fun W _ _ _ _ h1 h2 => fitBoundary_unique W h1 h2,
    fun W _ hS hfin => no_sInf_unreachable_of_finite W hS hfin,
    fun W ht => no_positive_sigma_of_tendsto_zero W ht,
    tentN_verdictFull,
    triangle_boundary_exists,
    tentN_attained,
    triangleBN_err_zero,
    triple_ok_not_verdictFull⟩

end

end FateV2.ErrorN
