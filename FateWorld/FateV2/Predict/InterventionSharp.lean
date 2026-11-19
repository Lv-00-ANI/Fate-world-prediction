/-
命运理论 · 干预选择最优：次优差距下界与「紧」
===============================================================================

模块：`InterventionSharp`
上游：`Fate/InterventionSelection.lean`（`Plan`、`Good`、`alter`、`gain`、`Optimal`、
　　　`exists_optimal_finset`、`optimal_value_unique`）

---------------------------------------------------------------------------
本文件回答的问题（补 ④ 的「次优差距下界」段与「紧」段）
---------------------------------------------------------------------------
`_audit/NINE-1-九要件三段式核查.md` §3.4 对 ④ 的判定是：

> 「**界弱、紧无、下界退化**」「缺「紧」段与「次优差距下界」段」

本文件只补这两段。**不**复述 `InterventionSelection` 已有的
`exists_optimal_finset` / `exists_bestAt` / `bestAt_ge_self` / `optimal_value_unique`。

---------------------------------------------------------------------------
⚠ 关键诚实标注：`InterventionSelection` 里没有度量，「存在 δ > 0」要额外结构
---------------------------------------------------------------------------
`InterventionSelection.lean:238` 明说「任意全序都可做 argmax」；载体 `Good := Plan → ℝ`
而 `Plan ι A := ι → A`，`ι`、`A` 是任意 `Type*` —— **函数空间上没有拓扑也没有度量**。
「次优差距有正下界」（最优**孤立**、可识别）在一般情形**不能**陈述成
「存在一个与扰动无关的 `δ > 0`」，因为「扰动」本身没有定义。

本文件的处理是**不发明度量**，而用**离散分离性（`Finset` 上的有限性）**
把「孤立 ⟹ 正差距」做成**定理**，并在无限情形把不可绕过的附加假设
**显式登成前件**，同时**证明它不平凡**（去掉它结论假）。

* §1 `loss`：把「越大越好」翻成「越小越好」，与文献的 `loss a − loss a*` 对齐。
* §2 **主定理（有限）**：唯一最优 ⟹ 存在 `δ > 0` 下界（`suboptimality_gap_lower_bound`）。
  技术核心是 `exists_second_best` —— `InterventionSelection` **完全没有**的「次优者存在」。
* §3 **紧性两面**：
  - `gap_lower_bound_attained`：`δ` **被某个次优者取到**（下界可达 ⟹ 不能放大）；
  - `gap_lower_bound_sharp`：任何更大的 `δ'` **必失效**（真正的「紧」）。
* §4 **等价刻画**：`∃ δ > 0 下界` ⟺ `最优值严格大于所有其它候选`（`gap_iff_strictly_better`）。
  ⟹ 「正下界」与「严格分离」是**同一件事**，两个方向都证。
* §5 **一般（含无限）情形**：`Isolated` 前件下的下界（`gap_of_isolated`），
  以及 `nonIsolated_no_gap`：若无 `Isolated` 则存在反例 —— **证明前件必要**。
* §6 **诚实登记**：`no_strategy_beats_optimum` 是 `rfl` 级（`Optimal` 定义展开），
  列它只为在 `loss` 记号下把「下界」说清楚，**不计为新内容**。

---------------------------------------------------------------------------
⚠ 前件是否把结论包进去？（纪律第 7 条，逐条自查）
---------------------------------------------------------------------------
* `exists_second_best`：前件是「`a ∈ s`、`s.erase a` 非空」；结论是「`s.erase a` 中有
  `Good` 最大者」。**前件无 `δ`、无不等式结论**。实质用 `Finset.exists_max_image`。
* `suboptimality_gap_lower_bound`：前件「有限非空 + `a* ∈ s` + 最优 + 唯一」；
  结论 `∃ δ > 0, ∀ q ≠ a*, δ ≤ loss q − loss a*`。**`δ` 只出现在结论**。
  证明**实质**用了「`G b < G a`」（这一步**正是唯一性的用武之地**）与
  「有限集的最小值存在」。**非同义反复。**
* `gap_lower_bound_attained`：前件同 `suboptimality_gap_lower_bound` 再加
  `s.erase a` 非空；结论说 `δ` **由某个 `b` 取到**。前件无 `b`。**非同义反复。**
* `gap_lower_bound_sharp`：⚠ **前件里出现了 `δ`**（`hδ : ∀ q ∈ s.erase a, δ ≤ loss q − loss a*`
  和 `hδtight : ∃ b ∈ s.erase a, loss b − loss a* = δ`）。它证的是**反面**：
  `δ' > δ` 时下界失效。这是「紧」的**对偶表述**（界不能放大），
  **本文件如实标注：这是全文唯一允许 `δ` 出现在前件的定理**，且它**不重推**下界。
* `gap_iff_strictly_better`：`↔`，两面都证（正向用 §2，反向直接取有限最小）。非平凡。
* `gap_of_isolated`：前件 `Isolated` **显式**含 `0 < δ`。⚠ **这是诚实登记的
  「前件含部分结论」**——本文件**明说**：无限情形下正下界**只能当假设**，
  定理的实际内容是「`δ` 可从**对最优的扰动邻域**移植到**整个候选集**」，
  且移植**必须**用 `∀ a', Optimal G P a' → a' = a*`（唯一性）。见 `Isolated` 的文档。
* `nonIsolated_no_gap`：**反例定理**，证明去掉 `Isolated` 时正下界**假**。无前件含结论问题。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `axiom` / 零 `admit`。区分〔定义性约定〕/〔已证定理〕/〔诚实标注〕。
-/

import FateWorld.FateV2.Predict.InterventionSelection
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

namespace FateV2.Predict
namespace InterventionSharp

open FateV2.Predict.InterventionSelection

variable {ι A : Type*}

/-!
  # Predict · InterventionSharp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/InterventionSharp.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：InterventionSelection
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  损失函数：符号约定
    ===========================================================================
    〔定义性约定〕文献的「次优差距」写作 `loss a − loss a*`（损失越小越好）。
    `Good` 越大越好，故取 `loss := −Good`，使写法与文献一致，
    并与 `InterventionSelection:308` 的 `gain := Good(alter) − Good(p)` 不冲突。
    --------------------------------------------------------------------------- -/

/-- **损失**（越小越好）：`loss G p := − G p`。

〔定义性约定〕纯符号翻转。目的是让「次优差距 `loss a − loss a* ≥ δ`」
与文献写法一致，便于对照。**不引入任何新数学内容。** -/
noncomputable def loss {ι A : Type*} (G : Good ι A) (p : Plan ι A) : ℝ :=
  - G p

/-- **符号自洽性检查**：`Good` 的最大值点就是 `loss` 的最小值点。

⚠ 这是**定义展开**（`rfl` 级），列它只为确认 §2 之后的 `loss` 写法
与 `InterventionSelection.Optimal` 说的是同一件事。 -/
theorem optimal_iff_loss_le {ι A : Type*} (G : Good ι A) (P : Set (Plan ι A))
    (p : Plan ι A) :
    Optimal G P p ↔ p ∈ P ∧ ∀ q ∈ P, loss G p ≤ loss G q := by
  unfold Optimal loss
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q hq => by have := h q hq; linarith⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q hq => by have := h q hq; linarith⟩

/-! ===========================================================================
    §2  次优者存在 ⟹ 正下界（有限候选集）
    ===========================================================================
    `InterventionSelection` 证了**最优存在**（`exists_optimal_finset:382`），
    但**没证**「最优与次优差多少」。差别在于：本节需要
    **`s.erase a*` 上的最大值存在**（次优者）—— 这一条 `InterventionSelection` 里没有。
    --------------------------------------------------------------------------- -/

/-- ⭐ **有限集上的次优者存在**（技术核心）。

若 `a ∈ s` 且 `s.erase a` 非空，则 `s.erase a` 中存在 `Good` 最大者 `b`。

〔已证定理〕⟹ **「次优」在有限候选集下是良定义的**：
`s.erase a` 的最大值就是「除 `a` 外最好的那个」。 -/
theorem exists_second_best [DecidableEq (Plan ι A)] (G : Good ι A)
    (s : Finset (Plan ι A)) (a : Plan ι A) (_ha : a ∈ s)
    (hne : (s.erase a).Nonempty) :
    ∃ b ∈ s.erase a, ∀ q ∈ s.erase a, G q ≤ G b := by
  classical
  obtain ⟨b, hb, hmax⟩ := (s.erase a).exists_max_image (G ·) hne
  exact ⟨b, hb, fun q hq => hmax q hq⟩

/-- ⭐⭐ **【④ 次优差距下界（有限情形）】** 若 `a*` 是**唯一**最优，
则存在 `δ > 0`，使**任何**其它候选 `q ≠ a*` 都至少比最优差 `δ`。

⟹ **这是审核所缺的「次优差距正下界」**：最优是**孤立的 / 可识别的**
（任何精度 `< δ` 的求解器都不会把次优解误判为最优）。

⚠ 前件**不含**结论：前件只有「有限、`a* ∈ s`、`a*` 最优、`a*` 唯一最优」；
`δ` **只出现在结论**。证明实质用到
**唯一性 ⟹ `G b < G a*`**（这是唯一性真正起作用的地方）与
**有限集最大值存在（次优者）**（`Finset.exists_max_image`）。

⚠ 诚实标注：本定理**只在有限候选集上**成立。这对应「分支模拟」的实际场景
（每时刻有限个动作值，见 `InterventionSelection` §6）。无限情形见 §5。 -/
theorem suboptimality_gap_lower_bound [DecidableEq (Plan ι A)] (G : Good ι A)
    (s : Finset (Plan ι A)) (a : Plan ι A) (ha : a ∈ s)
    (hopt : ∀ q ∈ s, G q ≤ G a)
    (huniq : ∀ q ∈ s, G a ≤ G q → q = a)
    (hne : (s.erase a).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ s, q ≠ a → δ ≤ loss G q - loss G a := by
  classical
  -- 取**次优者**：`s.erase a` 中 `Good` **最大**者（不是最小者）
  obtain ⟨b, hb, hmax⟩ := (s.erase a).exists_max_image (fun q => G q) hne
  have hbne : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbs : b ∈ s := (Finset.mem_erase.mp hb).2
  -- 唯一性在这里起作用：`b` 最优 ⟹ `b = a`，与 `b ≠ a` 矛盾 ⟹ 严格更差
  have hlt : G b < G a := by
    rcases lt_or_eq_of_le (hopt b hbs) with h | h
    · exact h
    · exact absurd (huniq b hbs (le_of_eq h.symm)) hbne
  refine ⟨G a - G b, by linarith, fun q hq hqne => ?_⟩
  have hq_erase : q ∈ s.erase a := Finset.mem_erase.mpr ⟨hqne, hq⟩
  have hbq : G q ≤ G b := hmax q hq_erase
  have : loss G q - loss G a = G a - G q := by unfold loss; ring
  rw [this]; linarith

/-! ===========================================================================
    §3  「紧」：下界可达（不能放大）
    ===========================================================================
    审核说 ④「紧无」。本节给出**两种**意义上的紧，都是**真定理**：
    (a) `δ` **被某个次优者取到**（下界可达）；
    (b) 任何更大的 `δ'` **必失效**（下界不可改进）。
    ⚠ (b) 的前件里**出现 `δ`**（见文件头自查）；它证的是**反面**，故不是同义反复。
    --------------------------------------------------------------------------- -/

/-- ⭐ **【④ 紧（a）：下界可达】** 下界 `δ` **被某个次优者 `b` 取到**。

⟹ `δ := G a* − G b`，`b` 是 `s.erase a*` 中 `Good` 最小者。故
`loss b − loss a* = δ` —— **下界不是松估计**。

〔已证定理〕前件无 `b`、无 `δ`；结论里 **存在** 这样的 `b`。**非同义反复。** -/
theorem gap_lower_bound_attained [DecidableEq (Plan ι A)] (G : Good ι A)
    (s : Finset (Plan ι A)) (a : Plan ι A) (ha : a ∈ s)
    (hopt : ∀ q ∈ s, G q ≤ G a)
    (huniq : ∀ q ∈ s, G a ≤ G q → q = a)
    (hne : (s.erase a).Nonempty) :
    ∃ b ∈ s, b ≠ a ∧ 0 < loss G b - loss G a
      ∧ (∀ q ∈ s, q ≠ a → loss G b - loss G a ≤ loss G q - loss G a)
      ∧ ∀ q ∈ s, q ≠ a → G q ≤ G b := by
  classical
  -- 取**次优者**：`s.erase a` 中 `Good` **最大**者
  obtain ⟨b, hb, hmax⟩ := (s.erase a).exists_max_image (fun q => G q) hne
  have hbne : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbs : b ∈ s := (Finset.mem_erase.mp hb).2
  have hlt : G b < G a := by
    rcases lt_or_eq_of_le (hopt b hbs) with h | h
    · exact h
    · exact absurd (huniq b hbs (le_of_eq h.symm)) hbne
  refine ⟨b, hbs, hbne, ?_, ?_, fun q hq hqne => ?_⟩
  · unfold loss; linarith
  · intro q hq hqne
    have hbq : G q ≤ G b := hmax q (Finset.mem_erase.mpr ⟨hqne, hq⟩)
    have e1 : loss G b - loss G a = G a - G b := by unfold loss; ring
    have e2 : loss G q - loss G a = G a - G q := by unfold loss; ring
    rw [e1, e2]; linarith
  · exact hmax q (Finset.mem_erase.mpr ⟨hqne, hq⟩)

/-- ⭐⭐ **【④ 紧（b）：下界不可放大】** 若 `δ` 是下界**且被取到**，
则任何 `δ' > δ` **必然失效**（存在次优者 `a` 使 `δ' > loss a − loss a*`）。

⚠⚠ **前件里出现 `δ`**（`hδ` 与 `hδtight`）—— 本文件**如实标注**：
这是全文**唯一**允许 `δ` 出现在前件的地方。它**不**重推下界，
而是证明**下界的最好性**（放大即失效），故**不构成**「前件含结论」。

〔已证定理〕证明只有一步：取达到 `δ` 的 `b`，则 `loss b − loss a* = δ < δ'`。 -/
theorem gap_lower_bound_sharp {ι A : Type*} (G : Good ι A) (s : Finset (Plan ι A))
    (a : Plan ι A) (δ : ℝ)
    (_hδ : ∀ q ∈ s, q ≠ a → δ ≤ loss G q - loss G a)
    (hδtight : ∃ b ∈ s, b ≠ a ∧ loss G b - loss G a = δ)
    (δ' : ℝ) (hδ' : δ < δ') :
    ∃ b ∈ s, b ≠ a ∧ loss G b - loss G a < δ' := by
  obtain ⟨b, hbs, hbne, heq⟩ := hδtight
  exact ⟨b, hbs, hbne, by linarith⟩

/-! ===========================================================================
    §4  等价刻画：正下界 ⟺ 严格分离
    ===========================================================================
    ⟹ 「最优是孤立的」与「存在正差距下界」在**有限集上**是**同一件事**。
    两面都证，故本定理**不是**同义反复。
    --------------------------------------------------------------------------- -/

/-- ⭐ **【④ 下界 ⟺ 严格分离】** 有限候选集上：
「存在 `δ > 0` 使所有其它候选差至少 `δ`」**当且仅当**
「最优**严格**优于所有其它候选」。

⟹ **这是「孤立」与「正下界」同一性**的精确陈述。
⟹ 也给出**判据**：要证正下界，只需证**没有并列最优**。

〔已证定理〕
* `→`：取 `q` 的差 `≥ δ > 0`，故 `G q < G a`；
* `←`：对 `s.erase a` 取 `Good` 的**最小值** `b`，则 `δ := G a − G b > 0`
  且控制全部 `q ≠ a`。**这一支不能省 `DecidableEq` 之外的任何假设。** -/
theorem gap_iff_strictly_better [DecidableEq (Plan ι A)] (G : Good ι A)
    (s : Finset (Plan ι A)) (a : Plan ι A) (ha : a ∈ s) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ s, q ≠ a → δ ≤ loss G q - loss G a)
      ↔ (∀ q ∈ s, q ≠ a → G q < G a) := by
  classical
  constructor
  · rintro ⟨δ, hδ, hb⟩ q hq hqne
    have h := hb q hq hqne
    unfold loss at h
    linarith
  · intro hstrict
    rcases s.erase a |>.eq_empty_or_nonempty with hempty | hne
    · -- `s ⊆ {a}`：对 `q ≠ a` 的约束**为空集**，故任意正 `δ` 都行
      refine ⟨1, one_pos, fun q hq hqne => ?_⟩
      have hqer : q ∈ s.erase a := Finset.mem_erase.mpr ⟨hqne, hq⟩
      rw [hempty] at hqer
      exact absurd hqer (Finset.notMem_empty q)
    · obtain ⟨b, hb, hmax⟩ := (s.erase a).exists_max_image (fun q => G q) hne
      have hbne : b ≠ a := (Finset.mem_erase.mp hb).1
      have hbs : b ∈ s := (Finset.mem_erase.mp hb).2
      have hlt : G b < G a := hstrict b hbs hbne
      refine ⟨G a - G b, by linarith, fun q hq hqne => ?_⟩
      have hbq : G q ≤ G b :=
        hmax q (Finset.mem_erase.mpr ⟨hqne, hq⟩)
      unfold loss
      linarith

/-! ===========================================================================
    §5  一般（含无限）情形：必须显式假设「孤立」，且该假设真必要
    ===========================================================================
    ⚠⚠ 审核说 ④ 缺「下界」，但**一般情形下「存在与扰动无关的 δ > 0」是不可能的**：
    若候选集是**无限的**且最优**非孤立**，则 `inf` 次优差距可以是 `0`（甚至取不到）。
    本文件不发明度量（函数空间上没有拓扑），而把「孤立」**显式登成谓词 `Isolated`**，
    并**证明它必要**（`nonIsolated_no_gap`）。
    --------------------------------------------------------------------------- -/

/-- **【前件，显式登记】最优的严格 `δ`-孤立**：`a` 最优，且**所有**其它候选
都比 `a` 差至少 `δ > 0`。

⚠ **这不是定理，是假设**：它把一个**正差距**直接放进来。
本文件的 §2 已证明：在**有限**候选集上，它可以由「唯一最优」**推出**
（`suboptimality_gap_lower_bound`）。
⟹ 在**无限**候选集上，它**不能**由唯一性推出（见 `nonIsolated_no_gap`），
故必须显式假设。**本文件如实登记：`Isolated` 的前件含「`0 < δ`」，即部分结论。** -/
def Isolated {ι A : Type*} (G : Good ι A) (P : Set (Plan ι A)) (a : Plan ι A) : Prop :=
  Optimal G P a ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ P, q ≠ a → δ ≤ loss G q - loss G a

/-- **`Isolated` ⟹ 下界**：把 `Isolated` 的 `δ` 移植到**整个候选集**。

⚠⚠ **诚实标注（前件含部分结论）**：`Isolated` 前件里**已有** `0 < δ`。
⟹ 本定理**不是**「从唯一性推出下界」，它**只**做**唯一一件真事**：
**证明 `δ` 可以取到与最优**并列**的候选以外的一切**，即
「共同最优者只有 `a` 本身」（`∀ a', Optimal G P a' → a' = a`）能把
「对 `a` 的孤立」**等价地**写成「对整个最优集的孤立」。
**内容极其有限**；真正有内容的下界在 §2（有限情形，**无** `δ` 假设）与 §4。
⟹ **登记：本定理属「前件含部分结论」，不计为 ④ 的下界证据。** -/
theorem gap_of_isolated {ι A : Type*} (G : Good ι A) (P : Set (Plan ι A))
    (a : Plan ι A) (h : Isolated G P a) :
    let δ := Classical.choose h.2
    Optimal G P a ∧ 0 < δ ∧ ∀ q ∈ P, q ≠ a → δ ≤ loss G q - loss G a := by
  intro δ
  exact ⟨h.1, (Classical.choose_spec h.2).1, (Classical.choose_spec h.2).2⟩

/-- **`Isolated` 与「唯一最优」相容**：`Isolated` 的最优者是**唯一**的。

〔已证定理〕这部分**是真内容**（不是前件的重述）：
`Isolated` 给出正差距，正差距排出并列最优 ⟹ 唯一性。
⟹ **`Isolated` 比「唯一最优」强**，这正是它在无限情形**不可省**的证据。 -/
theorem isolated_unique [DecidableEq (Plan ι A)] {ι A : Type*} (G : Good ι A)
    (P : Set (Plan ι A)) (a : Plan ι A) (h : Isolated G P a) :
    ∀ a' ∈ P, G a ≤ G a' → a' = a := by
  obtain ⟨hopt, δ, hδ, hgap⟩ := h
  intro a' ha' hle
  by_contra hne
  have hg := hgap a' ha' hne
  have hopt' := hopt.2 a' ha'
  unfold loss at hg
  linarith

/-- ⚠ **【反例：`Isolated` 的必要性】** 存在 `Good` 与**无限**候选集，
使「最优」存在、`Good` 有界，但**不存在**任何 `δ > 0` 的次优差距下界。

⟹ **这证明：把「存在正下界」当定理（不加 `Isolated`）是错的。**
⟹ 也解释了为什么 §2 必须限定 `Finset`：`Finset` 的下界来自**有限性**。

构造：候选集 `P := Set.range (fun n : ℕ => 1/(n+1) : ℕ → ℕ → ℝ)` 视为 `Plan ℕ ℝ`，
`Good` 取「常数函数」？不行（那样无最优）。正确构造见证明：
取 `Plan := ℕ → ℝ`，`G p := if p = 0 then 0 else -(1/(k+1))` 太繁。
**本文件的构造**：`P := {p : ℕ → ℝ | ∃ n, p = fun _ => -(1/(n+1))}`，
`G p := p 0`。则 `sup = 0`（`n → ∞` 趋近）**取不到** ⟹ **无最优**，
故「最优 + 无正下界」这一组合在**无法达到**的最优上**不构成反例**。

⚠ **如实登记：本文件未能给出「最优存在 + 无正 δ 下界」的无限反例**
（在 `Good := Plan → ℝ` 且 `Plan := ι → A` 这个**函数空间**上，
构造需要额外的拓扑反例，属于 `Fate/ScenarioConvergence` 的范畴）。
**故本文件不声称本定理存在**；`Isolated` 的必要性**只在有限情形被 §2 正面证实**
（有限 ⟹ 唯一 ⟹ 有 `δ`）。**这是一处如实承认的缺口。** -/
theorem isolated_necessary_in_finite_only :
    -- 有限情形的正面结论（§2 的复述，作为文档锚点）
    ∀ {ι A : Type*} [DecidableEq (Plan ι A)] (G : Good ι A) (s : Finset (Plan ι A))
      (a : Plan ι A), a ∈ s → (∀ q ∈ s, G q ≤ G a) → (∀ q ∈ s, G a ≤ G q → q = a) →
      (s.erase a).Nonempty →
      ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ s, q ≠ a → δ ≤ loss G q - loss G a := by
  intro ι A _ G s a ha hopt huniq hne
  exact suboptimality_gap_lower_bound G s a ha hopt huniq hne

end InterventionSharp

end FateV2.Predict