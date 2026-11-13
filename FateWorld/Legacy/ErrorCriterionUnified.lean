/-
# `ErrorCriterionUnified` —— 裁决 K 误差判据的**唯一权威口径**与其桥接

本轮任务（B3 · 裁决 K 判据统一）。背景：C3 审计（第 376 轮）实测发现主干断点 B3 ——
「裁决 K 的误差判据被定义 3 次互不相通」，而**真正被下游使用的是 `ScoreK.bandLoss`**。

本文件**只新建，不改任何已有模块**。

---

## §A 对照表：四处判据的**精确陈述**（逐字抄自源文件）

| # | 位置 | 标识符 | 精确陈述 | 实测扇入 |
|---|---|---|---|---|
| ① | `Fate/AttrAcceptable.lean:33` | `Fate.AttrAcceptable.AttrAcceptable` | `def AttrAcceptable (ε σ : ℝ) : Prop := σ / 2 ≤ ε ∧ ε ≤ 2 * σ` | **0**（全库仅注释提及） |
| ② | `Fate/ErrorCriterion.lean:51` | `Fate.ErrorCriterion.ErrorAcceptable` | `def ErrorAcceptable (ε σ : ℝ) : Prop := σ / 2 ≤ ε ∧ ε ≤ 2 * σ` | **0** |
| ③ | `Fate/ErrorCriterion.lean:158` | `Fate.ErrorCriterion.AttrAcceptableMirror` | `def AttrAcceptableMirror (ε σ : ℝ) : Prop := σ / 2 ≤ ε ∧ ε ≤ 2 * σ` | **0** |
| ④ | `Fate/ScoreK.lean:52` | `Fate.ScoreK.bandLoss` | `noncomputable def bandLoss (σ ε : ℝ) : ℝ := max 0 (max (σ / 2 - ε) (ε - 2 * σ))` | **5**（`EndToEndError` / `ErrBandLink` / `ErrDefinitions` / `ErrorDimUnified` / `ErrorGraph`） |
| ④' | `Fate/ErrorDimUnified.lean:114` | `Fate.ErrorDimUnified.bandCriterion` | `def bandCriterion : Criterion := fun σ ε => ScoreK.bandLoss σ ε = 0` | 2 |

**扇入的实测方式**（可复现，两种模式互证）：

```
grep -rn "ErrorCriterion\." Fate/*.lean | grep -v "^Fate/ErrorCriterion.lean"   # → 空
grep -rn "AttrAcceptableMirror" Fate/*.lean | grep -v "^Fate/ErrorCriterion.lean" # → 空
grep -rln "bandLoss" Fate/*.lean                                                # → 5 个文件
```

**⚠ 注意参数顺序**：①②③ 都是 `(ε σ)`（误差在前、尺度在后），
④ 是 `(σ ε)`（**尺度在前、误差在后**）。这是四处之间**唯一的实质差异**，
也是最容易接错的地方。本文件的每个桥接定理都显式标注了这一点。

---

## §B 裁决（任务 (b)）：**不是「强度不同」，而是「定义恒等」**

任务书要求「若真等价则证明等价，若不等价则给反例」。**实测结论是更强的第三种情况**：

> ①②③ **是同一个谓词**，不只是「等价」——三者的**定义体逐字相同**
> （`σ / 2 ≤ ε ∧ ε ≤ 2 * σ`），故它们之间的「等价」是 `Iff.rfl`，
> 连**外延相等**（`= ` 作为 `Prop` 的相等）都能不用 funext 而由 `rfl` 得到。

因此「3 处互不相通」的**真实病理不是语义分歧，而是重复定义 + 零扇入**：
三处各自 `unfold`、各自 prove `Iff.rfl` 式的区间刻画，却**没有任何一处**被下游引用
（下游全部直接写裸不等式或经 `bandLoss`）。
⟹ 统一口径的**代价极低**（桥接只需 `Iff.rfl`），本文件即为该桥接。

④ `bandLoss` 与 ①②③ **不是定义恒等**（一个是 `ℝ` 值函数，一个是 `Prop`），
需要用 `max` 的极值性质证。**这是本文件最实质的技术内容**（§2）。

---

## §C 权威口径（任务 (c)）

选 ②`Fate.ErrorCriterion.ErrorAcceptable`（= `Fate/ErrorCriterion.lean:51`）为**唯一权威口径**，
理由不是「它更对」（三者定义相同），而是：

1. 它的**命名**最不带偏见（`Attr*` 绑定「属性」，而裁决 K 明言「适用一切、强制」）；
2. 它**已有 19 条定理**（含 `errorAcceptable_iff_mem_Icc` / `lower` / `upper` / `mono_eps` /
   `scale_invariant` / `iff_ratio`）；
3. 它所在的文件**已经**把「与 ① 一致」写进了自己的 §5 —— 本文件把该一致性
   **升级为对全库可引用的唯一入口**。

本文件用 `abbrev Canonical` 作该权威口径的**别名**（`abbrev` 而非 `def`，
故 `Canonical` 与 `ErrorAcceptable` **定义上**是同一项，`Iff.rfl` 且 `rfl` 皆可）。
①② 向它桥接见 §1.3 / §1.4；④ 向它桥接见 §2。

---

## §D ⚠ 冲突登记（任务 (d)）：**一处真冲突，不可强行统一**

### D.1 【真冲突】判据是**逐点**谓词，`IsFitBoundary` 是**剖面级**极值谓词 —— 二者**互不蕴含**

`Fate/FitBoundary.lean:268`：
`def IsFitBoundary (W : ErrProfileWeak) (σ γ : ℝ) : Prop := W.err γ = σ ∧ ∀ γ', σ ≤ W.err γ'`
（存在性 `:317` / `:374`，唯一性 `:486`，不存在 `:680` / `:698`。）

它是**关于整条剖面的极值断言**（σ 被**达到**且是**全局下界**），
而 ②/④ 是**关于单个实数对** `(ε, σ)` 的谓词。二者在剖面级**互不蕴含**，
两个方向都有**机器验证的反例**（§3）：

* **边界存在 ⇏ 判据在全体 γ 成立**：反例 `profSqPlusOne`（`err γ = γ² + 1`，σ = 1）。
  γ = 0 是边界点，但 γ = 2 处 `err = 5`，`5 ≤ 2·1` 失败 ⟹ 判据在 γ = 2 不成立。
  定理 `boundary_does_not_imply_criterion_uniform`。
* **判据在全体 γ 成立 ⇏ 边界存在**：反例 `profThreeHalves`（`err ≡ 3/2`，σ = 1）。
  `3/2 ∈ [1/2, 2]` 对**每个** γ 成立，但没有任何 γ 使 `err γ = 1` ⟹ 无边界。
  定理 `criterion_uniform_does_not_imply_boundary`。

**⟹ 登记结论**：「裁决 K 的判据」与「恰好拟合/过拟合边界」**不是同一件事**，
**不能**相互替代。「误差必须刚好落在边界」的**逐点读法**是 ②；
**极值读法**是 `IsFitBoundary`。**本文件不强行统一二者**，只登记其相互关系：
* `isFitBoundary_implies_canonical`（§3.1）：**边界点处判据必成立**（唯一的正向联系，
  且它是**真蕴含**，不是同义反复 —— 需要 `err ≥ 0` 才能从 `err γ = σ` 得到 `σ ≥ 0`）。

### D.2 【退化区，非冲突】σ < 0：判据与边界**同时为空**

* `canonical_false_of_neg`（§4.1）：σ < 0 时**无任何** ε 满足判据
  （区间 `[σ/2, 2σ]` 下界 > 上界，为空）。
* `not_hasFitBoundary_of_neg`（§4.2）：σ < 0 时**不存在**边界
  （`ErrProfileWeak.err ≥ 0` 与 `err γ = σ < 0` 矛盾）。

⟹ 二者在 σ < 0 上**一致地空**，故**不是冲突**；但它是**共同的盲区**：
此区判据**毫无鉴别力**（恒定 `False`），任何「依判据放行」的实现
在 σ < 0 时会把**一切**拒绝掉。**使用处必须显式要求 `0 ≤ σ`。**

### D.3 【退化区】σ = 0：判据退化为单点

`canonical_zero_iff`（§4.3）：σ = 0 时判据 ⟺ `ε = 0`。
与 `IsFitBoundary` 相容（`err γ = 0` 且 `0 ≤ err γ'` 恒真），
但**与 `Fate/FitBoundary.lean:735` 的 `profConstOne_no_boundary` 对照可知**：
σ = 0 是边界判定最脆弱的点（`err ≡ 1` 在 σ = 0 下无边界、在 σ = 1 下有边界）。

---

## §E ⚠ 附带修正登记：`ScoreK` 注释中「反向需 `0 < σ`」是**冗余的**

`Fate/ScoreK.lean:110-116` 的注释原文：

> **⚠ 反向需要 `0 < σ`** —— 否则当 `σ = 0` 时带退化为 `[0,0]`，
> 而 `bandLoss 0 0 = 0` 但 `ε ≠ 0` 也可能给出 `0`（因 `max 0` 的截断）。

**实测该断言为假。** 因 `σ = 0` 时 `bandLoss 0 ε = max 0 (max (-ε) ε) = |ε|`
（定理 `bandLoss_zero_eq_abs`，§2.2），故 `bandLoss 0 ε = 0 ↔ ε = 0`。
一般地 `max 0 X = 0 ↔ X ≤ 0`（`max_le_iff` + `max_eq_left`），
于是 `bandLoss σ ε = 0 ↔ σ/2 ≤ ε ∧ ε ≤ 2σ` **对一切 σ, ε 成立，无需 `0 < σ`**。

⟹ 本文件的 `bridge_bandLoss`（§2.1）是 `ScoreK.bandLoss_eq_zero_iff`
**去掉 `0 < σ` 前件的加强版**；`bandLoss_eq_zero_iff_pos`（§2.3）表明
`ScoreK` 原定理是本定理的直接特例。**本文件不改 `ScoreK`**（纪律 2），只登记。

---

## §F 本文件的实质内容与非实质内容（诚实分层）

| 层 | 定理 | 性质 |
|---|---|---|
| **非实质**（定义恒等的桥） | §1 全部 | `Iff.rfl` / `rfl`。**不声称是数学贡献**，只作口径统一的可引用入口 |
| **实质**（需真推理） | §2 `bridge_bandLoss` 及其推论 | 用 `max` 的极值刻画**去掉 `0<σ` 前件**；且 `bandLoss = 0` 与 `Prop` 判据的对应**不是**定义恒等 |
| **实质**（新增刻画） | §2.4 `canonical_iff_log` | 判据 ⟺ `\|log(ε/σ)\| ≤ log 2`（σ>0, ε>0）：**「同阶」=「与 σ 的乘性距离不超过 2 倍」**，用 `Real.exp_log` / `Real.log_le_iff_le_exp` 证 |
| **实质**（反例） | §3.2 / §3.3 | 两个显式剖面 + 数值，证 D.1 的两个否定方向 |
| **实质**（退化区） | §4 | σ<0 双重为空、σ=0 单点 |
| **实质**（具名结论） | §5 `adjudicationK_criterion_unified` | 把 B3 的裁决**汇编成一条可引用的合取定理**，供下游/审计单点引用 |

**⚠ 自查（纪律 7：前件是否把结论包进去）**：
* §2.1 `bridge_bandLoss` 前件 `bandLoss σ ε = 0`，结论是**两个不等式** —— 需经
  `max_le_iff` 拆三层 `max`，**不同义反复**。
* §2.4 `canonical_iff_log` 前件 `0 < σ`、`0 < ε`（仅为可除性/对数的定义域），
  结论 `|log(ε/σ)| ≤ log 2` —— 与「区间判据」**形式完全不同**，需 `Real.exp_log` 桥接，
  **不同义反复**。
* §3.1 `isFitBoundary_implies_canonical`：前件是**剖面级极值断言**，结论是**逐点不等式**，
  **不同义反复**（且必须用 `err_nonneg` 才能过）。
* §1 的桥接**是同义反复**（`Iff.rfl`），**本文件已在 §F 表格中如实标注为「非实质」**，
  不当作数学贡献声称。

**零 `sorry` / 零 `admit` / 零 `axiom`。** 提交前实测 `lake env lean` 两遍，EXIT=0。
-/

import FateWorld.Legacy.AttrAcceptable
import FateWorld.Legacy.ErrorCriterion
import FateWorld.Legacy.ScoreK
import FateWorld.Legacy.FitBoundary
import FateWorld.Legacy.ErrorDimUnified
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Fate

namespace ErrorCriterionUnified

noncomputable section

/-! ===========================================================================
  §1  ⭐ 唯一权威口径与 ①②③ 的桥接
  =========================================================================== -/

/-! ### §1.1 权威口径 -/

/-- ⭐⭐ **唯一权威口径**：别名指向 `Fate/ErrorCriterion.lean:51` 的 `ErrorAcceptable`。

`abbrev`（而非 `def`）⟹ `Canonical` 与 `ErrorAcceptable` 是**同一项**，
故本文件的一切 `Canonical` 结论对 `ErrorAcceptable` 直接可用，**无需转换**。

参数顺序：`(ε σ)` —— **误差在前、尺度在后**（与 ① ② ③ 一致，与 ④ 相反）。 -/
abbrev Canonical (ε σ : ℝ) : Prop := ErrorCriterion.ErrorAcceptable ε σ

/-- 权威口径的**展开**（与源文件 `Fate/ErrorCriterion.lean:51` 的定义体逐字一致）。 -/
theorem canonical_iff (ε σ : ℝ) : Canonical ε σ ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ :=
  Iff.rfl

/-- 权威口径的区间刻画（与 `ErrorCriterion.errorAcceptable_iff_mem_Icc` 同陈述，
此处从权威别名再导出一次，以便只用 `Canonical` 的下游不必打开 `ErrorCriterion`）。 -/
theorem canonical_iff_mem_Icc (ε σ : ℝ) :
    Canonical ε σ ↔ ε ∈ Set.Icc (σ / 2) (2 * σ) :=
  Iff.rfl

/-! ### §1.2 ① 的桥接（`Fate/AttrAcceptable.lean:33`） -/

/-- ⭐ **桥接 ① → 权威口径**：`AttrAcceptable ε σ ↔ Canonical ε σ`。

**⚠ 非实质**：二者定义体逐字相同，故为 `Iff.rfl`。（审计 B3 的第 1 处。） -/
theorem bridge_attrAcceptable (ε σ : ℝ) :
    AttrAcceptable.AttrAcceptable ε σ ↔ Canonical ε σ :=
  Iff.rfl

/-- 桥接 ① 的**外延相等**形式（比 `↔` 更强）：两个谓词是**同一函数**。 -/
theorem def_eq_attrAcceptable :
    AttrAcceptable.AttrAcceptable = (Canonical : ℝ → ℝ → Prop) :=
  rfl

/-! ### §1.3 ③ 的桥接（`Fate/ErrorCriterion.lean:158`） -/

/-- ⭐ **桥接 ③ → 权威口径**：`AttrAcceptableMirror ε σ ↔ Canonical ε σ`。

**⚠ 非实质**：`Iff.rfl`。（审计 B3 的第 3 处。） -/
theorem bridge_attrAcceptableMirror (ε σ : ℝ) :
    ErrorCriterion.AttrAcceptableMirror ε σ ↔ Canonical ε σ :=
  Iff.rfl

/-- 桥接 ③ 的**外延相等**形式。 -/
theorem def_eq_attrAcceptableMirror :
    ErrorCriterion.AttrAcceptableMirror = (Canonical : ℝ → ℝ → Prop) :=
  rfl

/-! ### §1.4 ⭐ 为什么「三处互不相通」在语义上是**假问题**（登记为定理）

三处定义体逐字相同 ⟹ 它们之间**不存在强/弱关系可言**，
只有「谁被引用」的**工程问题**。下面把「不存在强弱关系」写成两条可检验的定理：
任一处成立 ⟺ 权威口径成立（不是单向蕴含）。 -/

/-- ⭐ **三处判据两两之间也无强弱之分**（① ⟺ ③，均经权威口径）。

若有人主张「`AttrAcceptable` 比 `AttrAcceptableMirror` 强/弱」，此定理即为反驳：
二者互为充要，故**方向性不存在**。 -/
theorem attrAcceptable_iff_attrAcceptableMirror (ε σ : ℝ) :
    AttrAcceptable.AttrAcceptable ε σ ↔ ErrorCriterion.AttrAcceptableMirror ε σ :=
  Iff.rfl

/-- ⭐ **权威性判据的「无偏向性」**：三处判据对 `(ε, σ)` 的真值函数完全相同。 -/
theorem three_definitions_agree :
    (∀ ε σ : ℝ, AttrAcceptable.AttrAcceptable ε σ ↔ Canonical ε σ) ∧
    (∀ ε σ : ℝ, ErrorCriterion.AttrAcceptableMirror ε σ ↔ Canonical ε σ) :=
  ⟨bridge_attrAcceptable, bridge_attrAcceptableMirror⟩

/-! ===========================================================================
  §2  ⭐⭐ ④ `ScoreK.bandLoss` 与权威口径的桥接（本文件最实质的部分）
  =========================================================================== -/

/-! ### §2.1 ⭐⭐ 无条件桥接（去掉 `ScoreK` 原定理的 `0 < σ` 前件） -/

/-- ⭐⭐ **`bandLoss = 0` ⟺ 权威口径成立**，**对一切** σ, ε（无需 `0 < σ`）。

**⚠ 参数顺序**：`bandLoss` 是 `(σ, ε)`，`Canonical` 是 `(ε, σ)` —— 顺序相反。

**证明**（非平凡）：`max 0 X = 0 ↔ X ≤ 0`；再对 `max (σ/2 - ε) (ε - 2σ)` 用两次
`max_le_iff` 拆成两条不等式。

**⚠ 这加强** `Fate/ScoreK.lean` 的 `bandLoss_eq_zero_iff`（原定理要 `0 < σ`，
且其注释声称反向"需要 `0 < σ`"是错误的，见 §E 与 §2.2）。 -/
theorem bridge_bandLoss (σ ε : ℝ) :
    ScoreK.bandLoss σ ε = 0 ↔ Canonical ε σ := by
  unfold ScoreK.bandLoss
  constructor
  · intro h
    have h0 : max 0 (max (σ / 2 - ε) (ε - 2 * σ)) ≤ 0 := le_of_eq h
    have hm : max (σ / 2 - ε) (ε - 2 * σ) ≤ 0 := (max_le_iff.mp h0).2
    exact ⟨by linarith [(max_le_iff.mp hm).1], by linarith [(max_le_iff.mp hm).2]⟩
  · rintro ⟨h1, h2⟩
    exact max_eq_left (max_le (by linarith) (by linarith))

/-- ⭐ **非负性**：`bandLoss` 恒非负（`max 0 _` 的左分量）。 -/
theorem bandLoss_nonneg (σ ε : ℝ) : 0 ≤ ScoreK.bandLoss σ ε :=
  le_max_left 0 _

/-- ⭐ **二分法定理**：`bandLoss` 或为零（合格），或严格正（不合格）。 -/
theorem bandLoss_eq_zero_or_pos (σ ε : ℝ) :
    ScoreK.bandLoss σ ε = 0 ∨ 0 < ScoreK.bandLoss σ ε :=
  (eq_or_lt_of_le (bandLoss_nonneg σ ε)).elim (fun h => Or.inl h.symm) Or.inr

/-! ### §2.2 ⚠ 修正 `ScoreK` 注释的错误断言（σ = 0 时的真实行为） -/

/-- ⭐⭐ **σ = 0 时 `bandLoss` 就是绝对值**：`bandLoss 0 ε = |ε|`。

这**直接反驳** `Fate/ScoreK.lean:110-116` 注释中
「`σ = 0` 时 …… `bandLoss 0 0 = 0` 但 `ε ≠ 0` 也可能给出 `0`」的说法：
`|ε| = 0 ↔ ε = 0`，故截断**不会**误判。 -/
theorem bandLoss_zero_eq_abs (ε : ℝ) : ScoreK.bandLoss 0 ε = |ε| := by
  unfold ScoreK.bandLoss
  rw [show (0 : ℝ) / 2 - ε = -ε by ring, show ε - 2 * 0 = ε by ring]
  rcases le_total 0 ε with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith : -ε ≤ ε), max_eq_right h]
  · rw [abs_of_nonpos h, max_eq_left (by linarith : ε ≤ -ε),
      max_eq_right (by linarith : (0 : ℝ) ≤ -ε)]

/-- ⭐ **σ = 0 时无「截断误判」**：`bandLoss 0 ε = 0 ↔ ε = 0`（对照 §4.3 `canonical_zero_iff`）。 -/
theorem bandLoss_zero_eq_zero_iff (ε : ℝ) :
    ScoreK.bandLoss 0 ε = 0 ↔ ε = 0 := by
  rw [bandLoss_zero_eq_abs, abs_eq_zero]

/-! ### §2.3 ⭐ `ScoreK` 原定理是本文件定理的特例（`0 < σ` 前件冗余） -/

/-- ⭐ **`ScoreK.bandLoss_eq_zero_iff` 可由本文件的 `bridge_bandLoss` 导出**：
原定理的 `0 < σ` 前件**未被使用**。 -/
theorem bandLoss_eq_zero_iff_pos {σ : ℝ} (_hσ : 0 < σ) {ε : ℝ} :
    ScoreK.bandLoss σ ε = 0 ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ :=
  (bridge_bandLoss σ ε).trans (canonical_iff ε σ)

/-- ⭐ **`ErrorDimUnified.bandCriterion`（⑤）与权威口径一致**（同样无需 `0 < σ`）。 -/
theorem bridge_bandCriterion (σ ε : ℝ) :
    ErrorDimUnified.bandCriterion σ ε ↔ Canonical ε σ :=
  bridge_bandLoss σ ε

/-- ⭐ `ErrorDimUnified.bandCriterion_iff`（带 `0 < σ`）是本桥的无条件特例。 -/
theorem bandCriterion_iff_pos {σ ε : ℝ} (_hσ : 0 < σ) :
    ErrorDimUnified.bandCriterion σ ε ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ :=
  (bridge_bandCriterion σ ε).trans (canonical_iff ε σ)

/-! ### §2.4 ⭐⭐ 新增刻画：判据 = 「与 σ 的**乘性距离**不超过 2 倍」

$\sigma/2 \le \varepsilon \le 2\sigma$ 在 $(\sigma,\varepsilon) > 0$ 上等价于
$\bigl|\log(\varepsilon/\sigma)\bigr| \le \log 2$ —— 即「$\varepsilon$ 与 $\sigma$
的比值落在 $[1/2, 2]$」，也就是**「同阶」的精确含义**（裁决 K「误差 ≈ 噪声尺度」）。

这是与「双不等式」**形式完全不同**的刻画，故**不是同义反复**。 -/

/-- ⭐⭐ **对数刻画**：`0 < σ`、`0 < ε` 时，权威口径 ⟺ `|log(ε/σ)| ≤ log 2`。 -/
theorem canonical_iff_log {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    Canonical ε σ ↔ |Real.log (ε / σ)| ≤ Real.log 2 := by
  have hr : 0 < ε / σ := div_pos hε hσ
  have hexp1 : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hexp2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have key1 : -Real.log 2 ≤ Real.log (ε / σ) ↔ σ / 2 ≤ ε := by
    rw [Real.le_log_iff_exp_le hr, hexp1]
    rw [le_div_iff₀ hσ]
    constructor
    · intro h; linarith
    · intro h; linarith
  have key2 : Real.log (ε / σ) ≤ Real.log 2 ↔ ε ≤ 2 * σ := by
    rw [Real.log_le_iff_le_exp hr, hexp2]
    rw [div_le_iff₀ hσ]
  have hab : (|Real.log (ε / σ)| ≤ Real.log 2) ↔
      (-Real.log 2 ≤ Real.log (ε / σ) ∧ Real.log (ε / σ) ≤ Real.log 2) := abs_le
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  constructor
  · rintro ⟨a, b⟩; exact hab.mpr ⟨key1.mpr a, key2.mpr b⟩
  · intro h; exact ⟨key1.mp (hab.mp h).1, key2.mp (hab.mp h).2⟩

/-- ⭐ **σ 是合格带的乘性中心**：`(σ/2)·(2σ) = σ²`，且 σ 自身合格（σ ≥ 0）。

⟹ 合格带是「以 σ 为**几何中心**、乘性半宽 2 倍」的对称带。 -/
theorem band_geometric_center {σ : ℝ} (hσ : 0 ≤ σ) :
    (σ / 2) * (2 * σ) = σ ^ 2 ∧ Canonical σ σ := by
  refine ⟨by ring, ?_⟩
  exact ErrorCriterion.self_acceptable hσ

/-! ===========================================================================
  §3  ⚠⚠ 真冲突：判据（逐点）与 `IsFitBoundary`（剖面级极值）**互不蕴含**
  =========================================================================== -/

/-! ### §3.1 唯一的正向联系：**边界点处判据必成立**（真蕴含，非同义反复） -/

/-- ⭐⭐ **`IsFitBoundary` ⟹ 该点满足权威口径**。

前件是**剖面级极值断言**（`err γ = σ` 且 σ 是全局下界），
结论是**逐点不等式对**。**必须**用 `ErrProfileWeak.err_nonneg` 才能从
`err γ = σ` 得到 `σ ≥ 0`（否则 `σ/2 ≤ σ` 不成立）⟹ **非同义反复**。 -/
theorem isFitBoundary_implies_canonical {W : R238E3.ErrProfileWeak} {σ γ : ℝ}
    (h : R238E3.IsFitBoundary W σ γ) : Canonical (W.err γ) σ := by
  obtain ⟨h1, h2⟩ := h
  have hnn := R238E3.ErrProfileWeak.err_nonneg W γ
  rw [h1] at hnn
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  rw [h1]
  constructor <;> linarith

/-- ⭐ **边界的 σ 必非负**（`err ≥ 0` 的推论；与 §4.1 的退化区相接）。 -/
theorem sigma_nonneg_of_isFitBoundary {W : R238E3.ErrProfileWeak} {σ γ : ℝ}
    (h : R238E3.IsFitBoundary W σ γ) : 0 ≤ σ := by
  have hnn := R238E3.ErrProfileWeak.err_nonneg W γ
  rw [h.1] at hnn
  exact hnn

/-- ⭐ **边界存在 ⟹ 存在满足判据的点**（存在形式）。 -/
theorem exists_canonical_of_hasFitBoundary {W : R238E3.ErrProfileWeak} {σ : ℝ}
    (h : R238E3.HasFitBoundary W σ) : ∃ γ, Canonical (W.err γ) σ := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, isFitBoundary_implies_canonical hγ⟩

/-! ### §3.2 ⚠ 反例一：**边界存在，但判据并非在全体 γ 成立**

剖面 `profSqPlusOne`：`err γ = γ² + 1`，σ = 1。
* γ = 0 是边界点（`err 0 = 1`，且 `1 ≤ γ² + 1` 恒成立）；
* 但 γ = 2 处 `err = 5 > 2·1` ⟹ 判据**失败**。

⟹ `HasFitBoundary` **不蕴含**「判据在一切 γ 成立」。 -/

/-- 剖面 ①：`err γ = γ² + 1`（`bias = γ²`，`var = 1`）。 -/
def profSqPlusOne : R238E3.ErrProfileWeak where
  bias := fun γ => γ ^ 2
  var := fun _ => 1
  bias_nonneg := fun γ => sq_nonneg γ
  var_nonneg := fun _ => by norm_num

/-- `profSqPlusOne` 的误差展开。 -/
theorem profSqPlusOne_err (γ : ℝ) : profSqPlusOne.err γ = γ ^ 2 + 1 := by
  simp [R238E3.ErrProfileWeak.err, profSqPlusOne]

/-- ⭐ `γ = 0` 是 `profSqPlusOne` 在 σ = 1 下的**边界点**。 -/
theorem profSqPlusOne_isFitBoundary : R238E3.IsFitBoundary profSqPlusOne 1 0 := by
  refine ⟨?_, ?_⟩
  · rw [profSqPlusOne_err]; norm_num
  · intro γ'
    rw [profSqPlusOne_err]
    nlinarith [sq_nonneg γ']

/-- ⭐ `profSqPlusOne` 在 σ = 1 下**有边界**。 -/
theorem profSqPlusOne_hasBoundary : R238E3.HasFitBoundary profSqPlusOne 1 :=
  ⟨0, profSqPlusOne_isFitBoundary⟩

/-- ⭐⭐ **反例一定理**：`profSqPlusOne` 在 γ = 2 处**不满足**判据
（`err 2 = 5`，而合格带上界为 `2·1 = 2`）。 -/
theorem profSqPlusOne_canonical_fails : ¬ Canonical (profSqPlusOne.err 2) 1 := by
  rw [profSqPlusOne_err]
  norm_num [ErrorCriterion.ErrorAcceptable]

/-- ⭐⭐ **`HasFitBoundary` ⇏ 判据在全体 γ 成立**（反例封装）。 -/
theorem boundary_does_not_imply_criterion_uniform :
    ∃ (W : R238E3.ErrProfileWeak) (σ : ℝ),
      R238E3.HasFitBoundary W σ ∧ ∃ γ, ¬ Canonical (W.err γ) σ :=
  ⟨profSqPlusOne, 1, profSqPlusOne_hasBoundary, 2, profSqPlusOne_canonical_fails⟩

/-! ### §3.3 ⚠ 反例二：**判据在全体 γ 成立，但不存在边界**

剖面 `profThreeHalves`：`err ≡ 3/2`，σ = 1。
`3/2 ∈ [1/2, 2]` 对**每个** γ 成立（判据处处成立），
但没有任何 γ 使 `err γ = 1`（`3/2 ≠ 1`）⟹ 无边界。

⟹ 「判据处处成立」**不蕴含** `HasFitBoundary`。 -/

/-- 剖面 ②：`err ≡ 3/2`（`bias ≡ 3/2`，`var ≡ 0`）。 -/
def profThreeHalves : R238E3.ErrProfileWeak where
  bias := fun _ => 3 / 2
  var := fun _ => 0
  bias_nonneg := fun _ => by norm_num
  var_nonneg := fun _ => le_refl 0

/-- `profThreeHalves` 的误差恒为 `3/2`。 -/
theorem profThreeHalves_err (γ : ℝ) : profThreeHalves.err γ = 3 / 2 := by
  simp [R238E3.ErrProfileWeak.err, profThreeHalves]

/-- ⭐ **判据在 `profThreeHalves` 上处处成立**（σ = 1）。 -/
theorem profThreeHalves_canonical_uniform (γ : ℝ) :
    Canonical (profThreeHalves.err γ) 1 := by
  rw [profThreeHalves_err]
  norm_num [ErrorCriterion.ErrorAcceptable]

/-- ⭐⭐ **`profThreeHalves` 在 σ = 1 下无边界**（因 `err ≡ 3/2 ≠ 1`，σ 从未被达到）。 -/
theorem profThreeHalves_noBoundary : ¬ R238E3.HasFitBoundary profThreeHalves 1 := by
  rintro ⟨γ, h1, _h2⟩
  rw [profThreeHalves_err] at h1
  norm_num at h1

/-- ⭐⭐ **判据处处成立 ⇏ 边界存在**（反例封装）。 -/
theorem criterion_uniform_does_not_imply_boundary :
    ∃ (W : R238E3.ErrProfileWeak) (σ : ℝ),
      (∀ γ, Canonical (W.err γ) σ) ∧ ¬ R238E3.HasFitBoundary W σ :=
  ⟨profThreeHalves, 1, profThreeHalves_canonical_uniform, profThreeHalves_noBoundary⟩

/-! ===========================================================================
  §4  ⚠ 退化区登记（σ < 0 与 σ = 0）
  =========================================================================== -/

/-! ### §4.1 σ < 0：判据**恒假** -/

/-- ⚠ **σ < 0 时判据无鉴别力**：对一切 ε，判据不成立
（合格区间 `[σ/2, 2σ]` 下界大于上界，为空集）。 -/
theorem canonical_false_of_neg {σ : ℝ} (hσ : σ < 0) (ε : ℝ) :
    ¬ Canonical ε σ := by
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  rintro ⟨h1, h2⟩
  linarith

/-- ⚠ **σ < 0 时合格集为空**。 -/
theorem canonical_set_empty_of_neg {σ : ℝ} (hσ : σ < 0) :
    {ε : ℝ | Canonical ε σ} = ∅ := by
  ext ε
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact canonical_false_of_neg hσ ε

/-! ### §4.2 σ < 0：边界**必然不存在** -/

/-- ⚠ **σ < 0 时不存在边界**（`err ≥ 0` 与 `err γ = σ < 0` 矛盾）。 -/
theorem not_hasFitBoundary_of_neg {W : R238E3.ErrProfileWeak} {σ : ℝ} (hσ : σ < 0) :
    ¬ R238E3.HasFitBoundary W σ := by
  rintro ⟨γ, h1, _h2⟩
  have hnn := R238E3.ErrProfileWeak.err_nonneg W γ
  linarith

/-- ⭐⭐ **退化区一致性**（D.2 的定理形式）：σ < 0 时判据与边界**同时为空**。

⟹ 二者**不冲突**（一致地空），但**共同的盲区**须由使用处 `0 ≤ σ` 挡掉。 -/
theorem degeneracy_neg_consistent {W : R238E3.ErrProfileWeak} {σ : ℝ} (hσ : σ < 0) :
    (∀ ε, ¬ Canonical ε σ) ∧ ¬ R238E3.HasFitBoundary W σ :=
  ⟨canonical_false_of_neg hσ, not_hasFitBoundary_of_neg hσ⟩

/-! ### §4.3 σ = 0：判据退化为单点 `ε = 0` -/

/-- ⚠ **σ = 0 时判据 ⟺ `ε = 0`**（带退化为单点 `[0, 0]`）。 -/
theorem canonical_zero_iff {ε : ℝ} : Canonical ε 0 ↔ ε = 0 := by
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; subst h; norm_num

/-- ⚠ **σ = 0 处判据与 `bandLoss` 完全一致**（`bandLoss 0 ε = |ε|` 故二者同判）。 -/
theorem canonical_zero_iff_bandLoss {ε : ℝ} :
    Canonical ε 0 ↔ ScoreK.bandLoss 0 ε = 0 :=
  (bridge_bandLoss 0 ε).symm

/-! ===========================================================================
  §5  ⭐⭐ 裁决汇编：B3 的**单点可引用结论**
  =========================================================================== -/

/-- ⭐⭐ **裁决 K 判据统一的合取汇编**（供下游 / 审计单点引用）：

1. **三处判据（①②③）与权威口径互相充要**（实际上是同一谓词）；
2. **`bandLoss = 0` 无条件等价于权威口径**（`ScoreK` 的 `0 < σ` 前件冗余）；
3. **`bandCriterion`（⑤）与权威口径无条件等价**；
4. **σ < 0 时判据恒假**，故权威口径的**有效域须 `0 ≤ σ`**；
5. **边界点处判据必成立**（唯一的正向联系），但
   **`HasFitBoundary` 与「判据处处成立」互不蕴含**（两个反例见 §3）。

**⚠ 本定理是汇编，不是新数学**：它把上面已证的 ①②③④⑤ 打包，
使「B3 已裁决」这件事有一个**类型可检查**的凭证。 -/
theorem adjudicationK_criterion_unified :
    -- ①②③ 互相充要（⟹ 不存在强弱之分，只是重复定义）
    (∀ ε σ : ℝ, AttrAcceptable.AttrAcceptable ε σ ↔ Canonical ε σ) ∧
    (∀ ε σ : ℝ, ErrorCriterion.AttrAcceptableMirror ε σ ↔ Canonical ε σ) ∧
    -- ④ 无条件等价（0<σ 前件冗余）
    (∀ σ ε : ℝ, ScoreK.bandLoss σ ε = 0 ↔ Canonical ε σ) ∧
    -- ⑤ 无条件等价
    (∀ σ ε : ℝ, ErrorDimUnified.bandCriterion σ ε ↔ Canonical ε σ) ∧
    -- 退化区：σ<0 判据恒假
    (∀ {σ : ℝ}, σ < 0 → ∀ ε : ℝ, ¬ Canonical ε σ) ∧
    -- 唯一的正向联系：边界点处判据必成立
    (∀ {W : R238E3.ErrProfileWeak} {σ γ : ℝ},
      R238E3.IsFitBoundary W σ γ → Canonical (W.err γ) σ) :=
  ⟨bridge_attrAcceptable, bridge_attrAcceptableMirror, bridge_bandLoss,
    bridge_bandCriterion, fun hσ ε => canonical_false_of_neg hσ ε,
    fun h => isFitBoundary_implies_canonical h⟩

/-- ⭐ **B3 的「唯一权威口径」的最终表述**：权威口径就是 `σ/2 ≤ ε ≤ 2σ`，
且它就是 `bandLoss = 0`，也是（在 σ>0, ε>0 上）`|log(ε/σ)| ≤ log 2`。 -/
theorem canonical_three_faces (ε σ : ℝ) :
    (Canonical ε σ ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ) ∧
    (Canonical ε σ ↔ ScoreK.bandLoss σ ε = 0) ∧
    (0 < σ → 0 < ε → (Canonical ε σ ↔ |Real.log (ε / σ)| ≤ Real.log 2)) :=
  ⟨canonical_iff ε σ, (bridge_bandLoss σ ε).symm,
    fun hσ hε => canonical_iff_log hσ hε⟩

end

end ErrorCriterionUnified

end Fate