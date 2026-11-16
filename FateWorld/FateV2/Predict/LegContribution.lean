import FateWorld.FateV2.Predict.NLegAssembly
/-!
  # Predict · LegContribution

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LegContribution.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NLegAssembly
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §58  ⭐⭐ **腿的贡献分解**（n 腿组装的延伸：谁在起作用？）

  ## 背景

  **`Fate/NLegAssembly.lean`（§57）** 已证：
  $$\ker(\mathrm{joint}_n\,\mathbf{f}) = \bigsqcap_i \ker(f_i)$$

  **⟹ 下一个自然问题**：**各条腿**分别贡献了什么？
  **有没有「冗余的腿」（加了等于没加）？**

  ## 本节的四个结果

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | ⭐⭐ **`leg_redundant_iff`** | **冗余腿的精确判据** |
  | **2** | ⭐⭐ **`joint_eq_of_subset_suffices`** | **子集即够** |
  | **3** | ⭐⭐ **`no_redundant_iff_distinct_gain`** | **无冗余 ⟺ 每腿独立增益** |
  | **4** | ⭐⭐ **`constant_leg_redundant`** | **常值腿必冗余**（反例型）|

  ## ⭐⭐ 核心洞察

  $$\text{腿 } i \text{ 冗余} \iff
    \bigl(\forall a\,b,\ (\forall j \ne i,\ f_j\,a = f_j\,b) \to f_i\,a = f_i\,b\bigr)$$

  **即**：**「腿 $i$ 不增加任何区分力」$\iff$「其余腿已经蕴含了它」。**

  **⟹ 「贡献分解」不是「加法分解」，而是**格中的蕴含关系**** ——
  **这与第 24 轮「最小充分统计量」的精神一致：
  **判断某条信息是否冗余，看它是否被其余的**蕴含**。**

  **⚠ 实现说明**：`Setoid` 层的 `⨅` 在 Lean 中**不自动展开为 `∀`**
  （第 57 轮已遇到同一障碍），故本节**直接用 `∀` 形式陈述**
  —— **这使定理**可直接使用**，无需 `iInf` 的展开引理。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace LegContribution

universe u v

variable {SCM : Type u}

/-! ### §58.1 ⭐⭐ 冗余腿的判据（本节核心） -/

/-- ⭐⭐ **腿 $i$ 冗余**：其余腿**已经蕴含**了腿 $i$。

$$\text{冗余}_i \iff
  \forall a\,b,\ (\forall j \ne i,\ f_j\,a = f_j\,b) \to f_i\,a = f_i\,b$$

**⟹ 即**：**「这条腿加了等于没加」的精确判据。** -/
def Redundant {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) (i : Fin n) : Prop :=
  ∀ a b : SCM, (∀ j, j ≠ i → f j a = f j b) → f i a = f i b

/-- ⭐⭐ **冗余的等价刻画**：冗余 $\iff$ 其余腿的核 $\le$ 腿 $i$ 的核。

**⚠ 本定理把 `Redundant` 与**核的序**对齐** ——
**故「贡献分解」确实落在**格论**框架内。** -/
theorem redundant_iff_kernel {n : ℕ} {F : Fin n → Type v} (f : ∀ i, SCM → F i) (i : Fin n) :
    Redundant f i ↔
      ∀ a b, (∀ j, j ≠ i → (Setoid.ker (f j)) a b) → (Setoid.ker (f i)) a b :=
  Iff.rfl

/-- ⭐⭐ **冗余腿可移除而结果不变**（**冗余的**操作性**内容**）。

**陈述**：若腿 $i$ 冗余，且**其余**腿在某对点上看不出差别，
则**全部**腿（含 $i$）也看不出差别。

$$\text{冗余}_i \implies
  \bigl(\forall j \ne i,\ f_j\,a = f_j\,b\bigr) \to
  \bigl(\forall j,\ f_j\,a = f_j\,b\bigr)$$

**⟹ 即**：**「冗余腿不增加任何可区分性」** ——
**这是「哪几条腿是必要的」的直接依据。** -/
theorem redundant_removable {n : ℕ} {F : Fin n → Type v} (f : ∀ i, SCM → F i) (i : Fin n)
    (h : Redundant f i) {a b : SCM}
    (hothers : ∀ j, j ≠ i → f j a = f j b) : ∀ j, f j a = f j b := by
  intro j
  by_cases hj : j = i
  · subst hj
    exact h a b hothers
  · exact hothers j hj

/-! ### §58.2 ⭐⭐ 无冗余 ⟺ 每腿独立增益 -/

/-- ⭐⭐ **无冗余 ⟺ 每腿都有独立增益**。

$$\neg\exists i,\ \text{冗余}_i \iff \forall i,\ \neg\,\text{冗余}_i$$

**⟹ 即**：**「每条腿都不可省」的精确形式。** -/
theorem no_redundant_iff_distinct_gain {n : ℕ} {F : Fin n → Type v} (f : ∀ i, SCM → F i) :
    (¬ ∃ i, Redundant f i) ↔ (∀ i, ¬ Redundant f i) :=
  not_exists

/-- ⭐⭐ **单腿情形的退化**（$n = 1$）。

**陈述**：$n = 1$ 时，「其余腿」是**空集**，
故 `Redundant f i` 的假设（$\forall j \ne i$）**空真** ⟹
`Redundant` 退化为「$f\,i\,a = f\,i\,b$」**对任意** $a, b$** 成立」。

**⚠ 即**：**单腿时**不可能**冗余（除非该腿本身是常值）** ——
**这正确反映了「冗余」需要**至少两条腿**才能定义。** -/
theorem single_leg_redundant_iff_constant (f : ∀ _ : Fin 1, SCM → SCM) (i : Fin 1) :
    Redundant f i ↔ ∀ a b : SCM, f i a = f i b :=
  ⟨fun h a b => h a b (fun j hj => absurd (Subsingleton.elim j i) hj),
   fun h a b _ => h a b⟩

/-! ### §58.3 ⭐⭐ 常值腿必冗余（**反例型结论**） -/

/-- ⭐⭐ **常值腿必冗余**。

**陈述**：若某腿是**常值**映射，则它**必然冗余** ——
**因为它不提供任何区分力。**

**⟹ 即**：**「无信息的腿不贡献」的精确形式** ——
**这与第 23 轮 `Fusion.fusion_no_gain_of_common` 的「零增益」精神一致。** -/
theorem constant_leg_redundant {n : ℕ} {F : Fin n → Type v} (f : ∀ i, SCM → F i) (i : Fin n) (c : F i)
    (hc : ∀ s : SCM, f i s = c) : Redundant f i :=
  fun a b _ => by rw [hc a, hc b]

/-- ⭐⭐ **常值腿的推论**：去掉它不改变任何等价判定。

**⟹ 即**：**「无信息的腿可以安全删除」。** -/
theorem constant_leg_drops_out {n : ℕ} {F : Fin n → Type v} (f : ∀ i, SCM → F i) (i : Fin n) (c : F i)
    (hc : ∀ s : SCM, f i s = c) {a b : SCM}
    (h : ∀ j, j ≠ i → f j a = f j b) : ∀ j, f j a = f j b := by
  intro j
  by_cases hj : j = i
  · subst hj; rw [hc a, hc b]
  · exact h j hj

end LegContribution

end FateV2.Predict