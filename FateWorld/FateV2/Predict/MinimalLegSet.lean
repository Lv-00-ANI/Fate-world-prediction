import FateWorld.FateV2.Predict.LegContribution
/-!
  # Predict · MinimalLegSet

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MinimalLegSet.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LegContribution
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §59  ⭐⭐ **最小充分腿集**（贡献分解的**优化版本**）

  ## 背景

  | 轮次 | 已证 |
  |---|---|
  | **57** | $\ker(\mathrm{joint}_n) = \bigsqcap_i \ker(f_i)$ |
  | **58** | 「腿 $i$ 冗余 $\iff$ 其余腿蕴含它」|

  **⟹ 本轮的优化问题**：**最小的必要腿集是什么？**

  ## 定义

  | 概念 | 定义 |
  |---|---|
  | **充分** | $I$ 的联合区分力 $=$ **全部**腿的联合区分力 |
  | **极小充分** | $I$ 充分，且 $I$ 的**任何真子集都不充分** |

  ## 本节的四个结果

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | ⭐⭐ **`sufficient_mono`** | **充分性的单调性**（加腿仍充分）|
  | **2** | ⭐⭐ **`exists_minimal_sufficient`** | ⭐ **极小充分集必存在**（有限情形）|
  | **3** | ⭐⭐ **`minimal_iff_no_redundant`** | ⭐ **极小 ⟺ 无冗余腿**（与 §58 对接）|
  | **4** | ⭐ **`full_is_sufficient`** | 全集平凡充分 |

  ## ⭐⭐ 核心洞察

  **「极小充分」与「无冗余」是**同一件事的两种说法****：
  - **§58 的「无冗余」**：每一条腿都**不可删**
  - **本节的「极小充分」**：任何**真子集**都不充分

  **⟹ 即**：**贡献分解的**局部**判据（单腿冗余）与**整体**判据（子集极小）
  在本框架下**完全一致**。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace MinimalLegSet

universe u v

variable {SCM : Type u}

/-! ### §59.1 ⭐⭐ 充分性的定义与单调性 -/

/-- ⭐⭐ **子集 $I$ 充分**：$I$ 的联合区分力等于**全部**腿的联合区分力。

$$\text{充分}(I) :=
  \forall a\,b,\ \bigl(\forall i \in I,\ f_i\,a = f_i\,b\bigr) \leftrightarrow
           \bigl(\forall i,\ f_i\,a = f_i\,b\bigr)$$ -/
def Sufficient {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) (I : Set (Fin n)) : Prop :=
  ∀ a b : SCM, (∀ i ∈ I, f i a = f i b) ↔ (∀ i, f i a = f i b)

/-- ⭐ **全集平凡充分**。 -/
theorem full_is_sufficient {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) : Sufficient f Set.univ :=
  fun _ _ => ⟨fun h i => h i trivial, fun h i _ => h i⟩

/-- ⭐⭐ **充分性的单调性**：加腿仍充分。

$$I \subseteq J \implies \text{充分}(I) \to \text{充分}(J)$$

**⟹ 即**：**「已有的充分腿集，加更多腿仍然充分」** ——
**这是「极小」定义有意义的前提。** -/
theorem sufficient_mono {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) {I J : Set (Fin n)} (hIJ : I ⊆ J)
    (hI : Sufficient f I) : Sufficient f J := by
  intro a b
  constructor
  · intro hJ
    exact (hI a b).mp fun i hi => hJ i (hIJ hi)
  · intro h i _
    exact h i

/-! ### §59.2 ⭐⭐ 极小充分 -/

/-- ⭐⭐ **极小充分**：$I$ 充分，且其**任何真子集都不充分**。

$$ \text{极小}(I) := \text{充分}(I) \wedge
  \forall J \subsetneq I,\ \neg\,\text{充分}(J)$$ -/
def MinimalSufficient {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) (I : Set (Fin n)) : Prop :=
  Sufficient f I ∧ ∀ J : Set (Fin n), J ⊂ I → ¬ Sufficient f J

/-! ### §59.3 ⭐⭐ 极小 ⟺ 无冗余（与 §58 对接） -/

/-- ⭐⭐ **极小充分 ⟹ 无冗余腿**（**与 §58 的对接**）。

**陈述**：若 $I$ 极小充分，则 $I$ 中**没有**任何腿是（相对 $I$ 的）冗余腿。

**即**：每一条腿都**不可删**。

**⟹ 即**：**贡献分解的**局部**判据（单腿冗余）与**整体**判据（子集极小）
在本框架下**完全一致**。** -/
theorem minimal_iff_no_redundant {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) (I : Set (Fin n)) :
    MinimalSufficient f I ↔
      Sufficient f I ∧ ∀ i ∈ I, ¬ Sufficient f (I \ {i}) := by
  constructor
  · rintro ⟨hS, hmin⟩
    refine ⟨hS, ?_⟩
    intro i hi hdel
    have hsub : I \ {i} ⊂ I := by
      refine ⟨fun x hx => hx.1, ?_⟩
      intro hcon
      have : i ∈ I \ {i} := hcon hi
      exact this.2 rfl
    exact hmin (I \ {i}) hsub hdel
  · rintro ⟨hS, hno⟩
    refine ⟨hS, fun J hJ hJS => ?_⟩
    obtain ⟨hJI, hne⟩ := Set.ssubset_iff_subset_ne.mp hJ
    have hex : ∃ i ∈ I, i ∉ J := by
      by_contra hc
      push Not at hc
      exact hne (Set.Subset.antisymm hJI hc)
    obtain ⟨i, hiI, hiJ⟩ := hex
    -- `J ⊆ I \ {i}`：用 `J ⊆ I` 且 `i ∉ J`
    have hJsub : J ⊆ I \ {i} := fun x hx => ⟨hJI hx, fun hcon => hiJ (hcon ▸ hx)⟩
    exact hno i hiI (sufficient_mono f hJsub hJS)

/-! ### §59.4 ⭐⭐ 极小充分集的存在性 -/

/-- ⭐⭐ **极小充分集必存在**（**有限腿集**）。

**陈述**：对任意有限腿集（`Fin n`），存在一个**极小充分**子集。

**⟹ 即**：**「最小的必要腿集」总是存在** ——
**这是「贡献分解」优化问题的**可解性保证****
（虽然本节**不给出**构造算法）。

**⚠ 本节只证**存在性**（用 `Set.univ` 平凡充分 + 有限性）；
**构造性版本**（如何**找到**它）留待后续。** -/
theorem exists_minimal_sufficient {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) :
    ∃ I : Set (Fin n), MinimalSufficient f I := by
  -- 用「充分子集的收集 + 极小元」论证；这里用 `Set.univ` 平凡充分 + 良基性
  classical
  by_contra h
  push Not at h
  -- 若不存在极小充分集，则可从 `univ` 起**无限下降** —— 与 `Fin n` 有限矛盾
  have : ∀ I : Set (Fin n), Sufficient f I → ∃ J ⊂ I, Sufficient f J := by
    intro I hI
    by_contra hc
    push Not at hc
    exact h I ⟨hI, fun J hJ => hc J hJ⟩
  -- 迭代产生严格下降链 —— 但 `Set (Fin n)` 有限，矛盾
  obtain ⟨J, hJsub, hJsuf⟩ := this Set.univ (full_is_sufficient f)
  -- 用 `ncard` 严格下降构造矛盾
  have hcard : ∀ I : Set (Fin n), Sufficient f I → ∃ J ⊂ I, Sufficient f J := this
  -- 从 `univ` 开始，每次 `ncard` 严格下降
  let rec descend : ∀ k : ℕ, ∃ I : Set (Fin n), I.ncard + k ≤ n ∧ Sufficient f I := by
    intro k
    induction k with
    | zero => exact ⟨Set.univ, by simp, full_is_sufficient f⟩
    | succ m ih =>
      obtain ⟨I, hIle, hIsuf⟩ := ih
      obtain ⟨J, hJsub, hJsuf⟩ := hcard I hIsuf
      refine ⟨J, ?_, hJsuf⟩
      have := Set.ncard_lt_ncard hJsub (Set.toFinite _)
      omega
  obtain ⟨I, hIle, _⟩ := descend (n + 1)
  have : I.ncard ≤ n := by
    have := Set.ncard_le_ncard (Set.subset_univ I) (Set.toFinite _)
    simpa using this
  omega

end MinimalLegSet

end FateV2.Predict