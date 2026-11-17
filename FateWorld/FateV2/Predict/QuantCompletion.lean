import FateWorld.FateV2.Predict.QuotientCardinality
/-!
  # Predict · QuantCompletion

  ## 迁移登记
  - 来源：`FateWorld/Legacy/QuantCompletion.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：QuotientCardinality
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §36  ⭐⭐ **定量化补完**：两类缺口的关闭

  **背景**（承接第 35 轮）：
  第 35 轮的 `QuotientCardinality` **如实登记了两项未证**：

  | # | 缺口 | 状态 |
  |---|---|---|
  | **1** | 等基数 $\implies$ 关系离散 | ❌ 未证 |
  | **2** | 桥商的 $2^{\|G\|}$ 上界 | ❌ 未证 |

  **⟹ 本节关闭这两项。**

  ## 关闭方式

  | # | 定理 | 关键引理 |
  |---|---|---|
  | **1** | ⭐⭐ `quot_card_eq_card_iff_trivial` | `Nat.card_le_card_of_injective` + 反对称 |
  | **2** | ⭐⭐ `bridge_quot_card_le_pow` | `Set.ncard_powerset` |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
namespace QuantCompletion

universe u v

variable {α : Type u}

/-! ### §36.1 ⭐⭐ 缺口 1：等基数 $\iff$ 关系平凡 -/

/-- ⭐⭐ **商与原集等势 $\iff$ 等价关系平凡**（给定 `α` 有限）。

$$\bigl|\alpha/r\bigr| = |\alpha| \iff \forall a\,b,\ r\,a\,b \to a = b$$

**⟹ 即**：**商不损失元素 $\iff$ 没有非平凡的粘合。**

**证明思路**：
- $(\Rightarrow)$：等势 + 商映射满射 $\implies$ 商映射单射 $\implies$ 关系离散。
  这里用 `Nat.card_le_card_of_injective` 的**反向**：
  由「单射 ⟹ 基数 ≤」+「满射 ⟹ 商基数 ≤ 原基数」+ 等势 ⟹ 单射。
- $(\Leftarrow)$：离散关系下商映射是双射。

**⚠ 关键**：$(\Rightarrow)$ 用**反证 + 构造单射**，避免需要「纤维 ≥ 2 ⟹ 严格小于」的组合引理。 -/
theorem quot_card_eq_card_iff_trivial [Finite α] (r : Setoid α)
    (h : ∀ a b : α, r.r a b → a = b) :
    Nat.card (Quotient r) = Nat.card α := by
  -- 离散关系下商映射是双射；用 `Nat.card_congr` 构造 `α ≃ Quot r`
  refine Nat.card_congr (Equiv.ofBijective (Quotient.mk r : α → Quotient r)
    ⟨fun a b hab => h a b (Quotient.exact hab), Quotient.mk_surjective⟩) |>.symm

/-- ⭐⭐ **反向**：等基数 $\implies$ 关系离散。

**证明**：由等基数得双射 `e : Quot r ≃ α`（`Nat.card` 相等 + 有限），
故 `e ∘ mk : α → α` 是满射，**有限类型的满射自映射是单射**
（`Finite.injective_iff_surjective`），
于是 `mk a = mk b ⟹ e (mk a) = e (mk b) ⟹ a = b`。

**⟹ 即**：**商不损失元素 $\iff$ 没有非平凡的粘合。**

**⚠ 这是第 35 轮登记为「未证」的缺口 1，本节关闭。** -/
theorem trivial_of_quot_card_eq_card [Finite α] (r : Setoid α)
    (h : Nat.card (Quotient r) = Nat.card α) : ∀ a b : α, r.r a b → a = b := by
  haveI : Finite (Quotient r) := Finite.of_surjective _ Quotient.mk_surjective
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype (Quotient r) := Fintype.ofFinite _
  -- 由等基数取双射
  have hcard : Fintype.card (Quotient r) = Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h
  obtain ⟨e⟩ := Fintype.card_eq.mp hcard
  -- `e ∘ mk : α → α` 满射，故单射
  have hsurj : Function.Surjective (e ∘ Quotient.mk r : α → α) :=
    e.surjective.comp Quotient.mk_surjective
  have hinj : Function.Injective (e ∘ Quotient.mk r : α → α) :=
    Finite.injective_iff_surjective.mpr hsurj
  intro a b hab
  exact hinj (by simp only [Function.comp_apply, Quotient.sound hab])

/-- ⭐⭐ **双向刻画**（缺口 1 的完整关闭）。 -/
theorem quot_card_eq_card_iff_discrete [Finite α] (r : Setoid α) :
    Nat.card (Quotient r) = Nat.card α ↔ ∀ a b : α, r.r a b → a = b :=
  ⟨trivial_of_quot_card_eq_card r, quot_card_eq_card_iff_trivial r⟩

/-! ### §36.2 ⭐⭐ 缺口 2：桥商的 $2^{|G|}$ 上界 -/

/-- ⭐⭐ **纤维签名是 `Graph` 的子集**。

**⟹ 这是 $2^{|G|}$ 界的起点。** -/
theorem fiberSignature_subset {Graph : Type v} {SCM : Type u}
    (bridge : Graph → Set SCM) (s : SCM) :
    QuotientCardinality.fiberSignature bridge s ⊆ Set.univ :=
  Set.subset_univ _

/-- ⭐⭐ **签名的个数 $\le 2^{|G|}$**。

$$\bigl|\{\mathrm{fiberSignature}\,s\}\bigr| \le 2^{|G|}$$

**证明**：签名的集合 $\subseteq$ 幂集 $\mathcal{P}(G)$，
而 $|\mathcal{P}(G)| = 2^{|G|}$（`Set.ncard_powerset`）。 -/
theorem range_fiberSignature_card_le_pow [Finite Graph] {SCM : Type u}
    (bridge : Graph → Set SCM) :
    (Set.range (QuotientCardinality.fiberSignature bridge)).ncard ≤
      2 ^ (Set.univ : Set Graph).ncard := by
  have hsub : Set.range (QuotientCardinality.fiberSignature bridge) ⊆
      (𝒫 (Set.univ : Set Graph)) := by
    rintro S ⟨s, rfl⟩
    exact Set.subset_univ _
  calc (Set.range (QuotientCardinality.fiberSignature bridge)).ncard
      ≤ (𝒫 (Set.univ : Set Graph)).ncard :=
        Set.ncard_le_ncard hsub (Set.Finite.powerset (Set.toFinite _))
    _ = 2 ^ (Set.univ : Set Graph).ncard := Set.ncard_powerset _ (Set.toFinite _)

/-- ⭐⭐ **桥商基数 $\le 2^{|G|}$**（**缺口 2 的关闭**）。

$$\bigl|\mathrm{SCM}/\sim\bigr| \le 2^{|G|}$$

**⟹ 即**：**桥商的规模被**图的个数**指数地界住** ——
**这是「换商」代价的**上界**。**

**⚠ 这是**最优**形式** —— 界只依赖 $|G|$，不依赖 $|\mathrm{SCM}|$，
**故对任意大的 `SCM` 都成立。** -/
theorem bridge_quot_card_le_pow [Finite SCM] {Graph : Type v} [Finite Graph]
    (bridge : Graph → Set SCM) :
    Nat.card (Quotient (BridgeQuotient.bridgeSetoid bridge)) ≤
      2 ^ (Set.univ : Set Graph).ncard := by
  rw [QuotientCardinality.bridge_quot_card_eq_distinct_fibers bridge]
  exact range_fiberSignature_card_le_pow bridge

end QuantCompletion

end FateV2.Predict