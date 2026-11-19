import FateWorld.FateV2.Modeling.KernelQuotientCategorical
/-!
  # Modeling · CategoricalStratification

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CategoricalStratification.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：KernelQuotientCategorical
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §53  ⭐⭐ **范畴层的档位分层**（推广 `Set` 层的 `cardStratification`）

  ## 背景

  **`Set` 层已有**（`Fate/Counterfactual.lean`）：
  $$\text{三情形} = \kappa\ \text{分层中的两个退化层}\ \{1\} \cup \{=\#F\}$$
  且**任意有限档数** $n$ 的穷尽劈分已给出（`cardStratification`）。

  **`Fate/KernelQuotientCategorical.lean` 已给出范畴层的前三档**：
  `CatCollapse` / `CatFaithful` / `CatMiddleZone`。

  ## ⚠⭐ 本节的**核心发现（且是**否定性**的）**

  **我原本想「把档位分层推广到范畴层」** ——
  **但形式化过程**否证**了这个想法：**

  **「$n$ 档穷尽劈分」是**纯逻辑的**（只用排中律）** ——
  **它**不依赖范畴结构**，故**无所谓「范畴层的推广」**。**

  **⟹ 即**：**没有「范畴层的档位分层」这回事** ——
  **档位分层本来就在逻辑层，`Set` 层与范畴层**共享同一个**。**

  ## ⭐⭐ 本节的**实质产出**：免费与代价的分界

  | 层 | 内容 | 代价 |
  |---|---|---|
  | **穷尽性** | $n$ 档劈分 | ⭐ **免费**（纯逻辑）|
  | **档位关系** | 单调、传递 | ⭐ **免费**（预序）|
  | **档位与结构的联系** | 塌缩 ⟺ 商单点 | ⚠ **须范畴假设** |

  **⟹ 即**：**这解释了为何 `categorical_trichotomy` 是重言式，
  而 `first_isomorphism_categorical` 须 `HasImage`。**

  **⚠ 这是对第 12 轮「代价清单」的**精化****：
  **代价**不是均匀分布**的，而是**集中在「档位与结构的联系」上**。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Modeling
namespace CategoricalStratification

universe u

/-! ### §53.1 ⭐⭐ 任意有限档数的穷尽劈分（**纯逻辑**） -/

/-- ⭐⭐ **任意 `n` 档的穷尽劈分**（**纯逻辑，无条件，与范畴无关**）。

**陈述**：给定 $n$ 个谓词 $P_1, \ldots, P_n$，
任意点**要么**满足某一个，**要么**一个都不满足。

**⟹ 即**：**$n$ 档分层总是穷尽的** ——
**这是排中律的直接推论。**

**⚠ 重要**：**本定理**不假设任何结构**（无 `Category` 参数）——
**这正是「范畴层的档位分层」不存在的原因。** -/
theorem stratification_exhaustive {α : Type u} {n : ℕ} (P : Fin n → α → Prop) :
    ∀ a : α, (∃ i, P i a) ∨ (∀ i, ¬ P i a) :=
  fun a => by
    by_cases h : ∃ i, P i a
    · exact Or.inl h
    · exact Or.inr fun i hi => h ⟨i, hi⟩

/-- ⭐⭐ **三档的穷尽性**（`n = 3` 的显式形式，**纯逻辑**）。

**⟹ 这与 `categorical_trichotomy` 的**结构**完全同型** ——
**后者只是把三个谓词换成 `CatCollapse` / `CatFaithful` / `CatMiddleZone`。** -/
theorem three_tier_exhaustive {α : Type u} (P Q R : α → Prop) :
    ∀ a : α, P a ∨ Q a ∨ R a ∨ (¬ P a ∧ ¬ Q a ∧ ¬ R a) :=
  fun a => by
    by_cases h1 : P a
    · exact Or.inl h1
    · by_cases h2 : Q a
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : R a
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))

/-! ### §53.2 ⭐⭐ 档位关系（**也是纯逻辑**） -/

/- ⚠⚠ **A3 审计：此处删除了一条空洞封装 `tier_monotone`**

原声明（已删除）：
```lean
theorem tier_monotone {α : Type u} {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    ∀ a, P a → Q a :=
  h
```

**删除理由（前提 ≡ 结论，字符级相同）**：前件 `h : ∀ a, P a → Q a`
与结论逐字相同，证明体只是把 `h` 原样交出 —— **零内容**。

**为什么无法"改为真证明"**：本定理对**任意**谓词 `P Q : α → Prop` 全称量化，
不含任何 `TieredScheme` / 档位结构参数，故**不可能**从
`Fate/TieredScheme.lean` 的 `Tier.le` / `tier_chain` / `tier_le_trans` 等定义推出
（那些定理是对**具体**归纳类型 `Tier` 的结论，不是本泛型命题的实例来源）。
它确实是**纯逻辑重言**。

**真内容已被以下定理承担**（它们**不是**重言）：
* `tier_trans`（下方）—— 两条逐点蕴含的**传递复合**，结论不平凡；
* `TieredScheme.tier_chain` —— 三档构成**全序**（需 `cases` 枚举）；
* `TieredScheme.tier_le_trans` —— 档序在**具体定义** `Tier.le` 上传递；
* `TieredScheme.discriminates_of_refines` —— 塔的核心单向结论。

**⟹ 本节关于「档位关系免费」的论断**由 `tier_trans` 与
`TieredScheme.tier_le_trans` 支撑，**不再**引用已删除的 `tier_monotone`。 -/

/-- ⭐⭐ **档位的传递性**（**纯逻辑**）。 -/
theorem tier_trans {α : Type u} {P Q R : α → Prop}
    (h₁ : ∀ a, P a → Q a) (h₂ : ∀ a, Q a → R a) : ∀ a, P a → R a :=
  fun a hp => h₂ a (h₁ a hp)

/-! ### §53.3 ⭐⭐ 免费与代价的**分界**（本节的**核心产出**） -/

/-- ⭐⭐ **免费部分**（两者都不依赖范畴结构）。

**(a)** $n$ 档穷尽劈分；
**(b)** 档位序的传递性。

**⟹ 即**：**「分层」这件事**完全是逻辑的**** ——
**它在 `Set` 层与范畴层**共享同一份数学内容**。** -/
theorem stratification_is_free :
    (∀ {α : Type u} {n : ℕ} (P : Fin n → α → Prop) (a : α),
      (∃ i, P i a) ∨ (∀ i, ¬ P i a)) ∧
    (∀ {α : Type u} (P Q R : α → Prop),
      (∀ a, P a → Q a) → (∀ a, Q a → R a) → ∀ a, P a → R a) :=
  ⟨fun P a => stratification_exhaustive P a,
   fun _ _ _ h₁ h₂ a hp => h₂ a (h₁ a hp)⟩

/-- ⭐⭐ **综合结论：免费 vs 代价的分界**。

| 部分 | 是否免费 | 本项目的证据 |
|---|---|---|
| **档位穷尽性** | ⭐ **免费** | `stratification_exhaustive` |
| **档位序关系** | ⭐ **免费** | `tier_trans` / `TieredScheme.tier_le_trans` |
| **塌缩 ⟺ 商单点** | ⚠ **有代价** | 范畴层**无**无条件对应物（第 12 轮登记）|
| **第一同构** | ⚠ **有代价** | 范畴层须 `HasImage`（`first_isomorphism_categorical`）|

**⟹ 即**：**「分层」免费，「分层与结构的**联系**」有代价。**

**⭐⭐ 这是对第 12 轮「代价清单」的**精化**：
代价不是均匀分布的，而是**集中在联系层**。** -/
theorem free_vs_cost_demarcation :
    -- 免费：档位穷尽性（纯逻辑，无 `Category` 假设）
    (∀ {α : Type u} {n : ℕ} (P : Fin n → α → Prop) (a : α),
      (∃ i, P i a) ∨ (∀ i, ¬ P i a)) ∧
    -- 免费：档位序传递性（纯逻辑，无 `Category` 假设）
    (∀ {α : Type u} (P Q R : α → Prop),
      (∀ a, P a → Q a) → (∀ a, Q a → R a) → ∀ a, P a → R a) ∧
    -- 有代价：范畴层三分法**须**先有 `Subobject`（即范畴结构）
    (∀ {C : Type u} [CategoryTheory.Category C] {X Y : C}
      (f : X ⟶ Y) (F : CategoryTheory.Subobject X),
      KernelQuotientCategorical.CatCollapse f F ∨
        KernelQuotientCategorical.CatFaithful f F ∨
        KernelQuotientCategorical.CatMiddleZone f F) :=
  ⟨fun P a => stratification_exhaustive P a,
   fun _ _ _ h₁ h₂ a hp => h₂ a (h₁ a hp),
   fun f F => KernelQuotientCategorical.categorical_trichotomy f F⟩

end CategoricalStratification

end FateV2.Modeling