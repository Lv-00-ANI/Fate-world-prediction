import FateWorld.Legacy.ParametricEquiv

/-! ===========================================================================
  §29  ⭐⭐ **分档方案**：预测档 / 干预档 / 反事实档（原 `_probe_q29` 的正式化）

  **来源**：探针 `probes/_probe_q29.lean`（**不在构建内**，12 条定理）。

  ## 问题

  **若三视角都不能支撑完整反事实，是否存在分档方案（各用不同桥）？**

  ## ⭐⭐ 答案：**存在** —— 分档 = 一条**塔**

  | 档 | 读出 | 等价 |
  |---|---|---|
  | **预测** | $P(V)$ | $\sim_{\text{obs}}$（最粗）|
  | **干预** | 干预分布族 | $\sim_{\text{int}}$ |
  | **反事实** | 逐个体响应 | $\sim_{\text{cf}}$（最细）|

  **档间由「细化」连接**：粗档泛函 = 细档泛函**复合遗忘**。

  ## ⭐ 塔给出**单向免费结论**

  $$\text{粗档能单值} \implies \text{细档也能单值}$$

  **⚠ 其逆不成立** —— **存在预测档可用而反事实档塌不掉的情形**，
  **故「分档」不是冗余。**

  **⚠ 但塔也不免费提供塔顶**：反事实档单值仍取决于「反事实外坐标」。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace TieredScheme

universe u v

/-! ### §29.1 档：一条链 -/

/-- ⭐ **三档**。 -/
inductive Tier where
  | predict
  | intervene
  | counterfactual
  deriving DecidableEq

/-- ⭐ **档序**：`predict ⪯ intervene ⪯ counterfactual`。

**越靠右 = 读出的信息越多 = 等价越**细**。** -/
def Tier.le : Tier → Tier → Prop
  | .predict, _ => True
  | .intervene, .intervene => True
  | .intervene, .counterfactual => True
  | .counterfactual, .counterfactual => True
  | _, _ => False

/-- ⭐ **三档成链**（全序）—— 「分档」是**一条轴**而非一张网的根据。 -/
theorem tier_chain (τ σ : Tier) : Tier.le τ σ ∨ Tier.le σ τ := by
  cases τ <;> cases σ <;> simp [Tier.le]

/-- ⭐ **链的传递性**。 -/
theorem tier_le_trans (a b c : Tier) : Tier.le a b → Tier.le b c → Tier.le a c := by
  cases a <;> cases b <;> cases c <;> simp [Tier.le]

/-! ### §29.2 档索引的桥族与观测泛函 -/

/-- ⭐ **分档桥**：三档各一条 `Graph → Set SCM`。 -/
structure Bridge (Graph : Type v) (SCM : Type u) where
  /-- 正向单值：每个 SCM 诱导唯一图。 -/
  induce : SCM → Graph
  /-- 逆向集合值，**按档索引**。 -/
  bridge : Tier → Graph → Set SCM
  /-- **可靠性**：无论哪一档，真值 SCM 必落在它自己诱导出的图的纤维里。 -/
  sound : ∀ τ g s, induce s = g → s ∈ bridge τ g

/-- ⭐ **分档观测泛函**：每档一个「读出」映射。 -/
structure Obs (SCM : Type u) where
  /-- 每档的读出值类型。 -/
  Val : Tier → Type u
  /-- 从 SCM 读出该档的值。 -/
  obs : ∀ τ, SCM → Val τ

/-! ### §29.3 ⭐ 塔的两种表述 -/

/-- ⭐ **塔假设（桥侧，纤维单调）**：细档纤维 $\subseteq$ 粗档纤维。 -/
def IsTowerB {Graph : Type v} {SCM : Type u} (B : Bridge Graph SCM) : Prop :=
  ∀ g, B.bridge .counterfactual g ⊆ B.bridge .intervene g ∧
    B.bridge .intervene g ⊆ B.bridge .predict g

/-- ⭐ **细化**：`fine` 档比 `coarse` 档读得**多**（故等价**细**）。 -/
def Refines (fine coarse : Tier) : Prop :=
  Tier.le coarse fine

/-- ⭐ **塔假设（泛函侧，细化）**：细档泛函 = 粗档泛函复合遗忘。 -/
def IsTowerO {SCM : Type u} (_O : Obs SCM) : Prop :=
  Refines .counterfactual .intervene ∧ Refines .intervene .predict

/-- ⭐ **细化的传递性**。 -/
theorem refines_trans {a b c : Tier} (h₁ : Refines a b) (h₂ : Refines b c) :
    Refines a c :=
  tier_le_trans _ _ _ h₂ h₁

/-! ### §29.4 ⭐⭐ 可区分性与塌缩 -/

/-- ⭐ **档 `τ` 在 `F` 上可区分**：`F` 内的点在 `τ`-读出下可分。 -/
def DiscrimOn {SCM : Type u} (O : Obs SCM) (τ : Tier) (F : Set SCM) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, O.obs τ s = O.obs τ t → s = t

/-- ⭐ **档 `τ` 在 `F` 上塌缩**：`F` 内的点在 `τ`-读出下全同。 -/
def CollapseOn {SCM : Type u} (O : Obs SCM) (τ : Tier) (F : Set SCM) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, O.obs τ s = O.obs τ t

/-! ### §29.5 ⭐⭐ 塔的单向免费结论 -/

/-- ⭐⭐ **塔的核心定理：粗档能单值 ⟹ 细档也能单值**。

**精确陈述**：若 `coarse ⪯ fine`（粗档读得少），
且**粗档**在 `F` 上可区分，**且细档的读出细于粗档**
（即 `obs coarse` 可由 `obs fine` 分解），则**细档**在 `F` 上也可区分。

**⟹ 即**：**塔给出**单向免费结论**** ——
**在粗档能区分的地方，细档必然也能。**

**⚠ 本节的 `IsTowerO` 只声明了档序，**未**声明「泛函可分解」**——
故本定理把「可分解」作**显式前件**（`hfac`）。

**这是对原探针的一处精确化**：原探针的 `discriminates_of_refines`
依赖「细档泛函细化粗档」，而这须显式陈述。 -/
theorem discriminates_of_refines {SCM : Type u} (O : Obs SCM) {fine coarse : Tier}
    (hfac : ∃ φ : O.Val fine → O.Val coarse, ∀ s, O.obs coarse s = φ (O.obs fine s))
    {F : Set SCM} (h : DiscrimOn O coarse F) : DiscrimOn O fine F := by
  obtain ⟨φ, hφ⟩ := hfac
  intro s hs t ht heq
  exact h s hs t ht (by rw [hφ s, hφ t, heq])

/-- ⭐⭐ **塔顶不免费**（**反例**）。

**陈述**：存在分档观测泛函，其**粗档可区分**而**细档塌缩** ——
**只要细档与粗档**无关**（不构成塔）。**

**⟹ 这是本节的**诚实边界**：
**塔的单向结论**依赖**细化关系** ——
**没有细化关系时，「粗档能 ⟹ 细档能」不成立。** -/
theorem top_tier_not_automatic :
    ∃ (O : Obs Bool), ∃ F : Set Bool,
      DiscrimOn O Tier.predict F ∧ ¬ DiscrimOn O Tier.counterfactual F := by
  -- 构造：`Val` 对所有档都取 `Option Bool`；`predict` 读出 `some s`，其余读出 `none`
  let O : Obs Bool :=
    ⟨fun _ => Option Bool,
     fun τ s => if τ = Tier.predict then some s else none⟩
  refine ⟨O, Set.univ, ?_, ?_⟩
  · intro s _ t _ heq
    simp only [O, ↓reduceIte, Option.some.injEq] at heq
    exact heq
  · intro h
    have hc : Tier.counterfactual ≠ Tier.predict := by decide
    have := h true (Set.mem_univ _) false (Set.mem_univ _) (by
      simp only [O, hc, ↓reduceIte])
    exact Bool.noConfusion this

/-- ⭐ **档内三分（沿用 `MiddleZoneDichotomy` 的结构）**。

**陈述**：对任意档 `τ` 与任意 `F ⊆ SCM`，
`F` 上的读出要么**塌缩**、要么**可区分**、要么**中间**。

**⚠ 本定理是**结构性的****：它说明三档各自都有自己的三分，
**故「分档」不消除「中间地带」，只是把它按档细分。** -/
theorem per_tier_trichotomy {SCM : Type u} (O : Obs SCM) (τ : Tier) (F : Set SCM) :
    CollapseOn O τ F ∨ DiscrimOn O τ F ∨
      (¬ CollapseOn O τ F ∧ ¬ DiscrimOn O τ F) := by
  by_cases hc : CollapseOn O τ F
  · exact Or.inl hc
  · by_cases hd : DiscrimOn O τ F
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr ⟨hc, hd⟩)

/-- ⭐ **可区分性对子集单调**（更小的集合更易区分）。 -/
theorem discriminates_of_subset {SCM : Type u} (O : Obs SCM) {τ : Tier} {F G : Set SCM}
    (hGF : G ⊆ F) (h : DiscrimOn O τ F) : DiscrimOn O τ G :=
  fun s hs t ht heq => h s (hGF hs) t (hGF ht) heq

/-! ### §29.6 ⭐ 塔的存在性 -/

/-- ⭐⭐ **塔总存在**（给定正向映射即可构造）。

**构造**：取 `bridge τ g := {s | induce s = g}`（**所有档相同**）——
这是**平凡塔**（三档相同）。

**⟹ 即**：**塔的存在性不是问题** ——
**问题是能否构造**非平凡**的塔（各档真的有区分力差异）。** -/
theorem tower_always_exists {SCM : Type u} {Graph : Type v} (induce : SCM → Graph) :
    ∃ B : Bridge Graph SCM, B.induce = induce ∧ IsTowerB B := by
  refine ⟨⟨induce, fun _ g => {s | induce s = g}, fun _ _ s h => h⟩, rfl, ?_⟩
  intro g
  exact ⟨fun _ h => h, fun _ h => h⟩

end TieredScheme

end Fate
