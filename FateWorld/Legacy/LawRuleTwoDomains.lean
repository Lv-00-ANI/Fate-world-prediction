/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.LawRuleTwoDomains
主题：**`LawRule` 的两个领域实例 + 共享格骨架（通用性实证）**

---------------------------------------------------------------------------
本模块做什么
---------------------------------------------------------------------------
第 857 轮宏观重估指出 `LawRule` 是完备格，且 `compose R₁ R₂ = R₁ ⊓ R₂`
（`LawRule.compose_eq_inf`）。但此前「通用」只在**类型参数层面**成立：
`LawRule C X Y` 只是个类型表达式，没有任何**领域**层面的两个实例共享它。

本模块用**同一个** `LawRule` 骨架写两个**真正不同**的领域实例，并证明它们
共享 `compose` / `compose_eq_inf`：

* **实例 A —— 线性回归（确定性，输出空间 `ℝ`）**
  `linRule a c x := {δ_{a·x}}`：给定零截距斜率 `a` 与输入 `x`，
  规律唯一确定观测分布 `δ_{a·x}`。

* **实例 B —— 二状态马尔可夫链（随机，输出空间 `Fin 2`）**
  `markovRule p c i := { p • δ₁ + (1-p) • δ₀ }`：给定转移概率 `p`，
  规律唯一确定下一步状态的**两点混合**分布。

两例在**数学上不同类**（确定性 vs 随机；`ℝ` vs `Fin 2`；`δ` vs 加权和），
却共享同一 `LawRule C X Y` 定义与同一 `compose = ⊓` 定理 —— 这是「通用」
从类型参数层落到**领域**层的实证。

---------------------------------------------------------------------------
内容清单
---------------------------------------------------------------------------
§1 两个领域共用的上下文空间 `C₀` 与两个（不同的）输出空间。
§2 实例 A：`linRule`；可辨识性 `linRule_identifiable`（真实内容：
   斜率被规律**读出**，非装饰参数）。
§3 实例 B：`markovRule`；总质量计算 `markovRule_val_one` 与可辨识性
   `markovRule_identifiable`。
§4 ⭐ 共享骨架：两例都满足 `compose_eq_inf`（各自 `⊓` 的实例）。
§5 ⭐⭐ 非平凡内容：`linRule a ∘ linRule b` 的允许集**非空 ⟺ a = b`
   （组合是**真约束**，不是空谈）。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- **未修改任何已有模块**；本文件是新增的独立模块，仅 `import Fate.LawRuleLattice`。
- 零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats` / `?_`。
- 本模块**不**声称 `compose = ⊓` 是「规则复合」在语义上唯一正确的读法；
  它只证明**在同一 `LawRule` 定义下**，两个不同领域的实例都共享该等式
  （`LawRuleLattice` 已登记「`⊆` 还是 `⊇` 作序」为开放问题）。
- 实例 B 的参数 `p : ENNReal` 是**总质量参数**（`p` 即 `μ {1}`）；
  未附加 `p ≤ 1` 的概率归一化前件，因为 `LawRule` 的载体是**任意测度**，
  不限于概率测度 —— 这是骨架的实际范围，如实登记。
- 存在性：两实例均在每点给出**单点允许集**（`IsPoint` 档），
  不涉及复合相容性以外的深层分析。
-/

import FateWorld.Legacy.LawRuleLattice

namespace Fate

namespace LawRuleTwoDomains

open MeasureTheory

open LawRule

/-! ===========================================================================
    §1  两个领域共用的上下文空间与各自（不同）的输出空间
    =========================================================================== -/

/-- **共享上下文空间**：单点上下文（无额外条件信息）。

两领域都用它 —— 这是「同一骨架」在上下文侧的直接体现；
差异全部落在状态 / 输出空间与规则本体上。 -/
abbrev C₀ : CtxSpace := ⟨PUnit⟩

/-- **实例 A 的空间**：`ℝ`（实直线的标准拓扑与可测结构）。

状态空间与输出空间**同为** `ℝ`（回归：输入与观测都是实数）。 -/
abbrev Xℝ : StateSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)
  borel_le := OpensMeasurableSpace.borel_le

/-- **实例 B 的空间**：`Fin 2`（二状态的标准拓扑与可测结构）。

状态空间与输出空间**同为** `Fin 2`（马尔可夫链：状态 = 下标的有限集）。 -/
abbrev XF2 : StateSpace where
  Carrier := Fin 2
  topo := inferInstanceAs (TopologicalSpace (Fin 2))
  meas := inferInstanceAs (MeasurableSpace (Fin 2))
  borel_le := OpensMeasurableSpace.borel_le

/-! ===========================================================================
    §2  实例 A：线性回归的 `LawRule`
    =========================================================================== -/

/-- **实例 A（线性回归规则）**。

给定零截距斜率 `a : ℝ`，规则 `linRule a` 在上下文 `c` 与输入 `x` 处允许
**唯一**分布 `δ_{a·x}`（确定性退化：残差为零）。

与实例 B 对照：这里是**单点测度**，输出空间是**不可数**的 `ℝ`。 -/
noncomputable def linRule (a : ℝ) : LawRule C₀ Xℝ Xℝ :=
  fun _ x => {Measure.dirac (a * x)}

/-- **实例 A 单点档**：`linRule a` 是 `IsPoint`（允许集恒为单点集）。 -/
theorem linRule_isPoint (a : ℝ) : IsPoint (linRule a) :=
  fun _ x => ⟨Measure.dirac (a * x), rfl⟩

/-- **实例 A 的斜率可辨识**：若两条斜率 `a`、`b` 产生**同一个**规则，
则 `a = b`。

证明要点：在输入 `x = 1` 处比较 `δ_{a·1}` 与 `δ_{b·1}`（`linRule` 的定义性展开），
再用「`δ_m = δ_n → m = n`」这一事实（把等式两边作用在单点集 `{a·1}` 上，
一边得 `1`、另一边得 `0`，矛盾）。

**这不是同义反复**：前件是「规则相等」，结论是「参数相等」，二者中间隔着
`δ` 的**单射性**这一实质步骤（规律把参数读出，而非把结论包进前件）。 -/
theorem linRule_identifiable {a b : ℝ} (h : linRule a = linRule b) : a = b := by
  -- 取 x = 1 处两条规则的允许集相等
  have h1 : (Measure.dirac (a * 1) : Measure ℝ) = Measure.dirac (b * 1) := by
    have h2 : linRule a PUnit.unit 1 = linRule b PUnit.unit 1 := by rw [h]
    rw [linRule, linRule] at h2
    exact Set.singleton_injective h2
  by_contra hne
  have hab : a * 1 ≠ b := by simpa using hne
  -- 在单点集 {a·1} 上求质量：左边为 1
  have h' := congrArg (fun μ : Measure ℝ => μ {a * 1}) h1
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton (a * 1))] at h'
  -- 右边（δ_{b·1}）在 {a·1} 上为 0，因为 b·1 ≠ a·1
  have hb : (b * 1) ∉ ({a * 1} : Set ℝ) := by
    simp only [Set.mem_singleton_iff]
    intro hh; exact hab (by simpa using hh.symm)
  rw [Measure.dirac_apply, Set.indicator_of_notMem hb] at h'
  exact one_ne_zero h'

/-! ===========================================================================
    §3  实例 B：二状态马尔可夫链的 `LawRule`
    =========================================================================== -/

/-- **实例 B（二状态马尔可夫链规则）**。

给定总质量参数 `p : ENNReal`，规则 `markovRule p` 在上下文 `c` 与状态 `i` 处
允许**唯一**分布

    μ_p := p • δ₁ + (1 - p) • δ₀,

即「下一步为状态 1 的权重是 `p`、为状态 0 的权重是 `1 - p`」的两点混合
（`μ_p {1} = p`，见 `markovRule_val_one`）。

与实例 A 对照：这里是**加权和**而非单点测度，输出空间是**有限**的 `Fin 2`。
两例的数学结构不同，却共享同一骨架 —— 这正是通用性实证的关键。 -/
noncomputable def markovRule (p : ENNReal) : LawRule C₀ XF2 XF2 :=
  fun _ _ =>
    Set.singleton (p • (Measure.dirac (1 : Fin 2)) + (1 - p) • Measure.dirac (0 : Fin 2))

/-- **实例 B 单点档**：`markovRule p` 是 `IsPoint`（允许集恒为单点集）。 -/
theorem markovRule_isPoint (p : ENNReal) : IsPoint (markovRule p) := by
  intro c i
  exact ⟨p • (Measure.dirac (1 : Fin 2)) + (1 - p) • Measure.dirac (0 : Fin 2), rfl⟩

/-- **实例 B 的总质量计算**：`μ_p {1} = p`。

这是把 `p` 与可观测量（在状态 `1` 上的质量）**对齐**的桥，
后续可辨识性直接用到它。 -/
theorem markovRule_val_one (p : ENNReal) :
    (p • (Measure.dirac (1 : Fin 2)) + (1 - p) • Measure.dirac (0 : Fin 2)) {1} = p := by
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_singleton (1 : Fin 2))]
  have h0 : (0 : Fin 2) ∉ ({1} : Set (Fin 2)) := by
    simp [Set.mem_singleton_iff, zero_ne_one]
  rw [Measure.dirac_apply, Set.indicator_of_notMem h0, smul_zero, add_zero,
      smul_eq_mul, mul_one]

/-- **实例 B 的参数可辨识**：若两条参数 `p`、`q` 产生**同一个**规则，则 `p = q`。

证明：把规则相等在 `(c, i) = (unit, 0)` 处展开得到 `μ_p = μ_q`，
对 `{1}` 取质量，由 `markovRule_val_one` 得 `p = q`。

**这不是同义反复**：前件「规则相等」给出「测度相等」，结论「参数相等」
需经 `markovRule_val_one` 的**实质计算**。 -/
theorem markovRule_identifiable {p q : ENNReal} (h : markovRule p = markovRule q) : p = q := by
  have h2 : markovRule p PUnit.unit 0 = markovRule q PUnit.unit 0 := by rw [h]
  unfold markovRule at h2
  have heq := Set.singleton_injective h2
  rw [← markovRule_val_one p, ← markovRule_val_one q, heq]

/-! ===========================================================================
    §4  ⭐ 两个实例共享同一个 `compose = ⊓` 骨架
    =========================================================================== -/

/-- ⭐ **实例 A 的 `compose` 就是格的 `⊓`**（`compose_eq_inf` 在 `ℝ` 输出空间上的实例）。

注意：这是**同一条** `compose_eq_inf`（泛型格定理）在 `Y = ℝ` 上的取值，
本模块的实质贡献是「该泛型定理在**实数回归领域**确实有可用实例」。 -/
theorem linRule_compose_eq_inf (a b : ℝ) :
    compose (linRule a) (linRule b) = linRule a ⊓ linRule b :=
  compose_eq_inf _ _

/-- ⭐ **实例 B 的 `compose` 就是格的 `⊓`**（`compose_eq_inf` 在 `Fin 2` 输出空间上的实例）。

它与 `linRule_compose_eq_inf` 是**同一条** `compose_eq_inf`，
只是输出空间由 `ℝ` 换成 `Fin 2` —— **这就是「通用」的领域层实证**：
两个数学上完全不同类的实例，共享同一格骨架。 -/
theorem markovRule_compose_eq_inf (p q : ENNReal) :
    compose (markovRule p) (markovRule q) = markovRule p ⊓ markovRule q :=
  compose_eq_inf _ _

/-- ⭐⭐ **共享双序**：两个实例的格序都等于「逐点包含」。

实例 A：`R₁ ≤ R₂ ⟺ ∀ c x, R₁ c x ⊆ R₂ c x`；
实例 B：**同一命题形状**（只是 `x : Fin 2`）。
这把「共享骨架」从 `compose` 延伸到**序结构**（`Iff.rfl`，即定义性一致）。 -/
theorem linRule_le_iff (R₁ R₂ : LawRule C₀ Xℝ Xℝ) :
    R₁ ≤ R₂ ↔ ∀ c x, R₁ c x ⊆ R₂ c x := Iff.rfl

/-- 实例 B 的序结构（与实例 A **同一条** `Iff.rfl`）。 -/
theorem markovRule_le_iff (R₁ R₂ : LawRule C₀ XF2 XF2) :
    R₁ ≤ R₂ ↔ ∀ c x, R₁ c x ⊆ R₂ c x := Iff.rfl

/-- ⭐⭐⭐ **共享单位元**：同一个格 `⊤` 在两个实例上都是 `compose` 的单位元
（`⊤` = 无约束规则），由**同一条** `compose_top` 得到。 -/
theorem shared_compose_top :
    (∀ (a : ℝ), compose (linRule a) (⊤ : LawRule C₀ Xℝ Xℝ) = linRule a) ∧
    (∀ (p : ENNReal), compose (markovRule p) (⊤ : LawRule C₀ XF2 XF2) = markovRule p) :=
  ⟨fun _ => compose_top _, fun _ => compose_top _⟩

/-! ===========================================================================
    §5  ⭐⭐ 非平凡内容：组合是**真约束**（两个领域各自可检验）
    =========================================================================== -/

/-- ⭐⭐ **实例 A 的组合非空 ⟺ 斜率相等**。

这是本模块对实例 A 的**实质语义定理**：两条线性回归规则 `linRule a`
与 `linRule b` 的「组合」（= 允许集的交）在所有点都非空，**当且仅当** `a = b`。

* `←`：`a = b` 时两者是同一规则，交为单点集（非空）。
* `→`：若各点交非空，则在 `x = 1` 处取交中元素 `μ`，
  得 `μ = δ_{a·1} = δ_{b·1}`，再用 `δ` 单射性得 `a·1 = b·1`，故 `a = b`。

**这不是同义反复**：前件是「∀ c x，允许集交非空」，结论是参数相等；
中间经过 `δ` 单射性，非平凡。 -/
theorem linRule_compose_nonempty_iff (a b : ℝ) :
    (∀ c x, (compose (linRule a) (linRule b) c x).Nonempty) ↔ a = b := by
  constructor
  · intro hne
    -- 在 x = 1 处取交中元素 μ，得 δ_{a·1} = δ_{b·1}
    have h1 : (Measure.dirac (a * 1) : Measure ℝ) = Measure.dirac (b * 1) := by
      have hmem := hne PUnit.unit 1
      unfold compose linRule at hmem
      obtain ⟨μ, hμ1, hμ2⟩ := hmem
      simp only [Set.mem_singleton_iff] at hμ1 hμ2
      rw [← hμ1, ← hμ2]
    by_contra h
    have hab : a * 1 ≠ b := by simpa using h
    have h' := congrArg (fun μ : Measure ℝ => μ {a * 1}) h1
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton (a * 1))] at h'
    have hb : (b * 1) ∉ ({a * 1} : Set ℝ) := by
      simp only [Set.mem_singleton_iff]
      intro hh; exact hab (by simpa using hh.symm)
    rw [Measure.dirac_apply, Set.indicator_of_notMem hb] at h'
    exact one_ne_zero h'
  · intro hab c x
    subst hab
    unfold compose linRule
    exact ⟨Measure.dirac (a * x), rfl, rfl⟩

/-- ⭐⭐ **实例 B 的组合非空 ⟺ 参数相等**（与实例 A 同形，但用总质量计算）。

两条马尔可夫链规则 `markovRule p`、`markovRule q` 的组合在各点非空
**当且仅当** `p = q`；其证明用 `markovRule_val_one`（对 `{1}` 取质量）。
这把实例 A 的语义形状**逐字搬到**一个数学上不同的领域，
是「骨架通用」的又一可检验证据。 -/
theorem markovRule_compose_nonempty_iff (p q : ENNReal) :
    (∀ c x, (compose (markovRule p) (markovRule q) c x).Nonempty) ↔ p = q := by
  constructor
  · intro hne
    have hmem := hne PUnit.unit 0
    unfold compose markovRule at hmem
    obtain ⟨μ, hμ1, hμ2⟩ := hmem
    simp only at hμ1 hμ2
    have heq : (p • (Measure.dirac (1 : Fin 2)) + (1 - p) • Measure.dirac (0 : Fin 2))
             = (q • (Measure.dirac (1 : Fin 2)) + (1 - q) • Measure.dirac (0 : Fin 2)) := by
      rw [← hμ1, ← hμ2]
    rw [← markovRule_val_one p, ← markovRule_val_one q, heq]
  · intro hpq c x
    subst hpq
    unfold compose markovRule
    exact ⟨p • (Measure.dirac (1 : Fin 2)) + (1 - p) • Measure.dirac (0 : Fin 2), rfl, rfl⟩

end LawRuleTwoDomains

end Fate
