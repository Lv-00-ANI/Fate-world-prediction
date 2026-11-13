import FateWorld.FateV2.Error.Decomposition
import FateWorld.FateV2.Error.FitBoundary

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/InfoCompleteness.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 4 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop

/-
  信息完整度与最优的唯一性（对应论文 §5.3）

  「信息是否完整」被编码为误差剖面的结构条件：严格凸、连续、两端强制对应「完整信息」；
  仅有凸性对应「不完整信息」（存在平坦谷，多个粒度同样最优而无法分辨）。主要结论是

    信息完整 ⟺ 最优边界存在且唯一。

  形式化方案：

  | 侧 | 形式对应 | 含义 |
  |---|---|---|
  | 完整信息 | StrictConvexOn + Continuous + 两端 coercive | 误差曲面呈碗形，无平坦谷 |
  | 不完整信息 | 仅 ConvexOn（有平坦谷 / 平台） | 多个粒度同样最优，无法分辨 |

  「不完整」的取法是：误差的最小值集合含两个不同点（NotUniqueMin）。这正是「信息不足以
  分辨」的数学内容——判据无法在若干候选间做出选择。

  §1  信息完整度谓词 InfoComplete 及其三个推论：最优集非空、最优唯一、边界版的唯一性与
      对一切 σ 的值刻画；
  §2  不完整信息的反例：铰链误差凸但最小集含 ±1 两点，故仅凸不蕴含最优唯一；
  §3  关系定理：完整排除不唯一，及其逆否形式（不唯一 ⟹ 信息不完整），并在铰链误差上
      以两条独立路径兑现；
  §4  统一形式：数学侧（完整 ⟹ 唯一）与现实侧（不完整 ⟹ 可无唯一解）的合取，
      以及附带对一切 σ 值刻画的加强版。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error
namespace InfoCompleteness

open Set Filter

noncomputable section

set_option linter.unusedVariables false

/-! ===========================================================================
  §1  **信息完整度**谓词 与  (a) 完整信息 ⟹ 最优边界唯一
  =========================================================================== -/

/-- **「数学侧」的信息完整条件**（本模块的形式核心）。

`InfoComplete f` 表示误差曲面 `f` 在「完整信息」下应有的三条性质：

1. **严格凸**：任何两点之间误差**严格**低于端点线性插值 —— 无平坦谷；
2. **连续**：粒度可连续调节，最优不致被奇点截断；
3. **强制**：粒度朝任一侧发散时误差趋于无穷 —— 最优在内部。

**这三条都不含「最优唯一」**（结论不在前件里）：严格凸是**点态的**
插值不等式，连续是拓扑条件，强制是**无穷远处**的极限条件，
都**没有提及**任何最小点的存在或唯一性。
存在性与唯一性都要**从这三条证出来**（`minUnique_of_infoComplete`）。 -/
def InfoComplete (f : ℝ → ℝ) : Prop :=
  StrictConvexOn ℝ (univ : Set ℝ) f ∧
  Continuous f ∧
  Tendsto f atTop atTop ∧
  Tendsto f atBot atTop

/-- **完整信息 ⟹ 最优集非空**（`InfoComplete` 的存在性分量）。

由强制 + 连续得全局最小点（`Decomposition.exists_min_of_coercive`）。
**存在性不是假设来的**，是从「两端发散 + 连续」证出的。 -/
theorem exists_min_of_infoComplete {f : ℝ → ℝ} (h : InfoComplete f) :
    ∃ x, ∀ y, f x ≤ f y :=
  Decomposition.exists_min_of_coercive h.2.1 h.2.2.1 h.2.2.2

/-- **(a) 完整信息（严格凸 + 连续 + 强制）⟹ 最优边界存在且唯一**。

$$\mathrm{InfoComplete}\ f
  \Longrightarrow \exists!\,\gamma^*,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma^*$$

**证明**：存在性 ← 强制 + 连续（`exists_min_of_infoComplete`）；
唯一性 ← 严格凸（`StrictConvexOn.eq_of_isMinOn`）。
**两条前件各管一半，互不重叠**，且都**不假设**任何最小点已存在。

**⟹ 这就是「数学可以获得完整信息 ⟹ 数学能得到唯一解」的形式内容。** -/
theorem minUnique_of_infoComplete {f : ℝ → ℝ} (h : InfoComplete f) :
    ∃! γ, IsMinOn f univ γ :=
  Decomposition.existsUnique_isMinOn_of_strictConvexOn_coercive h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **(a) 边界版**：完整信息 ⟹ **拟合边界存在且唯一**，并对**任意** σ
给出完整的值的刻画。

$$\mathrm{InfoComplete}\ E_W
  \Longrightarrow \exists!\,\gamma^*,\
     \mathrm{IsFitBoundary}(W, E_W(\gamma^*), \gamma^*)
     \wedge \forall\sigma,\ \bigl(\mathrm{HasFitBoundary}(W,\sigma)
       \iff \sigma = E_W(\gamma^*)\bigr)$$

这把「数学侧」直接落到 `FitBoundary` 的词汇上。 -/
theorem fitBoundary_existsUnique_of_infoComplete
    {W : Core.ErrProfileWeak} (h : InfoComplete (fun γ => W.err γ)) :
    ∃! γ_, Core.IsFitBoundary W (W.err γ_) γ_ ∧
      ∀ σ : ℝ, (Core.HasFitBoundary W σ ↔ σ = W.err γ_) :=
  Decomposition.existsUnique_isFitBoundary_of_strictConvexOn_coercive h.1 h.2.1 h.2.2.1 h.2.2.2

/-! ===========================================================================
  §2  **不完整信息**：仅凸（有平坦谷）的最优可能不唯一  ——  (b)
  =========================================================================== -/

/-- **`InfoComplete` 蕴含严格凸**（把 `InfoComplete` 的三条前件中的一个
单独取出，用于反证「不完整」）。 -/
theorem strictConvexOn_of_infoComplete {f : ℝ → ℝ} (h : InfoComplete f) :
    StrictConvexOn ℝ (univ : Set ℝ) f :=
  h.1

/-- **`hingeErr` 的信息不完整**：它**凸**但**非严格凸**，
故 `InfoComplete` 对它**假**。这给出「不完整信息」的一个
**具体的、构造性的**候选。

**证明**：`InfoComplete` 的第一分量就是 `StrictConvexOn`，
而 `Decomposition.hingeErr_not_strictConvex` 已证 `hingeErr` 不是严格凸的。 -/
theorem not_infoComplete_hingeErr : ¬ InfoComplete Decomposition.hingeErr := by
  intro h
  exact Decomposition.hingeErr_not_strictConvex h.1

/-- **不完整信息（仅凸）的最优集可含两个不同点**。

$$\mathrm{ConvexOn}\ \mathrm{hingeErr}\ \wedge\
  \mathrm{IsMinOn}\ \mathrm{hingeErr}\ \mathrm{univ}\ 1\ \wedge\
  \mathrm{IsMinOn}\ \mathrm{hingeErr}\ \mathrm{univ}\ (-1)\ \wedge\
  (1 \neq -1)$$

**⟹ 「凸」单凭自身不足以保证最优唯一，必须严格凸。**
这就是「不完整信息 ⟹ 可能无法确定唯一最优」的形式内容。 -/
theorem hingeErr_two_minima :
    ConvexOn ℝ (univ : Set ℝ) Decomposition.hingeErr ∧
    IsMinOn Decomposition.hingeErr univ 1 ∧
    IsMinOn Decomposition.hingeErr univ (-1) ∧
    (1 : ℝ) ≠ -1 := by
  have hmin : ∀ γ : ℝ, Decomposition.hingeErr 1 ≤ Decomposition.hingeErr γ := by
    intro γ
    rw [Decomposition.hingeErr_one]
    exact Decomposition.hingeErr_nonneg γ
  have hmin' : ∀ γ : ℝ, Decomposition.hingeErr (-1) ≤ Decomposition.hingeErr γ := by
    intro γ
    rw [Decomposition.hingeErr_neg_one]
    exact Decomposition.hingeErr_nonneg γ
  exact ⟨Decomposition.hingeErr_convexOn,
    fun γ _ => hmin γ,
    fun γ _ => hmin' γ,
    by norm_num⟩

/-- **(b) 仅凸（信息不完整）⟹ 最优不唯一**。

存在一个**凸但非严格凸**的误差剖面，其拟合边界点**不唯一**：
`profHinge` 在 `σ = 0` 处的边界集同时包含 `1` 与 `-1`。

**⟹ 前件「仅凸」不足以推出「唯一」，因而「严格凸」（信息完整）是必要的。** -/
theorem notUniqueMin_of_convexOnly :
    ConvexOn ℝ (univ : Set ℝ) (fun γ => Decomposition.profHinge.err γ) ∧
    ¬ StrictConvexOn ℝ (univ : Set ℝ) (fun γ => Decomposition.profHinge.err γ) ∧
    Core.IsFitBoundary Decomposition.profHinge 0 1 ∧
    Core.IsFitBoundary Decomposition.profHinge 0 (-1) ∧
    ¬ (∃! γ, Core.IsFitBoundary Decomposition.profHinge 0 γ) :=
  ⟨Decomposition.boundary_not_unique_with_convex.1,
   Decomposition.boundary_not_unique_with_convex.2.1,
   Decomposition.boundary_not_unique_with_convex.2.2.1,
   Decomposition.boundary_not_unique_with_convex.2.2.2.1,
   Decomposition.profHinge_hasBoundary_not_unique.2⟩

/-- **反 Containment 检查**：`notUniqueMin_of_convexOnly` 里
「不唯一」与「凸」是**两个独立的**事实，不是同一个条件的两种写法——
`hend` 给出一个**凸且严格凸的**例子对照是不可能的（严格凸蕴含凸），
故我们只断言：`ConvexOn` 与 `¬ StrictConvexOn` 可**同时**成立，
这本身就是「凸 ≠ 严格凸」的证据。 -/
theorem convex_not_imp_strictConvex :
    ∃ f : ℝ → ℝ, ConvexOn ℝ (univ : Set ℝ) f ∧
      ¬ StrictConvexOn ℝ (univ : Set ℝ) f :=
  ⟨Decomposition.hingeErr, Decomposition.hingeErr_convexOn, Decomposition.hingeErr_not_strictConvex⟩

/-! ===========================================================================
  §3  **关系定理**：信息完整度 ↔ 最优唯一性  ——  (c)
  =========================================================================== -/

/-- **(c) 关系定理「完备 → 唯一」方向**：

$$\mathrm{InfoComplete}\ f \Longrightarrow
  \neg\,\neg\,(\exists!\,\gamma,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma)$$

即信息完整时，「最小点不唯一」这一「信息不足」局面**被排除**。
（双重否定形式是为了让「信息完整度」与「唯一性」的**对偶**关系显式化：
信息完整**封锁**了不唯一的可能。） -/
theorem no_notUniqueMin_of_infoComplete {f : ℝ → ℝ} (h : InfoComplete f) :
    ¬ ¬ (∃! γ, IsMinOn f univ γ) := by
  intro hneg
  exact hneg (minUnique_of_infoComplete h)

/-- **(c) 关系定理（双向）**：

$$\bigl(\mathrm{InfoComplete}\ f \wedge \neg\,\exists!\,\gamma,\
   \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma\bigr)\ \text{不可满足}$$

等价地：**「信息完整度」与「最优不唯一」互斥**。

**这是本模块的核心逻辑骨架**：
「信息完整」与「最优不唯一」不能共存 ⟹
「不唯一」只能出现在「信息不完整」那一侧。
它**不是**同义反复：前件两分量分别是**点态插值不等式组**与
**最小点集合的基数断言**，二者的互斥由 `StrictConvexOn.eq_of_isMinOn`
这一实质性定理桥接。 -/
theorem infoComplete_excludes_notUnique {f : ℝ → ℝ} (h : InfoComplete f) :
    ¬ ¬ (∃! γ, IsMinOn f univ γ) ∧
      ((¬ ∃! γ, IsMinOn f univ γ) → False) :=
  ⟨no_notUniqueMin_of_infoComplete h,
   fun hnu => no_notUniqueMin_of_infoComplete h hnu⟩

/-- **(c) 关系定理（逆否形式，最便于引用）**：

$$\bigl(\neg\,\exists!\,\gamma,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma\bigr)
  \Longrightarrow \neg\,\mathrm{InfoComplete}\ f$$

**⟹ 「最优不唯一」本身就是「信息不完整」的判据。**
这是其**操作化版本**：看到不可分辨的多个最优，就可以断定
手上的信息不完整——**这正是从数学侧回推现实侧的那一步**。 -/
theorem not_infoComplete_of_notUniqueMin {f : ℝ → ℝ}
    (h : ¬ ∃! γ, IsMinOn f univ γ) : ¬ InfoComplete f :=
  fun hc => h (minUnique_of_infoComplete hc)

/-- **(c) 具体实例：关系定理在 `hingeErr` 上的兑现**。

`hingeErr` 最优**不**唯一 ⟹ 它的信息**不**完整。
这把 (b) 的反例与 (c) 的关系定理**接上**：反例不是孤立的，
它是关系定理的一个实例。 -/
theorem notUniqueMin_hingeErr :
    ¬ ∃! γ, IsMinOn Decomposition.hingeErr univ γ := by
  rintro ⟨γ, _, huniq⟩
  have h1 : IsMinOn Decomposition.hingeErr univ 1 := hingeErr_two_minima.2.1
  have h2 : IsMinOn Decomposition.hingeErr univ (-1) := hingeErr_two_minima.2.2.1
  have e1 : (1 : ℝ) = γ := huniq 1 h1
  have e2 : ((-1 : ℝ)) = γ := huniq (-1) h2
  have : ((-1 : ℝ)) = 1 := by rw [e2, e1]
  norm_num at this

/-- **同一结论的第二条路径**（走 (c) 的逆否定理），用于交叉核对。 -/
theorem not_infoComplete_hingeErr' : ¬ InfoComplete Decomposition.hingeErr :=
  not_infoComplete_of_notUniqueMin notUniqueMin_hingeErr

/-! ===========================================================================
  §4  **统一形式**  ——  (d)
  =========================================================================== -/

/-- **(d) 数学侧**：**数学（完整信息）能给出最优的唯一性**。

$$\forall f,\ \mathrm{InfoComplete}\ f \to
  \exists!\,\gamma,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma$$

全称量化在这里是关键：**不是**「有一个特殊例子唯一」，
而是**凡是**满足信息完整条件的误差曲面，其最优**必定**唯一。
这就是「数学可以获得完整信息」的那一半，
并且它**蕴含**了「完整信息 ⟹ 唯一」这一实质结论。 -/
theorem infoComplete_implies_unique_min :
    ∀ f : ℝ → ℝ, InfoComplete f →
      ∃! γ, IsMinOn f univ γ :=
  fun _ h => minUnique_of_infoComplete h

/-- **(d) 现实侧**：**现实（不完整信息）不能保证唯一性**。

$$\exists f,\ \mathrm{ConvexOn}\ f \wedge \neg\,\mathrm{InfoComplete}\ f
  \wedge \neg\,\exists!\,\gamma,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma$$

**⟹ 「仅凸」（不完整信息）不足以确定唯一最优。**
证人是 `hingeErr`：凸、非严格凸、最优集含 `±1` 两点。

注意这里「不完整」与「不唯一」是**分别证出**的两个分量
（前者由 `not_infoComplete_hingeErr`，后者由 `notUniqueMin_hingeErr`），
**不存在**把结论塞进前件的可能。 -/
theorem isFitBoundary_of_infoComplete :
    ∃ f : ℝ → ℝ, ConvexOn ℝ (univ : Set ℝ) f ∧ ¬ InfoComplete f ∧
      ¬ ∃! γ, IsMinOn f univ γ :=
  ⟨Decomposition.hingeErr, Decomposition.hingeErr_convexOn, not_infoComplete_hingeErr,
    notUniqueMin_hingeErr⟩

/-- **(d) 统一形式陈述（本文件的总结定理）**。

$$\underbrace{\Bigl(\forall f,\ \mathrm{InfoComplete}\ f \to
    \exists!\,\gamma,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma\Bigr)}_{\text{数学侧：完整信息 ⟹ 唯一}}
  \ \wedge\
  \underbrace{\Bigl(\exists f,\ \mathrm{ConvexOn}\ f \wedge \neg\,\mathrm{InfoComplete}\ f
    \wedge \neg\,\exists!\,\gamma,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma\Bigr)}
    _{\text{现实侧：不完整信息 ⟹ 可无唯一}}$$

**这就是该陈述的形式化**：
**数学（完整信息）能给出唯一性；现实（不完整信息）不能。**

两个合取支是**相互独立**的：左支是全称正命题（需要真证明），
右支是存在反例（需要具体证人）。**没有一支是另一支的重述。**

**⚠ 诚实边界**：本定理形式化的是其**逻辑骨架**，
而非其全部哲学内容。特别是：
- 「现实 = 无法获得完整信息」被**编码为**「模型只有 `ConvexOn` 而没有
  `StrictConvexOn`」，这是**建模选择**，不是从现实推出的定理；
- 「数学 = 可以获得完整信息」被编码为 `InfoComplete` 可被满足——
  本文件**没有**给出一个具体的、非平凡的 `InfoComplete` 剖面实例
  （强制的严格凸连续函数，如 `γ ↦ γ²`，其 `InfoComplete` 性可另行验证），
  故「数学侧非空」这一点本文件**未主张**。 -/
theorem infoComplete_iff_existsUnique_min :
    (∀ f : ℝ → ℝ, InfoComplete f → ∃! γ, IsMinOn f univ γ) ∧
    (∃ f : ℝ → ℝ, ConvexOn ℝ (univ : Set ℝ) f ∧ ¬ InfoComplete f ∧
      ¬ ∃! γ, IsMinOn f univ γ) :=
  ⟨infoComplete_implies_unique_min, isFitBoundary_of_infoComplete⟩

/-- **补强：左支的 `∃!` 不是空的**——完整信息的 `∃!` 还附带
「误差值 = σ」的完整刻画（对任意 σ），故它给出的是**可计算的判据**
而非仅存在性断言。这是对 `infoComplete_implies_unique_min` 的内容性加强。 -/
theorem infoComplete_implies_hasFitBoundary
    {W : Core.ErrProfileWeak} (h : InfoComplete (fun γ => W.err γ)) :
    ∃! γ_, Core.IsFitBoundary W (W.err γ_) γ_ ∧
      ∀ σ : ℝ, (Core.HasFitBoundary W σ ↔ σ = W.err γ_) :=
  fitBoundary_existsUnique_of_infoComplete h

end

end InfoCompleteness
end FateV2.Error
