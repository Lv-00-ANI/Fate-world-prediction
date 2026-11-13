import FateWorld.FateV2.Predict.CausalPath

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/CausalDescendant.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 3 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict

/-! ===========================================================================
  §63  **d-分离的**后代层**** —— 图论层的**最后一块**

  ## 背景

  | 轮次 | 已做 |
  |---|---|
  | **60** | 图论层（路径、阻断）|
  | **61** | 方向层（三元组四类）|
  | **62** | 路径层（逐节点开口性）|

  **⚠ 第 62 轮的边界登记**：
  > **严格的 d-分离还包括「collider 的**后代**在 `Z` 中也开口」；
  > **本节暂只做 collider 本身**

  **⟹ 本轮补上「后代」，使 d-分离的定义与**标准定义**完全一致。**

  ## 标准定义（Pearl）

  $$\text{路径开口} := \text{每个中间点 } v \text{ 满足}$$
  $$\bigl(v \text{ 是非 collider} \wedge v \notin Z\bigr)
    \vee \bigl(v \text{ 是 collider} \wedge \mathrm{desc}(v) \cap Z \neq \varnothing\bigr)$$

  **⟹ 第 62 轮的 `openAt` 只有前半；本轮加上后半。**

  ## 本节的产出

  | # | 内容 |
  |---|---|
  | **1** | **`DStep.fwdOnly`**：判断一步是否前向 |
  | **2** | **`Reachable`**：有向可达（后代关系）|
  | **3** | **`openAt'`**：**完整的开口性**（含后代）|
  | **4** | **`dSep_complete`**：**完整的 d-分离** |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

namespace CausalDescendant

universe u

variable {V : Type u}

/-! ### §63.1 有向可达（后代关系） -/

/-- **有向可达**：存在一条**全前向**的路径。

$$\mathrm{Reach}\,G\,a\,b :=
  \exists\, \text{全 } \mathrm{fwd} \text{ 的路径 } a \to \cdots \to b$$

**⟹ 即**：**「$b$ 是 $a$ 的后代」** ——
**这是 d-分离标准定义所需的唯一新概念。** -/
inductive Reach (G : CausalDirection.CausalGraph V) : V → V → Prop where
  /-- **自反**：`a` 可达自己。 -/
  | refl (a : V) : Reach G a a
  /-- **前进一步**：沿 `a → b` 的边，再走 `b` 到 `c`。 -/
  | step {a b c : V} (h : G.Adj a b) (w : Reach G b c) : Reach G a c

/-- **可达的自反性**（显式形式）。 -/
theorem reach_refl (G : CausalDirection.CausalGraph V) (a : V) : Reach G a a :=
  Reach.refl a

/-- **可达的传递性**（**结构定理**）。 -/
theorem reach_trans (G : CausalDirection.CausalGraph V) {a b c : V}
    (h₁ : Reach G a b) (h₂ : Reach G b c) : Reach G a c := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact Reach.step h (ih h₂)

/-- **一步即可达**（从边推可达）。 -/
theorem reach_of_adj (G : CausalDirection.CausalGraph V) {a b : V}
    (h : G.Adj a b) : Reach G a b :=
  Reach.step h (Reach.refl b)

/-! ### §63.2 完整的开口性（含后代） -/

/-- **完整的单个中间点开口性**（**标准定义**）。

$$\text{openAt}'(s_1, s_2, b, Z) :=
  \begin{cases}
    \exists z \in Z,\ \mathrm{Reach}\,G\,b\,z & \text{若 } b \text{ 是 collider}\\
    b \notin Z & \text{否则}
  \end{cases}$$

**⟹ 与第 62 轮 `openAt` 的差别**：
**collider 情形从「$b \in Z$」放宽为「$b$ **或其后代**在 $Z$ 中」。**

**⟹ 这是 Pearl 的标准定义。** -/
def openAt' (G : CausalDirection.CausalGraph V) {a b c : V}
    (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c) (Z : Set V) : Prop :=
  match s₁, s₂ with
  | .fwd _, .bwd _ => ∃ z ∈ Z, Reach G b z   -- collider：`b` 或其后代在 `Z` 中
  | _, _ => b ∉ Z                            -- 非 collider：`b` 不在 `Z` 中

/-- **两者的一致性**：**若 `b ∈ Z`，则第 62 轮的 `openAt` 蕴含新的 `openAt'`**。

**⟹ 即**：**本轮的定义是第 62 轮的**放宽**** ——
**旧定义成立的路径，在新定义下**仍开口**。** -/
theorem openAt_imp_openAt' (G : CausalDirection.CausalGraph V) {a b c : V}
    {s₁ : CausalPath.DStep G a b} {s₂ : CausalPath.DStep G b c} {Z : Set V}
    (h : CausalPath.openAt G s₁ s₂ Z) : openAt' G s₁ s₂ Z := by
  cases s₁ <;> cases s₂
  · -- fwd, fwd：非 collider，两边都是 `b ∉ Z`
    simpa [openAt', CausalPath.openAt] using h
  · -- fwd, bwd：collider；旧定义给 `b ∈ Z`，取 `z := b`
    have hb : b ∈ Z := by simpa [CausalPath.openAt] using h
    exact ⟨b, hb, Reach.refl b⟩
  · -- bwd, fwd：非 collider
    simpa [openAt', CausalPath.openAt] using h
  · -- bwd, bwd：非 collider
    simpa [openAt', CausalPath.openAt] using h

/-! ### §63.3 完整的 d-分离 -/

/-- **完整的路径开口性**（用 `openAt'`）。 -/
def DOpen' (G : CausalDirection.CausalGraph V) (Z : Set V) :
    {a b : V} → CausalPath.DWalk G a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons _ (.nil _) => True
  | _, _, .cons s₁ (.cons s₂ w) => openAt' G s₁ s₂ Z ∧ DOpen' G Z (.cons s₂ w)

/-- **完整的 d-连通**（标准定义）。 -/
def DConnected' (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) : Prop :=
  ∃ w : CausalPath.DWalk G a b, DOpen' G Z w

/-- **完整的 d-分离**（**标准定义 / Pearl**）。

$$a \perp\!\!\!\perp_{d} b \mid Z := \neg\,\mathrm{DConnected}'\,G\,Z\,a\,b$$

**⟹ 这是与 Pearl《Causality》§1.2.3 定义 1.2.3 一致的版本** ——
**区别仅在于「collider 的后代在 `Z` 中」这一放宽。** -/
def DSeparated' (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) : Prop :=
  ¬ DConnected' G Z a b

/-- **d-分离的不可自反性**（**完整版本**，与第 62 轮对应）。 -/
theorem not_dseparated_self' (G : CausalDirection.CausalGraph V) (Z : Set V) (a : V) :
    ¬ DSeparated' G Z a a :=
  fun h => h ⟨CausalPath.DWalk.nil a, trivial⟩

/-! ### §63.4 单调性的**反转**（后代层的代价） -/

/-! ⚠ **注意：加入后代后，单调性**不再显然****。

**第 60/62 轮的单调性**（$Z \subseteq Z' \implies$ 更易分离）
**依赖「`Z` 越大越易阻断」；
**但 collider 情形下「`Z` 越大，collider **越容易开口**」** ——
**即**方向相反**。**

**⟹ 即**：**d-分离关于 `Z` **不是单调的**** ——
**这是一个**有内容的观察**（且解释了为何 d-分离的数学不平凡）。

**⚠ 本节如实登记这一点，**不假装单调性成立**。**

**该断言**可由反例真正证伪**（见下方）——
**故本段不再需要以 `True` 占位。** -/

/-! #### 反例：d-分离关于 `Z` **不单调**（第 69 轮补证） -/

/-- **反例图**：`0 → 1 ← 2`，外加 `1 → 3`。

- 顶点 `1` 是路径 `0 → 1 ← 2` 上的 **collider**；
- 顶点 `3` 是 `1` 的**后代**。

**⟹ 这是验证「后代开口」所需的最小结构。** -/
def dsepCounterGraph : Fin 4 → Fin 4 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 3)

/-- 无环性见证：沿 `dsepCounterGraph` 的每一步都使此秩**严格增大**
（`0 ↦ 0`、`2 ↦ 0`、`1 ↦ 1`、`3 ↦ 2`）。 -/
def dsepCounterRank : Fin 4 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2
  | _ => 0

/-- **反例图是无环的**（由秩函数给出真证明）。 -/
theorem dsepCounterGraph_acyclic :
    ∀ v : Fin 4, ¬ Relation.TransGen dsepCounterGraph v v := by
  have hstep : ∀ {p q : Fin 4}, dsepCounterGraph p q → dsepCounterRank p < dsepCounterRank q := by
    intro p q hp
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; decide
    · subst h1; subst h2; decide
    · subst h1; subst h2; decide
  intro v h
  have hgen : ∀ {a b : Fin 4},
      Relation.TransGen dsepCounterGraph a b → dsepCounterRank a < dsepCounterRank b := by
    intro a b hab
    induction hab with
    | single h => exact hstep h
    | tail _ hbc ih => exact lt_trans ih (hstep hbc)
  exact absurd (hgen h) (lt_irrefl _)

/-- **反例图**（`CausalGraph` 实例）。 -/
def dsepCounterG : CausalDirection.CausalGraph (Fin 4) :=
  ⟨dsepCounterGraph, dsepCounterGraph_acyclic⟩

/-- **路径 `0 → 1 ← 2`**（collider 在 `1`）。 -/
def dsepCounterWalk : CausalPath.DWalk dsepCounterG 0 2 :=
  CausalPath.DWalk.cons
    (CausalPath.DStep.fwd (show dsepCounterGraph 0 1 from Or.inl ⟨rfl, rfl⟩))
    (CausalPath.DWalk.cons
      (CausalPath.DStep.bwd (show dsepCounterGraph 2 1 from Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (CausalPath.DWalk.nil 2))

/-- `1 → 3`：**`3` 是 collider `1` 的后代**。 -/
theorem dsepCounter_1_3 : dsepCounterGraph 1 3 := Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **`Z = ∅` 时该路径关闭**（collider 需要 `Z` 中有后代，而 `∅` 中没有）。 -/
theorem dsepCounter_closed : ¬ DOpen' dsepCounterG (∅ : Set (Fin 4)) dsepCounterWalk := by
  simp [DOpen', dsepCounterWalk, openAt']

/-- **`Z' = {3}` 时同一条路径打开**（`3` 是 collider 的后代且 `3 ∈ Z'`）。 -/
theorem dsepCounter_open : DOpen' dsepCounterG ({3} : Set (Fin 4)) dsepCounterWalk := by
  refine ⟨?_, trivial⟩
  exact ⟨3, rfl, Reach.step dsepCounter_1_3 (Reach.refl 3)⟩

/-- **`Z ⊆ Z'`**（`∅ ⊆ {3}`）。 -/
theorem dsepCounter_subset : (∅ : Set (Fin 4)) ⊆ ({3} : Set (Fin 4)) :=
  Set.empty_subset _

/-- **d-分离关于 `Z` **不单调****（**真反例，取代原先的 `True` 占位**）。

$$\exists\, G,\ Z \subseteq Z',\ a,\ b,\ w:\quad
  \neg\,\mathrm{DOpen}'\,G\,Z\,w \;\wedge\; \mathrm{DOpen}'\,G\,Z'\,w$$

**语义**：**同一条**连接 $a$ 与 $b$ 的路径**，
**在较小的 $Z$ 下被阻断，在较大的 $Z'$ 下反而**被打开**** ——
**故「$Z$ 越大越易分离」**是错的****；
**其机制正是 collider：$Z$ 增大时 collider **从阻断变为开口**。**

**⟹ 这解释了为何 d-分离的数学不平凡** ——
**它的「阻断」判据对 $Z$ **不是单调谓词****。** -/
theorem dsep_not_monotone :
    ∃ (G : CausalDirection.CausalGraph (Fin 4)) (Z Z' : Set (Fin 4)) (a b : Fin 4)
      (w : CausalPath.DWalk G a b),
      Z ⊆ Z' ∧ ¬ DOpen' G Z w ∧ DOpen' G Z' w :=
  ⟨dsepCounterG, ∅, {3}, 0, 2, dsepCounterWalk,
   dsepCounter_subset, dsepCounter_closed, dsepCounter_open⟩

/-- **推论（`DSeparated'` 形式）**：反例图在 `Z' = {3}` 下**不** d-分离 `0` 与 `2`
（那条打开的路径就是见证）。 -/
theorem dsepCounter_not_separated :
    ¬ DSeparated' dsepCounterG ({3} : Set (Fin 4)) 0 2 :=
  fun h => h ⟨dsepCounterWalk, dsepCounter_open⟩

/-! ### §63.5 **标准名别名**（**第 214 轮**）

**⚠ 背景**：`DSeparated'`（**带 `'` 后缀**）才是 **Pearl 的标准定义**，
而 `CausalPath.DSeparated`（**无后缀**）是**漏掉后代的简化版** ——
**这造成**命名误导**（正式名字给了不完整的版本）。**

**本节的别名**让**标准定义**有**明确的正式名字**。 -/

/-- **标准 d-分离**（**Pearl《Causality》§1.2.3 定义 1.2.3**）。 -/
def DSeparatedStd (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) : Prop :=
  DSeparated' G Z a b

/-- **标准 d-连通**。 -/
def DConnectedStd (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) : Prop :=
  DConnected' G Z a b

/-- **一致性**：`DSeparatedStd` 与 `DSeparated'` 定义相同。 -/
theorem dseparatedStd_iff_dseparated' (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) :
    DSeparatedStd G Z a b ↔ DSeparated' G Z a b := Iff.rfl

/-- **标准 d-分离的不可自反性**（用新名字重述）。 -/
theorem not_dseparatedStd_self (G : CausalDirection.CausalGraph V) (Z : Set V) (a : V) :
    ¬ DSeparatedStd G Z a a :=
  not_dseparated_self' G Z a

end CausalDescendant

end FateV2.Predict
