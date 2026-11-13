import FateWorld.Legacy.CausalPath
import FateWorld.Legacy.SCMSemantics
import FateWorld.Legacy.FinMarkov
open MeasureTheory

/-! ===========================================================================
  §P213-B1  ⭐⭐⭐ **Pearl 1.2.4 的最小特例**（链 $a \to b \to c$，$Z = \{b\}$）

  ## 目标（**纯概率层**，不接 `DSeparated`）

  在 `CausalGraph`（有向无环）上取**链** $a \to b \to c$，令 $Z = \{b\}$。
  设三变量联合律 $p(a,b,c)$ 满足**链式 Markov 分解**

  $$p(a,b,c) \;=\; p(a)\,p(b\mid a)\,p(c\mid b),$$

  则 $a \perp\!\!\!\perp c \mid b$，即**乘法形式**

  $$p(a,b,c)\cdot p(b) \;=\; p(a,b)\cdot p(b,c).$$

  ## 口径选择（**为什么用乘法形式**）

  | 形式 | 问题 |
  |---|---|
  | 商形式 $p(a,c\mid b)=p(a\mid b)p(c\mid b)$ | 需 $p(b)\neq 0$，且在 $\mathbb R$ 上要额外除法引理 |
  | **乘法形式**（本文件） | **处处有定义**，**无需非零前提**；$p(b)>0$ 时**等价于**商形式 |

  **⟹ 本文件主定理用乘法形式**（与项目 `FinMarkov.CondIndepFin` 同口径），
  **并额外给出**「$p(b) \ne 0$ 时的商形式」推论 `chainMarkov_condIndep_ratio`
  —— 即用户提示中的 $\frac{p(a,b,c)}{p(b)}=\frac{p(a,b)}{p(b)}\cdot\frac{p(b,c)}{p(b)}$ 版本，
  **并显式证明两者等价**。

  ## 本文件的产出

  | # | 内容 |
  |---|---|
  | 1 | `ChainMarkov`：链式 Markov 分解（$p(a,b,c)=\alpha(a)\beta(a,b)\gamma(b,c)$）|
  | 2 | `chainMarkov_margAB` / `chainMarkov_margBC`：两个二元边缘律的显式值 |
  | 3 | ⭐⭐⭐ `chainMarkov_condIndep`：**乘法形式的条件独立**（主定理，无前提）|
  | 4 | ⭐⭐⭐ `chainMarkov_condIndep_ratio`：$p(b)\ne 0$ 时的**商形式** |
  | 5 | `chainGraph` / `chainGraph_isChain` / `chainGraph_tripleType`：**图侧的最小实例**（$a\to b\to c$，DAG 已验证）|
  | 6 | `p213_chain`：**图 + 概率**合成的最终陈述（Pearl 1.2.4 最小特例）|

  ## ⚠ 非平凡性

  主定理**不是** `True`：结论是联合律上的一个**真实约束**。
  **反例**： `badP`（$p(0,0,0)=p(1,0,1)=1$，$b$ 固定为 0，
  $c=a$ 完全由 $a$ 决定）在 $(a,b,c)=(1,0,0)$ 处给出
  $0\cdot 2 \neq 1\cdot 1$ —— **结论失效**，
  故主定理的假设「$\gamma$ 只读 $b$」**不可去掉**。见文末 `counterexample`。

  **⚠ 无 `sorry` / `admit` / `axiom`**（依项目纪律）。
  =========================================================================== -/

namespace Fate

namespace P213B1

set_option autoImplicit false

open Finset

universe u

/-! ⚠ **实例作用域**：三个边缘律展开引理各自只用到**一部分** `Fintype` 实例
（例如 `chainMarkov_margAB` 只对 `c` 求和），故**不在文件级声明** `[Fintype _]`，
而在**每个定理处就地声明**，以免 `unusedSectionVars` 噪音。 -/
variable {A B C : Type u}

/-! ===========================================================================
  §P213-B1.1  ⭐⭐⭐ **链式 Markov 分解**
  =========================================================================== -/

/-- ⭐⭐⭐ **链式 Markov 分解**（$a \to b \to c$ 的因子化）。

$$p(a,b,c) \;=\; \alpha(a)\;\beta(a,b)\;\gamma(b,c)$$

**读法**：$\alpha = p(a)$，$\beta = p(b\mid a)$（未归一），
$\gamma = p(c\mid b)$（未归一）。
**关键结构点**：$\gamma$ **只依赖 $(b,c)$**，**不依赖 $a$**
—— 这正是「$c$ 的机制只读其父 $b$」的概率表述，
**也是条件独立能成立的唯一原因**。 -/
def ChainMarkov (p : A × B × C → ℝ) : Prop :=
  ∃ α : A → ℝ, ∃ β : A × B → ℝ, ∃ γ : B × C → ℝ,
    ∀ a b c, p (a, b, c) = α a * β (a, b) * γ (b, c)

/-! ### §P213-B1.2 边缘律的显式值 -/

/-- ⭐⭐ $(a,b)$ 的边缘律。 -/
noncomputable def margAB [Fintype C] (p : A × B × C → ℝ) (a : A) (b : B) : ℝ :=
  ∑ c, p (a, b, c)

/-- ⭐⭐ $(b,c)$ 的边缘律。 -/
noncomputable def margBC [Fintype A] (p : A × B × C → ℝ) (b : B) (c : C) : ℝ :=
  ∑ a, p (a, b, c)

/-- ⭐⭐ $b$ 的边缘律。 -/
noncomputable def margB [Fintype A] [Fintype C] (p : A × B × C → ℝ) (b : B) : ℝ :=
  ∑ a, ∑ c, p (a, b, c)

/-- ⭐⭐⭐ **在 Markov 分解下，$(a,b)$ 边缘律 = $\alpha(a)\beta(a,b)\cdot\Gamma(b)$**，
其中 $\Gamma(b) := \sum_c \gamma(b,c)$（$\gamma$ **与 $a$ 无关**是关键）。 -/
theorem chainMarkov_margAB [Fintype C] {p : A × B × C → ℝ}
    {α : A → ℝ} {β : A × B → ℝ} {γ : B × C → ℝ}
    (hP : ∀ a b c, p (a, b, c) = α a * β (a, b) * γ (b, c))
    (a : A) (b : B) :
    margAB p a b = α a * β (a, b) * (∑ c, γ (b, c)) := by
  simp only [margAB]
  calc ∑ c, p (a, b, c)
      = ∑ c, α a * β (a, b) * γ (b, c) :=
        Finset.sum_congr rfl fun c _ => hP a b c
    _ = α a * β (a, b) * (∑ c, γ (b, c)) := by
        rw [Finset.mul_sum]

/-- ⭐⭐⭐ **在 Markov 分解下，$(b,c)$ 边缘律 = $\gamma(b,c)\cdot\AlphaBeta(b)$**，
其中 $\AlphaBeta(b) := \sum_a \alpha(a)\beta(a,b)$。 -/
theorem chainMarkov_margBC [Fintype A] {p : A × B × C → ℝ}
    {α : A → ℝ} {β : A × B → ℝ} {γ : B × C → ℝ}
    (hP : ∀ a b c, p (a, b, c) = α a * β (a, b) * γ (b, c))
    (b : B) (c : C) :
    margBC p b c = (∑ a, α a * β (a, b)) * γ (b, c) := by
  simp only [margBC]
  calc ∑ a, p (a, b, c)
      = ∑ a, α a * β (a, b) * γ (b, c) :=
        Finset.sum_congr rfl fun a _ => hP a b c
    _ = (∑ a, α a * β (a, b)) * γ (b, c) := by
        rw [Finset.sum_mul]

/-- ⭐⭐ $b$ 的边缘律的显式值：

$$\text{margB}(b) = \Bigl(\sum_a \alpha(a)\beta(a,b)\Bigr)\Bigl(\sum_c \gamma(b,c)\Bigr).$$ -/
theorem chainMarkov_margB [Fintype A] [Fintype C] {p : A × B × C → ℝ}
    {α : A → ℝ} {β : A × B → ℝ} {γ : B × C → ℝ}
    (hP : ∀ a b c, p (a, b, c) = α a * β (a, b) * γ (b, c))
    (b : B) :
    margB p b = (∑ a, α a * β (a, b)) * (∑ c, γ (b, c)) := by
  simp only [margB]
  calc ∑ a, ∑ c, p (a, b, c)
      = ∑ a, ∑ c, α a * β (a, b) * γ (b, c) := by
        refine Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun c _ => hP a b c
    _ = ∑ a, α a * β (a, b) * (∑ c, γ (b, c)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = (∑ a, α a * β (a, b)) * (∑ c, γ (b, c)) := by
        rw [Finset.sum_mul]

/-! ===========================================================================
  §P213-B1.3  ⭐⭐⭐ **主定理：链式 Markov ⟹ 条件独立**（乘法形式）
  =========================================================================== -/

/-- ⭐⭐⭐ **Pearl 1.2.4 的最小特例（纯概率层）**。

$$p(a,b,c) = p(a)p(b\mid a)p(c\mid b) \;\Longrightarrow\;
  p(a,b,c)\cdot p(b) = p(a,b)\cdot p(b,c)$$

**即** $a \perp\!\!\!\perp c \mid b$（乘法形式，**无需任何非零前提**）。

**证明**（纯代数）：设 $p = \alpha\beta\gamma$，记
$\Gamma(b)=\sum_c\gamma(b,c)$、$S(b)=\sum_a\alpha(a)\beta(a,b)$。则

$$\text{lhs} = \alpha(a)\beta(a,b)\gamma(b,c)\cdot S(b)\Gamma(b),
\qquad
\text{rhs} = \alpha(a)\beta(a,b)\Gamma(b)\cdot S(b)\gamma(b,c),$$

两边都等于 $\alpha(a)\beta(a,b)\gamma(b,c)S(b)\Gamma(b)$。 ∎

**⚠ 关键点**：$\gamma$ **不依赖 $a$** —— 故 $\text{margBC}$ 中 $\gamma(b,c)$ **可以提出求和号**。
若 $\gamma$ 依赖 $a$，则 $\text{margBC}(b,c)$ 会变成 $\sum_a \alpha\beta\gamma(a,\cdot)$，
本证明**立刻失效**（见文末 `counterexample`）。 -/
theorem chainMarkov_condIndep [Fintype A] [Fintype C] {p : A × B × C → ℝ}
    (h : ChainMarkov p) :
    ∀ a b c, p (a, b, c) * margB p b = margAB p a b * margBC p b c := by
  obtain ⟨α, β, γ, hP⟩ := h
  intro a b c
  have hAB : margAB p a b = α a * β (a, b) * (∑ c, γ (b, c)) :=
    chainMarkov_margAB hP a b
  have hBC : margBC p b c = (∑ a, α a * β (a, b)) * γ (b, c) :=
    chainMarkov_margBC hP b c
  have hB : margB p b = (∑ a, α a * β (a, b)) * (∑ c, γ (b, c)) :=
    chainMarkov_margB hP b
  rw [hAB, hBC, hB, hP a b c]
  ring

/-! ### §P213-B1.4  ⭐⭐ 商形式（$p(b)\ne 0$）

**用户提示中的形式**：$\dfrac{p(a,b,c)}{p(b)}
= \dfrac{p(a,b)}{p(b)}\cdot\dfrac{p(b,c)}{p(b)}$。
**它确实成立，但需要 $p(b)\ne 0$**（否则两边都除以 0）。
**⟹ 本小节把它从乘法形式**推出**，并给出等价性。 -/

theorem chainMarkov_condIndep_ratio [Fintype A] [Fintype C] {p : A × B × C → ℝ}
    (h : ChainMarkov p)
    {b : B} (hb : margB p b ≠ 0) (a : A) (c : C) :
    p (a, b, c) / margB p b
      = (margAB p a b / margB p b) * (margBC p b c / margB p b) := by
  have hmul := chainMarkov_condIndep h a b c
  field_simp
  linarith [hmul]

/-- ⭐⭐ **两种形式等价**（在 $p(b)\ne 0$ 处）：乘法形式 ⟺ 商形式。 -/
theorem condIndep_iff_ratio [Fintype A] [Fintype C] {p : A × B × C → ℝ} {b : B}
    (hb : margB p b ≠ 0)
    (a : A) (c : C) :
    (p (a, b, c) * margB p b = margAB p a b * margBC p b c)
      ↔ (p (a, b, c) / margB p b
          = (margAB p a b / margB p b) * (margBC p b c / margB p b)) := by
  constructor
  · intro h
    field_simp
    linarith [h]
  · intro h
    field_simp at h
    linarith [h]

/-! ===========================================================================
  §P213-B1.5  ⭐⭐ **图侧的最小实例**：$a \to b \to c$（DAG 已验证）
  =========================================================================== -/

/-- ⭐⭐ **三顶点链图**：顶点 `Fin 3`，边 $0 \to 1 \to 2$（即 $a\to b\to c$）。

**无环性**：边关系是 $\{(0,1),(1,2)\}$，传递闭包只含 $(0,1),(1,2),(0,2)$，
**均非自反** —— 故是合法 `CausalGraph`（DAG）。**这里显式验证，不假设。** -/
def chainGraph : CausalDirection.CausalGraph (Fin 3) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  acyclic := by
    intro v h
    -- 传递闭包中的每条边都把顶点「严格推高」，故不可能回到起点。
    have key : ∀ x y : Fin 3, Relation.TransGen
        (fun u v : Fin 3 => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single hstep =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; decide
          · subst h1; subst h2; decide
      | tail _ hstep ih =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; omega
          · subst h1; subst h2; omega
    exact absurd (key v v h) (lt_irrefl v)

/-- ⭐⭐ **`chainGraph` 确实是链**（按项目 `CausalDirection.IsChain` 的定义）。 -/
theorem chainGraph_isChain :
    CausalDirection.IsChain chainGraph (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) :=
  Or.inl ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- ⭐⭐ **`chainGraph` 的三元组类型是 `chain_fwd`**。 -/
theorem chainGraph_tripleType :
    CausalDirection.TripleType chainGraph (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) :=
  CausalDirection.TripleType.chain_fwd (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)

/-! ===========================================================================
  §P213-B1.6  ⭐⭐⭐ **最终陈述：Pearl 1.2.4 最小特例（图 + 概率合成）**
  =========================================================================== -/

/-- ⭐⭐⭐ **Pearl 1.2.4 的最小特例**。

对 `chainGraph`（$a\to b\to c$，已验证为 DAG）上的链，
**若**联合律 $p$ 满足链式 Markov 分解（$c$ 的机制只读 $b$），
**则** $a \perp\!\!\!\perp c \mid b$（乘法形式），**且**在 $p(b)\ne 0$ 处商形式也成立。

**⚠ 这是**非平凡**的**：结论是 $p$ 上的**真实约束**（见 `counterexample`），
**不是 `True`**。 -/
theorem p213_chain (p : Fin 3 × Fin 3 × Fin 3 → ℝ) (h : ChainMarkov p) :
    (∀ a b c, p (a, b, c) * margB p b = margAB p a b * margBC p b c) ∧
    (∀ a b c, margB p b ≠ 0 →
      p (a, b, c) / margB p b
        = (margAB p a b / margB p b) * (margBC p b c / margB p b)) :=
  ⟨chainMarkov_condIndep h,
   fun a _ c hb => chainMarkov_condIndep_ratio h hb a c⟩


/-! ### P213-B1.7 非平凡性证据（反例：c 的机制依赖 a 则结论失效） -/

/-- 一个不含链式 Markov 结构的联合律：c 的机制读 a。 -/
noncomputable def badP : Fin 2 × Fin 2 × Fin 2 → ℝ :=
  fun t => if t = ((0:Fin 2), (0:Fin 2), (0:Fin 2)) then 1
           else if t = ((1:Fin 2), (0:Fin 2), (1:Fin 2)) then 1 else 0

/-- 反例：badP 不满足乘法形式条件独立。 -/
theorem counterexample :
    ¬ (∀ (a b c : Fin 2), badP (a, b, c) * margB badP b
        = margAB badP a b * margBC badP b c) := by
  intro h
  have h0 := h 1 0 0
  simp only [badP, margB, margAB, margBC, Fin.sum_univ_two] at h0
  norm_num at h0

/-- badP 确实不是链式 Markov。 -/
theorem counterexample_not_chainMarkov : ¬ ChainMarkov badP := by
  intro h
  exact counterexample (chainMarkov_condIndep h)

end P213B1

end Fate