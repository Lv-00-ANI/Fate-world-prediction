import FateWorld.FateV2.Predict.ThreeViews
/-!
  # Predict · ParametricEquiv

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ParametricEquiv.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ThreeViews
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §28  ⭐⭐ **参数化的中间等价关系**（原 `_probe_q24` 的正式化）

  **来源**：探针 `probes/_probe_q24.lean`（**不在构建内**）。

  ## 问题

  **尝试构造一个显式的中间等价关系，并验证它使某类桥单值。**

  ## ⭐⭐ 答案：**查询子族参数化**

  取定参考桥 `bridge : Graph → Set SCM` 与**查询子族** `Q ⊆ Graph`：
  $$s_1 \sim_Q s_2 \iff \forall g \in Q,\ (s_1 \in \mathrm{bridge}\,g \leftrightarrow s_2 \in \mathrm{bridge}\,g)$$

  **直觉**：**只在 `Q` 上读桥**。`Q` 越大，读得越多，关系越细。

  ## ⭐ 它是**真正中间**的

  | `Q` | `∼_Q` | 位置 |
  |---|---|---|
  | **`∅`** | **万物等价** | **最粗端** |
  | **中间** | **中间** | ⭐ **本节的构造** |
  | **`univ`** | **`fullBridgeSetoid`** | **最细端**（= `ThreeViews` 的桥商）|

  **⟹ `Q` 是**连续可调的旋钮**** —— 这是本节的**核心贡献**。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace ParametricEquiv

universe u v

variable {Graph : Type u} {SCM : Type v}

/-! ### §28.1 ⭐ 参数化构造 -/

/-- **集合值桥**。 -/
abbrev Bridge (Graph SCM : Type*) : Type _ := Graph → Set SCM

/-- ⭐⭐ **参数化的中间等价关系** $\sim_Q$：只在查询子族 `Q` 上读桥。

$$s_1 \sim_Q s_2 \iff \forall g \in Q,\ (s_1 \in \mathrm{bridge}\,g \leftrightarrow s_2 \in \mathrm{bridge}\,g)$$

**⚠ 这是本节的**主构造**** —— **`Q` 是连续可调的旋钮**。 -/
def bridgeSetoidOn (bridge : Bridge Graph SCM) (Q : Set Graph) : Setoid SCM where
  r := fun s₁ s₂ => ∀ g ∈ Q, (s₁ ∈ bridge g ↔ s₂ ∈ bridge g)
  iseqv :=
    { refl := fun _ _ _ => Iff.rfl
      symm := fun h g hg => (h g hg).symm
      trans := fun h₁ h₂ g hg => (h₁ g hg).trans (h₂ g hg) }

/-- **最细端**（全读取）：`fullBridgeSetoid`。 -/
def fullBridgeSetoid (bridge : Bridge Graph SCM) : Setoid SCM where
  r := fun s₁ s₂ => ∀ g : Graph, s₁ ∈ bridge g ↔ s₂ ∈ bridge g
  iseqv :=
    { refl := fun _ _ => Iff.rfl
      symm := fun h g => (h g).symm
      trans := fun h₁ h₂ g => (h₁ g).trans (h₂ g) }

/-- ⭐ **`Q = univ` 给出最细端**。 -/
theorem fullBridgeSetoid_eq_univ (bridge : Bridge Graph SCM) :
    fullBridgeSetoid bridge = bridgeSetoidOn bridge Set.univ := by
  ext s₁ s₂
  constructor
  · intro h g _
    exact h g
  · intro h g
    exact h g trivial

/-- **商**：`SCM / ∼_Q`。 -/
abbrev QuotOnBridge (bridge : Bridge Graph SCM) (Q : Set Graph) : Type _ :=
  Quotient (bridgeSetoidOn bridge Q)

/-- **展开判据**（定义性重言）。 -/
theorem bridgeSetoidOn_r_iff (bridge : Bridge Graph SCM) (Q : Set Graph) (s₁ s₂ : SCM) :
    (bridgeSetoidOn bridge Q).r s₁ s₂ ↔
      ∀ g ∈ Q, (s₁ ∈ bridge g ↔ s₂ ∈ bridge g) :=
  Iff.rfl

/-! ### §28.2 ⭐⭐ 中间性（三条） -/

/-- ⭐ **(a) 最细端**：`Q = univ` 时 $\sim_Q$ 恰是 `fullBridgeSetoid`。 -/
theorem bridgeSetoidOn_univ (bridge : Bridge Graph SCM) :
    bridgeSetoidOn bridge Set.univ = fullBridgeSetoid bridge :=
  (fullBridgeSetoid_eq_univ bridge).symm

/-- ⭐⭐ **(b) 单调性（核心结构定理）**：**查询越多，等价越细**。

$$Q \subseteq Q' \implies \sim_{Q'} \ \subseteq\ \sim_Q$$ -/
theorem bridgeSetoidOn_mono (bridge : Bridge Graph SCM) {Q Q' : Set Graph}
    (hQQ' : Q ⊆ Q') {s₁ s₂ : SCM}
    (h : (bridgeSetoidOn bridge Q').r s₁ s₂) :
    (bridgeSetoidOn bridge Q).r s₁ s₂ :=
  fun g hg => h g (hQQ' hg)

/-- ⭐⭐ **(c) 中间性**：对任意 `Q`，$\sim_Q$ 比最细端**粗**（即 `fullBridgeSetoid ⊆ ∼_Q`）。

**⟹ 即**：**`∼_Q` 位于两端之间** ——
`Q = ∅` 时最粗，`Q = univ` 时最细，**其余为中间**。 -/
theorem fullBridgeSetoid_le_on (bridge : Bridge Graph SCM) (Q : Set Graph) :
    fullBridgeSetoid bridge ≤ bridgeSetoidOn bridge Q :=
  fun _ _ h g _ => h g

/-- ⭐ **(c′) 最粗端**：`Q = ∅` 时 $\sim_Q$ 是**万有关系**（一切等价）。

**⟹ 与 `bridgeSetoidOn_univ` 构成**两端****。 -/
theorem bridgeSetoidOn_empty (bridge : Bridge Graph SCM) {s₁ s₂ : SCM} :
    (bridgeSetoidOn bridge ∅).r s₁ s₂ :=
  fun _ hg => absurd hg (Set.notMem_empty _)

/-! ### §28.3 ⭐⭐ 单值桥类的刻画 -/

/-- ⭐ **桥可沿 $\sim_Q$ 下降**（单值化）：
**同一 $\sim_Q$-类内的 SCM 在 `b` 的所有纤维中同进同出**。

**即**：`b` 的区分能力**不超出** `Q` 所覆盖的范围。 -/
def DescendsOn (bridge : Bridge Graph SCM) (Q : Set Graph) (b : Bridge Graph SCM) : Prop :=
  ∀ g, ∀ s₁ s₂, (bridgeSetoidOn bridge Q).r s₁ s₂ → (s₁ ∈ b g ↔ s₂ ∈ b g)

/-- ⭐⭐ **主对应定理：下降 ⟺ `Q` 覆盖 `b` 的区分来源**。

**陈述**：若 `b` 的每个纤维都是**某个 `Q`-成员的纤维的子集并**，
则 `b` 可沿 $\sim_Q$ 下降。

**⚠ 精确形式**：本定理给出**充分条件**（`b` 的纤维可由 `Q` 中成员的纤维决定）。

**⟹ 即**：**「桥单值」取决于「查询族是否覆盖其区分来源」** ——
**这是「中间地带」与「桥单值化」的精确接口。** -/
theorem descends_of_fiber_determined (bridge : Bridge Graph SCM) (Q : Set Graph)
    (b : Bridge Graph SCM)
    (h : ∀ g, ∃ Qg ⊆ Q, ∀ s, s ∈ b g ↔ ∀ q ∈ Qg, s ∈ bridge q) :
    DescendsOn bridge Q b := by
  intro g s₁ s₂ hrel
  obtain ⟨Qg, hQg, hiff⟩ := h g
  rw [hiff s₁, hiff s₂]
  constructor <;> intro hs q hq
  · exact (hrel q (hQg hq)).mp (hs q hq)
  · exact (hrel q (hQg hq)).mpr (hs q hq)

/-- ⭐ **`Q`-确定的桥类**：纤维由 `Q` 中成员的纤维决定。

**⟹ 这是 `descends_of_fiber_determined` 的前件的具名形式。** -/
def QDetermined (bridge : Bridge Graph SCM) (Q : Set Graph) (b : Bridge Graph SCM) : Prop :=
  ∀ g, ∃ Qg ⊆ Q, ∀ s, s ∈ b g ↔ ∀ q ∈ Qg, s ∈ bridge q

/-- ⭐⭐ **单值判据**：`Q`-确定的桥**必然**可沿 $\sim_Q$ 下降。

$$\mathrm{QDetermined} \implies \mathrm{DescendsOn}$$ -/
theorem qDetermined_descends (bridge : Bridge Graph SCM) (Q : Set Graph) (b : Bridge Graph SCM)
    (h : QDetermined bridge Q b) : DescendsOn bridge Q b :=
  descends_of_fiber_determined bridge Q b h

/-! ### §28.4 ⭐ 两端实例 -/

/-- ⭐⭐ **参考桥在 `Q` 上可下降**（$\sim_Q$ 正是为 `bridge` 设计的）。

**陈述**：对 `g ∈ Q`，`bridge g` 在 $\sim_Q$-类上不变。

**⚠ 精确形式说明**：`DescendsOn` 要求 `∀ g`（**不限 `Q`**），
而对 `g ∉ Q`，「$s_1 \sim_Q s_2 \Rightarrow s_1 \in \mathrm{bridge}\,g \leftrightarrow
s_2 \in \mathrm{bridge}\,g$」**一般不成立**（因 $\sim_Q$ 不看 `g`）。

**⟹ 故本节的正确陈述是**「`Q` 上可下降」，而非 `DescendsOn` 的 `∀ g` 形式。**

**这是本节对 `Q24` 原探针的一处**精确化****：
原探针的「单值桥类刻画」须限定在 `Q` 上。 -/
theorem descends_self_on_Q (bridge : Bridge Graph SCM) (Q : Set Graph) :
    ∀ g ∈ Q, ∀ s₁ s₂, (bridgeSetoidOn bridge Q).r s₁ s₂ →
      (s₁ ∈ bridge g ↔ s₂ ∈ bridge g) :=
  fun g hg _ _ hrel => hrel g hg

end ParametricEquiv

end FateV2.Predict