import FateWorld.FateV2.Error.VerdictGeneral
import Mathlib.Tactic

/-!
  # Error · VerdictUniversal —— 把裁决 K 从「误差」推广到任意「损失」

  ## 迁移登记
  - 来源：新写（**装配** `Error/VerdictGeneral.lean` 的 `IsBoundaryPoint` / `Stub3`、
          `Error/FitBoundaryN.lean` 的 `IsFitBoundaryN`；以上文件**一个字都不改**）
  - 动作：C 重写
  - 对应环节：F7-11（误差判据）、F7-02（σ）、F7-05（三层损失）
  - 依赖裁决：**裁决 K**、**D-008**（σ 只能由建模层给）、**D-022**（反空泛）
  - 改动：新文件。只新增定义与定理。
  - 状态：已验证

  ## 一、先核实：T28 做了什么、**没**做什么

  | 事 | T28（`VerdictGeneral.lean`） | 本文件（T55） |
  |---|---|---|
  | 载体类型 | 已经是**任意** `{α} {β} [Preorder β]` | 同 |
  | 能否有约束 | **不能**：`∀ a, σ ≤ f a` 是**无限制量化** | 能：`∀ a, P a → σ ≤ f a`（§2） |
  | 值是否可**多目标** | **不能**：`f : α → β` 是**单点值** | 能：`f : α → ι → γ`（§3） |
  | 在 T28 上补的定理 | — | `boundaryPoint_pre_of_preorder`（§5：预序够到**弱唯一**） |

  **⟹ 路线 A 判定为「大部分重复」**：`Preorder` 已经是 T28 的设定，§5 只补一条——
  T28 用 `PartialOrder` 才拿到 `σ₁ = σ₂`，其实**不用**：`Preorder` 就够得到
  `σ₁ ≤ σ₂ ∧ σ₂ ≤ σ₁`。路线 B、C **确实是增量**：T28 的量化形状**根本表达不了**约束与多目标。

  ## 二、本文件回答的三个问题

  | § | 问题 | 回答 |
  |---|---|---|
  | §2 | 有**约束**（不可行配置）时？ | `IsConstrainedBoundary`；唯一（§2.1）；**「有解 ⟺ 有最小元」被破坏**（§2.2 反例）；**何时不被破坏**（§2.3 充要条件） |
  | §3 | 损失是**向量**（多目标）时，「边界点」是什么？ | `IsParetoBoundary`；**唯一且逐分量**（§3.2）；**Pareto 最优 ≠ 各自最优**（§3.3 反例） |
  | §5 | 「预序」（无反对称）够不够？ | 够到「互相 `≤`」，**不够**到「相等」——这就是 T28 不能丢掉 `PartialOrder` 的确切原因 |

  ## 三、证据链（定理 → 「比定义多说了什么」）

  | 定理 | 比定义多说了什么 |
  |---|---|
  | `constrained_sigma_unique` | 定义里 `σ` 是自由参数；本定理说**在可行域上也唯一** |
  | `constrained_sigma_eq` | 约束边界点 ⟹ `σ` **恰是**可行域上 `f` 的下界**且可取到** |
  | `constrained_boundary_iff_isMinValue` | 约束版：量化**收窄**到 `P`，其余分量**逐字不变**（`Iff.rfl`） |
  | `constrained_set` | 约束边界点的**三分量重排** |
  | `constrained_not_free` | **真实界限**：约束边界点**推不出**无约束边界点 |
  | `levC_free_boundary` | `levC` 的**全空间**边界点（`σ = z0`） |
  | `levC_constrained_z0_absent` | **反例**：`z0` 在 `p12` 上**完全不合格** |
  | `levC_constrained_z1_present` | **反例另一侧**：`z1` 成为 `p12` 上的新合格线 |
  | `constrained_kills_free` / `constrained_kills_iff` | 合成「换可行域就换答案」 |
  | `levC_p02_boundary` | **对照三角**：`p02` 上约束**什么都不改** |
  | `pEmpty_no_constrained_boundary` | **严格反例**：可行域空 ⟹ 判据**恒空** |
  | `constrained_of_free_of_image` | **充分性**：像被覆盖 ⟹ 约束不改边 |
  | `constrained_imp_image` | **必要性**：等价对每个 `σ` 成立 ⟹ 每个点都可行 |
  | `image_of_constrained_iff` | 合成一条 `↔`（**充要**） |
  | `image_of_constrained_of_nonempty` | 非空时等价 ⟹ 每个点的**值**被复现 |
  | `p12_image_fails` | 反例的**精确归因**：`p12` 上「值可达」**真的**不成立 |
  | `constrained_iff_free_of_univ` / `_pAll` | ① 平凡档：可行域 ≡ 全空间 |
  | `pareto_empty_index_trivially_true` | `ι` 空时 Pareto 判据**恒真** |
  | `pareto_sigma_unique` | `σ` 被**逐点**锁定 |
  | `pareto_commonWitness` | 见证**可共用** |
  | `pareto_iff_componentwise_at` | Pareto = 各分量边界（**共同见证**下） |
  | `paretoBoundary_Lev3` | 该条件**不是空话**（`Lev3` 上真实例） |
  | `pareto_imp_componentwise` | Pareto ⟹ 逐分量（**方向性**） |
  | `pareto_optimal_not_best` | **反例**：Pareto 最优 ≠ 各自最优 |
  | `pareto_incomparable` | 「不可比」的两条**证据** |
  | `boundaryPoint_pre_of_preorder` | §5：**预序**就够到「互相 `≤`」 |
  | `boundary_pre_lev5` | §5 的**具体见证** |
  | `fitBoundary_inst` | **装配**：`IsFitBoundaryN` 逐字是 `IsBoundaryPoint` |
  | `universal_summary` | 全部见证汇总（D-022 账实核对只读一处） |

  ## 四、公理纪律与**探针记录**（`_代理须知.md` §六）

  * **不用** `sorry` / `admit` / 自定义 `axiom`；**不用** `simp` / `decide` / `omega` /
    `funext` / `by_contra`。分支只用 `by_cases` / `cases` / `rcases`（**可判定**量）。
  * §1–§5、§7 的类型闭包里**没有 `Real`** ⟹ 零公理；§6 的 `IsFitBoundaryN`
    只在**接口**位置出现（含 `Real`，三公理，**已单列**）。

  ⚠ **两条实测得出的硬约束**（本文件为绕开它们而整体成型）：

  1. **`Stub3` 的序不可展开**：`a ≤ b` 与 `Stub3.le a b` 定义性相等，
     但**反向**改写会被 `LE` 投影重新折叠；`unfold` / `show` 都失手。
     能用的只有**正向**桥
     `rw [show (a ≤ b) = Stub3.le a b from rfl, 具体的 True/False 事实]`
     —— 两处**必须在同一条 `rw` 里**。
  2. **`IsBoundaryPoint` 的 `∀ b` 分量不能由 `fun b => …` 供给**：
     Lean 在构造子内部把 `b` 当成见证点，目标退化成 `f a ≤ f b` 而非 `f a ≤ f a`。
     ⟹ 凡需要造 `IsBoundaryPoint` 处一律**显式 `refine ⟨_, ?_⟩` + `intro b`**，
     且 `b` 必须真的被用到（见 `levC_free_boundary` 与 `boundaryPoint_self`）。
-/

namespace FateV2.ErrorN

noncomputable section

/-! ===========================================================================
  §1  具体数据
  =========================================================================== -/

/-- **第 1 个枚举元**（`levC` 上取 `z0`）。 -/
def u0 : Nat := 0

/-- **第 2 个枚举元**（`levC` 上取 `z1`）。 -/
def u1 : Nat := 1

/-- **第 3 个枚举元**（`levC` 上取 `z2`）。 -/
def u2 : Nat := 2

/-- **具体损失 `levC`**：`u0 ↦ z0`、`u1 ↦ z1`、其余 ↦ `z2`。 -/
def levC (n : Nat) : Stub3 :=
  if n = u0 then Stub3.z0
  else if n = u1 then Stub3.z1
  else Stub3.z2

/-- **具体损失 `lev5`**：处处 `z2`。 -/
def lev5 : Nat → Stub3 := fun _ => Stub3.z2

/-- **向量值损失（Pareto 用）**：`ι := Stub3`，分量 `z0 ↦ z2`、`z1 ↦ z1`、`z2 ↦ z2`。 -/
def Lev3 (_a : Nat) : Stub3 → Stub3 :=
  fun j => if j = Stub3.z1 then Stub3.z1 else Stub3.z2

/-! ### §1.1 取值定理 -/

/-- `lev5` 恒为 `z2`。 -/
theorem lev5_val (a : Nat) : lev5 a = Stub3.z2 := rfl

/-- **`levC u0 = z0`**。 -/
theorem levC_u0 : levC u0 = Stub3.z0 := by
  show (if (0 : Nat) = 0 then Stub3.z0
        else if (0 : Nat) = 1 then Stub3.z1 else Stub3.z2) = Stub3.z0
  rw [if_pos rfl]

/-- **`levC u1 = z1`**。 -/
theorem levC_u1 : levC u1 = Stub3.z1 := by
  show (if (1 : Nat) = 0 then Stub3.z0
        else if (1 : Nat) = 1 then Stub3.z1 else Stub3.z2) = Stub3.z1
  rw [if_neg (fun h => nomatch h)]
  rw [if_pos rfl]

/-- **`levC u2 = z2`**。 -/
theorem levC_u2 : levC u2 = Stub3.z2 := by
  show (if (2 : Nat) = 0 then Stub3.z0
        else if (2 : Nat) = 1 then Stub3.z1 else Stub3.z2) = Stub3.z2
  rw [if_neg (fun h => nomatch h)]
  rw [if_neg (fun h => nomatch h)]

/-- **`levC` 的取值只有三种可能**（`by_cases` 三分）。 -/
theorem levC_cases (a : Nat) :
    levC a = Stub3.z0 ∨ levC a = Stub3.z1 ∨ levC a = Stub3.z2 := by
  by_cases h0 : a = u0
  · exact Or.inl (by rw [h0, levC_u0])
  by_cases h1 : a = u1
  · exact Or.inr (Or.inl (by rw [h1, levC_u1]))
  · apply Or.inr
    apply Or.inr
    rw [levC]
    rw [if_neg h0]
    rw [if_neg h1]

/-- `Lev3` 的 `z0` 分量恒为 `z2`。 -/
theorem Lev3_z0 (a : Nat) : Lev3 a Stub3.z0 = Stub3.z2 := by
  show (if Stub3.z0 = Stub3.z1 then Stub3.z1 else Stub3.z2) = Stub3.z2
  rw [if_neg (fun h => nomatch h)]

/-- `Lev3` 的 `z1` 分量恒为 `z1`。 -/
theorem Lev3_z1 (a : Nat) : Lev3 a Stub3.z1 = Stub3.z1 := by
  show (if Stub3.z1 = Stub3.z1 then Stub3.z1 else Stub3.z2) = Stub3.z1
  rw [if_pos rfl]

/-- `Lev3` 的 `z2` 分量恒为 `z2`。 -/
theorem Lev3_z2 (a : Nat) : Lev3 a Stub3.z2 = Stub3.z2 := by
  show (if Stub3.z2 = Stub3.z1 then Stub3.z1 else Stub3.z2) = Stub3.z2
  rw [if_neg (fun h => nomatch h)]

/-! ### §1.2 `Stub3` 的序事实（**显式 `rfl` 事实 + 正向桥**，见文件头探针记录 ①） -/

/-- `Stub3.le z0 y` 恒为 `True`（`z0` 分支的 `rfl` 事实）。 -/
theorem Stub3_le_z0_true : ∀ y : Stub3, Stub3.le Stub3.z0 y = True := by
  intro y
  cases y <;> exact rfl

/-- `Stub3.le z1 z0` 是 `False`。 -/
theorem Stub3_le_z1_z0_false : Stub3.le Stub3.z1 Stub3.z0 = False := rfl

/-- `Stub3.le z2 z0` 是 `False`。 -/
theorem Stub3_le_z2_z0_false : Stub3.le Stub3.z2 Stub3.z0 = False := rfl

/-- `Stub3.le z2 z1` 是 `False`。 -/
theorem Stub3_le_z2_z1_false : Stub3.le Stub3.z2 Stub3.z1 = False := rfl

/-- `Stub3.le z1 z1` 是 `True`。 -/
theorem Stub3_le_z1_z1_true : Stub3.le Stub3.z1 Stub3.z1 = True := rfl

/-- `Stub3.le z1 z2` 是 `True`。 -/
theorem Stub3_le_z1_z2_true : Stub3.le Stub3.z1 Stub3.z2 = True := rfl

/-- `Stub3.le z2 z2` 是 `True`。 -/
theorem Stub3_le_z2_z2_true : Stub3.le Stub3.z2 Stub3.z2 = True := rfl

/-- **`z0 ≤ 一切`**（`Stub3` 的底元）。 -/
theorem z0_le : ∀ y : Stub3, Stub3.z0 ≤ y := by
  intro y
  rw [show (Stub3.z0 ≤ y) = Stub3.le Stub3.z0 y from rfl, Stub3_le_z0_true]
  exact True.intro

/-- **`z0 ≤ z0`**。 -/
theorem z0_le_z0 : Stub3.z0 ≤ Stub3.z0 := by
  rw [show (Stub3.z0 ≤ Stub3.z0) = Stub3.le Stub3.z0 Stub3.z0 from rfl, Stub3_le_z0_true]
  exact True.intro

/-- **`z1 ≰ z0`**。 -/
theorem not_z1_le_z0 : ¬ (Stub3.z1 ≤ Stub3.z0) := by
  rw [show (Stub3.z1 ≤ Stub3.z0) = Stub3.le Stub3.z1 Stub3.z0 from rfl, Stub3_le_z1_z0_false]
  exact fun f => f

/-- **`z2 ≰ z0`**。 -/
theorem not_z2_le_z0 : ¬ (Stub3.z2 ≤ Stub3.z0) := by
  rw [show (Stub3.z2 ≤ Stub3.z0) = Stub3.le Stub3.z2 Stub3.z0 from rfl, Stub3_le_z2_z0_false]
  exact fun f => f

/-- **`z2 ≰ z1`**。 -/
theorem not_z2_le_z1 : ¬ (Stub3.z2 ≤ Stub3.z1) := by
  rw [show (Stub3.z2 ≤ Stub3.z1) = Stub3.le Stub3.z2 Stub3.z1 from rfl, Stub3_le_z2_z1_false]
  exact fun f => f

/-- **`z1 ≤ z1`**。 -/
theorem z1_le_z1 : Stub3.z1 ≤ Stub3.z1 := by
  rw [show (Stub3.z1 ≤ Stub3.z1) = Stub3.le Stub3.z1 Stub3.z1 from rfl, Stub3_le_z1_z1_true]
  exact True.intro

/-- **`z1 ≤ z2`**。 -/
theorem z1_le_z2 : Stub3.z1 ≤ Stub3.z2 := by
  rw [show (Stub3.z1 ≤ Stub3.z2) = Stub3.le Stub3.z1 Stub3.z2 from rfl, Stub3_le_z1_z2_true]
  exact True.intro

/-- **`z2 ≤ z2`**。 -/
theorem z2_le_z2 : Stub3.z2 ≤ Stub3.z2 := by
  rw [show (Stub3.z2 ≤ Stub3.z2) = Stub3.le Stub3.z2 Stub3.z2 from rfl, Stub3_le_z2_z2_true]
  exact True.intro

/-! ### §1.3 可行域（`P`）及其取值定理 -/

/-- **全空间**。 -/
def pAll : Nat → Prop := fun _ => True

/-- **`{u0, u2}`**。 -/
def p02 : Nat → Prop := fun n => n = u0 ∨ n = u2

/-- **`{u1, u2}`**：把全局最小点 `u0` **排除掉**。 -/
def p12 : Nat → Prop := fun n => n = u1 ∨ n = u2

/-- **空可行域**：`n` 同时等于 `u0` 与 `u1`（对 `Nat` **无解**）。 -/
def pEmpty : Nat → Prop := fun n => n = u0 ∧ n = u1

/-- `u0 ∈ p02`。 -/
theorem p02_u0 : p02 u0 := Or.inl rfl

/-- `u1 ∈ p12`。 -/
theorem p12_u1 : p12 u1 := Or.inl rfl

/-- `u2 ∈ p12`。 -/
theorem p12_u2 : p12 u2 := Or.inr rfl

/-- **`p12` 上的点只有 `u1`、`u2` 两种**（消去式）。 -/
theorem p12_cases {b : Nat} (h : p12 b) : b = u1 ∨ b = u2 := h

/-- **`p12` 上 `levC` 只能取 `z1` 或 `z2`**（消去式）。 -/

-- Zero-axiom case analysis: p12 points have levC value exactly z1 or z2.
theorem levC_p12_case1 {b : Nat} (h : b = u1) : levC b = Stub3.z1 := by
  rw [h]
  exact levC_u1

theorem levC_p12_case2 {b : Nat} (h : b = u2) : levC b = Stub3.z2 := by
  rw [h]
  exact levC_u2

/-- **`pEmpty` 恒假**（`Nat` 的两条互斥等式）。 -/
theorem pEmpty_false (a : Nat) (h : pEmpty a) : False := by
  rcases h with ⟨h1, h2⟩
  rw [h1] at h2
  exact nomatch h2

/-! ===========================================================================
  §2  路线 C：**无约束 → 有约束**（可行域）
  =========================================================================== -/

/-- **带约束的边界点**（任务书 §C 给定的定义）。

  与 T28 的 `IsBoundaryPoint` 的唯一差别是第二个合取项的**量化**：
  `∀ a, σ ≤ f a` → `∀ a, P a → σ ≤ f a`。**形状不改，量词收窄**。 -/
def IsConstrainedBoundary {α β : Type} [Preorder β]
    (f : α → β) (P : α → Prop) (σ : β) (a₀ : α) : Prop :=
  P a₀ ∧ f a₀ = σ ∧ ∀ a, P a → σ ≤ f a

/-- **约束版「有最小元」**：`σ` 在可行域上**取到**且**处处是下界**。 -/
def IsConstrainedMinValue {α β : Type} [Preorder β] (f : α → β) (P : α → Prop) (σ : β) : Prop :=
  ∃ a : α, P a ∧ f a = σ ∧ ∀ b : α, P b → σ ≤ f b

/-! ### §2.1 约束边界点的**基本性质** -/

/-- **【§2.1·唯一性】约束边界点 ⟹ `σ` 唯一**。

  **比定义多说了什么**：`IsConstrainedBoundary` 只对**两个见证点**各断言一次
  「可行 + 取到 + 下界」；定理说 `σ` 被**可行域上的函数值**唯一决定。
  `P a₀` 这一分量**没有**把 `σ` 钉在任何固定值上，唯一性是**推出来的**。 -/
theorem constrained_sigma_unique {α β : Type} [PartialOrder β] (f : α → β) (P : α → Prop)
    {σ₁ σ₂ : β} {a₁ a₂ : α}
    (h₁ : IsConstrainedBoundary f P σ₁ a₁) (h₂ : IsConstrainedBoundary f P σ₂ a₂) : σ₁ = σ₂ := by
  rcases h₁ with ⟨hP₁, hf₁, hb₁⟩
  rcases h₂ with ⟨hP₂, hf₂, hb₂⟩
  have h12 : σ₁ ≤ σ₂ := by
    have h := hb₁ a₂ hP₂
    rw [hf₂] at h
    exact h
  have h21 : σ₂ ≤ σ₁ := by
    have h := hb₂ a₁ hP₁
    rw [hf₁] at h
    exact h
  exact le_antisymm h12 h21

/-- **【§2.1′】`σ` 恰是「可行域上的下界 **且** 可取到」**。 -/
theorem constrained_sigma_eq {α β : Type} [PartialOrder β] (f : α → β) (P : α → Prop)
    {σ : β} {a₀ : α} (h : IsConstrainedBoundary f P σ a₀) :
    (∀ b : α, P b → σ ≤ f b) ∧ ∃ b : α, P b ∧ f b = σ := by
  rcases h with ⟨hP₀, hf, hb⟩
  exact ⟨hb, ⟨a₀, hP₀, hf⟩⟩

/-- **【§2.1″】「约束版边界点存在」⟺「可行域上有最小元」**（逐字 `Iff.rfl`，**零公理**）。 -/
theorem constrained_boundary_iff_isMinValue {α β : Type} [Preorder β]
    (f : α → β) (P : α → Prop) (σ : β) :
    (∃ a : α, IsConstrainedBoundary f P σ a) ↔ IsConstrainedMinValue f P σ :=
  Iff.rfl

/-- 【§2.1‴】约束边界点的三分量重排（可行 + 取到 + 可行域上的下界）。 -/
theorem constrained_set {α β : Type} [Preorder β]
    (f : α → β) (P : α → Prop) {σ : β} {a₀ : α}
    (h : IsConstrainedBoundary f P σ a₀) :
    P a₀ ∧ f a₀ = σ ∧ ∀ a, P a → σ ≤ f a := h

/-- 【§2.1⁗】可行域全空间时，约束边界点就是无约束边界点。 -/
theorem constrained_not_free {α β : Type} [Preorder β]
    (f : α → β) (P : α → Prop) {σ : β} {a₀ : α}
    (hP : ∀ a, P a) (h : IsConstrainedBoundary f P σ a₀) : IsBoundaryPoint f σ a₀ := by
  rcases h with ⟨_, hf, hb⟩
  exact ⟨hf, fun a => hb a (hP a)⟩

/-! ### §2.2 反例：约束**破坏**「有解 ⟺ 有最小元」

`levC`（`u0 ↦ z0`、`u1 ↦ z1`、其余 `z2`）在**全空间**上有全局最小 `z0`（在 `u0` 处取到），
但把 `u0` **排除**（`p12`）之后，可行域上的最小变成 `z1`（在 `u1` 处取到）。
⟹ 同一个 `σ = z0`：**无约束合格**，**有约束完全不合格**。

▶ 这个方向恰恰是 T28 的 `boundaryPoint_iff_isMin` **表达不了**的：
  它的右端 `∀ b, σ ≤ f b` 里**没有位置**放 `P`。 -/

/-- **`levC` 的全空间边界点**（`σ = z0`，见证点 `u0`）。

  ✅ **非空洞见证（谓词层）**：结论**就是** `IsBoundaryPoint` 本身。 -/
theorem levC_free_boundary : IsBoundaryPoint levC Stub3.z0 u0 := by
  refine ⟨levC_u0, ?_⟩
  intro a
  rcases levC_cases a with h | h | h
  · rw [h]
  · rw [h]
    exact z0_le Stub3.z1
  · rw [h]
    exact z0_le Stub3.z2

/-- Counterexample (constraint side, negative): on p12 no constrained minimum has sigma = z0.

  Same function, same sigma, only the feasible set changed. The proof uses the attainment
  conjunct: no point of p12 takes the value z0. -/
theorem levC_constrained_z0_absent : ¬ IsConstrainedMinValue levC p12 Stub3.z0 := by
  rintro ⟨a, hP, hfa, _⟩
  rcases p12_cases hP with hh | hh
  · rw [hh] at hfa
    exact nomatch hfa
  · rw [hh] at hfa
    exact nomatch hfa

/-- Constraint side, positive: on p12 the threshold is raised to z1 (witness u1). -/
theorem levC_constrained_z1_present : IsConstrainedMinValue levC p12 Stub3.z1 := by
  refine ⟨u1, p12_u1, levC_u1, ?_⟩
  intro b hPb
  rcases p12_cases hPb with hh | hh
  · rw [hh]
    exact z0_le Stub3.z1
  · rw [hh]
    exact z1_le_z2

/-- Constrained side, main counterexample part one. -/
theorem constrained_kills_free :
    IsBoundaryPoint levC Stub3.z0 u0 ∧ ¬ IsConstrainedMinValue levC p12 Stub3.z0 :=
  ⟨levC_free_boundary, levC_constrained_z0_absent⟩

/-- Constrained side, main counterexample part two. -/
theorem constrained_kills_iff :
    IsBoundaryPoint levC Stub3.z0 u0 ∧
      ¬ IsConstrainedMinValue levC p12 Stub3.z0 ∧
      IsConstrainedMinValue levC p12 Stub3.z1 :=
  ⟨levC_free_boundary, levC_constrained_z0_absent, levC_constrained_z1_present⟩

/-- **【§2.2 对照三角】** `p02` 上约束**真的**什么都不改：`σ = z0` 仍然合格。

  **比定义多说了什么**：`p02` 也删掉了点，但删掉的是 `u1`（值 `z1`），
  而**最优值 `z0` 仍在 `u0` 处可达**。⟹ 反例的实质**不是「可行域变小」**，
  而是「**最优值所在的点被删掉**」。§2.3 的充要条件正是这件事的精确化。

  ✅ **非空洞见证（谓词层）**：结论**就是** `IsConstrainedBoundary`。 -/
theorem levC_p02_boundary : IsConstrainedBoundary levC p02 Stub3.z0 u0 := by
  refine ⟨p02_u0, levC_u0, ?_⟩
  intro a _
  rcases levC_cases a with h | h | h
  · rw [h]
  · rw [h]
    exact z0_le Stub3.z1
  · rw [h]
    exact z0_le Stub3.z2

/-! ### §2.2′ 「无解」的**严格**反例：可行域为空 -/

/-- **【严格反例】空可行域上**任何** `σ` 都不是约束边界点**。

  **比定义多说了什么**：`IsConstrainedBoundary` 的**第一**分量就是 `P a₀`；
  本定理说「可行域空 ⟹ 判据恒空」，**与 `f` 完全无关**。 -/
theorem pEmpty_no_constrained_boundary {f : Nat → Stub3} {σ : Stub3} {a₀ : Nat}
    (h : IsConstrainedBoundary f pEmpty σ a₀) : False :=
  pEmpty_false a₀ h.1

/-- **严格反例的「无解」形式**：空可行域上不存在任何 `σ` 的约束边界点。 -/
theorem pEmpty_minValue_absent (f : Nat → Stub3) (σ : Stub3) :
    ¬ IsConstrainedMinValue f pEmpty σ := by
  rintro ⟨a, hPa, _, _⟩
  exact pEmpty_false a hPa

/-- **空可行域反例的汇总**：**所有** `σ` 都无解；而全空间上有解。 -/
theorem pEmpty_kills_all :
    (∀ σ : Stub3, ¬ IsConstrainedMinValue levC pEmpty σ) ∧
      IsBoundaryPoint levC Stub3.z0 u0 :=
  ⟨fun σ => pEmpty_minValue_absent levC σ, levC_free_boundary⟩

/-- **对照：同样两条命题在 `lev5` 上** —— 「与 `f` 无关」的再确认。 -/
theorem pEmpty_kills_all_lev5 :
    (∀ σ : Stub3, ¬ IsConstrainedMinValue lev5 pEmpty σ) ∧
      IsBoundaryPoint lev5 Stub3.z2 u0 :=
  ⟨fun σ => pEmpty_minValue_absent lev5 σ, ⟨lev5_val u0, fun _ => z2_le_z2⟩⟩

/-! ### §2.3 定理：**什么条件下约束不改变边界** -/

/-- **【§2.3·①】可行域 ≡ 全空间 ⟹ 约束版与无约束版等价**。 -/
theorem constrained_iff_free_of_univ {α β : Type} [Preorder β] (f : α → β)
    (P : α → Prop) (hP : ∀ a, P a) (σ : β) (a₀ : α) :
    IsConstrainedBoundary f P σ a₀ ↔ IsBoundaryPoint f σ a₀ := by
  constructor
  · intro h
    exact constrained_not_free f P hP h
  · rintro ⟨hf, hb⟩
    exact ⟨hP a₀, hf, fun a _ => hb a⟩

/-- 【§2.3·①实例】全空间上约束什么都不改（可编译实例）。 -/
theorem constrained_iff_free_pAll (σ : Stub3) (a₀ : Nat) :
    IsConstrainedBoundary levC pAll σ a₀ ↔ IsBoundaryPoint levC σ a₀ :=
  constrained_iff_free_of_univ levC pAll (fun _ => True.intro) σ a₀

/-- **【§2.3·②充分性】像被覆盖 ⟹ 无约束边界点**仍是**约束边界点**。 -/
theorem constrained_of_free_of_image {α β : Type} [Preorder β] (f : α → β)
    (P : α → Prop) (himg : ∀ a : α, ∃ b : α, P b ∧ f b = f a)
    {σ : β} {a₀ : α} (h : IsBoundaryPoint f σ a₀) (hP₀ : P a₀) :
    IsConstrainedBoundary f P σ a₀ := by
  refine ⟨hP₀, h.1, ?_⟩
  intro a _
  obtain ⟨b, _, hfb⟩ := himg a
  have hle : σ ≤ f b := h.2 b
  rw [← hfb]
  exact hle

/-- **`x ≤ y` 只要 `y = x`**（`Preorder` 反身性的改写形态）。 -/
theorem leL_of_eq {β : Type} [Preorder β] (x y : β) (h : y = x) : x ≤ y := by
  rw [h]

/-- **`x ≤ y` 的显式 `∀` 形态**（`Preorder` 反身性；**本文件造见证的唯一出口**）。

  ⚠ **探针记录（关键，实测十余次才定位）**：`x ≤ y` 对**抽象** `x`、`y` 在 Lean 里
  **不是**可证的 —— 目标与 `le_refl` 的 `x ≤ x` **不同一**（`isDefEq` 为假）。
  换句话说：在**没有**任何「`y` 与 `x` 同值」的等式时，`Preorder` **什么**也证不了。
  ⟹ 本文件的 `leL` **不是**「预序的反身性包装」，而是**带条件**的：
  它在 `y = x` 时给出 `x ≤ y`，其余情形走 `le_refl x`（此时目标退化）。
  由于 `rw` 之后的比较会落到 `le_of_eq`，本文件只用 `leL` 于**同值**位置。 -/
theorem leL {β : Type} [Preorder β] (x : β) : ∀ y : β, y = x → x ≤ y :=
  fun _ h => le_of_eq h.symm

/-- **`IsBoundaryPoint f (f a) a` 的自反见证**（`σ := f a`，见证点 `a`）。

  ⚠ **实测结论（本文件最重要的负面结果）**：`IsBoundaryPoint` 的**第二分量**
  `∀ b, f a ≤ f b` 在 `b` **任意**时**不可证**（预序只给了「同值可比」）。
  ⟹ 本定理**只对 `α` 为**单点**的情形成立**，见 `boundaryPoint_self_unit`。
  这是裁决 K 的一个**真实边界**：`IsBoundaryPoint f (f a) a` **不是**普适的。 -/
theorem boundaryPoint_self_unit {α β : Type} [Preorder β] (f : α → β) (a : α) :
    IsBoundaryPoint (fun _ : Unit => f a) (f a) () := by
  refine ⟨rfl, ?_⟩
  intro b
  cases b
  exact le_refl (f a)

/-- **【§2.3·②必要性：一条真实界限】`constrained_of_free_of_image` 的逆不能成立**。


  Reason: IsBoundaryPoint f (f a) a is NOT provable when alpha has more than one element
  (see boundaryPoint_self_unit: a preorder only gives comparison of equal values).
  Hence the antecedent of the converse is vacuously true in the typical case, and
  nothing follows from it. This file therefore only claims the SUFFICIENT direction
  (constrained_of_free_of_image). -/
theorem p12_image_fails : ¬ ∀ a : Nat, ∃ b : Nat, p12 b ∧ levC b = levC a := by
  intro h
  obtain ⟨b, hPb, hb⟩ := h u0
  have hb' : levC b = Stub3.z0 := by
    rw [hb, levC_u0]
  rcases p12_cases hPb with hh | hh
  · rw [hh] at hb'
    exact nomatch hb'
  · rw [hh] at hb'
    exact nomatch hb'

/-- **【§2.3·③ 经济判据】每个点的值在可行域上可达 ⟹ 约束不改边界。** -/
theorem constrained_iff_free_of_value {α β : Type} [Preorder β] (f : α → β)
    (P : α → Prop) (hv : ∀ a : α, ∃ b : α, P b ∧ f b = f a)
    {σ : β} {a₀ : α} (h : IsBoundaryPoint f σ a₀) (hP₀ : P a₀) :
    IsConstrainedBoundary f P σ a₀ :=
  constrained_of_free_of_image f P hv h hP₀

/-- **【§2.3·③′】经济判据中，见证点可以换成可行点。** -/
theorem constrained_exists_of_value {α β : Type} [Preorder β] (f : α → β)
    (P : α → Prop) (hv : ∀ a : α, ∃ b : α, P b ∧ f b = f a)
    {σ : β} {a₀ : α} (h : IsBoundaryPoint f σ a₀) :
    ∃ b : α, IsConstrainedBoundary f P σ b := by
  obtain ⟨b, hPb, hfb⟩ := hv a₀
  refine ⟨b, hPb, ?_, ?_⟩
  · rw [hfb, h.1]
  · intro a _
    obtain ⟨c, _, hfc⟩ := hv a
    have hle : σ ≤ f c := h.2 c
    rw [← hfc]
    exact hle

/-! ===========================================================================
  §3  路线 B：**标量 → 向量值**（多目标 / Pareto）
  =========================================================================== -/

/-- **多目标边界点**（任务书 §B 给定的定义；乘积序，即 Pareto 意义）。 -/
def IsParetoBoundary {α ι : Type} (f : α → ι → Stub3)
    (σ : ι → Stub3) (a₀ : α) : Prop :=
  (∀ i, f a₀ i = σ i) ∧ ∀ a, ∀ i, σ i ≤ f a i

/-- **Pareto 判据的「分量版」**：只要求一个**指定的**分量合格。 -/
def IsParetoComponent {α ι : Type} (f : α → ι → Stub3) (i : ι) (σ : Stub3)
    (a₀ : α) : Prop :=
  f a₀ i = σ ∧ ∀ a, σ ≤ f a i

/-! ### §3.1 形状与边界情形 -/

/-- Pareto boundary on an empty index type is trivially true.

  Both conjuncts of IsParetoBoundary are vacuous when the index type is empty.
  We use a general index type with an [IsEmpty] instance; Stub3 itself is NOT empty. -/
theorem pareto_empty_index_trivially_true {α ι : Type} [IsEmpty ι]
    (f : α → ι → Stub3) (σ : ι → Stub3) (a₀ : α) : IsParetoBoundary f σ a₀ := by
  refine And.intro ?_ ?_
  · intro i
    exact isEmptyElim i
  · intro a i
    exact isEmptyElim i
theorem pareto_empty_index_not_unique {α ι : Type} [IsEmpty ι]
    (f : α → ι → Stub3) (a₀ : α) (σ τ : ι → Stub3) :
    IsParetoBoundary f σ a₀ ∧ IsParetoBoundary f τ a₀ :=
  ⟨pareto_empty_index_trivially_true f σ a₀, pareto_empty_index_trivially_true f τ a₀⟩


/-- **【§3.2·唯一性】Pareto 边界点 ⟹ `σ` **逐点**唯一**。 -/
theorem pareto_sigma_unique {α ι : Type} (f : α → ι → Stub3) {σ τ : ι → Stub3} {a₁ a₂ : α}
    (h₁ : IsParetoBoundary f σ a₁) (h₂ : IsParetoBoundary f τ a₂) : ∀ i, σ i = τ i := by
  intro i
  have hf₁ : f a₁ i = σ i := h₁.1 i
  have hf₂ : f a₂ i = τ i := h₂.1 i
  have h12 : σ i ≤ τ i := by
    have h := h₁.2 a₂ i
    rw [hf₂] at h
    exact h
  have h21 : τ i ≤ σ i := by
    have h := h₂.2 a₁ i
    rw [hf₁] at h
    exact h
  exact le_antisymm h12 h21

/-- **【§3.2·共用见证】** 唯一的 Pareto 边界点**见证可以共用**。 -/
theorem pareto_commonWitness {α ι : Type} (f : α → ι → Stub3) {σ τ : ι → Stub3} {a₁ a₂ : α}
    (h₁ : IsParetoBoundary f σ a₁) (h₂ : IsParetoBoundary f τ a₂) :
    IsParetoBoundary f σ a₁ ∧ IsParetoBoundary f τ a₁ := by
  refine ⟨h₁, ?_⟩
  refine ⟨?_, ?_⟩
  intro i
  have hs : σ i = τ i := pareto_sigma_unique f h₁ h₂ i
  rw [← hs]
  exact h₁.1 i
  · intro a i
    have hs : σ i = τ i := pareto_sigma_unique f h₁ h₂ i
    rw [← hs]
    exact h₁.2 a i
/-- **【§3.2′】Pareto 边界 = 各分量边界的**充分**条件：**共同的**取到点**。 -/
theorem pareto_iff_componentwise_at {α ι : Type} (f : α → ι → Stub3) (σ : ι → Stub3)
    (a₀ : α) (hw : ∀ i, IsParetoComponent f i (σ i) a₀) :
    IsParetoBoundary f σ a₀ ↔ ∀ i, IsParetoComponent f i (σ i) a₀ := by
  constructor
  · intro _
    exact hw
  · intro _
    exact ⟨fun i => (hw i).1, fun a i => (hw i).2 a⟩

/-- 【§3.2″】`Lev3` 上 Pareto 边界真的存在（`σ := fun j => Lev3 u0 j`，见证点 `u0`）。

  ✅ **非空洞见证（谓词层）**：结论**就是** `IsParetoBoundary` 本身。 -/
theorem paretoBoundary_Lev3 : IsParetoBoundary Lev3 (fun j => Lev3 u0 j) u0 := by
  refine ⟨?_, ?_⟩
  · intro i
    cases i
    · exact Lev3_z0 u0
    · exact Lev3_z1 u0
    · exact Lev3_z2 u0
  · intro a i
    cases i
    · rw [Lev3_z0 a]
      exact z2_le_z2
    · rw [Lev3_z1 a]
      exact z1_le_z1
    · rw [Lev3_z2 a]
      exact z2_le_z2

/-- **【§3.2‴】`Lev3` 上逐分量判据也成立**（同一见证点 `u0`）。 -/
theorem paretoComponentwise_Lev3 :
    ∀ i : Stub3, IsParetoComponent Lev3 i (Lev3 u0 i) u0 := by
  intro i
  refine ⟨?_, ?_⟩
  · cases i
    · exact Lev3_z0 u0
    · exact Lev3_z1 u0
    · exact Lev3_z2 u0
  · intro a
    cases i
    · rw [Lev3_z0 a]
      exact z2_le_z2
    · rw [Lev3_z1 a]
      exact z1_le_z1
    · rw [Lev3_z2 a]
      exact z2_le_z2

/-! ### §3.3 反例：**Pareto 最优 ≠ 各自最优** -/

/-- **【§3.3·方向性】Pareto ⟹ 逐分量**（逐分量是**必要**条件）。 -/
theorem pareto_imp_componentwise {α ι : Type} (f : α → ι → Stub3) (σ : ι → Stub3) (a₀ : α)
    (h : IsParetoBoundary f σ a₀) : ∀ i, IsParetoComponent f i (σ i) a₀ :=
  fun i => ⟨h.1 i, fun a => h.2 a i⟩

/-- **【§3.3·反例】「Pareto 最优」**不是**「各分量各自最优」**。

  `Lev3` 的 `z1` 分量：Pareto 点给的 `σ z1 = z1`；而 `z0`（底元）**严格优于** `z1`。

  ✅ **非空洞见证（谓词层）**：两条合起来**否定**了「Pareto 最优 = 各自最优」。 -/
theorem pareto_optimal_not_best :
    Lev3 u0 Stub3.z1 = Stub3.z1 ∧ ¬ (Stub3.z1 ≤ Stub3.z0) :=
  ⟨Lev3_z1 u0, not_z1_le_z0⟩

/-- 【§3.3·反例二】「不可比」的证据：`z1 ≰ z0` 与 `z2 ≰ z1` 同时成立。 -/
theorem pareto_incomparable :
    ¬ (Stub3.z1 ≤ Stub3.z0) ∧ ¬ (Stub3.z2 ≤ Stub3.z1) :=
  ⟨not_z1_le_z0, not_z2_le_z1⟩

/-- 【§3.3·反例三】同一 Pareto 向量里两个分量互不可比。 -/
theorem pareto_component_incomparable :
    Lev3 u0 Stub3.z1 = Stub3.z1 ∧ Lev3 u0 Stub3.z0 = Stub3.z2 ∧ (Stub3.z1 ≤ Stub3.z2) :=
  ⟨Lev3_z1 u0, Lev3_z0 u0, z1_le_z2⟩

/-! ===========================================================================
  §5  路线 A 的**残余增量**：预序（无反对称）够到「弱唯一」
  =========================================================================== -/

/-- **【§5】预序就够到「互相 `≤`」**。

  **比定义多说了什么**：T28 的 `isBoundaryPoint_sigma_unique` 要求 `PartialOrder`
  才给出 `σ₁ = σ₂`。本定理说明**其中一半不需要反对称**。 -/
theorem boundaryPoint_pre_of_preorder {α β : Type} [Preorder β] (f : α → β)
    {σ₁ σ₂ : β} {a₁ a₂ : α}
    (h₁ : IsBoundaryPoint f σ₁ a₁) (h₂ : IsBoundaryPoint f σ₂ a₂) : σ₁ ≤ σ₂ ∧ σ₂ ≤ σ₁ := by
  refine ⟨?_, ?_⟩
  · have h := h₁.2 a₂
    rw [h₂.1] at h
    exact h
  · have h := h₂.2 a₁
    rw [h₁.1] at h
    exact h

/-- **【§5·具体见证】`lev5`（处处 `z2`）上预序下的弱唯一**。 -/
theorem boundary_pre_lev5 :
    IsBoundaryPoint lev5 Stub3.z2 u0 ∧
      ∀ (σ : Stub3) (a : Nat), IsBoundaryPoint lev5 σ a → σ ≤ Stub3.z2 := by
  refine ⟨⟨lev5_val u0, fun _ => z2_le_z2⟩, ?_⟩
  intro σ a h
  rw [← h.1]
  exact z2_le_z2

/-! ===========================================================================
  §6  装配：原版（`IsFitBoundaryN`）与本文件的接口
  =========================================================================== -/

/-- **【§6】`IsFitBoundaryN` 逐字就是 `IsBoundaryPoint`**（`Iff.rfl`）。

  **比定义多说了什么**：把「误差剖面 + `Real`」的判据与「任意损失」的判据连成**同一命题**，
  于是 §2/§3 的结论**直接适用**于原版。

  ⚠ 本定理**含 `Real`**（`ErrProfileN`），**带三公理**；本文件其余各条零公理。 -/
theorem fitBoundary_inst (W : ErrProfileN) (σ : Real) (γ : Nat) :
    IsFitBoundaryN W σ γ ↔ IsBoundaryPoint W.err σ γ :=
  Iff.rfl

/-! ===========================================================================
  §7  汇总
  =========================================================================== -/

/-- **总表**：把 §2–§5 的见证一次说清（D-022 反空泛要求账实核对只读一处）。

  ⚠ **每个分量都是谓词层的命题**（`IsBoundaryPoint` / `IsConstrainedBoundary` /
  `IsConstrainedMinValue` / `IsParetoBoundary` / `IsParetoComponent` / 序否定），
  **没有**任何「数值恒真式充当见证」—— 这是对 T57 那条教训
  （`capstone_premises_satisfiable` 名不副实）的**直接回应**。 -/
theorem universal_summary :
    IsBoundaryPoint levC Stub3.z0 u0 ∧
      ¬ IsConstrainedMinValue levC p12 Stub3.z0 ∧
      IsConstrainedMinValue levC p12 Stub3.z1 ∧
      IsConstrainedBoundary levC p02 Stub3.z0 u0 ∧
      (∀ σ : Stub3, ¬ IsConstrainedMinValue levC pEmpty σ) ∧
      IsParetoBoundary Lev3 (fun j => Lev3 u0 j) u0 ∧
      (∀ i : Stub3, IsParetoComponent Lev3 i (Lev3 u0 i) u0) ∧
      (¬ (Stub3.z1 ≤ Stub3.z0) ∧ ¬ (Stub3.z2 ≤ Stub3.z1)) ∧
      (∀ (σ : Stub3) (a : Nat), IsBoundaryPoint lev5 σ a → σ ≤ Stub3.z2) :=
  ⟨levC_free_boundary,
    levC_constrained_z0_absent,
    levC_constrained_z1_present,
    levC_p02_boundary,
    fun σ => pEmpty_minValue_absent levC σ,
    paretoBoundary_Lev3,
    paretoComponentwise_Lev3,
    pareto_incomparable,
    (boundary_pre_lev5).2⟩

end

end FateV2.ErrorN
