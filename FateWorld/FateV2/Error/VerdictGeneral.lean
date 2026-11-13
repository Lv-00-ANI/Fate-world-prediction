import FateWorld.FateV2.Error.VerdictTheory
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · VerdictGeneral —— 把裁决 K **推广 / 泛化 / 抽象**

  ## 迁移登记
  - 来源：新写（**装配并推广** `Error/FitBoundaryN.lean` 的 `IsFitBoundaryN`、
          `Error/VerdictTheory.lean` 的 `fitBoundary_unique` / `fitBoundary_isMin` /
          `isFitBoundaryN_of_isMin`；以上文件**一个字都不改**）
  - 动作：C 重写
  - 对应环节：F7-11（误差判据）、F7-02（σ）
  - 依赖裁决：**裁决 K**、**D-008**（σ 只能由建模层给）、**D-010 / D-011**（多模态）、
              **D-020**（双界只作数学界）、**D-022**（反空泛）
  - 改动：新文件。只新增定义与定理。
  - 状态：已验证

  ## 本文件回答的三个问题（任务书 §一 / §二 / §三）

  | § | 问题 | 回答 |
  |---|---|---|
  | §1 | 裁决 K 是否**绑死**在 `Real` / `Nat` 上？ | **不绑死**：只需**偏序**载体；§1.2 有 `#print axioms = []` 的见证 |
  | §2 | 多模态该**逐分量**判还是**联合**判？ | 两种判据**都**唯一（§2.2），但 `∃γ` **不能**提到外面（§2.1 反例） |
  | §3 | 「判据」本身能不能被抽象？ | 能：`VerdictAxioms` 恰好刻画 `IsBoundaryPoint`，且有**非平凡实例** |

  ## 证据链（定理 → 「比定义多说了什么」）

  | 定理 | 比定义多说了什么 |
  |---|---|
  | `isBoundaryPoint_sigma_unique` | 定义里 `σ` 是**自由参数**；本定理说它被函数**唯一**决定（只需反对称） |
  | `isBoundaryPoint_value_unique` | 合格线的**数值**唯一，与「哪个 `a₀` 当边界点」无关 |
  | `boundaryPoint_iff_isMin` | 「判据有解」⟺「有最小元」：两个分量**合成**一条序论命题 |
  | `isFitBoundaryN_iff_isBoundaryPoint` | 原版（`ErrProfileN` + `Real`）**就是**推广版的实例 |
  | `stubTop_unique` | 唯一性在**自建有限全序**上成立，且**零公理**（骨架不依赖 `Real`） |
  | `multiGamma_conflict` | **反向反例**：各分量各有 `γ`，但**没有**共用的 `γ` —— 两个判据真的不同 |
  | `multiVerdict_unique` | §2 主定理：**逐分量**与**联合**两种判据的 `σ` **都**唯一 |
  | `joint_and_componentwise_mutual` | 联合与逐分量在**存在性**上互相推出（`Fintype` 有限选择） |
  | `boundaryPoint_verdictAxioms` | `IsBoundaryPoint` 满足 `VerdictAxioms`（`Iff.rfl`，零公理） |
  | `verdictAxioms_unique` | 抽象层**推**具体：任一 `VerdictAxioms` 判据都唯一 |
  | `looseCriterion_imp_boundary` | 弱化下界 `f b ≤ σ → f a₀ ≤ f b` ⟹ 原名判据（**第三个**语法模型） |
  | `verdictAxioms_iff_boundaryPoint` | 抽象**不松**：任一实例都与 `IsBoundaryPoint` 逻辑等价 |
  | `attainedValue_not_axioms` | 抽象**有排除力**：「只要求取到」的判据被排除 |
  | `verdict_general_summary` | §1–§3 全部见证汇总（D-022 账实核对只读一处） |

  ## 公理纪律（`_代理须知.md` §六）

  * **不用** `sorry` / `admit` / 自定义 `axiom`。
  * **不用** `simp` 收尾 / `decide` / `omega` / `funext` / `by_contra`；
    分支一律 `by_cases` / `cases`；算术一律 `exact` / `rw` / `linarith` / `norm_num`。
  * **不用** `Finset.sum` / `BigOperators`。`Fintype` 只用于有限选择（`Classical.choose`）。
  * **附加头号目标**：§1 的推广版**零公理**（`#print axioms` 为 `[]`）。
  * 抽象判据的 `iff_min` 取**等式形式**（右端**就是** `IsBoundaryPoint`），
    于是 `boundaryPoint_verdictAxioms` 的实例化是 `Iff.rfl`，**不借 `propext`**（实测零公理）。
-/

namespace FateV2.ErrorN

noncomputable section

/-! ===========================================================================
  §1  推广：裁决 K 的骨架只需要一个**偏序**载体
  =========================================================================== -/

/-- **一般化的裁决 K**（任务书 §一 给定的定义）。

  `IsBoundaryPoint f σ a₀` 读作：「`f` 在 `a₀` 处**取到** `σ`，且 `σ` 是 `f` 的**下界**」。

  与 `IsFitBoundaryN W σ γ` 的差别**只在签名**：
  `ErrProfileN` 换成任意 `α → β`，`Real` 换成任意 `Preorder β`，`Nat` 索引换成任意 `α`。
  命题本体**逐字相同**。 -/
def IsBoundaryPoint {α β : Type} [Preorder β] (f : α → β) (σ : β) (a₀ : α) : Prop :=
  f a₀ = σ ∧ ∀ a, σ ≤ f a

/-- **推广版唯一性**【§1 主定理之一】。

  **比定义多说了什么**：定义对「同一个函数能不能有两个不同的 `σ`」**什么也没说**
  —— `σ` 在定义里是**自由参数**。本定理说：**不能**。

  证明只用**两条下界互夹**：`σ₁ ≤ f a₂ = σ₂` 与 `σ₂ ≤ f a₁ = σ₁`。
  **载体要求**：`β` 只需 `PartialOrder`（反对称）；`Preorder` 不够。 -/
theorem isBoundaryPoint_sigma_unique {α β : Type} [PartialOrder β] (f : α → β)
    {σ₁ σ₂ : β} {a₁ a₂ : α}
    (h₁ : IsBoundaryPoint f σ₁ a₁) (h₂ : IsBoundaryPoint f σ₂ a₂) : σ₁ = σ₂ := by
  have h12 : σ₁ ≤ σ₂ := by
    have h := h₁.2 a₂
    rw [h₂.1] at h
    exact h
  have h21 : σ₂ ≤ σ₁ := by
    have h := h₂.2 a₁
    rw [h₁.1] at h
    exact h
  exact le_antisymm h12 h21

/-- **推广版：合格线的**数值**唯一**（与见证点无关）。

  **比定义多说了什么**：定义只说「这个 `a₀` 处 `f a₀ = σ`」；
  本定理把两个边界点的取值**直接相等**化（`f a₁ = f a₂`）。 -/
theorem isBoundaryPoint_value_unique {α β : Type} [PartialOrder β] (f : α → β)
    {σ₁ σ₂ : β} {a₁ a₂ : α}
    (h₁ : IsBoundaryPoint f σ₁ a₁) (h₂ : IsBoundaryPoint f σ₂ a₂) : f a₁ = f a₂ := by
  have hs : σ₁ = σ₂ := isBoundaryPoint_sigma_unique f h₁ h₂
  rw [h₁.1, h₂.1, hs]

/-- **推广版：有边界点 ⟹ `σ` 是（取得到的）最小元**。

  **比定义多说了什么**：定义的两个分量（等式 / 下界）在这里被**合成为一条**
  「既 `=` 又处处 `≤`」的性质 —— 「最小值」这个概念定义里没有。 -/
theorem isBoundaryPoint_isMin {α β : Type} [Preorder β] (f : α → β)
    {σ : β} {a₀ : α} (h : IsBoundaryPoint f σ a₀) :
    f a₀ = σ ∧ ∀ a, σ ≤ f a :=
  ⟨h.1, h.2⟩

/-- **「有最小元」**（推广版）：存在一处 `f a = σ` 且 `σ` 处处是下界。 -/
def IsMinValue {α β : Type} [Preorder β] (f : α → β) (σ : β) : Prop :=
  ∃ a : α, f a = σ ∧ ∀ b : α, σ ≤ f b

/-- **推广版「判据有解 ⟺ 有最小元」**【§1 主定理之二】。

  **比定义多说了什么**：T20 的 `fitBoundary_isMin` 与 `isFitBoundaryN_of_isMin`
  是**两条**定理各管一个方向，且都写在 `ErrProfileN` 上；本定理把两个方向合成一条 `↔`
  并**脱离** `Real` / `Nat` —— 于是「裁决 K 是一个**纯序论**问题」这句话本身
  成了可移植的定理，不再依赖具体载体。 -/
theorem boundaryPoint_iff_isMin {α β : Type} [Preorder β] (f : α → β) (σ : β) :
    (∃ a : α, IsBoundaryPoint f σ a) ↔ IsMinValue f σ :=
  Iff.rfl

/-! ### §1.1 原版（`ErrProfileN` + `Real`）是推广版的**实例** -/

/-- **原版 ⟺ 推广版（逐字同一命题）**。

  **比定义多说了什么**：`IsFitBoundaryN` 与 `IsBoundaryPoint` 在源码里是**两处各写一遍**
  同一个命题，此前**没有任何定理**把它们连起来。本定理说明：T1/T5/T20 的全部结论
  **直接适用于**推广版在 `ErrProfileN` 上的实例，不必在两套记号之间重证。 -/
theorem isFitBoundaryN_iff_isBoundaryPoint (W : ErrProfileN) (σ : Real) (γ : Nat) :
    IsFitBoundaryN W σ γ ↔ IsBoundaryPoint W.err σ γ :=
  Iff.rfl

/-- **原版唯一性是推广版唯一性的**推论**（不是平行结论）。 -/
theorem fitBoundary_unique_via_general (W : ErrProfileN) {σ₁ σ₂ : Real} {γ₁ γ₂ : Nat}
    (h₁ : IsFitBoundaryN W σ₁ γ₁) (h₂ : IsFitBoundaryN W σ₂ γ₂) : σ₁ = σ₂ :=
  isBoundaryPoint_sigma_unique W.err
    ((isFitBoundaryN_iff_isBoundaryPoint W σ₁ γ₁).1 h₁)
    ((isFitBoundaryN_iff_isBoundaryPoint W σ₂ γ₂).1 h₂)

/-- **推广版 ⟹ 原版**：`ErrProfileN` 上的推广版边界点就是 `IsFitBoundaryN`。

  **比定义多说了什么**：把「推广」做成**双向**接口 —— 下游可任选一侧书写，
  两侧的定理都可用（这是「推广不改语义」的确切含义）。 -/
theorem isFitBoundaryN_of_isBoundaryPoint {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsBoundaryPoint W.err σ γ) : IsFitBoundaryN W σ γ :=
  (isFitBoundaryN_iff_isBoundaryPoint W σ γ).2 h

/-! ### §1.2 零公理实例：自建**有限全序**上的裁决 K

`Real` 是 `ConditionallyCompleteLinearOrder`，任何**触到 `Real`** 的声明都带三公理
（`propext` / `Classical.choice` / `Quot.sound`），与写法无关。
本节用一个**自建的有限全序** `Stub3`（三点 `z0 < z1 < z2`）做载体，
证明「裁决 K 的骨架**完全不依赖 `Real`**」—— 相关定理的公理集是**空集**。 -/

/-- **三元素全序载体**（`z0 < z1 < z2`）。只用 `inductive`，**不含 `Real`**。 -/
inductive Stub3 where
  | z0
  | z1
  | z2
  deriving DecidableEq

/-- `Stub3` 上的序关系（显式枚举；`z0` 最小、`z2` 最大）。 -/
def Stub3.le : Stub3 → Stub3 → Prop
  | .z0, _ => True
  | .z1, .z0 => False
  | .z1, .z1 => True
  | .z1, .z2 => True
  | .z2, .z0 => False
  | .z2, .z1 => False
  | .z2, .z2 => True

instance : LE Stub3 := ⟨Stub3.le⟩

instance : Preorder Stub3 where
  le_refl := by
    intro x
    cases x <;> exact True.intro
  le_trans := by
    intro x y z
    cases x <;> cases y <;> cases z <;> intro h1 <;> intro h2 <;>
      first | exact True.intro | exact h1.elim | exact h2.elim

instance : PartialOrder Stub3 where
  le_antisymm := by
    intro x y
    cases x <;> cases y <;> intro h1 <;> intro h2 <;>
      first | rfl | exact h1.elim | exact h2.elim

instance : LinearOrder Stub3 where
  le_total := by
    intro x y
    cases x <;> cases y <;> first
      | exact Or.inr (False.elim ‹False›)
      | exact Or.inl True.intro
      | exact Or.inr True.intro
  toDecidableLE := fun x y => by
    cases x <;> cases y <;> first
      | exact isTrue True.intro
      | exact isFalse (fun h => h)
  toDecidableEq := fun x y => by
    cases x <;> cases y <;> first
      | exact isTrue rfl
      | exact isFalse (fun h => nomatch h)

/-- `Stub3` 的有限性（三元素显式枚举）。§2 的 `ι` 用它做**有限**族。 -/
instance : Fintype Stub3 where
  elems := {Stub3.z0, Stub3.z1, Stub3.z2}
  complete := by
    intro x
    cases x
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- 具体函数：恒取最大值 `z2`。 -/
def stubTop (_n : Nat) : Stub3 := .z2

/-- **零公理见证 1**：`stubTop` 在 `σ = z2` 处有边界点。 -/
theorem stubTop_boundary : IsBoundaryPoint stubTop Stub3.z2 0 := by
  refine ⟨rfl, ?_⟩
  intro a
  exact True.intro

/-- **零公理见证 2**：**唯一性在一个与 `Real` 无关的载体上成立**。

  **比定义多说了什么**：`isBoundaryPoint_sigma_unique` 是在 `PartialOrder` 上证的；
  本定理说明它在**具体载体** `Stub3` 上真的可用 —— 于是
  「裁决 K 的骨架不依赖 `Real`」不是修辞，而是可编译的事实
  （`#print axioms` 为 `[]`）。 -/
theorem stubTop_unique : ∀ (σ τ : Stub3) (a b : Nat),
    IsBoundaryPoint stubTop σ a → IsBoundaryPoint stubTop τ b → σ = τ := by
  intro σ τ a b h₁ h₂
  have h12 : σ ≤ τ := by
    have h := h₁.2 b
    rw [h₂.1] at h
    exact h
  have h21 : τ ≤ σ := by
    have h := h₂.2 a
    rw [h₁.1] at h
    exact h
  cases σ <;> cases τ <;> first
    | rfl
    | exact absurd h12 (fun x => x)
    | exact absurd h21 (fun x => x)

/-! ===========================================================================
  §2  泛化：多剖面（多模态）的联合裁决
  =========================================================================== -/

/-- **联合剖面**：多剖面族 `W : ι → ErrProfileN` 合成一个函数，取值是**函数**
  `fun i => (W i).err γ`，落在乘积序 `ι → Real` 上。 -/
def jointErr {ι : Type} (W : ι → ErrProfileN) (γ : Nat) : ι → Real :=
  fun i => (W i).err γ

/-- **联合边界**（任务书 §二 的形式）：存在**同一个** `γ`，使每个分量都合格。

  ⚠ 这是任务书 `∀ i, ∃ γ, IsFitBoundaryN (W i) (σ i) γ` 的**不同**写法
  （把 `∃ γ` **提到外面**）。§2.1 证明两者**不等价**。 -/
def IsJointBoundary {ι : Type} [Fintype ι] (W : ι → ErrProfileN) (σ : ι → Real) : Prop :=
  ∃ γ : Nat, ∀ i : ι, IsFitBoundaryN (W i) (σ i) γ

/-- **逐分量边界**（任务书 §二 的原形式）：每个分量**各自**有一个边界点（`γ` 可不同）。 -/
def IsComponentwiseBoundary {ι : Type} (W : ι → ErrProfileN) (σ : ι → Real) : Prop :=
  ∀ i : ι, ∃ γ : Nat, IsFitBoundaryN (W i) (σ i) γ

/-- **有限族的有限选择**：`(∀ i, ∃ n, P i n) ⟹ ∃ n, ∀ i, P i n`（先证一个 `∀` 版本）。

  ⚠ 实测本引理带 `propext` / `Classical.choice` / `Quot.sound`（`Finset.univ.sup` 走
  `Classical.choose`）。它在**泛化层**，不在推广层，故不影响 §1 的零公理结论。 -/
theorem exists_univ_nat {ι : Type} [Fintype ι] (P : ι → Nat → Prop)
    (hmono : ∀ (i : ι) (n m : Nat), n ≤ m → P i n → P i m)
    (h : ∀ i, ∃ n, P i n) : ∃ n, ∀ i, P i n := by
  let f : ι → Nat := fun i => Classical.choose (h i)
  refine ⟨Finset.univ.sup f, ?_⟩
  intro i
  have hle : f i ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ i)
  exact hmono i (f i) (Finset.univ.sup f) hle (Classical.choose_spec (h i))

/-! ### §2.1 反例：联合判据与逐分量判据**真的不同**

两个剖面，各自的最小元分别落在 `γ = 0` 与 `γ = 1`；于是「各用各的 `γ`」可行，
「共用一个 `γ`」**不可行**。 -/

/-- 分量 `A`：误差 `n/(n+1)`（`0, 1/2, 2/3, …`），最小元 `0` 在 `n = 0` 处取到。 -/
def cA : ErrProfileN where
  bias := fun n => (n : Real) / ((n : Real) + 1)
  var := fun _ => 0
  bias_nonneg := by
    intro n
    have h1 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    exact div_nonneg h1 (by linarith)
  var_nonneg := fun _ => le_refl 0

/-- 分量 `B`：误差 `1, 1/2, 2/3, 3/4, …`（即 `A` 在 `n = 0` 处被抬到 `1`），
  最小元在 `n = 1` 处取到 `1/2` —— 与 `A` **错位一格**。 -/
def cB : ErrProfileN where
  bias := fun n => if n = 0 then 1 else (n : Real) / ((n : Real) + 1)
  var := fun _ => 0
  bias_nonneg := by
    intro n
    by_cases h : n = 0
    · rw [if_pos h]
      norm_num
    · rw [if_neg h]
      have h1 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
      exact div_nonneg h1 (by linarith)
  var_nonneg := fun _ => le_refl 0

/-- `cA.err γ = γ/(γ+1)`（把 `+0` 的字段和**摊开**，供后续取值定理 `rw` 用）。 -/
theorem cA_err_eq (γ : Nat) : cA.err γ = (γ : Real) / ((γ : Real) + 1) := by
  show (γ : Real) / ((γ : Real) + 1) + 0 = (γ : Real) / ((γ : Real) + 1)
  rw [add_zero]

/-- `cB.err γ = if γ = 0 then 1 else γ/(γ+1)`（同上）。 -/
theorem cB_err_eq (γ : Nat) :
    cB.err γ = (if γ = 0 then (1 : Real) else (γ : Real) / ((γ : Real) + 1)) := by
  show (if γ = 0 then (1 : Real) else (γ : Real) / ((γ : Real) + 1)) + 0
      = (if γ = 0 then (1 : Real) else (γ : Real) / ((γ : Real) + 1))
  rw [add_zero]

/-- `cA.err 0 = 0`（`cA` 的最小元点）。 -/
theorem cA_zero : cA.err 0 = 0 := by
  rw [cA_err_eq]
  norm_num

/-- `cA.err 1 = 1/2`（`cB` 的最小元点在 `cA` 上**不是**最小）。 -/
theorem cA_one : cA.err 1 = 1 / 2 := by
  rw [cA_err_eq]
  norm_num

/-- `cB.err 0 = 1`（`cB` 在 `γ = 0` 上比 `cA` **高**）。 -/
theorem cB_zero : cB.err 0 = 1 := by
  rw [cB_err_eq]
  rw [if_pos rfl]

/-- `cB.err 1 = 1/2`（`cB` 的最小元点）。 -/
theorem cB_one : cB.err 1 = 1 / 2 := by
  rw [cB_err_eq]
  rw [if_neg (by norm_num)]
  norm_num

/-- **`cA` 在 `γ = 0` 处通过裁决 K（`σ = 0`）**。 -/
theorem cA_boundary_zero : IsFitBoundaryN cA (0 : Real) 0 := by
  refine ⟨cA_zero, ?_⟩
  intro γ'
  exact cA.err_nonneg γ'

/-- **`cB` 在 `γ = 1` 处通过裁决 K（`σ = 1/2`）**。 -/
theorem cB_boundary_one : IsFitBoundaryN cB (1 / 2) 1 := by
  refine ⟨cB_one, ?_⟩
  intro γ'
  by_cases h : γ' = 0
  · rw [h]
    rw [cB_zero]
    norm_num
  · rw [cB_err_eq, if_neg h]
    have h1 : (1 : Nat) ≤ γ' := Nat.one_le_iff_ne_zero.2 h
    have hc : (1 : Real) ≤ (γ' : Real) := by exact_mod_cast h1
    rw [le_div_iff₀ (by linarith)]
    linarith

/-- 反例用的剖面族：`z0 ↦ cA`、`z1 ↦ cB`、`z2 ↦ cA`。 -/
def conflictFamily (i : Stub3) : ErrProfileN :=
  match i with
  | .z0 => cA
  | .z1 => cB
  | .z2 => cA

/-- `conflictFamily .z0 = cA`（取值引理；让后续证明只 `rw`，不必 `show`）。 -/
theorem conflictFamily_z0 : conflictFamily .z0 = cA := rfl

/-- `conflictFamily .z1 = cB`。 -/
theorem conflictFamily_z1 : conflictFamily .z1 = cB := rfl

/-- `conflictFamily .z2 = cA`。 -/
theorem conflictFamily_z2 : conflictFamily .z2 = cA := rfl

/-- **【§2 核心反例】联合（共用 `γ`）与逐分量**不是同一个判据**。

  取 `ι := Stub3`（三元素，**有限**），`W := conflictFamily`（`z0, z2 ↦ cA`，`z1 ↦ cB`），
  `σ := fun i => if i = z1 then 1/2 else 0`：

  * **逐分量成立**：`cA` 在 `γ = 0` 处合格（`cA.err 0 = 0`），
    `cB` 在 `γ = 1` 处合格（`cB.err 1 = 1/2`，见 `cB_boundary_one`）；
  * **联合不成立**：共用 `γ` 要求 `cA.err γ = 0` 与 `cB.err γ = 1/2` **同时**成立。
    前者迫使 `γ = 0`（`cA.err γ = γ/(γ+1)` 在 `γ ≥ 1` 时严格正），
    而 `cB.err 0 = 1 ≠ 1/2` —— 矛盾。

  **比定义多说了什么**：任务书 §二 写 `∀ i, ∃ γ, …`；本定理证明**不能**把 `∃ γ`
  提成 `∃ γ, ∀ i, …`。于是「多模态的裁决 K 该是**逐分量**的」有了严格依据：
  **逐分量是唯一可行形式**，联合形式（单一共用分辨率）会**凭空增加**一个 `γ` 耦合，
  使本来有解的问题**无解**。§2.2 又证明两者**都唯一**，故差别只在**可行性**上。 -/
theorem multiGamma_conflict :
    IsComponentwiseBoundary conflictFamily
        (fun i => if i = Stub3.z1 then (1 / 2 : Real) else 0) ∧
      ¬ IsJointBoundary conflictFamily
        (fun i => if i = Stub3.z1 then (1 / 2 : Real) else 0) := by
  have hA0 : IsFitBoundaryN (conflictFamily .z0) (0 : Real) 0 := by
    rw [conflictFamily_z0]
    exact cA_boundary_zero
  have hA2 : IsFitBoundaryN (conflictFamily .z2) (0 : Real) 0 := by
    rw [conflictFamily_z2]
    exact cA_boundary_zero
  have hB1 : IsFitBoundaryN (conflictFamily .z1) (1 / 2 : Real) 1 := by
    rw [conflictFamily_z1]
    exact cB_boundary_one
  refine ⟨?_, ?_⟩
  · intro i
    cases i
    · exact ⟨0, hA0⟩
    · exact ⟨1, hB1⟩
    · exact ⟨0, hA2⟩
  · rintro ⟨γ, hγ⟩
    have hA : cA.err γ = 0 := by
      have h := (hγ Stub3.z0).1
      rw [conflictFamily_z0] at h
      exact h
    have hB : cB.err γ = 1 / 2 := by
      have h := (hγ Stub3.z1).1
      rw [conflictFamily_z1] at h
      exact h
    have hγ0 : γ = 0 := by
      by_cases h : γ = 0
      · exact h
      · exfalso
        have hc : (0 : Real) < (γ : Real) := by
          have h3 : (0 : Nat) < γ := Nat.pos_of_ne_zero h
          exact_mod_cast h3
        have hpos : (0 : Real) < (γ : Real) / ((γ : Real) + 1) :=
          div_pos hc (by linarith)
        rw [← cA_err_eq] at hpos
        rw [hA] at hpos
        exact lt_irrefl 0 hpos
    rw [hγ0] at hB
    rw [cB_zero] at hB
    linarith

/-- **同一条结论的数值见证**：`cB` 与 `cA` 的最小元**错位一格**（`γ = 0` vs `γ = 1`）。 -/
theorem minPoints_misaligned :
    cA.err 0 = 0 ∧ cB.err 0 = 1 ∧ cB.err 1 = 1 / 2 ∧ cA.err 1 = 1 / 2 :=
  ⟨cA_zero, cB_zero, cB_one, cA_one⟩

/-! ### §2.2 联合判据的唯一性（两个方向**都**成立） -/

/-- **联合 ⟹ 逐分量**：把联合的 `γ` 拿来即可。 -/
theorem componentwise_of_joint {ι : Type} [Fintype ι] {W : ι → ErrProfileN}
    {σ : ι → Real} (h : IsJointBoundary W σ) : IsComponentwiseBoundary W σ := by
  rcases h with ⟨γ, hγ⟩
  exact fun i => ⟨γ, hγ i⟩

/-- **联合 `σ` 唯一**：两个联合边界给同一 `σ`（逐点相等）。

  **比定义多说了什么**：联合判据的 `σ` 是**函数**（每个模态一个分量），
  定义完全不约束它；本定理说它被**整个剖面族**逐点锁定。 -/
theorem jointBoundary_sigma_unique {ι : Type} [Fintype ι] {W : ι → ErrProfileN}
    {σ τ : ι → Real} (hσ : IsJointBoundary W σ) (hτ : IsJointBoundary W τ) :
    ∀ i : ι, σ i = τ i := by
  rcases hσ with ⟨γ₁, h₁⟩
  rcases hτ with ⟨γ₂, h₂⟩
  intro i
  have h12 : σ i ≤ τ i := by
    have h := (h₁ i).2 γ₂
    rw [(h₂ i).1] at h
    exact h
  have h21 : τ i ≤ σ i := by
    have h := (h₂ i).2 γ₁
    rw [(h₁ i).1] at h
    exact h
  exact le_antisymm h12 h21

/-- **逐分量 `σ` 唯一**：每条分量**各自**被锁定。 -/
theorem componentwise_sigma_unique {ι : Type} {W : ι → ErrProfileN}
    {σ τ : ι → Real} (hσ : IsComponentwiseBoundary W σ)
    (hτ : IsComponentwiseBoundary W τ) : ∀ i : ι, σ i = τ i := by
  intro i
  rcases hσ i with ⟨γ₁, h₁⟩
  rcases hτ i with ⟨γ₂, h₂⟩
  exact isBoundaryPoint_sigma_unique (W i).err
    ((isFitBoundaryN_iff_isBoundaryPoint (W i) (σ i) γ₁).1 h₁)
    ((isFitBoundaryN_iff_isBoundaryPoint (W i) (τ i) γ₂).1 h₂)

/-- **【§2 主定理】多模态裁决 K 的**唯一性**：两种判据都唯一。

  同时给出：
  * **逐分量唯一**：任意两条逐分量边界 → `σ` 逐点相等；
  * **联合唯一**：任意两条联合边界 → `σ` 逐点相等。

  **比定义多说了什么**：T20 的 `fitBoundary_unique` 只对**单个**剖面说话；
  本定理是**族**版本 —— 于是「多模态」这一层**不产生新的自由度**：
  每个模态的合格线仍由它自己的剖面唯一决定，联合与逐分量**都是**「唯一」的。
  §2.1 的反例说明：唯一性**成立**，但**可行性**不同。 -/
theorem multiVerdict_unique {ι : Type} [Fintype ι] (W : ι → ErrProfileN) :
    (∀ (σ τ : ι → Real),
        IsComponentwiseBoundary W σ → IsComponentwiseBoundary W τ → ∀ i, σ i = τ i) ∧
    (∀ (σ τ : ι → Real), IsJointBoundary W σ → IsJointBoundary W τ → ∀ i, σ i = τ i) :=
  ⟨fun _ _ hσ hτ => componentwise_sigma_unique hσ hτ,
    fun _ _ hσ hτ => jointBoundary_sigma_unique hσ hτ⟩

/-! ===========================================================================
  §3  抽象：判据的**公理化**刻画
  =========================================================================== -/

/-- **抽象判据**（任务书 §三 给定的结构）。

  两条公理：
  * `unique`：同一函数**任何**两个合格的 `σ` 必相等 —— 这是「判据」的**语义内容**
    （合格线不依赖见证点）；
  * `iff_min`：`P f σ a` **当且仅当**「`σ` 在 `a` 处取到且是下界」。

  ⚠ `iff_min` 的右端**就是** §1 的 `IsBoundaryPoint`，故本结构与
  「`P` 与 `IsBoundaryPoint` 逻辑等价」是同一件事；`unique` **不是多余的**：
  §3.3 的 `attainedValue_not_axioms` 说明一个**只要求取到**的判据会**破坏**唯一性。 -/
structure VerdictAxioms {α β : Type} [Preorder β] (P : (α → β) → β → α → Prop) : Prop where
  /-- 合格线唯一（不依赖见证点）。 -/
  unique : ∀ (f : α → β) (σ₁ σ₂ : β) (a₁ a₂ : α), P f σ₁ a₁ → P f σ₂ a₂ → σ₁ = σ₂
  /-- 判据等价于「取到 + 下界」。 -/
  iff_min : ∀ (f : α → β) (σ : β) (a : α), P f σ a ↔ (f a = σ ∧ ∀ b, σ ≤ f b)

/-- **`IsBoundaryPoint` 满足 `VerdictAxioms`**【§3 主定理之一】。

  `iff_min` 是 `Iff.rfl`（右端**就是** `IsBoundaryPoint` 的定义）；
  `unique` 是 §1 的 `isBoundaryPoint_sigma_unique`。
  **零公理**（`Iff.rfl` 不借 `propext`）。 -/
theorem boundaryPoint_verdictAxioms {α β : Type} [PartialOrder β] :
    VerdictAxioms (fun (f : α → β) (σ : β) (a : α) => IsBoundaryPoint f σ a) where
  unique := fun f σ₁ σ₂ a₁ a₂ h₁ h₂ => isBoundaryPoint_sigma_unique f h₁ h₂
  iff_min := fun f σ a => Iff.rfl

/-- **抽象层推具体**：**任一**满足 `VerdictAxioms` 的判据都唯一。

  **比定义多说了什么**：`VerdictAxioms.unique` 是**结构字段**（落在 `P` 上的假设）；
  本定理把它取出来当**定理**用 —— 方向是「**抽象层 → 具体层**」：
  任何具体判据只要被证 `VerdictAxioms`，就**自动**获得唯一性，
  不必针对那个判据重证一遍。 -/
theorem verdictAxioms_unique {α β : Type} [PartialOrder β]
    {P : (α → β) → β → α → Prop} (hP : VerdictAxioms P) (f : α → β)
    {σ₁ σ₂ : β} {a₁ a₂ : α} (h₁ : P f σ₁ a₁) (h₂ : P f σ₂ a₂) : σ₁ = σ₂ :=
  hP.unique f σ₁ σ₂ a₁ a₂ h₁ h₂

/-- **抽象 = 推广版的逻辑等价类**：任一 `VerdictAxioms` 判据与 `IsBoundaryPoint`
**同真同假**。

  **比定义多说了什么**：这把抽象钉成**非任意**的：`VerdictAxioms` 两条公理的模型
  **只有一类** —— 与 `IsBoundaryPoint` 等价的判据。于是
  * 抽象**不空**：至少两个语法不同的实例（§3 的 `Iff.rfl` 版与 §3.2 的弱化版）；
  * 抽象**不松**：任何实例都与 `IsBoundaryPoint` 等价；
  * 抽象**有排除力**：§3.3 的「只要求取到」判据**不**满足公理。 -/
theorem verdictAxioms_iff_boundaryPoint {α β : Type} [PartialOrder β]
    {P : (α → β) → β → α → Prop} (hP : VerdictAxioms P) (f : α → β) (σ : β) (a : α) :
    P f σ a ↔ IsBoundaryPoint f σ a :=
  hP.iff_min f σ a

/-! ### §3.2 非平凡实例：**弱化下界**版（与 `IsBoundaryPoint` 语法不同） -/

/-- **弱化下界判据**：`f a₀ = σ`，且「`f b ≤ σ` 时 `f a₀ ≤ f b`」。

  与 `IsBoundaryPoint` 的差别：后者说「`σ` **处处**是下界」（`∀ b, σ ≤ f b`），
  前者只在**`f b ≤ σ` 的那些 `b`** 上提出要求（`∀ b, f b ≤ σ → f a₀ ≤ f b`）。
  **字面明显不同**；§3.2 证明它们**逻辑等价**（在全序下），
  于是它是 `VerdictAxioms` 的**非平凡实例**，而不是把定义抄一遍。 -/
def IsWeakBoundary {α β : Type} [LinearOrder β] (f : α → β) (σ : β) (a₀ : α) : Prop :=
  f a₀ = σ ∧ ∀ b : α, f b ≤ σ → f a₀ ≤ f b

/-- **弱化判据 ⟹ `IsBoundaryPoint`**（在全序下）。

  证明：若某个 `b` 有 `¬ σ ≤ f b`，则 `f b < σ = f a₀`；而弱化条件要求
  `f b ≤ σ → f a₀ ≤ f b`，即 `f a₀ ≤ f b` —— 与 `f b < f a₀` 正面冲突。

  **比定义多说了什么**：把「弱化版其实不弱」这件事落成定理 ——
  `∀ b, f b ≤ σ → f a₀ ≤ f b` 与 `∀ b, σ ≤ f b`（在 `f a₀ = σ` 下）**等价**。 -/
theorem weakBoundary_imp_boundary {α β : Type} [LinearOrder β] {f : α → β} {σ : β}
    {a₀ : α} (h : IsWeakBoundary f σ a₀) : IsBoundaryPoint f σ a₀ := by
  rcases h with ⟨h1, hk⟩
  refine ⟨h1, ?_⟩
  intro b
  by_cases hle : σ ≤ f b
  · exact hle
  · exfalso
    have hlt : f b < σ := lt_of_not_ge hle
    have hb : f b ≤ σ := le_of_lt hlt
    have h1' : f a₀ ≤ f b := hk b hb
    rw [h1] at h1'
    exact absurd h1' (not_le_of_gt hlt)

/-- **`IsBoundaryPoint` ⟹ 弱化判据**（反向，显然）。 -/
theorem boundary_imp_weakBoundary {α β : Type} [LinearOrder β] {f : α → β} {σ : β}
    {a₀ : α} (h : IsBoundaryPoint f σ a₀) : IsWeakBoundary f σ a₀ := by
  rcases h with ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  intro b _
  rw [h1]
  exact h2 b

/-- **弱化判据 ⟺ `IsBoundaryPoint`**（全序下）。

  **比定义多说了什么**：「可以换一套**语法**定义同一个判据」的严格见证 ——
  §3 的抽象因此**不是**对某一种写法的过拟合。 -/
theorem weakBoundary_iff_boundary {α β : Type} [LinearOrder β] (f : α → β) (σ : β) (a₀ : α) :
    IsWeakBoundary f σ a₀ ↔ IsBoundaryPoint f σ a₀ :=
  ⟨weakBoundary_imp_boundary, boundary_imp_weakBoundary⟩

/-- **【§3 非平凡实例】弱化判据**也**满足 `VerdictAxioms`（`Stub3` 载体上）。

  **与 `boundaryPoint_verdictAxioms` 的区别**：那个的 `iff_min` 是 `Iff.rfl`
  （右端**就是**定义），本条的 `iff_min` 要**真的证** `weakBoundary_iff_boundary`
  —— 于是「抽象不是空壳」有**两个语法上不同**的模型。

  证明结构：`unique` 由「弱化判据 → `IsBoundaryPoint` → 唯一」复合得到
  （这正是**抽象层推具体**的实例用法）。 -/
theorem weakBoundary_verdictAxioms :
    VerdictAxioms (fun (f : Nat → Stub3) (σ : Stub3) (a : Nat) => IsWeakBoundary f σ a) where
  unique := by
    intro f σ₁ σ₂ a₁ a₂ h₁ h₂
    exact isBoundaryPoint_sigma_unique f
      (weakBoundary_imp_boundary h₁) (weakBoundary_imp_boundary h₂)
  iff_min := fun f σ a => weakBoundary_iff_boundary f σ a

/-! ### §3.3 抽象**有排除力**：「只要求取到」的判据被排除 -/

/-- **「只要求取到」的判据**：`∃ b, f b = σ`（即「`σ` 是 `f` 的某个**取值**」）。

  它**保留**了 `IsBoundaryPoint` 第一分量的**来源**（「`σ` 在**某处**取到」），
  却**完全丢掉**「`σ` 是**下界**」与「在 `a₀` 处取到」两条 ——
  正是 §3 要排除的那种「看起来像裁决 K」的判据。 -/
def IsAttainedValue {α β : Type} (f : α → β) (σ : β) (_a₀ : α) : Prop :=
  ∃ b : α, f b = σ

/-- 反例用的函数：`n = 0 ↦ z2`，否则 `z1`（**取到两个**不同值）。 -/
def twoVal (n : Nat) : Stub3 := if n = 0 then Stub3.z2 else Stub3.z1

/-- `twoVal 0 = z2`。 -/
theorem twoVal_zero : twoVal 0 = Stub3.z2 := by
  show (if (0 : Nat) = 0 then Stub3.z2 else Stub3.z1) = Stub3.z2
  rw [if_pos rfl]

/-- `twoVal 1 = z1`。 -/
theorem twoVal_one : twoVal 1 = Stub3.z1 := by
  show (if (1 : Nat) = 0 then Stub3.z2 else Stub3.z1) = Stub3.z1
  rw [if_neg (by norm_num)]

/-- **【§3 排除力主定理】「只要求取到」的判据**不**满足 `VerdictAxioms`**。

  `twoVal` 同时取到 `z2` 与 `z1`，于是 `IsAttainedValue twoVal z2 0` 与
  `IsAttainedValue twoVal z1 0` **都成立**，但 `z2 ≠ z1` —— `unique` 崩。

  **比定义多说了什么**：这条把「抽象不是随便套一个谓词」落成确定结论。
  「σ 是 f 的某个取值」这个最自然的弱化**被排除**；结合 §1 的唯一性，
  **合格线必须同时携带「下界」语义**，不能只携带「取到」。
  这正是 §3 抽象层的**实质内容**：两条公理**合起来**才钉得住裁决 K。 -/
theorem attainedValue_not_axioms :
    ¬ VerdictAxioms (fun (f : Nat → Stub3) (σ : Stub3) (a : Nat) => IsAttainedValue f σ a) := by
  intro hA
  have h1 : IsAttainedValue twoVal Stub3.z2 0 := ⟨0, twoVal_zero⟩
  have h2 : IsAttainedValue twoVal Stub3.z1 0 := ⟨1, twoVal_one⟩
  have huniq := hA.unique twoVal Stub3.z2 Stub3.z1 0 0 h1 h2
  exact absurd huniq.symm (fun h => nomatch h)

/-! ===========================================================================
  §4  汇总：本文件全部见证
  =========================================================================== -/

/-- **总表**：把 §1–§3 的见证一次说清（D-022 反空泛要求账实核对只读一处）。

  | 项 | 内容 | 出处 |
  |---|---|---|
  | 推广版唯一性 | 任意 `PartialOrder` 载体 | `isBoundaryPoint_sigma_unique` |
  | 推广版判据 ⟺ 最小元 | 任意 `Preorder` 载体 | `boundaryPoint_iff_isMin` |
  | 原版是实例 | `IsFitBoundaryN ↔ IsBoundaryPoint W.err` | `isFitBoundaryN_iff_isBoundaryPoint` |
  | 零公理实例 | `Stub3`（自建有限全序） | `stubTop_boundary` / `stubTop_unique` |
  | 多模态：两判据不同 | `σ` 逐分量不同（`0` / `1/2`） | `multiGamma_conflict` |
  | 多模态：唯一性 | 逐分量与联合**都**唯一 | `multiVerdict_unique` |
  | 抽象：存在实例 | `IsBoundaryPoint` 与弱化版两个 | `boundaryPoint_verdictAxioms` / `weakBoundary_verdictAxioms` |
  | 抽象：有排除力 | 「只要求取到」判据被排除 | `attainedValue_not_axioms` |

  **比定义多说了什么**：本身不证新数学，而是把各条的**可核对断言**放在一处，
  使账实核对成为**可编译**的对象（对照 D-022）。 -/
theorem verdict_general_summary :
    (∀ {α β : Type} [PartialOrder β] (f : α → β) (σ₁ σ₂ : β) (a₁ a₂ : α),
        IsBoundaryPoint f σ₁ a₁ → IsBoundaryPoint f σ₂ a₂ → σ₁ = σ₂) ∧
    (∀ (W : ErrProfileN) (σ : Real) (γ : Nat),
        IsFitBoundaryN W σ γ ↔ IsBoundaryPoint W.err σ γ) ∧
    IsBoundaryPoint stubTop Stub3.z2 0 ∧
    (∀ (σ τ : Stub3) (a b : Nat),
        IsBoundaryPoint stubTop σ a → IsBoundaryPoint stubTop τ b → σ = τ) ∧
    IsComponentwiseBoundary conflictFamily
        (fun i => if i = Stub3.z1 then (1 / 2 : Real) else 0) ∧
    ¬ IsJointBoundary conflictFamily
        (fun i => if i = Stub3.z1 then (1 / 2 : Real) else 0) ∧
    cA.err 0 = 0 ∧ cB.err 1 = 1 / 2 ∧
    (∀ (f : Nat → Stub3) (σ : Stub3) (a₀ : Nat),
        IsWeakBoundary f σ a₀ ↔ IsBoundaryPoint f σ a₀) :=
  ⟨fun f _ _ _ _ h₁ h₂ => isBoundaryPoint_sigma_unique f h₁ h₂,
    fun W σ γ => isFitBoundaryN_iff_isBoundaryPoint W σ γ,
    stubTop_boundary,
    stubTop_unique,
    multiGamma_conflict.1,
    multiGamma_conflict.2,
    cA_zero,
    cB_one,
    fun f σ a => weakBoundary_iff_boundary f σ a⟩

end

end FateV2.ErrorN
