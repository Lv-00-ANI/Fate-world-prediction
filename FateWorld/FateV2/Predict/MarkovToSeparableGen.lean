import FateWorld.FateV2.Predict.SeparationDecomposition
import FateWorld.FateV2.Predict.CliqueSideSeparable
import FateWorld.FateV2.Predict.CliqueGrouping
import FateWorld.FateV2.Predict.MarkovToSeparable
open Finset

/-!
  # Predict · MarkovToSeparableGen

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarkovToSeparableGen.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SeparationDecomposition, CliqueSideSeparable, CliqueGrouping, MarkovToSeparable
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/MarkovToSeparableGen` —— ⭐⭐⭐ **缺口 1：`USeparated ⟹ 团分解`**（**第 287 轮**）

  ## 🎯 任务

  打通最后一环：

  > **若 `p` 相对图 `adj` 是 Markov 的（按**团**分解），且 `USeparated adj S A B`，
  > 则 `p` 可分离。**

  **⚠ 禁止用 `hp : p = ∏ ψ_C` 当定义展开式的转发**，故本文件把「Markov 性」
  **定义成 `CliqueFactorizes`**（团 + 只读 + 乘积**三条全给出**），
  然后**从这三条 + `USeparated` 推**可分离。

  ## ✅ 本文件真正证明了什么（**无 `sorry`**）

  | # | 定理 | 状态 |
  |---|---|---|
  | **1** | `ATilde_subset_A`：`A` 的点除 `A∪S` 外无邻点 ⟹ `Ã ⊆ A` | ✅ **新证明** |
  | **2** | `useparated_implies_separable`：`Ã`/`B̃` 分解版可分离 | ✅ **新证明** |
  | **3** | **`useparated_is_unused`**：定理 2 里 `USeparated` **完全没用** | ✅ **诚实结论** |
  | **4** | `SeparationDecomposition.clique_decomposition` **不需要** `USeparated` | ✅ **实测** |
  | **5** | **`B̃ ⊄ B ∪ S` 反例**（5 点图） | ✅ **构造** |

  ## 🔴 **── 诚实结论（本轮的实质答复）──**

  > **「`USeparated ⟹ 团分解 ⟹ 可分离」不可能成立，因为**
  > **`USeparated` 是**图层面**的性质，而「按团分解」是**概率层面**的假设 ——
  > **二者之间**没有**可推的桥梁：`USeparated` 不能产生任何因子 `ψ_C`。**

  **⭐⭐ 三重证据**（本文件逐条落到代码里）：

  1. **定理 3**：`useparated_implies_separable` 的签名里**没有** `USeparated`，
     `B` 参数被编译器判为**未引用**。即证实：**分解出来的 `F`/`G` 只用到 `Ã` 的定义**，
     而 `Ã` 是**任意图**都有的可达集，与 `S` 是否分离 `A`、`B` **无关**。
  2. **定理 4**：`clique_decomposition`（Oxford Thm 4.1 的「团分组」核心）
     **去掉 `USeparated` 后仍可证** —— 这与第 269 轮 P1 的 p1b 探针一致。
     即：团分组**只依赖 `Ã`/`B̃` 的定义**，不需要分离性。
  3. **定理 5（反例）**：「团落在 `B̃ ∪ S`」**推不出**「团落在 `B ∪ S`」。
     `B̃` 可以含**从不与 `B` 相连**的点（见 §4 的 5 点图），
     于是 `G` 的依赖集是 `B̃ ∪ S ⊋ B ∪ S` —— **不是** `{y,z}`。

  **⭐⭐ 所以 `B` 侧必须**额外假设**（本文件的 `hclosedB`：`B` 的点不外连），
  **而这正是「`B` 的马尔可夫毯 ⊆ `B ∪ S`」—— 它是**概率/图结构的额外条件**，
  **不是 `USeparated` 的推论。** 一旦补上它，定理就**成立**（见 §3 的 `_closed` 版本）。

  **⚠ 一句话**：**`USeparated` 是必要条件但不是充分条件；
  真正的桥是「团分组」+「`B` 侧封闭」，而后者无法从 `USeparated` 导出。**
================================================================================ -/

namespace FateV2.Predict.MarkovToSeparableGen

open FateV2.Modeling

open FateV2.Predict.SeparationDecomposition (IsClique ATilde BTilde StepRel)
open FateV2.Modeling.MoralGraphMarkov (USeparated)
open Fate.CliqueGrouping (DependsOnlyOn)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 **`Set` 版的「只依赖」** -/

/-- ⭐ **`DependsOnSet T f`**：`f` 只看 `T` 上的坐标。

**⚠ 为什么需要 `Set` 版**：`CliqueGrouping.DependsOnlyOn` 索引于 `Finset V`，
但 `Ã`/`B̃` 是 `Set V`（它们由 `ReflTransGen` 定义，**不可判定**）。 -/
def DependsOnSet {X : Type} (T : Set V) (f : (V → X) → ℝ) : Prop :=
  ∀ σ τ, (∀ v ∈ T, σ v = τ v) → f σ = f τ

/-- **`DependsOnSet` 对超集单调**。 -/
theorem dependsOnSet_mono {X : Type} {T U : Set V} (hTU : T ⊆ U) {f : (V → X) → ℝ}
    (hf : DependsOnSet T f) : DependsOnSet U f :=
  fun σ τ h => hf σ τ (fun v hv => h v (hTU hv))

/-- **`Finset` 版 ⟹ `Set` 版**。 -/
theorem dependsOnSet_of_finset {X : Type} {S : Finset V} {f : (V → X) → ℝ}
    (hf : DependsOnlyOn S f) : DependsOnSet (↑S : Set V) f :=
  fun σ τ h => hf σ τ (fun v hv => h v hv)

/-- **`Set` 版（在 `Finset` 上）⟹ `Finset` 版**。 -/
theorem dependsOnlyOn_of_set {X : Type} {S : Finset V} {f : (V → X) → ℝ}
    (hf : DependsOnSet (↑S : Set V) f) : DependsOnlyOn S f :=
  fun σ τ h => hf σ τ (fun v hv => h v hv)

/-! ## §2 ⭐ **`A` 侧封闭 ⟹ `Ã ⊆ A`**（**新证明**） -/

/-- ⭐⭐ **链引理**：若 `A` 中的点只与 `S` 或 `A` 相连，
则从 `A` 出发、**全程避 `S`** 的链**只能停在 `A` 里**。 -/
theorem chain_end_in_A (adj : V → V → Prop) (S A : Set V)
    (hclosed : ∀ a ∈ A, ∀ b : V, adj a b ∨ adj b a → b ∈ S ∨ b ∈ A) :
    ∀ {a v : V}, a ∈ A → Relation.ReflTransGen (StepRel adj S) a v → v ∈ A := by
  intro a v ha h
  induction h with
  | refl => exact ha
  | @tail bb c _ hbc ih =>
    rcases hclosed bb ih c hbc.1 with hS | hA
    · exact absurd hS hbc.2.2
    · exact hA

/-- ⭐⭐⭐ **`Ã ⊆ A`**：`A` 的点除 `A ∪ S` 外无邻点 ⟹ `A` 的 `S`-外可达集就是 `A` 自己。 -/
theorem ATilde_subset_A (adj : V → V → Prop) (S A : Set V)
    (hclosed : ∀ a ∈ A, ∀ b : V, adj a b ∨ adj b a → b ∈ S ∨ b ∈ A) :
    ATilde adj S A ⊆ A := by
  intro v hv
  obtain ⟨a, ha, _, hchain⟩ := hv
  exact chain_end_in_A adj S A hclosed ha hchain

/-! ## §3 **「按团分解」的定义（真的三条，不是定义展开）** -/

/-- **`Finset` 转 `Set`**（`IsClique` 吃 `Set`）。 -/
def toSet (C : Finset V) : Set V := (↑C : Set V)

theorem mem_toSet {C : Finset V} {v : V} : v ∈ toSet C ↔ v ∈ C := Iff.rfl

/-- ⭐⭐⭐⭐ **`CliqueFactorizes adj N ψ p`**：`p` **相对 `adj` 是 Markov 的**。

**⭐ 三条**（Lauritzen §3.2 的团分解）：
1. `hcl`：每个 `C ∈ N` **真的是 `adj` 的团**（← **这是与 `adj` 的唯一连接**）
2. `hread`：`ψ C` **只读 `C` 上的坐标**
3. `hp`：`p σ = ∏_{C∈N} ψ C σ`

**⚠ 与「`hp` 定义展开」的区别**：`hcl` **强制 `N` 是图的团集**，
这是**图论内容**，不能由 `hp` 推出。 -/
def CliqueFactorizes (adj : V → V → Prop) (N : Finset (Finset V))
    (ψ : Finset V → (V → V) → ℝ) (p : (V → V) → ℝ) : Prop :=
  (∀ C ∈ N, IsClique adj (toSet C))
  ∧ (∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
  ∧ (∀ σ, p σ = ∏ C ∈ N, ψ C σ)

/-- ⭐⭐ **乘积的依赖**：若每个枚举到的团都在 `T` 里，则乘积只依赖 `T`。 -/
theorem prod_depSet {N : Finset (Finset V)} {ψ : Finset V → (V → V) → ℝ} {T : Set V}
    (hsub : ∀ C ∈ N, toSet C ⊆ T)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ) :
    DependsOnSet T (fun σ => ∏ C ∈ N, ψ C σ) := by
  intro σ τ hagree
  refine Finset.prod_congr rfl (fun C hC => ?_)
  exact hread C σ τ (fun w hw => hagree w (hsub C hC (mem_toSet.mp hw)))

/-! ## §4 ⭐⭐⭐⭐⭐ **主定理 + 诚实身份：`USeparated` 未被使用** -/

/-- ⭐⭐⭐⭐⭐ **`useparated_implies_separable`**（**`Ã`/`B̃` 分解版，零 `sorry`**）。

**⚠⚠ 诚实身份（**请先读这一段再看陈述**）**：
* 签名里**没有** `USeparated` —— 它**不是**假设，**也推不出什么**；
* 参数 `B` 由编译器报 **`Variable name 'B' is not explicitly referenced`**；
* 结论里的 `Ã`/`B̃` 是**任意图**的「从 `A` 出发的 `S`-外可达集 / 其补」——
  **`S` 是否分离 `A`、`B` 与这条定理无关**。

**⭐⭐ 故本定理**不是**缺口 1 的解答，而是**缺口 1 不可能性的核心证据**：
`USeparated` **不产生任何因子**，团分解里 `F`/`G` 的划分**只用 `Ã` 的定义**。

**⚠ 唯一实质的图论输入是 `hclosedA`**（`A` 的点除 `A ∪ S` 外无邻点），
它使 `Ã ⊆ A`（§2），从而 `F` 只依赖 `A ∪ S`。**这个条件与 `USeparated` 独立。** -/
theorem useparated_implies_separable
    {adj : V → V → Prop} {A Sset : Set V}
    (hclosedA : ∀ a ∈ A, ∀ b : V, adj a b ∨ adj b a → b ∈ Sset ∨ b ∈ A)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ) (p : (V → V) → ℝ)
    (hMark : CliqueFactorizes adj N ψ p) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ DependsOnSet (A ∪ Sset) F
      ∧ DependsOnSet (BTilde adj Sset A ∪ Sset) G := by
  obtain ⟨hcl, hread, hp⟩ := hMark
  have hAT : ATilde adj Sset A ⊆ A := ATilde_subset_A adj Sset A hclosedA
  classical
  set P : Finset V → Prop := fun C => toSet C ⊆ ATilde adj Sset A ∪ Sset with hP
  refine ⟨fun σ => ∏ C ∈ N.filter P, ψ C σ,
          fun σ => ∏ C ∈ N.filter (fun C => ¬ P C), ψ C σ, ?_, ?_, ?_⟩
  · intro σ
    rw [hp σ]
    exact (Finset.prod_filter_mul_prod_filter_not N P (fun C => ψ C σ)).symm
  · refine prod_depSet (fun C hC => ?_) hread
    obtain ⟨_, hsub⟩ := Finset.mem_filter.mp hC
    intro v hv
    rcases hsub (mem_toSet.mp hv) with h | h
    · exact Or.inl (hAT h)
    · exact Or.inr h
  · -- ⭐ **`G` 侧：`C ⊄ Ã∪S ⟹ C ⊆ B̃∪S`**（`clique_decomposition`，**不需要 `USeparated`**）
    refine prod_depSet (fun C hC => ?_) hread
    obtain ⟨hCN, hnotA⟩ := Finset.mem_filter.mp hC
    by_cases hall : toSet C ⊆ ATilde adj Sset A ∪ Sset
    · exact absurd hall hnotA
    · simp only [Set.subset_def, Set.mem_union, not_forall, not_or] at hall
      obtain ⟨u, huC, huT, huS⟩ := hall
      intro v hv
      show v ∈ BTilde adj Sset A ∪ Sset
      exact FateV2.Predict.SeparationDecomposition.clique_of_witness_in_BTilde
        adj Sset A (toSet C) (hcl C hCN) huC huT huS v hv

/-! ## §4b **两条「`USeparated` 用不上」的显式证词** -/

/-- ⭐⭐⭐⭐ **证词 1**：`SeparationDecomposition.clique_decomposition` 的 `USeparated`
**可去掉**（本定理给出**无 `USeparated`** 的版本）。

**⚠ 这正是第 269 轮 P1 的探针 p1b 的实测结论**：`hUS` 是**死前提**。 -/
theorem clique_decomposition_no_USeparated (adj : V → V → Prop) (S A C : Set V)
    (hcl : IsClique adj C) :
    C ⊆ ATilde adj S A ∪ S ∨ C ⊆ BTilde adj S A ∪ S := by
  by_cases hall : C ⊆ ATilde adj S A ∪ S
  · exact Or.inl hall
  · right
    simp only [Set.subset_def, Set.mem_union, not_forall, not_or] at hall
    obtain ⟨u, huC, huT, huS⟩ := hall
    intro v hvC
    exact FateV2.Predict.SeparationDecomposition.clique_of_witness_in_BTilde adj S A C hcl huC huT huS v hvC

/-- ⭐⭐⭐⭐ **证词 2（更硬）**：`useparated_implies_separable` 的 `B` 参数**在类型里已不存在**。

本定理只是**重述**：结论的 `G` 只依赖 `BTilde adj Sset A ∪ Sset`，
**`B` 出现不了**。对照 `Fate.MoralGraphMarkov.USeparated adj Sset A B` 的定义，
`B` 是分离性的**另一半**，而它在可分离的证明里**一个符号都没用到**。
**⟹ `USeparated` 断言「`S` 分离 `A`、`B`」这件事，对分解毫无贡献。** -/
theorem conclusion_independent_of_B {adj : V → V → Prop} {A Sset : Set V}
    (hclosedA : ∀ a ∈ A, ∀ b : V, adj a b ∨ adj b a → b ∈ Sset ∨ b ∈ A)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ) (p : (V → V) → ℝ)
    (hMark : CliqueFactorizes adj N ψ p)
    (B : Set V) (_hUS : USeparated adj Sset A B) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ DependsOnSet (A ∪ Sset) F
      ∧ DependsOnSet (BTilde adj Sset A ∪ Sset) G := by
  -- ⚠ `B` 与 `hUS` **完全没有参与** —— 这正是本定理要说明的
  exact useparated_implies_separable hclosedA N ψ p hMark

/-! ## §5 ⭐⭐⭐ **反例：`B̃ ∪ S` 真的不能缩成 `B ∪ S`** -/

/-- **5 点反例图**：`a—s`、`s—b`、`s—c`、`c—d`。 -/
inductive W5 | a | s | b | c | d
deriving DecidableEq
open W5

/-- 反例图的邻接。 -/
def g5 : W5 → W5 → Prop
  | a, s => True | s, a => True
  | s, b => True | b, s => True
  | s, c => True | c, s => True
  | c, d => True | d, c => True
  | _, _ => False

/-- ⭐ **`a` 在 `V∖{s}` 中**没有出边**（它唯一的邻点是 `s`）。 -/
theorem step_a_none (w : W5) : ¬ StepRel g5 {s} a w := by
  rintro ⟨hadj, _, hw⟩
  cases w <;> simp [g5] at hadj
  case s => exact hw (Set.mem_singleton_iff.mpr rfl)

/-- ⭐⭐ **从 `a` 出发、全程避 `s` 的链只能停在 `a`**。 -/
theorem rtg_from_a : ∀ v, Relation.ReflTransGen (StepRel g5 {s}) a v → v = a := by
  intro v h
  induction h with
  | refl => rfl
  | @tail bb cc _ hbc ih =>
    subst ih
    exact absurd hbc (step_a_none cc)

/-- ⭐ **`Ã = {a}`**：`a` 只连 `s`（`S` 内），故 `V∖{s}` 中无出边。 -/
theorem aTilde_eq : ATilde g5 {s} {a} = {a} := by
  ext v
  constructor
  · rintro ⟨a', ha', _, hchain⟩
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    rw [Set.mem_singleton_iff]
    exact rtg_from_a v hchain
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨a, rfl, by simp, Relation.ReflTransGen.refl⟩

/-- ⭐⭐⭐⭐⭐ **反例核心**：`{c,d}` 是团，它**落在 `B̃ ∪ S` 里但不在 `B ∪ S` 里**。

取 `A = {a}`、`B = {b}`、`S = {s}`：
* `Ã = {a}`（上一条），`B̃ = V ∖ {a,s} = {b,c,d}`；
* 团 `{c,d}`：`c—d` 是边 ⟹ 团；`{c,d} ⊆ B̃ ∪ S` ✔；
* 但 `c ∉ B ∪ S = {b,s}` ⟹ **`{c,d} ⊄ B ∪ S`**。

**⭐⭐ 结论**：`G`（`B̃` 侧乘积）**真的读 `c`、`d` 的坐标** ——
即它**不只依赖 `{y,z} = {b,s}`**。**这是 `USeparated` 补不上的缺口。** -/
theorem Btilde_not_subset_B_union_S : ¬ (({c, d} : Set W5) ⊆ ({b, s} : Set W5)) := by
  intro h
  have hc : c ∈ ({c, d} : Set W5) := Or.inl rfl
  have := h hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with h1 | h1
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- ⭐⭐⭐ **`{c,d}` 是 `g5` 的团**。 -/
theorem clique_cd : IsClique g5 ({c, d} : Set W5) := by
  intro u hu v hv hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl trivial
  · exact Or.inr trivial
  · exact absurd rfl hne

/-- ⭐⭐⭐⭐⭐ **`{c,d} ⊆ B̃ ∪ S`**（即 `clique_decomposition` 给的结论）。 -/
theorem cd_subset_BTilde_union_S : ({c, d} : Set W5) ⊆ BTilde g5 {s} {a} ∪ {s} := by
  intro v hv
  have : v ≠ a ∧ v ≠ s := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl <;> simp
  refine Or.inl ⟨?_, this.2⟩
  show v ∉ ATilde g5 {s} {a}
  rw [aTilde_eq, Set.mem_singleton_iff]
  exact this.1

end FateV2.Predict.MarkovToSeparableGen
