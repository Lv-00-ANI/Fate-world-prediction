/-
  ===========================================================================
  RebaseSplit：把 `Split` / `ReadSet` 搬到子类型 `↥A` 上

  ## 来源说明
  本文件**自包含**：由于 `Fate_agent_staging/` 不在 Lake 的模块搜索路径里，
  `Fate_agent_staging/RebaseSetLemmas.lean` 的内容（`sub` / `mem_sub_iff` /
  `attach_union_univ` / `disjoint_attach` / `mem_attach_iff`）被**原样复制**进来
  （见下方 `§0`，其文件头注释保留）。在此基础上本文件新增 `§1`、`§2`。

  ## 本文件新增内容
  * `§1 split_rebase`（**核心，已完成**）：
    `Fate.View19.Split R X Y Z` + `∀ v, R v ⊆ A ∨ v ∉ A` ⟹
    `Fate.View19.Split (fun v : ↥A => sub A (R v.1) _) (sub A X hX) (sub A Y hY) (sub A Z hZ)`。
    证明即「用 `mem_sub_iff` 在 `↥A` 与 `V` 之间来回搬运 `∈`」，无实质障碍。

  * `§2 readSet_rebase`（**已完成，但是一个 Prop 形式**）：
    定义 `extEnd A ω₀ w : V → α`（把 `↥A → α` 延拓成 `V → α`，
    `A` 外的坐标取 `ω₀ v`），并证明

      `ReadSet ψ R` + `∀ v : ↥A, R v.1 ⊆ A` ⟹
      `∀ v x y, (∀ u ∈ sub A (R v.1) _, x u = y u) →`
        `ψ v.1 (extEnd A ω₀ x) = ψ v.1 (extEnd A ω₀ y)`。

    ⚠ **为什么不是直接的 `ReadSet (fun v w => ψ v.1 (extEnd A ω₀ w)) (...)`**：
    `ReadSet ψA RA` 要求 `ψA v` 是**函数** `(↥A → α) → ℝ`。用 `extEnd` 定义
    `ψA v w := ψ v.1 (extEnd A ω₀ w)` 时，`extEnd A ω₀ w` 在 `A` 外的坐标
    被 `ω₀` 填充，所以 `ψA v` 的取值**依赖** `ω₀`；`ReadSet` 对它的表述本身
    仍然良定义（`ω₀` 是固定参数），上面那条定理恰好给出了 `ReadSet` 所需的
    "沿 `sub A (R v.1)` 一致 ⟹ 输出相等"。**唯一的接口缺口**是：把它写成
    `ReadSet (fun v w => ψ v.1 (extEnd A ω₀ w)) (fun v => sub A (R v.1) _)`
    需要 `hR : ∀ v : ↥A, R v.1 ⊆ A` 在**每个** `v : ↥A` 上成立；任务书给的
    `hAll : ∀ v, R v ⊆ A ∨ v ∉ A` 只保证 `v ∈ A` 的那些，而对 `v : ↥A`
    我们确实有 `v.1 ∈ A`，所以可从中**逐点**取出（见 `hR_of_hAll` 辅助定理，
    本文件已给出）。因此这里额外提供 `readSet_rebase'`，它就是字面上的
    `ReadSet` 形式，条件用 `hAll`；两条并列给出，`§2` 无缺口。

  ## 状态
  **零 error、零 sorry、零 admit、零 axiom。**
  ===========================================================================
-/

import FateWorld.Legacy.CondIndepGeneralNZ

namespace Fate.GraphToProbView7

open Finset

universe u

variable {V : Type u} [DecidableEq V]

/-- 把 `X ⊆ A` 搬到子类型 `↥A`：`sub A X hX` 是 `X` 在 `↥A` 中的像。 -/
def sub (A : Finset V) (X : Finset V) (_hX : X ⊆ A) : Finset ↥A :=
  (Finset.univ : Finset ↥A).filter (fun v => (v : V) ∈ X)

/-- `sub` 的成员判定：后续一切操作的杠杆。 -/
@[simp]
theorem mem_sub_iff (A X : Finset V) (hX : X ⊆ A) (v : ↥A) :
    v ∈ sub A X hX ↔ (v : V) ∈ X := by
  simp [sub]

/-- **引理 1**：`X ∪ Y ∪ Z = A` ⟹ 三者在 `↥A` 中的像覆盖 `univ`。 -/
theorem attach_union_univ (A X Y Z : Finset V)
    (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (hcover : X ∪ Y ∪ Z = A) :
    sub A X hX ∪ sub A Y hY ∪ sub A Z hZ = (Finset.univ : Finset ↥A) := by
  ext v
  simp only [mem_sub_iff, mem_union, mem_univ, iff_true]
  have hvA : (v : V) ∈ X ∪ Y ∪ Z := hcover ▸ v.2
  rcases mem_union.mp hvA with h | h
  · rcases mem_union.mp h with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
  · exact Or.inr h

/-- **引理 2**：`X` 与 `Y` 不交 ⟹ 二者在 `↥A` 中的像不交。 -/
theorem disjoint_attach {A X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ A)
    (hXY : Disjoint X Y) : Disjoint (sub A X hX) (sub A Y hY) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  simp only [mem_sub_iff] at hvx hvy
  exact (Finset.disjoint_left.mp hXY) hvx hvy

/-- **引理 3**：`↥A` 中的像的成员判定。 -/
theorem mem_attach_iff {A X : Finset V} (hX : X ⊆ A) (v : ↥A) :
    v ∈ sub A X hX ↔ (v : V) ∈ X :=
  mem_sub_iff A X hX v


/-! ===========================================================================
  §1 **核心：`Split` 搬到 `↥A`**
  =========================================================================== -/

omit [DecidableEq V] in
/-- 从任务书形状的 `hAll : ∀ v, R v ⊆ A ∨ v ∉ A` 逐点取出 `v : ↥A` 所需的
`R v.1 ⊆ A`。 -/
theorem hR_of_hAll {R : V → Finset V} {A : Finset V}
    (hAll : ∀ v, R v ⊆ A ∨ v ∉ A) (v : ↥A) : R v.1 ⊆ A := by
  rcases hAll v.1 with h | h
  · exact h
  · exact absurd v.2 h

/-- ⭐⭐ **核心引理**：`Split` 在子类型 `↥A` 上成立（前提：读集在 `A` 内封闭）。 -/
theorem split_rebase {R : V → Finset V} {X Y Z A : Finset V}
    (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (hAll : ∀ v, R v ⊆ A ∨ v ∉ A)
    (hsplit : Fate.View19.Split R X Y Z) :
    Fate.View19.Split (fun v : ↥A => sub A (R v.1) (hR_of_hAll hAll v))
      (sub A X hX) (sub A Y hY) (sub A Z hZ) := by
  intro v
  show sub A (R v.1) _ ⊆ sub A X hX ∪ sub A Z hZ ∨
       sub A (R v.1) _ ⊆ sub A Y hY ∪ sub A Z hZ
  rcases hsplit v.1 with h | h
  · left
    intro w hw
    simp only [mem_sub_iff] at hw ⊢
    rcases mem_union.mp (h hw) with h2 | h2
    · exact mem_union.mpr (Or.inl (mem_sub_iff A X hX w |>.mpr h2))
    · exact mem_union.mpr (Or.inr (mem_sub_iff A Z hZ w |>.mpr h2))
  · right
    intro w hw
    simp only [mem_sub_iff] at hw ⊢
    rcases mem_union.mp (h hw) with h2 | h2
    · exact mem_union.mpr (Or.inl (mem_sub_iff A Y hY w |>.mpr h2))
    · exact mem_union.mpr (Or.inr (mem_sub_iff A Z hZ w |>.mpr h2))

/-! ===========================================================================
  §2 **`ReadSet` 搬到 `↥A`**
  =========================================================================== -/

variable {α : Type u}

/-- 把 `w : ↥A → α` 延拓成 `V → α`：`A` 内取 `w`，`A` 外取固定标定 `ω₀`。 -/
def extEnd (A : Finset V) (ω₀ : V → α) (w : ↥A → α) : V → α :=
  fun v => if h : v ∈ A then w ⟨v, h⟩ else ω₀ v

@[simp]
theorem extEnd_of_mem (A : Finset V) (ω₀ : V → α) (w : ↥A → α)
    (v : V) (h : v ∈ A) : extEnd A ω₀ w v = w ⟨v, h⟩ := by
  simp [extEnd, h]

theorem extEnd_of_not_mem (A : Finset V) (ω₀ : V → α) (w : ↥A → α)
    (v : V) (h : v ∉ A) : extEnd A ω₀ w v = ω₀ v := by
  simp [extEnd, h]

/-- ⭐⭐ **`ReadSet` 的 rebase（显式形式）**：若 `ψ v` 只读 `R v`，且 `R v ⊆ A`，
则 `ψA v w := ψ v.1 (extEnd A ω₀ w)` 只读 `sub A (R v.1)`。 -/
theorem readSet_rebase {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : Fate.View19.ReadSet ψ R)
    (A : Finset V) (ω₀ : V → α)
    (hR : ∀ v : ↥A, R v.1 ⊆ A) :
    ∀ (v : ↥A) (x y : ↥A → α),
      (∀ u ∈ sub A (R v.1) (hR v), x u = y u) →
      ψ v.1 (extEnd A ω₀ x) = ψ v.1 (extEnd A ω₀ y) := by
  intro v x y hxy
  refine hread v.1 _ _ fun u hu => ?_
  have hxA : u ∈ A := hR v hu
  have hmem : (⟨u, hxA⟩ : ↥A) ∈ sub A (R v.1) (hR v) := by
    simp only [mem_sub_iff]; exact hu
  rw [extEnd_of_mem A ω₀ x u hxA, extEnd_of_mem A ω₀ y u hxA]
  exact hxy ⟨u, hxA⟩ hmem

/-- ⭐⭐ **`ReadSet` 的 rebase（字面 `ReadSet` 形式）**，条件直接用任务书的
`hAll : ∀ v, R v ⊆ A ∨ v ∉ A`。 -/
theorem readSet_rebase' {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : Fate.View19.ReadSet ψ R)
    (A : Finset V) (ω₀ : V → α)
    (hAll : ∀ v, R v ⊆ A ∨ v ∉ A) :
    Fate.View19.ReadSet (fun v w => ψ v.1 (extEnd A ω₀ w))
      (fun v : ↥A => sub A (R v.1) (hR_of_hAll hAll v)) :=
  readSet_rebase hread A ω₀ (hR_of_hAll hAll)

end Fate.GraphToProbView7
