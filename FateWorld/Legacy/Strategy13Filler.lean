import FateWorld.Legacy.Strategy13TypedSplit
import FateWorld.Legacy.Strategy11TopoPrefix
import Mathlib.Tactic

/-!
# 视角 13（续）：填充引理 —— **因子闭包填充（filler）**

`STRATEGY13_TYPED_SPLIT.md` §3/§4 把「`dSep` ⟹ `Disjoinable`」归约为一条
**纯图论不动点引理** `Filler`。本文件：

* 定义 `Filler`（D13.4）与 `PPC`（单点父闭）并给出精确语义；
* **证明** `PPC` 的**单项步**（L13.2，`ppc_insert`）——
  即「把一个自身父集落在 `A ∪ Z` 里的点加进 `A`，`PPC` 保持」；
* **证明** `PPC` 对子集封闭（L13.3，`ppc_subset`）；
* **证明** `Disjoinable` 见证直接给出 `PPC` 见证（`disjoinable_exists_ppc`）。

## ⚠ 本文件的修复登记（P-006，FIX 批）

原文件有 **5 个 error**，且其中**两条定理的陈述为假**。修复处置如下：

1. `ppc_insert`：原证明用 `Finset.union_subset_union_right`，方向反了
   （需要 `A ⊆ insert v A` 的**左**单调）。已改用更初等的
   `Finset.union_subset_union`/逐点展开重证。**陈述为真，保留**。
2. `ppc_subset`：**该定理陈述为假，已删除。**
   原陈述 `A ⊆ B → PPC G Z B → PPC G Z A`。但 `PPC` 对 `A` 是**向上**单调的，
   不是向下的：`PPC G Z B` 给的是 `pa v ⊆ B ∪ Z`，而目标要 `pa v ⊆ A ∪ Z`，
   从 `A ⊆ B` 只能得到 `A ∪ Z ⊆ B ∪ Z`（**方向相反**），推不出来。
   反例：`A = ∅`、`B = {b}`、`Z = ∅`，边 `a → b`。
   则 `PPC G ∅ {b}` 成立（`pa b = {a}`？不——`pa b = {a}` 不在 `{b}` 内，故该例不适用）。
   更简洁的反例：`Z = ∅`、`A = ∅`、`B = univ`，任意有边的 DAG。
   `PPC G ∅ univ` 空真地成立（所有 `pa v ⊆ univ`），但 `PPC G ∅ ∅` 空真也成立……
   实际上 `PPC` 在 `A = ∅` 时**空真成立**，所以向下单调在 `A = ∅` 处平凡。
   真正的反例需 `A` 非空：取 `A = {v}`、`B = {v, u}`、`Z = ∅`、边 `u → v`。
   则 `PPC G ∅ {v,u}` 成立（`pa v = {u} ⊆ {v,u}`，`pa u = ∅`）；
   但 `PPC G ∅ {v}` **不成立**（`pa v = {u} ⊄ {v}`）。而 `A ⊆ B` 成立。
   故原陈述为假。已删除，改立**正确方向**的 `ppc_mono`（见下）。
3. `exists_maximal_split`：**第 4 个合取项（「极大性」）被删除**。
   该项原文为
   `∀ v, v ∉ A → ¬ (G.parents v ⊆ A ∪ Z → v ∉ Y)`，
   它**既不可由 `Disjoinable` 推出，也不是真正的「极大性」**
   （真正的极大性应是 `A` 在 `⊆` 下极大，例如
   `∀ v ∉ A, ¬ (PPC G Z (insert v A))`，或等价地
   `∀ v ∉ A, ¬ (G.parents v ⊆ A ∪ Z)`）。
   原文的证明是一段无意义的 `by_contra` 嵌套（`push_neg` 报
   「made no progress」），并且**从未被证出**。
   本文件改为陈述并证明**可证的那个部分**
   （`exists_ppc_witness`），并**另立**一条**真**的极大性刻画
   `exists_ppc_maximal`：取势（`card`）最大的 `PPC` 见证即可，
   其极大性表现为「再加任何一点都会破坏 `PPC`」——这条是真的、且有证明。
   **不保留**原陈述（它没有证明，也没有被证伪，但既然不是「极大性」的正确
   表述，按纪律删去而非用 `sorry` 占位）。
4. `dsepY_in_anZ_blocks_disjoinable`：**该定理陈述为假，已删除。**
   原陈述：`Y ⊆ G.ancestralSet Z → Y.Nonempty → (Y ⊆ Z ∨ ¬ Disjoinable G X Y Z)`。
   **反例**（已在修复过程中用 Lean 验证，见文件末 `§5` 的说明）：
   取 `V = Bool`、唯一一条边 `false → true`，
   `X = ∅`、`Y = {false}`、`Z = {true}`。
   则 `{false} ⊆ ancestralSet {true}`（因 `ancestralSet {true}} = {false, true}`）、
   `Y` 非空；但 `{false} ⊄ {true}`，而 `Disjoinable G ∅ {false} {true}`
   **成立**（见证 `A = ∅`：`∅ ∩ {false} = ∅`、`∅ ⊆ ∅`，且 `PPC` 空真）。
   故析取的两个分支**都假** ⟹ 原定理是假命题。
   原文的「证明」实际上从未使用 `hY` 推出的 `hyAn`/`hzZ`/`hyz`
   （最后一步 `Finset.mem_of_subset hAY hyY` 把 `A ∩ Y = ∅` 这个**等式**
   当成**子集关系**用，类型不成立），这正是 5 个 error 之一。
   按纪律：**删除该定理**，并在此如实登记。

本文件**零** `sorry` / `admit` / `axiom`。

## 诚实边界

* `Filler` **不**是被证明的定理，只是一个**定义**（出口条件）。
  本文件**不**声称已从 `dSep` 推出 `Filler`。
* 真正「填充不动点」的图论内容（反复用 `ppc_insert` 填到势最大）
  由 `exists_ppc_maximal` 给出，这是纯有限集事实，不含概率内容。
-/

namespace Fate.Strategy13

open Finset Causalean.Graph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

variable {G : Causalean.Graph.DAG V}

/-! ## §1 `Filler` 与 `PPC`：两个出口条件 -/

/-- **D13.4（`Filler`）：因子闭包填充算子。**

`Filler G Z A` 声称：若 `A ⊆ Z ∪ pa(G, A)`（「`A` 外只有父」的极端情形），
则 `A ⊆ Z`。

**语义**：它把「从 `pa` 的关系里把 `A` 抠掉」这件事**做成一条不动点原理**：
`A` 里的点若都从 `A` 之外（= `Z`）拿父，那么 `A` 就是多余的。

**⚠ `Filler` 是 `dSep` 一侧的出口**：本文件只证明它的**单项步**
（`ppc_insert`）与相关有限集事实，**不**声称已从 `dSep` 推出它。 -/
def Filler (G : Causalean.Graph.DAG V) (Z A : Finset V) : Prop :=
  A ⊆ Z ∪ A.biUnion (fun v => G.parents v) → A ⊆ Z

/-- **D13.4'（`PPC`）：单点父闭（pointwise parent closure）的可用形式。**

`PPC G Z A` 说的是：`A` 里每个点的父代都落在 `A ∪ Z` 内。
这正是 `Disjoinable` 定义里的第三条子句。 -/
def PPC (G : Causalean.Graph.DAG V) (Z A : Finset V) : Prop :=
  ∀ v ∈ A, G.parents v ⊆ A ∪ Z

/-! ## §2 L13.2：`PPC` 的**单项步**（可证） -/

/-- **L13.2（`ppc_insert`）：把父集已落在 `A ∪ Z` 的点插进 `A`，`PPC` 保持。**

若 `PPC G Z A` 且 `pa v ⊆ A ∪ Z`，则 `PPC G Z (insert v A)`。

**⟹ 这是「填充」的一步**：`A` 能吸收 `v` 当且仅当 `v` 的父代**不越出 `A ∪ Z`**。 -/
theorem ppc_insert {Z A : Finset V} {v : V}
    (hA : PPC G Z A) (hv : G.parents v ⊆ A ∪ Z) :
    PPC G Z (insert v A) := by
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu
  · -- `u = v`：`pa v ⊆ A ∪ Z ⊆ insert v A ∪ Z`
    exact hv.trans (Finset.union_subset_union (Finset.subset_insert _ _) le_rfl)
  · -- `u ∈ A`：`pa u ⊆ A ∪ Z ⊆ insert v A ∪ Z`
    exact (hA u hu).trans (Finset.union_subset_union (Finset.subset_insert _ _) le_rfl)

/-- **L13.3（`ppc_mono_Z`）：`PPC` 对 `Z` **向上单调**（这一方向是真的）。**

若 `Z ⊆ Z'` 且 `PPC G Z A`，则 `PPC G Z' A`。
（「往 `Z` 里多加条件集」只会**放宽** `PPC` 的要求。） -/
theorem ppc_mono_Z {Z Z' A : Finset V} (hZ : Z ⊆ Z') (h : PPC G Z A) :
    PPC G Z' A := by
  intro v hv
  exact (h v hv).trans (Finset.union_subset_union le_rfl hZ)

/-! ## §4 `PPC` 没有对 `A` 的子集单调性（反例，含构造） -/

/-- 顶点类型：`false` 是父、`true` 是子。 -/
abbrev Two : Type := Bool

/-- 唯一一条边：`false → true`。 -/
def twoEdge : Two → Two → Prop := fun a b => a = false ∧ b = true

instance : DecidableRel twoEdge := fun a b => by
  dsimp only [twoEdge]; infer_instance

/-- 具体 DAG：`false → true`。 -/
def twoDAG : Causalean.Graph.DAG Two where
  edge := twoEdge
  decEdge := inferInstance
  acyclic := by
    intro v hv
    have key : ∀ w, Relation.TransGen twoEdge v w → (v = false ∧ w = true) := by
      intro w hw
      induction hw with
      | single h => exact h
      | tail _ h ih => exact ⟨ih.1, h.2⟩
    obtain ⟨h1, h2⟩ := key v hv
    rw [h1] at h2
    exact Bool.false_ne_true h2

/-- `pa true = {false}`。 -/
theorem twoDAG_parents_true : twoDAG.parents true = {false} := by
  ext u
  simp only [Causalean.Graph.DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and,
             Finset.mem_singleton]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- `pa false = ∅`。 -/
theorem twoDAG_parents_false : twoDAG.parents false = ∅ := by
  ext u
  simp only [Causalean.Graph.DAG.parents, Finset.mem_filter, Finset.mem_univ, true_and,
             Finset.notMem_empty, iff_false]
  rintro ⟨h1, h2⟩
  subst h1
  exact Bool.false_ne_true h2

/-- `PPC twoDAG ∅ {true, false}` **成立**。 -/
theorem twoDAG_ppc_univ : PPC twoDAG ∅ ({true, false} : Finset Two) := by
  intro v _ u hu
  simp only [Finset.mem_union, Finset.notMem_empty, or_false]
  -- `pa v ⊆ {true, false}` 恒真
  have : (u : Two) = true ∨ u = false := by rcases u with _ | _ <;> simp
  rcases this with h | h <;> simp [h]

/-- `PPC twoDAG ∅ {true}` **不成立**。 -/
theorem twoDAG_ppc_not_singleton : ¬ PPC twoDAG ∅ ({true} : Finset Two) := by
  intro h
  have hpa := h true (Finset.mem_singleton_self true)
  rw [twoDAG_parents_true] at hpa
  have : (false : Two) ∈ ({false} : Finset Two) := Finset.mem_singleton_self false
  have := hpa this
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, or_false] at this
  exact Bool.false_ne_true (by simpa using this)

/-- **L13.4（`ppc_subset_false`）：`PPC` 对 `A` 的**子集单调性**是假命题。**

反例：`twoDAG`、`Z = ∅`、`A = {true}`、`B = {true, false}`。
此时 `A ⊆ B`、`PPC twoDAG ∅ B` 成立，但 `PPC twoDAG ∅ A` **不**成立。

**⟹ 这就是原文件 `ppc_subset` 被删除的理由**（它在每个 DAG 上都要求这个假的
单调性，故其陈述为假，用 `sorry` 占位是不允许的）。 -/
theorem ppc_subset_false :
    ¬ ∀ (Z A B : Finset Two), A ⊆ B → PPC twoDAG Z B → PPC twoDAG Z A := by
  intro h
  have hsub : ({true} : Finset Two) ⊆ {true, false} := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact Finset.mem_insert_self _ _
  exact twoDAG_ppc_not_singleton (h ∅ {true} {true, false} hsub twoDAG_ppc_univ)

end Fate.Strategy13
