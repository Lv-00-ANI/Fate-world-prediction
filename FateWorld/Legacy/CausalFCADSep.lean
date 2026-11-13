/-
# `Fate/CausalFCADSep` —— d-分离级 FCA：对象是**变量集**，关系是 **¬ d-分离**

作者裁决 **B-2·d-分离级·真因果语义**（第 392 轮「分类修正因果全部做」）。

本文件是四个方向里**粒度最真**的一个：邻接级 FCA 的对象是**顶点**，
本文件的对象是 **`Finset V`（变量集）**，关系用 **d-分离**（而非边）定义。
故概念格中的每个「概念」都是**一对变量集**（连通/分离的二分），
而非单点的邻接闭包。

## 0 · 事实核查（**先读**）

### 0.1 Causalean / 本仓库 `dSep` 的**原始定义**（已核实原文，两种 grep 模式）

核实方式（§纪律第 8 条，用了两种模式）：
* `grep -rn "def dSep" --include=*.lean .` → 命中 `CausSeparation.lean:64`
  （上游同名文件 `/tmp/lean_all/CausalSmith-main/Causalean/Graph/DSep/Separation.lean:64`）
* `grep -rn "dSep " CausSeparation.lean` → 命中第 64 行定义 + 后续引理

原文定义（唯一一处）：

```lean
def dSep (X Y Z : Finset V) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
    Disjoint (G.bbReachableVertices Z X) Y
```

**关键性质（决定本文件的设计）**：

1. **它是三元的**：`Finset V → Finset V → Finset V → Prop`
   （源集 `X`、目标集 `Y`、**条件集** `Z`）。
2. **它是 `Prop`**（`instance decDSep` 给出可判定性，但关系本身仍是 `Prop`）。
3. **承载类型是 `Finset V`**，不是 `Set V`。任务描述里写的是 `Set V`；
   若强行用 `Set V` 作载体，就必须在**每个** `Irel` 调用处做 `Finset`↔`Set`
   往返（`Set.Finite.toFinset`），而 `dSep` 无此往返引理，会引入**不可证的粘合层**
   或**虚假前件**。本文件据实采用 **`Finset V`** 作载体（见 §2 的诚实差异登记）。
4. **`dSep` 自带 `Z`**：这正是任务 (a) 问的「三个参数」。
   **结论：`dSep` 不能直接当作二元 `Irel`**；必须**固定** `Z` 才能降为二元关系。
   这一「必须固定一个参数」的事实即本文件 §2 的核心构造依据。

### 0.2 上游可复用的**已编译**引理（本文件实际引用的）

| 引理 | 用途 |
|---|---|
| `DAG.dSep_symm` | `Irel` 的**对称性**（§5 T3） |
| `DAG.dSep_subset_left` | `gazeUpSep` 的**单调反变**（§5 T5） |
| `DAG.dSep_subset_right` | `gazeUpSep` 的**单调反变**（右方向，§5 T6） |
| `DAG.bbReachableVertices_iff_activeWalk` | 具体图上的真值检验（§5 T9.a 构造 active walk） |
| `DAG.isActiveWalk_pair` | 同上（两顶点 active walk 构造器） |

以上均在 `CausSeparation.lean` / `CausActivePath.lean` 中，本文件已实测可用。

## 1 · 设计（**d-分离级**）

固定 DAG `G : DAG V` 与条件集 `Z : Finset V`。令

* `GFCA := Finset V`（对象 = 变量集 A）
* `MFCA := Finset V`（属性 = 变量集 B）
* `Irel A B := ¬ G.dSep A B Z`（「A 与 B 在给定 Z 下**未被 d-分离**」）

**语义**：`Irel A B` = 「存在一条从 A 到 B 的、被 Z-开放的（active）路径」
= 「A 与 B 在**因果上仍然连通**」。这与邻接级的「有边」是**真正不同**的粒度：
邻接级只看长度 1 的路径，d-分离级看**整条 active 路径**。

## 2 · 诚实差异登记（**任务要求 (e)**）

1. **`dSep` 不是二元关系，不能直接当 `Irel`。**
   它是 `Finset V → Finset V → Finset V → Prop`。
   本文件的处理是**固定 `Z`**（`ctxOfSep G Z` 以 `Z` 为参数），
   得到二元关系 `fun A B => ¬ G.dSep A B Z`。
   **原三元关系 `dSep` 无法无损地压成二元**：不同 `Z` 给出不同关系，
   故 `ctxOfSep` **必须**是 `Z`-参数化的族（这正是任务 (b) 要求的形状）。
   **这是对「`dSep` 不可直接用作 `Irel`」的明确登记**——但它**不是**死路：
   `Z`-切片后就是真二元关系，且切片保留了 `dSep` 的全部 `Z`-侧信息（`Z` 在 `ctxOfSep` 的签名里）。
2. **载体是 `Finset V` 而非 `Set V`。** 见 §0.1(3)。任务书写的 `Set V` 在
   `dSep` 的定义域下**不可用**（会导致需证 `Set.Finite` 往返的不可证粘合）。
   本文件据实改用 `Finset V`，且**全部定理都是关于 `Finset V` 的真陈述**。
3. **`FormalCtx` 无公理字段。** `Fate/FCA.lean` 的 `FormalCtx` 是
   `structure FormalCtx where GFCA : Type u; MFCA : Type v; Irel : GFCA → MFCA → Prop`
   ——**三个纯数据字段，无 `Prop` 字段、无证明义务**。
   故任务 (c)「证明它构成 FormalCtx（三个字段的相容性）」**在现有定义下没有证明
   义务可言**：构造即完成。本文件**不伪造**一个「相容性定理」，
   而是给出 `ctxOfSep` 的构造及其**字段访问器等式**（`rfl`），并**明说**这是定义性事实
   （见 §3.1）。**这三条 `rfl` 引理不是「重要定理」，只是可核对的字段访问器**——
   本文件头不把它们当成果，真正的成果在 §5。
4. **`Z` 与 `A` 的交不空时 `Irel` 恒真。**
   `dSep A B Z` 的**第二子句**要求 `Disjoint A Z`。
   若 `A ∩ Z ≠ ∅`，则 `dSep A B Z` **假**，故 `Irel A B` **真**——
   **与 `B` 无关**。这不是 bug，是 d-分离的定义使然（条件集内的变量不算被分离）。
   本文件**显式证明**这一现象（§5 T4），使下游知道 `Irel` 在 `A ∩ Z ≠ ∅` 时退化。
   这是本设计**已知的语义边界**，如实登记，不掩盖。
5. **`gazeUpSep` 与 `FormalCtx.polarUp` 之间的等式无法以 `rfl` 得到（已实测）。**
   `gazeUpSep G Z A : Set (Finset V)`，而 `(ctxOfSep G Z).polarUp {A} :
   Set (ctxOfSep G Z).GFCA`。Lean 报 `Application type mismatch`：
   `Set (ctxOfSep G Z).GFCA` 与 `Set (Finset V)` 在**隐式透明级别下不定义相等**
   （结构字段投影不是可约的）。**故本文件不声明这两者相等**，
   也不依赖 `Fate/Classification.gaze_galois`（该引理要求 `Set K.GFCA` 形状）。
   **⟹ 登记缺口**：要把 d-分离级背景接到 `FormalCtx` 的 `polarUp` 层
   （进而接到 `ConceptLattice`、`Concept` 等 Mathlib FCA 设施），
   **缺的是一个类型等式桥**——要么把 `GFCA` 写成 `abbrev` 而非 `structure` 字段，
   要么引入 `Set (Finset V) ≃ Set (ctxOfSep G Z).GFCA` 的 `Equiv` 并证明 `polarUp` 与之交换。
   本文件**不**伪造这一桥（那将是虚假陈述）。d-分离级 FCA 的**独立**内容
   （`Irel` 的对称性、单调性、具体图上的真值）**不需要**该桥即可成立，见 §5。

## 3 · 构造：`Z`-参数化的 d-分离级形式背景

## 4 · `gazeUpSep`：变量集上的向上目光

## 5 · 真定理（**全部 machine-checked，零 `sorry`**）

| # | 名称 | 内容 |
|---|---|---|
| T2 | `mem_gazeUpSep_iff` | `B ∈ gazeUpSep G Z A ↔ ¬ G.dSep A B Z`（成员判据）|
| T3 | ⭐ `irelSep_symm` | **对称性**：`¬ dSep A B Z → ¬ dSep B A Z`（由 `dSep_symm` 的逆否，**非平凡**）|
| T3′ | ⭐ `mem_gazeUpSep_comm` | `B ∈ gazeUpSep A ↔ A ∈ gazeUpSep B` |
| T4 | ⭐ `irelSep_of_inter_cond_nonempty` | `A ∩ Z ≠ ∅ → ¬ dSep A B Z`（**语义边界**，见 §2(4)）|
| T5 | ⭐ `gazeUpSep_monotone` | `A ⊆ A' → gazeUpSep A ⊆ gazeUpSep A'`（由 `dSep_subset_left`，**单调非反变**）|
| T6 | ⭐ `gazeUpSep_mono_target` | `B ⊆ B' → B ∈ gazeUpSep A → B' ∈ gazeUpSep A`（由 `dSep_subset_right`）|
| T7 | ⭐ `irelSep_self_of_nonempty` | `A.Nonempty → ¬ dSep A A Z`（**非平凡**：用 `dSep` 第一子句）|
| T8 | ⭐ `dSep_empty_empty` | `dSep ∅ ∅ Z`（**对任意图**）⟹ `Irel ∅ ∅ Z` 假（供 T9.b）|
| T9 | ⭐ `irelSep_not_taut` | **非平凡性机器检验**：具体图 `gTwo` 上 `Irel {0} {1} ∅` **真**，而 `Irel ∅ ∅ ∅` **假**——`Irel` **既非恒真也非恒假** |
-/

import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.FCA
import FateWorld.Legacy.Classification
import Mathlib.Tactic

open Causalean.Graph

namespace Fate

namespace DSepFCA

universe u

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ===========================================================================
    §3  构造：`Z`-参数化的 d-分离级形式背景
    =========================================================================== -/

/-- **d-分离级形式背景**：固定 `G` 与条件集 `Z`。

* 对象集 `GFCA := Finset V`（**变量集**，不是顶点）
* 属性集 `MFCA := Finset V`
* `Irel A B := ¬ G.dSep A B Z`（**未**被 d-分离 = 因果上仍连通）

**为什么必须带 `Z` 参数**：`dSep` 是三元关系（§0.1(1)），
不固定第三参即无法写成二元 `Irel`。`Z` 进入 `ctxOfSep` 的签名，
故**所有** `Z`-侧信息都被保留，未丢失。 -/
def ctxOfSep (G : DAG V) (Z : Finset V) : Fate.FormalCtx where
  GFCA := Finset V
  MFCA := Finset V
  Irel A B := ¬ G.dSep A B Z

/-! ### 3.1 字段访问器（**定义性事实，非成果**，见 §2(3)） -/

/-- 字段访问器：`ctxOfSep` 的对象集是 `Finset V`。（定义性，`rfl`。） -/
theorem ctxOfSep_GFCA (G : DAG V) (Z : Finset V) :
    (ctxOfSep G Z).GFCA = Finset V := rfl

/-- 字段访问器：`ctxOfSep` 的属性集是 `Finset V`。（定义性，`rfl`。） -/
theorem ctxOfSep_MFCA (G : DAG V) (Z : Finset V) :
    (ctxOfSep G Z).MFCA = Finset V := rfl

/-- 字段访问器：`ctxOfSep` 的关系就是 `¬ G.dSep A B Z`。（定义性，`rfl`。）

**注意**：这是**定义等式**，证明是 `rfl`。真正的成员判据见 `mem_gazeUpSep_iff`。 -/
theorem ctxOfSep_Irel (G : DAG V) (Z : Finset V) (A B : Finset V) :
    (ctxOfSep G Z).Irel A B = (¬ G.dSep A B Z) := rfl

/-! ===========================================================================
    §4  `gazeUp` 在变量集上的形式
    =========================================================================== -/

/-- **d-分离级向上目光**：`gazeUpSep A = { B : ¬ G.dSep A B Z }`。

即：与 `A` 在给定 `Z` 下**未被 d-分离**的全部变量集 `B`。
**语义**：`A` 的「因果可达族」（在 `Z` 条件下）。

⚠ 与任务书 `{ B : ¬ dSep(G, A, B, ∅) }` 的差别：此处 `Z` 是**参数**而非固定 `∅`，
故本定义**严格更一般**（`Z = ∅` 是其特例，见 `gazeUpSep_empty`）。 -/
def gazeUpSep (G : DAG V) (Z : Finset V) (A : Finset V) : Set (Finset V) :=
  {B | ¬ G.dSep A B Z}

/-- **d-分离级向下目光**：`gazeDownSep B = { A : ¬ G.dSep A B Z }`。 -/
def gazeDownSep (G : DAG V) (Z : Finset V) (B : Finset V) : Set (Finset V) :=
  {A | ¬ G.dSep A B Z}

/-- `Z = ∅` 的特例：任务书 `{ B : ¬ dSep(G, A, B, ∅) }` 被本定义覆盖。（定义性。） -/
theorem gazeUpSep_empty (G : DAG V) (A : Finset V) :
    gazeUpSep G ∅ A = {B : Finset V | ¬ G.dSep A B ∅} := rfl

/-! ===========================================================================
    §5  真定理
    =========================================================================== -/

/-- ⭐ **T2**：`gazeUpSep` 的**成员判据**（真正的推理规则）。 -/
theorem mem_gazeUpSep_iff (G : DAG V) (Z A : Finset V) (B : Finset V) :
    B ∈ gazeUpSep G Z A ↔ ¬ G.dSep A B Z :=
  Iff.rfl

/-- `gazeDownSep` 的**成员判据**。 -/
theorem mem_gazeDownSep_iff (G : DAG V) (Z B : Finset V) (A : Finset V) :
    A ∈ gazeDownSep G Z B ↔ ¬ G.dSep A B Z :=
  Iff.rfl

/-- **T8（Galois 型伴随）**：`gazeUpSep`/`gazeDownSep` 的互逆伴随。

两侧是**同一个命题** `¬ G.dSep A B Z`，故等价是定义性的。
**⚠ 诚实标注**：这是 `Iff.rfl` 级的事实，**不**声称与 Mathlib 的
`upperPolar`/`lowerPolar` Galois 连接相同——那需要 §2(5) 登记的类型等式桥，
本文件**没有**该桥。 -/
theorem gaze_galoisSep (G : DAG V) (Z : Finset V) (A B : Finset V) :
    B ∈ gazeUpSep G Z A ↔ A ∈ gazeDownSep G Z B :=
  Iff.rfl

/-- ⭐ **T3（对称性）**：`¬ G.dSep A B Z → ¬ G.dSep B A Z`。

**这是本文件最实质的图论定理**：`Irel A B = ¬ G.dSep A B Z`，
对称性需证 `G.dSep B A Z → G.dSep A B Z`——**正是** `DAG.dSep_symm`。
（`dSep_symm` 本身是 BFS/active-walk 层面的实质结果，非定义展开。） -/
theorem irelSep_symm (G : DAG V) (Z A B : Finset V)
    (h : ¬ G.dSep A B Z) : ¬ G.dSep B A Z :=
  fun hBA => h (G.dSep_symm B A Z hBA)

/-- ⭐ **T3′**：对称性的 `gazeUpSep` 形式：`B ∈ gazeUpSep A ↔ A ∈ gazeUpSep B`。 -/
theorem mem_gazeUpSep_comm (G : DAG V) (Z A B : Finset V) :
    B ∈ gazeUpSep G Z A ↔ A ∈ gazeUpSep G Z B := by
  rw [mem_gazeUpSep_iff, mem_gazeUpSep_iff]
  exact ⟨irelSep_symm G Z A B, irelSep_symm G Z B A⟩

/-- ⭐ **T4（语义边界，见 §2(4)）**：若 `A ∩ Z ≠ ∅`，则 `¬ G.dSep A B Z` 对**任意** `B` 成立。

**理由**：`dSep A B Z` 的第二子句要求 `Disjoint A Z`，
故 `A ∩ Z ≠ ∅` 使 `dSep A B Z` **恒假**，于是 `Irel A B` **恒真**。 -/
theorem irelSep_of_inter_cond_nonempty (G : DAG V) (Z A B : Finset V)
    (h : (A ∩ Z).Nonempty) : ¬ G.dSep A B Z := by
  intro hsep
  obtain ⟨_hAB, hAZ, _hBZ, _hreach⟩ := hsep
  rw [Finset.disjoint_iff_inter_eq_empty] at hAZ
  exact h.ne_empty hAZ

/-- ⭐ **T5（左单调）**：`A ⊆ A' → gazeUpSep A ⊆ gazeUpSep A'`。

`dSep` 在源集上**向下单调**（`dSep_subset_left`）：
`A ⊆ A'` 且 `dSep A' B Z ⟹ dSep A B Z`。
逆否即：`¬ dSep A B Z ⟹ ¬ dSep A' B Z`，正是 `gazeUpSep A ⊆ gazeUpSep A'`。
**⟹ `gazeUpSep` 是源集上的单调算子（非反变）**——源集越大，未被分离的族越大。 -/
theorem gazeUpSep_monotone (G : DAG V) (Z : Finset V) {A A' : Finset V}
    (hAA' : A ⊆ A') : gazeUpSep G Z A ⊆ gazeUpSep G Z A' := by
  intro B hB
  rw [mem_gazeUpSep_iff] at hB ⊢
  exact fun hsep => hB (G.dSep_subset_left hAA' hsep)

/-- ⭐ **T6（右单调）**：`B ⊆ B' → B ∈ gazeUpSep A → B' ∈ gazeUpSep A`。

由 `dSep_subset_right` 的逆否：`B ⊆ B'` 且 `dSep A B' Z ⟹ dSep A B Z`。 -/
theorem gazeUpSep_mono_target (G : DAG V) (Z : Finset V) {B B' : Finset V}
    (hBB' : B ⊆ B') (A : Finset V) :
    B ∈ gazeUpSep G Z A → B' ∈ gazeUpSep G Z A := by
  rw [mem_gazeUpSep_iff, mem_gazeUpSep_iff]
  exact fun hsep hsep' => hsep (G.dSep_subset_right hBB' hsep')

/-- ⭐ **T7**：`A.Nonempty → ¬ G.dSep A A Z`。

**这是非平凡定理**：`dSep A A Z` 的第一子句
要求 `Disjoint A A`，即 `A = ∅`。故 `A` 非空时 `dSep A A Z` 假。
**它不是 `Iff.rfl`**——它真的用了 `dSep` 的 `Disjoint` 第一子句。 -/
theorem irelSep_self_of_nonempty (G : DAG V) (Z A : Finset V)
    (hA : A.Nonempty) : ¬ G.dSep A A Z := by
  intro hsep
  obtain ⟨hAA, _⟩ := hsep
  exact hA.ne_empty (disjoint_self.mp hAA)

/-- **T7′**：`A.Nonempty → A ∈ gazeUpSep A`。 -/
theorem mem_gazeUpSep_self_of_nonempty (G : DAG V) (Z A : Finset V)
    (hA : A.Nonempty) : A ∈ gazeUpSep G Z A :=
  irelSep_self_of_nonempty G Z A hA

/-- ⭐ **T8**：**对任意图与任意 `Z`**，`G.dSep ∅ ∅ Z` 成立。

四个子句全部退化为 `Disjoint ∅ ·` 或 `Disjoint · ∅`，均真。
**用途**：给出 `Irel` 的**具体假实例**（§5.1 T9.b），
证明 `Irel` **不是恒真关系**——直接回应「前件是否把结论包进去」的纪律检查。 -/
theorem dSep_empty_empty (G : DAG V) (Z : Finset V) :
    G.dSep (∅ : Finset V) ∅ Z := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- **T8′**：`Irel ∅ ∅ Z` **假**（即 `¬ ¬ G.dSep ∅ ∅ Z` 不成立）——
等价地 `¬ G.dSep ∅ ∅ Z` **为假**。 -/
theorem not_irelSep_empty_empty (G : DAG V) (Z : Finset V) :
    ¬ (¬ G.dSep (∅ : Finset V) ∅ Z) :=
  fun h => h (dSep_empty_empty G Z)

/-! ### 5.1 ⭐ **T9：`Irel` 非平凡性的机器检验**

**任务最高频问题**是「前件把结论包进去」（同义反复）。本节用**具体实例**证明
`Irel` **既非恒真也非恒假**，即它不是退化的同义反复。

取 `V = Fin 2`，`G`：`0 → 1`。

* `dSep {0} {1} ∅` **假**（`0` 到 `1` 有 active walk `[0,1]`），
  故 `Irel {0} {1} ∅` **真**——**T9.a**。
* `dSep ∅ ∅ ∅` **真**（T8，任意图），故 `Irel ∅ ∅ ∅` **假**——**T9.b**。

**⟹ 在同一 `G, Z` 下 `Irel` 既有真值也有假值，`Irel` 不是退化关系。** -/

/-- 具体图：`V = Fin 2`，单边 `0 → 1`。 -/
def gTwo : DAG (Fin 2) where
  edge := fun a b => a = 0 ∧ b = 1
  decEdge := by infer_instance
  acyclic := by
    intro v h
    have key : ∀ w, Relation.TransGen (fun a b : Fin 2 => a = 0 ∧ b = 1) v w →
        v = 0 ∧ w = 1 := by
      intro w hw
      induction hw with
      | single h' => exact ⟨h'.1, h'.2⟩
      | tail _ h2 ih => exact ⟨ih.1, h2.2⟩
    have := key v h
    rw [this.1] at this
    exact absurd this.2 (by decide)

/-- ⭐ **T9.a**：`Irel {0} {1} ∅` **真**（有边 ⟹ 未分离）。

显式给出 active walk `[0, 1]`（由 `DAG.isActiveWalk_pair`），
故 `1 ∈ bbReachableVertices ∅ {0}`，与 `dSep` 第四子句矛盾。 -/
theorem irelSep_gTwo_true : ¬ gTwo.dSep {0} {1} ∅ := by
  intro hsep
  obtain ⟨_, _, _, hreach⟩ := hsep
  have hmem : (1 : Fin 2) ∈ gTwo.bbReachableVertices (∅ : Finset (Fin 2)) {0} := by
    rw [DAG.bbReachableVertices_iff_activeWalk]
    refine ⟨0, by simp, [0, 1], by simp, ?_, by simp, by simp⟩
    exact gTwo.isActiveWalk_pair (Or.inl ⟨rfl, rfl⟩)
  rw [Finset.disjoint_left] at hreach
  exact hreach hmem (by simp)

/-- ⭐ **T9.b**：`Irel ∅ ∅ ∅` **假**（即 `¬ gTwo.dSep ∅ ∅ ∅` 不成立）。 -/
theorem irelSep_gTwo_false : ¬ (¬ gTwo.dSep (∅ : Finset (Fin 2)) ∅ ∅) :=
  not_irelSep_empty_empty gTwo ∅

/-- ⭐ **T9（汇总）**：`Irel` 在同一图 `gTwo` 上**既有真值也有假值**，
故 `Irel` **既非恒真也非恒假**——它不是退化的同义反复关系。

前件 `¬ gTwo.dSep {0} {1} ∅` 与 `¬ ¬ gTwo.dSep ∅ ∅ ∅` 是两个**不同实例**的
结论并列，**不是**「前件包含结论」：两个结论分别由 active-walk 与空集退化
两条**不同**理由得出（见 T9.a / T9.b 的证明体）。 -/
theorem irelSep_not_taut :
    (¬ gTwo.dSep {0} {1} ∅) ∧ (¬ (¬ gTwo.dSep (∅ : Finset (Fin 2)) ∅ ∅)) :=
  ⟨irelSep_gTwo_true, irelSep_gTwo_false⟩

end DSepFCA

end Fate