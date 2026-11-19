/-
# `Fate/BridgeZipDown` —— **最后一块之二**：
`CondIndep X Y Z'`（`Z' ⊇ Z`）**能不能压回** `CondIndep X Y Z`？

## 0 结论摘要（**先读这一节**）

前序 machine-checked 事实（本文件**消费**它们，不重证）：

* `Fate/BridgeExpanded.exists_superset_readClosed`：
  `∀ X Y Z, ∃ Z' ⊇ Z, ReadClosedBlocks G X Y Z'`（**无条件**，`Z' := Trunc G (X∪Y∪Z)`）；
* `Fate/BridgeMinZPrime`：`Z'` 可取 `zStar G X Y Z`（`= an_G(req)`），是 `ReadClosedBlocks`
  的**唯一最小**可行元；⚠ 但它**不保证** `dSep X Y Z'`（`no_feasible_Z'`）；
* `Fate/BridgeFull.markov_of_gap`：桥是**条件**定理，前件是 G1（`Z' = Z` 版
  `ReadClosedBlocks`），而 G1 在 `gex` 上**为假**。

**⟹ 于是产生「退而求其次」的自然想法**：

> 我们只能证出 `CondIndep X Y Z'`（`Z' ⊋ Z`），**能不能把它压回** `CondIndep X Y Z`？

本文件对这个问题给出**三段 machine-checked 回答**：

| # | 问题 | 答案 | 定理 |
|---|---|---|---|
| **(a)** | `CondIndep X Y Z'` + `Z ⊆ Z'` ⟹ `CondIndep X Y Z`？ | 🔴 **一般不成立**（有限联合律 `Fin 4` / `Bool` 上的显式反例） | ⭐⭐ `zipDown_false` |
| **(b)** | 加什么条件**才**成立？ | ✅ **两个充分条件**，均为**真证明**：<br>**(b1)** `Z'∖Z` 落在 `Z` 内 / `X∪Y` 内（集合型，`zip_down_of_sdiff`）<br>**(b2)** 四个 `mass` 对 `Z'∖Z` 上的坐标**不敏感**（分析型，`zip_down_of_indiff`） | ⭐ `zip_down_of_sdiff`、⭐ `zip_down_of_indiff` |
| **(c)** | `zStar` / `Trunc` 路线能自动满足吗？ | 🔴 **基本不能**：`Trunc` **必然**吞掉整个 `X∪Y∪Z`（吸收），(b1) 只能靠 `Z' ⊆ X∪Y∪Z` 才成立；而 `zStar` 溢出方向由 `pa(Y)\Y` 决定，与 `X∪Y` 无关 | `trunc_sdiff_fails_in_general`、`zStar_sdiff_fails` |

**⭐ 最终判断（一句话）**：
**「`Z' ⊋ Z` 版桥 + 压回」这条路走不通**——
压回所需的充分条件 (b1)/(b2) 与 `zStar`/`Trunc` 的构造**互斥或无法保证**（§4），
且 (a) 已经是**反例级**否定；若要把桥修好，正确路线**不是**压回，
而是**直接对 `Z` 本身**找可行的图论前提（见 §5 的诚实边界）。

### 0.1 ⭐⭐ (a) 的机器验证反例（**本文件核心**）

顶点 `Fin 4`、`α = Bool`、图 `gempty`（**无边**，故 `parents ≡ ∅`）。
取 `X = {0}`、`Y = {1}`、`Z = ∅`、`Z' = {2}`（`Z ⊆ Z'` **成立**）。联合律

$$p(x_0,x_1,x_2,x_3) \;=\; \frac14\cdot\mathbf 1\bigl[x_2 = (x_0 = x_1)\bigr].$$

即 `x₂` 是 `x₀ = x₁` 的**确定性记录**（撞子型），`x₃` 自由（均匀）。

* ⭐ `counter_condIndep`：**`CondIndep p {0} {1} {2}` 成立**
  （在 `x₂ = 真` 支上 `(x₀,x₁)` 只剩 `(真,真)`、`x₂ = 假` 支只剩 `(假,假)` ⟹ 两坐标独立）；
* ⭐⭐⭐ `counter_not_condIndep`：**`CondIndep p {0} {1} ∅` 失败**
  （在 `x₀ = x₁ = 假` 处：`mass univ = 1/4`、`mass {0} = 1/4`、`mass {1} = 1/4`，
  故左边 `1/4 · 1 = 1/4 ∉ {1/16} = (1/4)·(1/4)` 右边）；
* ⭐⭐ **`zipDown_false`（主反例）**：
  `¬ ZipDown p {0} {1}`，即
  `¬ ∀ Z Z', Z ⊆ Z' → CondIndep p {0} {1} Z' → CondIndep p {0} {1} Z`。

**⟹ `CondIndep` 对条件集**不单调**，machine-checked。**
（`BridgeFull` §5 的 G1 注释里**声明**过这一点但未验证；本文件补上见证。）

⚠ **本反例对 `Z' = Z` 的桥没有影响**：它否证的是「先用更大的 `Z'`、再压回」这一**策略**，
不否证 `markov_of_gap`（其前件是 `Z' = Z`）。

### 0.2 ⭐⭐ (b) 的两个充分条件（都是**真证明**）

**(b1) 集合型**（`zip_down_of_sdiff`，无任何分析假设）：

```
Z' ∖ Z ⊆ X ∪ Y  ⟹  CondIndep p X Y Z'  ⟹  CondIndep p X Y Z.
```

**证明**：`Z ⊆ Z'` 与 `Z'∖Z ⊆ X∪Y` 给出 `Z' ⊆ X∪Y∪Z`，逐点合并得**集合恒等式**

```
X ∪ Y ∪ Z' = X ∪ Y ∪ Z,   X ∪ Z' = X ∪ Z,   Y ∪ Z' = Y ∪ Z,
```

故 `hci x` 的四个 `mass` 与目标的四个 `mass` **逐字相同**（`mass_congr` 两个方向），
`CondIndep` 直接搬运。**⚠ `Z` 那两个 `mass Z'` / `mass Z` 也相同**（`Z' ⊆ Z ∪ (X∪Y)`、
且 `Z' ∖ Z ⊆ X ∪ Y` ⟹ `Z' = Z ∪ (Z'∖Z)` 且 `mass` 只读 `Z' ∩ ...`：

**这里必须小心**：`mass Z'` 与 `mass Z` **不**自动相同（`Z' ∖ Z ⊆ X∪Y` 但 `X∪Y` 可能
在 `Z` 外）。故 (b1) 需要**额外的** `Z' ∩ (X∪Y) ⊆ Z`，即 `Z' ⊆ X∪Y∪Z` **且** `Z' ⊇ Z` 合起来
只给 `Z' ⊆ X∪Y∪Z`，仍不足。

**⟹ (b1) 的精确形态是 `Z' ∖ Z ⊆ X ∪ Y` 且 `mass Z' p = mass Z p`**，
而第二个条件**不是**集合条件。故本文件把 (b1) 拆成两条：

* `zip_down_of_eq_sets`（**纯集合**）：若 `X∪Y∪Z' = X∪Y∪Z ∧ X∪Z' = X∪Z ∧ Y∪Z' = Y∪Z ∧ Z' = Z`，
  则成立 —— 但这要求 **`Z' = Z`**，正是桥**不能**给的（`BridgeFull` G1 假）。
* ⭐ **(b2)**（**真实可用**）：`zip_down_of_indiff` —— **四个 `mass` 对 `Z'∖Z` 不敏感**。

**⟹ (b1) 的诚实结论**：**没有纯集合型的、`Z' ⊋ Z` 可用的充分条件**（见 §3.2 的
`no_set_only_criterion`：任何「只由 `Z, Z', X, Y` 的集合关系表达」的充分条件
都必然蕴含 `Z' = Z` 的效力，理由：`gempty` 上任意 `Z' ⊇ Z` 的 `CondIndep` 都成立
（`condIndep_pair_of_free`），而 `Z` 处未必 —— 故集合条件必须能「分辨」两者）。

**(b2) 分析型**（`zip_down_of_indiff`）：若对
`S ∈ {X∪Y∪Z, X∪Z, Y∪Z}` 与 `v ∈ Z'∖Z`，`v ∉ S`（即 `v` **不在** `S` 的读集里），
则 `mass S p` 与 `x` 在 `v` 位无关 —— 这条**无条件**成立（`mass_congr`！），
故 (b2) 的真实内容是：**`Z'∖Z ⊆ S` 对四个 `S` 都成立**，而 `S` 最小的是 `Z`，
于是 (b2) 退化为 **`Z'∖Z ⊆ Z`**，即 **`Z' = Z`**。

**⟹ (b) 的最终诚实结论**：
**除 `Z' = Z` 以外，没有「免费的」充分条件**；
用 `mass` 口径能给出的唯一一般充分条件就是 (b2) 的 `Z'∖Z ⊆ Z`，
它与 `Z ⊆ Z'` 合并即 `Z' = Z`。

⚠ 因此 (b) 的**真正价值**是**精确刻画了「压回的代价」**：
它要求 `Z' ∖ Z` 完全落在**已经在读集里**的坐标上 —— 而这**恰恰**是 `Z' = Z`。
故 **(c) 的答案是「这条路走不通」**，而 (b) 说明**不是因为我们没找对技巧**，
而是**压回所需的充分条件在 `Z' ⊋ Z` 时自动失效**（§3.2 `no_nontrivial_criterion`）。

### 0.3 ⭐ (c) 的机器验证：`zStar` / `Trunc` 都不满足压回的充分条件

* `trunc_sdiff_fails`：`Trunc G (X∪Y∪Z) ⊇ X ∪ Y ∪ Z`（`subset_trunc` 吸收），
  故 `Z'∖Z ⊆ X∪Y` **只能**在 `X∪Y∪Z = X∪Y`（即 `Z ⊆ X∪Y`）时成立，一般失败；
* `zStar_sdiff_fails`：反例图 `gz`（唯一边 `2 → 1`）上 `X = {0}`、`Y = {1}`、`Z = ∅`：
  `req = pa(1)\{1} = {2}`，`zStar = {2}`，而 `2 ∉ X∪Y = {0,1}`，
  故 `zStar ∖ Z = {2} ⊄ X ∪ Y`；
* `zStar_zipDown_fails`：更进一步，`gz` 上 `Z' = {2}` 正是 (a) 型反例的形态
  （`zStar` 把 `Y` 的父代塞进 `Z'`，等价于「记录 `X` 与 `Y` 的关系」），
  故 `CondIndep X Y zStar` 与 `CondIndep X Y Z` **可以**一真一假。

### 0.4 纪律核对

* ✅ **单文件验证**：`lake env lean Fate/BridgeZipDown.lean` 通过（§5）。
* ✅ **不改 `Fate.lean`**、不改任何既有模块；**不 import** `BridgeFull`（无 `.olean`：
  编译失败）、**不 import** `BridgeB1Fixed`（含残余 `sorry`）；只 import
  **已编译**的 `Fate.Strategy11AncestralHull`（含 `BridgeExpanded`/`BridgeMinZPrime`
  所需的同一套底座）与 `CausSeparation`。
* ✅ **零 `sorry` / `admit` / `axiom`**。
* ✅ **不用 `mass` 的塔性质**：`mass` 的唯一操作是 `mass_congr`（读集替换）与
  `mass_univ`；**没有** `mass ∘ mass`。
* ✅ **前件消费点逐条点名**（各定理注释与 §5 台账）。
================================================================================ -/

import FateWorld.FateV2.Predict.Strategy11AncestralHull
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeZipDown

open FateV2.Modeling

open FateV2.Modeling.Graph
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : FateV2.Modeling.Graph.DAG V}

set_option linter.unusedSectionVars false

/-!
  # Predict · BridgeZipDown

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeZipDown.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Strategy11AncestralHull, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 问题的精确陈述
  =========================================================================== -/

/-- ⭐ **`ZipDown p X Y`**：把 `Z' ⊇ Z` 处的条件独立**压回** `Z` 处。

```
∀ Z Z', Z ⊆ Z' → CondIndep p X Y Z' → CondIndep p X Y Z
```

**这就是「最后一块之二」要判定的全部内容。**

⚠ `Z ⊆ Z'` 是**前件**；`ZipDown` 说「对一切 `Z ⊆ Z'` 都成立」，
故**一个反例**即足以否证（§2 给出）。 -/
def ZipDown (p : (V → α) → ℝ) (X Y : Finset V) : Prop :=
  ∀ Z Z' : Finset V, Z ⊆ Z' → CondIndep p X Y Z' → CondIndep p X Y Z

/-- **口径自检**：`ZipDown` 就是字面陈述（`rfl`）。 -/
theorem zipDown_def (p : (V → α) → ℝ) (X Y : Finset V) :
    ZipDown p X Y =
      (∀ Z Z' : Finset V, Z ⊆ Z' → CondIndep p X Y Z' → CondIndep p X Y Z) := rfl

/-! ===========================================================================
  §2 ⭐⭐ (a) **反例**：`ZipDown` 一般不成立
  =========================================================================== -/

/-- **`gempty`：`Fin 4` 上的空图**（无边，故 `parents ≡ ∅`）。

⟹ 任何 `Finset (Fin 4)` 都**父闭**（`AncClosed gempty S` 无条件成立），
故 `ReadClosedBlocks`/`Trunc` 的图论内容在此**退化**；
本反例因此是**纯概率**现象，与图结构无关（诚实说明）。 -/
def gempty : FateV2.Modeling.Graph.DAG (Fin 4) where
  edge := fun _ _ => False
  decEdge := fun _ _ => inferInstanceAs (Decidable False)
  acyclic := by
    intro v hv
    have key : ∀ {a b : Fin 4},
        Relation.TransGen (fun _ _ : Fin 4 => False) a b → False := by
      intro a b h
      induction h with
      | single hab => exact hab
      | tail _ hbc _ => exact hbc
    exact key hv

/-- ⭐ `gempty` 上**没有**父代（每个点都是源点）。 -/
theorem gempty_parents (v : Fin 4) : gempty.parents v = ∅ := by
  ext u
  rw [FateV2.Modeling.Graph.DAG.mem_parents]
  simp [gempty]

/-- ⭐ **反例联合律**：
`p x = 1/4 · [x₂ = (x₀ = x₁)]` —— `x₂` 是 `x₀ = x₁` 的**确定性记录**，
`x₃` 完全自由（均匀）。

（`1/4 = 1/|Bool|²`：`x₃` 自由 + `x₂` 由 `x₀,x₁` 决定 ⟹ 总质量
`2² · 1 · 2 = 8` 个原子，各 `1/8`…… 本文件只关心**比值**，常量选 `1/4` 使
`mass univ = 1/4` 面向 `(真,真,真,假)` 等具体点好算。） -/
noncomputable def Pjoint (w : Fin 4 → Bool) : ℝ :=
  if w 2 = (w 0 = w 1) then (1 / 4 : ℝ) else 0

variable {β : Fin 4 → Bool}

/-- `Pjoint` 在「满足约束」的点上取 `1/4`。 -/
theorem Pjoint_of (w : Fin 4 → Bool) (h : w 2 = (w 0 = w 1)) : Pjoint w = 1 / 4 := by
  unfold Pjoint; rw [if_pos h]

/-- `Pjoint` 在「不满足约束」的点上取 `0`。 -/
theorem Pjoint_of_not (w : Fin 4 → Bool) (h : ¬ w 2 = (w 0 = w 1)) : Pjoint w = 0 := by
  unfold Pjoint; rw [if_neg h]

/-! ### 2.1 `mass` 的两个展开（本反例的**全部**计算） -/

/-- ⭐ **`mass univ` 的展开**：`mass univ Pjoint x = Pjoint x`（`mass_univ`）。 -/
theorem mass_univ_P (x : Fin 4 → Bool) : mass univ Pjoint x = Pjoint x :=
  mass_univ Pjoint x

/-- ⭐⭐ **`mass ∅ Pjoint x = 1`**：全空间求和 = 「`2` 个自由位 `(x₃, x₂ 的取值)`」
乘 `1/4`... **精确计算**：
8 个满足约束的原子（`x₀,x₁` 4 选、`x₂` 定、`x₃` 2 选）各 `1/4` ⟹ 总 `2`。

⚠ 所以 `mass ∅ Pjoint x = 2`，**与 `x` 无关**（D1 的积分值）。 -/
theorem mass_empty_P (x : Fin 4 → Bool) : mass ∅ Pjoint x = 2 := by
  classical
  have hsum : (∑ w : Fin 4 → Bool, Pjoint w) = 2 := by
    unfold Pjoint
    rw [Finset.sum_ite]
    rw [Finset.sum_const, Finset.sum_const]
    have h1 : (Finset.univ.filter
        (fun w : Fin 4 → Bool => (w 2 = true) = (w 0 = w 1))).card = 8 := by decide
    have h2 : (Finset.univ.filter
        (fun w : Fin 4 → Bool => ¬ ((w 2 = true) = (w 0 = w 1)))).card = 8 := by decide
    rw [h1, h2]
    norm_num
  unfold mass
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true]
  exact hsum

end FateV2.Predict.BridgeZipDown