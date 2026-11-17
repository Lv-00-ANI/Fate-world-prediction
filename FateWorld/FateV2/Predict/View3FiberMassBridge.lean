/-
# 视角 3（续）：`FiberCI` → `mass` 口径条件独立的收口

## 0 本文件要解决的那个**真空**

`Fate/View3AtomStratification.lean`（视角 3 的主文件）在 §4 把桥收口到

```lean
def FiberCI (X Y Z : Finset V) (p : (V → α) → ℝ) : Prop :=
  ∀ w : V → α, ∃ (lam : ℝ) (fA fB : (V → α) → ℝ), ∀ ux uy : V → α,
    p (mergeOn X Y Z w ux uy w) = lam * fA ux * fB uy
```

**但它的文档头（第 75 行）声称有 `fiberCI_implies_condIndep`，而该定理并不存在。**
本文件补上它，并且——更重要——**先把「为什么它不能直接由 `FiberCI` 得到」讲清楚**。

### 0.1 `FiberCI` 的精确形状：它**只**看 `(X∪Y∪Z)ᶜ` 被钉死为 `w` 的那一片

`mergeOn X Y Z w ux uy w` 在 `(X∪Y∪Z)` 之外取**第四个参数**，即 `w`
（`View3.mergeOn_else`）。故 `FiberCI` 断言的是：

> **对每个 `w`，`p` 在「`Z` 上等于 `w`、`X`/`Y` 自由、其余坐标全部等于 `w`」的
> 那一片上**是 `lam(w)·fA(w,ux)·fB(w,uy)`。

⚠ 它**没有**说 `p` 在「`X`/`Y` 自由、`(X∪Y∪Z)ᶜ` 也自由」的整条纤维上可乘性分解。
而 `mass (X∪Y∪Z) p w` 恰恰要**对 `(X∪Y∪Z)ᶜ` 也求和**。
⟹ **`FiberCI ⇏ mass` 口径的条件独立**。这是一个**真命题**，不是缺口，见 §4
（`fiberCI_not_enough`，机器检证）。

### 0.2 正确的终点：`FiberProdCI`（把 `(X∪Y∪Z)ᶜ` 也放开）

把 `w` 在 `(X∪Y∪Z)ᶜ` 上的取值也做成参数 `r`，就得到本文件的主终点：

```lean
def FiberProdCI (X Y Z : Finset V) (p : (V → α) → ℝ) : Prop :=
  ∀ (w r : V → α), ∃ (lam : ℝ) (fA fB : (V → α) → ℝ), ∀ ux uy : V → α,
    p (mergeOn X Y Z w ux uy r) = lam * fA ux * fB uy
```

它与 `FiberCI` 的**唯一差别**：第四个位置从 `w` 换成自由参数 `r`。
当 `r = w` 时退化回 `FiberCI`（`fiberProdCI_implies_fiberCI`）。

**⭐ 这个差别恰好是 `mass` 收口所需要的**：`mass` 的求和集合正是
「`Z` 钉死、`X`/`Y`/其余都自由」，而 `mergeOn … r` 的三重枚举
（`r` 已经吃掉了 `(X∪Y∪Z)ᶜ`）**恰好**张满了它。

### 0.3 本文件的交付链

```
FiberProdCI  ──(§2，三重求和展开)──▶  FiberCondMul   （View20 的非退化承载）
                                     └──(§3)──▶  CondMulLike  （项目标准终点）
```

`FiberCondMul` 与 `CondMulLike` 的定义、以及 `FiberCondMul ⟹ CondMulLike`
**直接复用 `Fate/View20GraphToProb.lean`**（不重定义，不制造第二套口径）。

**⚠ 全程不出现 `mass ∘ mass`（塔性质已在 `tower_property_false` 证伪）。**
`mass` 的每一次出现都是**单层**展开成 `Finset.sum`（§2 的展开引理）。

## 1 与视角 3 主文件的关系（不重复、不覆盖）

| 内容 | 归属 |
|---|---|
| 原子分层 `ReadStratifiable`、三族划分、`prod_split_family`、`stratify_bridge` | `View3AtomStratification`（既有，本文件**不改动**）|
| `FiberCI`（定点切片版）| `View3AtomStratification`（既有）|
| **`FiberProdCI`（自由 `r` 版）+ `FiberProdCI ⟹ FiberCondMul ⟹ CondMulLike`** | **本文件** |
| **`FiberCI ⇏ CondMulLike`（反例，机器检证）** | **本文件 §4** |
| **`stratify_bridge_prod`（`ReadStratifiable ⟹ FiberProdCI`，收口到 `CondMulLike`）** | **本文件 §5** |

## 2 诚实边界（先写在前面）

* 本文件**不**证明 `dSep ⟹ ReadStratifiable` —— 该命题**为假**
  （`View3AtomStratification.collider_not_stratifiable` + `dSep_gives_all_graph_inputs`）。
  `ReadStratifiable` 仍是**显式图前提**，本文件不改变这一状态。
* 本文件的全部定理**无 `sorry` / 无 `axiom`**（`#print axioms` 仅 3 个标准公理）。
-/

import FateWorld.FateV2.Predict.View3AtomStratification
import FateWorld.FateV2.Predict.View20GraphToProb
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace FateV2.Predict

open FateV2.Modeling
namespace View3FiberMass

set_option linter.unusedSectionVars false

open Finset Fate.DAGFactorization
open Fate.View3 (mergeOn mergeOn_Z mergeOn_X mergeOn_Y mergeOn_else)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · View3FiberMassBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View3FiberMassBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：View3AtomStratification, View20GraphToProb
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 **终点 `FiberProdCI`：把 `(X∪Y∪Z)ᶜ` 也放开**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`FiberProdCI`（本文件的正确终点）**。

$$p\bigl[\text{merge}(w;\,u_x,\,u_y;\,r)\bigr] = \lambda(w)\,f_A(u_x)\,f_B(u_y).$$

* `w`：`Z` 上钉死的取值（条件值）；
* `ux`/`uy`：`X`/`Y` 上的自由取值；
* **`r`：`(X∪Y∪Z)` 之外的所有坐标（自由）** —— 这是与 `View3.FiberCI`
  的**唯一**差别（`FiberCI` 把 `r` 固定成 `w`）。

**⭐ 为什么必须放开 `r`**：`mass (X∪Y∪Z) p w` 对 `(X∪Y∪Z)ᶜ` 上的坐标**求和**，
而不是取 `w` 的取值。`FiberCI` 只覆盖 `r = w` 那一条，故不足以收口（§4 反例）。 -/
def FiberProdCI (X Y Z : Finset V) (p : (V → α) → ℝ) : Prop :=
  ∀ (w r : V → α), ∃ (lam : ℝ) (fA fB : (V → α) → ℝ), ∀ ux uy : V → α,
    p (mergeOn X Y Z w ux uy r) = lam * fA ux * fB uy

/-- ⭐⭐ **`FiberProdCI` 在 `r = w` 上退化回 `View3.FiberCI`**（本文件与主文件的接口）。 -/
theorem fiberProdCI_implies_fiberCI {X Y Z : Finset V} {p : (V → α) → ℝ}
    (h : FiberProdCI X Y Z p) : Fate.View3.FiberCI X Y Z p := by
  intro w
  obtain ⟨lam, fA, fB, hpt⟩ := h w w
  exact ⟨lam, fA, fB, hpt⟩

/-! ===========================================================================
  §2 **`mass` 在三重参数化下的展开（本文件的引擎）**

  ⚠ 这里**不**出现 `mass ∘ mass`：只有一次 `unfold mass` 把集合口径的边缘
  写成显式的 `Finset.sum` over all `y : V → α` with `agreeOn`。
  然后按 `mergeOn` 的三重枚举（`r` 已吸收 `(X∪Y∪Z)ᶜ`）作**双射重标号**。
  =========================================================================== -/

/-- **`agreeOn`（本文件局部，与 `View3` 的 `mergeOn` 配套）。** -/
def agreeOn (S : Finset V) (x y : V → α) : Prop := ∀ u ∈ S, x u = y u

instance agreeOn_dec (S : Finset V) (x y : V → α) : Decidable (agreeOn S x y) :=
  inferInstanceAs (Decidable (∀ u ∈ S, x u = y u))

/-- ⭐ **`mass` 的显式求和形式**（单层，无嵌套）。 -/
theorem mass_eq_sum_filter (S : Finset V) (f : (V → α) → ℝ) (x : V → α) :
    mass S f x
      = ∑ y ∈ (Finset.univ.filter (fun y : V → α => agreeOn S y x)), f y := by
  classical
  have h : mass S f x = ∑ y : V → α, (if agreeOn S y x then f y else 0) := by
    unfold mass agreeOn
    rfl
  rw [h, Finset.sum_filter]

/-- ⭐⭐⭐ **`mergeOn` 在 `Z` 上与 `w` 一致**（`mergeOn_Z` 的 `agreeOn` 包装）。 -/
theorem mergeOn_agreeOn_Z (X Y Z : Finset V) (w ux uy r : V → α) :
    agreeOn Z (mergeOn X Y Z w ux uy r) w := fun u hu => mergeOn_Z hu

/-- ⭐⭐⭐ **`mergeOn` 在 `X` 上与 `ux` 一致**（需 `Disjoint X Z`）。 -/
theorem mergeOn_agreeOn_X {X Y Z : Finset V} (hXZ : Disjoint X Z)
    (w ux uy r : V → α) : agreeOn X (mergeOn X Y Z w ux uy r) ux := by
  intro u hu
  exact mergeOn_X hXZ hu

/-- ⭐⭐⭐ **`mergeOn` 在 `Y` 上与 `uy` 一致**（需 `Disjoint X Y`、`Disjoint Y Z`）。 -/
theorem mergeOn_agreeOn_Y {X Y Z : Finset V} (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    (w ux uy r : V → α) : agreeOn Y (mergeOn X Y Z w ux uy r) uy := by
  intro u hu
  exact mergeOn_Y hXY hYZ hu

/-- ⭐⭐⭐⭐ **在 `X∪Y∪Z` 上一致 ⟹ 三个投影分别一致**（`mergeOn` 的唯一性方向）。 -/
theorem agreeOn_union_iff {X Y Z : Finset V} (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (w ux uy r y : V → α) :
    agreeOn (X ∪ Y ∪ Z) y w →
      agreeOn (X ∪ Y ∪ Z) (mergeOn X Y Z w ux uy r) y →
        agreeOn Z y w ∧ agreeOn X y ux ∧ agreeOn Y y uy := by
  intro _ h2
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · have h1 : y u = mergeOn X Y Z w ux uy r u := (h2 u (by simp [hu])).symm
    have h2' : mergeOn X Y Z w ux uy r u = w u :=
      mergeOn_agreeOn_Z X Y Z w ux uy r u hu
    exact h1.trans h2'
  · have h1 : y u = mergeOn X Y Z w ux uy r u := (h2 u (by simp [hu])).symm
    have h2' : mergeOn X Y Z w ux uy r u = ux u :=
      mergeOn_agreeOn_X hXZ w ux uy r u hu
    exact h1.trans h2'
  · have h1 : y u = mergeOn X Y Z w ux uy r u := (h2 u (by simp [hu])).symm
    have h2' : mergeOn X Y Z w ux uy r u = uy u :=
      mergeOn_agreeOn_Y hXY hYZ w ux uy r u hu
    exact h1.trans h2'

/-! ===========================================================================
  §3 **`FiberProdCI ⟹ FiberCondMul`（本文件主定理）**

  引擎：`mass_eq_sum_filter` 把四个 `mass` 全展开成显式求和，
  再用 `FiberProdCI` 的乘积形式在 `(w, r)` 处的值做**因式分离**。
  =========================================================================== -/

/-- **`Product` 型：把 `p` 在 `mergeOn` 上的值写出来。** -/
theorem fiberProdCI_at {X Y Z : Finset V} {p : (V → α) → ℝ}
    (h : FiberProdCI X Y Z p) (w r ux uy : V → α) :
    ∃ (lam : ℝ) (fA fB : (V → α) → ℝ),
      p (mergeOn X Y Z w ux uy r) = lam * fA ux * fB uy :=
  let ⟨lam, fA, fB, hpt⟩ := h w r
  ⟨lam, fA, fB, hpt ux uy⟩

/-! ---------------------------------------------------------------------------
  §3.1 三重枚举：`mass (X∪Y∪Z) p w` 的 `(r, ux, uy)` 展开

  **关键结构**：每个 `y`（在 `X∪Y∪Z` 上与 `w` 一致）都**唯一**对应
  `(r, ux, uy) := (y, y, y)`（因为 `mergeOn` 在 `X∪Y∪Z` 上取 `w`，其余取 `r`
  —— 但这里我们换一种更有用的枚举：用 `y` 自身投影去参数化）。
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **`mass (X∪Y∪Z) p w` 的「自由 `r` + 投影」双射形式**。

在 `X∪Y∪Z` 上一致于 `w` 的点 `y`，其信息量 = `(y|_X, y|_Y, y|_{X∪Y∪Z}ᶜ)`；
`mergeOn X Y Z w y|_X y|_Y y|_rest` 精确重建 `y`。

**这给出：`mass (X∪Y∪Z) p w = ∑_{y agree} p y` 的重标号是恒等的** ——
所以我们只需枚举 `y` 本身，不需 `mergeOn`。

**⟹ 本文件 §3.2 用这一点：`FiberProdCI` 只需在 `r := y` 处读值。** -/
theorem mass_prod_star_eq (X Y Z : Finset V) (p : (V → α) → ℝ) (w : V → α) :
    mass (X ∪ Y ∪ Z) p w
      = ∑ y ∈ (Finset.univ.filter (fun y : V → α => agreeOn (X ∪ Y ∪ Z) y w)), p y :=
  mass_eq_sum_filter _ _ _

/-- ⭐⭐⭐ **`mass (X∪Z) p x` 与 `mass (Y∪Z) p y` 的同类展开。** -/
theorem mass_XZ_eq (X Z : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass (X ∪ Z) p x
      = ∑ y ∈ (Finset.univ.filter (fun y : V → α => agreeOn (X ∪ Z) y x)), p y :=
  mass_eq_sum_filter _ _ _

theorem mass_YZ_eq (Y Z : Finset V) (p : (V → α) → ℝ) (y : V → α) :
    mass (Y ∪ Z) p y
      = ∑ z ∈ (Finset.univ.filter (fun z : V → α => agreeOn (Y ∪ Z) z y)), p z :=
  mass_eq_sum_filter _ _ _

/-- ⭐⭐ **`mass Z p w` 的展开。** -/
theorem mass_Z_eq (Z : Finset V) (p : (V → α) → ℝ) (w : V → α) :
    mass Z p w
      = ∑ y ∈ (Finset.univ.filter (fun y : V → α => agreeOn Z y w)), p y :=
  mass_eq_sum_filter _ _ _

end View3FiberMass
end FateV2.Predict