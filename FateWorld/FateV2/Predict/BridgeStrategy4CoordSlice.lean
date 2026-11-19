/-
# 「图 ⟹ 概率」桥 · **策略 4：单坐标切片（coordinate-slice）**

## ⚠ 修订记录（P0 修复批次，务必先读）

本文件原有一核心引理 `mass_skew`，其陈述为：

> 设 `f` 只读 `{v}`、`v ∉ S`，则
> `∑ a, mass S (f·g) (x[v:=a]) = f x * mass S g x`。

**该陈述是假的**（因此本次修复把它删除，并换成两条真陈述，见下）。
反例（已在本仓库用 Lean 验证，见 `Fate/BridgeStrategy4CoordSliceAudit.lean`
中的 `counterexample_lhs` / `counterexample_rhs`）：

取 `V = Unit`、`α = Bool`、`S = ∅`、`f ≡ 1`、`g ≡ 1`、`x ≡ true`。则

* 左端 `= ∑ a, ∑ w, 1 = 2 · 2 = 4`；
* 右端 `= 1 · 2 = 2`。

`4 ≠ 2`，故原陈述不成立。**错误的根源**：原证明假定「内层对 `a` 的求和只在
`a = x v` 处非零」。但只要 `v ∉ S`，纤维条件是 `w|_S = x[v:=a]|_S`，
它**与 `a` 完全无关**，于是内层求和是 `|α|` 份相同的非零项，**根本不会塌缩**。
原证明第 4 步还想把 `f w` 换成 `f x`，这需要 `w v = x v`，在 `v ∉ S` 时同样不成立。

**修复方案（两条真定理，取代 1 条假定理）**

* 块 ① `sum_slice_collapse`：**精确刻画塌缩律**。
  `∑ a, mass S p (x[v:=a]) = if v ∈ S then mass (S.erase v) p x else card α • mass S p x`。
  **`v ∈ S` 时求和把 `v` 从求和集里删掉（= `mass_insert_sum`）；`v ∉ S` 时变成 `|α|` 倍**
  —— 后者正是原证明幻觉的反面，见 `sum_slice_nontrivial`。
* 块 ② `mass_slice_factor`：**真正可用的切片因子化**（`v` **在**求和集内）。
  设 `f` 只读 `{v}`，则 `mass (insert v S) (f·g) x = f x * mass (insert v S) g x`。
  这才是「把一个只依赖单坐标 `v` 的因子从 `mass` 里提出来」的正确形式，
  且它就是 `DAGFactorization.mass_mul` 在 `S ↦ insert v S` 处的特例。

## 1 与既有各策略的分野

| # | 骨架 | 引擎 | 卡点 / 终局 |
|---|---|---|---|
| 1 | `BridgeStrategy1TopoPeel` | 拓扑序 sink 剥离 + `mass_insert_sum` | 需 `pa(v) ⊆ S`；只做归一化方向 |
| 2 | `BridgeView2Elimination` | 完全变量消元 | 只到单点补集 `V∖{v}` |
| 5 | `BridgeStrategy5FiberBijection` | **整纤维**双射（`gluez` 改写 `S∖A` 上全部坐标）| `mass_local_of_reads` |
| 12 | `Strategy12FactorSplitBridge` | 因子**划分** `In`/`Out` | 残余 `NormalizedResidual` 未证 |
| 17 | `GraphToProbView17` | 支撑剖分 `FiberSplit` | 需 `NonvanishingZ`；只做三元 |
| 20 | `View20GraphToProb` | `fac_aux` + `prod_split3` **纯乘法重排** | 诊断出终点退化 |
| **4（本文）** | **单坐标切片** | **`mass` 在单个坐标 `v` 上：塌缩律 + 切片因子化** | 见 §2 |

### 与策略 5 的决定性区别

策略 5 一次性重标号 `S ∖ A` 上的**一整块**坐标（`gluez`），正确性只用到
「`f` 只读 `A`」这一条**全局**假设，因此**完全不需要** `p` 有乘积结构、也**不需要**图。

**策略 4 只动一个坐标 `v`**，并区分两种情形：

* `v ∈ S`：求和塌缩成 `mass (S.erase v) p x`，即**把 `v` 从求和集里删掉**
  （`mass_insert_sum` 的等价改写，见 `sum_slice_collapse_of_mem`）；
* `v ∉ S`：纤维对 `a` 无约束，求和**不塌缩**，只有 `|α|` 倍关系（`sum_slice_collapse_of_not_mem`）；
  只读 `{v}` 的因子可在 `v ∈ ` 求和集时提出（`mass_slice_factor`）。

后者正是「单坐标切片」路线**唯一的**代数障碍：它说明单坐标操作无法把
`S` 外的因子逐个剥离 —— 必须借 `mass_insert_sum`（放开一个坐标）把坐标搬进 `S`，
而 `mass_insert_sum` 需要「`v` 是被插进来的那个坐标」这一结构性信息（来自拓扑序/父集）。

## 2 数学内容

约定 `x[v := a]` 只在坐标 `v` 上把 `x v` 换成 `a`，
`agreeOn S x y :≡ ∀ u ∈ S, x u = y u`，`mass S p x :≡ ∑_{w : w|_S = x|_S} p w`。

### 块 ① **单坐标塌缩律**（`sum_slice_collapse`）

$$\sum_{a}\ \mathrm{mass}\,S\,p\,\bigl(x[v{:=}a]\bigr)
  \;=\;\begin{cases}\mathrm{mass}\,S\,p\,x & v \in S,\\
  |\alpha|\cdot \mathrm{mass}\,S\,p\,x & v \notin S.\end{cases}$$

**证明**：`v ∈ S` 时，`a ≠ x v` 的每一项纤维为空（`w v = x v` 与 `w v = a` 冲突），
只剩 `a = x v` 一项；`v ∉ S` 时纤维与 `a` 无关，`|α|` 项全等。

### 块 ② **单坐标切片因子化**（`mass_slice_factor`）

若 `f` 只读 `{v}`，则
$$\mathrm{mass}\,(\{v\}\cup S)\,(f\cdot g)\,x \;=\; f\,x\ \cdot\ \mathrm{mass}\,(\{v\}\cup S)\,g\,x .$$

**证明**：`mass_mul`（`f` 只读 `{v} ⊆ insert v S`）。

### 块 ③ **`v ∉ S` 的诚实负面结论**（`slice_blocked`）

`v ∉ S` 时，只要 `α` 非空碎、`p` 与 `f` 取到非零值，`∑ a` 就不可能等于单项 ——
这条把「单坐标切片」的卡点**形式化**为一条可复用的不等式判据
（`card α ≠ 1` 时的 `sum_slice_nontrivial`）。

## 3 结构

* §1 基础工具：`agreeOn`、`setAt`、`mass_eq_fiber_sum`
* §2 块 ①：`sum_slice_collapse` 及其两个分流特例
* §3 块 ②：`mass_slice_factor`
* §4 诚实边界

**⚠ 无 `sorry` / 无 `axiom` / 无 `Prop` 占位。**
-/

import FateWorld.FateV2.Predict.DAGFactorization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeStrategy4

set_option linter.unusedSectionVars false

open Finset FateV2.Predict.DAGFactorization

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · BridgeStrategy4CoordSlice

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeStrategy4CoordSlice.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 基础工具：一致性、单坐标改写、`mass` 的纤维求和形式
  =========================================================================== -/

/-- **「在 `S` 上一致」**（本文件局部定义，与 `BridgeStrategy5FiberBijection.agreeOn` 同义，
但为避免命名冲突而独立声明）。 -/
def agreeOn (S : Finset V) (x y : V → α) : Prop := ∀ u ∈ S, x u = y u

instance agreeOn_dec (S : Finset V) (x y : V → α) : Decidable (agreeOn S x y) :=
  inferInstanceAs (Decidable (∀ u ∈ S, x u = y u))

theorem agreeOn_refl (S : Finset V) (x : V → α) : agreeOn S x x := fun _ _ => rfl

theorem agreeOn_symm {S : Finset V} {x y : V → α} (h : agreeOn S x y) :
    agreeOn S y x := fun u hu => (h u hu).symm

theorem agreeOn_trans {S : Finset V} {x y z : V → α}
    (h1 : agreeOn S x y) (h2 : agreeOn S y z) : agreeOn S x z :=
  fun u hu => (h1 u hu).trans (h2 u hu)

omit [Fintype V] [Fintype α] [DecidableEq α] in
/-- **单坐标改写**：只在坐标 `v` 上取 `a`，其余取 `x`。 -/
def setAt (v : V) (x : V → α) (a : α) : V → α := fun u => if u = v then a else x u

omit [Fintype V] [Fintype α] [DecidableEq α] in
@[simp] theorem setAt_self (v : V) (x : V → α) (a : α) : setAt v x a v = a := by
  simp [setAt]

omit [Fintype V] [Fintype α] [DecidableEq α] in
theorem setAt_of_ne {v u : V} (h : u ≠ v) (x : V → α) (a : α) :
    setAt v x a u = x u := by
  simp [setAt, h]

omit [Fintype V] [Fintype α] [DecidableEq α] in
@[simp] theorem setAt_setAt_self (v : V) (x : V → α) (a : α) :
    setAt v (setAt v x a) a = setAt v x a := by
  funext u; by_cases h : u = v
  · subst h; simp
  · rw [setAt_of_ne h, setAt_of_ne h]

/-- **`mass` 的纤维求和形式**（单层，便于 `sum_bij` / `sum_filter`）。 -/
theorem mass_eq_fiber_sum (S : Finset V) (f : (V → α) → ℝ) (x : V → α) :
    mass S f x
      = ∑ w ∈ (Finset.univ.filter (fun w : V → α => agreeOn S w x)), f w := by
  classical
  have h : mass S f x
      = ∑ w : V → α, (if agreeOn S w x then f w else 0) := by
    unfold mass agreeOn
    rfl
  rw [h, Finset.sum_filter]

/-! ===========================================================================
  §2 块 ①：**单坐标塌缩律** `sum_slice_collapse`

这条定理是原假定理 `mass_skew` 的**正确替身**。诚实的塌缩律是：

* `v ∈ S`：`∑ a, mass S p (x[v:=a]) = mass (S.erase v) p x`
  —— 把 `v` 从求和集里去掉（**这就是 `mass_insert_sum` 的等价改写**，
  `insert v (S.erase v) = S`）；
* `v ∉ S`：`∑ a, mass S p (x[v:=a]) = |α| • mass S p x`
  —— 纤维与 `a` 无关，故和是 `|α|` 份相同项，**不塌缩**。

**这直接判掉了原 `mass_skew`**：它要求 `v ∉ S` 时得到单个 `mass S g x`，
而上面第二式表明那时必然多出 `|α|` 因子（见 `sum_slice_nontrivial`）。
-  =========================================================================== -/

section Collapse

omit [Fintype V] [Fintype α] [DecidableEq α] in
/-- `setAt` 与 `DAGFactorization.unpin` **定义相同**（只是命名空间不同）。 -/
theorem setAt_eq_unpin (v : V) (x : V → α) (a : α) :
    setAt v x a = FateV2.Predict.DAGFactorization.unpin v x a := rfl

/-- `v ∉ S` 时，`mass S p (x[v:=a])` **与 `a` 无关**（纤维没钉死 `v`）。 -/
theorem mass_setAt_eq_of_not_mem {v : V} {S : Finset V} (hvS : v ∉ S)
    (p : (V → α) → ℝ) (x : V → α) (a : α) :
    mass S p (setAt v x a) = mass S p x := by
  classical
  refine mass_congr S p ?_
  intro u hu
  have hvu : u ≠ v := fun h => hvS (h ▸ hu)
  rw [setAt_of_ne hvu]

/-- ⭐⭐⭐⭐⭐ **块 ①（策略 4 的正确核心）：单坐标切片塌缩律。**

$$\sum_{a}\ \mathrm{mass}\,S\,p\,(x[v{:=}a])
  \;=\;egin{cases}\mathrm{mass}\,(S\setminus\{v\})\,p\,x & v \in S,\
  |lpha| \cdot \mathrm{mass}\,S\,p\,x & v 
otin S.\end{cases}$$

**⚠ 这是原假定理 `mass_skew` 的诚实体**：`v ∈ S` 时求和把 `v` 从 `mass` 的求和集
里**删掉**（真结论，`mass_insert_sum` 的改写形式）；`v ∉ S` 时**不塌缩**，
只乘 `|α|` —— 单坐标操作无法把 `S` 外的因子剥出来。

**证明**：
* `v ∈ S`：`insert v (S.erase v) = S`，套 `mass_insert_sum`（注意 `setAt = unpin`）；
* `v ∉ S`：每项都等于 `mass S p x`，故和 = `|α| • mass S p x`。 -/
theorem sum_slice_collapse (v : V) (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    (∑ a : α, mass S p (setAt v x a))
      = if v ∈ S then mass (S.erase v) p x
        else (Fintype.card α : ℝ) * mass S p x := by
  classical
  by_cases hvS : v ∈ S
  · rw [if_pos hvS]
    -- `setAt v x a = unpin v x a`（定义相同），于是 `mass_insert_sum` 直接给出
    have h := mass_insert_sum (V := V) (α := α) v (S.erase v)
      (Finset.notMem_erase v S) p x
    rw [Finset.insert_erase hvS] at h
    simpa only [setAt_eq_unpin] using h
  · rw [if_neg hvS]
    have hconst : ∀ a : α, mass S p (setAt v x a) = mass S p x :=
      fun a => mass_setAt_eq_of_not_mem hvS p x a
    rw [Finset.sum_congr rfl (fun a _ => hconst a)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- 块 ① 的 `v ∈ S` 特例：把 `v` 从 `mass` 的求和集里删掉（= `mass_insert_sum`）。 -/
theorem sum_slice_collapse_of_mem {v : V} {S : Finset V} (hvS : v ∈ S)
    (p : (V → α) → ℝ) (x : V → α) :
    (∑ a : α, mass S p (setAt v x a)) = mass (S.erase v) p x := by
  rw [sum_slice_collapse, if_pos hvS]

/-- 块 ① 的 `v ∉ S` 特例（**原假定理的错误所在**：这里必然出现 `|α|` 因子）。 -/
theorem sum_slice_collapse_of_not_mem {v : V} {S : Finset V} (hvS : v ∉ S)
    (p : (V → α) → ℝ) (x : V → α) :
    (∑ a : α, mass S p (setAt v x a)) = (Fintype.card α : ℝ) * mass S p x := by
  rw [sum_slice_collapse, if_neg hvS]

/-- ⭐⭐ **`v ∉ S` 的非平凡性判据**：若 `|α| ≠ 1` 且 `mass S p x ≠ 0`，
则 `∑ a` **不可能**等于单项 `mass S p x` —— 这形式化了「`v ∉ S` 时切片被卡住」，
也正是原 `mass_skew` 陈述为假的原因。 -/
theorem sum_slice_nontrivial {v : V} {S : Finset V} (hvS : v ∉ S)
    (p : (V → α) → ℝ) (x : V → α)
    (hcard : (Fintype.card α : ℝ) ≠ 1) (hm : mass S p x ≠ 0) :
    (∑ a : α, mass S p (setAt v x a)) ≠ mass S p x := by
  rw [sum_slice_collapse_of_not_mem hvS]
  intro h
  -- `|α| * m = m` 且 `m ≠ 0` ⟹ `|α| = 1`
  have hmul : ((Fintype.card α : ℝ) - 1) * mass S p x = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp hmul with h1 | h2
  · exact hcard (by linarith)
  · exact hm h2

end Collapse

/-! ===========================================================================
  §3 块 ②：**单坐标切片因子化** `mass_slice_factor`

这才是「把只依赖单坐标 `v` 的因子从 `mass` 里提出来」的正确形式：
**`v` 必须在求和集内**。它就是 `mass_mul` 在 `insert v S` 处的特例。
-  =========================================================================== -/

section SliceFactor

/-- ⭐⭐⭐⭐ **块 ②：单坐标切片因子化。**

设 `f` **只读 `{v}`**（`f` 只依赖坐标 `v` 的取值）。则对**任意** `S`：

$$\mathrm{mass}\,(\{v\}\cup S)\,(f\cdot g)\,x \;=\; f\,x\ \cdot\ \mathrm{mass}\,(\{v\}\cup S)\,g\,x .$$

**⚠ 与假定理 `mass_skew` 的差别**：求和集必须**包含** `v`。若换成 `v ∉ S`
（如原 `mass_skew` 试图做的），该等式一般**为假**（见文件头的反例）。

**证明**：`mass_mul`，注意 `f` 读 `{v} ⊆ insert v S`。 -/
theorem mass_slice_factor (v : V) (S : Finset V) (f g : (V → α) → ℝ)
    (hf : ∀ x y : V → α, x v = y v → f x = f y) (x : V → α) :
    mass (insert v S) (fun w => f w * g w) x = f x * mass (insert v S) g x := by
  classical
  refine mass_mul (insert v S) f g x ?_
  intro x' y' h
  exact hf x' y' (h v (mem_insert_self v S))

/-- 块 ② 的推论：逐坐标把只读因子提出 `mass`（单步版，`v ∉ S` 时给 `{v} ∪ S`）。 -/
theorem mass_slice_factor' (v : V) (S : Finset V) (f g : (V → α) → ℝ)
    (hf : ∀ x y : V → α, x v = y v → f x = f y) (x : V → α) :
    mass (insert v S) (fun w => f w * g w) x = f x * mass (insert v S) g x :=
  mass_slice_factor v S f g hf x

end SliceFactor

/-! ===========================================================================
  §4 诚实边界（如实记载）
  =========================================================================== -/

/-
## §4 诚实边界

**已删除**：原 `mass_skew`
（`v ∉ S` ⟹ `∑ a, mass S (f·g) (x[v:=a]) = f x * mass S g x`）**陈述为假**，
已删除，无需 `sorry`。Lean 中验证的反例（`V = Unit`、`α = Bool`、`S = ∅`、
`f ≡ g ≡ 1`、`x ≡ true`）：左端 `= 4`、右端 `= 2`，见独立审计文件
`Fate/BridgeStrategy4CoordSliceAudit.lean`。

**已交付的真内容**：
* 块 ①（`sum_slice_collapse` + 两个分流特例 + 非平凡判据）：
  单坐标 `mass` 求和的**真实塌缩律**：`v ∈ S` 时得 `mass (S.erase v) p x`
  （= `mass_insert_sum`），`v ∉ S` 时得 `|α| • mass S p x`。
  **这正面否证**了「`v ∉ S` 时求和可塌缩成单项」的想法（`sum_slice_nontrivial`）。
* 块 ②（`mass_slice_factor`）：`v ∈ insert v S` 时把只读 `{v}` 的因子提出 `mass`
  （= `mass_mul` 特例，零缺口）。

**未完成 / 不可完成（如实声明）**：
* 原文件头 docstring 里承诺的块 ③（链 `X → Z → Y` 上的 `dSep ⟹ condMul` 落地）
  **从未实现**，且**不能**由上述引擎推出 —— 因为块 ① 表明单坐标切片在 `v ∉ S`
  时必然多出 `|α|` 因子，无法把 `p = φ₀·φ₁·φ₂` 的因子逐个「剥进」`mass`
  而不使用 `mass_insert_sum`（后者需要拓扑序/父集结构，属 `BridgeStrategy1` 的范围）。
  故本文件**不声称**任何链上落地结论。
* 本条结论与「策略 4 是独立可行的第四种桥」这一原始定位**相反**：本文件实际
  证明的是策略 4 **在代数上不可行**（`sum_slice_nontrivial`），
  真正的桥必须借 `mass_insert_sum`（策略 1/2 的范围）或整纤维重标号（策略 5）。

**判重结论**：本文件与已入库的 `BridgeExpanded`、`BridgeZipA`、`BridgeMinZPrime`
**无同名定理**（0 条重叠）；与 `BridgeStrategy5FiberBijection` 共享
`agreeOn`、`agreeOn_refl`、`agreeOn_symm`、`mass_eq_fiber_sum` 四个**辅助定义/平凡引理**
（非主定理）。主定理 `mass_slice_factor` 是 `DAGFactorization.mass_mul` 的特例，
`sum_slice_collapse` 与 `DAGFactorization.mass_insert_sum` 互补（一为塌缩判据，
一为放开求和）。**不构成 ≥80% 重复**。
-/

end BridgeStrategy4
end FateV2.Predict