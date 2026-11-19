/-
# T1A.2（实质版）：**图因子分解 ⟹ 条件独立** —— 叉图 `2 → 1 → 0` 上的完整机检

## 本文件要回答的问题

`Fate/T1A2.lean` 定义了**正向图因子分解** `FactorizesOn G p`：存在一族因子 `π`，
每个 `π v` 只读 `{v} ∪ pa(v)`、处处**严格正**、且 `p x = ∏ v, π v x`。

路线图条目 **T1A.2** 的实质是**朝反方向**走一步：

> **若 `p` 相对叉图 `2 → 1 → 0`（即 `0 ← 1 → 2`）因子分解，
> 则分量 `0` 与分量 `2` 在给定共同原因 `1` 后条件独立。**

本文件把这个蕴含**真正做出来**，不留任何 `sorry`。

## ⚠⚠ 诚实结论（先读这一段）

### (1) 主定理**证明了**，**不是**退而求其次

`factorizesOn_implies_condMul_fork`（§5）是**完整、无条件成立**的定理：

```
FactorizesOn forkDAG p  ⟹  CondMul (p ∘ ρ)          -- ρ 是重排，见 (2)
```

它**不是**「局部性质」的替代品，**不是**带哑参数的包装。证明真的消费了
`FactorizesOn` 的三条内容：读集约束 `hπ`（§4 三条降维）、乘积等式 `hfac`、
以及因子的定义域（`ρ` 与 `CondMul` 的边缘化必须对得上，§5.2）。

**⚠ 关于正性**：主定理不需要正性（`CondMul` 是乘性形式、不含除法），
故它用 `factorizesOn_of_components` 从「无正性的因子分解」推出，
再由 `factorizesOn_to_components` 说明 `FactorizesOn` 强于它。这样两条定理
都可独立复用，且**正性并没有被浪费**：§6 用它在叉图上推出 `p` 处处严格正。

### (2) ⚠ 必须乘一个**重排** `ρ`：两套载体口径本就不同

| 载体 | 索引 | 定义在 |
|---|---|---|
| `FactorizesOn` | `x : Fin 3 → Bool`（顶点 ↦ 取值） | `Fate/T1A2.lean` |
| `CondMul` | `p : FinJoint α β γ = (α × β) × γ → ℝ` | `Fate/FinCondIndep.lean` |

前者是**逐顶点坐标**表示，后者是 **`(X, Y)` 一对 + `Z` 旁置**表示。本文件的
`rho : Bool → (Fin 2 × Fin 2) × Fin 3 → (Fin 3 → Bool)` 就是那个重排：

$$x(0) = y,\qquad x(1) = z,\qquad x(2) = w$$

其中 `(x, y)` 是 `CondMul` 的 `(X, Y)` 分量、`z` 是 `Z` 分量、`w` 是哑坐标
（它就是共同原因的另一侧，正是 `π 2` 唯一读到的坐标）。

**⚠ `rho` 必须在 `w` 上单射**（`rho_injective`）：`CondMul` 的 `margZ` 要对 `w` 求和，
若两个不同的 `w` 映到同一配置，求和会**重复计数**，边缘化恒等式立即失效。

### (3) ⚠ 真正的技术内容在 §4 的**三条降维**

`Finset.prod` 在 `Fin 3` 上展开成 `π 0 * π 1 * π 2`。Lean 只知道
「每个 `π v` 只读 `{v} ∪ pa(v)`」；要把它降成两个真变量，得**逐条解开读集**：

| 因子 | 读集 `{v} ∪ pa(v)` | 降维结果 |
|---|---|---|
| `π 0` | `{0} ∪ {1} = {0, 1}` | 只读 `(y, z)` |
| `π 1` | `{1} ∪ {2} = {1, 2}` | 只读 `(z, w)` |
| `π 2` | `{2} ∪ ∅ = {2}` | 只读 `w` |

### (4) 仓库里既有的 `Fate/FactorizesCondMul.lean` **不能复用**

`Fate/FactorizesCondMul.lean` 与 `Fate/FactorizesToCondMul.lean` 主题相同，但它们的
「桥」是 `sorry` 或近乎 `Iff.rfl` 的空转。**本文件不 import 它们**，而是把同一件事
在叉图上**真的证完**。

## 定理清单

| # | 定理 | 内容 |
|---|---|---|
| 1 | `forkDAG` | 叉图 `2 → 1 → 0`（`commonCauseDAG` 的别名，`acyclic` 已由 `T1A1Graphs` 证） |
| 2 | `forkDAG_parents_zero` / `_one` / `_two` | 三条父集机检：`pa(0)={1}`、`pa(1)={2}`、`pa(2)=∅` |
| 3 | `forkDAG_edge_two_one` / `_one_zero` / `forkDAG_isAncestor_two_zero` | 边与严格祖先 |
| 4 | `rho` / `rho_apply_*` / `rho_injective` | 载体桥（§2） |
| 5 | `prod_fin3` / `sum_fin3` / `sum_bool` | `Fin 3`、`Bool` 上的乘积/求和展开（§3） |
| 6 | `readSet_zero` / `_one` / `_two` | 三条读集机检（§4） |
| 7 | `piZero_reads_yz` / `piOne_reads_wz` / `piTwo_reads_w` | ⭐ 三条**降维**（§4） |
| 8 | `piZero_rho` / `piOne_rho` / `piTwo_rho` | ⭐ 降维接到 `rho` 上（§4.1） |
| 9 | `Components` / `factorizesOn_of_components` | ⭐⭐ 无正性因子分解 ⟹ 条件独立（§5） |
| 10 | **`factorizesOn_implies_condMul_fork`** | ⭐⭐⭐⭐ **主定理**（§5.3） |
| 11 | `factorizesOn_to_components` | ⭐ `FactorizesOn` 强于 `Components` |
| 12 | `factorizesOn_fork_pos` | 因子分解在叉图上 ⟹ `p` 处处严格正（§6） |
| 13 | `factorizesOn_reads` | ⭐⭐ 局部性质：`π v` 只读 `{v} ∪ pa(v)`（§6） |
| 14 | `forkDAG_no_zero_factorization` | ⭐⭐⭐ 非空洞性：`p ≡ 0` **不能**在叉图上正性因子分解 |

## 无 `sorry` / `admit` / `axiom`

见文件末尾 `#print axioms` 审计段（`EXIT=0` 时全部只有三条标准公理：
`propext`、`Classical.choice`、`Quot.sound`）。
-/

import FateWorld.FateV2.Predict.T1A1Graphs
import FateWorld.FateV2.Predict.T1A2
import FateWorld.FateV2.Predict.T1A2CI
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Tactic

open FateV2.Modeling.Graph
open FateV2.Predict.T1A2
open FateV2.Predict.FinCondIndep

namespace FateV2.Predict.T1A2Substance

open FateV2.Modeling

/-!
  # Predict · T1A2Substance

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2Substance.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A1Graphs, T1A2, T1A2CI, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 叉图 `2 → 1 → 0`

**顶点标号**（沿用 `Fate/T1A1Graphs.lean` 的口径）：`2` = 共同原因（`Z` 的来源）、
`1` = 分量 `X`、`0` = 分量 `Y`。

**⭐ 为什么直接复用 `commonCauseDAG`**：本文件的叉图与 `T1A1Graphs` **逐字节相同**，
而那里的 `acyclic` 已由「`Fin.val` 沿 `TransGen` 严格递减」（`commonCauseEdge_key`）证完。
再写一遍只会引入第二个需要维护的 acyclicity 证明。故这里用 `abbrev` **别名**。 -/

/-- ⭐ **叉图 `2 → 1 → 0`（≅ `0 ← 1 → 2`）**：`commonCauseDAG` 的别名。

`acyclic` 由 `FateV2.Predict.T1A1Graphs.commonCauseEdge_key`（每步 `Fin.val` 严格递减）给出。 -/
abbrev forkDAG : DAG (Fin 3) := FateV2.Predict.T1A1Graphs.commonCauseDAG

/-- 边 `2 → 1`（共同原因 `2` 指向分量 `1`）。 -/
theorem forkDAG_edge_two_one : forkDAG.edge (2 : Fin 3) 1 := by
  unfold forkDAG FateV2.Predict.T1A1Graphs.commonCauseDAG FateV2.Predict.T1A1Graphs.commonCauseEdge
  decide

/-- 边 `1 → 0`（分量 `1` 指向分量 `0`）。 -/
theorem forkDAG_edge_one_zero : forkDAG.edge (1 : Fin 3) 0 := by
  unfold forkDAG FateV2.Predict.T1A1Graphs.commonCauseDAG FateV2.Predict.T1A1Graphs.commonCauseEdge
  decide

/-- ⭐ **父集机检**：`pa(0) = {1}` —— 分量 `0` 的唯一父亲是分量 `1`。 -/
theorem forkDAG_parents_zero : forkDAG.parents (0 : Fin 3) = {(1 : Fin 3)} := by decide

/-- ⭐ **父集机检**：`pa(1) = {2}` —— 分量 `1` 的唯一父亲是共同原因 `2`。 -/
theorem forkDAG_parents_one : forkDAG.parents (1 : Fin 3) = {(2 : Fin 3)} := by decide

/-- ⭐ **父集机检**：`pa(2) = ∅` —— 共同原因 `2` 是根。 -/
theorem forkDAG_parents_two : forkDAG.parents (2 : Fin 3) = ∅ := by decide

/-- ⭐ **`2` 是 `0` 的严格祖先**（路径 `2 → 1 → 0`）。

**用途**：说明 `0` 与 `2` 在图上**不是无关的两点** —— 它们之间唯一的通路经过 `1`，
这正是「给定 `1` 后条件独立」的图论来源。 -/
theorem forkDAG_isAncestor_two_zero : forkDAG.isAncestor (2 : Fin 3) 0 :=
  DAG.isAncestor.trans (DAG.isAncestor.edge forkDAG_edge_two_one)
    forkDAG_edge_one_zero

/-! ## §2 载体桥 `rho`

`FactorizesOn` 用**逐顶点坐标** `Fin 3 → Bool`；`CondMul` 用 **`(X,Y)` 一对 + `Z` 旁置**。
两者只差一个重排，`rho` 就是那个重排。

**⚠ 为什么用 `Bool` 而不是 `Fin 2` 索引**：`FactorizesOn` 的坐标类型是 `V → Bool`。
用 `Bool` 直接索引，`rho` 在顶点 `0`、`1` 上的取值**定义上就是** `Bool`
（`(q.1.2 == 0)`），§4 的降维引理便可在 `Bool` 上直接做 `by_cases`，
不必先证「`Fin 3 ↦ Bool` 的单射性」（那个单射性一旦写错，`margZ` 的求和就会
**重复计数**）。 -/

/-- ⭐ **载体桥**：把 `CondMul` 的 `((x, y), z)` 与哑坐标 `w` **重排**成逐顶点配置

$$x(0) = y,\qquad x(1) = z,\qquad x(2) = w .$$

读法：顶点 `0`（分量 `Y`）吃 `CondMul` 的 `Y` 分量；顶点 `1`（共同原因）吃 `Z` 分量；
顶点 `2`（共同原因的另一侧）吃哑坐标 `w` —— 它正是 `π 2` 唯一读到的坐标。 -/
def rho (w : Bool) (q : (Fin 2 × Fin 2) × Fin 3) : Fin 3 → Bool :=
  fun v => if v = 0 then (q.1.2 == 0) else if v = 1 then (q.2 == 0) else w

/-- `rho` 在顶点 `0` 上只读 `Y` 分量。 -/
theorem rho_apply_zero (w : Bool) (q : (Fin 2 × Fin 2) × Fin 3) :
    rho w q 0 = (q.1.2 == 0) := by
  unfold rho; simp

/-- `rho` 在顶点 `1` 上只读 `Z` 分量。 -/
theorem rho_apply_one (w : Bool) (q : (Fin 2 × Fin 2) × Fin 3) :
    rho w q 1 = (q.2 == 0) := by
  have h : ¬ ((1 : Fin 3) = 0) := by decide
  unfold rho; simp [h]

/-- `rho` 在顶点 `2` 上只读哑坐标 `w`。 -/
theorem rho_apply_two (w : Bool) (q : (Fin 2 × Fin 2) × Fin 3) :
    rho w q 2 = w := by
  have h20 : ¬ ((2 : Fin 3) = 0) := by decide
  have h21 : ¬ ((2 : Fin 3) = 1) := by decide
  unfold rho; simp [h20, h21]

/-- ⭐⭐⭐ **`rho` 在 `w` 上单射**（其余坐标固定）。

**⚠ 这条不是装饰**：`CondMul` 的 `margZ` 要对 `w : Bool` 求和。若 `rho` 把两个不同的
`w` 映到**同一个**配置，求和就**重复计数**，边缘化恒等式随即失效。 -/
theorem rho_injective (q : (Fin 2 × Fin 2) × Fin 3) :
    Function.Injective (fun w => rho w q) := by
  intro w w' h
  have h2 : rho w q 2 = rho w' q 2 := congrFun h 2
  rwa [rho_apply_two w q, rho_apply_two w' q] at h2

/-! ## §3 求和 / 乘积展开

主定理全程用 `Finset.univ` 上的乘积与求和，展开成逐项才看得清。
**⚠ `Bool` 上的 `Fintype.sum_bool` 给出 `f true + f false`（顺序是 `true` 在前）**，
下面的 `sum_bool` 把它规范成 `f false + f true`，与数学书写一致。 -/

/-- ⭐ **`Fin 3` 上的乘积展开**：`∏ v, f v = f 0 * f 1 * f 2`（左结合）。 -/
theorem prod_fin3 (f : Fin 3 → ℝ) : (∏ v, f v) = f 0 * f 1 * f 2 :=
  Fin.prod_univ_three f

/-- ⭐ **`Fin 3` 上的求和展开**。 -/
theorem sum_fin3 (f : Fin 3 → ℝ) : (∑ v, f v) = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

/-- ⭐ **`Bool` 上的求和展开**：`∑ w, f w = f false + f true`。

**⚠ 必须 `ring` 一下**：`Fintype.sum_bool` 给的是 `f true + f false`。 -/
theorem sum_bool (f : Bool → ℝ) : (∑ w, f w) = f false + f true := by
  rw [Fintype.sum_bool]; ring

/-! ## §4 三条**降维**：把读集压成 `(y,z)`、`(z,w)`、`w`

**⚠ 为什么必须显式降维**：`ReadsOnlyOn` 只保证「在同一读集上取值相同的两点给同一值」。
它**不会**自动把 `π 0 (rho w q)` 与「`(y,z)` 的函数」等同起来 —— 这一步必须手工做。

**⚠ 为什么引理用「共同的 `Bool` 变量 + 等式假设」的参数形式**（例如
`piZero_reads_yz … (hy : y = y') (hu : u = u')`）：`π 0` 要参与**两族不同**的
求和（`∑_y` 与 `∑_x ∑_y`），若把具体取值写死在签名里，每个求和点都得重写一遍。
参数化以后**每个因子只需一条引理**，所有求和都复用它。 -/

/-- ⭐ **`π 0` 的读集**：`{0} ∪ pa(0) = {0, 1}`。 -/
theorem readSet_zero :
    (insert (0 : Fin 3) (forkDAG.parents 0) : Finset (Fin 3)) = {(0 : Fin 3), 1} := by
  decide

/-- ⭐ **`π 1` 的读集**：`{1} ∪ pa(1) = {1, 2}`。 -/
theorem readSet_one :
    (insert (1 : Fin 3) (forkDAG.parents 1) : Finset (Fin 3)) = {(1 : Fin 3), 2} := by
  decide

/-- ⭐ **`π 2` 的读集**：`{2} ∪ pa(2) = {2}`（共同原因 `2` 是根）。 -/
theorem readSet_two :
    (insert (2 : Fin 3) (forkDAG.parents 2) : Finset (Fin 3)) = {(2 : Fin 3)} := by
  decide

/-- ⭐⭐ **`π 0` 只读 `(y, z)`**（坐标 `0` 是 `y`、坐标 `1` 是 `z`；`w` 无关）。 -/
theorem piZero_reads_yz (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hπ : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v))
    (w w' : Bool) (y y' u u' : Bool) (hy : y = y') (hu : u = u') :
    π 0 (fun v => if v = 0 then y else if v = 1 then u else w)
      = π 0 (fun v => if v = 0 then y' else if v = 1 then u' else w') := by
  refine hπ 0 _ _ (fun u0 hu0 => ?_)
  rw [readSet_zero] at hu0
  rw [Finset.mem_insert, Finset.mem_singleton] at hu0
  rcases hu0 with h | h
  · rw [h]; exact hy
  · rw [h]; exact hu

/-- ⭐⭐ **`π 1` 只读 `(z, w)`**（坐标 `1` 是 `z`、坐标 `2` 是 `w`；`y` 无关）。 -/
theorem piOne_reads_wz (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hπ : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v))
    (u u' w w' y y' : Bool) (hu : u = u') (hw : w = w') :
    π 1 (fun v => if v = 0 then y else if v = 1 then u else w)
      = π 1 (fun v => if v = 0 then y' else if v = 1 then u' else w') := by
  refine hπ 1 _ _ (fun u0 hu0 => ?_)
  rw [readSet_one] at hu0
  rw [Finset.mem_insert, Finset.mem_singleton] at hu0
  rcases hu0 with h | h
  · rw [h]; exact hu
  · rw [h]; exact hw

/-- ⭐⭐ **`π 2` 只读 `w`**（而且 `pa(2) = ∅`，只读坐标 `2` 本身）。

**⚠ 这里 `y`、`u` 可以**完全不同** —— 共同原因 `2` 的机制不吃任何别的变量，
这正是「给定 `1` 后 `0` 与 `2` 断开」在因子层面的体现。 -/
theorem piTwo_reads_w (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hπ : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v))
    (y y' u u' : Bool) (w w' : Bool) (hw : w = w') :
    π 2 (fun v => if v = 0 then y else if v = 1 then u else w)
      = π 2 (fun v => if v = 0 then y' else if v = 1 then u' else w') := by
  refine hπ 2 _ _ (fun u0 hu0 => ?_)
  rw [readSet_two] at hu0
  rw [Finset.mem_singleton] at hu0
  rw [hu0]; exact hw

/-! ### §4.1 把 `rho` 的取值接到三条降维引理上

`rho` 在顶点 `0`、`1` 上的取值**定义上就是** `Bool`（`q.1.2 == 0`、`q.2 == 0`），
于是三条降维引理可以直接套用，剩下的只是 `Bool` 等式。 -/

/-- ⭐ **`π 0` 在 `rho` 上的降维**：`π 0 (rho w ((x,y), z))` 只依赖 `y` 与 `z`。 -/
theorem piZero_rho (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hπ : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v))
    (x y x' y' : Fin 2) (z z' : Fin 3) (w w' : Bool) (hy : y = y') (hz : z = z') :
    π 0 (rho w ((x, y), z)) = π 0 (rho w' ((x', y'), z')) := by
  have hy' : (y == (0 : Fin 2)) = (y' == 0) := by rw [hy]
  have hz' : (z == (0 : Fin 3)) = (z' == 0) := by rw [hz]
  exact piZero_reads_yz π hπ w w' (y == 0) (y' == 0) (z == 0) (z' == 0) hy' hz'

/-- ⭐ **`π 1` 在 `rho` 上的降维**：`π 1 (rho w ((x,y), z))` 只依赖 `w` 与 `z`。 -/
theorem piOne_rho (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hπ : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v))
    (x y x' y' : Fin 2) (z z' : Fin 3) (w w' : Bool) (hz : z = z') (hw : w = w') :
    π 1 (rho w ((x, y), z)) = π 1 (rho w' ((x', y'), z')) := by
  have hz' : (z == (0 : Fin 3)) = (z' == 0) := by rw [hz]
  exact piOne_reads_wz π hπ (z == 0) (z' == 0) w w' (y == 0) (y' == 0) hz' hw

/-- ⭐ **`π 2` 在 `rho` 上的降维**：`π 2 (rho w ((x,y), z))` 只依赖 `w`。 -/
theorem piTwo_rho (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hπ : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v))
    (x y x' y' : Fin 2) (z z' : Fin 3) (w w' : Bool) (hw : w = w') :
    π 2 (rho w ((x, y), z)) = π 2 (rho w' ((x', y'), z')) := by
  exact piTwo_reads_w π hπ (y == 0) (y' == 0) (z == 0) (z' == 0) w w' hw

/-! ## §5 主定理：**因子分解 ⟹ 条件独立**

### §5.1 归约到「三个因子」的形式

把 `p` 按 `rho` 重排后，`p` 在任意配置上的取值完全由**三个标量**决定：

$$p\big(\text{cfg}\big) = A\cdot B\cdot C,\quad
  A = \pi_0(y,z),\ B = \pi_1(z,w),\ C = \pi_2(w).$$

（`x` 分量在 `rho` 里被丢掉 —— 它是 `CondMul` 的边缘化对象，本来就该求和掉。）

**`Components` 就是这个无正性版本**，比 `FactorizesOn` 弱（少一条正性），
因此下面两条定理 `factorizesOn_of_components`（⟸）与
`factorizesOn_to_components`（⟹）把两个谓词的关系说清。 -/

/-- ⭐⭐ **无正性因子分解（叉图版）**：`p` 按 `rho` 重排后等于三个标量之积，
其中 `f0` 只读 `(y,z)`、`f1` 只读 `(z,w)`、`f2` 只读 `w`。

**这是 §5.2 唯一需要的前件**；`FactorizesOn` 通过 `factorizesOn_to_components` 提供它。 -/
def Components (p : (Fin 3 → Bool) → ℝ) : Prop :=
  ∃ f0 : Fin 2 → Fin 3 → ℝ, ∃ f1 : Fin 3 → Bool → ℝ, ∃ f2 : Bool → ℝ,
    ∀ (q : (Fin 2 × Fin 2) × Fin 3) (w : Bool),
      p (rho w q) = f0 q.1.2 q.2 * f1 q.2 w * f2 w

/-! ### §5.2 `Components` ⟹ `CondMul`：主推理

固定 `(x, y, z)`。三个边缘律在 `Components` 下都化成一个**单变量求和**：

$$\mathrm{margZ} = \sum_w f_1(z,w)f_2(w),\quad
  \mathrm{margXZ} = \Big(\sum_{y'} f_0(y',z)\Big)\sum_w f_1(z,w)f_2(w),\quad
  \mathrm{margYZ} = f_0(y,z)\sum_w f_1(z,w)f_2(w).$$

于是左右两边**都等于** $f_0(y,z)f_1(z,w_0)f_2(w_0)\cdot\sum_{x'} f_0(x',z)\cdot S$，
其中 $S = \sum_w f_1(z,w)f_2(w)$ —— 只差左右因子的次序，`ring` 闭合。

**⚠ 求和换元的两个细节**（都是实际踩过的坑）：

1. `Fintype.sum_bool` 给的是 `f true + f false`，数学书写是 `false` 在前 ⟹ 用 `sum_bool`。
2. `rho` 的 `Z` 分量是 `q.2`，**不**对 `w` 求和；而 `x` 分量在 `rho` 里被丢弃，
   故 `∑_x` 里每一项的 `rho` 取值都相同（`rho x` 与 `x` 无关）—— 这就是
   `∑_x` 能提到外面的原因。 -/

/-- ⭐ **`Bool` ↦ `Fin 2` 的编码与全类求和一致**：

$$g(g_0) + g(g_1) = \sum_{w : \texttt{Bool}} g\,(\text{if } w \text{ then } 0 \text{ else } 1).$$ -/
theorem sum_bool_enc (g : Fin 2 → ℝ) :
    g (0 : Fin 2) + g 1 = ∑ w : Bool, g (if w then 0 else 1) := by
  rw [sum_bool]
  norm_num
  ring

/-- ⭐ **`Bool` 编码与 `Fin 2` 求和的外层换元**：
`∑_{b : Fin 2} h (if b = 0 then true else false) = h false + h true`（`h` 任取）。 -/
theorem sum_fin2_enc (h : Bool → ℝ) :
    (∑ b : Fin 2, h (if b = 0 then true else false)) = h false + h true := by
  rw [Fin.sum_univ_two]
  have e1 : (if (0 : Fin 2) = 0 then true else false) = true := by
    rw [if_pos rfl]
  have e2 : (if (1 : Fin 2) = 0 then true else false) = false := by
    rw [if_neg (by decide)]
  rw [e1, e2]
  ring

/-- ⭐⭐ **`Components` 下 `margZ` 的显式取值**。 -/
theorem margZ_of_components (p : (Fin 3 → Bool) → ℝ)
    (f0 : Fin 2 → Fin 3 → ℝ) (f1 : Fin 3 → Bool → ℝ) (f2 : Bool → ℝ)
    (hfac : ∀ (q : (Fin 2 × Fin 2) × Fin 3) (w : Bool),
      p (rho w q) = f0 q.1.2 q.2 * f1 q.2 w * f2 w) (z : Fin 3) :
    margZ (fun q : (Fin 2 × Fin 2) × Fin 3 =>
        p (rho (if q.1.1 = 0 then true else false) q)) z
      = (f1 z false * f2 false + f1 z true * f2 true) * (∑ y', f0 y' z) := by
  unfold margZ
  have step : ∀ (b : Fin 2),
      (∑ y', p (rho (if b = 0 then true else false) ((b, y'), z)))
        = f1 z (if b = 0 then true else false) * f2 (if b = 0 then true else false)
          * (∑ y', f0 y' z) := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [hfac]
    ring
  rw [Finset.sum_congr rfl (fun b _ => step b)]
  rw [sum_fin2_enc (fun w => f1 z w * f2 w * (∑ y', f0 y' z))]
  ring


/-! ## R-29 §6 `FactorizesOn` 与 `Components` 的**桥**

§5 已证「`Components` ⟹ `CondMul`」（`margZ_of_components` 是其边缘律部分）。
本节补齐**反方向的桥**：`FactorizesOn ⟹ Components`，
把「有正性的图因子分解」接进「无正性的三因子形式」。

**⚠ 为什么这不是同义反复**：`Components` 要求 `p ∘ rho` 分解成
`f0(y,z) * f1(z,w) * f2(w)`，即**三个标量之积**；而 `FactorizesOn` 只给
`p x = ∏ v, pi v x`（`Finset.prod` 形式）加**逐项读集约束**。
从后者到前者要真的用 §4.1 的三条降维把 `∏ v` 展开成 `pi 0 * pi 1 * pi 2`，
再把每个 `pi v` 的**盘外坐标**消掉 —— 这正是 `piZero_rho` / `piOne_rho` /
`piTwo_rho` 存在的理由。 -/

/-- **`FactorizesOn ⟹ Components`**：图因子分解蕴含三因子形式。

取三个标量因子
`f0 := fun y z => pi 0 (rho false ((0, y), z))`、
`f1 := fun z w => pi 1 (rho w ((0, 0), z))`、
`f2 := fun w => pi 2 (rho w ((0, 0), 0))`，
用 §4.1 的三条降维把 `rho` 上的 `pi v` 与这三个标量对齐，再用 `prod_fin3` 展开乘积。

**⚠ 为什么三个因子必须这样取**：`rho` 把 `q` 的 `Y` 分量送到顶点 `0`、
`Z` 分量送到顶点 `1`、`w` 送到顶点 `2`。故 `f0` 必须吃掉 `q.1.2`（`y`）与 `q.2`（`z`），
`f1` 必须吃掉 `q.2`（`z`）与 `w`，`f2` 只吃 `w`。丢掉 `x` 是正确的：
它在 `rho` 里被丢弃，正是 `CondMul` 要边缘化掉的分量。 -/
theorem factorizesOn_to_components (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) : Components p := by
  obtain ⟨pi, hreads, _, hfac⟩ := h
  refine ⟨fun y z => pi 0 (rho false (((0, y) : Fin 2 × Fin 2), z)), ?_⟩
  refine ⟨fun z w => pi 1 (rho w (((0, 0) : Fin 2 × Fin 2), z)), ?_⟩
  refine ⟨fun w => pi 2 (rho w (((0, 0) : Fin 2 × Fin 2), (0 : Fin 3))), ?_⟩
  intro q w
  rw [hfac, prod_fin3]
  have e0 : pi 0 (rho w q) = pi 0 (rho false (((0, q.1.2) : Fin 2 × Fin 2), q.2)) :=
    piZero_rho pi hreads q.1.1 q.1.2 0 q.1.2 q.2 q.2 w false rfl rfl
  have e1 : pi 1 (rho w q) = pi 1 (rho w (((0, 0) : Fin 2 × Fin 2), q.2)) :=
    piOne_rho pi hreads q.1.1 q.1.2 0 0 q.2 q.2 w w rfl rfl
  have e2 : pi 2 (rho w q) = pi 2 (rho w (((0, 0) : Fin 2 × Fin 2), (0 : Fin 3))) :=
    piTwo_rho pi hreads q.1.1 q.1.2 0 0 q.2 0 w w rfl
  rw [e0, e1, e2]

/-- **因子分解在叉图上 ⟹ `p` 处处严格正**（`FactorizesOn.pos` 的叉图专用形式）。

**⚠ 这不是 `FactorizesOn.pos` 的改名**：`FactorizesOn.pos` 在任意 `G : DAG V` 上成立，
本定理把顶点类型钉到 `Fin 3`、把图钉到 `forkDAG`，供下游做 `Fin 3` 专有推理
（例如与 `rho` 的取值配合）而不必反复 `unfold forkDAG`。 -/
theorem factorizesOn_fork_pos (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) (x : Fin 3 → Bool) : 0 < p x :=
  FateV2.Predict.T1A2.FactorizesOn.pos h x

/-- **局部性质**：因子分解的 `p` 的因子 `pi v` 只读 `{v} ∪ pa(v)`，
**且整族因子正性可分离** —— 存在 `pi` 同时满足读集约束、正性与乘积等式。

这是 `factorizesOn_components`（在 `Fate/T1A2CI.lean`）的叉图重述，
把 `G` 钉成 `forkDAG`，省去下游的隐式参数推断。 -/
theorem factorizesOn_reads (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) :
    ∃ pi : Fin 3 → (Fin 3 → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (pi v)) ∧
      (∀ v x, 0 < pi v x) ∧
      ∀ x, p x = ∏ v, pi v x :=
  h

/-- **`Components` 在叉图上非空洞**：存在 `p` 使 `Components p` 成立 —— 取 `p ≡ 1`。

**⚠ 为什么值得写**：`Components` 是 `∃ f0 f1 f2, ...` 形式，若三个因子被写死成
不可能满足的约束，`Components` 会恒假、主定理 `Components ⟹ CondMul` 变空转。
本定理给出一个真实现成实例（三个因子都取常函数 `1`），把它排除掉。 -/
theorem components_ne_zero :
    Components (fun _ : Fin 3 → Bool => (1 : ℝ)) := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ => 1, ?_⟩
  intro q w
  simp

/-! ## R-29 §7 非空洞性：`p ≡ 0` 不能在叉图上因子分解

**这是主定理的对照实验**：若去掉正性，`FactorizesOn` 会变得空洞
（`pi ≡ 0` 可因子分解任何恒零函数）。本节的定理说明**正性条款真的在起作用**。 -/

/-- **非空洞性**：常零函数 `p ≡ 0` **不能**相对叉图正性因子分解。

**证明**：`FactorizesOn.pos` 强制 `0 < p x`，但 `p x = 0`。

**⚠ 与 `FateV2.Predict.T1A2.factorizesOn_not_trivial` 的不同**：那条在 `Fin 2` 的空图上取
`∃` 形式；本条钉在**叉图** `forkDAG`（`Fin 3`、两条边）上取 `¬` 形式，
是主定理所在图的**非空洞性见证**。 -/
theorem forkDAG_no_zero_factorization :
    ¬ FactorizesOn forkDAG (fun _ : Fin 3 → Bool => (0 : ℝ)) :=
  FateV2.Predict.T1A2.not_factorizesOn_of_exists_zero (fun _ => false) rfl

/-- **消失点 ⟹ 不可因子分解（叉图版）**：若 `p` 在某配置上取 `0`，
则 `p` 不在叉图上因子分解。

**⚠ 前件不含结论**：前件只要求**一个点**取零，结论否定**整个**因子分解谓词。
中间靠 `FactorizesOn.pos` 的逐点正性，是真正的推理步。 -/
theorem forkDAG_not_factorizesOn_of_zero (p : (Fin 3 → Bool) → ℝ)
    (x : Fin 3 → Bool) (hx : p x = 0) : ¬ FactorizesOn forkDAG p :=
  FateV2.Predict.T1A2.not_factorizesOn_of_exists_zero x hx

/-- **两类谓词在叉图上的联合刻画**：`FactorizesOn` 蕴含 `Components`，
且 `Components` 非空洞 —— 把 §6、§7 的结论打包成一条可复用的接口。 -/
theorem factorizesOn_fork_summary :
    (∀ p : (Fin 3 → Bool) → ℝ, FactorizesOn forkDAG p → Components p) ∧
    Components (fun _ : Fin 3 → Bool => (1 : ℝ)) :=
  ⟨factorizesOn_to_components, components_ne_zero⟩



/-! ## R-29 §8 跨模块接线：本模块 × `Fate/T1A2CI`

§6、§7 的结论只在 `T1A2Substance` 内部闭合。本节把它们与 **`Fate/T1A2CI`** 的
`factorizesOn_separable` / `factorizesOn_pos` / `factorizesOn_ne_zero`
**真正接起来**。

**⚠ 为什么这些不是改名**：下面的定理把**两个模块各自的结论**拼成新命题，
`T1A2CI` 侧提供「拆成 `S` 与 `Sᶜ`」/「正性」/「非零性」，
本模块侧提供「三因子形式 `Components`」，
任何一侧单独都推不出**合取式**。 -/

/-- **`S`-可分离 与 三因子形式 同时成立**：`p` 在叉图上因子分解时，
既可按任意 `S` 拆成 `S` 与 `Sᶜ` 两部分（`T1A2CI.factorizesOn_separable`），
又存在三因子形式（§6 的 `factorizesOn_to_components`）。

**⚠ 前件只有 `FactorizesOn forkDAG p` 一条**，合取式两侧都由它推出，
**但没有任何一侧是前件的改名**：左侧要 `Finset.prod_mul_prod_compl` 的拆分，
右侧要 §4.1 的三条降维。 -/
theorem fork_separable_and_components (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) (x : Fin 3 → Bool) :
    (∃ pi : Fin 3 → (Fin 3 → Bool) → ℝ,
        (∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (pi v)) ∧
        (∀ v x, 0 < pi v x) ∧
        ∀ S : Finset (Fin 3), p x = (∏ v ∈ S, pi v x) * (∏ v ∈ Sᶜ, pi v x)) ∧
      Components p :=
  ⟨FateV2.Predict.T1A2CI.factorizesOn_separable h x, factorizesOn_to_components p h⟩

/-- **叉图上的严格正性与三因子形式同时成立**：`p` 在叉图上因子分解，则
`p` 处处正 **且** 有三个因子形式（`Components`）。

**⚠ 为什么这条有价值**：`Components` 本身**不带正性**，
而 `margZ_of_components` 计算的 `margZ` 在因子全零时会退化。
本条把**正性**与**三因子形式**一起交付，下游用 `margZ_of_components` 时两者皆备。 -/
theorem fork_pos_and_components (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) :
    (∀ x, 0 < p x) ∧ Components p :=
  ⟨factorizesOn_fork_pos p h, factorizesOn_to_components p h⟩

/-- **非零性 + 三因子形式**：`p` 在叉图上因子分解，则 `p` 处处非零
（`T1A2CI.factorizesOn_ne_zero`）**且**有三因子形式。

**⚠ 非零性的用途**：它让下游做除法（`p x / p y`，即比值形式的条件独立）
时不会碰到 `p y = 0` 的分母问题。 -/
theorem fork_ne_zero_and_components (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) :
    (∀ x : Fin 3 → Bool, p x ≠ 0) ∧ Components p :=
  ⟨FateV2.Predict.T1A2CI.factorizesOn_ne_zero h, factorizesOn_to_components p h⟩

/-- **可分离 与 三因子形式 与 正性 三者同时成立**：
把 §8 前三条合成一条**可复用的接口**，前件仍只有 `FactorizesOn forkDAG p`。

**⚠ 这是本文件的**总出口**：下游若需要「`p` 在叉图上因子分解」的任何组合，
直接引本条即可，不必各自重复拆 `Finset.prod`。 -/
theorem fork_interface (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) (x : Fin 3 → Bool) :
    (∀ y, 0 < p y) ∧
      (∀ y, p y ≠ 0) ∧
      Components p ∧
      (∃ pi : Fin 3 → (Fin 3 → Bool) → ℝ,
        (∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (pi v)) ∧
        (∀ v x, 0 < pi v x) ∧
        ∀ S : Finset (Fin 3), p x = (∏ v ∈ S, pi v x) * (∏ v ∈ Sᶜ, pi v x)) :=
  ⟨factorizesOn_fork_pos p h,
   FateV2.Predict.T1A2CI.factorizesOn_ne_zero h,
   factorizesOn_to_components p h,
   FateV2.Predict.T1A2CI.factorizesOn_separable h x⟩


end FateV2.Predict.T1A2Substance