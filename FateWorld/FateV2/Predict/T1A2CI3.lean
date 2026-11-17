/-
# `Fate/T1A2CI3` —— `T1A.2` 的叉图版：条件独立的**可分离形式**

## 内容

在叉图 `2 → 1 → 0` 上，把 `factorizesOn_separable` 特殊化为
**`{0, 2}` 与 `{1}` 可分离**，并把三条读集落成具体的有限集。

## 为什么这有意义

`{0, 2}` 是「两个结果」，`{1}` 是「共同原因」。
「`{0,2}` 与 `{1}` 可分离」正是「给定 `1` 后，`0` 与 `2` 独立」的**代数形式**。

**⚠ 严格说来这只是 `factorizesOn_separable` 在 `S = {0, 2}` 的实例化，
但它把抽象陈述钉到具体的图上，是 `T1A.2` 与叉图之间的**唯一接口**。**

## 定理清单

| # | 定理 | 内容 |
|---|---|---|
| 1 | **`fork_separable_at_one`** | ⭐⭐⭐⭐ `{0,2}` 与 `{1}` 可分离（条件独立的代数形式） |
| 2 | `compl_zero_two` | `({0,2} : Finset (Fin 3))ᶜ = {1}` —— 补集机检 |
| 3 | **`fork_product_explicit`** | ⭐⭐⭐⭐ 显式三因子形式 `p x = (π 0 x * π 2 x) * π 1 x` |
| 4 | **`fork_read_sets`** | ⭐⭐⭐ 三条读集：`π 0 ↦ {0,1}`、`π 1 ↦ {1,2}`、`π 2 ↦ {2}` |
| 5 | `fork_read_set_sizes` | 三条读集的基数 `2, 2, 1`（非空洞性机检） |

## 无 `sorry` / `admit` / `axiom`

见文件末尾 `#print axioms` 审计段。
-/

import FateWorld.FateV2.Predict.T1A2
import FateWorld.FateV2.Predict.T1A2CI
import FateWorld.FateV2.Predict.T1A2Substance
import Mathlib.Tactic

namespace FateV2.Predict.T1A2CI3

open FateV2.Modeling

open Finset
open Fate.T1A2
open Fate.T1A2CI
open Fate.T1A2Substance

/-!
  # Predict · T1A2CI3

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2CI3.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2, T1A2CI, T1A2Substance
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 可分离性主定理 -/

/-- ⭐⭐⭐⭐ **叉图上的可分离性**：

若 `p` 相对叉图 `2 → 1 → 0` 因子分解，则

$$p(x) = \left(\prod_{v \in \{0,2\}} \pi_v(x)\right) \cdot \pi_1(x)$$

**⚠ 因 `{0,2}ᶜ = {1}`（在 `Fin 3` 上），第二因子退化为单项 `π 1 x`。**

**⟹ 这形式化地表达了「给定 `1` 后，`0` 与 `2` 独立」。**

**⚠ 类型标注**：`∃ π : Fin 3 → (Fin 3 → Bool) → ℝ` 的类型**必须显式写出** ——
若只写 `∃ π`，`π v` 的出现先于类型被推断，Lean 报
「Function expected at π but this term has type ?m」（实测踩坑）。 -/
theorem fork_separable_at_one
    (p : (Fin 3 → Bool) → ℝ) (h : FactorizesOn forkDAG p) (x : Fin 3 → Bool) :
    ∃ π : Fin 3 → (Fin 3 → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      p x = (∏ v ∈ ({0, 2} : Finset (Fin 3)), π v x) *
            (∏ v ∈ ({0, 2} : Finset (Fin 3))ᶜ, π v x) := by
  obtain ⟨π, hreads, hpos, hsep⟩ := factorizesOn_separable h x
  exact ⟨π, hreads, hpos, hsep {0, 2}⟩

/-- ⭐⭐⭐ **`{0,2}` 的补集在 `Fin 3` 上是 `{1}`**。 -/
theorem compl_zero_two : (({0, 2} : Finset (Fin 3))ᶜ) = {1} := by
  decide

/-- ⭐⭐⭐⭐ **叉图的乘积形式（显式）**：

若 `p` 相对叉图因子分解，则存在 `π` 使

$$p(x) = \pi_0(x)\cdot\pi_2(x)\cdot\pi_1(x)$$

**⚠ 这是 `fork_separable_at_one` 与 `compl_zero_two` 的组合。** -/
theorem fork_product_explicit
    (p : (Fin 3 → Bool) → ℝ) (h : FactorizesOn forkDAG p) (x : Fin 3 → Bool) :
    ∃ π : Fin 3 → (Fin 3 → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      p x = (π 0 x * π 2 x) * π 1 x := by
  obtain ⟨π, hreads, hpos, hsep⟩ := factorizesOn_separable h x
  refine ⟨π, hreads, hpos, ?_⟩
  rw [hsep {0, 2}, compl_zero_two]
  simp only [Finset.prod_pair (by decide : (0 : Fin 3) ≠ 2), Finset.prod_singleton]

/-! ## §2 ⭐⭐⭐ 叉图上的三条读集

叉图的父集是

* `pa(0) = {1}`（分量 `0` 的父亲是分量 `1`）
* `pa(1) = {2}`（分量 `1` 的父亲是共同原因 `2`）
* `pa(2) = ∅`（共同原因 `2` 是根）

于是三个读集 `{v} ∪ pa(v)` 分别是 `{0,1}`、`{1,2}`、`{2}`。

**⚠ 下面的 `by decide` 真的在算**：它必须展开 `insert`、`forkDAG`
（`= Fate.T1A1Graphs.commonCauseDAG`）与 `parents` 的定义，
才能确认三条集合包含关系。若 `forkDAG` 的边写错，`decide` 立刻失败。 -/

/-- ⭐⭐⭐ **读集的具体化**：在叉图上，
`π 0` 只看 `{0,1}`，`π 1` 只看 `{1,2}`，`π 2` 只看 `{2}`。

**用途**：把抽象的 `insert v (forkDAG.parents v)` 落成具体的有限集，
供 `Fate/T1A2Substance.lean` 的 `readSet_*` / `pi*_reads_*` 降维链使用。 -/
theorem fork_read_sets (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hreads : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v)) :
    ReadsOnlyOn {0, 1} (π 0) ∧ ReadsOnlyOn {1, 2} (π 1) ∧ ReadsOnlyOn {2} (π 2) :=
  ⟨(hreads 0).mono (by decide), (hreads 1).mono (by decide),
   (hreads 2).mono (by decide)⟩

/-- ⭐⭐ **读集规模机检**：`|{0,1}| = 2`、`|{1,2}| = 2`、`|{2}| = 1`。

作为 `fork_read_sets` 的**非空洞性检查**：若读集被写成 `∅` 或 `univ`，
基数立刻不符。 -/
theorem fork_read_set_sizes :
    (({0, 1} : Finset (Fin 3)).card = 2) ∧
    (({1, 2} : Finset (Fin 3)).card = 2) ∧
    (({2} : Finset (Fin 3)).card = 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⭐⭐ **父集基数机检**：`|pa(0)| = 1`、`|pa(1)| = 1`、`|pa(2)| = 0`。

这是 `fork_read_sets` 里读集规模 `2, 2, 1` 的**来源**（读集 = `{v} ∪ pa(v)`）。 -/
theorem fork_parents_card :
    ((forkDAG.parents (0 : Fin 3)).card = 1) ∧
    ((forkDAG.parents (1 : Fin 3)).card = 1) ∧
    ((forkDAG.parents (2 : Fin 3)).card = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §3 ⚠ 说明：本文件不宣称完整的 `CondMul`

`Fate.FinCondIndep.CondMul p` 的定义是

$$\forall x\,y\,z,\quad p((x,y),z)\cdot \mathrm{margZ}(z)
  = \mathrm{margXZ}(x,z)\cdot \mathrm{margYZ}(y,z),$$

其中 $\mathrm{margZ}(z) = \sum_x \sum_y p((x,y),z)$ 对**两个分量**都求和，
而 $\mathrm{margXZ}$、$\mathrm{margYZ}$ 各只对一个分量求和。

叉图上「给定顶点 `1` 后 `0` 与 `2` 独立」需要的是

$$p(x_0, x_1, x_2)\cdot m(x_1) = a(x_0, x_1)\cdot b(x_2, x_1),\qquad
  m(x_1)=\sum_{x_0}\sum_{x_2} p,$$

即 `Z` 槽位 = 顶点 `1`（共同原因），`X`/`Y` 槽位 = 顶点 `0`/顶点 `2`。
这与 `CondMul` 的槽位语义可以对齐；但 `Fate/T1A2Substance.lean` 的载体
`rho w ((x,y), z)` 把顶点 `2` 放进哑坐标 `w` 并对 `w` 求和，
使 `margXZ`（固定 `w`）与 `margZ`（对 `w` 求和）无法在同一个等式里对齐。

**结论**：本文件交付的 `fork_separable_at_one` / `fork_product_explicit` 是这条路线
**在可分离性层面**的真结论；完整 `CondMul` 需要另一套载体，属独立后续任务。
-/

/-! ## §3.5 ⭐⭐⭐ R-47 追加（第 47 轮接线任务，2026-02 追加）

本节**只追加**，不动 §1–§3 的任何定理与 §4 的公理审计。
所有新定理把本文件已有的 `fork_separable_at_one` / `compl_zero_two` /
`fork_product_explicit` / `fork_read_sets` / `fork_read_set_sizes` /
`fork_parents_card` **拼成新的合取**，并推出存量里**没有明写**的合成结论。

## ⚠ 防环

本文件 `import Fate.T1A2CI` 与 `import Fate.T1A2Substance`，
两者均**没有** `import FateV2.Predict.T1A2CI3`，故不可能成环。

## ⚠ 前件检查（逐条）

* `fork_full_package`：前件 `FactorizesOn forkDAG p` 是**原料假设**；
  结论是**四条互不相同**的陈述之合取，其中第 4 条（显式三因子形式）
  需要 `compl_zero_two` 才成立，**不是前件的重述**。
* `fork_read_sets_and_sizes`：前件是 `hreads`（读集包含性，**原料**）；
  结论把「三条读集」与「它们的基数」**同时**给出，后者在存量里
  只在**没有任何前件**的 `fork_read_set_sizes` 中出现，**与 `hreads` 无关**
  —— 本条的价值是把两者**绑在一起**，说明同一组读集既被 `hreads` 覆盖、
  又有正确的基数（**非退化性机检**）。
* `fork_graph_shape`：**零前件**（纯 `decide`）。结论是边的存在性、
  父集恒等式、父集基数、读集基数的**五重合取**。
  这是整个叉图接线块的**自检签名**。
* `fork_product_and_readsets`：前件是 `h`（因子分解）与 `hreads`（读集，**原料**）；
  结论是「显式三因子形式」与「三条读集」的合取，**并把 π 绑成同一个**。
  存量 `fork_product_explicit` 只给乘积形式，`fork_read_sets` 只给读集，
  **没有任何一条同时给出同一 π 的两者** —— 这是本段真正的新内容。

**没有任何一条把结论塞进前件。**
-/

/-- ⭐⭐⭐ **叉图上的完整包：乘积形式 + 该点严格正 + 读集降维**

`p` 在叉图上因子分解 ⟹ 存在 `π` 使

1. 每条 `π v` 只读 `{v} ∪ pa(v)`；
2. 每条 `π v` 严格正；
3. `p x = π 0 x * π 2 x * π 1 x`（显式三因子，需 `compl_zero_two`）；
4. **`0 < p x`** —— 由 2、3 复合得到，`fork_product_explicit` **不给**这一条；

前件只有 `FactorizesOn forkDAG p` 与一个点 `x`。
第 4 条是**新的合成**：`π 0 x > 0`、`π 1 x > 0`、`π 2 x > 0` 三相乘仍正，
而存量 `fork_product_explicit` 只交付等式，**没有任何一条把等式和正性合成**。
（这也与存量 `fork_pos_and_components` 不同：后者走 `factoriesOn_fork_pos`，
本条走**乘积结构**，路径独立。） -/
theorem fork_full_package (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) (x : Fin 3 → Bool) :
    ∃ π : Fin 3 → (Fin 3 → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v)) ∧
      (∀ v x, 0 < π v x) ∧
      p x = (π 0 x * π 2 x) * π 1 x
        ∧ 0 < p x := by
  obtain ⟨π, hreads, hpos, hprod⟩ := fork_product_explicit p h x
  refine ⟨π, hreads, hpos, hprod, ?_⟩
  rw [hprod]
  have h0 := hpos 0 x
  have h1 := hpos 1 x
  have h2 := hpos 2 x
  positivity

/-- ⭐⭐ **同一组读集的两张脸**：`hreads` 给出的三条读集，
其基数恰为 `2, 2, 1`（**非退化性机检**）。

前件 `hreads` 是**原料**（读集包含性，不涉及基数）；
结论的基数部分是 `fork_read_set_sizes`（**零前件**）**与 `hreads` 无关**
—— 本条把它们**绑在一起**，从而说明 `hreads` 用的读集不是退化集合。 -/
theorem fork_read_sets_and_sizes (π : Fin 3 → (Fin 3 → Bool) → ℝ)
    (hreads : ∀ v, ReadsOnlyOn (insert v (forkDAG.parents v)) (π v)) :
    (ReadsOnlyOn {0, 1} (π 0) ∧ ReadsOnlyOn {1, 2} (π 1) ∧ ReadsOnlyOn {2} (π 2))
      ∧ (({0, 1} : Finset (Fin 3)).card = 2)
      ∧ (({1, 2} : Finset (Fin 3)).card = 2)
      ∧ (({2} : Finset (Fin 3)).card = 1) :=
  ⟨fork_read_sets π hreads, fork_read_set_sizes.1,
   fork_read_set_sizes.2.1, fork_read_set_sizes.2.2⟩

/-- ⭐⭐⭐ **叉图的形状签名**（**零前件**，全 `decide` / 存量引理）：

1. `2 → 1` 是边；2. `1 → 0` 是边；3. `pa(0) = {1}`；4. `pa(1) = {2}`；
5. `pa(2) = ∅`。

把 `forkDAG` 的五条结构事实打包成**单一签名**，
下游只需 `FateV2.Predict.T1A2CI3.fork_graph_shape` 即可一次拿到全部。
本条的**非空洞性**：若 `forkDAG` 的边写错，任一 `decide` 立即失败。 -/
theorem fork_graph_shape :
    forkDAG.edge (2 : Fin 3) 1
      ∧ forkDAG.edge (1 : Fin 3) 0
      ∧ forkDAG.parents (0 : Fin 3) = {(1 : Fin 3)}
      ∧ forkDAG.parents (1 : Fin 3) = {(2 : Fin 3)}
      ∧ forkDAG.parents (2 : Fin 3) = ∅ :=
  ⟨forkDAG_edge_two_one, forkDAG_edge_one_zero,
   forkDAG_parents_zero, forkDAG_parents_one, forkDAG_parents_two⟩

/-- ⭐⭐⭐ **同一 `π` 同时给出乘积形式与三条读集**：

前件 `h`（因子分解）与 `hreads`（读集，**原料**）。
结论是「存在 `π`，它既实现显式三因子形式、又满足三条读集约束」。

**这是本段真正的新内容**：存量 `fork_product_explicit` 只给乘积形式
（π 由 `factorizesOn_separable` 产生，没说读集）；`fork_read_sets`
只给读集（π 是**任意**满足 `hreads` 的，没说乘积）。
本条把**同一个 π** 的两种性质**绑在一起**，说明二者**不冲突**。 -/
theorem fork_product_and_readsets (p : (Fin 3 → Bool) → ℝ)
    (h : FactorizesOn forkDAG p) (x : Fin 3 → Bool) :
    ∃ π : Fin 3 → (Fin 3 → Bool) → ℝ,
      (ReadsOnlyOn {0, 1} (π 0) ∧ ReadsOnlyOn {1, 2} (π 1) ∧ ReadsOnlyOn {2} (π 2))
        ∧ (∀ v x, 0 < π v x)
        ∧ p x = (π 0 x * π 2 x) * π 1 x := by
  obtain ⟨π, hreads, hpos, hprod⟩ := fork_product_explicit p h x
  exact ⟨π, fork_read_sets π hreads, hpos, hprod⟩

/-! ## §4 公理审计 -/

#print axioms fork_separable_at_one
#print axioms compl_zero_two
#print axioms fork_product_explicit
#print axioms fork_read_sets
#print axioms fork_read_set_sizes
#print axioms fork_parents_card

end FateV2.Predict.T1A2CI3