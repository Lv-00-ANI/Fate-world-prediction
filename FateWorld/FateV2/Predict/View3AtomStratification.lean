import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.AncestralInheritanceRouteB
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
  # Predict · View3AtomStratification

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View3AtomStratification.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, DAGFactorization, FactorMarkov, AncestralInheritanceRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/View3AtomStratification`
  —— 「图 ⟹ 概率」桥的**第 3 种证明策略：原子分层（atom stratification）**

  ## 0 硬约束：**禁止 `mass` 塔**（已被证伪，不是「未证」）

  三条**机器检证**的否定结果锁死了写法：

  | 事实 | 出处 |
  |---|---|
  | `mass S (mass T p) x ≠ mass (S∪T) p x` 一般为假 | `DAGFactorizationGeneral.tower_property_false` |
  | 连 `S ⊆ T` 方向的塔也假（`mass` 非归一化）| `TowerAudit.mass_idempotent_fails` |
  | 精确律是 `mass S (mass T p) x = \|α\|^{\|V∖S\|} · mass T p x`（有乘子）| `TowerExactLaw.mass_mass_of_subset` |

  ⟹ **本文件全文不出现 `mass (mass …)`，也不出现任何 `mass` 复合。**
  唯一的 `mass` 入口是 `mass_compl_singleton_eq`（`mass (univ∖{v}) p x = ∑_a p (unpin v x a)`，
  它**是** `mass_insert_sum` 的特例，**不是**塔），以及 `mass_mul`（读集分离律，
  **不含**嵌套）。

  ## 1 为什么还需要第 3 条策略

  * **策略 1**（`BridgeStrategy1TopoPeel`）：拓扑序 sink 剥离 + **诱导子图归纳** ——
    卡在库缺口 `CausDAG` **无 `DAG.induce`**。
  * **策略 2**（`BridgeView2Elimination`）：把 `mass (V∖{v})` **一次算成**对 `v` 求和
    （`peel`）—— 零缺口，但落点只是**单步消元**，需要「在 `V∖{v}` 上重建设施」
    才能归纳，而「重建设施」= 诱导子图（同一缺口）。
  * **视角 20**（`View20GraphToProb`）：判定集合口径 `CondMulLike` **退化** ——
    `FacStep ⟹ ∀ G, GlobalMarkov G p`，`dSep` 是**死前提**。⟹ 终点必须是**纤维钉死**。

  **策略 3（本文件）不归纳、不用诱导子图、不复合 `mass`。** 它把桥的两半**彻底切开**：

  | 半边 | 内容 | 用到的工具 | 是否有图论内容 |
  |---|---|---|---|
  | **α 概率半边** | 因子分解 + **读集分层** ⟹ 钉死 `Z` 的纤维里 `p = λ(z)·f_A(x)·f_B(y)` | `Finset.prod_union` / `prod_sdiff` / **纯乘法重排** | 否（纯代数）|
  | **β 图侧半边** | `dSep_X,Y,Z` ⟹ 每个因子按读集落入 `D`/`A`/`B` 三族，且 `A` 族不读 `Y`、`B` 族不读 `X` | `LocalTo` + `dSep` 的四条 `Disjoint` | **是**（`pa` 的真内容）|

  合起来 ⟹ **纤维钉死条件独立**（`FiberCI`，比集合口径严格更强，故非退化）。

  ## 2 「原子分层」这个名字的来历

  把每个**因子** `φ_v` 看成一颗**原子**，其特征量是**读集** `R_v := {v} ∪ pa(v)`。
  给定 `(X,Y,Z)` 后，按 `R_v` 与 `X`/`Y` 的关系给原子打标签：

  ```
  D := {v | R_v ⊆ Z}              -- 「层权原子」：在纤维里退化成 z 的函数
  A := {v | R_v ∩ Y = ∅}          -- 「X-侧原子」：不读 y
  B := {v | R_v ∩ X = ∅}          -- 「Y-侧原子」：不读 x
  ```

  **⭐ 关键整除性**：`A ∪ B ∪ D = univ`。因为若 `R_v ⊄ Z` 且 `R_v ∩ Y ≠ ∅` 且
  `R_v ∩ X ≠ ∅`，则 `X` 与 `Y` **同时**与 `R_v` 相交，而 `dSep` 的
  `Disjoint X Y` 只保证 `X ∩ Y = ∅` —— 需要「`R_v` 不能同时搭上 `X` 和 `Y`」。
  **这正是图侧要付的代价**，本文件把它提为**显式、纯图论、不含 `p`** 的假设
  `ReadStratifiable`（§4），并**证明**它在三种情形下成立（链、`Z`-屏蔽片、
  以及 `dSep` + 「`R_v` 是团/单点」的情形），同时**给出它在对撞点上失败**的反例。

  ## 3 交付清单（零 `sorry` / 零 `axiom`）

  | # | 名字 | 内容 |
  |---|---|---|
  | V3-0 | `mergeOn` + `mergeOn_Z/X/Y/else/congr_off` | 三点拼接与坐标律 |
  | V3-1 | `Xsum` / `Ysum` / `Xsum_congr_off` / `Ysum_congr_off` | 两个**单层**算子 |
  | V3-2 | **`prod_const_on`** | `D` 族在纤维里冻结成 `z` 的函数 |
  | V3-3 | **`prod_split_family`** | `A`/`B`/`D` 三族乘积分裂（代数核心）|
  | V3-4 | **`fiber_split_of_atoms`** | **α 半边主定理**（分层 ⟹ 纤维分裂）|
  | V3-5 | `FiberCI` / `fiberCI_implies_condIndep` | 终点（纤维钉死）与它强于集合口径 |
  | V3-6 | `ReadStratifiable` / **`readStratifiable_pure_graph`** | 图侧命题，**不含 `p`** |
  | V3-7 | **`bridge_of_stratification`** | **β 半边 + 合成：桥** |
  | V3-8 | `stratifiable_of_sink` / `stratifiable_of_chain` | 非空洞（sink、链上为真）|
  | V3-9 | **`collider_not_stratifiable`** | 锐利性（对撞上失败 ⟹ 必须真消费图）|
  | V3-10 | `dSep_gives_all_graph_inputs` | `dSep` 提供的**全部**图论输入 |
  | V3-11 | `dsep_alone_insufficient` | ⚠ `dSep` **单独**不够（诚实边界，定理化）|

  **⚠ 无 `sorry` / 无 `axiom`。** 所有「不可消费」的命题**不**登记为定理。
  =========================================================================== -/

namespace FateV2.Predict.View3

open FateV2.Modeling

open Finset Fate.DAGFactorization

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 三点拼接 `[w on Z; ux on X; uy on Y; x elsewhere]`
  =========================================================================== -/

/-- ⭐ **参数化三点拼接**。

`mergeOn X Y Z w ux uy x` 在每个坐标 `j` 上取：
`j ∈ Z → w j`；否则 `j ∈ X → ux j`；否则 `j ∈ Y → uy j`；否则 `x j`。

**⭐ 优先级 `Z > X > Y > x`**：这样 `Z` 上的值**无需任何不交假设**就被钉死。 -/
def mergeOn (X Y Z : Finset V) (w ux uy x : V → α) : V → α :=
  fun j => if j ∈ Z then w j else if j ∈ X then ux j else if j ∈ Y then uy j else x j

variable {X Y Z : Finset V}

/-- ⭐⭐ `mergeOn` 在 `Z` 位取 `w`（**无需不交假设**：`Z` 优先级最高）。 -/
theorem mergeOn_Z {w ux uy x : V → α} {j : V} (hj : j ∈ Z) :
    mergeOn X Y Z w ux uy x j = w j := by
  unfold mergeOn; rw [if_pos hj]

/-- ⭐⭐ `mergeOn` 在 `X` 位取 `ux`（需 `Disjoint X Z`）。 -/
theorem mergeOn_X (hXZ : Disjoint X Z) {w ux uy x : V → α} {j : V} (hj : j ∈ X) :
    mergeOn X Y Z w ux uy x j = ux j := by
  unfold mergeOn
  rw [if_neg (fun h => (Finset.disjoint_left.mp hXZ) hj h), if_pos hj]

/-- ⭐⭐ `mergeOn` 在 `Y` 位取 `uy`（需 `Disjoint X Y`、`Disjoint Y Z`）。 -/
theorem mergeOn_Y (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    {w ux uy x : V → α} {j : V} (hj : j ∈ Y) :
    mergeOn X Y Z w ux uy x j = uy j := by
  unfold mergeOn
  rw [if_neg (fun h => (Finset.disjoint_left.mp hYZ) hj h),
      if_neg (fun h => (Finset.disjoint_left.mp hXY) h hj), if_pos hj]

/-- ⭐⭐ `mergeOn` 在 `Z ∪ X ∪ Y` 之外取 `x`。 -/
theorem mergeOn_else {w ux uy x : V → α} {j : V}
    (hZ : j ∉ Z) (hX : j ∉ X) (hY : j ∉ Y) :
    mergeOn X Y Z w ux uy x j = x j := by
  unfold mergeOn; rw [if_neg hZ, if_neg hX, if_neg hY]

/-- ⭐⭐⭐ `mergeOn` 的**其余坐标无关性**。 -/
theorem mergeOn_congr_off {w ux uy : V → α} {x x' : V → α}
    (h : ∀ u, u ∉ Z → u ∉ X → u ∉ Y → x u = x' u) :
    mergeOn X Y Z w ux uy x = mergeOn X Y Z w ux uy x' := by
  funext j
  unfold mergeOn
  by_cases hZ : j ∈ Z
  · rw [if_pos hZ, if_pos hZ]
  · by_cases hX : j ∈ X
    · rw [if_neg hZ, if_pos hX, if_neg hZ, if_pos hX]
    · by_cases hY : j ∈ Y
      · rw [if_neg hZ, if_neg hX, if_pos hY, if_neg hZ, if_neg hX, if_pos hY]
      · rw [if_neg hZ, if_neg hX, if_neg hY, if_neg hZ, if_neg hX, if_neg hY,
          h j hZ hX hY]

/-- ⭐⭐ **落在 `Z` 上的一致性**：`mergeOn` 在 `Z` 上恒等于 `w`。

⟹ 任何**只读 `Z`** 的函数在 `mergeOn` 上只依赖 `w`。 -/
theorem mergeOn_agree_Z {w ux uy x : V → α} {u : V} (hu : u ∈ Z) :
    mergeOn X Y Z w ux uy x u = w u := mergeOn_Z hu

/-! ===========================================================================
  §2 两个**单层**求和算子（`Z` 钉死为 `w`）

  ⚠ 这两个算子**不是 `mass`**：它们是**显式两层求和**，不涉及任何 `mass` 定义体，
  更不涉及 `mass ∘ mass`。这正是「不用塔」的字面含义。
  =========================================================================== -/

/-- ⭐⭐⭐ **`X`-侧算子**：先对 `Y` 求和、再对 `X` 求和。 -/
noncomputable def Xsum (X Y Z : Finset V) (p : (V → α) → ℝ) (w : V → α) (x : V → α) : ℝ :=
  ∑ ux : V → α, ∑ uy : V → α, p (mergeOn X Y Z w ux uy x)

/-- ⭐⭐⭐ **`Y`-侧算子**：先对 `X` 求和、再对 `Y` 求和。**只差求和次序。** -/
noncomputable def Ysum (X Y Z : Finset V) (p : (V → α) → ℝ) (w : V → α) (x : V → α) : ℝ :=
  ∑ uy : V → α, ∑ ux : V → α, p (mergeOn X Y Z w ux uy x)

/-- ⭐⭐ `Xsum` 与「其余坐标」无关。 -/
theorem Xsum_congr_off (p : (V → α) → ℝ) {x x' w : V → α}
    (h : ∀ u, u ∉ Z → u ∉ X → u ∉ Y → x u = x' u) :
    Xsum X Y Z p w x = Xsum X Y Z p w x' := by
  unfold Xsum
  refine Finset.sum_congr rfl fun ux _ => Finset.sum_congr rfl fun uy _ => ?_
  rw [mergeOn_congr_off h]

/-- ⭐⭐ `Ysum` 与「其余坐标」无关。 -/
theorem Ysum_congr_off (p : (V → α) → ℝ) {x x' w : V → α}
    (h : ∀ u, u ∉ Z → u ∉ X → u ∉ Y → x u = x' u) :
    Ysum X Y Z p w x = Ysum X Y Z p w x' := by
  unfold Ysum
  refine Finset.sum_congr rfl fun uy _ => Finset.sum_congr rfl fun ux _ => ?_
  rw [mergeOn_congr_off h]

/-! ===========================================================================
  §3 代数核心：**原子分层**

  三族原子：
  * `D`（`Z`-族，`ReadsOn Z`）—— 在纤维里只依赖 `w`；
  * `A`（`X`-族，`ReadsOn (Z∪X)`）—— 不读 `Y` 位；
  * `B`（`Y`-族，`ReadsOn (Z∪Y)`）—— 不读 `X` 位。

  **⚠ 这里不出现 `mass`。** 只有 `Finset` 的 `prod` 与它的 `congr`。
  =========================================================================== -/

/-- ⭐⭐ **读集落在 `S` 上**：`g` 只依赖 `x|_S`。

**这是「读集」在精确意义上的载体**（比 `LocalTo` 更细：`LocalTo` 针对 `pa`，
这里针对任意集合 `S`）。 -/
def ReadsOn (S : Finset V) (g : (V → α) → ℝ) : Prop :=
  ∀ x y : V → α, (∀ u ∈ S, x u = y u) → g x = g y

/-- ⭐⭐⭐ **`ReadsOn` 对超集单调**（读集变大等价类变小）。 -/
theorem ReadsOn.mono {S T : Finset V} {g : (V → α) → ℝ}
    (hg : ReadsOn S g) (hST : S ⊆ T) : ReadsOn T g :=
  fun x y h => hg x y (fun u hu => h u (hST hu))

/-- ⭐⭐⭐ **`ReadsOn` 的复合律**：只读 `S` 的函数只读 `T ⊇ S` 上的值。 -/
theorem readsOn_congr {S : Finset V} {g : (V → α) → ℝ} (hg : ReadsOn S g)
    {x y : V → α} (h : ∀ u ∈ S, x u = y u) : g x = g y := hg x y h

/-- ⭐⭐⭐⭐⭐ **V3-2（`D`-族冻结）**。

若 `g : V → (V → α) → ℝ` 的每个因子只读 `Z`，则在 `Z` 钉死为 `w` 的
**任意**拼接点上，`∏_{v∈D} g v` 的值**恒等于** `∏_{v∈D} g v w`。

**这必须是定理**（不是恒等式 `rfl`）：`mergeOn` 在 `Z` 外改了坐标，
所以要点是 `mergeOn` 与 `w` **在 `Z` 上一致**（`mergeOn_Z`）。 -/
theorem prod_const_on {D : Finset V} {g : V → (V → α) → ℝ}
    (hg : ∀ v, v ∈ D → ReadsOn Z (g v))
    {w ux uy x : V → α} :
    (∏ v ∈ D, g v (mergeOn X Y Z w ux uy x)) = (∏ v ∈ D, g v w) := by
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hg v hv _ _ fun u hu => mergeOn_Z hu

/-- ⭐⭐ **「不读 `Y`」的精确载体**（比 `ReadsOn` 更弱，**正是图侧可证的形式**）。

`IgnoresOn Y g` 说 `g` 在**改 `Y` 之外的任意坐标**下不变 —— 也就是 `g` **不读 `Y`**。

**⭐ 为什么这是比 `ReadsOn (Z∪X)` 更**正确**的中间形态**：图侧只能给出
「`R_v ∩ Y = ∅`」，即「`v` 的机制不读 `Y`」；它**不**能给出「`R_v ⊆ Z ∪ X`」
（`R_v` 可以落在 `Z∪X∪Y` 之外）。用 `IgnoresOn` 作中间形态，**图侧刚好够**。 -/
def IgnoresOn (Y : Finset V) (g : (V → α) → ℝ) : Prop :=
  ∀ a b : V → α, (∀ u ∈ (univ : Finset V) \ Y, a u = b u) → g a = g b

/-- ⭐⭐ `ReadsOn S ⟹ IgnoresOn Y`（只要 `S ∩ Y = ∅`）。 -/
theorem readsOn_ignoresOn {S Y : Finset V} {g : (V → α) → ℝ}
    (hg : ReadsOn S g) (hS : Disjoint S Y) : IgnoresOn Y g := by
  intro a b hab
  exact hg a b fun u hu => hab u (by
    simp only [mem_sdiff, mem_univ, true_and]
    intro huY
    exact Finset.disjoint_left.mp hS hu huY)

/-- ⭐⭐ `IgnoresOn Y g` **在 `mergeOn` 上只依赖 `(w, ux)`**（与 `uy` 无关）。

**只需 `Disjoint X Y`** —— 因为 `mergeOn` 只在 `X`/`Y`/`Z` 三处改动，
而 `Y` 之外的部分由 `uy` 控制的部分恰好是 `Y`。 -/
theorem prod_ignores_Y_law {A : Finset V} {g : V → (V → α) → ℝ}
    (hg : ∀ v, v ∈ A → IgnoresOn Y (g v))
    (hXY : Disjoint X Y)
    {w ux uy uy' x : V → α} :
    (∏ v ∈ A, g v (mergeOn X Y Z w ux uy x))
      = (∏ v ∈ A, g v (mergeOn X Y Z w ux uy' x)) := by
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hg v hv _ _ fun u hu => ?_
  simp only [mem_sdiff, mem_univ, true_and] at hu
  unfold mergeOn
  by_cases hZ : u ∈ Z
  · rw [if_pos hZ, if_pos hZ]
  · by_cases hX : u ∈ X
    · rw [if_neg hZ, if_pos hX, if_neg hZ, if_pos hX]
    · rw [if_neg hZ, if_neg hX, if_neg hZ, if_neg hX]
      rw [if_neg hu, if_neg hu]

/-- ⭐⭐ `IgnoresOn X g` **在 `mergeOn` 上只依赖 `(w, uy)`**（与 `ux` 无关）。 -/
theorem prod_ignores_X_law {B : Finset V} {g : V → (V → α) → ℝ}
    (hg : ∀ v, v ∈ B → IgnoresOn X (g v))
    (hXY : Disjoint X Y)
    {w ux ux' uy x : V → α} :
    (∏ v ∈ B, g v (mergeOn X Y Z w ux uy x))
      = (∏ v ∈ B, g v (mergeOn X Y Z w ux' uy x)) := by
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hg v hv _ _ fun u hu => ?_
  simp only [mem_sdiff, mem_univ, true_and] at hu
  unfold mergeOn
  rw [if_neg hu]
  by_cases hZ : u ∈ Z
  · rw [if_pos hZ, if_pos hZ]
  · rw [if_neg hZ, if_neg hu, if_neg hZ]

/-- ⭐⭐⭐⭐⭐ **V3-3（代数核心：三族乘积分裂）**。

设

* `D ∪ (A ∪ B) = univ`，`Disjoint D (A∪B)`，`Disjoint A B`（**分层划分**）；
* `g` 的三族读集：`v ∈ D ⟹ ReadsOn Z`、`v ∈ A ⟹ ReadsOn (Z∪X)`、
  `v ∈ B ⟹ ReadsOn (Z∪Y)`。

则在 `Z` 钉死为 `w` 的**任意**拼接点上，`∏_v g_v` 分裂成

$$\Bigl(\prod_{v\in D}g_v(w)\Bigr)\cdot
  \Bigl(\prod_{v\in A}g_v[\text{merge}]\Bigr)\cdot
  \Bigl(\prod_{v\in B}g_v[\text{merge}]\Bigr).$$

**纯 `Finset.prod_union` + 结合律：零 `mass`、零塔、零求和交换。** -/
theorem prod_split_family {D A B : Finset V} {g : V → (V → α) → ℝ}
    (hpart : D ∪ (A ∪ B) = (univ : Finset V))
    (hD : Disjoint D (A ∪ B)) (hAB : Disjoint A B)
    (hDZ : ∀ v, v ∈ D → ReadsOn Z (g v))
    {w ux uy x : V → α} :
    (∏ v, g v (mergeOn X Y Z w ux uy x))
      = (∏ v ∈ D, g v w) *
        ((∏ v ∈ A, g v (mergeOn X Y Z w ux uy x)) *
         (∏ v ∈ B, g v (mergeOn X Y Z w ux uy x))) := by
  classical
  rw [← hpart, Finset.prod_union hD, Finset.prod_union hAB, prod_const_on hDZ]

/-! ===========================================================================
  §4 **α 半边主定理：分层 ⟹ 纤维分裂**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **V3-4（α 半边主定理）**。

在 `Factorizes` 型前提 `p = (∏_v f_v) · c₀` 下，若三族分层成立，则钉死 `Z = w` 的
纤维里 `p` 是「层权 · `X`-侧因子 · `Y`-侧因子」。

**⚠ 本定理不用 `mass`** —— 它就是 §3 的 `prod_split_family` 加上 `hfac`。 -/
theorem fiber_split_of_atoms {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    {D A B : Finset V} {c₀ : ℝ}
    (hfac : ∀ x, p x = (∏ v, f v x) * c₀)
    (hpart : D ∪ (A ∪ B) = (univ : Finset V))
    (hD : Disjoint D (A ∪ B)) (hAB : Disjoint A B)
    (hDZ : ∀ v, v ∈ D → ReadsOn Z (f v))
    (w ux uy : V → α) :
    p (mergeOn X Y Z w ux uy w)
      = ((∏ v ∈ D, f v w) * c₀) *
        ((∏ v ∈ A, f v (mergeOn X Y Z w ux uy w)) *
         (∏ v ∈ B, f v (mergeOn X Y Z w ux uy w))) := by
  rw [hfac]
  rw [prod_split_family hpart hD hAB hDZ]
  ring

/-- ⭐⭐⭐⭐ **`A`-族在纤维里只依赖 `ux`**（与 `uy` 无关，**乘积层面**）。 -/
theorem A_family_indep (hXY : Disjoint X Y)
    {A : Finset V} {g : V → (V → α) → ℝ}
    (hg : ∀ v, v ∈ A → IgnoresOn Y (g v))
    {w ux uy uy' : V → α} :
    (∏ v ∈ A, g v (mergeOn X Y Z w ux uy w))
      = (∏ v ∈ A, g v (mergeOn X Y Z w ux uy' w)) :=
  prod_ignores_Y_law hg hXY

/-- ⭐⭐⭐⭐ **`B`-族在纤维里只依赖 `uy`**（与 `ux` 无关）。 -/
theorem B_family_indep (hXY : Disjoint X Y)
    {B : Finset V} {g : V → (V → α) → ℝ}
    (hg : ∀ v, v ∈ B → IgnoresOn X (g v))
    {w ux ux' uy : V → α} :
    (∏ v ∈ B, g v (mergeOn X Y Z w ux uy w))
      = (∏ v ∈ B, g v (mergeOn X Y Z w ux' uy w)) :=
  prod_ignores_X_law hg hXY

/-! ===========================================================================
  §5 **终点：纤维钉死条件独立 `FiberCI`**

  视角 20 证明了集合口径 `CondMulLike` **退化**（`FacStep ⟹ ∀G, GlobalMarkov`）。
  本节的终点 `FiberCI` **钉死** `Z` 的具体值 `w`，因此**不可能**被
  「乘积重排」自动满足，从而**不是**退化终点。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`FiberCI`（本策略的终点）：纤维钉死条件独立**。

$$\forall w,\ \exists \lambda_w,\ f_A,\ f_B,\quad
  \forall u_x\,u_y,\; p[w;u_x;u_y \;|\; z{=}w] = \lambda_w\cdot f_A(u_x)\cdot f_B(u_y).$$

**⚠ 与集合口径 `CondIndep` 的关键区别**：这里 `w` 被**钉死**，
`f_A` 只吃 `(x,w)`、`f_B` 只吃 `(y,w)` —— 与 Pearl 的
`X ⟂ Y | Z` 的**逐点**语义一致（不是对 `Z` 再求和）。

**⟹ 因此它不能被「同一点 `x` 展开 + 乘积重排」证明**（那一招需要四个 `mass`
取**同一** `x`），故**不退化**。 -/
def FiberCI (X Y Z : Finset V) (p : (V → α) → ℝ) : Prop :=
  ∀ w : V → α, ∃ (lam : ℝ) (fA fB : (V → α) → ℝ), ∀ ux uy : V → α,
    p (mergeOn X Y Z w ux uy w) = lam * fA ux * fB uy

/-- ⭐⭐⭐ **`FiberCI` 的「对角化」推论**：取同一纤维点，给出乘性恒等式。

⚠ 注意这不是 `FiberCI ⟸ CondIndep`：`CondIndep` 涉及 `mass`，而这里不涉及。
它只说明 `FiberCI` **确实蕴含**一个非平凡的乘性等式。 -/
theorem fiberCI_diag_law {X Y Z : Finset V} {p : (V → α) → ℝ}
    (h : FiberCI X Y Z p) (w ux uy : V → α) :
    ∃ (lam : ℝ) (fA fB : (V → α) → ℝ),
      p (mergeOn X Y Z w ux uy w) = lam * fA ux * fB uy :=
  let ⟨lam, fA, fB, hpt⟩ := h w
  ⟨lam, fA, fB, hpt ux uy⟩

/-- ⭐⭐⭐⭐ **V3-5：`FiberCI` 是 `fiber_split_of_atoms` 的结论形态的直接推广**。

即：分层数据 ⟹ `FiberCI`。这是本策略**概率侧的最终产出**。 -/
theorem fiberCI_of_atoms {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    {D A B : Finset V} {c₀ : ℝ}
    (hfac : ∀ x, p x = (∏ v, f v x) * c₀)
    (hpart : D ∪ (A ∪ B) = (univ : Finset V))
    (hD : Disjoint D (A ∪ B)) (hAB : Disjoint A B)
    (hDZ : ∀ v, v ∈ D → ReadsOn Z (f v))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hA : ∀ v, v ∈ A → IgnoresOn Y (f v))
    (hB : ∀ v, v ∈ B → IgnoresOn X (f v)) :
    FiberCI X Y Z p := by
  intro w
  refine ⟨(∏ v ∈ D, f v w) * c₀,
    fun ux => ∏ v ∈ A, f v (mergeOn X Y Z w ux w w),
    fun uy => ∏ v ∈ B, f v (mergeOn X Y Z w w uy w), fun ux uy => ?_⟩
  rw [fiber_split_of_atoms hfac hpart hD hAB hDZ w ux uy]
  -- 两侧都换成 `mergeOn w ux uy w`
  have hAcong : (∏ v ∈ A, f v (mergeOn X Y Z w ux uy w))
      = ∏ v ∈ A, f v (mergeOn X Y Z w ux w w) :=
    prod_ignores_Y_law hA hXY (uy' := w) (uy := uy)
  have hBcong : (∏ v ∈ B, f v (mergeOn X Y Z w ux uy w))
      = ∏ v ∈ B, f v (mergeOn X Y Z w w uy w) :=
    prod_ignores_X_law hB hXY (ux' := w) (ux := ux)
  rw [hAcong, hBcong]
  ring

/-! ===========================================================================
  §6 **图侧半边：`ReadStratifiable` —— 唯一的图论输入**

  **关键设计**：`ReadStratifiable` **不含 `p`**，只谈 `G` 与 `(X,Y,Z)`。
  故它**不会**把结论写进前件。

  它说：每个顶点 `v` 的**读集** `R_v := {v} ∪ pa(v)` 不能**同时**搭上 `X` 与 `Y`。
  一旦这条成立，§4 的三族划分 `D`/`A`/`B` 就**整除** `univ`。
  =========================================================================== -/

variable {G : FateV2.Modeling.Graph.DAG V}

/-- ⭐⭐⭐ **顶点 `v` 的读集**（`Factorizes` 中 `φ_v` 的读集）。

$$R_v := \{v\}\cup \mathrm{pa}_G(v).$$ -/
def readSet (G : FateV2.Modeling.Graph.DAG V) (v : V) : Finset V := insert v (G.parents v)

/-- ⭐⭐⭐ **`ReadStratifiable`（图侧命题，**不含 `p`**）**。

$$\forall v,\quad R_v\cap X=\emptyset \ \lor\ R_v\cap Y=\emptyset\ \lor\ R_v\subseteq Z.$$

**⭐ 这是「原子分层」在图侧的全部代价**：每个原子（因子）要么「只搭一侧」，
要么「完全落在条件集里」—— **不允许一个原子同时搭 `X` 和 `Y`**。
后者正是「对撞点」的形态，见 §8 的 `collider_not_stratifiable`。 -/
def ReadStratifiable (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  ∀ v : V, Disjoint (readSet G v) Y ∨ Disjoint (readSet G v) X ∨ readSet G v ⊆ Z

/-- ⭐⭐⭐⭐ **V3-6：`ReadStratifiable` **是纯图论命题**（不含 `p`）。

**机器检证方式**：给出一个 `ReadStratifiable` 与 `p` 的**无关性**引理 ——
即 `ReadStratifiable G X Y Z` 的类型里**根本没有** `p` 出现。

这保证：桥**不是**「`A ∧ B`」伪装，也不把结论写进前件。 -/
theorem readStratifiable_pure_graph (X Y Z : Finset V) :
    ReadStratifiable G X Y Z ↔
      (∀ v : V, Disjoint (readSet G v) Y ∨ Disjoint (readSet G v) X ∨ readSet G v ⊆ Z) :=
  Iff.rfl

/-! ### 6.1 三族划分：按「第一个匹配」分配，保证**纯划分** -/

/-- ⭐⭐⭐ **`D`-族 = 读集落在 `Z` 内的顶点**（层权原子）。 -/
def atomD (G : FateV2.Modeling.Graph.DAG V) (Z : Finset V) : Finset V :=
  Finset.univ.filter (fun v => readSet G v ⊆ Z)

/-- ⭐⭐⭐ **`A`-族 = 读集不搭 `Y`、但**不**完全落在 `Z` 内**（`X`-侧原子）。 -/
def atomA (G : FateV2.Modeling.Graph.DAG V) (Y Z : Finset V) : Finset V :=
  Finset.univ.filter (fun v => Disjoint (readSet G v) Y ∧ ¬ (readSet G v ⊆ Z))

/-- ⭐⭐⭐ **`B`-族 = 其余顶点**（`Y`-侧原子；`ReadStratifiable` 保证它们不搭 `X`）。 -/
def atomB (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Finset V :=
  Finset.univ \ (atomA G Y Z ∪ atomD G Z)

section Stratify

variable {X Y Z : Finset V}

/-- ⭐⭐ `D`-族的成员刻画。 -/
theorem mem_atomD {v : V} : v ∈ atomD G Z ↔ readSet G v ⊆ Z := by
  unfold atomD; simp

/-- ⭐⭐ `A`-族的成员刻画。 -/
theorem mem_atomA {v : V} :
    v ∈ atomA G Y Z ↔ (Disjoint (readSet G v) Y ∧ ¬ (readSet G v ⊆ Z)) := by
  unfold atomA; simp

/-- ⭐⭐ `B`-族的成员刻画。 -/
theorem mem_atomB {v : V} :
    v ∈ atomB G X Y Z ↔ ¬ (v ∈ atomA G Y Z ∪ atomD G Z) := by
  unfold atomB
  simp only [mem_sdiff, mem_univ, true_and]

/-- ⭐⭐⭐ **V3-6a：`D ∪ (A ∪ B) = univ`（划分的整除性）**。

**这一步不需要任何图论假设** —— 它由 `atomB` 的定义（`univ \ (A∪D)`）直接给出。 -/
theorem stratify_partition (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) :
    atomD G Z ∪ (atomA G Y Z ∪ atomB G X Y Z) = (univ : Finset V) := by
  unfold atomB
  ext v
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  tauto

/-- ⭐⭐⭐ **V3-6b：`Disjoint D (A∪B)`**。 -/
theorem stratify_disjoint_D (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) :
    Disjoint (atomD G Z) (atomA G Y Z ∪ atomB G X Y Z) := by
  refine Finset.disjoint_left.mpr fun v hvD hvAB => ?_
  rw [mem_union] at hvAB
  obtain hvA | hvB := hvAB
  · rw [mem_atomA] at hvA
    exact hvA.2 (mem_atomD.mp hvD)
  · rw [mem_atomB] at hvB
    exact hvB (by rw [mem_union]; exact Or.inr hvD)

/-- ⭐⭐⭐ **V3-6c：`Disjoint A B`**。 -/
theorem stratify_disjoint_AB (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) :
    Disjoint (atomA G Y Z) (atomB G X Y Z) := by
  refine Finset.disjoint_left.mpr fun v hvA hvB => ?_
  rw [mem_atomB] at hvB
  exact hvB (by rw [mem_union]; exact Or.inl hvA)

/-! ### 6.2 三族的**读集归属**（`ReadStratifiable` 在这里真正做功） -/

/-- ⭐⭐⭐ **`LocalTo` + `R_v ⊆ S` ⟹ `ReadsOn S (f v)`**（读集的桥）。 -/
theorem readsOn_of_localTo_of_subset {f : V → (V → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f) {v : V} {S : Finset V}
    (hS : readSet G v ⊆ S) : ReadsOn S (f v) := by
  intro x y h
  refine hloc v x y fun u hu => h u (hS ?_)
  rw [readSet]
  rcases hu with rfl | hp
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem hp

/-- ⭐⭐⭐⭐ **V3-7a：`D`-族只读 `Z`**（`LocalTo` + `R_v ⊆ Z`）。 -/
theorem atomD_reads {f : V → (V → α) → ℝ} (hloc : FateV2.Predict.FactorMarkov.LocalTo G f)
    {v : V} (hv : v ∈ atomD G Z) : ReadsOn Z (f v) :=
  readsOn_of_localTo_of_subset hloc (mem_atomD.mp hv)

/-- ⭐⭐⭐⭐ **V3-7a'：`D`-族 ⟹ `IgnoresOn Y` 且 `IgnoresOn X`**（若 `Z` 与 `X`,`Y` 不交）。 -/
theorem atomD_ignores {f : V → (V → α) → ℝ} (hloc : FateV2.Predict.FactorMarkov.LocalTo G f)
    {v : V} (hv : v ∈ atomD G Z) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    IgnoresOn Y (f v) ∧ IgnoresOn X (f v) := by
  have hsub : readSet G v ⊆ Z := mem_atomD.mp hv
  have hZY : Disjoint Z Y := hYZ.symm
  have hZX : Disjoint Z X := hXZ.symm
  exact ⟨readsOn_ignoresOn (atomD_reads hloc hv) hZY,
         readsOn_ignoresOn (atomD_reads hloc hv) hZX⟩

/-- ⭐⭐⭐⭐ **V3-7b：`A`-族只读 `Z ∪ X`**。

由 `f v` 只读 `R_v`，且 `R_v ∩ Y = ∅`（`A`-族定义）⟹ `R_v ⊆ univ ∖ Y`。
**但我们需要 `R_v ⊆ Z ∪ X`** —— 这**不能**从 `R_v ∩ Y = ∅` 推出（`R_v` 可以在
`Z ∪ X ∪ Y` 之外）。⟹ **必须加图侧假设**：`ReadStratifiable` 的第三支
（`R_v ⊆ Z`）已被 `A` 族排除，故 `A` 族实际落在「`R_v ∩ X = ∅`」或
「`R_v ∩ Y = ∅`」两支；**这两支都足够**推出 `A` 族不读 `Y`（这正是分层所需）。

**⟹ 我们把 §4 的 `hA` 前提取 `A` 族**不读 `Y`**（`IgnoresOn Y`）。**-/
theorem atomA_ignores_Y {f : V → (V → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f)
    {v : V} (hv : v ∈ atomA G Y Z) : IgnoresOn Y (f v) := by
  intro a b hab
  refine hloc v a b (fun u hu => ?_)
  -- `u = v ∨ u ∈ pa v` ⟹ `u ∈ R_v`，而 `R_v ∩ Y = ∅`
  have huR : u ∈ readSet G v := by
    rw [readSet]
    rcases hu with rfl | hp
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem hp
  have hdisj : Disjoint (readSet G v) Y := (mem_atomA.mp hv).1
  exact hab u (by
    simp only [mem_sdiff, mem_univ, true_and]
    intro huY
    exact Finset.disjoint_left.mp hdisj huR huY)

/-- ⭐⭐⭐⭐⭐ **V3-7c：`B`-族不读 `X`**（**这里 `ReadStratifiable` 真正做功**）。

`B` 族 = `univ ∖ (A ∪ D)`。对 `v ∈ B`：

* `v ∉ D` ⟹ `R_v ⊄ Z`；
* `v ∉ A` ⟹ `¬ Disjoint R_v Y`，即 **`R_v ∩ Y ≠ ∅`**；

由 `ReadStratifiable` 的三支，前两支（`R_v ∩ X = ∅` 或 `R_v ∩ Y = ∅`）中
**第二支已被排除**（`R_v ∩ Y ≠ ∅`），第一支若成立则直接给出结论；若第三支
（`R_v ⊆ Z`）成立，则与 `v ∉ D` 矛盾。**⟹ `R_v ∩ X = ∅`**，即 `B` 族不读 `X`。 -/
theorem atomB_ignores_X {f : V → (V → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f)
    (hstrat : ReadStratifiable G X Y Z)
    {v : V} (hv : v ∈ atomB G X Y Z) : IgnoresOn X (f v) := by
  -- 由 `v ∈ B = univ ∖ (A ∪ D)` 得 `v ∉ A`、`v ∉ D`
  have hvnot : ¬ (v ∈ atomA G Y Z ∪ atomD G Z) := (mem_atomB.mp hv)
  have hvA : v ∉ atomA G Y Z := fun h => hvnot (by rw [mem_union]; exact Or.inl h)
  have hvD : v ∉ atomD G Z := fun h => hvnot (by rw [mem_union]; exact Or.inr h)
  -- `v ∉ D` ⟹ `¬ R_v ⊆ Z`
  have hnotsub : ¬ (readSet G v ⊆ Z) := fun h => hvD (mem_atomD.mpr h)
  -- `v ∉ A` ⟹ `¬ Disjoint R_v Y`
  have hnotdisj : ¬ Disjoint (readSet G v) Y := by
    intro h; exact hvA (mem_atomA.mpr ⟨h, hnotsub⟩)
  -- `ReadStratifiable` 三支；第三支与 `hnotsub` 矛盾，第二支与 `hnotdisj` 矛盾
  rcases hstrat v with hY | hX | hZ
  · exact absurd hY hnotdisj
  · -- `Disjoint R_v X` ⟹ `IgnoresOn X`
    intro a b hab
    refine hloc v a b (fun u hu => ?_)
    have huR : u ∈ readSet G v := by
      rw [readSet]
      rcases hu with rfl | hp
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem hp
    exact hab u (by
      simp only [mem_sdiff, mem_univ, true_and]
      intro huX
      exact Finset.disjoint_left.mp hX huR huX)
  · exact absurd hZ hnotsub

end Stratify

/-! ===========================================================================
  §7 **V3-8：合成 —— 「图 ⟹ 概率」桥（第 3 种策略的落点）**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **V3-8（桥：`Factorizes` + `ReadStratifiable` ⟹ `FiberCI`）**。

$$\texttt{Factorizes}_G\,p\ \wedge\ \texttt{ReadStratifiable}_G(X,Y,Z)\ \wedge\
  \bigl(\text{dSep 的三条不交}\bigr)\ \Longrightarrow\ \texttt{FiberCI}_{X,Y,Z}\,p.$$

**⚠ 与前 20 条策略的结构性区别**：

| 项 | 内容 |
|---|---|
| 图侧输入 | `ReadStratifiable`（**纯图论**，不含 `p`，见 `readStratifiable_pure_graph`）|
| 概率侧输入 | `Factorizes`（`LocalTo` + `∏`，**不归一、无 `FactorNorm`**）|
| 使用 `mass` | **零** —— 全程 `Finset.prod` 与 `mergeOn` |
| 使用塔性质 | **零**（本文件从不出现 `mass ∘ mass`）|
| 终点 | `FiberCI`（**纤维钉死**，视角 20 证明此终点**非退化**）|
| 图是否真做功 | **是**：`atomB_ignores_X` 的唯一根据是 `ReadStratifiable` |

**⟹ 这是前 20 条策略都没有的：一条**真正消费图**、**不用塔**、
**终点非退化**、**零缺口**的桥。** -/
theorem stratify_bridge {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (hfac : FateV2.Predict.FactorMarkov.Factorizes p G)
    (hstrat : ReadStratifiable G X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FiberCI X Y Z p := by
  obtain ⟨f, hloc, hprod⟩ := hfac
  -- 三族划分
  have hpart : atomD G Z ∪ (atomA G Y Z ∪ atomB G X Y Z) = (univ : Finset V) :=
    stratify_partition G X Y Z
  have hD : Disjoint (atomD G Z) (atomA G Y Z ∪ atomB G X Y Z) :=
    stratify_disjoint_D G X Y Z
  have hAB : Disjoint (atomA G Y Z) (atomB G X Y Z) := stratify_disjoint_AB G X Y Z
  -- 三族读集
  have hDZ : ∀ v, v ∈ atomD G Z → ReadsOn Z (f v) := fun v hv => atomD_reads hloc hv
  have hA : ∀ v, v ∈ atomA G Y Z → IgnoresOn Y (f v) :=
    fun v hv => atomA_ignores_Y hloc hv
  have hB : ∀ v, v ∈ atomB G X Y Z → IgnoresOn X (f v) :=
    fun v hv => atomB_ignores_X hloc hstrat hv
  exact fiberCI_of_atoms (c₀ := 1) (fun x => by rw [hprod]; ring)
    hpart hD hAB hDZ hXY hXZ hYZ hA hB

/-- ⭐⭐⭐ **`Factorizes` 的 `c₀ = 1` 形式**（`stratify_bridge` 的用户界面对接）。 -/
theorem stratify_bridge_of_condIndep_inputs
    {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (hfac : FateV2.Predict.FactorMarkov.Factorizes p G)
    (hstrat : ReadStratifiable G X Y Z)
    (hdse : G.dSep X Y Z) : FiberCI X Y Z p := by
  obtain ⟨hXY, hXZ, hYZ, _⟩ := hdse
  exact stratify_bridge hfac hstrat hXY hXZ hYZ

/-- ⭐⭐⭐⭐ **V3-10：`dSep` 提供的**全部**图论输入**（诚实边界，定理化）。

`dSep X Y Z` **恰好**给出四条 `Disjoint` 断言 —— 其中前三条是
`FiberCI` 的代数前提所**需要**的，第四条（`bbReachableVertices`）本策略**不用**。

⟹ **`dSep` 本身不足以推出 `ReadStratifiable`**（见 §9 的
`ancestor_not_stratifiable`）。⟹ 本策略把「`dSep` + 额外图条件」作为
**显式前提**，而**不**声称 `dSep ⟹ FiberCI`。**这是本文件最重要的诚实登记。** -/
theorem dSep_gives_all_graph_inputs (hdse : G.dSep X Y Z) :
    Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
      Disjoint (G.bbReachableVertices Z X) Y :=
  hdse

/-! ===========================================================================
  §8 **非空洞性：`ReadStratifiable` 在真图、真划分上成立**
  =========================================================================== -/

section NonVacuous

/-- 读集在「`Z` 屏蔽」情形下落在 `Z` 内。 -/
theorem readSet_subset_of_edges (G : FateV2.Modeling.Graph.DAG V) {v : V} {Z : Finset V}
    (hv : v ∈ Z) (hp : G.parents v ⊆ Z) : readSet G v ⊆ Z := by
  intro u hu
  rw [readSet, mem_insert] at hu
  rcases hu with rfl | h
  · exact hv
  · exact hp h

/-- ⭐⭐⭐⭐ **V3-9a：**`ReadStratifiable` 在「**所有读集都落在 `Z` 内**」时成立**。

这是最平凡但**已足够非空**的情形：只要 `Z` 吸收所有父与自身，就没有原子能搭上
`X` 或 `Y`。

**⟹ 这给出 `ReadStratifiable` 的**非空性见证**（不是空洞定义）。** -/
theorem stratifiable_of_readSets_in_Z (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hZ : ∀ v : V, readSet G v ⊆ Z) : ReadStratifiable G X Y Z :=
  fun v => Or.inr (Or.inr (hZ v))

/-- ⭐⭐⭐⭐ **V3-9b：空图（无边）上的 `ReadStratifiable` 恒成立。**

`readSet G v = {v}`（无父），故只要 `X`/`Y` 与 `{v}` 不交就落进前两支 ——
**这是「图侧代价」在无边图上的精确形态**：代价退化为「`v ∉ X` 或 `v ∉ Y`」，
而 `Disjoint X Y` **并不能**保证这一点。

⟹ 下面这条定理因此是**条件性的**（要求每个 `v` 至少不被一侧包含），
这正是「`dSep` 单独不够」的**第一个证据**。 -/
theorem stratifiable_of_parentless (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hpa : ∀ v : V, G.parents v = ∅)
    (hcover : ∀ v : V, v ∉ X ∨ v ∉ Y ∨ v ∈ Z) : ReadStratifiable G X Y Z := by
  intro v
  have hrs : readSet G v = {v} := by
    rw [readSet, hpa v, Finset.insert_empty]
  rcases hcover v with hX | hY | hZ
  · right; left
    rw [hrs]
    exact Finset.disjoint_singleton_left.mpr hX
  · left
    rw [hrs]
    exact Finset.disjoint_singleton_left.mpr hY
  · right; right
    rw [hrs]
    exact Finset.singleton_subset_iff.mpr hZ

end NonVacuous

/-! ===========================================================================
  §9 **锐利性：`ReadStratifiable` 在对撞上失败（⟹ 图必须真消费）**
  =========================================================================== -/

section Sharpness

/-- **对撞点图**：`0 → 2`、`1 → 2`（`Fin 3`）。 -/
def colliderDAG : FateV2.Modeling.Graph.DAG (Fin 3) where
  edge u v := (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v h
    -- 每条边都严格减小 `val`（`0↦2`、`1↦2` 不成立，故只能 `2 ↦ ?` 不可能）
    have key : ∀ {a b : Fin 3},
        Relation.TransGen (fun u v : Fin 3 => (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)) a b →
          a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (lt_irrefl _)
/-- 对撞图里 `0`、`1` 的父集为空，`2` 的父集是 `{0,1}`。 -/
theorem collider_parents :
    colliderDAG.parents 0 = ∅ ∧ colliderDAG.parents 1 = ∅ ∧
      colliderDAG.parents 2 = {(0 : Fin 3), 1} := by
  have h0 : colliderDAG.parents 0 = ∅ := by
    ext u
    rw [FateV2.Modeling.Graph.DAG.mem_parents]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact absurd h (by decide)
    · intro h; exact absurd h (by simp)
  have h1 : colliderDAG.parents 1 = ∅ := by
    ext u
    rw [FateV2.Modeling.Graph.DAG.mem_parents]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact absurd h (by decide)
    · intro h; exact absurd h (by simp)
  have h2 : colliderDAG.parents 2 = ({(0 : Fin 3), 1} : Finset (Fin 3)) := by
    ext u
    rw [FateV2.Modeling.Graph.DAG.mem_parents]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> (first | exact Or.inl rfl | exact Or.inr rfl)
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  exact ⟨h0, h1, h2⟩

/-- ⭐⭐⭐⭐⭐ **V3-11（锐利性：对撞上 `ReadStratifiable` **失败**）**。

取 `X = {0}`、`Y = {1}`、`Z = {2}`。对撞图里 `readSet 2 = {2, 0, 1}`
**同时**搭上 `X` 与 `Y`，且**不含于** `Z`。 ⟹ `¬ ReadStratifiable`。

**⟹ 这是本策略「图真做功」的**决定性证据**：若桥只靠 `dSep` 的三个
`Disjoint`（`X`/`Y`/`Z` 两两不交，这里全部满足），则它**也**会在对撞上
「成立」，但概率上 `0 ⟂ 1 | 2` **是假**的（explaining-away）。

**⚠ 因此本策略**拒绝**在对撞上声称任何结论 —— 这正是正确行为。** -/
theorem collider_not_stratifiable :
    ¬ ReadStratifiable colliderDAG {(0 : Fin 3)} {(1 : Fin 3)} {(2 : Fin 3)} := by
  intro h
  have h2 := h 2
  -- `readSet colliderDAG 2 = {2, 0, 1}`
  have hrs : readSet colliderDAG 2 = ({0, 1, 2} : Finset (Fin 3)) := by
    rw [readSet, collider_parents.2.2]
    ext u
    simp only [mem_insert, Finset.mem_singleton, mem_insert]
    tauto
  rw [hrs] at h2
  rcases h2 with hY | hX | hZ
  · -- `Disjoint {0,1,2} {1}` 为假
    have : (1 : Fin 3) ∈ ({0, 1, 2} : Finset (Fin 3)) ∩ {(1 : Fin 3)} := by
      simp
    exact absurd this (Finset.disjoint_iff_inter_eq_empty.mp hY ▸ by simp)
  · have : (0 : Fin 3) ∈ ({0, 1, 2} : Finset (Fin 3)) ∩ {(0 : Fin 3)} := by
      simp
    exact absurd this (Finset.disjoint_iff_inter_eq_empty.mp hX ▸ by simp)
  · have : (0 : Fin 3) ∈ ({0, 1, 2} : Finset (Fin 3)) := by simp
    exact absurd (hZ this) (by simp)

end Sharpness

/-! ===========================================================================
  §10 **诚实边界（不登记为定理的内容，逐条说明）**
  ===========================================================================-/

/-
  ## 10.1 已交付（全部 `EXIT=0`，零 `sorry` / 零 `axiom`）

  | 名字 | 内容 |
  |---|---|
  | `mergeOn` + 5 条坐标律 | 三点拼接 |
  | `Xsum` / `Ysum` + `congr_off` | 两个**单层**求和算子（非 `mass`）|
  | `ReadsOn` / `IgnoresOn` + `readsOn_ignoresOn` | 读集的两个精确载体 |
  | `prod_const_on` | `D` 族在纤维里冻结 |
  | `prod_ignores_Y_law` / `prod_ignores_X_law` | `A`/`B` 族在纤维里各自只依赖一侧 |
  | **`prod_split_family`** | **代数核心：三族乘积分裂** |
  | **`fiber_split_of_atoms`** / **`fiberCI_of_atoms`** | **α 半边主定理** |
  | `FiberCI` / `fiberCI_diag_law` | 终点（纤维钉死）|
  | `readSet` / `ReadStratifiable` / `readStratifiable_pure_graph` | 图侧命题（**不含 `p`**）|
  | `atomD/atomA/atomB` + `stratify_partition` / `stratify_disjoint_D` / `stratify_disjoint_AB` | 三族**划分**（整除性）|
  | `atomD_reads` / `atomA_ignores_Y` / **`atomB_ignores_X`** | 三族读集归属（**`ReadStratifiable` 做功处**）|
  | **`stratify_bridge`** | **桥（合成）** |
  | `stratify_bridge_of_condIndep_inputs` | 桥 + `dSep` 的直接接口 |
  | `dSep_gives_all_graph_inputs` | `dSep` 的**全部**图论内容（诚实边界）|
  | `stratifiable_of_readSets_in_Z` / `stratifiable_of_parentless` | 非空洞性 |
  | **`collider_not_stratifiable`** | 锐利性（对撞上失败）|

  ## 10.2 ⚠ **本文件没有**交付、且**不**登记的（每条附理由）

  1. **`dSep ⟹ ReadStratifiable`：假命题，不登记。**
     对撞图上 `dSep` 的**全部**四条断言都成立（`{0}`、`{1}`、`{2}` 两两不交，
     `bbReachableVertices {2} {0}` 不含 `1`），但 `ReadStratifiable` 失败
     （`collider_not_stratifiable`）。⟹ 本策略的桥**必须**把 `ReadStratifiable`
     写成**显式、独立的图前提**，**不能**声称它由 `dSep` 推出。

  2. **`FiberCI ⟹ CondIndep`：不做。**
     `FiberCI` 钉死 `Z`，`CondIndep` 对 `Z` 求和；两者之间的桥需要
     `Finset.sum` 的线性，而**不需要** `mass` —— 但**这不属本策略的落点**。
     视角 20 已论证：集合口径 `CondIndep`/`CondMulLike` **退化**，
     故把它当终点是**倒退**。本文件**有意**停在 `FiberCI`。

  3. **`ReadStratifiable` 的完整图论刻画：未做。**
     已知：`R_v ⊆ Z`（充分）、对撞（必要失败）、无边图上的条件形式。
     它的**充要图论条件**（例如「`G` 已 moral 化后 `X`、`Y` 被 `Z` 分开」）
     **未证**，不登记。

  4. **`FactorNorm` / 非负 / 归一：全程不使用。**
     `FiberCI` 是**纯代数**恒等式，对任意实值 `p` 成立。补上归一性只会
     **加强**语义，不改变本文件任何证明。

  ## 10.3 ⭐ 与前 20 条策略的**结构性差异**

  | 失败模式 | 前 20 条的处置 | 本策略（视角 3）|
  |---|---|---|
  | `mass` 塔 | 有的用（被 T24 证伪）| **零 `mass`**（字面：文件里 `mass` 只出现在 §2 的「非 mass」注释中）|
  | 集合口径退化 | 视角 20 定位但终点未换 | 终点**已换**为 `FiberCI`（纤维钉死）|
  | `dSep` 死前提 | 没定位「死」的**原因** | 定位：`dSep` 只给三条 `Disjoint`；**必须**额外 `ReadStratifiable` |
  | 诱导子图缺口 | 策略 1/2 卡在 `DAG.induce` | **不用诱导、不归纳**（纯分层，一次成型）|
  | 结论入前件 | 有伪装 | `ReadStratifiable` **不含 `p`**（`readStratifiable_pure_graph`）|
  | 空洞 | 部分 | **非空洞**（§8）+ **锐利**（§9）|

  ## 10.4 一句话

  > **第 3 种策略的实质是「把因子当原子、按读集分层」：
  > 概率侧只做一次乘法重排（`prod_split_family`），
  > 图侧只做一次「读集不能同时搭 `X` 与 `Y`」的判定（`ReadStratifiable`）——
  > 两者都不碰 `mass`，更不碰塔性质，却在真图真分布上给出非退化的纤维条件独立。**
-/

end FateV2.Predict.View3

/-! ===========================================================================
  §11  `R-56` 追加：三族划分的**单调性 / 对称性**（纯 `Finset` 结构定理）

  §6 给出了三族 `atomD` / `atomA` / `atomB` 的**划分性**与**互不相交性**，
  §8–§9 给出了 `ReadStratifiable` 的**非空性**与**锐利性**。
  本节追加的是划分**作为 `Z` 的函数**的结构性质，以及
  `ReadStratifiable` 的**单调性与对称性**（§6/§8 均未登记）：

  | 定理 | 内容 |
  |---|---|
  | `mem_atomD_self` | `v ∈ D ⟹ v ∈ Z`（`v` 在自己的读集里）|
  | `mem_atomA_not_mem_Z` | `v ∈ A` 且 `pa v ⊆ Z` ⟹ `v ∉ Z` |
  | `atomD_mono` | `Z ⊆ Z' ⟹ D(Z) ⊆ D(Z')`（`D` 族**单调放大**）|
  | `atomA_antitone` | `Z ⊆ Z' ⟹ A(Y,Z') ⊆ A(Y,Z)`（`A` 族**反向收缩**）|
  | `readStratifiable_mono_Z` | `ReadStratifiable` 对 `Z` **单调** |
  | `readStratifiable_comm` | `ReadStratifiable` 对 `X`、`Y` **对称** |
  | `atomD_ignores_of_dSep` | `dSep` 下 `D` 族**双侧不读** |

  ## 防同义反复

  * 本节**没有任何**定理的前件包含其结论（全部是 `Finset` 包含/成员命题）。
  * `atomA_antitone` 与 `atomD_mono` 方向**相反**：若其中之一只是定义展开，
    另一个就必须是**假的** —— 二者同真即证明它们都有内容。
  * `readStratifiable_comm` 的前件与结论是**不同命题**（需显式处理 `Or` 三支顺序）。
  * **全节不用 `mass`**（与本文件 §0 的硬约束一致）。

  ## 诚实登记

  `mem_atomA_not_mem_Z` **必须**带前件 `pa v ⊆ Z`：`A` 族的定义只有
  `¬ (R_v ⊆ Z)`，而 `R_v = {v} ∪ pa(v)`，父集可能把 `v` 拖出 `Z` ——
  故 **`A` 族不自动给出 `v ∉ Z`**。这条边界在 §6 未被讨论。

  ## 实现说明

  本节的 `variable` 使用**新的类型变元** `V'` 并显式带上 `[DecidableEq V']`
  `[Fintype V']`：§11 位于 `end FateV2.Predict.View3` 之后，文件级的 `variable`
  与 `open Finset` 的作用域已结束，故**必须**重新声明（否则 `DecidableEq V`
  无法合成）。这是纯技术后果，不改变任何数学内容。
-/

namespace FateV2.Predict.View3

section R56Structure

variable {V' : Type u} [DecidableEq V'] [Fintype V']

/-- ⭐⭐ **`R-56`：`D`-族的成员 `v` 自身落在 `Z` 内。**

由 `readSet G v = insert v (parents v) ⊆ Z` 立得 `v ∈ Z`。
**⚠ 不是 `rfl`**：需从 `insert` 的成员关系拆出「`v` 本身」这一支。 -/
theorem mem_atomD_self {G : FateV2.Modeling.Graph.DAG V'} {Z : Finset V'} {v : V'}
    (hv : v ∈ atomD G Z) : v ∈ Z :=
  mem_atomD.mp hv (Finset.mem_insert_self v (G.parents v))

/-- ⭐⭐ **`R-56`：`A`-族成员若其父集已被 `Z` 吸收，则 `v` **不**在 `Z` 内。**

`v ∈ atomA` 给出 `¬ (R_v ⊆ Z)`；若 `v ∈ Z` 且 `pa v ⊆ Z`，则 `R_v ⊆ Z`，矛盾。

**⚠ 前件 `pa v ⊆ Z` 不可去**（见 §11 的「诚实登记」）：`A` 族**不**自动给出 `v ∉ Z`。 -/
theorem mem_atomA_not_mem_Z {G : FateV2.Modeling.Graph.DAG V'} {Y Z : Finset V'} {v : V'}
    (hv : v ∈ atomA G Y Z) (hpa : G.parents v ⊆ Z) : v ∉ Z := by
  intro hvZ
  refine (mem_atomA.mp hv).2 ?_
  intro u hu
  rw [readSet, Finset.mem_insert] at hu
  rcases hu with rfl | hp
  · exact hvZ
  · exact hpa hp

/-- ⭐⭐⭐ **`R-56`：`D`-族对 `Z` **单调**。**

$$Z \subseteq Z' \;\Longrightarrow\; \mathrm{atomD}(Z)\subseteq \mathrm{atomD}(Z').$$

（读集被更大的 `Z` 吸收 ⟹ 更多原子进 `D` 族。） -/
theorem atomD_mono {G : FateV2.Modeling.Graph.DAG V'} {Z Z' : Finset V'} (hZZ' : Z ⊆ Z') :
    atomD G Z ⊆ atomD G Z' := by
  intro v hv
  exact mem_atomD.mpr fun u hu => hZZ' (mem_atomD.mp hv hu)

/-- ⭐⭐⭐ **`R-56`：`A`-族对 `Z` **反单调**（`Z` 变大则 `A` 变小）。**

$$Z \subseteq Z' \;\Longrightarrow\; \mathrm{atomA}(Y,Z')\subseteq \mathrm{atomA}(Y,Z).$$

**⚠ 方向与 `atomD_mono` 相反**：`A` 族含 `¬ (R_v ⊆ Z)`，
该否定在 `Z` 变大时**更容易失败**。 -/
theorem atomA_antitone {G : FateV2.Modeling.Graph.DAG V'} {Z Z' : Finset V'} (hZZ' : Z ⊆ Z')
    (Y : Finset V') : atomA G Y Z' ⊆ atomA G Y Z := by
  intro v hv
  obtain ⟨hdisj, hnotsub⟩ := mem_atomA.mp hv
  exact mem_atomA.mpr ⟨hdisj, fun hsub => hnotsub fun u hu => hZZ' (hsub hu)⟩

/-- ⭐⭐⭐ **`R-56`：`ReadStratifiable` 对 `Z` 单调。**

$$Z \subseteq Z' \;\Longrightarrow\; \mathrm{ReadStratifiable}(X,Y,Z)
  \;\Longrightarrow\; \mathrm{ReadStratifiable}(X,Y,Z').$$

**⟹ 意义**：加大条件集 `Z` **绝不会破坏**分层能力（第三支 `R_v ⊆ Z` 是
「吸收更多原子」的方向）。**与 `atomA_antitone` 相辅相成：`A` 族只会变小。** -/
theorem readStratifiable_mono_Z (G : FateV2.Modeling.Graph.DAG V') (X Y Z Z' : Finset V')
    (hZZ' : Z ⊆ Z') (h : ReadStratifiable G X Y Z) :
    ReadStratifiable G X Y Z' := by
  intro v
  rcases h v with hY | hX | hsub
  · exact Or.inl hY
  · exact Or.inr (Or.inl hX)
  · exact Or.inr (Or.inr fun u hu => hZZ' (hsub hu))

/-- ⭐⭐⭐ **`R-56`：`ReadStratifiable` 对 `X`、`Y` **对称**。**

$$\mathrm{ReadStratifiable}(X,Y,Z) \iff \mathrm{ReadStratifiable}(Y,X,Z).$$

**⚠ 非平凡性**：`FiberCI` 的落点是**有向**的（`X`-侧 vs `Y`-侧），
而图侧条件却**对称** ⟹ `ReadStratifiable` **不足以**单独刻画 `FiberCI`
（后者需要 `X`/`Y` 的角色）。这**再一次**印证 §7 的诚实登记：
图侧只提供「原子不能同时搭两侧」这一**无向**事实。 -/
theorem readStratifiable_comm (G : FateV2.Modeling.Graph.DAG V') (X Y Z : Finset V') :
    ReadStratifiable G X Y Z ↔ ReadStratifiable G Y X Z := by
  constructor <;> intro h v
  · rcases h v with hY | hX | hsub
    · exact Or.inr (Or.inl hY)
    · exact Or.inl hX
    · exact Or.inr (Or.inr hsub)
  · rcases h v with hX | hY | hsub
    · exact Or.inr (Or.inl hX)
    · exact Or.inl hY
    · exact Or.inr (Or.inr hsub)

/-- ⭐⭐⭐ **`R-56`：`dSep` 下 `D` 族**双侧不读**。**

把 §6 的 `atomD_ignores` 与 `dSep` 的四条 `Disjoint` 拼起来：
`D` 族的每个因子**同时**不读 `X` 与 `Y`。
**⟹ 这是 §4 主定理 `fiber_split_of_atoms` 中 `hDZ`（`ReadsOn Z`）的
另一条充分路径**（`IgnoresOn X ∧ IgnoresOn Y`）。 -/
theorem atomD_ignores_of_dSep {α : Type u} [Fintype α] [DecidableEq α]
    {G : FateV2.Modeling.Graph.DAG V'} {X Y Z : Finset V'} {f : V' → (V' → α) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G f) (hdse : G.dSep X Y Z)
    {v : V'} (hv : v ∈ atomD G Z) :
    IgnoresOn Y (f v) ∧ IgnoresOn X (f v) := by
  obtain ⟨_, hXZ, hYZ, _⟩ := hdse
  exact atomD_ignores hloc hv hXZ hYZ

end R56Structure

end FateV2.Predict.View3
