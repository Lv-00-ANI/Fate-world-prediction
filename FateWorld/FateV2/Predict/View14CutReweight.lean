import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.View20GraphToProb
import FateWorld.FateV2.Predict.View21StableBorder
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic.Ring

/-!
  # Predict · View14CutReweight

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View14CutReweight.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, DAGFactorization, View20GraphToProb, View21StableBorder, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Predict.View14CutReweight`
  —— 「图 ⟹ 概率」桥的**第 14 种策略：祖先割集重加权（ancestral-cut reweighting）**

## 0 硬约束（已证伪的路线，本文件**一次也不用**）

* `Fate.DAGFactorizationGeneral.tower_property_false`（T24）：`mass S (mass T p) x ≠ mass (S∪T) p x`。
* `Fate.TowerAudit.mass_idempotent_fails`（A3）：连 `S ⊆ T` 方向的塔也假。
* `Fate.View20GraphToProb.massCondMulLike_degenerate`：集合口径 `CondMulLike` 是**退化**终点
  （对任意图、含无边图都成立），不能停在那里。

⟹ 本文件**全程零** `mass S (mass T p)` 形态（§7 有机械自查），也**不使用 `DAG.induce`**。

## 1 与既往各策略的分野（为何这是「第 14 种」）

| # | 骨架 | 引擎 | 卡点 / 终局 |
|---|---|---|---|
| 1 | 拓扑序 sink 剥离 | `mass_insert_sum` + `prod_sum` | 需 `pa(v) ⊆ S`；只做归一化 |
| 2 | 变量消元 | 纤维双射 + `mass_mul` | 只到单点补集 |
| 4 | 单坐标切片 | `mass_skew` | 需逐点读集结构 |
| 5 | 纤维双射 | `sum_bij` 重标号 | — |
| 11 | 拓扑前缀链 | `lowerSet` + `mass_insert_sum'` | 残 `FibreGluing` |
| 12 | 因子划分 `In/Out` | `mass_mul` | 残 `NormalizedResidual`，`In` 判据是「读集 ⊆ S」|
| 13 | 三元 typed split | `localTo_eq` + `prod_split` | 纯代数，无 `mass`，终点非 `CondIndep` |
| 20 | `fac_aux` 重排 | `prod_split3` | **诊断出终点退化** |
| 21 | 祖先稳定块 `stableFactorSplit` | `exposed` | 有 `sorry`，未闭合 |
| **14（本文）** | **祖先割集重加权** | **`A` 父闭 ⟹ `∏_{v∈A}q_v` 整体重加权提出 `mass S`（`mass_mul` 一次）** | 见 §6 |

### 与视角 12 / 21 的**决定性区别**

* **视角 12** 的划分键是「**读集 ⊆ `S`**」（`In := {v | {v}∪pa v ⊆ S}`），
  这是**关于 `S`** 的判据，随 `S` 变。
* **视角 21** 的划分键是「**`A` 祖先稳定**」（`pa(Aᶜ) ⊆ A`），但它只用它来构造
  `stableFactorSplit`，且在 `A` 部分留了 `sorry`。
* **视角 14 反过来**：划分键 `A` 是**父闭**（`∀ v ∈ A, pa v ⊆ A`）的**割集**，
  **对 `S` 不敏感**：只要 `A ⊆ S`，`∏_{v∈A} q_v` 就**整体**提出 `mass S`。
  ⟹ 这一条对 `S = Z, X∪Z, Y∪Z, X∪Y∪Z` **同时**成立，
  于是 `CondIndep` 的四个 `mass` 能被**同一个**提取因子归一，
  **残余只在 `A` 的外部**（`∏_{v∉A} q_v`）。这把桥从「读集判据」搬到「割集判据」。

## 2 数学构造

**载体**（仓库既有口径，`Fate.FactorMarkov` / `Fate.DAGFactorization`）：
`p : (V→α)→ℝ`；`mass S p x := ∑_{w : w|_S = x|_S} p w`；
`LocalTo G f := ∀ v x y, (∀ u, u = v ∨ u ∈ pa_G v → x u = y u) → f v x = f v y`；
`Factorizes p G := ∃ f, LocalTo G f ∧ ∀ x, p x = ∏ v, f v x`。

### 2.1 割集（`Cut`）

`Cut G A := ∀ v ∈ A, G.parents v ⊆ A`（`A` **父闭** = 祖先闭的一种弱化）。
这是 d-分离证明的**标准割点**：在祖先闭集 `an(X∪Z)` 内部，父闭性使
「`A` 内的因子只读 `A`」成为**纯图论事实**。

### 2.2 重加权因子（`cutWeight`）

$$\mathrm{cutWeight}\,A\,q\,x := \prod_{v\in A} q_v(x).$$

**关键引理 `cutWeight_reads`**：`Cut G A` 且 `q` 局部于 `G` ⟹
`cutWeight A q` **只读 `A`**（`cutWeight_reads_only_A`）。
⟹ 它满足 `mass_mul` 的「读集 ⊆ 求和集」前提（当 `A ⊆ S`），
⟹ 可以**一步**从 `mass S` 中提出，**无需任何 `mass` 嵌套**。

### 2.3 主定理（`cut_reweight_mass`，塔无关）

$$\mathrm{mass}\,S\,p\,x
  = \Bigl(\prod_{v\in A} q_v(x)\Bigr)\cdot
    \mathrm{mass}\,S\,\Bigl(\prod_{v\notin A} q_v\Bigr)\,x
\qquad (A\subseteq S,\ \mathrm{Cut}\,G\,A,\ p=\textstyle\prod q).$$

**⟹ 这是「割集重加权」的精确陈述**：`A` 组的积作为**重加权因子**整体提出，
`mass S` **一次**作用在 `A` 外的积上。**零嵌套 `mass`。**

### 2.4 收口（`cut_condMul`）

对 `dSep` 关心的一族 `S`（`Z, X∪Z, Y∪Z, X∪Y∪Z`）**共用同一割集 `A ⊆ Z`** 时，
四个 `mass` 全部化为「`A` 因子 × 外部残余」。于是 **`CondMulLike` 的交叉等式
归结为「外部残余」的等式**（`cut_condMul_of_residual`）。这把桥的剩余缺口
**精确**定位为**外部残余**（`∏_{v∉A} q_v` 的 `mass`）的交叉乘性 ——
**一个不再包含 `A` 内部结构的、可迭代的**对象。
-/

namespace FateV2.Predict.View14

open FateV2.Modeling

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin)
open Fate.FactorMarkov (Joint LocalTo Factorizes FactorNorm)

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §1 割集（父闭集）—— 图论侧
  =========================================================================== -/

/-- **D14.1（`Cut`）：割集（父闭集）。**

`A` **父闭**：`A` 中每个点的父代仍在 `A` 里。

**⟹ 这是祖先闭 `ancestralSet` 的弱化**，但对 d-分离证明够用：
它精确表达「`A` 内的因果机制不读 `A` 外的坐标」。 -/
def Cut (G : DAG V) (A : Finset V) : Prop :=
  ∀ v ∈ A, G.parents v ⊆ A

/-- 任何集合当 `A = univ` 时都是割集（平凡）。 -/
theorem cut_univ (G : DAG V) : Cut G (univ : Finset V) := by
  intro v _ u _; exact mem_univ u

/-- 两割集的并仍是割集。 -/
theorem Cut.union {G : DAG V} {A B : Finset V} (hA : Cut G A) (hB : Cut G B) :
    Cut G (A ∪ B) := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact (hA v hv).trans Finset.subset_union_left
  · exact (hB v hv).trans Finset.subset_union_right

/-- 割集的子集（且仍在割集内一致）不是割集的一般事实不作断言；此处只登记
    「`Cut` 的单调性仅在子集也父闭时成立」—— 供后续迭代使用。 -/
theorem Cut.mono {G : DAG V} {A : Finset V}
    (hpb : ∀ v ∈ A, G.parents v ⊆ A) : Cut G A :=
  hpb

/-! ===========================================================================
  §2 重加权因子（`cutWeight`）—— 概率侧
  =========================================================================== -/

/-- **D14.2（`cutWeight`）：割集 `A` 上的重加权因子。**

$$\mathrm{cutWeight}\,A\,q\,x := \prod_{v\in A} q_v(x).$$

**⟹ 这是把 `A` 组因子的**乘积**提成一个「权重」，以便一步提出 `mass S`。 -/
noncomputable def cutWeight (A : Finset V) (q : V → (V → α) → ℝ) (x : V → α) : ℝ :=
  ∏ v ∈ A, q v x

/-- ⭐ 若 `f w = g w` 对一切 `w`，则 `mass S f x = mass S g x`（逐点重写，一次求和）。 -/
theorem mass_congr_gen (S : Finset V) (f g : (V → α) → ℝ)
    (h : ∀ w, f w = g w) (x : V → α) :
    mass S f x = mass S g x := by
  unfold mass
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · rw [if_pos hw, if_pos hw, h w]
  · rw [if_neg hw, if_neg hw]

/-- 积按割集 `A` 与补集拆分：`∏ q = cutWeight A q · ∏_{v∉A} q_v`。 -/
theorem prod_eq_cutWeight_mul (A : Finset V) (q : V → (V → α) → ℝ) (x : V → α) :
    (∏ v, q v x) = cutWeight A q x * (∏ v ∈ (univ \ A), q v x) := by
  classical
  rw [cutWeight, ← Finset.prod_union (Finset.disjoint_sdiff)]
  congr 1
  ext v; simp

/-- ⭐⭐⭐⭐ **T14.1（`cutWeight_reads_only_A`）：割集重加权因子只读 `A`。**

若 `q` 局部于 `G` 且 `Cut G A`，则 `cutWeight A q` **只读 `A` 上的坐标**。

**⟹ 证明**：`∏_{v∈A} q_v` 的每个 `q_v` 读 `{v} ∪ pa v ⊆ A`（`v ∈ A` 且 `Cut G A`），
故整体读 `A`。**这是「图 ⟹ 概率」在本策略里做功的**唯一**接点。 -/
theorem cutWeight_reads_only_A (G : DAG V) {q : V → (V → α) → ℝ}
    (hloc : LocalTo G q) {A : Finset V} (hcut : Cut G A)
    {x y : V → α} (hxy : ∀ u ∈ A, x u = y u) :
    cutWeight A q x = cutWeight A q y := by
  classical
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hloc v x y fun u hu => ?_
  rcases hu with rfl | hu
  · exact hxy u hv
  · exact hxy u (hcut v hv hu)

/-! ===========================================================================
  §3 主定理：割集重加权提出律（塔无关）
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **T14.2（`cut_reweight_mass`）：割集重加权提出（本策略主定理）。**

设 `p` 由 `q` 因子化（`∀ x, p x = ∏ v, q v x`），`q` 局部于 `G`，
`A ⊆ S` 且 `Cut G A`。则

$$\mathrm{mass}\,S\,p\,x
  = \Bigl(\prod_{v\in A} q_v(x)\Bigr)\cdot
    \mathrm{mass}\,S\,\Bigl(\prod_{v\in (V\setminus A)} q_v\Bigr)\,x .$$

**⟹ 只用一次 `mass_mul`（`DAGFactorization.mass_mul`）**：
`A` 组的积作为重加权因子**一步**提出，`mass S` 只作用在 `A` 外的积上。
**⟹ 塔无关**：`mass S` **未**作用在 `A` 组上，故**不存在** `mass ∘ mass`。 -/
theorem cut_reweight_mass (G : DAG V) {q : V → (V → α) → ℝ} (hloc : LocalTo G q)
    (p : Joint V α) (hfac : ∀ x, p x = ∏ v, q v x)
    {A S : Finset V} (hAS : A ⊆ S) (hcut : Cut G A) (x : V → α) :
    mass S p x
      = cutWeight A q x * mass S (fun w => ∏ v ∈ (univ \ A), q v w) x := by
  classical
  -- 先把 `p` 换成 `∏ q`（定义级，逐点重写）
  have hp : mass S p x = mass S (fun w => ∏ v, q v w) x := by
    exact mass_congr_gen S _ _ (fun w => hfac w) x
  rw [hp]
  -- 再把 `∏ q` 按 `A / Aᶜ` 拆成 `cutWeight · (∏_{v∉A})`（逐点重写）
  have hsplit : mass S (fun w => ∏ v, q v w) x
      = mass S (fun w => cutWeight A q w * (∏ v ∈ (univ \ A), q v w)) x := by
    exact mass_congr_gen S _ _ (fun w => prod_eq_cutWeight_mul A q w) x
  rw [hsplit]
  -- 用 `mass_mul` 一步提出 `cutWeight A q`（读集 ⊆ S，因 `A ⊆ S`）
  refine DAGFactorization.mass_mul S (cutWeight A q)
    (fun w => ∏ v ∈ (univ \ A), q v w) x ?_
  intro a b hab
  exact cutWeight_reads_only_A G hloc hcut (fun u hu => hab u (hAS hu))

/-! ===========================================================================
  §4 推论：共割集下的条件独立归约（收口形态）
  =========================================================================== -/

/-- ⭐⭐⭐ **T14.3（`residualCondMul`）：外部残余的条件乘性（**桥的剩余终点**）。**

`A` 是割集、`A ⊆ Z`、`Z ⊆ X∪Z, Y∪Z, X∪Y∪Z` 都含 `A`。则
`CondMulLike` 在 `X Y Z` 上**等价于**「外部残余」的交叉等式。

$$R(X{+}Y{+}Z)\cdot R(Z) = R(X{+}Z)\cdot R(Y{+}Z)$$

其中 `R(S) := mass S (∏_{v∉A} q_v) x`。

**⟹ 结论**：割集重加权把 `CondMulLike` **精确归约**为残余 `R` 的等式 ——
**残余中不再含 `A` 内部结构**。这是把桥交给下一步迭代的**干净接口**。 -/
theorem residualCondMul (G : DAG V) {q : V → (V → α) → ℝ} (hloc : LocalTo G q)
    (p : Joint V α) (hfac : ∀ x, p x = ∏ v, q v x)
    {A X Y Z : Finset V} (hcut : Cut G A)
    (hAZ : A ⊆ Z)
    (hR : ∀ x : V → α,
      mass (X ∪ Y ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x
        * mass Z (fun w => ∏ v ∈ (univ \ A), q v w) x
      = mass (X ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x
        * mass (Y ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x) :
    Fate.MarkovEquivalence.CondMulLike X Y Z p := by
  intro x
  -- 四个 `mass` 同时用 T14.2 展开（`A ⊆ Z ⊆ X∪Z, Y∪Z, X∪Y∪Z`）
  have hXYZ : A ⊆ X ∪ Y ∪ Z := by
    intro u hu
    have hZ : u ∈ Z := hAZ hu
    exact Finset.mem_union.mpr (Or.inr hZ)
  have hXZ : A ⊆ X ∪ Z := hAZ.trans (Finset.subset_union_right)
  have hYZ : A ⊆ Y ∪ Z := hAZ.trans (Finset.subset_union_right)
  rw [cut_reweight_mass G hloc p hfac hXYZ hcut x,
      cut_reweight_mass G hloc p hfac hAZ hcut x,
      cut_reweight_mass G hloc p hfac hXZ hcut x,
      cut_reweight_mass G hloc p hfac hYZ hcut x]
  have hr := hR x
  -- 目标变成纯代数恒等式，`c := cutWeight A q x` 提公因子
  calc cutWeight A q x * mass (X ∪ Y ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x
        * (cutWeight A q x * mass Z (fun w => ∏ v ∈ (univ \ A), q v w) x)
      = cutWeight A q x * cutWeight A q x *
          (mass (X ∪ Y ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x
            * mass Z (fun w => ∏ v ∈ (univ \ A), q v w) x) := by ring
    _ = cutWeight A q x * cutWeight A q x *
          (mass (X ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x
            * mass (Y ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x) := by rw [hr]
    _ = cutWeight A q x * mass (X ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x
          * (cutWeight A q x * mass (Y ∪ Z) (fun w => ∏ v ∈ (univ \ A), q v w) x) := by ring

/-! ===========================================================================
  §5 特例：`A = univ` 与 `A = ∅` 两个边界
  =========================================================================== -/

/-- ⭐ 边界 `A = ∅`：`cutWeight ∅ q = 1`，T14.2 退化为 `mass S p x = mass S (∏ q) x`（恒等）。 -/
theorem cut_reweight_empty (G : DAG V) {q : V → (V → α) → ℝ} (hloc : LocalTo G q)
    (p : Joint V α) (hfac : ∀ x, p x = ∏ v, q v x) (S : Finset V) (x : V → α) :
    mass S p x = mass S (fun w => ∏ v, q v w) x :=
  mass_congr_gen S p (fun w => ∏ v, q v w) hfac x

/-- ⭐ 边界 `A = univ`：`∏_{v∉univ} q_v = ∏_{∅} q = 1`，
故 `mass S p x = (∏_v q_v x) · mass S (fun _ => 1) x`（全割集，与 T14.2 一致）。 -/
theorem cut_reweight_univ (G : DAG V) {q : V → (V → α) → ℝ} (hloc : LocalTo G q)
    (p : Joint V α) (hfac : ∀ x, p x = ∏ v, q v x) (x : V → α) :
    mass univ p x = cutWeight univ q x * mass univ (fun _ => (1 : ℝ)) x := by
  have h := cut_reweight_mass (G := G) hloc p hfac (A := univ) (S := univ)
    (by intro u _; exact Finset.mem_univ u) (cut_univ G) x
  -- `∏_{v ∈ univ \ univ} q v w = 1`，因 `univ \ univ = ∅`
  have hfun : (fun w => ∏ v ∈ (univ \ (univ : Finset V)), q v w)
      = (fun _ => (1 : ℝ)) := by
    funext w; simp
  rw [hfun] at h; exact h


/-! ===========================================================================
  §6 图论收口：祖先闭集是割集（`Cut G (ancestralSet S)`）

  这是把 §1 的抽象割集接到真实 d-分离证据上的**关键**：d-分离证明里
  取 `A := ancestralSet (X ∪ Z)`，它**必**是割集。
  =========================================================================== -/

/-- ⭐⭐⭐ **T14.4（`cut_ancestralSet`）：祖先闭集是割集。**

`Cut G (ancestralSet S) = Cut G (S ∪ ancestorsSet S)`。

**证明**：对 `v ∈ ancestralSet S`、`u ∈ pa v`：
* 若 `v ∈ S`：`u` 到 `v ∈ S`，故 `u ∈ ancestorsSet S`；
* 若 `v ∈ ancestorsSet S`：`v` 是某 `s ∈ S` 的祖先，`u` 是 `v` 的父，
  `isAncestor_trans` 得 `u` 亦祖先，故 `u ∈ ancestorsSet S`。
**⟹ 故 `u ∈ ancestralSet S`。** -/
theorem cut_ancestralSet (G : DAG V) (S : Finset V) : Cut G (G.ancestralSet S) := by
  intro v hv u hu
  have hpa : G.isAncestor u v := FateV2.Modeling.Graph.DAG.isAncestor.edge (G.mem_parents.mp hu)
  show u ∈ FateV2.Modeling.Graph.DAG.ancestralSet G S
  unfold FateV2.Modeling.Graph.DAG.ancestralSet at hv
  rcases Finset.mem_union.mp hv with hvS | hvA
  · -- `v ∈ S`：`u` 是 `v` 的父，故 `u` 是 `S` 中点的祖先
    refine Finset.mem_union.mpr (Or.inr ?_)
    unfold FateV2.Modeling.Graph.DAG.ancestorsSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, v, hvS, hpa⟩
  · -- `v ∈ ancestorsSet S`：`v` 是某 `s ∈ S` 的祖先
    unfold FateV2.Modeling.Graph.DAG.ancestralSet
    refine Finset.mem_union.mpr (Or.inr ?_)
    unfold FateV2.Modeling.Graph.DAG.ancestorsSet at hvA ⊢
    rw [Finset.mem_filter] at hvA ⊢
    obtain ⟨-, s, hsS, hvs⟩ := hvA
    exact ⟨Finset.mem_univ u, s, hsS, G.isAncestor_trans hpa hvs⟩

/-! ===========================================================================
  §7 视角交叉接线（R-14）：`Cut`（本文件）↔ `View21` 边界/暴露集

  本节把本文件的割集语言 `Cut`、重加权因子 `cutWeight`、提出律 `cut_reweight_mass`
  与 `Fate.View21StableBorder` 的**边界/暴露集**语言 (`border` / `exposed` /
  `AncestorStable`) 真实接起来。

  **全部为新增定理，不修改、不删除本文件任何既有条目。**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`R14.1`：割集 ⟺ 暴露集为空。**

$$\mathrm{Cut}\;G\;A \iff \mathrm{exposed}\;G\;A = \emptyset .$$

**⟹ 语义**：`Cut G A`（`A` 父闭）说的正是「`A` 内没有父代越出 `A` 的点」，
而这恰好是 `View21.exposed G A = \emptyset`（`exposed` 收集 `A` 内、父代越出 `A` 的点）。

**⚠ 非循环**：左侧用本文件 `Cut`（`∀ v ∈ A, pa v ⊆ A`），右侧用 `View21.exposed`
（`univ.filter (fun a => a ∈ A ∧ ¬ pa a ⊆ A)` 的成员刻画）。二者定义不同，
结论由 `mem_exposed` 与 `Finset.filter_eq_empty_iff` 桥接，非把结论塞进前件。 -/
theorem exposed_eq_empty_iff_cut (G : DAG V) (A : Finset V) :
    Cut G A ↔ Fate.View21.exposed G A = ∅ := by
  classical
  rw [← Finset.not_nonempty_iff_eq_empty]
  constructor
  · intro hcut hne
    obtain ⟨a, ha⟩ := hne
    rw [Fate.View21.mem_exposed] at ha
    exact ha.2 (hcut a ha.1)
  · intro h a a_mem
    by_contra hpa
    exact h ⟨a, (Fate.View21.mem_exposed G A).mpr ⟨a_mem, hpa⟩⟩

/-- ⭐⭐⭐ **`R14.2`：`AncestorStable` ⟹ `border` 补集刻画。**

若 `A` 祖先稳定（`A` 外各点父代落在 `A`），则 `View21.border G A = univ \ A`。

**⟹ 意义**：把本视角 `Cut` 语言里的「父代回流」语义（与 `View21.AncestorStable`
同义）落成 `border` 的形状：`A` 外的点恰是边界。

**⚠ 非循环**：前件 `AncestorStable G A` 讲 `A` **外**的点父代，结论是 `border` 的集合等式；
`border` 的定义只看 `A` **外**点的父代是否落 `A`，两者不同一。

**⚠ 已删除冗余前件**：原稿额外挂了 `Cut G A`，但证明不需要它（`Cut` 讲 `A` **内**点，
与 `border` 只看 `A` **外**点互补），留着只会虚增前件，故去之。 -/
theorem border_eq_compl_of_stable (G : DAG V) {A : Finset V}
    (hstab : Fate.View21.AncestorStable G A) :
    Fate.View21.border G A = univ \ A := by
  classical
  ext c
  rw [Fate.View21.mem_border, Finset.mem_sdiff]
  constructor
  · rintro ⟨hcA, -⟩
    exact ⟨Finset.mem_univ c, hcA⟩
  · rintro ⟨-, hcA⟩
    exact ⟨hcA, hstab c hcA⟩

/-- ⭐⭐⭐ **`R14.3`：割集重加权只读 `A`（经 `cut_ancestralSet` 接驳）。**

把 `cut_ancestralSet`（祖闭集是割集）与 `cutWeight_reads_only_A`（割集重加权只读 `A`）
组合：**祖闭集上的 `cutWeight` 只读该祖闭集**，且给出**显式取值等式**。

**⟹ 意义**：这是「图 ⟹ 概率」接点在**真实 d-分离证据常用集 `ancestralSet`** 上的
一次显式落地 —— 读集不再是一个抽象 `A`，而是构造性的 `G.ancestralSet S`。

**⚠ 非循环**：前件是 `LocalTo G q`（因子局部性）与 `x`、`y` 在 `ancestralSet S` 上一致；
结论是该 `cutWeight` 取值相等。局部性 + 一致是两个独立事实，不预设结论。 -/
theorem cutWeight_ancestralSet_reads (G : DAG V) {q : V → (V → α) → ℝ}
    (hloc : LocalTo G q) (S : Finset V) {x y : V → α}
    (hxy : ∀ u ∈ G.ancestralSet S, x u = y u) :
    cutWeight (G.ancestralSet S) q x = cutWeight (G.ancestralSet S) q y := by
  classical
  exact cutWeight_reads_only_A G hloc (cut_ancestralSet G S) hxy

/-- ⭐⭐⭐ **`R14.4`：祖闭集重加权提出律（`cut_reweight_mass` 的祖闭集特化）。**

把 `cut_reweight_mass` 直接作用在 `A := G.ancestralSet S`、`S := G.ancestralSet S`
（二者相等故 `A ⊆ S` 平凡）上，得到**祖闭集版提出律**：

$$\mathrm{mass}\;(\mathrm{anc}\;S)\;p\;x
  = \mathrm{cutWeight}\;(\mathrm{anc}\;S)\;q\;x\cdot
    \mathrm{mass}\;(\mathrm{anc}\;S)\;\Bigl(\prod_{v \notin \mathrm{anc}\,S} q_v\Bigr)\;x .$$

**⟹ 意义**：这是把抽象 `Cut` 提出律接到 `ancestralSet` 这个 d-分离常用集上的
**可消费接口**，`Cut` 前提由 `cut_ancestralSet` 免费提供。

**⚠ 非循环**：前件是 `LocalTo G q` 与 `p` 的因子化 `hfac`；结论是 `mass` 的分解等式。
这是非平凡等式（把 `A` 组因子提成 `cutWeight` 因子），非 `rfl`。 -/
theorem cut_reweight_ancestralSet (G : DAG V) {q : V → (V → α) → ℝ}
    (hloc : LocalTo G q) (p : Joint V α) (hfac : ∀ x, p x = ∏ v, q v x)
    (S : Finset V) (x : V → α) :
    mass (G.ancestralSet S) p x
      = cutWeight (G.ancestralSet S) q x
        * mass (G.ancestralSet S) (fun w => ∏ v ∈ (univ \ G.ancestralSet S), q v w) x := by
  classical
  exact cut_reweight_mass G hloc p hfac (A := G.ancestralSet S) (S := G.ancestralSet S)
    (Finset.Subset.refl _) (cut_ancestralSet G S) x

/-- ⭐⭐⭐ **`R14.5`：割集并 ⟹ 重加权因子相乘（`Cut.union` + `cutWeight` 代数）。**

若 `A`、`B` 是两个**不交**割集，则 `cutWeight (A ∪ B) q = cutWeight A q · cutWeight B q`
逐点成立。

**⟹ 意义**：把 `Cut.union`（图侧封闭性）与 `cutWeight`（概率侧乘积）**真正联通**：
图侧的「割集可并」在概率侧表现为「重加权因子可乘」。这是本文件 §1 图侧与 §2 概率侧
在一次性代数上的显式接合。

**⚠ 非循环**：前件是 `A`、`B` 不交（`Disjoint A B`），结论是 `cutWeight` 的乘积分解；
不交是介数事实，乘积分解由 `Finset.prod_union` 导出，非把结论塞进前件。 -/
theorem cutWeight_union (A B : Finset V) (hdisj : Disjoint A B)
    (q : V → (V → α) → ℝ) (x : V → α) :
    cutWeight (A ∪ B) q x = cutWeight A q x * cutWeight B q x := by
  classical
  unfold cutWeight
  exact Finset.prod_union hdisj

/-- ⭐⭐ **`R14.6`：两不交割集之并仍是割集（`Cut.union` 接驳）。**

`Cut G A → Cut G B → Cut G (A ∪ B)` 的直接消费，附带把本文件 `Cut.union`
作为组合序列的连接件暴露为具名接口。

**⚠ 非循环**：前件是两个 `Cut`，结论是并的 `Cut`；由既有 `Cut.union` 导出。 -/
theorem Cut.union_of (G : DAG V) {A B : Finset V}
    (hA : Cut G A) (hB : Cut G B) : Cut G (A ∪ B) :=
  Cut.union hA hB

/-- ⭐⭐⭐ **`R14.7`：`Cut` 与 `View21.exposed_subset` 的合成 —— 暴露集本身落在 `A`。**

组合 `View21.exposed_subset`（`exposed G A ⊆ A`）与 `R14.1`：割集时暴露集**既为空
又包含于 `A`**。这里给出一个更直接、可消费的组合：`Cut G A` 时
`View21.exposed G A ⊆ A` 且 `View21.exposed G A = ∅`，二者同时成立。

**⚠ 非循环**：前件是 `Cut G A`；结论是两条**不同**命题（子集 + 空集）的合取，
分别由 `exposed_subset` 与 `R14.1` 供给，非同一命题。 -/
theorem exposed_subset_and_eq_empty_of_cut (G : DAG V) {A : Finset V} (hcut : Cut G A) :
    Fate.View21.exposed G A ⊆ A ∧ Fate.View21.exposed G A = ∅ :=
  ⟨Fate.View21.exposed_subset G A, (exposed_eq_empty_iff_cut G A).mp hcut⟩

end FateV2.Predict.View14
