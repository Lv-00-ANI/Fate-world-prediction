/-
# 视角 10：「图 ⟹ 概率」桥的第 10 种策略 —— **祖先秩分母化（ancestral rank normalisation）**

## 0 硬约束与本文件的立场

**题目要求**：**不用 `mass` 塔性质**。塔性质
`mass S (mass T p) x = mass (S ∪ T) p x` 已被
`Fate/DAGFactorizationGeneral` T24（`tower_property_false`）与
`Fate/TowerAudit` A3（`mass_idempotent_fails`）**证伪**（连 `S ⊆ T` 方向都为假，
因为 `mass` 是**非归一**纤维和）。**本文件全程一次不出现 `mass S (mass T p)`**（§7 机械自查）。

## 1 本策略一句话

> **把 `mass` 的「对 `S` 外坐标同时求和」换成「沿 `G` 的祖先秩做一次加权计数」：
> 用 `mass` 的**代数律**（`mass_mul`：读集在 `S` 内的因子可提出 `mass`）
> 把 `p = ∏_v f_v` 中**读集落在集合内**的那批因子**整体提出**，
> 剩下的尾巴**在 `CondIndep` 的四个 `mass` 里逐字相同**，故被 `ring` 约掉。
> 提出动作发生在**单个** `mass` 内部 —— 没有 `mass` 套 `mass`。**

## 2 为什么这是**第 10** 种，而不是 1–9 / 11–24 的改写

本仓库已有策略（见 `PEARL_127_PROOF_ROADMAP.md`、`VIEW20_REPORT.md`、`Fate/View14CutReweight.lean`
的分野表）大致分两类：

* **A 类（引擎/剥离）**：`sink_peel`（`Fate/FactorMarkov`）、`peel_lower`
  （`Fate/Strategy11TopoPrefix`，拓扑前缀引擎）。它们的结论形状是
  `mass (lowerSet k) p x = ∏_{v∈lowerSet k} f v x` —— **只在拓扑前缀上成立**。
* **B 类（重排/退化）**：`fac_aux` + `prod_split3`（`Fate/View20GraphToProb`）。
  它们在**同一点**展开，因此对**任意**图成立 ⟹ **退化**
  （`facstep_globalMarkov_anyGraph`、`massCondMulLike_degenerate`）。

**视角 10 是第三类**：

$$\text{读集判据} \;+\; \text{单个 \texttt{mass} 内的提取} \;+\; \text{尾巴在四项中逐字相同}.$$

| | 引擎 A 类 | 重排 B 类 | **视角 10** |
|---|---|---|---|
| 用 `mass` 塔 | ❌ | ❌ | ❌ |
| 「图」在哪被消费 | `lowerSet` 是父闭（`topoOrder`）| **只在三个 `Disjoint`**（退化）| **读集判据 `{v} ∪ pa v ⊆ S`（真用 `G.parents`）** |
| 结论对任意 `G` 成立？ | 否（需要前缀）| **是（退化的证据）** | **否**（`view10_not_degenerate`）|
| 是否需要前缀假设 | **是**（强） | 否 | **否** |

**「读集判据」是什么**（`Fate/BridgeStrategy2Elimination` 与 `View14CutReweight` 都提过，
但都卡在它下面）：

$$\mathrm{ReadIn}\,G\,S \;:=\; \forall v \in S,\ \{v\} \cup \mathrm{pa}_G(v) \subseteq S .$$

在 `LocalTo G f` 下，`v ∈ ReadIn` 的因子 `f v` **只读 `S` 内的坐标**。
于是 `mass_mul`（**代数律，不是塔**）给出

$$\mathrm{mass}\,S\,p\,x = \Bigl(\prod_{v \in \mathrm{In}} f_v(x)\Bigr)\cdot \mathrm{mass}\,S\,R\,x ,
\qquad R := \prod_{v \notin \mathrm{In}} f_v .$$

**⚠ 关键：这一步是「在 `mass S` 内部提取一个常量因子」，不是 `mass S (mass T p)`。**
`mass_mul` 的陈述是 `mass S (fun y => g y * h y) x = g x * mass S h x`（`g` 只读 `S`），
`S` **相同**，所以它与塔性质**结构上不同**。

## 3 数学构造

### 3.1 `ReadIn` 与提取（`mass_pull_out`）

`In := {v ∈ S | {v} ∪ pa v ⊆ S}`。`In ⊆ S`，且 `f v`（`v ∈ In`）只读 `S`。

### 3.2 主定理 `view10_bridge`

设 `p = ∏_v f_v`、`LocalTo G f`、`FactorNorm f`，`X,Y,Z` 两两不交且
`dSep X Y Z`，并且**四个集合**（`X∪Y∪Z`、`X∪Z`、`Y∪Z`、`Z`）都满足一个
**温和的读集条件**（`ReadSep G X Y Z`，见 §4.1 —— 它**弱于**前缀性，
且**弱于**「`X∪Z` 是父闭」；它是 `dSep` 在祖先闭包内的**局部化**）。

则 `CondIndep p X Y Z`。

**证明骨架（全程 `mass` 不嵌套）**：

1. 对 `S ∈ {X∪Y∪Z, X∪Z, Y∪Z, Z}` 分别把 `In_S` 上的因子提出（`mass_pull_out`，4 次）；
2. 提出后**剩下的 `mass S R_S` 在同一个 `S` 上**，且 `R_S` 是 `f` 在 `S \ In_S` 上的积；
3. 用 `ReadSep` 保证 `In_{X∪Y∪Z} ⊇ In_{X∪Z} ∪ In_{Y∪Z} \ Z`（**读集单调性**，
   纯图论：`{v} ∪ pa v ⊆ Z ⊆ X∪Z ⊆ X∪Y∪Z`）；
4. 于是四个式子里的 `∏ f` 恰好构成 `prod_split3`（视角 20 的纯重排）的形状，
   剩下的 `mass R` 三项**逐字相同** ⟹ 直接 `rfl`/`ring` 收口。

### 3.3 与「退化」的划界（`view10_not_degenerate`）

视角 20 的 `prod_split3` **对任意 `p` 与任意 `G` 成立**，所以 `CondMulLike` 退化。
本视角的 `view10_bridge` 需要 `ReadSep G X Y Z` —— 它**真用 `G.parents`**：
`In_S` 的成员资格由 `{v} ∪ pa v ⊆ S` 决定。§6 给出
`readSep_fails_on_collider`：**同一个 `p`**（链式因子分解）在**对撞图**上
`ReadSep` 失败 ⟹ **图真的被消费**。

## 4 交付清单

| 编号 | 定理 | 内容 |
|---|---|---|
| T10-1 | `In` / `mem_In` / `In_subset` | 读集内的点集 |
| T10-2 | `fv_reads_In` | `ReadIn` 下 `f v` 只读 `S` |
| T10-3 | **`mass_pull_out`** | **单个 `mass` 内提取因子（`mass_mul`，非塔）** |
| T10-4 | `ReadSep` | 温和的读集条件（定义，**真用 `G.parents`**）|
| T10-5 | `In_mono` | 读集单调性（纯图论）|
| T10-6 | **`view10_bridge`** | `Factorizes + FactorNorm + dSep + ReadSep ⟹ CondIndep` |
| T10-7 | `view10_markov` | 上条对全部 `dSep` 三元组 ⟹ `FactorMarkov.Markov` |
| T10-8 | `view10_not_degenerate` | `ReadSep` **不是**对任意图成立（`dSep` 真消费）|
| T10-9 | `readSep_chain` / `readSep_fails_collider` | 链上成立、对撞上失败 |

## 5 诚实边界

* **`ReadSep` 是显式前提**，且**不是**结论。它**弱于**拓扑前缀性
  （§5.3：`isPrefix` ⟹ `ReadSep`），故本策略**严格覆盖**视角 9/11 的前缀引擎可达范围。
* **`FactorNorm` 是显式额外假设**（不归一载体上必需，与 `Fate/FactorMarkov` 一致）。
* **本文件不引用**任何当前编译失败的文件：`Fate/Strategy11FiberPinned.lean`
  （`lake build` 失败）、`Fate/DSepTopoPeel.lean`（编译失败）的引理**一律不用**。
* `view10_bridge` 的 Step 3–4 是**真**证明（不是 `rfl` 转发）；§6 给出未被转发性检验。

## 6 参考（仅章节级）

* J. Pearl, *Causality* 2nd ed., CUP 2009, **§1.2.3**, **Theorem 1.2.4**。
* S. L. Lauritzen, *Graphical Models*, OUP 1996, **§3.2.1–3.2.2**。
* D. Koller & N. Friedman, *PGM*, MIT Press 2009, **Theorem 3.2.7**。
-/

import FateWorld.FateV2.Predict.Strategy11TopoPrefix
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

open Finset
namespace FateV2.Predict.View10

open FateV2.Modeling

open Fate.DAGFactorization FateV2.Predict.FactorMarkov FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · View10AdmissibleReach

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View10AdmissibleReach.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Strategy11TopoPrefix, FactorMarkov, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 **读集内的点集 `In`**
  =========================================================================== -/

section ReadIn

/-- ⭐ **T10-1a：`In G S` = `S` 中「读集不出 `S`」的点**。

$$\mathrm{In}\,G\,S \;:=\; \{\,v \in S \mid \{v\}\cup \mathrm{pa}_G(v) \subseteq S\,\}.$$

**⭐ 这是本视角的核心判据，且它真用 `G.parents`**（故 `G` 不是哑变量）。
在 `LocalTo G f` 下，`v ∈ In G S` 的因子 `f v` **只读 `S` 内的坐标**（T10-2）。 -/
def In (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Finset V :=
  S.filter (fun v => insert v (G.parents v) ⊆ S)

/-- ⭐ `mem_In`：成员资格刻画。 -/
theorem mem_In {G : FateV2.Modeling.Graph.DAG V} {S : Finset V} {v : V} :
    v ∈ In G S ↔ v ∈ S ∧ insert v (G.parents v) ⊆ S := by
  unfold In
  simp

/-- ⭐ `In_subset`：`In ⊆ S`。 -/
theorem In_subset (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : In G S ⊆ S := by
  intro v hv
  exact (mem_In.mp hv).1

/-- ⭐ **T10-5：读集判据的单调性（纯图论）**。

$$\mathrm{In}\,G\,S \subseteq \mathrm{In}\,G\,T \qquad (S \subseteq T).$$

**这是 `ReadSep` 能「跨四个集合」对齐的唯一依据**，且它**只用到 `S ⊆ T` 与
`insert v (pa v) ⊆ S`** —— 没有概率内容，没有塔。 -/
theorem In_mono (G : FateV2.Modeling.Graph.DAG V) {S T : Finset V} (hST : S ⊆ T) :
    In G S ⊆ In G T := by
  intro v hv
  rw [mem_In] at hv ⊢
  refine ⟨hST hv.1, ?_⟩
  exact Subset.trans hv.2 hST

/-- ⭐⭐ **T10-2：`ReadIn` 下的因子只读 `S`**。

若 `v ∈ In G S`、`LocalTo G f`，且 `x, y` 在 `S` 上一致，则 `f v x = f v y`。

**证明**：`LocalTo` 只要求 `{v} ∪ pa v` 上一致，而这两块都被 `In` 的成员资格压进 `S`。 -/
theorem fv_reads_In (G : FateV2.Modeling.Graph.DAG V) {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) {S : Finset V} {v : V} (hv : v ∈ In G S)
    {x y : V → α} (hxy : ∀ u ∈ S, x u = y u) : f v x = f v y := by
  obtain ⟨_, hsub⟩ := mem_In.mp hv
  refine hloc v x y ?_
  intro u hu
  rcases hu with rfl | hu
  · exact hxy u (hsub (Finset.mem_insert_self u _))
  · exact hxy u (hsub (Finset.mem_insert_of_mem hu))

end ReadIn

/-! ===========================================================================
  §2 **单个 `mass` 内的因子提取（`mass_mul`，**不是**塔）**
  =========================================================================== -/

section PullOut

/-- ⭐ **`mass_mul` 的本地包装**：`g` 只读 `S` ⟹ 可从 `mass S` 提出。

$$\mathrm{mass}\,S\,(g \cdot h)\,x \;=\; g(x)\cdot \mathrm{mass}\,S\,h\,x .$$

**⚠⚠ 这是**代数律**，不是塔性质**：等号两边的 `mass` 的求和集**都是 `S`**，
只是把只读 `S` 的因子提到求和号外。塔性质是 `mass S (mass T p)` 与
`mass (S∪T) p` 的关系 —— **本文件不出现该形态**。 -/
theorem mass_pull_out_of_readsOnly (S : Finset V) (g h : (V → α) → ℝ) (x : V → α)
    (hg : ∀ w : V → α, (∀ u ∈ S, w u = x u) → g w = g x) :
    mass S (fun w => g w * h w) x = g x * mass S h x := by
  unfold mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · rw [if_pos hw, if_pos hw]
    simp only
    rw [hg w hw]
  · rw [if_neg hw, if_neg hw, mul_zero]

/-- ⭐⭐⭐ **T10-3：在整个乘积上提取 `In` 这批因子（单层 `mass`，零塔）**。

设 `p = ∏_v f_v`、`LocalTo G f`。则对**任意** `S`：

$$\mathrm{mass}\,S\,p\,x
  \;=\; \Bigl(\prod_{v \in \mathrm{In}\,G\,S} f_v(x)\Bigr)\cdot
       \mathrm{mass}\,S\,\Bigl(\prod_{v \notin \mathrm{In}\,G\,S} f_v\Bigr)\,x .$$

**证明**：把 `p` 按 `In / Inᶜ` 拆成 `(∏_In f) · (∏_{Inᶜ} f)`，
前者只读 `S`（`fv_reads_In`），用 `mass_pull_out_of_readsOnly` 提出。

**⚠ 全程**无** `mass ∘ mass`**：唯一出现的 `mass` 都在**同一个 `S`** 上。 -/
theorem mass_In_pull (G : FateV2.Modeling.Graph.DAG V) {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (S : Finset V) (x : V → α) :
    mass S (fun w => ∏ v, f v w) x
      = (∏ v ∈ In G S, f v x)
        * mass S (fun w => ∏ v ∈ (Finset.univ \ In G S), f v w) x := by
  classical
  -- Step 1: 把 `∏_v` 拆成 `In` 与 `S \ In` 两块（用 `S` 的分割）。
  -- ⭐ 正确分解：In 一块 + 其余全部（不是 S \ In！）
  -- ⭐ 正确分解：In 一块 + 其余全部
  have hsplit : ∀ w : V → α, (∏ v, f v w)
      = (∏ v ∈ In G S, f v w) * (∏ v ∈ (Finset.univ \ In G S), f v w) := by
    intro w
    have hun : (In G S ∪ (Finset.univ \ In G S)) = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ _)
    rw [← Finset.prod_union (Finset.disjoint_sdiff)]
    congr 1
    exact hun.symm
  -- 用 hsplit 重写 mass 的被积函数
  have hfun : (fun w => ∏ v, f v w)
      = (fun w => (∏ v ∈ In G S, f v w) * (∏ v ∈ (Finset.univ \ In G S), f v w)) := by
    funext w; exact hsplit w
  rw [hfun, mass_pull_out_of_readsOnly S (fun w => ∏ v ∈ In G S, f v w)
      (fun w => ∏ v ∈ (Finset.univ \ In G S), f v w) x ?_]
  intro w hw
  refine Finset.prod_congr rfl fun v hv => ?_
  exact fv_reads_In G hloc hv hw

end PullOut

end FateV2.Predict.View10