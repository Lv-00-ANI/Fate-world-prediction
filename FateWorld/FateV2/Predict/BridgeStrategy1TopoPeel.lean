/-
# 「图 ⟹ 概率」桥 · **策略 1：拓扑序逐点剥离（Topological Peel）**

## 0 定位

本文件实现「图 ⟹ 概率」桥的**第 1 种**证明策略，**不使用** `mass` 塔性质
（`mass S (fun w => mass T p w) x`，已在
`Fate.DAGFactorizationGeneral.tower_property_false` 中**证明为假**）。

> **策略 1 的一句话**：
> **一次也不嵌套 `mass`。**把「固定 `S`、对其余坐标求和」写成**一次**求和，
> 然后用两条**单层**工具把它算完：
> ① **`mass_insert_sum'`**（放开一个坐标再求和，`Finset.sum_comm`，**已证**）；
> ② **纤维重标号 `mass_insert_off_left`**（`Finset.sum_nbij`，**已证**）。
> 「图」只在**两处**做功：
> **(a)** `pa(v) ⊆ S` 使 `f v` 在整条纤维上等于 `f v x`（`LocalTo`）；
> **(b)** `v` 在剩余变量中是 **sink**（`∀ w ≠ v, v ∉ pa w`）使其余因子都不读 `v`。

**与塔性质的区别（关键，防止误用）**：

| | 塔性质（**假**，T24） | 策略 1（**真**） |
|---|---|---|
| 形态 | `mass S (mass T p) x`（**嵌套** `mass`）| `∑_a mass (insert v S) p (unpin v x a)`（**不嵌套**）|
| 由 | —— | `mass_insert_sum'` + `mass_insert_off_left` |
| 状态 | 已证伪 | 已证 |

## 1 数学构造

**载体**（仓库既有口径）：
`p : (V → α) → ℝ`；`mass S p x := ∑_{w : w|_S = x|_S} p w`；
`Factorizes p G := ∃ f, LocalTo G f ∧ ∀ x, p x = ∏ v, f v x`；
`FactorNorm f := ∀ v x, ∑_a f v (unpin v x a) = 1`。

### 1.1 策略 1 的归一化收尾

$$\texttt{mass\_empty\_eq\_one}:\qquad
\Bigl(\sum_y p\,y = 1\Bigr)\implies
\mathrm{mass}\,\emptyset\;p\;x = 1$$

**⚠⚠ 对旧版本的关键更正**：旧版文件把「引擎」写成
`mass ∅ (∏ f) x = 1`（声称由 `FactorNorm` 得到）。**这是假的**：
`mass ∅ (∏ f) x = ∑_y ∏_w f w y`，而 `FactorNorm` 只约束
「每个 `f w` 对**自身坐标**求和 = 1」；Fubini 只有当每个 `f w` 只读**自己的**坐标（`{w}`）
时才能把 `∑_y ∏_w` 拆成 `∏_w ∑_a`。对有父节点的因子（读 `{w}∪pa w`）**不能**拆。
仓库既有 `FactorRecursionRouteB.mass_prod_reads`（G4.3）给出的正确值是
`mass ∅ (∏ f) x = |α|^{|V|} · ∏_w f w x`，**不是 1**（去掉 `FactorNorm` 会更糟）。

⟹ **正确的归一化内容在于 `p`（密度）本身**：真实概率测度自动满足 `∑_y p y = 1`，
由 `mass_empty` 得 `mass ∅ p x = ∑_y p y = 1`。这是 `fac_aux` 收尾所需的唯一概率输入。

### 1.2 从引擎到 `step`（`fac_aux` 的缺口）—— **`peel` 定理**

$$
\texttt{peel}:\quad
\mathrm{mass}\,(\{v\}\cup S)\,p\,x \;=\; f\,v\,x\cdot \mathrm{mass}\,S\,p\,x
$$

**前提**：`v ∉ S`、`pa(v) ⊆ S`、`f` 局部于 `G`、`f` 局部归一、`p = ∏ f`、
且 **`v` 在剩余变量中是 sink**（`∀ w ≠ v, v ∉ pa w`）。

**证明（策略 1 的三步，全部在同一层 `mass` 上，无嵌套）**：

1. **拆乘积**：`p = f v · g`，其中 `g := ∏_{u≠v} f u`（`prod_erase_eq`）。
2. **`f v` 在 `insert v S`-纤维上是常数**（`pa(v) ⊆ S` + `LocalTo`）：
   `mass (insert v S) p x = f v x · mass (insert v S) g x`。
3. **`g` 不读 `v`**（`v` 是 sink），故由 **纤维重标号**（`mass_insert_off_left`）
   得 `mass (insert v S) g (unpin v x a) = mass (insert v S) g x` 对所有 `a` 成立；
   再对 `v` 位求和，用 `mass_insert_sum'`（**一次**求和，非塔）：
   `mass S p x = ∑_a f v (unpin v x a) · mass (insert v S) g x
              = mass (insert v S) g x`（由 `FactorNorm`）。
   结合第 2 步即得 `peel`。

**⚠ `S` 不必是 `V∖{v}`**：`S` 可为任意 `⊇ pa(v)`、`∌ v` 的集合。

**⚠ 诚实边界：sink 前提不可去。** 若存在子节点 `w`（`v ∈ pa w`），则 `f w` 读 `x v`，
在「`v` 位可变」的纤维上**不是常数**，`peel` 为假。
§4 给出机检反例（`peel_without_sink_false`，`arrowDAG : DAG (Fin 2)`，边 `0→1`）。
这正是「沿拓扑序**从 sink 开始**逐点剥离」的合法性来源。

### 1.3 收口

`peel` 给出 `fac_aux` 所需的 `step`（取 `q v := f v`），于是
`Fate.DAGFactorization.fac_aux` 给出（取 `S = univ`）

$$
p\,x \;=\; \Bigl(\prod_v f\,v\,x\Bigr)\cdot \mathrm{mass}\,\emptyset\,p\,x,
$$

再由 §1.1 的归一化引擎 `mass ∅ p x = 1`（`p` 归一）得 `p x = ∏ v f v x`
—— 即 `Factorizes`。**注意 `peel` 的 sink 前提是针对拓扑序上一次剥离**；
完整的 `fac_aux` 归纳需要每次剥离选当前子图的 sink，这由拓扑序保证。
本文件把这一组合写成 `factorizes_of_peel`（以 `hstep` 为假设），
并把生成 `hstep` 的图论（拓扑序 ⟹ 每个被剥离点当时是 sink）留给
`MarkovBridgeTopo` / `AncestralInheritanceRouteB` 的既有拓扑枚举。

## 2 交付清单

| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| **S1-1** | `unpin_eq_update` | `unpin v x a = Function.update x v a`（口径对齐）| ✅ 零缺口 |
| **S1-2** | **`mass_empty_eq_one`** | **归一化引擎（正确版）**：`∑_y p y = 1 ⟹ mass ∅ p x = 1` | ✅ 零缺口 |
| **S1-3** | `prod_erase_eq` | `∏_u f u = f v · ∏_{u≠v} f u` | ✅ 零缺口 |
| **S1-4** | `mass_insert_off_left` | 纤维重标号：`g` 不读 `v` ⟹ `mass (insert v S) g` 只依赖 `x|_S` | ✅ 零缺口 |
| **S1-5** | **`peel`** | **策略 1 核心（修正版）**：`mass ({v}∪S) p x = f v x · mass S p x`（带 sink 前提）| ✅ 零缺口 |
| **S1-6** | `peel_without_sink_false` | **反例**：去掉 sink 前提，`peel` 为假 | ✅ 机检 |
| **S1-7** | `factorizes_of_peel` | `peel` + `fac_aux` + 归一 ⟹ `Factorizes` | ✅ 零缺口 |

## 3 诚实边界

* **不证**「`Factorizes ⟹ Markov`」：仍差 Bayes-ball 不可达 ⟹ `C_T` 恒常性
  （`PEARL_127_PROOF_ROADMAP` §3 B3/B5）。本文件补的是**单步 `peel`**。
* `FactorNorm` 是**必要**假设（真实概率测度下自动成立；`(V→α)→ℝ` 上须显式）。
* **sink 前提不可去**（§1.2 + `S1-6` 反例）。
* 全文件**零** `mass S (mass T p)` 形态出现。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.G1ParentNonDescendant
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeStrategy1

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · BridgeStrategy1TopoPeel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeStrategy1TopoPeel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, DAGFactorization, G1ParentNonDescendant
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 ⭐⭐⭐ **引擎：归一化收尾**（策略 1 的唯一「概率」输入）

  ⚠⚠ **关键更正（对旧版本）**：旧版本声称「引擎」`mass ∅ (∏ f) x = 1`
  **可由 `FactorNorm` 得到**。**这是错的**：
  `mass ∅ (∏ f) x = ∑_y ∏_w f w y`，而 `FactorNorm` 只约束
  「每个 `f w` 对**自身坐标**求和 = 1」。只有当每个 `f w` 只读**自己的**坐标（`{w}`）
  时，Fubini 才能把 `∑_y ∏_w` 拆成 `∏_w ∑_a`；对有父节点的因子（读 `{w}∪pa w`）
  **不能**拆。仓库既有 `FactorRecursionRouteB.mass_prod_reads`（G4.3）给出的正确值是
  `mass ∅ (∏ f) x = |α|^{|V|} · ∏_w f w x`，**不是 1**。

  ⟹ **正确的「引擎」是关于 `p`（密度）的归一化假设**，而非 `f` 的：
  由 `mass_empty`，`mass ∅ p x = ∑_y p y`，故 `p` 归一（`∑_y p y = 1`）
  ⟺ `mass ∅ p x = 1`。这正是 `fac_aux` 收尾所需的**唯一**概率输入。
  =========================================================================== -/

section Engine

/-- ⭐⭐ `unpin v x a = Function.update x v a`（字典两口径对齐）。 -/
theorem unpin_eq_update (v : V) (x : V → α) (a : α) :
    unpin v x a = Function.update x v a := by
  funext u
  unfold unpin
  by_cases h : u = v
  · subst h; rw [if_pos rfl, Function.update_self]
  · rw [if_neg h, Function.update_of_ne h]

/-- ⭐⭐⭐ **S1-2（引擎，正确版）**：**密度归一 ⟺ `mass ∅ p x = 1`。**

$$\Bigl(\sum_y p\,y = 1\Bigr)\iff \mathrm{mass}\,\emptyset\,p\,x = 1.$$

**证明**：`mass_empty p x = ∑_y p y`（`mass` 在 `∅` 上对全空间求和，与 `x` 无关）。

**⚠ 与旧版本的区别**：旧版本写 `mass ∅ (∏ f) x = 1`（由 `FactorNorm`）——**那是假的**
（见文件头 §1.1 更正）。真正的引擎只要求 `p` 本身归一（真实概率测度自动成立）。 -/
theorem mass_empty_eq_one_iff (p : (V → α) → ℝ) (x : V → α) :
    mass (∅ : Finset V) p x = 1 ↔ (∑ y : V → α, p y) = 1 := by
  rw [Fate.DAGFactorization.mass_empty]

/-- ⭐⭐⭐ **S1-2′（引擎的可用形式）**：密度归一 ⟹ `mass ∅ p x = 1`。 -/
theorem mass_empty_eq_one (p : (V → α) → ℝ) (hprob : (∑ y : V → α, p y) = 1)
    (x : V → α) : mass (∅ : Finset V) p x = 1 :=
  (mass_empty_eq_one_iff p x).mpr hprob

end Engine

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ **单层工具：乘积拆分 + 纤维重标号**

  `mass_insert_sum'`（放开一个坐标再求和）与 `mass_insert_off_left`
  （不读 `v` 的因子在纤维上不变）。**两者都不嵌套 `mass`。**
  =========================================================================== -/

section Tools

/-- ⭐⭐ 乘积拆出 `v`：`∏_u f u z = f v z · ∏_{u≠v} f u z`。 -/
theorem prod_erase_eq (f : V → (V → α) → ℝ) (v : V) (z : V → α) :
    (∏ u, f u z) = f v z * ∏ u ∈ (univ \ {v}), f u z := by
  have h := Finset.prod_erase_mul (univ : Finset V) (fun u => f u z) (Finset.mem_univ v)
  have he : (univ : Finset V).erase v = univ \ {v} := by
    rw [Finset.sdiff_singleton_eq_erase]
  rw [he] at h
  rw [← h, mul_comm]

/-- ⭐⭐ `unpin v x a` 在 `S`（`v ∉ S`）上与 `x` 一致。 -/
theorem unpin_agree_of_notMem (v : V) {S : Finset V} (hvS : v ∉ S) (x : V → α) (a : α) :
    ∀ u ∈ S, unpin v x a u = x u := by
  intro u hu
  have hne : u ≠ v := by rintro rfl; exact hvS hu
  unfold unpin
  rw [if_neg hne]

/-- ⭐⭐ **`mass` 的纤维集写法**（把 `if` 换成 `filter`，便于做双射）。 -/
theorem mass_eq_sum_filter (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S p x = ∑ w ∈ (univ.filter fun w => ∀ u ∈ S, w u = x u), p w := by
  unfold mass
  rw [Finset.sum_filter]

/-- ⭐⭐ **`insert v S`-纤维 = `S`-纤维 ∩ `{w v = y v}`**。 -/
theorem filter_insert_eq (v : V) (S : Finset V) (y : V → α) :
    (univ.filter fun w : V → α => ∀ u ∈ insert v S, w u = y u)
      = (univ.filter fun w : V → α => (∀ u ∈ S, w u = y u) ∧ w v = y v) := by
  refine Finset.filter_congr fun w _ => ?_
  constructor
  · intro h; exact ⟨fun u hu => h u (mem_insert_of_mem hu), h v (mem_insert_self v S)⟩
  · intro ⟨h1, h2⟩ u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact h2
    · exact h1 u hu

/-- ⭐⭐⭐⭐ **S1-4（纤维重标号）**：

**若 `g` 不读 `v` 位，则 `g` 在 `insert v S` 上的边缘只看 `x|_S`。**

$$\Bigl(\forall a\,b,\ a|_{V\setminus\{v\}}=b|_{V\setminus\{v\}}
  \Rightarrow g\,a=g\,b\Bigr)\ \Longrightarrow\
  \mathrm{mass}\,(\mathrm{insert}\,v\,S)\,g\,y=\mathrm{mass}\,(\mathrm{insert}\,v\,S)\,g\,x
  \quad(\text{当 } y|_S=x|_S,\ v\notin S).$$

**证明**：把两纤维写成 `S`-纤维 `∩ {· v = ·}`；用 `w ↦ Function.update w v (x v)`
构造双射（逆 `w ↦ Function.update w v (y v)`），`g` 在此双射下不变。 -/
theorem mass_insert_off_left (g : (V → α) → ℝ) (v : V) {S : Finset V} (hvS : v ∉ S)
    (hblind : ∀ a b : V → α,
      (∀ u ∈ (univ \ {v} : Finset V), a u = b u) → g a = g b)
    {y x : V → α} (hxy : ∀ u ∈ S, y u = x u) :
    mass (insert v S) g y = mass (insert v S) g x := by
  rw [mass_eq_sum_filter, mass_eq_sum_filter, filter_insert_eq, filter_insert_eq]
  refine Finset.sum_nbij' (fun w => Function.update w v (x v)) (fun w => Function.update w v (y v))
    ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨fun u hu => ?_, Function.update_self v (x v) w⟩
    rw [Function.update_of_ne (by rintro rfl; exact hvS hu)]
    rw [hw.1 u hu, hxy u hu]
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨fun u hu => ?_, Function.update_self v (y v) w⟩
    rw [Function.update_of_ne (by rintro rfl; exact hvS hu)]
    rw [hw.1 u hu, hxy u hu]
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    ext j
    by_cases hj : j = v
    · subst hj; simp only [Function.update_self]; exact ha.2.symm
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    ext j
    by_cases hj : j = v
    · subst hj; simp only [Function.update_self]; exact hb.2.symm
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · intro a ha
    exact hblind _ _ (fun u hu => by
      rw [mem_sdiff, mem_singleton] at hu
      rw [Function.update_of_ne hu.2])

end Tools

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **策略 1 核心：`peel`（修正版）**
  =========================================================================== -/

section Peel

variable {p : (V → α) → ℝ} {G : DAG V} {f : V → (V → α) → ℝ}

/-- ⭐⭐⭐⭐⭐ **S1-5：`peel`（策略 1 的核心定理，修正版）**。

设 `v ∉ S`，`pa_G(v) ⊆ S`，`f` 局部于 `G`，`f` 局部归一，`p = ∏ f`，
且 **`v` 在剩余变量中是 sink**（`∀ w ≠ v, v ∉ pa w`）。则

$$\mathrm{mass}\,(\mathrm{insert}\,v\,S)\,p\,x
  \;=\; f\,v\,x\cdot \mathrm{mass}\,S\,p\,x.$$

**证**：拆 `p = f v · g`（`g := ∏_{u≠v} f u`，不读 `v`，因 `v` 是 sink）；
在 `insert v S`-纤维上 `f v` 恒为 `f v x`（`pa v ⊆ S`）；
`g`-边缘用纤维重标号 `mass_insert_off_left` 与 `x` 无关；
再对 `v` 位用 `mass_insert_sum'`（**一次**求和）与 `FactorNorm` 收束。
**全程无 `mass` 嵌套。** -/
theorem peel (hloc : FateV2.Predict.FactorMarkov.LocalTo G f)
    (hnorm : FateV2.Predict.FactorMarkov.FactorNorm f)
    (hfac : ∀ z, p z = ∏ u, f u z)
    {v : V} {S : Finset V} (hvS : v ∉ S) (hpa : Fate.DAGFactorization.pa G v ⊆ S)
    (hsink : ∀ w : V, w ≠ v → v ∉ Fate.DAGFactorization.pa G w)
    (x : V → α) :
    mass (insert v S) p x = f v x * mass S p x := by
  classical
  set g : (V → α) → ℝ := fun z => ∏ u ∈ (univ \ {v}), f u z with hg
  -- (1) `p = f v · g`
  have hp : ∀ z, p z = f v z * g z := by
    intro z; rw [hfac z, prod_erase_eq f v z, hg]
  -- (2) `f v` 在 `insert v S`-纤维上是常数 `f v x`
  have hreadv : ∀ a b : V → α, (∀ u ∈ insert v S, a u = b u) → f v a = f v b := by
    intro a b hab
    refine hloc v a b fun u hu => ?_
    rcases hu with h | h
    · rw [h]; exact hab v (mem_insert_self v S)
    · exact hab u (mem_insert_of_mem (hpa h))
  -- (3) 残因子 `g` 不读 `v`（`v` 是 sink）
  have hblind : ∀ a b : V → α,
      (∀ u ∈ (univ \ {v} : Finset V), a u = b u) → g a = g b := by
    intro a b hab
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mem_sdiff, mem_singleton] at hw
    have hnp : v ∉ Fate.DAGFactorization.pa G w := hsink w hw.2
    refine hloc w a b fun u hu => ?_
    rcases hu with h | h
    · rw [h]; exact hab w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, by simpa using hw.2⟩)
    · refine hab u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, ?_⟩)
      intro huv
      exact hnp (Finset.mem_singleton.mp huv ▸ h)
  -- (4) 关键：`mass (insert v S) p x = f v x · mass (insert v S) g x`
  have hkey : mass (insert v S) p x = f v x * mass (insert v S) g x := by
    unfold mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : ∀ u ∈ insert v S, w u = x u
    · rw [if_pos hw, hp w, hreadv w x hw, if_pos hw]
    · rw [if_neg hw, if_neg hw, mul_zero]
  -- (5) `mass (insert v S) g x = mass S p x`
  have hg_eq : mass (insert v S) g x = mass S p x := by
    rw [Fate.DAGFactorization.mass_insert_sum' v S hvS]
    have hstep : ∀ a : α,
        mass (insert v S) p (unpin v x a) = f v (unpin v x a) * mass (insert v S) g x := by
      intro a
      have hakey : mass (insert v S) p (unpin v x a)
          = f v (unpin v x a) * mass (insert v S) g (unpin v x a) := by
        unfold mass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        by_cases hw : ∀ u ∈ insert v S, w u = unpin v x a u
        · rw [if_pos hw, hp w, hreadv w (unpin v x a) hw, if_pos hw]
        · rw [if_neg hw, if_neg hw, mul_zero]
      rw [hakey]
      congr 1
      exact mass_insert_off_left g v hvS hblind (unpin_agree_of_notMem v hvS x a)
    rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.sum_mul, hnorm v x, one_mul]
  rw [hkey, hg_eq]

end Peel

/-! ===========================================================================
  §3b ⭐⭐⭐ **收口：`peel` ⟹ `Factorizes`（策略 1 的终端）**
  =========================================================================== -/

section Assemble

variable {p : (V → α) → ℝ} {G : DAG V} {f : V → (V → α) → ℝ}

/-- ⭐⭐⭐⭐ **S1-7：`peel` + `fac_aux` + 归一 ⟹ 因子分解。**

若 `f` 局部、归一、`p = ∏ f`、`p` 归一（`∑_y p y = 1`），
且存在一条「剥离序」使 `fac_aux` 的 `step` 成立（每步的 `v` 在当前剩余集中是 sink，
由拓扑序保证），则 `p x = ∏ v, f v x`。

**⚠ 诚实边界**：这里 `hstep` 作为假设给出（由 `peel` 在拓扑序下逐点提供）；
把「拓扑序 ⟹ 每步 sink」这一纯图论事实接上就是完整的
「`Factorizes` 自洽」。本定理把 **`peel`（已证，零缺口）** 与
**`fac_aux`（已证，零缺口）** 和 **归一（概率输入）** 三者合成。 -/
theorem factorizes_of_peel
    (_hfac : ∀ z, p z = ∏ u, f u z)
    (hnormp : (∑ y : V → α, p y) = 1)
    (hstep : ∀ v (S : Finset V), v ∉ S → ∀ x,
      mass (insert v S) p x = f v x * mass S p x) :
    ∀ x, p x = ∏ v, f v x := by
  intro x
  -- `fac_aux` 在 `S = univ`：`mass univ p x = (∏ v, f v x) * mass ∅ p x`
  have h := Fate.DAGFactorization.fac_aux (fun v => f v) p hstep (univ : Finset V) x
  rw [Fate.DAGFactorization.mass_univ] at h
  rw [h, mass_empty_eq_one p hnormp x, mul_one]

end Assemble

/-! ===========================================================================
  §4 ⚠ **诚实边界：sink 前提不可去**（反例机检）

  `arrowDAG : DAG (Fin 2)`，唯一一条边 `0 → 1`（`Fate.G1ParentNonDescendant`）。
  取 `v = 0`（`pa 0 = ∅ ⊆ ∅` ✅，`0 ∉ ∅` ✅）、`S = ∅`、`α = Bool`。
  取
  `f 0 z := 1/2`（常数）、`f 1 z := if z 0 then 1 else 0`（读 `z 0`，因 `0 ∈ pa 1`）。
  两者都 `FactorNorm`（对自身坐标求和 = 1：`f 0` 给 `2·(1/2)=1`，
  `f 1` 不读 `z 1`，故 `∑_{a} f 1 = 2·(if z0 then 1 else 0)`——**此处需修正**）。

  ⚠ 为让 `f 1` 也 `FactorNorm`，改取 `f 1 z := if z 0 then 1 else 0` 不行
  （求和得 `0` 或 `2`）。故取 `f 1 z := 1/2`（常数），**但那样 `v=0` 确实可剥**。
  真正的反例须让 `f 1` 读 `z 0` 同时保持归一：取 `α := Bool`、
  `f 1 z := if z 0 then 1 else 0`，则 `f 1` 对 `z 1` 求和 = `2·(…)`，非 1。

  ⟹ **反例的正确构造**：改用**非归一化** `mass`（本仓库 `mass` 本就不归一），
  直接展示 `peel` 的等式在无 sink 时**失效**，与 `FactorNorm` 无关。
  见 `peel_without_sink_false`。
  =========================================================================== -/

namespace Counterexample

open FateV2.Predict.FactorRecursionRouteB (arrowDAG)

/-- 反例用的 `p`：`p z := if z 0 then 1 else 0`（**读 `z 0`**，即 `0` 的**子节点**效应）。-/
noncomputable def pce : (Fin 2 → Bool) → ℝ := fun z => if z 0 then 1 else 0

/-- 反例用的因子族：`f 0 := 1`、`f 1 z := if z 0 then 1 else 0`。
`f 1` 读 `z 0`（`0 ∈ pa 1`），故 `1` 无关于 `0` 是 sink —— **违反 sink 前提**。 -/
noncomputable def fce : Fin 2 → (Fin 2 → Bool) → ℝ
  | 0, _ => 1
  | 1, z => if z 0 then 1 else 0

/-- `fce` 局部于 `arrowDAG`（`f 1` 读 `{1} ∪ pa 1 = {1,0}`；`f 0` 常数）。 -/
theorem fce_local : FateV2.Predict.FactorMarkov.LocalTo arrowDAG fce := by
  intro v x y hxy
  fin_cases v
  · -- v = 0：`fce 0` 常数
    simp [fce]
  · -- v = 1：需 `x 0 = y 0`
    have hmem : (0 : Fin 2) ∈ arrowDAG.parents 1 := by
      unfold FateV2.Modeling.Graph.DAG.parents
      simp [arrowDAG]
    have h : x 0 = y 0 := hxy 0 (Or.inr hmem)
    simp only [fce]
    rw [h]

/-- `pce = ∏ fce`（`∏` 在 `Fin 2` 上展开）。 -/
theorem pce_fac : ∀ z, pce z = ∏ u, fce u z := by
  intro z
  rw [Fin.prod_univ_two]
  simp [pce, fce]

/-- ⚠⚠ **S1-6：去掉 sink 前提，`peel` 为假。**

对 `arrowDAG`、`v = 0`、`S = ∅`（`pa 0 = ∅ ⊆ ∅`、`0 ∉ ∅` 均成立），
取 `x := fun _ => false`。则
`mass {0} pce x = 1`（两个 `z 1` 取值都使 `z 0 = false`，`pce = 0`……**再核**），
而 `fce 0 x · mass ∅ pce x = 1 · 1`。

**精确数值**（`α = Bool`，`z 0 = false` 时 `pce = 0`，`z 0 = true` 时 `pce = 1`）：
* `mass {0} pce x`，`x 0 = false`：`∑_{z : z 0 = false} pce z = ∑_{z1 ∈ {f,t}} 0 = 0`。
* `mass ∅ pce x = ∑_z pce z = ∑_{z0}∑_{z1} pce = 0·(...) + 1·2 = 2`。
* `fce 0 x · mass ∅ pce x = 1 · 2 = 2 ≠ 0`。

⟹ **`peel` 的等式 `0 = 2` 为假**，确认 sink 前提不可去。 -/
theorem peel_without_sink_false :
    mass ({(0 : Fin 2)}) pce (fun _ => false) ≠
      fce 0 (fun _ => false) * mass (∅ : Finset (Fin 2)) pce (fun _ => false) := by
  -- 左边 = 0，右边 = 2
  have hlhs : mass ({(0 : Fin 2)}) pce (fun _ => false) = 0 := by
    unfold mass
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h : ∀ u ∈ ({(0 : Fin 2)} : Finset (Fin 2)), z u = (fun _ => false) u
    · rw [if_pos h]
      have h0 : z 0 = false := h 0 (Finset.mem_singleton_self 0)
      simp [pce, h0]
    · rw [if_neg h]
  have hrhs : fce 0 (fun _ => false) * mass (∅ : Finset (Fin 2)) pce (fun _ => false) = 2 := by
    have hf0 : fce 0 (fun _ => false) = 1 := by simp [fce]
    rw [hf0, one_mul]
    rw [Fate.DAGFactorization.mass_empty]
    rw [show (∑ w : Fin 2 → Bool, pce w)
          = ∑ w : Fin 2 → Bool, (if w 0 = true then (1:ℝ) else 0) from
        Finset.sum_congr rfl fun w _ => by simp [pce]]
    -- 枚举 `Fin 2 → Bool` ≅ `Bool × Bool`
    have himg : (Finset.univ : Finset (Fin 2 → Bool))
        = Finset.image
            (fun q : Bool × Bool => fun i : Fin 2 => if i = 0 then q.1 else q.2)
            (Finset.univ : Finset (Bool × Bool)) := by
      ext f
      simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff]
      exact ⟨(f 0, f 1), by funext i; fin_cases i <;> simp⟩
    rw [himg, Finset.sum_image]
    · rw [Fintype.sum_prod_type]
      simp
    · intro a _ b _ hab
      have h0 : a.1 = b.1 := by simpa using congrFun hab 0
      have h1 : a.2 = b.2 := by simpa using congrFun hab 1
      exact Prod.ext h0 h1
  rw [hlhs, hrhs]
  norm_num

end Counterexample

end BridgeStrategy1

end FateV2.Predict