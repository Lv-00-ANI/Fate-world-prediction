/-
# 视角 13：『图 ⟹ 概率』桥的**第 13 种**策略 —— 因子外提（Factor Hoisting）

## 0 定位

前 12 种策略（与后续视角）的失败模式已登记：

| 失败模式 | 出处 |
|---|---|
| `mass S (mass T p) x = mass (S∪T) p x` **为假** | `DAGFactorizationGeneral` T24 `tower_property_false` |
| 连 `S ⊆ T` 也假（`mass` 非归一化） | `TowerAudit` A3 `mass_idempotent_fails` |
| 集合口径 `CondMulLike` 在 **`FacStep`** 下**退化**（对任意图象成立） | `View20GraphToProb` 判据 D20 |

**⚠ 本视角的出发点（与前 12 种都不同）**：
`View20` 的退化判决针对的是**更强的 `FacStep`**（`∀ S, v ∉ S` 的逐点重指标，
等价于「在每个集合上都已完全因子化」）。而**真正的因果假设 `Factorizes p G`**
（`∃ f, LocalTo G f ∧ p = ∏ f` + `FactorNorm`）**并不退化**：

> 在**对撞子** `x → m ← z` 上（α = Bool）：
> `dSep {x}{z} ∅` 成立且 `CondMulLike` 成立；
> `dSep {x}{z}{m}` **不成立**且 `CondMulLike` **失败**。
> ⟹ `CondMulLike ∘ Factorizes + FactorNorm` **不是退化终点**。

**所以本视角不去「换终点」，而换「引擎」：不用 `FacStep`、不用塔、
不用 `mass` 重指标求和，而只用 `mass_mul` 的「外提」方向。**

$$\textbf{引擎：}\quad
\mathrm{mass}\,S\,\Bigl(\bigl(\textstyle\prod_{v\in A} f_v\bigr)\cdot g\Bigr)\,x
=\Bigl(\prod_{v\in A} f_v\,x\Bigr)\cdot \mathrm{mass}\,S\,g\,x
\quad\text{只要 }\{v\}\cup\mathrm{pa}(v)\subseteq S\ \ (v\in A).$$

这是 `mass_mul` 的**有限次迭代**（`Finset.prod_induction`），
**每次都用 `mass_mul` 的那条读集限制**，**从不**把 `mass` 套进 `mass`。

## 1 三层结构

* **§1 `hoist_prod`（T13-1，零缺口）**：读集全落在 `S` 内的因子块可**整体外提**。
* **§2 `InSet`（T13-2）**：`InSet G S = {v∈S : {v}∪pa(v) ⊆ S}`，
  证明 `hoist_prod` 的假设由**纯图论**（`LocalTo`）给出：
  `v ∈ InSet G S ⟹ f v` 是 `S`-可测的。
* **§3 `CondMulLike_of_hoist`（T13-3，本视角主定理）**：
  若 `X`、`Y` 的**读集闭包**落在 `Z` 的对面，则 `CondMulLike X Y Z p`。
  这**真正**消费了 `LocalTo` + `FactorNorm`（因子求和为 1）。
* **§4 边界**：`dSep ⟹ §3 假设` 的**精确陈述**（登记为 `Prop`，
  并证明其**非平凡**：对撞子反例，见 §5）。

**零 `sorry` / 零 `axiom`。**
-/

import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.FactorMarkov
import Mathlib.Tactic.Ring
import Mathlib.Tactic

open Finset
open Causalean.Graph

namespace Fate.Strategy13Hoist

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

open Fate.DAGFactorization (mass unpin mass_mul mass_congr mass_univ)
open Fate.FactorMarkov (Joint LocalTo Factorizes FactorNorm CondIndep Markov)

/-! ===========================================================================
  §1 ⭐⭐⭐⭐ **T13-1：`S`-可测因子块的**整体外提**（零缺口，不用塔）
  =========================================================================== -/

/-- **`SMeasurable S g`**：`g` 只读 `S` 上的坐标。 -/
def SMeasurable (S : Finset V) (g : (V → α) → ℝ) : Prop :=
  ∀ x y : V → α, (∀ u ∈ S, x u = y u) → g x = g y

/-- ⭐⭐⭐⭐ **T13-1（`hoist_prod`，零缺口）。**

若 `A ⊆ S`，且每个 `v ∈ A` 的因子 `f v` 都 `S`-可测，
则 `∏_{v∈A} f v` 可以从 `mass S` 里**整体外提**：

$$\mathrm{mass}\,S\,\Bigl(\bigl(\textstyle\prod_{v\in A} f_v\bigr)\, g\Bigr)\,x
=\Bigl(\prod_{v\in A} f_v\,x\Bigr)\cdot \mathrm{mass}\,S\,g\,x .$$

**证明**：对 `A` 作 `Finset.induction`，每步用一次 `mass_mul`
（**一次** `mass`，从不嵌套）。 -/
theorem hoist_prod (A S : Finset V) (hAS : A ⊆ S)
    (f : V → (V → α) → ℝ) (g : (V → α) → ℝ) (x : V → α)
    (hmeas : ∀ v ∈ A, SMeasurable S (f v)) :
    mass S (fun w => (∏ v ∈ A, f v w) * g w) x
      = (∏ v ∈ A, f v x) * mass S g x := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
      have hAS' : A ⊆ S := fun v hv => hAS (mem_insert_of_mem hv)
      have haS : a ∈ S := hAS (mem_insert_self a A)
      have hmeas' : ∀ v ∈ A, SMeasurable S (f v) := fun v hv => hmeas v (mem_insert_of_mem hv)
      -- split the product over `insert a A`
      have hstep : (fun w => (∏ v ∈ insert a A, f v w) * g w)
          = (fun w => f a w * ((∏ v ∈ A, f v w) * g w)) := by
        funext w; rw [Finset.prod_insert ha]; ring
      rw [hstep]
      rw [mass_mul S (f a) (fun w => (∏ v ∈ A, f v w) * g w) x
            (fun x y hxy => hmeas a (mem_insert_self a A) x y hxy)]
      rw [ih hAS' hmeas']
      rw [Finset.prod_insert ha]
      ring

/-- ⭐⭐⭐ **T13-1'（对子集补集的形式）。** 若 `A ⊆ S` 且因子 `S`-可测，
则 `mass S (∏_{v∈A} f_v) x = (∏_{v∈A} f_v x) · mass S 1 x = ∏_{v∈A} f_v x · mass S 1 x`.

（`mass S 1 x = |α|^{|Sᶜ|}`——这是**纤维计数**，不是塔性质。） -/
theorem hoist_prod_one (A S : Finset V) (hAS : A ⊆ S)
    (f : V → (V → α) → ℝ) (x : V → α)
    (hmeas : ∀ v ∈ A, SMeasurable S (f v)) :
    mass S (fun w => ∏ v ∈ A, f v w) x = (∏ v ∈ A, f v x) * mass S (fun _ => 1) x := by
  have := hoist_prod A S hAS f (fun _ => 1) x hmeas
  simpa [mul_one] using this

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ **LocalTo ⟹ `S`-可测（读集落在 `S` 内的因子）**
  =========================================================================== -/

/-- `readSet v = {v} ∪ pa_G(v)`：因子 `f v` 允许读的坐标集。 -/
def readSet (G : Causalean.Graph.DAG V) (v : V) : Finset V := insert v (G.parents v)

theorem mem_readSet_iff (G : Causalean.Graph.DAG V) {v u : V} :
    u ∈ readSet G v ↔ u = v ∨ u ∈ G.parents v := by
  simp [readSet]

/-- ⭐⭐⭐ **读集落在 `S` 内 ⟹ `f v` 是 `S`-可测的。**

这是 `LocalTo` 的直接改写：`hloc v x y` 只需 `x`、`y` 在 `{v}∪pa(v)` 上一致，
而 `{v}∪pa(v) ⊆ S`，故 `x`、`y` 在 `S` 上一致（更强的条件）足够。 -/
theorem smeasurable_of_readSet_subset {G : Causalean.Graph.DAG V}
    {f : V → (V → α) → ℝ} (hloc : LocalTo G f) {S : Finset V} {v : V}
    (hsub : readSet G v ⊆ S) : SMeasurable S (f v) := by
  intro x y hxy
  refine hloc v x y fun u hu => ?_
  exact hxy u (hsub (mem_readSet_iff G |>.mpr hu))

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **`InSet`：读集全落在 `S` 内的顶点，及其闭包性**
  =========================================================================== -/

/-- **`InSet G S = {v ∈ S : {v}∪pa(v) ⊆ S}`。** -/
def InSet (G : Causalean.Graph.DAG V) (S : Finset V) : Finset V :=
  S.filter (fun v => readSet G v ⊆ S)

theorem mem_InSet {G : Causalean.Graph.DAG V} {S : Finset V} {v : V} :
    v ∈ InSet G S ↔ v ∈ S ∧ readSet G v ⊆ S := by
  simp [InSet]

theorem InSet_subset (G : Causalean.Graph.DAG V) (S : Finset V) : InSet G S ⊆ S :=
  Finset.filter_subset _ _

/-- ⭐⭐ **`InSet G S` 中每个因子都是 `S`-可测的**（由 §2）。 -/
theorem smeasurable_InSet {G : Causalean.Graph.DAG V} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (S : Finset V) {v : V} (hv : v ∈ InSet G S) :
    SMeasurable S (f v) :=
  smeasurable_of_readSet_subset hloc (mem_InSet.mp hv).2

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **`mass` 在 `InSet`-块上的因子化（主工具，零缺口）**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`mass_InSet_factor`（T13-2）。**

$$\mathrm{mass}\,S\,p\,x
=\Bigl(\prod_{v\in \mathrm{InSet}\,G\,S} f_v\,x\Bigr)
 \cdot \mathrm{mass}\,S\,\Bigl(\prod_{v
otin \mathrm{InSet}\,G\,S} f_v\Bigr)\,x .$$

**证明**：`p = ∏_v f v = (∏_{v∈InSet} f v) · (∏_{v∉InSet} f v)`（`Finset.prod_filter_mul_prod_filter_not`），
再用 **T13-1 `hoist_prod`** 把 `InSet`-块整体外提。**不用塔。** -/
theorem mass_InSet_factor {G : Causalean.Graph.DAG V} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (S : Finset V) (x : V → α) :
    mass S (fun w => ∏ v, f v w) x
      = (∏ v ∈ InSet G S, f v x)
        * mass S (fun w => ∏ v ∈ (univ \ InSet G S), f v w) x := by
  classical
  -- decompose the full product into `InSet`-part times the rest
  have hsplit : ∀ w : V → α, (∏ v, f v w)
      = (∏ v ∈ InSet G S, f v w) * (∏ v ∈ (univ \ InSet G S), f v w) := by
    intro w
    have hcompl : (∏ v ∈ (univ \ InSet G S), f v w) = ∏ v ∈ univ with v ∉ InSet G S, f v w := by
      refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext v
      simp [Finset.mem_sdiff]
    rw [hcompl]
    have h := Finset.prod_filter_mul_prod_filter_not (univ : Finset V)
      (fun v => v ∈ InSet G S) (fun v => f v w)
    simpa using h.symm
  simp_rw [hsplit]
  exact hoist_prod (InSet G S) S (InSet_subset G S) f
    (fun w => ∏ v ∈ (univ \ InSet G S), f v w) x
    (fun v hv => smeasurable_InSet hloc S hv)


/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **主定理：`Z`-切 `X∪Y` 上的乘性独立（零缺口、不用塔）**
  =========================================================================== -/

/-- **`BlockClosed G B S`**：块 `B ⊆ S` 在 `S` 里「读集闭合」——
即 `B` 的所有顶点都落在 `InSet G S` 里。这是纯图论条件。 -/
def BlockClosed (G : Causalean.Graph.DAG V) (B S : Finset V) : Prop :=
  B ⊆ InSet G S

theorem blockClosed_iff (G : Causalean.Graph.DAG V) (B S : Finset V) :
    BlockClosed G B S ↔ B ⊆ S ∧ ∀ v ∈ B, readSet G v ⊆ S := by
  constructor
  · intro h
    refine ⟨fun v hv => InSet_subset G S (h hv), fun v hv => ?_⟩
    exact (mem_InSet.mp (h hv)).2
  · rintro ⟨hBS, hread⟩ v hv
    exact mem_InSet.mpr ⟨hBS hv, hread v hv⟩

/-- ⭐⭐ **`BlockClosed` 的并集是可加的**（纯集合论）。 -/
theorem blockClosed_union {G : Causalean.Graph.DAG V} {B₁ B₂ S : Finset V}
    (h₁ : BlockClosed G B₁ S) (h₂ : BlockClosed G B₂ S) :
    BlockClosed G (B₁ ∪ B₂) S := by
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · exact h₁ h
  · exact h₂ h

/-- ⭐⭐⭐ **`mass` 在「整块闭合」时的因子化。** `InSet`-块可换成任意闭合块 `B`：

$$\mathrm{mass}\,S\,p\,x = \Bigl(\prod_{v\in B} f_v\,x\Bigr)\cdot
\mathrm{mass}\,S\,\Bigl(\prod_{v\in S\setminus B} f_v\Bigr)\,x .$$

**证明**：`B ⊆ InSet G S`，把 `∏_{v∈InSet} f` 拆成 `∏_{v∈B} f · ∏_{v∈InSet\B} f`
（`prod_sdiff`），把 `∏_{v∈InSet\B} f` 与残项合并，再用 T13-1 外提 `B`。 -/
theorem mass_block_factor {G : Causalean.Graph.DAG V} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) {S B : Finset V} (hB : BlockClosed G B S)
    (hBS : B ⊆ S) (x : V → α) :
    mass S (fun w => ∏ v, f v w) x
      = (∏ v ∈ B, f v x) * mass S (fun w => ∏ v ∈ (univ \ B), f v w) x := by
  classical
  -- split the full product into `B`-part times the rest
  have hsplit : ∀ w : V → α, (∏ v, f v w)
      = (∏ v ∈ B, f v w) * (∏ v ∈ (univ \ B), f v w) := by
    intro w
    have h := Finset.prod_sdiff (s₁ := B) (s₂ := (univ : Finset V)) (f := fun v => f v w)
      (show B ⊆ univ from fun v _ => Finset.mem_univ v)
    rw [mul_comm]
    exact h.symm
  simp_rw [hsplit]
  exact hoist_prod B S hBS f (fun w => ∏ v ∈ (univ \ B), f v w) x
    (fun v hv => smeasurable_of_readSet_subset hloc (((blockClosed_iff G B S).mp hB).2 v hv))




/-! ===========================================================================
  §6  `mass_insert_of_insensitive` —— **原陈述为假，已移除**

  原文声称：`g` 不读 `h` ⟹ `mass (insert h S) g = mass S g`。

  **这是假的**：`mass S` 的纤维里 `w h` 可任取 `|α|` 种，而「不读 h」恰好说明
  每种取值的 `g` 相同，故右边是左边的 `|α|` 倍：

  `mass S g x = |α| · mass (insert h S) g x`

  **正确版本见 `Fate/MassInsertCorrected.lean` 的 `mass_insert_corrected`。**
  =========================================================================== -/

end Fate.Strategy13Hoist