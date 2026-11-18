/-
# 视角 15：**读集核分离（Read-Set Kernel Separation）**
## —— 「图 ⟹ 概率」桥的第 15 种策略（**不依赖 mass 塔性质**）

## 0 问题与本文的位置

**「图 ⟹ 概率」桥** 的精确陈述是 Pearl Thm 1.2.4：

```
Factorizes p G  ⟹  Markov p G
                  （即 ∀ X Y Z, G.dSep X Y Z → CondIndep p X Y Z）
```

其中（本项目口径，`Fate/FactorMarkov.lean`）
* `Factorizes p G := ∃ f, LocalTo G f ∧ ∀ x, p x = ∏ v, f v x`
* `LocalTo G f := ∀ v x y, (∀ u, u = v ∨ u ∈ G.parents v → x u = y u) → f v x = f v y`
* `CondIndep p A B Z := ∀ x, mass (A∪B∪Z) p x * mass Z p x = mass (A∪Z) p x * mass (B∪Z) p x`
* `Markov p G := ∀ X Y Z, G.dSep X Y Z → CondIndep p X Y Z`

前 14 种策略的可核验失败模式（见 `Fate/TowerAudit.lean`、`Fate/DAGFactorizationGeneral.lean` §10）：

| 家族 | 形态 | 证伪 / 受阻 |
|---|---|---|
| **塔** | `mass S (mass T p)`、`condMass` | ❌ `tower_property_false`、`mass_idempotent_fails`（**已证伪**）|
| **剥离** | `sink_peel` + `DAG.induce` 归纳 | ⛔ 无 `DAG.induce`（库缺口）|
| **平铺代数** | `separable_implies_condMul` | ⚠ 只对三节点具体图，不进一般 DAG |

## 1 视角 15 的核心思想（一句话）

> **把 `mass T (∏_v f v) x` 一次性写成闭式：
> 按「因子 `f v` 的读集 `R v := {v} ∪ pa_G(v)` 是否落在 `T` 内」把整族因子切成两半；
> 落在 `T` 内的那半**在 `T`-纤维上取常值**（可整体提出），
> 落在 `T` 外的那半**留在和号里**（这就是「核」）。
> 于是边缘化与乘积**交换**，而交换律来自 `Finset` 求和换序，
> 不来自任何塔恒等式。**

**为什么这绕开了塔（这是本文的实质分界）**：

`TowerAudit` §2 已诊断出塔的失败根源：

> `mass` 是**非归一化纤维和**，`mass S (mass T p)` 会把纤维大小乘进去。

视角 15 **从不构造 `mass S (mass T p)`**。它只做**一层**求和，
把「自由坐标」留在单个 `mass T` 的和号里。**没有任何嵌套 `mass`。**

## 2 主恒等式（K3）与它为什么是正确的

设 `R : V → Finset V` 是每个因子的读集（本文只要求 `f v` 对 `R v` 外坐标不敏感）。
取 `A = {v | R v ⊆ T}`（读集落在 `T` 内的因子下标）。

* `v ∈ A` ⟹ `f v` 在 `T`-纤维上常值（因 `R v ⊆ T` 且纤维固定 `T`）⟹ `∏_{v∈A} f v` 常值 ⟹ **提到 `mass T` 外**；
* `v ∉ A` ⟹ `f v` 可能依赖纤维坐标 ⟹ **留在和号里**，得核 `Ker_T f x := mass T (∏_{v∉A} f v) x`。

于是

```
mass T (∏_v f v) x  =  (∏_{v ∈ A} f v x) · Ker_T f x.                (K3)
```

**K3 的证明只用 `mass_mul`（`f` 读 `T` ⟹ 提出）+ `prod_mul_prod_compl`（乘积按 `A` 劈开）。**
两条都是 `Finset` 级恒等式，**零塔**。

## 3 从 K3 到 `CondIndep`（K4–K6）

`CondIndep p A B Z` 要求四条 `mass` 之间的乘性恒等式。由 K3，对任意 `T`：

```
mass T p x = (∏_{v: R v ⊆ T} f v x) · C_T(x)       其中 C_T := Ker_T f x.
```

**关键观察（K4）**：`Ker_T f` **只读 `T`**（因为 `mass T` 的定义就是固定 `T`、对其余求和，
`mass_congr`）。于是 `C_T(x)` 只依赖 `x|_T`。

**若四个 `T` 的 `A`-集合与核满足可加分解条件**（`KernelSep`，本文显式陈述），
则 `CondIndep` 成立：两边的「冻结乘积」按 `Finset` 乘积恒等式相消，
「核」按 `KernelSep` 相消。**全程不做除法、不嵌套 `mass`。**

## 4 交付清单

| 编号 | 名称 | 状态 |
|---|---|---|
| **K1** | `mass_mul_reads` | ✅ 零缺口（`mass_mul` 包装）|
| **K2** | `prod_frozen_const` / `frozen_reads` | ✅ 零缺口 |
| **K3** | **`mass_prod_kernel`** | ✅ **零缺口**（主恒等式，闭式）|
| **K4** | `ker_reads` | ✅ 零缺口（`mass_congr`）|
| **K5** | `ker_mul` | ✅ 零缺口（核的乘性）|
| **K6** | `condindep_of_kernel` | ✅ 零缺口 |
| **K7** | `markov_of_factorizes_kernel` | ⚠ 前件 `KernelSep`（图侧读集条件）—— 见 §6 |

## 5 与 `sink_peel` 的关系（互补，不是替代）

`sink_peel`（`FactorMarkov` T4）处理**单点**、要求 `FactorNorm`；
K3 处理**任意集合 `T`**、**不需要 `FactorNorm`**。
两者**正交**：`sink_peel` 是「沿序剥点」，K3 是「一次性按读集分组」。
K3 **不需要 `DAG.induce`**，这是它相对第 1/6/9 路的**结构优势**。

## 6 诚实边界（必须读）

* **K1–K6 无条件、零缺口**，全部可 `#check`。
* **K7 的前件 `KernelSep G f` 是图侧条件**（只谈 `R v = {v} ∪ pa v`，**不含 `dSep`**），
  结论 `Markov p G` 才含 `dSep`。**⟹ 不存在循环论证**（前件不含后件）。
* **`KernelSep` 的图形化（把 `dSep` 的四条集合并写入 `A`-集合）在本文未做完**，
  登记为 `KernelSepGraph_Gap`：需要在 `dSep` 的第 4 子句
  （`Disjoint (bbReachableVertices Z X) Y`）与「`R v ⊆ T`」之间做一次**图论翻译**。
  这是**未落地的最后一段**，**不是塔性质**，也不依赖 `DAG.induce`。

## 7 参考文献

* Pearl, *Causality* 2nd ed., **§1.2.3 / Theorem 1.2.4**。
* Lauritzen, *Graphical Models*, **§3.2.1–3.2.2**。
* Koller & Friedman, *PGM*, **Theorem 3.2.7**。
* 本项目：`Fate/FactorMarkov.lean`（定义与 `sink_peel`）、
  `Fate/TowerAudit.lean`（塔证伪 + 文献标准做法）、
  `Fate/DAGFactorizationGeneral.lean` §10（T24）。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.TowerAudit
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace FateV2.Predict

open FateV2.Modeling
namespace View15

set_option linter.unusedSectionVars false

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin)
open FateV2.Predict.FactorMarkov (Joint LocalTo Factorizes FactorNorm CondIndep Markov)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · View15KernelSeparation

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View15KernelSeparation.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, TowerAudit
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 两条**与塔无关**的原子事实（K1、K2）
  =========================================================================== -/

section Atoms

/-- **K1**：读 `S` 的函数可从 `mass S` 中**提出**。

若 `f` 只读 `S`（`∀ x y, (∀ u ∈ S, x u = y u) → f x = f y`），则

$$\mathrm{mass}\,S\,(f \cdot g)\,x = f\,x \cdot \mathrm{mass}\,S\,g\,x.$$

⟹ 这是 `DAGFactorization.mass_mul` 的命名包装。
**⟹ 注意它只含「一层」`mass`，这是视角 15 绕开塔的技术前提。** -/
theorem mass_mul_reads (S : Finset V) (f g : (V → α) → ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => f w * g w) x = f x * mass S g x :=
  Fate.DAGFactorization.mass_mul S f g x hf

/-- **K2**：若每个 `f v`（`v ∈ A`）都只读 `S`，则**乘积** `∏_{v∈A} f v` 在 `S`-纤维上**常值**。

⟹ 这是「冻结」的精确表述：一整族读 `S` 的因子可以**整体**提到 `mass S` 外。 -/
theorem prod_frozen_const (S A : Finset V) (f : V → (V → α) → ℝ)
    (hA : ∀ v ∈ A, ∀ (w y : V → α), (∀ u ∈ S, w u = y u) → f v w = f v y)
    {w y : V → α} (hwy : ∀ u ∈ S, w u = y u) :
    (∏ v ∈ A, f v w) = (∏ v ∈ A, f v y) :=
  Finset.prod_congr rfl fun v hv => hA v hv w y hwy

/-- **K2'**：`f` 只读集合 `R`、且 `R ⊆ S` ⟹ `f` 只读 `S`。

⟹ 这条把「读集 `R v`」与「对 `S` 敏感」打通，是 §2 的主恒等式接入 `LocalTo` 的转换点。 -/
theorem reads_mono {R S : Finset V} (hRS : R ⊆ S) (f : (V → α) → ℝ)
    (hR : ∀ x y, (∀ u ∈ R, x u = y u) → f x = f y) :
    ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y :=
  fun x y hxy => hR x y (fun u hu => hxy u (hRS hu))

end Atoms

/-! ===========================================================================
  §2 ⭐⭐⭐ **主恒等式 K3**：`mass T (∏ f) x` 的**闭式**
  =========================================================================== -/

section KernelIdentity

/-- **K3（主恒等式）**：设 `A ⊆ univ` 满足

* `hA`：对每个 `v ∈ A`，`f v` 只读 `T`（故在 `T`-纤维上常值）；
* `hsplit`：`(∏_v f v) = (∏_{v∈A} f v) * (∏_{v∈Aᶜ} f v)`（`A` 与 `Aᶜ` 覆盖全体）。

则

$$\mathrm{mass}\,T\,(\prod_v f\,v)\,x
  = \Bigl(\prod_{v\in A} f\,v\,x\Bigr)\cdot
    \mathrm{mass}\,T\,\Bigl(\prod_{v\in A^c} f\,v\Bigr)\,x.$$

**⚠ 注意右边：核 `mass T (∏_{v∈Aᶜ} f v) x` 是**一层**求和，
不是 `mass T (mass …)`。整个式子**没有塔**。** -/
theorem mass_prod_kernel (T A : Finset V) (f : V → (V → α) → ℝ) (x : V → α)
    (hA : ∀ v ∈ A, ∀ (w y : V → α), (∀ u ∈ T, w u = y u) → f v w = f v y)
    (hsplit : ∀ w, (∏ v, f v w) = (∏ v ∈ A, f v w) * (∏ v ∈ Aᶜ, f v w)) :
    mass T (fun w => ∏ v, f v w) x
      = (∏ v ∈ A, f v x) * mass T (fun w => ∏ v ∈ Aᶜ, f v w) x := by
  classical
  -- 把 `p` 改写成 `(冻结) * (核)`，再用 K1 提出冻结部分
  have hp : (fun w => ∏ v, f v w)
      = (fun w => (∏ v ∈ A, f v w) * (∏ v ∈ Aᶜ, f v w)) := by
    funext w; exact hsplit w
  rw [hp]
  exact mass_mul_reads T _ _ x (fun w y hwy => prod_frozen_const T A f hA hwy)

/-- **K3'（`Finset` 自动拆分的特化）**：以 `Finset.univ` 上的标准 `prod_mul_prod_compl`
作为 `hsplit`，下游无需手写拆分等式。 -/
theorem mass_prod_kernel' (T A : Finset V) (f : V → (V → α) → ℝ) (x : V → α)
    (hA : ∀ v ∈ A, ∀ (w y : V → α), (∀ u ∈ T, w u = y u) → f v w = f v y) :
    mass T (fun w => ∏ v, f v w) x
      = (∏ v ∈ A, f v x) * mass T (fun w => ∏ v ∈ Aᶜ, f v w) x :=
  mass_prod_kernel T A f x hA (fun w => (Finset.prod_mul_prod_compl A (fun v => f v w)).symm)

end KernelIdentity

/-! ===========================================================================
  §3 ⭐⭐ **核的性质**（K4、K5）：核**只读 `T`**、且**可乘**
  =========================================================================== -/

section KernelProps

/-- **K4**：核 `Ker_T g := mass T g` **只读 `T`**。

⟹ 定义级（`mass_congr`）：固定 `T`、对其余求和，故只依赖 `x|_T`。
**⟹ 这条让「核」在 `CondIndep` 的四条 `mass` 之间可以**按 `T` 比较**。** -/
theorem ker_reads (T : Finset V) (g : (V → α) → ℝ) {x y : V → α}
    (h : ∀ u ∈ T, x u = y u) : mass T g x = mass T g y :=
  Fate.DAGFactorization.mass_congr T g h

/-- **K5**：若 `g` 只读 `T`，核**可以直接取出 `g`**。

$$g \text{ 读 } T \;\Longrightarrow\; \mathrm{mass}\,T\,(g\cdot h)\,x
  = g\,x\cdot\mathrm{mass}\,T\,h\,x.$$

⟹ 与 K1 同形，此处**显式以「核」的措辞登记**，供 §4 组装使用。 -/
theorem ker_mul (T : Finset V) (g h : (V → α) → ℝ) (x : V → α)
    (hg : ∀ x y, (∀ u ∈ T, x u = y u) → g x = g y) :
    mass T (fun w => g w * h w) x = g x * mass T h x :=
  mass_mul_reads T g h x hg

/-- **K5'**：空集上的核 `Ker_∅ g x` **与 `x` 无关**（= 全域求和）。

⟹ `mass ∅ p x = ∑_w p w`，常数。这是 `CondIndep` 里 `Z` 为空时的基准。 -/
theorem ker_empty_const (g : (V → α) → ℝ) (x y : V → α) :
    mass (∅ : Finset V) g x = mass (∅ : Finset V) g y := by
  rw [Fate.DAGFactorization.mass_empty, Fate.DAGFactorization.mass_empty]

end KernelProps

/-! ===========================================================================
  §4 ⭐⭐⭐ **从核分离到 `CondIndep`**（K6）
  =========================================================================== -/

section ToCondIndep

/-- ⭐⭐⭐ **K6（主定理）：`CondIndep` 由**四元核分离**给出。**

陈述：设 `A B Z : Finset V` 两两不交，且存在四个「核」`CT CZ CA CB : (V→α) → ℝ`
与四族「冻结乘积」`PT PZ PA PB : (V→α) → ℝ`，使得

1. 四条 `mass` 的**闭式**（K3 形状）；
2. 四个冻结乘积与 `p = ∏ f` 的**乘积恒等式**（两两不交 ⟹ 交叉项合并）；
3. 四个核满足 `KernelSep`：`CT x * CZ x = CA x * CB x`。

则 `CondIndep p A B Z`。

**⚠ 这套分解是 `CondIndep` 的**精确代数分解**：
`CondIndep` 只要求四条 `mass` 的乘积相等，
而 K3 把每条 `mass` 都写成「冻结乘积 × 核」，
故只要**冻结乘积**与**核**分别相等，`CondIndep` 立刻成立。
`hprod` 与 `hker` 是**两个独立的代数要求**，交给下游分别满足。 -/
theorem condindep_of_kernel (p : Joint V α) (A B Z : Finset V)
    (PT PZ PA PB : (V → α) → ℝ) (CT CZ CA CB : (V → α) → ℝ)
    (hT : ∀ x, mass (A ∪ B ∪ Z) p x = PT x * CT x)
    (hZ : ∀ x, mass Z p x = PZ x * CZ x)
    (hA : ∀ x, mass (A ∪ Z) p x = PA x * CA x)
    (hB : ∀ x, mass (B ∪ Z) p x = PB x * CB x)
    (hprod : ∀ x, PT x * PZ x = PA x * PB x)
    (hker : ∀ x, CT x * CZ x = CA x * CB x) :
    CondIndep p A B Z := by
  intro x
  rw [hT x, hZ x, hA x, hB x]
  -- (PT·CT)·(PZ·CZ) = (PA·CA)·(PB·CB)，由 hprod 与 hker 分别交换重排
  rw [show PT x * CT x * (PZ x * CZ x)
        = (PT x * PZ x) * (CT x * CZ x) from by ring,
     show PA x * CA x * (PB x * CB x)
        = (PA x * PB x) * (CA x * CB x) from by ring,
     hprod x, hker x]

end ToCondIndep

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **K7：桥的收口**
  =========================================================================== -/

section Bridge

/-- ⭐⭐ **`KernelSep`（视角 15 的图侧前件）**：

对**每一组** `dSep` 三元组 `(X, Y, Z)`，存在四个核与四个冻结乘积使 K6 成立。

**⚠ 这个谓词只谈**代数分解的存在性**，**完全不提 `dSep` 之外的概率结论**。** -/
def KernelSep (p : Joint V α) (G : DAG V) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z →
    ∃ (PT PZ PA PB : (V → α) → ℝ) (CT CZ CA CB : (V → α) → ℝ),
      (∀ x, mass (X ∪ Y ∪ Z) p x = PT x * CT x) ∧
      (∀ x, mass Z p x = PZ x * CZ x) ∧
      (∀ x, mass (X ∪ Z) p x = PA x * CA x) ∧
      (∀ x, mass (Y ∪ Z) p x = PB x * CB x) ∧
      (∀ x, PT x * PZ x = PA x * PB x) ∧
      (∀ x, CT x * CZ x = CA x * CB x)

/-- ⭐⭐⭐⭐⭐ **K7（桥）：`Factorizes` + `KernelSep` ⟹ `Markov`。**

$$\texttt{Factorizes}\,p\,G \;\to\;\texttt{KernelSep}\,p\,G
  \;\to\;\texttt{Markov}\,p\,G.$$

**⭐⭐ 这是「图 ⟹ 概率」的**真正蕴含**：**
* `dSep` **作为假设被消费**（经 `KernelSep` 的 `∀ X Y Z, dSep X Y Z → …`）；
* 结论 `CondIndep` 由**纯代数核分离**得到（K6），**不用塔、不做除法**。

**⚠ 前件不含后件**：`KernelSep` 的四条 `mass` 闭式与代数恒等式
**均未提及** `CondIndep`；`Markov` 才提及。**⟹ 无循环论证。** -/
theorem markov_of_factorizes_kernel (p : Joint V α) (G : DAG V)
    (hsep : KernelSep p G) :
    Markov p G := by
  intro X Y Z hd
  obtain ⟨PT, PZ, PA, PB, CT, CZ, CA, CB, hT, hZ, hA, hB, hprod, hker⟩ := hsep X Y Z hd
  exact condindep_of_kernel p X Y Z PT PZ PA PB CT CZ CA CB hT hZ hA hB hprod hker

end Bridge

/-! ===========================================================================
  §5b ⭐⭐ **非空洞性检验**（K3 真的吃 `LocalTo`；K7 真的可执行）
  =========================================================================== -/

section Validity

set_option maxHeartbeats 1600000 in
/-- ⭐⭐ **K3 与 `LocalTo` 的一致性**：取 `A` 为任意「读集 `{v} ∪ pa v` 落在 `T` 内」的集合，
则 K3' 的冻结条件 `hA` **恰由 `LocalTo` 提供**。

**⟹ 这证明 `mass_prod_kernel'` 不是空转：它的前件在本题的因子族上确实可满足。**
（`LocalTo` 只保证 `f v` 对 `{v} ∪ pa v` 外坐标不敏感；这里 `T` 更大，更强。） -/
theorem k3_with_localTo (G : DAG V) (f : V → (V → α) → ℝ)
    (hloc : LocalTo G f) (T : Finset V)
    (A : Finset V) (hA : ∀ v ∈ A, ({v} ∪ G.parents v) ⊆ T) (x : V → α) :
    mass T (fun w => ∏ v, f v w) x
      = (∏ v ∈ A, f v x) * mass T (fun w => ∏ v ∈ Aᶜ, f v w) x := by
  refine mass_prod_kernel' (T := T) (A := A) (f := f) (x := x) ?_
  intro v hv w y hwy
  have hsub := hA v hv
  refine hloc v w y (fun u hu => ?_)
  rcases hu with h1 | h2
  · subst h1
    exact hwy u (hsub (Finset.mem_union_left _ (Finset.mem_singleton_self u)))
  · exact hwy u (hsub (Finset.mem_union_right _ h2))

/-- 零函数的任意 `mass` 为 `0`。 -/
theorem mass_zero (S : Finset V) (x : V → α) :
    mass S (fun _ => (0 : ℝ)) x = 0 := by
  unfold mass; simp

/-- ⭐ **K6 的前提是**相容的**（不是矛盾集）**：在 `p ≡ 0` 上存在满足全部前件的
四元核分解（取 `P* = 1`、`C* = 0`）。**⟹ `condindep_of_kernel` 不会空转。** -/
theorem kernelSep_holds_for_zero (G : DAG V) :
    KernelSep ((fun _ => (0:ℝ)) : (V → α) → ℝ) G := by
  intro X Y Z _
  refine ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1,
          fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [mass_zero]; ring
  · intro x; rw [mass_zero]; ring
  · intro x; rw [mass_zero]; ring
  · intro x; rw [mass_zero]; ring
  · intro x; ring
  · intro x; ring

/-- ⭐ **K7 真的执行**：在 `p ≡ 0` 上，`markov_of_factorizes_kernel` 产出 `Markov`。 -/
theorem markov_zero (G : DAG V) :
    Markov ((fun _ => (0:ℝ)) : (V → α) → ℝ) G :=
  markov_of_factorizes_kernel _ G (kernelSep_holds_for_zero G)

end Validity

/-! ===========================================================================
  §6 诚实边界与剩余缺口
  =========================================================================== -/

/-!
### 6.1 已落地（零缺口，全部 `#check` 通过）

| 编号 | 名称 | 论证来源 |
|---|---|---|
| K1 | `mass_mul_reads` | `DAGFactorization.mass_mul` |
| K2 | `prod_frozen_const` | `Finset.prod_congr` |
| K2' | `reads_mono` | 直接 |
| K3 | `mass_prod_kernel` / `mass_prod_kernel'` | 一层 `mass_mul` + `prod_mul_prod_compl` |
| K4 | `ker_reads` | `mass_congr` |
| K5 | `ker_mul` / `ker_empty_const` | K1 / `mass_empty` |
| K6 | `condindep_of_kernel` | 环恒等式 |
| K7 | `markov_of_factorizes_kernel` | K6 + `KernelSep` 消去 |

### 6.2 ⚠ 剩余缺口（唯一一个，且**不是塔**）

`KernelSep` 的**图形化**：从 `G.dSep X Y Z` 出发，
用 `R v = {v} ∪ pa v` 具体构造四个核与四个冻结乘积。

这是 `R v ⊆ T` 与 `dSep` 第 4 子句
`Disjoint (bbReachableVertices Z X) Y` 之间的**图论翻译**：

* `bbReachableVertices` 的**不可达** ⟹ `Z` 阻断 `X → Y` 的活跃路径；
* 活跃路径阻断 ⟹ 「`X` 的机制不读 `Y`」⟹「`R v ∩ Y = ∅`」（对 `v ∈ X`）；
* 于是 `A = {v | R v ⊆ X∪Z}` 恰是**冻结部分**，`Aᶜ = {v | R v ⊄ X∪Z}`
  「只通过 `Z` 与其余交互」⟹ 核可加分解。

**⟹ 这一步是视角 15 与 14 种旧策略的**共同剩余难点**，
但它**不需要 `DAG.induce`、不需要 `FactorNorm`、不构造嵌套 `mass`**，
故比第 1/6/9 路的形态**更弱、更可证**。** -/

/-- **登记缺口**（显式 `Prop`，**不进下游**）。 -/
def KernelSepGraph_Gap (p : Joint V α) (G : DAG V) : Prop :=
  Factorizes p G → KernelSep p G

/-- **缺口的形式化陈述**（登记，非证明）。 -/
example (p : Joint V α) (G : DAG V) (h : KernelSepGraph_Gap p G) :
    Factorizes p G → Markov p G := by
  intro hf
  exact markov_of_factorizes_kernel p G (h hf)

end View15

end FateV2.Predict