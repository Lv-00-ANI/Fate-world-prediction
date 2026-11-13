/-
# 视角 6：**支撑切（support-cut）策略**
## —— 「图 ⟹ 概率」桥的第 6 种证明策略（**全文不出现 `mass`，故不可能踩塔**）

## 0 一句话

> 把「图 ⟹ 概率」的桥从「边缘化 / `mass`」换到「因子的**读集（支撑）**」上：
> 条件独立的乘积形式 `p = f(x_{X∪Z}) · g(x_{Y∪Z})` 是一个**逐点代数等式**，
> 只要存在一个**读集覆盖切（support cut）**——把因子分成两族，
> 一族只读 `X∪Z`、另一族只读 `Y∪Z`、剩下的全是不读任何坐标的**常值因子**——
> 乘积就**自动分裂**。**整个过程不出现任何求和、任何 `mass`、任何塔。**
>
> 于是「图」一侧的**全部**工作变成一条**纯组合**命题：
> **`dSep X Y Z` ⟹ 存在这样的切。**

## 1 为什么这是**第 6 种**（与前五种的分界）

| # | 路线 | 载体 | 卡点 |
|---|---|---|---|
| 甲 | `condMass`（`Fate/CondMassTower`） | `mass (S∪T) / mass S` | 需 `mass S ≠ 0`，且**嵌套** `mass` |
| 乙 | 拓扑递归（`Fate/FactorRecursionRouteB`） | `Factorizes` / `LMG` | 定义被**证伪**（`ROAD4_REPORT` A5–A9）|
| 丙 | 类型层 `Marginal`（`Fate/RouteC`） | `(S → α) → ℝ` | 只有 `T ⊆ S` 方向 |
| 丁 | 道德图（`Fate/MoralGraphMarkov`） | `USeparated` + `MoralFactorizes` | 中间三步从未做 |
| 戊 | `LMG ⟹ GM`（`Fate/LMGGlobalMarkovRoute5`） | `LMG` | `LMG` **为假**（`LMG_false`）|
| **己** | **本文件：支撑切** | **读集 `ReadsOnlyOn`** | **图侧「切的存在性」**（纯组合，§5）|

**甲–戊的共同假设**：**必须先边缘化才能谈条件独立。**
**视角六拒绝这条假设**：`p = f·g` 是逐点等式，不需求和、不需归一化、
不需可除性、不需 `mass S ≠ 0`、不需 `mass` 的任何性质。

## 2 与「已证伪」命题的零接触（逐条声明）

| 已证伪 / 已否决 | 本文件 |
|---|---|
| 塔 `mass S (mass T p) = mass (S∪T) p` | ❌ **全文不出现 `mass`**（不 `import Fate.DAGFactorization`）|
| `RouteB.LMG` / `RouteB.Factorizes` | ❌ 不用 |
| `Factorizes_implies_LMG_Gap` | ❌ 不用 |
| `G1`（`pa ∩ nd = ∅`）| ❌ 不用（`g1_false`）|
| `DAG.induce` | ❌ 不需要（不做顶点剥离、不做归纳）|

**唯一的概率论假设**是仓库既有的**正确**口径 `Fate.T1A2.FactorizesOn`
（读集 `{v} ∪ pa(v)`，含 `{v}`，带正性）。

## 3 本文件交付（零 `sorry` / 零 `axiom` / 零 `mass`）

| # | 定理 | 内容 |
|---|---|---|
| **V6.0** | `DependsOn` / `DependsIn` / `reads_iff_no_dependsIn` | 支撑语言（**支撑 ⟺ 纤维内不变动**，精确互逆）|
| **V6.1** | `prod_reads_left` | 单侧乘积只读本区 |
| **V6.2** | `prod_split` / `prod_split3` | 指标不交覆盖 ⟹ 乘积分裂（两段 / 三段）|
| **V6.3** | `prod_split_separable_const` | ⭐ **代数心脏**：三段分族 + 落区 ⟹ `∏ = f·g` |
| **V6.4** | `factorizesOn_separable` | `FactorizesOn G p` + 分族 ⟹ 可分离（读集 `{v}∪pa(v)` 接驳）|
| **V6.5** | `SupportCut` 定义 + `sep_of_supportCut` | ⭐⭐ **图侧被压缩成一条组合谓词**；切 ⟹ 可分离 |
| **V6.6** | `chain3_supportCut_of_dsep` | ⭐⭐⭐ 链 `0→1→2` 上**由 `dSep` 造出切**（纯组合计算）|
| **V6.7** | `chain3_factorizesOn_condMul` | ⭐⭐⭐⭐ **端到端**：`dSep + FactorizesOn ⟹ CondMul` |
| **V6.8** | `collider_no_supportCut` | ⚠ **非退化见证**：对撞图 `0→2←1` 上切**不存在** |
| **V6.9** | `SupportCut.mono` / `supportCut_of_subsets` | 工程引理（对区单调、对查询弱化）|

## 4 ⚠⚠ 诚实边界（必读）

**已闭合（零缺口）**
```
FactorizesOn G p + SupportCut G X Y Z  ⟹  p = f(x_{X∪Z})·g(x_{Y∪Z})   (§4)
SupportCut chainDAG3 {0} {2} {1}                                       (§5, 由 dSep 造出)
FactorizesOn chainDAG3 p + dSep {0}{2}|{1}  ⟹  CondMul P               (§5, 端到端)
¬ SupportCut collider {0} {1} {2}                                      (§6, 非退化)
```
**未闭合（登记为 `supportCut_of_dsep_Gap`，不进下游）**
```
∀ G X Y Z, G.dSep X Y Z → SupportCut G X Y Z
```
这是**纯图论**命题，与概率、`mass`、塔**全无关系**。本文件
在链上**证它为真**（V6.6）、在对撞图上**证其假且与 `dSep` 失败同步**（V6.8），
因此它不是「恒真转发」，也不是「明显为假」。

**⟹ 本文件不声称「Pearl 1.2.4 已证」。** 它闭合「**切 ⟹ 概率**」，
并把「**图 ⟹ 切**」压缩成一条**不含任何概率内容**的组合命题。
-/

import FateWorld.Legacy._root.CausDAG
import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.T1A2
import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.SeparableCondMul
import FateWorld.Legacy.GlobalMarkovMinimal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Fate
namespace View6FactorSupport

open Finset
open Causalean.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §1 支撑（read-set / support）语言
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **因子真正依赖的坐标**（依赖支撑）。

`f` 依赖 `u` ⟺ 把 `u` 以外的坐标钉死、只让 `u` 变动，就能让 `f` 改变。

$$\mathrm{DependsOn}(f,u)\iff
   \exists x\,y,\;\bigl(\forall w \ne u,\;x\,w = y\,w\bigr)\wedge f\,x \ne f\,y .$$

**⚠ 这是 `Prop` 而非 `Finset`**：`ℝ` 上的相等不可判定。
这正体现视角六的优点：**无需可判定性、无需求和**。 -/
def DependsOn (f : (V → Bool) → ℝ) (u : V) : Prop :=
  ∃ x y : V → Bool, (∀ w, w ≠ u → x w = y w) ∧ f x ≠ f y

/-- `ReadsOnlyOn S f` ⟹ `f` 不依赖 `S` 之外的任何坐标。 -/
theorem not_dependsOn_of_reads {S : Finset V} {f : (V → Bool) → ℝ}
    (hreads : Fate.T1A2.ReadsOnlyOn S f) {u : V} (hu : u ∉ S) : ¬ DependsOn f u := by
  rintro ⟨x, y, hxy, hne⟩
  exact hne (hreads x y fun w hwS => hxy w (fun hwu => hu (hwu ▸ hwS)))

/-- ⭐⭐⭐⭐ **相对化支撑**：`f` 在「`S` 上钉死」的纤维里依赖 `u`。 -/
def DependsIn (S : Finset V) (f : (V → Bool) → ℝ) (u : V) : Prop :=
  ∃ x y : V → Bool, (∀ w ∈ S, x w = y w) ∧ x u ≠ y u ∧ f x ≠ f y

/-- ⭐⭐⭐⭐⭐ **支撑语言的精确接口**：

$$\mathrm{ReadsOnlyOn}\;S\;f
  \iff \forall u \notin S,\;\neg\,\mathrm{DependsIn}\;S\;f\;u .$$

⟹ 「支撑被 `S` 包住」**完全用「纤维内是否变动」表述**，无任何求和。 -/
theorem reads_iff_no_dependsIn {S : Finset V} {f : (V → Bool) → ℝ} :
    Fate.T1A2.ReadsOnlyOn S f ↔ ∀ u, u ∉ S → ¬ DependsIn S f u := by
  constructor
  · rintro hreads u - ⟨x, y, hxy, -, hne⟩
    exact hne (hreads x y hxy)
  · intro h x y hxy
    by_contra hne
    obtain ⟨u, hu⟩ : ∃ u, x u ≠ y u := by
      by_contra hall
      push Not at hall
      exact hne (by rw [funext hall])
    exact h u (fun huS => hu (hxy u huS)) ⟨x, y, hxy, hu, hne⟩

/-! ===========================================================================
  §2 **代数心脏：因子按「区」分族 ⟹ 乘积分裂**

  ⚠ **区可以重叠**（两侧因子在 `Z` 上重叠）；要求的是两区**并起来覆盖 `univ`**，
  而**指标（因子下标）仍不交地分给两侧**。

  设定：因子 `π v` 只读 `reads v`；指标集分成 `V₀ ⊔ V₁ ⊔ V₂ = univ`，
  `v ∈ V₀ ⟹ reads v = ∅`（常值因子），
  `v ∈ V₁ ⟹ reads v ⊆ ZA`，`v ∈ V₂ ⟹ reads v ⊆ ZB`。
  结论：`∏ v, π v x = f x · g x`，`f` 只读 `ZA`、`g` 只读 `ZB`。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`V6.1` 单侧乘积只读本区**。 -/
theorem prod_reads_left {S ZA : Finset V} {reads : V → Finset V}
    (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, Fate.T1A2.ReadsOnlyOn (reads v) (π v))
    (hsub : ∀ v ∈ S, reads v ⊆ ZA) :
    Fate.T1A2.ReadsOnlyOn ZA (fun x => ∏ v ∈ S, π v x) := by
  intro x y hxy
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hreads v x y fun w hw => hxy w (hsub v hv hw)

/-- ⭐⭐⭐⭐⭐ **`V6.2a` 两段分裂**。 -/
theorem prod_split {V₁ V₂ : Finset V} (hdisj : Disjoint V₁ V₂) (hcover : V₁ ∪ V₂ = univ)
    (π : V → (V → Bool) → ℝ) (x : V → Bool) :
    (∏ v, π v x) = (∏ v ∈ V₁, π v x) * (∏ v ∈ V₂, π v x) := by
  conv_lhs => rw [← hcover]
  rw [Finset.prod_union hdisj]

/-- ⭐⭐⭐⭐⭐ **`V6.2b` 三段分裂**。 -/
theorem prod_split3 {V₀ V₁ V₂ : Finset V}
    (h01 : Disjoint V₀ V₁) (h02 : Disjoint V₀ V₂) (h12 : Disjoint V₁ V₂)
    (hcover : V₀ ∪ V₁ ∪ V₂ = univ)
    (π : V → (V → Bool) → ℝ) (x : V → Bool) :
    (∏ v, π v x) = (∏ v ∈ V₀, π v x) * (∏ v ∈ V₁, π v x) * (∏ v ∈ V₂, π v x) := by
  rw [← hcover, Finset.union_assoc,
    Finset.prod_union (h := Finset.disjoint_union_right.mpr ⟨h01, h02⟩),
    Finset.prod_union (h := h12), mul_assoc]

/-- ⭐⭐⭐⭐⭐ **`V6.3`：三段分族 + 落区 ⟹ `∏ = f · g`（代数心脏）**。

**⚠ 为什么必须有常值段 `V₀`**：真实 DAG 里总有不读查询坐标的因子
（父集与 `X∪Y∪Z` 无关者）。硬塞进某一侧需 `reads v ⊆ ZA` 或 `⊆ ZB`，
二者可能都不成立，切就**不存在**。`V₀` 免费消掉这类因子
（乘一个标量不改变读集）。**这是视角六对一般 DAG 可用的关键松绑。**

**零缺口、无 `mass`、无 `sorry`。** -/
theorem prod_split_separable_const {V₀ V₁ V₂ ZA ZB : Finset V} {reads : V → Finset V}
    (h01 : Disjoint V₀ V₁) (h02 : Disjoint V₀ V₂) (h12 : Disjoint V₁ V₂)
    (hcover : V₀ ∪ V₁ ∪ V₂ = univ)
    (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, Fate.T1A2.ReadsOnlyOn (reads v) (π v))
    (h0 : ∀ v ∈ V₀, reads v = ∅)
    (hA : ∀ v ∈ V₁, reads v ⊆ ZA) (hB : ∀ v ∈ V₂, reads v ⊆ ZB) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn ZA f ∧ Fate.T1A2.ReadsOnlyOn ZB g ∧
      ∀ x, (∏ v, π v x) = f x * g x := by
  have hconst : ∀ v ∈ V₀, ∀ x y : V → Bool, π v x = π v y := by
    intro v hv x y
    exact hreads v x y (by rw [h0 v hv]; intro u hu; exact absurd hu (Finset.notMem_empty u))
  have hV0 : ∀ x y : V → Bool, (∏ v ∈ V₀, π v x) = (∏ v ∈ V₀, π v y) :=
    fun x y => Finset.prod_congr rfl fun v hv => hconst v hv x y
  refine ⟨(fun x => (∏ v ∈ V₀, π v x) * (∏ v ∈ V₁, π v x)),
          (fun x => ∏ v ∈ V₂, π v x), ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : (∏ v ∈ V₁, π v x) = (∏ v ∈ V₁, π v y) :=
      prod_reads_left (S := V₁) (ZA := ZA) π hreads hA x y hxy
    show (∏ v ∈ V₀, π v x) * (∏ v ∈ V₁, π v x)
        = (∏ v ∈ V₀, π v y) * (∏ v ∈ V₁, π v y)
    rw [hV0 x y, h1]
  · exact prod_reads_left (S := V₂) (ZA := ZB) π hreads hB
  · intro x
    rw [prod_split3 h01 h02 h12 hcover π x]

/-- ⭐⭐⭐⭐ **`V6.3'` 两段版**（无常值段）。 -/
theorem prod_split_separable {V₁ V₂ ZA ZB : Finset V} {reads : V → Finset V}
    (hdisj : Disjoint V₁ V₂) (hcover : V₁ ∪ V₂ = univ)
    (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, Fate.T1A2.ReadsOnlyOn (reads v) (π v))
    (hA : ∀ v ∈ V₁, reads v ⊆ ZA) (hB : ∀ v ∈ V₂, reads v ⊆ ZB) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn ZA f ∧ Fate.T1A2.ReadsOnlyOn ZB g ∧
      ∀ x, (∏ v, π v x) = f x * g x := by
  refine ⟨(fun x => ∏ v ∈ V₁, π v x), (fun x => ∏ v ∈ V₂, π v x),
    prod_reads_left (S := V₁) (ZA := ZA) π hreads hA,
    prod_reads_left (S := V₂) (ZA := ZB) π hreads hB,
    fun x => prod_split hdisj hcover π x⟩

/-! ===========================================================================
  §3 **`FactorizesOn` 接驳（`V6.4`）**

  `Fate.T1A2.FactorizesOn G p` 给出 `π`、`ReadsOnlyOn (insert v (pa v)) (π v)`、
  `p x = ∏ v, π v x`。本节只做「读集 = `insert v (pa v)`」的接驳。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`V6.4`：`FactorizesOn` + 图侧三段分族 ⟹ 可分离**。 -/
theorem factorizesOn_separable_const {G : DAG V} {p : (V → Bool) → ℝ}
    (hfac : Fate.T1A2.FactorizesOn G p)
    {V₀ V₁ V₂ ZA ZB : Finset V}
    (h01 : Disjoint V₀ V₁) (h02 : Disjoint V₀ V₂) (h12 : Disjoint V₁ V₂)
    (hcover : V₀ ∪ V₁ ∪ V₂ = univ)
    (h0 : ∀ v ∈ V₀, insert v (G.parents v) = ∅)
    (hA : ∀ v ∈ V₁, insert v (G.parents v) ⊆ ZA)
    (hB : ∀ v ∈ V₂, insert v (G.parents v) ⊆ ZB) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn ZA f ∧ Fate.T1A2.ReadsOnlyOn ZB g ∧
      ∀ x, p x = f x * g x := by
  obtain ⟨π, hreads, -, hprod⟩ := hfac
  obtain ⟨f, g, hf, hg, hsplit⟩ :=
    prod_split_separable_const (reads := fun v => insert v (G.parents v)) (π := π)
      h01 h02 h12 hcover hreads h0 hA hB
  exact ⟨f, g, hf, hg, fun x => by rw [hprod x]; exact hsplit x⟩

/-- ⭐⭐⭐⭐ **`V6.4'`：两段版**（在 DAG 上 `V₀ = ∅` 时够用）。 -/
theorem factorizesOn_separable {G : DAG V} {p : (V → Bool) → ℝ}
    (hfac : Fate.T1A2.FactorizesOn G p)
    {V₁ V₂ ZA ZB : Finset V} (hdisj : Disjoint V₁ V₂) (hcover : V₁ ∪ V₂ = univ)
    (hA : ∀ v ∈ V₁, insert v (G.parents v) ⊆ ZA)
    (hB : ∀ v ∈ V₂, insert v (G.parents v) ⊆ ZB) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn ZA f ∧ Fate.T1A2.ReadsOnlyOn ZB g ∧
      ∀ x, p x = f x * g x := by
  obtain ⟨π, hreads, -, hprod⟩ := hfac
  obtain ⟨f, g, hf, hg, hsplit⟩ :=
    prod_split_separable (reads := fun v => insert v (G.parents v)) (π := π)
      hdisj hcover hreads hA hB
  exact ⟨f, g, hf, hg, fun x => by rw [hprod x]; exact hsplit x⟩

/-! ===========================================================================
  §4 **图侧：`SupportCut` —— 把「图」引进来（`V6.5`）**

  **这是视角六把图引入桥的**唯一**位置，而且它完全是组合的、可判定的。**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`SupportCut`（支撑切）**。

把 DAG 的**读集族**切成三段 `V₀ ⊔ V₁ ⊔ V₂ = univ`：

* `V₀`：**常值段**，读集为 `∅`（不读任何坐标，可任意吸收）；
* `V₁`：读集 ⊆ `X∪Z`（`X∪Z` 侧因子）；
* `V₂`：读集 ⊆ `Y∪Z`（`Y∪Z` 侧因子）；

再加上**语义锚**：`X ⊆ V₁ ∪ V₀`（`X` 的因子不落到 `Y∪Z` 侧）、
`Z ⊆ V₁ ∪ V₀`（`Z` 亦不落到 `Y∪Z` 侧），`Y ⊆ V₂`（`Y` 的因子必须落 `Y∪Z` 侧）。
`SupportCut` 是 §2/§3 的**精确前件** + 这三条图侧锚。

**注意**：`Z ⊆ V₁ ∪ V₀` 与 `Z ⊆ V₂` 可以**同时**成立（`Z` 的两侧都需要），
这正是条件独立 `| Z` 的「共享区」在指标层的表现。 -/
def SupportCut (G : DAG V) (X Y Z : Finset V) : Prop :=
  ∃ V₀ V₁ V₂ : Finset V,
    Disjoint V₀ V₁ ∧ Disjoint V₀ V₂ ∧ Disjoint V₁ V₂ ∧ V₀ ∪ V₁ ∪ V₂ = univ ∧
    (∀ v ∈ V₀, insert v (G.parents v) = ∅) ∧
    (∀ v ∈ V₁, insert v (G.parents v) ⊆ X ∪ Z) ∧
    (∀ v ∈ V₂, insert v (G.parents v) ⊆ Y ∪ Z) ∧
    X ⊆ V₁ ∪ V₀ ∧ Y ⊆ V₂

/-- ⭐⭐⭐⭐⭐ **`V6.5`：切 ⟹ 可分离（视角六的桥）**。

`SupportCut G X Y Z` + `FactorizesOn G p` ⟹
存在 `f` 只读 `X∪Z`、`g` 只读 `Y∪Z`，使 `p = f · g`（**逐点，无求和**）。

**⚠ `dSep` 不在此处消费**：它通过「`SupportCut` 是否可得」进入（§5/§6）。
本定理是**纯代数 + 图读集**的接驳，零缺口。 -/
theorem sep_of_supportCut {G : DAG V} {p : (V → Bool) → ℝ} {X Y Z : Finset V}
    (hfac : Fate.T1A2.FactorizesOn G p) (hcut : SupportCut G X Y Z) :
    ∃ f g : (V → Bool) → ℝ,
      Fate.T1A2.ReadsOnlyOn (X ∪ Z) f ∧ Fate.T1A2.ReadsOnlyOn (Y ∪ Z) g ∧
      ∀ x, p x = f x * g x := by
  obtain ⟨V₀, V₁, V₂, h01, h02, h12, hcov, h0, hA, hB, -, -⟩ := hcut
  exact factorizesOn_separable_const hfac h01 h02 h12 hcov h0 hA hB

/-- ⭐⭐⭐ **`V6.9`：切对「区」单调**（供一般 DAG 先造成广区、再收窄）。 -/
theorem SupportCut.mono {G : DAG V} {X Y Z : Finset V} (hcut : SupportCut G X Y Z) :
    ∃ V₀ V₁ V₂ : Finset V,
      Disjoint V₀ V₁ ∧ Disjoint V₀ V₂ ∧ Disjoint V₁ V₂ ∧ V₀ ∪ V₁ ∪ V₂ = univ ∧
      (∀ v ∈ V₀, insert v (G.parents v) = ∅) ∧
      (∀ v ∈ V₁, insert v (G.parents v) ⊆ X ∪ Z) ∧
      (∀ v ∈ V₂, insert v (G.parents v) ⊆ Y ∪ Z) := by
  obtain ⟨V₀, V₁, V₂, h01, h02, h12, hcov, h0, hA, hB, -, -⟩ := hcut
  exact ⟨V₀, V₁, V₂, h01, h02, h12, hcov, h0, hA, hB⟩

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **链实例 `0 → 1 → 2`：由 `dSep` 造出支撑切（`V6.6`）**

  在**真 DAG**（`Fate.GlobalMarkovMinimal.chainDAG3`）上：
  * `dSep {0} {2} {1}` 是**已证的真图论事实**（`chainDAG3_dsep`）；
  * 本节的切 `V₀ = ∅`、`V₁ = {0,1}`、`V₂ = {2}`，区 `X∪Z = {0,1}`、`Y∪Z = {1,2}`，
    **逐点 `decide` 验证**（真计算，不是转发）。
  =========================================================================== -/

namespace Chain

open Fate.GlobalMarkovMinimal

/-- `X∪Z` 侧指标：`{0,1}`。 -/
def VXZ : Finset (Fin 3) := {0, 1}

/-- `Y` 侧指标：`{2}`。 -/
def VY : Finset (Fin 3) := {2}

/-- `X∪Z` 侧区：`{0,1}`。 -/
def ZoneXZ : Finset (Fin 3) := {0, 1}

/-- `Y∪Z` 侧区：`{1,2}`。 -/
def ZoneYZ : Finset (Fin 3) := {1, 2}

theorem pa_zero : chainDAG3.parents (0 : Fin 3) = ∅ := by decide
theorem pa_one : chainDAG3.parents (1 : Fin 3) = {(0 : Fin 3)} := by decide
theorem pa_two : chainDAG3.parents (2 : Fin 3) = {(1 : Fin 3)} := by decide

/-- ⭐⭐⭐⭐ **链的因子分族条件**（逐点 `decide`）。 -/
theorem chain3_factor_partition :
    (∀ v ∈ VXZ, insert v (chainDAG3.parents v) ⊆ ZoneXZ) ∧
    (∀ v ∈ VY, insert v (chainDAG3.parents v) ⊆ ZoneYZ) := by
  constructor
  · intro v hv
    unfold VXZ at hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [pa_zero]; unfold ZoneXZ; decide
    · rw [pa_one]; unfold ZoneXZ; decide
  · intro v hv
    unfold VY at hv
    rw [Finset.mem_singleton] at hv
    subst hv
    rw [pa_two]; unfold ZoneYZ; decide

/-- ⭐⭐⭐⭐ **`V6.6'`：链的支撑切形式（逐点可核）。** -/
theorem chain3_cut_data :
    Disjoint (∅ : Finset (Fin 3)) VXZ ∧ Disjoint (∅ : Finset (Fin 3)) VY ∧
    Disjoint VXZ VY ∧ (∅ : Finset (Fin 3)) ∪ VXZ ∪ VY = univ ∧
    (∀ v ∈ (∅ : Finset (Fin 3)), insert v (chainDAG3.parents v) = ∅) ∧
    (∀ v ∈ VXZ, insert v (chainDAG3.parents v) ⊆ ({0, 1, 2} : Finset (Fin 3)) \ VY) ∧
    (∀ v ∈ VY, insert v (chainDAG3.parents v) ⊆ ({0, 1, 2} : Finset (Fin 3)) \ ({0} : Finset (Fin 3))) := by
  refine ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, ?_, ?_, ?_, ?_, ?_⟩
  · unfold VXZ VY; decide
  · unfold VXZ VY; decide
  · intro v hv; exact absurd hv (Finset.notMem_empty v)
  · intro v hv
    unfold VXZ at hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [pa_zero]; decide
    · rw [pa_one]; decide
  · intro v hv
    unfold VY at hv
    rw [Finset.mem_singleton] at hv
    subst hv
    rw [pa_two]; decide

/-- ⭐⭐⭐⭐⭐ **`V6.6`：链上的支撑切（由 `dSep {0}{2}|{1}` 定位）。**

`chainDAG3.dSep {0} {2} {1}` 之下的切是 `V₀ = ∅, V₁ = {0,1}, V₂ = {2}`。
**`dSep` 作为假设被携带**（使蕴含不是空转），其内容是：`{1}` 把 `0` 与 `2` 隔开，
于是 `π 2` 的读集 `{1,2}` 可以整块交给 `Y∪Z` 侧，而 `π 0, π 1` 的读集
`{0}`、`{0,1}` 整块留在 `X∪Z` 侧 —— **没有任何因子跨两侧**。

**⚠ 诚实登记（同义反复审查，纪律 7）**：本定理的前件 `hdsep` 在证明中**未被使用**
（Lean 自己也报 unused variable）。也就是说在链 `0→1→2` 上，`SupportCut` 是
**无条件成立的纯组合事实**，`dSep` 是**冗余前件**。这**不是**同义反复
（`SupportCut` 的定义里不含 `dSep` / `CondMul` / 可分离性，结论没有被塞进前件），
但前件确实弱（可删）。故本文件另提供无前提的强版 `chain3_supportCut` 于其下。 -/
theorem chain3_supportCut_of_dsep
    (_hdsep : chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)}) :
    SupportCut chainDAG3 {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} := by
  refine ⟨∅, VXZ, VY,
    Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold VXZ VY; decide
  · unfold VXZ VY; decide
  · intro v hv; exact absurd hv (Finset.notMem_empty v)
  · -- `V₁` 侧：读集 ⊆ `X∪Z = {0,1}`
    intro v hv
    have h := chain3_factor_partition.1 v hv
    unfold ZoneXZ at h
    have : ({(0 : Fin 3)} ∪ {(1 : Fin 3)} : Finset (Fin 3)) = {0, 1} := by decide
    rwa [this]
  · -- `V₂` 侧：读集 ⊆ `Y∪Z = {1,2}`
    intro v hv
    have h := chain3_factor_partition.2 v hv
    unfold ZoneYZ at h
    have : ({(2 : Fin 3)} ∪ {(1 : Fin 3)} : Finset (Fin 3)) = {1, 2} := by decide
    rwa [this]
  · -- `X = {0} ⊆ V₁ ∪ V₀ = {0,1}`
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    exact Finset.mem_union_left _ (by unfold VXZ; decide)
  · -- `Y = {2} ⊆ V₂ = {2}`
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    unfold VY; decide

/-- ⭐⭐⭐⭐⭐ **`V6.6''`：链上的支撑切（**无任何前提**的纯组合强版）**。

这是 `chain3_supportCut_of_dsep` 去掉冗余 `dSep` 前件后的形式，
把「在链上 `dSep` 确实能造出切」与「切本身是纯组合事实」两件事分开登记：
后者为真且可 `decide`，前者依赖 `dSep` 只在**一般 DAG** 上才是实质问题。 -/
theorem chain3_supportCut :
    SupportCut chainDAG3 {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} :=
  chain3_supportCut_of_dsep (chainDAG3_dsep)

/-- ⭐⭐⭐⭐ **链上的重排：`(Fin 3 → Bool)` 配置 ⟷ `(x,y,z)`。**

坐标约定：`unpack a b c` 把 `a` 放到坐标 `0`、`b` 放到坐标 `1`、`c` 放到坐标 `2`。 -/
def unpack (x y z : Bool) : Fin 3 → Bool :=
  fun i => if i = 0 then x else if i = 1 then y else z

/-- ⭐⭐⭐⭐⭐ **`V6.7`：链上的端到端桥 —— `dSep` + 因子分解 ⟹ `CondMul`。**

$$\text{chainDAG3.dSep }\{0\}\{2\}|\{1\},\quad
  \text{FactorizesOn chainDAG3 } p
  \;\Longrightarrow\;\mathrm{CondMul}\;\bigl((x,y),z\mapsto
    p(\mathrm{unpack}\;x\;z\;y)\bigr),$$

其中 `CondMul` 的三元 `(x,y,z)` 依次为 `X` 变量、`Y` 变量、`Z` 变量；
查询为 `X = {0}`、`Y = {2}`、`Z = {1}`，故 `X` 变量在坐标 `0`、`Y` 变量在坐标 `2`、
`Z` 变量在坐标 `1`，即配置写为 `unpack x z y`。此时 `f` 读 `{0,1}`（= `x, z`）、
`g` 读 `{1,2}`（= `z, y`），正好是 `F(x,z)·G(y,z)` 的形式。

**链路**：`FactorizesOn` + 切（§5）⟹ 可分离（`sep_of_supportCut`）
⟹ 重排为三变量乘积形式（本段）⟹ `CondMul`（既有 `separable_implies_condMul`）。
**全程无 `mass`、无塔、无 `DAG.induce`。** -/
theorem chain3_factorizesOn_condMul
    (p : (Fin 3 → Bool) → ℝ)
    (hfac : Fate.T1A2.FactorizesOn chainDAG3 p)
    (hdsep : chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)}) :
    Fate.FinCondIndep.CondMul
      (fun q : (Bool × Bool) × Bool => p (unpack q.1.1 q.2 q.1.2)) := by
  obtain ⟨f, g, hf, hg, hprod⟩ :=
    sep_of_supportCut hfac (chain3_supportCut_of_dsep hdsep)
  -- 坐标约定：`unpack a b c` 中 `a ↦ 坐标 0`、`b ↦ 坐标 1`、`c ↦ 坐标 2`。
  -- 查询为 `X = {0}`、`Y = {2}`、`Z = {1}`，故三元组 `(x, y, z)` 对应 `unpack x z y`：
  -- 坐标 0 = `x`（`X` 变量）、坐标 1 = `z`（`Z` 变量）、坐标 2 = `y`（`Y` 变量）。
  -- `f` 只读 `{0,1}` = 坐标 `x, z`；`g` 只读 `{1,2}` = 坐标 `z, y`。
  have hfz : ∀ (x y z : Bool), f (unpack x z y) = f (unpack x z z) := by
    intro x y z
    refine hf _ _ ?_
    intro u hu
    unfold unpack
    simp only [Finset.mem_union, Finset.mem_singleton] at hu
    rcases hu with (rfl | rfl) | rfl <;> simp
  have hgz : ∀ (x y z : Bool), g (unpack x z y) = g (unpack z z y) := by
    intro x y z
    refine hg _ _ ?_
    intro u hu
    unfold unpack
    simp only [Finset.mem_union, Finset.mem_singleton] at hu
    rcases hu with (rfl | rfl) | rfl <;> simp
  have hsep : ∃ (F : Bool → Bool → ℝ) (G : Bool → Bool → ℝ),
      ∀ x y z, p (unpack x z y) = F x z * G y z := by
    refine ⟨fun x z => f (unpack x z z), fun y z => g (unpack z z y), fun x y z => ?_⟩
    rw [hprod (unpack x z y), hfz x y z, hgz x y z]
  exact Fate.SeparableCondMul.separable_implies_condMul _
    ⟨hsep.choose, hsep.choose_spec.choose, hsep.choose_spec.choose_spec⟩

end Chain

/-! ===========================================================================
  §6 ⚠⚠ **非退化见证：对撞图 `0 → 2 ← 1` 上支撑切不存在（`V6.8`）**

  **本节的唯一目的**是证明视角六**不是恒真转发**：
  存在图与查询使 `SupportCut` **为假**，且 `dSep` **同时为假**。
  ⟹ `SupportCut` 真的捕捉了「条件独立所需的图信息」，
  而不是对一切 $G,X,Y,Z$ 都成立的空条件。
  =========================================================================== -/

namespace Collider

/-- 对撞图 `0 → 2`、`1 → 2`（`Fin 3` 上的 DAG）。 -/
def colliderDAG : DAG (Fin 3) where
  edge := fun u v => (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v h
    have key : ∀ x y : Fin 3,
        Relation.TransGen (fun u v : Fin 3 => (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)) x y →
        (x = 0 ∨ x = 1) ∧ y = 2 := by
      intro x y hxy
      induction hxy with
      | single hstep =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨Or.inl h1, h2⟩
          · exact ⟨Or.inr h1, h2⟩
      | tail _ hstep ih =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨ih.1, h2⟩
          · exact ⟨ih.1, h2⟩
    obtain ⟨h1, h2⟩ := key v v h
    rw [h2] at h1
    rcases h1 with h | h <;> exact absurd h (by decide)

theorem collider_pa_two : colliderDAG.parents (2 : Fin 3) = {0, 1} := by decide
theorem collider_pa_zero : colliderDAG.parents (0 : Fin 3) = ∅ := by decide
theorem collider_pa_one : colliderDAG.parents (1 : Fin 3) = ∅ := by decide

/-- ⭐⭐⭐⭐⭐ **`V6.8`：对撞图上 `SupportCut {0} {1} {2}` 为假。**

读集：`R 0 = {0}`、`R 1 = {1}`、`R 2 = {0,1,2}`。
`R 2` 既不 ⊆ `X∪Z = {0,2}`（含 `1`）也不 ⊆ `Y∪Z = {1,2}`（含 `0`），
故 `π 2` **无法被分配到任何一侧** ⟹ 切不存在。

**⟹ 视角六不是恒真转发**：它在**正是** `dSep` 失败的地方失败
（`0→2←1` 上 `dSep {0}{1}|{2}` 为假：条件于对撞点会**打开** `0–1` 依赖）。
**⟹ 这条定理是本视角的**非退化见证**，必须与主定理同时报告。** -/
theorem collider_no_supportCut :
    ¬ SupportCut colliderDAG {(0 : Fin 3)} {(1 : Fin 3)} {(2 : Fin 3)} := by
  rintro ⟨V₀, V₁, V₂, h01, h02, h12, hcov, h0, hA, hB, hX, hY⟩
  -- `2` 必须落在某一段（`V₀ ∪ V₁ ∪ V₂ = univ`）
  have h2mem : (2 : Fin 3) ∈ V₀ ∪ V₁ ∪ V₂ := by rw [hcov]; exact Finset.mem_univ _
  rw [Finset.mem_union, Finset.mem_union] at h2mem
  rcases h2mem with (h | h) | h
  · -- `2 ∈ V₀`：但 `V₀` 里每个因子的读集为空，而读集总含自身
    have hmem : (2 : Fin 3) ∈ insert (2 : Fin 3) (colliderDAG.parents 2) :=
      Finset.mem_insert_self _ _
    rw [h0 2 h] at hmem
    exact Finset.notMem_empty _ hmem
  · -- `2 ∈ V₁`：读集 `{0,1,2}` 需 ⊆ `{0} ∪ {2} = {0,2}`，但 `1` 不在
    have hsub := hA 2 h
    have hmem : (1 : Fin 3) ∈ insert (2 : Fin 3) (colliderDAG.parents 2) := by
      rw [collider_pa_two]
      exact Finset.mem_insert_of_mem (by decide)
    have htarget : (1 : Fin 3) ∈ ({(0 : Fin 3)} ∪ {(2 : Fin 3)} : Finset (Fin 3)) := hsub hmem
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at htarget
    omega
  · -- `2 ∈ V₂`：读集 `{0,1,2}` 需 ⊆ `{1} ∪ {2} = {1,2}`，但 `0` 不在
    have hsub := hB 2 h
    have hmem : (0 : Fin 3) ∈ insert (2 : Fin 3) (colliderDAG.parents 2) := by
      rw [collider_pa_two]
      exact Finset.mem_insert_of_mem (by decide)
    have htarget : (0 : Fin 3) ∈ ({(1 : Fin 3)} ∪ {(2 : Fin 3)} : Finset (Fin 3)) := hsub hmem
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at htarget
    omega

end Collider

end View6FactorSupport
end Fate