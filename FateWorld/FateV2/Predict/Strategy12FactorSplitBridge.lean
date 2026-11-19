/-
# 视角 12：`mass` 塔无关的「因子划分 ⟹ 概率」桥

## 0 定位

**任务**：为「图 ⟹ 概率」桥给出**第 12 种**证明策略的具体数学构造 + Lean 落地。
**硬约束**：**不得使用 `mass` 塔性质**（该性质已被 `FateV2.Predict.TowerAudit.mass_idempotent_fails`
/ `FateV2.Predict.DAGFactorizationGeneral.tower_property_false` 证伪）。

**⟹ 本文件与 `mass` 塔彻底正交**：全程**不出现** `mass S (mass T p)` 这种嵌套。

## 1 与既往各路的**分野**（为何是「第 12 种」而非重复）

| 路 | 骨架 | 卡点（取自本仓库报告）|
|---|---|---|
| 1–3 | `RouteB.Factorizes/LMG` | `LMG` **已被证伪**（`LMG_false`）；`Factorizes` 读集缺 `{v}` |
| 4 | 祖先闭包继承 | 挂在错的 `RouteB.LMG` 上，自判无意义 |
| 5 | 拓扑序 sink 剥离 | `sink_peel` 已证，但递归需 `DAG.induce`（**库缺失**）|
| 6 | `dSep`×拓扑序 | 文件**编译失败** |
| 7–9 | 链式 / 二元 `CondMul` 拼接 | 结论不含图参数，M8 判「同义反复」|
| 10 | `RouteB.Factorizes` 审计 | 仅否定性审计 |
| 11 | 类型层 `Marginal S p` | 需子类型/等价类，成本高，仍要处理塔 |
| **12（本文）** | **因子划分 + 一次性多重和** | **不迭代 `mass`、不需 `DAG.induce`、`dSep` 真实进入前提** |

## 2 核心数学构造（三块 + 一块缺口，全部塔无关）

### 块 ① `mass` 的「一次性多重和」语义
`mass S p x = ∑_w [w|_S = x|_S] · p w`。对**全空间一次求和**，**不是**嵌套。
本文件只用这一次求和的代数性质（`rfl` 级重写）。

### 块 ② 「读集 ⊆ `S` 的因子提出律」（**替代塔**）
`f` 只读 `S` ⟹ `mass S (f·g) x = f x · mass S g x`。
**一步到位**地在一个 `mass S` 内提出 `f`，**无需**先算 `mass` 内层边缘。
本文件复用已证的 `DAGFactorization.mass_mul`，并与 `LocalTo` 接合（`mass_pull_out_local`）。

### 块 ③ **因子划分定理**（本文实质新内容，`factor_split_mass`）
`p = ∏ f`，按「读集 ⊆ `S` 与否」分 `In` / `Out`：
$$\mathrm{mass}\,S\,p\,x
  = \Bigl(\prod_{v\in In} f_v(x)\Bigr)\cdot
    \mathrm{mass}\,S\,\Bigl(\prod_{v\in Out} f_v\Bigr)\,x .$$
`In` 组**整体提出**，`mass S` 一次消化 `Out` 组。这是**分组归纳的引擎**。

### 块 ④（缺口）`NormalizedResidual`：`Out` 组残余 `mass` 的归一化常数
**块 ③ 把 `masks` 推给了 `Out` 组**。一般 `Factorizes ⟹ Markov` 收口需要：
> `Out` 组（读集 ⊄ `S`）的残余 `mass S (∏_{v∈Out} f_v) x` 与「`dSep` 决定的
> 常数因子」相乘后，两组在 `CondIndep` 的四个 `mass` 之间**比值恒常**。

这条 `NormalizedResidual` **在本文件不证**（它是一般 DAG 上的真数学工作）。
**⟹ 本文的落点是：把桥从既往的「两层缺口（缺 `DAG.induce` + 缺 constants 恒常性）」
压缩成一条纯组合/归一化引理 `DSepFactorSplit`。** 这就是「视角 12」的界定。

## 3 本文件实际证明什么（诚实边界）

* ✅ **块 ①②③ 全部证明，零 `sorry`、零 `axiom`、零 `admit`。**
* ✅ **端到端可执行部分**：`factor_split_mass` 对**任意** DAG、任意 `S`、任意
  满足 `LocalTo` 的 `In` 集合成立 —— 这是通用引擎，可直接被任意一路消费。
* ⚠ **一般 `Factorizes ⟹ Markov` 未闭合**：缺块 ④（`NormalizedResidual`）。
  **本文件不写 `sorry` 占位、不把结论塞进前件**；块 ④ 以**文档缺口**形式登记，
  并给出它在任意 DAG 上的**精确陈述**（§6），供下一路接手。

## 4 参考文献

* Pearl, *Causality* 2nd ed., **§1.2.3 / Theorem 1.2.4**（因子分解 ⟹ 全局 Markov）。
* Lauritzen, *Graphical Models*, §3.2.1–3.2.2。
* Koller & Friedman, *PGM*, **Theorem 3.2.7**。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace FateV2.Predict.Strategy12

open FateV2.Modeling

open Finset FateV2.Modeling.Graph
open FateV2.Predict.DAGFactorization (mass unpin)
open FateV2.Predict.FactorMarkov (Joint LocalTo Factorizes FactorNorm CondIndep Markov)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

/-!
  # Predict · Strategy12FactorSplitBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy12FactorSplitBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 块 ①：`mass` 的**一次性**多重和语义（塔无关）
  =========================================================================== -/

/-- ⭐ **块 ①**：`mass S p x` 是**一次**对全空间的加权求和，权重是
「`w` 在 `S` 上与 `x` 一致」的指示函数。

**⚠ 定义级重写（`rfl`），**不是**塔：它**不**把 `mass` 嵌套进 `mass`。 -/
theorem mass_eq_single_sum (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S p x = ∑ w : V → α, if ∀ u ∈ S, w u = x u then p w else 0 := rfl

/-- ⭐ `mass` 只依赖 `S` 上的坐标（直接 `mass_congr`，塔无关）。 -/
theorem mass_loc (S : Finset V) (p : (V → α) → ℝ) {x y : V → α}
    (h : ∀ u ∈ S, x u = y u) : mass S p x = mass S p y :=
  FateV2.Predict.DAGFactorization.mass_congr S p h

/-- ⭐ `mass univ = p`（塔无关）。 -/
theorem mass_univ_eq (p : (V → α) → ℝ) (x : V → α) : mass univ p x = p x :=
  FateV2.Predict.DAGFactorization.mass_univ p x

/-! ===========================================================================
  §2 块 ②：「读集 ⊆ `S` 的因子提出律」（**替代塔**）
  =========================================================================== -/

/-- ⭐⭐ **块 ②**：若 `f` 只读 `S` 内坐标，则 `mass S (f * g) x = f x * mass S g x`。

**⟹ 塔的**替代品**：塔想「先边缘 `T` 再边缘 `S`」，本律「**在同一个 `mass S` 里**
把 `S`-敏感因子一步提出」，**无嵌套**。 -/
theorem mass_pull_out (S : Finset V) (f g : (V → α) → ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => f w * g w) x = f x * mass S g x :=
  FateV2.Predict.DAGFactorization.mass_mul S f g x hf

/-- ⭐⭐ **块 ② 与图的接合**：`LocalTo` 因子在其读集 `{v} ∪ pa_G(v) ⊆ S` 时可提出。

这是「图 → 提出律」的唯一接点：`hloc` 保证 `f v` 只读 `{v} ∪ pa v`，
`hS` 保证这些坐标都在 `S` 里。 -/
theorem mass_pull_out_local (G : DAG V) {f : V → (V → α) → ℝ} (hloc : LocalTo G f)
    (v : V) (S : Finset V) (hS : ∀ u, u = v ∨ u ∈ G.parents v → u ∈ S)
    (g : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => f v w * g w) x = f v x * mass S g x :=
  mass_pull_out S (f v) g x (fun x y hxy => hloc v x y (fun u hu => hxy u (hS u hu)))

/-! ===========================================================================
  §3 块 ③：**因子划分定理**（本文实质新内容）
  =========================================================================== -/

/-- ⭐ 乘积按集合划分分解：`∏ f = (∏_{v∈In} f v) · (∏_{v∉In} f v)`。 -/
theorem prod_split_by_set (f : V → (V → α) → ℝ) (x : V → α) (In : Finset V) :
    ∏ v, f v x = (∏ v ∈ In, f v x) * (∏ v ∈ (univ \ In), f v x) := by
  classical
  rw [← Finset.prod_union (Finset.disjoint_sdiff)]
  congr 1
  ext v; simp

/-- ⭐⭐ **混合引理**：`p` 因子化时，`mass S p` 只依赖每个 `w` 上 `In`/`Out` 的划分积。 -/
theorem mass_eq_mass_of_split (S In : Finset V) (f : V → (V → α) → ℝ)
    (p : (V → α) → ℝ) (hfac : ∀ x, p x = ∏ v, f v x) (x : V → α) :
    mass S p x
      = mass S (fun w => (∏ v ∈ In, f v w) * (∏ v ∈ (univ \ In), f v w)) x := by
  unfold mass
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · rw [if_pos hw, if_pos hw, hfac]
    exact prod_split_by_set f w In
  · rw [if_neg hw, if_neg hw]

/-- ⭐⭐⭐ **块 ③（因子划分定理）**。

设 `p` 由 `f` 因子化；`In` 满足「所有 `v ∈ In` 的读集 ⊆ `S`」。则

$$\mathrm{mass}\,S\,p\,x
  = \Bigl(\prod_{v\in In} f_v(x)\Bigr)\cdot
    \mathrm{mass}\,S\,\Bigl(\prod_{v\in Out} f_v\Bigr)\,x ,\quad Out = V\setminus In.$$

**⟹ 读法**：`mass S` 只作用在 `Out` 组的积上；`In` 组的积**整体提出**。
**⟹ 塔无关**：`In` 组**从未**被求边缘（不需要 `mass In`），`mass S` **一次**消化 `Out`。 -/
theorem factor_split_mass (G : DAG V) {f : V → (V → α) → ℝ} (hloc : LocalTo G f)
    (p : Joint V α) (hfac : ∀ x, p x = ∏ v, f v x)
    (S In : Finset V)
    (hIn : ∀ v ∈ In, ∀ u, u = v ∨ u ∈ G.parents v → u ∈ S)
    (x : V → α) :
    mass S p x
      = (∏ v ∈ In, f v x) * mass S (fun w => ∏ v ∈ (univ \ In), f v w) x := by
  classical
  rw [mass_eq_mass_of_split S In f p hfac x]
  refine mass_pull_out S (fun w => ∏ v ∈ In, f v w)
    (fun w => ∏ v ∈ (univ \ In), f v w) x ?_
  intro x y hxy
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hloc v x y (fun u hu => hxy u (hIn v hv u hu))

/-! ===========================================================================
  §4 推论：`FactorNorm` × `factor_split_mass` 的「全 `In`」退化形式
  =========================================================================== -/

/-- ⭐⭐ **全 `In` 特例**：若每个顶点的读集 ⊆ `S`（`In = univ`），则
`mass S p x = (∏_v f v x) · mass S (∏_{v∈∅} f v) x = (∏_v f v x) · mass S 1 x`。

这是块 ③ 在 `In = univ` 时的直接读数（`Out = ∅`，残余为常值 `1` 的 `mass`）。 -/
theorem factor_split_mass_all_in (G : DAG V) {f : V → (V → α) → ℝ} (hloc : LocalTo G f)
    (p : Joint V α) (hfac : ∀ x, p x = ∏ v, f v x)
    (S : Finset V)
    (hAll : ∀ v, ∀ u, u = v ∨ u ∈ G.parents v → u ∈ S)
    (x : V → α) :
    mass S p x
      = (∏ v, f v x) * mass S (fun _ => (1 : ℝ)) x := by
  have h := factor_split_mass (G := G) hloc p hfac S univ
    (fun v _ u hu => hAll v u hu) x
  simpa using h

/-! ===========================================================================
  §5 与 `CondIndep` 的对齐：**本策略把桥归约到什么**（供下一路接手）
  =========================================================================== -/

/-!
### §5.1 `CondIndep` 在块 ③ 下的形状

`CondIndep p X Y Z` 要求对每条 `x`：
```
mass (X∪Y∪Z) p x · mass Z p x = mass (X∪Z) p x · mass (Y∪Z) p x。
```
块 ③ 把每个 `mass S p x` 改写成
`(∏_{v∈In_S} f v x) · R_S x`，其中 `R_S := mass S (∏_{v∈Out_S} f v)` 是残余。

代入后 `CondIndep` 变成**四个交叉相乘的等式**。**若**对 `S ∈ {Z, X∪Y∪Z, X∪Z, Y∪Z}`
残余 `R_S` 满足「`In` 组恒常且 `R_S` 与 `f` 的支撑无关」，等式化为
纯**乘积代数恒等式**（由 `dSep` 确定的集合关系给出）——即桥收口。

### §5.2 ⚠ 这正是缺口 ④（`NormalizedResidual`）

上段「**若**」即块 ④。它的**精确陈述**：

```
NormalizedResidual (p G) :=
  ∀ S T : Finset V,   -- S 为 `X∪Z` 型、T 为 `Y∪Z` 型
  ...  -- 残余 R_S、R_T 使得 R_{X∪Y∪Z} · 1 = R_{X∪Z} · R_{Y∪Z} / (∏_Z f)
```

**⟹ 本文件不证它**（一般 DAG 上的真数学工作，需 `FactorNorm` 逐坐标塌缩
`Out` 组、并证残余只依赖 `S` 常数）。**本文件把它作为**唯一的剩余缺口**留下，
不写 `sorry`、不塞前件。**

### §5.3 为什么不退回到塔

既往多路试图在块 ③ 之后「先 `mass Out`、再 `mass S`」，这正是**塔**。
本文**明确禁止**这条：块 ③ 的 `mass S (∏_{v∈Out} f v)` 是**一次** `mass`，
残余 `R_S` 的定义**不含** `mass ∘ mass`。块 ④ 要在**这个一次 `mass` 的形状内**
用 `FactorNorm` 塌缩，而非嵌套。**这是本策略与「塔」在**语法层**就分道的地方。** -/

/-! ===========================================================================
  §6 缺口登记（`NormalizedResidual` / `DSepFactorSplit`）—— **文档，非定理**
  =========================================================================== -/

/-!
### §6.1 `NormalizedResidual`（**缺口 ④**，一般 DAG 上仍缺）

```
NormalizedResidual (G : DAG V) (p : Joint V α) (f : V → (V → α) → ℝ) : Prop :=
  FactorNorm f → LocalTo G f → (∀ x, p x = ∏ v, f v x) →
  ∀ S : Finset V,
    ∃ c : ℝ, c ≠ 0 ∧
      mass S (fun w => ∏ v ∈ (univ \ In_S), f v w) x = c * (∏ v ∈ In_S, f v x)⁻¹ * mass S p x
```
其中 `In_S := {v | {v} ∪ pa_G(v) ⊆ S}`。

### §6.2 `DSepFactorSplit`（**缺口 ④ 的图论化**，任意 DAG 上仍缺）

```
DSepFactorSplit (G : DAG V) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z →
    In_Z ⊆ In_{X∪Z} ∩ In_{Y∪Z}
    ∧ In_{X∪Y∪Z} = In_Z                      -- （示意；真形式需按 dSep 第 4 子句）
```
**⟹ 这条「`In` 集合随 `S` 的单调/相容性」是 `NormalizedResidual` 能跨四个 `S`
一致收口的**纯组合条件**。它在 `dSep` 的 Bayes-Ball 第 4 子句下**应当**成立，
但需要一条新引理「d-分离的祖先闭包 ⟹ 读集嵌套」。**本文件未证。**

### §6.3 本策略的**净贡献**（可被下一路直接消费）

1. **块 ③ `factor_split_mass`**：**已证、通用、零缺口**。任何一路要「按图把因子
   分组、把一组整体提出 `mass`」，可直接调用它，**不必**碰塔。
2. **缺口的**降维**：既往是「缺 `DAG.induce`（库）+ 缺 constants 恒常性（数学）」
   两层；本策略只需一层 `NormalizedResidual`（纯代数-图论引理）。
   `DAG.induce` **不再需要**（块 ③ 不需要诱导子图）。
3. **语法级塔隔离**：残余 `R_S` 是**一次** `mass`，故与 `tower_property_false`
   的反例（`1 ≠ 0`）**在语法上不可能相撞**。
-/

/-! ===========================================================================
  §7 汇总表
  =========================================================================== -/

/-!
| 块 | 内容 | 定理名 | 状态 |
|---|---|---|---|
| ① | `mass` 一次性多重和 | `mass_eq_single_sum`, `mass_loc`, `mass_univ_eq` | ✅ 零缺口 |
| ② | 读集 ⊆ `S` 的因子提出（替代塔）| `mass_pull_out`, `mass_pull_out_local` | ✅ 零缺口 |
| ③ | **因子划分定理** | `prod_split_by_set`, `mass_eq_mass_of_split`, **`factor_split_mass`** | ✅ **零缺口（实质新内容）** |
| ③' | 全 `In` 退化形式 | `factor_split_mass_all_in` | ✅ 零缺口 |
| ④ | `NormalizedResidual` / `DSepFactorSplit` | —（**文档缺口**）| ❌ **未证（不写 sorry）** |

**⟹ 结论**：视角 12 落地了**桥的核心引擎（块 ③）**，并把剩余缺口
从「两层」压到「一条」，同时**在语法上排除**了被证伪的 `mass` 塔。
-/

end FateV2.Predict.Strategy12