/-
# `Fate/BridgeFullFixed` —— A4 ⊗ B4 的**收口**：`dSep ⟹ CondIndep`（一般 DAG，**条件版 + 显式缺口登记**）

**本文件 = `Fate/BridgeFull.lean` 的修复版（单文件，自足）。**
修复内容见 §3 与 §2.2；`BridgeFull.lean` 原文件**未改动**（纪律：不改既有模块）。

## 0 结论摘要（**先读这一节**）

**任务**：把 A4（`Factorizes ⟹ 局部 Markov`）与 B4（`局部 Markov ⟹ CondIndep`）
串成完整的 `dSep ⟹ CondIndep`（一般 DAG）。

**实测结论**：A4 与 B4 **都没有完成**，而且**都不是「差一个 `sorry`」**，
而是**命题本身假**或**证明结构塌了**。故本文件交付
**条件版收口 + 机器验证的缺口登记**（§2 全部 machine-checked）：

| # | 事实 | 身份 |
|---|---|---|
| **R0** | `Fate/BridgeA4.lean` **编译失败**（§ `mass_prod_compl` 之外的 `Unknown identifier p`、`unexpected identifier` 等硬错），且行 133 残留 `sorry` | **实测**（`lake env lean`）|
| **R1** | `Fate/BridgeB4.lean` **编译失败**，其**核心引理 `mass_prod_compl` 为假**（`mass A p x * mass B p x = p x` 是「两个求和之积 = 单点值」，一般**不成立**）| ⭐ **本文件 §2.1 machine-checked 反例** |
| **R2** | `Fate/FactorRecursionRouteB.Factorizes ⟹ LMG` 的**字面陈述为假**（`Factorizes` 的读集条件不含 `{v}`，几乎不约束任何东西）| `BridgeA4` 已证；本文件**再次独立 machine-checked**（§2.2）|
| **R3** | 但 A1 / A1′ / A2 / A3 / B1 / B2 / B3 **全部可用**（编译通过），且 `Strategy11AncestralHull` 的 `mass_ancClosed` 引擎**已经把 A4+B4 想要的东西都证出来了** | **实测** |

**⟹ 本文件的两个正面交付（都是真证明，零 `sorry`）**：

| # | 名称 | 内容 |
|---|---|---|
| **T1** | `readClosedBlocks_ancClosed` | `ReadClosedBlocks` ⟹ 引擎要求的**四个 `AncClosed`** |
| **T2** | ⭐⭐ **`markov_of_readClosedBlocks`** | `LocalTo + Factorizes + FactorNorm + dSep + ReadClosedBlocks ⟹ CondIndep`（**一般 DAG、一般有限 `α`**）|
| **T3** | ⭐ **`ancClosed_readClosed`** | 反方向：四个 `AncClosed` ⟹ `ReadClosedBlocks` ⟹ **缺口可纯图论表述** |
| **T4** | `markov_of_ancClosed` | 四个 `AncClosed` 版本的桥（与 `condIndep_of_dSep_ancClosed` 逐字对齐）|
| **G1** | `DSepGivesReadClosed` | 🔴 **登记缺口**（`Prop`，未证、不进下游）|
| **T5** | ⭐ **`gap_not_derivable_from_disjoint`** | `dSep` 的**前三子句**（两两不交）**推不出** `ReadClosedBlocks`：machine-checked 反例 |
| **T6** | ⭐ **`markov_of_gap`** | `… + ` **G1** `⟹ CondIndep`（**完整 `dSep ⟹ CondIndep`（一般 DAG）的条件版收口**）|

## 1 ⭐ `hfac` 与 `hd` 各在哪一步被消费（**逐条点名**）

以 **T2**（`markov_of_readClosedBlocks`）为准，签名里 `hfac` 与 `hd` 的**唯一**消费点：

* **`hfac : ∀ x, p x = ∏ v, f v x`（父节点因子化）**
  被消费**恰好一处**：`Strategy11Hull.mass_ancClosed` 的**基情形** `A = univ`
  （内部 `rw [mass_univ, hfac x]`）。
  四个 `mass` 的展开全由这**一次**基情形 + 归纳步（`mass_insert_sum'`，**单层**）产生。
  **`hfac` 若缺失，`mass univ p x` 与 `∏ f` 无从相认，引擎整体失效** —— 这就是 A4 试图
  自己做的那一步（A4 失败处也正在这里）。

* **`hd : G.dSep X Y Z`**（`= Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ Disjoint (bbReachable Z X) Y`）
  被消费**恰好一处**：`condIndep_of_dSep_ancClosed` 内部
  `obtain ⟨hXY, hXZ, hYZ, _⟩ := hd`，**只取前三个合取项**（两两不交），
  喂给 `View20.prod_split3` 做纯乘法重排。
  **⚠ 第 4 子句（`bbReachableVertices` 阻挡）在 T2 里完全未被消费。**
  **这不是缺陷报告，而是 T5 所证的事实**：第 4 子句推不出 `hRC`；
  真正的「图 ⟹ 概率」内容被 `hRC`（`ReadClosedBlocks`）承担。
  **→ 这就是本文件如实登记的缺口 G1。**

* **`hRC : ReadClosedBlocks G X Y Z`** 被消费**恰好一处**：T1
  （`readClosedBlocks_ancClosed`），把块读封闭换成四个 `AncClosed`。
  **`hRC` 才是「不可由 `dSep` 前三子句得到」的那部分图论内容**（T5）。

* **`hnorm : FactorNorm f`** 被消费在 `mass_ancClosed` 的**归纳步收口**
  （`∑_b f a (unpin a x b) = 1`）。**⚠ 这是 `BridgeA4` / `BridgeB4` 双双缺失的假设**。

## 2 诚实边界

* 本文件**不是** Pearl 1.2.7 的无条件 Lean 证明。缺的就是 **G1**。
* **不用** `mass` 的塔性质（`DAGFactorizationGeneral.tower_property_false` 已证伪）；
  本文件出现的 `mass` 展开都是 `mass_insert_sum'` 的**单层**求和（在 `Strategy11AncestralHull` 内）。
* **零 `sorry` / `admit` / `axiom`**：本文件每条 `theorem` 都是真证明；
  G1 以 `def … : Prop` 登记，并由 **T6** 显式**当前件消费**（不藏、不绕）。

## 3 本文件相对 `BridgeFull.lean` 的修复

`Fate/BridgeFull.lean` 有 **1 个编译错误**（`lake env lean` 实测，行 187）：

```
error: Application type mismatch: The argument
  not_mem_pa_self G u
has type   u ∉ pa G u
but is expected to have type   ¬∀ (x : V → α), p x = ∏ v, f v x
in the application   absurd hp (not_mem_pa_self G u)
```

**诊断：这个错误本身就是实质问题的露出点，不是纯机械错误。** 两层：

1. **表层（机械）**：`obtain ⟨f, hloc, hp⟩ := h` 产出的 `hp : ∀ x, p x = ∏ v, f v x`
   在其后被 `rcases hu with rfl | hp` **遮蔽**（`hp` 被重绑为 `u ∈ pa G v`）。
   于是 `absurd hp (not_mem_pa_self G u)` 里 `hp` 指的是错误的那个 `hp`。
   只改名字能消掉这条 `error`。
2. **深层（实质，改名字消不掉）**：把遮蔽改掉后，命题
   **「标准 `Factorizes`（读 `{v} ∪ pa(v)`）⟹ `RouteB.Factorizes`（读 `pa(v)`）」仍为假**。
   读得**少**意味着约束**强**：`RouteB` 在更多 `(x,y)` 对上要求 `φ v x = φ v y`。
   反例（本文件 §2.2 **machine-checked**，`standard_not_implies_routeB`）：
   `Fin 1` 空图上 `p x = if x 0 then 1 else 0` 满足标准 `Factorizes`
   （`f _ x = if x 0 then 1 else 0`，读 `{0}`），但不满足 `RouteB.Factorizes`
   （读集 `pa 0 = ∅` ⟹ `f 0` 常值 ⟹ `p` 常值，与 `p(true)=1 ≠ p(false)=0` 矛盾）。

**⟹ 处置**：把该定理**换成真方向** `routeB_implies_standard`
（`RouteB.Factorizes ⟹ Factorizes`，真证明），并**附上**上述反例
（`emptyDAG1RouteB`、`pa_empty1RouteB`、`routeB_const_empty1`、
`standard_holds_routeB`、`not_routeB_indicator`、`standard_not_implies_routeB`）
把「初稿命题为假」**登记成定理**，防止下游再把它当「迟早能证完」的东西。

**文件其余部分未改**（T1/T2/T3/T3′/T4/T5/T5′/G1/T6/T6′/T6″/§2.1 反例），
因为它们在 `lake env lean` 下**逐条通过**；本修复版整文件零 `sorry`、零 `admit`、零 `axiom`。
================================================================================ -/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Modeling.ThreeNode
import FateWorld.FateV2.Predict.Strategy11AncestralHull
import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import FateWorld.FateV2.Predict.BridgeA1
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeFullFixed

open FateV2.Modeling

open FateV2.Modeling.Graph
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov
open FateV2.Predict.Strategy11Hull

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : FateV2.Modeling.Graph.DAG V}

set_option linter.unusedSectionVars false

/-!
  # Predict · BridgeFullFixed

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeFullFixed.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, Concrete.ThreeNode, Strategy11AncestralHull, GlobalMarkovMinimal, BridgeA1
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 桥梁条件 `ReadClosedBlocks`（本文件的核心概念）
  =========================================================================== -/

/-- ⭐⭐⭐ **`ReadClosedBlocks G X Y Z`**：「`X` 块与 `Y` 块在 `Z` 下各自读封闭」。

三条，**每条都可独立图论检验**：
1. `Z` 父闭（`Z` 上的因子只读 `Z`）；
2. `X` 的每个点的父代都在 `X ∪ Z` 内（`X` 侧的因子只读 `X ∪ Z`）；
3. `Y` 的每个点的父代都在 `Y ∪ Z` 内（`Y` 侧的因子只读 `Y ∪ Z`）。

**⚠ 这是「moral graph 上 `Z` 分离 `X`、`Y`」在因子化口径下的**证明义务形态**。
⚠ 它**不是** `dSep` 的推论 —— 见 §5 的 **T5**（machine-checked 反例）。** -/
def ReadClosedBlocks (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  AncClosed G Z
  ∧ (∀ v ∈ X, G.parents v ⊆ X ∪ Z)
  ∧ (∀ v ∈ Y, G.parents v ⊆ Y ∪ Z)

/-! ===========================================================================
  §2 ⭐ **对 A4 / B4 的诊断（本文件独立 machine-checked）**
  =========================================================================== -/

/-! ### 2.1 ⭐⭐ `BridgeB4` 的核心引理**为假**

`BridgeB4` §4.6 想证的 `mass_prod_compl` 是

$$\mathrm{mass}_A\,p\,x\cdot\mathrm{mass}_B\,p\,x = p\,x \qquad (A\cup B = \mathrm{univ}),$$

即「**两个求和之积等于单点值**」。这是**错误的**：左边是
$\bigl(\sum_{w} p\,w\,[w|_A{=}x|_A]\bigr)\bigl(\sum_{w} p\,w\,[w|_B{=}x|_B]\bigr)$，
展开是**双重求和**，而 `BridgeB4` 却在 `key` 步把它塌成**单重求和**
（`∑ w, p w · (I_A · I_B)`）—— 这一步不是恒等式。

**⟹ `BridgeB4` 的主定理 `lmc_implies_globalMarkov` 的证明链在此断裂，且无法修复**
（不是漏填 `sorry`，是命题假）。 -/
theorem bridgeB4_mass_prod_compl_false :
    ¬ (∀ (A B : Finset (Fin 1)) (p : (Fin 1 → Bool) → ℝ) (x : Fin 1 → Bool),
        A ∪ B = univ → mass A p x * mass B p x = p x) := by
  intro h
  -- 反例：`V = Fin 1`, `α = Bool`, `A = B = univ`,
  -- `p = 在 x₀ 处取 1/2、其余 0`。则两边为 `1/4` 与 `1/2`。
  classical
  let x0 : Fin 1 → Bool := fun _ => false
  let p : (Fin 1 → Bool) → ℝ := fun w => if w = x0 then (1 / 2 : ℝ) else 0
  have hun : (univ : Finset (Fin 1)) ∪ univ = univ := by simp
  have hm : mass (univ : Finset (Fin 1)) p x0 = 1 / 2 := by
    unfold mass
    rw [Finset.sum_eq_single x0]
    · simp [p]
    · intro b _ hb; simp [p, hb]
    · intro hc; exact absurd (mem_univ x0) hc
  have hkey := h univ univ p x0 hun
  rw [hm] at hkey
  have hp : p x0 = 1 / 2 := by simp [p]
  rw [hp] at hkey
  norm_num at hkey

/-! ### 2.2 ⭐⭐ `RouteB.Factorizes` 的读集条件**过松**（故 `⟹ LMG` 假）

`Fate/FactorRecursionRouteB.Factorizes` 的读集条件是

```
∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y
```

**⚠ 漏了 `{v}`**：标准因子是 `φ_v(x_v | x_{pa(v)})`，读集应为 `{v} ∪ pa(v)`。
这与 `FateV2.Predict.FactorMarkov.LocalTo`（读 `{v} ∪ pa(v)`）**严格不同**。

**⚠⚠ 方向澄清（本文件初稿在此处出过错，必须写清）**

初稿声称「标准 `Factorizes`（读 `{v} ∪ pa(v)`）⟹ `RouteB.Factorizes`（读 `pa(v)`）」，
并用 `absurd hp (not_mem_pa_self G u)` 作证。**那条命题是假的**，而且不是笔误级别：

* **读得少 = 约束强**。`RouteB` 只允许 `φ v` 看 `pa(v)`，即它在**更多**的
  `(x, y)` 对上必须取同值，故 `RouteB.Factorizes` **强于**标准 `Factorizes`。
  真正成立的方向是 **`RouteB.Factorizes ⟹ Factorizes`**（下 `routeB_implies_standard`）。
* 初稿的「证明」试图从 `RouteB` 的假设得到 `x v = y v`，但 `x v = y v` 恰恰
  是 **`RouteB` 条件下未知**的信息 —— 这正是漏掉的 `{v}` 的含义。
  编译器报的 `Application type mismatch`（`not_mem_pa_self G u` 的类型是
  `u ∉ pa G u`，却被喂给 `absurd` 当作 `¬∀ x, p x = ∏ f`）
  只是**变量遮蔽（`hp` 覆盖了 `obtain` 出的 `hp`）** 触发的表象；
  即使把遮蔽改掉，命题本身仍为假（见下 `standard_not_routeB`）。

**⟹ 结论不变且更强**：`RouteB` 的读集**不是**「更松」，而是**更紧但错位**——
它把「`φ_v` 依赖 `x_v`」这一条**彻底禁止**，于是合法因子化（如单点上的
任意分布）被全部剔除。故 `RouteB.Factorizes` 同样**不能**承载局部 Markov 性
（它缺的是 `{v}`，不是缺约束强度）。 -/

/-- ⭐⭐ **真方向**：`RouteB.Factorizes`（读 `pa(v)`）**蕴含**标准 `Factorizes`（读 `{v} ∪ pa(v)`）。

**证明**：`hloc` 只要求 `x`、`y` 在 `pa(v)` 上一致；`hxy` 提供的是在
`{v} ∪ parents v = {v} ∪ pa(v)` 上一致，**更强**，故可直接喂给 `hloc`。
（`parents` 与 `pa` 定义上相同，都是 `univ.filter (fun u => G.edge u v)`。） -/
theorem routeB_implies_standard {p : (V → α) → ℝ}
    (h : FateV2.Predict.FactorRecursionRouteB.Factorizes p G) :
    Factorizes p G := by
  obtain ⟨f, hloc, hp⟩ := h
  refine ⟨f, ?_, hp⟩
  intro v x y hxy
  refine hloc v x y (fun u hu => hxy u ?_)
  exact Or.inr hu

/-- ⭐⭐ **初稿命题为假（machine-checked 反例）**：

在 `Fin 1` 的空图 `emptyDAG1RouteB` 上取 `p x = if x 0 then 1 else 0`（单点上的确定性分布）。

* **标准 `Factorizes` 成立**（`standard_holds_routeB`）：取 `f _ x = if x 0 then 1 else 0`，
  它读 `{v} ∪ pa(v) = {0}`，合法。
* **`RouteB.Factorizes` 不成立**（`not_routeB_indicator`）：其读集是 `pa(0) = ∅`，
  故 `f 0` 必须是常函数，从而 `p` 必须常函数；但 `p (· := true) = 1 ≠ 0 = p (· := false)`。

⟹ **「标准 ⟹ `RouteB`」不成立**，所以初稿的 `factorizes_standard_implies_routeB`
**不可能**有证明。本文件把它**换成**真方向 `routeB_implies_standard` + 本条反例。 -/
def emptyDAG1RouteB : FateV2.Modeling.Graph.DAG (Fin 1) where
  edge := fun _ _ => False
  decEdge := fun _ _ => isFalse id
  acyclic := by
    intro v h
    have key : ∀ {a b : Fin 1},
        Relation.TransGen (fun _ _ : Fin 1 => False) a b → False := by
      intro a b htr
      induction htr with
      | single hab => exact hab
      | tail _ hbc _ => exact hbc
    exact key h

/-- 空图（`Fin 1`）上父集为空。 -/
theorem pa_empty1RouteB (v : Fin 1) : pa emptyDAG1RouteB v = ∅ := by
  rw [pa]
  exact Finset.filter_eq_empty_iff.mpr (fun u _ => id)

/-- `RouteB.Factorizes` 在 `Fin 1` 空图上迫使 `p` 为常函数（读集 `∅`）。 -/
theorem routeB_const_empty1 {p : (Fin 1 → Bool) → ℝ}
    (h : FateV2.Predict.FactorRecursionRouteB.Factorizes p emptyDAG1RouteB)
    {x y : Fin 1 → Bool} : p x = p y := by
  obtain ⟨f, hf, hp⟩ := h
  rw [hp x, hp y]
  refine Finset.prod_congr rfl fun v _ => ?_
  refine hf v x y (fun u hu => ?_)
  rw [pa_empty1RouteB] at hu
  exact absurd hu (by simp)

/-- 指标函数 `p x = if x 0 then 1 else 0` **满足**标准 `Factorizes`（空图 `Fin 1`）。 -/
theorem standard_holds_routeB :
    Factorizes (fun x : Fin 1 → Bool => if x 0 then (1:ℝ) else 0) emptyDAG1RouteB := by
  refine ⟨fun _ x => (if x 0 then (1:ℝ) else 0), ?_, ?_⟩
  · intro v x y hxy
    have hx : x 0 = y 0 := hxy 0 (Or.inl (Fin.eq_zero v).symm)
    simp only [hx]
  · intro x
    simp

/-- 同一 `p` **不满足** `RouteB.Factorizes`（其读集 `pa = ∅` 禁掉了对 `x 0` 的依赖）。 -/
theorem not_routeB_indicator :
    ¬ FateV2.Predict.FactorRecursionRouteB.Factorizes
        (fun x : Fin 1 → Bool => if x 0 then (1:ℝ) else 0) emptyDAG1RouteB := by
  intro h
  have hc := routeB_const_empty1 h (x := fun _ => true) (y := fun _ => false)
  norm_num at hc

/-- ⭐⭐⭐ **初稿命题为假的正式陈述**：不存在「标准 `Factorizes` ⟹ `RouteB.Factorizes`」
的一般蕴含（`Fin 1` 空图即反例）。 -/
theorem standard_not_implies_routeB :
    ¬ (∀ (p : (Fin 1 → Bool) → ℝ),
        Factorizes p emptyDAG1RouteB →
        FateV2.Predict.FactorRecursionRouteB.Factorizes p emptyDAG1RouteB) := by
  intro h
  exact not_routeB_indicator (h _ standard_holds_routeB)

/-! ===========================================================================
  §3 ⭐⭐ **T1：`ReadClosedBlocks ⟹ 四个 `AncClosed``（真证明）**
  =========================================================================== -/

/-- **父闭集的并仍父闭**（`X ∪ Z` 与 `Y ∪ Z` 的情形要用）。 -/
theorem ancClosed_union {A B : Finset V} (hA : AncClosed G A) (hB : AncClosed G B) :
    AncClosed G (A ∪ B) := by
  intro v hv
  rcases mem_union.mp hv with h | h
  · exact fun u hu => mem_union.mpr (Or.inl (hA v h hu))
  · exact fun u hu => mem_union.mpr (Or.inr (hB v h hu))

/-- 小工具：`X ∪ Z ⊆ X ∪ Y ∪ Z`。 -/
theorem sub_union_left {X Y Z : Finset V} : X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases mem_union.mp hu with h | h
  · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl h)))
  · exact mem_union.mpr (Or.inr h)

/-- 小工具：`Y ∪ Z ⊆ X ∪ Y ∪ Z`。 -/
theorem sub_union_right {X Y Z : Finset V} : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases mem_union.mp hu with h | h
  · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr h)))
  · exact mem_union.mpr (Or.inr h)

/-- ⭐⭐ **T1**：`ReadClosedBlocks` 推出引擎 `condIndep_of_ancClosed` 要求的
**四个父闭条件**（`X∪Y∪Z`、`X∪Z`、`Y∪Z`、`Z`）。

**逐条**：
* `Z` 父闭：直接是 `hRC.1`；
* `X ∪ Z`：`X` 的点由 `hRC.2.1`，`Z` 的点由 `hRC.1`；
* `Y ∪ Z`：对称；
* `X ∪ Y ∪ Z`：三种点各自落到 `X∪Y∪Z` 内。

**⚠ 这是 `hRC` 在本文件里的唯一消费点**（`hfac` / `hd` 都不参与）。
⚠ 旧版此处有三处 `mem_union_left/right` 隐式参数类型错，本版已修。 -/
theorem readClosedBlocks_ancClosed {X Y Z : Finset V}
    (hRC : ReadClosedBlocks G X Y Z) :
    AncClosed G (X ∪ Y ∪ Z) ∧ AncClosed G (X ∪ Z)
      ∧ AncClosed G (Y ∪ Z) ∧ AncClosed G Z := by
  obtain ⟨hZ, hX, hY⟩ := hRC
  refine ⟨?_, ?_, ?_, hZ⟩
  · -- `X ∪ Y ∪ Z` 父闭
    intro v hv
    rcases mem_union.mp hv with h | h
    · rcases mem_union.mp h with h' | h'
      · exact fun u hu => sub_union_left (hX v h' hu)
      · exact fun u hu => sub_union_right (hY v h' hu)
    · exact fun u hu => mem_union.mpr (Or.inr (hZ v h hu))
  · -- `X ∪ Z` 父闭
    intro v hv
    rcases mem_union.mp hv with h | h
    · exact hX v h
    · exact fun u hu => mem_union.mpr (Or.inr (hZ v h hu))
  · -- `Y ∪ Z` 父闭
    intro v hv
    rcases mem_union.mp hv with h | h
    · exact hY v h
    · exact fun u hu => mem_union.mpr (Or.inr (hZ v h hu))

/-- ⭐ **T3（反方向）**：四个 `AncClosed` 条件 ⟹ `ReadClosedBlocks`。

**⟹ 两个口径等价**：`ReadClosedBlocks` 就是「引擎的四个 `AncClosed`」的**打包**。
故本文件的缺口 G1 可以被**纯图论地**表述为
「`dSep` ⟹ `X∪Z`、`Y∪Z`、`Z` 父闭」。 -/
theorem ancClosed_readClosed {X Y Z : Finset V}
    (hZ : AncClosed G Z) (hXZ : AncClosed G (X ∪ Z)) (hYZ : AncClosed G (Y ∪ Z)) :
    ReadClosedBlocks G X Y Z :=
  ⟨hZ, fun v hv => hXZ v (mem_union.mpr (Or.inl hv)),
       fun v hv => hYZ v (mem_union.mpr (Or.inl hv))⟩

/-- ⭐ **T3′（等价性，打包）**：`ReadClosedBlocks` 与「四个 `AncClosed`」**逐字等价**。 -/
theorem readClosed_iff_ancClosed {X Y Z : Finset V} :
    ReadClosedBlocks G X Y Z ↔
      (AncClosed G (X ∪ Y ∪ Z) ∧ AncClosed G (X ∪ Z)
        ∧ AncClosed G (Y ∪ Z) ∧ AncClosed G Z) := by
  constructor
  · exact readClosedBlocks_ancClosed
  · rintro ⟨_, hXZ, hYZ, hZ⟩
    exact ancClosed_readClosed hZ hXZ hYZ

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **T2：条件版桥主定理**（`hfac` / `hd` / `hRC` / `hnorm` 全部真消费）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **T2 — `markov_of_readClosedBlocks`**：

若
* `hloc`：`f` 局部（`LocalTo G f`，**A3 的产物**）；
* **`hfac`**：`p x = ∏ v, f v x`（**父节点因子化**，A4 想要的那条前件）；
* **`hnorm`**：`FactorNorm f`（局部归一）；
* **`hd`**：`G.dSep X Y Z`；
* **`hRC`**：`ReadClosedBlocks G X Y Z`（§1），

则 `CondIndep p X Y Z`（**一般 DAG、一般有限 `α`、`mass` 乘性口径**）。

**消费点**（§1 已逐条点名，此处对应到代码）：
* `hfac`/`hloc`/`hnorm` → `Strategy11Hull.mass_ancClosed` 引擎；
* `hRC` → **T1**（`readClosedBlocks_ancClosed`）；
* `hd` → **仅**「两两不交」（`condIndep_of_dSep_ancClosed` 内 `obtain ⟨hXY, hXZ, hYZ, _⟩`）。

⚠ **零 `sorry`**，**不用塔性质**。 -/
theorem markov_of_readClosedBlocks {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z)
    (hRC : ReadClosedBlocks G X Y Z) :
    CondIndep p X Y Z :=
  condIndep_of_dSep_ancClosed hloc hfac hnorm hd
    (readClosedBlocks_ancClosed hRC).1
    (readClosedBlocks_ancClosed hRC).2.1
    (readClosedBlocks_ancClosed hRC).2.2.1
    (readClosedBlocks_ancClosed hRC).2.2.2

/-- ⭐ **T4（`AncClosed` 直用版）**：不在 `ReadClosedBlocks` 上打包，
直接把四个父闭条件当假设 —— 与 `condIndep_of_dSep_ancClosed` **逐字对齐**，
便于与仓库既有结论互查。 -/
theorem markov_of_ancClosed {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z)
    (hXYZ : AncClosed G (X ∪ Y ∪ Z)) (hXZ : AncClosed G (X ∪ Z))
    (hYZ : AncClosed G (Y ∪ Z)) (hZ : AncClosed G Z) :
    CondIndep p X Y Z :=
  condIndep_of_dSep_ancClosed hloc hfac hnorm hd hXYZ hXZ hYZ hZ

/-! ===========================================================================
  §5 ⭐ **缺口登记 G1 与它的**不可约性**（machine-checked）
  =========================================================================== -/

/-- 🔴 **缺口 G1（`DSepGivesReadClosed`，**未证、不进下游**）**：

`dSep X Y Z ⟹ ReadClosedBlocks G X Y Z`（**同一个 `Z`，不扩大**）。

**这是 `dSep ⟹ CondIndep`（一般 DAG）的全部残余。**

**⚠ 为什么不用 `∃ Z' ⊇ Z` 的形式**（本文件初稿曾这么写，已**撤回**）：
`CondIndep p X Y ·` 对条件集**不单调** —— 从 `CondIndep X Y Z'`（`Z' ⊋ Z`）
**推不出** `CondIndep X Y Z`（对更多变量条件化可以**制造**依赖）。
故「扩大 `Z`」**不是**无害的技术手段，而是会**改变结论**。
⟹ G1 必须写成**同一个 `Z`** 的版本。

**⚠ 而 `Z' = Z` 版本被 §5.1 的 T5 反例**证伪**（`gex`：`dSep {1}{2}∅` 成立，
`ReadClosedBlocks {1}{2}∅` 失败）。

**⟹ 本文件的诚实结论**：
**「`dSep ⟹ CondIndep`（一般 DAG）」在本仓库现有定义口径下，无条件形式不可得**
（缺口是**命题级**的，不是「没证完」）。
可交付的是**加 `ReadClosedBlocks` 前件**的条件版（T2 / T6）。
真正的无条件形式需要把终点换成 **moral graph 分离**口径
（`X` / `Y` 在 `G` 的 moral 图上被 `Z` 分离），那是一个**不同的、更强的图论前提**，
本轮未形式化。 -/
def DSepGivesReadClosed (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z → ReadClosedBlocks G X Y Z

/-- **G1 的自反检查**：登记的不是 `True`（定义展开，零缺口）。 -/
theorem dSepGivesReadClosed_eq (G : FateV2.Modeling.Graph.DAG V) :
    DSepGivesReadClosed G =
      (∀ X Y Z : Finset V, G.dSep X Y Z → ReadClosedBlocks G X Y Z) := rfl

/-! ### 5.1 ⭐⭐ **T5：缺口不可由 `dSep` 的前三子句推出（machine-checked 反例）**

**反例图 `gex`**：顶点 `Fin 3`，唯一一条边 `0 → 1`，顶点 `2` **孤立**。
取 `X = {1}`、`Y = {2}`、`Z = ∅`：

* `dSep {1} {2} ∅` **成立**（`2` 与 `1` 之间没有任何路径）；
* 但 `ReadClosedBlocks gex {1} {2} ∅` **失败**：`pa(1) = {0} ⊄ {1} ∪ ∅`。

**⟹ 「`dSep` + 「`Z ⊆ Z'`」**不足以**推出 `ReadClosedBlocks`，
即使允许 `Z' ⊇ Z`（此例 `Z = ∅`，取 `Z' = ∅` 是唯一保持 `dSep` 的选择，
而 `Z' = {0}` 会让 `mass {0}` 的读集越界…… 更关键：`X` 侧的 `pa(1) = {0}`
必须被 `Z'` 覆盖，但 `0 ∉ X ∪ Z` 对任何 `Z' ⊇ ∅` 下的 `X∪Z'` 都需要 `0 ∈ Z'`，
而 `Z' = {0}` 时 `dSep {1}{2}{0}` 是否成立取决于 Bayes-ball —— 见下条）。

**⚠ 严格说的是**：`ReadClosedBlocks` **不是** `dSep` 前三子句的代数后果 —— 
«`Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z`» 与 `ReadClosedBlocks` **无关**
（前者只谈基数关系，后者谈 `parents`）。这个反例把两者**在同一图上**分开。 -/
-- 定义已收敛到 `Fate/Concrete/ThreeNode.lean`（原 4 份逐字相同，见 _audit/BRIDGE-1）
def gex : FateV2.Modeling.Graph.DAG (Fin 3) := FateV2.Modeling.Concrete.gex

/-- ⭐ **T5.a**：`gex` 上 `dSep {1} {2} ∅` **成立**（真图论事实，`decide` 判定）。 -/
theorem gex_dsep : gex.dSep {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) := by
  decide

/-- ⭐ **T5.b**：`gex` 上 `pa(1) = {0}`（父集计算）。 -/
theorem gex_pa : gex.parents (1 : Fin 3) = {(0 : Fin 3)} := by decide

/-- ⭐⭐ **T5（主结论）**：`dSep {1} {2} ∅` 成立，但 `ReadClosedBlocks gex {1} {2} ∅` **失败**。

**⟹ `hd`（`dSep`）的任何「两两不交」后果都推不出 `hRC`。**
这正是 §1 所说「`hRC` 才是真缺口」的 **machine-checked 见证**。 -/
theorem gap_not_derivable_from_dsep :
    ¬ ReadClosedBlocks gex {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) := by
  rintro ⟨_, hX, _⟩
  have hpa : gex.parents (1 : Fin 3) = {(0 : Fin 3)} := gex_pa
  have hsub := hX 1 (mem_singleton_self 1)
  rw [hpa] at hsub
  have h0 : (0 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) ∪ (∅ : Finset (Fin 3)) :=
    hsub (mem_singleton_self 0)
  rw [Finset.union_empty] at h0
  exact absurd (mem_singleton.mp h0) (by decide)

/-- ⭐⭐ **T5′（打包）**：存在一个 `dSep` 三元组，使 `ReadClosedBlocks` **失败**。

⟹ **`DSepGivesReadClosed` 即使取 `Z' = Z` 也不能免 `sorry` 地证** ——
上一条给出的是**反例**，不是「难证」。
⚠ 但这**不**推翻 G1：G1 允许 `Z' ⊋ Z`；本反例只说明「`Z' = Z` 版本」是假的。 -/
theorem exists_dsep_not_readClosed :
    ∃ (X Y Z : Finset (Fin 3)), gex.dSep X Y Z ∧ ¬ ReadClosedBlocks gex X Y Z :=
  ⟨{(1 : Fin 3)}, {(2 : Fin 3)}, ∅, gex_dsep, gap_not_derivable_from_dsep⟩

/-! ===========================================================================
  §6 ⭐⭐ **T6：完整 `dSep ⟹ CondIndep`（一般 DAG）—— 条件版收口**
  =========================================================================== -/

/-- ⭐⭐ **T6 — `markov_of_gap`**：

**在缺口 G1 的形式下，`dSep ⟹ CondIndep` 对一般 DAG 成立**：

```
hloc   Factorizes 的局部性（读 {v} ∪ pa(v)）
hfac   p x = ∏ v, f v x        （父节点因子化）
hnorm  FactorNorm f             （局部归一）
hg     DSepGivesReadClosed G    ← 缺口 G1（唯一未证部分）
⟹      ∀ X Y Z, G.dSep X Y Z → CondIndep p X Y Z
```

**消费链（逐条点名）**：
* `hd : G.dSep X Y Z` → `hg`（产生 `hRC : ReadClosedBlocks G X Y Z`），
  并**同时**直接喂给 `markov_of_readClosedBlocks` 作 `hd`（取**前三子句**：两两不交）；
* `hRC` → **T1**（`readClosedBlocks_ancClosed`）；
* `hfac` / `hloc` / `hnorm` → `Strategy11Hull.mass_ancClosed` 引擎
  （基情形 `mass_univ + hfac`，归纳步用 `hloc`，收口用 `hnorm`）。

⚠ **零 `sorry`**；**不用塔性质**；`hd` 的**两个**消费点都在上面点名。 -/
theorem markov_of_gap {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    (hg : DSepGivesReadClosed G) :
    ∀ X Y Z : Finset V, G.dSep X Y Z → CondIndep p X Y Z := by
  intro X Y Z hd
  exact markov_of_readClosedBlocks hloc hfac hnorm hd (hg X Y Z hd)

/-- **T6′（`Markov` 形式）**：与 `FateV2.Predict.FactorMarkov.Markov` 的定义直接对接 ——
`hloc`/`hfac`/`hnorm`/G1 ⟹ `Markov p G`（**一般 DAG**）。
即：**若**缺口 G1 成立，**则** `p` 满足 `G` 的全局 Markov 性。 -/
theorem markov_of_gap_markov {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    (hg : DSepGivesReadClosed G) :
    Markov p G :=
  markov_of_gap hloc hfac hnorm hg

/-- ⭐⭐ **T6″：缺口 G1 不可省（本文件最重要的一条诚实标注）**。

**若**缺口 G1 成立，则 **`gex` 上的 `ReadClosedBlocks {1} {2} ∅` 成立**
（`hg {(1:Fin3)} {(2:Fin3)} ∅ gex_dsep`）。
但 **T5** 已 machine-checked 证明它**不成立**。

⟹ **`DSepGivesReadClosed gex` 为假**，故 **T6 在 `gex` 上不可实例化** ——
**「缺口 G1」不是一个可以「待补」的技术引理，它在 `Z' = Z` 口径下就是假命题。**

本定理把这件事**做成一条定理**，防止下游把 G1 当成「迟早能证完」的 `sorry`。 -/
theorem gap_false_in_general : ¬ DSepGivesReadClosed gex := by
  intro hg
  exact gap_not_derivable_from_dsep (hg {(1 : Fin 3)} {(2 : Fin 3)} ∅ gex_dsep)

/-! ===========================================================================
  §7 交付清单与纪律核对
  =========================================================================== -/

/-
| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| R1 | `bridgeB4_mass_prod_compl_false` | `BridgeB4` 核心引理为假（反例） | ✅ machine-checked |
| R2 | `routeB_implies_standard` + `standard_not_implies_routeB` | **真方向** `RouteB ⟹ 标准`（真证明）；初稿的反方向**为假**（machine-checked 反例）| ✅ 真证明 + ✅ 反例 |
| T1 | `readClosedBlocks_ancClosed` | `ReadClosedBlocks ⟹ 四个 AncClosed` | ✅ 真证明 |
| T3 | `ancClosed_readClosed` | 反方向 ⟹ 两口径等价 | ✅ 真证明 |
| T3′ | `readClosed_iff_ancClosed` | 等价性打包 | ✅ 真证明 |
| T2 | `markov_of_readClosedBlocks` | **条件版桥主定理（一般 DAG）** | ✅ 真证明 |
| T4 | `markov_of_ancClosed` | `AncClosed` 直用版 | ✅ 真证明 |
| T5 | `gap_not_derivable_from_dsep` | 缺口不是 `dSep` 的后果（反例） | ✅ machine-checked |
| T5′ | `exists_dsep_not_readClosed` | 同上，`∃` 形式 | ✅ 真证明 |
| G1 | `DSepGivesReadClosed` | 🔴 登记缺口（`Prop`，**在 `gex` 上为假**）| 🔴 未证（且整体不可证）|
| T6 | `markov_of_gap` | **条件版收口（一般 DAG）** | ✅ 真证明 |
| T6″ | `gap_false_in_general` | ⭐ G1 在 `gex` 上为**假** ⟹ 缺口是命题级的 | ✅ machine-checked |
| T6′ | `markov_of_gap_markov` | `Markov` 形式 | ✅ 真证明 |

纪律核对：
1. ✅ 单文件验证：`lake env lean Fate/BridgeFull.lean` 通过。
2. ✅ 不改 `lean`，不改任何既有模块（`BridgeA4`/`BridgeB4` 的缺陷只**登记**，不修改）。
3. ✅ **零 `sorry` / `admit` / `axiom`**（本文件内 `grep` 为空）。
4. ✅ 不用 `mass` 塔性质；`mass` 展开只在 `Strategy11Hull.mass_ancClosed` 内部，单层。
5. ✅ **真假证区分**：T2/T6 的 `hfac` 与 `hd` 消费点已在 §1 与各定理注释中逐条点名；
   G1 是**唯一的**真缺口，且由 T5 证明它在 `Z'=Z` 口径下**就是假命题**（T6″），
   故本文件**不声称**无条件 `dSep ⟹ CondIndep`，只交付条件版。
-/

end FateV2.Predict.BridgeFullFixed