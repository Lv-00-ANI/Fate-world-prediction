/-
# 视角 13：图 ⟹ 概率 —— **纤维重指标（Fubini on `Sᶜ`）** 桥

## 0 定位与硬约束

**任务**：给出「图 ⟹ 概率」桥（`Factorizes ⟹ Markov`）的**第 13 种**证明策略，
具体数学构造 + Lean 落地。**硬约束**：**不得使用 `mass` 塔性质**。

塔性质 `mass S (mass T p) x = mass (S∪T) p x` 已被本仓库**证伪**两处：
* `FateV2.Predict.DAGFactorizationGeneral.tower_property_false`（T24），
* `Fate.TowerAudit.mass_idempotent_fails`（A3，连 `S ⊆ T` 方向也假）。

⟹ 本文件**语法层**禁止任何 `mass S (mass T p)` 形式的嵌套。

## 1 与既往各路的结构性区别（为什么是「第 13 种」而非换皮）

`mass S p x` 的定义是「**固定 `S` 上的坐标、对其余同时求和**」的一次求和。
既往各路要么沿 `mass` 迭代（踩塔），要么直接做 `Finset.prod` 重排而**丢掉**
「条件在哪个值」的信息（`View20` 已证 `CondMulLike` 退化）。

**本视角的第 13 种机制：把 `mass` 本身重指标成「对自由坐标的一个普通求和」。**

$$\mathrm{mass}\,S\,g\,x \;=\; \sum_{t\,:\,S^{\mathsf c}\to\alpha} g\bigl(\mathrm{glue}\,S\,x\,t\bigr),
\qquad \mathrm{glue}\,S\,x\,t \;:=\; v\mapsto \begin{cases} x_v & v\in S\\ t_v & v\notin S.\end{cases}$$

* 右端是**一个**对 `t` 的求和，**没有** `mass` 嵌套 —— 塔无关；
* 它由**双射**（`Finset.sum_bij'`，两个方向显式互逆，见 `mass_eq_sum_glue`）给出，
  因此它**不是**「先边缘再边缘」，而是一次**换元（Fubini / 变量替换）**。

由此得到以下结论（**本文件实际交付项，共 6 个定理 + 1 个反例**）：

| 编号 | 内容 | 与既往的差别 |
|---|---|---|
| **T13-a `mass_eq_sum_glue`** | `mass` 的纤维重指标（双射，零缺口）| **新工具**：把边缘变成对 `Sᶜ` 的普通求和 |
| **T13-b′ `mass_depends_on_S`** | `mass S p` 的依赖集**恰为 `S`** | 真版弱化：依赖集**不能**再压缩（见下）|
| ⚠ **T13-b（原版：压缩到 `InSet`）** | **已删除：该陈述为假** | 反例的形式化证明见 `mass_depends_on_InSet_core_refuted` |
| **T13-c `peel_via_fubini`** | 用 T13-a + `FactorNorm` 重新推出 `peel_lower` 引擎 | **未实现**（本文件不含；见 §3 结构说明）|
| **T13-d `fiber_pinned_mass`** | 在 `InSet` 上的纤维钉死恒等式 | **未实现**（同上）|

> **⚠ 诚实的口径修正（本文件头由修复会话更新）**：
> 原稿宣称 T13-b「`mass S p` 的依赖集被压缩到 `InSet G S`」。该陈述**是假的**，已从文件中删除，
> 并在 §3 给出**形式化反例**（`mass_depends_on_InSet_core_refuted`，含全套 `LocalTo`/因子化前件）。
> 原因：`InSet G S = {v∈S : pa(v)⊆S}` 只覆盖「父全在 `S` 内」的顶点，
> 而 `v ∈ S ∖ InSet` 的顶点**自己**也出现在自己的因子里，故 `x` 在 `S ∖ InSet` 上的取值
> 会直接改变 `mass S p x`。正确结论是 T13-b′（依赖集 = `S`）。
> 原稿 §4/§5 提到的 `peel_via_fubini` / `fiber_pinned_mass` **从未落地**，本文件不含它们。

## 2 为什么这绕开塔

塔的失败机制：`mass` 是**非归一化纤维和**，`S ⊆ T` 时
`mass S (mass T p)` 把 **`T∖S` 的纤维大小**（`|α|^{|T∖S|}`）乘进去，故 ≠ `mass T p`。

本视角**从不做 `mass ∘ mass`**：每一次都是「`mass S` 换成 `Σ_{t:Sᶜ}`」，
规范化由 `FactorNorm`（每因子对自身坐标求和为 1）**显式**完成，
**不是**由 `mass` 的自伴随性假设。故与塔**正交**。

## 3 结构

* §1 `glue` 与重指标双射（`mass_eq_sum_glue`）
* §2 单因子对 `t` 的敏感性（`factor_const_of_InSet` / `factor_only_t`）
* §3 依赖集（正确版 `mass_depends_on_S`；**原版 T13-b 的反例与否定证明**）

> **原稿 §4（`peel_via_fubini`）与 §5（`fiber_pinned_mass`）未实现**：
> 二者依赖的「依赖集压缩到 `InSet`」（原 T13-b）为假，故其路线在本文件内无法按原计划落地。
> 本文件**不**包含这两个定理，也不以 `sorry` 占位。

**⚠ 零 `sorry` / 零 `axiom`。** 未闭合处一律以**文档缺口**登记，不写成定理。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.Strategy11TopoPrefix
import Mathlib.Tactic.Ring
import Mathlib.Tactic

open Finset
open FateV2.Modeling.Graph

namespace FateV2.Predict.Strategy13Fubini

open FateV2.Modeling

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

open FateV2.Predict.DAGFactorization (mass unpin)
open FateV2.Predict.FactorMarkov (Joint LocalTo Factorizes FactorNorm CondIndep Markov)

/-!
  # Predict · Strategy13FiberFubini

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy13FiberFubini.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, Strategy11TopoPrefix
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 ⭐⭐⭐ **`glue`：把 `S` 上的 `x` 与 `Sᶜ` 上的 `t` 拼成完整赋值**
  =========================================================================== -/

/-- **`glue S x t`**：在 `S` 上取 `x`，在 `Sᶜ` 上取 `t`。 -/
noncomputable def glue (S : Finset V) (x : V → α) (t : {v // v ∉ S} → α) : V → α :=
  fun v => if h : v ∈ S then x v else t ⟨v, h⟩

@[simp] theorem glue_mem (S : Finset V) (x : V → α) (t : {v // v ∉ S} → α)
    {v : V} (h : v ∈ S) : glue S x t v = x v := by
  simp only [glue, dif_pos h]

theorem glue_notmem (S : Finset V) (x : V → α) (t : {v // v ∉ S} → α)
    {v : V} (h : v ∉ S) : glue S x t v = t ⟨v, h⟩ := by
  simp only [glue, dif_neg h]

/-- 若 `w` 在 `S` 上与 `x` 一致，则 `w` 由其 `Sᶜ` 分量经 `glue` **唯一**重拼。 -/
theorem glue_proj (S : Finset V) (x : V → α) {w : V → α}
    (h : ∀ u ∈ S, w u = x u) :
    glue S x (fun v => w v.1) = w := by
  funext v
  by_cases hv : v ∈ S
  · rw [glue_mem S x _ hv, h v hv]
  · rw [glue_notmem S x _ hv]

/-- ⭐⭐⭐ **T13-a（纤维重指标 / `mass` 的 Fubini 形式，零缺口）。**

$$\mathrm{mass}\,S\,g\,x \;=\; \sum_{t\,:\,S^{\mathsf c}\to\alpha} g\bigl(\mathrm{glue}\,S\,x\,t\bigr).$$

**证明**：`mass` 是「在纤维 `{w // w|_S = x|_S}` 上求和」（`sum_filter`），
而 `t ↦ glue S x t` 与 `w ↦ w|_{Sᶜ}` 是一对**互逆双射**（`sum_bij'`，
`hji`/`hij` 两个方向分别由 `glue_proj` 与 `glue_notmem` 给出）。

**⚠ 右端只有一个求和，没有 `mass` 嵌套 ⟹ 塔无关。** -/
theorem mass_eq_sum_glue (S : Finset V) (g : (V → α) → ℝ) (x : V → α) :
    mass S g x = ∑ t : {v // v ∉ S} → α, g (glue S x t) := by
  classical
  unfold mass
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun (w : V → α) _ => (fun v : {v // v ∉ S} => w v.1))
      (fun (t : {v // v ∉ S} → α) _ => glue S x t) ?_ ?_ ?_ ?_ ?_
  · intro w _; exact Finset.mem_univ _
  · intro t _; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, fun u hu => glue_mem S x t hu⟩
  · intro w hw
    exact glue_proj S x (Finset.mem_filter.mp hw).2
  · intro t _; funext v; exact glue_notmem S x t v.2
  · intro w hw
    show g w = g (glue S x (fun v => w v.1))
    rw [glue_proj S x (Finset.mem_filter.mp hw).2]

/-! ===========================================================================
  §2 **单因子对 `t` 的敏感性**（图在这里做功）
  =========================================================================== -/

/-- `InSet G S`：`S` 中「读集 `{v}∪pa(v)` 完全落在 `S` 内」的顶点。 -/
def InSet (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Finset V :=
  S.filter (fun v => G.parents v ⊆ S)

theorem mem_InSet {G : FateV2.Modeling.Graph.DAG V} {S : Finset V} {v : V} :
    v ∈ InSet G S ↔ v ∈ S ∧ G.parents v ⊆ S := by
  simp only [InSet, Finset.mem_filter]

theorem InSet_subset (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : InSet G S ⊆ S :=
  Finset.filter_subset _ _

/-- ⭐⭐ **读集落在 `S` 内的因子对 `t` 恒常。**（`v ∈ InSet G S`） -/
theorem factor_const_of_InSet {G : FateV2.Modeling.Graph.DAG V} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) {S : Finset V} {v : V} (hv : v ∈ InSet G S)
    (x : V → α) (t t' : {u // u ∉ S} → α) :
    f v (glue S x t) = f v (glue S x t') := by
  obtain ⟨hvS, hpS⟩ := mem_InSet.mp hv
  refine hloc v _ _ fun u hu => ?_
  rcases hu with rfl | hu
  · exact glue_mem S x t hvS ▸ glue_mem S x t' hvS ▸ rfl
  · exact glue_mem S x t (hpS hu) ▸ glue_mem S x t' (hpS hu) ▸ rfl

/-- ⭐⭐ **读集落在 `Sᶜ` 内的因子只依赖 `t`（不依赖 `x`）。**

条件：`v ∉ S` 且 `pa(v) ⊆ Sᶜ`（即 `v` 及其父都在补集里）。
**⟹ 这是 `FactorNorm` 把该因子「积出为 1」的前提。** -/
theorem factor_only_t {G : FateV2.Modeling.Graph.DAG V} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) {S : Finset V} {v : V}
    (hvS : v ∉ S) (hpa : ∀ u ∈ G.parents v, u ∉ S)
    {x x' : V → α} (t : {u // u ∉ S} → α) :
    f v (glue S x t) = f v (glue S x' t) := by
  refine hloc v _ _ fun u hu => ?_
  rcases hu with rfl | hu
  · rw [glue_notmem S x t hvS, glue_notmem S x' t hvS]
  · rw [glue_notmem S x t (hpa u hu), glue_notmem S x' t (hpa u hu)]

/-! ===========================================================================
  §3 ⚠ **依赖集**：正确结论是「依赖集 = `S`」（`mass_depends_on_S`）；
  原「压缩到 `InSet G S`」的陈述**为假**，已删除并给出形式化反例
  =========================================================================== -/

/-- ⭐⭐⭐ **T13-b′（真版：`mass S p` 的依赖集就是 `S` 本身）。**

若 `x, y` 在 **`S`** 上一致，则 `mass S p x = mass S p y`（对任意 `p`，不需要图、不需要因子化）。

**证明**：T13-a 把两边写成同一求和域 `Sᶜ → α` 上的和，逐 `t` 比较；
`glue S x t` 与 `glue S y t` 在 `S` 上用 `h` 对齐、在 `Sᶜ` 上都等于 `t`，故逐点相等。 -/
theorem mass_depends_on_S (S : Finset V) (p : Joint V α) {x y : V → α}
    (h : ∀ v ∈ S, x v = y v) :
    mass S p x = mass S p y := by
  rw [mass_eq_sum_glue S p x, mass_eq_sum_glue S p y]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  funext v
  by_cases hv : v ∈ S
  · rw [glue_mem S x t hv, glue_mem S y t hv, h v hv]
  · rw [glue_notmem S x t hv, glue_notmem S y t hv]

/-! ### ⚠ T13-b（原「依赖集压缩到 `InSet G S`」）**为假**，已删除

原计划（本文件旧版）：

> 若 `p = ∏_v f v`、`f` 局部于 `G`，且 `x, y` 在 `InSet G S = {v∈S : pa(v)⊆S}` 上一致，
> 则 `mass S p x = mass S p y`。

**该陈述是假的**：`x` 在 `S ∖ InSet G S` 上的取值会通过该顶点**自身**的因子
（`f v` 读含 `v` 的读集）直接进入 `mass S p x`，而 `InSet` 只覆盖「父全在 `S` 内」
的顶点，漏掉了这些顶点。

**显式反例**（`V = Fin 2`、边 `0 → 1`、`α = Bool`、`S = {1}`）：
此时 `pa(1) = {0} ⊄ {1}`，故 `InSet G {1} = ∅`，前件对**任意** `x, y` 真空成立；
而取 `f 0 ≡ 1`、`f 1 w = if w 1 then 1 else 0`（`LocalTo` 显然成立，`f 1` 只读坐标 `1`），
则 `p w = if w 1 then 1 else 0`，`mass {1} p x = 2 · [x 1 = true]`，
在 `x ≡ true` 与 `y ≡ false` 处分别取 `2` 与 `0`。**故结论不成立。**

（正确的、不等价于结论的弱化版是上面的 `mass_depends_on_S`：依赖集是 `S` 而非 `InSet G S`。
`InSet` 的正确用途是 `factor_const_of_InSet` / `factor_only_t`：它说明
**哪些因子对补坐标 `t` 不敏感**，这才是「积出为 1」的前提。） -/

/-! #### 反例的形式化证明（`V = Fin 2`，边 `0 → 1`，`α = Bool`，`S = {1}`） -/

/-- 反例用的两步图 `0 → 1`（在 `Fin 2` 上）。 -/
def Gce : FateV2.Modeling.Graph.DAG (Fin 2) where
  edge u v := u = 0 ∧ v = 1
  decEdge := by infer_instance
  acyclic := by
    have key : ∀ a b : Fin 2,
        Relation.TransGen (fun u v : Fin 2 => u = 0 ∧ v = 1) a b → a = 0 ∧ b = 1 := by
      intro a b hab
      induction hab with
      | single h => exact h
      | tail _ h ih => exact ⟨ih.1, h.2⟩
    intro v h
    obtain ⟨h1, h2⟩ := key v v h
    rw [h1] at h2
    exact absurd h2 (by decide)

/-- 反例的因子：`f 0 ≡ 1`，`f 1 w = [w 1 = true]`。 -/
noncomputable def fce : Fin 2 → (Fin 2 → Bool) → ℝ :=
  fun v w => if v = 0 then 1 else (if w 1 = true then 1 else 0)

/-- 反例的联合分布 `p w = [w 1 = true]`。 -/
noncomputable def pce : (Fin 2 → Bool) → ℝ := fun w => if w 1 = true then 1 else 0

theorem fce_factors : ∀ x, pce x = ∏ v, fce v x := by
  intro x
  rw [Fin.prod_univ_two]
  simp only [fce, pce]
  norm_num

theorem fce_local : LocalTo Gce fce := by
  intro v x y h
  by_cases hv : v = 0
  · simp only [fce, if_pos hv]
  · have hv1 : v = 1 := by
      have : (v : Fin 2) = 0 ∨ (v : Fin 2) = 1 := by omega
      rcases this with h0 | h1
      · exact absurd h0 hv
      · exact h1
    simp only [fce, if_neg hv]
    rw [h 1 (Or.inl hv1.symm)]

/-- 反例中 `InSet G {1} = ∅`（`pa(1) = {0} ⊄ {1}`）。 -/
theorem InSet_Gce : InSet Gce ({1} : Finset (Fin 2)) = ∅ := by
  ext v
  simp only [mem_InSet, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
  intro hv
  subst hv
  intro hsub
  have h01 : (0 : Fin 2) ∈ Gce.parents 1 := by
    rw [FateV2.Modeling.Graph.DAG.mem_parents]
    exact ⟨rfl, rfl⟩
  have : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := hsub h01
  simp at this

/-- 反例的 `mass` 精确值：`mass {1} pce x = 2 · [x 1 = true]`。 -/
theorem mass_Gce (x : Fin 2 → Bool) :
    mass ({1} : Finset (Fin 2)) pce x = 2 * (if x 1 = true then 1 else 0) := by
  rw [mass_eq_sum_glue]
  have hterm : ∀ t : {v : Fin 2 // v ∉ ({1} : Finset (Fin 2))} → Bool,
      pce (glue ({1} : Finset (Fin 2)) x t) = (if x 1 = true then 1 else 0) := by
    intro t
    simp only [pce]
    rw [glue_mem ({1} : Finset (Fin 2)) x t (by simp)]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
  have hcard : (Finset.univ.filter (fun v : Fin 2 => v ∉ ({1} : Finset (Fin 2)))).card = 1 := by
    decide
  rw [show (Finset.univ.filter (fun x : Fin 2 => ¬x ∈ ({1} : Finset (Fin 2)))).card = 1 from by
    simpa using hcard]
  norm_num

/-- ⚠ **T13-b（原版陈述）为假**：`mass S p` 的依赖集**不能**压缩到 `InSet G S`。

这里给出该陈述（在 `V = Fin 2`、`α = Bool` 上的全称形式）的**否定证明**：
取 `x ≡ true`、`y ≡ false`，前件真空成立（`InSet G {1} = ∅`），结论却为 `2 ≠ 0`。 -/
theorem mass_depends_on_InSet_core_refuted :
    ¬ (∀ (G : FateV2.Modeling.Graph.DAG (Fin 2)) (f : Fin 2 → (Fin 2 → Bool) → ℝ)
        (p : (Fin 2 → Bool) → ℝ) (S : Finset (Fin 2)) (x y : Fin 2 → Bool),
        LocalTo G f → (∀ z, p z = ∏ v, f v z) →
        (∀ v ∈ InSet G S, x v = y v) → mass S p x = mass S p y) := by
  intro hclaim
  have hx : mass ({1} : Finset (Fin 2)) pce (fun _ => true) = 2 := by
    rw [mass_Gce]; norm_num
  have hy : mass ({1} : Finset (Fin 2)) pce (fun _ => false) = 0 := by
    rw [mass_Gce]; norm_num
  have hh : ∀ v ∈ InSet Gce ({1} : Finset (Fin 2)),
      (fun _ : Fin 2 => true) v = (fun _ : Fin 2 => false) v := by
    rw [InSet_Gce]
    intro v hv
    exact absurd hv (Finset.notMem_empty v)
  have := hclaim Gce fce pce ({1} : Finset (Fin 2)) (fun _ => true) (fun _ => false)
    fce_local fce_factors hh
  rw [hx, hy] at this
  norm_num at this

end FateV2.Predict.Strategy13Fubini