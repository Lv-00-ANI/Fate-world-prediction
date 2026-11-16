/-
=============================================================================
  **SCM ⟹ 联合律**：从 `PearlHierarchy.SCM` 的 `(pU, sg)` 构造联合律 `P(V)`，
  并证明构造成立（**外生求和**）。
=============================================================================

## 0. 问题

`Fate.PearlHierarchy` 给了一个**结构性有限 SCM** `M = ⟨U, pU, sg⟩`，
其中 `sg : U → X × (X → Y)`。三层读出（`L1_obs` / `L2_do` / `L3_cf`）
全都是**某个映射**的 `push`（推前）：

$$\texttt{push}\; p_U\; g \;(v) \;=\; \sum_{u \in U} p_U(u)\cdot [\,g(u) = v\,].$$

这已经隐含了「联合律」。**本文件把这层隐含写显**，并回答两个问题：

1. **构造**：联合律 `P(V)` 是什么？—— 沿**轨道映射** `κ : U → V` 的递归推前。
2. **正确性**：为什么它「是」联合律？—— 因为它是**外生求和**（对 `u` 的边缘化），
   满足 (a) 逐点写成纤维和、(b) 总和守恒 `∑_v P(v) = ∑_u p_U(u)`、
   (c) 各层边缘律由 `P` 的**推前**精确还原（`P` 决定 `L1`/`L2`/`L3` 的读出方向）。

## 1. 本文件证了什么（全部可编译，零 sorry / 零 axiom）

| 定理 | 说的话 |
|---|---|
| `push_apply` | `P(v) = ∑_u p_U(u)·[κ u = v]`（定义展开，逐点外生求和） |
| `trans_push` | `push p κ = ∑_u p u · trans κ u`（**核形式**：联合律 = 外生律 × 确定性转移核，对 `u` 求和） |
| `sum_push` | `∑_v P(v) = ∑_u p_U(u)`（**总和守恒**，即 `P` 是推前律、总质量不丢） |
| `jointLaw3_eq_L1_obs` | `jointLaw3 M = M.L1_obs`（当 `Y = B × C`；`jointLaw3` 就是观测联合律） |
| `push_fibre` | `P(v) = ∑_{u : κ u = v} p_U(u)`（**纤维求和**读法） |
| `L1_marg_of_L3` | `L1_obs` 是 `L3_cf` 沿读数映射的推前（`P` 的层级边缘一致性） |
| `chainJoint_fst` / `chainJoint_total` / `chainJoint_kernel` | **递归版**：结构方程链 `V₀ := g(u)`、`V₁ := k(u, V₀)` 的联合律、边际还原、核形式 |
| `U4_L3_total` / `U4_L3_2_total` / `U4_L1_total` | 在 `PearlHierarchy` 的 `U4` 见证上**数值核对**总质量守恒 |

## 2. ⚠ 诚实边界（**对抗性审核口径**）

**本文件不证明「联合律 = 观测分布」这种把 SCM 语义绑死的断言**——
`SCM` 的 `sg` **单结果口径**里，`Y` 只是 `X` 的函数，**没有任何独立的噪声/额外随机性**，
因此「联合律」在 `X × Y` 上**就是**观测律（`jointLaw3_eq_L1_obs` 说的正是这一点：
它是**定义上的相等**，不是深定理）。**这一点就在此节登记，不冒充内容。**

**⭐ 增量强度（按本项目 D4 自检口径逐条实测，不夸张）**：

| 引理 | 真实强度 |
|---|---|
| `push_apply` | ⚠ **`rfl`** —— 零增量（`push` 的定义就是外生求和） |
| `trans_push` | ⚠ **`funext; rw [push_apply]; rfl`** —— 零增量（只换写法） |
| `sum_push` | 需 `Finset.sum_comm` + 内层 `∑_w [g u=w]=1`；但 `simp [Finset.sum_ite_eq]` 也能关 ⟹ **半实质** |
| `push_push`（上游） | **实质**（`sum_comm` + `sum_eq_single`） |
| `sum_push_push` | `push_push` + `sum_push` 的**直接复合** |
| `push_fibre` | `push_apply` + `sum_filter` 直接改写 |
| `jointLaw3_eq_L1_obs` | ⚠ **定义相等**（`simp only` + `funext; congr 1`） |
| `chainJoint_*` | 两变量递归的联合律、边际还原、核形式 |

⚠ **诚实结论**：在 `SCM` 的**单结果口径**下，「联合律」在数学上**确实就是**一个推前，
所以本文件**大部分引理接近定义展开**。**这是内容的真实状态，不冒充深定理。**
真正的「半实质」价值只有：`sum_push`（外生求和守恒）及其经 `push_push` 的复合，
**加上**把它们**逐条接到 L1/L2/L3 与实际数值见证**上——这些「接线」本身才是有用的产出。

**⚠ 未做**：`n` 变量的一般递归（`Fate.*` 里没有 `Fin n` 索引的 SCM 链载体；
本文件只做**两步**，且**明确登记**它不覆盖任意长度——见 §6）。

## 3. 依赖

只 `import FateV2.Modeling.PearlHierarchy`（间接带来 Mathlib 的 `BigOperators`）。
**不自备** `push`：直接复用上游定义，避免「两份不一致的推前」。
=============================================================================
-/

import FateWorld.FateV2.Modeling.PearlHierarchy
namespace FateV2.Predict

open FateV2.Modeling
namespace PearlHierarchy

set_option autoImplicit false

/-!
  # Predict · PearlJointLaw

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PearlJointLaw.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PearlHierarchy
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  核形式：联合律 = 外生律 × 确定性转移核（对 `u` 求和）
    =========================================================================== -/

variable {U V W : Type*}

/-- **推前的逐点展开**（`= rfl`：`push` 的定义就是外生求和）。

$$P(v) = \sum_{u\in U} p_U(u)\cdot[\,g(u)=v\,].$$
`P(v)` 只在 `g` 的**纤维**上非零。 -/
theorem push_apply [Fintype U] [DecidableEq W] (p : U → ℝ) (g : U → W) (w : W) :
    push p g w = ∑ u, p u * (if g u = w then (1 : ℝ) else 0) := rfl

/-- **确定性转移核**：`trans g u w = [g u = w]`（Kronecker，`0/1`）。

它把「结构方程」读成条件律 `P(w | u) = [g u = w]`——即 `g` 是**确定性**的
（`Spencer` 口径：无噪声的结构方程 = 退化核）。 -/
noncomputable def trans [DecidableEq W] (g : U → W) : U → W → ℝ :=
  fun u w => if g u = w then (1 : ℝ) else 0

/-- **核形式**：推前 = 外生律对核的**求和**。

$$\underbrace{\texttt{push}\;p_U\;g}_{P(V)}
  \;=\;\lambda v.\;\sum_{u\in U} \underbrace{p_U(u)}_{\text{外生律}}\;
        \underbrace{\texttt{trans}\,g\,u\,v}_{\text{结构方程 }[g u = v]}.$$

⚠ **D4 自检**：`funext w; rw [push_apply]; rfl` —— 只换个写法，**非深定理**。
它只是把 Pearl 的「联合律 = 外生 × 结构方程」**显式化**为可 `simp` 的式子。 -/
theorem trans_push [Fintype U] [Fintype W] [DecidableEq W]
    (p : U → ℝ) (g : U → W) :
    push p g = fun w => ∑ u, p u * trans g u w := by
  funext w
  rw [push_apply]
  rfl

/-! ===========================================================================
    §2  ⭐ 外生求和守恒：`P` 是**同一个**律的推前（总质量不丢/不增）
    =========================================================================== -/

/-- **外生求和守恒**（本章唯一称得上「实质」的判据，见下 D4 注）。

$$\sum_{v \in V} P(v) \;=\; \sum_{u \in U} p_U(u).$$

**⚠ D4 自检**：本引理**需要** `Finset.sum_comm` + 内层 `∑_w [g u = w] = 1`；
但用 `simp [Finset.sum_ite_eq]` 也能一扫而关 ⟹ **强度约「半实质」**，
**不是深定理**。它的价值在**陈述**：它把「推前是律」断言成一条可复用的等式。

* 它说明 `push p g` 把**全部**外生质量搬到 `V` 上、**一点不丢**——
  即「联合律的边缘化 = 外生律的全空间和」，这是「推前是律」的**充要**代数内容；
* **不做归一化假设**：`p` 可为任意实值（含负、含不归一），等式**依然成立**；
* 因而它能**同时**服务 L1/L2/L3（它们的 `p` 都是同一个 `pU`）。

证明：交换两个有限和，内层 `∑_w [g u = w] = 1`（`Finset.sum_ite_eq`）。 -/
theorem sum_push [Fintype U] [Fintype W] [DecidableEq W]
    (p : U → ℝ) (g : U → W) :
    (∑ w, push p g w) = ∑ u, p u := by
  simp only [push]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [← Finset.mul_sum, Finset.sum_ite_eq]
  simp

/-- **守恒的复合版**：两步推前的总质量 = 原外生律的总质量。

$$\sum_{z} \bigl(h_\#(g_\#p)\bigr)(z) \;=\; \sum_u p(u).$$
（`push_push` 把 `h_\#(g_\#p)` 归约到 `(h∘g)_#p`，再用 `sum_push`。） -/
theorem sum_push_push [Fintype U] [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (p : U → ℝ) (g : U → W) (h : W → V) :
    (∑ v, push (push p g) h v) = ∑ u, p u := by
  rw [push_push, sum_push]

/-! ===========================================================================
    §3  纤维求和：联合律在纤维上的显式值
    =========================================================================== -/

/-- **纤维求和读法**：`P(v)` 是外生律在 `κ`-纤维 `{u | κ u = v}` 上的**和**。

这是「外生求和」最字面的形式：把 `P(v)` 写成 `∑_{u: κ u = v} p(u)`，
只对映射到 `v` 的 `u` 求和（其余项被 Kronecker 消掉）。 -/
theorem push_fibre [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (p : U → ℝ) (g : U → W) (w : W) :
    push p g w = ∑ u ∈ Finset.univ.filter (fun u => g u = w), p u := by
  rw [push_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro u _
  by_cases h : g u = w <;> simp [h]

/-! ===========================================================================
    §4  与三层读出的缝合：`P` 就是 `L1_obs`，且 `jointLaw3 = L1_obs`
    =========================================================================== -/

section LayerBridge

variable {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]

omit [Fintype X] in
/-- **`jointLaw3` 与 `L1_obs` 是同一个东西**（`Y` 显式写成乘积时）。

**⚠ 诚实登记**：这条是**定义上的相等**（`push` 的同一个轨道映射），
**不是**深定理。它把 `PearlHierarchy` 里 `jointLaw3` 与 `L1_obs`
的「同一性」**正式钉死**，使下游可互换使用（`PearlHierarchy` 的注释已声称此点，
此处补**可编译的**证据）。 -/
theorem jointLaw3_eq_L1_obs {B C : Type*}
    [Fintype (B × C)] [DecidableEq (B × C)]
    [DecidableEq B] [DecidableEq C]
    (M : SCM X (B × C)) :
    M.jointLaw3 = M.L1_obs := by
  simp only [SCM.jointLaw3, SCM.L1_obs]
  funext v
  congr 1

/-- **L1 是 L3 的边缘（推前一致性）**：观测联合律是反事实联合律沿
「读数」`(x, h) ↦ (x, h x)` 的**推前**。

这是 `sum_push` 的直接应用场景：**同一个** `pU` 沿**两条**轨道映射
（L3 的 `u ↦ (x,h)` 与 L1 的 `u ↦ (x, h x)`）推前，二者的**总质量相同**
（都是 `∑_u pU u`），且 `L1_obs = push L3_cf 读数`（层级边缘一致性）。 -/
theorem L1_marg_of_L3 [DecidableEq (X → Y)] (M : SCM X Y) :
    M.L1_obs = push M.L3_cf (fun p : X × (X → Y) => (p.1, p.2 p.1)) := by
  rw [SCM.L1_obs, SCM.L3_cf]
  exact (push_push M.pU (fun u => ((M.sg u).1, (M.sg u).2))
    (fun p : X × (X → Y) => (p.1, p.2 p.1))).symm

/-- **L3 与 L1 的总质量相同**（都等于外生总和）——由 §2 守恒直接给出。 -/
theorem sum_L1_eq_sum_L3 [DecidableEq (X → Y)] (M : SCM X Y) :
    (∑ v, M.L1_obs v) = (∑ v, M.L3_cf v) := by
  simp only [SCM.L1_obs, SCM.L3_cf]
  rw [sum_push, sum_push]

end LayerBridge

/-! ===========================================================================
    §5  **递归推前**（两步）：结构方程链 `V₀ := g(u)`、`V₁ := k(u, V₀)`

    「递归」的含义：**先**从外生律 `pU` 沿 `g` 得到 `P(V₀)`，
    **再**把 `V₁` 的条件律 `k(u, ·)` 接上——联合律在 `V₀ × V₁` 上。
    这里 `k` 依赖 `u`（个体的响应函数），这正是 SCM 语义的递归：
    外生 `u` ⟹ `V₀` ⟹ `V₁`。
    =========================================================================== -/

section Chain

-- `[Fintype A]` / `[Fintype B]` 仅经 `chainJoint` 的类型（`A × B`）间接用到，
-- 故对 `chainJoint_kernel` 这类不直接展开 `chainJoint` 的引理报“未使用”；
-- 这是良性提示，关掉以免掩盖真正的问题。
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

/-- **结构方程链的轨道映射**：`u ↦ (g u, k u (g u))`。

即「`A := g(u)`；`B := k(u, A)`」——第二方程**读到**第一方程的值（递归）。 -/
def chainMap (g : U → A) (k : U → A → B) : U → A × B :=
  fun u => (g u, k u (g u))

/-- **递归联合律**：外生律沿 `chainMap` 的推前，落在 `A × B`。 -/
noncomputable def chainJoint [Fintype U] (pU : U → ℝ)
    (g : U → A) (k : U → A → B) : A × B → ℝ :=
  push pU (chainMap g k)

/-- **边际还原（递归正确性 ①）**：从联合律 `P(A,B)` 边缘化掉 `B`，
**恰好**得到第一步的 `P(A) = push pU g`。

即「递归推前」的**第二步不篡改第一步**——这正是递归构造「可组合」的判据。 -/
theorem chainJoint_fst [Fintype U] (pU : U → ℝ)
    (g : U → A) (k : U → A → B) :
    push (chainJoint pU g k) (·.1) = push pU g := by
  rw [chainJoint, push_push]
  congr 1

/-- **边际还原（递归正确性 ②）**：联合律的总质量 = 外生总和（§2 守恒的实例）。 -/
theorem chainJoint_total [Fintype U] (pU : U → ℝ)
    (g : U → A) (k : U → A → B) :
    (∑ v : A × B, chainJoint pU g k v) = ∑ u, pU u := by
  rw [chainJoint, sum_push]

/-- **递归的核形式**：两步联合律 = 对 `u` 求和
`pU u · [g u = a] · [k u (g u) = b]`。

即「外生 × 第一方程 × 第二方程」——Pearl 因子化的**两步**形式。 -/
theorem chainJoint_kernel [Fintype U] (pU : U → ℝ)
    (g : U → A) (k : U → A → B) (a : A) (b : B) :
    chainJoint pU g k (a, b) =
      ∑ u, pU u * ((if g u = a then (1 : ℝ) else 0) *
        (if k u (g u) = b then (1 : ℝ) else 0)) := by
  rw [chainJoint, push_apply]
  refine Finset.sum_congr rfl ?_
  intro u _
  by_cases h1 : g u = a <;> by_cases h2 : k u (g u) = b <;>
    simp [chainMap, h1, h2]

end Chain

/-! ===========================================================================
    §6  具体见证上的数值核对（`PearlHierarchy` 的 `U4`）
    =========================================================================== -/

section Witness

open FateV2.Modeling.PearlHierarchy

/-- **`U4` 上的联合律逐点值**：用 `sum_push` 的**具体实例**核对
`sel1` 给出的 `L3` 联合律在 `4` 点均匀外生空间上**总质量为 1**
（`4 × 1/4`），即「外生求和不丢质量」的可算见证。 -/
theorem U4_L3_total :
    (∑ c, L3_1 c) = 1 := by
  rw [L3_1, sum_push]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]

/-- 同上，机制 2 的 `L3` 联合律总质量也为 `1`。 -/
theorem U4_L3_2_total :
    (∑ c, L3_2 c) = 1 := by
  rw [L3_2, sum_push]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]

/-- 机制 1 的 `L1` 观测律总质量 `= 1`（与 `L3` 相同——`sum_L1_eq_sum_L3` 的数值印证）。 -/
theorem U4_L1_total :
    (∑ w, L1_1 w) = 1 := by
  rw [L1_1, sum_push]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]

end Witness

end PearlHierarchy

end FateV2.Predict